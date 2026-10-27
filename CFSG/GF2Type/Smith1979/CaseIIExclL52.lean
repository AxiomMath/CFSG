module

public import CFSG.Open.StatedDefs
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.QuotientGroup.Basic
import CFSG.Open.StatedZModTwo
import CFSG.GroupTheory.GL52.SylowSeven

public section

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup

theorem commutator_mem_of_involutive {C : Type*} [Group C] [Finite C] (Z : Subgroup C)
    [Z.Normal] (τ : C →* C) (hτ : ∀ c, τ (τ c) = c) (hτZ : ∀ z ∈ Z, τ z = z)
    (hZ : ∀ z ∈ Z, z * z = 1 → z = 1) (hfix : ∀ c, τ c = c → c ∈ Z) (a b : C) :
    a * b * a⁻¹ * b⁻¹ ∈ Z := by
  have hle : Z ≤ Z.comap τ := fun z hz => by
    rw [Subgroup.mem_comap, hτZ z hz]
    exact hz
  let τ' : C ⧸ Z →* C ⧸ Z := QuotientGroup.map Z Z τ hle
  have hinv : Function.Involutive τ' := fun q => by
    refine QuotientGroup.induction_on q fun c => ?_
    simp only [τ', QuotientGroup.map_mk, hτ]
  have hfpf : MonoidHom.FixedPointFree τ' := by
    intro q
    refine QuotientGroup.induction_on q fun c => ?_
    intro hq
    simp only [τ', QuotientGroup.map_mk] at hq
    obtain ⟨z, hz⟩ : ∃ z : C, τ c = c * z := ⟨c⁻¹ * τ c, by group⟩
    have hzZ : z ∈ Z := by
      have h1 : c⁻¹ * τ c ∈ Z := QuotientGroup.eq.1 hq.symm
      rwa [hz, inv_mul_cancel_left] at h1
    have h3 : c * (z * z) = c := by
      calc c * (z * z) = (c * z) * z := by group
        _ = τ c * τ z := by rw [← hz, hτZ z hzZ]
        _ = τ (c * z) := (map_mul τ c z).symm
        _ = τ (τ c) := by rw [← hz]
        _ = c := hτ c
    have hz1 : z = 1 := hZ z hzZ (mul_left_cancel (h3.trans (mul_one c).symm))
    have hc : τ c = c := by rw [hz, hz1, mul_one]
    exact (QuotientGroup.eq_one_iff c).2 (hfix c hc)
  have hcomm := hfpf.commute_all_of_involutive hinv (a : C ⧸ Z) (b : C ⧸ Z)
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm.eq]
  group

theorem commutator_mem_zpowers_of_fixed {H : Type*} [Group H] [Finite H] (σ : MulAut H)
    (hσ : σ * σ = 1) {y : H} (hy : Odd (orderOf y)) (hσy : σ y = y)
    (hC : ∀ x : H, σ x = x → x * y = y * x → x ∈ zpowers y) {a b : H}
    (ha : a * y = y * a) (hb : b * y = y * b) : a * b * a⁻¹ * b⁻¹ ∈ zpowers y := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut H => f x) hσ
    simpa using this
  have hσC : ∀ x : H, x * y = y * x → σ x * y = y * σ x := fun x hx => by
    have := congrArg σ hx
    rwa [map_mul, map_mul, hσy] at this
  let C : Subgroup H := centralizer ({y} : Set H)
  have hmemC : ∀ x : H, x ∈ C ↔ x * y = y * x := fun x => mem_centralizer_singleton_iff
  let τ : C →* C :=
    { toFun := fun c => ⟨σ (c : H), (hmemC _).2 (hσC c ((hmemC c).1 c.2))⟩
      map_one' := Subtype.ext (show σ (1 : H) = 1 from map_one σ)
      map_mul' := fun a b =>
        Subtype.ext (show σ ((a : H) * b) = σ (a : H) * σ (b : H) from map_mul σ (a : H) (b : H)) }
  let Z : Subgroup C := (zpowers y).subgroupOf C
  haveI : Z.Normal := ⟨fun n hn g => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hn)
    have hg : Commute (g : H) y := (hmemC g).1 g.2
    have hgn : Commute (g : H) (n : H) := by
      rw [← hk]
      exact hg.zpow_right k
    refine Subgroup.mem_subgroupOf.2 ?_
    have h : ((g * n * g⁻¹ : C) : H) = n := mul_inv_eq_iff_eq_mul.2 hgn.eq
    rw [h]
    exact Subgroup.mem_subgroupOf.1 hn⟩
  have key := commutator_mem_of_involutive Z τ (fun c => Subtype.ext (hσσ c))
    (fun z hz => by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hz)
      refine Subtype.ext ?_
      change σ z = z
      rw [← hk, map_zpow, hσy])
    (fun z hz hzz => by
      have hz' : (z : H) ∈ zpowers y := Subgroup.mem_subgroupOf.1 hz
      have h1 : orderOf (z : H) ∣ orderOf y := orderOf_dvd_of_mem_zpowers hz'
      have h2 : orderOf (z : H) ∣ 2 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [pow_two]
        exact congrArg Subtype.val hzz
      have h3 : orderOf (z : H) ∣ Nat.gcd (orderOf y) 2 := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one hy.coprime_two_right, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact Subtype.ext h3)
    (fun c hc => Subgroup.mem_subgroupOf.2
      (hC c (congrArg Subtype.val hc) ((hmemC c).1 c.2)))
    ⟨a, (hmemC a).2 ha⟩ ⟨b, (hmemC b).2 hb⟩
  exact Subgroup.mem_subgroupOf.1 key

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let T : Subgroup G :=
    { carrier := {n | ∃ a ∈ A, ∃ b ∈ B, a * b = n}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        have hc := h a₂ ha₂ b₁ hb₁
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [hc]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc := h a ha b hb
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [hc] }
  have hsup : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hsup hg

theorem nonempty_mulEquiv_gl_of_psl_two {n : ℕ} {X : Type} [Group X]
    (hX : CFSG.Open.StatedClassicalModel X .PSL n 2 1) :
    Nonempty (X ≃* GL (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK2 : Nat.card K = 2 := by simpa using hK
  letI : Fintype K := Fintype.ofFinite K
  let f : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, hK2, ZMod.card])
  have h1 := CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2 (Fin n)
  have h2 := CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK2 n
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
    (by rw [h1, Subgroup.bot_subgroupOf])).trans (QuotientGroup.quotientBot.trans
      ((MulEquiv.subgroupCongr h2).trans (Subgroup.topEquiv.trans
        (Units.mapEquiv (RingEquiv.mapMatrix f).toMulEquiv)))))⟩

theorem false_of_gl52_fix_seven (σ : MulAut (GL (Fin 5) (ZMod 2))) (hσ : σ * σ = 1)
    {y : GL (Fin 5) (ZMod 2)} (hy : orderOf y = 7) (hσy : σ y = y)
    (hC : ∀ x : GL (Fin 5) (ZMod 2), σ x = x → x * y = y * x → x ∈ zpowers y) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := CFSG.GroupTheory.GL52.exists_sylow_eq_of_card (H := zpowers y)
    (by rw [Nat.card_zpowers, hy]) CFSG.GroupTheory.GL52.syl7_card_sylow
  obtain ⟨-, X, Y, ⟨hXY, hinf, hcomm⟩, ⟨eX⟩, -, -⟩ := CFSG.GroupTheory.GL52.syl7_structure Q
  have hyN : y ∈ Subgroup.normalizer (Q : Set (GL (Fin 5) (ZMod 2))) :=
    Subgroup.le_normalizer (H := (Q : Subgroup (GL (Fin 5) (ZMod 2)))) (by
      rw [hQ]
      exact mem_zpowers y)
  obtain ⟨x, hx, w, hw, hxw⟩ := exists_mul_of_mem_sup hcomm (hXY ▸ hyN)
  have hcardX : Nat.card X = 6 := by
    rw [Nat.card_congr eX.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hx6 : x ^ 6 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
    rw [hcardX] at h
    exact congrArg Subtype.val h
  have hx7 : x ^ 7 = 1 := by
    have h7 : (x * w) ^ 7 = 1 := by
      rw [hxw, ← hy]
      exact pow_orderOf_eq_one y
    rw [(show Commute x w from hcomm x hx w hw).mul_pow] at h7
    have hmem : x ^ 7 ∈ X ⊓ Y := ⟨X.pow_mem hx 7, by
      rw [eq_inv_of_mul_eq_one_left h7]
      exact Y.inv_mem (Y.pow_mem hw 7)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hx1 : x = 1 := by
    calc x = x ^ 7 * (x ^ 6)⁻¹ := by group
      _ = 1 := by rw [hx7, hx6]; simp
  have hyY : y ∈ Y := by
    rw [← hxw, hx1, one_mul]
    exact hw
  have hzY : zpowers y ≤ Y := (zpowers_le).2 hyY
  obtain ⟨a, b, hab⟩ : ∃ a b : X, a * b ≠ b * a := by
    refine ⟨eX.symm (Equiv.swap 0 1), eX.symm (Equiv.swap 1 2), fun h => ?_⟩
    have := congrArg eX h
    simp only [map_mul, MulEquiv.apply_symm_apply] at this
    revert this
    decide
  have hcom := commutator_mem_zpowers_of_fixed σ hσ (y := y) ⟨3, by omega⟩ hσy hC
    (hcomm a a.2 y hyY) (hcomm b b.2 y hyY)
  have hmem : (a : GL (Fin 5) (ZMod 2)) * b * (a : GL (Fin 5) (ZMod 2))⁻¹ *
      (b : GL (Fin 5) (ZMod 2))⁻¹ ∈ X ⊓ Y :=
    ⟨X.mul_mem (X.mul_mem (X.mul_mem a.2 b.2) (X.inv_mem a.2)) (X.inv_mem b.2), hzY hcom⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact hab (Subtype.ext (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hmem)))

theorem false_of_psl52_fix_seven {X : Type} [Group X]
    (hX : CFSG.Open.StatedClassicalModel X .PSL 5 2 1) (σ : MulAut X) (hσ : σ * σ = 1) {y : X}
    (hy : orderOf y = 7) (hσy : σ y = y)
    (hC : ∀ x : X, σ x = x → x * y = y * x → x ∈ Subgroup.zpowers y) : False := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_gl_of_psl_two hX
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hσ
    simpa using this
  refine false_of_gl52_fix_seven (e'.symm.trans (σ.trans e')) ?_ (y := e' y) ?_ ?_ ?_
  · refine MulEquiv.ext fun g => ?_
    change e' (σ (e'.symm (e' (σ (e'.symm g))))) = g
    rw [MulEquiv.symm_apply_apply, hσσ, MulEquiv.apply_symm_apply]
  · rw [MulEquiv.orderOf_eq]
    exact hy
  · change e' (σ (e'.symm (e' y))) = e' y
    rw [MulEquiv.symm_apply_apply, hσy]
  · intro x hx hxy
    change e' (σ (e'.symm x)) = x at hx
    have hx' : σ (e'.symm x) = e'.symm x := by
      have := congrArg e'.symm hx
      simpa using this
    have hxy' : e'.symm x * y = y * e'.symm x := by
      have := congrArg e'.symm hxy
      simpa using this
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hC _ hx' hxy')
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, hk, MulEquiv.apply_symm_apply]

end CFSG.GF2Type.Smith1979.Case2
