module

public import CFSG.LargeExtraspecial.S10EightG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

section Groups

variable {X : Type*} [Group X]

theorem map_conj_le_normalizer {H H' : Subgroup X} (h : H' ≤ normalizer (H : Set X)) (g : X) :
    H'.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  intro x hx
  rw [mem_map_conj_iff] at hx
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : g⁻¹ * (x * y * x⁻¹) * g =
      (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.mp (h hx) _

theorem map_conj_map_conj (H : Subgroup X) (g g' : X) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g').toMonoidHom =
      H.map (MulAut.conj (g' * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (H : Subgroup X) : H.map (MulAut.conj (1 : X)).toMonoidHom = H := by
  ext x
  rw [mem_map_conj_iff]
  simp

theorem map_conj_eq_self {H : Subgroup X} {g : X} (hg : ∀ h ∈ H, g * h = h * g) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_map_conj_iff]
  constructor
  · intro hx
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e, hg _ hx]
    simpa using hx
  · intro hx
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [hg x hx]
        _ = x := by group
    rw [e]
    exact hx

theorem exists_mem_normalizer_not_mem_of_lt [Finite X] {p : ℕ} [Fact p.Prime]
    {P S₀ : Subgroup X} (hP : IsPGroup p P) (hlt : S₀ < P) :
    ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set X) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set X)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem exists_conj_mutual [Finite X] {p : ℕ} [Fact p.Prime] {A K : Subgroup X}
    (hA : IsPGroup p A) (hAK : A ≤ K) {m : X} (hm : m ∈ K)
    (hle : A.map (MulAut.conj m).toMonoidHom ≤ normalizer (A : Set X))
    (hne : A.map (MulAut.conj m).toMonoidHom ≠ A) :
    ∃ m' ∈ K, A.map (MulAut.conj m').toMonoidHom ≠ A ∧
      A.map (MulAut.conj m').toMonoidHom ≤ normalizer (A : Set X) ∧
      A ≤ normalizer ((A.map (MulAut.conj m').toMonoidHom : Subgroup X) : Set X) := by
  set C := A.map (MulAut.conj m).toMonoidHom with hC
  have hCp : IsPGroup p C := hA.map _
  have hPp : IsPGroup p (A ⊔ C : Subgroup X) := IsPGroup.to_sup_of_normal_left' hA hCp hle
  have hCK : C ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hm (hAK ha)) (inv_mem hm)
  by_cases hN : A ⊔ C ≤ normalizer (C : Set X)
  · exact ⟨m, hm, hne, hle, le_sup_left.trans hN⟩
  set N₁ := (A ⊔ C) ⊓ normalizer (C : Set X) with hN₁
  have hlt : N₁ < A ⊔ C := lt_of_le_of_ne inf_le_left fun h => hN (h ▸ inf_le_right)
  obtain ⟨y, hyP, hyN₁, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hPp hlt
  have hyK : y ∈ K := sup_le hAK hCK hyP
  have hCN₁ : C ≤ N₁ := le_inf le_sup_right le_normalizer
  have hN₁y : N₁.map (MulAut.conj y).toMonoidHom = N₁ := by
    ext x
    rw [mem_map_conj_iff]
    constructor
    · intro hx
      have := (mem_normalizer_iff.mp hyN (y⁻¹ * x * y)).mp hx
      simpa [mul_assoc] using this
    · intro hx
      have := (mem_normalizer_iff.mp (inv_mem hyN) x).mp hx
      simpa [mul_assoc] using this
  set C' := C.map (MulAut.conj y).toMonoidHom with hC'
  have hC'N : C' ≤ normalizer (C : Set X) :=
    (map_mono hCN₁).trans (hN₁y.le.trans inf_le_right)
  have hCN' : C ≤ normalizer (C' : Set X) := by
    have h1 := map_conj_le_normalizer (inf_le_right : N₁ ≤ normalizer (C : Set X)) y
    rw [hN₁y] at h1
    exact hCN₁.trans h1
  have hC'ne : C' ≠ C := by
    intro h
    apply hyN₁
    refine Subgroup.mem_inf.mpr ⟨hyP, ?_⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨x', hx', he⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      have : x' = x := by
        have := congrArg (fun w => y⁻¹ * w * y) he
        simpa [mul_assoc] using this
      rw [← this]
      exact hx'
  refine ⟨m⁻¹ * y * m, mul_mem (mul_mem (inv_mem hm) hyK) hm, ?_, ?_, ?_⟩
  · intro h
    apply hC'ne
    have e1 : C' = (A.map (MulAut.conj (m⁻¹ * y * m)).toMonoidHom).map
        (MulAut.conj m).toMonoidHom := by
      rw [hC', hC, map_conj_map_conj, map_conj_map_conj]
      congr 2
      group
    rw [e1, h]
  · have h1 := map_conj_le_normalizer hC'N m⁻¹
    rw [hC', hC, map_conj_map_conj, map_conj_map_conj, map_conj_map_conj] at h1
    rw [show m⁻¹ * m = 1 by group, map_conj_one] at h1
    exact h1
  · have h1 := map_conj_le_normalizer hCN' m⁻¹
    rw [hC', hC, map_conj_map_conj, map_conj_map_conj, map_conj_map_conj] at h1
    rw [show m⁻¹ * m = 1 by group, map_conj_one] at h1
    exact h1

end Groups

theorem perm_three_cube_of_comm : ∀ σ ρ : Equiv.Perm (Fin 3), ρ ^ 3 = 1 → ρ ≠ 1 →
    σ * ρ = ρ * σ → σ ^ 3 = 1 := by
  decide +kernel

theorem eq_τ₁_of_stab_Γ₁ : ∀ γ : Gm, act γ E00 = E00 → γ.2 = 1 → γ ≠ 1 → γ = τ₁ := by
  decide +kernel

theorem eq_τ₁_of_conj : ∀ γ : Gm, γ.2 = 1 → γ * γ = 1 → γ ≠ 1 → γ * τ₁ * γ⁻¹ = τ₁ →
    γ = τ₁ := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem fix_τ₁_cases : ∀ γ σ : Gm, act τ₁ (act γ E00) = act γ E00 → σ.1 = 1 → σ ^ 3 = 1 →
    σ ≠ 1 → act γ E00 = E00 ∨ act γ E00 = act σ E00 ∨ act γ E00 = act (σ * σ) E00 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace DirDec

variable {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
include D

theorem mem_Xb_of_mul_self {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆) (hd1 : d ≠ 1) {c : S.O}
    (hc : c ∈ Rbar S g t) (hcc : c * c = 1) (hcd : c * d = d * c) : c ∈ Xb := by
  have hdY := ((D.mem_commutator_iff).mp hd).1
  have hd3 := ((D.mem_commutator_iff).mp hd).2
  obtain ⟨x, hx, u, hu, rfl⟩ := D.exists_mul hc
  have hxu : x * u = u * x := D.comm x hx u hu
  have hxd : x * d = d * x := D.comm x hx d hdY
  have hud : u * d = d * u := by
    have h1 : x * (u * d) = x * (d * u) := by
      calc x * (u * d) = x * u * d := by group
        _ = d * (x * u) := hcd
        _ = (d * x) * u := by group
        _ = (x * d) * u := by rw [hxd]
        _ = x * (d * u) := by group
    exact mul_left_cancel h1
  obtain ⟨e⟩ := D.iso
  have hu3 : u ^ 3 = 1 := by
    have h := perm_three_cube_of_comm (e ⟨u, hu⟩) (e ⟨d, hdY⟩)
      (by rw [← map_pow]; rw [show (⟨d, hdY⟩ : Yb) ^ 3 = 1 from Subtype.ext hd3, map_one])
      (fun h => hd1 (by
        have := e.injective (h.trans (map_one e).symm)
        exact congrArg Subtype.val this))
      (by rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hud)
    rw [← map_pow] at h
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hu2 : u * u ∈ Xb := by
    have e1 : u * u = (x * x)⁻¹ * ((x * u) * (x * u)) := by
      rw [show (x * u) * (x * u) = x * x * (u * u) by
        calc (x * u) * (x * u) = x * (u * x) * u := by group
          _ = x * (x * u) * u := by rw [hxu]
          _ = x * x * (u * u) := by group]
      group
    rw [e1, hcc, mul_one]
    exact inv_mem (mul_mem hx hx)
  have hu1 : u * u = 1 := by
    have : u * u ∈ Xb ⊓ Yb := ⟨hu2, mul_mem hu hu⟩
    rw [D.inf] at this
    exact (Subgroup.mem_bot).mp this
  have hu' : u = 1 := by
    calc u = u ^ 3 * (u * u)⁻¹ := by group
      _ = 1 := by rw [hu3, hu1]; group
  rw [hu', mul_one]
  exact hx

end DirDec

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem commute_of_map_eq {k : S.M} (hY : ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆) {d : S.O}
    (hd : d ∈ ⁅Yb, Yb⁆) {c : S.O} (hc : c ∈ (S.Lbar g ⊓ Xb).map (cK S k)) : c * d = d * c := by
  have hdk : d ∈ ⁅Yb, Yb⁆.map (cK S k) := by rw [hY]; exact hd
  rw [mem_map_cK_iff] at hc hdk
  have h := D.dec.comm _ hc.2 _ ((D.dec.mem_commutator_iff).mp hdk).1
  calc c * d = S.ρ k * (((S.ρ k)⁻¹ * c * S.ρ k) * ((S.ρ k)⁻¹ * d * S.ρ k)) * (S.ρ k)⁻¹ := by
        group
    _ = S.ρ k * (((S.ρ k)⁻¹ * d * S.ρ k) * ((S.ρ k)⁻¹ * c * S.ρ k)) * (S.ρ k)⁻¹ := by rw [h]
    _ = d * c := by group

omit D in
theorem map_le_Lbar_mul (k : S.M) : (S.Lbar g ⊓ Xb).map (cK S k) ≤ S.Lbar ((k : G) * g) := by
  rw [Lbar_mul S k g]
  exact map_mono inf_le_left

theorem map_eq_of_Lbar_eq (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k k₁ : S.M}
    (hkk : S.Lbar ((k : G) * g) = S.Lbar ((k₁ : G) * g)) :
    (S.Lbar g ⊓ Xb).map (cK S k) = (S.Lbar g ⊓ Xb).map (cK S k₁) := by
  set k₂ := k₁⁻¹ * k with hk₂
  have hL : S.Lbar ((k₂ : G) * g) = S.Lbar g := by
    have h1 : ((k₂ : S.M) : G) * g = ((k₁⁻¹ : S.M) : G) * ((k : G) * g) := by
      rw [hk₂, Subgroup.coe_mul, mul_assoc]
    have h2 : g = ((k₁⁻¹ : S.M) : G) * ((k₁ : G) * g) := by
      rw [← mul_assoc, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, one_mul]
    rw [h1, Lbar_mul S k₁⁻¹, hkk, ← Lbar_mul S k₁⁻¹, ← h2]
  have h0 := map_le_Lbar_mul (g := g) (Xb := Xb) k₂
  rw [hL] at h0
  have h2 := D.timmesfeld_10_8_two hCE hP h0
  have hk : k = k₁ * k₂ := by rw [hk₂]; group
  rw [hk]
  change (S.Lbar g ⊓ Xb).map (MulAut.conj (S.ρ (k₁ * k₂))).toMonoidHom = _
  rw [map_mul, ← map_conj_map_conj]
  change ((S.Lbar g ⊓ Xb).map (cK S k₂)).map (cK S k₁) = _
  rw [h2]

theorem eq_of_mem_inf_lin {k : S.M} (hY : ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆)
    {τ : S.O} (hτk : τ ∈ (S.Lbar g ⊓ Xb).map (cK S k))
    (hR : Rbar S g τ = (S.Lbar g ⊓ Xb) ⊔ Yb) :
    (S.Lbar g ⊓ Xb).map (cK S k) = S.Lbar g ⊓ Xb := by
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hτL := map_le_Lbar_mul (g := g) (Xb := Xb) k hτk
  have hle : (S.Lbar g ⊓ Xb).map (cK S k) ≤ S.Lbar g ⊓ Xb := by
    intro c hc
    have hcL := map_le_Lbar_mul (g := g) (Xb := Xb) k hc
    have hcR : c ∈ (S.Lbar g ⊓ Xb) ⊔ Yb := hR ▸ Lbar_mul_le_Rbar hτL hcL
    have hcR' : c ∈ Rbar S g t := sup_le (inf_le_right.trans D.dec.le_Rbar_left)
      D.dec.le_Rbar_right hcR
    have hcc : c * c = 1 := S4.mul_self_of_mem_Lbar S (conj_mem_QG' S k.2 X.haQ) hcL
    have hcX := D.dec.mem_Xb_of_mul_self hdY' hd1 hcR' hcc (D.commute_of_map_eq hY hdY' hc)
    obtain ⟨e, he, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_commute (A := S.Lbar g ⊓ Xb)
      (B := Yb) (fun a ha b hb => D.dec.comm a ha.2 b hb) hcR
    have hu1 : u = 1 := by
      have heX : e ∈ Xb := (Subgroup.mem_inf.mp he).2
      have h1 : e⁻¹ * (e * u) ∈ Xb := mul_mem (inv_mem heX) hcX
      have : u ∈ Xb ⊓ Yb := ⟨by simpa using h1, hu⟩
      rw [D.dec.inf] at this
      exact (Subgroup.mem_bot).mp this
    rw [hu1, mul_one]
    exact he
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (cK_injective k)).symm.le

end Dec108

end CFSG.LargeExtraspecial.S10
