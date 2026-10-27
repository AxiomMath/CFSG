module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Std
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Extr
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2ModZ

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

namespace Psi

variable {G : Type} [Group G] {H : Type} [Group H] {k : ℕ} {A : Subgroup G}

structure Data (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))) (z : G) (δ : sylowT →* G)
    (vec : H → Fin 3 → ZMod (2 ^ k)) (sv : H → ZMod 2) (tv : H → sylowT)
    (us : ZMod 2 → ZMod (2 ^ k)) (dm : sylowT → Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    Prop where
  vec_mul : ∀ p q, vec (p * q) = vec p + us (sv p) • (dm (tv p) *ᵥ vec q)
  sv_mul : ∀ p q, sv (p * q) = sv p + sv q
  tv_mul : ∀ p q, tv (p * q) = tv p * tv q
  vec_one : vec 1 = 0
  eq_one : ∀ p, vec p = 0 → sv p = 0 → tv p = 1 → p = 1
  us_zero : us 0 = 1
  z_sq : z * z = 1
  conj_z : ∀ x, z * el ι x * z⁻¹ = el ι (us 1 • x)
  conj_δ : ∀ t x, δ t * el ι x * (δ t)⁻¹ = el ι (dm t *ᵥ x)
  comm : ∀ t, δ t * z = z * δ t
  inter : ∀ (s : ZMod 2) t, z ^ s.val * δ t ∈ A → s = 0 ∧ t = 1

variable {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))} {z : G} {δ : sylowT →* G}
  {vec : H → Fin 3 → ZMod (2 ^ k)} {sv : H → ZMod 2} {tv : H → sylowT}
  {us : ZMod 2 → ZMod (2 ^ k)} {dm : sylowT → Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))}

@[expose] def psiFun (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))) (z : G)
    (δ : sylowT →* G) (vec : H → Fin 3 → ZMod (2 ^ k)) (sv : H → ZMod 2) (tv : H → sylowT)
    (p : H) : G :=
  el ι (vec p) * (z ^ (sv p).val * δ (tv p))

variable (hd : Data ι z δ vec sv tv us dm)
include hd

theorem Data.zpow_val_mul (s s' : ZMod 2) : z ^ s.val * z ^ s'.val = z ^ (s + s').val := by
  rcases zmod2_eq_zero_or_one s with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one s' with rfl | rfl
  · show z ^ 0 * z ^ 0 = z ^ 0
    rw [pow_zero, one_mul]
  · show z ^ 0 * z ^ 1 = z ^ 1
    rw [pow_zero, one_mul]
  · show z ^ 1 * z ^ 0 = z ^ 1
    rw [pow_zero, mul_one]
  · show z ^ 1 * z ^ 1 = z ^ 0
    rw [pow_one, hd.z_sq, pow_zero]

theorem Data.zpow_mul_el (s : ZMod 2) (x : Fin 3 → ZMod (2 ^ k)) :
    z ^ s.val * el ι x = el ι (us s • x) * z ^ s.val := by
  rcases zmod2_eq_zero_or_one s with rfl | rfl
  · show z ^ 0 * el ι x = el ι (us 0 • x) * z ^ 0
    rw [hd.us_zero, one_smul, pow_zero, one_mul, mul_one]
  · show z ^ 1 * el ι x = el ι (us 1 • x) * z ^ 1
    rw [pow_one, ← hd.conj_z, inv_mul_cancel_right]

theorem Data.δ_mul_el (t : sylowT) (x : Fin 3 → ZMod (2 ^ k)) :
    δ t * el ι x = el ι (dm t *ᵥ x) * δ t := by
  rw [← hd.conj_δ, inv_mul_cancel_right]

theorem Data.δ_mul_zpow (t : sylowT) (j : ℕ) : δ t * z ^ j = z ^ j * δ t :=
  (Commute.pow_right (hd.comm t : Commute (δ t) z) j).eq

theorem Data.wPart_mul_el (s : ZMod 2) (t : sylowT) (x : Fin 3 → ZMod (2 ^ k)) :
    z ^ s.val * δ t * el ι x = el ι (us s • (dm t *ᵥ x)) * (z ^ s.val * δ t) := by
  rw [mul_assoc, hd.δ_mul_el, ← mul_assoc, hd.zpow_mul_el, mul_assoc]

theorem Data.psiFun_mul (p q : H) :
    psiFun ι z δ vec sv tv (p * q) = psiFun ι z δ vec sv tv p * psiFun ι z δ vec sv tv q := by
  unfold psiFun
  rw [hd.vec_mul, hd.sv_mul, hd.tv_mul, el_add, map_mul, ← hd.zpow_val_mul]
  have e := hd.wPart_mul_el (sv p) (tv p) (vec q)
  calc el ι (vec p) * el ι (us (sv p) • (dm (tv p) *ᵥ vec q)) *
        (z ^ (sv p).val * z ^ (sv q).val * (δ (tv p) * δ (tv q)))
      = el ι (vec p) * (el ι (us (sv p) • (dm (tv p) *ᵥ vec q)) * (z ^ (sv p).val * δ (tv p))) *
          (z ^ (sv q).val * δ (tv q)) := by
        rw [show z ^ (sv p).val * z ^ (sv q).val * (δ (tv p) * δ (tv q)) =
          z ^ (sv p).val * (δ (tv p) * z ^ (sv q).val) * δ (tv q) by
            rw [hd.δ_mul_zpow]; group]
        group
    _ = el ι (vec p) * (z ^ (sv p).val * δ (tv p)) *
          (el ι (vec q) * (z ^ (sv q).val * δ (tv q))) := by
        rw [← e]
        group

@[expose] def psi : H →* G where
  toFun := psiFun ι z δ vec sv tv
  map_one' := by
    have h1 : tv 1 = 1 := by
      have := hd.tv_mul 1 1
      rw [mul_one] at this
      exact left_eq_mul.1 this
    have h2 : sv 1 = 0 := by
      have := hd.sv_mul 1 1
      rw [mul_one] at this
      exact left_eq_add.1 this
    show el ι (vec 1) * (z ^ (sv 1).val * δ (tv 1)) = 1
    rw [hd.vec_one, h1, h2, el_zero, map_one, ZMod.val_zero, pow_zero, one_mul, one_mul]
  map_mul' := hd.psiFun_mul

theorem psi_apply (p : H) : psi hd p = el ι (vec p) * (z ^ (sv p).val * δ (tv p)) := rfl

theorem psi_injective : Function.Injective (psi hd) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  rw [psi_apply] at hp
  have h1 : z ^ (sv p).val * δ (tv p) ∈ A := by
    rw [eq_inv_of_mul_eq_one_right hp]
    exact inv_mem (el_mem ι _)
  obtain ⟨hs, ht⟩ := hd.inter _ _ h1
  rw [hs, ht, map_one, mul_one, ZMod.val_zero, pow_zero, mul_one, el_eq_one_iff] at hp
  exact hd.eq_one p hp hs ht

theorem mem_A_iff (p : H) : psi hd p ∈ A ↔ sv p = 0 ∧ tv p = 1 := by
  rw [psi_apply]
  constructor
  · intro hp
    refine hd.inter _ _ ?_
    rw [show z ^ (sv p).val * δ (tv p) = (el ι (vec p))⁻¹ *
      (el ι (vec p) * (z ^ (sv p).val * δ (tv p))) by group]
    exact mul_mem (inv_mem (el_mem ι _)) hp
  · rintro ⟨hs, ht⟩
    rw [hs, ht, map_one, mul_one, ZMod.val_zero, pow_zero, mul_one]
    exact el_mem ι _

theorem psi_of_mem (p : H) (hs : sv p = 0) (ht : tv p = 1) : psi hd p = el ι (vec p) := by
  rw [psi_apply, hs, ht, map_one, mul_one, ZMod.val_zero, pow_zero, mul_one]

theorem mem_Mm_iff (hz : z ∉ Mm A δ.range) (p : H) : psi hd p ∈ Mm A δ.range ↔ sv p = 0 := by
  rw [psi_apply]
  constructor
  · intro hp
    rcases zmod2_eq_zero_or_one (sv p) with h0 | h1
    · exact h0
    · exfalso
      apply hz
      rw [h1, show (1 : ZMod 2).val = 1 from rfl, pow_one] at hp
      have h2 := mul_mem (mul_mem (inv_mem (mem_sup_left (T := δ.range) (el_mem ι (vec p)))) hp)
        (inv_mem (mem_sup_right (S := A) (MonoidHom.mem_range.2 ⟨tv p, rfl⟩)))
      rwa [show (el ι (vec p))⁻¹ * (el ι (vec p) * (z * δ (tv p))) * (δ (tv p))⁻¹ = z by group]
        at h2
  · intro hs
    rw [hs, ZMod.val_zero, pow_zero, one_mul]
    exact mul_mem (mem_sup_left (el_mem ι _)) (mem_sup_right ⟨tv p, rfl⟩)

theorem psi_t (p : H) (hv : vec p = 0) (hs : sv p = 1) (ht : tv p = 1) : psi hd p = z := by
  rw [psi_apply, hv, hs, ht, el_zero, map_one, one_mul, mul_one, show (1 : ZMod 2).val = 1 from rfl,
    pow_one]

theorem mem_E_iff {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {hn : 8 ≤ n}
    (hι : ECoords θ hn k A ι) (p : H) :
    psi hd p ∈ E θ hn ↔ (sv p = 0 ∧ tv p = 1) ∧ 2 • vec p = 0 := by
  constructor
  · intro hp
    have hA := (mem_A_iff hd p).1 (hι.E_le hp)
    refine ⟨hA, ?_⟩
    have h2 := sq_eq_one_of_mem_E θ hn hp
    rwa [psi_of_mem hd p hA.1 hA.2, ← el_nsmul, el_eq_one_iff] at h2
  · rintro ⟨⟨hs, ht⟩, h2⟩
    have hA : psi hd p ∈ A := (mem_A_iff hd p).2 ⟨hs, ht⟩
    rw [hι.mem_E_iff_sq_eq_one hA, psi_of_mem hd p hs ht, ← el_nsmul, h2, el_zero]

theorem psi_mem_Tm (p : H) : psi hd p ∈ Tm A z δ.range := by
  rw [psi_apply]
  exact mul_mem (TermData.A_le_Tm (el_mem ι _)) (mul_mem (pow_mem TermData.z_mem_Tm _)
    (TermData.D_le_Tm ⟨tv p, rfl⟩))

theorem range_psi [Finite G] [Finite H] (hcard : Nat.card H = Nat.card (Tm A z δ.range)) :
    (psi hd).range = Tm A z δ.range := by
  refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨p, hp⟩ => hp ▸ psi_mem_Tm hd p) ?_
  rw [← hcard, MonoidHom.range_eq_map, card_map_of_injective (psi_injective hd), Subgroup.card_top]

end Psi

section Transport

variable {G : Type} [Group G] {H : Type} [Group H]

theorem natCard_centralizer_psi {Ψ : H →* G} (hinj : Function.Injective Ψ) (x : H) :
    Nat.card (centralizer ({x} : Set H)) =
      Nat.card (Ψ.range ⊓ centralizer ({Ψ x} : Set G) : Subgroup G) := by
  have e : (centralizer ({x} : Set H)).map Ψ = Ψ.range ⊓ centralizer ({Ψ x} : Set G) := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      have hy'' : y' ∈ centralizer ({x} : Set H) := hy'
      refine Subgroup.mem_inf.2 ⟨⟨y', rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff] at hy'' ⊢
      rw [← map_mul, ← map_mul, hy'']
    · intro hy
      obtain ⟨⟨y', rfl⟩, hy⟩ := Subgroup.mem_inf.1 hy
      refine ⟨y', ?_, rfl⟩
      show y' ∈ centralizer ({x} : Set H)
      rw [mem_centralizer_singleton_iff] at hy ⊢
      apply hinj
      rw [map_mul, map_mul, hy]
  rw [← e, card_map_of_injective hinj]

theorem natCard_inf_centralizer_conj {T : Subgroup G} {y : G} (hy : y ∈ normalizer (T : Set G))
    (x : G) : Nat.card (T ⊓ centralizer ({y * x * y⁻¹} : Set G) : Subgroup G) =
      Nat.card (T ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have hy' : y⁻¹ ∈ normalizer (T : Set G) := inv_mem hy
  refine Nat.card_congr ⟨fun t => ⟨y⁻¹ * t * y, ?_⟩, fun t => ⟨y * t * y⁻¹, ?_⟩, fun t => ?_,
    fun t => ?_⟩
  · obtain ⟨htT, htC⟩ := Subgroup.mem_inf.1 t.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 hy' t).1 htT
      rwa [inv_inv] at this
    · have ht := mem_centralizer_singleton_iff.1 htC
      rw [mem_centralizer_singleton_iff]
      calc y⁻¹ * ↑t * y * x = y⁻¹ * (↑t * (y * x * y⁻¹)) * y := by group
        _ = y⁻¹ * (y * x * y⁻¹ * ↑t) * y := by rw [ht]
        _ = x * (y⁻¹ * ↑t * y) := by group
  · obtain ⟨htT, htC⟩ := Subgroup.mem_inf.1 t.2
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hy t).1 htT, ?_⟩
    have ht := mem_centralizer_singleton_iff.1 htC
    rw [mem_centralizer_singleton_iff]
    calc y * ↑t * y⁻¹ * (y * x * y⁻¹) = y * (↑t * x) * y⁻¹ := by group
      _ = y * (x * ↑t) * y⁻¹ := by rw [ht]
      _ = y * x * y⁻¹ * (y * ↑t * y⁻¹) := by group
  · exact Subtype.ext (by group)
  · exact Subtype.ext (by group)

@[expose] def CondE (T : Subgroup G) (x : G) : Prop :=
  x = 1 ∨ (x * x = 1 ∧ (∃ g ∈ T, g * g = x) ∧
    2 ^ 8 ≤ Nat.card (T ⊓ centralizer ({x} : Set G) : Subgroup G))

theorem CondE.conj {T : Subgroup G} {y x : G} (hy : y ∈ normalizer (T : Set G))
    (hx : CondE T x) : CondE T (y * x * y⁻¹) := by
  rcases hx with rfl | ⟨hx2, ⟨g, hg, hgx⟩, hc⟩
  · left
    group
  · right
    refine ⟨by rw [show y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ by group, hx2]; group,
      ⟨y * g * y⁻¹, (mem_normalizer_iff.1 hy g).1 hg, by rw [← hgx]; group⟩, ?_⟩
    rw [natCard_inf_centralizer_conj hy]
    exact hc

theorem condE_psi_iff {Ψ : H →* G} (hinj : Function.Injective Ψ) {T : Subgroup G}
    (hT : Ψ.range = T) (x : H) :
    CondE T (Ψ x) ↔ x = 1 ∨ (x * x = 1 ∧ (∃ g : H, g * g = x) ∧
      2 ^ 8 ≤ Nat.card (centralizer ({x} : Set H))) := by
  rw [CondE, natCard_centralizer_psi hinj, hT]
  have h1 : Ψ x = 1 ↔ x = 1 := by rw [← map_one Ψ, hinj.eq_iff]
  have h2 : Ψ x * Ψ x = 1 ↔ x * x = 1 := by rw [← map_mul, ← map_one Ψ, hinj.eq_iff]
  have h3 : (∃ g ∈ T, g * g = Ψ x) ↔ ∃ g : H, g * g = x := by
    constructor
    · rintro ⟨g, hg, hgx⟩
      rw [← hT] at hg
      obtain ⟨g', rfl⟩ := hg
      exact ⟨g', hinj (by rw [map_mul, hgx])⟩
    · rintro ⟨g, rfl⟩
      exact ⟨Ψ g, hT ▸ ⟨g, rfl⟩, by rw [map_mul]⟩
  rw [h1, h2, h3]

end Transport

section Models

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {m : ℕ} {A : Subgroup G}

@[expose] noncomputable def kapU (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    sylowT →* G :=
  (ModIso.kap θ hn).comp sylowT.subtype

theorem range_kapU (hn : 8 ≤ n) : (kapU θ hn).range = DU θ hn := by
  rw [kapU, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

theorem kapU_inter (c : Config G L Q n θ z) (h : TermData θ c.hn8 z m A (DU θ c.hn8))
    (s : ZMod 2) (t : sylowT) (hst : z ^ s.val * kapU θ c.hn8 t ∈ A) : s = 0 ∧ t = 1 := by
  have hD : kapU θ c.hn8 t ∈ DU θ c.hn8 := kap_mem_DU θ c.hn8 t
  rcases zmod2_eq_zero_or_one s with rfl | rfl
  · refine ⟨rfl, ?_⟩
    rw [ZMod.val_zero, pow_zero, one_mul] at hst
    have h1 : kapU θ c.hn8 t ∈ A ⊓ DU θ c.hn8 := Subgroup.mem_inf.2 ⟨hst, hD⟩
    rw [h.inf_eq_bot c, mem_bot] at h1
    apply Subtype.ext
    exact ModIso.kap_injective θ c.hn8 (by rw [OneMemClass.coe_one, map_one]; exact h1)
  · exfalso
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one] at hst
    apply h.z_not_mem_Mm c
    have h1 := mul_mem (mem_sup_left (T := DU θ c.hn8) hst) (inv_mem (mem_sup_right hD))
    rwa [mul_inv_cancel_right] at h1

@[expose] def tvOf (a b c : ZMod 2) : sylowT := tripleEquiv (a, b, c)

theorem tvOf_mul (a b c a' b' c' : ZMod 2) :
    tvOf (a + a') (b + b' + a * c') (c + c') = tvOf a b c * tvOf a' b' c' :=
  Subtype.ext (Units.ext (unitri_mul a b c a' b' c').symm)

theorem tvOf_eq_one {a b c : ZMod 2} (h : tvOf a b c = 1) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h1 : tripleEquiv (a, b, c) = tripleEquiv (0, 0, 0) := by
    rw [show tvOf a b c = tripleEquiv (a, b, c) from rfl] at h
    rw [h]
    exact Subtype.ext (Units.ext unitri_zero.symm)
  have h2 := tripleEquiv.injective h1
  simp only [Prod.mk.injEq] at h2
  exact h2

theorem tvOf_zero : tvOf 0 0 0 = 1 := Subtype.ext (Units.ext unitri_zero)

@[expose] def dm4 (t : sylowT) : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  Z4M.dMat (tripleEquiv.symm t).1 (tripleEquiv.symm t).2.1 (tripleEquiv.symm t).2.2

@[expose] def dm8 (t : sylowT) : Matrix (Fin 3) (Fin 3) (ZMod 8) :=
  Z8M.dMat (tripleEquiv.symm t).1 (tripleEquiv.symm t).2.1 (tripleEquiv.symm t).2.2

theorem data_two (c : Config G L Q n θ z)
    (h : LevelDatum θ c.hn8 z 2 A) (ht : Terminal θ c.hn8 A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 2)), ECoords θ c.hn8 2 A ι ∧
      Psi.Data ι z (kapU θ c.hn8) (Z4M.vec : Z4M → Fin 3 → ZMod (2 ^ 2)) Z4M.s
        (fun p => tvOf p.a p.b p.c) (Z4M.uS : ZMod 2 → ZMod (2 ^ 2)) dm4 := by
  obtain ⟨ι, hι, hκ⟩ := exists_termData_std_two c h
  have hD := termData_DU c h ht
  have hzinv : ∀ a ∈ A, z * a * z⁻¹ = a⁻¹ := by
    rcases h.zact with h1 | ⟨h3, -⟩
    · exact h1
    · omega
  refine ⟨ι, hι, ⟨fun p q => ?_, fun p q => rfl, fun p q => (tvOf_mul _ _ _ _ _ _).symm ▸ ?_,
    Z4M.vec_one, fun p hv hs ht => ?_, Z4M.uS_zero, z_mul_self c, fun x => ?_, fun t x => ?_,
    fun t => ?_, kapU_inter c hD⟩⟩
  · rw [Z4M.vec_mul]
    rfl
  · rfl
  · obtain ⟨ha, hb, hc⟩ := tvOf_eq_one ht
    exact Z4M.ext_vec (hv.trans Z4M.vec_one.symm) hs ha hb hc
  · rw [hzinv _ (el_mem ι x), ← el_neg]
    congr 1
    show -x = (-1 : ZMod 4) • x
    rw [neg_one_smul]
  · rw [show t = tripleEquiv (tripleEquiv.symm t) from (tripleEquiv.apply_symm_apply t).symm]
    exact hκ _ _ _ x
  · exact (mem_centralizer_singleton_iff.1
      (L_le_centralizer_z c (ModIso.kap_mem_L θ c.hn8 _)))

theorem exists_unit_three {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 3))} (c : Config G L Q n θ z)
    (h : LevelDatum θ c.hn8 z 3 A) :
    ∃ u : (ZMod 8)ˣ, ((u : ZMod 8) = -1 ∨ (u : ZMod 8) = 3) ∧
      ∀ x, z * el ι x * z⁻¹ = el ι (((u : ZMod 8) : ZMod (2 ^ 3)) • x) := by
  obtain ⟨u, hu, hux⟩ := ZAct.el_conj ι h.zAct
  have hu' : (u : ZMod 8) = -1 ∨ (u : ZMod 8) = 3 := by
    rcases hu with h1 | ⟨-, h1⟩
    · exact Or.inl h1
    · right
      rw [h1]
      decide
  have hsq : ∀ v : ZMod 8, v = -1 ∨ v = 3 → v * v = 1 := by decide
  exact ⟨⟨u, u, hsq u hu', hsq u hu'⟩, hu', hux⟩

theorem data_three
    (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z 3 A) (ht : Terminal θ c.hn8 A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 3)), ECoords θ c.hn8 3 A ι ∧
      ∃ u : (ZMod 8)ˣ, ((u : ZMod 8) = -1 ∨ (u : ZMod 8) = 3) ∧
        Psi.Data ι z (kapU θ c.hn8) (Z8M.vec : Z8M u → Fin 3 → ZMod (2 ^ 3)) Z8M.s
          (fun p => tvOf p.a p.b p.c) (Z8M.uS u : ZMod 2 → ZMod (2 ^ 3)) dm8 := by
  obtain ⟨ι, hι, hκ⟩ := exists_termData_std_three c h
  have hD := termData_DU c h ht
  obtain ⟨u, hu, hux⟩ := exists_unit_three (ι := ι) c h
  refine ⟨ι, hι, u, hu, ⟨fun p q => ?_, fun p q => rfl, fun p q => (tvOf_mul _ _ _ _ _ _).symm ▸ ?_,
    Z8M.vec_one, fun p hv hs ht => ?_, Z8M.uS_zero u, z_mul_self c, fun x => ?_, fun t x => ?_,
    fun t => ?_, kapU_inter c hD⟩⟩
  · rw [Z8M.vec_mul]
    rfl
  · rfl
  · obtain ⟨ha, hb, hc⟩ := tvOf_eq_one ht
    exact Z8M.ext_vec (hv.trans Z8M.vec_one.symm) hs ha hb hc
  · rw [hux x]
    rfl
  · rw [show t = tripleEquiv (tripleEquiv.symm t) from (tripleEquiv.apply_symm_apply t).symm]
    exact hκ _ _ _ x
  · exact (mem_centralizer_singleton_iff.1
      (L_le_centralizer_z c (ModIso.kap_mem_L θ c.hn8 _)))

end Models

section Final

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {A : Subgroup G}

theorem cardN_expo (L : Subgroup G) (n : ℕ) (z : G) :
    (cardN L n z = 2 ^ 7 ∧ expo L n z = 4) ∨ (cardN L n z = 2 ^ 8 ∧ expo L n z = 8) := by
  by_cases h : IsASmall L n z
  · exact Or.inl ⟨cardN_of_ASmall h, expo_of_ASmall h⟩
  · exact Or.inr ⟨cardN_of_not_ASmall h, expo_of_not_ASmall h⟩

theorem false_of_two
    (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z 2 A) (ht : Terminal θ c.hn8 A) : False := by
  obtain ⟨ι, hι, hd⟩ := data_two c h ht
  have hD := termData_DU c h ht
  have hrD := range_kapU (θ := θ) c.hn8
  set Ψ := Psi.psi hd with hΨ
  have hinj : Function.Injective Ψ := Psi.psi_injective hd
  have hcardT : Nat.card Z4M = Nat.card (Tm A z (kapU θ c.hn8).range) := by
    rw [hrD, hD.card_Tm c, h.card, Z4M.card_Z4M]
    norm_num
  have hrange : Ψ.range = Tm A z (DU θ c.hn8) := by
    rw [← hrD]
    exact Psi.range_psi hd hcardT
  have hzM : z ∉ Mm A (kapU θ c.hn8).range := by
    rw [hrD]
    exact hD.z_not_mem_Mm c
  have hmemT : ∀ p : Z4M, Ψ p ∈ Tm A z (DU θ c.hn8) := fun p => hrange ▸ ⟨p, rfl⟩
  have hE : ∀ p : Z4M, Ψ p ∈ E θ c.hn8 ↔ p ∈ Z4M.Em := by
    intro p
    rw [Psi.mem_E_iff hd hι]
    constructor
    · rintro ⟨⟨hs, htv⟩, h2⟩
      obtain ⟨ha, hb, hc⟩ := tvOf_eq_one htv
      refine ⟨⟨hs, ha, hb, hc⟩, ?_, ?_, ?_⟩
      · simpa [Z4M.vec, two_nsmul, two_mul] using congrFun h2 0
      · simpa [Z4M.vec, two_nsmul, two_mul] using congrFun h2 1
      · simpa [Z4M.vec, two_nsmul, two_mul] using congrFun h2 2
    · rintro ⟨⟨hs, ha, hb, hc⟩, h0, h1, h2⟩
      refine ⟨⟨hs, by rw [ha, hb, hc]; exact tvOf_zero⟩, ?_⟩
      funext i
      fin_cases i
      · simpa [Z4M.vec, two_nsmul, two_mul] using h0
      · simpa [Z4M.vec, two_nsmul, two_mul] using h1
      · simpa [Z4M.vec, two_nsmul, two_mul] using h2
  have hcharE : ∀ x, x ∈ E θ c.hn8 ↔ x ∈ Tm A z (DU θ c.hn8) ∧ CondE (Tm A z (DU θ c.hn8)) x := by
    intro x
    constructor
    · intro hx
      have hxT : x ∈ Tm A z (DU θ c.hn8) := TermData.A_le_Tm (h.E_le hx)
      refine ⟨hxT, ?_⟩
      obtain ⟨p, rfl⟩ := hrange ▸ hxT
      rw [condE_psi_iff hinj hrange, ← Z4M.mem_Em_iff]
      exact (hE p).1 hx
    · rintro ⟨hxT, hx⟩
      obtain ⟨p, rfl⟩ := hrange ▸ hxT
      rw [condE_psi_iff hinj hrange, ← Z4M.mem_Em_iff] at hx
      exact (hE p).2 hx
  have hchar : ∀ y ∈ normalizer (Tm A z (DU θ c.hn8) : Set G),
      y ∈ normalizer (E θ c.hn8 : Set G) := by
    intro y hy
    refine mem_normalizer_fintype fun e he => ?_
    obtain ⟨heT, heC⟩ := (hcharE e).1 he
    exact (hcharE _).2 ⟨(mem_normalizer_iff.1 hy e).1 heT, heC.conj hy⟩
  have hsyl := hD.sylow_of_char c hchar
  obtain ⟨x, hxM, hxA, ⟨g, hxg⟩, hcard, hnc, hexp⟩ := hD.exists_extremal c hsyl
  obtain ⟨p, rfl⟩ := hrange ▸ TermData.Mm_le_Tm hxM
  have hpM : p ∈ Z4M.Mm := by
    have := (Psi.mem_Mm_iff hd hzM p).1 (by rw [hrD]; exact hxM)
    exact this
  have hpA : p ∉ Z4M.Am := by
    rintro ⟨hs, ha, hb, hc⟩
    apply hxA
    refine (Psi.mem_A_iff hd p).2 ⟨hs, ?_⟩
    show tvOf p.a p.b p.c = 1
    rw [ha, hb, hc]
    exact tvOf_zero
  have hp2 : p * p = 1 := by
    apply hinj
    rw [map_mul, map_one, hxg, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group,
      z_mul_self c]
    group
  have hpC : Nat.card (centralizer ({p} : Set Z4M)) = cardN L n z := by
    rw [natCard_centralizer_psi hinj, hrange, hcard]
  have htm : Ψ Z4M.tm = z := Psi.psi_t hd Z4M.tm (by funext i; fin_cases i <;> rfl) rfl tvOf_zero
  rcases Z4M.conj_or_exp (cardN_expo L n z) p hpM hpA hp2 hpC with ⟨k, hk⟩ | ⟨y, hy, hye⟩
  · apply hnc (Ψ k) (hmemT k)
    have := mem_centralizer_singleton_iff.1 hk
    rw [mem_centralizer_singleton_iff, ← htm, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, this]
  · apply hye
    apply hinj
    rw [map_pow, map_one]
    refine hexp (Ψ y) (Subgroup.mem_inf.2 ⟨hmemT y, ?_⟩)
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]

theorem false_of_three
    (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z 3 A)
    (ht : Terminal θ c.hn8 A) (he : expo L n z = 8) : False := by
  obtain ⟨ι, hι, u, hu, hd⟩ := data_three c h ht
  have hD := termData_DU c h ht
  have hrD := range_kapU (θ := θ) c.hn8
  set Ψ := Psi.psi hd with hΨ
  have hinj : Function.Injective Ψ := Psi.psi_injective hd
  have hcardT : Nat.card (Z8M u) = Nat.card (Tm A z (kapU θ c.hn8).range) := by
    rw [hrD, hD.card_Tm c, h.card, Z8M.card_Z8M]
    norm_num
  have hrange : Ψ.range = Tm A z (DU θ c.hn8) := by
    rw [← hrD]
    exact Psi.range_psi hd hcardT
  have hzM : z ∉ Mm A (kapU θ c.hn8).range := by
    rw [hrD]
    exact hD.z_not_mem_Mm c
  have hmemT : ∀ p : Z8M u, Ψ p ∈ Tm A z (DU θ c.hn8) := fun p => hrange ▸ ⟨p, rfl⟩
  have hsyl := hD.sylow_of_char c (hD.char_of_three_le c le_rfl)
  have hN : cardN L n z = 2 ^ 8 := by
    rcases cardN_expo L n z with ⟨-, h4⟩ | ⟨h8, -⟩
    · rw [h4] at he
      norm_num at he
    · exact h8
  obtain ⟨x, hxM, hxA, ⟨g, hxg⟩, hcard, hnc, hexp⟩ := hD.exists_extremal c hsyl
  obtain ⟨p, rfl⟩ := hrange ▸ TermData.Mm_le_Tm hxM
  have hpM : p ∈ Z8M.Mm u := by
    have := (Psi.mem_Mm_iff hd hzM p).1 (by rw [hrD]; exact hxM)
    exact this
  have hpA : p ∉ Z8M.Am u := by
    rintro ⟨hs, ha, hb, hc⟩
    apply hxA
    refine (Psi.mem_A_iff hd p).2 ⟨hs, ?_⟩
    show tvOf p.a p.b p.c = 1
    rw [ha, hb, hc]
    exact tvOf_zero
  have hp2 : p * p = 1 := by
    apply hinj
    rw [map_mul, map_one, hxg, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group,
      z_mul_self c]
    group
  have hpC : Nat.card (centralizer ({p} : Set (Z8M u))) = 2 ^ 8 := by
    rw [natCard_centralizer_psi hinj, hrange, hcard, hN]
  have htm : Ψ (Z8M.tm u) = z := Psi.psi_t hd (Z8M.tm u) Z8M.vec_tm rfl tvOf_zero
  rcases Z8M.conj_or_exp hu p hpM hpA hp2 hpC with ⟨k, hk⟩ | ⟨y, hy, hye⟩
  · apply hnc (Ψ k) (hmemT k)
    have := mem_centralizer_singleton_iff.1 hk
    rw [mem_centralizer_singleton_iff, ← htm, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, this]
  · apply hye
    apply hinj
    rw [map_pow, map_one, ← he]
    refine hexp (Ψ y) (Subgroup.mem_inf.2 ⟨hmemT y, ?_⟩)
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]

end Final

end CFSG.OddStandard.AltStdSmall4.G2
