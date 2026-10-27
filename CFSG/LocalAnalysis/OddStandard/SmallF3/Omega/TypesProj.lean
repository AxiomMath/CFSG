module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def piGroup (Q : QuadraticForm (ZMod 3) V) : Subgroup (OGroup Q) :=
  Subgroup.zpowers (piOrth Q)

private lemma aux_piOrth_zpow (k : ℤ) :
    piOrth Q ^ k = 1 ∨ piOrth Q ^ k = piOrth Q := by
  have h2 : piOrth Q ^ (2 : ℤ) = 1 := by
    rw [zpow_two, piOrth_mul_self]
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_piGroup_iff {g : OGroup Q} : g ∈ piGroup Q ↔ g = 1 ∨ g = piOrth Q := by
  constructor
  · intro hg
    change g ∈ Subgroup.zpowers (piOrth Q) at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact aux_piOrth_zpow k
  · rintro (rfl | rfl)
    · exact (piGroup Q).one_mem
    · exact Subgroup.mem_zpowers (piOrth Q)

theorem piOrth_mem_center : piOrth Q ∈ Subgroup.center (OGroup Q) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (g : V ≃ₗ[ZMod 3] V) ((piOrth Q : V ≃ₗ[ZMod 3] V) v) =
    (piOrth Q : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v)
  rw [coe_piOrth_apply, coe_piOrth_apply, map_neg]

instance piGroup_normal : (piGroup Q).Normal :=
  ⟨fun n hn g => by
    rcases (mem_piGroup_iff.mp hn) with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact (piGroup Q).one_mem
    · have hc : g * piOrth Q = piOrth Q * g :=
        Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_zpowers (piOrth Q)⟩

theorem piOrth_ne_one (h : 0 < Module.finrank (ZMod 3) V) : piOrth Q ≠ 1 := by
  intro hπ
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  have h1 : (piOrth Q : V ≃ₗ[ZMod 3] V) v = v := by
    have hc := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V) v) hπ
    simpa using hc
  rw [coe_piOrth_apply] at h1
  have h2 : (2 : ZMod 3) • v = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h1
  exact hv ((isUnit_of_invertible (2 : ZMod 3)).smul_eq_zero.mp h2)

theorem card_piGroup (h : 0 < Module.finrank (ZMod 3) V) : Nat.card (piGroup Q) = 2 := by
  have hord : orderOf (piOrth Q) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact piOrth_mul_self) (piOrth_ne_one h)
  change Nat.card (Subgroup.zpowers (piOrth Q)) = 2
  rw [Nat.card_zpowers, hord]

abbrev ProjOrth (Q : QuadraticForm (ZMod 3) V) : Type := OGroup Q ⧸ piGroup Q

noncomputable abbrev toProj (Q : QuadraticForm (ZMod 3) V) : OGroup Q →* ProjOrth Q :=
  QuotientGroup.mk' (piGroup Q)

private lemma aux_unit_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

private lemma aux_sign_compose (σ β : ℤˣ) (k : ℕ) :
    σ * (σ * β * (-1) ^ k) * (-1) ^ k = β := by
  have hσ : σ * σ = 1 := aux_unit_mul_self σ
  have hp : (-1 : ℤˣ) ^ k * (-1) ^ k = 1 := aux_unit_mul_self _
  rw [show σ * (σ * β * (-1) ^ k) * (-1) ^ k =
      (σ * σ) * β * ((-1) ^ k * (-1) ^ k) by group, hσ, hp, mul_one, one_mul]

private lemma aux_neg_mul_mul_pow (u : ℤˣ) (r : ℕ) :
    (-1 : ℤˣ) * u * (-1) ^ r = (-1) ^ (r + 1) * u := by
  rw [pow_succ, mul_comm ((-1 : ℤˣ) ^ r) (-1)]
  ac_rfl

theorem toProj_piOrth : toProj Q (piOrth Q) = 1 := by
  change QuotientGroup.mk' (piGroup Q) (piOrth Q) = 1
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff (piOrth Q)).mpr (Subgroup.mem_zpowers (piOrth Q))

private lemma aux_quadSign_restrict_congr {A B : Submodule (ZMod 3) V} (h : A = B) :
    quadSign (Q.restrict A) = quadSign (Q.restrict B) := by
  rw [h]

@[expose] def HasType (x : ProjOrth Q) (r : ℕ) (α : ℤˣ) : Prop :=
  x ≠ 1 ∧ ∃ t : OGroup Q, t * t = 1 ∧ invType t = (r, α) ∧ toProj Q t = x

theorem piOrth_mul_mul_self {t : OGroup Q} (htt : t * t = 1) :
    (piOrth Q * t) * (piOrth Q * t) = 1 := by
  have hc : t * piOrth Q = piOrth Q * t :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
  calc (piOrth Q * t) * (piOrth Q * t)
      = piOrth Q * (t * piOrth Q) * t := by group
    _ = piOrth Q * (piOrth Q * t) * t := by rw [hc]
    _ = (piOrth Q * piOrth Q) * (t * t) := by group
    _ = 1 := by rw [piOrth_mul_self, htt, mul_one]

theorem commSp_piOrth_mul {t : OGroup Q} (htt : t * t = 1) : commSp (piOrth Q * t) = fixSp t := by
  ext v
  rw [mem_commSp_iff (piOrth_mul_mul_self htt), mem_fixSp_iff]
  change ((piOrth Q : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) v = -v ↔
    (t : V ≃ₗ[ZMod 3] V) v = v
  rw [LinearEquiv.mul_apply, coe_piOrth_apply, neg_inj]

theorem invType_piOrth_mul (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    invType (piOrth Q * t) =
      (Module.finrank (ZMod 3) V - invDim t,
        quadSign Q * invSign t * (-1) ^ (invDim t * (Module.finrank (ZMod 3) V - invDim t))) := by
  simp only [invType]
  apply Prod.ext
  · simp only [invDim]
    rw [commSp_piOrth_mul htt]
    have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  · simp only [invSign]
    rw [aux_quadSign_restrict_congr (commSp_piOrth_mul htt)]
    exact quadSign_fixSp_eq hQ htt

private lemma aux_even_mul_sub_of_odd {n r : ℕ} (hr : r ≤ n) (hn : Odd n) :
    Even (r * (n - r)) := by
  rw [Nat.even_mul]
  rcases Nat.even_or_odd r with he | ho
  · exact Or.inl he
  · refine Or.inr ?_
    rw [Nat.even_sub hr]
    exact ⟨fun hen => absurd hen (Nat.not_even_iff_odd.mpr hn),
      fun her => absurd her (Nat.not_even_iff_odd.mpr ho)⟩

private lemma aux_neg_one_pow_mul_sub_of_odd {n r : ℕ} (hr : r ≤ n) (hn : Odd n) :
    ((-1 : ℤˣ) ^ (r * (n - r))) = 1 :=
  (aux_even_mul_sub_of_odd hr hn).neg_one_pow

private lemma aux_neg_one_pow_mul_sub_of_even {n r : ℕ} (hr : r ≤ n) (hn : Even n) :
    ((-1 : ℤˣ) ^ (r * (n - r))) = (-1) ^ r := by
  apply neg_one_pow_congr
  rw [Nat.even_mul]
  constructor
  · rintro (her | hnr)
    · exact her
    · have h1 : Even (n - (n - r)) :=
        (Nat.even_sub (Nat.sub_le n r)).mpr ⟨fun _ => hnr, fun _ => hn⟩
      rwa [Nat.sub_sub_self hr] at h1
  · intro her
    exact Or.inl her

theorem invType_piOrth_mul_of_odd (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hn : Odd (Module.finrank (ZMod 3) V)) (hσ : quadSign Q = 1) :
    invType (piOrth Q * t) = (Module.finrank (ZMod 3) V - invDim t, invSign t) := by
  rw [invType_piOrth_mul hQ htt, hσ, one_mul,
    aux_neg_one_pow_mul_sub_of_odd (invDim_le t) hn, mul_one]

theorem invType_piOrth_mul_of_even_plus (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hn : Even (Module.finrank (ZMod 3) V)) (hσ : quadSign Q = 1) :
    invType (piOrth Q * t) =
      (Module.finrank (ZMod 3) V - invDim t, (-1) ^ invDim t * invSign t) := by
  rw [invType_piOrth_mul hQ htt, hσ, one_mul,
    aux_neg_one_pow_mul_sub_of_even (invDim_le t) hn, mul_comm]

theorem invType_piOrth_mul_of_even_minus (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hn : Even (Module.finrank (ZMod 3) V)) (hσ : quadSign Q = -1) :
    invType (piOrth Q * t) =
      (Module.finrank (ZMod 3) V - invDim t, (-1) ^ (invDim t + 1) * invSign t) := by
  rw [invType_piOrth_mul hQ htt, hσ,
    aux_neg_one_pow_mul_sub_of_even (invDim_le t) hn, aux_neg_mul_mul_pow (invSign t) (invDim t)]

private lemma aux_hasType_sub_forward (hQ : Q.Nondegenerate) {x : ProjOrth Q} {r : ℕ}
    (hr : r ≤ Module.finrank (ZMod 3) V) {α : ℤˣ} (h : HasType x r α) :
    HasType x (Module.finrank (ZMod 3) V - r)
      (quadSign Q * α * (-1) ^ (r * (Module.finrank (ZMod 3) V - r))) := by
  simp only [HasType] at h ⊢
  rcases h with ⟨hx1, t, htt, htype, rfl⟩
  refine ⟨hx1, piOrth Q * t, piOrth_mul_mul_self htt, ?_, ?_⟩
  · have hdim : invDim t = r := by
      simpa only [invType] using congrArg Prod.fst htype
    have hsign : invSign t = α := by
      simpa only [invType] using congrArg Prod.snd htype
    rw [invType_piOrth_mul hQ htt, hdim, hsign]
  · rw [map_mul, toProj_piOrth, one_mul]

theorem hasType_iff_hasType_sub (hQ : Q.Nondegenerate) {x : ProjOrth Q} {r : ℕ}
    (hr : r ≤ Module.finrank (ZMod 3) V) {α : ℤˣ} :
    HasType x r α ↔
      HasType x (Module.finrank (ZMod 3) V - r)
        (quadSign Q * α * (-1) ^ (r * (Module.finrank (ZMod 3) V - r))) := by
  constructor
  · exact aux_hasType_sub_forward hQ hr
  · intro h
    have hf := aux_hasType_sub_forward (hQ := hQ)
      (hr := Nat.sub_le (Module.finrank (ZMod 3) V) r)
      (α := quadSign Q * α * (-1) ^ (r * (Module.finrank (ZMod 3) V - r))) h
    rw [Nat.sub_sub_self hr] at hf
    rw [show (Module.finrank (ZMod 3) V - r) * r =
      r * (Module.finrank (ZMod 3) V - r) from Nat.mul_comm _ _] at hf
    rwa [aux_sign_compose] at hf

theorem hasType_iff_of_odd (hQ : Q.Nondegenerate) {x : ProjOrth Q} {r : ℕ}
    (hr : r ≤ Module.finrank (ZMod 3) V) {α : ℤˣ} (hn : Odd (Module.finrank (ZMod 3) V))
    (hσ : quadSign Q = 1) :
    HasType x r α ↔ HasType x (Module.finrank (ZMod 3) V - r) α := by
  rw [hasType_iff_hasType_sub hQ hr, hσ, one_mul,
    aux_neg_one_pow_mul_sub_of_odd hr hn, mul_one]

theorem hasType_iff_of_even_plus (hQ : Q.Nondegenerate) {x : ProjOrth Q} {r : ℕ}
    (hr : r ≤ Module.finrank (ZMod 3) V) {α : ℤˣ} (hn : Even (Module.finrank (ZMod 3) V))
    (hσ : quadSign Q = 1) :
    HasType x r α ↔ HasType x (Module.finrank (ZMod 3) V - r) ((-1) ^ r * α) := by
  rw [hasType_iff_hasType_sub hQ hr, hσ, one_mul,
    aux_neg_one_pow_mul_sub_of_even hr hn, mul_comm]

theorem hasType_iff_of_even_minus (hQ : Q.Nondegenerate) {x : ProjOrth Q} {r : ℕ}
    (hr : r ≤ Module.finrank (ZMod 3) V) {α : ℤˣ} (hn : Even (Module.finrank (ZMod 3) V))
    (hσ : quadSign Q = -1) :
    HasType x r α ↔ HasType x (Module.finrank (ZMod 3) V - r) ((-1) ^ (r + 1) * α) := by
  rw [hasType_iff_hasType_sub hQ hr, hσ,
    aux_neg_one_pow_mul_sub_of_even hr hn, aux_neg_mul_mul_pow α r]

theorem isConj_toProj_iff (hQ : Q.Nondegenerate) {s t : OGroup Q} (hs : s * s = 1)
    (ht : t * t = 1) :
    IsConj (toProj Q s) (toProj Q t) ↔
      invType s = invType t ∨ invType s = invType (piOrth Q * t) := by
  have ht' : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self ht
  constructor
  · intro hconj
    rw [isConj_iff] at hconj
    obtain ⟨y, hy⟩ := hconj
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
    have hy' : toProj Q (g * s * g⁻¹) = toProj Q t := by
      rw [map_mul, map_mul, map_inv]
      exact hy
    have hmem : (g * s * g⁻¹) / t ∈ piGroup Q := by
      refine (QuotientGroup.eq_iff_div_mem (N := piGroup Q)).mp ?_
      change toProj Q (g * s * g⁻¹) = toProj Q t
      exact hy'
    rw [div_eq_mul_inv] at hmem
    rcases (mem_piGroup_iff.mp hmem) with h1 | h1
    · left
      have hgt : g * s * g⁻¹ = t := by
        have h := congrArg (fun z => z * t) h1
        simpa [mul_assoc] using h
      rw [← invType_conj hQ hs g, hgt]
    · right
      have hgt : g * s * g⁻¹ = piOrth Q * t := by
        have h := congrArg (fun z => z * t) h1
        simpa [mul_assoc] using h
      rw [← invType_conj hQ hs g, hgt]
  · rintro (h | h)
    · exact (toProj Q).map_isConj ((isConj_iff_invType_eq hQ hs ht).mpr h)
    · have h1 := (toProj Q).map_isConj ((isConj_iff_invType_eq hQ hs ht').mpr h)
      simpa only [map_mul, toProj_piOrth, one_mul] using h1

end CFSG.OddStandard.SmallF3.Omega
