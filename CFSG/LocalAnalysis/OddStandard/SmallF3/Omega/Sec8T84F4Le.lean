module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E1Lem35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E3UpA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private lemma mem_sup_or_mul_of_normalizes {t : G} {T0 T : Subgroup G}
    (ht : t * t = 1) (hT : T = zpowers t ⊔ T0)
    (hnorm : ∀ u ∈ T0, t * u * t⁻¹ ∈ T0) :
    ∀ u ∈ T, u ∈ T0 ∨ u * t ∈ T0 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let K : Subgroup G :=
    { carrier := {x : G | x ∈ T0 ∨ x * t ∈ T0}
      one_mem' := Or.inl T0.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (T0.mul_mem hx hy)
        · exact Or.inr (by simpa [mul_assoc] using T0.mul_mem hx hy)
        · have hw : t * y * t ∈ T0 := by
            have h := hnorm y hy
            rwa [htinv] at h
          refine Or.inr ?_
          have h : (x * t) * (t * y * t) ∈ T0 := T0.mul_mem hx hw
          have heq : (x * y) * t = (x * t) * (t * y * t) := by
            calc
              (x * y) * t = x * (y * t) := by group
              _ = x * ((t * t) * (y * t)) := by rw [ht, one_mul]
              _ = (x * t) * (t * y * t) := by group
          rwa [← heq] at h
        · have hw : t * y ∈ T0 := by
            have h := hnorm (y * t) hy
            rwa [show t * (y * t) * t⁻¹ = t * y from by group] at h
          refine Or.inl ?_
          have h : (x * t) * (t * y) ∈ T0 := T0.mul_mem hx hw
          have heq : x * y = (x * t) * (t * y) := by
            calc
              x * y = x * ((t * t) * y) := by rw [ht, one_mul]
              _ = (x * t) * (t * y) := by group
          rwa [← heq] at h
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (T0.inv_mem hx)
        · refine Or.inr ?_
          have hw : t * (x * t)⁻¹ * t ∈ T0 := by
            have h := hnorm (x * t)⁻¹ (T0.inv_mem hx)
            rwa [htinv] at h
          have hx' : x = (x * t) * t := by rw [mul_assoc, ht, mul_one]
          have hxinv : x⁻¹ = t * (x * t)⁻¹ := by
            conv_lhs => rw [hx']
            rw [mul_inv_rev, htinv]
          rw [hxinv]
          exact hw }
  have hT0K : T0 ≤ K := fun x hx => Or.inl hx
  have hzpK : zpowers t ≤ K := by
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [ht]; exact T0.one_mem)
  have hTK : T ≤ K := by
    rw [hT]
    exact sup_le hzpK hT0K
  intro u hu
  exact hTK hu

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_E8_le_T0 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {A : Subgroup G}
    (hA : A ≤ T) (h8 : IsElemAb2 A 8) : A ≤ T1 ⊔ T2 := by
  by_contra hle
  obtain ⟨x, hxA, hxT0⟩ := Set.not_subset.mp hle
  have hAe : CFSG.Open.IsElemAbelian 2 A := h8.1
  have hAcard : Nat.card A = 2 ^ 8 := h8.2
  have hxT : x ∈ T := hA hxA
  have hx2 : x * x = 1 := hAe.mul_self_eq_one hxA
  obtain ⟨a, haT1, hxaeq⟩ :=
    sec8t84_lemma35 D.t_sq rfl D.T_eq D.comm D.inf D.swap1 D.swap2 x hxT hx2 hxT0
  have hmem : ∀ u ∈ T, u ∈ T1 ⊔ T2 ∨ u * t ∈ T1 ⊔ T2 :=
    mem_sup_or_mul_of_normalizes D.t_sq D.T_eq
      (fun u hu => sec8t84_wr_conj_mem D.wr hu)
  have hrel : (T1 ⊔ T2).relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨x, hxA, hxT0, ?_⟩
    intro b hbA
    by_cases hb : b ∈ T1 ⊔ T2
    · exact Or.inr hb
    · left
      have hbt : b * t ∈ T1 ⊔ T2 := (hmem b (hA hbA)).resolve_left hb
      have hxt : x * t ∈ T1 ⊔ T2 := (hmem x hxT).resolve_left hxT0
      have h1 : (b * t) * (x * t)⁻¹ = b * x⁻¹ := by group
      rw [← inv_eq_of_mul_eq_one_right hx2, ← h1]
      exact (T1 ⊔ T2).mul_mem hbt ((T1 ⊔ T2).inv_mem hxt)
  have hcardT : Nat.card ↥((T1 ⊔ T2) ⊓ A) = 2 ^ 7 := by
    have h2 : 2 * Nat.card ↥((T1 ⊔ T2) ⊓ A) = Nat.card A := by
      rw [← Subgroup.relIndex_mul_card (H := T1 ⊔ T2) (K := A), hrel]
    rw [hAcard] at h2
    norm_num at h2 ⊢
    omega
  let R : Subgroup G := ((T1 ⊔ T2) ⊓ A).map (MulAut.conj (a⁻¹)).toMonoidHom
  have hAeInter : CFSG.Open.IsElemAbelian 2 ((T1 ⊔ T2) ⊓ A) := hAe.mono inf_le_right
  have hRe : CFSG.Open.IsElemAbelian 2 R := by
    change CFSG.Open.IsElemAbelian 2
      (((T1 ⊔ T2) ⊓ A).map (MulAut.conj (a⁻¹)).toMonoidHom)
    exact hAeInter.map (MulAut.conj (a⁻¹)).toMonoidHom
  have hRcard : Nat.card ↥R = Nat.card ↥((T1 ⊔ T2) ⊓ A) := by
    change Nat.card ↥(((T1 ⊔ T2) ⊓ A).map (MulAut.conj (a⁻¹)).toMonoidHom) =
      Nat.card ↥((T1 ⊔ T2) ⊓ A)
    exact Subgroup.card_map_of_injective (K := (T1 ⊔ T2) ⊓ A)
      (f := (MulAut.conj (a⁻¹)).toMonoidHom) (MulAut.conj (a⁻¹)).injective
  have hRle : R ≤ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    constructor
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact (T1 ⊔ T2).mul_mem ((T1 ⊔ T2).mul_mem
        ((T1 ⊔ T2).inv_mem (Subgroup.mem_sup_left haT1)) hz.1)
        (Subgroup.mem_sup_left haT1)
    · have hxcomm : z * (a * t * a⁻¹) = (a * t * a⁻¹) * z := by
        rw [← hxaeq]; exact hAe.comm hz.2 hxA
      have hconj : a⁻¹ * z * a * t = t * (a⁻¹ * z * a) := by
        calc a⁻¹ * z * a * t = a⁻¹ * (z * (a * t * a⁻¹)) * a := by group
          _ = a⁻¹ * ((a * t * a⁻¹) * z) * a := by rw [hxcomm]
          _ = t * (a⁻¹ * z * a) := by group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      change a⁻¹ * z * a ∈ centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hconj.symm
  obtain ⟨R1, hR1T1, hR1e, hR1card, -, -⟩ :=
    sec8t84_wr_elem_cent D.wr hRle hRe
  have hR1le16 : Nat.card R1 ≤ 16 := by
    refine sec8t84_no_e32 (P := T1) (B1 := V1) (B2 := F1) ?_ hR1T1 hR1e
    intro B hB hBe hBcard
    exact D.mod1.only B hB ⟨hBe, by rw [hBcard]; norm_num⟩
  have h128 : 128 ≤ Nat.card R1 := by
    rw [hR1card, hRcard, hcardT]
    norm_num
  omega

end TData

end CFSG.OddStandard.SmallF3.Omega
