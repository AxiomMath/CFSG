module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Data
public import CFSG.CGT.PushingUpLit.CGT6.Emb5FourT
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V] {G T Y H Q : Subgroup (MulAut V)}

omit [Finite V] in
theorem Emb55Data.mem_normalizer_Q (d : Emb55Data V G T Y H Q) {h : MulAut V} (hh : h ∈ H) :
    h ∈ Subgroup.normalizer (Q : Set (MulAut V)) :=
  Subgroup.mem_normalizer_iff.mpr fun q =>
    ⟨fun hq => d.Qnorm h hh q hq, fun hq => by
      have h1 := d.Qnorm h⁻¹ (H.inv_mem hh) _ hq
      have e : h⁻¹ * (h * q * h⁻¹) * h⁻¹⁻¹ = q := by group
      rwa [e] at h1⟩

theorem Emb55Data.exists_crit (d : Emb55Data V G T Y H Q) {y : MulAut V} (hy : y ∈ Y)
    (hy1 : y ≠ 1) :
    ∃ D : Subgroup (MulAut V), D ≤ Q ∧ (∀ x ∈ D, x ^ 3 = 1) ∧
      (∀ h ∈ H, ∀ x ∈ D, h * x * h⁻¹ ∈ D) ∧
      (∀ x ∈ D, ∀ q ∈ Q, ⁅x, q⁆ ∈ D ∧ ∀ z ∈ D, ⁅x, q⁆ * z = z * ⁅x, q⁆) ∧
      ((∀ h ∈ H, ∀ x ∈ D, h * x = x * h) → IsPGroup 3 ↥H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQne : Q ≠ ⊥ := by
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hbot
    apply hy1
    have : y ∈ Q := d.Qcent y (d.yH hy) fun q hq => by rw [hbot q hq]; simp
    exact hbot y this
  have hQnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    odd_critical_exponent_subgroup (p := 3) (by norm_num) d.Q3
  refine ⟨D.map Q.subtype, Subgroup.map_subtype_le D, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hDexp x hx
    simpa using congrArg Subtype.val this
  · intro h hh x hx
    exact conj_mem_map_of_characteristic' (D := D) (d.mem_normalizer_Q hh) hx
  · rintro _ ⟨x, hx, rfl⟩ q hq
    have hmem : ⁅x, (⟨q, hq⟩ : ↥Q)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set ↥Q) :=
      hDcomm (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top _))
    refine ⟨⟨⁅x, ⟨q, hq⟩⁆, hmem.1, by simp [commutatorElement_def]⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hmem.2 z hz
    simpa [commutatorElement_def] using (congrArg Subtype.val this).symm
  · intro hcent ⟨h, hh⟩
    have hmem := d.mem_normalizer_Q hh
    set φ : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨h, hmem⟩ with hφ
    have hφfix : φ ∈ fixingSubgroup (MulAut ↥Q) (D : Set ↥Q) := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      show ((φ x : ↥Q) : MulAut V) = x
      rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have := hcent h hh x ⟨x, hx, rfl⟩
      rw [this]; group
    obtain ⟨k, hk⟩ := hDfix ⟨φ, hφfix⟩
    have hφk : φ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcentQ : ∀ q ∈ Q, h ^ 3 ^ k * q = q * h ^ 3 ^ k := by
      intro q hq
      have h1 := congrArg (fun ψ : MulAut ↥Q => ((ψ ⟨q, hq⟩ : ↥Q) : MulAut V)) hφk
      have e : φ ^ 3 ^ k = Subgroup.normalizerMonoidHom Q (⟨h, hmem⟩ ^ 3 ^ k) := by
        rw [hφ, map_pow]
      simp only [e, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow,
        MulAut.one_apply] at h1
      have h2 : h ^ 3 ^ k * q * (h ^ 3 ^ k)⁻¹ = q := h1
      calc h ^ 3 ^ k * q = (h ^ 3 ^ k * q * (h ^ 3 ^ k)⁻¹) * h ^ 3 ^ k := by group
        _ = q * h ^ 3 ^ k := by rw [h2]
    have hpowH : h ^ 3 ^ k ∈ H := H.pow_mem hh _
    have hpowQ : h ^ 3 ^ k ∈ Q := d.Qcent _ hpowH hcentQ
    obtain ⟨j, hj⟩ := d.Q3 ⟨h ^ 3 ^ k, hpowQ⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    simpa [pow_mul] using this

end CFSG.CGT.PushingUpLit.CGT6E
