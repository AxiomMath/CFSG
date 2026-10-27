module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

variable {K : Type*} [Field K] [CharP K 3]

theorem eq_one_or_eq_neg_one_of_mul_mem {ν : K} (hν : ν ≠ 0) {F : AddSubgroup K}
    (hF : F.index = 3) (hmul : ∀ x ∈ F, ν * x ∈ F) : ν = 1 ∨ ν = -1 := by
  classical
  have hle : F ≤ F.comap (AddMonoidHom.mulLeft ν) := fun x hx => hmul x hx
  let φ : K ⧸ F →+ K ⧸ F := QuotientAddGroup.map F F (AddMonoidHom.mulLeft ν) hle
  have hcard : Nat.card (K ⧸ F) = 3 := hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsAddCyclic (K ⧸ F) := isAddCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg (φ g))
  have hφ : ∀ q : K ⧸ F, φ q = m • q := by
    intro q
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg q)
    rw [map_zsmul, ← hm, smul_comm]
  have hall : ∀ x : K, (ν - (m : K)) * x ∈ F := by
    intro x
    have h := hφ (x : K ⧸ F)
    have h1 : φ (x : K ⧸ F) = ((ν * x : K) : K ⧸ F) := rfl
    rw [h1, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq] at h
    have h2 : (ν - (m : K)) * x = -(-(ν * x) + m • x) := by
      rw [zsmul_eq_mul]
      ring
    rw [h2]
    exact F.neg_mem h
  have hνm : ν = (m : K) := by
    by_contra hne
    have hne' : ν - (m : K) ≠ 0 := sub_ne_zero.mpr hne
    have htop : F = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have h := hall ((ν - (m : K))⁻¹ * y)
      rwa [← mul_assoc, mul_inv_cancel₀ hne', one_mul] at h
    rw [htop, AddSubgroup.index_top] at hF
    norm_num at hF
  have hcast : ZMod.castHom (dvd_refl 3) K (m : ZMod 3) = (m : K) := map_intCast _ m
  rw [← hcast] at hνm
  generalize (m : ZMod 3) = r at hνm
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  fin_cases r
  · exact absurd (hνm.trans (map_zero _)) hν
  · exact Or.inl (hνm.trans (map_one _))
  · right
    have h2 : ν = 2 := hνm.trans (map_ofNat _ 2)
    rw [h2]
    linear_combination h3

theorem eq_one_or_eq_neg_one_of_mul_mem_mult {ν : K} (hν : ν ≠ 0)
    {F : Subgroup (Multiplicative K)} (hF : F.index = 3)
    (hmul : ∀ x ∈ F, Multiplicative.ofAdd (ν * Multiplicative.toAdd x) ∈ F) :
    ν = 1 ∨ ν = -1 :=
  eq_one_or_eq_neg_one_of_mul_mem hν (F := AddSubgroup.toSubgroup.symm F)
    (by rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply]; exact hF)
    fun x hx => hmul (.ofAdd x) hx

end CFSG.HardMathSupport.Foote.SPLScalar
