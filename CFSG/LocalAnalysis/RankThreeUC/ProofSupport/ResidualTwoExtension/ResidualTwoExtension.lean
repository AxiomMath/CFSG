module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualConjugateClosure.ResidualConjugateClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualTwoExtension

open CFSG.LocalAnalysis.RankThreeUC SourceSetting Subgroup

variable {G : Type} [Group G]

theorem exists_two_pow_mem (K P : Subgroup G) (hPK : P ≤ Subgroup.normalizer K)
    (hP : IsPGroup 2 P) : ∀ x ∈ K ⊔ P, ∃ n : ℕ, x ^ (2 ^ n) ∈ K := by
  intro x hx
  have hx' : x ∈ ((K ⊔ P : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left K P hPK] at hx'
  obtain ⟨k, hk, p, hp, rfl⟩ := hx'
  haveI : (K.subgroupOf (P ⊔ K)).Normal := normal_subgroupOf_sup_of_le_normalizer hPK
  have hx : k * p ∈ P ⊔ K := by rw [sup_comm]; exact hx
  obtain ⟨n, hn⟩ := hP ⟨p, hp⟩
  refine ⟨n, ?_⟩
  let S : Subgroup G := P ⊔ K
  let y : S := ⟨k * p, hx⟩
  let q : S := ⟨p, (le_sup_left : P ≤ P ⊔ K) hp⟩
  have hyq : (QuotientGroup.mk' (K.subgroupOf S)) y = (QuotientGroup.mk' (K.subgroupOf S)) q := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [mem_subgroupOf]
    have := (mem_normalizer_iff''.mp (hPK hp) k⁻¹).mp (inv_mem hk)
    simpa [q, y, mul_assoc] using this
  have h1 : (QuotientGroup.mk' (K.subgroupOf S)) (y ^ (2 ^ n)) = 1 := by
    rw [map_pow, hyq, ← map_pow]
    have : q ^ (2 ^ n) = 1 := by
      apply Subtype.ext
      have := congrArg (fun z : P => (z : G)) hn
      simpa [q] using this
    rw [this, map_one]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem oPrimeResidual_sup_two_group (K P : Subgroup G) (hPK : P ≤ Subgroup.normalizer K)
    (hP : IsPGroup 2 P) (hK : oPrimeResidual 3 K = K) :
    oPrimeResidual 3 (K ⊔ P) = K ∧ QuotientIsTwoGroup 3 (K ⊔ P) := by
  have h1 : oPrimeResidual 3 (K ⊔ P) = K := by
    refine le_antisymm ?_ ?_
    · unfold oPrimeResidual
      refine (closure_le K).2 ?_
      rintro x ⟨hx, j, hj⟩
      obtain ⟨n, hn⟩ := exists_two_pow_mem K P hPK hP x hx
      have hcop : IsCoprime ((2 ^ n : ℕ) : ℤ) ((3 ^ j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow _ _ (by norm_num))
      obtain ⟨a, b, hab⟩ := hcop
      have hx1 : x ^ (3 ^ j) = 1 := hj ▸ pow_orderOf_eq_one x
      have : x = (x ^ (2 ^ n)) ^ a := by
        have e1 : x ^ (b * ((3 ^ j : ℕ) : ℤ)) = 1 := by
          rw [mul_comm, zpow_mul, zpow_natCast, hx1, one_zpow]
        have e2 : x ^ (a * ((2 ^ n : ℕ) : ℤ)) = (x ^ (2 ^ n)) ^ a := by
          rw [mul_comm, zpow_mul, zpow_natCast]
        calc x = x ^ (a * ((2 ^ n : ℕ) : ℤ) + b * ((3 ^ j : ℕ) : ℤ)) := by rw [hab, zpow_one]
          _ = (x ^ (2 ^ n)) ^ a := by rw [zpow_add, e1, mul_one, e2]
      rw [this]
      exact zpow_mem hn a
    · calc K = oPrimeResidual 3 K := hK.symm
        _ ≤ _ := ResidualConjugateClosure.oPrimeResidual_mono le_sup_left
  refine ⟨h1, ?_⟩
  intro y hy
  rw [h1]
  exact exists_two_pow_mem K P hPK hP y hy

theorem conj_mem_normalClosureUnder (X A : Subgroup G) {a : G} (ha : a ∈ A) {h : G}
    (hh : h ∈ normalClosureUnder X A) : a * h * a⁻¹ ∈ normalClosureUnder X A := by
  have hle : (normalClosureUnder X A).map (MulAut.conj a).toMonoidHom ≤
      normalClosureUnder X A := by
    unfold normalClosureUnder
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_map]
    have e : (MulAut.conj a).toMonoidHom.comp (MulAut.conj (g : G)).toMonoidHom =
        (MulAut.conj ((⟨a, ha⟩ * g : A) : G)).toMonoidHom := by
      ext z
      simp [mul_assoc]
    rw [e]
    exact le_iSup (fun h : A => X.map (MulAut.conj (h : G)).toMonoidHom) (⟨a, ha⟩ * g)
  exact hle ⟨h, hh, by simp⟩

theorem le_normalizer_normalClosureUnder (X A : Subgroup G) :
    A ≤ Subgroup.normalizer (normalClosureUnder X A) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_normalClosureUnder X A ha, fun h' => ?_⟩
  have := conj_mem_normalClosureUnder X A (inv_mem ha) h'
  simpa [mul_assoc] using this

theorem oPrimeResidual_normalClosureUnder_sup_two_group [Finite G] (Y A P : Subgroup G)
    (hYA : Y ≤ A) (hPA : P ≤ A) (hP : IsPGroup 2 P) :
    oPrimeResidual 3 (normalClosureUnder (oPrimeResidual 3 Y) A ⊔ P) =
        normalClosureUnder (oPrimeResidual 3 Y) A ∧
      QuotientIsTwoGroup 3 (normalClosureUnder (oPrimeResidual 3 Y) A ⊔ P) :=
  oPrimeResidual_sup_two_group _ P
    (hPA.trans (le_normalizer_normalClosureUnder _ A)) hP
    (ResidualConjugateClosure.oPrimeResidual_normalClosureUnder_oPrimeResidual 3 Y A)

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualTwoExtension
