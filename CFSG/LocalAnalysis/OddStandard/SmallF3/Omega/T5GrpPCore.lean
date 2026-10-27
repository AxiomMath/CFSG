module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A B : Type} [Group A] [Group B]

private lemma twoPrimeRes_subgroupOf_normal (D : Subgroup A) :
    ((twoPrimeRes D).subgroupOf D).Normal := by
  let S : Set A := {g | g ∈ D ∧ ∃ k : ℕ, orderOf g = 2 ^ k}
  have hSdef : twoPrimeRes D = Subgroup.closure S := rfl
  have hS : ∀ k ∈ D, ∀ g ∈ S, k * g * k⁻¹ ∈ S := by
    rintro k hk g ⟨hgD, m, hm⟩
    refine ⟨D.mul_mem (D.mul_mem hk hgD) (D.inv_mem hk), m, ?_⟩
    rw [← hm]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj k) g)
  have hle : D ≤ Subgroup.normalizer (twoPrimeRes D) := by
    rw [hSdef]
    exact (Subgroup.le_normalizer_closure_iff (H := D) (s := S)).mpr
      fun k hk g hg => Subgroup.subset_closure (hS k hk g hg)
  exact Subgroup.normal_subgroupOf_of_le_normalizer hle

theorem t5_map_inSubgroup_pCore [Finite A] (f : A →* B) (h2 : ∀ k ∈ f.ker, k * k = 1)
    (D : Subgroup A) :
    CFSG.inSubgroup (CFSG.pCore 2) (D.map f) = (CFSG.inSubgroup (CFSG.pCore 2) D).map f := by
  let fD : ↥D →* ↥(D.map f) := f.subgroupMap D
  have hfD : Function.Surjective fD := f.subgroupMap_surjective D
  have hcore : (CFSG.pCore 2 ↥D).map fD = CFSG.pCore 2 ↥(D.map f) := by
    apply le_antisymm
    · have hnorm : ((CFSG.pCore 2 ↥D).map fD).Normal :=
        (CFSG.pCore_normal (p := 2) (G := ↥D)).map fD hfD
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥D).map fD) :=
        IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥D)) fD
      exact le_sSup ⟨hnorm, hp⟩
    · let P : Subgroup ↥D := (CFSG.pCore 2 ↥(D.map f)).comap fD
      have hPnorm : P.Normal :=
        (CFSG.pCore_normal (p := 2) (G := ↥(D.map f))).comap fD
      have hPp : IsPGroup 2 P := by
        rw [isPGroup_iff_orderOf_dvd_pow]
        intro g
        obtain ⟨a, ha⟩ :=
          (CFSG.pCore_isPGroup (p := 2) (G := ↥(D.map f))).exists_pow_pow_eq_one
            ⟨fD g.1, g.2⟩
        have ha' : fD g.1 ^ 2 ^ a = 1 := by
          simpa using congrArg
            (fun y : ↥(CFSG.pCore 2 ↥(D.map f)) => (y : ↥(D.map f))) ha
        refine ⟨a + 1, ?_⟩
        have hker : g.1 ^ 2 ^ a ∈ fD.ker := by
          rw [MonoidHom.mem_ker, map_pow, ha']
        have hk : ((g.1 ^ 2 ^ a : ↥D) : A) ∈ f.ker := by
          rw [MonoidHom.mem_ker]
          have hcoe : ((fD (g.1 ^ 2 ^ a) : ↥(D.map f)) : B) =
              f ((g.1 ^ 2 ^ a : ↥D) : A) := rfl
          rw [← hcoe, hker]
          rfl
        have hsq : ((g.1 : A) ^ 2 ^ a) * ((g.1 : A) ^ 2 ^ a) = 1 := by
          simpa using h2 _ hk
        have hpow : (g.1 : A) ^ 2 ^ (a + 1) = 1 := by
          have h2a : 2 ^ (a + 1) = 2 ^ a * 2 := by rw [pow_succ]
          rw [h2a, pow_mul, pow_two, hsq]
        have hpowD : (g.1 : ↥D) ^ 2 ^ (a + 1) = 1 := by
          apply Subtype.ext
          simpa using hpow
        rw [← Subgroup.orderOf_coe g]
        exact orderOf_dvd_iff_pow_eq_one.mpr hpowD
      have hle : P ≤ CFSG.pCore 2 ↥D := le_sSup ⟨hPnorm, hPp⟩
      calc CFSG.pCore 2 ↥(D.map f) = P.map fD :=
            (Subgroup.map_comap_eq_self_of_surjective hfD _).symm
        _ ≤ (CFSG.pCore 2 ↥D).map fD := Subgroup.map_mono hle
  calc
    CFSG.inSubgroup (CFSG.pCore 2) (D.map f)
        = (CFSG.pCore 2 ↥(D.map f)).map (D.map f).subtype := rfl
    _ = ((CFSG.pCore 2 ↥D).map fD).map (D.map f).subtype := by rw [hcore]
    _ = (CFSG.pCore 2 ↥D).map ((D.map f).subtype.comp fD) := by rw [Subgroup.map_map]
    _ = (CFSG.pCore 2 ↥D).map (f.comp D.subtype) := rfl
    _ = ((CFSG.pCore 2 ↥D).map D.subtype).map f := by rw [Subgroup.map_map]
    _ = (CFSG.inSubgroup (CFSG.pCore 2) D).map f := rfl

theorem t5_xout_eq_pCore [Finite A] (f : A →* B) (h2 : ∀ k ∈ f.ker, k * k = 1)
    (D : Subgroup A)
    (h : (twoPrimeRes D).map f = (CFSG.inSubgroup (CFSG.pCore 2) D).map f) :
    twoPrimeRes D = CFSG.inSubgroup (CFSG.pCore 2) D := by
  set X : Subgroup A := twoPrimeRes D with hX
  have hXD : X ≤ D := by
    rw [hX]
    exact Iff.mpr (Subgroup.closure_le (K := D)) fun g hg => hg.1
  have hXnorm : (X.subgroupOf D).Normal := by
    rw [hX]
    exact twoPrimeRes_subgroupOf_normal D
  have hXf : IsPGroup 2 (X.map f) := by
    rw [h]
    change IsPGroup 2 (((CFSG.pCore 2 ↥D).map D.subtype).map f)
    rw [Subgroup.map_map]
    exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥D)) (f.comp D.subtype)
  have hXp : IsPGroup 2 ↥X := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    obtain ⟨a, ha⟩ :=
      hXf.exists_pow_pow_eq_one ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
    have ha' : f x.1 ^ 2 ^ a = 1 := by
      simpa using congrArg (fun y : ↥(X.map f) => (y : B)) ha
    have hker : x.1 ^ 2 ^ a ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, ha']
    have hsq : x.1 ^ 2 ^ a * (x.1 ^ 2 ^ a) = 1 := h2 _ hker
    have hpow : x.1 ^ 2 ^ (a + 1) = 1 := by
      have h2a : 2 ^ (a + 1) = 2 ^ a * 2 := by rw [pow_succ]
      rw [h2a, pow_mul, pow_two, hsq]
    refine ⟨a + 1, ?_⟩
    rw [← Subgroup.orderOf_coe x]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hPX : CFSG.inSubgroup (CFSG.pCore 2) D ≤ X := by
    intro y hy
    change y ∈ (CFSG.pCore 2 ↥D).map D.subtype at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨k, hk⟩ :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥D)).exists_orderOf_eq_pow ⟨z, hz⟩
    rw [hX]
    refine Subgroup.subset_closure ⟨z.2, k, ?_⟩
    change orderOf (z : A) = 2 ^ k
    rw [Subgroup.orderOf_coe z]
    exact (Subgroup.orderOf_coe (⟨z, hz⟩ : ↥(CFSG.pCore 2 ↥D))).trans hk
  have hXP : X ≤ CFSG.inSubgroup (CFSG.pCore 2) D := by
    have hsub : X.subgroupOf D ≤ CFSG.pCore 2 ↥D :=
      le_sSup ⟨hXnorm, hXp.comap_subtype⟩
    calc X = (X.subgroupOf D).map D.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hXD).symm
      _ ≤ (CFSG.pCore 2 ↥D).map D.subtype := Subgroup.map_mono hsub
      _ = CFSG.inSubgroup (CFSG.pCore 2) D := rfl
  exact le_antisymm hXP hPX

end CFSG.OddStandard.SmallF3.Omega
