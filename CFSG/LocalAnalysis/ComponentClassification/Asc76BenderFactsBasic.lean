module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderCount
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ComponentClassification.AschbacherToolkit.Bender

section Borel

variable {L : Type*} [Group L] [Finite L]

theorem fusionBenderBorel_of_mulEquiv_sz {a : ℕ} (ha : 1 ≤ a) (e : L ≃* Sz a) :
    fusionBenderBorel L (2 ^ (2 * a + 1)) 2 := by
  have : Finite (Sz a) := Finite.of_equiv L e.toEquiv
  exact (bender_suzuki_borel_full a ha).map_mulEquiv e.symm

theorem fusionBenderBorel_of_mulEquiv_psu3 {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) :
    fusionBenderBorel L (2 ^ f) 3 := by
  have : Finite (PSU3 2 f) := Finite.of_equiv L e.toEquiv
  exact (bender_psu3_borel_full f hf).map_mulEquiv e.symm

variable {q k : ℕ}

theorem inf_eq_bot_of_fusionBenderBorel (hB : fusionBenderBorel L q k) {P Q : Sylow 2 L}
    (hne : P ≠ Q) : (P : Subgroup L) ⊓ Q = ⊥ :=
  (eq_bot_iff_forall _).2 fun _ hx => Omega.eq_one_of_mem_of_mem (hB P).1 hne.symm hx.1 hx.2

omit [Finite L] in
theorem sq_eq_one_of_fusionBenderBorel (hB : fusionBenderBorel L q k) (P : Sylow 2 L) {c : L}
    (hcP : c ∈ (P : Subgroup L)) (hc : c ∈ centralizer ((P : Subgroup L) : Set L)) :
    c ^ 2 = 1 :=
  (benderBorel_sylowCenter hB P).2.1 c ⟨hcP, hc⟩

theorem mem_centralizer_of_fusionBenderBorel (hB : fusionBenderBorel L q k) (hq : 2 ≤ q)
    (P : Sylow 2 L) {x : L} (hxP : x ∈ (P : Subgroup L)) (hx : x ^ 2 = 1) :
    x ∈ centralizer ((P : Subgroup L) : Set L) := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  obtain ⟨hSE, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB P
  have hZ : 1 < Nat.card (sylowCenter (P : Subgroup L)) := by
    rw [hZcard]
    omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hZ)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨g, hg, hgz⟩ := (isStronglyEmbedded_of_fusion hSE).involutions_conjugate_in
    (Subgroup.le_normalizer (sylowCenter_le _ hzZ)) ⟨hz1', hZ2 z hzZ⟩
    (Subgroup.le_normalizer hxP) ⟨hx1, hx⟩
  have hmem := conj_mem_sylowCenter hg hzZ
  rw [show g⁻¹ * z * g = x from hgz] at hmem
  exact hmem.2

theorem center_eq_bot_of_fusionBenderBorel [IsSimpleGroup L] (hB : fusionBenderBorel L q k)
    (hq : 2 ≤ q) (hk : 2 ≤ k) : center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with h | h
  · exact h
  exfalso
  obtain ⟨P⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨-, -, hZ, hP⟩ := benderBorel_sylowCenter hB P
  have hle : (P : Subgroup L) ≤ sylowCenter (P : Subgroup L) := fun x hx => by
    have hxc : x ∈ center L := by
      rw [h]
      exact mem_top x
    exact ⟨hx, Subgroup.mem_centralizer_iff.mpr fun p _ => mem_center_iff.mp hxc p⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [hZ, hP] at hcard
  have hlt := Nat.pow_lt_pow_right (show 1 < q by omega) (show 1 < k by omega)
  rw [pow_one] at hlt
  omega

end Borel

section Models

variable {L : Type*} [Group L]

theorem isBenderGroup_of_mulEquiv_sz {a : ℕ} (ha : 1 ≤ a) (e : L ≃* Sz a) :
    CFSG.BenderSuzuki.IsBenderGroup L := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr hmodel.symm))

theorem isBenderGroup_of_mulEquiv_psu3 {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) :
    CFSG.BenderSuzuki.IsBenderGroup L := by
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  exact .isPSU3 f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))

theorem exists_eq_conj_of_forall_apply_eq {L : Type} [Group L] [Finite L]
    (hL : CFSG.BenderSuzuki.IsBenderGroup L) (P : Sylow 2 L) (φ : MulAut L)
    (hφ : ∀ x ∈ (P : Subgroup L), φ x = x) :
    ∃ c ∈ (P : Subgroup L), c ∈ centralizer ((P : Subgroup L) : Set L) ∧ φ = MulAut.conj c := by
  obtain ⟨c, hcP, hc⟩ :=
    (CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFactsHold L hL P).aut_inner φ hφ
  refine ⟨c, hcP, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_, MulEquiv.ext fun x => ?_⟩
  · have h1 : c * p * c⁻¹ = p := (hc p).symm.trans (hφ p hp)
    calc p * c = c * p * c⁻¹ * c := by rw [h1]
      _ = c * p := by group
  · rw [hc x, MulAut.conj_apply]

end Models

section Count

variable {L : Type*} [Group L] [Finite L]

theorem card_sylow_eq_card_add_one_of_mulEquiv {G : Type*} [Group G] (e : L ≃* G)
    {R : Sylow 2 G} (h : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1) (P : Sylow 2 L) :
    Nat.card (Sylow 2 L) = Nat.card (P : Subgroup L) + 1 := by
  have : Finite G := Finite.of_equiv L e.toEquiv
  rw [card_sylow_eq_of_mulEquiv e 2, h, Sylow.card_eq_multiplicity R,
    Sylow.card_eq_multiplicity P, Nat.card_congr e.toEquiv]

theorem card_sylow_of_mulEquiv_sz {a : ℕ} (ha : 1 ≤ a) (e : L ≃* Sz a) (P : Sylow 2 L) :
    Nat.card (Sylow 2 L) = Nat.card (P : Subgroup L) + 1 := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  let e₂ : SuzukiMatrixGroup a ≃* Sz a :=
    (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a).symm).trans
      (MulEquiv.subgroupCongr hmodel)
  obtain ⟨S, hS⟩ := SuzukiAut.exists_sylow_eq_rootSub a (by omega)
  have h := (SuzukiAut.normalizer_and_card_sylow a (by omega)).2
  rw [← hS] at h
  exact card_sylow_eq_card_add_one_of_mulEquiv (e.trans e₂.symm) h P

omit [Finite L] in
theorem exists_mulEquiv_hermitian_of_mulEquiv_psu3 {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (J : HermitianForm 3 K),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧ Nat.card K = (2 ^ f) ^ 2 ∧
      Nat.card {x : K // J.conj x = x} = 2 ^ f ∧
      Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := CFSG.BenderSuzuki.binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    CFSG.BenderSuzuki.quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  obtain ⟨e₁⟩ :=
    CFSG.BenderSuzuki.projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed
  exact ⟨K, inferInstance, inferInstance, inferInstance, J, hJ, hKcard, hfixed,
    ⟨e.trans (e₁.trans (MulEquiv.subgroupCongr hmodel)).symm⟩⟩

theorem card_sylow_of_mulEquiv_psu3 {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) (P : Sylow 2 L) :
    Nat.card (Sylow 2 L) = Nat.card (P : Subgroup L) + 1 := by
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, ⟨e'⟩⟩ :=
    exists_mulEquiv_hermitian_of_mulEquiv_psu3 hf e
  obtain ⟨S, hS⟩ := UnitaryAut.exists_sylow_eq_root J f hf hKcard hfixed hJ
  have h := (UnitaryAut.normalizer_and_card_sylow J f hf hKcard hfixed hJ).2
  rw [← hS] at h
  exact card_sylow_eq_card_add_one_of_mulEquiv e' h P

theorem exists_mem_smul_eq_of_fusionBenderBorel {q k : ℕ} (hB : fusionBenderBorel L q k)
    {P : Sylow 2 L} (hcard : Nat.card (Sylow 2 L) = Nat.card (P : Subgroup L) + 1)
    {S₀ S : Sylow 2 L} (h₀ : S₀ ≠ P) (hS : S ≠ P) : ∃ r ∈ (P : Subgroup L), r • S₀ = S :=
  Omega.exists_smul_eq (hB P).1 hcard h₀ hS

end Count

end CFSG.ComponentClassification.Asc76X
