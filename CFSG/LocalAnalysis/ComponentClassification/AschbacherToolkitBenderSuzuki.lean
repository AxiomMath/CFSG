module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
import CFSG.Models.BenderSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

theorem nestedAt_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (T : Sylow 2 (SuzukiMatrixGroup m)) : NestedAt (T : Subgroup (SuzukiMatrixGroup m)) := by
  classical
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := fun x =>
    iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let G := SuzukiMatrixGroup m
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_, hpi_formula, hFp, _, _, _, hFcard, _, hroot_mul, hcommF, hcoord, _, _, _, _⟩
  have hF_le_G : F ≤ G := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ G := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hH_le_NF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    External.suzukiTorusClosure_le_normalizer_rootClosure m pi hpi_sq hpi_formula
  have hmemF : ∀ A : GL (Fin 4) K, A ∈ F ↔ ∃ a b : K, A = SuzukiRootGL m a b :=
    External.suzukiRootGL_mem_closure_iff m pi hpi_sq hpi_formula
  have hcenF : ∀ A : GL (Fin 4) K, A ∈ F →
      ((∀ B ∈ F, B * A = A * B) ↔ ∃ b : K, A = SuzukiRootGL m 0 b) := by
    intro A hA
    constructor
    · intro hc
      have hAc : (⟨A, hA⟩ : F) ∈ Subgroup.center F :=
        Subgroup.mem_center_iff.mpr fun B => Subtype.ext (hc B B.2)
      rw [← hcommF] at hAc
      exact (hcoord ⟨A, hA⟩).mp hAc
    · intro hb B hB
      have hAc : (⟨A, hA⟩ : F) ∈ commutator F := (hcoord ⟨A, hA⟩).mpr hb
      rw [hcommF] at hAc
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hAc ⟨B, hB⟩)
  let R : Subgroup G := F.subgroupOf G
  have hB := bender_suzukiMatrixGroup_borel m hm
  have hRp : IsPGroup 2 R := hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hF_le_G).symm
  have hRcard : Nat.card R = q ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_G).toEquiv]
    exact hFcard
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  have hSR : (S : Subgroup G) = R := by
    obtain ⟨-, -, -, hScard⟩ := benderBorel_sylowCenter hB S
    exact (Subgroup.eq_of_le_of_card_ge hRS (by rw [hScard, hRcard])).symm
  obtain ⟨hSE, hZ2, -, -⟩ := benderBorel_sylowCenter hB S
  apply nestedAt_of_one_sylow S _ T
  rw [hSR] at hSE hZ2 ⊢
  have hmemR : ∀ g : G, g ∈ R ↔ ∃ a b : K, (g : GL (Fin 4) K) = SuzukiRootGL m a b := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    exact hmemF g
  have hmemZ : ∀ g : G, g ∈ sylowCenter R ↔
      ∃ b : K, (g : GL (Fin 4) K) = SuzukiRootGL m 0 b := by
    intro g
    rw [mem_sylowCenter]
    constructor
    · rintro ⟨hgR, hgc⟩
      have hgF : (g : GL (Fin 4) K) ∈ F := hgR
      refine (hcenF _ hgF).mp fun B hB => ?_
      have := hgc ⟨B, hF_le_G hB⟩ hB
      exact congrArg Subtype.val this
    · intro hb
      have hgF : (g : GL (Fin 4) K) ∈ F := by
        obtain ⟨b, hb⟩ := hb
        exact (hmemF _).mpr ⟨0, b, hb⟩
      refine ⟨hgF, fun t ht => Subtype.ext ((hcenF _ hgF).mpr hb t ht)⟩
  have hZT : sylowCenter R ≤ ⁅R, R⁆ := by
    intro g hg
    have hgR : g ∈ R := sylowCenter_le R hg
    let eR : R ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_G
    have hgF : (eR ⟨g, hgR⟩ : F) ∈ commutator F := by
      rw [hcommF]
      refine Subgroup.mem_center_iff.mpr fun B => Subtype.ext ?_
      have := (mem_sylowCenter.mp hg).2 ⟨B, hF_le_G B.2⟩ B.2
      change (B : GL (Fin 4) K) * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (B : GL (Fin 4) K)
      exact congrArg Subtype.val this
    have hcommR : (commutator F).map eR.symm.toMonoidHom = commutator R := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ eR.symm.surjective]
    have h1 : (⟨g, hgR⟩ : R) ∈ commutator R := by
      rw [← hcommR]
      exact ⟨eR ⟨g, hgR⟩, hgF, by simp⟩
    have h2 : (commutator R).map R.subtype = ⁅R, R⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h2]
    exact ⟨⟨g, hgR⟩, h1, rfl⟩
  have hroot_inv : ∀ a b : K, (SuzukiRootGL m a b)⁻¹ = SuzukiRootGL m a (b + a * pi a) := by
    intro a b
    apply inv_eq_of_mul_eq_one_right
    rw [hroot_mul]
    have h1 : a + a = 0 := CharTwo.add_self_eq_zero a
    have h2 : b + (b + a * pi a) + a * pi a = 0 := by
      have := CharTwo.add_self_eq_zero b
      have := CharTwo.add_self_eq_zero (a * pi a)
      calc b + (b + a * pi a) + a * pi a = (b + b) + (a * pi a + a * pi a) := by ring
        _ = 0 := by simp only [CharTwo.add_self_eq_zero]
    rw [h1, h2]
    exact External.suzukiRootGL_zero_zero m
  have hfirst : ∀ a b a' b' : K, SuzukiRootGL m a b = SuzukiRootGL m a' b' → a = a' := by
    intro a b a' b' h
    have h02 := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) 0 1) h
    simpa [SuzukiRootGL, SuzukiRootMatrix] using h02
  have htrans : ∀ x ∈ R, x ∉ sylowCenter R → ∀ y ∈ R, y ∉ sylowCenter R →
      ∃ n ∈ Subgroup.normalizer (R : Set G), n⁻¹ * x * n * y⁻¹ ∈ sylowCenter R := by
    intro x hx hxZ y hy hyZ
    obtain ⟨a, b, hab⟩ := (hmemR x).mp hx
    obtain ⟨a', b', hab'⟩ := (hmemR y).mp hy
    have ha : a ≠ 0 := by
      rintro rfl
      exact hxZ ((hmemZ x).mpr ⟨b, hab⟩)
    have ha' : a' ≠ 0 := by
      rintro rfl
      exact hyZ ((hmemZ y).mpr ⟨b', hab'⟩)
    let u : Kˣ := Units.mk0 (a' / a) (div_ne_zero ha' ha)
    have huH : SuzukiTorusGL m u ∈ H := Subgroup.subset_closure ⟨u, rfl⟩
    let n : G := ⟨(SuzukiTorusGL m u)⁻¹, G.inv_mem (hH_le_G huH)⟩
    have hnN : n ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro r
      have hNF := Subgroup.mem_normalizer_iff.mp (hH_le_NF (H.inv_mem huH)) (r : GL (Fin 4) K)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hNF
    refine ⟨n, hnN, (hmemZ _).mpr ?_⟩
    have hconj := External.suzukiTorusGL_conj_root m pi hpi_sq hpi_formula a b u
    have hua : (u : K) * a = a' := div_mul_cancel₀ a' ha
    refine ⟨(u : K) * pi (u : K) * b + (b' + a' * pi a') + a' * pi a', ?_⟩
    change (SuzukiTorusGL m u)⁻¹⁻¹ * (x : GL (Fin 4) K) * (SuzukiTorusGL m u)⁻¹ *
      (y : GL (Fin 4) K)⁻¹ = _
    rw [inv_inv, hab, hconj, hab', hroot_inv, hroot_mul, hua, CharTwo.add_self_eq_zero]
  exact nestedAt_of_coset_transitive hSE hZ2 hZT htrans

theorem nestedAt_of_mulEquiv_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  let e' : SuzukiMatrixGroup a ≃* Sz a :=
    (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a).symm).trans
      (MulEquiv.subgroupCongr hmodel)
  let e'' : X ≃* SuzukiMatrixGroup a := e.trans e'.symm
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e'' e''.surjective
  exact nestedAt_of_mulEquiv e'' (nestedAt_suzukiMatrixGroup a (by omega)) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
