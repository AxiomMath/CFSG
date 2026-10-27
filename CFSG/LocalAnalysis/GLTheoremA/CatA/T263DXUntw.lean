module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXLangSel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXPBig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner
import CFSG.GroupTheory.QuasisimpleCenterDivisibility

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem comap_act_of_map {C G : Type*} [Group C] [Group G] (ι : C →* G)
    (hι : Function.Injective ι) {F P : Subgroup C} {R : Subgroup G} (hRF : R ≤ F.map ι)
    (hact : ⁅P.map ι, R⁆ ≠ ⊥) (hinn : P.map ι ≤ R ⊔ (F.map ι ⊓ Subgroup.centralizer (R : Set G))) :
    ⁅P, R.comap ι⁆ ≠ ⊥ ∧
      P ≤ R.comap ι ⊔ (F ⊓ Subgroup.centralizer ((R.comap ι : Subgroup C) : Set C)) := by
  have hJ : (R.comap ι).map ι = R :=
    Subgroup.map_comap_eq_self (hRF.trans (Subgroup.map_le_range ι F))
  refine ⟨fun h0 => hact ?_, fun x hx => ?_⟩
  · have h1 := congrArg (Subgroup.map ι) h0
    rwa [Subgroup.map_commutator, hJ, Subgroup.map_bot] at h1
  · have hx' : ι x ∈ (R.comap ι ⊔
        (F ⊓ Subgroup.centralizer ((R.comap ι : Subgroup C) : Set C))).map ι := by
      rw [Subgroup.map_sup, hJ]
      refine sup_le_sup_left ?_ R (hinn (Subgroup.mem_map_of_mem ι hx))
      rintro _ ⟨⟨c, hcF, rfl⟩, hcR⟩
      refine ⟨c, ⟨hcF, Subgroup.mem_centralizer_iff.2 fun j hj => hι ?_⟩, rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.1 hcR (ι j) hj
    exact (Subgroup.mem_map_iff_mem hι).1 hx'

section LangSel

open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (isComponentOf_comap_of_injective map_fixSubgroup_eq_of_conj)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (open_isQuasisimple)


theorem exists_comp_of_langSetup_two {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    (hq4 : 4 ≤ S.D.q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ S.D.q ^ 2 - 1)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1) {C : Type*} [Group C] [Finite C]
    (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (P : Subgroup C) (hPβ : P ≤ fixSubgroup β) (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ J : Subgroup C, IsComponentOf J (fixSubgroup β) ∧
      p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (J : Set C)) := by
  classical
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hP' : P.map ι ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.map_mono hPβ
  obtain ⟨i, hiq, hact, hinn⟩ := langSel_of_q4 hK2 S hq4 hp hp2 hT hap h1 (P.map ι) hP'
    (hP2.map ι) (fun h0 => hP1 ((Subgroup.map_eq_bot_iff_of_injective P hι).1 h0))
  have hbig := pBigComponents_of_dvd_sq_sub_one S hT h1 hp hp2 hpq hq4 i
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
  generalize rationalComponent S.ρ S.Γ (rootCharHom a) i = R at hiq hact hinn hbig hle hsub
  rw [← hfix] at hle hinn hsub
  have hFrange : (fixSubgroup β).map ι ≤ ι.range := Subgroup.map_le_range ι _
  have hRrange : R ≤ ι.range := hle.trans hFrange
  have hcomp : IsComponentOf (R.comap ι) (fixSubgroup β) := by
    have h := isComponentOf_comap_of_injective ι hι hRrange hFrange
      ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hiq⟩
    rwa [Subgroup.comap_map_eq_self_of_injective hι] at h
  have hJ : (R.comap ι).map ι = R := Subgroup.map_comap_eq_self hRrange
  let e : ↥(R.comap ι) ≃* ↥R :=
    (Subgroup.equivMapOfInjective (R.comap ι) ι hι).trans (MulEquiv.subgroupCongr hJ)
  have hJq : CFSG.IsQuasisimple ↥(R.comap ι) := CFSG.IsQuasisimple.of_mulEquiv e hiq
  have hpR : p ∣ Nat.card ↥R := by
    by_contra h
    exact hbig ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  have hpJ : p ∣ Nat.card ↥(R.comap ι) := by
    rw [Nat.card_congr e.toEquiv]
    exact hpR
  obtain ⟨hact', hinn'⟩ := comap_act_of_map ι hι hle hact hinn
  exact ⟨R.comap ι, hcomp, CFSG.dvd_card_quotient_center_of_quasisimple hJq hp hpJ, hact', hinn'⟩

end LangSel


theorem exists_comp_of_two_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K ^ 2 - 1) (β : MulAut ↥(adjointGroup τ K))
    (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K)) (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    (P : Subgroup ↥(adjointGroup τ K)) (hPβ : P ≤ fixSubgroup β) (hP2 : IsPGroup 2 ↥P)
    (hP1 : P ≠ ⊥) :
    ∃ J : Subgroup ↥(adjointGroup τ K), IsComponentOf J (fixSubgroup β) ∧
      p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (J : Set ↥(adjointGroup τ K))) := by
  open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
    CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.GLTheoremA.S267.Gen in
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK, hK2]
  have hpK : ¬ p ∣ Nat.card K := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (hK ▸ hd)))
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    exists_inndiag_of_mem_innAutDerived_untw hτ (fun _ => by omega) hp β hβmem hβp hβ1
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' | h'
    · subst h'
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
        (by omega)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h'])
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ hp hpK (Or.inr hK4) hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  exact exists_comp_of_langSetup_two hK2 S (by rw [hSq]; exact hK4) hp hp2
    (by rw [hSq]; exact hpq) hT hap h1 ι hinj hrange β hconj P hPβ hP2 hP1

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
