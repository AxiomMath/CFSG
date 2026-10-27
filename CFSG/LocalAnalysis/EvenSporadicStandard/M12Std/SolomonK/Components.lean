module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Step1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.ComponentCount
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Assembly.OrderReductions.PermutationReduction
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Comp

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.SectionRank

variable {K : Type} [Group K] [Finite K]

theorem exists_component (hP : P12Facts) (hK : SolomonA12HypK K) :
    ∃ L : Subgroup K, CFSG.IsComponent L := by
  by_contra hno
  push Not at hno
  have hlayer : layer K = ⊥ := by
    rw [layer.eq_sSup]
    exact le_antisymm (sSup_le fun L hL => (hno L hL).elim) bot_le
  have hpCore_bot : pCore 2 K = ⊥ :=
    eq_bot_of_normal_isPGroup hP hK (Q := pCore 2 K) inferInstance pCore_isPGroup
  have hodd_bot : oddCore K = ⊥ :=
    hK.fusionSimple.1 (oddCore K) (CFSG.oddCore_normal (G := K))
      (CFSG.ABGLocalTools.odd_card_oddCore (H := K))
  have hfit_bot : fittingSubgroup K = ⊥ := by
    have hle := CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore (G := K)
    rw [hpCore_bot, hodd_bot, bot_sup_eq] at hle
    exact le_bot_iff.mp hle
  have hgf_bot : generalizedFitting K = ⊥ := by
    rw [generalizedFitting.eq_sup, hfit_bot, hlayer, bot_sup_eq]
  have hcent := CFSG.centralizer_generalizedFitting_le K
  rw [hgf_bot] at hcent
  have hbot1 : ∀ x : K, x = 1 := by
    intro x
    have hx : x ∈ Subgroup.centralizer ((⊥ : Subgroup K) : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1, one_mul, mul_one]
    exact Subgroup.mem_bot.mp (hcent hx)
  have hsub : Subsingleton K := ⟨fun a b => by rw [hbot1 a, hbot1 b]⟩
  have hcard1 : Nat.card K = 1 := by
    have hle : Nat.card K ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have hpos : 0 < Nat.card K := Finite.card_pos_iff.mpr ⟨1⟩
    omega
  have h9 := two_part_card hP hK
  rw [hcard1] at h9
  simp [Nat.factorization_one] at h9

theorem card_componentIndex_le_four (hP : P12Facts) (hK : SolomonA12HypK K) :
    Nat.card (ComponentIndex K) ≤ 4 := by
  by_contra h
  rw [not_le] at h
  have hdiv : 2 ^ 10 ∣ Nat.card K := by
    have h2 : 2 ^ 10 ∣ 4 ^ Nat.card (ComponentIndex K) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact h2.trans (four_pow_dvd_card K)
  have hne : Nat.card K ≠ 0 := (Finite.card_pos_iff.mpr ⟨1⟩).ne'
  have hle : 10 ≤ (Nat.card K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdiv
  have h9 := two_part_card hP hK
  omega

theorem component_splits_of_card_le_four {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hK : IsKGroupCat X) (hS : SchreierFor Catalog)
    (hcard : Nat.card (ComponentIndex X) ≤ 4) (hZ : center X = ⊥)
    (L : Subgroup X) (hL : CFSG.IsComponent L) :
    L.Normal ∧ IsSimpleGroup ↥L ∧ ∃ C : Subgroup X, C.Normal ∧ Disjoint L C ∧ L ⊔ C = ⊤ ∧
      ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := by
  classical
  haveI : Group.IsSolvable (Equiv.Perm (CFSG.LocalCores.ComponentIndex X)) :=
    CFSG.OrderReductions.PermutationReduction.permutation_solvable_of_card_le_four _ hcard
  let P : X →* Equiv.Perm (CFSG.LocalCores.ComponentIndex X) :=
    MulAction.toPermHom X (CFSG.LocalCores.ComponentIndex X)
  haveI : Group.IsPerfect P.range := Group.IsPerfect.range P
  have hrange_self : ⁅P.range, P.range⁆ = P.range := Subgroup.commutator_eq_self
  have hrange_bot : P.range = ⊥ := by
    by_contra hne
    have hlt : ⁅P.range, P.range⁆ < P.range :=
      Group.IsSolvable.commutator_lt_of_ne_bot
        (G := Equiv.Perm (CFSG.LocalCores.ComponentIndex X)) (H := P.range) hne
    rw [hrange_self] at hlt
    exact (lt_irrefl P.range) hlt
  have hPone : ∀ x : X, P x = 1 := by
    intro x
    have hx : P x ∈ P.range := ⟨x, rfl⟩
    rw [hrange_bot] at hx
    simpa using hx
  have hLmap : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L := by
    intro x
    have hfix : x • (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex X) = ⟨L, hL⟩ := by
      have h := DFunLike.congr_fun (hPone x) (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex X)
      simpa [P] using h
    have hfix' : (x • (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex X)).1 = L :=
      congrArg Subtype.val hfix
    simpa [CFSG.GH74.GLS.Stage2.Bender.Thm1.smul_component_val] using hfix'
  have hLnorm : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [hLmap g] at hmem
  haveI : L.Normal := hLnorm
  haveI hPerfectL : Group.IsPerfect ↥L := hL.1.1
  haveI hSimpleQuot : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hCatalog : CFSG.Blueprint.Catalog (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK L
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
  haveI hOuterQuot : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥L ⧸ Subgroup.center ↥L)) :=
    hS (↥L ⧸ Subgroup.center ↥L) hL.1.2.2 hCatalog
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥L
  have hsup : L ⊔ Subgroup.centralizer (L : Set X) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hnormalizes : (⊤ : Subgroup X) ≤ Subgroup.normalizer (L : Set X) :=
      le_of_eq (Subgroup.normalizer_eq_top L).symm
    obtain ⟨implementer, himpl, haction⟩ :=
      CFSG.ComponentClassification.ComponentInnerActions.perfect_normalizer_action_inner
        (G := X) (⊤ : Subgroup X) L hnormalizes (⟨x, trivial⟩ : (⊤ : Subgroup X))
    have haction' : ∀ member ∈ L,
        x * member * x⁻¹ = implementer * member * implementer⁻¹ := haction
    refine Subgroup.mem_sup_of_normal_left.mpr
      ⟨implementer, himpl, implementer⁻¹ * x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro member hmemb
      have key : implementer⁻¹ * x * member = member * implementer⁻¹ * x := by
        calc implementer⁻¹ * x * member
            = implementer⁻¹ * (x * member * x⁻¹) * x := by group
          _ = implementer⁻¹ * (implementer * member * implementer⁻¹) * x := by
                rw [haction' member hmemb]
          _ = member * implementer⁻¹ * x := by group
      simpa only [mul_assoc] using key.symm
    · group
  have hcenterL : Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply Subtype.ext
    have hzX : (z : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by rw [hsup]; trivial
      obtain ⟨l, hl, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      have hzl : l * (z : X) = (z : X) * l := by
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨l, hl⟩ : ↥L))
      have hzc : (z : X) * c = c * (z : X) :=
        Subgroup.mem_centralizer_iff.mp hc (z : X) z.property
      rw [← hlc]
      calc (l * c) * (z : X) = l * (c * (z : X)) := by group
        _ = l * ((z : X) * c) := by rw [hzc]
        _ = (l * (z : X)) * c := by group
        _ = ((z : X) * l) * c := by rw [hzl]
        _ = (z : X) * (l * c) := by group
    have hz1 : (z : X) = 1 := by
      rw [hZ] at hzX
      simpa using hzX
    simpa using hz1
  have hsimpleL : IsSimpleGroup ↥L := by
    have e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hcenterL).trans QuotientGroup.quotientBot
    exact e.symm.isSimpleGroup
  refine ⟨hLnorm, hsimpleL, Subgroup.centralizer (L : Set X), ?_, ?_, hsup, ?_⟩
  · exact Subgroup.normal_centralizer
  · rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgL, hgC⟩ := hg
    have hz : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hyc : (y : X) * g = g * (y : X) :=
        Subgroup.mem_centralizer_iff.mp hgC (y : X) y.property
      simpa using hyc
    rw [hcenterL] at hz
    have hg1 : (⟨g, hgL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hz
    simpa using congrArg Subtype.val hg1
  · intro l hl c hc
    exact Subgroup.mem_centralizer_iff.mp hc l hl

theorem exists_split (hSch : SchreierFor Catalog) (hP : P12Facts) (hKg : IsKGroupCat K)
    (hK : SolomonA12HypK K) :
    ∃ L C : Subgroup K, L.Normal ∧ IsSimpleGroup ↥L ∧ (∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) ∧
      C.Normal ∧ Disjoint L C ∧ L ⊔ C = ⊤ ∧ ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := by
  haveI : Group.IsPerfect K := isPerfect_of_hyp hP hK
  obtain ⟨L, hL⟩ := exists_component hP hK
  have hcard : Nat.card (ComponentIndex K) ≤ 4 := card_componentIndex_le_four hP hK
  have hZ : center K = ⊥ := hK.fusionSimple.2.1
  obtain ⟨hLnorm, hLsimple, C, hCnorm, hdisj, hsup, hcomm⟩ :=
    component_splits_of_card_le_four hKg hSch hcard hZ L hL
  have hnonab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨(a' : K), a'.2, (b' : K), b'.2, ?_⟩
    intro h
    apply hab
    have hq : (a' * b' : ↥L) = b' * a' := Subtype.ext (by simpa using h)
    simpa using congrArg (fun z : ↥L => (z : ↥L ⧸ Subgroup.center ↥L)) hq
  exact ⟨L, C, hLnorm, hLsimple, hnonab, hCnorm, hdisj, hsup, hcomm⟩

end CFSG.EvenSporadicStandard.M12Std.SolomonK
