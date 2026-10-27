module

public import CFSG.GH74.Generic.BProg.B1.Shapes
public import CFSG.GH74.Generic.BProg.B1.PilotS5
public import CFSG.GH74.Generic.BProg.B1.PilotS1Facts
public import CFSG.GH74.Generic.BProg.B1.PilotS1Models
public import CFSG.GH74.Generic.Frame
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage2.Final.ModelFam
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.NS.Leaf
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5

section Gen

theorem card_map_eq_of_inj {G N : Type*} [Group G] [Group N] (π : G →* N) (S : Subgroup G)
    (h : ∀ s ∈ S, π s = 1 → s = 1) : Nat.card ↥(S.map π) = Nat.card ↥S := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun s : S => (⟨π s, Subgroup.mem_map_of_mem _ s.2⟩ : S.map π)) ⟨?_, ?_⟩).symm
  · intro a b hab
    have h1 : π ((a : G)⁻¹ * b) = 1 := by
      have := congrArg Subtype.val hab
      simp only at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have h2 : (a : G)⁻¹ * b = 1 := h _ (S.mul_mem (S.inv_mem a.2) b.2) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem exists_lift_elementaryAbelian_pow {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H)
    {p : ℕ} (hp : p.Prime) (hker : ¬ p ∣ Nat.card ρ.ker) (E : Subgroup H) (hE : E ≤ ρ.range)
    [IsElementaryAbelian p E] {k : ℕ} (hEcard : Nat.card E = p ^ k) :
    ∃ E₀ : Subgroup G, IsElementaryAbelian p E₀ ∧ Nat.card E₀ = p ^ k ∧ E₀.map ρ = E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero k hp.ne_zero)
  set P' : Subgroup G := E.comap ρ with hP'
  let f : P' →* E := (ρ.comp P'.subtype).codRestrict E fun x => x.2
  have hfsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg⟩ := hE e.2
    exact ⟨⟨g, show ρ g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  have hfx : ∀ x : P', (f x : H) = ρ x := fun x => rfl
  have hkerf : Nat.card f.ker = Nat.card ρ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h2 := congrArg Subtype.val this
      rwa [hfx] at h2
    · show ρ x.1 ∈ E
      rw [MonoidHom.mem_ker.mp x.2]; exact E.one_mem
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfx]
      exact MonoidHom.mem_ker.mp x.2
    · intro x; rfl
    · intro x; rfl
  have hPc : Nat.card P' = Nat.card ρ.ker * p ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hEcard,
      hkerf] at h1
    rw [h1, mul_comm]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P'))
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPc, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero k hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp]
    simp
  have hSinj : ∀ x ∈ S.map P'.subtype, ∀ y ∈ S.map P'.subtype, ρ x = ρ y → x = y := by
    have key : ∀ x ∈ S.map P'.subtype, ρ x = 1 → x = 1 := by
      intro x hx hρx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have h1 : orderOf (x' : G) ∣ p ^ k := by
        rw [← hScard]
        have := Subgroup.orderOf_dvd_natCard (S : Subgroup P') hx'
        simpa [Subgroup.orderOf_coe] using this
      have h2 : orderOf (x' : G) ∣ Nat.card ρ.ker := by
        have hmem : (x' : G) ∈ ρ.ker := hρx
        have := Subgroup.orderOf_dvd_natCard ρ.ker hmem
        simpa [Subgroup.orderOf_coe] using this
      have hcop : Nat.Coprime (p ^ k) (Nat.card ρ.ker) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := key _ (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  set E₀ : Subgroup G := S.map P'.subtype with hE₀
  have hE₀card : Nat.card E₀ = p ^ k := by
    rw [hE₀, Subgroup.card_map_of_injective P'.subtype_injective, hScard]
  have hmapE : E₀.map ρ = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      exact g'.2
    · have : Nat.card (E₀.map ρ) = Nat.card E₀ := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : E₀ => ⟨ρ x, Subgroup.mem_map_of_mem _ x.2⟩) ⟨?_, ?_⟩).symm
        · intro x y hxy
          exact Subtype.ext (hSinj _ x.2 _ y.2 (congrArg Subtype.val hxy))
        · rintro ⟨_, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
      rw [this, hE₀card, hEcard]
  refine ⟨E₀, ?_, hE₀card, hmapE⟩
  have hEx : ∀ x ∈ E₀, ρ x ∈ E := fun x hx => hmapE ▸ Subgroup.mem_map_of_mem _ hx
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exponent_dvd_p := ?_ }
  · apply hSinj _ (Subgroup.mul_mem _ a.2 b.2) _ (Subgroup.mul_mem _ b.2 a.2)
    have := (IsMulCommutative.is_comm (M := E)).comm ⟨ρ a, hEx _ a.2⟩ ⟨ρ b, hEx _ b.2⟩
    simpa using congrArg Subtype.val this
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
    apply hSinj _ (Subgroup.pow_mem _ x.2 p) _ (Subgroup.one_mem _)
    have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (ρ x) (hEx _ x.2)
    simpa using this

end Gen

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem exists_source_of_model {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) {P : Type} [Group P]
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* P) {F' : Type} [Field F'] [Finite F'] {z₀ : P}
    (hP : GrpS1 F' P z₀) (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ A : Subgroup G, IsSource2 x K A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀, hc₀⟩ := hP.exists_e8
  set V : Subgroup (↥K ⧸ pPrimeCore 2 ↥K) := E₀.map e.symm.toMonoidHom with hV
  have hVel : CFSG.IsElementaryAbelian 2 ↥V := IsElementaryAbelian.map _
  have hVc : Nat.card ↥V = 2 ^ 3 := by
    rw [hV, Subgroup.card_map_of_injective e.symm.injective, hc₀]
    norm_num
  set π : ↥K →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 CFSG.pPrimeCore_coprime_card
  have hVr : V ≤ π.range := by
    rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨P', hP'el, hP'c, -⟩ := exists_lift_elementaryAbelian_pow π Nat.prime_two hker V hVr hVc
  set A : Subgroup G := P'.map K.subtype with hA
  have hAK : A ≤ K := Subgroup.map_subtype_le _
  refine ⟨A, hAK.trans hK.1, IsElementaryAbelian.map_subtype, ?_, Or.inl ⟨hAK, h1⟩⟩
  rw [hA, Subgroup.card_map_of_injective K.subtype_injective, hP'c]
  norm_num

theorem eq_one_of_proj_eq_one {x : G} {g : ↥(centralizer ({x} : Set G))} (hg : g * g = 1)
    (h : proj x g = 1) : g = 1 := by
  have hodd := proj_odd x g h
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
  have : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 this

theorem eq_of_proj_eq {x a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) (hab : a * b = b * a) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (h : proj x ⟨a, ha⟩ = proj x ⟨b, hb⟩) : a = b := by
  set ga : ↥(centralizer ({x} : Set G)) := ⟨a, ha⟩ with hga
  set gb : ↥(centralizer ({x} : Set G)) := ⟨b, hb⟩ with hgb
  have hcomm : ga * gb = gb * ga := Subtype.ext hab
  have hga2 : ga * ga = 1 := Subtype.ext ha2
  have hgb2 : gb * gb = 1 := Subtype.ext hb2
  have hg2 : (ga⁻¹ * gb) * (ga⁻¹ * gb) = 1 := by
    have h1 : Commute ga⁻¹ gb := (Commute.inv_left hcomm)
    have h2 : (ga⁻¹ * gb) ^ 2 = 1 := by
      rw [h1.mul_pow, inv_pow, pow_two ga, hga2, pow_two gb, hgb2]
      simp
    rwa [pow_two] at h2
  have hg1 : proj x (ga⁻¹ * gb) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have := eq_one_of_proj_eq_one hg2 hg1
  have h3 : ga = gb := inv_mul_eq_one.1 this
  exact congrArg Subtype.val h3

theorem exists_y_of_e8 {x : G} {K A : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (he8 : ∀ E : Subgroup (CentralizerBar x), E ≤ imgBar x K → CFSG.IsElementaryAbelian 2 ↥E →
      Nat.card ↥E = 8 → xbar x ∈ E)
    (hAK : A ≤ K) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) :
    x ∈ A ∧ ∃ y : G, y ∈ A ∧ y ∈ K ∧ y ∈ centralizer ({x} : Set G) ∧ orderOf y = 2 ∧
      x * y = y * x ∧ x ≠ y ∧ bar x y ∈ imgBar x K ∧ orderOf (bar x y) = 2 ∧
      bar x y ∉ zpowers (xbar x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
  have hAC : A ≤ centralizer ({x} : Set G) := hAK.trans hKC
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
  set Ab : Subgroup (CentralizerBar x) := imgBar x A with hAb
  have hAbS : Ab ≤ imgBar x K := imgBar_mono x hAK
  have hAbel : CFSG.IsElementaryAbelian 2 ↥Ab := by
    have : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf (centralizer ({x} : Set G))) :=
      IsElementaryAbelian.subgroupOf hAC
    exact IsElementaryAbelian.map (proj x)
  have hAbc : Nat.card ↥Ab = 8 := by
    rw [hAb, imgBar, card_map_eq_of_inj, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv,
      hA8]
    intro g hg hg1
    exact eq_one_of_proj_eq_one (Subtype.ext (hAsq g hg)) hg1
  have hxbarAb : xbar x ∈ Ab := he8 Ab hAbS hAbel hAbc
  have hxA : x ∈ A := by
    obtain ⟨g, hgA, hgx⟩ := mem_imgBar.1 hxbarAb
    have hxeq : proj x ⟨x, hxC⟩ = proj x g := hgx.symm
    have := eq_of_proj_eq hxC g.2 (Subgroup.mem_centralizer_singleton_iff.1 g.2).symm hx2
      (hAsq g hgA) hxeq
    rw [this]
    exact hgA
  refine ⟨hxA, ?_⟩
  obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ∉ zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ zpowers x := hcon
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hx, hA8] at this
    omega
  have hyK : y ∈ K := hAK hyA
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hy2sq : y * y = 1 := hAsq y hyA
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2sq) hy1
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxyne : x ≠ y := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  obtain ⟨hbmem, hbne, hb2⟩ := bar_facts hKC hyK hy2
  have hyne : bar x y ∉ zpowers (xbar x) := by
    intro hmem
    rcases mem_zpowers_of_two (PilotS5.orderOf_xbar hx) hmem with h | h
    · exact hbne h
    · have h1 : proj x ⟨x, hxC⟩ = proj x ⟨y, hyC⟩ := by
        rw [← bar_of_mem hyC, h]; rfl
      exact hxyne (eq_of_proj_eq hxC hyC hxy hx2 hy2sq h1)
  exact ⟨y, hyA, hyK, hyC, hy2, hxy, hxyne, hbmem, hb2, hyne⟩

theorem D_facts {x y : G} {A : Subgroup G} (hx : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : x * y = y * x) (hxyne : x ≠ y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hAC : A ≤ centralizer ({x} : Set G)) :
    closure ({x, y} : Set G) ≤ A ∧ closure ({x, y} : Set G) ≤ centralizer ({x} : Set G) ∧
      CFSG.IsElementaryAbelian 2 ↥(closure ({x, y} : Set G)) ∧
      2 ≤ pRank 2 ↥(closure ({x, y} : Set G)) ∧
      closure ({x, y} : Set G) ≤ centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨-, hDel, hD4⟩ := closure_pair_facts hx hy2 hxy hxyne
  have hDA : closure ({x, y} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact hxA
    · rw [Set.mem_singleton_iff.1 h]; exact hyA
  refine ⟨hDA, hDA.trans hAC, hDel, ?_, fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(closure ({x, y} : Set G)))).comm
      ⟨b, hb⟩ ⟨a, ha⟩)⟩
  have := CFSG.pRank_eq_of_card_eq_pow (A := ↥(closure ({x, y} : Set G))) Nat.one_lt_two (k := 2)
    (by rw [hD4]; norm_num)
  omega

omit [Finite G] in
theorem centralizes_Dbar {x y : G} {J : Subgroup (CentralizerBar x)}
    (hyC : y ∈ centralizer ({x} : Set G))
    (hJ : J ≤ centralizer ({bar x y} : Set (CentralizerBar x))) :
    J ≤ centralizer ((imgBar x (closure ({x, y} : Set G)) : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) := by
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set Q : Subgroup G := ((centralizer (J : Set (CentralizerBar x))).comap (proj x)).map
    (centralizer ({x} : Set G)).subtype with hQ
  have hxQ : x ∈ Q := ⟨⟨x, hxC⟩, by
    show proj x ⟨x, hxC⟩ ∈ centralizer (J : Set (CentralizerBar x))
    exact Subgroup.mem_centralizer_iff.2 fun l _ =>
      (Subgroup.mem_center_iff.1 (xbar_mem_center x)) l, rfl⟩
  have hyQ : y ∈ Q := ⟨⟨y, hyC⟩, by
    show proj x ⟨y, hyC⟩ ∈ centralizer (J : Set (CentralizerBar x))
    rw [← bar_of_mem hyC]
    exact Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hJ hl), rfl⟩
  have hDQ : closure ({x, y} : Set G) ≤ Q := by
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact hxQ
    · rw [Set.mem_singleton_iff.1 h]; exact hyQ
  intro l hl
  refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
  obtain ⟨c', hc', rfl⟩ := hg
  obtain ⟨c'', hc'', hcc⟩ := hDQ hc'
  have : c'' = c' := Subtype.ext hcc
  subst this
  exact (Subgroup.mem_centralizer_iff.1 hc'' l hl).symm

theorem exists_adm_of_split1 {x : G} {K A : Subgroup G} {F' : Type} [Field F'] [Finite F']
    (hodd : Odd (Nat.card F')) (hbig : 4 ≤ Nat.card F') (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split1Like F' (imgBar x K) (xbar x))
    (hCY : ∀ w ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
      w = 1 ∨ w = xbar x)
    (he8 : ∀ E : Subgroup (CentralizerBar x), E ≤ imgBar x K → CFSG.IsElementaryAbelian 2 ↥E →
      Nat.card ↥E = 8 → xbar x ∈ E)
    (hAK : A ≤ K) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  classical
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨hxA, y, hyA, hyK, hyC, hy2, hxy, hxyne, hbmem, hb2, hyne⟩ :=
    exists_y_of_e8 hx hK he8 hAK hAel hA8
  obtain ⟨J₁, J₂, hS⟩ := hY.split (bar x y) hbmem hb2 (fun h => hyne (h ▸ Subgroup.mem_zpowers _))
  obtain ⟨hDA, hDC, hDel, hDrank, hDcomm⟩ := D_facts hx hy2 hxy hxyne hxA hyA (hAK.trans hKC)
  have hLD := centralizes_Dbar hyC (fun l hl => (hS.le₁ hl).1)
  have hLself : pLayerOf 2 (centralizer ((imgBar x (closure ({x, y} : Set G)) :
      Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ⊓ J₁) = J₁ := by
    rw [inf_eq_right.2 hLD]
    exact le_antisymm (sSup_le fun L' hL' => hL'.1) (le_sSup (hS.isPCompIn_self₁ hodd hbig))
  refine ⟨y, J₁, ⟨⟨hyC, hy2, hyne, hY.subtermRel hodd hbig hCY hbmem hS,
    fun _ => ⟨hS.isPCompIn₁ hodd hbig, fun L' hL' _ => hS.card_le_of_isPCompIn hodd hbig hL'⟩⟩,
    closure ({x, y} : Set G), J₁, ⟨hDA, hDel, hDrank⟩, Or.inl ⟨⟨hyC, hy2, hyne, hDC, hDel,
      fun d hd => Subgroup.le_normalizer hd, ?_⟩, Subgroup.le_normalizer hyK,
      hS.pLayerOf_ne_bot hodd hbig, hS.isPCompIn₁ hodd hbig, ?_⟩⟩⟩
  · rw [inf_eq_left.2 hDcomm]
    exact hDrank
  · rw [hLself]
    exact hS.isPCompIn_self₁ hodd hbig

end GLevel

theorem QShape1Big.qShape1 {Kt : Type} [Group Kt] (h : QShape1Big Kt) : QShape1 Kt := by
  rcases h with ⟨F, _, _, hF, -, e⟩ | ⟨q, F, _, _, hF, hq, e⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, hF, e⟩
  · exact Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq, e⟩

theorem exists_grpS1_of_shape1 {Kt : Type} [Group Kt] (h : QShape1 Kt) :
    ∃ (P : Type) (_ : Group P) (F' : Type) (_ : Field F') (_ : Finite F') (z : P),
      Nonempty (Kt ≃* P) ∧ GrpS1 F' P z := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · obtain ⟨z, hz⟩ := grpS1_lin hF
    exact ⟨_, inferInstance, F, inferInstance, inferInstance, z, ⟨e⟩, hz⟩
  · obtain ⟨F', _, _, -, z, hz⟩ := grpS1_uni hF hq
    exact ⟨_, inferInstance, F', inferInstance, inferInstance, z, ⟨e⟩, hz⟩

section GLevel2

variable {G : Type} [Group G] [Finite G]

theorem shape1_data {x : G} {K : Subgroup G} (hG : Gen4 G) (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) {P : Type} [Group P]
    (eP : (↥K ⧸ pPrimeCore 2 ↥K) ≃* P) {F' : Type} [Field F'] [Finite F'] {z₀ : P}
    (hP : GrpS1 F' P z₀) (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) :
    x ∈ K ∧ IsQuasisimple ↥(imgBar x K) ∧ Nat.card ↥(center ↥(imgBar x K)) = 2 ∧
      Split1Like F' (imgBar x K) (xbar x) ∧
      (∀ w ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
        w = 1 ∨ w = xbar x) ∧
      (∀ E : Subgroup (CentralizerBar x), E ≤ imgBar x K → CFSG.IsElementaryAbelian 2 ↥E →
        Nat.card ↥E = 8 → xbar x ∈ E) := by
  obtain ⟨eK⟩ := hat_equiv_imgBar hK
  have hS : IsSL4Model ↥(imgBar x K) := IsSL4Model.of_mulEquiv h1 eK
  have hxbar : xbar x ∈ imgBar x K := xbar_mem_of_isSL4Model hG hx hS
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxK : x ∈ K := by
    have h2 : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ 1) = 1 := by
      apply Subtype.ext
      simpa using (by rw [← hx]; exact pow_orderOf_eq_one x : x ^ 2 = 1)
    exact Subgroup.mem_subgroupOf.1 (mem_of_two_pow_eq_one_of_map_mem hK.2 h2 hxbar)
  set e : ↥(imgBar x K) ≃* P := eK.symm.trans eP with he
  have hzc : ∀ g ∈ imgBar x K, g * xbar x = xbar x * g := fun g _ => xbar_comm x g
  have hez : e ⟨xbar x, hxbar⟩ = z₀ := hP.equiv_central e hxbar hzc (PilotS5.orderOf_xbar hx)
  have hKc : IsComponent (imgBar x K) := by
    obtain ⟨-, Kb, hKb, -, hmap, -⟩ := hK
    show IsComponent ((K.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))))
    rw [hmap]
    exact hKb
  have hB2 := frame_B2 hG hx hKc (CFSG.GH74.Generic.IsSL4Model.q8Frame hS)
  refine ⟨hxK, hKc.1, IsSL4Model.natCard_center hS, hP.split1Like e hxbar hez, fun w hw => ?_,
    fun E hE hel hc => hP.e8_of_equiv e hxbar hez E hE hel hc⟩
  have : w ∈ zpowers (xbar x) := by rw [← hB2.2.2.1]; exact hw
  exact mem_zpowers_of_two (PilotS5.orderOf_xbar hx) this

omit [Finite G] in
theorem source_le {x : G} {K A : Subgroup G} (hxK : x ∈ K) (hA : IsSource2 x K A) :
    A ≤ K ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 8 := by
  obtain ⟨-, hAel, hA8, hcase⟩ := hA
  refine ⟨?_, hAel, hA8⟩
  rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -⟩
  · exact hAK
  · rw [hAE]
    exact sup_le hEK (Subgroup.zpowers_le.2 hxK)

theorem exists_adm_of_shape1_big {x : G} {K A : Subgroup G} (hG : Gen4 G) (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h1 : QShape1Big (↥K ⧸ pPrimeCore 2 ↥K))
    (hA : IsSource2 x K A) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  obtain ⟨P, _, F', _, _, z₀, ⟨eP⟩, hodd, hbig, hP⟩ := exists_grpS1_of_big h1
  obtain ⟨hxK, -, -, hY, hCY, he8⟩ := shape1_data hG hx hK eP hP h1.qShape1
  obtain ⟨hAK, hAel, hA8⟩ := source_le hxK hA
  exact exists_adm_of_split1 hodd hbig hx hK hY hCY he8 hAK hAel hA8

end GLevel2

end CFSG.GH74.Generic.BProg.B1.PilotS1

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem sourceExistsFor_shape1 : SourceExistsFor QShape1 := by
  intro G _ _ _hyp _noAlt x K hcirc h1
  obtain ⟨P, _, F', _, _, z, ⟨e⟩, hP⟩ := PilotS1.exists_grpS1_of_shape1 h1
  exact PilotS1.exists_source_of_model hcirc.1.1.1.2.2 e hP h1

theorem admissibleExistsFor_shape1_big : AdmissibleExistsFor PilotS1.QShape1Big := by
  intro G _ _ hyp _noAlt x K hcirc h1 A hA
  exact PilotS1.exists_adm_of_shape1_big hyp.gen4 hcirc.1.1.1.1 hcirc.1.1.1.2.2 h1 hA

end CFSG.GH74.Generic.BProg.B1
