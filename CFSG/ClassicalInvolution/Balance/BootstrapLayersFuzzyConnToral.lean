module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnStab
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnModel
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnComp
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnFrame
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalAll
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyPair

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices LinkMove mem_fuzzyVertices_map)
open scoped commutatorElement

section Commute

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

theorem mem_linkStab_of_oddQuotMk_comm (hinv : ConjInvariant 𝒞) {B : Subgroup G}
    (hB : FuzzyFrameOn p f 𝒞 B) (haB : a ∈ fuzzyVertices p f 𝒞 B) {g x : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (hxC : x ∈ Subgroup.centralizer ({a} : Set G))
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hxa : x ≠ a)
    (hcomm : oddQuotMk a ⟨g, hg⟩ * oddQuotMk a ⟨x, hxC⟩ =
      oddQuotMk a ⟨x, hxC⟩ * oddQuotMk a ⟨g, hg⟩) :
    g ∈ linkStab (p := p) (f := f) hinv a B := by
  refine mem_linkStab_of_coset hinv hB haB hg hxB hx1 hxa ?_
  have h := (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hg hxC).mp hcomm
  rw [involutionOddCore_eq_oddCoreIn]
  have h2 := conj_mem_oddCoreIn (inv_mem hxC) h
  have e : x⁻¹ * (g * x * g⁻¹ * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * (g * x * g⁻¹) := by group
  rwa [e] at h2

end Commute

section Toral

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

theorem mem_linkStab_of_toral (hinv : ConjInvariant 𝒞) (hp2 : p ≠ 2)
    (hs : SecData p f a (linkFamily p f 𝒞 a)) (D : LocalLieSystemAt p f (linkFamily p f 𝒞 a) a)
    (h5 : ∀ j, 5 ≤ p ^ D.exp j) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    {B J N : Subgroup G} {t u : G} (hb : FrameBasis p f 𝒞 a B J t N u) (j : Fin D.card)
    (hjJ : modOdd a (triangleResidual J a) ≤ (secComponentHom hs.normalizes D j).range)
    (hjN : modOdd a (triangleResidual N a) ≤ (secComponentHom hs.normalizes D j).range) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hgj : oddQuotMk a ⟨g, hg⟩ ∈ (secComponentHom hs.normalizes D j).range) :
    g ∈ linkStab (p := p) (f := f) hinv a B := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set ψ := secComponentHom hs.normalizes D j with hψ
  have ha2 : a * a = 1 := hb.sq hb.aB
  have haJ : a ∈ trivialOnQuot J := hb.tqJ hb.aB
  have haN : a ∈ trivialOnQuot N := hb.tqN hb.aB
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hb.comm hb.tB hb.aB)
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hb.comm hb.uB hb.aB)
  have hRJ : triangleResidual J a ∈ linkFamily p f 𝒞 a :=
    triangleResidual_mem_linkFamily hb.memJ hb.clsJ haJ
  have hRN : triangleResidual N a ∈ linkFamily p f 𝒞 a :=
    triangleResidual_mem_linkFamily hb.memN hb.clsN haN
  have hsJ := isSectionMember_triangleResidual hb.clsJ ha2 haJ
  have hsN := isSectionMember_triangleResidual hb.clsN ha2 haN
  have h4 : 4 ≤ p ^ D.exp j := by
    have := h5 j
    omega
  have hquasi : ∀ (i : Fin D.card), ∀ R ∈ fundamentalSubgroups (D.tag i) (compModel D i).D,
      CFSG.Open.IsQuasisimple ↥R := fun i R hR => fundQuasisimple_core hp2 (D.isFundTag i)
    (D.admissible i) (by have := h5 i; omega) R hR
  have hqsJ := hs.isQuasisimple_modOdd D hquasi hRJ
  have hqsN := hs.isQuasisimple_modOdd D hquasi hRN
  obtain ⟨R₁, hR₁, hR₁K⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hRJ, hs.le _ hRJ⟩ hjJ
  obtain ⟨R₂, hR₂, hR₂K⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hRN, hs.le _ hRN⟩ hjN
  have hperf := ModelFacts.fundPerfect_core (D.tag j) (D.rank j) p (D.exp j) hp2
    (D.isFundTag j) (D.admissible j) h4
  have hgen := hMFC (D.tag j) (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j) (h5 j)
  have key := ModelFacts.range_le_iSup_of_commutingPair ψ
    (secComponentHom_ker_le_center hs.normalizes D j)
    (fun R hR => commutator_self_eq_of_le (hperf R hR)) hgen hR₁ hR₂
    (u₁ := oddQuotMk a ⟨t, htC⟩) (u₂ := oddQuotMk a ⟨u, huC⟩)
    (by rw [hR₁K]; exact oddQuotMk_mem_modOdd hsJ.mem htC)
    (by rw [hR₂K]; exact oddQuotMk_mem_modOdd hsN.mem huC)
    (by
      rw [hR₁K]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hsJ.isCentralInvolution.central _ hk)))
    (by
      rw [hR₂K]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hsN.isCentralInvolution.central _ hk)))
    (by
      rw [hR₁K]
      exact oddQuotMk_centralizes_triangleResidual hb.clsJ ha2 haJ hqsJ (hb.tqJ hb.uB) huC)
    (by
      rw [hR₂K]
      exact oddQuotMk_centralizes_triangleResidual hb.clsN ha2 haN hqsN (hb.tqN hb.tB) htC)
  set S₀ : Subgroup ↥C := (linkStab (p := p) (f := f) hinv a B).subgroupOf C with hS₀
  have hRT : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      ((∀ y ∈ R.map ψ, oddQuotMk a ⟨t, htC⟩ * y = y * oddQuotMk a ⟨t, htC⟩) ∨
        (∀ y ∈ R.map ψ, oddQuotMk a ⟨u, huC⟩ * y = y * oddQuotMk a ⟨u, huC⟩) ∨
        (∀ y ∈ R.map ψ, (oddQuotMk a ⟨t, htC⟩ * oddQuotMk a ⟨u, huC⟩) * y =
          y * (oddQuotMk a ⟨t, htC⟩ * oddQuotMk a ⟨u, huC⟩))) →
      R.map ψ ≤ S₀.map (oddQuotMk a) := by
    intro R _ hcond y hy
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (componentClassificationOddCore ↥C) y
    have hc' : oddQuotMk a c = y := hc
    refine ⟨c, ?_, hc'⟩
    show (c : G) ∈ linkStab (p := p) (f := f) hinv a B
    rcases hcond with h | h | h
    · refine mem_linkStab_of_oddQuotMk_comm hinv hb.frame hb.vertex c.2 htC hb.tB hb.t_ne_one
        hb.ta ?_
      show oddQuotMk a c * _ = _ * oddQuotMk a c
      rw [hc']
      exact (h y hy).symm
    · refine mem_linkStab_of_oddQuotMk_comm hinv hb.frame hb.vertex c.2 huC hb.uB hb.u_ne_one
        hb.u_ne_a ?_
      show oddQuotMk a c * _ = _ * oddQuotMk a c
      rw [hc']
      exact (h y hy).symm
    · have hxC : t * u ∈ C := mul_mem htC huC
      refine mem_linkStab_of_oddQuotMk_comm hinv hb.frame hb.vertex c.2 hxC
        (mul_mem hb.tB hb.uB) hb.tu_ne_one hb.tu_ne_a ?_
      have e : oddQuotMk a ⟨t * u, hxC⟩ = oddQuotMk a ⟨t, htC⟩ * oddQuotMk a ⟨u, huC⟩ := by
        rw [← map_mul]
        rfl
      show oddQuotMk a c * _ = _ * oddQuotMk a c
      rw [e, hc']
      exact (h y hy).symm
  have hT : ψ.range ≤ S₀.map (oddQuotMk a) :=
    key.trans (iSup₂_le fun R hR => iSup_le fun hcond => hRT R hR hcond)
  obtain ⟨s, hsS, hsg⟩ := hT hgj
  have hmem : ((s⁻¹ * ⟨g, hg⟩ : ↥C) : G) ∈ involutionOddCore a := by
    rw [involutionOddCore_eq_oddCoreIn]
    exact ⟨_, QuotientGroup.eq.mp hsg, rfl⟩
  have hsS' : (s : G) ∈ linkStab (p := p) (f := f) hinv a B := hsS
  have hg' : (s : G) * ((s⁻¹ * ⟨g, hg⟩ : ↥C) : G) = g := by
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  rw [← hg']
  exact mul_mem hsS' (oddCoreIn_le_linkStab hinv hb.frame hb.vertex hmem)

theorem mem_linkStab_of_mem_range (hinv : ConjInvariant 𝒞) (hp2 : p ≠ 2)
    (hs : SecData p f a (linkFamily p f 𝒞 a)) (D : LocalLieSystemAt p f (linkFamily p f 𝒞 a) a)
    (h5 : ∀ j, 5 ≤ p ^ D.exp j) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    {B J N : Subgroup G} {t u : G} (hb : FrameBasis p f 𝒞 a B J t N u) (j : Fin D.card) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hgj : oddQuotMk a ⟨g, hg⟩ ∈ (secComponentHom hs.normalizes D j).range) :
    g ∈ linkStab (p := p) (f := f) hinv a B := by
  have ha2 : a * a = 1 := hb.sq hb.aB
  have haJ : a ∈ trivialOnQuot J := hb.tqJ hb.aB
  have haN : a ∈ trivialOnQuot N := hb.tqN hb.aB
  have htC : t ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hb.comm hb.tB hb.aB)
  have huC : u ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hb.comm hb.uB hb.aB)
  have hRJ : triangleResidual J a ∈ linkFamily p f 𝒞 a :=
    triangleResidual_mem_linkFamily hb.memJ hb.clsJ haJ
  have hRN : triangleResidual N a ∈ linkFamily p f 𝒞 a :=
    triangleResidual_mem_linkFamily hb.memN hb.clsN haN
  have hsJ := isSectionMember_triangleResidual hb.clsJ ha2 haJ
  have hsN := isSectionMember_triangleResidual hb.clsN ha2 haN
  obtain ⟨cJ, hcJ⟩ := hs.exists_comp D hRJ
  obtain ⟨cN, hcN⟩ := hs.exists_comp D hRN
  have hmemt : oddQuotMk a ⟨t, htC⟩ ∈ (secComponentHom hs.normalizes D cJ).range :=
    hcJ (oddQuotMk_mem_modOdd hsJ.mem htC)
  have hmemu : oddQuotMk a ⟨u, huC⟩ ∈ (secComponentHom hs.normalizes D cN).range :=
    hcN (oddQuotMk_mem_modOdd hsN.mem huC)
  by_cases hjJ : j = cJ
  · by_cases hjN : j = cN
    · subst hjJ
      subst hjN
      exact mem_linkStab_of_toral hinv hp2 hs D h5 hMFC hb _ hcJ hcN hg hgj
    · exact mem_linkStab_of_oddQuotMk_comm hinv hb.frame hb.vertex hg huC hb.uB hb.u_ne_one
        hb.u_ne_a (hs.comm_of_ne D hjN hgj hmemu)
  · exact mem_linkStab_of_oddQuotMk_comm hinv hb.frame hb.vertex hg htC hb.tB hb.t_ne_one hb.ta
      (hs.comm_of_ne D hjJ hgj hmemt)

end Toral

section Transport

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

theorem reflTransGen_frameLink_of_comp (hinv : ConjInvariant 𝒞) (hp2 : p ≠ 2)
    (hs : SecData p f a (linkFamily p f 𝒞 a)) (D : LocalLieSystemAt p f (linkFamily p f 𝒞 a) a)
    (h5 : ∀ j, 5 ≤ p ^ D.exp j) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    {B J N : Subgroup G} {t u : G} (hb : FrameBasis p f 𝒞 a B J t N u) {B' : Subgroup G}
    (hB' : FuzzyFrameOn p f 𝒞 B') (haB' : a ∈ fuzzyVertices p f 𝒞 B') (j : Fin D.card)
    {J₁ : Subgroup G} {t₁ : G} (hJ₁𝒞 : J₁ ∈ 𝒞) (hJ₁ : IsClassicalMember p f J₁ t₁)
    (ht₁B : t₁ ∈ B) (hBJ₁ : B ≤ trivialOnQuot J₁)
    (hj₁ : modOdd a (triangleResidual J₁ a) ≤ (secComponentHom hs.normalizes D j).range)
    {J₂ : Subgroup G} {t₂ : G} (hJ₂𝒞 : J₂ ∈ 𝒞) (hJ₂ : IsClassicalMember p f J₂ t₂)
    (ht₂B' : t₂ ∈ B') (hB'J₂ : B' ≤ trivialOnQuot J₂) (ht₂a : t₂ ≠ a)
    (hj₂ : modOdd a (triangleResidual J₂ a) ≤ (secComponentHom hs.normalizes D j).range) :
    Relation.ReflTransGen (frameLink p f 𝒞 a) B B' := by
  have ha2 : a * a = 1 := hb.sq hb.aB
  have haJ₁ : a ∈ trivialOnQuot J₁ := hBJ₁ hb.aB
  have haJ₂ : a ∈ trivialOnQuot J₂ := hB'J₂ haB'.1
  have hR₁ : triangleResidual J₁ a ∈ linkFamily p f 𝒞 a :=
    triangleResidual_mem_linkFamily hJ₁𝒞 hJ₁ haJ₁
  have hR₂ : triangleResidual J₂ a ∈ linkFamily p f 𝒞 a :=
    triangleResidual_mem_linkFamily hJ₂𝒞 hJ₂ haJ₂
  have hs₁ := isSectionMember_triangleResidual hJ₁ ha2 haJ₁
  have hs₂ := isSectionMember_triangleResidual hJ₂ ha2 haJ₂
  obtain ⟨g, hg, hgj, hgt⟩ := hs.exists_conj_of_vertices D hp2 j
    (by have := h5 j; omega) hR₁ hR₂ hs₁.isCentralInvolution hs₂.isCentralInvolution hj₁ hj₂
  have hgS := mem_linkStab_of_mem_range hinv hp2 hs D h5 hMFC hb j hg hgj
  have hB'' : FuzzyFrameOn p f 𝒞 (B.map (MulAut.conj g).toMonoidHom) :=
    FuzzyFrameOn.map hinv hb.frame g
  have haB'' : a ∈ fuzzyVertices p f 𝒞 (B.map (MulAut.conj g).toMonoidHom) := by
    have := mem_fuzzyVertices_map hinv hb.vertex g
    rwa [conj_eq_of_mem_centralizer_singleton hg] at this
  have ht₂B'' : t₂ ∈ B.map (MulAut.conj g).toMonoidHom := hgt ▸ conj_mem_conjSub ht₁B
  have hB'c := hB'
  obtain ⟨-, -, -, -, hel', -, -⟩ := hB'c
  have hcomm : a * t₂ = t₂ * a :=
    congrArg Subtype.val (hel'.1.is_comm.comm (⟨a, haB'.1⟩ : B') ⟨t₂, ht₂B'⟩)
  obtain ⟨-, M, -, hM, -⟩ := hb.vertex
  have hF4 : Nat.card (Subgroup.closure ({a, t₂} : Set G)) = 2 ^ 2 := by
    have h := card_closure_pair_eq_four ha2 hs₂.isCentralInvolution.sq
      hM.isCentralInvolution.ne_one hs₂.isCentralInvolution.ne_one (Ne.symm ht₂a) hcomm
    rw [h]
    norm_num
  have hFB' : Subgroup.closure ({a, t₂} : Set G) ≤ B' := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact haB'.1
    · exact ht₂B'
  have hFB'' : Subgroup.closure ({a, t₂} : Set G) ≤ B.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact haB''.1
    · exact ht₂B''
  exact ((mem_linkStab_iff (p := p) (f := f) hinv).mp hgS).2.tail
    ⟨hB'', hB', haB'', haB', Or.inl ⟨_, ⟨hFB'', hF4⟩, ⟨hFB', hF4⟩⟩⟩

end Transport

end CFSG.ClassicalInvolution.Balance.Bootstrap
