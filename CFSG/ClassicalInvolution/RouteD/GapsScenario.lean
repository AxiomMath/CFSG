module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ}

section Nodes

variable {ι : Type} {K : Subgroup G}

structure LNodes (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] {ι : Type} (adj : ι → ι → Prop)
    (Ω : Set (Subgroup G)) (K : Subgroup G) where
  J : ι → Subgroup G
  w : ι → G
  mem : ∀ a, J a ∈ Ω
  cl : ∀ a, IsClassicalMember p f (J a) (w a)
  commK : ∀ a, Commutes K (J a)
  comm : ∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (J a) (J b)
  pair : ∀ a b, adj a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (J a) (J b)

namespace LNodes

variable {adj : ι → ι → Prop}

@[expose] def Adj (adj : ι → ι → Prop) (a b : ι) : Prop := adj a b ∨ adj b a

variable (nd : LNodes p f adj Ω K)

omit [Finite G] in
theorem pair_of_adj {a b : ι} (h : Adj adj a b) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J a) (nd.J b) := by
  rcases h with h | h
  · exact nd.pair a b h
  · obtain ⟨W, hW⟩ := nd.pair b a h
    exact ⟨W, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW⟩

omit [Finite G] in
theorem not_commutes_of_adj {a b : ι} (h : Adj adj a b) : ¬ Commutes (nd.J a) (nd.J b) := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact not_commutes_of_linearBlockStandardPair hW

omit [Finite G] in
theorem commutes_of_not_adj {a b : ι} (hab : a ≠ b) (h : ¬ Adj adj a b) :
    Commutes (nd.J a) (nd.J b) :=
  nd.comm a b hab (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))

omit [Finite G] in
theorem adj_ne (nd : LNodes p f adj Ω K) {a b : ι} (h : Adj adj a b) : a ≠ b := by
  rintro rfl
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact ne_of_linearBlockStandardPair hW rfl

omit [Finite G] in
theorem ne_J (hΩ : InClass p f Ω) {a b : ι} (hab : a ≠ b) : nd.J a ≠ nd.J b := by
  intro h
  by_cases hadj : Adj adj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact ne_of_linearBlockStandardPair hW h
  · have := nd.commutes_of_not_adj hab hadj
    rw [← h] at this
    exact not_commutes_self_of_mem hΩ (nd.mem a) this

omit [Finite G] in
theorem commute_w (h2 : (2 : GaloisField p f) ≠ 0) (a b : ι) :
    Commute (nd.w a) (nd.w b) := by
  by_cases hab : a = b
  · subst hab; exact Commute.refl _
  by_cases hadj : Adj adj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact standardPair_involutions_commute h2 hW (nd.cl a).mem (nd.cl b).mem
      (nd.cl a).orderOf_eq_two (nd.cl b).orderOf_eq_two
  · exact (nd.commutes_of_not_adj hab hadj) _ (nd.cl a).mem _ (nd.cl b).mem

omit [Finite G] in
theorem conjSub_w (h2 : (2 : GaloisField p f) ≠ 0) {a b : ι} (h : Adj adj a b) :
    conjSub (nd.w b) (nd.J a) = nd.J a := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact conjSub_eq_of_standardPair h2 hW (nd.cl b).mem (nd.cl b).orderOf_eq_two

omit [Finite G] in
theorem mem_loc (b : ι) {L : Subgroup G} (hL : L ∈ Ω) (hc : Commutes L (nd.J b)) :
    L ∈ centralizingMembers Ω {nd.w b} :=
  mem_centralizingMembers_of_commutes hL (nd.cl b).mem hc

end LNodes

end Nodes

section Scenarios

variable {ι : Type} {adj : ι → ι → Prop} {K : Subgroup G} {z : G}

theorem scenarioA
    (hF : OrthGeom (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f adj Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp a₀ a₁ e b : ι} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (h0 : LNodes.Adj adj pp a₀) (h1 : LNodes.Adj adj pp a₁) (h01 : a₀ ≠ a₁) (h01' : ¬ LNodes.Adj adj a₀ a₁)
    (hea₀ : e ≠ a₀) (hea₁ : e ≠ a₁)
    (hdis : (LNodes.Adj adj e a₀ ∧ ¬ LNodes.Adj adj e a₁) ∨ (¬ LNodes.Adj adj e a₀ ∧ LNodes.Adj adj e a₁))
    (hbpp : b ≠ pp) (hb0 : b ≠ a₀) (hb1 : b ≠ a₁) (hbe : b ≠ e)
    (hbpp' : ¬ LNodes.Adj adj b pp) (hb0' : ¬ LNodes.Adj adj b a₀) (hb1' : ¬ LNodes.Adj adj b a₁)
    (hbe' : ¬ LNodes.Adj adj b e) : False := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t := by
    have := standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
    exact this
  have hKJ : ∀ a, K ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact not_commutes_self_of_mem hΩ c.hK this
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hKw : ∀ a, Commute z (nd.w a) := fun a =>
    (nd.commK a) z c.hz.mem (nd.w a) (nd.cl a).mem
  have mxJ : ∀ a, a ≠ b → ¬ LNodes.Adj adj a b → nd.J a ∈ centralizingMembers Ω {nd.w b} :=
    fun a hab hadj => nd.mem_loc b (nd.mem a) (nd.commutes_of_not_adj hab hadj)
  have mxK : K ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b c.hK (nd.commK b)
  have mxβ : β ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b hβ (hfix b hbpp)
  have hppne : ∀ a, LNodes.Adj adj pp a → a ≠ pp := fun a h => (nd.adj_ne h).symm
  have hfix0 : Commutes β (nd.J a₀) := hfix a₀ (hppne a₀ h0)
  have hfix1 : Commutes β (nd.J a₁) := hfix a₁ (hppne a₁ h1)
  have hcomm0β : Commutes (nd.J a₀) β := commutes_symm hfix0
  have hcomm1β : Commutes (nd.J a₁) β := commutes_symm hfix1
  refine star_config cx hF (c := nd.J pp) (wc := nd.w pp)
    (l := ![nd.J a₀, nd.J a₁, β]) (w := ![nd.w a₀, nd.w a₁, t]) ?_ (nd.cl pp) ?_ ?_ ?_ ?_ ?_
  · exact mxJ pp hbpp.symm (fun h => hbpp' h.symm)
  · intro i
    fin_cases i
    · exact mxJ a₀ hb0.symm (fun h => hb0' h.symm)
    · exact mxJ a₁ hb1.symm (fun h => hb1' h.symm)
    · exact mxβ
  · intro i
    fin_cases i
    · exact nd.cl a₀
    · exact nd.cl a₁
    · exact ht
  · intro i
    fin_cases i
    · exact ⟨nd.ne_J hΩ (nd.adj_ne h0), nd.not_commutes_of_adj h0, nd.commute_w h2 _ _,
        nd.conjSub_w h2 h0⟩
    · exact ⟨nd.ne_J hΩ (nd.adj_ne h1), nd.not_commutes_of_adj h1, nd.commute_w h2 _ _,
        nd.conjSub_w h2 h1⟩
    · exact ⟨(hβJ pp).symm, fun h => hmov (commutes_symm h),
        (commute_of_conjSub_eq' h2 (c.hex _ (nd.mem pp)) (nd.cl pp) hnorm).symm, hnorm⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ⟨nd.ne_J hΩ h01, nd.commutes_of_not_adj h01 h01'⟩
    · exact ⟨(hβJ a₀).symm, hcomm0β⟩
    · exact ⟨nd.ne_J hΩ h01.symm, nd.commutes_of_not_adj h01.symm (fun h => h01' h.symm)⟩
    · exact absurd rfl hij
    · exact ⟨(hβJ a₁).symm, hcomm1β⟩
    · exact ⟨hβJ a₀, hfix0⟩
    · exact ⟨hβJ a₁, hfix1⟩
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd hij (by decide) | skip
    ·
      refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hΩ hea₀,
        nd.ne_J hΩ hea₁, nd.commute_w h2 _ _, nd.commute_w h2 _ _, ?_⟩
      rcases hdis with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · intro hiff
        exact nd.not_commutes_of_adj ha (hiff.mpr (nd.commutes_of_not_adj hea₁ hb'))
      · intro hiff
        exact nd.not_commutes_of_adj hb' (hiff.mp (nd.commutes_of_not_adj hea₀ ha))
    ·
      exact ⟨K, z, mxK, c.hz, hKJ a₀, hKne, hKw a₀, hzt,
        fun hiff => hnKβ (hiff.mp (nd.commK a₀))⟩
    ·
      exact ⟨K, z, mxK, c.hz, hKJ a₁, hKne, hKw a₁, hzt,
        fun hiff => hnKβ (hiff.mp (nd.commK a₁))⟩

theorem scenarioC
    (hF : OrthFacts (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f adj Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp b : ι} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (hbpp : b ≠ pp) (hbpp' : ¬ LNodes.Adj adj b pp) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hβJ : β ≠ nd.J pp := fun h => by
    have := nd.commK pp
    rw [← h] at this
    exact hnKβ this
  have hnormK : conjSub t K = K :=
    conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact sign_config cx hF (a := K) (b := β) (d := nd.J pp) (wa := z) (wb := t) (wd := nd.w pp)
    (nd.mem_loc b c.hK (nd.commK b)) (nd.mem_loc b hβ (hfix b hbpp))
    (nd.mem_loc b (nd.mem pp) (nd.commutes_of_not_adj hbpp.symm (fun h => hbpp' h.symm)))
    c.hz ht (nd.cl pp) hKne hβJ ⟨W, hW⟩ hmov (nd.commK pp) hzt
    (commute_of_conjSub_eq' h2 (c.hex _ (nd.mem pp)) (nd.cl pp) hnorm).symm hnormK hnorm


end Scenarios

end CFSG.ClassicalInvolution.RouteD.Gaps
