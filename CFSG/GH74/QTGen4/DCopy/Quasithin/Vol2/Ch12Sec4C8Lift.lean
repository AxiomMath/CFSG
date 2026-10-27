module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Lift
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8T

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S1248

open S1248

theorem comp1248Lift_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hpre : Pre1242_F4) (hinv : InvolFact1248_F4) (h68 : E6.E68Stmt) (hlist : Lemma115_3_List)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hKF : KnownFacts15122Types)
    (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact) (hKG3 : HatA67Fact1248)
    (hI31 : AS_I_3_1_one_two) (hKG5 : L2pEmbedFact1248) : Comp1248Lift_F4 := by
  intro G _ _ T L V U hS X hXLU hX3 hXC l hl hlU hl2 K hK hKp
  classical
  obtain ⟨z, hF⟩ := S1248.exists_facts_F4 h331 h1222 h323 h3228 hpre hS
  have hyp := hS.cx.hyp
  have := hyp.simple
  have hev : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
  set U₀ := U ⊓ conjSubgroup U l with hU₀def
  have hU₀U : U₀ ≤ U := inf_le_left
  have hidx : U₀.relIndex U = 2 := relIndex_inf_conj hS hl.1 hlU
  have hW₀ : U₀ = U ∨ (U₀ ≤ U ∧ U₀.relIndex U = 2) := Or.inr ⟨hU₀U, hidx⟩
  have hWU : U = U ∨ (U ≤ U ∧ U.relIndex U = 2) := Or.inl rfl
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => hF.cx.sq u (hS.le hu)
  have hXNU : X ≤ Subgroup.normalizer (U : Set G) := hXLU.trans inf_le_right

  have hXNUl : X ≤ Subgroup.normalizer ((conjSubgroup U l : Subgroup G) : Set G) := by
    intro x hx
    have hlx : l * x * l⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hl.2 x).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have h1 := Subgroup.mem_normalizer_iff.1 (hXNU hlx) (l * y * l⁻¹)
    have e : l * (x * y * x⁻¹) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) * (l * x * l⁻¹)⁻¹ := by
      group
    rw [e]
    exact h1
  have hXNU₀ : X ≤ Subgroup.normalizer (U₀ : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXNU hx, hXNUl hx⟩
  have hXU₀ : X ⊓ Subgroup.centralizer (U₀ : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_le hU2 hXNU hX3 hXC hU₀U hidx
  have hXU : X ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
    have hd : Nat.card ↥(X ⊓ Subgroup.centralizer (U : Set G)) ∣ 3 :=
      hX3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [h3, hX3])).symm.le.trans inf_le_right) hXC

  have htype : ∀ {W : Subgroup G}, (W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) →
      X ≤ Subgroup.normalizer (W : Set G) → X ⊓ Subgroup.centralizer (W : Set G) = ⊥ →
      ∀ J, IsComponentIn J (Subgroup.centralizer (W : Set G)) → IsSimpleGroup ↥J ∧
        3 ∣ Nat.card J ∧ ∃ q : ℕ, QuasithinUnique.Ch1.IsFermatOrMersennePrime q ∧
          CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥J .PSL 2 q 1 := by
    intro W hW hXN hXW J hJ
    obtain ⟨hs, q, hq, hqsl⟩ :=
      hF.comp_type_core_F4 hinv h68 hlist hF318 h36 h38 hKF hKG1 hKG2 hKG3 hW hXN hX3 hXW hJ
    exact ⟨hs, three_dvd_card_psl2 hqsl, q, hq, hqsl⟩
  have hT2 : IsPGroup 2 V := hyp.sylow.1.to_le hF.cx.le_T
  have huniq : ∀ {W : Subgroup G}, (W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) →
      X ≤ Subgroup.normalizer (W : Set G) → X ⊓ Subgroup.centralizer (W : Set G) = ⊥ →
      ∀ J J', IsComponentIn J (Subgroup.centralizer (W : Set G)) →
        IsComponentIn J' (Subgroup.centralizer (W : Set G)) → J = J' := by
    intro W hW hXN hXW J J' hJ hJ'
    have hWU' : W ≤ U := by
      rcases hW with rfl | ⟨h, -⟩
      · exact le_rfl
      · exact h
    have h1 := htype hW hXN hXW J hJ
    have h2 := htype hW hXN hXW J' hJ'
    exact eq_of_three_dvd hev (hT2.to_le (hWU'.trans hS.le)) (hF.mem_gamma_F4 hinv hW).2.1 hXN hX3
      hXW hJ hJ' h1.1 h2.1 h1.2.1 h2.2.1

  have h115₀ := hF.lemma115Hyp_F4 hinv hW₀
  have h115 := hF.lemma115Hyp_F4 hinv hWU
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQ₀ : IsSylowTwoOf Q (Subgroup.centralizer (U₀ : Set G)) := h115₀.sylow
  have hQU : IsSylowTwoOf Q (Subgroup.centralizer (U : Set G)) := h115.sylow

  obtain ⟨-, hKz, -, -⟩ := h115.component_action hK
  have hKO : K ≤ Subgroup.centralizer
      (oddCoreIn (Subgroup.centralizer (U₀ : Set G)) : Set G) := by
    refine le_centralizer_of_inverts hF.z_sq hKz ?_ h115₀.inverts_oddCoreIn
    exact (hK.1.trans (Subgroup.centralizer_le hU₀U)).trans (le_normalizer_oddCoreIn _)

  have hq := qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hSQ : CFSG.SectionRank.IsSQTKCat ↥(Subgroup.centralizer (U₀ : Set G)) :=
    hq.1 _ h115₀.pCore_ne_bot
  have hUH₀ : U ≤ Subgroup.centralizer (U₀ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (hF.V_le_centralizer (hS.le hu)) w (hS.le (hU₀U hw)))
  have hKq := QuasithinUnique.BenderBranch.isQuasisimple_of_isComponentIn hK
  have hK2 : Id2519.IsTwoComponentIn K
      (Subgroup.centralizer (U₀ : Set G) ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [inf_eq_right.2 (Subgroup.centralizer_le hU₀U)]
    exact Id2519.isTwoComponentIn_of_isComponentIn hK (E6.two_dvd_card_of_isQuasisimple hKq)
  obtain ⟨K₁, hK₁, hKK₁⟩ := hI31 G (Subgroup.centralizer (U₀ : Set G)) U K hSQ hUH₀
    (hT2.to_le hS.le) hK2 hKO

  have hVQ : V ≤ Q := le_inf hF.cx.le_T hF.V_le_centralizer
  have hVZ : V ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.1 inf_le_right
  have hUN : ∀ u ∈ U, CFSG.conjugate K₁ u = K₁ := fun u hu =>
    QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.2
      (E6.mem_normalizer_of_mem_center_sylow hQ₀ hK₁ (hVQ (hS.le hu)) (hVZ (hS.le hu)))
  have hKK₁' : K ≤ K₁ := hKK₁.trans (iSup₂_le fun u hu => (hUN u hu).le)

  obtain ⟨-, -, q, hq', hqsl⟩ := htype hW₀ hXNU₀ hXU₀ K₁ hK₁
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    have hKg := Unc25G2.isComponentIn_conjugate hK (hQU.1 hg)
    exact QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1
      (huniq hWU hXNU hXU _ _ hKg hK)

  have hS₁ : IsSylowTwoOf (Q ⊓ K₁) K₁ := E6.isSylowTwoOf_inf_of_subnormal' hQ₀ hK₁.1 hK₁.2.2
  obtain ⟨p, hp, hpsl⟩ := hKp
  have hKe : K = K₁ :=
    hKG5 G K K₁ (Q ⊓ K₁) p q hp hq' hpsl hqsl hKK₁' hS₁ (inf_le_left.trans hQK)
  refine ⟨hKe ▸ hK₁, fun K' hK' _ => ?_⟩
  rw [hKe]
  exact huniq hW₀ hXNU₀ hXU₀ K' K₁ hK' hK₁

end CFSG.Quasithin.H13
