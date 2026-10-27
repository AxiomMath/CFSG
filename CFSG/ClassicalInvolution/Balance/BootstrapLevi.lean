module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameCore
public import CFSG.ClassicalInvolution.RouteD.GapsLocal
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_cherry [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hΩ : InClass p f Ω)
    (hconn : OmegaConnected Ω) :
    ∃ M ∈ Ω, ∃ K ∈ Ω, ∃ N ∈ Ω, Commutes K M ∧ Commutes M N ∧ K ≠ N ∧ ¬ Commutes K N := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L' ∨ Commutes L L' := by
    intro L hL L' hL'
    have key : ∀ L'', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) L L'' →
        L'' ∈ Ω ∧ (L = L'' ∨ Commutes L L'') := by
      intro L'' h
      induction h with
      | refl => exact ⟨hL, Or.inl rfl⟩
      | @tail b c _ hbc ih =>
        obtain ⟨hbΩ, hLb⟩ := ih
        refine ⟨hbc.1, ?_⟩
        rcases hLb with rfl | hLb
        · exact Or.inr hbc.2
        · by_cases hLc : L = c
          · exact Or.inl hLc
          · exact Or.inr (hcon b hbΩ L hL c hbc.1 hLb hbc.2 hLc)
    exact (key L' (hconn L hL L' hL')).2
  obtain ⟨K₀, hK₀⟩ := hΩ.nonempty
  obtain ⟨z, hz⟩ := hΩ.classical K₀ hK₀
  have hnorm : Subgroup.normalizer (K₀ : Set G) = ⊤ := by
    rw [eq_top_iff, ← hΩ.generated]
    refine iSup₂_le fun L hL => ?_
    rcases hall L hL K₀ hK₀ with rfl | h
    · exact Subgroup.le_normalizer
    · refine le_trans (fun l hl => ?_) (Subgroup.centralizer_le_normalizer (K₀ : Set G))
      exact Subgroup.mem_centralizer_iff.mpr fun k hk => (h l hl k hk).symm
  have : K₀.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₀ with h | h
  · exact hz.ne_one (by simpa [h] using hz.mem)
  · refine not_subset_center_of_ne_one hnab hz.ne_one fun w hw => ?_
    rw [Set.mem_singleton_iff] at hw
    subst hw
    show w ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ K₀ := by rw [h]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isClassicalMember hz hg)


theorem exists_nonA1_localComponent [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hconn : OmegaConnected Ω)
    (hP1 : ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z}) :
    ∃ x : G, (∃ M ∈ Ω, IsClassicalMember p f M x) ∧
      ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), ∃ i : Fin D.card,
        ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
  obtain ⟨M, hM, K, hK, N, hN, hKM, hMN, hKN, hnc⟩ := exists_cherry hnab hΩ hconn
  obtain ⟨x, hx⟩ := hΩ.classical M hM
  have hP1x := hP1 M hM x hx
  have hxc : ¬ ({x} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hx.ne_one
  obtain ⟨D⟩ : Nonempty (LieSystemData p f (locQuot Ω x) (locFamily Ω x)) := hIH {x} hxc
  have hcen : ∀ {L : Subgroup G}, Commutes L M → L ≤ Subgroup.centralizer ({x} : Set G) :=
    fun h l hl => Subgroup.mem_centralizer_singleton_iff.mpr (h l hl x hx.mem)
  have hKx : K ∈ centralizingMembers Ω {x} := ⟨hK, hcen hKM⟩
  have hNx : N ∈ centralizingMembers Ω {x} := ⟨hN, hcen hMN.symm⟩
  have hKmem : locImg Ω x K ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩
  have hNmem : locImg Ω x N ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨N, hNx, rfl⟩
  obtain ⟨i, R, hR, hRK⟩ := D.fundamental _ hKmem
  obtain ⟨j, S, hS, hSN⟩ := D.fundamental _ hNmem
  have hij : i = j := by
    by_contra hij
    apply hnc
    refine commutes_of_commutes_locImg hΩ hP1x hKx hNx ?_
    intro a ha b hb
    rw [hRK] at ha
    rw [hSN] at hb
    obtain ⟨r, -, rfl⟩ := ha
    obtain ⟨s, -, rfl⟩ := hb
    exact D.commute i j hij r s
  subst hij
  refine ⟨x, ⟨M, hM, hx⟩, D, i, ?_⟩
  rintro ⟨ht, hr⟩
  have hR1 := eq_top_of_psl_two (p := p) (e := D.exp i) ht hr hR
  have hS1 := eq_top_of_psl_two (p := p) (e := D.exp i) ht hr hS
  apply hKN
  refine locImg_injOn hΩ hP1x hKx hNx ?_
  rw [hRK, hSN, hR1, hS1]


section Tags

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem levi_or_exotic (D : LieSystemData p f X Φ) (i : Fin D.card)
    (h : ¬ (D.tag i = .PSL ∧ D.rank i = 2)) :
    ((D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨ HasA2Pairs (D.tag i)) ∨
      (D.tag i = .G2 ∨ D.tag i = .twistedE6 ∨ D.tag i = .trialityD4) := by
  have hadm := D.admissible i
  have hfund := D.isFundTag i
  generalize D.tag i = t at hadm hfund h ⊢
  generalize D.rank i = n at hadm h ⊢
  cases t with
  | PSL =>
    refine Or.inl (Or.inl ⟨rfl, ?_⟩)
    have h2 : 2 ≤ n := hadm.2.2.1
    by_contra hlt
    exact h ⟨rfl, by omega⟩
  | PSU => exact Or.inl (Or.inr (Or.inl rfl))
  | PSp => exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  | POmegaOdd | POmegaPlus | POmegaMinus | E6 | E7 | E8 | F4 =>
    exact Or.inl (Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; decide))))
  | G2 => exact Or.inr (Or.inl rfl)
  | twistedE6 => exact Or.inr (Or.inr (Or.inl rfl))
  | trialityD4 => exact Or.inr (Or.inr (Or.inr rfl))
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

end Tags


section Residual

@[expose] def ExoticLeviBlock (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), InClass p f Ω → ∀ x : G,
    LocalOddCentral Ω {x} → p ^ f = 9 →
    ∀ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), ∀ i : Fin D.card,
      (D.tag i = .G2 ∨ D.tag i = .twistedE6 ∨ D.tag i = .trialityD4) →
      ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L)

theorem exactMembers_of_connected_nine [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f = 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    (hP1 : ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z})
    (hexotic : ExoticLeviBlock p f) : ExactMembers Ω := by
  obtain ⟨x, ⟨M, hM, hx⟩, D, i, hi⟩ := exists_nonA1_localComponent hnab hΩ hIH hconn hP1
  have hP1x := hP1 M hM x hx
  rcases levi_or_exotic D i hi with hlevi | hex
  · obtain ⟨L, hL, hlev⟩ := (LocalLeviComponent.of_levi D i hlevi).exists_member hp2 hq hΩ
    exact exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1x hL hlev
  · obtain ⟨L, hL, hlev⟩ := hexotic G Ω hΩ x hP1x h9 D i hex
    exact exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1x hL hlev

end Residual

section Frame

variable {A : Subgroup G}

theorem exactMembers_and_localOddCentral_of_frameFamily_of_layers_exotic [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      CentralizerGenerationModOTwo Ω A a)
    (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨hΔ, K₀, hK₀, z₀, hz₀A, hz₀, hK₀A, hP1⟩ :=
    deltaCore_eq_bot_and_localOddCentral_of_frameFamily hnab hp2 hq hΩ hIH hconn hM hMF1 hcover
      hloc hgenModO
  have hK₀Ω : K₀ ∈ Ω := hM.subset hK₀
  have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle hK₀Ω hz₀ hP1
  refine ⟨?_, hP1all⟩
  by_cases h9 : p ^ f = 9
  · exact exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH hconn hP1all hexotic
  · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
      Nat.prime_two A hM.elem (by rw [hM.card]; norm_num)
    exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hsingle hIH hK₀Ω hz₀
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hM.elem hF₀.1)
      (hK₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)

end Frame

end CFSG.ClassicalInvolution.Balance.Bootstrap
