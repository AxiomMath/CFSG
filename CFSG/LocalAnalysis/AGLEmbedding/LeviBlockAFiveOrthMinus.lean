module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusFives
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthMinusBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.RankThreeTheoremC LeviBlock

private theorem center_eq_bot_of_twistedD (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hD : IsLieOf IdxTwistedD (↥L ⧸ Subgroup.center ↥L)) : Subgroup.center ↥L = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rcases hZ Y L hL hodd (Or.inr (Or.inr (Or.inl hD))) with h1 | ⟨-, ⟨e6⟩⟩
  · exact h1
  · exfalso
    obtain ⟨⟨dI, hv⟩, hdI, ⟨e⟩⟩ := hD
    cases dI with
    | twistedD n q =>
      have hq2 : q.p = 2 := hdI
      have hmodel :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv hq2 e
      rw [hq2] at hmodel
      obtain ⟨⟨-, hf, hn⟩, K, hKf, hKfin, hK, b, c, hirr, ⟨e'⟩⟩ := hmodel
      have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) =
          CFSG.Open.ordTwistedD n (2 ^ q.exponent) :=
        (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .POmegaMinus) (n := n)
          ⟨⟨Nat.prime_two, hf, hn⟩, K, hKf, hKfin, hK, b, c, hirr, ⟨e'⟩⟩).2.2.2.2 rfl
      have h360 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 := by
        rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
        simp [Nat.factorial]
      have := orthMinus_sixteen_dvd hn hf
      rw [← hcard, h360] at this
      norm_num at this
    | _ => exact hdI.elim

private theorem three_le_pRank_of_twistedD {X : Type} [Group X] [Finite X]
    (hD : IsLieOf IdxTwistedD X) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨⟨dI, hv⟩, hdI, ⟨e⟩⟩ := hD
  cases dI with
  | twistedD n q =>
    have hq2 : q.p = 2 := hdI
    have hmodel :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv hq2 e
    rw [hq2] at hmodel
    obtain ⟨⟨-, -, hn⟩, K, hKf, hKfin, hK, b, c, -, ⟨e'⟩⟩ := hmodel
    have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e']
    exact CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three hn b c
  | _ => exact hdI.elim

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

private noncomputable def orthDiagTorus (b c : K) (hr : 3 ≤ r) :
    (Fin r → Kˣ) →* ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
  ((prodHom (Fin 2 → K)).comp (OrthogonalSplit.torusElt r K)).codRestrict _ fun t =>
    tailRootSupr_le (map_rootSupr_le ⟨_, (by
      rw [← (OrthogonalSplit.orthogonal_geometry_split_root_generation (K := K) hr).1]
      exact OrthogonalSplit.torusElt_mem_orthElementaryGroup hr t), rfl⟩)

private theorem orthDiagTorus_injective (b c : K) (hr : 3 ≤ r) :
    Function.Injective (orthDiagTorus b c hr) := by
  intro t t' h
  have h' := LinearEquiv.congr_fun (congrArg Subtype.val h)
  exact OrthogonalSplit.torusElt_injective
    (LinearEquiv.ext fun v => congrArg Prod.fst (h' (v, 0)))

end Torus

theorem kFactCompParabTwoFivesOn_twistedD (hLB : LeviBlocksOfFiveComponents)
    (hZ : OddCenterRest) : KFactCompParabTwoFivesOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hD h3 C₁ C₂ hne hC₁ hC₂
  exfalso
  obtain ⟨dI, hdI, ⟨e⟩⟩ := hD
  obtain ⟨K, _, _, _, b, c, r, s, dc, ρ, hr, hirr, hcuts, hρ, -⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  obtain ⟨β, hker, hpi, hcomm⟩ := KFactProofs.minus_exists_levi_data ρ hρ hcuts hr hirr
  have hkerρ : ρ.toMonoidHom.ker ≤ Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective]
    exact bot_le
  obtain ⟨j₁, j₂, hj, hq₁, hq₂, h60₁, h60₂⟩ := (hLB Y L P hCP.parab.1 _ ρ.toMonoidHom
    ρ.surjective hkerρ (Fin s ⊕ Unit) (orthLeviGroup K r dc) (orthLeviBlock K r dc b c) β hker
    hpi hcomm (isQuasisimple_or_isSolvable_orthLeviBlock hirr)).2 C₁ C₂ hne hC₁ hC₂
  obtain ⟨f, hK⟩ := orthMinus_card_eq_two_pow (K := K)
  obtain ⟨h4, hr4⟩ : Nat.card K = 4 ∧ 4 ≤ r := by
    rcases j₁ with l | u <;> rcases j₂ with l' | u'
    · obtain ⟨e₁, e₄⟩ := orthLeviBlock_inl_of_sixty hK l hq₁ h60₁
      obtain ⟨e₁', -⟩ := orthLeviBlock_inl_of_sixty hK l' hq₂ h60₂
      exact ⟨e₄, KFactProofs.minus_four_le_of_two_blocks hcuts (fun he => hj (by rw [he]))
        e₁ e₁'⟩
    · have := (orthLeviBlock_inl_of_sixty hK l hq₁ h60₁).2
      have := orthLeviBlock_inr_of_sixty hK hirr u' hq₂ h60₂
      omega
    · have := orthLeviBlock_inr_of_sixty hK hirr u hq₁ h60₁
      have := (orthLeviBlock_inl_of_sixty hK l' hq₂ h60₂).2
      omega
    · exact absurd (congrArg Sum.inr (Subsingleton.elim u u')) hj
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, h4]
  have hrL : r ≤ CFSG.Open.pRank 3 L := CFSG.SectionRank.le_pRank_of_injective (by norm_num)
    (fun x y => mul_comm x y)
    (fun x => by
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← hunits]
      exact pow_card_eq_one')
    (by rw [Nat.card_fun, hunits, Nat.card_fin])
    (L.subtype.comp (ρ.toMonoidHom.comp (orthDiagTorus b c hr)))
    (L.subtype_injective.comp (ρ.injective.comp (orthDiagTorus_injective b c hr)))
    (by
      rintro _ ⟨t, rfl⟩
      exact (ρ _).2)
  omega

theorem kFactCompParabOneFiveOn_twistedD (hZ : OddCenterRest) :
    KFactCompParabOneFiveOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hD C hC5
  refine Or.inl ?_
  have hbot := center_eq_bot_of_twistedD hZ hCP.comp hCP.odd hD
  have h3 := three_le_pRank_of_twistedD hD
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm))] at h3
  obtain ⟨E, -, hE, hcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    Nat.prime_three ((by norm_num : 2 ≤ 3).trans h3)
  refine ⟨E.map L.subtype, Subgroup.map_subtype_le E, CFSG.SectionRank.isElemAbelian_map hE _,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, -, rfl⟩, hxC⟩
    have hxZ : x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC l l.2)
    rw [hbot, Subgroup.mem_bot] at hxZ
    rw [hxZ, map_one]
    exact Subgroup.one_mem _

end CFSG.AGLEmbedding
