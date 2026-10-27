module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Desc3

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {IsK : GroupClass}
  {S Up Lo : List TauCeti.SporadicName} {R : GroupClass}

theorem reach_base (c : DescCtx H N IsK S Up Lo R) {K₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsK K₁) : R (↥K₁ ⧸ center ↥K₁) := by
  obtain ⟨Y, _, σ, hσ, hσk, hY⟩ := hK₁
  have : Group.IsPerfect ↥K₁ := hK₁L.isQuasisimple.1
  obtain ⟨e⟩ := cqEquiv_of_cover σ hσ hσk
  exact c.rc.iso _ _ e.symm (c.rc.K_reach Y hY)

theorem isK_of_lt_step (c : DescCtx H N IsK S Up Lo R) {B A : Subgroup H} (hBK : KLike IsK B)
    (hR : R (↥B ⧸ center ↥B)) (hBA : Lt B A) (hlt : cqCard B < cqCard A)
    (hA : ∃ s ∈ S, OddCover s A) : IsK (↥B ⧸ CFSG.oddCore ↥B) := by
  have hBK' := hBK
  obtain ⟨Y, _, σ, hσ, hσk, hY⟩ := hBK'
  have hBq : CFSG.IsQuasisimple ↥B := (lt_inL_left hBA).isQuasisimple
  have hAB : B ≠ A := by
    intro h
    subst h
    exact lt_irrefl _ hlt
  obtain ⟨m, L, T, s, hm, hch, h0, hT, -⟩ :=
    c.junction c.hkp N c.hN B A (lt_inL_left hBA) (lt_inL_right hBA) hBA hAB (c.rc.not_exc _ hR).1
      (c.rc.not_exc _ hR).2
  have hL0 : InL (L 0) := h0 ▸ lt_inL_left hBA
  have hlast : L m = A := hch.last
  subst h0
  have hRL := reach_chain c.ih c.hUp c.rc c.hN c.hidx c.hkp hch hT hL0 hL0 hBK
    (Reached.refl hR)
  have hmono : ∀ i, i ≤ m → cqCard (L 0) ≤ cqCard (L i) := fun i hi => chain_zero_le hch i hi
  have : Group.IsPerfect ↥(L 0) := hBq.1
  obtain ⟨e₀⟩ := cqEquiv_of_cover σ hσ hσk
  have hcq : ∀ i, 1 ≤ i → i ≤ m → IsK (↥(L (i - 1)) ⧸ CFSG.oddCore ↥(L (i - 1))) →
      cqCard (L (i - 1)) = cqCard (L 0) := by
    intro i hi him hK'
    have hPq : CFSG.IsQuasisimple ↥(L (i - 1)) := (hch.elem i hi him).2.2.2.isQuasisimple
    have : Group.IsPerfect ↥(L (i - 1)) := hPq.1
    obtain ⟨e₁⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥(L (i - 1))))
      (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']
        exact oddCore_le_center hPq)
    obtain ⟨e₂⟩ := c.rc.K_cq _ _ hK' hY
    exact Nat.card_congr (e₁.trans (e₂.trans e₀.symm)).toEquiv
  have key := chain_down (m := m)
    (fun i => (∃ s ∈ S, OddCover s (L i)) ∨
      (cqCard (L i) = cqCard (L 0) ∧ IsK (↥(L i) ⧸ CFSG.oddCore ↥(L i))))
    (Or.inl (hlast ▸ hA)) (by
      intro i hi him hΦ
      rcases hΦ with hL | ⟨hcard, hK⟩
      · rcases hch.link i hi him with h5a | h5b
        · obtain ⟨π, hπ, hk⟩ := chain_link5a_cover hch hi him h5a
          obtain ⟨s', hs', hcov⟩ := hL
          exact Or.inl ⟨s', hs', oddCover_of_cover hcov π hπ hk⟩
        · have hK' := chain_link5b_isK c.ih c.hUp c.rc c.hKiso c.hN c.hidx c.hkp hch hT
            hL0 hL0 hBK hi him h5b (hRL _ (by omega)) hL
          exact Or.inr ⟨hcq i hi him hK', hK'⟩
      · rcases hch.link i hi him with h5a | h5b
        · obtain ⟨π, hπ, hk⟩ := chain_link5a_cover hch hi him h5a
          have hperf : Group.IsPerfect ↥(L i) := (hch.comp i him).2.isQuasisimple.1
          have heq : cqCard (L (i - 1)) = cqCard (L i) := (cqCard_eq_of_cover hperf π hπ hk).symm
          have h1 : cqCard (L 0) = cqCard (L (i - 1)) := by
            have := hmono (i - 1) (by omega)
            omega
          refine Or.inr ⟨by omega, ?_⟩
          obtain ⟨ρ, hρ, hρk⟩ := chain_cover_of_eq hch (i - 1) (by omega) h1
          have hσρ : Function.Surjective (σ.comp ρ) := hσ.comp hρ
          exact isK_quot_of_cover c.hKiso c.rc.K_quot c.rc.K_iso π hπ hK (σ.comp ρ) hσρ hY
        · exfalso
          have h1 := chain_link5b_lt hch hi him h5b
          have h2 := hmono (i - 1) (by omega)
          omega) 0 (Nat.zero_le _)
  rcases key with ⟨s', hs', hcov⟩ | ⟨-, hK⟩
  · exfalso
    obtain ⟨f⟩ := hcov.2.2
    exact c.rc.K_not_sporadic Y hY s' (List.mem_append_left _ hs') ⟨e₀.symm.trans f⟩
  · exact hK

theorem isK_of_reach (c : DescCtx H N IsK S Up Lo R) {L₀ : Subgroup H} (hL₀ : InL L₀)
    (hL₀t : ∃ s ∈ S, OddCover s L₀) {K₁ : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsK K₁) :
    ∀ A, ReflTransGen Lt K₁ A → cqCard K₁ < cqCard A → (∃ s ∈ S, OddCover s A) →
      IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) := by
  have hR := reach_base c hK₁L hK₁
  have hK₁' := hK₁
  obtain ⟨Y, _, σ, hσ, hσk, hY⟩ := hK₁'
  have hperf₁ : Group.IsPerfect ↥K₁ := hK₁L.isQuasisimple.1
  intro A hKA
  induction hKA with
  | refl => exact fun h => absurd h (lt_irrefl _)
  | tail hKB hBA ihB =>
    rename_i B A
    intro hlt hA
    by_cases hB : cqCard K₁ < cqCard B
    · have hty := typeL_of_reach c hK₁L hK₁ hR hL₀ hL₀t B hKB hB
      exact ihB hB hty
    · have hRB := reach_reflTransGen c.junction c.ih c.hUp c.rc c.hN c.hidx c.hkp hK₁L hK₁ hKB hR
      have heq : cqCard K₁ = cqCard B := by
        have := hRB.2.1
        omega
      obtain ⟨π, hπ, hk⟩ := hRB.2.2 heq
      have hBperf : Group.IsPerfect ↥B := (lt_inL_left hBA).isQuasisimple.1
      have hBK : KLike IsK B :=
        ⟨Y, inferInstance, σ.comp π, hσ.comp hπ, cover_comp π σ hk hσk, hY⟩
      have hBisK := isK_of_lt_step c hBK hRB.1 hBA (by omega) hA
      exact isK_quot_of_cover c.hKiso c.rc.K_quot c.rc.K_iso π hπ hBisK σ hσ hY

theorem desc_of_reach (c : DescCtx H N IsK S Up Lo R) {L₀ : Subgroup H} (hL₀ : InL L₀)
    (hL₀t : ∃ s ∈ S, OddCover s L₀) {K₁ L₁ : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsK K₁)
    (h : ReflTransGen Lt K₁ L₁) :
    (∃ π : ↥L₁ →* ↥K₁, Function.Surjective π ∧ π.ker ≤ center ↥L₁) ∨
      ((∃ s ∈ S, OddCover s L₁) ∧ IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) := by
  have hR := reach_base c hK₁L hK₁
  have hreach := reach_reflTransGen c.junction c.ih c.hUp c.rc c.hN c.hidx c.hkp hK₁L hK₁ h hR
  by_cases heq : cqCard K₁ = cqCard L₁
  · exact Or.inl (hreach.2.2 heq)
  · have hlt : cqCard K₁ < cqCard L₁ := lt_of_le_of_ne hreach.2.1 heq
    have hty := typeL_of_reach c hK₁L hK₁ hR hL₀ hL₀t L₁ h hlt
    exact Or.inr ⟨hty, isK_of_reach c hL₀ hL₀t hK₁L hK₁ L₁ h hlt hty⟩

theorem known_of_maximal {Y : Type} [Group Y] [Finite Y] (thm22 : Sol78Thm22At Y)
    (rc : ReachFacts IsK S Up Lo R) (hUY : Balance.UHered Y) {N' : Subgroup Y}
    (hFS : FStarSimple N')
    (hidx : N'.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hmax : Maximal P)
    (hR : R (↥P ⧸ center ↥P))
    (hns : ¬ ∃ s ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s)
    (hlow : Odd (Nat.card ↥(center ↥P)) → ¬ ∃ s ∈ Lo, IsSporadic (↥P ⧸ center ↥P) s)
    (hev : KEven IsK → ∀ (X : Type) [Group X], IsK X →
      Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P)) →
        HasEvenCover ↥N') (hscope : ClosureScope IsK N' P) : R ↥N' := by
  have hPq : CFSG.IsQuasisimple ↥P := hmax.1.isQuasisimple
  have hstd : StdBare P :=
    stdBare_of_maximal thm22 hkp hFS hidx hmax (rc.rank _ hPq hR fun _ => hns)
  exact rc.closure Y hUY N' hFS hidx hkp P (solStd_of_inL_of_stdBare hmax.1 hstd) hPq hR hns hlow
    hev hscope

theorem klike_hlow (rc : ReachFacts IsK S Up Lo R) {P : Subgroup H} (hPq : CFSG.IsQuasisimple ↥P)
    (hK : KLike IsK P) :
    Odd (Nat.card ↥(center ↥P)) → ¬ ∃ s ∈ Lo, IsSporadic (↥P ⧸ center ↥P) s := by
  obtain ⟨Y, _, σ, hσ, hσk, hY⟩ := hK
  have : Group.IsPerfect ↥P := hPq.1
  rintro hodd ⟨s, hs, ⟨f⟩⟩
  obtain ⟨e⟩ := cqEquiv_of_cover σ hσ hσk
  exact rc.K_odd_lo Y hY (odd_card_center_of_cover σ hσ hσk hodd) s hs ⟨e.symm.trans f⟩

theorem not_max_of_reach (c : DescCtx H N IsK S Up Lo R) {L₀ : Subgroup H} (hL₀ : InL L₀)
    (hL₀t : ∃ s ∈ S, OddCover s L₀) {K₁ : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsK K₁)
    {G₁ : Subgroup H} (hNG : N ≤ G₁) : ¬ (K₁ ≤ G₁ ∧ Maximal (K₁.subgroupOf G₁)) := by
  rintro ⟨hKG, hmax⟩
  have := c.hN.normal
  let N' : Subgroup ↥G₁ := N.subgroupOf G₁
  have hNe : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNG
  have hN'simple : IsSimpleGroup ↥N' := by
    have := c.hN.isSimpleGroup
    exact MulEquiv.isSimpleGroup hNe
  have hna : ∃ a b : ↥N', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := c.hN.nonabelian
    exact ⟨hNe.symm a, hNe.symm b, fun h => hab (hNe.symm.injective (by simpa [map_mul] using h))⟩
  have hC : centralizer (N' : Set ↥G₁) ≤ N' := by
    intro x hx
    have hxC : (x : H) ∈ centralizer (N : Set H) := by
      rw [mem_centralizer_iff]
      intro n hn
      have := mem_centralizer_iff.1 hx ⟨n, hNG hn⟩ hn
      exact congrArg Subtype.val this
    exact c.hN.centralizer_le hxC
  have hFS' : FStarSimple N' := fStarSimple_of_normal_simple hN'simple hna hC
  have hidx' : N'.index ≤ 2 := by
    have hdvd : N.relIndex G₁ ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N G₁
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd).trans c.hidx
  have hkp' := kProper_of_section c.hkp G₁ (MonoidHom.id ↥G₁) Function.surjective_id
  have hK₁' := hK₁
  obtain ⟨Y, _, σ, hσ, hσk, hY⟩ := hK₁'
  have hq₁ : CFSG.IsQuasisimple ↥K₁ := hK₁L.isQuasisimple
  have : Group.IsPerfect ↥K₁ := hq₁.1
  obtain ⟨e⟩ := cqEquiv_of_cover σ hσ hσk
  let eK : ↥(K₁.subgroupOf G₁) ≃* ↥K₁ := Subgroup.subgroupOfEquivOfLe hKG
  have hq' : CFSG.IsQuasisimple ↥(K₁.subgroupOf G₁) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hq₁
  have hR' : R (↥(K₁.subgroupOf G₁) ⧸ center ↥(K₁.subgroupOf G₁)) :=
    c.rc.iso _ _ (cqEquivOfMulEquiv eK).symm (reach_base c hK₁L hK₁)
  have hns : ¬ ∃ s ∈ S ++ Up, IsSporadic (↥(K₁.subgroupOf G₁) ⧸ center ↥(K₁.subgroupOf G₁)) s := by
    rintro ⟨s', hs', ⟨f⟩⟩
    exact c.rc.K_not_sporadic Y hY s' hs' ⟨e.symm.trans ((cqEquivOfMulEquiv eK).symm.trans f)⟩
  have hlow : Odd (Nat.card ↥(center ↥(K₁.subgroupOf G₁))) →
      ¬ ∃ s ∈ Lo, IsSporadic (↥(K₁.subgroupOf G₁) ⧸ center ↥(K₁.subgroupOf G₁)) s := by
    rintro hodd ⟨s', hs', ⟨f⟩⟩
    have hodd' : Odd (Nat.card ↥(center ↥K₁)) :=
      (Nat.card_congr (Subgroup.centerCongr eK).toEquiv) ▸ hodd
    exact klike_hlow c.rc hq₁ hK₁ hodd' ⟨s', hs', ⟨(cqEquivOfMulEquiv eK).symm.trans f⟩⟩
  have hev : KEven IsK → ∀ (X : Type) [Group X], IsK X →
      Nonempty ((↥(K₁.subgroupOf G₁) ⧸ center ↥(K₁.subgroupOf G₁)) ≃* (X ⧸ center X)) →
        Odd (Nat.card ↥(center ↥(K₁.subgroupOf G₁))) → HasEvenCover ↥N' := by
    intro hKeven X _ _ _ hodd
    exfalso
    have hodd' : Odd (Nat.card ↥(center ↥K₁)) :=
      (Nat.card_congr (Subgroup.centerCongr eK).toEquiv) ▸ hodd
    exact (Nat.not_even_iff_odd.2 hodd') (even_center_of_klike hq₁ hK₁ hKeven)
  have hKsub : KLike IsK (K₁.subgroupOf G₁) := by
    refine ⟨Y, inferInstance, σ.comp eK.toMonoidHom, hσ.comp eK.surjective, fun x hx => ?_, hY⟩
    have hz := Subgroup.mem_center_iff.1 (hσk (show eK x ∈ σ.ker from hx))
    rw [Subgroup.mem_center_iff]
    intro g
    exact eK.injective (by simpa using hz (eK g))
  have hRN' : R ↥N' :=
    known_of_maximal
      (c.thm22 ↥G₁ (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup G₁)) c.rc
      (c.ih.uHered.of_section (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup G₁))
      hFS' hidx' hkp' hmax hR' hns hlow hev (Or.inr (Or.inl hKsub))
  exact c.rc.notR H N c.hN c.hidx c.hkp ⟨L₀, hL₀, hL₀t⟩ (c.rc.iso _ _ hNe hRN')

end CFSG.EvenSporadicStandard.Induction.Hyp
