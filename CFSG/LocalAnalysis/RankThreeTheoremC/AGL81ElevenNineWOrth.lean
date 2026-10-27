module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWIndex
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveOrth
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OrthMinus
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveBlockOK
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveTower
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexOrthPlus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.OrthogonalInvolutions
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (IsWBlock)
open scoped commutatorElement

section Plane

variable {K : Type} [Field K] {b c : K}

theorem isOmegaTwisted_pow {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} {e : K}
    (hg : IsOmegaTwisted b c g e) : ∀ n : ℕ, IsOmegaTwisted b c (g ^ n) (n • e)
  | 0 => by
    rw [pow_zero, zero_nsmul]
    exact (omegaRotations b c).one_mem
  | n + 1 => by
    rw [pow_succ, succ_nsmul]
    exact (isOmegaTwisted_pow hg n).mul hg

theorem isOmegaTwisted_zero_of_odd [Finite K] [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c))
    (ho : Odd (orderOf g)) : IsOmegaTwisted b c g 0 := by
  have hb := minusPlane_b_ne_zero hirr
  obtain ⟨l, hl | hl, hgl⟩ := isOmegaTwisted_of_mem_orthogonalGroup hb hg
  · rwa [hl] at hgl
  · exfalso
    have h1 := isOmegaTwisted_pow hgl (orderOf g)
    rw [pow_orderOf_eq_one] at h1
    have hn : orderOf g • l = l := by
      obtain ⟨k, hk⟩ := ho
      rw [hk, add_nsmul, one_nsmul, two_mul, add_nsmul, CharTwo.add_self_eq_zero, zero_add]
    rw [hn] at h1
    unfold IsOmegaTwisted at h1
    have h2 : (l • (1 : Module.End K (Fin 2 → K))) = 0 := by
      have h3 : ((1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) : Module.End K (Fin 2 → K)) = 1 := rfl
      rw [h3, one_mul, mul_one] at h1
      exact (add_eq_left.mp h1.symm)
    have h4 := congrArg (fun f : Module.End K (Fin 2 → K) => f (Pi.single 0 1) 0) h2
    simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, LinearMap.zero_apply, Pi.zero_apply] at h4
    exact hb (hl ▸ h4)

theorem commute_of_odd_of_mem_orthogonalGroup_tail [Finite K] [CharP K 2] {m : ℕ} (hm : m = 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g h : ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin m ⊕ Fin m → K) × (Fin 2 → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))
    (hgo : Odd (orderOf g)) (hho : Odd (orderOf h)) : g * h = h * g := by
  subst hm
  set φ := LinearEquiv.autCongr (minusTailZeroIsometry (K := K) (b := b) (c := c)).toLinearEquiv
  have hmem : ∀ {x}, x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K b c)) →
      φ x ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c) := fun hx => by
    rw [← orthMinus_map_autCongr_orthogonalGroup (minusTailZeroIsometry (K := K) (b := b) (c := c))]
    exact ⟨_, hx, rfl⟩
  refine φ.injective ?_
  rw [map_mul, map_mul]
  exact commute_of_isOmegaTwisted_zero
    (isOmegaTwisted_zero_of_odd hirr (hmem hg) (by rw [MulEquiv.orderOf_eq]; exact hgo))
    (isOmegaTwisted_zero_of_odd hirr (hmem hh) (by rw [MulEquiv.orderOf_eq]; exact hho))

end Plane

section LeviData

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r s : ℕ} {d : Fin (s + 1) → ℕ} {b c : K}

variable (K r d) in
@[expose] noncomputable def orthLeviBlockZ (b c : K) : ∀ j, Subgroup (orthLeviGroup K r d j)
  | .inl l => orthLeviBlock K r d b c (.inl l)
  | .inr _ => ⊥

variable (K r d) in
@[expose] noncomputable def orthLeviTop (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    ∀ j, Subgroup (orthLeviGroup K r d j)
  | .inl _ => ⊤
  | .inr _ => omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))

theorem range_orthLeviHom_le_pi_top (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) :
    (orthLeviHom b c hd).range ≤ Subgroup.pi Set.univ (orthLeviTop K r d hirr) := by
  rintro _ ⟨z, rfl⟩
  rw [Subgroup.mem_pi]
  rintro (l | u) -
  · exact Subgroup.mem_top _
  · exact ParabCensus.orthResHom_mem_omegaGroup hd hr hirr z

theorem not_two_dvd_relIndex_orthLeviBlock_inl (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (l : Fin s) :
    ¬ 2 ∣ (orthLeviBlock K r d b c (.inl l)).relIndex (orthLeviTop K r d hirr (.inl l)) := by
  change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
      GL (Fin (d l.succ - d l.castSucc)) K).range).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact ParabCensus.not_two_dvd_index_range_toGL _

theorem orthLeviBlock_inl_eq_bot_or_isWBlock (l : Fin s) :
    orthLeviBlock K r d b c (.inl l) = ⊥ ∨ IsWBlock ↥(orthLeviBlock K r d b c (.inl l)) := by
  rcases ParabCensus.range_toGL_cases (K := K) (d l.succ - d l.castSucc) with
    hbot | ⟨-, -, hs⟩ | ⟨hq, hodd⟩
  · exact Or.inl hbot
  · exact Or.inr (Or.inr hs)
  · exact Or.inr (Or.inl ⟨hq, hodd⟩)

theorem blockOKP_orthLeviBlock_inl {p : ℕ} [OddPrime p] (l : Fin s)
    (hne : orthLeviBlock K r d b c (.inl l) ≠ ⊥) :
    BlockOKP p (orthMinus_leviOver K r d b c (.inl l)) (orthLeviBlock K r d b c (.inl l)) := by
  change BlockOKP p ⊤ (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range
  rcases ParabCensus.range_toGL_cases (K := K) (d l.succ - d l.castSucc) with
    hbot | ⟨-, hm, -⟩ | ⟨hq, -⟩
  · exact absurd hbot hne
  · exact blockOK_gl_slP (p := p) _ (by omega)
  · exact blockOK_gl_slP (p := p) _ (two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq))

theorem commutator_range_le_pi_orthLeviBlockZ (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hm0 : r - d (Fin.last s) = 0) :
    ⁅(orthLeviHom b c hd).range, (orthLeviHom b c hd).range⁆ ≤
      Subgroup.pi Set.univ (orthLeviBlockZ K r d b c) := by
  intro z hz
  rw [Subgroup.mem_pi]
  rintro (l | u) -
  · exact (Subgroup.mem_pi _).1 (commutator_range_orthLeviHom_le hd hz) (.inl l) trivial
  · let ev := Pi.evalMonoidHom (orthLeviGroup K r d) (Sum.inr u : Fin s ⊕ Unit)
    have hA : ∀ y ∈ (orthLeviHom b c hd).range.map ev,
        y ∈ TauCeti.QuadraticMap.orthogonalGroup
          (quadTail (r - d (Fin.last s)) (minusTailForm K b c)) ∧ Odd (orderOf y) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      have hx := ParabCensus.orthResHom_mem_omegaGroup hd hr hirr x
      exact ⟨omegaGroup_le _ _ hx, (ParabCensus.odd_card_omegaGroup_tail_of_eq_zero hm0
        hirr).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)⟩
    have hbot : ⁅(orthLeviHom b c hd).range.map ev, (orthLeviHom b c hd).range.map ev⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      obtain ⟨h1, h2⟩ := hA y hy
      obtain ⟨h1', h2'⟩ := hA y' hy'
      exact commute_of_odd_of_mem_orthogonalGroup_tail hm0 hirr h1' h1 h2' h2
    have hmem : ev z ∈ ⁅(orthLeviHom b c hd).range.map ev, (orthLeviHom b c hd).range.map ev⁆ := by
      rw [← Subgroup.map_commutator]
      exact ⟨z, hz, rfl⟩
    rw [hbot] at hmem
    exact hmem

theorem pi_orthLeviBlockZ_le :
    Subgroup.pi Set.univ (orthLeviBlockZ K r d b c) ≤
      Subgroup.pi Set.univ (orthLeviBlock K r d b c) := by
  intro x hx
  rw [Subgroup.mem_pi] at hx ⊢
  rintro (l | u) -
  · exact hx (.inl l) trivial
  · have h := hx (.inr u) trivial
    change x (.inr u) ∈ (⊥ : Subgroup _) at h
    rw [Subgroup.mem_bot.mp h]
    exact Subgroup.one_mem _

theorem odd_relIndex_orthLeviBlockZ (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hm0 : r - d (Fin.last s) = 0) :
    Odd ((Subgroup.pi Set.univ (orthLeviBlockZ K r d b c)).relIndex
      (orthLeviHom b c hd).range) := by
  have hle : Subgroup.pi Set.univ (orthLeviBlockZ K r d b c) ≤ (orthLeviHom b c hd).range :=
    pi_orthLeviBlockZ_le.trans
      (pi_orthLeviBlock_le_range hd hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
  refine Nat.not_even_iff_odd.mp fun he => ?_
  refine ParabCensus.not_two_dvd_relIndex_pi_of_finite (T := orthLeviTop K r d hirr) ?_ hle
    (range_orthLeviHom_le_pi_top hd hr hirr) ?_ (even_iff_two_dvd.mp he)
  · rintro (l | u)
    · exact le_top
    · exact bot_le
  · rintro (l | u)
    · exact not_two_dvd_relIndex_orthLeviBlock_inl hirr l
    · change ¬ 2 ∣ (⊥ : Subgroup (orthLeviGroup K r d (.inr u))).relIndex
        (omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
          (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))
      rw [Subgroup.relIndex_bot_left]
      exact (ParabCensus.odd_card_omegaGroup_tail_of_eq_zero hm0 hirr).not_two_dvd_nat

theorem odd_relIndex_orthLeviBlock (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hm1 : 1 ≤ r - d (Fin.last s)) :
    Odd ((Subgroup.pi Set.univ (orthLeviBlock K r d b c)).relIndex
      (orthLeviHom b c hd).range) := by
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  refine Nat.not_even_iff_odd.mp fun he => ?_
  refine ParabCensus.not_two_dvd_relIndex_pi_of_finite (T := orthLeviTop K r d hirr) ?_
    (pi_orthLeviBlock_le_range hd hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
    (range_orthLeviHom_le_pi_top hd hr hirr) ?_ (even_iff_two_dvd.mp he)
  · rintro (l | u)
    · exact le_top
    · exact CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup
        (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))
  · rintro (l | u)
    · exact not_two_dvd_relIndex_orthLeviBlock_inl hirr l
    · change ¬ 2 ∣ (orthResDer K b c (r - d (Fin.last s))).relIndex
        (omegaGroup (quadTail (r - d (Fin.last s)) (minusTailForm K b c))
          (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))
      rw [ParabCensus.relIndex_orthResDer_omegaGroup hK hm1 hirr]
      norm_num

theorem orthResDer_isQuasisimple_center (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) {m : ℕ}
    (hm1 : 1 ≤ m) : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m) ∧
      Subgroup.center ↥(orthResDer K b c m) = ⊥ := by
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨hsimple, hna, -⟩ := orthResDer_facts (K := K) (b := b) (c := c) hK hm1 hirr
  haveI := hsimple
  exact orthMinus_isQuasisimple_of_simple hna

end LeviData

theorem leviInnOnPW_orthMinus (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : LeviInnOnPW p (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hC hLn _ _ hrk
  haveI := hLn
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  obtain ⟨dI, hdI, ⟨e⟩⟩ := id hC
  obtain ⟨K, _, _, _, b, c, r, s, d, ρ, hr, hirr, hcuts, hρ, -⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hker : ρ.toMonoidHom.ker ≤ Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective]
    exact bot_le
  have hρo : Odd (Nat.card ρ.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective, Subgroup.card_bot]
    exact odd_one
  have hH : ∀ (x : ↥(orthParab r (minusTailForm K b c) d)) (j : Fin s ⊕ Unit),
      orthLeviHom b c hcuts x j ∈ orthMinus_leviOver K r d b c j := by
    rintro x (l | u)
    · exact Subgroup.mem_top _
    · exact orthResHom_mem_orthogonalGroup hcuts _
  have hinj : ∀ x : ↥(orthParab r (minusTailForm K b c) d),
      ρ.toMonoidHom (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) = 1 → x = 1 :=
    fun x hx => Subtype.ext (ρ.injective (hx.trans (map_one ρ).symm))
  by_cases hm0 : r - d (Fin.last s) = 0
  · refine leviInnAtW_of_levi_data_index (OddPrime.ne_two p) hCP.parab.1 hCP.odd ρ.toMonoidHom
      ρ.surjective hker hρo _ hρ.symm (orthLeviBlockZ K r d b c) (orthMinus_leviOver K r d b c)
      (orthLeviHom b c hcuts) (isPGroup_ker_orthLeviHom hcuts)
      (pi_orthLeviBlockZ_le.trans (pi_orthLeviBlock_le_range hcuts hr
        (commutator_orthogonalGroup_quadTail_minus hr hirr)))
      (commutator_range_le_pi_orthLeviBlockZ hcuts hr hirr hm0)
      (odd_relIndex_orthLeviBlockZ hcuts hr hirr hm0) ?_ (fun x j => hH x j) ?_
      (fun j A _ _ _ x hx _ => hinj x hx) (fun j _ x hx _ => by rw [hinj x hx, map_one]) hrk
    · rintro (l | u)
      · exact orthLeviBlock_inl_eq_bot_or_isWBlock (b := b) (c := c) l
      · exact Or.inl rfl
    · rintro (l | u) hne
      · exact blockOKP_orthLeviBlock_inl (b := b) (c := c) l hne
      · exact absurd rfl hne
  · have hm1 : 1 ≤ r - d (Fin.last s) := by omega
    obtain ⟨hq, hcen⟩ := orthResDer_isQuasisimple_center (K := K) (b := b) (c := c) hirr hm1
    refine leviInnAtW_of_levi_data_index (OddPrime.ne_two p) hCP.parab.1 hCP.odd ρ.toMonoidHom
      ρ.surjective hker hρo _ hρ.symm (orthLeviBlock K r d b c) (orthMinus_leviOver K r d b c)
      (orthLeviHom b c hcuts) (isPGroup_ker_orthLeviHom hcuts)
      (pi_orthLeviBlock_le_range hcuts hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
      (commutator_range_orthLeviHom_le hcuts) (odd_relIndex_orthLeviBlock hcuts hr hirr hm1) ?_
      (fun x j => hH x j) ?_
      (fun j A _ _ _ x hx _ => hinj x hx) (fun j _ x hx _ => by rw [hinj x hx, map_one]) hrk
    · rintro (l | u)
      · exact orthLeviBlock_inl_eq_bot_or_isWBlock (b := b) (c := c) l
      · refine Or.inr (Or.inl ⟨hq, ?_⟩)
        change Odd (Nat.card (Subgroup.center ↥(orthResDer K b c (r - d (Fin.last s)))))
        rw [hcen, Subgroup.card_bot]
        exact odd_one
    · rintro (l | u) hne
      · exact blockOKP_orthLeviBlock_inl (b := b) (c := c) l hne
      · exact orthMinus_blockOK_orthResDerP p hirr _ hq

theorem fieldIndexOnPW_orthMinus (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : FieldIndexOnPW p (IsLieOf IdxTwistedD) :=
  fieldIndexOnPW_of_outPNice (fun _ _ _ _ _ _ hC _ => outPNiceP_of_idxTwistedD p hC)
    (leviInnOnPW_orthMinus p hGA)

theorem fieldIndexOnPW_orthPlus (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : FieldIndexOnPW p (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD _ hrank
  exfalso
  have h4 := four_le_pRank_idxD (oddCenterRest_of_griess hGA) hCP.comp hCP.odd hD
  have h3 := hrank 3 Nat.prime_three (by norm_num)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
