module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Small
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeSmall

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs (eq_top_of_card_lt_factorial_index
  card_small_cases_or_alt_eight)

private theorem exists_le_surj_of_isFiveComponent {Y : Type} [Group Y] {P : Subgroup Y}
    {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hC : IsFiveComponent P C) :
    ∃ (N : Subgroup Y) (ψ : ↥N →* alternatingGroup (Fin 5)), N ≤ P ∧ Function.Surjective ψ := by
  obtain ⟨-, f, hf⟩ := hC
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥P)
  set N' := C.comap π
  refine ⟨N'.map P.subtype, f.comp ((π.subgroupComap C).comp
    (N'.equivMapOfInjective P.subtype P.subtype_injective).symm.toMonoidHom), ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact hf.comp ((π.subgroupComap_surjective C (QuotientGroup.mk'_surjective _)).comp
      (MulEquiv.surjective _))

private theorem card_dvd_card_map_centerQuotient {Y : Type} [Group Y] [Finite Y]
    {L W : Subgroup Y} (hWL : W ≤ L) (hodd : Odd (Nat.card (Subgroup.center ↥L))) {U : Type}
    [Group U] [Finite U] [IsSimpleGroup U] (h2 : 2 ∣ Nat.card U) (ψ : ↥W →* U)
    (hψ : Function.Surjective ψ) :
    Nat.card U ∣ Nat.card ((W.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  set f : ↥W →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hWL) with hf
  have hk : f.ker ≤ ψ.ker := by
    have : (f.ker.map ψ).Normal := (MonoidHom.normal_ker f).map ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map ψ) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hU : Nat.card U ∣ Nat.card f.ker := by
        have := Subgroup.card_map_dvd f.ker ψ
        rwa [h, Subgroup.card_top] at this
      have hZ : Nat.card f.ker ∣ Nat.card (Subgroup.center ↥L) := by
        have hle : f.ker.map (Subgroup.inclusion hWL) ≤ Subgroup.center ↥L := by
          rintro _ ⟨w, hw, rfl⟩
          have : QuotientGroup.mk' (Subgroup.center ↥L) (Subgroup.inclusion hWL w) = 1 := hw
          exact (QuotientGroup.eq_one_iff _).mp this
        have := Subgroup.card_dvd_of_le hle
        rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWL)] at this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((h2.trans hU).trans hZ))
  obtain ⟨ψ', hψ', -⟩ := LeviBlock.exists_factor f.rangeRestrict f.rangeRestrict_surjective ψ hψ
    (by rw [MonoidHom.ker_rangeRestrict]; exact hk)
  have hr : f.range = (W.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [← hr]
  exact Subgroup.card_dvd_of_surjective hψ'

private theorem sixty_mem_of_isFiveComponent (hLB : LeviBlocksOfFiveComponents) {Y : Type}
    [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L) {K : Type} [Group K] [Finite K]
    (ρ : K →* ↥L) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K) {𝒯 : Set ℕ}
    (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯) {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)}
    (hC : IsFiveComponent P C) : 60 ∈ 𝒯 := by
  obtain ⟨k, G, _, _, S, β, hkerβ, hpi, hcomm, hS, h𝒯⟩ := hQ
  obtain ⟨j, hq, h60⟩ := (hLB Y L P hPL K ρ hρ hker (Fin k) G S β hkerβ hpi hcomm hS).1 C hC
  exact h60 ▸ h𝒯 j hq

private theorem small_card_five_void {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P)
    (h : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60 ∨ Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 ∨
      Nat.card (↥L ⧸ Subgroup.center ↥L) = 168 ∨ Nat.card (↥L ⧸ Subgroup.center ↥L) = 6048)
    {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hC : IsFiveComponent P C) : False := by
  have hPL : P ≤ L := hCP.parab.1
  obtain ⟨N, ψ, hNP, hψ⟩ := exists_le_surj_of_isFiveComponent hC
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h60N := card_dvd_card_map_centerQuotient (hNP.trans hPL) hCP.odd
    (by rw [hA5]; norm_num) ψ hψ
  rw [hA5] at h60N
  set Pb := (P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))
  have h60 : 60 ∣ Nat.card Pb :=
    h60N.trans (Subgroup.card_dvd_of_le (Subgroup.map_mono fun x hx => hNP hx))
  have hdvd : Nat.card Pb ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    Subgroup.card_subgroup_dvd_card _
  obtain ⟨-, T, ⟨hTL, -, hTi⟩, hNT⟩ := hCP.parab
  have hTP : T ≤ P := fun x hx => hNT ⟨hTL hx, Subgroup.le_normalizer hx⟩
  have hodd : ¬ 2 ∣ Pb.index := fun h2 => hTi (h2.trans
    ((Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)).trans
      (Subgroup.index_dvd_of_le fun x hx => hTP hx)))
  have hmul := Subgroup.card_mul_index Pb
  obtain ⟨m, hm⟩ := h60
  rw [hm] at hmul hdvd
  have hle : Pb.index ≤ 3 ∧ 60 ≤ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rcases h with h | h | h | h <;> rw [h] at hmul hdvd
    · have h1 : m * Pb.index = 1 := by linarith
      exact ⟨by rw [Nat.eq_one_of_mul_eq_one_left h1]; norm_num, by rw [h]⟩
    · have h6 : m * Pb.index = 6 := by linarith
      have hi : Pb.index ∣ 6 := Dvd.intro_left m h6
      have hi6 : Pb.index ≤ 6 := Nat.le_of_dvd (by norm_num) hi
      refine ⟨?_, by rw [h]; norm_num⟩
      interval_cases hidx : Pb.index <;> omega
    · exact absurd (dvd_of_mul_right_dvd hdvd) (by norm_num)
    · exact absurd (dvd_of_mul_right_dvd hdvd) (by norm_num)
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hCP.comp.2.2.2
  have htop : Pb = ⊤ := eq_top_of_card_lt_factorial_index (lt_of_le_of_lt
    ((Nat.factorial_le hle.1).trans (by decide : Nat.factorial 3 ≤ 6)) (by omega))
  have hZP : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ P := by
    intro z hz
    have hc : ∀ t : Y, t ∈ L → (z : Y) * t = t * (z : Y) := fun t ht =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t, ht⟩)).symm
    refine hNT ⟨z.2, Subgroup.mem_normalizer_iff.mpr fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
    · rw [hc t (hTL ht), mul_inv_cancel_right]
      exact ht
    · have h3 : (z : Y) * ((z : Y) * t * (z : Y)⁻¹) = (z : Y) * t := by
        rw [hc _ (hTL ht)]
        group
      have h4 : (z : Y) * t * (z : Y)⁻¹ = t := mul_left_cancel h3
      rw [h4] at ht
      exact ht
  refine hCP.ne_top (le_antisymm hPL fun l hl => ?_)
  have hmem : QuotientGroup.mk' (Subgroup.center ↥L) ⟨l, hl⟩ ∈ Pb := htop ▸ Subgroup.mem_top _
  obtain ⟨p, hp, hpl⟩ := Subgroup.mem_map.mp hmem
  have hz : p⁻¹ * ⟨l, hl⟩ ∈ Subgroup.center ↥L := QuotientGroup.eq.mp hpl
  have := P.mul_mem (Subgroup.mem_subgroupOf.mp hp) (hZP _ hz)
  simpa using this

private theorem alt_eight_five_void (hZ : OddCenterRest) (hLB : LeviBlocksOfFiveComponents)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (hS : IsSmallTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (e8 : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8))
    {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hC : IsFiveComponent P C) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
    ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨e8⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hZ1 : Subgroup.center ↥L = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rcases hZ Y L hCP.comp hCP.odd (Or.inr (Or.inr (Or.inr (Or.inr hS)))) with h1 | ⟨-, ⟨e6⟩⟩
    · exact h1
    · exfalso
      have h := Nat.card_congr (e6.symm.trans e8).toEquiv
      simp only [nat_card_alternatingGroup, Nat.card_fin] at h
      exact absurd h (by decide)
  let ι : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥L))
      ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ1]),
        QuotientGroup.mk'_surjective _⟩
  let ρ : Matrix.SpecialLinearGroup (Fin 4) K →* ↥L :=
    ι.symm.toMonoidHom.comp (e.symm.toMonoidHom.comp (LinearFlag.proj 4 K))
  have hρs : Function.Surjective ρ :=
    ι.symm.surjective.comp (e.symm.surjective.comp (LinearFlag.proj_surjective 4 K))
  have hρ : ∀ g, e (QuotientGroup.mk (ρ g)) = LinearFlag.proj 4 K g := fun g => by
    show e (ι (ι.symm (e.symm (LinearFlag.proj 4 K g)))) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  obtain ⟨σ, e', I, hσs, hσ, -, hcomap, -, -⟩ :=
    exists_comap_eq_flagStabilizer hCP.odd (by norm_num) e hρs hρ hCP.parab
  have hker : σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : LinearFlag.proj 4 K g = 1 := by
      rw [← hσ g, hg, QuotientGroup.mk_one, map_one]
    exact LinearFlag.scalars_le_center 4 K (LinearFlag.proj_eq_one_iff.1 h1)
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap σ) (linBlockOrders K) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by norm_num) I
  obtain ⟨m, -, h60⟩ := sixty_mem_of_isFiveComponent hLB hCP.parab.1 σ hσs hker hQ hC
  have h4 := ((ordA_eq_sixty_iff (f := 1) hK).1 h60.symm).2
  rw [hK] at h4
  norm_num at h4

private theorem small_five_void (hZ : OddCenterRest) (hLB : LeviBlocksOfFiveComponents)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (hS : IsSmallTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)}
    (hC : IsFiveComponent P C) : False := by
  rcases card_small_cases_or_alt_eight hS with h | ⟨⟨e8⟩⟩
  · exact small_card_five_void hCP h hC
  · exact alt_eight_five_void hZ hLB hCP hS e8 hC

theorem kFactCompParabTwoFivesOn_small (hZ : OddCenterRest) (hLB : LeviBlocksOfFiveComponents) :
    KFactCompParabTwoFivesOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS _ C₁ _ _ hC₁ _
  exact (small_five_void hZ hLB hCP hS hC₁).elim

theorem kFactCompParabOneFiveOn_small (hZ : OddCenterRest) (hLB : LeviBlocksOfFiveComponents) :
    KFactCompParabOneFiveOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS C hC
  exact (small_five_void hZ hLB hCP hS hC).elim

end CFSG.AGLEmbedding
