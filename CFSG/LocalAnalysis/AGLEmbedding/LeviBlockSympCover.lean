module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)

noncomputable def spFlagProjEquiv (r : ℕ) (K : Type) [Field K] [CharP K 2] :
    StatedProj (StatedSp r K) ≃* StatedSp r K :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot r)).trans
    QuotientGroup.quotientBot

theorem exists_mulEquiv_statedSp_of_idxB (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hB : IsLieOf IdxB (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 2 ≤ r ∧
      Nonempty (↥L ≃* StatedSp r K) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hB
  cases d
  case B r q =>
    have hq2 : q.p = 2 := hd
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr : 2 ≤ r := hrange.1
    have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by omega) e
        rwa [hq2] at hm
    obtain ⟨⟨-, hf, -⟩, K, hKf, hKfin, hK, ⟨e'⟩⟩ := hmodel
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    refine ⟨r, K, hKf, hKfin, inferInstance, hr, ?_⟩
    have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rcases hZ Y L hL hodd (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩) with h1 | ⟨-, ⟨e6⟩⟩
      · exact h1
      · exfalso
        have h360 : Nat.card (StatedProj (StatedSp r K)) = 360 := by
          rw [← Nat.card_congr e'.toEquiv, Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
          simp [Nat.factorial]
        rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK] at h360
        have hdvd : 2 ^ 4 ∣ 360 := by
          rw [← h360]
          refine Dvd.dvd.mul_right ?_ _
          rw [← pow_mul]
          exact Nat.pow_dvd_pow 2 (by nlinarith)
        norm_num at hdvd
    have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    exact ⟨((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      hbot.symm)).trans e').trans (spFlagProjEquiv r K)⟩
  all_goals exact hd.elim

variable {r : ℕ} {K : Type} [Field K]

theorem exists_flagStabilizer_of_compParab [Finite K] [CharP K 2] {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P) (φ : ↥L ≃* StatedSp r K) :
    ∃ (ρ : StatedSp r K ≃* ↥L) (I : Set ℕ) (t : ℕ), (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧ t ∈ I ∧
      (∀ c ∈ I, c ≤ t) ∧ (P.subgroupOf L).comap ρ.toMonoidHom = flagStabilizer r K I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPL, T, ⟨hTL, hT2, hTi⟩, hNP⟩ := hCP.parab
  set T₀ : Subgroup ↥L := T.subgroupOf L
  have hNT₀ : Subgroup.normalizer (T₀ : Set ↥L) ≤ P.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNP ⟨x.2, Subgroup.mem_normalizer_fintype fun s hs => ?_⟩
    have h1 : (⟨s, hTL hs⟩ : ↥L) ∈ T₀ := Subgroup.mem_subgroupOf.2 hs
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨s, hTL hs⟩).1 h1
    simpa [T₀, Subgroup.mem_subgroupOf] using h2
  have hT₁ : IsPGroup 2 (T₀.map φ.toMonoidHom) := (hT2.comap_subtype (K := L)).map _
  have hT₁i : ¬ 2 ∣ (T₀.map φ.toMonoidHom).index := by
    rw [show φ.toMonoidHom = (φ : ↥L →* StatedSp r K) from rfl, Subgroup.index_map_equiv]
    exact hTi
  let S₁ : Sylow 2 (StatedSp r K) := hT₁.toSylow hT₁i
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp r K) U S₁
  let ψ : ↥L ≃* StatedSp r K := φ.trans (MulAut.conj x⁻¹)
  have hψT : T₀.map ψ.toMonoidHom = SymplecticFlag.unipotent r K := by
    have h1 : ((x • U : Sylow 2 (StatedSp r K)) : Subgroup (StatedSp r K)) =
        T₀.map φ.toMonoidHom := by rw [hx]; rfl
    rw [Sylow.coe_subgroup_smul, hU] at h1
    have h1' : T₀.map φ.toMonoidHom =
        (SymplecticFlag.unipotent r K).map (MulAut.conj x).toMonoidHom := by
      rw [← h1]
      rfl
    have h2 : T₀.map ψ.toMonoidHom = (T₀.map φ.toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    have : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      change x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [h2, h1', Subgroup.map_map, this, Subgroup.map_id]
  have hB : SymplecticFlag.borelSubgroup r K ≤ (P.subgroupOf L).map ψ.toMonoidHom := by
    rw [← SymplecticHigher.normalizer_unipotent, ← hψT,
      ← Subgroup.map_normalizer_eq_of_bijective _ ψ.bijective]
    exact Subgroup.map_mono hNT₀
  obtain ⟨hPeq, -⟩ := SymplecticHigher.borel_overgroups _ hB
  set I := SymplecticHigher.borelCuts K ((P.subgroupOf L).map ψ.toMonoidHom)
  have hI := SymplecticHigher.borelCuts_le (K := K) ((P.subgroupOf L).map ψ.toMonoidHom)
  have hcomap : (P.subgroupOf L).comap ψ.symm.toMonoidHom = flagStabilizer r K I := by
    rw [← hPeq, Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]
  have hne : I.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have htop : (P.subgroupOf L).comap ψ.symm.toMonoidHom = ⊤ := by
      rw [hcomap, hemp, SymplecticHigher.flagStabilizer_empty]
    apply hCP.ne_top
    refine le_antisymm hPL fun y hy => ?_
    have hyψ : ψ ⟨y, hy⟩ ∈ (P.subgroupOf L).comap ψ.symm.toMonoidHom := htop ▸ Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using hyψ
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  set t := Nat.findGreatest (· ∈ I) r
  refine ⟨ψ.symm, I, t, hI, Nat.findGreatest_spec (hI i₀ hi₀).2 hi₀,
    fun c hc => Nat.le_findGreatest (hI c hc).2 hc, hcomap⟩

theorem exists_hasLeviBlocks_of_idxB (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) (hB : IsLieOf IdxB (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (𝒯 : Set ℕ),
      Function.Surjective ρ ∧ HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯 ∧ 5515776 ∉ 𝒯 ∧
        25920 ∉ 𝒯 := by
  obtain ⟨r, K, _, _, _, -, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  obtain ⟨f, -, hq⟩ := spFlag_card_eq_two_pow (K := K)
  refine ⟨StatedSp r K, inferInstance, inferInstance, ρ.toMonoidHom, spBlockOrders (Nat.card K),
    ρ.surjective, ?_, u38_not_mem_spBlockOrders hq, u42_not_mem_spBlockOrders hq⟩
  rw [hρ]
  exact hasLeviBlocks_spFlag hI htI hmax

end CFSG.AGLEmbedding.LeviBlock
