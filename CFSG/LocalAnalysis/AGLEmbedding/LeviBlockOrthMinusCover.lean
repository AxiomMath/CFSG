module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedASetup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

theorem orthMinus_sixteen_dvd {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) :
    16 ∣ CFSG.Open.ordTwistedD n (2 ^ f) := by
  rw [CFSG.Open.ordTwistedD, CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hf (by omega)), Nat.div_one]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  rw [← pow_mul]
  calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ (f * (n * (n - 1))) := pow_dvd_pow 2
      ((show 4 ≤ n * (n - 1) by nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]).trans
        (Nat.le_mul_of_pos_left _ hf))

theorem exists_mulEquiv_orthElementary_of_twistedD (hZ : OddCenterRest) {Y : Type} [Group Y]
    [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (dI : TauCeti.ValidLieTypeIndex)
    (hdI : IdxTwistedD dI.1) (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie dI).Group) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
      3 ≤ r ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        (∀ n q, dI.1 = .twistedD n q → Nat.card K = q.card) ∧
        Nonempty (↥L ≃* ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) := by
  obtain ⟨dI, hv⟩ := dI
  cases dI
  case twistedD n q =>
    have hq2 : q.p = 2 := hdI
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv
      hq2 e
    rw [hq2] at hmodel
    obtain ⟨⟨-, hf, hn⟩, K, hKf, hKfin, hK, b, c, hirr, ⟨e'⟩⟩ := hmodel
    have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    refine ⟨n - 1, K, hKf, hKfin, inferInstance, b, c, by omega, hirr, fun n₁ q₁ h₁ => ?_, ?_⟩
    · injection h₁ with h₂ h₃
      rw [← h₃, hK, TauCeti.PrimePower.card_def, hq2]
    have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rcases hZ Y L hL hodd (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hdI, ⟨e⟩⟩))) with h1 | ⟨-, ⟨e6⟩⟩
      · exact h1
      · exfalso
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
    have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    exact ⟨((((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      hbot.symm)).trans e').trans (orthMinusStatedProjEquiv (by omega))).trans
        (tailOmegaEquiv (minusTailIsometry n K b c) (coe_quadMinus n K b c)
          (commutator_orthogonalGroup_quadMinus hn hirr)))⟩
  all_goals exact hdI.elim

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

open scoped Pointwise in
theorem exists_comap_eq_orthParab {r : ℕ} (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hP : IsParabolicTwo L P)
    (φ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥L) :
    ∃ (ρ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥L) (s : ℕ)
      (d : Fin (s + 1) → ℕ), OrthCuts r d ∧
        (P.subgroupOf L).comap ρ.toMonoidHom = orthParab r (minusTailForm K b c) d := by
  classical
  set E := orthElementaryGroup (quadTail r (minusTailForm K b c)) with hEdef
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  obtain ⟨T₀, hT₀⟩ := ToralCensus.exists_sylow_normalizer_le_comap_of_surjective
    (ρ := φ.toMonoidHom) φ.surjective hP
  obtain ⟨⟨U, hU⟩, hNU, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr hani hreg
    (Or.inr finrank_fin_two_fun)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq E U T₀
  have hxU : (T₀ : Subgroup E) = (U : Subgroup E).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  set ρ : E ≃* ↥L := (MulAut.conj x).trans φ with hρdef
  have hB : (tailBorel r (minusTailForm K b c)).subgroupOf E ≤
      (P.subgroupOf L).comap ρ.toMonoidHom := by
    intro y hy
    rw [← hNU, ← hU] at hy
    have h1 : (MulAut.conj x).toMonoidHom y ∈ Subgroup.normalizer ((T₀ : Subgroup E) : Set E) := by
      rw [hxU, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.mem_map_of_mem _ hy
    exact hT₀ h1
  set M := ((P.subgroupOf L).comap ρ.toMonoidHom).map E.subtype with hMdef
  have hMG : M ≤ E := Subgroup.map_subtype_le _
  have hBM : tailBorel r (minusTailForm K b c) ≤ M := fun z hz =>
    ⟨⟨z, tailBorel_le hz⟩, hB (Subgroup.mem_subgroupOf.2 hz), rfl⟩
  have ha₀ : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have hM' := tail_overgroup_stabilizers hani ha₀ hMG hBM
  set Jf : Finset (Fin r) :=
    Finset.univ.filter (fun i => tailWeylElt r (minusTailForm K b c) (Pi.single 0 1) i ∉ M)
  set D : Finset ℕ := insert 0 (Jf.image fun i : Fin r => (i : ℕ) + 1) with hD
  have h0D : 0 ∈ D := Finset.mem_insert_self _ _
  obtain ⟨s, hs⟩ : ∃ s, D.card = s + 1 := ⟨D.card - 1, by
    have := Finset.card_pos.2 ⟨0, h0D⟩
    omega⟩
  set d : Fin (s + 1) → ℕ := fun k => D.orderEmbOfFin hs k with hd
  have hdmem : ∀ k, d k ∈ D := fun k => Finset.orderEmbOfFin_mem D hs k
  have hdrange : ∀ m ∈ D, ∃ k, d k = m := fun m hm => by
    have : m ∈ Set.range (D.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hm
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk⟩
  have hDle : ∀ m ∈ D, m ≤ r := fun m hm => by
    rcases Finset.mem_insert.1 hm with rfl | hm
    · omega
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hm
      exact i.isLt
  have hcuts : OrthCuts r d := by
    refine ⟨(D.orderEmbOfFin hs).strictMono, ?_, hDle _ (hdmem _)⟩
    obtain ⟨k₀, hk₀⟩ := hdrange 0 h0D
    have := (D.orderEmbOfFin hs).monotone (Fin.zero_le k₀)
    change d 0 ≤ d k₀ at this
    omega
  refine ⟨ρ, s, d, hcuts, ?_⟩
  ext y
  rw [mem_orthParab, ← Subgroup.mem_map_iff_mem E.subtype_injective, ← hMdef, hM',
    Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, Submodule.mem_stabilizer_submodule_iff_map_eq]
  refine ⟨fun ⟨_, h⟩ k => ?_, fun h => ⟨y.2, fun i hi => ?_⟩⟩
  · rcases Finset.mem_insert.1 (hdmem k) with h0 | hk
    · rw [h0, tailFlag_zero, Submodule.map_bot]
    · obtain ⟨i, hi, hik⟩ := Finset.mem_image.1 hk
      rw [← hik]
      exact h i (Finset.mem_filter.1 hi).2
  · obtain ⟨k, hk⟩ := hdrange ((i : ℕ) + 1)
      (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩,
        rfl⟩))
    have := h k
    rwa [hk] at this

theorem exists_orthCover_of_twistedD (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) (dI : TauCeti.ValidLieTypeIndex)
    (hdI : IdxTwistedD dI.1) (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie dI).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K) (r s : ℕ)
      (d : Fin (s + 1) → ℕ) (ρ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥L),
      3 ≤ r ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ OrthCuts r d ∧
        (P.subgroupOf L).comap ρ.toMonoidHom = orthParab r (minusTailForm K b c) d ∧
        ∀ n q, dI.1 = .twistedD n q → Nat.card K = q.card := by
  obtain ⟨r, K, hKf, hKfin, hK2, b, c, hr, hirr, hq, ⟨φ⟩⟩ :=
    exists_mulEquiv_orthElementary_of_twistedD hZ hCP.comp hCP.odd dI hdI e
  obtain ⟨ρ, s, d, hcuts, hρ⟩ := exists_comap_eq_orthParab hr hirr hCP.parab φ.symm
  exact ⟨K, hKf, hKfin, hK2, b, c, r, s, d, ρ, hr, hirr, hcuts, hρ, hq⟩

end CFSG.AGLEmbedding.LeviBlock
