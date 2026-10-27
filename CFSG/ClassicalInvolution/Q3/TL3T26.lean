module

public import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.ClassicalInvolution.SmallCases.A7Q1

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

@[expose] def ThmD1GenBelow (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 2 ^ r) →
    (∀ J ∈ Ω, AEmpty Ω J) →
    ∀ P : Set (Subgroup G), P ⊆ Ω → Nat.card ↥(pSpan P) < n →
    (∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) →
    classicalInvolutionOddCore ↥(pSpan P) = ⊥ →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    ∀ L ∈ P, ∀ L' ∈ P, (¬ ∃ x ∈ pSpan P, conjSub x L = L') →
      ∀ a ∈ L, ∀ b ∈ L', a * b = b * a

@[expose] def D1GenLeaf (r : ℕ) : Prop := ∀ n, ThmDGenBelow r n → ThmD1GenBelow r n

theorem oddCoreImg_le_of_le_normalizer {H M : Subgroup G} (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set G)) : oddCoreImg H ≤ oddCoreImg M :=
  TC.le_oddCoreImg_of_normalizes ((oddCoreImg_le H).trans hHM)
    (fun _ hm _ ho => conj_mem_oddCoreImg (hMN hm) ho) (odd_natCard_oddCoreImg H)

omit [Finite G] in
theorem oddCore_eq_bot_of_oddCoreImg {H : Subgroup G} (h : oddCoreImg H = ⊥) :
    classicalInvolutionOddCore ↥H = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h

variable {r : ℕ} {Ω : Set (Subgroup G)}

theorem comm_of_mem_omegaNbr (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJΩ, hJK, hJN⟩ := (TC.mem_omegaNbr_iff hΩ h2).mp hJ
  have hP2 : IsPGroup 2 ↥(J ⊔ K) := (h2 J hJΩ).to_sup_of_normal_right' (h2 K hK) hJN
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  exact Q3CP.l67Gen G Ω hΩ S K (TC.mem_RSet_of_isPGroup hK (h2 K hK)) J
    (TC.mem_RSet_of_isPGroup hJΩ (h2 J hJΩ)) (le_sup_right.trans hPS) (le_sup_left.trans hPS)
    (Ne.symm hJK)

theorem conjSub_mem_kPerp (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {c : G} (hc : c * z = z * c) {L : Subgroup G}
    (hL : L ∈ KPerp Ω K) : conjSub c L ∈ KPerp Ω K := by
  have hcz : c * z * c⁻¹ = z := by rw [hc]; group
  have htw : conjSub c K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
  rw [A7Q.Gen.kPerp_eq_of_twin hΩ hK htw]
  rcases Set.mem_insert_iff.mp hL with rfl | hL'
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (omegaNbr_conj hΩ.conjInvariant hL' c)

theorem pSpan_omegaNbr_le_centralizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) :
    pSpan (omegaNbr Ω K) ≤ Subgroup.centralizer (K : Set G) :=
  pSpan_le fun _ hJ y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
    comm_of_mem_omegaNbr hΩ h2 hK hJ x hx y hy

theorem pSpan_kPerp_le_normalizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) :
    pSpan (KPerp Ω K) ≤ Subgroup.normalizer ((pSpan (omegaNbr Ω K) : Subgroup G) : Set G) := by
  refine pSpan_le fun L hL => ?_
  rcases Set.mem_insert_iff.mp hL with rfl | hL'
  · exact (Subgroup.le_centralizer_iff.mp (pSpan_omegaNbr_le_centralizer hΩ h2 hK)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact (le_pSpan hL').trans Subgroup.le_normalizer

theorem pSpan_kPerp_le_centralizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    pSpan (KPerp Ω K) ≤ Subgroup.centralizer ({z} : Set G) := by
  refine pSpan_le fun L hL => ?_
  rcases Set.mem_insert_iff.mp hL with rfl | hL'
  · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (isUniqueInvolution_comm hz hx)
  · exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_omegaNbr hΩ h2 hK hL' z hz.mem y hy).symm

theorem centralizer_le_normalizer_pSpan_kPerp (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((pSpan (KPerp Ω K) : Subgroup G) : Set G) := by
  set M := pSpan (KPerp Ω K) with hM
  have hconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ x ∈ M, c * x * c⁻¹ ∈ M := by
    intro c hc x hx
    have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hle : M ≤ M.comap (MulAut.conj c).toMonoidHom := by
      refine pSpan_le fun L hL y hy => ?_
      show c * y * c⁻¹ ∈ M
      exact le_pSpan (conjSub_mem_kPerp hΩ hK hz hc' hL) (conj_mem_conjSub hy)
    exact hle hx
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj c hc x
  · intro hx
    have := hconj c⁻¹ (Subgroup.inv_mem _ hc) _ hx
    simpa [mul_assoc] using this

theorem oddCoreImg_pSpan_omegaNbr_eq_bot (hD : ThmDHyp r Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    oddCoreImg (pSpan (omegaNbr Ω K)) = ⊥ := by
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hD.inO2 K hK z hz
  have hC : oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
    TC.oddCoreImg_centralizer_eq_bot hD.odd hQn hQ2 hzQ
  have hLKM : pSpan (omegaNbr Ω K) ≤ pSpan (KPerp Ω K) :=
    pSpan_le fun J hJ => le_pSpan (Set.mem_insert_of_mem _ hJ)
  have h1 := oddCoreImg_le_of_le_normalizer hLKM (pSpan_kPerp_le_normalizer hD.hyp hD.two hK)
  have h2 := oddCoreImg_le_of_le_normalizer (pSpan_kPerp_le_centralizer hD.hyp hD.two hK hz)
    (centralizer_le_normalizer_pSpan_kPerp hD.hyp hK hz)
  rw [hC] at h2
  exact le_bot_iff.mp (h1.trans h2)

omit [Finite G] in
theorem nbrGen_eq_pSpan {K : Subgroup G} (hK : K ∈ Ω) :
    nbrGen (TC.nbrAdj Ω) K = pSpan (omegaNbr Ω K) := by
  unfold nbrGen pSpan
  congr 1
  ext J
  simp only [Set.mem_ofPred_eq, TC.nbrAdj, hK, true_and]

theorem sepHyp_of_d1Gen (hD : ThmDHyp r Ω) (hZ : Subgroup.center G = ⊥)
    (h1 : ThmD1GenBelow r (Nat.card G)) : TC.SepHyp Ω := by
  intro K J J' hKJ hKJ' hJ'
  obtain ⟨hK, hJ⟩ := hKJ
  obtain ⟨-, hJ''⟩ := hKJ'
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  set P := omegaNbr Ω K with hP
  have hPΩ : P ⊆ Ω := fun L hL => hL.1
  have hcomm : ∀ L ∈ P, ∀ x ∈ K, ∀ y ∈ L, x * y = y * x :=
    fun L hL => comm_of_mem_omegaNbr hD.hyp hD.two hK hL
  have hPC : pSpan P ≤ Subgroup.centralizer ({z} : Set G) :=
    pSpan_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm L hL z hz.mem y hy).symm
  have hCtop : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    apply hz.ne_one
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
      exact this
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hcard : Nat.card ↥(pSpan P) < Nat.card G := by
    calc Nat.card ↥(pSpan P) ≤ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) :=
          Subgroup.card_le_of_le hPC
      _ < Nat.card G := by
          have := Subgroup.card_le_card_group (Subgroup.centralizer ({z} : Set G))
          refine lt_of_le_of_ne this fun h => hCtop ?_
          exact (Subgroup.card_eq_iff_eq_top _).mp h
  have hPN : pSpan P ≤ Subgroup.normalizer (K : Set G) :=
    pSpan_le fun L hL => ((TC.mem_omegaNbr_iff hD.hyp hD.two).mp hL).2.2
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := by
    intro L hL x hx
    have h := omegaNbr_conj hD.hyp.conjInvariant hL x
    rwa [conjSub_eq_of_mem_normalizer (hPN hx)] at h
  have hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥ :=
    oddCore_eq_bot_of_oddCoreImg (oddCoreImg_pSpan_omegaNbr_eq_bot hD hK)
  have hE2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    intro L hL u hu
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hD.inO2 L (hPΩ hL) u hu
    refine ⟨Q ⊓ pSpan P, inf_le_right, fun x hx q hq => ⟨hQn.conj_mem q hq.1 x,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hq.2) (Subgroup.inv_mem _ hx)⟩,
      hQ2.to_le inf_le_left, huQ, le_pSpan hL hu.mem⟩
  have hnc : ¬ ∃ x ∈ pSpan P, conjSub x J = J' := by
    rintro ⟨x, hx, hxJ⟩
    apply hJ'
    exact ⟨x, by rw [nbrGen_eq_pSpan hK]; exact hx, hxJ⟩
  have hJJ' := h1 G Ω hD.hyp hD.two hD.card hD.aEmpty P hPΩ hcard hinv hodd hE2 J hJ J' hJ'' hnc
  refine ⟨hJ.1, (TC.mem_omegaNbr_iff hD.hyp hD.two).mpr ⟨hJ''.1, ?_, ?_⟩⟩
  · intro h
    exact hnc ⟨1, Subgroup.one_mem _, by rw [conjSub_one, h]⟩
  · exact le_normalizer_of_comm fun x hx y hy => (hJJ' y hy x hx).symm

theorem graphFam_of_d1Gen (hD : ThmDHyp r Ω) (hZ : Subgroup.center G = ⊥)
    (h1 : ThmD1GenBelow r (Nat.card G)) (hconn : Disconnected.DConnected Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : GraphFam Ω (TC.nbrAdj Ω) :=
  TC.graphFam hD.hyp hD.two (sepHyp_of_d1Gen hD hZ h1) (fun J hJ => hD.trans K hK J hJ) hD.gen
    hconn

end CFSG.ClassicalInvolution.Q3.TC.Thin
