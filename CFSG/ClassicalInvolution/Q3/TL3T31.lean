module

public import CFSG.ClassicalInvolution.Q3.TL3T27

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

structure CHypG (r : ℕ) (IH : ℕ → Prop) (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ L ∈ Ω, IsPGroup 2 L
  card : ∀ L ∈ Ω, Nat.card L = 2 ^ r
  aEmpty : ∀ L ∈ Ω, AEmpty Ω L
  gen : pSpan Ω = ⊤
  trans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L'
  odd : classicalInvolutionOddCore G = ⊥
  center : Subgroup.center G = ⊥
  conn : Disconnected.DConnected Ω
  oddCent : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
    oddCoreImg (Subgroup.centralizer ({u} : Set G)) = ⊥
  perp : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → ∀ M ∈ KPerp Ω L, ∀ v : G,
    IsUniqueInvolution M v → TC.TwoIn u v
  d1 : ThmD1GenBelow r (Nat.card G)
  d2 : ThmDGenBelow r (Nat.card G)
  ih : IH (Nat.card G)

structure CHyp (r : ℕ) (IH : ℕ → Prop) (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop
    extends CHypG r IH Ω where
  adj : TC.nbrAdj Ω K J
  max : orbOf (TC.nbrAdj Ω) K J ∈ maxOrbs (TC.nbrAdj Ω) K

variable {r : ℕ} {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHypG

variable (hS : CHypG r IH Ω)
include hS

theorem oddCoreImg_pSpan_omegaNbr_eq_bot {K : Subgroup G} (hK : K ∈ Ω) :
    oddCoreImg (pSpan (omegaNbr Ω K)) = ⊥ := by
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  have hLKM : pSpan (omegaNbr Ω K) ≤ pSpan (KPerp Ω K) :=
    pSpan_le fun J hJ => le_pSpan (Set.mem_insert_of_mem _ hJ)
  have h1 := oddCoreImg_le_of_le_normalizer hLKM (pSpan_kPerp_le_normalizer hS.hyp hS.two hK)
  have h2 := oddCoreImg_le_of_le_normalizer (pSpan_kPerp_le_centralizer hS.hyp hS.two hK hz)
    (centralizer_le_normalizer_pSpan_kPerp hS.hyp hK hz)
  rw [hS.oddCent K hK z hz] at h2
  exact le_bot_iff.mp (h1.trans h2)

theorem card_pSpan_omegaNbr_lt {K : Subgroup G} (hK : K ∈ Ω) :
    Nat.card ↥(pSpan (omegaNbr Ω K)) < Nat.card G := by
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  have hPC : pSpan (omegaNbr Ω K) ≤ Subgroup.centralizer ({z} : Set G) :=
    pSpan_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_omegaNbr hS.hyp hS.two hK hL z hz.mem y hy).symm
  have hCtop : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    apply hz.ne_one
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rw [hS.center, Subgroup.mem_bot] at hzc
    exact hzc
  calc Nat.card ↥(pSpan (omegaNbr Ω K)) ≤ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) :=
        Subgroup.card_le_of_le hPC
    _ < Nat.card G := by
        have := Subgroup.card_le_card_group (Subgroup.centralizer ({z} : Set G))
        refine lt_of_le_of_ne this fun h => hCtop ?_
        exact (Subgroup.card_eq_iff_eq_top _).mp h

omit [Finite G] in
theorem exists_normal_two_of_perp {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {X : Subgroup G}
    (hXC : X ≤ Subgroup.centralizer ({z} : Set G)) {L : Subgroup G} (hL : L ∈ KPerp Ω K)
    (hLX : L ≤ X) {u : G} (hu : IsUniqueInvolution L u) : ∃ Q : Subgroup G, Q ≤ X ∧
      (∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q := by
  obtain ⟨Q, ⟨-, hQ2, hQn⟩, huQ⟩ := hS.perp K hK z hz L hL u hu
  exact ⟨Q ⊓ X, inf_le_right, fun x hx q hq => ⟨hQn x (hXC hx) q hq.1,
    X.mul_mem (X.mul_mem hx hq.2) (X.inv_mem hx)⟩, hQ2.to_le inf_le_left, huQ, hLX hu.mem⟩

theorem sepHyp : TC.SepHyp Ω := by
  intro K J J' hKJ hKJ' hJ'
  obtain ⟨hK, hJ⟩ := hKJ
  obtain ⟨-, hJ''⟩ := hKJ'
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  set P := omegaNbr Ω K with hP
  have hPΩ : P ⊆ Ω := fun L hL => hL.1
  have hPC : pSpan P ≤ Subgroup.centralizer ({z} : Set G) :=
    pSpan_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_omegaNbr hS.hyp hS.two hK hL z hz.mem y hy).symm
  have hPN : pSpan P ≤ Subgroup.normalizer (K : Set G) :=
    pSpan_le fun L hL => ((TC.mem_omegaNbr_iff hS.hyp hS.two).mp hL).2.2
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := by
    intro L hL x hx
    have h := omegaNbr_conj hS.hyp.conjInvariant hL x
    rwa [conjSub_eq_of_mem_normalizer (hPN hx)] at h
  have hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥ :=
    oddCore_eq_bot_of_oddCoreImg (hS.oddCoreImg_pSpan_omegaNbr_eq_bot hK)
  have hE2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q := fun L hL u hu =>
    hS.exists_normal_two_of_perp hK hz hPC (Set.mem_insert_of_mem _ hL) (le_pSpan hL) hu
  have hnc : ¬ ∃ x ∈ pSpan P, conjSub x J = J' := by
    rintro ⟨x, hx, hxJ⟩
    apply hJ'
    exact ⟨x, by rw [nbrGen_eq_pSpan hK]; exact hx, hxJ⟩
  have hJJ' := hS.d1 G Ω hS.hyp hS.two hS.card hS.aEmpty P hPΩ (hS.card_pSpan_omegaNbr_lt hK)
    hinv hodd hE2 J hJ J' hJ'' hnc
  refine ⟨hJ.1, (TC.mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hJ''.1, ?_, ?_⟩⟩
  · intro h
    exact hnc ⟨1, Subgroup.one_mem _, by rw [conjSub_one, h]⟩
  · exact le_normalizer_of_comm fun x hx y hy => (hJJ' y hy x hx).symm

theorem graphFam {K : Subgroup G} (hK : K ∈ Ω) : GraphFam Ω (TC.nbrAdj Ω) :=
  TC.graphFam hS.hyp hS.two hS.sepHyp (fun J hJ => hS.trans K hK J hJ) hS.gen hS.conn

end CHypG

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp r IH Ω K J)
include hS

theorem graphFam' : GraphFam Ω (TC.nbrAdj Ω) :=
  hS.toCHypG.graphFam hS.adj.1

theorem orb_subset : orbOf (TC.nbrAdj Ω) K J ⊆ omegaNbr Ω K := fun _ hM =>
  (adj_of_mem_orbOf hS.graphFam'.graph hS.adj hM).2

theorem pSpan_orb_le : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ pSpan (omegaNbr Ω K) :=
  pSpan_le fun _ hM => le_pSpan (hS.orb_subset hM)

end CHyp

@[expose] def CLeafE8G (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CHyp r IH Ω K J → ∀ E : Subgroup G, E8Struct (pSpan (orbOf (TC.nbrAdj Ω) K J)) E → False

@[expose] def CLeafE64G (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CHyp r IH Ω K J → Nonempty (AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 7 AE.e64Sets AE.e64Sub) →
      False

@[expose] def CLeafE29G (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CHyp r IH Ω K J → Nonempty (AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 8 AE.e29Sets AE.e29Sub) →
      False

theorem CSetting.toCHyp {K J : Subgroup G} (hS : CSetting r IH Ω K J) : CHyp r IH Ω K J where
  toCHypG :=
    { hyp := hS.cex.hyp
      two := hS.cex.two
      card := hS.cex.card
      aEmpty := hS.cex.aEmpty
      gen := hS.cex.gen
      trans := hS.cex.trans
      odd := hS.cex.odd
      center := hS.center
      conn := hS.conn
      oddCent := fun L hL u hu => by
        obtain ⟨Q, hQn, hQ2, huQ⟩ := hS.cex.inO2 L hL u hu
        exact TC.oddCoreImg_centralizer_eq_bot hS.cex.odd hQn hQ2 huQ
      perp := fun L hL u hu M hM v hv => by
        obtain ⟨Q, hQn, hQ2, hvQ⟩ := hS.cex.inO2 M (Set.mem_insert_iff.mp hM |>.elim
          (fun h => h ▸ hL) (fun h => h.1)) v hv
        have hvu : v ∈ Subgroup.centralizer ({u} : Set G) := by
          rcases Set.mem_insert_iff.mp hM with rfl | hM'
          · rw [hv.eq hu]
            exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (comm_of_mem_omegaNbr hS.cex.hyp hS.cex.two hL hM' u hu.mem v hv.mem).symm
        exact ⟨Q ⊓ Subgroup.centralizer ({u} : Set G), ⟨inf_le_right, hQ2.to_le inf_le_left,
          fun c hc p hp => ⟨hQn.conj_mem p hp.1 c, Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hp.2)
            (Subgroup.inv_mem _ hc)⟩⟩, hvQ, hvu⟩
      d1 := hS.d1
      d2 := thmDGenBelow_of_absBelow hS.cex.below
      ih := hS.cex.ih }
  adj := hS.adj
  max := hS.max

theorem cLeafE8_of_G (h : CLeafE8G r IH) : CLeafE8 r IH :=
  fun G _ _ Ω K J hS E hE => h G Ω K J hS.toCHyp E hE

theorem cLeafE64_of_G (h : CLeafE64G r IH) : CLeafE64 r IH :=
  fun G _ _ Ω K J hS hI => h G Ω K J hS.toCHyp hI

theorem cLeafE29_of_G (h : CLeafE29G r IH) : CLeafE29 r IH :=
  fun G _ _ Ω K J hS hI => h G Ω K J hS.toCHyp hI

end CFSG.ClassicalInvolution.Q3.TC.Thin
