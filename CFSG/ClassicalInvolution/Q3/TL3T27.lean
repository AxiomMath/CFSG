module

public import CFSG.ClassicalInvolution.Q3.TL3T26

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

theorem mem_normalizer_pSpan {P : Set (Subgroup G)} {g : G}
    (hg : ∀ L ∈ P, conjSub g L ∈ P) (hg' : ∀ L ∈ P, conjSub g⁻¹ L ∈ P) :
    g ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G) := by
  have key : ∀ c : G, (∀ L ∈ P, conjSub c L ∈ P) → ∀ x ∈ pSpan P, c * x * c⁻¹ ∈ pSpan P := by
    intro c hc x hx
    have hle : pSpan P ≤ (pSpan P).comap (MulAut.conj c).toMonoidHom :=
      pSpan_le fun L hL y hy => le_pSpan (hc L hL) (conj_mem_conjSub hy)
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ hg' _ hx
    simpa [mul_assoc] using this

variable [Finite G] {r : ℕ} {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

theorem card_pSpan_omegaNbr_lt (hD : ThmDHyp r Ω) (hZ : Subgroup.center G = ⊥) {K : Subgroup G}
    (hK : K ∈ Ω) : Nat.card ↥(pSpan (omegaNbr Ω K)) < Nat.card G := by
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  have hPC : pSpan (omegaNbr Ω K) ≤ Subgroup.centralizer ({z} : Set G) :=
    pSpan_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_omegaNbr hD.hyp hD.two hK hL z hz.mem y hy).symm
  have hCtop : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    apply hz.ne_one
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  calc Nat.card ↥(pSpan (omegaNbr Ω K)) ≤ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) :=
        Subgroup.card_le_of_le hPC
    _ < Nat.card G := by
        have := Subgroup.card_le_card_group (Subgroup.centralizer ({z} : Set G))
        refine lt_of_le_of_ne this fun h => hCtop ?_
        exact (Subgroup.card_eq_iff_eq_top _).mp h

structure CSetting (r : ℕ) (IH : ℕ → Prop) (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop where
  cex : DCex r IH Ω
  center : Subgroup.center G = ⊥
  conn : Disconnected.DConnected Ω
  d1 : ThmD1GenBelow r (Nat.card G)
  adj : TC.nbrAdj Ω K J
  max : orbOf (TC.nbrAdj Ω) K J ∈ maxOrbs (TC.nbrAdj Ω) K

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting r IH Ω K J)
include hS

theorem graphFam : GraphFam Ω (TC.nbrAdj Ω) :=
  graphFam_of_d1Gen hS.cex.toThmDHyp hS.center hS.d1 hS.conn hS.adj.1

theorem orb_subset : orbOf (TC.nbrAdj Ω) K J ⊆ omegaNbr Ω K := fun _ hM =>
  (adj_of_mem_orbOf hS.graphFam.graph hS.adj hM).2

theorem pSpan_orb_le : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ pSpan (omegaNbr Ω K) :=
  pSpan_le fun _ hM => le_pSpan (hS.orb_subset hM)

omit hS [Finite G] in
theorem conjSub_mem_orb (hK : K ∈ Ω) {l : G} (hl : l ∈ pSpan (omegaNbr Ω K)) {M : Subgroup G}
    (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) : conjSub l M ∈ orbOf (TC.nbrAdj Ω) K J := by
  obtain ⟨a, ha, rfl⟩ := hM
  rw [← nbrGen_eq_pSpan hK] at hl
  exact ⟨l * a, Subgroup.mul_mem _ hl ha, by rw [conjSub_mul]⟩

theorem thmD :
    (∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∀ L' ∈ orbOf (TC.nbrAdj Ω) K J, L = L') ∨
      (∃ W : Subgroup G, WIn (orbOf (TC.nbrAdj Ω) K J) (pSpan (orbOf (TC.nbrAdj Ω) K J)) =
        {W}) ∨
      (∃ E : Subgroup G, E8Struct (pSpan (orbOf (TC.nbrAdj Ω) K J)) E) ∨
      Nonempty (AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 7 AE.e64Sets AE.e64Sub) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent (orbOf (TC.nbrAdj Ω) K J) n)) ∨
      Nonempty (AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 8 AE.e29Sets AE.e29Sub) := by
  have hD := hS.cex.toThmDHyp
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  have hPΩ : π ⊆ Ω := fun M hM => (hS.orb_subset hM).1
  have hcard : Nat.card ↥(pSpan π) < Nat.card G :=
    lt_of_le_of_lt (Subgroup.card_le_of_le hS.pSpan_orb_le)
      (card_pSpan_omegaNbr_lt hD hS.center hS.adj.1)
  have htrans : ∀ L ∈ π, ∀ L' ∈ π, ∃ x ∈ pSpan π, conjSub x L = L' := by
    intro L hL L' hL'
    obtain ⟨a, ha, rfl⟩ := orbOf_subset_gen hS.graphFam.graph hS.adj hL
    obtain ⟨b, hb, rfl⟩ := orbOf_subset_gen hS.graphFam.graph hS.adj hL'
    refine ⟨b * a⁻¹, Subgroup.mul_mem _ hb (Subgroup.inv_mem _ ha), ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]
  have hinv : ∀ L ∈ π, ∀ x ∈ pSpan π, conjSub x L ∈ π :=
    fun L hL x hx => conjSub_mem_orb hS.adj.1 (hS.pSpan_orb_le hx) hL
  have hN : pSpan (omegaNbr Ω K) ≤ Subgroup.normalizer ((pSpan π : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_pSpan (fun L hL => conjSub_mem_orb hS.adj.1 hl hL)
      (fun L hL => conjSub_mem_orb hS.adj.1 (Subgroup.inv_mem _ hl) hL)
  have hodd : classicalInvolutionOddCore ↥(pSpan π) = ⊥ := by
    apply oddCore_eq_bot_of_oddCoreImg
    have h1 := oddCoreImg_le_of_le_normalizer hS.pSpan_orb_le hN
    rw [oddCoreImg_pSpan_omegaNbr_eq_bot hD hS.adj.1] at h1
    exact le_bot_iff.mp h1
  have hE2 : ∀ L ∈ π, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan π ∧
      (∀ x ∈ pSpan π, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    intro L hL u hu
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hD.inO2 L (hPΩ hL) u hu
    refine ⟨Q ⊓ pSpan π, inf_le_right, fun x hx q hq => ⟨hQn.conj_mem q hq.1 x,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hq.2) (Subgroup.inv_mem _ hx)⟩,
      hQ2.to_le inf_le_left, huQ, le_pSpan hL hu.mem⟩
  exact thmDGenBelow_of_absBelow hS.cex.below G Ω hD.hyp hD.two hD.card hD.aEmpty π hPΩ hcard
    htrans hinv hodd hE2

theorem not_singleton
    (h : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∀ L' ∈ orbOf (TC.nbrAdj Ω) K J, L = L') : False := by
  have hD := hS.cex.toThmDHyp
  have hF := hS.graphFam
  have hK : K ∈ Ω := hS.adj.1
  have hJ : J ∈ Ω := hS.adj.2.1
  have hJK := orbOf_mem_maxOrbs hF hS.adj hS.max
  have h1 : orbOf (TC.nbrAdj Ω) K J = {J} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨mem_orbOf_self K J,
      fun L hL => h L hL J (mem_orbOf_self K J)⟩
  have h2 : (orbOf (TC.nbrAdj Ω) J K).ncard = 1 := by
    rw [← ncard_eq_of_isMaxOrb hF hK hJ hS.max hJK, h1, Set.ncard_singleton]
  have h3 : orbOf (TC.nbrAdj Ω) J K = {K} := by
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h2
    have hKa : K ∈ ({a} : Set (Subgroup G)) := ha ▸ mem_orbOf_self J K
    rw [Set.mem_singleton_iff] at hKa
    rw [ha, hKa]
  have hgen := le_iSup_of_maxOrb hF hS.adj hS.max
  rw [h1, h3] at hgen
  have hJKle : J ⊔ K = ⊤ := by
    rw [eq_top_iff, ← hD.gen]
    refine pSpan_le fun L hL => (hgen L hL).trans (iSup₂_le fun M hM => ?_)
    rcases hM with hM | hM
    · rw [Set.mem_singleton_iff] at hM
      rw [hM]
      exact le_sup_left
    · rw [Set.mem_singleton_iff] at hM
      rw [hM]
      exact le_sup_right
  have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
    ((TC.mem_omegaNbr_iff hD.hyp hD.two).mp hS.adj.2).2.2
  have h2grp : IsPGroup 2 ↥(J ⊔ K) := (hD.two J hJ).to_sup_of_normal_right' (hD.two K hK) hJN
  rw [hJKle] at h2grp
  have hG2 : IsPGroup 2 G := h2grp.of_equiv Subgroup.topEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  have : Nontrivial G := ⟨⟨z, 1, hz.ne_one⟩⟩
  have hnt := hG2.center_nontrivial
  rw [Subgroup.nontrivial_iff_ne_bot] at hnt
  exact hnt hS.center

end CSetting

@[expose] def CLeafW (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CSetting r IH Ω K J → ∀ W : Subgroup G,
      WIn (orbOf (TC.nbrAdj Ω) K J) (pSpan (orbOf (TC.nbrAdj Ω) K J)) = {W} → False

@[expose] def CLeafE8 (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CSetting r IH Ω K J → ∀ E : Subgroup G, E8Struct (pSpan (orbOf (TC.nbrAdj Ω) K J)) E → False

@[expose] def CLeafE64 (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CSetting r IH Ω K J → Nonempty (AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 7 AE.e64Sets AE.e64Sub) →
      False

@[expose] def CLeafE29 (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CSetting r IH Ω K J → Nonempty (AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 8 AE.e29Sets AE.e29Sub) →
      False

@[expose] def CLeafAE (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G),
    CSetting r IH Ω K J → ∀ n : ℕ, 5 ≤ n → Nonempty (AEIdent (orbOf (TC.nbrAdj Ω) K J) n) → False

theorem dLeafC_of (h1 : D1GenLeaf r) (hW : CLeafW r IH) (hE8 : CLeafE8 r IH)
    (hE64 : CLeafE64 r IH) (hE29 : CLeafE29 r IH) (hAE : CLeafAE r IH) : DLeafC r IH := by
  intro G _ _ Ω hc hZ hconn
  have hD := hc.toThmDHyp
  have hd1 : ThmD1GenBelow r (Nat.card G) := h1 _ (thmDGenBelow_of_absBelow hc.below)
  obtain ⟨K, hK, L, hL, hKL⟩ : ∃ K ∈ Ω, ∃ L ∈ Ω, K ≠ L := by
    by_contra hcon
    push Not at hcon
    exact hc.not (Or.inl hcon)
  have hF := graphFam_of_d1Gen hD hZ hd1 hconn hK
  obtain ⟨J₀, hKJ₀⟩ : ∃ J₀, TC.nbrAdj Ω K J₀ := by
    rcases Relation.ReflTransGen.cases_head (hF.conn K hK L hL) with h | ⟨c, hKc, -⟩
    · exact absurd h hKL
    · exact ⟨c, hKc⟩
  obtain ⟨P, hP⟩ := exists_isMaxOrb hKJ₀
  obtain ⟨⟨J, hKJ, rfl⟩, -⟩ := id hP
  have hS : CSetting r IH Ω K J := ⟨hc, hZ, hconn, hd1, hKJ, hP⟩
  rcases hS.thmD with h0 | ⟨W, hW'⟩ | ⟨E, hE⟩ | hI | ⟨n, hn, hI⟩ | hI
  · exact hS.not_singleton h0
  · exact hW G Ω K J hS W hW'
  · exact hE8 G Ω K J hS E hE
  · exact hE64 G Ω K J hS hI
  · exact hAE G Ω K J hS n hn hI
  · exact hE29 G Ω K J hS hI

theorem thmDAbs_of_leaves₄ (h1 : D1GenLeaf r) (hW : CLeafW r IH) (hE8 : CLeafE8 r IH)
    (hE64 : CLeafE64 r IH) (hE29 : CLeafE29 r IH) (hAE : CLeafAE r IH) (hE4 : DLeafE4 r IH)
    (hstar : DLeafStar r IH) (hend : DLeafEnd r IH) (hih : ∀ n, IH n) : ThmDAbs r :=
  thmDAbs_of_leaves₃ (dLeafC_of h1 hW hE8 hE64 hE29 hAE) hE4 hstar hend hih

section Cit3


theorem thmD2Step_of_leaves₃ {r : ℕ} (h1 : D1GenLeaf r) (hW : CLeafW r (PackIH r))
    (hE8 : CLeafE8 r (PackIH r)) (hE64 : CLeafE64 r (PackIH r)) (hE29 : CLeafE29 r (PackIH r))
    (hAE : CLeafAE r (PackIH r)) (hE4 : DLeafE4 r (PackIH r)) (hstar : DLeafStar r (PackIH r))
    (hend : DLeafEnd r (PackIH r)) (n : ℕ) :
    CIT3Below n → TL4.TightBelowRPlus r n → ThmDAbsBelow r (n + 1) :=
  thmD2Step_of_leaves₂ (dLeafC_of h1 hW hE8 hE64 hE29 hAE) hE4 hstar hend n

end Cit3

end CFSG.ClassicalInvolution.Q3.TC.Thin
