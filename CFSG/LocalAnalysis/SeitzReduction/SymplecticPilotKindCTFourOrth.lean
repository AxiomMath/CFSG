module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTFourCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Torus

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {e : L ≃* StatedSp N K}

theorem CtLinParam.mem_torusCore [Finite K] (hK : 4 ≤ Nat.card K) {k : Fin N}
    (P : CtLinParam ε e k) {I : Finset (Fin (2 * N + ε))} (hI2 : 2 ≤ I.card)
    (hIk : I ⊆ (planeCoordsQ2 ε {k})ᶜ) {T : Subgroup (StatedSp N K)}
    (hT : ∀ x ∈ T, ∃ t : Fin N → Kˣ, diagSp K N t = x ∧ ∀ a ∈ I, ∀ b ∈ I,
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a =
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) b b)
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ blockSpecialLinear I) :
    P.Φ ⟨x, LinearPilot.blockSpecialLinear_mono hIk hx⟩ ∈
      centralizerPerfectCore (modelToG e T) := by
  set H : Subgroup (q2Block ε K {k}) := (blockSpecialLinear I).subgroupOf (q2Block ε K {k})
    with hH
  have hHmap : H.map (q2Block ε K {k}).subtype = blockSpecialLinear I := by
    rw [hH, subgroupOf_map_subtype, inf_eq_left.mpr
      (show blockSpecialLinear I ≤ q2Block ε K {k} from LinearPilot.blockSpecialLinear_mono hIk)]
  have hHperf : ⁅H, H⁆ = H := by
    apply Subgroup.map_injective (q2Block ε K {k}).subtype_injective
    rw [map_commutator, hHmap, LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hI2 hK]
  have hmem : (⟨x, LinearPilot.blockSpecialLinear_mono hIk hx⟩ : q2Block ε K {k}) ∈ H := hx
  have hcent : H.map P.Φ ≤ centralizer (modelToG e T : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨d, hd, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    obtain ⟨t, rfl, hconst⟩ := hT d hd
    rw [diagSp_eq_rootTorusHom_mul t k, map_mul, Subgroup.coe_mul]
    have h1 : P.Φ z ∈ centralizer (modelToG e (rootTorusSp K k) : Set G) := by
      have : P.Φ z ∈ neighbourCore e k := P.range_eq ▸ ⟨z, rfl⟩
      exact F4Pilot.centralizerPerfectCore_le_centralizer _ this
    have h2 := mem_centralizer_iff.1 h1 _
      (UnitaryPilot.symm_mem_modelToG e ⟨t k, rfl⟩)
    have hd' := diagSp_update_mem_spBlock_compl (K := K) t k
    have h3 : ((e.symm (diagSp K N (Function.update t k 1)) : L) : G) =
        P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), ctEmbed_mem_q2Block_iff.2 hd'⟩ :=
      (P.N1 _ hd').symm
    have hzc : (z : SpecialLinearGroup (Fin (2 * N + ε)) K) *
        ctEmbed ε (diagSp K N (Function.update t k 1)) =
        ctEmbed ε (diagSp K N (Function.update t k 1)) * z :=
      commute_of_mem_blockSpecialLinear_of_diag (I := I) hz
        (fun a b hab => ctEmbed_diagSp_apply_ne _ hab) hconst
    have h4 : P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)),
        ctEmbed_mem_q2Block_iff.2 hd'⟩ * P.Φ z = P.Φ z * P.Φ ⟨ctEmbed ε (diagSp K N
          (Function.update t k 1)), ctEmbed_mem_q2Block_iff.2 hd'⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzc.symm
    rw [h3]
    calc ((e.symm (rootTorusHom K N k (t k)) : L) : G) *
          P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), _⟩ * P.Φ z
        = ((e.symm (rootTorusHom K N k (t k)) : L) : G) * (P.Φ z *
          P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), _⟩) := by rw [mul_assoc, h4]
      _ = P.Φ z * (((e.symm (rootTorusHom K N k (t k)) : L) : G) *
          P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), _⟩) := by
          rw [← mul_assoc, h2, mul_assoc]
  have hle : H.map P.Φ ≤ centralizerPerfectCore (modelToG e T) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hcent (by rw [← map_commutator, hHperf])
  exact hle ⟨_, hmem, rfl⟩

end Torus

section Odd

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

variable (K) in
@[expose] noncomputable def oddLeviTorusSp (J : Finset (Fin n)) : Subgroup (StatedSp n K) :=
  (leviTorusSp K J).map (MulAut.conj (oddSwapSp K n)).toMonoidHom

theorem exists_of_mem_oddLeviTorusSp {J : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ oddLeviTorusSp K J) :
    ∃ t ∈ leviTorusParam K J, diagSp K n (oddCoordInv t) = x := by
  obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hx
  refine ⟨t, ht, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [oddSwapSp_mul_diagSp, mul_inv_cancel_right]

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] noncomputable def oddPieceCore (e : L ≃* StatedSp n K) (J : Finset (Fin n)) :
    Subgroup G :=
  centralizerPerfectCore (modelToG e (oddLeviTorusSp K J))

theorem oddPieceCore_eq_map [Finite G] (e : L ≃* StatedSp n K) (J : Finset (Fin n)) :
    oddPieceCore e J =
      (pieceCore e J).map (MulAut.conj ((e.symm (oddSwapSp K n) : L) : G)).toMonoidHom := by
  rw [oddPieceCore, oddLeviTorusSp, UnitaryPilot.modelToG_map_conj, pieceCore_def,
    F4Pilot.map_centralizerPerfectCore]

theorem commute_oddPieceCore_of_commute [Finite G] (e : L ≃* StatedSp n K)
    {J J' : Finset (Fin n)} (h : ∀ a ∈ pieceCore e J, ∀ b ∈ pieceCore e J', Commute a b) :
    ∀ a ∈ oddPieceCore e J, ∀ b ∈ oddPieceCore e J', Commute a b := by
  intro a ha b hb
  rw [oddPieceCore_eq_map] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have := (h a' ha' b' hb').eq
  change _ * _ = _ * _
  set l : G := ((e.symm (oddSwapSp K n) : L) : G)
  calc l * a' * l⁻¹ * (l * b' * l⁻¹) = l * (a' * b') * l⁻¹ := by group
    _ = l * (b' * a') * l⁻¹ := by rw [this]
    _ = l * b' * l⁻¹ * (l * a' * l⁻¹) := by group

end Odd

section Comm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {ε : ℕ} {e : L ≃* StatedSp 4 K}

omit [Finite G] in
theorem CtLinParam.mem_oddPieceCore_zero (hK : 4 ≤ Nat.card K) (P : CtLinParam ε e 2)
    {x : SpecialLinearGroup (Fin (2 * 4 + ε)) K}
    (hx : x ∈ blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))))
    (hx' : x ∈ q2Block ε K {2}) : P.Φ ⟨x, hx'⟩ ∈ oddPieceCore e ({0} : Finset (Fin 4)) := by
  have hI2 : 2 ≤ ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))).card := by
    rw [Finset.card_pair (ctE_ne_ctF _ _).symm]
  have hIk : ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) ⊆
      (planeCoordsQ2 ε ({2} : Finset (Fin 4)))ᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_compl]
    rcases ha with rfl | rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
  refine P.mem_torusCore hK hI2 hIk (T := oddLeviTorusSp K ({0} : Finset (Fin 4))) ?_ hx
  intro y hy
  obtain ⟨t, ht, rfl⟩ := exists_of_mem_oddLeviTorusSp hy
  refine ⟨oddCoordInv t, rfl, ?_⟩
  have ht01 : t 0 = t 1 := ((mem_leviTorusParam.1 ht) 0 (Finset.mem_singleton_self 0)).1
    (by decide)
  have hval : ∀ a ∈ ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))),
      ((ctEmbed ε (diagSp K 4 (Function.update (oddCoordInv t) 2 1)) :
        SpecialLinearGroup (Fin (2 * 4 + ε)) K) : Matrix (Fin (2 * 4 + ε)) (Fin (2 * 4 + ε)) K)
          a a = (((t 0)⁻¹ : Kˣ) : K) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [ctEmbed_diagSp_apply_self]
      simp [oddCoordInv]
    · rw [ctEmbed_diagSp_apply_self]
      simp [oddCoordInv, ht01]
  intro a ha b hb
  rw [hval a ha, hval b hb]

omit [Finite G] in
theorem CtLinParam.mem_oddPieceCore_two (hK : 4 ≤ Nat.card K) (P : CtLinParam ε e 0)
    {y : SpecialLinearGroup (Fin (2 * 4 + ε)) K}
    (hy : y ∈ blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))))
    (hy' : y ∈ q2Block ε K {0}) : P.Φ ⟨y, hy'⟩ ∈ oddPieceCore e ({2} : Finset (Fin 4)) := by
  have hI2 : 2 ≤ ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))).card := by
    rw [Finset.card_pair (ctE_ne_ctF _ _).symm]
  have hIk : ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))) ⊆
      (planeCoordsQ2 ε ({0} : Finset (Fin 4)))ᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_compl]
    rcases ha with rfl | rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
  refine P.mem_torusCore hK hI2 hIk (T := oddLeviTorusSp K ({2} : Finset (Fin 4))) ?_ hy
  intro z hz
  obtain ⟨t, ht, rfl⟩ := exists_of_mem_oddLeviTorusSp hz
  refine ⟨oddCoordInv t, rfl, ?_⟩
  have ht23 : t 2 = t 3 := ((mem_leviTorusParam.1 ht) 2 (Finset.mem_singleton_self 2)).1
    (by decide)
  have hval : ∀ a ∈ ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))),
      ((ctEmbed ε (diagSp K 4 (Function.update (oddCoordInv t) 0 1)) :
        SpecialLinearGroup (Fin (2 * 4 + ε)) K) : Matrix (Fin (2 * 4 + ε)) (Fin (2 * 4 + ε)) K)
          a a = (((t 2)⁻¹ : Kˣ) : K) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [ctEmbed_diagSp_apply_self]
      simp [oddCoordInv]
    · rw [ctEmbed_diagSp_apply_self]
      simp [oddCoordInv, ht23]
  intro a ha b hb
  rw [hval a ha, hval b hb]

theorem hcomm_of_orth (hK : 4 ≤ Nat.card K) (P : ∀ k : Fin 4, CtLinParam ε e k)
    (horth : ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)), Commute a b) :
    ∀ x ∈ blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))),
      ∀ y ∈ blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))),
      ∀ (hx : x ∈ q2Block ε K {2}) (hy : y ∈ q2Block ε K {0}),
        Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩) := by
  intro x hxI y hyI hx hy
  exact commute_oddPieceCore_of_commute e horth _ ((P 2).mem_oddPieceCore_zero hK hxI hx) _
    ((P 0).mem_oddPieceCore_two hK hyI hy)

end Comm

@[expose] def SpLinearFourOrthInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, RootKindSp e t f k κ) →
        ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)),
          Commute a b

@[expose] def SpLinearEvenFourAlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, RootKindSp e t f k .linearEven) →
        ∃ P : ∀ k : Fin 4, CtLinParam 0 e k, CtLinParamAgree P

theorem spLinearOddCoverFourInput_of_orth
    (h : SpLinearFourOrthInput .linearOdd) : SpLinearOddCoverFourInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP : ∀ k : Fin 4, Nonempty (CtLinParam 1 e k) := fun k =>
    nonempty_ctLinParam_linearOdd (m := 3) hset hKc hf le_rfl e htC ht k (hroot k)
  obtain ⟨Q, hQ⟩ := exists_ctLinParamAgree_odd hq le_rfl fun k => (hP k).some
  exact spGlobalCoverType_four_of_ctLinParamAgree hKc hf (Or.inr ⟨rfl, rfl⟩) Q hQ
    (hcomm_of_orth hq Q (h G L hset f K hKc hf e t ht hKt hroot))

theorem spLinearEvenCoverFourInput_of_align_orth (ha : SpLinearEvenFourAlignInput)
    (h : SpLinearFourOrthInput .linearEven) : SpLinearEvenCoverFourInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨Q, hQ⟩ := ha G L hset f K hKc hf e t ht hKt hroot
  exact spGlobalCoverType_four_of_ctLinParamAgree hKc hf (Or.inl ⟨rfl, rfl⟩) Q hQ
    (hcomm_of_orth hq Q (h G L hset f K hKc hf e t ht hKt hroot))

theorem spKindCoverInput_linearOdd_of_orth
    (h : SpLinearFourOrthInput .linearOdd) : SpKindCoverInput .linearOdd :=
  spKindCoverInput_linearOdd_of_four (spLinearOddCoverFourInput_of_orth h)

theorem spKindCoverInput_linearEven_of_align_orth
    (ha : SpLinearEvenFourAlignInput) (h : SpLinearFourOrthInput .linearEven) :
    SpKindCoverInput .linearEven :=
  spKindCoverInput_linearEven_of_four (spLinearEvenCoverFourInput_of_align_orth ha h)

end CFSG.SeitzReduction.SymplecticPilot
