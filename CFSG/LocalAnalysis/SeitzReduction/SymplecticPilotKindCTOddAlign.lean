module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddRigid
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTAgree

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Tor

variable {K : Type} [Field K] {N : ℕ}

theorem ctTorGL_inv (a : Kˣ) : ctTorGL (N := N) a⁻¹ = (ctTorGL (K := K) a)⁻¹ :=
  Units.ext rfl

theorem ctTorAut_inv (a : Kˣ) : ctTorAut (N := N) a⁻¹ = (ctTorAut (K := K) a)⁻¹ := by
  rw [ctTorAut, ctTorGL_inv, map_inv]
  rfl

theorem ctTorAut_inv_apply (a : Kˣ) (x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
    ctTorAut a⁻¹ (ctTorAut a x) = x := by
  rw [ctTorAut_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem ctTorAut_apply_inv (a : Kˣ) (x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
    ctTorAut a (ctTorAut a⁻¹ x) = x := by
  rw [ctTorAut_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem ctTorEntry_q2Par (b : K) (i : Fin (2 * N + 1)) :
    ctTorEntry b (q2Par N 1 i) = ctTorEntry b i := by
  obtain ⟨w, rfl⟩ := (q2Coord N 1).surjective i
  rw [q2Par_q2Coord]
  rcases w with u | e
  · rw [Sum.map_inl, ctTorEntry_of_ne (q2Coord_inl_ne_ctV _),
      ctTorEntry_of_ne (q2Coord_inl_ne_ctV _)]
  · obtain rfl : e = 0 := Subsingleton.elim _ _
    rfl

theorem ctGraph_ctTorAut [CharP K 2] (a : Kˣ) (y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
    ctGraph 1 (ctTorAut a y) = ctTorAut a⁻¹ (ctGraph 1 y) := by
  apply Subtype.ext
  ext i j
  rw [ctTorAut_apply_apply, coe_ctGraph, coe_ctGraph, q2GramMat_mul_mul_apply,
    q2GramMat_mul_mul_apply, transpose_apply, transpose_apply, ← map_inv, ctTorAut_apply_apply,
    ctTorEntry_q2Par, ctTorEntry_q2Par, inv_inv]
  ring

theorem ctTorAut_ctGraph_ctTorAut_ctGraph [CharP K 2] (a : Kˣ)
    (x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
    ctTorAut a (ctGraph 1 (ctTorAut a (ctGraph 1 x))) = x := by
  rw [ctGraph_ctTorAut, ctGraph_ctGraph, ctTorAut_apply_inv]

@[expose] noncomputable def ctTorBlock (a : Kˣ) (R : Finset (Fin N)) : MulAut (q2Block 1 K R) where
  toFun x := ⟨ctTorAut a (x : SpecialLinearGroup (Fin (2 * N + 1)) K), ctTorAut_mem_q2Block a x.2⟩
  invFun x := ⟨ctTorAut a⁻¹ (x : SpecialLinearGroup (Fin (2 * N + 1)) K),
    ctTorAut_mem_q2Block a⁻¹ x.2⟩
  left_inv _ := Subtype.ext (ctTorAut_inv_apply a _)
  right_inv _ := Subtype.ext (ctTorAut_apply_inv a _)
  map_mul' x y := Subtype.ext (map_mul (ctTorAut (N := N) (K := K) a)
    (x : SpecialLinearGroup (Fin (2 * N + 1)) K) y)

theorem coe_ctTorBlock (a : Kˣ) {R : Finset (Fin N)} (x : q2Block 1 K R) :
    ((ctTorBlock a R x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) =
      ctTorAut a (x : SpecialLinearGroup (Fin (2 * N + 1)) K) := rfl

theorem ctTorBlock_fix [CharP K 2] (a : Kˣ) {R : Finset (Fin N)} {x : q2Block 1 K R}
    (hx : x ∈ ctSpBlock 1 K R) : ctTorBlock a R x = x := by
  obtain ⟨y, -, hy⟩ := mem_ctSpBlock.1 hx
  apply Subtype.ext
  rw [coe_ctTorBlock, ← hy, ctTorAut_ctEmbed]

theorem ctTorAut_transvection_eq_iff (a : Kˣ) (p : Fin N) :
    ctTorAut a (SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K)) =
        SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K) ↔ a = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * N + 1)) K =>
      (z : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) (q2Coord N 1 (Sum.inl (Sum.inl p)))
        (ctV N)) h
    have h2 : ((SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K) :
        SpecialLinearGroup (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)
        (q2Coord N 1 (Sum.inl (Sum.inl p))) (ctV N) = 1 := by
      rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply,
        single_apply_same, Matrix.one_apply_ne (q2Coord_inl_ne_ctV _), zero_add]
    simp only [ctTorAut_apply_apply] at h1
    rw [ctTorEntry_of_ne (q2Coord_inl_ne_ctV _), ctTorEntry_ctV, one_mul, h2, one_mul] at h1
    have h3 : (a⁻¹ : Kˣ) = 1 := Units.ext h1
    rw [inv_eq_one] at h3
    exact h3
  · rintro rfl
    rw [ctTorAut_one, MulAut.one_apply]

theorem ctTorAut_ctGraph_transvection_ne [CharP K 2] (a : Kˣ) (p : Fin N) :
    ctTorAut a (ctGraph 1
      (SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K))) ≠
        SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K) := by
  intro h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * N + 1)) K =>
    (z : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) (q2Coord N 1 (Sum.inl (Sum.inl p)))
      (ctV N)) h
  have hinv : (SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K))⁻¹ =
      SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) 1 :=
    inv_eq_of_mul_eq_one_right (ct_transvection_one_mul_self _)
  have hne1 : ctV N ≠ q2Coord N 1 (Sum.inl (Sum.inl p)) := (q2Coord_inl_ne_ctV _).symm
  have hne2 : ctV N ≠ q2Coord N 1 (Sum.inl (Sum.inr p)) := (q2Coord_inl_ne_ctV _).symm
  have hpv : q2Par N 1 (ctV N) = ctV N := by
    rw [q2Par_q2Coord]
    rfl
  have hpe : q2Par N 1 (q2Coord N 1 (Sum.inl (Sum.inl p))) =
      q2Coord N 1 (Sum.inl (Sum.inr p)) := by
    rw [q2Par_q2Coord]
    rfl
  have h3 : ((SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K) :
      SpecialLinearGroup (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)
      (ctV N) (q2Coord N 1 (Sum.inl (Sum.inr p))) = 0 := by
    rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      single_apply_of_row_ne hne1.symm, Matrix.one_apply_ne hne2, add_zero]
  have h4 : ((SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p)) (1 : K) :
      SpecialLinearGroup (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)
      (q2Coord N 1 (Sum.inl (Sum.inl p))) (ctV N) = 1 := by
    rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      single_apply_same, Matrix.one_apply_ne (q2Coord_inl_ne_ctV _), zero_add]
  rw [ctTorAut_apply_apply, coe_ctGraph, hinv, q2GramMat_mul_mul_apply, transpose_apply, hpv,
    hpe, h3, h4, mul_zero, zero_mul] at h1
  exact zero_ne_one h1

end Tor

section Edge

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N : ℕ}
  {e : L ≃* StatedSp N K}

@[expose] noncomputable def CtLinParam.twistTor {k : Fin N} (P : CtLinParam 1 e k) (a : Kˣ) :
    CtLinParam 1 e k where
  Φ := P.Φ.comp (ctTorBlock a {k}).toMonoidHom
  ker_le := by
    intro x hx
    have hx' : ctTorBlock a {k} x ∈ P.Φ.ker := hx
    have h1 := P.ker_le hx'
    rw [mem_center_iff] at h1 ⊢
    intro g
    apply (ctTorBlock (K := K) a {k}).injective
    rw [map_mul, map_mul]
    exact h1 _
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 y hy := by
    change P.Φ (ctTorBlock a {k} ⟨ctEmbed 1 y, _⟩) = _
    rw [ctTorBlock_fix a (mem_ctSpBlock.2 ⟨y, hy, rfl⟩)]
    exact P.N1 y hy

theorem CtLinParam.twistTor_Φ_apply {k : Fin N} (P : CtLinParam 1 e k) (a : Kˣ)
    (x : q2Block 1 K {k}) : (P.twistTor a).Φ x = P.Φ (ctTorBlock a {k} x) :=
  rfl

theorem CtLinParam.exists_ctTor_of_overlap [Finite G] [Finite K] (hK : 4 ≤ Nat.card K)
    (hN : 4 ≤ N) {k l : Fin N} (hkl : k ≠ l) (P : CtLinParam 1 e k) (Q : CtLinParam 1 e l) :
    ∃ a : Kˣ, (∀ (x : SpecialLinearGroup (Fin (2 * N + 1)) K) (hx : x ∈ q2Block 1 K {k, l}),
        P.Φ ⟨x, q2Block_pair_le_left' k l hx⟩ =
          Q.Φ ⟨ctTorAut a x, q2Block_pair_le_right' k l (ctTorAut_mem_q2Block a hx)⟩) ∨
      ∀ (x : SpecialLinearGroup (Fin (2 * N + 1)) K) (hx : x ∈ q2Block 1 K {k, l}),
        P.Φ ⟨x, q2Block_pair_le_left' k l hx⟩ =
          Q.Φ ⟨ctTorAut a (ctGraph 1 x), q2Block_pair_le_right' k l
            (ctTorAut_mem_q2Block a (ctGraph_mem_q2Block hx))⟩ := by
  have hcard : ((planeCoordsQ2 1 ({k, l} : Finset (Fin N)))ᶜ).card = 2 * N + 1 - 4 := by
    rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_pair hkl, Fintype.card_fin]
  obtain ⟨p, hp⟩ : ({k, l}ᶜ : Finset (Fin N)).Nonempty := compl_pair_nonempty (by omega) k l
  have hpkl : p ∉ ({k, l} : Finset (Fin N)) := Finset.mem_compl.1 hp
  set φP : q2Block 1 K {k, l} →* G := P.Φ.comp (Subgroup.inclusion (q2Block_pair_le_left' k l))
  set φQ : q2Block 1 K {k, l} →* G := Q.Φ.comp (Subgroup.inclusion (q2Block_pair_le_right' k l))
  have hrange : ∀ {m : Fin N} (Φ : q2Block 1 K {m} →* G)
      (h : q2Block 1 K {k, l} ≤ q2Block 1 K {m}),
      (Φ.comp (Subgroup.inclusion h)).range = ((q2Block 1 K {k, l}).subgroupOf
        (q2Block 1 K {m})).map Φ := by
    intro m Φ h
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have h2 : 2 ≤ ((planeCoordsQ2 1 ({k, l} : Finset (Fin N)))ᶜ).card := by omega
  have hr : φP.range = φQ.range := by
    rw [hrange P.Φ, hrange Q.Φ, P.map_overlap_eq hK hkl h2]
    have h2' : 2 ≤ ((planeCoordsQ2 1 ({l, k} : Finset (Fin N)))ᶜ).card := by
      rwa [Finset.pair_comm]
    have h3 := Q.map_overlap_eq hK hkl.symm h2'
    rw [show ({l, k} : Finset (Fin N)) = {k, l} from Finset.pair_comm l k] at h3
    rw [h3, sup_comm]
  have hS : ∀ s ∈ ctSpBlock 1 K ({k, l} : Finset (Fin N)), φP s = φQ s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := mem_ctSpBlock.1 hs
    have hyk : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have e1 := P.N1 y hyk
    have e2 := Q.N1 y hyl
    have hs' : s = ⟨ctEmbed 1 y, ctEmbed_mem_q2Block_iff.2 hy⟩ := Subtype.ext hys.symm
    rw [hs']
    exact e1.trans e2.symm
  have hQinj : Function.Injective φQ := by
    have := Q.injective_overlap hkl.symm
    intro x y hxy
    have h1 : (⟨x, by rw [Finset.pair_comm]; exact x.2⟩ : q2Block 1 K {l, k}) =
        ⟨y, by rw [Finset.pair_comm]; exact y.2⟩ := this hxy
    exact Subtype.ext (congrArg (fun w : q2Block 1 K {l, k} =>
      (w : SpecialLinearGroup (Fin (2 * N + 1)) K)) h1)
  obtain ⟨a, h1 | h1⟩ := exists_ctTor_of_range_eq (by omega) hpkl φP φQ
    (P.injective_overlap hkl) hQinj hr hS
  · exact ⟨a, Or.inl fun x hx => h1 ⟨x, hx⟩⟩
  · exact ⟨a, Or.inr fun x hx => h1 ⟨x, hx⟩⟩

end Edge

section Align

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {N : ℕ} {e : L ≃* StatedSp N K}

theorem exists_ctLinParamAgree_odd (hK : 4 ≤ Nat.card K) (hN : 4 ≤ N)
    (P : ∀ k : Fin N, CtLinParam 1 e k) :
    ∃ Q : ∀ k : Fin N, CtLinParam 1 e k, CtLinParamAgree Q := by
  classical
  obtain ⟨o⟩ : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hex : ∀ k : Fin N, ∃ R : CtLinParam 1 e k,
      ∀ (x : SpecialLinearGroup (Fin (2 * N + 1)) K) (hx : x ∈ q2Block 1 K {k, o}),
        R.Φ ⟨x, q2Block_pair_le_left' k o hx⟩ = (P o).Φ ⟨x, q2Block_pair_le_right' k o hx⟩ := by
    intro k
    by_cases hko : k = o
    · subst hko
      exact ⟨P k, fun x hx => rfl⟩
    · obtain ⟨a, h1 | h1⟩ := CtLinParam.exists_ctTor_of_overlap hK hN hko (P k) (P o)
      · refine ⟨(P k).twistTor a⁻¹, fun x hx => ?_⟩
        rw [CtLinParam.twistTor_Φ_apply]
        have h2 := h1 _ (ctTorAut_mem_q2Block a⁻¹ hx)
        exact h2.trans (congrArg (P o).Φ (Subtype.ext (ctTorAut_apply_inv a x)))
      · refine ⟨((P k).twistTor a).twist, fun x hx => ?_⟩
        rw [CtLinParam.twist_Φ_apply, CtLinParam.twistTor_Φ_apply]
        have h2 := h1 _ (ctTorAut_mem_q2Block a (ctGraph_mem_q2Block hx))
        exact h2.trans (congrArg (P o).Φ (Subtype.ext (ctTorAut_ctGraph_ctTorAut_ctGraph a x)))
  choose Q hQ using hex
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl : x ∈ q2Block 1 K {k, l} := mem_q2Block_pair' hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SpecialLinearGroup (Fin (2 * N + 1)) K)
      (hy : y ∈ q2Block 1 K {m}) (hy' : y ∈ q2Block 1 K {o}),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQ _ y (mem_q2Block_pair' hy hy')
  by_cases hko : k = o
  · subst hko
    exact (hagreeo x hx hx).trans (hagreeo x hx' hx).symm
  by_cases hlo : l = o
  · subst hlo
    exact (hagreeo x hx hx').trans (hagreeo x hx' hx').symm
  obtain ⟨p, hp⟩ : ({o, k, l}ᶜ : Finset (Fin N)).Nonempty := compl_triple_nonempty hN o k l
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  set y := SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (N := N) (Sum.inl p)) (1 : K)
    with hy
  have hyR : ∀ R : Finset (Fin N), p ∉ R → y ∈ q2Block 1 K R := by
    intro R hpR
    refine LinearPilot.transvection_mem_blockSpecialLinear _ ?_ (ctV_mem_compl R) 1
    rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2]
    exact hpR
  have hyk : y ∈ q2Block 1 K {k} := hyR _ (by simpa using hp.2.1)
  have hyl : y ∈ q2Block 1 K {l} := hyR _ (by simpa using hp.2.2)
  have hyo : y ∈ q2Block 1 K {o} := hyR _ (by simpa using hp.1)
  have hQinj := (Q l).injective_overlap (Ne.symm hkl)
  have hylk : y ∈ q2Block 1 K {l, k} := mem_q2Block_pair' hyl hyk
  obtain ⟨a, h1 | h1⟩ := CtLinParam.exists_ctTor_of_overlap hK (by omega) hkl (Q k) (Q l)
  ·
    have h2 := h1 y (mem_q2Block_pair' hyk hyl)
    rw [hagreeo y hyk hyo, ← hagreeo y hyl hyo] at h2
    have hmem : ctTorAut a y ∈ q2Block 1 K {l, k} := ctTorAut_mem_q2Block a hylk
    have h3 : (⟨y, hylk⟩ : q2Block 1 K {l, k}) = ⟨ctTorAut a y, hmem⟩ := hQinj h2
    have ha1 : a = 1 := (ctTorAut_transvection_eq_iff a p).1
      (congrArg (fun w : q2Block 1 K {l, k} => (w : SpecialLinearGroup (Fin (2 * N + 1)) K))
        h3).symm
    subst ha1
    exact (h1 x hxkl).trans (congrArg (Q l).Φ (Subtype.ext
      (show ctTorAut (N := N) (K := K) 1 x = x by rw [ctTorAut_one, MulAut.one_apply])))
  ·
    exfalso
    have h2 := h1 y (mem_q2Block_pair' hyk hyl)
    rw [hagreeo y hyk hyo, ← hagreeo y hyl hyo] at h2
    have hmem : ctTorAut a (ctGraph 1 y) ∈ q2Block 1 K {l, k} :=
      ctTorAut_mem_q2Block a (ctGraph_mem_q2Block hylk)
    have h3 : (⟨y, hylk⟩ : q2Block 1 K {l, k}) = ⟨ctTorAut a (ctGraph 1 y), hmem⟩ := hQinj h2
    exact ctTorAut_ctGraph_transvection_ne a p
      (congrArg (fun w : q2Block 1 K {l, k} => (w : SpecialLinearGroup (Fin (2 * N + 1)) K))
        h3).symm

end Align

end CFSG.SeitzReduction.SymplecticPilot
