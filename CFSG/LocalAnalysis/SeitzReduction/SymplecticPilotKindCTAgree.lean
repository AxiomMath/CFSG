module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTRigid

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] {N ε : ℕ}

theorem ct_transvection_one_mul_self {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    SpecialLinearGroup.transvection hab (1 : K) * SpecialLinearGroup.transvection hab 1 = 1 := by
  apply Subtype.ext
  change Matrix.transvection a b (1 : K) * Matrix.transvection a b 1 = 1
  rw [Matrix.transvection_mul_transvection_same a b hab (1 : K) 1, CharTwo.add_self_eq_zero,
    Matrix.transvection_zero]

theorem ctGraph_transvection_ne {p p' : Fin N} (hpp : p ≠ p') :
    ctGraph ε (SpecialLinearGroup.transvection (show q2Coord N ε (Sum.inl (Sum.inl p)) ≠
      q2Coord N ε (Sum.inl (Sum.inl p')) from fun h => hpp (Sum.inl.inj (Sum.inl.inj
        ((q2Coord N ε).injective h)))) (1 : K)) ≠
      SpecialLinearGroup.transvection (show q2Coord N ε (Sum.inl (Sum.inl p)) ≠
      q2Coord N ε (Sum.inl (Sum.inl p')) from fun h => hpp (Sum.inl.inj (Sum.inl.inj
        ((q2Coord N ε).injective h)))) (1 : K) := by
  set a := q2Coord N ε (Sum.inl (Sum.inl p)) with ha
  set b := q2Coord N ε (Sum.inl (Sum.inl p')) with hb
  have hab : a ≠ b := fun h => hpp (Sum.inl.inj (Sum.inl.inj ((q2Coord N ε).injective h)))
  intro h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * N + ε)) K =>
    (z : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a b) h
  have hinv : (SpecialLinearGroup.transvection hab (1 : K))⁻¹ =
      SpecialLinearGroup.transvection hab 1 :=
    inv_eq_of_mul_eq_one_right (ct_transvection_one_mul_self hab)
  rw [coe_ctGraph, hinv, q2GramMat_mul_mul_apply, transpose_apply,
    SpecialLinearGroup.transvection_coe] at h1
  have hpa : q2Par N ε a = q2Coord N ε (Sum.inl (Sum.inr p)) := by
    rw [ha, q2Par_q2Coord]; rfl
  have hpb : q2Par N ε b = q2Coord N ε (Sum.inl (Sum.inr p')) := by
    rw [hb, q2Par_q2Coord]; rfl
  rw [hpa, hpb] at h1
  simp only [Matrix.add_apply, single_apply, Matrix.one_apply,
    (q2Coord N ε).injective.eq_iff, ha, hb] at h1
  simp [hpp, Ne.symm hpp] at h1

section Edge

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {e : L ≃* StatedSp N K}

omit [CharP K 2] in
theorem q2Block_pair_le_left' (k l : Fin N) : q2Block ε K {k, l} ≤ q2Block ε K {k} :=
  q2Block_anti (by simp)

omit [CharP K 2] in
theorem q2Block_pair_le_right' (k l : Fin N) : q2Block ε K {k, l} ≤ q2Block ε K {l} :=
  q2Block_anti (by simp)

omit [CharP K 2] in
theorem mem_q2Block_pair' {k l : Fin N} {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hx : x ∈ q2Block ε K {k}) (hx' : x ∈ q2Block ε K {l}) : x ∈ q2Block ε K {k, l} := by
  have h := blockSpecialLinear_inf_le _ _ ⟨hx, hx'⟩
  rw [q2Block, show ({k, l} : Finset (Fin N)) = {k} ∪ {l} from rfl, planeCoordsQ2_union,
    Finset.compl_union]
  exact h

omit [Finite G] in
theorem CtLinParam.injective_overlap {k : Fin N} (P : CtLinParam ε e k) {l : Fin N}
    (hkl : k ≠ l) : Function.Injective (P.Φ.comp (Subgroup.inclusion (q2Block_pair_le_left' k l))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  have hz' : Subgroup.inclusion (q2Block_pair_le_left' k l) z ∈ P.Φ.ker := hz
  have hc := P.ker_le hz'
  have h1 := LinearPilot.eq_one_of_mem_center_of_mem_blockSpecialLinear
    (I := (planeCoordsQ2 ε ({k, l} : Finset (Fin N)))ᶜ)
    (Finset.compl_subset_compl.2 (planeCoordsQ2_mono (by simp)))
    (j := q2Coord N ε (Sum.inl (Sum.inl l))) (by
      rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2, inPlanes_inl]
      simpa using Ne.symm hkl) (by
      rw [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2, inPlanes_inl]
      simp) hc z.2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  exact congrArg (fun w : q2Block ε K {k} => (w : SpecialLinearGroup (Fin (2 * N + ε)) K)) h1

theorem CtLinParam.eq_or_eq_ctGraph_of_overlap [Finite K] (hK : 4 ≤ Nat.card K) (hN : 4 ≤ N)
    {k l : Fin N} (hkl : k ≠ l) (P : CtLinParam 0 e k) (Q : CtLinParam 0 e l) :
    (∀ (x : SpecialLinearGroup (Fin (2 * N + 0)) K) (hx : x ∈ q2Block 0 K {k, l}),
      P.Φ ⟨x, q2Block_pair_le_left' k l hx⟩ = Q.Φ ⟨x, q2Block_pair_le_right' k l hx⟩) ∨
    (∀ (x : SpecialLinearGroup (Fin (2 * N + 0)) K) (hx : x ∈ q2Block 0 K {k, l}),
      P.Φ ⟨x, q2Block_pair_le_left' k l hx⟩ =
        Q.Φ ⟨ctGraph 0 x, q2Block_pair_le_right' k l (ctGraph_mem_q2Block hx)⟩) := by
  have hcard : ((planeCoordsQ2 0 ({k, l} : Finset (Fin N)))ᶜ).card = 2 * N - 4 := by
    rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_pair hkl, Fintype.card_fin]
    omega
  obtain ⟨p, hp⟩ : ({k, l}ᶜ : Finset (Fin N)).Nonempty := compl_pair_nonempty (by omega) k l
  have hpkl : p ∉ ({k, l} : Finset (Fin N)) := Finset.mem_compl.1 hp
  set φP : q2Block 0 K {k, l} →* G := P.Φ.comp (Subgroup.inclusion (q2Block_pair_le_left' k l))
  set φQ : q2Block 0 K {k, l} →* G := Q.Φ.comp (Subgroup.inclusion (q2Block_pair_le_right' k l))
  have hrange : ∀ {m : Fin N} (Φ : q2Block 0 K {m} →* G)
      (h : q2Block 0 K {k, l} ≤ q2Block 0 K {m}),
      (Φ.comp (Subgroup.inclusion h)).range = ((q2Block 0 K {k, l}).subgroupOf
        (q2Block 0 K {m})).map Φ := by
    intro m Φ h
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have h2 : 2 ≤ ((planeCoordsQ2 0 ({k, l} : Finset (Fin N)))ᶜ).card := by omega
  have hr : φP.range = φQ.range := by
    rw [hrange P.Φ, hrange Q.Φ, P.map_overlap_eq hK hkl h2]
    have h2' : 2 ≤ ((planeCoordsQ2 0 ({l, k} : Finset (Fin N)))ᶜ).card := by
      rwa [Finset.pair_comm]
    have h3 := Q.map_overlap_eq hK hkl.symm h2'
    rw [show ({l, k} : Finset (Fin N)) = {k, l} from Finset.pair_comm l k] at h3
    rw [h3, sup_comm]
  have hS : ∀ s ∈ ctSpBlock 0 K ({k, l} : Finset (Fin N)), φP s = φQ s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := mem_ctSpBlock.1 hs
    have hyk : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have e1 := P.N1 y hyk
    have e2 := Q.N1 y hyl
    have hs' : s = ⟨ctEmbed 0 y, ctEmbed_mem_q2Block_iff.2 hy⟩ := Subtype.ext hys.symm
    rw [hs']
    exact e1.trans e2.symm
  rcases eq_or_eq_ctGraph_of_range_eq (by omega) hpkl φP φQ (P.injective_overlap hkl)
      (by
        have := Q.injective_overlap hkl.symm
        intro x y hxy
        have h1 : (⟨x, by rw [Finset.pair_comm]; exact x.2⟩ : q2Block 0 K {l, k}) =
            ⟨y, by rw [Finset.pair_comm]; exact y.2⟩ := this hxy
        exact Subtype.ext (congrArg (fun w : q2Block 0 K {l, k} =>
          (w : SpecialLinearGroup (Fin (2 * N + 0)) K)) h1))
      hr hS with h1 | h1
  · left
    intro x hx
    exact h1 ⟨x, hx⟩
  · right
    intro x hx
    exact h1 ⟨x, hx⟩

end Edge

section Align

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {e : L ≃* StatedSp N K}

theorem exists_ctLinParamAgree [Finite K] (hK : 4 ≤ Nat.card K) (hN : 5 ≤ N)
    (P : ∀ k : Fin N, CtLinParam 0 e k) :
    ∃ Q : ∀ k : Fin N, CtLinParam 0 e k, CtLinParamAgree Q := by
  classical
  have hcomp := fun {k l : Fin N} (R : CtLinParam 0 e k) (R' : CtLinParam 0 e l)
      (hkl : k ≠ l) => CtLinParam.eq_or_eq_ctGraph_of_overlap hK (by omega) hkl R R'
  set o : Fin N := ⟨0, by omega⟩ with ho
  let Ag : ∀ k : Fin N, CtLinParam 0 e k → Prop := fun k R =>
    ∀ (x : SpecialLinearGroup (Fin (2 * N + 0)) K) (hx : x ∈ q2Block 0 K {k, o}),
      R.Φ ⟨x, q2Block_pair_le_left' k o hx⟩ = (P o).Φ ⟨x, q2Block_pair_le_right' k o hx⟩
  let Q : ∀ k : Fin N, CtLinParam 0 e k := fun k =>
    if Ag k (P k) then P k else (P k).twist
  have hQoo : Q o = P o := by
    change (if Ag o (P o) then P o else (P o).twist) = P o
    exact ite_eq_left (fun x hx => rfl)
  have hQo : ∀ k : Fin N, Ag k (Q k) := by
    intro k
    by_cases h : Ag k (P k)
    · change Ag k (if Ag k (P k) then P k else (P k).twist)
      rw [ite_eq_left h]
      exact h
    · change Ag k (if Ag k (P k) then P k else (P k).twist)
      rw [ite_eq_right h]
      have hk : k ≠ o := by
        rintro rfl
        exact h fun x hx => rfl
      rcases hcomp (P k) (P o) hk with h1 | h1
      · exact absurd h1 h
      · intro x hx
        rw [CtLinParam.twist_Φ_apply]
        have hγx : ctGraph 0 x ∈ q2Block 0 K {k, o} := ctGraph_mem_q2Block hx
        have h2 := h1 _ hγx
        have h3 : (P o).Φ ⟨ctGraph 0 (ctGraph 0 x),
            q2Block_pair_le_right' k o (ctGraph_mem_q2Block hγx)⟩ =
            (P o).Φ ⟨x, q2Block_pair_le_right' k o hx⟩ :=
          congrArg (P o).Φ (Subtype.ext (ctGraph_ctGraph x))
        rw [← h3, ← h2]
        rfl
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl : x ∈ q2Block 0 K {k, l} := mem_q2Block_pair' hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SpecialLinearGroup (Fin (2 * N + 0)) K)
      (hy : y ∈ q2Block 0 K {m}) (hy' : y ∈ q2Block 0 K {o}),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQo _ y (mem_q2Block_pair' hy hy')
  by_cases hko' : k = o
  · subst hko'
    rw [hQoo] at *
    exact (hagreeo x hx' hx).symm
  by_cases hlo : l = o
  · subst hlo
    rw [hQoo]
    exact hagreeo x hx hx'
  rcases hcomp (Q k) (Q l) hkl with h1 | h1
  · exact h1 x hxkl
  · exfalso
    obtain ⟨p, hp⟩ : ({o, k, l}ᶜ : Finset (Fin N)).Nonempty := compl_triple_nonempty
      (by omega) o k l
    obtain ⟨p', hp'⟩ : (({o, k, l, p} : Finset (Fin N))ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_four (a := o) (b := k) (c := l) (d := p)
      omega
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp hp'
    set a₀ := q2Coord N 0 (Sum.inl (Sum.inl p)) with ha₀
    set b₀ := q2Coord N 0 (Sum.inl (Sum.inl p')) with hb₀
    have hab : a₀ ≠ b₀ := fun h => hp'.2.2.2 (Sum.inl.inj (Sum.inl.inj
      ((q2Coord N 0).injective h))).symm
    set y := SpecialLinearGroup.transvection hab (1 : K) with hy
    have hyR : ∀ R : Finset (Fin N), p ∉ R → p' ∉ R → y ∈ q2Block 0 K R := by
      intro R hpR hp'R
      refine LinearPilot.transvection_mem_blockSpecialLinear hab ?_ ?_ 1
      · rw [Finset.mem_compl, ha₀, q2Coord_mem_planeCoordsQ2]; exact hpR
      · rw [Finset.mem_compl, hb₀, q2Coord_mem_planeCoordsQ2]; exact hp'R
    have hyk : y ∈ q2Block 0 K {k} := hyR _ (by simpa using hp.2.1) (by simpa using hp'.2.1)
    have hyl : y ∈ q2Block 0 K {l} := hyR _ (by simpa using hp.2.2) (by simpa using hp'.2.2.1)
    have hyo : y ∈ q2Block 0 K {o} := hyR _ (by simpa using hp.1) (by simpa using hp'.1)
    have hγy := fun {R : Finset (Fin N)} (h : y ∈ q2Block 0 K R) => ctGraph_mem_q2Block (ε := 0) h
    have h2 := h1 y (mem_q2Block_pair' hyk hyl)
    rw [hagreeo y hyk hyo, hagreeo _ (hγy hyl) (hγy hyo)] at h2
    have hyok : y ∈ q2Block 0 K {o, k} := mem_q2Block_pair' hyo hyk
    have h3 : (⟨y, hyok⟩ : q2Block 0 K {o, k}) = ⟨ctGraph 0 y, ctGraph_mem_q2Block hyok⟩ :=
      (P o).injective_overlap (l := k) (Ne.symm hko') h2
    have h4 := congrArg (fun w : q2Block 0 K {o, k} =>
      (w : SpecialLinearGroup (Fin (2 * N + 0)) K)) h3
    exact ctGraph_transvection_ne (ε := 0) (K := K) (Ne.symm hp'.2.2.2) h4.symm

end Align

end CFSG.SeitzReduction.SymplecticPilot
