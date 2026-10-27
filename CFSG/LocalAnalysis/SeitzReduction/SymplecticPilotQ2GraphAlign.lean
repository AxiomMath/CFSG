module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {N ε : ℕ}
  {hK : Nat.card K = 2} {e : L ≃* StatedSp N K}

theorem q2Block_pair_le_left (k l : Fin N) : q2Block ε K {k, l} ≤ q2Block ε K {k} :=
  q2Block_anti (by simp)

theorem q2Block_pair_le_right (k l : Fin N) : q2Block ε K {k, l} ≤ q2Block ε K {l} :=
  q2Block_anti (by simp)

theorem mem_q2Block_pair {k l : Fin N} {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hx : x ∈ q2Block ε K {k}) (hx' : x ∈ q2Block ε K {l}) : x ∈ q2Block ε K {k, l} := by
  have h := blockSpecialLinear_inf_le _ _ ⟨hx, hx'⟩
  rw [q2Block, show ({k, l} : Finset (Fin N)) = {k} ∪ {l} from rfl, planeCoordsQ2_union,
    Finset.compl_union]
  exact h

theorem NsLinParam.map_overlap_eq [CharP K 2] {k : Fin N} (P : NsLinParam hK ε e k) {l : Fin N}
    (hkl : k ≠ l) (hperf : ⁅q2Block ε K {k, l}, q2Block ε K {k, l}⁆ = q2Block ε K {k, l}) :
    ((q2Block ε K {k, l}).subgroupOf (q2Block ε K {k})).map P.Φ =
      centralizerPerfectCore (modelToG e (nsTorusSp K k) ⊔ modelToG e (nsTorusSp K l)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; omega)
  have hnl : nsElt (K := K) l ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
    have := nsElt_mem_spBlock_compl (K := K) hkl
    simpa using this
  set a : q2Block ε K {k} := ⟨q2Embed ε hK (nsElt l), (q2Embed_mem_q2Block_iff hK).2 hnl⟩ with ha
  have hPa : P.Φ a = ((e.symm (nsElt l) : L) : G) := P.N1 _ hnl
  have hmodel : perfectCore (centralizer ({a} : Set (q2Block ε K {k}))) =
      (q2Block ε K {k, l}).subgroupOf (q2Block ε K {k}) := by
    apply Subgroup.map_injective (q2Block ε K {k}).subtype_injective
    rw [LinearPilot.map_perfectCore_centralizer_singleton (q2Block ε K {k}).subtype_injective,
      range_subtype, subgroupOf_map_subtype, inf_of_le_left (q2Block_pair_le_left k l)]
    exact perfectCore_q2Block_inf_centralizer hK hkl hperf
  rw [F4Pilot.centralizerPerfectCore_sup, ← P.range_eq, nsTorusSp,
    centralizer_modelToG_zpowers, ← hPa,
    ← LinearPilot.map_perfectCore_centralizer_singleton P.injective, hmodel]

theorem NsLinParam.eq_or_eq_q2Graph_of_overlap [CharP K 2] (hε : ε ≤ 1) (hN : 4 ≤ N)
    {k l : Fin N} (hkl : k ≠ l) (P : NsLinParam hK ε e k) (Q : NsLinParam hK ε e l) :
    (∀ (x : SpecialLinearGroup (Fin (2 * N + ε)) K) (hx : x ∈ q2Block ε K {k, l}),
      P.Φ ⟨x, q2Block_pair_le_left k l hx⟩ = Q.Φ ⟨x, q2Block_pair_le_right k l hx⟩) ∨
    (∀ (x : SpecialLinearGroup (Fin (2 * N + ε)) K) (hx : x ∈ q2Block ε K {k, l}),
      P.Φ ⟨x, q2Block_pair_le_left k l hx⟩ =
        Q.Φ ⟨q2Graph ε hK x, q2Block_pair_le_right k l (q2Graph_mem_q2Block hK hx)⟩) := by
  have hcard : 3 ≤ ((planeCoordsQ2 ε ({k, l} : Finset (Fin N)))ᶜ).card := by
    rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_pair hkl, Fintype.card_fin]
    omega
  have hperf := commutator_q2Block_eq (K := K) hcard
  obtain ⟨p, hp⟩ : ({k, l}ᶜ : Finset (Fin N)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_pair hkl, Fintype.card_fin]
    omega
  obtain ⟨p', hp'⟩ : (({k, l, p} : Finset (Fin N))ᶜ).Nonempty := compl_triple_nonempty hN k l p
  have hpkl : p ∉ ({k, l} : Finset (Fin N)) := Finset.mem_compl.1 hp
  have hp'kl : p' ∉ ({k, l} : Finset (Fin N)) := fun h => by
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact hp'.1 h
    · exact hp'.2.1 h
  have hpp' : p ≠ p' := fun h => by
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
    exact hp'.2.2 h.symm
  set φP : q2Block ε K {k, l} →* G := P.Φ.comp (Subgroup.inclusion (q2Block_pair_le_left k l))
  set φQ : q2Block ε K {k, l} →* G := Q.Φ.comp (Subgroup.inclusion (q2Block_pair_le_right k l))
  have hrange : ∀ {m : Fin N} (Φ : q2Block ε K {m} →* G) (h : q2Block ε K {k, l} ≤ q2Block ε K {m}),
      (Φ.comp (Subgroup.inclusion h)).range = ((q2Block ε K {k, l}).subgroupOf
        (q2Block ε K {m})).map Φ := by
    intro m Φ h
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have hr : φP.range = φQ.range := by
    rw [hrange P.Φ, hrange Q.Φ, P.map_overlap_eq hkl hperf]
    have h2 := Q.map_overlap_eq hkl.symm (by rwa [Finset.pair_comm])
    rw [show ({l, k} : Finset (Fin N)) = {k, l} from Finset.pair_comm l k] at h2
    rw [h2, sup_comm]
  have hS : ∀ s ∈ q2SpBlock ε K hK ({k, l} : Finset (Fin N)), φP s = φQ s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := (mem_q2SpBlock hK).1 hs
    have hyk : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have e1 := P.N1 y hyk
    have e2 := Q.N1 y hyl
    have hs' : s = ⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩ := Subtype.ext hys.symm
    rw [hs']
    exact e1.trans e2.symm
  rcases eq_or_eq_q2Graph_of_range_eq hK hε hpp' hpkl hp'kl hcard φP φQ
      (P.injective.comp (Subgroup.inclusion_injective _))
      (Q.injective.comp (Subgroup.inclusion_injective _)) hr hS with h1 | h1
  · left
    intro x hx
    exact h1 ⟨x, hx⟩
  · right
    intro x hx
    exact h1 ⟨x, hx⟩

omit [Finite G] in
@[expose] noncomputable def NsLinParam.twist [CharP K 2] {k : Fin N} (P : NsLinParam hK ε e k) :
    NsLinParam hK ε e k where
  Φ := P.Φ.comp (q2GraphBlock ε hK {k}).toMonoidHom
  injective := P.injective.comp (q2GraphBlock ε hK {k}).injective
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 y hy := by
    change P.Φ (q2GraphBlock ε hK {k} ⟨q2Embed ε hK y, _⟩) = _
    rw [q2GraphBlock_fix hK ((mem_q2SpBlock hK).2 ⟨y, hy, rfl⟩)]
    exact P.N1 y hy

omit [Finite G] in
theorem NsLinParam.twist_Φ_apply [CharP K 2] {k : Fin N} (P : NsLinParam hK ε e k)
    (x : q2Block ε K {k}) : P.twist.Φ x = P.Φ (q2GraphBlock ε hK {k} x) :=
  rfl

omit [Finite G] in
@[expose] def NsLinParamAgree (P : ∀ k : Fin N, NsLinParam hK ε e k) : Prop :=
  ∀ (k l : Fin N) (x : SpecialLinearGroup (Fin (2 * N + ε)) K) (hx : x ∈ q2Block ε K {k})
    (hx' : x ∈ q2Block ε K {l}), (P k).Φ ⟨x, hx⟩ = (P l).Φ ⟨x, hx'⟩

theorem exists_nsLinParamAgree [CharP K 2] (hε : ε ≤ 1) (hN : 5 ≤ N)
    (P : ∀ k : Fin N, NsLinParam hK ε e k) :
    ∃ Q : ∀ k : Fin N, NsLinParam hK ε e k, NsLinParamAgree Q := by
  classical
  have hcomp := fun {k l : Fin N} (R : NsLinParam hK ε e k) (R' : NsLinParam hK ε e l)
      (hkl : k ≠ l) => NsLinParam.eq_or_eq_q2Graph_of_overlap hε (by omega) hkl R R'
  set o : Fin N := ⟨0, by omega⟩ with ho
  let Ag : ∀ k : Fin N, NsLinParam hK ε e k → Prop := fun k R =>
    ∀ (x : SpecialLinearGroup (Fin (2 * N + ε)) K) (hx : x ∈ q2Block ε K {k, o}),
      R.Φ ⟨x, q2Block_pair_le_left k o hx⟩ = (P o).Φ ⟨x, q2Block_pair_le_right k o hx⟩
  let Q : ∀ k : Fin N, NsLinParam hK ε e k := fun k =>
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
        rw [NsLinParam.twist_Φ_apply]
        have hγx : q2Graph ε hK x ∈ q2Block ε K {k, o} := q2Graph_mem_q2Block hK hx
        have h2 := h1 _ hγx
        have h3 : (P o).Φ ⟨q2Graph ε hK (q2Graph ε hK x),
            q2Block_pair_le_right k o (q2Graph_mem_q2Block hK hγx)⟩ =
            (P o).Φ ⟨x, q2Block_pair_le_right k o hx⟩ :=
          congrArg (P o).Φ (Subtype.ext (by
            change q2Graph ε hK (q2Graph ε hK x) = x
            rw [← MulAut.mul_apply, q2Graph_mul_self, MulAut.one_apply]))
        rw [← h3, ← h2]
        rfl
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl : x ∈ q2Block ε K {k, l} := mem_q2Block_pair hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SpecialLinearGroup (Fin (2 * N + ε)) K)
      (hy : y ∈ q2Block ε K {m}) (hy' : y ∈ q2Block ε K {o}),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQo _ y (mem_q2Block_pair hy hy')
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
    set a₀ := q2Coord N ε (Sum.inl (Sum.inl p)) with ha₀
    set b₀ := q2Coord N ε (Sum.inl (Sum.inl p')) with hb₀
    have hab : a₀ ≠ b₀ := fun h => hp'.2.2.2 (Sum.inl.inj (Sum.inl.inj
      ((q2Coord N ε).injective h))).symm
    set y := SpecialLinearGroup.transvection hab (1 : K) with hy
    have hyR : ∀ R : Finset (Fin N), p ∉ R → p' ∉ R → y ∈ q2Block ε K R := by
      intro R hpR hp'R
      refine LinearPilot.transvection_mem_blockSpecialLinear hab ?_ ?_ 1
      · rw [Finset.mem_compl, ha₀, q2Coord_mem_planeCoordsQ2]; exact hpR
      · rw [Finset.mem_compl, hb₀, q2Coord_mem_planeCoordsQ2]; exact hp'R
    have hyk : y ∈ q2Block ε K {k} := hyR _ (by simpa using hp.2.1) (by simpa using hp'.2.1)
    have hyl : y ∈ q2Block ε K {l} := hyR _ (by simpa using hp.2.2) (by simpa using hp'.2.2.1)
    have hyo : y ∈ q2Block ε K {o} := hyR _ (by simpa using hp.1) (by simpa using hp'.1)
    have hγy := fun {R : Finset (Fin N)} (h : y ∈ q2Block ε K R) => q2Graph_mem_q2Block hK h
    have h2 := h1 y (mem_q2Block_pair hyk hyl)
    rw [hagreeo y hyk hyo, hagreeo _ (hγy hyl) (hγy hyo)] at h2
    have h3 := congrArg Subtype.val ((P o).injective h2)
    exact q2Graph_transvection_ne (ε := ε) hK (Ne.symm hp'.2.2.2) h3.symm

end CFSG.SeitzReduction.SymplecticPilot
