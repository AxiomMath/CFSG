module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)

private theorem kdc_fixSubgroup_one {K : Type} [Group K] :
    fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem kdc_fixSubgroup_conj {K : Type} [Group K] (v : K) :
    fixSubgroup (MulAut.conj v) = Subgroup.centralizer ({v} : Set K) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem kdc_fixSubgroup_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (α : MulAut S) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    rw [mem_fixSubgroup] at hy
    have h2 : e (α (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h3 := congrArg e.symm h2
    simpa using h3
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup] at hx
    rw [mem_fixSubgroup]
    show e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]

private theorem kdc_congr_symm_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (α : MulAut S) : MulAut.congr e.symm (MulAut.congr e α) = α := by
  ext x
  simp [MulAut.congr_apply]

private theorem kdc_congr_ne_one {S T : Type} [Group S] [Group T] (e : S ≃* T) {α : MulAut S}
    (h : α ≠ 1) : MulAut.congr e α ≠ 1 := by
  intro h1
  apply h
  apply (MulAut.congr e).injective
  rw [h1, map_one]

private theorem kdc_center_eq_bot {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

private theorem kdc_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem kdc_eq_top_of_pComp {p : ℕ} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    {I : Subgroup T} (hI : GLAPComponent p (⊤ : Subgroup T) I) : I = ⊤ := by
  rcases kdc_isSubnormal_top hI.2.1 rfl with h | h
  · exact absurd h (glaPComponent_ne_bot' hI)
  · exact h

private theorem kdc_coprime_ker {p : ℕ} {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (X : Subgroup S) : Nat.Coprime p (Nat.card ↥(X ⊓ e.toMonoidHom.ker)) := by
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective
  rw [hk, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right p

private theorem kdc_eq_bot_of_perfect_of_solvable {Y : Type} [Group Y] {J S : Subgroup Y}
    (hS : Group.IsSolvable ↥S) (hJS : J ≤ S) (hperf : ⁅J, J⁆ = J) : J = ⊥ := by
  by_contra hne
  have hJ'ne : J.subgroupOf S ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJS, h0, Subgroup.map_bot]
  have hlt : ⁅J.subgroupOf S, J.subgroupOf S⁆ < J.subgroupOf S :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅J.subgroupOf S, J.subgroupOf S⁆ = J.subgroupOf S := by
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJS]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

private theorem kdc_false_of_map_solvable {p : ℕ} (hp : p.Prime) {S T : Type} [Group S] [Group T]
    [Finite S] (e : S ≃* T) {X L : Subgroup S} (hL : GLAPComponent p X L)
    (hsol : Group.IsSolvable ↥(X.map e.toMonoidHom)) : False := by
  have h1 := glaPComponent_map hp e.toMonoidHom (kdc_coprime_ker e X) hL
  have hJ : L.map e.toMonoidHom = ⊥ :=
    kdc_eq_bot_of_perfect_of_solvable hsol h1.1 (glaPComponent_perfect h1)
  exact glaPComponent_ne_bot' hL
    ((Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).1 hJ)

private theorem kdc_false_of_map_layer {p : ℕ} (hp : p.Prime) {S T : Type} [Group S] [Group T]
    [Finite S] (e : S ≃* T) {X L : Subgroup S} (hL : GLAPComponent p X L)
    (hlay : GLAPLayer p (X.map e.toMonoidHom) = ⊥) : False := by
  have h1 := glaPComponent_map hp e.toMonoidHom (kdc_coprime_ker e X) hL
  have h2 : L.map e.toMonoidHom ≤ GLAPLayer p (X.map e.toMonoidHom) := le_sSup h1
  rw [hlay, le_bot_iff] at h2
  exact glaPComponent_ne_bot' hL
    ((Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).1 h2)

private theorem kdc_layer_eq_bot {p : ℕ} {Y : Type} [Group Y] {X : Subgroup Y}
    (h : ∀ L : Subgroup Y, GLAPComponent p X L → False) : GLAPLayer p X = ⊥ := by
  refine le_antisymm ?_ bot_le
  unfold GLAPLayer
  exact sSup_le fun L hL => (h L hL).elim

private theorem kdc_chev_split {p : ℕ} {S : Type} [Group S] (h : IsChevSimple p S) :
    (∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      ∃ i : TauCeti.CFSGIndex, ambiguousChev p i ∧ Nonempty (S ≃* i.Group) := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic q hq => exact (show False from hi).elim
    | alternating n hn => exact (show False from hi).elim
    | sporadic s => exact (show False from hi).elim
    | lie d => exact Or.inl ⟨d, hi, ⟨e⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e⟩⟩

private theorem kdc_noP_lie_inner {p : ℕ} (hp : p.Prime) (hC : KDCharP p) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = p)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (α : MulAut S) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (hin : α ∈ inner S) (L : Subgroup S) (hL : GLAPComponent p (fixSubgroup α) L) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, rfl⟩ := (show α ∈ (MulAut.conj : S →* MulAut S).range from hin)
  have hup : u ^ p = 1 := by
    have h1 : MulAut.conj (u ^ p) = 1 := by
      rw [map_pow]
      exact hα
    have hcen : u ^ p ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := DFunLike.congr_fun h1 g
      rw [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.1 hg).symm
    rw [kdc_center_eq_bot hnc, Subgroup.mem_bot] at hcen
    exact hcen
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hv : orderOf (e u) = p :=
    orderOf_eq_prime (by rw [← map_pow, hup, map_one])
      (fun h => hu1 (e.injective (h.trans (map_one e).symm)))
  have hlay : GLAPLayer p
      (Subgroup.centralizer ({e u} : Set (TauCeti.CFSGIndex.lie d).Group)) = ⊥ :=
    hC d hd (e u) hv
  have hmap : (fixSubgroup (MulAut.conj u)).map e.toMonoidHom =
      Subgroup.centralizer ({e u} : Set (TauCeti.CFSGIndex.lie d).Group) := by
    rw [← kdc_fixSubgroup_congr, congr_conj, kdc_fixSubgroup_conj]
  exact kdc_false_of_map_layer hp e hL (by rw [hmap]; exact hlay)

private theorem kdc_noP_amb {p : ℕ} (hp : p.Prime) (hA : KDAmbSolv p) {S : Type} [Group S]
    [Finite S] (i : TauCeti.CFSGIndex) (hi : ambiguousChev p i) (e : S ≃* i.Group)
    (α : MulAut S) (hα : α ^ p = 1) (hα1 : α ≠ 1) (L : Subgroup S)
    (hL : GLAPComponent p (fixSubgroup α) L) : False := by
  have hβp : MulAut.congr e α ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hsol := hA i hi (MulAut.congr e α) hβp (kdc_congr_ne_one e hα1)
  rw [kdc_fixSubgroup_congr] at hsol
  exact kdc_false_of_map_solvable hp e hL hsol

private theorem kdc_unique_lie {p : ℕ} (hp : p.Prime) (hU : KDOutChevUnique p) {S : Type}
    [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = p)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (α : MulAut S) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (hout : α ∉ inner S) (I J : Subgroup S) (hI : GLAPComponent p (fixSubgroup α) I)
    (hJ : GLAPComponent p (fixSubgroup α) J) : I = J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hβp : MulAut.congr e α ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := kdc_congr_ne_one e hα1
  have hord : orderOf (MulAut.congr e α) = p := orderOf_eq_prime hβp hβ1
  have hβout : MulAut.congr e α ∉
      (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* _).range := by
    rintro ⟨g, hg⟩
    apply hout
    show α ∈ (MulAut.conj : S →* MulAut S).range
    rw [MonoidHom.mem_range]
    refine ⟨e.symm g, ?_⟩
    rw [← kdc_congr_symm_congr e α, ← hg, congr_conj]
  have hI' := glaPComponent_map hp e.toMonoidHom (kdc_coprime_ker e (fixSubgroup α)) hI
  have hJ' := glaPComponent_map hp e.toMonoidHom (kdc_coprime_ker e (fixSubgroup α)) hJ
  rw [← kdc_fixSubgroup_congr e α] at hI'
  rw [← kdc_fixSubgroup_congr e α] at hJ'
  exact Subgroup.map_injective (f := e.toMonoidHom) e.injective
    (hU d hd _ hord hβout _ _ hI' hJ')

theorem kdChevInner_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hC : KDCharP p)
    (hA : KDAmbSolv p) : KDChevInner p := by
  intro S _ _ hS hnc hcat α hα hα1 hin
  refine kdc_layer_eq_bot fun L hL => ?_
  rcases kdc_chev_split hcat with ⟨d, hd, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · exact kdc_noP_lie_inner hp hC hnc d hd e α hα hα1 hin L hL
  · exact kdc_noP_amb hp hA i hi e α hα hα1 L hL

theorem kdChevUnique_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hC : KDCharP p)
    (hU : KDOutChevUnique p) (hA : KDAmbSolv p) : KDChevUnique p := by
  intro S _ _ hS hnc hcat α hα I J hI hJ
  by_cases hα1 : α = 1
  · subst hα1
    rw [kdc_fixSubgroup_one] at hI hJ
    exact (kdc_eq_top_of_pComp hI).trans (kdc_eq_top_of_pComp hJ).symm
  · rcases kdc_chev_split hcat with ⟨d, hd, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · by_cases hin : α ∈ inner S
      · exact (kdc_noP_lie_inner hp hC hnc d hd e α hα hα1 hin I hI).elim
      · exact kdc_unique_lie hp hU d hd e α hα hα1 hin I J hI hJ
    · exact (kdc_noP_amb hp hA i hi e α hα hα1 I hI).elim

end CFSG.LocalAnalysis.GLTheoremA
