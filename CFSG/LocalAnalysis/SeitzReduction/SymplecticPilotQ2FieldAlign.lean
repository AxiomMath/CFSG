module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt elt_injective)
open CFSG.Quasithin (perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section Overlap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

omit [Finite G] [Finite F] in
theorem centralizer_modelToG_zpowers (e : L ≃* StatedSp n K) (x : StatedSp n K) :
    centralizer (modelToG e (zpowers x) : Set G) =
      centralizer ({((e.symm x : L) : G)} : Set G) := by
  rw [UnitaryPilot.modelToG_def, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rfl

omit [Finite G] in
theorem nsElt_mem_spBlock_compl {k l : Fin n} (hkl : k ≠ l) :
    nsElt (K := K) l ∈ spBlock K ({k}ᶜ : Finset (Fin n)) := by
  rw [spBlock_compl_singleton]
  exact nsTorusSp_le_complSp (Ne.symm hkl) (nsElt_mem_nsTorusSp l)

theorem NsFieldParam.map_overlap_eq [CharP F 2] (P : NsFieldParam e t ι σ k) (hF : 4 ≤ Nat.card F)
    {l : Fin n} (hkl : k ≠ l) :
    ((spBlock F ({k, l}ᶜ : Finset (Fin n))).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map
        P.Φ =
      centralizerPerfectCore (modelToG e (nsTorusSp K k) ⊔ modelToG e (nsTorusSp K l)) := by
  set a : spBlock F ({k}ᶜ : Finset (Fin n)) :=
    ⟨spFieldMap n ι (nsElt l), spFieldMap_mem_spBlock ι (nsElt_mem_spBlock_compl hkl)⟩ with ha
  have hPa : P.Φ a = ((e.symm (nsElt l) : L) : G) := P.N1 _ (nsElt_mem_spBlock_compl hkl)
  have hmodel : perfectCore (centralizer ({a} : Set (spBlock F ({k}ᶜ : Finset (Fin n))))) =
      (spBlock F ({k, l}ᶜ : Finset (Fin n))).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n))) := by
    apply map_injective (spBlock F ({k}ᶜ : Finset (Fin n))).subtype_injective
    rw [LinearPilot.map_perfectCore_centralizer_singleton (spBlock F _).subtype_injective,
      range_subtype, subgroupOf_map_subtype, coe_subtype]
    have hle : spBlock F ({k, l}ᶜ : Finset (Fin n)) ≤ spBlock F ({k}ᶜ : Finset (Fin n)) :=
      spBlock_mono fun x hx => mem_compl_singleton_iff'.2 (mem_compl_pair_iff'.1 hx).1
    rw [inf_of_le_left hle, ha]
    change perfectCore (spBlock F ({k}ᶜ : Finset (Fin n)) ⊓
      centralizer ({spFieldMap n ι (nsElt l)} : Set (StatedSp n F))) = _
    rw [spFieldMap_nsElt]
    exact perfectCore_spBlock_compl_inf_centralizer_nsElt k l (commutator_spBlock_eq hF _)
  rw [F4Pilot.centralizerPerfectCore_sup, ← P.range_eq, nsTorusSp,
    centralizer_modelToG_zpowers, ← hPa,
    ← LinearPilot.map_perfectCore_centralizer_singleton P.injective, hmodel]

end Overlap

section Compare

variable {G : Type*} [Group G] {K : Type} [Field K] {F : Type} [Field F] [Finite F] [CharP F 2]
  {n : ℕ} {ι : K →+* F} {σ : F ≃+* F}

theorem eq_or_eq_fieldSp_of_range_eq (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {I : Finset (Fin n)} (hI : 2 ≤ I.card)
    (φP φQ : spBlock F I →* G) (hP : Function.Injective φP) (hQ : Function.Injective φQ)
    (hr : φP.range = φQ.range)
    (hι : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K I),
      φP ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ =
        φQ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩) :
    (∀ (x : StatedSp n F) (hx : x ∈ spBlock F I), φP ⟨x, hx⟩ = φQ ⟨x, hx⟩) ∨
      (∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
        φP ⟨x, hx⟩ = φQ ⟨fieldSp n F σ x, fieldSp_mem_spBlock σ hx⟩) := by
  set θ : MulAut (spBlock F I) := ((MonoidHom.ofInjective hP).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective hQ).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQ).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hP y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  set α : MulAut (StatedSp I.card F) :=
    ((spBlockEquiv I).trans θ).trans (spBlockEquiv I).symm with hαdef
  have hαapp : ∀ g, spBlockEquiv I (α g) = θ (spBlockEquiv I g) := fun g =>
    (spBlockEquiv I).apply_symm_apply _
  have hαfix : ∀ g : StatedSp I.card K, α (statedSpMap ι I.card g) = statedSpMap ι I.card g := by
    intro g
    set y : spBlock F I := spBlockEquiv I (statedSpMap ι I.card g) with hy
    have hgK := (spBlockEquiv (F := K) I g).2
    have hyx : y = ⟨spFieldMap n ι (spBlockEquiv I g : StatedSp n K),
        spFieldMap_mem_spBlock ι hgK⟩ := by
      apply Subtype.ext
      change (y : StatedSp n F) = spFieldMap n ι (spBlockEquiv I g : StatedSp n K)
      rw [hy, coe_spBlockEquiv, coe_spBlockEquiv, spEmbed_statedSpMap, spFieldMap_eq_statedSpMap]
    have hθy : θ y = y := hQ ((hθ y).trans (by rw [hyx]; exact hι _ hgK))
    apply (spBlockEquiv I).injective
    rw [hαapp, hθy]
  obtain ⟨ρ, hρι, hρ⟩ := exists_ringEquiv_eq_fieldSp_of_fix hI ι α hαfix
  have hρσ : ρ = 1 ∨ ρ = σ := F4Pilot.eq_one_or_eq_of_forall_fixSubfield hσ fun c => by
    obtain ⟨d, hd⟩ := (hfix c).1 c.2
    rw [← hd, hρι]
  have hθx : ∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
      ((θ ⟨x, hx⟩ : spBlock F I) : StatedSp n F) = fieldSp n F ρ x := by
    intro x hx
    obtain ⟨g, hg⟩ := (spBlockEquiv I).surjective ⟨x, hx⟩
    rw [← hg, ← hαapp, hρ, coe_spBlockEquiv, F4Pilot.fieldSp_eq_statedSpMap,
      spEmbed_statedSpMap, ← coe_spBlockEquiv, hg, F4Pilot.fieldSp_eq_statedSpMap]
  have key : ∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
      φP ⟨x, hx⟩ = φQ ⟨fieldSp n F ρ x, fieldSp_mem_spBlock ρ hx⟩ := by
    intro x hx
    rw [← hθ ⟨x, hx⟩]
    exact congrArg φQ (Subtype.ext (hθx x hx))
  rcases hρσ with rfl | rfl
  · left
    intro x hx
    rw [key x hx]
    exact congrArg φQ (Subtype.ext (show fieldSp n F 1 x = x by
      rw [map_one, MulAut.one_apply]))
  · right
    exact key

end Compare

section Edge

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] [CharP F 2] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F}
  {σ : F ≃+* F}

theorem NsFieldParam.eq_or_eq_fieldSp_of_overlap (hF : 4 ≤ Nat.card F) (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {k l : Fin n} (hkl : k ≠ l)
    (P : NsFieldParam e t ι σ k) (Q : NsFieldParam e t ι σ l)
    (hI : 2 ≤ ({k, l}ᶜ : Finset (Fin n)).card) :
    (∀ (x : StatedSp n F) (hx : x ∈ spBlock F ({k, l}ᶜ : Finset (Fin n))),
      P.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem'
          (fun h => (mem_compl_pair_iff'.1 h).1 rfl)) hx⟩ =
        Q.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem'
          (fun h => (mem_compl_pair_iff'.1 h).2 rfl)) hx⟩) ∨
    (∀ (x : StatedSp n F) (hx : x ∈ spBlock F ({k, l}ᶜ : Finset (Fin n))),
      P.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem'
          (fun h => (mem_compl_pair_iff'.1 h).1 rfl)) hx⟩ =
        Q.Φ ⟨fieldSp n F σ x, spBlock_mono (subset_compl_singleton_of_notMem'
          (fun h => (mem_compl_pair_iff'.1 h).2 rfl)) (fieldSp_mem_spBlock σ hx)⟩) := by
  set I : Finset (Fin n) := ({k, l}ᶜ : Finset (Fin n)) with hIdef
  have hkI : k ∉ I := fun h => (mem_compl_pair_iff'.1 h).1 rfl
  have hlI : l ∉ I := fun h => (mem_compl_pair_iff'.1 h).2 rfl
  have hIk : spBlock F I ≤ spBlock F ({k}ᶜ : Finset (Fin n)) :=
    spBlock_mono (subset_compl_singleton_of_notMem' hkI)
  have hIl : spBlock F I ≤ spBlock F ({l}ᶜ : Finset (Fin n)) :=
    spBlock_mono (subset_compl_singleton_of_notMem' hlI)
  have hrange : ∀ {m : Fin n} (R : NsFieldParam e t ι σ m)
      (h : spBlock F I ≤ spBlock F ({m}ᶜ : Finset (Fin n))),
      (R.Φ.comp (Subgroup.inclusion h)).range =
        ((spBlock F I).subgroupOf (spBlock F ({m}ᶜ : Finset (Fin n)))).map R.Φ := by
    intro m R h
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have hr : (P.Φ.comp (Subgroup.inclusion hIk)).range =
      (Q.Φ.comp (Subgroup.inclusion hIl)).range := by
    rw [hrange P hIk, hrange Q hIl, hIdef, P.map_overlap_eq hF hkl, Finset.pair_comm,
      Q.map_overlap_eq hF hkl.symm, sup_comm]
  exact eq_or_eq_fieldSp_of_range_eq hσ hfix hI _ _
    (P.injective.comp (Subgroup.inclusion_injective hIk))
    (Q.injective.comp (Subgroup.inclusion_injective hIl)) hr fun x hx =>
      ((P.N1 x (spBlock_mono (subset_compl_singleton_of_notMem' hkI) hx)).trans
        (Q.N1 x (spBlock_mono (subset_compl_singleton_of_notMem' hlI) hx)).symm)

end Edge

section Align

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

omit [Finite G] [Finite F] in
@[expose] noncomputable def NsFieldParam.twist (P : NsFieldParam e t ι σ k)
    (hσι : ∀ c, σ (ι c) = ι c) : NsFieldParam e t ι σ k where
  Φ := P.Φ.comp (fieldBlockSp σ ({k}ᶜ : Finset (Fin n))).toMonoidHom
  injective := P.injective.comp (fieldBlockSp σ ({k}ᶜ : Finset (Fin n))).injective
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 x hx := by
    change P.Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) ⟨spFieldMap n ι x, _⟩) = _
    rw [fieldBlockSp_spFieldMap hσι hx]
    exact P.N1 x hx
  N3 x := P.N3 (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x)

omit [Finite G] [Finite F] in
theorem NsFieldParam.twist_Φ_apply (P : NsFieldParam e t ι σ k) (hσι : ∀ c, σ (ι c) = ι c)
    (x : spBlock F ({k}ᶜ : Finset (Fin n))) :
    (P.twist hσι).Φ x = P.Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x) :=
  rfl

omit [Finite G] [Finite F] in
@[expose] def NsFieldParamAgree (P : ∀ k : Fin n, NsFieldParam e t ι σ k) : Prop :=
  ∀ (k l : Fin n) (x : StatedSp n F) (hx : x ∈ spBlock F ({k}ᶜ : Finset (Fin n)))
    (hx' : x ∈ spBlock F ({l}ᶜ : Finset (Fin n))), (P k).Φ ⟨x, hx⟩ = (P l).Φ ⟨x, hx'⟩

theorem exists_nsFieldParamAgree [CharP K 2] (hF : 4 ≤ Nat.card F) (hn : 4 ≤ n)
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : ∀ k : Fin n, NsFieldParam e t ι σ k) :
    ∃ Q : ∀ k : Fin n, NsFieldParam e t ι σ k, NsFieldParamAgree Q := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hσι : ∀ c, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have hσσ : ∀ x : StatedSp n F, fieldSp n F σ (fieldSp n F σ x) = x := by
    intro x
    have h2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    rw [← MulAut.mul_apply, ← map_mul, h2, map_one, MulAut.one_apply]
  have hcomp := fun {k l : Fin n} (R : NsFieldParam e t ι σ k)
      (R' : NsFieldParam e t ι σ l) (hkl : k ≠ l) =>
    NsFieldParam.eq_or_eq_fieldSp_of_overlap hF hσ hfix hkl R R'
      (by rw [card_compl_pair_of_ne hkl]; omega)
  set o : Fin n := ⟨0, by omega⟩ with ho
  have hko : ∀ k : Fin n, k ∉ ({k, o}ᶜ : Finset (Fin n)) := fun k h =>
    (mem_compl_pair_iff'.1 h).1 rfl
  have hok : ∀ k : Fin n, o ∉ ({k, o}ᶜ : Finset (Fin n)) := fun k h =>
    (mem_compl_pair_iff'.1 h).2 rfl
  let Ag : ∀ k : Fin n, NsFieldParam e t ι σ k → Prop := fun k R =>
    ∀ (x : StatedSp n F) (hx : x ∈ spBlock F ({k, o}ᶜ : Finset (Fin n))),
      R.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' (hko k)) hx⟩ =
        (P o).Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' (hok k)) hx⟩
  let Q : ∀ k : Fin n, NsFieldParam e t ι σ k := fun k =>
    if Ag k (P k) then P k else (P k).twist hσι
  have hQoo : Q o = P o := ite_eq_left (fun x hx => rfl)
  have hQo : ∀ k : Fin n, Ag k (Q k) := by
    intro k
    by_cases h : Ag k (P k)
    · change Ag k (if Ag k (P k) then P k else (P k).twist hσι)
      rw [ite_eq_left h]
      exact h
    · change Ag k (if Ag k (P k) then P k else (P k).twist hσι)
      rw [ite_eq_right h]
      have hk : k ≠ o := by
        rintro rfl
        exact h fun x hx => rfl
      rcases hcomp (P k) (P o) hk with h1 | h1
      · exact absurd h1 h
      · intro x hx
        rw [NsFieldParam.twist_Φ_apply]
        have hσx : fieldSp n F σ x ∈ spBlock F ({k, o}ᶜ : Finset (Fin n)) :=
          fieldSp_mem_spBlock σ hx
        have h2 := h1 _ hσx
        have h3 : (P o).Φ ⟨fieldSp n F σ (fieldSp n F σ x),
            spBlock_mono (subset_compl_singleton_of_notMem' (hok k))
              (fieldSp_mem_spBlock σ hσx)⟩ =
            (P o).Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' (hok k)) hx⟩ :=
          congrArg (P o).Φ (Subtype.ext (hσσ x))
        rw [← h3, ← h2]
        exact congrArg (P k).Φ (Subtype.ext (coe_fieldBlockSp_eq_fieldSp σ _ _))
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra hc
    push Not at hc
    exact hσ1 (RingEquiv.ext hc)
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl := mem_spBlock_compl_pair hx hx'
  have hagreeo : ∀ {m : Fin n} (y : StatedSp n F) (hy : y ∈ spBlock F ({m}ᶜ : Finset (Fin n)))
      (hy' : y ∈ spBlock F ({o}ᶜ : Finset (Fin n))), (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQo _ y (mem_spBlock_compl_pair hy hy')
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
    obtain ⟨i, hi⟩ : ({o, k, l}ᶜ : Finset (Fin n)).Nonempty := compl_triple_nonempty hn o k l
    have hio : i ≠ o := fun h => by simp [h] at hi
    have hik : i ≠ k := fun h => by simp [h] at hi
    have hil : i ≠ l := fun h => by simp [h] at hi
    set y : StatedSp n F := elt (.positiveLong i) c with hy
    have hyN : ∀ m : Fin n, i ≠ m → y ∈ spBlock F ({m}ᶜ : Finset (Fin n)) := fun m him =>
      elt_positiveLong_mem_spBlock (mem_compl_singleton_iff'.2 him) c
    have hσy : fieldSp n F σ y = elt (.positiveLong i) (σ c) := fieldSp_elt σ _ c
    have hσyN : ∀ m : Fin n, i ≠ m → fieldSp n F σ y ∈ spBlock F ({m}ᶜ : Finset (Fin n)) :=
      fun m him => fieldSp_mem_spBlock σ (hyN m him)
    have h2 := h1 y (mem_spBlock_compl_pair (hyN k hik) (hyN l hil))
    rw [hagreeo y (hyN k hik) (hyN o hio), hagreeo _ (hσyN l hil) (hσyN o hio)] at h2
    have h3 := congrArg Subtype.val ((P o).injective h2)
    simp only at h3
    rw [hσy, hy] at h3
    exact hc (elt_injective _ h3).symm

end Align

end CFSG.SeitzReduction.SymplecticPilot
