module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldRigid
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt elt_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)

section Twist

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  [CharP F 2] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F} {k : Fin n}

@[expose] noncomputable def FieldNeighbourParam.twist (P : FieldNeighbourParam e t ι σ k)
    (hσι : ∀ c, σ (ι c) = ι c) : FieldNeighbourParam e t ι σ k :=
  FieldNeighbourParam.ofNormalized
    (P.Φ.comp (fieldBlockSp σ ({k}ᶜ : Finset (Fin n))).toMonoidHom)
    (by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
        ← MonoidHom.range_eq_map, P.range_eq])
    (by
      intro x hx
      have hx' : P.Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x) = P.Φ 1 := by
        rw [map_one]
        exact hx
      have h1 := P.injective hx'
      rw [← map_one (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)))] at h1
      rw [(fieldBlockSp σ ({k}ᶜ : Finset (Fin n))).injective h1]
      exact one_mem _)
    (fun x hx => by
      change P.Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) ⟨spFieldMap n ι x, _⟩) = _
      rw [fieldBlockSp_spFieldMap hσι hx]
      exact P.N1 x hx)
    (fun x => P.N3 (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x))

theorem FieldNeighbourParam.twist_Φ_apply (P : FieldNeighbourParam e t ι σ k)
    (hσι : ∀ c, σ (ι c) = ι c) (x : spBlock F ({k}ᶜ : Finset (Fin n))) :
    (P.twist hσι).Φ x = P.Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x) :=
  rfl

end Twist

section Normalize

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F}
  {σ : F ≃+* F}

omit [Finite G] [CharP K 2] [Finite F] in
theorem mem_spBlock_compl_pair {x : StatedSp n F} {k l : Fin n}
    (hk : x ∈ spBlock F ({k}ᶜ : Finset (Fin n))) (hl : x ∈ spBlock F ({l}ᶜ : Finset (Fin n))) :
    x ∈ spBlock F ({k, l}ᶜ : Finset (Fin n)) := by
  intro a b hab
  by_cases ha : a ∈ planeCoords ({k}ᶜ : Finset (Fin n)) ∧ b ∈ planeCoords ({k}ᶜ : Finset (Fin n))
  · refine hl a b fun h' => hab ⟨?_, ?_⟩
    · exact mem_compl_pair_iff'.2 ⟨mem_compl_singleton_iff'.1 ha.1, mem_compl_singleton_iff'.1 h'.1⟩
    · exact mem_compl_pair_iff'.2 ⟨mem_compl_singleton_iff'.1 ha.2, mem_compl_singleton_iff'.1 h'.2⟩
  · exact hk a b ha

omit [Finite G] [CharP K 2] [Finite F] in
theorem card_compl_pair_of_ne {k l : Fin n} (hkl : k ≠ l) :
    ({k, l}ᶜ : Finset (Fin n)).card = n - 2 := by
  rw [Finset.card_compl, Finset.card_pair hkl, Fintype.card_fin]

theorem exists_fieldParamAgree (hK : 4 ≤ Nat.card K) (hn : 4 ≤ n) (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (P : ∀ k : Fin n, FieldNeighbourParam e t ι σ k) :
    ∃ Q : ∀ k : Fin n, FieldNeighbourParam e t ι σ k, FieldParamAgree Q := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hσι : ∀ c, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have hσσ : ∀ x : StatedSp n F, fieldSp n F σ (fieldSp n F σ x) = x := by
    intro x
    have h2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    rw [← MulAut.mul_apply, ← map_mul, h2, map_one, MulAut.one_apply]
  have hcomp := fun {k l : Fin n} (R : FieldNeighbourParam e t ι σ k)
      (R' : FieldNeighbourParam e t ι σ l) (hkl : k ≠ l) =>
    R.eq_or_eq_fieldSp_of_overlap hK hσ hfix R' (I := ({k, l}ᶜ : Finset (Fin n)))
      (fun h => (mem_compl_pair_iff'.1 h).1 rfl) (fun h => (mem_compl_pair_iff'.1 h).2 rfl)
      (by rw [card_compl_pair_of_ne hkl]; omega)
  set o : Fin n := ⟨0, by omega⟩ with ho
  have hko : ∀ k : Fin n, k ∉ ({k, o}ᶜ : Finset (Fin n)) := fun k h =>
    (mem_compl_pair_iff'.1 h).1 rfl
  have hok : ∀ k : Fin n, o ∉ ({k, o}ᶜ : Finset (Fin n)) := fun k h =>
    (mem_compl_pair_iff'.1 h).2 rfl
  let Ag : ∀ k : Fin n, FieldNeighbourParam e t ι σ k → Prop := fun k R =>
    ∀ (x : StatedSp n F) (hx : x ∈ spBlock F ({k, o}ᶜ : Finset (Fin n))),
      R.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' (hko k)) hx⟩ =
        (P o).Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' (hok k)) hx⟩
  let Q : ∀ k : Fin n, FieldNeighbourParam e t ι σ k := fun k =>
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
        rw [FieldNeighbourParam.twist_Φ_apply]
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

end Normalize

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {n : ℕ}

theorem exists_injective_fieldRow (hK : 4 ≤ Nat.card K) (hn : 5 ≤ n) (e : L ≃* StatedSp n K)
    {t : G} {ι : K →+* F} {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ k : Fin n, Nonempty (FieldNeighbourParam e t ι σ k)) :
    ∃ ψ : StatedSp n F →* G, Function.Injective ψ ∧ ψ.range = spGlobal e ∧
      (∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x) := by
  obtain ⟨Q, hQ⟩ := exists_fieldParamAgree hK (by omega) hσ hfix fun k => (hparam k).some
  exact exists_injective_fieldRow_of_agree hK hn Q hQ

end Main

end CFSG.SeitzReduction.SymplecticPilot
