module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormKernel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54Good

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.SemisimpleComponentStructure
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem compG_le_centZ (i : ComponentIndex ↥(centZ z)) : compG z i ≤ centZ z :=
  Subgroup.map_subtype_le _

theorem compG_le_layer (i : ComponentIndex ↥(centZ z)) :
    compG z i ≤ (layer ↥(centZ z)).map (centZ z).subtype := by
  rw [layer_eq_componentClassification]
  exact Subgroup.map_mono (Layer.component_le i.property)

theorem compG_comm {i j : ComponentIndex ↥(centZ z)} (hij : compG z i ≠ compG z j) {x y : G}
    (hx : x ∈ compG z i) (hy : y ∈ compG z j) : x * y = y * x := by
  have hne : i.val ≠ j.val := fun h => hij (congrArg (Subgroup.map (centZ z).subtype) h)
  have h := LocalComponents.commute_of_ne i.val j.val i.property j.property hne
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb
  exact congrArg Subtype.val this.symm

theorem exists_compG_conj {c : G} (hc : c ∈ centZ z) (i : ComponentIndex ↥(centZ z)) :
    ∃ j : ComponentIndex ↥(centZ z), compG z j = (compG z i).map (MulAut.conj c).toMonoidHom := by
  refine ⟨⟨i.val.map (MulAut.conj (⟨c, hc⟩ : ↥(centZ z))).toMonoidHom,
    (LocalComponents.equiv_iff _ _).2 i.property⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : G), ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply]⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem conj_invol {H : Type*} [Group H] {t : H} (ht : t * t = 1) (q : H) :
    t * (t * q * t⁻¹) * t⁻¹ = q := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [ht']
  calc t * (t * q * t) * t = (t * t) * q * (t * t) := by simp only [mul_assoc]
    _ = q := by rw [ht]; simp

def conjInv {H : Type*} [Group H] (Q : Subgroup H) (t : H) (ht : t * t = 1)
    (hQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) : MulAut ↥Q where
  toFun q := ⟨t * q * t⁻¹, hQ q q.2⟩
  invFun q := ⟨t * q * t⁻¹, hQ q q.2⟩
  left_inv q := Subtype.ext (conj_invol ht q)
  right_inv q := Subtype.ext (conj_invol ht q)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem exists_noncentral_s (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥)
    (hP : Psub z = zpowers z) (ht : t * t = 1) (htc : t ∈ centZ z)
    (i : ComponentIndex ↥(centZ z)) (hnorm : ∀ n ∈ compG z i, t * n * t⁻¹ ∈ compG z i) :
    ∃ s ∈ compG z i, s⁻¹ * (t * s * t⁻¹) ∈ zpowers z ∧ ∃ q ∈ compG z i, s * q ≠ q * s := by
  set tH : ↥(centZ z) := ⟨t, htc⟩ with htH
  have hnormH : ∀ q ∈ i.val, tH * q * tH⁻¹ ∈ i.val := by
    intro q hq
    obtain ⟨b, hb, hbq⟩ := hnorm (q : G) ⟨q, hq, rfl⟩
    have : b = tH * q * tH⁻¹ := Subtype.ext hbq
    rw [← this]
    exact hb
  have htt : tH * tH = 1 := Subtype.ext ht
  let τ : MulAut ↥i.val := conjInv i.val tH htt hnormH
  have hinv : Function.Involutive τ := fun q => Subtype.ext (conj_invol htt _)
  obtain ⟨x, hxnc, hxf⟩ :=
    InvolutionFixedPoints.exists_noncentral_lifted_fixed i.property.2.2 τ hinv
  rw [FixedCentralPreimage.mem_iff] at hxf
  refine ⟨(((x : ↥i.val) : ↥(centZ z)) : G), ⟨x, x.2, rfl⟩, ?_, ?_⟩
  · have := center_component_mem_zpowers hodd hP i _ hxf
    simpa [τ, conjInv, htH] using this
  · rw [Subgroup.mem_center_iff] at hxnc
    push Not at hxnc
    obtain ⟨g, hg⟩ := hxnc
    exact ⟨(((g : ↥i.val) : ↥(centZ z)) : G), ⟨g, g.2, rfl⟩,
      fun h => hg (Subtype.ext (Subtype.ext h.symm))⟩

theorem mem_normPair_of_comm_mem_zpowers {s : G} (hs : s ∈ centZ z)
    (hc : s⁻¹ * (t * s * t⁻¹) ∈ zpowers z) : s ∈ normPair z t := by
  set c := s⁻¹ * (t * s * t⁻¹) with hcdef
  have hcs : c * s = s * c := commute_of_mem_zpowers_of_mem_centZ hc hs
  have e : s * t * s⁻¹ = c⁻¹ * t := by
    have h1 : c * (s * t * s⁻¹) = t := by
      calc c * (s * t * s⁻¹) = (c * s) * t * s⁻¹ := by group
        _ = (s * c) * t * s⁻¹ := by rw [hcs]
        _ = t := by rw [hcdef]; group
    exact eq_inv_mul_of_mul_eq h1
  have hmem : s * t * s⁻¹ ∈ pair z t := by
    rw [e]
    exact mul_mem (inv_mem (mem_sup_left hc)) (mem_sup_right (mem_zpowers t))
  have hsz : s * z * s⁻¹ ∈ pair z t := by
    rw [mem_centralizer_singleton_iff.1 hs, mul_inv_cancel_right]
    exact mem_sup_left (mem_zpowers z)
  exact mem_normalizer_fintype fun n hn => conj_mem_sup_of_conj_mem
    (conj_mem_zpowers_of_conj_mem hsz) (conj_mem_zpowers_of_conj_mem hmem) n hn

theorem Level55.card_le_two_mul_card_inf (d : Level55 G t z) {A : Subgroup G}
    (hAC : A ≤ centZ z) (hAn : A ≤ normPair z t) :
    Nat.card A ≤ 2 * Nat.card (centPair z t ⊓ A : Subgroup G) := by
  by_cases hA : A ≤ centPair z t
  · rw [inf_eq_right.2 hA]
    omega
  · obtain ⟨x, hxA, hxK⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    have h2 := d.relIndex_centPair_eq_two hAC hAn hxA hxK
    have := Subgroup.relIndex_mul_card (H := centPair z t) (K := A)
    rw [h2] at this
    omega

theorem map_conj_pow_ne {Q : Subgroup G} {σ : G} (hσ : orderOf σ = 23)
    (hnot : σ ∉ normalizer (Q : Set G)) {j k : ℕ} (hjk : j < k) (hk : k < 23) :
    Q.map (MulAut.conj (σ ^ j)).toMonoidHom ≠ Q.map (MulAut.conj (σ ^ k)).toMonoidHom := by
  intro h
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  have hg : (σ ^ d)⁻¹ ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_fintype fun n hn => ?_
    have hmem : σ ^ j * n * (σ ^ j)⁻¹ ∈ Q.map (MulAut.conj (σ ^ j)).toMonoidHom :=
      ⟨n, hn, rfl⟩
    rw [h] at hmem
    obtain ⟨y, hy, hyn⟩ := hmem
    have hyn' : σ ^ (j + d) * y * (σ ^ (j + d))⁻¹ = σ ^ j * n * (σ ^ j)⁻¹ := hyn
    have : (σ ^ d)⁻¹ * n * (σ ^ d)⁻¹⁻¹ = y := by
      calc (σ ^ d)⁻¹ * n * (σ ^ d)⁻¹⁻¹
          = (σ ^ (j + d))⁻¹ * (σ ^ j * n * (σ ^ j)⁻¹) * σ ^ (j + d) := by
            rw [pow_add]; group
        _ = y := by rw [← hyn']; group
    rw [this]
    exact hy
  have hg' : σ ^ d ∈ normalizer (Q : Set G) := inv_mem_iff.1 hg
  have hd0 : 0 < d := by omega
  have hcop : Nat.Coprime d (orderOf σ) := by
    rw [hσ]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 23)).2
      (Nat.not_dvd_of_pos_of_lt hd0 (by omega))).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact hnot (hm ▸ pow_mem hg' m)

end CFSG.EvenSporadicStandard.TwoB
