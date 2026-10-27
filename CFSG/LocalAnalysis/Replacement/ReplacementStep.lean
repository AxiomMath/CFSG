module

public import CFSG.LocalAnalysis.Replacement.ThompsonSubgroup
public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.Replacement.ClassTwo
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG

namespace GlaubermanReplacement

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

private theorem relIndex_sup_of_le_normalizer {H K : Subgroup G} (h : H ≤ normalizer K) :
    K.relIndex (H ⊔ K) = K.relIndex H := by
  have hK : K ≤ normalizer K := le_normalizer
  rw [← relIndex_subgroupOf (sup_le h hK), subgroupOf_sup h hK, relIndex_sup_right,
    relIndex_subgroupOf h]

private theorem card_mul_relIndex {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  simpa using relIndex_mul_relIndex ⊥ H K bot_le h

section Construction

variable (A : Subgroup G) (b : G)

private def commutators : Subgroup G :=
  closure ((⁅·, b⁆) '' (A : Set G))

private def replacement : Subgroup G :=
  (A ⊓ A.map (MulAut.conj b).toMonoidHom) ⊔ commutators A b

variable {A b}

private theorem commutator_mem_commutators {a : G} (ha : a ∈ A) : ⁅a, b⁆ ∈ commutators A b :=
  subset_closure ⟨a, ha, rfl⟩

private theorem commutators_le_sup :
    commutators A b ≤ A ⊔ A.map (MulAut.conj b).toMonoidHom := by
  refine closure_le _ |>.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have := mul_mem_sup ha (mem_map_of_mem (MulAut.conj b).toMonoidHom (inv_mem ha))
  simpa [commutatorElement_def, mul_assoc] using this

private theorem sup_commutators :
    A ⊔ commutators A b = A ⊔ A.map (MulAut.conj b).toMonoidHom := by
  refine le_antisymm (sup_le le_sup_left commutators_le_sup) (sup_le le_sup_left ?_)
  rintro _ ⟨a, ha, rfl⟩
  have := mul_mem_sup ha (commutator_mem_commutators (b := b) (inv_mem ha))
  simpa [commutatorElement_def, mul_assoc] using this

private theorem commutators_le {B : Subgroup G} (hB : B.Normal) (hb : b ∈ B) :
    commutators A b ≤ B := by
  refine closure_le _ |>.2 ?_
  rintro _ ⟨a, -, rfl⟩
  exact B.mul_mem (hB.conj_mem b hb a) (B.inv_mem hb)

private theorem inf_le_map {B : Subgroup G} (hb : b ∈ B) (hBA : ⁅B, B⁆ ≤ A) :
    A ⊓ B ≤ A.map (MulAut.conj b).toMonoidHom := by
  rintro x ⟨hxA, hxB⟩
  refine ⟨x * ⁅x⁻¹, b⁻¹⁆, A.mul_mem hxA (hBA (commutator_mem_commutator (inv_mem hxB)
    (inv_mem hb))), ?_⟩
  simp [commutatorElement_def, mul_assoc]

end Construction

section Normalizing

variable {A N : Subgroup G} {b : G}

private theorem map_conj_le (hAN : A ≤ N) (hbN : b ∈ normalizer N) :
    A.map (MulAut.conj b).toMonoidHom ≤ N :=
  (map_mono hAN).trans (mem_normalizer_iff_map_conj_eq.1 hbN).le

private theorem le_normalizer_map_conj (hNA : N ≤ normalizer A) (hbN : b ∈ normalizer N) :
    N ≤ normalizer (A.map (MulAut.conj b).toMonoidHom) := by
  rw [← map_equiv_normalizer_eq]
  exact (mem_normalizer_iff_map_conj_eq.1 hbN).ge.trans (map_mono hNA)

variable [IsMulCommutative A]

private theorem commutator_sup_map_conj_le (hAN : A ≤ N) (hNA : N ≤ normalizer A)
    (hbN : b ∈ normalizer N) :
    ⁅A ⊔ A.map (MulAut.conj b).toMonoidHom, A ⊔ A.map (MulAut.conj b).toMonoidHom⁆ ≤
      A ⊓ A.map (MulAut.conj b).toMonoidHom :=
  commutator_sup_le_inf (hAN.trans (le_normalizer_map_conj hNA hbN))
    ((map_conj_le hAN hbN).trans hNA)

end Normalizing

private theorem isMulCommutative_commutators {p : ℕ} (hp : Odd p) {A B : Subgroup G} {b : G}
    [IsMulCommutative A] [B.Normal] (hB : IsPGroup p B)
    (hclass : ⁅B, B⁆ ≤ (center B).map B.subtype) (hBA : ⁅B, B⁆ ≤ A) (hb : b ∈ B)
    (hH : ⁅A ⊔ A.map (MulAut.conj b).toMonoidHom, A ⊔ A.map (MulAut.conj b).toMonoidHom⁆ ≤
      centralizer (A ⊔ A.map (MulAut.conj b).toMonoidHom : Subgroup G)) :
    IsMulCommutative (commutators A b) := by
  have hclass' : commutator B ≤ center B := by
    rwa [← map_le_map_iff_of_injective B.subtype_injective, map_subtype_commutator]
  have hfix {g : G} {c : B} (h : g * c = c * g) : MulAut.conjNormal g c = c :=
    Subtype.ext (by simp [h])
  have hfixA {g : G} (hg : g ∈ A) (c : B) (hc : c ∈ commutator B) : MulAut.conjNormal g c = c :=
    hfix (setLike_mul_comm hg (hBA (map_subtype_commutator B ▸ mem_map_of_mem _ hc)))
  refine isMulCommutative_closure ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ -
  have hdisp (g : G) (c : B) :
      (((MulAut.conjNormal g : MulAut B).toMonoidHom c * c⁻¹ : B) : G) = ⁅g, (c : G)⁆ := by
    simp [commutatorElement_def]
  let X : B →* B := (MulAut.conjNormal a : MulAut B).toMonoidHom
  let Y : B →* B := (MulAut.conjNormal a' : MulAut B).toMonoidHom
  let b' : B := ⟨b, hb⟩
  let w : B := Y b' * b'⁻¹
  have hw : (w : G) = ⁅a', b⁆ := hdisp a' b'
  have hz : ((X w * w⁻¹ : B) : G) ∈
      centralizer (A ⊔ A.map (MulAut.conj b).toMonoidHom : Subgroup G) := by
    refine hH ?_
    rw [hdisp, hw]
    exact commutator_mem_commutator (mem_sup_left ha)
      (commutators_le_sup (commutator_mem_commutators ha'))
  have hfixz {g : G} (hg : g ∈ A) : MulAut.conjNormal g (X w * w⁻¹) = X w * w⁻¹ :=
    hfix (mem_centralizer_iff.1 hz g (mem_sup_left hg))
  have hXY (v : B) : X (Y v) = Y (X v) := by
    simp only [X, Y, MulEquiv.coe_toMonoidHom]
    rw [← MulAut.mul_apply, ← map_mul, setLike_mul_comm ha ha', map_mul, MulAut.mul_apply]
  have key := commute_of_commutator_le_center hp hB hclass' hXY (hfixA ha) (hfixA ha')
    (inv_mul_cancel_right _ _).symm (inv_mul_cancel_right _ _).symm (inv_mul_cancel_right _ _).symm
    (hfixz ha) (hfixz ha')
  change Commute ⁅a, b⁆ ⁅a', b⁆
  rw [← hdisp a b', ← hw]
  exact key.map B.subtype

section Replacement

variable {A B N : Subgroup G} {b : G}

private theorem replacement_le (hAN : A ≤ N) (hbN : b ∈ normalizer N) : replacement A b ≤ N :=
  sup_le (inf_le_left.trans hAN) (commutators_le_sup.trans (sup_le hAN (map_conj_le hAN hbN)))

private theorem isMulCommutative_replacement {p : ℕ} (hp : Odd p) [IsMulCommutative A] [B.Normal]
    (hB : IsPGroup p B) (hclass : ⁅B, B⁆ ≤ (center B).map B.subtype) (hBA : ⁅B, B⁆ ≤ A)
    (hb : b ∈ B) (hAN : A ≤ N) (hNA : N ≤ normalizer A) (hbN : b ∈ normalizer N) :
    IsMulCommutative (replacement A b) := by
  have hD := inf_le_centralizer_sup (A := A) (D := A.map (MulAut.conj b).toMonoidHom)
  have := isMulCommutative_commutators hp hB hclass hBA hb
    ((commutator_sup_map_conj_le hAN hNA hbN).trans hD)
  have hle : replacement A b ≤ A ⊔ A.map (MulAut.conj b).toMonoidHom :=
    sup_le (inf_le_left.trans le_sup_left) commutators_le_sup
  rw [← le_centralizer_iff_isMulCommutative]
  exact sup_le (hD.trans (centralizer_le hle)) <| le_centralizer_iff.1 <|
    sup_le (hD.trans (centralizer_le commutators_le_sup)) (le_centralizer _)

private theorem card_replacement [Finite G] [IsMulCommutative A] (hB : B.Normal) (hb : b ∈ B)
    (hBA : ⁅B, B⁆ ≤ A) (hAN : A ≤ N) (hNA : N ≤ normalizer A) (hbN : b ∈ normalizer N) :
    Nat.card (replacement A b) = Nat.card A := by
  set A' := A.map (MulAut.conj b).toMonoidHom
  set C := commutators A b
  have hCA : C ≤ normalizer A :=
    commutators_le_sup.trans ((sup_le hAN (map_conj_le hAN hbN)).trans hNA)
  have hCD : C ≤ normalizer (A ⊓ A' : Subgroup G) :=
    (le_centralizer_iff.1 inf_le_centralizer_sup).trans' commutators_le_sup |>.trans
      (centralizer_le_normalizer _)
  have hDC : A ⊓ A' ⊓ C = A ⊓ C := le_antisymm (inf_le_inf_right _ inf_le_left)
    (le_inf (le_inf inf_le_left ((inf_le_inf_left A (commutators_le hB hb)).trans
      (inf_le_map hb hBA))) inf_le_right)
  have hindex : (A ⊓ A').relIndex (replacement A b) = (A ⊓ A').relIndex A' := calc
    _ = (A ⊓ A').relIndex C := by
      rw [replacement, sup_comm, relIndex_sup_of_le_normalizer hCD]
    _ = A.relIndex (C ⊔ A) := by
      rw [← inf_relIndex_right, hDC, inf_relIndex_right, relIndex_sup_of_le_normalizer hCA]
    _ = A.relIndex A' := by
      rw [sup_comm, sup_commutators, sup_comm,
        relIndex_sup_of_le_normalizer ((map_conj_le hAN hbN).trans hNA)]
    _ = (A ⊓ A').relIndex A' := (inf_relIndex_right A A').symm
  have hDR : A ⊓ A' ≤ replacement A b := le_sup_left
  rw [← card_mul_relIndex hDR, hindex, card_mul_relIndex inf_le_right,
    card_map_of_injective (MulAut.conj b).injective]

private theorem mem_normalizer_replacement [Finite G] (hB : B.Normal) (hb : b ∈ B)
    (hBA : ⁅B, B⁆ ≤ A) : b ∈ normalizer (replacement A b) := by
  have hle : (replacement A b).map (MulAut.conj b).toMonoidHom ≤ replacement A b := by
    rw [replacement, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have := mul_mem_sup hx (commutator_mem_commutators (b := b) (inv_mem hx.1))
      simpa [commutatorElement_def, mul_assoc] using this
    · rintro _ ⟨c, hc, rfl⟩
      have hbc : ⁅b, c⁆ ∈ A ⊓ B := le_inf hBA (commutator_le_self B)
        (commutator_mem_commutator hb (commutators_le hB hb hc))
      have := mul_mem_sup (mem_inf.2 ⟨hbc.1, inf_le_map hb hBA hbc⟩) hc
      simpa [commutatorElement_def, mul_assoc] using this
  exact mem_normalizer_iff_map_conj_eq.2 <|
    eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj b).injective).ge

private theorem le_normalizer_replacement [IsMulCommutative A] (hB : B.Normal) (hb : b ∈ B)
    (hBA : ⁅B, B⁆ ≤ A) (hAN : A ≤ N) (hNA : N ≤ normalizer A) (hbN : b ∈ normalizer N) :
    N ≤ normalizer (replacement A b) := by
  set A' := A.map (MulAut.conj b).toMonoidHom
  have hCA : commutators A b ≤ normalizer A :=
    commutators_le_sup.trans ((sup_le hAN (map_conj_le hAN hbN)).trans hNA)
  have hHB : (A ⊔ A') ⊓ B ≤ replacement A b := by
    intro x hx
    obtain ⟨hxH, hxB⟩ := mem_inf.1 hx
    rw [← sup_commutators] at hxH
    obtain ⟨a, ha, c, hc, rfl⟩ : x ∈ (A : Set G) * commutators A b :=
      coe_mul_of_right_le_normalizer_left _ _ hCA ▸ hxH
    have haB : a ∈ B := by
      simpa using B.mul_mem hxB (B.inv_mem (commutators_le hB hb hc))
    exact mul_mem_sup ⟨ha, inf_le_map hb hBA ⟨ha, haB⟩⟩ hc
  have hR : replacement A b = (A ⊓ A') ⊔ ((A ⊔ A') ⊓ B) :=
    le_antisymm (sup_le_sup_left (le_inf commutators_le_sup (commutators_le hB hb)) _)
      (sup_le le_sup_left hHB)
  have hNA' := le_normalizer_map_conj hNA hbN
  rw [hR]
  refine le_trans (le_inf ?_ ?_) (inf_normalizer_le_normalizer_sup _ _)
  · exact (le_inf hNA hNA').trans inf_normalizer_le_normalizer_inf
  · exact (le_inf ((le_inf hNA hNA').trans (inf_normalizer_le_normalizer_sup _ _))
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

end Replacement

private theorem exists_mem_normalizer_notMem {p : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {A B N : Subgroup G} [B.Normal] (hAN : A ≤ N) (hNAB : N ≤ A ⊔ B) (hBN : ¬ B ≤ N) :
    ∃ b ∈ B, b ∈ normalizer N ∧ b ∉ N := by
  have := (hG.to_subgroup (A ⊔ B)).isNilpotent
  have hlt : N.subgroupOf (A ⊔ B) < ⊤ :=
    lt_top_iff_ne_top.2 fun h ↦ hBN (le_sup_right.trans (subgroupOf_eq_top.1 h))
  obtain ⟨x, hxN', hxN⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hNAB, mem_subgroupOf] at hxN'
  rw [mem_subgroupOf] at hxN
  obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_normal_right.1 x.2
  have hcx : c = a⁻¹ * x := by rw [← hac, inv_mul_cancel_left]
  refine ⟨c, hc, hcx ▸ mul_mem (inv_mem (le_normalizer (hAN ha))) hxN', fun hcN ↦ hxN ?_⟩
  exact hac ▸ N.mul_mem (hAN ha) hcN

theorem exists_replacement {p : ℕ} (hp : p.Prime) (hodd : Odd p) {S : Type*} [Group S] [Finite S]
    (hS : IsPGroup p S) {A B : Subgroup S} (hB : B.Normal)
    (hclass : ⁅B, B⁆ ≤ (center B).map B.subtype) (hBZ : ⁅B, B⁆ ≤ thompsonCenter S)
    (hA : A ∈ maxOrderAbelianSubgroups S) (hBA : ¬ B ≤ normalizer A) :
    ∃ A' ∈ maxOrderAbelianSubgroups S, ¬ B ≤ A' ∧ B ⊓ normalizer A < B ⊓ normalizer A' := by
  have := hA.1
  have := Fact.mk hp
  have hBA' : ⁅B, B⁆ ≤ A := hBZ.trans (thompsonCenter_le hA)
  have hAN : A ≤ A ⊔ (B ⊓ normalizer A) := le_sup_left
  have hNA : A ⊔ (B ⊓ normalizer A) ≤ normalizer A := sup_le le_normalizer inf_le_right
  obtain ⟨b, hb, hbN, hbN'⟩ := exists_mem_normalizer_notMem hS hAN
    (sup_le_sup_left inf_le_left A) fun h ↦ hBA (h.trans hNA)
  refine ⟨replacement A b, mem_maxOrderAbelianSubgroups.2
    ⟨isMulCommutative_replacement hodd (hS.to_subgroup B) hclass hBA' hb hAN hNA hbN,
      (card_replacement hB hb hBA' hAN hNA hbN).trans hA.2⟩,
    fun h ↦ hbN' (replacement_le hAN hbN (h hb)), SetLike.lt_iff_le_and_exists.2 ⟨?_, b, ?_, ?_⟩⟩
  · exact le_inf inf_le_left
      (le_sup_right.trans (le_normalizer_replacement hB hb hBA' hAN hNA hbN))
  · exact ⟨hb, mem_normalizer_replacement hB hb hBA'⟩
  · exact fun h ↦ hbN' (mem_sup_right h)

end GlaubermanReplacement

end CFSG
