module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RRk
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ElemCover (n : ℕ) (X : Subgroup G) : Prop :=
  ∀ y ∈ X, y ^ 2 = 1 →
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 2 E ∧ n ≤ Nat.card E ∧ y ∈ E

theorem RankFacts.elemCover {X : Subgroup G} (h : RankFacts X) : ElemCover 8 X := by
  intro y hy hy2
  obtain ⟨E, hEX, hE, hcard, hyE⟩ := h.cover y hy hy2
  exact ⟨E, hEX, hE, hcard.ge, hyE⟩

private lemma isElemAbelian_map_iff' {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] {f : Γ₁ →* Γ₂}
    (hf : Function.Injective f) (p : ℕ) (E : Subgroup Γ₁) :
    IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  constructor
  · intro h
    haveI : IsMulCommutative (E.map f) := h.1
    refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
    · intro a ha b hb
      apply hf
      rw [map_mul, map_mul]
      exact setLike_mul_comm (s := E.map f) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    · intro x hx
      apply hf
      simpa using h.2 (f x) (show f x ∈ E.map f from ⟨x, hx, rfl⟩)
  · intro h
    haveI : IsMulCommutative E := h.1
    refine ⟨inferInstance, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa using congrArg f (h.2 x hx)

private lemma transport_rank' {X Y : Subgroup G} (e : ↥X ≃* ↥Y) {E : Subgroup G} (hE : E ≤ X) :
    ∃ E' : Subgroup G, E' ≤ Y ∧ Nat.card E' = Nat.card E ∧
      (IsElemAbelian 2 E' ↔ IsElemAbelian 2 E) ∧
      (∀ x (hx : x ∈ X), x ∈ E → ((e ⟨x, hx⟩ : ↥Y) : G) ∈ E') ∧
      (∀ y ∈ E', ∃ (x : G) (hx : x ∈ X), x ∈ E ∧ ((e ⟨x, hx⟩ : ↥Y) : G) = y) := by
  refine ⟨((E.subgroupOf X).map e.toMonoidHom).map Y.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, -, hzy⟩ := Subgroup.mem_map.1 hy
    rw [← hzy]
    exact z.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y),
      Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  · calc IsElemAbelian 2 (((E.subgroupOf X).map e.toMonoidHom).map Y.subtype)
        ↔ IsElemAbelian 2 ((E.subgroupOf X).map (Y.subtype.comp e.toMonoidHom)) := by
          rw [Subgroup.map_map]
      _ ↔ IsElemAbelian 2 (E.subgroupOf X) :=
          isElemAbelian_map_iff'
            (fun a b h => e.injective (Subgroup.subtype_injective Y h)) 2 _
      _ ↔ IsElemAbelian 2 E :=
          (isElemAbelian_map_iff' (Subgroup.subtype_injective X) 2 (E.subgroupOf X)).symm.trans
            (by rw [Subgroup.map_subgroupOf_eq_of_le hE])
  · intro x hx hxE
    exact Subgroup.mem_map.2
      ⟨e ⟨x, hx⟩, Subgroup.mem_map.2 ⟨⟨x, hx⟩, hxE, rfl⟩, rfl⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
    refine ⟨(w : G), w.2, hw, ?_⟩
    rw [← hzy, ← hwz]
    rfl

theorem ElemCover.of_mulEquiv {X Y : Subgroup G} {n : ℕ} (e : ↥X ≃* ↥Y) (h : ElemCover n X) :
    ElemCover n Y := by
  intro y hy hy2
  let x : ↥X := e.symm ⟨y, hy⟩
  have hx2 : (x : G) ^ 2 = 1 := by
    have hx2' : x ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      change (e (e.symm ⟨y, hy⟩)) ^ 2 = 1
      rw [e.apply_symm_apply]
      exact Subtype.ext hy2
    have := congrArg (fun z : ↥X => (z : G)) hx2'
    simpa using this
  obtain ⟨E₀, hE₀X, hE₀, hnE₀, hxmem⟩ := h (x : G) x.2 hx2
  obtain ⟨E', hE'Y, hcard', hiff', hfwd, -⟩ := transport_rank' e hE₀X
  refine ⟨E', hE'Y, hiff'.mpr hE₀, ?_, ?_⟩
  · rwa [hcard']
  · have hcoe : ((e ⟨(x : G), x.2⟩ : ↥Y) : G) = y := by
      have hx' : (⟨(x : G), x.2⟩ : ↥X) = x := rfl
      rw [hx']
      exact congrArg (fun z : ↥Y => (z : G)) (e.apply_symm_apply (⟨y, hy⟩ : ↥Y))
    have hmem := hfwd (x : G) x.2 hxmem
    rwa [hcoe] at hmem

theorem ElemCover.conj {X : Subgroup G} {n : ℕ} (c : G) (h : ElemCover n X) :
    ElemCover n (conjSub c X) :=
  ElemCover.of_mulEquiv
    (Subgroup.equivMapOfInjective X (MulAut.conj c).toMonoidHom (MulAut.conj c).injective) h

theorem ElemCover.prod {P X Y : Subgroup G} {n m : ℕ} (h : IsInternalDirect P X Y)
    (hX : ElemCover n X) (hY : ElemCover m Y) : ElemCover (n * m) P := by
  obtain ⟨hsup, hinf, hcomm⟩ := h
  intro x hxP hx2
  have hcent : X ≤ Subgroup.centralizer (Y : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  have hLE : X ≤ Subgroup.normalizer (Y : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(X ⊔ Y) : Set G) = (X : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X Y hLE
  rw [← hsup] at hxP
  change x ∈ (↑(X ⊔ Y) : Set G) at hxP
  rw [hcoe, Set.mem_mul] at hxP
  obtain ⟨a, ha, b, hb, hab⟩ := hxP
  have hsq : (a * b) ^ 2 = 1 := by
    rw [← hab] at hx2
    exact hx2
  have hcab : Commute a b := hcomm a ha b hb
  have hsq2 : a ^ 2 * b ^ 2 = 1 := by
    rw [← hcab.mul_pow 2]
    exact hsq
  have ha2 : a ^ 2 = 1 := by
    have hmem : a ^ 2 ∈ X ⊓ Y := by
      refine ⟨?_, ?_⟩
      · simpa [pow_two] using X.mul_mem ha ha
      · have h1 : a ^ 2 = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq2
        rw [h1]
        exact Y.inv_mem (by simpa [pow_two] using Y.mul_mem hb hb)
    rwa [hinf, Subgroup.mem_bot] at hmem
  have hb2 : b ^ 2 = 1 := by simpa [ha2] using hsq2
  obtain ⟨E1, hE1X, hE1, hnE1, haE1⟩ := hX a ha ha2
  obtain ⟨E2, hE2Y, hE2, hmE2, hbE2⟩ := hY b hb hb2
  refine ⟨E1 ⊔ E2, ?_, ?_, ?_, ?_⟩
  · rw [← hsup]
    exact sup_le (hE1X.trans le_sup_left) (hE2Y.trans le_sup_right)
  · exact IsElemAbelian.sup_of_commute hE1 hE2
      (fun u hu v hv => hcomm u (hE1X hu) v (hE2Y hv))
  · have hcentE : E2 ≤ Subgroup.centralizer (E1 : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hcomm w (hE1X hw) z (hE2Y hz)
    have hnormalE : E2 ≤ Subgroup.normalizer (E1 : Set G) :=
      hcentE.trans (Subgroup.centralizer_le_normalizer _)
    have hdisjE : Disjoint E1 E2 := by
      rw [disjoint_iff]
      exact le_bot_iff.mp ((inf_le_inf hE1X hE2Y).trans hinf.le)
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E1 E2 hnormalE hdisjE]
    exact Nat.mul_le_mul hnE1 hmE2
  · rw [← hab]
    exact Subgroup.mul_mem_sup haE1 hbE2

end CFSG.OddStandard.HigherRank.YamadaG23
