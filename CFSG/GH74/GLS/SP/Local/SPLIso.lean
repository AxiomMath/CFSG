module

public import CFSG.GH74.GLS.SP.Local.SPLCoordStage
public import CFSG.GH74.GLS.SP.Local.SPLCoord
public import CFSG.GH74.GLS.SP.Local.SPLModelCoord

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

theorem SPLCoord.comp_ringEquiv {F F' : Type*} [Field F] [Field F'] {P : Type*} [Group P]
    {x₁ x₂ x₃ x₄ : F → P} (h : SPLCoord x₁ x₂ x₃ x₄) (e : F' ≃+* F) :
    SPLCoord (x₁ ∘ e) (x₂ ∘ e) (x₃ ∘ e) (x₄ ∘ e) where
  add₁ s s' := by simp only [Function.comp]; rw [map_add]; exact h.add₁ _ _
  add₂ s s' := by simp only [Function.comp]; rw [map_add]; exact h.add₂ _ _
  add₃ s s' := by simp only [Function.comp]; rw [map_add]; exact h.add₃ _ _
  add₄ s s' := by simp only [Function.comp]; rw [map_add]; exact h.add₄ _ _
  surj g := by
    obtain ⟨s, c, a, b, hg⟩ := h.surj g
    exact ⟨e.symm s, e.symm c, e.symm a, e.symm b, by simpa using hg⟩
  inj s c a b s' c' a' b' he := by
    have := h.inj _ _ _ _ _ _ _ _ he
    exact ⟨e.injective this.1, e.injective this.2.1, e.injective this.2.2.1,
      e.injective this.2.2.2⟩
  cen₂ c g := h.cen₂ _ g
  c13 s a := h.c13 _ _
  c34 a b := by simp only [Function.comp, map_mul]; exact h.c34 _ _
  c14 s b := by
    simp only [Function.comp, map_div₀, map_mul, map_pow, map_ofNat]
    exact h.c14 _ _

theorem splLeafIso_of_nat (hNM : NatModStmt) : SPLLeafIso := by
  intro G _ _ hG D hst h42 hch Fq _ _ hF hq
  classical
  have hs := hst.setup
  have h1 := hst.set
  have h3 := hst.m2
  have hR := hst.m1.toR₁
  obtain ⟨F, hFfield, hFfin, hFq, x₁, x₂, x₃, x₄, hx, r1, r2, r3, r4⟩ :=
    coords_of_stage hNM D.toSPLNot3 hs h1 h3 hR
  have hodd : Odd (Nat.card Fq) := hq ▸ hs.odd_q
  obtain ⟨y₁, y₂, y₃, y₄, hy, s1, s2, s3, s4⟩ := model_coords Fq hF hodd
  have : Fintype F := Fintype.ofFinite F
  have : Fintype Fq := Fintype.ofFinite Fq
  have hcard : Fintype.card F = Fintype.card Fq := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFq, hq]
  let e : F ≃+* Fq := FiniteField.ringEquivOfCardEq hcard
  have hy' := hy.comp_ringEquiv e
  obtain ⟨φ, hφ⟩ := SPLCoord.exists_mulEquiv hx hy'
  refine ⟨φ, ?_⟩
  intro i hi1 hi4 g
  have key : ∀ (Y : Subgroup G) (Z : Subgroup (StatedProj (StatedSp 2 Fq)))
      (xa : F → ↥D.P) (ya : Fq → ↥(SP.modelSystem Fq hF).U),
      (∀ s, φ (xa s) = ya (e s)) →
      (∀ g : ↥D.P, (g : G) ∈ Y ↔ ∃ s, xa s = g) →
      (∀ g : ↥(SP.modelSystem Fq hF).U, (g : StatedProj (StatedSp 2 Fq)) ∈ Z ↔ ∃ s, ya s = g) →
      ((g : G) ∈ Y ↔ ((φ g : ↥(SP.modelSystem Fq hF).U) : StatedProj (StatedSp 2 Fq)) ∈ Z) := by
    intro Y Z xa ya hxy hX hY
    rw [hX g, hY (φ g)]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨e s, (hxy s).symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨e.symm t, φ.injective ?_⟩
      rw [hxy, ht.symm]
      simp
  have hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · rw [root_p1]
    exact key _ _ _ _ (fun s => (hφ s).2.2.2) r4 s4
  · rw [root_p2]
    exact key _ _ _ _ (fun s => (hφ s).2.1) r2 s2
  · rw [root_p3]
    exact key _ _ _ _ (fun s => (hφ s).2.2.1) r3 s3
  · rw [root_p4]
    exact key _ _ _ _ (fun s => (hφ s).1) r1 s1

end CFSG.GH74.GLS.SP.Local
