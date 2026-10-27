module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterSym

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.GorensteinWalter Projectivization

section Structure

theorem transposition_structure {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (h5 : Fintype.card Ω = 5)
    (B : Subgroup (Equiv.Perm Ω)) [CFSG.IsElementaryAbelian 2 B] {r : ℕ} (hr : Nat.card B = 2 ^ r)
    (hB : B ≠ ⊥)
    (h : Module.finrank (ZMod 2) (evenWeight Ω) ≤
      Module.finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) + r) :
    ((∃ x y, x ≠ y ∧ B = Subgroup.closure {Equiv.swap x y}) ∨
      (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
        B = Subgroup.closure {Equiv.swap x y, Equiv.swap z t})) ∧
    Module.finrank (ZMod 2) (evenWeight Ω) =
      Module.finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) + r := by
  classical
  obtain ⟨s, hs2, hsdisj, hscard, hBgen, -, hfin⟩ :=
    even_weight_action_inequality_transpositions (by rw [h5]; decide) B hr h
  refine ⟨?_, hfin⟩
  have hr1 : 1 ≤ r := by
    by_contra h0
    have : r = 0 := by omega
    apply hB
    rw [← Subgroup.card_eq_one, hr, this]
    rfl
  have hr2 : r ≤ 2 := by
    have hbU : (s.biUnion id).card = ∑ Δ ∈ s, Δ.card :=
      Finset.card_biUnion (fun x hx y hy hxy => hsdisj hx hy hxy)
    have h2 : ∑ Δ ∈ s, Δ.card = 2 * s.card := by
      rw [Finset.sum_congr rfl hs2, Finset.sum_const, smul_eq_mul, mul_comm]
    have hle : (s.biUnion id).card ≤ Fintype.card Ω := Finset.card_le_univ _
    omega
  have hcases : r = 1 ∨ r = 2 := by omega
  rcases hcases with rfl | rfl
  · obtain ⟨Δ, rfl⟩ := Finset.card_eq_one.mp hscard
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hs2 Δ (Finset.mem_singleton_self _))
    left
    refine ⟨x, y, hxy, ?_⟩
    rw [hBgen]
    congr 1
    ext σ
    simp only [Finset.mem_singleton, exists_eq_left, Finset.mem_insert, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, ha, b, hb, hab, rfl⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · rfl
      · exact Equiv.swap_comm _ _
      · exact absurd rfl hab
    · rintro rfl
      exact ⟨x, Or.inl rfl, y, Or.inr rfl, hxy, rfl⟩
  · obtain ⟨Δ₁, Δ₂, hne, rfl⟩ := Finset.card_eq_two.mp hscard
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hs2 Δ₁ (by simp))
    obtain ⟨z, t, hzt, rfl⟩ := Finset.card_eq_two.mp (hs2 Δ₂ (by simp))
    have hd : Disjoint ({x, y} : Finset Ω) {z, t} :=
      hsdisj (by simp) (by simp) hne
    rw [Finset.disjoint_left] at hd
    have hx : x ∈ ({x, y} : Finset Ω) := Finset.mem_insert_self x {y}
    have hy : y ∈ ({x, y} : Finset Ω) := Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    have hxz : x ≠ z := fun h => hd hx (by simp [h])
    have hxt : x ≠ t := fun h => hd hx (by simp [h])
    have hyz : y ≠ z := fun h => hd hy (by simp [h])
    have hyt : y ≠ t := fun h => hd hy (by simp [h])
    right
    refine ⟨x, y, z, t, hxy, hxz, hxt, hyz, hyt, hzt, ?_⟩
    rw [hBgen]
    congr 1
    ext σ
    simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨Δ, hΔ | hΔ, a, ha, b, hb, hab, rfl⟩
      · subst hΔ
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        left
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · rfl
        · exact Equiv.swap_comm _ _
        · exact absurd rfl hab
      · subst hΔ
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        right
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · rfl
        · exact Equiv.swap_comm _ _
        · exact absurd rfl hab
    · rintro (rfl | rfl)
      · exact ⟨{x, y}, Or.inl rfl, x, by simp, y, by simp, hxy, rfl⟩
      · exact ⟨{z, t}, Or.inr rfl, z, by simp, t, by simp, hzt, rfl⟩

end Structure

section Offender

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

theorem offender_transpositions (h5 : Fintype.card Ω = 5) (hW16 : Nat.card W = 16)
    (β : W ≃ₗ[ZMod 2] ↥(evenWeight Ω)) (G : Subgroup (Module.End (ZMod 2) W)ˣ)
    (ψ : ↥G →* Equiv.Perm Ω) (hψinj : Function.Injective ψ)
    (hψeq : ∀ (y : ↥G) (w : W), ((β (y.1.val w) : ↥(evenWeight Ω)) : Ω → ZMod 2) =
      permAct (ψ y) (β w : Ω → ZMod 2))
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) (hAG : A ≤ G) [CFSG.IsElementaryAbelian 2 A]
    (hA1 : A ≠ ⊥)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w}) :
    ((∃ x y, x ≠ y ∧ (A.subgroupOf G).map ψ = Subgroup.closure {Equiv.swap x y}) ∨
      (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
        (A.subgroupOf G).map ψ = Subgroup.closure {Equiv.swap x y, Equiv.swap z t})) ∧
    Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w} = Nat.card W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥A := by
    have := finite_units_end (k₀ := ZMod 2) (W := W)
    infer_instance
  have hAea : CFSG.IsElementaryAbelian 2 (A.subgroupOf G) :=
    CFSG.IsElementaryAbelian.subgroupOf hAG
  set B := (A.subgroupOf G).map ψ with hB
  have hBea : CFSG.IsElementaryAbelian 2 B := CFSG.IsElementaryAbelian.map ψ
  have hBcard : Nat.card B = Nat.card A :=
    ((Nat.card_congr ((A.subgroupOf G).equivMapOfInjective ψ hψinj).toEquiv).symm).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv)
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).mp (CFSG.IsElementaryAbelian.isPGroup 2 A)
  have hBr : Nat.card B = 2 ^ r := hBcard.trans hr
  have hBne : B ≠ ⊥ := by
    intro h
    apply hA1
    rw [← Subgroup.card_eq_one, ← hBcard, h]
    exact Subgroup.card_bot
  have hCeq : Nat.card {w : W // ∀ a ∈ A, a.val w = w} =
      Nat.card ↥(evenWeight Ω ⊓ fixedVectors B) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(β w.1 : Ω → ZMod 2), (β w.1).2, ?_⟩
        invFun := fun x => ⟨β.symm ⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun w => Subtype.ext (β.symm_apply_apply w.1)
        right_inv := fun x => Subtype.ext (by
          show ((β (β.symm ⟨x.1, x.2.1⟩) : ↥(evenWeight Ω)) : Ω → ZMod 2) = x.1
          rw [β.apply_symm_apply]) }
    · intro σ hσ
      obtain ⟨y, hy, rfl⟩ := hσ
      have hy' : y.1 ∈ A := Subgroup.mem_subgroupOf.mp hy
      rw [← hψeq y w.1, w.2 y.1 hy']
    · intro a ha
      have hβw : β (β.symm ⟨x.1, x.2.1⟩) = ⟨x.1, x.2.1⟩ := β.apply_symm_apply _
      apply β.injective
      apply Subtype.ext
      have h1 := hψeq ⟨a, hAG ha⟩ (β.symm ⟨x.1, x.2.1⟩)
      rw [hβw] at h1
      have h2 := x.2.2 (ψ ⟨a, hAG ha⟩) ⟨⟨a, hAG ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      show ((β (a.val (β.symm ⟨x.1, x.2.1⟩)) : ↥(evenWeight Ω)) : Ω → ZMod 2) = _
      rw [h1, hβw]
      exact h2
  have hE4 : Module.finrank (ZMod 2) (evenWeight Ω) = 4 := by
    have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
    rw [finrank_evenWeight, h5]
  have hCcard : Nat.card ↥(evenWeight Ω ⊓ fixedVectors B) =
      2 ^ Module.finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) := by
    let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
    have hfin : Module.Finite (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(evenWeight Ω ⊓ fixedVectors B))
    rw [Nat.card_zmod] at h
    exact h
  have hc : 4 ≤ r + Module.finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) := by
    have h := hoff
    rw [hW16, hr, hCeq, hCcard] at h
    exact le_of_two_pow_le_mul (a := 4) (by simpa using h)
  obtain ⟨hstruct, hfin⟩ := transposition_structure h5 B hBr hBne (by rw [hE4]; omega)
  refine ⟨hstruct, ?_⟩
  rw [hW16, hr, hCeq, hCcard, ← pow_add]
  have h4 : r + Module.finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) = 4 := by omega
  rw [h4]
  norm_num

end Offender

section Main

theorem binary_SL2_outer_quadratic_offender_deleted_module {n : ℕ} (hn : 2 ≤ n) {F : Type*}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))]
    [DecidableEq (ℙ F (Fin 2 → F))] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) (L : Subgroup (Module.End (ZMod 2) W)ˣ) (hL : ρ.toHomUnits.range = L)
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (L : Set (Module.End (ZMod 2) W)ˣ))
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w})
    (hAL : ¬ A ≤ L) :
    n = 2 ∧ Nat.card (EndRing ρ) = 2 ∧ Module.finrank (ZMod 2) W = 4 ∧
      Fintype.card (ℙ F (Fin 2 → F)) = 5 ∧
      ∃ (ψ : ↥(L ⊔ A) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
        (β : W ≃ₗ[ZMod 2] ↥(evenWeight (ℙ F (Fin 2 → F)))),
        (∀ (g : SL(2, F)) (h : ρ.toHomUnits g ∈ L ⊔ A),
          ψ ⟨ρ.toHomUnits g, h⟩ = MulAction.toPerm g) ∧
        (∀ (y : ↥(L ⊔ A)) (w : W),
          ((β ((y : (Module.End (ZMod 2) W)ˣ).val w) : ↥(evenWeight (ℙ F (Fin 2 → F)))) :
              ℙ F (Fin 2 → F) → ZMod 2) =
            permAct (ψ y) (β w : ℙ F (Fin 2 → F) → ZMod 2)) ∧
        ((L.subgroupOf (L ⊔ A)).map ψ.toMonoidHom = alternatingGroup (ℙ F (Fin 2 → F))) ∧
        ((∃ x y, x ≠ y ∧ (A.subgroupOf (L ⊔ A)).map ψ.toMonoidHom =
            Subgroup.closure {Equiv.swap x y}) ∨
          (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
            (A.subgroupOf (L ⊔ A)).map ψ.toMonoidHom =
              Subgroup.closure {Equiv.swap x y, Equiv.swap z t})) ∧
        Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w} = Nat.card W := by
  subst hL
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn2, hD2, hW16, φ, hφ⟩ := outer_core hn hF ρ hρ hirr A hA1 hAN hquad hoff hAL
  have hk : Fintype.card F = 4 := by rw [hF, hn2]; norm_num
  have hΩ : Fintype.card (ℙ F (Fin 2 → F)) = 5 := by rw [card_projectiveLine, hk]
  have hfinrank : Module.finrank (ZMod 2) W = 4 := by
    have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod, hW16] at h
    have h' : 2 ^ Module.finrank (ZMod 2) W = 2 ^ 4 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  refine ⟨hn2, hD2, hfinrank, hΩ, ?_⟩
  set ρU := ρ.toHomUnits with hρU_def
  have hρU_val : ∀ g, (ρU g).val = ρ g := fun g => by rw [hρU_def]; rfl
  let β : W ≃ₗ[ZMod 2] ↥(evenWeight (ℙ F (Fin 2 → F))) :=
    φ.toLinearEquiv (fun c w => by
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simp)
  have hβ : ∀ (g : SL(2, F)) (w : W),
      ((β ((ρU g).val w) : ↥(evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
        permAct (MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F)) g)
          (β w : ℙ F (Fin 2 → F) → ZMod 2) := by
    intro g w
    rw [hρU_val]
    exact hφ g w
  obtain ⟨βalt, hβalt⟩ := four_field_projective_alt hk
  have hπ : (MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F))).range =
      alternatingGroup (ℙ F (Fin 2 → F)) := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      have h : (βalt g : Equiv.Perm (ℙ F (Fin 2 → F))) =
          MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F)) g :=
        Equiv.ext (fun L => hβalt g L)
      rw [← h]
      exact (βalt g).2
    · intro hσ
      obtain ⟨g, hg⟩ := βalt.surjective ⟨σ, hσ⟩
      refine ⟨g, ?_⟩
      have h : (βalt g : Equiv.Perm (ℙ F (Fin 2 → F))) = σ := congrArg Subtype.val hg
      rw [← h]
      exact (Equiv.ext fun L => (hβalt g L).symm)
  set G := ρU.range ⊔ A with hG
  have hLG : ρU.range ≤ G := le_sup_left
  have hAG : A ≤ G := le_sup_right
  have hGN : ∀ y ∈ G, y ∈ Subgroup.normalizer (ρU.range : Set (Module.End (ZMod 2) W)ˣ) :=
    fun y hy => (sup_le Subgroup.le_normalizer hAN) hy
  obtain ⟨ψ, hψinj, hψeq, hψL, hψsurj⟩ :=
    exists_sym_extension hΩ β (MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F))) hπ ρU hβ G hLG hGN
  obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hAL
  have hsurj : Function.Surjective ψ := hψsurj ⟨a, hAG haA, haL⟩
  let ψe : ↥G ≃* Equiv.Perm (ℙ F (Fin 2 → F)) := MulEquiv.ofBijective ψ ⟨hψinj, hsurj⟩
  have hψe : ψe.toMonoidHom = ψ := rfl
  obtain ⟨hstruct, hcard⟩ := offender_transpositions hΩ hW16 β G ψ hψinj hψeq A hAG hA1 hoff
  refine ⟨ψe, β, fun g h => hψL g h, fun y w => hψeq y w, ?_, ?_, hcard⟩
  · rw [hψe]
    ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hy
      have h1 : ψ y = MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F)) g := by
        rw [← hψL g (hg ▸ y.2)]
        congr 1
        exact Subtype.ext hg.symm
      rw [h1, ← hπ]
      exact ⟨g, rfl⟩
    · intro hσ
      rw [← hπ] at hσ
      obtain ⟨g, rfl⟩ := hσ
      exact ⟨⟨ρU g, hLG ⟨g, rfl⟩⟩, Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩, hψL g _⟩
  · rw [hψe]
    exact hstruct

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules
