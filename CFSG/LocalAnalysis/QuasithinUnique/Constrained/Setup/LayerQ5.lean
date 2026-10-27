module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ3

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open TensorProduct Module

universe u

theorem no_transitive_perfect_orbit_k {k : Type*} [Field k] [CharP k 2] {W : Type u}
    [AddCommGroup W] [Module k W] [Finite W] [Nontrivial W] {s : ℕ} (hs : 2 ≤ s)
    (L : Fin s → Subgroup (W ≃ₗ[k] W))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hperf : ∀ i, Group.IsPerfect ↥(L i)) (hnt : ∀ i, Nontrivial ↥(L i))
    (hirr : IsIrrAct (⨆ i, L i))
    (A : Subgroup (W ≃ₗ[k] W)) [CFSG.IsElementaryAbelian 2 A]
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card (fixGL A))
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, conjSub a (L i) = L j)
    (htrans : ∀ i j, ∃ a ∈ A, conjSub a (L i) = L j) : False := by
  classical
  obtain ⟨F, hF, hFfin, hAlg, hMod, hTower, hcommut, hfinW, hspanF, habs, hsemi⟩ :=
    finite_irreducible_endomorphism_field_density.{u, 0, _} (⨆ i, L i) hirr
  have hFchar : CharP F 2 := charP_of_injective_algebraMap (algebraMap k F).injective 2
  have hlin : ∀ h ∈ (⨆ i, L i), ∀ (c : F) (w : W), h (c • w) = c • h w := by
    intro h hh c w
    let m : Module.End k W :=
      { toFun := fun w => c • w
        map_add' := fun x y => smul_add c x y
        map_smul' := fun a x => smul_comm c a x }
    have := (hcommut m).2 ⟨c, fun w => rfl⟩ h hh w
    exact this.symm
  have hnormA : ∀ a ∈ A, a ∈ Subgroup.normalizer ((⨆ i, L i : Subgroup (W ≃ₗ[k] W)) : Set _) := by
    have hle : ∀ a ∈ A, conjSub a (⨆ i, L i) ≤ ⨆ i, L i := by
      intro a ha
      rw [OrderIso.map_iSup]
      refine iSup_le fun i => ?_
      obtain ⟨j, hj⟩ := hperm a ha i
      rw [hj]
      exact le_iSup L j
    intro a ha
    exact mem_normalizer_of_conjSub_le (hle a ha) (hle a⁻¹ (A.inv_mem ha))
  have hsemiA : ∀ a ∈ A, ∃ σ : F ≃ₐ[k] F, ∀ (c : F) (w : W), a (c • w) = σ c • a w :=
    fun a ha => hsemi a (hnormA a ha)
  have hLle : ∀ i, L i ≤ (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)).range := fun i x hx =>
    mem_range_resK (hlin x (le_iSup L i hx))
  let LF : Fin s → Subgroup (W ≃ₗ[F] W) := fun i =>
    (L i).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
  have hLF : ∀ i, (LF i).map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = L i := fun i => by
    show ((L i).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))).map _ = L i
    rw [Subgroup.map_comap_eq, inf_eq_right.2 (hLle i)]
  have hLFperf : ∀ i, Group.IsPerfect ↥(LF i) := fun i =>
    isPerfect_of_map_eq _ resK_injective (LF i) (hLF i) (hperf i)
  have hLFnt : ∀ i, Nontrivial ↥(LF i) := fun i =>
    have := hnt i
    nontrivial_of_map_eq _ resK_injective (LF i) (hLF i) this
  let i0 : Fin s := ⟨0, by omega⟩
  let permHom : (W ≃ₗ[k] W) →* Equiv.Perm W :=
    { toFun := fun a => a.toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hpermHom : Function.Injective permHom := fun a b h =>
    LinearEquiv.ext fun w => congrArg (fun p : Equiv.Perm W => p w) h
  let Aperm : Subgroup (Equiv.Perm W) := A.map permHom
  have hApermEl : CFSG.IsElementaryAbelian 2 ↥Aperm := isElementaryAbelian_map permHom A
  have hAlin : ∀ a ∈ A, ∀ (c : F) (w : W), a (c • w) = c • a w := by
    have hoffP : Nat.card W ≤ Nat.card ↥Aperm * Nat.card {w : W // ∀ a ∈ Aperm, a w = w} := by
      have h1 : Nat.card ↥Aperm = Nat.card ↥A := Subgroup.card_map_of_injective hpermHom
      have h2 : Nat.card {w : W // ∀ a ∈ Aperm, a w = w} = Nat.card ↥(fixGL A) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun w => by
          constructor
          · intro h a ha
            exact h (permHom a) ⟨a, ha, rfl⟩
          · rintro h _ ⟨a, ha, rfl⟩
            exact h a ha)
      rw [h1, h2]
      exact hoff
    have key := no_field_action_of_perfect (F := F) (W := W) Aperm
      (by rintro _ ⟨a, ha, rfl⟩ x y; exact map_add a x y)
      (by
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨σ, hσ⟩ := hsemiA a ha
        exact ⟨σ.toRingEquiv, fun c w => hσ c w⟩)
      (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w; exact hquad a ha b hb w)
      hoffP (LF i0) (((Subgroup.nontrivial_iff_ne_bot _).1 (hLFnt i0))) (hLFperf i0)
    intro a ha c w
    have := (key (permHom a) ⟨a, ha, rfl⟩).2 c w
    exact this
  have hAle : A ≤ (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)).range := fun x hx =>
    mem_range_resK (hAlin x hx)
  let AF : Subgroup (W ≃ₗ[F] W) := A.comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
  have hAF : AF.map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = A := by
    show (A.comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))).map _ = A
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hAle]
  have hAFel : CFSG.IsElementaryAbelian 2 ↥AF :=
    isElementaryAbelian_comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) resK_injective A
  have hcommF : ∀ i j, i ≠ j → ∀ x ∈ LF i, ∀ y ∈ LF j, x * y = y * x := by
    intro i j hij x hx y hy
    apply resK_injective (F := F) (k := k) (W := W)
    rw [map_mul, map_mul]
    exact hcomm i j hij _ hx _ hy
  have hHF : (⨆ i, LF i).map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = ⨆ i, L i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hLF
  have hirrF : IsIrrAct (⨆ i, LF i) := by
    intro U hU
    have hUk : ∀ h ∈ (⨆ i, L i), ∀ u ∈ U.restrictScalars k, h u ∈ U.restrictScalars k := by
      intro h hh u hu
      rw [← hHF] at hh
      obtain ⟨y, hy, rfl⟩ := hh
      exact hU y hy u hu
    rcases hirr (U.restrictScalars k) hUk with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff k F W).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff k F W).1 h
  have hendF : ∀ f : Module.End F W, (∀ h ∈ ⨆ i, LF i, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w := by
    intro f hf
    have hfk : ∀ h ∈ (⨆ i, L i), ∀ w, (f.restrictScalars k) (h w) = h ((f.restrictScalars k) w) := by
      intro h hh w
      rw [← hHF] at hh
      obtain ⟨y, hy, rfl⟩ := hh
      exact hf y hy w
    exact (hcommut (f.restrictScalars k)).1 hfk
  have hquadF : ∀ a ∈ AF, ∀ b ∈ AF, ∀ w, b (a w - w) = a w - w := fun a ha b hb w =>
    hquad (resK k a) ha (resK k b) hb w
  have hoffF : Nat.card W ≤ Nat.card ↥AF * Nat.card ↥(fixGL AF) := by
    have h1 : Nat.card ↥AF = Nat.card ↥A := by
      rw [← hAF]
      exact (Subgroup.card_map_of_injective resK_injective).symm
    have h2 : Nat.card ↥(fixGL AF) = Nat.card ↥(fixGL A) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => by
        constructor
        · intro h a ha
          obtain ⟨af, rfl⟩ := hAle ha
          exact h af ha
        · intro h af haf
          exact h (resK k af) haf)
    rw [h1, h2]
    exact hoff
  have hconjF : ∀ a ∈ AF, ∀ i j, conjSub (resK k a) (L i) = L j → conjSub a (LF i) = LF j := by
    intro a ha i j h
    show conjSub a ((L i).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))) =
      (L j).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
    rw [conjSub_comap, h]
  have hpermF : ∀ a ∈ AF, ∀ i, ∃ j, conjSub a (LF i) = LF j := fun a ha i =>
    (hperm (resK k a) ha i).imp fun j hj => hconjF a ha i j hj
  have htransF : ∀ i j, ∃ a ∈ AF, conjSub a (LF i) = LF j := by
    intro i j
    obtain ⟨a, ha, h⟩ := htrans i j
    obtain ⟨af, rfl⟩ := hAle ha
    exact ⟨af, ha, hconjF af ha i j h⟩
  exact no_transitive_perfect_orbit hs LF hcommF hLFperf hLFnt hirrF hendF AF hquadF hoffF hpermF
    htransF

end CFSG.QuasithinUnique.Setup.Layer
