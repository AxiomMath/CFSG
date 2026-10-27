module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace

public section

namespace CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

variable {G : Type} [Group G] {q : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

theorem commSpace_invariant (ρ : Representation (ZMod q) G V) (Z : Subgroup G) {k : G}
    (hk : ∀ z ∈ Z, k * z = z * k) {u : V} (hu : u ∈ commSpace ρ Z) :
    ρ k u ∈ commSpace ρ Z := by
  unfold commSpace at hu ⊢
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    apply Submodule.subset_span
    refine ⟨x, hx, ρ k v, ?_⟩
    rw [map_sub, ← rho_mul_apply, hk x hx, rho_mul_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] noncomputable def restrictedRepresentation (ρ : Representation (ZMod q) G V) (K Z : Subgroup G)
    (hcentral : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) :
    Representation (ZMod q) K (commSpace ρ Z) where
  toFun k := (ρ (k : G)).restrict (p := commSpace ρ Z) (q := commSpace ρ Z)
    (fun _ hu => commSpace_invariant ρ Z (hcentral k k.2) hu)
  map_one' := by
    ext u; simp
  map_mul' a b := by
    ext u; simp [rho_mul_apply]

section General

variable (ρ : Representation (ZMod q) G V) (K Z : Subgroup G)
  (hcentral : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)

@[simp] theorem restrictedRepresentation_apply_coe (k : K) (u : commSpace ρ Z) :
    ((restrictedRepresentation ρ K Z hcentral k u : commSpace ρ Z) : V) = ρ (k : G) (u : V) := rfl

theorem fixedSpace_restrictedRepresentation (D : Subgroup G) (_hD : D ≤ K) :
    fixedSpace (restrictedRepresentation ρ K Z hcentral) (D.subgroupOf K) =
      Submodule.comap (commSpace ρ Z).subtype (commSpace ρ Z ⊓ fixedSpace ρ D) := by
  ext u
  rw [Submodule.mem_comap, Submodule.mem_inf, mem_fixedSpace_iff, mem_fixedSpace_iff]
  simp only [Submodule.subtype_apply, SetLike.coe_mem, true_and, Subgroup.mem_subgroupOf]
  constructor
  · intro h d hd
    exact congrArg Subtype.val (h ⟨d, _hD hd⟩ hd)
  · intro h d hd
    exact Subtype.ext (h d.1 hd)

end General

section Odd

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
  (K Z : Subgroup G) (hcentral : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)

theorem commSpace_restrictedRepresentation_subgroupOf [Finite Z] (hodd : Odd (Nat.card Z))
    (hZK : Z ≤ K) :
    commSpace (restrictedRepresentation ρ K Z hcentral) (Z.subgroupOf K) = ⊤ := by
  haveI : Fintype Z := Fintype.ofFinite Z
  have hcard : ((Fintype.card Z : ℕ) : ZMod 2) = 1 := by
    rw [← Nat.card_eq_fintype_card] at *
    exact (ZMod.natCast_eq_one_iff_odd).2 hodd
  rw [eq_top_iff]
  intro u _
  have hN := normOp_commSpace ρ Z u.2
  have key : u = -(∑ b : Z, (restrictedRepresentation ρ K Z hcentral ⟨b, hZK b.2⟩ u - u)) := by
    apply Subtype.ext
    simp only [Submodule.coe_neg, Submodule.coe_sum, Submodule.coe_sub,
      restrictedRepresentation_apply_coe, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ]
    rw [← normOp_apply, hN, ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard]
    simp
  rw [key]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun b _ => ?_)
  exact Submodule.subset_span ⟨⟨b, hZK b.2⟩, Subgroup.mem_subgroupOf.2 b.2, u, rfl⟩

theorem commSpace_restrictedRepresentation_top [Finite Z] (hodd : Odd (Nat.card Z))
    (hZK : Z ≤ K) :
    commSpace (restrictedRepresentation ρ K Z hcentral) ⊤ = ⊤ := by
  rw [eq_top_iff, ← commSpace_restrictedRepresentation_subgroupOf ρ K Z hcentral hodd hZK]
  unfold commSpace
  exact Submodule.span_mono fun w ⟨x, _, v, hw⟩ => ⟨x, Subgroup.mem_top _, v, hw⟩

end Odd

end CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation
