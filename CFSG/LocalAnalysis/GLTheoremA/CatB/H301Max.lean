module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

theorem range_eq_top_of_forall_inner {K A : Type*} [Group K] [Group A]
    (hinn : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g) (ι : K →* A) (hι : Function.Injective ι)
    (hN : ι.range.Normal) (hC : Subgroup.centralizer (ι.range : Set A) = ⊥) : ι.range = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  let e : K ≃* ι.range := MonoidHom.ofInjective hι
  obtain ⟨g, hg⟩ := hinn ((e.trans (MulAut.conjNormal (H := ι.range) a)).trans e.symm)
  have key : ∀ x : K, a * ι x * a⁻¹ = ι g * ι x * (ι g)⁻¹ := by
    intro x
    have h1 := congrArg (fun β : MulAut K => ι (β x)) hg
    simp only [MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply,
      MulAut.conj_apply, map_mul, map_inv, e, MonoidHom.ofInjective_apply] at h1
    exact h1
  have hmem : (ι g)⁻¹ * a ∈ Subgroup.centralizer (ι.range : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    calc ι x * ((ι g)⁻¹ * a) = (ι g)⁻¹ * (ι g * ι x * (ι g)⁻¹) * a := by group
      _ = (ι g)⁻¹ * (a * ι x * a⁻¹) * a := by rw [key x]
      _ = (ι g)⁻¹ * a * ι x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact MonoidHom.mem_range.2 ⟨g, hmem⟩

theorem exists_central_involution {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    ∃ X ∈ S, X ≠ 1 ∧ X * X = 1 ∧ ∀ s ∈ S, Commute X s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  have hZ := hS.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := (hS.to_subgroup (Subgroup.center S)).nontrivial_iff_card.1 hZ
  obtain ⟨X, hX⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2
    (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  refine ⟨((X : S) : G), (X : S).2, fun h => ?_, ?_, fun s hs => ?_⟩
  · have h1 : X = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hX
    exact absurd hX (by norm_num)
  · have h1 : X * X = 1 := by rw [← pow_two, ← hX, pow_orderOf_eq_one]
    exact congrArg (fun y : Subgroup.center S => ((y : S) : G)) h1
  · have h1 := Subgroup.mem_center_iff.1 X.2 ⟨s, hs⟩
    exact (congrArg (fun y : S => (y : G)) h1).symm

theorem exists_central_mod {G : Type*} [Group G] [Finite G] {Y V : Subgroup G}
    (hY : IsPGroup 2 Y) (hVY : V ≤ Y) (hVn : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hne : ¬ Y ≤ V) :
    ∃ g ∈ Y, g ∉ V ∧ g * g ∈ V ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup Y := V.subgroupOf Y
  haveI hWn : W.Normal := ⟨fun w hw y => Subgroup.mem_subgroupOf.2 (by
    simpa using hVn y y.2 w (Subgroup.mem_subgroupOf.1 hw))⟩
  have hQ : IsPGroup 2 (Y ⧸ W) := hY.to_quotient W
  have hQne : (⊤ : Subgroup (Y ⧸ W)) ≠ ⊥ := by
    intro h
    apply hne
    intro y hy
    have h1 : (QuotientGroup.mk (⟨y, hy⟩ : Y) : Y ⧸ W) ∈ (⊥ : Subgroup (Y ⧸ W)) := h ▸ trivial
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨X, -, hX1, hX2, hXc⟩ := exists_central_involution (hQ.to_subgroup ⊤) hQne
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective X
  refine ⟨g, g.2, fun hg => hX1 ((QuotientGroup.eq_one_iff g).2
    (Subgroup.mem_subgroupOf.2 hg)), ?_, fun y hy => ?_⟩
  · have h1 : (QuotientGroup.mk (g * g) : Y ⧸ W) = 1 := by rw [QuotientGroup.mk_mul, hX2]
    rw [QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  · have hc := (hXc (QuotientGroup.mk (⟨y, hy⟩ : Y)) trivial).eq
    have h1 : (QuotientGroup.mk (g * ⟨y, hy⟩ * g⁻¹ * (⟨y, hy⟩ : Y)⁻¹) : Y ⧸ W) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hc]
      group
    rw [QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1

end CFSG.LocalAnalysis.GLTheoremA.H301
