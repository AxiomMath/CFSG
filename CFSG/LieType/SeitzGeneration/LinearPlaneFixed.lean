module

public import CFSG.LieType.SeitzGeneration.SpFourFix
public import CFSG.LieType.SeitzGeneration.NonabLinear
public import CFSG.RankThree.PartOne.CTP.SeitzToral

public section

namespace CFSG.LieType.SeitzGeneration

section Rep

variable {G V K : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

theorem exists_fixed_of_plane_rep (ρ : G → Module.End K V) (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (hone : ρ 1 = 1) {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) (h3 : (3 : K) ≠ 0) {U : Submodule K V}
    (hU : ∀ e ∈ E, ∀ u ∈ U, ρ e u ∈ U) (hU0 : U ≠ ⊥) :
    ∃ z ∈ E, z ≠ 1 ∧ ∃ u ∈ U, u ≠ 0 ∧ ρ z u = u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy1, hxy21⟩ := exists_generators_of_plane hexp hcard
  have hcomp : ∀ g h v, ρ (g * h) v = ρ g (ρ h v) := fun g h v => by
    rw [hmul, Module.End.mul_apply]
  have hcube : ∀ g : G, g ^ 3 = 1 → ∀ v, ρ g (ρ g (ρ g v)) = v := fun g hg v => by
    have h : g * g * g = 1 := by rw [← pow_three']; exact hg
    rw [← hcomp, ← hcomp, h, hone]
    rfl
  have hfix : ∀ g : G, g ^ 3 = 1 → ∀ v, ρ g (v + ρ g v + ρ g (ρ g v)) =
      v + ρ g v + ρ g (ρ g v) := fun g hg v => by
    rw [map_add, map_add, hcube g hg]
    abel
  have hN : ∀ g ∈ E, g ≠ 1 → ∀ u ∈ U, u + ρ g u + ρ g (ρ g u) = 0 := by
    intro g hg hg1 u hu
    by_contra h0
    have hgu : ρ g u ∈ U := hU g hg u hu
    exact hcon g hg hg1 _ (U.add_mem (U.add_mem hu hgu) (hU g hg _ hgu)) h0 (hfix g (hexp g hg) u)
  have hxy : ∀ v, ρ y (ρ x v) = ρ x (ρ y v) := fun v => by
    rw [← hcomp, ← hcomp, hcomm y hy x hx]
  have hyc : ∀ v, ρ y (ρ y (ρ y v)) = v := hcube y (hexp y hy)
  have hxy2 : ∀ v, ρ y (ρ y (ρ x v)) = ρ x (ρ y (ρ y v)) := fun v => by
    rw [hxy, hxy]
  have hzero : ∀ u ∈ U, u = 0 := by
    intro u hu
    have hYu : ρ y u ∈ U := hU y hy u hu
    have hYYu : ρ y (ρ y u) ∈ U := hU y hy _ hYu
    have b := hN y hy hy1 u hu
    have c := hN (x * y) (E.mul_mem hx hy) hxy1 u hu
    have d := hN (x * (y * y)) (E.mul_mem hx (E.mul_mem hy hy)) hxy21 u hu
    have e1 := hN x hx hx1 (ρ y u) hYu
    have e2 := hN x hx hx1 (ρ y (ρ y u)) hYYu
    simp only [hcomp] at c d
    rw [hxy (ρ y u)] at c
    rw [hxy2 (ρ y (ρ y u)), hyc (ρ y u)] at d
    have h3u : (3 : K) • u = 0 := by
      linear_combination (norm := module) b + c + d - e1 - e2
    exact (smul_eq_zero.mp h3u).resolve_left h3
  exact hU0 ((Submodule.eq_bot_iff U).2 hzero)

end Rep

section SL

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_invariant_of_plane_sl (hn : 1 ≤ n) (h3 : (3 : F) ≠ 0)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x ∈ E, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
  by_contra hno
  push Not at hno
  let ρ : Matrix.SpecialLinearGroup (Fin n) F → Module.End F (Fin n → F) := fun x =>
    Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := fun g h => by
    simp only [ρ, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl
  have hone : ρ 1 = 1 := by
    simp only [ρ, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  have hρ : ∀ x v, ρ x v = (x : Matrix (Fin n) (Fin n) F).mulVec v := fun x v => by
    simp [ρ, Matrix.toLin'_apply]
  have : Nontrivial (Fin n → F) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨z, hz, hz1, u, -, hu0, hzu⟩ := exists_fixed_of_plane_rep ρ hmul hone hcomm hexp hcard h3
    (U := ⊤) (fun _ _ _ _ => trivial) top_ne_bot
  let W : Submodule F (Fin n → F) := LinearMap.ker (ρ z - 1)
  have hmemW : ∀ w, w ∈ W ↔ ρ z w = w := fun w => by
    simp [W, LinearMap.mem_ker, sub_eq_zero]
  have hWE : ∀ x ∈ E, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := fun x hx w hw => by
    rw [← hρ, hmemW] at *
    rw [← Module.End.mul_apply, ← hmul, hcomm z hz x hx, hmul, Module.End.mul_apply, hw]
  have hW0 : W ≠ ⊥ := fun h => hu0 (by
    have : u ∈ W := (hmemW u).2 hzu
    rw [h] at this
    exact (Submodule.mem_bot F).1 this)
  have hWt : W ≠ ⊤ := fun h => hz1 (by
    have h1 : ρ z = 1 := LinearMap.ext fun v => (hmemW v).1 (h ▸ Submodule.mem_top)
    have h2 : (z : Matrix (Fin n) (Fin n) F) = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_one]
      exact h1
    exact Subtype.ext h2)
  obtain ⟨x, hx, w, hw, hnot⟩ := hno W hW0 hWt
  exact hnot (hWE x hx w hw)

end SL

section Psl

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem closure_centralizers_psl_three_ab (hn : 2 ≤ n) (h3 : (3 : F) ≠ 0)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)))
    (E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    Subgroup.closure {k : Matrix.ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite (Matrix.SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (Subtype.val : Matrix.SpecialLinearGroup (Fin n) F →
      Matrix (Fin n) (Fin n) F) Subtype.val_injective
  set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) with hZdef
  set π : Matrix.SpecialLinearGroup (Fin n) F →* Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker
    π hπ (by rwa [hker]) E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.disjoint_def.mp hE'dis hc hk)
  have hE'exp : ∀ a ∈ E', a ^ 3 = 1 := by
    intro a ha
    have hk : a ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha 3) hk
  have hE'card : Nat.card E' = 9 := by
    let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
    have hfπsurj : Function.Surjective fπ := by
      intro e
      have : (e : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) ∈ E'.map π := hE'map ▸ e.2
      obtain ⟨x, hx, hxe⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have hfπinj : Function.Injective fπ := by
      intro x y hxy
      have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
      have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3' : x.1⁻¹ * y.1 = 1 :=
        Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3')
    rw [← hcard]
    exact Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  obtain ⟨W, hW0, hWt, hWE'⟩ := exists_invariant_of_plane_sl (by omega) h3 hE'comm hE'exp hE'card
  refine closure_centralizers_psl_of_reducible Nat.prime_three (by exact_mod_cast h3)
    (natCast_card_center_ne_zero (by omega)) E hcomm hexp (by rw [hcard]; norm_num) hW0 hWt ?_
  intro x hx w hw
  obtain ⟨e, he, hex⟩ : ∃ e ∈ E', π e = π x := by
    have : π x ∈ E'.map π := hE'map ▸ hx
    obtain ⟨e, he, h⟩ := this
    exact ⟨e, he, h⟩
  have hz : x * e⁻¹ ∈ Z := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hex, mul_inv_cancel]
  obtain ⟨r, -, hr⟩ := exists_scalar_of_mem_center (by omega) hz
  have hxe : (x : Matrix (Fin n) (Fin n) F) = r • (e : Matrix (Fin n) (Fin n) F) := by
    have h1 : x = (x * e⁻¹) * e := by group
    have h2 := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, hr, Matrix.smul_mul, Matrix.one_mul] at h2
    exact h2
  rw [hxe, Matrix.smul_mulVec]
  exact W.smul_mem r (hWE' e he w hw)

end Psl

end CFSG.LieType.SeitzGeneration
