module

public import CFSG.LocalAnalysis.OddStandard.Seitz77U
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup
open CFSG.OddStandard.Seitz77
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (unipAll)

section Cyclic

variable {M : Type*} [Group M] [IsCyclic M] [Finite M]

theorem eq_one_or_eq_of_mul_self {a b : M} (ha : a * a = 1) (hb : b * b = 1) (hb1 : b ≠ 1) :
    a = 1 ∨ a = b := by
  classical
  have : Fintype M := Fintype.ofFinite M
  by_contra hcon
  push Not at hcon
  obtain ⟨ha1, hab⟩ := hcon
  have h := IsCyclic.card_pow_eq_one_le (α := M) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset M) ⊆ Finset.univ.filter (fun x : M => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sq]
    rcases hx with rfl | rfl | rfl
    · exact mul_one 1
    · exact ha
    · exact hb
  have h3 : ({1, a, b} : Finset M).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, a, b, Ne.symm ha1, Ne.symm hb1, hab, rfl⟩
  have := Finset.card_le_card hsub
  omega

end Cyclic

section Field

theorem ringAut_isCyclic_and_card {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : IsCyclic (RingAut F) ∧ Nat.card (RingAut F) = n := by
  obtain ⟨σ₀, -, -, hσ₀, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hF
  exact ⟨isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₀, hσ₀⟩, hcard⟩

variable {F : Type} [Field F] [Finite F]

theorem card_fix_semilinear_sq_le {τ : RingAut F} (hτ : τ ≠ 1) (l : F) :
    Nat.card {b : F // l * τ b = b} ^ 2 ≤ Nat.card F := by
  obtain ⟨K, hK⟩ : ∃ K : Subfield F, ∀ x : F, x ∈ K ↔ τ x = x :=
    ⟨RingHom.eqLocusField (τ : F →+* F) (RingHom.id F), fun x => Iff.rfl⟩
  have hKsq : Nat.card K ^ 2 ≤ Nat.card F := by
    have hcard : Nat.card F = Nat.card K ^ Module.finrank K F :=
      Module.natCard_eq_pow_finrank
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hn1 : Module.finrank K F ≠ 1 := by
      intro h1
      rw [h1, pow_one] at hcard
      have hbij : Function.Bijective (Subtype.val : K → F) :=
        Subtype.val_injective.bijective_of_nat_card_le hcard.le
      refine hτ (RingEquiv.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := hbij.2 x
      exact (hK y.1).1 y.2
    have hn0 : Module.finrank K F ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hcard
      have := Finite.one_lt_card (α := F)
      omega
    calc Nat.card K ^ 2 ≤ Nat.card K ^ Module.finrank K F :=
          Nat.pow_le_pow_right hpos (by omega)
      _ = Nat.card F := hcard.symm
  have hinj : ∃ g : {b : F // l * τ b = b} → K, Function.Injective g := by
    by_cases h : ∃ b₀ : F, b₀ ≠ 0 ∧ l * τ b₀ = b₀
    · obtain ⟨b₀, hb₀, hfix₀⟩ := h
      have hτb₀ : τ b₀ ≠ 0 := (map_ne_zero τ).2 hb₀
      have hmem : ∀ b : {b : F // l * τ b = b}, b.1 / b₀ ∈ K := by
        intro b
        rw [hK, map_div₀, div_eq_div_iff hτb₀ hb₀]
        calc τ b.1 * b₀ = τ b.1 * (l * τ b₀) := by rw [hfix₀]
          _ = (l * τ b.1) * τ b₀ := by ring
          _ = b.1 * τ b₀ := by rw [b.2]
      refine ⟨fun b => ⟨b.1 / b₀, hmem b⟩, fun b₁ b₂ hb => ?_⟩
      exact Subtype.ext ((div_left_inj' hb₀).1 (congrArg Subtype.val hb))
    · have h0 : ∀ b : {b : F // l * τ b = b}, b.1 = 0 := fun b =>
        by_contra fun hne => h ⟨b.1, hne, b.2⟩
      exact ⟨fun _ => 1, fun b₁ b₂ _ => Subtype.ext ((h0 b₁).trans (h0 b₂).symm)⟩
  obtain ⟨g, hg⟩ := hinj
  exact (Nat.pow_le_pow_left (Nat.card_le_card_of_injective g hg) 2).trans hKsq

omit [Finite F] in
theorem eq_one_of_mul_self_eq_one [CharP F 2] {x : F} (hx : x * x = 1) : x = 1 := by
  rcases mul_self_eq_one_iff.1 hx with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

end Field

section Unip

variable {F : Type} [Field F] [CharP F 2]

theorem coords_eq_of_involution (α : MulAut (unipAll F)) (hα : ∀ g, α (α g) = g)
    (hf : autField α = 1) (hsw : autSwap α = false) (g : unipAll F) :
    coordA (α g) = coordA g ∧ coordB (α g) = coordB g := by
  obtain ⟨l, m, sw, hd⟩ := autField_spec α
  have hs : sw = false := (autSwap_eq hd).symm.trans hsw
  subst hs
  rw [hf] at hd
  have hA : ∀ x, coordA (α x) = (l : F) * coordA x := fun x => by
    have := hd.coordA_eq x
    simpa using this
  have hB : ∀ x, coordB (α x) = (m : F) * coordB x := fun x => by
    have := hd.coordB_eq x
    simpa using this
  have hl : (l : F) = 1 := by
    have h1 := hA (α (uelt 1 0 0))
    rw [hα, hA, coordA_uelt, mul_one] at h1
    exact eq_one_of_mul_self_eq_one h1.symm
  have hm : (m : F) = 1 := by
    have h1 := hB (α (uelt 0 1 0))
    rw [hα, hB, coordB_uelt, mul_one] at h1
    exact eq_one_of_mul_self_eq_one h1.symm
  exact ⟨by rw [hA, hl, one_mul], by rw [hB, hm, one_mul]⟩

theorem fix_inf_radOne_le_radCenter (α : MulAut (unipAll F)) (hsw : autSwap α = true) :
    fixSubgroup α ⊓ radOne F ≤ radCenter F := by
  rintro g ⟨hg, hg1⟩
  have h2 : α g ∈ (radOne F).map α.toMonoidHom := ⟨g, hg1, rfl⟩
  simp only [map_radOne_aut, hsw, ↓reduceIte] at h2
  have hg' : α g = g := hg
  rw [hg'] at h2
  rw [← radOne_inf_radTwo]
  exact ⟨hg1, h2⟩

theorem fix_inf_radTwo_le_radCenter (α : MulAut (unipAll F)) (hsw : autSwap α = true) :
    fixSubgroup α ⊓ radTwo F ≤ radCenter F := by
  rintro g ⟨hg, hg2⟩
  have h2 : α g ∈ (radTwo F).map α.toMonoidHom := ⟨g, hg2, rfl⟩
  simp only [map_radTwo_aut, hsw, ↓reduceIte] at h2
  have hg' : α g = g := hg
  rw [hg'] at h2
  rw [← radOne_inf_radTwo]
  exact ⟨h2, hg2⟩

theorem mul_le_of_sq_le {x y z : ℕ} (hx : x ^ 2 ≤ z) (hy : y ^ 2 ≤ z) : x * y ≤ z := by
  by_contra h
  push Not at h
  have h1 : z * z < (x * y) * (x * y) := Nat.mul_lt_mul'' h h
  have h2 : (x * y) * (x * y) = x ^ 2 * y ^ 2 := by ring
  have h3 : x ^ 2 * y ^ 2 ≤ z * z := Nat.mul_le_mul hx hy
  omega

variable [Finite F]

theorem card_fix_inf_radOne_le (α : MulAut (unipAll F)) (hsw : autSwap α = false)
    (hf : autField α ≠ 1) : Nat.card ↥(fixSubgroup α ⊓ radOne F) ≤ Nat.card F := by
  classical
  obtain ⟨l, m, sw, hd⟩ := autField_spec α
  have hs : sw = false := (autSwap_eq hd).symm.trans hsw
  subst hs
  set τ := autField α with hτ
  set H := fixSubgroup α ⊓ radOne F with hH
  have hfixH : ∀ g : H, α g = g := fun g => g.2.1
  let φ : H →* Multiplicative F :=
    { toFun := fun g => Multiplicative.ofAdd (coordA (g : unipAll F))
      map_one' := by simp [coordA, CFSG.OddStandard.Seitz77.coordA]
      map_mul' := fun g g' => by
        simp only [Subgroup.coe_mul, coordA_mul, ofAdd_add] }
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ Nat.card {c : F // ((l : F) * m) * τ c = c} := by
    refine Nat.card_le_card_of_injective
      (fun g => ⟨coordC ((g : H) : unipAll F), ?_⟩) ?_
    · obtain ⟨g, hgk⟩ := g
      have hA : coordA (g : unipAll F) = 0 := by
        have := MonoidHom.mem_ker.1 hgk
        simpa [φ] using this
      have hB : coordB (g : unipAll F) = 0 := (mem_radOne _).1 g.2.2
      have hg : (g : unipAll F) = uelt 0 0 (coordC (g : unipAll F)) := by
        conv_lhs => rw [← uelt_coords (g : unipAll F)]
        rw [hA, hB]
      have h1 := hfixH g
      rw [hg, hd.2] at h1
      exact (uelt_inj.1 h1).2.2
    · rintro ⟨⟨g, hg⟩, hgk⟩ ⟨⟨g', hg'⟩, hgk'⟩ hgg'
      have hc : coordC g = coordC g' := congrArg Subtype.val hgg'
      have hA : coordA g = 0 := by
        have := MonoidHom.mem_ker.1 hgk
        simpa [φ] using this
      have hA' : coordA g' = 0 := by
        have := MonoidHom.mem_ker.1 hgk'
        simpa [φ] using this
      have hB : coordB g = 0 := (mem_radOne _).1 hg.2
      have hB' : coordB g' = 0 := (mem_radOne _).1 hg'.2
      have : g = g' := by
        rw [← uelt_coords g, ← uelt_coords g', hA, hA', hB, hB', hc]
      subst this
      rfl
  have hrange : Nat.card φ.range ≤ Nat.card {a : F // (l : F) * τ a = a} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨Multiplicative.toAdd (x : Multiplicative F), ?_⟩) ?_
    · obtain ⟨x, g, rfl⟩ := x
      have h1 := hd.coordA_eq (g : unipAll F)
      simp only [Bool.false_eq_true, ite_false] at h1
      rw [hfixH g] at h1
      exact h1.symm
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext h1
  have h1 := card_fix_semilinear_sq_le hf ((l : F) * m)
  have h2 := card_fix_semilinear_sq_le hf (l : F)
  rw [← hcard]
  exact (Nat.mul_le_mul hker hrange).trans (mul_le_of_sq_le h1 h2)

theorem card_fix_inf_radTwo_le (α : MulAut (unipAll F)) (hsw : autSwap α = false)
    (hf : autField α ≠ 1) : Nat.card ↥(fixSubgroup α ⊓ radTwo F) ≤ Nat.card F := by
  classical
  obtain ⟨l, m, sw, hd⟩ := autField_spec α
  have hs : sw = false := (autSwap_eq hd).symm.trans hsw
  subst hs
  set τ := autField α with hτ
  set H := fixSubgroup α ⊓ radTwo F with hH
  have hfixH : ∀ g : H, α g = g := fun g => g.2.1
  let φ : H →* Multiplicative F :=
    { toFun := fun g => Multiplicative.ofAdd (coordB (g : unipAll F))
      map_one' := by simp [coordB, CFSG.OddStandard.Seitz77.coordB]
      map_mul' := fun g g' => by
        simp only [Subgroup.coe_mul, coordB_mul, ofAdd_add] }
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ Nat.card {c : F // ((l : F) * m) * τ c = c} := by
    refine Nat.card_le_card_of_injective
      (fun g => ⟨coordC ((g : H) : unipAll F), ?_⟩) ?_
    · obtain ⟨g, hgk⟩ := g
      have hB : coordB (g : unipAll F) = 0 := by
        have := MonoidHom.mem_ker.1 hgk
        simpa [φ] using this
      have hA : coordA (g : unipAll F) = 0 := (mem_radTwo _).1 g.2.2
      have hg : (g : unipAll F) = uelt 0 0 (coordC (g : unipAll F)) := by
        conv_lhs => rw [← uelt_coords (g : unipAll F)]
        rw [hA, hB]
      have h1 := hfixH g
      rw [hg, hd.2] at h1
      exact (uelt_inj.1 h1).2.2
    · rintro ⟨⟨g, hg⟩, hgk⟩ ⟨⟨g', hg'⟩, hgk'⟩ hgg'
      have hc : coordC g = coordC g' := congrArg Subtype.val hgg'
      have hB : coordB g = 0 := by
        have := MonoidHom.mem_ker.1 hgk
        simpa [φ] using this
      have hB' : coordB g' = 0 := by
        have := MonoidHom.mem_ker.1 hgk'
        simpa [φ] using this
      have hA : coordA g = 0 := (mem_radTwo _).1 hg.2
      have hA' : coordA g' = 0 := (mem_radTwo _).1 hg'.2
      have : g = g' := by
        rw [← uelt_coords g, ← uelt_coords g', hA, hA', hB, hB', hc]
      subst this
      rfl
  have hrange : Nat.card φ.range ≤ Nat.card {b : F // (m : F) * τ b = b} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨Multiplicative.toAdd (x : Multiplicative F), ?_⟩) ?_
    · obtain ⟨x, g, rfl⟩ := x
      have h1 := hd.coordB_eq (g : unipAll F)
      simp only [Bool.false_eq_true, ite_false] at h1
      rw [hfixH g] at h1
      exact h1.symm
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext h1
  have h1 := card_fix_semilinear_sq_le hf ((l : F) * m)
  have h2 := card_fix_semilinear_sq_le hf (m : F)
  rw [← hcard]
  exact (Nat.mul_le_mul hker hrange).trans (mul_le_of_sq_le h1 h2)

omit [Finite F] in
theorem card_fix_le_of_swap (α : MulAut (unipAll F)) (hα : ∀ g, α (α g) = g)
    (hsw : autSwap α = true) (hf : autField α = 1) :
    Nat.card ↥(fixSubgroup α) ≤ Nat.card F := by
  obtain ⟨-, β, hβ⟩ := exists_conj_graphField_of_swap α hα hsw
  rw [hf] at hβ
  have hgr : ∀ g, graphFieldAut (1 : RingAut F) g = graphAut g := by
    intro g
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    rw [graphFieldAut_uelt, graphAut_uelt]
    simp
  have e2 : ↥(fixSubgroup α) ≃ ↥(fixSubgroup (graphAut : MulAut ↥(unipAll F))) :=
    { toFun := fun u => ⟨β u.1, by
        show graphAut (β u.1) = β u.1
        rw [← hgr, ← hβ, show α u.1 = u.1 from u.2]⟩
      invFun := fun v => ⟨β.symm v.1, by
        show α (β.symm v.1) = β.symm v.1
        apply β.injective
        rw [hβ, hgr, MulEquiv.apply_symm_apply]
        exact v.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  rw [Nat.card_congr e2, fixSubgroup_graphAut, card_radCenter]

end Unip

section Thompson

open CFSG.GH74.GLS.Bg.Thompson

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_ker_map_subtype_iff {T : Subgroup G} {M : Type*} [Group M] (θ : ↥T →* M) {g : G}
    (hg : g ∈ T) : g ∈ θ.ker.map T.subtype ↔ θ ⟨g, hg⟩ = 1 := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact MonoidHom.mem_ker.mp hz
  · intro h
    exact ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr h, rfl⟩

theorem exists_extremal_conj_mem_ker [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) {M : Type*} [Group M]
    [IsCyclic M] [Finite M] (ψ : ↥T →* M) {u : G} (huT : u ∈ T) (hu2 : u * u = 1)
    (hu1 : ψ ⟨u, huT⟩ ≠ 1) :
    ∃ x : G, ∃ hx : x⁻¹ * u * x ∈ T, ψ ⟨_, hx⟩ = 1 ∧ IsExtremalIn 2 T (x⁻¹ * u * x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := ψ.ker.map T.subtype with hQ
  have hmemQ : ∀ g (hg : g ∈ T), g ∈ Q ↔ ψ ⟨g, hg⟩ = 1 := fun g hg =>
    mem_ker_map_subtype_iff ψ hg
  have hQT : Q ≤ T := Subgroup.map_subtype_le _
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have hqT := hQT hq
    rw [hmemQ _ (T.mul_mem (T.mul_mem ht hqT) (T.inv_mem ht))]
    have e : (⟨t * q * t⁻¹, T.mul_mem (T.mul_mem ht hqT) (T.inv_mem ht)⟩ : T) =
        ⟨t, ht⟩ * ⟨q, hqT⟩ * ⟨t, ht⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, (hmemQ q hqT).1 hq, mul_one, map_inv, mul_inv_cancel]
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
    obtain ⟨b, hb⟩ := g.2
    refine ⟨b, b.2, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨ψ ⟨t, ht⟩, ⟨_, rfl⟩⟩)
    refine ⟨k, ?_⟩
    have hbk : (b : G) ^ k ∈ T := T.zpow_mem b.2 k
    rw [hmemQ _ (T.mul_mem (T.inv_mem hbk) ht)]
    have e : (⟨((b : G) ^ k)⁻¹ * t, T.mul_mem (T.inv_mem hbk) ht⟩ : T) = (b ^ k)⁻¹ * ⟨t, ht⟩ :=
      Subtype.ext (by simp)
    have hk' : ψ b ^ k = ψ ⟨t, ht⟩ := by
      have := congrArg Subtype.val hk
      simpa [hb] using this
    rw [e, map_mul, map_inv, map_zpow, hk', inv_mul_cancel]
  have huQ : u ∉ Q := fun h => hu1 ((hmemQ u huT).1 h)
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T → g⁻¹ * u ^ (2 * k) * g ∈ Q := by
    intro g k _
    rw [pow_mul, sq, hu2, one_pow, mul_one, inv_mul_cancel]
    exact Q.one_mem
  have hc : ∀ g : G, g⁻¹ * u * g ∈ T → IsExtremalIn 2 T (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ Q ∨ u⁻¹ * (g⁻¹ * u * g) ∈ Q := by
    intro g hgT _
    have hy2 : (⟨_, hgT⟩ : T) * ⟨_, hgT⟩ = 1 := Subtype.ext (by
      show g⁻¹ * u * g * (g⁻¹ * u * g) = 1
      calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
        _ = 1 := by rw [hu2]; group)
    have hu2' : (⟨u, huT⟩ : T) * ⟨u, huT⟩ = 1 := Subtype.ext hu2
    have hψy : ψ ⟨_, hgT⟩ * ψ ⟨_, hgT⟩ = 1 := by rw [← map_mul, hy2, map_one]
    have hψu : ψ ⟨u, huT⟩ * ψ ⟨u, huT⟩ = 1 := by rw [← map_mul, hu2', map_one]
    rcases eq_one_or_eq_of_mul_self hψy hψu hu1 with h | h
    · exact Or.inl ((hmemQ _ hgT).2 h)
    · refine Or.inr ((hmemQ _ (T.mul_mem (T.inv_mem huT) hgT)).2 ?_)
      have e : (⟨u⁻¹ * (g⁻¹ * u * g), T.mul_mem (T.inv_mem huT) hgT⟩ : T) =
          (⟨u, huT⟩ : T)⁻¹ * ⟨_, hgT⟩ := rfl
      rw [e, map_mul, map_inv, h, inv_mul_cancel]
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc huT huQ hb hc with
    ⟨N, hN, -, hNp, huN⟩ | ⟨x, hx, hext, -⟩
  · exfalso
    have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply huN
      have h1 : (QuotientGroup.mk u : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff u).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M', hM', -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M'.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM'
    exact CFSG.LargeExtraspecial.GLR.index_ne_two_of_isSimpleGroup hnonab _
      ((Subgroup.index_comap_of_surjective M' (f := QuotientGroup.mk' N)
        QuotientGroup.mk_surjective).trans hMidx)
  · exact ⟨x, hQT hx, (hmemQ _ (hQT hx)).1 hx, hext⟩

end Thompson

end CFSG.LocalAnalysis.EvenBN.LinearThree
