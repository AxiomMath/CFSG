module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticRankTwoCounts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitStabilizer

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin Module Submodule

section Counting

theorem card_mul_eq_card_mul_of_rel {A B : Type*} [Finite A] [Finite B] (R : A → B → Prop)
    {a b : ℕ} (ha : ∀ x, Nat.card {y // R x y} = a) (hb : ∀ y, Nat.card {x // R x y} = b) :
    Nat.card A * a = Nat.card B * b := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  let I := {p : A × B // R p.1 p.2}
  have hfst : ∀ x : A, Nat.card {p : I // p.1.1 = x} = a := by
    intro x
    rw [← ha x]
    exact Nat.card_congr
      { toFun := fun p => ⟨p.1.1.2, by
          have h := p.1.2
          rw [show p.1.1.1 = x from p.2] at h
          exact h⟩
        invFun := fun y => ⟨⟨(x, y.1), y.2⟩, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨⟨x', y'⟩, h⟩, rfl⟩ := p
          rfl
        right_inv := fun y => rfl }
  have hsnd : ∀ y : B, Nat.card {p : I // p.1.2 = y} = b := by
    intro y
    rw [← hb y]
    exact Nat.card_congr
      { toFun := fun p => ⟨p.1.1.1, by
          have h := p.1.2
          rw [show p.1.1.2 = y from p.2] at h
          exact h⟩
        invFun := fun x => ⟨⟨(x.1, y), x.2⟩, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨⟨x', y'⟩, h⟩, rfl⟩ := p
          rfl
        right_inv := fun x => rfl }
  have h1 := Nat.card_congr (Equiv.sigmaFiberEquiv fun p : I => p.1.1)
  have h2 := Nat.card_congr (Equiv.sigmaFiberEquiv fun p : I => p.1.2)
  rw [Nat.card_sigma, Finset.sum_congr rfl fun x _ => hfst x, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at h1
  rw [Nat.card_sigma, Finset.sum_congr rfl fun y _ => hsnd y, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at h2
  exact h1.trans h2.symm

theorem card_subtype_split {α : Type*} [Finite α] (p r : α → Prop) :
    Nat.card {x // p x} = Nat.card {x // p x ∧ r x} + Nat.card {x // p x ∧ ¬r x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr ((Equiv.sumCompl fun x : {x // p x} => r x.1).symm.trans
    (Equiv.sumCongr (Equiv.subtypeSubtypeEquivSubtypeInter p r)
      (Equiv.subtypeSubtypeEquivSubtypeInter p fun x => ¬r x)))

theorem card_ne_add_one {α : Type*} [Finite α] {p : α → Prop} {a : α} (ha : p a) :
    Nat.card {x // p x ∧ x ≠ a} + 1 = Nat.card {x // p x} := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  rw [show (Finset.univ.filter fun x : α => p x ∧ x ≠ a) = (Finset.univ.filter p).erase a by
    ext x
    simp [and_comm]]
  exact Finset.card_erase_add_one (by simpa using ha)

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem card_between_mul {U X : Submodule K V} (hUX : U ≤ X) :
    Nat.card {W : Submodule K V // U ≤ W ∧ W ≤ X ∧ finrank K W = finrank K U + 1} *
        (Nat.card K ^ (finrank K U + 1) - Nat.card K ^ finrank K U) =
      Nat.card K ^ finrank K X - Nat.card K ^ finrank K U := by
  rw [← card_extensionsWith_le_mul hUX]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun W =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨h1, h2, h3⟩⟩)

theorem card_between_two {U X : Submodule K V} (hUX : U ≤ X)
    (hd : finrank K X = finrank K U + 2) :
    Nat.card {W : Submodule K V // U ≤ W ∧ W ≤ X ∧ finrank K W = finrank K U + 1} =
      Nat.card K + 1 := by
  have h := card_between_mul hUX
  rw [hd] at h
  have hq : 1 < Nat.card K := Finite.one_lt_card
  set N := Nat.card {W : Submodule K V // U ≤ W ∧ W ≤ X ∧ finrank K W = finrank K U + 1}
  generalize Nat.card K = q at h hq ⊢
  generalize finrank K U = u at h
  have hpos : 0 < q ^ (u + 1) - q ^ u := by
    have := Nat.pow_lt_pow_right hq (by omega : u < u + 1)
    omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  have e1 : q ^ (u + 2) = q ^ u * q * q := by ring
  have e2 : q ^ (u + 1) = q ^ u * q := by ring
  rw [e1, e2]
  have h1 : q ^ u ≤ q ^ u * q := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : q ^ u ≤ q ^ u * q * q := h1.trans (Nat.le_mul_of_pos_right _ (by omega))
  zify [h1, h2]
  ring

theorem card_lines_mul (X : Submodule K V) :
    Nat.card {W : Submodule K V // W ≤ X ∧ finrank K W = 1} * (Nat.card K - 1) =
      Nat.card K ^ finrank K X - 1 := by
  have h := card_between_mul (bot_le : ⊥ ≤ X)
  rw [finrank_bot, zero_add, pow_one, pow_zero] at h
  rw [← h]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun W =>
    ⟨fun ⟨h1, h2⟩ => ⟨bot_le, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩)

end Counting

section Polarity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure SingularImage (Q : QuadraticForm K V) (N : V →ₗ[K] V) : Prop where
  nondeg : (polarBilin Q).Nondegenerate
  singular : ∀ x ∈ LinearMap.range N, Q x = 0
  ker_eq : LinearMap.ker N = LinearMap.range N
  polar_self : ∀ x, polar Q (N x) x = 0
  finrank_eq : 2 * finrank K (LinearMap.range N) = finrank K V

@[expose] def nPolar (Q : QuadraticForm K V) (N : V →ₗ[K] V) (S : Submodule K V) :
    Submodule K V :=
  (LinearMap.BilinForm.orthogonal (polarBilin Q) S).map N

variable {Q : QuadraticForm K V} {N : V →ₗ[K] V}

theorem mem_orth_iff {S : Submodule K V} {x : V} :
    x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) S ↔ ∀ s ∈ S, polar Q s x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  exact Iff.rfl

theorem nPolar_le_range (S : Submodule K V) : nPolar Q N S ≤ LinearMap.range N := by
  rintro _ ⟨z, -, rfl⟩
  exact LinearMap.mem_range_self N z

namespace SingularImage

theorem apply_eq_zero_iff (hN : SingularImage Q N) {x : V} :
    N x = 0 ↔ x ∈ LinearMap.range N := by
  rw [← LinearMap.mem_ker, hN.ker_eq]

theorem polar_eq_zero (hN : SingularImage Q N) {x y : V} (hx : x ∈ LinearMap.range N)
    (hy : y ∈ LinearMap.range N) : polar Q x y = 0 :=
  polar_eq_zero_of_singular hN.singular hx hy

theorem polar_apply_comm [CharP K 2] (hN : SingularImage Q N) (y z : V) :
    polar Q (N y) z = polar Q (N z) y := by
  have h := hN.polar_self (y + z)
  rw [map_add, polar_add_left, polar_add_right, polar_add_right, hN.polar_self y,
    hN.polar_self z, zero_add, add_zero] at h
  rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
  exact h

theorem range_le_orth (hN : SingularImage Q N) {S : Submodule K V}
    (hS : S ≤ LinearMap.range N) :
    LinearMap.range N ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) S := fun _x hx =>
  mem_orth_iff.2 fun _s hs => hN.polar_eq_zero (hS hs) hx

theorem mem_nPolar_iff (hN : SingularImage Q N) {S : Submodule K V}
    (hS : S ≤ LinearMap.range N) {x : V} :
    x ∈ nPolar Q N S ↔ x ∈ LinearMap.range N ∧ ∀ z, N z = x → ∀ s ∈ S, polar Q s z = 0 := by
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    refine ⟨LinearMap.mem_range_self N z₀, fun z hz s hs => ?_⟩
    have hk : z - z₀ ∈ LinearMap.range N := (hN.apply_eq_zero_iff).1 (by rw [map_sub, hz,
      sub_self])
    have h1 := mem_orth_iff.1 hz₀ s hs
    have h2 := hN.polar_eq_zero (hS hs) hk
    rw [polar_sub_right, h1, sub_zero] at h2
    exact h2
  · rintro ⟨⟨z, rfl⟩, h⟩
    exact ⟨z, mem_orth_iff.2 fun s hs => h z rfl s hs, rfl⟩

theorem le_nPolar_iff (hN : SingularImage Q N) {S S' : Submodule K V}
    (hS : S ≤ LinearMap.range N) (hS' : S' ≤ LinearMap.range N) :
    S' ≤ nPolar Q N S ↔ ∀ y z, N y ∈ S → N z ∈ S' → polar Q (N y) z = 0 := by
  constructor
  · intro h y z hy hz
    exact ((hN.mem_nPolar_iff hS).1 (h hz)).2 z rfl (N y) hy
  · intro h x hx
    refine (hN.mem_nPolar_iff hS).2 ⟨hS' hx, fun z hz s hs => ?_⟩
    obtain ⟨y, rfl⟩ := hS hs
    exact h y z hs (hz ▸ hx)

theorem le_nPolar_comm [CharP K 2] (hN : SingularImage Q N) {S S' : Submodule K V}
    (hS : S ≤ LinearMap.range N) (hS' : S' ≤ LinearMap.range N) :
    S' ≤ nPolar Q N S ↔ S ≤ nPolar Q N S' := by
  rw [hN.le_nPolar_iff hS hS', hN.le_nPolar_iff hS' hS]
  exact ⟨fun h y z hy hz => by rw [hN.polar_apply_comm]; exact h z y hz hy,
    fun h y z hy hz => by rw [hN.polar_apply_comm]; exact h z y hz hy⟩

theorem finrank_nPolar [FiniteDimensional K V] (hN : SingularImage Q N) {S : Submodule K V}
    (hS : S ≤ LinearMap.range N) :
    finrank K (nPolar Q N S) + finrank K S = finrank K (LinearMap.range N) := by
  have hP : finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q) S) =
      finrank K V - finrank K S :=
    LinearMap.BilinForm.finrank_orthogonal hN.nondeg S
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (N.domRestrict (LinearMap.BilinForm.orthogonal (polarBilin Q) S))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
  have hkP : LinearMap.ker N ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) S :=
    hN.ker_eq ▸ hN.range_le_orth hS
  have hk : finrank K ((LinearMap.ker N).comap
      (LinearMap.BilinForm.orthogonal (polarBilin Q) S).subtype) =
      finrank K (LinearMap.range N) := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hkP), hN.ker_eq]
  have hSX := Submodule.finrank_mono hS
  have hV := hN.finrank_eq
  change finrank K ((LinearMap.BilinForm.orthogonal (polarBilin Q) S).map N) + finrank K S = _
  omega

theorem nPolar_nPolar [CharP K 2] [FiniteDimensional K V] (hN : SingularImage Q N)
    {S : Submodule K V} (hS : S ≤ LinearMap.range N) : nPolar Q N (nPolar Q N S) = S := by
  have hle : S ≤ nPolar Q N (nPolar Q N S) :=
    (hN.le_nPolar_comm (nPolar_le_range S) hS).2 le_rfl
  have h1 := hN.finrank_nPolar hS
  have h2 := hN.finrank_nPolar (nPolar_le_range (Q := Q) (N := N) S)
  exact (eq_of_le_of_finrank_eq hle (by omega)).symm

theorem le_nPolar_of_finrank_one [FiniteDimensional K V] (hN : SingularImage Q N)
    {ℓ : Submodule K V} (hℓ : ℓ ≤ LinearMap.range N) (h1 : finrank K ℓ = 1) :
    ℓ ≤ nPolar Q N ℓ := by
  rw [hN.le_nPolar_iff hℓ hℓ]
  intro y z hy hz
  by_cases hz0 : N z = 0
  · exact hN.polar_eq_zero (LinearMap.mem_range_self N y) ((hN.apply_eq_zero_iff).1 hz0)
  · have hspan := span_singleton_eq_of_mem h1 hz hz0
    rw [← hspan] at hy
    obtain ⟨c, hc⟩ := mem_span_singleton.1 hy
    rw [← hc, polar_smul_left_eq, hN.polar_self, mul_zero]

theorem nPolar_inf_le (hN : SingularImage Q N) {S S' : Submodule K V}
    (hS : S ≤ LinearMap.range N) (hS' : S' ≤ LinearMap.range N) :
    nPolar Q N S ⊓ nPolar Q N S' ≤ nPolar Q N (S ⊔ S') := by
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hx, hx'⟩ := hx
  rw [hN.mem_nPolar_iff hS] at hx
  rw [hN.mem_nPolar_iff hS'] at hx'
  refine (hN.mem_nPolar_iff (sup_le hS hS')).2 ⟨hx.1, fun z hz s hs => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 hs
  rw [polar_add_left, hx.2 z hz a ha, hx'.2 z hz b hb, add_zero]

theorem nPolar_le_of_codim_one [CharP K 2] [FiniteDimensional K V] (hN : SingularImage Q N)
    {H : Submodule K V} (hH : H ≤ LinearMap.range N)
    (h3 : finrank K H + 1 = finrank K (LinearMap.range N)) : nPolar Q N H ≤ H := by
  have h1 : finrank K (nPolar Q N H) = 1 := by
    have := hN.finrank_nPolar hH
    omega
  have h := hN.le_nPolar_of_finrank_one (nPolar_le_range H) h1
  rwa [hN.nPolar_nPolar hH] at h

theorem nPolar_eq_self_iff [CharP K 2] [FiniteDimensional K V] (hN : SingularImage Q N)
    {ℓ H : Submodule K V} (hℓ : ℓ ≤ LinearMap.range N) (hℓ1 : finrank K ℓ = 1)
    (hH : H ≤ LinearMap.range N) (hH2 : finrank K H = 2)
    (hX : finrank K (LinearMap.range N) = 4) (hℓH : ℓ ≤ H) :
    nPolar Q N H = H ↔ H ≤ nPolar Q N ℓ := by
  constructor
  · intro h
    rw [hN.le_nPolar_comm hℓ hH, h]
    exact hℓH
  · intro h
    obtain ⟨x, hxH, hxℓ⟩ : ∃ x ∈ H, x ∉ ℓ := by
      by_contra hc
      push Not at hc
      have := Submodule.finrank_mono (show H ≤ ℓ from hc)
      omega
    have hℓ'H : K ∙ x ≤ H := (span_singleton_le_iff_mem _ _).2 hxH
    have hℓ' : K ∙ x ≤ LinearMap.range N := hℓ'H.trans hH
    have hx0 : x ≠ 0 := fun h0 => hxℓ (h0 ▸ ℓ.zero_mem)
    have hℓ'1 : finrank K (K ∙ x) = 1 := finrank_span_singleton hx0
    have hsup : ℓ ⊔ K ∙ x = H := by
      refine eq_of_le_of_finrank_eq (sup_le hℓH hℓ'H) ?_
      rw [Submodule.finrank_sup_span_singleton hxℓ, hℓ1, hH2]
    have h2 : H ≤ nPolar Q N (K ∙ x) := by
      rw [← hsup]
      refine sup_le ?_ (hN.le_nPolar_of_finrank_one hℓ' hℓ'1)
      exact (hN.le_nPolar_comm hℓ' hℓ).2 (hℓ'H.trans h)
    have hle : H ≤ nPolar Q N H := by
      have h3 := le_inf h h2
      conv_rhs => rw [← hsup]
      exact h3.trans (hN.nPolar_inf_le hℓ hℓ')
    have hd := hN.finrank_nPolar hH
    exact (eq_of_le_of_finrank_eq hle (by omega)).symm

theorem map_eq_nPolar [FiniteDimensional K V] (hN : SingularImage Q N) {M : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) (hMd : finrank K M = finrank K (LinearMap.range N)) :
    M.map N = nPolar Q N (M ⊓ LinearMap.range N) := by
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q) (M ⊓ LinearMap.range N) =
      M ⊔ LinearMap.range N := by
    symm
    refine eq_of_le_of_finrank_eq (sup_le (fun m hm => mem_orth_iff.2 fun s hs =>
      polar_eq_zero_of_singular hM hs.1 hm) (fun x hx => mem_orth_iff.2 fun s hs =>
      hN.polar_eq_zero hs.2 hx)) ?_
    rw [LinearMap.BilinForm.finrank_orthogonal hN.nondeg]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq M (LinearMap.range N)
    have h2 := hN.finrank_eq
    omega
  have hX0 : (LinearMap.range N).map N = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_bot]
    exact (hN.apply_eq_zero_iff).2 hx
  rw [nPolar, horth, Submodule.map_sup, hX0, sup_bot_eq]

end SingularImage

theorem map_eq_self_iff_map_le [FiniteDimensional K V] {T : V ≃ₗ[K] V} {N : V →ₗ[K] V}
    (hTN : ∀ x, T x = x + N x) (P : Submodule K V) :
    P.map (T : V →ₗ[K] V) = P ↔ P.map N ≤ P := by
  constructor
  · intro h
    rintro _ ⟨m, hm, rfl⟩
    have hTm : T m ∈ P := by
      rw [← h]
      exact Submodule.mem_map_of_mem hm
    have := P.sub_mem hTm hm
    rwa [hTN, add_sub_cancel_left] at this
  · intro h
    refine eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq T P)
    rintro _ ⟨m, hm, rfl⟩
    rw [LinearEquiv.coe_coe, hTN]
    exact P.add_mem hm (h (Submodule.mem_map_of_mem hm))

theorem SingularImage.map_eq_self_iff [FiniteDimensional K V] (hN : SingularImage Q N)
    {T : V ≃ₗ[K] V} (hTN : ∀ x, T x = x + N x) {M : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) (hMd : finrank K M = finrank K (LinearMap.range N)) :
    M.map (T : V →ₗ[K] V) = M ↔
      nPolar Q N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N := by
  rw [map_eq_self_iff_map_le hTN, hN.map_eq_nPolar hM hMd]
  exact ⟨fun h => le_inf h (nPolar_le_range _), fun h => h.trans inf_le_left⟩

end Polarity

section Meet

variable {K : Type*} [Field K] [Finite K] {X : Submodule K (Fin 4 ⊕ Fin 4 → K)}

theorem card_containing_three {W : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hW : W ∈ singularSubspaces (quadPlus 4 K) 3) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ W ≤ M} = 2 := by
  have h := card_extensionsWith_singular (r := 4) (j := 3) (by norm_num) hW
  have hq : (1 : ℚ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  have hq1 : (Nat.card K : ℚ) - 1 ≠ 0 := by linarith
  have e : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ W ≤ M} =
      Nat.card (extensionsWith (fun X => ∀ x ∈ X, quadPlus 4 K x = 0) W 3) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M =>
      ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩)
  rw [e]
  have key : (Nat.card (extensionsWith (fun X => ∀ x ∈ X, quadPlus 4 K x = 0) W 3) : ℚ) = 2 := by
    rw [h, show (4 : ℕ) - 3 = 1 from rfl, show (4 : ℕ) - 3 - 1 = 0 from rfl, pow_one, pow_zero,
      div_eq_iff hq1]
    ring
  exact_mod_cast key

theorem card_containing_two {H : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hH : H ∈ singularSubspaces (quadPlus 4 K) 2) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M} = 2 * (Nat.card K + 1) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hA : Nat.card {W // W ∈ singularSubspaces (quadPlus 4 K) 3 ∧ H ≤ W} =
      (Nat.card K + 1) ^ 2 := by
    have h := card_extensionsWith_singular (r := 4) (j := 2) (by norm_num) hH
    have hq' : (1 : ℚ) < Nat.card K := by exact_mod_cast hq
    have hq1 : (Nat.card K : ℚ) - 1 ≠ 0 := by linarith
    have e : Nat.card {W // W ∈ singularSubspaces (quadPlus 4 K) 3 ∧ H ≤ W} =
        Nat.card (extensionsWith (fun X => ∀ x ∈ X, quadPlus 4 K x = 0) H 2) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun M =>
        ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩)
    rw [e]
    have key : (Nat.card (extensionsWith (fun X => ∀ x ∈ X, quadPlus 4 K x = 0) H 2) : ℚ) =
        ((Nat.card K : ℚ) + 1) ^ 2 := by
      rw [h, show (4 : ℕ) - 2 = 2 from rfl, show (4 : ℕ) - 2 - 1 = 1 from rfl, pow_one,
        div_eq_iff hq1]
      ring
    exact_mod_cast key
  have hinc := card_mul_eq_card_mul_of_rel
    (A := {W // W ∈ singularSubspaces (quadPlus 4 K) 3 ∧ H ≤ W})
    (B := {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M})
    (fun W M => W.1 ≤ M.1) (a := 2) (b := Nat.card K + 1)
    (fun W => by
      rw [← card_containing_three W.2.1]
      exact Nat.card_congr
        { toFun := fun M => ⟨M.1.1, M.1.2.1, M.2⟩
          invFun := fun M => ⟨⟨M.1, M.2.1, W.2.2.trans M.2.2⟩, M.2.2⟩
          left_inv := fun M => rfl
          right_inv := fun M => rfl })
    (fun M => by
      have h := card_between_two (U := H) (X := M.1) M.2.2 (by rw [M.2.1.1, hH.1])
      rw [hH.1] at h
      rw [← h]
      exact Nat.card_congr
        { toFun := fun W => ⟨W.1.1, W.1.2.2, W.2, W.1.2.1.1⟩
          invFun := fun W => ⟨⟨W.1, ⟨W.2.2.2, fun x hx => M.2.1.2 x (W.2.2.1 hx)⟩, W.2.1⟩,
            W.2.2.1⟩
          left_inv := fun W => rfl
          right_inv := fun W => rfl })
  rw [hA] at hinc
  have h' : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M} * (Nat.card K + 1) =
      2 * (Nat.card K + 1) * (Nat.card K + 1) := by
    rw [← hinc]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h'

variable (hX : X ∈ singularSubspaces (quadPlus 4 K) 4)
include hX

omit [Finite K] in
theorem card_inf_eq_top :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M ⊓ X = X} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨X, hX, inf_idem X⟩, fun M => Subtype.ext ?_⟩
  obtain ⟨M, hM, hMX⟩ := M
  have hXM : X ≤ M := inf_eq_right.1 hMX
  exact (eq_of_le_of_finrank_eq hXM (by rw [hM.1, hX.1])).symm

theorem card_inf_eq_three {H : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hHX : H ≤ X)
    (h3 : finrank K H = 3) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M ⊓ X = H} = 1 := by
  have hH : H ∈ singularSubspaces (quadPlus 4 K) 3 := ⟨h3, fun x hx => hX.2 x (hHX hx)⟩
  have h2 := card_containing_three hH
  have hrem := card_ne_add_one (p := fun M => M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M)
    (a := X) ⟨hX, hHX⟩
  rw [h2] at hrem
  have e : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M ⊓ X = H} =
      Nat.card {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M) ∧ M ≠ X} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ⟨fun ⟨hM, hMX⟩ => ?_,
      fun ⟨⟨hM, hHM⟩, hMX⟩ => ?_⟩)
    · refine ⟨⟨hM, hMX ▸ inf_le_left⟩, fun h => ?_⟩
      rw [h, inf_idem] at hMX
      rw [← hMX, hX.1] at h3
      exact absurd h3 (by norm_num)
    · refine ⟨hM, ?_⟩
      have hle : H ≤ M ⊓ X := le_inf hHM hHX
      have hd : finrank K (M ⊓ X : Submodule K (Fin 4 ⊕ Fin 4 → K)) ≤ 4 := by
        have := Submodule.finrank_mono (inf_le_right : M ⊓ X ≤ X)
        rwa [hX.1] at this
      have hd' := Submodule.finrank_mono hle
      rcases Nat.lt_or_ge (finrank K (M ⊓ X : Submodule K (Fin 4 ⊕ Fin 4 → K))) 4 with h | h
      · exact (eq_of_le_of_finrank_eq hle (by omega)).symm
      · exfalso
        have hMXX : M ⊓ X = X := eq_of_le_of_finrank_eq inf_le_right (by rw [hX.1]; omega)
        have hXM : X ≤ M := inf_eq_right.1 hMXX
        exact hMX (eq_of_le_of_finrank_eq hXM (by rw [hM.1, hX.1])).symm
  omega

theorem card_inf_eq_two {H : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hHX : H ≤ X)
    (h2 : finrank K H = 2) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M ⊓ X = H} = Nat.card K := by
  have hH : H ∈ singularSubspaces (quadPlus 4 K) 2 := ⟨h2, fun x hx => hX.2 x (hHX hx)⟩
  have hG := card_containing_two hH
  have hsplit := card_subtype_split (fun M => M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M)
    (fun M => M ⊓ X = H)
  have hmid : Nat.card {H' : Submodule K (Fin 4 ⊕ Fin 4 → K) // H' ≤ X ∧ H < H'} =
      Nat.card K + 2 := by
    have hb := card_between_two (U := H) (X := X) hHX (by rw [hX.1, h2])
    rw [h2] at hb
    have hHX' : H < X := lt_of_le_of_ne hHX fun h => by
      rw [h, hX.1] at h2
      exact absurd h2 (by norm_num)
    have hrem := card_ne_add_one (p := fun H' : Submodule K (Fin 4 ⊕ Fin 4 → K) =>
      H' ≤ X ∧ H < H') (a := X) ⟨le_rfl, hHX'⟩
    have e : Nat.card {H' : Submodule K (Fin 4 ⊕ Fin 4 → K) // (H' ≤ X ∧ H < H') ∧ H' ≠ X} =
        Nat.card {W : Submodule K (Fin 4 ⊕ Fin 4 → K) // H ≤ W ∧ W ≤ X ∧ finrank K W = 2 + 1} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun H' => ⟨fun ⟨⟨hH'X, hHH'⟩, hne⟩ => ?_,
        fun ⟨hHH', hH'X, hd⟩ => ?_⟩)
      · refine ⟨hHH'.le, hH'X, ?_⟩
        have h1 := Submodule.finrank_lt_finrank_of_lt hHH'
        have h3 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hH'X hne)
        rw [hX.1] at h3
        omega
      · refine ⟨⟨hH'X, lt_of_le_of_ne hHH' fun h => by rw [← h, h2] at hd; omega⟩, fun h => ?_⟩
        rw [h, hX.1] at hd
        omega
    omega
  have hrest : Nat.card {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M) ∧
      ¬M ⊓ X = H} = Nat.card K + 2 := by
    rw [← hmid]
    have hinc := card_mul_eq_card_mul_of_rel
      (A := {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M) ∧ ¬M ⊓ X = H})
      (B := {H' : Submodule K (Fin 4 ⊕ Fin 4 → K) // H' ≤ X ∧ H < H'})
      (fun M H' => M.1 ⊓ X = H'.1) (a := 1) (b := 1)
      (fun M => by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨⟨M.1 ⊓ X, inf_le_right, lt_of_le_of_ne (le_inf M.2.1.2 hHX)
          (Ne.symm M.2.2)⟩, rfl⟩, fun y => Subtype.ext (Subtype.ext y.2.symm)⟩)
      (fun H' => by
        have hd : finrank K H'.1 = 3 ∨ H'.1 = X := by
          have h1 := Submodule.finrank_lt_finrank_of_lt H'.2.2
          have h3 := Submodule.finrank_mono H'.2.1
          rw [hX.1] at h3
          rcases Nat.lt_or_ge (finrank K H'.1) 4 with h | h
          · left
            omega
          · right
            exact eq_of_le_of_finrank_eq H'.2.1 (by rw [hX.1]; omega)
        have hc : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M ⊓ X = H'.1} = 1 := by
          rcases hd with hd | hd
          · exact card_inf_eq_three hX H'.2.1 hd
          · rw [hd]
            exact card_inf_eq_top hX
        rw [← hc]
        exact Nat.card_congr
          { toFun := fun M => ⟨M.1.1, M.1.2.1.1, M.2⟩
            invFun := fun M => ⟨⟨M.1, ⟨M.2.1, H'.2.2.le.trans
              (M.2.2.symm.le.trans inf_le_left)⟩, by
              rw [M.2.2]
              exact (ne_of_lt H'.2.2).symm⟩, M.2.2⟩
            left_inv := fun M => rfl
            right_inv := fun M => rfl })
    simpa using hinc
  have hfirst : Nat.card {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ H ≤ M) ∧ M ⊓ X = H} =
      Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M ⊓ X = H} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M =>
      ⟨fun ⟨⟨hM, _⟩, hMX⟩ => ⟨hM, hMX⟩, fun ⟨hM, hMX⟩ => ⟨⟨hM, hMX ▸ inf_le_left⟩, hMX⟩⟩)
  rw [hG, hrest, hfirst] at hsplit
  omega

end Meet

section Elementary

variable {r : ℕ} {K : Type*} [Field K]

theorem exists_mem_elementary_blockUnip {C : Matrix (Fin r) (Fin r) K} (hC : C.transpose = -C)
    (hd : ∀ i, C i i = 0) :
    ∃ g ∈ orthElementaryGroup (quadPlus r K),
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = blockUnip C := by
  rw [eq_sum_of_alternating hC hd]
  refine Finset.sum_induction _ (fun C => ∃ g ∈ orthElementaryGroup (quadPlus r K),
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = blockUnip C)
    ?_ ?_ ?_
  · rintro a b ⟨g, hg, hga⟩ ⟨g', hg', hgb⟩
    exact ⟨g * g', mul_mem hg hg', by
      rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul, hga, hgb, blockUnip_add]⟩
  · exact ⟨1, one_mem _, by
      rw [blockUnip_zero, ← LinearMap.toMatrix'_id]
      rfl⟩
  · intro p hp
    have hp' : p.1 < p.2 := (Finset.mem_filter.1 hp).2
    exact ⟨_, eichler_mem_elementaryGroup _ _ _, (blockUnip_single hp'.ne _).symm⟩

theorem mem_elementary_of_fix_flag {T : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    (hfix : ∀ x ∈ flag r K r, T x = x) : T ∈ orthElementaryGroup (quadPlus r K) := by
  have hstab : T ∈ maxStab r K := by
    refine mem_maxStab.2 ⟨hT, le_antisymm ?_ fun x hx => ⟨x, hx, hfix x hx⟩⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, hfix x hx]
    exact hx
  obtain ⟨A, C, hC, hd, hM⟩ := exists_toMatrix'_of_mem_maxStab hstab
  have hA : (A : Matrix (Fin r) (Fin r) K) = 1 := by
    ext i j
    have h := congrFun (congrFun hM (Sum.inl i)) (Sum.inl j)
    rw [LinearMap.toMatrix'_apply, Matrix.fromBlocks_apply₁₁, LinearEquiv.coe_coe,
      hfix _ (mem_flag_top.2 fun k => by simp)] at h
    rw [← h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hA' : A = 1 := Units.ext hA
  subst hA'
  simp only [Units.val_one, inv_one, Matrix.one_mul, Matrix.transpose_one] at hM
  obtain ⟨g, hg, hgM⟩ := exists_mem_elementary_blockUnip hC hd
  have hTg : T = g := LinearEquiv.toLinearMap_injective
    (LinearMap.toMatrix'.injective (hM.trans hgM.symm))
  rw [hTg]
  exact hg

end Elementary

theorem eq_of_pred_mul_eq_pow_four {q n : ℕ} (hq : 1 < q) (h : (q - 1) * n = q ^ 4 - 1) :
    n = q ^ 3 + q ^ 2 + q + 1 := by
  have h1 : q ^ 4 - 1 = (q - 1) * (q ^ 3 + q ^ 2 + q + 1) := by
    have : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ q)]
    ring
  rw [h1] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem even_split_eight_singular_image_involution_fixed_counts {K : Type*} [Field K] [Finite K]
    [CharP K 2] {T : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)) (hT2 : T * T = 1)
    (hX : LinearMap.range ((T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) -
      LinearMap.id) ∈ singularSubspaces (quadPlus 4 K) 4) :
    T ∈ orthElementaryGroup (quadPlus 4 K) ∧ T ≠ 1 ∧
    Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
      L.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
      Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 ∧
    Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
      M.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
      2 * (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) + Nat.card K ^ 4 ∧
    ∀ M : Submodule K (Fin 4 ⊕ Fin 4 → K), M ∈ singularSubspaces (quadPlus 4 K) 4 ↔
      (∀ x ∈ M, quadPlus 4 K x = 0) ∧
        ∀ M', M ≤ M' → (∀ x ∈ M', quadPlus 4 K x = 0) → M' = M := by
  set N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) - LinearMap.id with hNdef
  have hQ : (polarBilin (quadPlus 4 K)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 K
  have hNx : ∀ x, N x = T x - x := fun x => rfl
  have hTN : ∀ x, T x = x + N x := fun x => by rw [hNx]; abel
  have hTT : ∀ x, T (T x) = x := fun x => by
    change (T * T) x = x
    rw [hT2]
    rfl
  have hNN : ∀ x, N (N x) = 0 := by
    intro x
    rw [hNx, hNx, map_sub, hTT]
    calc x - T x - (T x - x) = (2 : K) • (x - T x) := by module
      _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have hX4 : finrank K (LinearMap.range N) = 4 := hX.1
  have hker : LinearMap.ker N = LinearMap.range N := by
    have hle : LinearMap.range N ≤ LinearMap.ker N := by
      rintro _ ⟨x, rfl⟩
      exact hNN x
    have hrn := LinearMap.finrank_range_add_finrank_ker N
    rw [hX4, finrank_split] at hrn
    exact (eq_of_le_of_finrank_eq hle (by rw [hX4]; omega)).symm
  have hpolarself : ∀ x, polar (quadPlus 4 K) (N x) x = 0 := by
    intro x
    have h := map_of_mem hT x
    rw [hTN, QuadraticMap.map_add (quadPlus 4 K), hX.2 _ (LinearMap.mem_range_self N x),
      add_zero, add_eq_left, polar_comm] at h
    exact h
  have hN : SingularImage (quadPlus 4 K) N :=
    ⟨hQ, hX.2, hker, hpolarself, by rw [hX4, finrank_split]⟩
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hE : T ∈ orthElementaryGroup (quadPlus 4 K) := by
    obtain ⟨h, hh, hhX⟩ := exists_isometry_map_eq (le_refl 4) hX
    have hT' : h⁻¹ * T * h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
      mul_mem (mul_mem (inv_mem hh) hT) hh
    have hfix : ∀ x ∈ flag 4 K 4, (h⁻¹ * T * h) x = x := by
      intro x hx
      have hhx : h x ∈ LinearMap.range N := by
        rw [← hhX]
        exact Submodule.mem_map_of_mem hx
      have hNhx : N (h x) = 0 := by
        rw [← LinearMap.mem_ker, hker]
        exact hhx
      change h⁻¹ (T (h x)) = x
      rw [hTN, hNhx, add_zero, LinearEquiv.inv_apply_apply']
    have hE' := mem_elementary_of_fix_flag hT' hfix
    have hnorm := (orthogonal_elementary_normality (quadPlus 4 K)).2
    have hmem := hnorm.conj_mem ⟨h⁻¹ * T * h, hT'⟩ (Subgroup.mem_subgroupOf.2 hE') ⟨h, hh⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa [mul_assoc] using hmem
  have hT1 : T ≠ 1 := by
    intro h1
    have hN0 : N = 0 := LinearMap.ext fun x => by
      rw [hNx, h1]
      exact sub_self x
    have h0 : finrank K (LinearMap.range N) = 0 := by
      rw [hN0, LinearMap.range_zero, finrank_bot]
    omega
  have hlines : ∀ L : Submodule K (Fin 4 ⊕ Fin 4 → K), L ∈ singularSubspaces (quadPlus 4 K) 1 →
      (L.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L ↔
        L ≤ LinearMap.range N) := by
    intro L hL
    constructor
    · intro hTL
      obtain ⟨x, hxL, hx0⟩ := exists_ne_zero_of_one_le_finrank (T := L) (by rw [hL.1])
      have hspan := span_singleton_eq_of_mem hL.1 hxL hx0
      have hTx : T x ∈ L := by
        rw [← hTL]
        exact Submodule.mem_map_of_mem hxL
      rw [← hspan] at hTx
      obtain ⟨c, hc⟩ := mem_span_singleton.1 hTx
      have hc1 : c = 1 := by
        have h1 := hTT x
        rw [← hc, map_smul, ← hc, smul_smul] at h1
        have h2 : (c * c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
        have h3 : c * c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hx0)
        exact eq_of_sq_eq_sq_charTwo (by rw [pow_two, h3, one_pow])
      rw [hc1, one_smul] at hc
      have hNx0 : N x = 0 := by rw [hNx, ← hc, sub_self]
      rw [← hspan, span_singleton_le_iff_mem, ← hker]
      exact hNx0
    · intro hLX
      refine (map_eq_self_iff_map_le hTN L).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      have h0 : N x = 0 := by
        rw [← LinearMap.mem_ker, hker]
        exact hLX hx
      rw [h0]
      exact L.zero_mem
  have hcard1 : Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
      L.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
      Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 := by
    have h := card_lines_le_mul (Q := quadPlus 4 K) hX.2
    rw [hX4] at h
    have e : Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
        Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ LinearMap.range N} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun L =>
        ⟨fun ⟨hL, h⟩ => ⟨hL, (hlines L hL).1 h⟩, fun ⟨hL, h⟩ => ⟨hL, (hlines L hL).2 h⟩⟩)
    rw [e]
    exact eq_of_pred_mul_eq_pow_four hq1 h
  have hlinesX : Nat.card {ℓ : Submodule K (Fin 4 ⊕ Fin 4 → K) //
      ℓ ≤ LinearMap.range N ∧ finrank K ℓ = 1} =
      Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 := by
    have h := card_lines_mul (LinearMap.range N)
    rw [hX4, mul_comm] at h
    exact eq_of_pred_mul_eq_pow_four hq1 h
  have hhyp : Nat.card {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
      H ≤ LinearMap.range N ∧ finrank K H = 3} =
      Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 := by
    rw [← hlinesX]
    refine Nat.card_congr
      { toFun := fun H => ⟨nPolar (quadPlus 4 K) N H.1, nPolar_le_range _, by
          have := hN.finrank_nPolar H.2.1
          omega⟩
        invFun := fun ℓ => ⟨nPolar (quadPlus 4 K) N ℓ.1, nPolar_le_range _, by
          have := hN.finrank_nPolar ℓ.2.1
          omega⟩
        left_inv := fun H => Subtype.ext (hN.nPolar_nPolar H.2.1)
        right_inv := fun ℓ => Subtype.ext (hN.nPolar_nPolar ℓ.2.1) }
  have hgood : Nat.card {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
      H ≤ LinearMap.range N ∧ finrank K H = 2 ∧ nPolar (quadPlus 4 K) N H = H} =
      Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 := by
    have hinc := card_mul_eq_card_mul_of_rel
      (A := {ℓ : Submodule K (Fin 4 ⊕ Fin 4 → K) // ℓ ≤ LinearMap.range N ∧ finrank K ℓ = 1})
      (B := {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
        H ≤ LinearMap.range N ∧ finrank K H = 2 ∧ nPolar (quadPlus 4 K) N H = H})
      (fun ℓ H => ℓ.1 ≤ H.1) (a := Nat.card K + 1) (b := Nat.card K + 1)
      (fun ℓ => by
        have hP3 : finrank K (nPolar (quadPlus 4 K) N ℓ.1) = 3 := by
          have := hN.finrank_nPolar ℓ.2.1
          omega
        have h := card_between_two (U := ℓ.1) (X := nPolar (quadPlus 4 K) N ℓ.1)
          (hN.le_nPolar_of_finrank_one ℓ.2.1 ℓ.2.2) (by rw [hP3, ℓ.2.2])
        rw [← h, ℓ.2.2]
        exact Nat.card_congr
          { toFun := fun H => ⟨H.1.1, H.2, (hN.nPolar_eq_self_iff ℓ.2.1 ℓ.2.2 H.1.2.1 H.1.2.2.1
              hX4 H.2).1 H.1.2.2.2, H.1.2.2.1⟩
            invFun := fun H => ⟨⟨H.1, H.2.2.1.trans (nPolar_le_range _), H.2.2.2,
              (hN.nPolar_eq_self_iff ℓ.2.1 ℓ.2.2 (H.2.2.1.trans (nPolar_le_range _))
                H.2.2.2 hX4 H.2.1).2 H.2.2.1⟩, H.2.1⟩
            left_inv := fun H => rfl
            right_inv := fun H => rfl })
      (fun H => by
        have h := card_between_two (U := ⊥) (X := H.1) bot_le (by rw [finrank_bot, H.2.2.1])
        rw [finrank_bot, zero_add] at h
        rw [← h]
        exact Nat.card_congr
          { toFun := fun ℓ => ⟨ℓ.1.1, bot_le, ℓ.2, ℓ.1.2.2⟩
            invFun := fun ℓ => ⟨⟨ℓ.1, ℓ.2.2.1.trans H.2.1, ℓ.2.2.2⟩, ℓ.2.2.1⟩
            left_inv := fun ℓ => rfl
            right_inv := fun ℓ => rfl })
    rw [hlinesX] at hinc
    exact (Nat.eq_of_mul_eq_mul_right (by omega) hinc).symm
  have hinv : ∀ M ∈ singularSubspaces (quadPlus 4 K) 4,
      (M.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M ↔
        nPolar (quadPlus 4 K) N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N) :=
    fun M hM => hN.map_eq_self_iff hTN hM.2 (by rw [hM.1, hX4])
  have hdimH : ∀ M : Submodule K (Fin 4 ⊕ Fin 4 → K),
      finrank K (M ⊓ LinearMap.range N : Submodule K _) ≤ 4 := fun M => by
    have := Submodule.finrank_mono (inf_le_right : M ⊓ LinearMap.range N ≤ LinearMap.range N)
    rwa [hX4] at this
  have hcard4 : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
      M.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
      2 * (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) + Nat.card K ^ 4 := by
    have e : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
          nPolar (quadPlus 4 K) N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun M =>
        ⟨fun ⟨hM, h⟩ => ⟨hM, (hinv M hM).1 h⟩, fun ⟨hM, h⟩ => ⟨hM, (hinv M hM).2 h⟩⟩)
    rw [e, card_subtype_split _ (fun M => finrank K (M ⊓ LinearMap.range N : Submodule K _) = 2)]
    have h2 : Nat.card {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        nPolar (quadPlus 4 K) N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N) ∧
        finrank K (M ⊓ LinearMap.range N : Submodule K _) = 2} =
        Nat.card K * (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) := by
      have hinc := card_mul_eq_card_mul_of_rel
        (A := {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
          nPolar (quadPlus 4 K) N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N) ∧
          finrank K (M ⊓ LinearMap.range N : Submodule K _) = 2})
        (B := {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
          H ≤ LinearMap.range N ∧ finrank K H = 2 ∧ nPolar (quadPlus 4 K) N H = H})
        (fun M H => M.1 ⊓ LinearMap.range N = H.1) (a := 1) (b := Nat.card K)
        (fun M => by
          rw [Nat.card_eq_one_iff_exists]
          have hd := hN.finrank_nPolar (inf_le_right : M.1 ⊓ LinearMap.range N ≤ _)
          refine ⟨⟨⟨M.1 ⊓ LinearMap.range N, inf_le_right, M.2.2,
            (eq_of_le_of_finrank_eq M.2.1.2 (by omega))⟩, rfl⟩,
            fun y => Subtype.ext (Subtype.ext y.2.symm)⟩)
        (fun H => by
          rw [← card_inf_eq_two hX H.2.1 H.2.2.1]
          exact Nat.card_congr
            { toFun := fun M => ⟨M.1.1, M.1.2.1.1, M.2⟩
              invFun := fun M => ⟨⟨M.1, ⟨M.2.1, by rw [M.2.2, H.2.2.2]⟩, by
                rw [M.2.2, H.2.2.1]⟩, M.2.2⟩
              left_inv := fun M => rfl
              right_inv := fun M => rfl })
      rw [hgood, mul_one] at hinc
      rw [hinc, mul_comm]
    have h3 : Nat.card {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        nPolar (quadPlus 4 K) N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N) ∧
        ¬finrank K (M ⊓ LinearMap.range N : Submodule K _) = 2} =
        Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 + 1 := by
      have hbig : Nat.card {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
          H ≤ LinearMap.range N ∧ 3 ≤ finrank K H} =
          Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1 + 1 := by
        have hrem := card_ne_add_one (p := fun H : Submodule K (Fin 4 ⊕ Fin 4 → K) =>
          H ≤ LinearMap.range N ∧ 3 ≤ finrank K H) (a := LinearMap.range N)
          ⟨le_rfl, by rw [hX4]; omega⟩
        have e : Nat.card {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
            (H ≤ LinearMap.range N ∧ 3 ≤ finrank K H) ∧ H ≠ LinearMap.range N} =
            Nat.card {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
              H ≤ LinearMap.range N ∧ finrank K H = 3} := by
          refine Nat.card_congr (Equiv.subtypeEquivRight fun H =>
            ⟨fun ⟨⟨hHX, hd⟩, hne⟩ => ?_, fun ⟨hHX, hd⟩ => ⟨⟨hHX, by omega⟩, fun h => by
              rw [h, hX4] at hd
              omega⟩⟩)
          refine ⟨hHX, ?_⟩
          have h4 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hHX hne)
          rw [hX4] at h4
          omega
        omega
      rw [← hbig]
      have hinc := card_mul_eq_card_mul_of_rel
        (A := {M // (M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
          nPolar (quadPlus 4 K) N (M ⊓ LinearMap.range N) ≤ M ⊓ LinearMap.range N) ∧
          ¬finrank K (M ⊓ LinearMap.range N : Submodule K _) = 2})
        (B := {H : Submodule K (Fin 4 ⊕ Fin 4 → K) //
          H ≤ LinearMap.range N ∧ 3 ≤ finrank K H})
        (fun M H => M.1 ⊓ LinearMap.range N = H.1) (a := 1) (b := 1)
        (fun M => by
          rw [Nat.card_eq_one_iff_exists]
          have hd := hN.finrank_nPolar (inf_le_right : M.1 ⊓ LinearMap.range N ≤ _)
          have hle := Submodule.finrank_mono M.2.1.2
          refine ⟨⟨⟨M.1 ⊓ LinearMap.range N, inf_le_right, by have := M.2.2; omega⟩, rfl⟩,
            fun y => Subtype.ext (Subtype.ext y.2.symm)⟩)
        (fun H => by
          have hd4 := hdimH H.1
          have hle4 := Submodule.finrank_mono H.2.1
          rw [hX4] at hle4
          have hc : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
              M ⊓ LinearMap.range N = H.1} = 1 := by
            rcases Nat.lt_or_ge (finrank K H.1) 4 with h | h
            · exact card_inf_eq_three hX H.2.1 (by have := H.2.2; omega)
            · have hHX : H.1 = LinearMap.range N :=
                eq_of_le_of_finrank_eq H.2.1 (by rw [hX4]; omega)
              rw [hHX]
              exact card_inf_eq_top hX
          have hpol : nPolar (quadPlus 4 K) N H.1 ≤ H.1 := by
            rcases Nat.lt_or_ge (finrank K H.1) 4 with h | h
            · exact hN.nPolar_le_of_codim_one H.2.1 (by rw [hX4]; have := H.2.2; omega)
            · have := hN.finrank_nPolar H.2.1
              have h0 : nPolar (quadPlus 4 K) N H.1 = ⊥ :=
                Submodule.finrank_eq_zero.1 (by omega)
              rw [h0]
              exact bot_le
          rw [← hc]
          exact Nat.card_congr
            { toFun := fun M => ⟨M.1.1, M.1.2.1.1, M.2⟩
              invFun := fun M => ⟨⟨M.1, ⟨M.2.1, by rw [M.2.2]; exact hpol⟩, by
                  rw [M.2.2]
                  have := H.2.2
                  omega⟩, M.2.2⟩
              left_inv := fun M => rfl
              right_inv := fun M => rfl })
      simpa using hinc
    rw [h2, h3]
    ring
  exact ⟨hE, hT1, hcard1, hcard4, fun M => mem_singularSubspaces_iff_maximal⟩

end CFSG.ComponentClassification.UnbalancedCatalog
