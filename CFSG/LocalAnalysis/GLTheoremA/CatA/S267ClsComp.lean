module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}
variable (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) [Finite A]
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0) (hρ : IsIsomRep β ρ)
variable {𝒮 : Set (V →+ V)}

include hp hA hpK hρ

theorem exists_supported_element (hmax : IsMaxElem β ρ p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (ρ a v) = ρ a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, s v ∈ weightFamily (p := p) ρ i)
    (S : Finset (Hyperplane A p)) (hS : ∀ H ∈ S, weightSpace ρ H.1 ≠ ⊥) :
    ∃ x : A, (∀ H ∈ S, x ∉ H.1) ∧
      ∀ H' : Hyperplane A p, H' ∉ S → weightSpace ρ H'.1 ≠ ⊥ → x ∈ H'.1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun H hH => absurd hH (Finset.notMem_empty H), fun H' _ _ => H'.1.one_mem⟩
  | insert H S hHS ih =>
    obtain ⟨x, hx, hx'⟩ := ih fun H' h => hS H' (Finset.mem_insert_of_mem h)
    obtain ⟨a, haH, ha⟩ := exists_split β ρ hp hA hpK hρ hmax h𝒮 h𝒮W H
      (hS H (Finset.mem_insert_self H S))
    refine ⟨x * a, fun H'' hH'' => ?_, fun H' hH' hne => ?_⟩
    · rcases Finset.mem_insert.mp hH'' with heq | hmem
      · rw [heq]
        intro hxa
        have hxH : x ∈ H.1 := hx' H hHS (hS H (Finset.mem_insert_self H S))
        exact haH (by simpa using H.1.mul_mem (H.1.inv_mem hxH) hxa)
      · intro hxa
        have haH'' : a ∈ H''.1 := ha H'' (fun h => hHS (h ▸ hmem)) (hS H''
          (Finset.mem_insert_of_mem hmem))
        exact hx H'' hmem (by simpa using H''.1.mul_mem hxa (H''.1.inv_mem haH''))
    · have hH'S : H' ∉ S := fun h => hH' (Finset.mem_insert_of_mem h)
      have hH'H : H' ≠ H := fun h => hH' (h ▸ Finset.mem_insert_self H S)
      exact H'.1.mul_mem (hx' H' hH'S hne) (ha H' hH'H hne)

omit hρ in
theorem apply_eq_self_iff_of_supported {S : Finset (Hyperplane A p)} {x : A}
    (hx : ∀ H ∈ S, x ∉ H.1)
    (hx' : ∀ H' : Hyperplane A p, H' ∉ S → weightSpace ρ H'.1 ≠ ⊥ → x ∈ H'.1) (v : V) :
    ρ x v = v ↔ ∀ H ∈ S, ρ.asAlgebraHom (eps K A p (some H)) v = 0 := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  constructor
  · intro hv H hH
    refine eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK (hx H hH) ⟨v, rfl⟩ ?_
    rw [apply_asAlgebraHom_comm, hv]
  · intro h0
    conv_lhs => rw [← sum_eps_apply ρ hp hA hpK v, map_sum]
    conv_rhs => rw [← sum_eps_apply ρ hp hA hpK v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases i with _ | H
    · exact apply_asAlgebraHom_eSub ρ (Subgroup.mem_top x) v
    · by_cases hH : H ∈ S
      · rw [h0 H hH, map_zero]
      · by_cases hbot : weightSpace ρ H.1 = ⊥
        · have h1 : ρ.asAlgebraHom (eps K A p (some H)) v = 0 := by
            have hmem : ρ.asAlgebraHom (eps K A p (some H)) v ∈ weightSpace ρ H.1 := ⟨v, rfl⟩
            rw [hbot, Submodule.mem_bot] at hmem
            exact hmem
          rw [h1, map_zero]
        · exact apply_eq_of_mem_weightSpace ρ (hx' H hH hbot) ⟨v, rfl⟩

theorem card_biInf_sdiff [DecidableEq (Hyperplane A p)] (hmax : IsMaxElem β ρ p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (ρ a v) = ρ a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, s v ∈ weightFamily (p := p) ρ i)
    (hinj : Function.Injective ρ) (T : Finset (Hyperplane A p))
    (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) {S : Finset (Hyperplane A p)}
    (hST : S ⊆ T) : Nat.card ↥(⨅ H ∈ T \ S, H.1) = p ^ S.card := by
  have hA' := card_eq_pow_support β ρ hp hA hpK hρ hmax h𝒮 h𝒮W hinj T hT
  have hidx := index_biInf_eq β ρ hp hA hpK hρ hmax h𝒮 h𝒮W (T \ S)
    (fun H hH => (hT H).mp (Finset.mem_sdiff.mp hH).1)
  have h := Subgroup.card_mul_index (⨅ H ∈ T \ S, H.1)
  rw [hidx, hA', Finset.card_sdiff_of_subset hST] at h
  have hle : S.card ≤ T.card := Finset.card_le_card hST
  have hpos : 0 < p ^ (T.card - S.card) := pow_pos hp.pos _
  have hsplit : p ^ T.card = p ^ S.card * p ^ (T.card - S.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [hsplit] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

omit hρ in
@[expose] def fixGL (W : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ w ∈ W, g w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g h} hg hh w hw => by rw [LinearEquiv.mul_apply, hh w hw, hg w hw]
  inv_mem' := fun {g} hg w hw => by
    rw [LinearEquiv.coe_inv]
    exact (LinearEquiv.symm_apply_eq g).mpr (hg w hw).symm

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
