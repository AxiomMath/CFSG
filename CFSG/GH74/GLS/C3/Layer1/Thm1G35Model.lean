module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G35

abbrev D8 : Type := DihedralGroup 4

abbrev Z2 : Type := Multiplicative (ZMod 2)

theorem z2_mul_ne_one : ∀ q q' : Z2, q ≠ 1 → q' ≠ 1 → q * q' = 1 := by decide

@[expose] def swapHom : Z2 →* MulAut (D8 × D8) where
  toFun q := if q = 1 then 1 else MulEquiv.prodComm
  map_one' := by simp
  map_mul' q q' := by
    have key : (MulEquiv.prodComm : D8 × D8 ≃* D8 × D8) * MulEquiv.prodComm = 1 := by
      ext ⟨a, b⟩ <;> rfl
    by_cases hq : q = 1 <;> by_cases hq' : q' = 1
    · simp [hq, hq']
    · simp [hq, hq']
    · simp [hq, hq']
    · simp only [hq, hq', ite_false]
      rw [z2_mul_ne_one q q' hq hq']
      simp [key]

abbrev M35 : Type := (D8 × D8) ⋊[swapHom] Z2

instance : DecidableEq M35 := fun a b =>
  decidable_of_iff (SemidirectProduct.equivProd a = SemidirectProduct.equivProd b)
    (SemidirectProduct.equivProd (N := D8 × D8) (G := Z2) (φ := swapHom)).injective.eq_iff

instance : Fintype M35 :=
  Fintype.ofEquiv _ (SemidirectProduct.equivProd (N := D8 × D8) (G := Z2) (φ := swapHom)).symm

@[expose] def inl' (u v : D8) : M35 := ⟨(u, v), 1⟩

@[expose] def topg : M35 := ⟨1, Multiplicative.ofAdd 1⟩

theorem topg_conj_inl' : ∀ u v : D8, topg * inl' u v * topg⁻¹ = inl' v u := by decide +kernel

@[expose] def Vsub : Subgroup M35 := SemidirectProduct.rightHom.ker

theorem exists_inl'_of_mem_Vsub {m : M35} (hm : m ∈ Vsub) : ∃ u v, m = inl' u v := by
  obtain ⟨⟨u, v⟩, q⟩ := m
  have hq : q = 1 := hm
  subst hq
  exact ⟨u, v, rfl⟩

@[expose] def alphaFn : D8 → Z2
  | .r _ => 1
  | .sr _ => Multiplicative.ofAdd 1

theorem alpha_mul : ∀ a b : D8, alphaFn (a * b) = alphaFn a * alphaFn b := by decide

@[expose] def alpha : D8 →* Z2 := MonoidHom.mk' alphaFn alpha_mul

@[expose] def lamV : D8 × D8 →* Z2 :=
  (alpha.comp (MonoidHom.fst _ _)) * (alpha.comp (MonoidHom.snd _ _))

theorem lamV_swap (g : Z2) : lamV.comp (MulEquiv.toMonoidHom (swapHom g)) =
    (MulEquiv.toMonoidHom (MulAut.conj ((1 : Z2 →* Z2) g))).comp lamV := by
  ext ⟨a, b⟩
  by_cases hg : g = 1
  · simp [swapHom, hg]
  · simp [swapHom, hg, lamV, mul_comm]

@[expose] def lam : M35 →* Z2 := SemidirectProduct.lift lamV 1 lamV_swap

theorem lam_inl' (u v : D8) : lam (inl' u v) = alphaFn u * alphaFn v := by
  simp [lam, inl', SemidirectProduct.lift, lamV, alpha]

theorem z2_cases : ∀ q : Z2, q = 1 ∨ q = Multiplicative.ofAdd 1 := by decide

theorem lam_surjective : Function.Surjective lam := by
  intro q
  rcases z2_cases q with rfl | rfl
  · exact ⟨1, map_one lam⟩
  · refine ⟨inl' (DihedralGroup.sr 0) 1, ?_⟩
    rw [lam_inl']
    decide

@[expose, irreducible] def cent (m : M35) : Finset M35 := Finset.univ.filter (fun c => c * m = m * c)

@[expose, irreducible] def zc (m : M35) : Finset M35 :=
  (cent m).filter (fun z => ∀ c ∈ cent m, z * c = c * z)

theorem MC : ∀ m : M35, lam m = 1 → m * m = 1 → 32 ≤ (cent m).card → (zc m).card < 8 := by
  decide +kernel

theorem cent_x : ∀ s : D8, alphaFn s = Multiplicative.ofAdd 1 → (cent (inl' s 1)).card = 32 := by
  decide +kernel

theorem zc_x : ∀ s : D8, alphaFn s = Multiplicative.ofAdd 1 → (zc (inl' s 1)).card = 8 := by
  decide +kernel

theorem inl'_refl_sq : ∀ s : D8, alphaFn s = Multiplicative.ofAdd 1 → inl' s 1 * inl' s 1 = 1 := by
  decide +kernel

theorem inl'_f_sq : inl' (DihedralGroup.r 2) 1 * inl' (DihedralGroup.r 2) 1 = 1 := by decide +kernel

theorem cent_f : (cent (inl' (DihedralGroup.r 2) 1)).card = 64 := by decide +kernel

theorem big_inv : ∀ m : M35, m * m = 1 → (cent m).card = 64 →
    m = inl' (DihedralGroup.r 2) 1 ∨ m = inl' 1 (DihedralGroup.r 2) := by decide +kernel

end CFSG.GH74.GLS.C3.Layer1.Thm1G35

end
