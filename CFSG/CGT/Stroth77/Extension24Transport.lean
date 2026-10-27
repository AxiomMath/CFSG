module

public import CFSG.CGT.Stroth77.Extension22FourC4

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S}

section Transport

variable {k : Fin 3 → ℕ} (E : Torus k ≃+ Additive C)

@[expose] noncomputable def conjTorusIdx4 {g : S} (hg : g ∈ Subgroup.normalizer C) :
    Torus k →+ Torus k :=
  E.symm.toAddMonoidHom.comp ((conjAddHom hg).comp E.toAddMonoidHom)

theorem conjTorusIdx4_apply {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus k) :
    conjTorusIdx4 E hg x = E.symm (Additive.ofMul (conjBy hg (Additive.toMul (E x)))) := rfl

theorem conjTorusIdx4_apply_symm {g : S} (hg : g ∈ Subgroup.normalizer C) (y : C) :
    conjTorusIdx4 E hg (E.symm (Additive.ofMul y)) = E.symm (Additive.ofMul (conjBy hg y)) := by
  rw [conjTorusIdx4_apply, AddEquiv.apply_symm_apply]
  rfl

theorem conjTorusIdx4_mul {g h : S} (hg : g ∈ Subgroup.normalizer C)
    (hh : h ∈ Subgroup.normalizer C) :
    conjTorusIdx4 E (Subgroup.mul_mem _ hg hh) = (conjTorusIdx4 E hh).comp (conjTorusIdx4 E hg) :=
        by
  refine AddMonoidHom.ext fun x => ?_
  simp only [AddMonoidHom.comp_apply, conjTorusIdx4_apply, AddEquiv.apply_symm_apply]
  congr 2
  exact DFunLike.congr_fun (conjByHom_mul g h hg hh) (Additive.toMul (E x))

theorem conjTorusIdx4_congr {g g' : S} (hg : g ∈ Subgroup.normalizer C)
    (hg' : g' ∈ Subgroup.normalizer C) (h : g = g') :
    conjTorusIdx4 E hg = conjTorusIdx4 E hg' := by
  subst h
  rfl

theorem conjTorusIdx4_one :
    conjTorusIdx4 E (Subgroup.one_mem _ : (1 : S) ∈ Subgroup.normalizer C) =
      AddMonoidHom.id (Torus k) := by
  refine AddMonoidHom.ext fun x => ?_
  rw [conjTorusIdx4_apply]
  simp [conjBy]

theorem conjTorusIdx4_rels {τ : StrothTypeIndex} (D : StrothTypeData B τ)
    (hL : D.L ≤ Subgroup.normalizer C) :
    SigmaFourRels (conjTorusIdx4 E (hL D.uv_mem_L)) (conjTorusIdx4 E (hL D.t_mem_L))
      (conjTorusIdx4 E (hL D.u_mem_L)) (conjTorusIdx4 E (hL D.ρ_mem_L)) := by
  have huv := hL D.uv_mem_L
  have ht := hL D.t_mem_L
  have hu := hL D.u_mem_L
  have hρ := hL D.ρ_mem_L
  have H {a b : S} (ha : a ∈ Subgroup.normalizer C) (hb : b ∈ Subgroup.normalizer C)
      (h : a = b) : conjTorusIdx4 E ha = conjTorusIdx4 E hb :=
    conjTorusIdx4_congr E ha hb h
  have Hone {a : S} (ha : a ∈ Subgroup.normalizer C) (h : a = 1) :
      conjTorusIdx4 E ha = AddMonoidHom.id _ := by
    rw [H ha (Subgroup.one_mem _) h]
    exact conjTorusIdx4_one E
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← conjTorusIdx4_mul E huv huv]
    exact Hone _ D.uv_sq
  · rw [← conjTorusIdx4_mul E ht ht]
    exact Hone _ D.t_sq
  · rw [← conjTorusIdx4_mul E huv ht, ← conjTorusIdx4_mul E ht huv]
    exact H _ _ D.uv_comm_t
  · rw [← conjTorusIdx4_mul E hρ hρ, ← conjTorusIdx4_mul E (Subgroup.mul_mem _ hρ hρ) hρ]
    exact Hone _ D.rho_cube
  · rw [← conjTorusIdx4_mul E hu hu]
    exact Hone _ D.u_sq
  · rw [← conjTorusIdx4_mul E hu hρ, ← conjTorusIdx4_mul E (Subgroup.mul_mem _ hu hρ) hu,
      ← conjTorusIdx4_mul E (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hρ) hu) hρ]
    exact Hone _ D.u_rho
  · rw [← conjTorusIdx4_mul E huv hρ, ← conjTorusIdx4_mul E hρ ht]
    exact H _ _ D.uv_rho
  · rw [← conjTorusIdx4_mul E ht hρ, ← conjTorusIdx4_mul E hρ huv,
      ← conjTorusIdx4_mul E (Subgroup.mul_mem _ hρ huv) ht]
    exact H _ _ D.t_rho
  · rw [← conjTorusIdx4_mul E huv hu, ← conjTorusIdx4_mul E hu huv]
    exact H _ _ D.uv_comm_u
  · rw [← conjTorusIdx4_mul E ht hu, ← conjTorusIdx4_mul E hu huv,
      ← conjTorusIdx4_mul E (Subgroup.mul_mem _ hu huv) ht]
    exact H _ _ D.t_u

end Transport

theorem exists_torusEquiv_Idx4 {k : Fin 3 → ℕ} (hcomm : ∀ x y : C, x * y = y * x)
    (x : Fin 3 → C) (hx : ∀ i, x i ^ (2 ^ k i) = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hcard : Nat.card (Torus k) = Nat.card C) :
    ∃ E : Torus k ≃+ Additive C, ∀ i, E (gen k i) = Additive.ofMul (x i) := by
  classical
  letI : CommGroup C := { mul_comm := hcomm }
  let y : (i : Fin 3) → Additive C := fun i => Additive.ofMul (x i)
  have hy : ∀ i, (2 ^ k i) • y i = 0 := by
    intro i
    change (2 ^ k i) • Additive.ofMul (x i) = 0
    rw [← ofMul_pow, hx i]
    rfl
  let F : Torus k →+ Additive C := torusHomOfGens k y hy
  have hFgen : ∀ i : Fin 3, F (gen k i) = y i := fun i => torusHomOfGens_gen y hy i
  have hsurj : Function.Surjective F := by
    have hle : Subgroup.closure (Set.range x) ≤ F.range.toSubgroup' := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_toSubgroup']
      exact ⟨gen k i, hFgen i⟩
    intro z
    have hz : Additive.toMul z ∈ F.range.toSubgroup' := by
      apply hle
      rw [hgen]
      exact Subgroup.mem_top _
    rw [AddSubgroup.mem_toSubgroup'] at hz
    exact hz
  have hcardT : Nat.card (Torus k) = Nat.card (Additive C) := by
    rw [hcard]
    exact (Nat.card_congr Additive.ofMul).symm
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le (le_of_eq hcardT)
  exact ⟨AddEquiv.ofBijective F hbij, fun i => hFgen i⟩

end CFSG.CGT.Stroth77
