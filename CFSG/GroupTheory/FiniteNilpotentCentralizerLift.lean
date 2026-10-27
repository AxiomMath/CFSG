module

public import CFSG.GroupTheory.FiniteNilpotentExtension

public section

namespace CFSG.GroupTheory

universe u v

private theorem bijective_pow_of_mulEquiv'
    {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {n : ℕ} (h : Function.Bijective (fun a : A => a ^ n)) :
    Function.Bijective (fun b : B => b ^ n) := by
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply h.1
    apply e.injective
    simpa using hxy
  · intro y
    obtain ⟨a, ha⟩ := h.2 (e.symm y)
    refine ⟨e a, ?_⟩
    change (e a) ^ n = y
    have ha' : a ^ n = e.symm y := by simpa using ha
    rw [← map_pow e a n, ha', e.apply_symm_apply]

theorem exists_finite_section_centralizer_surjective
    {E A : Type*} [Group E] [CommGroup A]
    (π : E →* A) (hπ : Function.Surjective π)
    {F : Subgroup A} [Finite F]
    [Group.IsNilpotent π.ker]
    (hdiv : Function.Bijective (fun k : π.ker => k ^ Nat.card F)) :
    ∃ (s : F →* E) (L : Subgroup E),
      (∀ f : F, π (s f) = (f : A)) ∧
      Function.Injective s ∧
      L = s.range ∧
      Finite L ∧
      Subgroup.map π (Subgroup.centralizer (L : Set E)) = ⊤ := by
  classical
  let EF : Subgroup E := F.comap π
  have hK_le_EF : π.ker ≤ EF := by
    intro k hk
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.mp hk]
    exact F.one_mem
  let πF : EF →* F :=
    { toFun := fun x =>
        ⟨π (x : E), by simpa only [EF, Subgroup.mem_comap] using x.2⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp }
  have hπF : Function.Surjective πF := by
    intro f
    obtain ⟨e, he⟩ := hπ (f : A)
    have heF : e ∈ EF := by
      rw [Subgroup.mem_comap]
      exact he ▸ f.2
    exact ⟨⟨e, heF⟩, Subtype.ext he⟩
  have hkerF : πF.ker = π.ker.subgroupOf EF := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : π (x : E) = 1 := congrArg Subtype.val hx
      simpa only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] using hx'
    · intro hx
      have hx' : π (x : E) = 1 := by
        simpa only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] using hx
      rw [MonoidHom.mem_ker]
      exact Subtype.ext hx' 
  let eK : πF.ker ≃* π.ker :=
    (MulEquiv.subgroupCongr hkerF).trans (Subgroup.subgroupOfEquivOfLe hK_le_EF)
  have hNilF : Group.IsNilpotent πF.ker :=
    Group.nilpotent_of_mulEquiv eK.symm
  have hdivF : Function.Bijective (fun k : πF.ker => k ^ Nat.card F) :=
    bijective_pow_of_mulEquiv' eK.symm hdiv
  let nNilF : Group.IsNilpotent πF.ker := hNilF
  obtain ⟨sF, hsF⟩ :=
    exists_section_of_finite_nilpotent_extension πF hπF hdivF
  let s : F →* E := EF.subtype.comp sF
  have hs : ∀ f : F, π (s f) = (f : A) := by
    intro f
    have h := congrArg Subtype.val (DFunLike.congr_fun hsF f)
    have h' : π ((sF f : EF) : E) = (f : A) := by
      simpa [πF, MonoidHom.comp_apply] using h
    change π ((sF f : EF) : E) = (f : A)
    exact h' 
  have hsinj : Function.Injective s := by
    intro f g hfg
    exact Subtype.ext (by simpa only [hs] using congrArg π hfg)
  let L : Subgroup E := s.range
  have hL : L = s.range := rfl
  let sL : F →* L := s.codRestrict L (fun f => ⟨f, rfl⟩)
  have hsL : Function.Bijective sL := by
    constructor
    · intro f g hfg
      exact hsinj (congrArg (fun x : L => (x : E)) hfg)
    · intro x
      obtain ⟨f, hf⟩ := x.2
      exact ⟨f, Subtype.ext hf⟩
  let eL : F ≃* L := MulEquiv.ofBijective sL hsL
  have hLfin : Finite L := Finite.of_equiv F eL.toEquiv
  have hmap : Subgroup.map π (Subgroup.centralizer (L : Set E)) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨e, he⟩ := hπ a
    have hK : π.ker ≤ EF := hK_le_EF
    let aFun : F → π.ker → π.ker := fun f k =>
      ⟨s f * (k : E) * (s f)⁻¹, by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_mul, map_inv, hs f, k.2, mul_one, mul_inv_cancel]⟩
    let aAut : F → MulAut π.ker := fun f =>
      { toFun := aFun f
        invFun := fun k =>
          ⟨(s f)⁻¹ * (k : E) * s f, by
            rw [MonoidHom.mem_ker]
            rw [map_mul, map_mul, map_inv, hs f, k.2, mul_one, inv_mul_cancel]⟩
        left_inv := by
          intro k
          apply Subtype.ext
          dsimp only [aFun]
          group
        right_inv := by
          intro k
          apply Subtype.ext
          dsimp only [aFun]
          group
        map_mul' := by
          intro k l
          apply Subtype.ext
          dsimp only [aFun]
          simp only [Subgroup.coe_mul]
          group }
    have aAut_one : aAut 1 = 1 := by
      ext k
      dsimp only [aAut, aFun]
      simp only [map_one]
      change (1 : E) * (k : E) * (1 : E)⁻¹ = (k : E)
      group
    have aAut_mul : ∀ f g : F, aAut (f * g) = aAut f * aAut g := by
      intro f g
      ext k
      dsimp only [aAut, aFun]
      change s (f * g) * (k : E) * (s (f * g))⁻¹ =
        s f * (s g * (k : E) * (s g)⁻¹) * (s f)⁻¹
      rw [map_mul]
      group
    let α : F →* MulAut π.ker :=
      { toFun := aAut
        map_one' := aAut_one
        map_mul' := aAut_mul }
    let c : F → π.ker := fun f =>
      ⟨e⁻¹ * s f * e * (s f)⁻¹, by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs f, he]
        calc
          a⁻¹ * (↑f : A) * a * (↑f : A)⁻¹ =
              a⁻¹ * ((↑f : A) * a) * (↑f : A)⁻¹ := by group
          _ = a⁻¹ * (a * (↑f : A)) * (↑f : A)⁻¹ := by
                rw [mul_comm (↑f : A) a]
          _ = 1 := by group⟩
    have hcoc : ∀ f g : F, c (f * g) = c f * α f (c g) := by
      intro f g
      apply Subtype.ext
      dsimp only [c]
      rw [map_mul]
      change e⁻¹ * (s f * s g) * e * (s f * s g)⁻¹ =
        e⁻¹ * s f * e * (s f)⁻¹ *
          (s f * (e⁻¹ * s g * e * (s g)⁻¹) * (s f)⁻¹)
      group
    obtain ⟨u, hu⟩ := exists_inv_mul_of_finite_actor α hdiv c hcoc
    let cE : E := e * (u : E)⁻¹
    have hcE : cE ∈ Subgroup.centralizer (L : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with ⟨f, rfl⟩
      have hu' : (c f : E) = (u : E)⁻¹ * (α f u : E) :=
        congrArg Subtype.val (hu f)
      dsimp only [c] at hu'
      have hαu : (α f u : E) = s f * (u : E) * (s f)⁻¹ := rfl
      rw [hαu] at hu'
      have h1 : s f * e = e * (u : E)⁻¹ * s f * u := by
        calc
          s f * e = e * (e⁻¹ * s f * e * (s f)⁻¹) * s f := by group
          _ = e * ((u : E)⁻¹ * s f * u * (s f)⁻¹) * s f := by
                rw [hu']
                simp only [mul_assoc]
          _ = e * (u : E)⁻¹ * s f * u := by
                simp only [mul_assoc, inv_mul_cancel, mul_one]
      have h2 : s f * (e * (u : E)⁻¹) = e * (u : E)⁻¹ * s f := by
        calc
          s f * (e * (u : E)⁻¹) = (s f * e) * (u : E)⁻¹ := by group
          _ = (e * (u : E)⁻¹ * s f * u) * (u : E)⁻¹ := by rw [h1]
          _ = e * (u : E)⁻¹ * s f := by group
      simpa only [cE] using h2
    have hcEpi : π cE = a := by
      dsimp only [cE]
      rw [map_mul, map_inv, he, (u : π.ker).2]
      simp
    exact Subgroup.mem_map.mpr ⟨cE, hcE, hcEpi⟩
  exact ⟨s, L, hs, hsinj, hL, hLfin, hmap⟩

end CFSG.GroupTheory
