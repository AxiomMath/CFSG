module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4ElemUT

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

variable {K : Type*} [Field K]

theorem exists_conj_le_posUnip [Finite K] [CharP K 2]
    (A : Subgroup (orthElementaryGroup (quadPlus 4 K))) (hA : IsPGroup 2 A) :
    ∃ g : orthElementaryGroup (quadPlus 4 K),
      A.map (MulAut.conj g).toMonoidHom ≤
        (posUnip 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K)) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Finite ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
    Finite.of_equiv (GL (Fin 4 ⊕ Fin 4) K) (matrixEquiv 4 K).toEquiv
  obtain ⟨S, hS⟩ := posUnip_isSylow (r := 4) (K := K) (p := 2) (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (K := K) (r := 4) (by norm_num) ha)
  obtain ⟨S', hAS'⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (orthElementaryGroup (quadPlus 4 K)) S' S
  refine ⟨g, ?_⟩
  calc A.map (MulAut.conj g).toMonoidHom
      ≤ S'.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hAS'
    _ = ((g • S' : Sylow 2 (orthElementaryGroup (quadPlus 4 K))) :
          Subgroup (orthElementaryGroup (quadPlus 4 K))) := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
    _ = S := by rw [hg]
    _ = (posUnip 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K)) := hS

private noncomputable def leviPart (g : posUnip 4 K) : GL (Fin 4) K :=
  ((mem_posUnip_iff_levi_radical (r := 4) (K := K)).mp g.2).choose

private noncomputable def radPart (g : posUnip 4 K) : Matrix (Fin 4) (Fin 4) K :=
  (((mem_posUnip_iff_levi_radical (r := 4) (K := K)).mp g.2).choose_spec).choose

private theorem leviPart_spec (g : posUnip 4 K) :
    (leviPart g : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      (∀ i, (leviPart g : Matrix (Fin 4) (Fin 4) K) i i = 1) ∧
      radPart g ∈ altSubgroup 4 K ∧
      (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        levi 4 K (leviPart g) * radical 4 K (Multiplicative.ofAdd (radPart g)) :=
  (((mem_posUnip_iff_levi_radical (r := 4) (K := K)).mp g.2).choose_spec).choose_spec

private theorem eq_radical_of_leviPart_eq_one {g : posUnip 4 K} (hg : leviPart g = 1) :
    (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      radical 4 K (Multiplicative.ofAdd (radPart g)) := by
  rw [(leviPart_spec g).2.2.2, hg, map_one, one_mul]

private theorem leviPart_radPart_eq {g : posUnip 4 K} {A : GL (Fin 4) K}
    {B : Matrix (Fin 4) (Fin 4) K}
    (hg : (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      levi 4 K A * radical 4 K (Multiplicative.ofAdd B)) :
    A = leviPart g ∧ B = radPart g := by
  have hspec := (leviPart_spec g).2.2.2
  have hEg : levi 4 K A * radical 4 K (Multiplicative.ofAdd B) =
      levi 4 K (leviPart g) * radical 4 K (Multiplicative.ofAdd (radPart g)) :=
    hg.symm.trans hspec
  have hEq : levi 4 K (leviPart g)⁻¹ * levi 4 K A =
      radical 4 K (Multiplicative.ofAdd (radPart g)) *
        (radical 4 K (Multiplicative.ofAdd B))⁻¹ := by
    have h := congrArg (fun x => (levi 4 K (leviPart g))⁻¹ * x *
      (radical 4 K (Multiplicative.ofAdd B))⁻¹) hEg
    simpa [mul_assoc] using h
  have hEq' : levi 4 K ((leviPart g)⁻¹ * A) =
      radical 4 K (Multiplicative.ofAdd (radPart g - B)) := by
    calc levi 4 K ((leviPart g)⁻¹ * A)
        = levi 4 K (leviPart g)⁻¹ * levi 4 K A := by rw [map_mul, map_inv]
      _ = radical 4 K (Multiplicative.ofAdd (radPart g - B)) := by
          rw [hEq, ← map_inv, ← map_mul, ofAdd_sub, div_eq_mul_inv]
  obtain ⟨h1, h2⟩ := eq_one_of_levi_eq_radical (r := 4) (K := K) hEq'
  refine ⟨?_, (sub_eq_zero.1 h2).symm⟩
  calc A = leviPart g * (leviPart g)⁻¹ * A := by group
    _ = leviPart g * ((leviPart g)⁻¹ * A) := by group
    _ = leviPart g * 1 := by rw [h1]
    _ = leviPart g := mul_one _

private theorem radical_levi_comm (A : GL (Fin 4) K) (B : Matrix (Fin 4) (Fin 4) K) :
    radical 4 K (Multiplicative.ofAdd B) * levi 4 K A =
      levi 4 K A * radical 4 K (Multiplicative.ofAdd
        (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B *
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ)) := by
  have h := levi_mul_radical_mul_inv (r := 4) (K := K) A⁻¹ B
  rw [map_inv, inv_inv] at h
  calc radical 4 K (Multiplicative.ofAdd B) * levi 4 K A
      = levi 4 K A * ((levi 4 K A)⁻¹ * radical 4 K (Multiplicative.ofAdd B) *
          levi 4 K A) := by group
    _ = levi 4 K A * radical 4 K (Multiplicative.ofAdd
        (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B *
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ)) := by rw [h]

private theorem leviPart_radPart_spec_mul (g h : posUnip 4 K) :
    ((g * h : posUnip 4 K) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      levi 4 K (leviPart g * leviPart h) *
        radical 4 K (Multiplicative.ofAdd
          ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart g *
            ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ +
              radPart h)) := by
  have hg := (leviPart_spec g).2.2.2
  have hh := (leviPart_spec h).2.2.2
  rw [Subgroup.coe_mul, hg, hh, map_mul]
  have hc := radical_levi_comm (leviPart h) (radPart g)
  calc levi 4 K (leviPart g) * radical 4 K (Multiplicative.ofAdd (radPart g)) *
        (levi 4 K (leviPart h) * radical 4 K (Multiplicative.ofAdd (radPart h)))
      = levi 4 K (leviPart g) *
          (radical 4 K (Multiplicative.ofAdd (radPart g)) * levi 4 K (leviPart h)) *
            radical 4 K (Multiplicative.ofAdd (radPart h)) := by group
    _ = levi 4 K (leviPart g) *
          (levi 4 K (leviPart h) * radical 4 K (Multiplicative.ofAdd
            ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart g *
              ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ))) *
            radical 4 K (Multiplicative.ofAdd (radPart h)) := by rw [hc]
    _ = (levi 4 K (leviPart g) * levi 4 K (leviPart h)) *
          (radical 4 K (Multiplicative.ofAdd
            ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart g *
              ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ)) *
            radical 4 K (Multiplicative.ofAdd (radPart h))) := by group
    _ = (levi 4 K (leviPart g) * levi 4 K (leviPart h)) *
          radical 4 K (Multiplicative.ofAdd
            ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart g *
              ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ +
                radPart h)) := by
        congr 1
        rw [← map_mul, ← ofAdd_add]

private theorem leviPart_mul (g h : posUnip 4 K) :
    leviPart (g * h) = leviPart g * leviPart h :=
  (leviPart_radPart_eq (leviPart_radPart_spec_mul g h)).1.symm

private theorem radPart_mul (g h : posUnip 4 K) :
    radPart (g * h) =
      (((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart g *
        ((((leviPart h)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ + radPart h :=
  (leviPart_radPart_eq (leviPart_radPart_spec_mul g h)).2.symm

private theorem leviPart_conj_radPart_of_commute {g h : posUnip 4 K}
    (hgh : (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * h = h * g)
    (hh : leviPart h = 1) :
    (leviPart g : Matrix (Fin 4) (Fin 4) K) * radPart h *
      (leviPart g : Matrix (Fin 4) (Fin 4) K)ᵀ = radPart h := by
  have hprod : g * h = h * g := Subtype.ext (by simpa using hgh)
  have h1 := radPart_mul g h
  have h2 := radPart_mul h g
  rw [hh] at h1
  have h1' : radPart (g * h) = radPart g + radPart h := by
    simpa using h1
  have key : (((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart h *
      ((((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ + radPart g =
      radPart g + radPart h := by
    calc ((((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * radPart h *
        ((((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ + radPart g
        = radPart (h * g) := h2.symm
      _ = radPart (g * h) := by rw [hprod]
      _ = radPart g + radPart h := h1'
  have key' : (((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart h *
      ((((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ + radPart g =
      radPart h + radPart g := by rw [key, add_comm]
  have hC : (((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * radPart h *
      ((((leviPart g)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ = radPart h :=
    add_right_cancel key'
  have hfin := congrArg (fun X : Matrix (Fin 4) (Fin 4) K =>
    (leviPart g : Matrix (Fin 4) (Fin 4) K) * X *
      (leviPart g : Matrix (Fin 4) (Fin 4) K)ᵀ) hC
  simpa [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.coe_units_inv] using hfin.symm

private noncomputable def leviBlock : posUnip 4 K →* GL (Fin 4) K where
  toFun := leviPart
  map_one' := by
    have h : ((1 : posUnip 4 K) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K]
        (Fin 4 ⊕ Fin 4 → K)) =
        levi 4 K (1 : GL (Fin 4) K) *
          radical 4 K (Multiplicative.ofAdd (0 : Matrix (Fin 4) (Fin 4) K)) := by
      rw [map_one, ofAdd_zero, map_one, mul_one]
      simp
    exact (leviPart_radPart_eq h).1.symm
  map_mul' := leviPart_mul

theorem card_le_of_le_posUnip [Finite K] [CharP K 2]
    (A : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) (hAU : A ≤ posUnip 4 K)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1) :
    Nat.card A ≤ Nat.card K ^ 7 := by
  let f : A →* GL (Fin 4) K :=
    { toFun := fun x => leviPart ⟨x, hAU x.2⟩
      map_one' := leviBlock.map_one'
      map_mul' := fun x y => leviPart_mul ⟨x, hAU x.2⟩ ⟨y, hAU y.2⟩ }
  have hU : ∀ a ∈ f.range, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1 := by
    rintro a ⟨x, rfl⟩
    exact ⟨(leviPart_spec ⟨x, hAU x.2⟩).1, (leviPart_spec ⟨x, hAU x.2⟩).2.1⟩
  have hcommP : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a := by
    rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm x x.2 y y.2)
  have hsqP : ∀ a ∈ f.range, a * a = 1 := by
    rintro a ⟨x, rfl⟩
    show f x * f x = 1
    rw [← map_mul, ← map_one f]
    congr 1
    exact Subtype.ext (hsq x x.2)
  let fixSet : Type _ := {B : Matrix (Fin 4) (Fin 4) K // B ∈ altSubgroup 4 K ∧
    ∀ a ∈ f.range, (a : Matrix (Fin 4) (Fin 4) K) * B *
      (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B}
  let Φ : f.ker → fixSet := fun h =>
    ⟨radPart ⟨h.1, hAU h.1.2⟩,
      (leviPart_spec ⟨h.1, hAU h.1.2⟩).2.2.1,
      by
        intro a ha
        obtain ⟨x, rfl⟩ := ha
        have hh : leviPart ⟨h.1, hAU h.1.2⟩ = 1 := MonoidHom.mem_ker.1 h.2
        have hcommute : ((⟨x, hAU x.2⟩ : posUnip 4 K) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K]
              (Fin 4 ⊕ Fin 4 → K)) * (⟨h.1, hAU h.1.2⟩ : posUnip 4 K) =
            (⟨h.1, hAU h.1.2⟩ : posUnip 4 K) * ((⟨x, hAU x.2⟩ : posUnip 4 K) :
              (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
          simpa using hcomm x x.2 h.1 h.1.2
        exact leviPart_conj_radPart_of_commute hcommute hh⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hrad : radPart ⟨x, hAU x.2⟩ = radPart ⟨y, hAU y.2⟩ := congrArg Subtype.val hxy
    have hx1 : leviPart ⟨x, hAU x.2⟩ = 1 := MonoidHom.mem_ker.1 hx
    have hy1 : leviPart ⟨y, hAU y.2⟩ = 1 := MonoidHom.mem_ker.1 hy
    have hxdecomp := eq_radical_of_leviPart_eq_one (g := ⟨x, hAU x.2⟩) hx1
    have hydecomp := eq_radical_of_leviPart_eq_one (g := ⟨y, hAU y.2⟩) hy1
    have hxypos : (⟨x, hAU x.2⟩ : posUnip 4 K) = ⟨y, hAU y.2⟩ := by
      apply Subtype.ext
      rw [hxdecomp, hydecomp, hrad]
    have hxyA : x = y := Subtype.ext (by
      simpa using congrArg (fun z : posUnip 4 K =>
        (z : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) hxypos)
    exact Subtype.ext hxyA
  have hker : Nat.card f.ker ≤ Nat.card fixSet :=
    Nat.card_le_card_of_injective Φ hΦinj
  calc Nat.card A = Nat.card f.ker * Nat.card f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ Nat.card fixSet * Nat.card f.range := Nat.mul_le_mul_right _ hker
    _ = Nat.card f.range * Nat.card fixSet := Nat.mul_comm _ _
    _ ≤ Nat.card K ^ 7 := card_mul_card_altFix_le (K := K) f.range hU hcommP hsqP

theorem card_le_pow_seven_of_elemAbelian [Finite K] [CharP K 2]
    (A : Subgroup (orthElementaryGroup (quadPlus 4 K)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1) :
    Nat.card A ≤ Nat.card K ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hA2 : IsPGroup 2 A := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro a
    refine ⟨1, ?_⟩
    have h2 : a ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext (by simpa using hsq a a.2)
    simpa using orderOf_dvd_of_pow_eq_one h2
  obtain ⟨g, hg⟩ := exists_conj_le_posUnip A hA2
  let φ : orthElementaryGroup (quadPlus 4 K) →*
      ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
    (orthElementaryGroup (quadPlus 4 K)).subtype.comp (MulAut.conj g).toMonoidHom
  let A' : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := A.map φ
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (MulAut.conj g).injective
  have hcard : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective hφinj
  have hle : A' ≤ posUnip 4 K := by
    rintro x ⟨a, ha, rfl⟩
    exact hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  have hcomm' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact hcomm a ha b hb
  have hsq' : ∀ a ∈ A', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show φ a * φ a = 1
    rw [← map_mul, ← map_one φ]
    congr 1
    exact hsq a ha
  calc Nat.card A = Nat.card A' := hcard.symm
    _ ≤ Nat.card K ^ 7 := card_le_of_le_posUnip A' hle hcomm' hsq'

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
