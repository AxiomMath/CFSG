module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterModelOf
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsUnitary

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.RootCenter CFSG.ProperTwoGeneratedCore.UnitaryKernels
open CFSG.ProperTwoGeneratedCore.BenderFacts

theorem card_twist_of_mulEquiv {F : Type*} [Group F] {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J) (R : Sylow 2 F) (γ : MulAut F)
    (hγR : (R : Subgroup F).map γ.toMonoidHom = R) (hγ : γ ∉ (R : Subgroup F).map MulAut.conj)
    (hγ2 : γ ^ 2 = 1) :
    Nat.card {x : F // x ∈ (R : Subgroup F) ∧ x * γ x = 1} = (2 ^ f) ^ 2 := by
  have : CharP K 2 := charP_two_of_card f hcard
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  have : Finite F := Finite.of_equiv _ e.symm.toEquiv
  set U := (CFSG.omega₁ (G := (R : Subgroup F)) (p := 2)).map (R : Subgroup F).subtype with hUdef
  obtain ⟨-, hmem, hinj, -, hsq, -, -, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J f hf hcard hfixed hJ e R U hUdef
  obtain ⟨hcardR, hdata⟩ := unitaryRootCenterData_of_mulEquiv J f hf hcard hfixed hJ e R
  have hUiff := mem_omega_iff J hf hcard hfixed hJ e R
  have hγ2' : γ ^ 2 ∈ (R : Subgroup F).map MulAut.conj := hγ2 ▸ Subgroup.one_mem _
  have hγU : ∀ u ∈ U, γ u = u := fun u hu =>
    fix_omega J hf hcard hfixed hJ e R γ hγR hγ2' ((hUiff u).mp hu).1 ((hUiff u).mp hu).2
  have hγmem : ∀ x ∈ (R : Subgroup F), γ x ∈ (R : Subgroup F) := fun x hx => by
    rw [← hγR]
    exact Subgroup.mem_map_of_mem _ hx
  have hγγ : ∀ x, γ (γ x) = x := fun x => by
    have := DFunLike.congr_fun hγ2 x
    rwa [pow_two, MulAut.mul_apply, MulAut.one_apply] at this
  let ψ : (R : Subgroup F) →* (R : Subgroup F) :=
    { toFun := fun x => ⟨γ x, hγmem x x.2⟩
      map_one' := Subtype.ext (map_one γ)
      map_mul' := fun a b => Subtype.ext (map_mul γ (a : F) (b : F)) }
  have hfixC : ∀ x : (R : Subgroup F), ψ x = x → x ∈ U.subgroupOf R := by
    intro x hx
    have hx' : γ (x : F) = (x : F) := congrArg Subtype.val hx
    set δ := MulAut.conj (x : F) * γ with hδ
    have hδR : (R : Subgroup F).map δ.toMonoidHom = R := by
      rw [map_mul_mulAut, hγR, map_conj_of_mem x.2]
    have hδU : ∀ u ∈ U, δ u = u := by
      intro u hu
      rw [hδ, MulAut.mul_apply, hγU u hu, MulAut.conj_apply, ← ((hmem u).mp hu).2 x x.2,
        mul_inv_cancel_right]
    have hδ2 : δ ^ 2 = MulAut.conj ((x : F) ^ 2) := by
      ext y
      rw [pow_two, MulAut.mul_apply, hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
        MulAut.conj_apply, map_mul, map_mul, map_inv, hx', hγγ, MulAut.conj_apply, pow_two]
      group
    rcases hsq δ ⟨hδR, hδU⟩ (hδ2 ▸ Subgroup.mem_map_of_mem _ (hdata.sq_mem _ x.2)) with h | h
    · exfalso
      apply hγ
      have hγδ : γ = MulAut.conj (x : F)⁻¹ * δ := by
        rw [hδ, map_inv, inv_mul_cancel_left]
      rw [hγδ]
      exact Subgroup.mul_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.inv_mem _ x.2)) h
    · rw [hδ2] at h
      have hx2 : (x : F) ^ 2 = 1 :=
        hinj (Subgroup.pow_mem _ x.2 2) (Subgroup.one_mem _) (by rw [h, map_one])
      exact Subgroup.mem_subgroupOf.mpr ((hUiff _).mpr ⟨x.2, hx2⟩)
  have hUR : U ≤ (R : Subgroup F) := fun u hu => ((hUiff u).mp hu).1
  have hcount := card_mul_apply_eq_one (U := U.subgroupOf R)
    (fun u hu x => Subtype.ext (((hmem u).mp (Subgroup.mem_subgroupOf.mp hu)).2 x x.2))
    (fun x => Subgroup.mem_subgroupOf.mpr (hdata.sq_mem _ x.2)) ψ
    (fun x => Subtype.ext (hγγ x)) (fun u hu => Subtype.ext (hγU _ (Subgroup.mem_subgroupOf.mp hu)))
    hfixC hcardR (by
      rw [← card_omega J hf hcard hfixed hJ e R]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv)
  rw [← hcount]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem unitaryOuterModel_of_mulEquiv {F : Type*} [Group F] {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J) (R : Sylow 2 F) :
    UnitaryOuterModel F (R : Subgroup F) (2 ^ f) := by
  have : CharP K 2 := charP_two_of_card f hcard
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  have : Finite F := Finite.of_equiv _ e.symm.toEquiv
  have : Finite (MulAut F) := Finite.of_injective (fun γ : MulAut F => (γ : F → F))
    DFunLike.coe_injective
  set U := (CFSG.omega₁ (G := (R : Subgroup F)) (p := 2)).map (R : Subgroup F).subtype with hUdef
  obtain ⟨-, hmem, hinj, ⟨D, hinf, hsup, hnormal, hDcard, -⟩, hsq, -, -, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J f hf hcard hfixed hJ e R U hUdef
  obtain ⟨hcardR, hdata⟩ := unitaryRootCenterData_of_mulEquiv J f hf hcard hfixed hJ e R
  have hUiff := mem_omega_iff J hf hcard hfixed hJ e R
  have hfix := fix_omega J hf hcard hfixed hJ e R
  have hNA : (R : Subgroup F).map MulAut.conj ≤ rootCenterAut (R : Subgroup F) U := by
    rw [← hsup]; exact le_sup_left
  have hDA : D ≤ rootCenterAut (R : Subgroup F) U := by
    rw [← hsup]; exact le_sup_right
  have hA : ∀ γ : MulAut F, (R : Subgroup F).map γ.toMonoidHom = R →
      γ ^ 2 ∈ (R : Subgroup F).map MulAut.conj → γ ∈ rootCenterAut (R : Subgroup F) U :=
    fun γ hγR hγ2 => ⟨hγR, fun u hu => hfix γ hγR hγ2 ((hUiff u).mp hu).1 ((hUiff u).mp hu).2⟩
  refine ⟨?_, hcardR, ?_, ?_, ?_, ?_, ?_, hfix, ?_, ?_, ?_, ?_⟩
  · calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · intro x hx
    exact ((hUiff _).mp (hdata.sq_mem x hx)).2
  · intro x hx hx2 y hy
    exact ((hmem x).mp ((hUiff x).mpr ⟨hx, hx2⟩)).2 y hy
  · rw [← card_omega J hf hcard hfixed hJ e R]
    exact Nat.card_congr ⟨fun x => ⟨x.1, (hUiff x.1).mpr x.2⟩, fun x => ⟨x.1, (hUiff x.1).mp x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  · intro u hu hu1 hu2
    have h := card_sq_eq_of_mulEquiv_projectiveSpecialUnitary J hf hcard hfixed hJ e R
      (z := ⟨u, hu⟩) (fun h => hu1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hu2))
    rw [← h]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (by simpa using x.2.2)⟩
        invFun := fun x => ⟨x.1.1, x.1.2, by simpa using congrArg Subtype.val x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · intro x hx h1
    exact hinj hx (Subgroup.one_mem _) (by rw [h1, map_one])
  · intro γ hγR hγU u hu hu2 hγ2
    exact hsq γ ⟨hγR, fun v hv => hγU v ((hUiff v).mp hv).1 ((hUiff v).mp hv).2⟩
      (hγ2 ▸ Subgroup.mem_map_of_mem _ ((hUiff u).mpr ⟨hu, hu2⟩))
  · intro γ hγR hγ2
    obtain ⟨c, ⟨y, hy, rfl⟩, hc⟩ :=
      exists_inv_mul_sq_eq_one hNA hDA hnormal hinf hsup (hA γ hγR hγ2) hγ2
    exact ⟨y, hy, by rwa [← map_inv] at hc⟩
  · intro Y hY γ₁ h₁Y γ₂ h₂Y h₁R h₂R h₁2 h₂2 h₁ h₂
    have hodd : Odd (2 ^ f + 1) := (Even.pow_of_ne_zero (by decide) (by omega)).add_one
    exact mul_inv_mem_of_isPGroup hNA hDA hnormal hinf hsup hodd hDcard hY h₁Y h₂Y
      (hA γ₁ h₁R h₁2) (hA γ₂ h₂R h₂2) h₁ h₂
  · intro γ hγR hγ hγ2
    exact card_twist_of_mulEquiv J hf hcard hfixed hJ e R γ hγR hγ hγ2

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
