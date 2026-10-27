module

public import CFSG.LargeExtraspecial.S3bTen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem sub_mem_span_of_mem_clSub {g : G} {s : S.O} (hs : s ∈ S.Lbar g) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [← S.cl_commutator y.2 hxQ]
  rcases (S.conjBy g).commutator_eq_one_or_z hy.1 hx.2 with h | h
  · rw [h, S.cl_one]
    exact Submodule.zero_mem _
  · rw [h]
    exact Submodule.mem_span_singleton_self _

theorem lemma_3_11_two (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) :
    S.IsReducible ∨
      (Nat.card (S.Lbar g) = 2 ^ (S.width - 1) ∧
        Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1) ∧
        (∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), S.q v = 0) ∧
        finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width ∧
        ∀ s ∈ S.Lbar g, (∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
          s = 1) := by
  rcases S.lemma_3_10 hTI hn haQ hne with hL | hA | hR
  swap
  · exact absurd hA hno
  swap
  · exact Or.inl hR
  right
  have h1 := S.card_Lbar_mul g
  rw [S.card_L0 haQ hne, hL] at h1
  have hX : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1) := by
    refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (S.width - 1)) ?_
    rw [h1, ← pow_add]
    congr 1
    omega
  refine ⟨hL, hX, fun v hv => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hv, ?_, ?_⟩
  · have := S.finrank_clSub_QG_inf_Qa haQ hne hX
    omega
  · intro s hs hfix
    obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
    have hyC : (y : G) ∈ S.CQa g :=
      S.mem_CQa_of_fix hne hy fun w hw => hfix _ (S.cl_mem_clSub hw hw.1)
    have hC := S.card_CQa_mul haQ
    rw [hX] at hC
    have hCX : Nat.card (S.CQa g) = Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
      rw [hX]
      refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (S.width + 1)) ?_
      rw [hC, ← pow_add]
      congr 1
      ring
    have hle : S.QG ⊓ S.Qa g ≤ S.CQa g := by
      rw [← S.QG_inf_CQa hne]
      exact inf_le_right
    have heq : S.QG ⊓ S.Qa g = S.CQa g := eq_of_le_of_card_ge hle hCX.le
    rw [← heq] at hyC
    exact (S.ρ_eq_one_iff y).mpr hyC.1

theorem lemma_3_11_transvections (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) :
    S.IsReducible ∨
      ∀ φ : S.clSub (S.QG ⊓ S.Qa g) →ₗ[ZMod 2] ZMod 2,
        φ ⟨S.cl (g * S.z * g⁻¹), S.cl_mem_clSub ⟨haQ, S.conj_z_mem_Qa g⟩ haQ⟩ = 0 →
        ∃! s, s ∈ S.Lbar g ∧ ∀ w : S.clSub (S.QG ⊓ S.Qa g),
          (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + φ w • S.cl (g * S.z * g⁻¹) := by
  classical
  rcases S.lemma_3_11_two hTI hn haQ hne hno with hR | ⟨hL, -, -, hWn, hC⟩
  · exact Or.inl hR
  right
  set W := S.clSub (S.QG ⊓ S.Qa g) with hW
  set a' := S.cl (g * S.z * g⁻¹) with ha'
  have ha0 : a' ≠ 0 := S.cl_conj_z_ne_zero haQ hne
  have haW : a' ∈ W := S.cl_mem_clSub ⟨haQ, S.conj_z_mem_Qa g⟩ haQ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual (ZMod 2) S.Qt, ψ a' = 1 := by
    by_contra h
    push Not at h
    apply ha0
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) a').mp fun ψ => ?_
    exact (zmod2_eq_zero_or_eq_one _).resolve_right (h ψ)
  have hcoef : ∀ s ∈ S.Lbar g, ∀ w ∈ W,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) • a' := by
    intro s hs w hw
    rcases mem_span_singleton_iff.mp (S.sub_mem_span_of_mem_clSub hs hw) with h | h
    · rw [h, map_zero, zero_smul, add_zero]
      exact sub_eq_zero.mp h
    · rw [h, hψ, one_smul]
      calc (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
        _ = w + a' := by rw [h]
  set K : Submodule (ZMod 2) (Module.Dual (ZMod 2) W) :=
    LinearMap.ker (Module.Dual.eval (ZMod 2) W ⟨a', haW⟩) with hK
  let F : S.Lbar g → K := fun s => ⟨ψ ∘ₗ (((s : S.O) : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id) ∘ₗ
    W.subtype, by
      rw [hK, LinearMap.mem_ker, Module.Dual.eval_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [S.mem_fixLbar.mp (S.cl_mem_fixLbar_self haQ) _ s.2, sub_self, map_zero]⟩
  have hF : ∀ (s : S.Lbar g) (w : W), (F s : Module.Dual (ZMod 2) W) w =
      ψ (((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := fun _ _ => rfl
  have hFinj : Function.Injective F := by
    intro s t hst
    have hfix : ∀ w ∈ W, ((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
      intro w hw
      have h1 := congrArg (fun φ : K => (φ : Module.Dual (ZMod 2) W) ⟨w, hw⟩) hst
      simp only [hF] at h1
      rw [hcoef _ s.2 w hw, hcoef _ t.2 w hw, h1]
    have h1 : (t : S.O)⁻¹ * s = 1 := by
      refine hC _ (mul_mem (inv_mem t.2) s.2) fun w hw => ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
      rw [hfix w hw]
      exact LinearEquiv.symm_apply_apply _ _
    exact Subtype.ext (by
      calc (s : S.O) = t * ((t : S.O)⁻¹ * s) := by group
        _ = t := by rw [h1, mul_one])
  have hKcard : Nat.card K = 2 ^ (S.width - 1) := by
    set f := Module.Dual.eval (ZMod 2) W ⟨a', haW⟩ with hf
    have hf0 : f ≠ 0 := by
      intro h0
      apply ha0
      have : (⟨a', haW⟩ : W) = 0 := by
        refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp fun φ => ?_
        have := LinearMap.congr_fun h0 φ
        rw [hf, Module.Dual.eval_apply] at this
        simpa using this
      exact congrArg Subtype.val this
    have h1 : finrank (ZMod 2) (LinearMap.range f) + finrank (ZMod 2) K = S.width := by
      have := LinearMap.finrank_range_add_finrank_ker f
      rw [Subspace.dual_finrank_eq, hWn] at this
      exact this
    have h2 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      rwa [Module.finrank_self] at this
    have h3 : 1 ≤ finrank (ZMod 2) (LinearMap.range f) :=
      Submodule.one_le_finrank_iff.mpr fun h => hf0 (LinearMap.range_eq_bot.mp h)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  have : Finite K := Module.finite_of_finite (ZMod 2)
  have hbij : Function.Bijective F :=
    hFinj.bijective_of_nat_card_le (by rw [hKcard, hL])
  intro φ hφ
  have hφK : φ ∈ K := by
    rw [hK, LinearMap.mem_ker, Module.Dual.eval_apply]
    exact hφ
  obtain ⟨s, hs⟩ := hbij.2 ⟨φ, hφK⟩
  have hval : ∀ w : W, ψ (((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) = φ w := fun w => by
    have h1 := congrArg (fun ψ' : K => (ψ' : Module.Dual (ZMod 2) W) w) hs
    simpa only [hF] using h1
  refine ⟨(s : S.O), ⟨s.2, fun w => ?_⟩, ?_⟩
  · rw [hcoef _ s.2 w w.2, hval]
  · rintro t ⟨ht, htw⟩
    have h1 : F ⟨t, ht⟩ = ⟨φ, hφK⟩ := by
      refine Subtype.ext (LinearMap.ext fun w => ?_)
      rw [hF]
      change ψ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) = φ w
      rw [htw w, add_sub_cancel_left, map_smul, hψ, smul_eq_mul, mul_one]
    have := hFinj (h1.trans hs.symm)
    exact congrArg Subtype.val this

end Setting

end CFSG.LargeExtraspecial
