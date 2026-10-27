module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LieType.SteinbergBR.AutGL32

open Matrix Subgroup CFSG.QuasithinUnique.Setup.Family

noncomputable abbrev tau : MulAut GL32 :=
  CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2)

theorem tau_val (g : GL32) :
    ((tau g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (g⁻¹ : GL32).val.transpose :=
  CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_matrix 3 (ZMod 2) g

theorem tau_mul_tau : tau * tau = 1 := by
  rw [← sq]
  exact CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_sq 3 (ZMod 2)

theorem tau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_tau

theorem tau_mul_conj (g : GL32) : tau * MulAut.conj g = MulAut.conj (tau g) * tau :=
  MulEquiv.ext fun x => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_injective : Function.Injective (MulAut.conj : GL32 →* MulAut GL32) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center GL32 := Subgroup.mem_center_iff.2 fun x => by
    have := congrArg (fun φ : MulAut GL32 => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  rw [center_GL32, Subgroup.mem_bot] at hc
  exact hc

theorem tau_not_mem_inner : tau ∉ (MulAut.conj : GL32 →* MulAut GL32).range := by
  rintro ⟨g, hg⟩
  exact glGraphAut_ne_conj g hg.symm

@[expose] def sGL : GL32 :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], !![1, 1, 1; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

@[expose] def wGL : GL32 :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩

@[expose] def aGL : GL32 :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def bGL : GL32 :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

theorem uGL_val : ((sGL * tau sGL : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![0, 1, 0; 0, 0, 1; 1, 1, 1] := by
  rw [Units.val_mul, tau_val]
  decide

theorem orderOf_uGL : orderOf (sGL * tau sGL) = 2 ^ 2 := by
  apply orderOf_eq_prime_pow
  · intro h
    have := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    simp only [Units.val_pow_eq_pow_val, uGL_val, Units.val_one] at this
    revert this
    decide
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, uGL_val, Units.val_one]
    decide

theorem wGL_not_mem_zpowers : wGL ∉ zpowers (sGL * tau sGL) := by
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_uGL, Finset.mem_image]
  rintro ⟨k, hk, hkw⟩
  have := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) hkw
  simp only [Units.val_pow_eq_pow_val, uGL_val] at this
  have hk' : k < 4 := by simpa using hk
  interval_cases k <;> revert this <;> decide

theorem wGL_rel : wGL * sGL * tau wGL⁻¹ = tau sGL⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tau_val, tau_val, inv_inv, inv_inv]
  decide

theorem wGL_sq : wGL * wGL = 1 := Units.ext (by decide)

theorem wGL_ne_one : wGL ≠ 1 := fun h => by
  have := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  revert this
  decide

theorem aGL_sq : aGL * aGL = 1 := Units.ext (by decide)

theorem bGL_sq : bGL * bGL = 1 := Units.ext (by decide)

theorem aGL_mul_bGL : aGL * bGL = bGL * aGL := Units.ext (by decide)

theorem aGL_ne_one : aGL ≠ 1 := fun h => by
  have := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  revert this
  decide

theorem bGL_ne_one : bGL ≠ 1 := fun h => by
  have := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  revert this
  decide

theorem aGL_ne_bGL : aGL ≠ bGL := fun h => by
  have := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  revert this
  decide

theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1)
    (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hx) hx1

@[expose] noncomputable def alphaAut : MulAut GL32 := MulAut.conj sGL * tau

@[expose] noncomputable def betaAut : MulAut GL32 := MulAut.conj wGL

theorem alphaAut_sq : alphaAut ^ 2 = MulAut.conj (sGL * tau sGL) := by
  rw [sq, alphaAut, mul_assoc, ← mul_assoc tau, tau_mul_conj, mul_assoc, tau_mul_tau, mul_one,
    ← map_mul]

theorem orderOf_alphaAut : orderOf alphaAut = 2 ^ 3 := by
  have hu4 : (sGL * tau sGL) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (sGL * tau sGL)
    rwa [orderOf_uGL] at this
  have hu2 : (sGL * tau sGL) ^ 2 ≠ 1 := fun h => by
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    rw [orderOf_uGL] at this
    norm_num at this
  apply orderOf_eq_prime_pow
  · show ¬ alphaAut ^ (2 * 2) = 1
    rw [pow_mul, alphaAut_sq, ← map_pow]
    exact fun h => hu2 (conj_injective (h.trans (map_one _).symm))
  · show alphaAut ^ (2 * 4) = 1
    rw [pow_mul, alphaAut_sq, ← map_pow, hu4, map_one]

theorem betaAut_sq : betaAut ^ 2 = 1 := by
  rw [sq, betaAut, ← map_mul, wGL_sq, map_one]

theorem betaAut_rel : betaAut * alphaAut * betaAut⁻¹ = alphaAut⁻¹ := by
  rw [betaAut, alphaAut, ← map_inv, mul_assoc, mul_assoc, tau_mul_conj, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul, wGL_rel, _root_.mul_inv_rev, tau_inv, ← map_inv,
    tau_mul_conj]

theorem betaAut_not_mem_zpowers : betaAut ∉ zpowers alphaAut := by
  rw [mem_zpowers_iff]
  rintro ⟨k, hk⟩
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · rw [_root_.zpow_mul, zpow_two, ← sq, alphaAut_sq, ← map_zpow] at hk
    exact wGL_not_mem_zpowers (mem_zpowers_iff.2 ⟨j, conj_injective hk⟩)
  · rw [_root_.zpow_add, zpow_one, _root_.zpow_mul, zpow_two, ← sq, alphaAut_sq, ← map_zpow,
      alphaAut,
      ← mul_assoc, ← map_mul] at hk
    apply tau_not_mem_inner
    refine ⟨((sGL * tau sGL) ^ j * sGL)⁻¹ * wGL, ?_⟩
    rw [map_mul, map_inv, show MulAut.conj wGL = betaAut from rfl, ← hk, inv_mul_cancel_left]

theorem card_GL32 : Nat.card GL32 = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem index_inner : (MulAut.conj : GL32 →* MulAut GL32).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨tau, fun b => ?_⟩
  rcases aut_GL32_cases b with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · refine Or.inr ⟨⟨s, rfl⟩, fun h => tau_not_mem_inner ?_⟩
    obtain ⟨t, ht⟩ := h
    exact ⟨s⁻¹ * t, by rw [map_mul, ht, map_inv, inv_mul_cancel_left]⟩
  · refine Or.inl ⟨⟨s, by rw [mul_assoc, tau_mul_tau, mul_one]⟩, fun h => tau_not_mem_inner ?_⟩
    obtain ⟨t, ht⟩ := h
    exact ⟨s⁻¹ * t, by rw [map_mul, ht, map_inv, inv_mul_cancel_left]⟩

theorem card_mulAut_GL32 : Nat.card (MulAut GL32) = 336 := by
  rw [← Subgroup.card_mul_index (MulAut.conj : GL32 →* MulAut GL32).range, index_inner,
    ← Nat.card_congr (MonoidHom.ofInjective conj_injective).toEquiv, card_GL32]

theorem nonempty_closure_pair_mulEquiv_dihedralGroup {G : Type*} [Group G] [Finite G] {ρ σ : G}
    (hσ : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ zpowers ρ) :
    Nonempty (closure {ρ, σ} ≃* DihedralGroup (orderOf ρ)) := by
  have hρH : ρ ∈ closure ({ρ, σ} : Set G) := subset_closure (by simp)
  have hσH : σ ∈ closure ({ρ, σ} : Set G) := subset_closure (by simp)
  have hgen : (⊤ : Subgroup (closure ({ρ, σ} : Set G))) =
      zpowers ⟨ρ, hρH⟩ ⊔ zpowers ⟨σ, hσH⟩ := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union,
      ← closure_closure_coe_preimage (k := ({ρ, σ} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem
    (D := closure ({ρ, σ} : Set G)) ⟨ρ, hρH⟩ ⟨σ, hσH⟩ hgen (Subtype.ext (by simpa using hσ))
    (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ (by
      obtain ⟨k, hk⟩ := (mem_zpowers_iff).mp hmem
      exact (mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h

theorem nonempty_closure_mulEquiv_dihedral :
    Nonempty (closure ({alphaAut, betaAut} : Set (MulAut GL32)) ≃* DihedralGroup 8) := by
  have h := nonempty_closure_pair_mulEquiv_dihedralGroup betaAut_sq betaAut_rel
    betaAut_not_mem_zpowers
  rwa [orderOf_alphaAut] at h

theorem card_closure_alpha_beta :
    Nat.card (closure ({alphaAut, betaAut} : Set (MulAut GL32))) = 16 := by
  obtain ⟨e⟩ := nonempty_closure_mulEquiv_dihedral
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

end CFSG.LieType.SteinbergBR.AutGL32
