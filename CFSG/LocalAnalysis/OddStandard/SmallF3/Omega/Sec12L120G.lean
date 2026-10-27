module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem isEvenVec_add_vec {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  unfold IsEvenVec
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

theorem exists_natMod_lift_of_hom {V K B H : Subgroup G} (f : G → G) (hKV : K ≤ V)
    (hVK : V ≤ normalizer (K : Set G)) (hHV : H ≤ normalizer (V : Set G))
    (hHK : H ≤ normalizer (K : Set G)) (hfB : ∀ v ∈ V, f v ∈ B)
    (hmul : ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w) (hker : ∀ v ∈ V, f v = 1 ↔ v ∈ K)
    (hsurj : ∀ b ∈ B, ∃ v ∈ V, f v = b)
    (hconj : ∀ h ∈ H, ∀ v ∈ V, f (h * v * h⁻¹) = h * f v * h⁻¹)
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ B H (alternatingGroup (Fin 5))) :
    ∃ φ' : (Fin 5 → ZMod 2) → G,
      IsPermModuleMod (n := 5) IsEvenVec {0} φ' V K H (alternatingGroup (Fin 5)) ∧
        ∀ v, IsEvenVec v → f (φ' v) = φ v := by
  have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hφ0 : φ 0 = 1 := by
    have h00 : φ 0 = φ 0 * φ 0 := by simpa using hperm.1 0 0 h0ev h0ev
    exact mul_eq_left.1 h00.symm
  have hφB : ∀ v, IsEvenVec v → φ v ∈ B :=
    fun v hv => (hperm.2.2.1 (φ v)).2 ⟨v, hv, rfl⟩
  have hf1 : f 1 = 1 := (hker 1 V.one_mem).2 K.one_mem
  have hfinv : ∀ x ∈ V, f x⁻¹ = (f x)⁻¹ := by
    intro x hx
    have h := hmul x⁻¹ (V.inv_mem hx) x hx
    rw [inv_mul_cancel, hf1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hdiff : ∀ x ∈ V, ∀ x' ∈ V, f x = f x' → x⁻¹ * x' ∈ K := by
    intro x hx x' hx' heq
    have hxmem : x⁻¹ * x' ∈ V := V.mul_mem (V.inv_mem hx) hx'
    apply (hker _ hxmem).1
    calc f (x⁻¹ * x') = f x⁻¹ * f x' := hmul x⁻¹ (V.inv_mem hx) x' hx'
      _ = (f x)⁻¹ * f x' := by rw [hfinv x hx]
      _ = (f x')⁻¹ * f x' := by rw [heq]
      _ = 1 := inv_mul_cancel (f x')
  have hlift : ∀ v, IsEvenVec v → ∃ e : G, e ∈ V ∧ f e = φ v :=
    fun v hv => hsurj (φ v) (hφB v hv)
  choose! φ' hφ'V hφ'f using hlift
  have act : ∀ (h : G) (σ : Equiv.Perm (Fin 5)),
      (∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)) → h ∈ H →
      ∀ v, IsEvenVec v → (h * φ' v * h⁻¹)⁻¹ * φ' (permVec σ v) ∈ K := by
    intro h σ hσ hh v hv
    have hmem1 : h * φ' v * h⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hHV hh) (φ' v)).1 (hφ'V v hv)
    have hev : IsEvenVec (permVec σ v) := isEvenVec_permVec σ hv
    have hmem2 : φ' (permVec σ v) ∈ V := hφ'V (permVec σ v) hev
    apply hdiff (h * φ' v * h⁻¹) hmem1 (φ' (permVec σ v)) hmem2
    calc f (h * φ' v * h⁻¹) = h * f (φ' v) * h⁻¹ := hconj h hh (φ' v) (hφ'V v hv)
      _ = h * φ v * h⁻¹ := by rw [hφ'f v hv]
      _ = φ (permVec σ v) := hσ v hv
      _ = f (φ' (permVec σ v)) := (hφ'f (permVec σ v) hev).symm
  refine ⟨φ', ?_, fun v hv => hφ'f v hv⟩
  refine ⟨hKV, ?_, hHV, hHK, hφ'V, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKV).2 hVK
  · intro v w hv hw
    apply hdiff (φ' v * φ' w) (V.mul_mem (hφ'V v hv) (hφ'V w hw))
      (φ' (v + w)) (hφ'V (v + w) (isEvenVec_add_vec hv hw))
    calc f (φ' v * φ' w) = f (φ' v) * f (φ' w) :=
          hmul (φ' v) (hφ'V v hv) (φ' w) (hφ'V w hw)
      _ = φ v * φ w := by rw [hφ'f v hv, hφ'f w hw]
      _ = φ (v + w) := (hperm.1 v w hv hw).symm
      _ = f (φ' (v + w)) := (hφ'f (v + w) (isEvenVec_add_vec hv hw)).symm
  · intro v hv
    have h3 : φ v = 1 ↔ v = 0 := by
      constructor
      · intro hv1
        exact hperm.2.1 v 0 hv h0ev (hv1.trans hφ0.symm)
      · intro hv0
        rw [hv0]
        exact hφ0
    rw [(hker (φ' v) (hφ'V v hv)).symm, hφ'f v hv]
    exact h3.trans Set.mem_singleton_iff.symm
  · intro x hx
    obtain ⟨v, hv, hveq⟩ := (hperm.2.2.1 (f x)).1 (hfB x hx)
    refine ⟨v, hv, ?_⟩
    apply hdiff (φ' v) (hφ'V v hv) x hx
    rw [hφ'f v hv, hveq]
  · intro h hh
    obtain ⟨σ, hσAlt, hσ⟩ := hperm.2.2.2.1 h hh
    exact ⟨σ, hσAlt, act h σ hσ hh⟩
  · intro σ hσAlt
    obtain ⟨h, hh, hσ⟩ := hperm.2.2.2.2 σ hσAlt
    exact ⟨h, hh, act h σ hσ hh⟩

theorem isNatModA5_of_hom {V K B H : Subgroup G} (f : G → G) (hKV : K ≤ V)
    (hVK : V ≤ normalizer (K : Set G)) (hHV : H ≤ normalizer (V : Set G))
    (hHK : H ≤ normalizer (K : Set G)) (hfB : ∀ v ∈ V, f v ∈ B)
    (hmul : ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w) (hker : ∀ v ∈ V, f v = 1 ↔ v ∈ K)
    (hsurj : ∀ b ∈ B, ∃ v ∈ V, f v = b)
    (hconj : ∀ h ∈ H, ∀ v ∈ V, f (h * v * h⁻¹) = h * f v * h⁻¹)
    (hperm : ∃ φ : (Fin 5 → ZMod 2) → G,
      IsPermModuleVia IsEvenVec φ B H (alternatingGroup (Fin 5))) :
    IsNatModA5 V K H := by
  obtain ⟨φ, hφ⟩ := hperm
  obtain ⟨φ', h, -⟩ :=
    exists_natMod_lift_of_hom f hKV hVK hHV hHK hfB hmul hker hsurj hconj hφ
  exact ⟨φ', h⟩

end CFSG.OddStandard.SmallF3.Omega
