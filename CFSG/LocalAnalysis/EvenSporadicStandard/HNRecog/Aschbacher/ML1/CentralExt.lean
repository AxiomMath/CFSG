module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf
open scoped commutatorElement

private theorem commute_of_mem_preimage {E : Type} [Group E] (πb : E →* A5 × A5)
    (hsurj : Function.Surjective πb) (hcenter : πb.ker ≤ Subgroup.center E)
    {e₁ e₂ : E} (h₁ : (πb e₁).2 = 1) (h₂ : (πb e₂).1 = 1) : e₁ * e₂ = e₂ * e₁ := by
  classical
  haveI : Group.IsPerfect A5 :=
    ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩
  let S : Subgroup E := ((MonoidHom.snd A5 A5).comp πb).ker
  let φ : S →* A5 × A5 := πb.comp S.subtype
  have hS : ∀ {x : E}, x ∈ S ↔ (πb x).2 = 1 := fun {x} => by
    simp [S, MonoidHom.mem_ker]
  have hR : φ.range = (⊤ : Subgroup A5).prod (⊥ : Subgroup A5) := by
    apply le_antisymm
    · intro p hp
      obtain ⟨s, hs⟩ := hp
      rw [Subgroup.mem_prod]
      exact ⟨Subgroup.mem_top _, by rw [← hs]; simpa [φ] using hS.mp s.2⟩
    · intro p hp
      rw [Subgroup.mem_prod] at hp
      obtain ⟨-, hp2⟩ := hp
      have hp2' : p.2 = 1 := by simpa using hp2
      obtain ⟨e, he⟩ := hsurj p
      have heS : e ∈ S := by rw [hS, he, hp2']
      exact ⟨⟨e, heS⟩, by simp [φ, he]⟩
  have hperf : Group.IsPerfect φ.range := by
    rw [Subgroup.isPerfect_iff, hR, Subgroup.commutator_prod_prod]
    rw [show (⁅(⊤ : Subgroup A5), (⊤ : Subgroup A5)⁆) = ⊤ from by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top]
    simp [Subgroup.commutator_bot_left]
  have hmap_comm : Subgroup.map φ (commutator S) = φ.range := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top]
    exact Subgroup.isPerfect_iff.mp hperf
  have hcK : ∀ s : S, ⁅(s : E), e₂⁆ ∈ πb.ker := by
    intro s
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply Prod.ext <;> simp [commutatorElement_def, hS.mp s.2, h₂]
  have hcK' : ∀ s : S, ⁅(s : E), e₂⁆ ∈ Subgroup.center E := fun s => hcenter (hcK s)
  let c : S →* E :=
    { toFun := fun s => ⁅(s : E), e₂⁆
      map_one' := by simp
      map_mul' := fun s t => by
        have ht : ⁅(t : E), e₂⁆ ∈ Subgroup.center E := hcK' t
        have hs : ⁅(s : E), e₂⁆ ∈ Subgroup.center E := hcK' s
        change ⁅(s : E) * (t : E), e₂⁆ = ⁅(s : E), e₂⁆ * ⁅(t : E), e₂⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        rw [show (s : E) * ⁅(t : E), e₂⁆ * (s : E)⁻¹ = ⁅(t : E), e₂⁆ by
          rw [Subgroup.mem_center_iff.mp ht (s : E)]
          group]
        exact Subgroup.mem_center_iff.mp hs ⁅(t : E), e₂⁆ }
  have hcomm_le : commutator S ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcK' a) (c b)).symm
  have hker_le : φ.ker ≤ c.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have hcent : (s : E) ∈ Subgroup.center E := hcenter (by
      rw [MonoidHom.mem_ker]
      exact hs)
    change ⁅(s : E), e₂⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hcent e₂).symm
  have hsup : commutator S ⊔ φ.ker = ⊤ := by
    rw [eq_top_iff]
    intro s _
    have hsrange : φ s ∈ φ.range := ⟨s, rfl⟩
    rw [← hmap_comm] at hsrange
    obtain ⟨t, htC, htφ⟩ := hsrange
    have hmem : t⁻¹ * s ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, htφ, inv_mul_cancel]
    have hs_eq : s = t * (t⁻¹ * s) := by group
    rw [hs_eq]
    exact Subgroup.mul_mem_sup htC hmem
  have hc_top : c.ker = ⊤ :=
    eq_top_iff.mpr (hsup ▸ sup_le hcomm_le hker_le)
  have hc_one : c = 1 := MonoidHom.ext fun s => by
    have : s ∈ c.ker := by rw [hc_top]; exact Subgroup.mem_top s
    rwa [MonoidHom.mem_ker] at this
  have hce : ⁅e₁, e₂⁆ = 1 := by
    have h := DFunLike.congr_fun hc_one ⟨e₁, (hS (x := e₁)).mpr h₁⟩
    change c ⟨e₁, (hS (x := e₁)).mpr h₁⟩ = 1 at h
    exact h
  exact commutatorElement_eq_one_iff_mul_comm.mp hce

theorem sq_mem_of_inner_sq_mem {F : Type} [Group F] (Δ : Subgroup F) [Δ.Normal]
    (π : F →* A5 × A5) (hπ : Function.Surjective π) (hΔ : Δ ≤ π.ker)
    (hker : ∀ k ∈ π.ker, (∀ f : F, ⁅k, f⁆ ∈ Δ) ∧ k ^ 2 ∈ Δ)
    (hinner : ∀ (f : F) (a : A5), a ^ 2 = 1 → (π f = (a, 1) ∨ π f = (1, a)) → f ^ 2 ∈ Δ) :
    ∀ f : F, π f ^ 2 = 1 → f ^ 2 ∈ Δ := by
  classical
  let E := F ⧸ Δ
  let πb : E →* A5 × A5 := QuotientGroup.lift Δ π hΔ
  have hπb_mk : ∀ x : F, πb (QuotientGroup.mk x) = π x := fun x => QuotientGroup.lift_mk Δ hΔ x
  have hπb_surj : Function.Surjective πb := fun y => by
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨QuotientGroup.mk x, by rw [hπb_mk, hx]⟩
  have hK_center : πb.ker ≤ Subgroup.center E := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨kf, rfl⟩ := QuotientGroup.mk_surjective k
    obtain ⟨xf, rfl⟩ := QuotientGroup.mk_surjective x
    have hkf : kf ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπb_mk kf]
      exact hk
    have hcomm : ⁅kf, xf⁆ ∈ Δ := (hker kf hkf).1 xf
    have hce : ⁅(QuotientGroup.mk kf : E), (QuotientGroup.mk xf : E)⁆ = 1 := by
      change ⁅(QuotientGroup.mk' Δ) kf, (QuotientGroup.mk' Δ) xf⁆ = 1
      rw [← map_commutatorElement (QuotientGroup.mk' Δ) kf xf]
      exact (QuotientGroup.eq_one_iff (⁅kf, xf⁆)).mpr hcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hce).symm
  have hK_sq : ∀ k ∈ πb.ker, k ^ 2 = 1 := by
    intro k hk
    obtain ⟨kf, rfl⟩ := QuotientGroup.mk_surjective k
    have hkf : kf ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπb_mk kf]
      exact hk
    have hsq : kf ^ 2 ∈ Δ := (hker kf hkf).2
    have h2 : ((QuotientGroup.mk' Δ) (kf ^ 2) : E) = 1 :=
      (QuotientGroup.eq_one_iff (kf ^ 2)).mpr hsq
    rw [MonoidHom.map_pow] at h2
    exact h2
  intro f hf
  obtain ⟨a, b, hfab⟩ : ∃ a b : A5, π f = (a, b) := ⟨(π f).1, (π f).2, rfl⟩
  rw [hfab] at hf
  have ha : a ^ 2 = 1 := by
    have := congrArg Prod.fst hf
    simpa using this
  have hb : b ^ 2 = 1 := by
    have := congrArg Prod.snd hf
    simpa using this
  obtain ⟨f₁, hf₁⟩ := hπ (a, 1)
  obtain ⟨f₂, hf₂⟩ := hπ (1, b)
  have hf₁_sq : f₁ ^ 2 ∈ Δ := hinner f₁ a ha (Or.inl hf₁)
  have hf₂_sq : f₂ ^ 2 ∈ Δ := hinner f₂ b hb (Or.inr hf₂)
  let e₁ : E := QuotientGroup.mk f₁
  let e₂ : E := QuotientGroup.mk f₂
  let g : E := QuotientGroup.mk f
  have he₁ : πb e₁ = (a, 1) := by
    change πb (QuotientGroup.mk f₁) = (a, 1)
    rw [hπb_mk, hf₁]
  have he₂ : πb e₂ = (1, b) := by
    change πb (QuotientGroup.mk f₂) = (1, b)
    rw [hπb_mk, hf₂]
  have hg : πb g = (a, b) := by
    change πb (QuotientGroup.mk f) = (a, b)
    rw [hπb_mk, hfab]
  have he₁_sq : e₁ ^ 2 = 1 := by
    have h1 : ((QuotientGroup.mk' Δ) (f₁ ^ 2) : E) = 1 := by
      simpa using (QuotientGroup.eq_one_iff (f₁ ^ 2)).mpr hf₁_sq
    change ((QuotientGroup.mk' Δ) f₁ : E) ^ 2 = 1
    rw [← MonoidHom.map_pow]
    exact h1
  have he₂_sq : e₂ ^ 2 = 1 := by
    have h1 : ((QuotientGroup.mk' Δ) (f₂ ^ 2) : E) = 1 := by
      simpa using (QuotientGroup.eq_one_iff (f₂ ^ 2)).mpr hf₂_sq
    change ((QuotientGroup.mk' Δ) f₂ : E) ^ 2 = 1
    rw [← MonoidHom.map_pow]
    exact h1
  let k : E := (e₁ * e₂)⁻¹ * g
  have hke : k ∈ πb.ker := by
    rw [MonoidHom.mem_ker]
    change πb ((e₁ * e₂)⁻¹ * g) = 1
    rw [map_mul, map_inv, map_mul, he₁, he₂, hg]
    simp
  have hkcenter : k ∈ Subgroup.center E := hK_center hke
  have hksq : k ^ 2 = 1 := hK_sq k hke
  have he₁_2 : (πb e₁).2 = 1 := by rw [he₁]
  have he₂_1 : (πb e₂).1 = 1 := by rw [he₂]
  have hcomm_e : e₁ * e₂ = e₂ * e₁ :=
    commute_of_mem_preimage πb hπb_surj hK_center he₁_2 he₂_1
  have hg_decomp : g = e₁ * e₂ * k := by
    rw [show k = (e₁ * e₂)⁻¹ * g from rfl]
    group
  have hg_sq : g ^ 2 = 1 := by
    rw [hg_decomp]
    rw [Commute.mul_pow (Subgroup.mem_center_iff.mp hkcenter (e₁ * e₂))]
    rw [Commute.mul_pow hcomm_e]
    rw [he₁_sq, he₂_sq, hksq]
    simp
  have hf_sq : f ^ 2 ∈ Δ := by
    have h1 : ((QuotientGroup.mk' Δ) (f ^ 2) : E) = 1 := by
      rw [MonoidHom.map_pow]
      change g ^ 2 = 1
      exact hg_sq
    exact (QuotientGroup.eq_one_iff (f ^ 2)).mp (by simpa using h1)
  exact hf_sq

end CFSG.EvenSporadicStandard.HNRecog.ML1
