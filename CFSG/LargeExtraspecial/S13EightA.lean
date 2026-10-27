module

public import CFSG.LargeExtraspecial.S13Dich
public import CFSG.LargeExtraspecial.S13FiveA
public import CFSG.LargeExtraspecial.S13SevenA
public import CFSG.LargeExtraspecial.S13TwoB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

variable (S g) in
@[expose] def IsLinked (U : Submodule (ZMod 2) S.Qt) : Prop :=
  ∀ v ∈ U, v ≠ 0 → ∃ h : S.M, v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∧
    U ≤ S.clSub (S.QG ⊓ S.Qa ((h : G) * g))

omit [Finite G] in
theorem IsLinked.mono {U U' : Submodule (ZMod 2) S.Qt} (hU : IsLinked S g U) (h : U' ≤ U) :
    IsLinked S g U' := fun v hv hv0 => by
  obtain ⟨k, rfl, hk⟩ := hU v (h hv) hv0
  exact ⟨k, rfl, h.trans hk⟩

theorem IsLinked.sup_pt (H : Hyp4 S g) {U : Submodule (ZMod 2) S.Qt} (hU : IsLinked S g U)
    {p : S.M} (hpU : U ≤ S.clSub (S.QG ⊓ S.Qa ((p : G) * g))) :
    IsLinked S g (U ⊔ (ZMod 2) ∙ S.cl ((p : G) * g * S.z * ((p : G) * g)⁻¹)) := by
  set P := S.cl ((p : G) * g * S.z * ((p : G) * g)⁻¹) with hP
  have hPp : P ∈ S.clSub (S.QG ⊓ S.Qa ((p : G) * g)) :=
    S.cl_mem_clSub ⟨conj_mem_QG' S p.2 H.conj_mem, S.conj_z_mem_Qa _⟩
      (conj_mem_QG' S p.2 H.conj_mem)
  have hUp : ∀ {h : S.M}, S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ U →
      P ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := fun hh => cl_mem_clSub_symm H (hpU hh)
  intro v hv hv0
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 t with rfl | rfl
  ·
    rw [zero_smul, add_zero] at hv0 ⊢
    obtain ⟨k, rfl, hk⟩ := hU _ hw hv0
    exact ⟨k, rfl, sup_le hk ((Submodule.span_singleton_le_iff_mem _ _).mpr (hUp hw))⟩
  rw [one_smul] at hv0 ⊢
  by_cases hw0 : w = 0
  ·
    subst hw0
    rw [zero_add]
    exact ⟨p, rfl, sup_le hpU ((Submodule.span_singleton_le_iff_mem _ _).mpr hPp)⟩
  obtain ⟨k, rfl, hk⟩ := hU _ hw hw0
  have hne : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ P := fun h =>
    hv0 (by rw [h]; exact add_self_vec (ZMod 2) P)
  obtain ⟨h₃, hh₃⟩ := exists_pt_add H (hpU hw) hne
  refine ⟨h₃, by rw [hh₃, add_comm], sup_le ?_ ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    obtain ⟨j, rfl, -⟩ := hU _ hx hx0
    exact cl_mem_clSub_of_add H hh₃.symm (hpU hx) (hk hx)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact cl_mem_clSub_of_add H hh₃.symm hPp (hUp hw)

theorem mem_Fbar_mul_iff (hN : NormalInMbar S K) (m : S.M) (g₀ : G) {v : S.Qt} :
    v ∈ Fbar S ((m : G) * g₀) K ↔ (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fbar S g₀ K := by
  change v ∈ fixSub S (Ebar S ((m : G) * g₀) K) ↔ _
  rw [Ebar_mul hN (rfl : (m : G) * g₀ = (m : G) * g₀)]
  exact mem_fixSub_map_conj_iff _ _ _

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem Fbar_mul_eq_of_mem {h : S.M}
    (hh : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Fbar S g K) :
    Fbar S ((h : G) * g) K = Fbar S g K := by
  have Yh : Hyp13 S ((h : G) * g) K := Y.mul rfl
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  rw [← Yh.span_pair_eq (cl_mem_Fbar Yh.H) (pt_ne_zero Y.H h) hk hk1,
    ← Y.span_pair_eq hh (pt_ne_zero Y.H h) hk hk1]

theorem Fbar_inf_clSub_le {e : S.M}
    (heP : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (heF : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∉ Fbar S g K) :
    Fbar S g K ⊓ S.clSub (S.QG ⊓ S.Qa ((e : G) * g)) ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  intro v hv
  obtain ⟨hvF, hve⟩ := Submodule.mem_inf.mp hv
  by_contra hva
  have hv0 : v ≠ 0 := fun h => hva (h ▸ zero_mem _)
  obtain ⟨m, hmK, rfl⟩ := Y.exists_eq_cl_of_mem_Fbar hvF hv0
  have hm1 : S.ρ m ≠ 1 := by
    intro h1
    apply hva
    rw [← ρ_cl_conj_z S m Y.haQ, h1]
    exact Submodule.mem_span_singleton_self _
  have hem := cl_mem_clSub_symm Y.H hve
  apply heF
  have hzB : S.z ∈ S.QG ⊓ S.Qa ((m : G) * g) := Subgroup.mem_inf.mpr ⟨S.z_mem_QG,
    S.z_mem_Qa (conj_mem_QG' S m.2 Y.haQ) (conj_ne_z' S m.2 Y.hne)⟩
  have h1 : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) :=
    Submodule.mem_inf.mpr ⟨heP, hem⟩
  have e2 : S.QG ⊓ S.Qa g ⊓ (S.QG ⊓ S.Qa ((m : G) * g)) =
      S.QG ⊓ S.Qa g ⊓ S.Qa ((m : G) * g) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rwa [clSub_inf hzB, e2, Y.timmesfeld_13_1 hmK hm1] at h1

theorem mem_span_of_fix_Fbar {σ : S.O} (hσ : σ ∈ S.Lbar g) (hσE : σ ∉ Ebar S g K)
    {φ : S.Qt} (hφ : φ ∈ Fbar S g K) (hfix : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) φ = φ) :
    φ ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  by_contra hφa
  have hφ0 : φ ≠ 0 := fun h => hφa (h ▸ zero_mem _)
  obtain ⟨m, hmK, rfl⟩ := Y.exists_eq_cl_of_mem_Fbar hφ hφ0
  set k := S.ρ m with hk
  have hk1 : k ≠ 1 := by
    intro h1
    apply hφa
    rw [← ρ_cl_conj_z S m Y.haQ, ← hk, h1]
    exact Submodule.mem_span_singleton_self _
  rw [← ρ_cl_conj_z S m Y.haQ, ← hk] at hfix
  have hinv := Y.inv_of_not_mem hσ hσE k hmK
  have hσa := Lbar_apply_cl Y.H hσ
  have e1 : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      ((k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    have e2 : σ * k = k⁻¹ * σ := by rw [← hinv]; group
    have := congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) e2
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hσa] at this
    exact this
  rw [e1] at hfix
  have hk3 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, Y.pow_three hmK]; rfl
  have h2 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      S.cl (g * S.z * g⁻¹) := by
    have := congrArg (k : S.Qt ≃ₗ[ZMod 2] S.Qt) hfix
    rw [apply_inv_apply_O] at this
    exact this.symm
  exact cl_conj_z_ne_zero S Y.haQ Y.hne
    (fix_eq_zero Y.card_K Y.fpf hmK hk1 _ (fix_of_fix_sq hk3 h2))

end Hyp13

theorem exists_Lbar_fix_add (H : Hyp4 S g) {e f : S.M}
    (haf : S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((f : G) * g)))
    (hef : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((f : G) * g)))
    (he : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∉
      (ZMod 2) ∙ S.cl ((f : G) * g * S.z * ((f : G) * g)⁻¹))
    (hae : S.cl (g * S.z * g⁻¹) + S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∉
      (ZMod 2) ∙ S.cl ((f : G) * g * S.z * ((f : G) * g)⁻¹)) :
    ∃ l ∈ S.Lbar ((f : G) * g),
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) ∧
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹)) =
        S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) +
          S.cl ((f : G) * g * S.z * ((f : G) * g)⁻¹) := by
  set a := S.cl (g * S.z * g⁻¹) with ha
  set ve := S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) with hve
  set vf := S.cl ((f : G) * g * S.z * ((f : G) * g)⁻¹) with hvf
  have Hf : Hyp4 S ((f : G) * g) := H.mul f
  have hAQ := H.conj_mem
  have hEQ := conj_mem_QG' S e.2 H.conj_mem
  have hAf := (mem_Qa_iff_cl_mem Hf.conj_mem Hf.conj_ne hAQ).mpr haf
  have hEf := (mem_Qa_iff_cl_mem Hf.conj_mem Hf.conj_ne hEQ).mpr hef
  obtain ⟨l₁, hl₁, h₁⟩ := exists_Lbar_apply_eq_add Hf.conj_mem Hf.conj_ne
    (Subgroup.mem_inf.mpr ⟨hEQ, hEf⟩) he
  obtain ⟨l₃, hl₃, h₃⟩ := exists_Lbar_apply_eq_add Hf.conj_mem Hf.conj_ne
    (Subgroup.mem_inf.mpr ⟨mul_mem hAQ hEQ, mul_mem hAf hEf⟩) (by rwa [S.cl_mul hAQ hEQ])
  rw [S.cl_mul hAQ hEQ] at h₃
  have hfix : ∀ l ∈ S.Lbar ((f : G) * g), (l : S.Qt ≃ₗ[ZMod 2] S.Qt) vf = vf :=
    fun l hl => Lbar_apply_cl Hf hl
  have hcase : ∀ l ∈ S.Lbar ((f : G) * g),
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a ∨ (l : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + vf := by
    intro l hl
    rcases mem_span_cl_iff.mp (S.sub_mem_span_of_mem_clSub hl haf) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by rw [hvf, ← h]; abel)
  have h2 : vf + vf = 0 := add_self_vec (ZMod 2) vf
  rcases hcase l₁ hl₁ with h1a | h1a
  · exact ⟨l₁, hl₁, h1a, h₁⟩
  rcases hcase l₃ hl₃ with h3a | h3a
  · refine ⟨l₃, hl₃, h3a, ?_⟩
    rw [map_add, h3a] at h₃
    have := congrArg (fun v => v - a) h₃
    simp only [add_sub_cancel_left] at this
    rw [this]
    abel
  · refine ⟨l₃ * l₁, mul_mem hl₃ hl₁, ?_, ?_⟩
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h1a, map_add, h3a, hfix l₃ hl₃, add_assoc,
        h2, add_zero]
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h₁, map_add, hfix l₃ hl₃]
      rw [map_add, h3a] at h₃
      have h3e : (l₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) ve = ve := by
        have := congrArg (fun v => v - (a + vf)) h₃
        simp only [add_sub_cancel_left] at this
        rw [this]
        abel
      rw [h3e]

end CFSG.LargeExtraspecial.S13
