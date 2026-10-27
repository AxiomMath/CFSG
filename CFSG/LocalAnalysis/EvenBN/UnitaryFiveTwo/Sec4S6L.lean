module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6K
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6LMod
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSEight

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Lam

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

theorem Data.v_mem_K₂ : d.v ∈ d.K₂ := ⟨vSU, vSU_mem_K₂sub, rfl⟩

theorem Data.K₂_le_K₃ : d.K₂ ≤ d.K₃ := d.pull_mono K₂sub_le_K₃sub

include hKU in
theorem Data.exists_w₁ : ∃ k : ↥K₀, Data.theta h hf k = d.v :=
  Data.exists_theta_eq h hKU hf (Data.K₂_le_K₃ Data.v_mem_K₂)

noncomputable def Data.w₁ : ↥K₀ := Classical.choose (Data.exists_w₁ h hKU hf)

theorem Data.theta_w₁ : Data.theta h hf (Data.w₁ h hKU hf) = d.v :=
  Classical.choose_spec (Data.exists_w₁ h hKU hf)

@[expose] noncomputable def Data.U₁ : Subgroup G :=
  (d.X₂.comap (Data.theta h hf)).map K₀.subtype

@[expose] noncomputable def Data.Lam₁ : Subgroup G :=
  Data.U₁ h hf ⊔ (Data.U₁ h hf).map (MulAut.conj ((Data.w₁ h hKU hf : ↥K₀) : G)).toMonoidHom

theorem Data.mem_U₁ {x : G} : x ∈ Data.U₁ h hf ↔ ∃ hx : x ∈ K₀, Data.theta h hf ⟨x, hx⟩ ∈ d.X₂ := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hx, hθ⟩
    exact ⟨⟨x, hx⟩, hθ, rfl⟩

theorem Data.U₁_le_K₀ : Data.U₁ h hf ≤ K₀ := by
  rintro _ ⟨k, -, rfl⟩
  exact k.2

include hKU in
theorem Data.w₁_mem_K₀ : ((Data.w₁ h hKU hf : ↥K₀) : G) ∈ K₀ := (Data.w₁ h hKU hf).2

include hKU in
theorem Data.Lam₁_le_K₀ : Data.Lam₁ h hKU hf ≤ K₀ := by
  refine sup_le (Data.U₁_le_K₀ h hf) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact mul_mem (mul_mem (Data.w₁_mem_K₀ h hKU hf) (Data.U₁_le_K₀ h hf hu))
    (inv_mem (Data.w₁_mem_K₀ h hKU hf))

include hKU in
theorem Data.range_theta : (Data.theta h hf).range = d.K₃ := by
  apply le_antisymm
  · rintro _ ⟨k, rfl⟩
    exact Data.theta_mem_K₃ h hKU hf k
  · intro x hx
    obtain ⟨k, hk⟩ := Data.exists_theta_eq h hKU hf hx
    exact ⟨k, hk⟩

theorem Data.K₂_eq_sup_conj : d.K₂ = d.X₂ ⊔ d.X₂.map (MulAut.conj d.v).toMonoidHom := by
  show d.pull K₂sub = d.pull X₂sub ⊔ (d.pull X₂sub).map (MulAut.conj d.v).toMonoidHom
  rw [K₂sub_eq_sup_conj, Data.pull_sup]
  congr 1
  show (X₂sub.map (MulAut.conj vSU).toMonoidHom).map d.ι =
    (X₂sub.map d.ι).map (MulAut.conj d.v).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, Data.v]

include hKU in
theorem Data.theta_conj_w₁ (k : ↥K₀) :
    Data.theta h hf (Data.w₁ h hKU hf * k * (Data.w₁ h hKU hf)⁻¹) =
      d.v * Data.theta h hf k * d.v⁻¹ := by
  rw [map_mul, map_mul, map_inv, Data.theta_w₁]

include hKU in
theorem Data.theta_mem_K₂_of_mem_Lam₁ (k : ↥K₀) (hk : (k : G) ∈ Data.Lam₁ h hKU hf) :
    Data.theta h hf k ∈ d.K₂ := by
  have key : Data.Lam₁ h hKU hf ≤ (d.K₂.comap (Data.theta h hf)).map K₀.subtype := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hx0, hθ⟩ := (Data.mem_U₁ h hf).1 hx
      exact ⟨⟨x, hx0⟩, Subgroup.mem_comap.2 (d.pull_mono X₂sub_le_K₂sub hθ), rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hy0, hθ⟩ := (Data.mem_U₁ h hf).1 hy
      refine ⟨Data.w₁ h hKU hf * ⟨y, hy0⟩ * (Data.w₁ h hKU hf)⁻¹, ?_, rfl⟩
      refine Subgroup.mem_comap.2 ?_
      rw [Data.theta_conj_w₁ h hKU hf]
      exact mul_mem (mul_mem Data.v_mem_K₂ (d.pull_mono X₂sub_le_K₂sub hθ)) (inv_mem Data.v_mem_K₂)
  obtain ⟨c, hc, hck⟩ := key hk
  have : c = k := Subtype.ext hck
  rw [← this]
  exact hc

include hKU in
theorem Data.mem_Lam₁_of_theta_mem (k : ↥K₀) (hk : Data.theta h hf k ∈ d.K₂) :
    (k : G) ∈ Data.Lam₁ h hKU hf := by
  rw [Data.K₂_eq_sup_conj] at hk
  have hsub : d.X₂ ⊔ d.X₂.map (MulAut.conj d.v).toMonoidHom ≤
      ((Data.Lam₁ h hKU hf).subgroupOf K₀).map (Data.theta h hf) := by
    refine sup_le ?_ ?_
    · intro x hx
      have hx3 : x ∈ d.K₃ := Data.K₂_le_K₃ (d.pull_mono X₂sub_le_K₂sub hx)
      obtain ⟨l, hl⟩ := Data.exists_theta_eq h hKU hf hx3
      refine ⟨l, ?_, hl⟩
      show (l : G) ∈ Data.Lam₁ h hKU hf
      exact mem_sup_left ((Data.mem_U₁ h hf).2 ⟨l.2, by rw [hl]; exact hx⟩)
    · rintro _ ⟨y, hy, rfl⟩
      have hy3 : y ∈ d.K₃ := Data.K₂_le_K₃ (d.pull_mono X₂sub_le_K₂sub hy)
      obtain ⟨l, hl⟩ := Data.exists_theta_eq h hKU hf hy3
      have hlU : (l : G) ∈ Data.U₁ h hf := (Data.mem_U₁ h hf).2 ⟨l.2, by rw [hl]; exact hy⟩
      refine ⟨Data.w₁ h hKU hf * l * (Data.w₁ h hKU hf)⁻¹, ?_, ?_⟩
      · show ((Data.w₁ h hKU hf : ↥K₀) : G) * (l : G) * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹ ∈
          Data.Lam₁ h hKU hf
        exact mem_sup_right ⟨l, hlU, rfl⟩
      · rw [Data.theta_conj_w₁ h hKU hf, hl]
        rfl
  obtain ⟨l, hl, hlk⟩ := hsub hk
  have : l = k := Data.theta_injective h hf hlk
  rw [← this]
  exact hl

include hKU in
theorem Data.theta_mem_K₂_iff (k : ↥K₀) :
    (k : G) ∈ Data.Lam₁ h hKU hf ↔ Data.theta h hf k ∈ d.K₂ :=
  ⟨Data.theta_mem_K₂_of_mem_Lam₁ h hKU hf k, Data.mem_Lam₁_of_theta_mem h hKU hf k⟩

include hKU in
theorem Data.w₁_mem_Lam₁ : ((Data.w₁ h hKU hf : ↥K₀) : G) ∈ Data.Lam₁ h hKU hf :=
  (Data.theta_mem_K₂_iff h hKU hf _).2 (by rw [Data.theta_w₁]; exact Data.v_mem_K₂)

@[expose] noncomputable def Data.thetaLam : ↥(Data.Lam₁ h hKU hf) →* G :=
  (Data.theta h hf).comp (Subgroup.inclusion (Data.Lam₁_le_K₀ h hKU hf))

include hKU in
theorem Data.thetaLam_injective : Function.Injective (Data.thetaLam h hKU hf) := by
  intro a b hab
  have := Data.theta_injective h hf hab
  exact Subtype.ext (congrArg (fun x : ↥K₀ => (x : G)) this)

include hKU in
theorem Data.range_thetaLam : (Data.thetaLam h hKU hf).range = d.K₂ := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Data.theta_mem_K₂_of_mem_Lam₁ h hKU hf ⟨x, Data.Lam₁_le_K₀ h hKU hf x.2⟩ x.2
  · intro y hy
    obtain ⟨k, hk⟩ := Data.exists_theta_eq h hKU hf (Data.K₂_le_K₃ hy)
    have hkL : (k : G) ∈ Data.Lam₁ h hKU hf :=
      Data.mem_Lam₁_of_theta_mem h hKU hf k (by rw [hk]; exact hy)
    exact ⟨⟨k, hkL⟩, hk⟩

@[expose] noncomputable def Data.lamK₂ : ↥(Data.Lam₁ h hKU hf) ≃* ↥d.K₂ :=
  (MonoidHom.ofInjective (Data.thetaLam_injective h hKU hf)).trans
    (MulEquiv.subgroupCongr (Data.range_thetaLam h hKU hf))

@[expose] noncomputable def Data.K₂Equiv : ↥d.K₂ ≃* ↥K₂sub :=
  (Subgroup.equivMapOfInjective K₂sub d.ι d.ι_injective).symm

@[expose] noncomputable def Data.lamEquiv :
    ↥(Data.Lam₁ h hKU hf) ≃* Matrix.SpecialLinearGroup (Fin 2) CFSG.Fischer.F4 :=
  ((Data.lamK₂ h hKU hf).trans Data.K₂Equiv).trans k2Equiv.symm

theorem Data.K₂_conj_mem_F {g f : G} (hg : g ∈ d.K₂) (hf : f ∈ d.F) : g * f * g⁻¹ ∈ d.F := by
  obtain ⟨n, hn, rfl⟩ := hg
  obtain ⟨φ, hφ, rfl⟩ := hf
  rw [Data.Hyp.ι_conj]
  exact ⟨_, normalizer_A₂sub_conj_mem_Fsub (K₂sub_le_normalizer_A₂sub hn) hφ, rfl⟩

end Lam

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
