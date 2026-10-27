module

public import CFSG.LargeExtraspecial.AS35ZSOr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

noncomputable local instance : Fintype (IsoVec n) := Fintype.ofFinite _

@[expose] noncomputable def isoSmul (g : SUid frob n) (x : IsoVec n) : IsoVec n :=
  ⟨g • x.1, (smul_ne_zero_iff_ne g).2 x.2.1, by rw [herm_smul_smul, x.2.2]⟩

@[expose] noncomputable def isoPerm (g : SUid frob n) : IsoVec n ≃ IsoVec n where
  toFun := isoSmul g
  invFun := isoSmul g⁻¹
  left_inv x := Subtype.ext (inv_smul_smul g x.1)
  right_inv x := Subtype.ext (smul_inv_smul g x.1)

noncomputable abbrev fam (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) (IsoVec n → V) :=
  Submodule.pi Set.univ fun x => lineA ρ x.1

noncomputable abbrev Φ₀ : (IsoVec n → V) →ₗ[ZMod 2] V :=
  ∑ x : IsoVec n, LinearMap.proj x

noncomputable abbrev Ψ₀ (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) : (IsoVec n → V) →ₗ[ZMod 2] V :=
  ∑ x : IsoVec n, (oLine ρ x.1).comp (LinearMap.proj x)

theorem Φ₀_apply (a : IsoVec n → V) : Φ₀ a = ∑ x, a x := by simp [Φ₀]

theorem Ψ₀_apply (a : IsoVec n → V) : Ψ₀ ρ a = ∑ x, oLine ρ x.1 (a x) := by simp [Ψ₀]

@[expose] noncomputable def famSmul (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) (g : SUid frob n)
    (a : IsoVec n → V) : IsoVec n → V :=
  fun y => rs ρ g (a (isoSmul g⁻¹ y))

theorem Φ₀_famSmul (g : SUid frob n) (a : IsoVec n → V) :
    Φ₀ (famSmul ρ g a) = rs ρ g (Φ₀ a) := by
  rw [Φ₀_apply, Φ₀_apply, map_sum]
  exact Fintype.sum_equiv (isoPerm g⁻¹) _ _ fun y => rfl

theorem famSmul_mem (g : SUid frob n) {a : IsoVec n → V} (ha : a ∈ fam ρ) :
    famSmul ρ g a ∈ fam ρ := by
  intro y _
  have := apply_mem_lineA (ρ := ρ) g (isoSmul g⁻¹ y).2.2 (ha (isoSmul g⁻¹ y) (Set.mem_univ _))
  have e : g • (isoSmul g⁻¹ y).1 = y.1 := smul_inv_smul g y.1
  rw [e] at this
  exact this

open Classical in
theorem single_mem_fam (x : IsoVec n) {v : V} (hv : v ∈ lineA ρ x.1) :
    (Pi.single x v : IsoVec n → V) ∈ fam ρ := by
  intro y _
  by_cases hy : y = x
  · subst hy
    rw [Pi.single_eq_same]
    exact hv
  · rw [Pi.single_eq_of_ne hy]
    exact (lineA ρ y.1).zero_mem

open Classical in
theorem Φ₀_single (x : IsoVec n) (v : V) : Φ₀ (Pi.single x v : IsoVec n → V) = v := by
  rw [Φ₀_apply, Finset.sum_eq_single x (fun y _ hy => by rw [Pi.single_eq_of_ne hy])
    (fun hx => absurd (Finset.mem_univ x) hx), Pi.single_eq_same]

open Classical in
theorem Ψ₀_single (x : IsoVec n) (v : V) :
    Ψ₀ ρ (Pi.single x v : IsoVec n → V) = oLine ρ x.1 v := by
  rw [Ψ₀_apply, Finset.sum_eq_single x (fun y _ hy => by rw [Pi.single_eq_of_ne hy, map_zero])
    (fun hx => absurd (Finset.mem_univ x) hx), Pi.single_eq_same]

namespace ZSHyp

variable [FiniteDimensional (ZMod 2) V] (h : ZSHyp n q ρ)
include h

theorem Ψ₀_famSmul (g : SUid frob n) {a : IsoVec n → V} (ha : a ∈ fam ρ) :
    Ψ₀ ρ (famSmul ρ g a) = rs ρ g (Ψ₀ ρ a) := by
  rw [Ψ₀_apply, Ψ₀_apply, map_sum]
  refine Fintype.sum_equiv (isoPerm g⁻¹) _ _ fun y => ?_
  have hx := ha (isoSmul g⁻¹ y) (Set.mem_univ _)
  have e := h.oLine_smul g (isoSmul g⁻¹ y).2.1 (isoSmul g⁻¹ y).2.2 hx
  have e2 : g • (isoSmul g⁻¹ y).1 = y.1 := smul_inv_smul g y.1
  rw [e2] at e
  exact e

theorem polar_Ψ₀ {a b : IsoVec n → V} (ha : a ∈ fam ρ) (hb : b ∈ fam ρ) :
    polar q (Ψ₀ ρ a) (Ψ₀ ρ b) = polar q (Φ₀ a) (Φ₀ b) := by
  have hsum : ∀ u w : IsoVec n → V,
      polar q (∑ x, u x) (∑ y, w y) = ∑ x, ∑ y, polar q (u x) (w y) := fun u w => by
    simp only [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_comm
  rw [Ψ₀_apply, Ψ₀_apply, Φ₀_apply, Φ₀_apply, hsum, hsum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact h.polar_oLine x.2.1 x.2.2 y.2.1 y.2.2 (ha x (Set.mem_univ _)) (hb y (Set.mem_univ _))

noncomputable abbrev Wsp (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V :=
  (LinearMap.ker (Φ₀ ∘ₗ (fam ρ).subtype)).map (Ψ₀ ρ ∘ₗ (fam ρ).subtype)

theorem Wsp_eq_bot : Wsp ρ = ⊥ := by
  have hinv : ∀ g : PG n, ∀ w ∈ Wsp ρ, ρ g w ∈ Wsp ρ := by
    intro g w hw
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨⟨a, ha⟩, hker, rfl⟩ := hw
    refine ⟨⟨famSmul ρ g' a, famSmul_mem g' ha⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker] at hker ⊢
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hker ⊢
      rw [Φ₀_famSmul, hker, map_zero]
    · simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [h.Ψ₀_famSmul g' ha]
      rfl
  rcases h.irred _ hinv with hb | ht
  · exact hb
  · exfalso
    have hiso : ∀ v ∈ Wsp ρ, ∀ w ∈ Wsp ρ, polar q v w = 0 := by
      rintro _ ⟨⟨a, ha⟩, hka, rfl⟩ _ ⟨⟨b, hb⟩, hkb, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hka hkb
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hka hkb ⊢
      rw [h.polar_Ψ₀ ha hb, hka, hkb, polar_zero_left]
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2)
      (by rw [h.finrank_eq]; have := h.four_le; omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (h.nondeg.1 v fun w => hiso v (ht ▸ Submodule.mem_top) w (ht ▸ Submodule.mem_top))

theorem exists_J : ∃ J : V →ₗ[ZMod 2] V, (∀ g : PG n, ∀ v, ρ g (J v) = J (ρ g v)) ∧
    ∀ x : IsoVec n, ∀ a ∈ lineA ρ x.1, J a = oLine ρ x.1 a := by
  classical
  set Φ := Φ₀ ∘ₗ (fam ρ).subtype with hΦ
  set Ψ := Ψ₀ ρ ∘ₗ (fam ρ).subtype with hΨ
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← h.iSup_lineA_eq_top, iSup_le_iff]
    intro x v hv
    exact ⟨⟨Pi.single x v, single_mem_fam x hv⟩, Φ₀_single x v⟩
  have hker : LinearMap.ker Φ ≤ LinearMap.ker Ψ := by
    intro a ha
    have : Ψ a ∈ Wsp ρ := ⟨a, ha, rfl⟩
    rw [h.Wsp_eq_bot, Submodule.mem_bot] at this
    exact this
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective Φ hsurj
  have hσa : ∀ v, Φ (σ v) = v := fun v => by rw [← LinearMap.comp_apply, hσ, LinearMap.id_apply]
  have hJΦ : ∀ a, Ψ (σ (Φ a)) = Ψ a := by
    intro a
    have hm : σ (Φ a) - a ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker, map_sub, hσa, sub_self]
    have h0 := hker hm
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
    exact h0
  refine ⟨Ψ ∘ₗ σ, fun g v => ?_, fun x a ha => ?_⟩
  · obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    set a := σ v with ha
    have hv : v = Φ a := (hσa v).symm
    have e1 : ρ (QuotientGroup.mk g') v = Φ ⟨famSmul ρ g' a.1, famSmul_mem g' a.2⟩ := by
      rw [hv]
      exact (Φ₀_famSmul g' a.1).symm
    rw [e1]
    change ρ (QuotientGroup.mk g') (Ψ (σ v)) = Ψ (σ (Φ _))
    rw [hJΦ]
    exact (h.Ψ₀_famSmul g' a.2).symm
  · have e : Φ ⟨Pi.single x a, single_mem_fam x ha⟩ = a := Φ₀_single x a
    calc (Ψ ∘ₗ σ) a = Ψ (σ (Φ ⟨Pi.single x a, single_mem_fam x ha⟩)) := by rw [e]; rfl
      _ = Ψ ⟨Pi.single x a, single_mem_fam x ha⟩ := hJΦ _
      _ = oLine ρ x.1 a := Ψ₀_single x a

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
