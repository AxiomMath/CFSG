module

public import CFSG.LargeExtraspecial.S2SixLevi
public import CFSG.LargeExtraspecial.S2Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_zero_right eichler_conj
  eichler_add_smul_self)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

@[expose] def Realizes (F : Submodule (ZMod 2) V) (N : Submodule (ZMod 2) M)
    (α : omegaGroup q hq → omegaGroup q hq) (τ : M →ₗ[ZMod 2] M) : Prop :=
  (∀ v ∈ N, τ v ∈ N) ∧ (∀ v ∈ N, τ v = 0 → v = 0) ∧
    ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → ∀ v ∈ N,
      τ (ρ g v) = ρ (α g) (τ v)

variable {ρ}

omit [FiniteDimensional (ZMod 2) M] in
theorem Realizes.conj {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    {α : omegaGroup q hq → omegaGroup q hq} {τ : M →ₗ[ZMod 2] M} (hτ : Realizes ρ F N α τ)
    (hN : OmegaInvariant ρ F N) {x : omegaGroup q hq} (hx : (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    Realizes ρ F N (fun g => x * α g * x⁻¹) ((ρ x : M →ₗ[ZMod 2] M) ∘ₗ τ) := by
  refine ⟨fun v hv => hN x hx _ (hτ.1 v hv),
    fun v hv h => hτ.2.1 v hv ((ρ x).map_eq_zero_iff.mp h), fun g hg v hv => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hτ.2.2 g hg v hv, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ← LinearEquiv.mul_apply (ρ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
  rfl

omit [FiniteDimensional (ZMod 2) M] in
theorem Realizes.restrict {F K : Submodule (ZMod 2) V} {N W : Submodule (ZMod 2) M}
    {α : omegaGroup q hq → omegaGroup q hq} {τ : M →ₗ[ZMod 2] M} (hτ : Realizes ρ F N α τ)
    (hKF : fixGroup K ≤ fixGroup F) (hWN : W ≤ N) (hτW : ∀ v ∈ W, τ v ∈ W) :
    Realizes ρ K W α τ :=
  ⟨hτW, fun v hv => hτ.2.1 v (hWN hv), fun g hg v hv => hτ.2.2 g (hKF hg) v (hWN hv)⟩

omit [FiniteDimensional (ZMod 2) M] in
theorem Realizes.mem_fix {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    {α : omegaGroup q hq → omegaGroup q hq} {τ : M →ₗ[ZMod 2] M} (hτ : Realizes ρ F N α τ)
    (hα : IsAutOn F α) {a : V} (hαa : MapsRad F α a a) {v : M}
    (hv : v ∈ N ⊓ fixOf ρ (radFix q F a : Set (V ≃ₗ[ZMod 2] V))) :
    τ v ∈ N ⊓ fixOf ρ (radFix q F a : Set (V ≃ₗ[ZMod 2] V)) := by
  refine ⟨hτ.1 v hv.1, (mem_fixOf ρ).mpr fun t ht => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hα.surj t ht.2
  have hsa : (s : V ≃ₗ[ZMod 2] V) ∈ radFix q F a := (hαa s hs).mpr ht
  rw [← hτ.2.2 s hs v hv.1, ((mem_fixOf ρ).mp hv.2) s hsa]

omit [FiniteDimensional (ZMod 2) M] in
theorem eq_self_of_finrank_eq_one {W : Submodule (ZMod 2) M} (hW : finrank (ZMod 2) W = 1)
    {τ : M →ₗ[ZMod 2] M} (hτW : ∀ v ∈ W, τ v ∈ W) (hτinj : ∀ v ∈ W, τ v = 0 → v = 0) :
    ∀ v ∈ W, τ v = v := by
  obtain ⟨c, hc⟩ := exists_smul_of_finrank_eq_one hW hτW
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot fun h : W = ⊥ => by
      rw [h, finrank_bot] at hW
      exact zero_ne_one hW
    exact hw0 (hτinj w hw (by rw [hc w hw, zero_smul]))
  · intro v hv
    rw [hc v hv, one_smul]

variable (ρ)

theorem eq_self_of_finrank_two {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    {α : omegaGroup q hq → omegaGroup q hq} (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (hdim : finrank (ZMod 2) (perp q F) = 2 * 2) (hN : OmegaInvariant ρ F N) {p p₁ : V}
    (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ F N p p₁) (hdimN : finrank (ZMod 2) N = 2)
    (hαp : MapsRad F α p p)
    (hρ : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → ∀ v ∈ N,
      ρ (α g) v = ρ g v)
    (t : omegaGroup q hq) (ht : (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p) : α t = t := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hK2 : finrank (ZMod 2) (perp q K) = 2 := by
    have : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
      finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
    omega
  let E : V → omegaGroup q hq := fun v => ⟨eichler q p v, eichler_mem_omegaGroup hq p v⟩
  have hEL : ∀ v ∈ perp q K, (E v : V ≃ₗ[ZMod 2] V) ∈ radFix q F p := fun v hv =>
    (mem_radFix_iff hq hp0 hp hpF).mpr
      ⟨v, (mem_perp_sup_span_pair.mp hv).1, (mem_perp_sup_span_pair.mp hv).2.1, rfl⟩
  obtain ⟨φ, hφK, hφE, hadd⟩ := hα.exists_radFix_map hpF hp0 hp hpp₁ hαp
  replace hφE : ∀ v ∈ perp q K, α (E v) = E (φ v) := hφE
  have htwo := finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD
  have hW₁ : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) = 1 := by
    omega
  have hE1 : ∀ u ∈ perp q K, eichler q p u = 1 → u = 0 := fun u hu h =>
    eq_of_eichler_eq hp hpp₁ hu (Submodule.zero_mem _) (h.trans (eichler_zero_right q p).symm)
  have hφ0' : φ 0 = 0 := by
    have h := hadd 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    rwa [add_zero, vec_add_self] at h
  have hφ0 : ∀ v ∈ perp q K, v ≠ 0 → φ v ≠ 0 := by
    intro v hv hv0 h
    refine hv0 (hE1 v hv (congrArg Subtype.val (hα.inj (E v) 1 (hEL v hv).2 (one_mem _) ?_)))
    rw [hα.map_one, hφE v hv, h]
    exact Subtype.ext (eichler_zero_right q p)
  have hKF : ∀ u ∈ perp q K, u ≠ 0 → (∀ w ∈ N, ρ (E u) w = w) → q u = 0 := by
    intro u hu hu0 htriv
    obtain ⟨-, hpu, -⟩ := mem_perp_sup_span_pair.mp hu
    by_contra hqu
    have hqu1 : q u = 1 := (zmod2_eq_zero_or_eq_one _).resolve_left hqu
    have hup : u ≠ p := by
      rintro rfl
      rw [hp] at hqu1
      exact zero_ne_one hqu1
    have hli : LinearIndependent (ZMod 2) ![p, u] :=
      linearIndependent_pair_iff.mpr ⟨hp0, hu0, Ne.symm hup⟩
    have hb0 := (timmesfeld_2_1_b0 ρ hF (m := 2) le_rfl hdim hN hp₁F hpF hp₁0 hp₁ hp hp₁p
      hD.symm (E u) (hEL u hu) (eichler_ne_one hq hp hpu hli)
      (not_isTypeA_eichler hq hp0 hp hpu hqu1)).1
    have hNle : N ≤ N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) := by
      intro w hw
      rw [← hb0]
      exact ⟨hw, mem_fixSpace.mpr (htriv w hw)⟩
    have hbot : N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) = ⊥ := by
      rw [eq_bot_iff, ← hD.2]
      exact le_inf (inf_le_left.trans hNle) le_rfl
    rw [hbot, finrank_bot] at hW₁
    exact zero_ne_one hW₁
  have hS : ∀ v ∈ perp q K, φ v ≠ v → q (v + φ v) = 0 := by
    intro v hv hne
    have hu : v + φ v ∈ perp q K := Submodule.add_mem _ hv (hφK v hv)
    have hu0 : v + φ v ≠ 0 := fun h => hne (by
      rw [add_eq_zero_iff_eq_neg, vec_neg] at h
      exact h.symm)
    refine hKF _ hu hu0 fun w hw => ?_
    have hpv := (mem_perp_sup_span_pair.mp hv).2.1
    have hpφv := (mem_perp_sup_span_pair.mp (hφK v hv)).2.1
    have hEuv : E (v + φ v) = E v * α (E v) := by
      rw [hφE v hv]
      exact Subtype.ext (eichler_mul hpv hpφv).symm
    have hvv : E v * E v = 1 := Subtype.ext (eichler_mul_self hpv)
    rw [hEuv, map_mul, LinearEquiv.mul_apply, hρ _ (hEL v hv).2 w hw,
      ← LinearEquiv.mul_apply, ← map_mul, hvv, map_one]
    rfl
  have ha2 : ∀ v ∈ perp q K, v ≠ 0 → q v = 0 → q (φ v) = 0 := by
    intro v hv hv0 hqv
    obtain ⟨hvF, hpv, hp₁v⟩ := mem_perp_sup_span_pair.mp hv
    obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hpF hvF hp0 hv0 hp hqv
    have hgΩ := radGen_le_omegaFix hq F hg
    set g' : omegaGroup q hq := ⟨g, hgΩ.1⟩
    have hg'F : (g' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hgΩ.2
    have h1 := hα.mapsRad_apply hp0 hp hpF hαp hg'F
    change MapsRad F α (g p) _ at h1
    rw [hgp] at h1
    set v' := (α g' : V ≃ₗ[ZMod 2] V) p with hv'
    have hαgO : (α g' : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp (α g').2).1
    have hv'q : q v' = 0 := by
      rw [hv', TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hαgO, hp]
    have hv'0 : v' ≠ 0 := fun h => hp0 ((α g' : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h)
    have hvp : v ≠ p := by
      rintro rfl
      rw [polar_comm, hp₁v] at hpp₁
      exact zero_ne_one hpp₁
    have hpv' : p ≠ v' := by
      intro h
      rw [← h] at h1
      exact hvp (IsAutOn.eq_of_mapsRad hF (by omega) hvF hpF hv0 hp0 hqv hp h1 hαp)
    have hEv : (E v : V ≃ₗ[ZMod 2] V) ∈ radFix q F v :=
      ⟨(eichler_mem_pointRadical_inf hp hqv hpv).2, eichler_mem_fixGroup hpF hvF⟩
    have hαEv : (α (E v) : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p ⊓ pointRadical q v' :=
      ⟨((hαp _ (hEL v hv).2).mp (hEL v hv)).1, ((h1 _ (hEL v hv).2).mp hEv).1⟩
    rw [hφE v hv] at hαEv
    rcases mem_pointRadical_inf_of_orthogonal hq hp0 hv'0 hpv' hp hαEv with h | h
    · exact absurd (hE1 _ (hφK v hv) h) (hφ0 v hv hv0)
    · have hpv'0 : polar q p v' = 0 := by
        by_contra hne
        rw [CFSG.ClassicalGroups.Orthogonal.eichler_of_not (fun h' => hne h'.2)] at h
        exact hφ0 v hv hv0 (hE1 _ (hφK v hv) h)
      have hv''K : v' + polar q v' p₁ • p ∈ perp q K := by
        rw [mem_perp_sup_span_pair]
        refine ⟨Submodule.add_mem _ (apply_mem_perp hαgO (hα.mem g' hg'F) hpF)
          (Submodule.smul_mem _ _ hpF), ?_, ?_⟩
        · rw [polar_add_right, polar_smul_right, polar_self_eq_zero, hpv'0, smul_zero,
            add_zero]
        · simp only [polar_add_right, polar_smul_right, hp₁p, smul_eq_mul, mul_one]
          rw [polar_comm q p₁ v', zmod2_add_self]
      have := eq_of_eichler_eq hp hpp₁ (hφK v hv) hv''K
        (h.trans (eichler_add_smul_self hp v' _).symm)
      rw [this, map_add_eq, map_smul_zmod2, hp, mul_zero, add_zero, polar_smul_right,
        polar_comm q v' p, hpv'0, smul_zero, add_zero, hv'q]
  have hsing : ∀ v ∈ perp q K, q v = 0 → φ v = v := by
    intro v hv hqv
    by_cases hv0 : v = 0
    · rw [hv0, hφ0']
    by_contra hne
    have h1 := hS v hv hne
    rw [map_add_eq, hqv, ha2 v hv hv0 hqv, zero_add, zero_add] at h1
    have h2 := polar_eq_one_of_finrank_eq_two hq hK hK2 hv (hφK v hv) hv0 (hφ0 v hv hv0)
      (Ne.symm hne)
    rw [h1] at h2
    exact zero_ne_one h2
  have hall : ∀ v ∈ perp q K, φ v = v := by
    intro v hv
    rcases zmod2_eq_zero_or_eq_one (q v) with hqv | hqv
    · exact hsing v hv hqv
    by_contra hne
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hqv
      exact zero_ne_one hqv
    set u := v + φ v with hu
    have huK : u ∈ perp q K := Submodule.add_mem _ hv (hφK v hv)
    have hqu : q u = 0 := hS v hv hne
    have hu0 : u ≠ 0 := by
      rintro h0
      rw [h0, map_zero] at hqu
      exact absurd hqu (by rw [hu] at h0; exact fun _ => hne (by
        rw [add_eq_zero_iff_eq_neg, vec_neg] at h0
        exact h0.symm))
    have hvu : v ≠ u := by
      intro h
      apply hφ0 v hv hv0
      have : v + φ v = v + 0 := by rw [← hu, ← h, add_zero]
      exact add_left_cancel this
    have hpol := polar_eq_one_of_finrank_eq_two hq hK hK2 hv huK hv0 hu0 hvu
    have hφv : φ v = v + u := by rw [hu, ← add_assoc, vec_add_self, zero_add]
    have hqφv : q (φ v) = 0 := by
      rw [hφv, map_add_eq, hqv, hqu, hpol]
      decide
    have h1 := hsing u huK hqu
    have h2 := hsing (φ v) (hφK v hv) hqφv
    have hv' : v = u + φ v := by rw [hu, add_assoc, vec_add_self, add_zero]
    apply hne
    calc φ v = φ (u + φ v) := by rw [← hv']
      _ = φ u + φ (φ v) := hadd u huK (φ v) (hφK v hv)
      _ = u + φ v := by rw [h1, h2]
      _ = v := hv'.symm
  obtain ⟨u, hu, htu⟩ := exists_eq_eichler_perp hq hpF hp0 hp hpp₁ ht
  have htE : t = E u := Subtype.ext htu
  rw [htE, hφE u hu, hall u hu]

end S2

end CFSG.LargeExtraspecial
