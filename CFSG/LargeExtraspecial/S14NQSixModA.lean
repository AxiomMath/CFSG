module

public import CFSG.LargeExtraspecial.S14NQSixEich
public import CFSG.LargeExtraspecial.S14NQSixOrd3
public import CFSG.LargeExtraspecial.S8FiveC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S2
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

abbrev A0 (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (p : V) : Submodule (ZMod 2) M :=
  fixOf ρ (radFix q ⊥ p : Set (V ≃ₗ[ZMod 2] V))

@[expose] noncomputable def eichlerElt (hq : q.polarBilin.Nondegenerate) (u w : V) :
    omegaGroup q hq :=
  ⟨eichler q u w, eichler_mem_omegaGroup hq u w⟩

@[expose] noncomputable def zElt (hq : q.polarBilin.Nondegenerate) (e₁ f₁ e₂ f₂ : V) :
    omegaGroup q hq :=
  eichlerElt hq e₁ e₂ * eichlerElt hq f₁ f₂

structure Plus6 (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (p p₁ e₁ f₁ e₂ f₂ : V) : Prop where
  hV : finrank (ZMod 2) V = 6
  hM : finrank (ZMod 2) M = 8
  hp0 : p ≠ 0
  hp : q p = 0
  hp₁ : q p₁ = 0
  hpp₁ : polar q p p₁ = 1
  hD : RadDecomp ρ ⊥ ⊤ p p₁
  B : HypBasis q p p₁ e₁ f₁ e₂ f₂
  faith : ∀ y : omegaGroup q hq,
    (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) →
      (∀ v ∈ A0 ρ p, ρ y v = v) → (y : V ≃ₗ[ZMod 2] V) = 1

omit [FiniteDimensional (ZMod 2) M] in
theorem mapsTo_A0 (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) {p : V} (hp0 : p ≠ 0)
    (hp : q p = 0) (g : omegaGroup q hq) (hgp : (g : V ≃ₗ[ZMod 2] V) p = p) {v : M}
    (hv : v ∈ A0 ρ p) : ρ g v ∈ A0 ρ p := by
  rw [mem_fixOf] at hv ⊢
  intro k hk
  have hk' : ((g⁻¹ * k * g : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈ radFix q ⊥ p := by
    have h := (map_conj_radFix hq hp0 hp (by rw [perp_bot]; exact Submodule.mem_top)
      (mem_omegaGroup.mp g.2).1 (by rw [fixGroup_bot]; exact Subgroup.mem_top _)
      (k : V ≃ₗ[ZMod 2] V)).mp (by rw [hgp]; exact hk)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have e : k * g = g * (g⁻¹ * k * g) := by group
  calc ρ k (ρ g v) = ρ (k * g) v := by rw [map_mul, LinearEquiv.mul_apply]
    _ = ρ (g * (g⁻¹ * k * g)) v := by rw [e]
    _ = ρ g (ρ (g⁻¹ * k * g) v) := by rw [map_mul, LinearEquiv.mul_apply]
    _ = ρ g v := by rw [hv _ hk']

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_p_of_mem_fixGroup {p p₁ : V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) : g p = p :=
  (mem_fixGroup_sup_span_pair.mp hg).2.1

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_p₁_of_mem_fixGroup {p p₁ : V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) : g p₁ = p₁ :=
  (mem_fixGroup_sup_span_pair.mp hg).2.2

namespace Plus6

variable {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ e₁ f₁ e₂ f₂ : V}
  (P : Plus6 ρ p p₁ e₁ f₁ e₂ f₂)
include P

theorem dims {N : Submodule (ZMod 2) M} (hN : ∀ e : omegaGroup q hq, ∀ v ∈ N, ρ e v ∈ N) :
    4 ∣ finrank (ZMod 2) N ∧
      finrank (ZMod 2) N = 2 * finrank (ZMod 2) (N ⊓ A0 ρ p : Submodule (ZMod 2) M) := by
  obtain ⟨h1, -, h3⟩ := S8.dvd_and_two_mul_of_invariant ρ (m := 3) (by norm_num)
    (by rw [P.hV]) P.hp0 P.hp P.hp₁ P.hpp₁ P.hD hN
  exact ⟨by simpa using h1, h3⟩

theorem finrank_A0 : finrank (ZMod 2) (A0 ρ p) = 4 := by
  have h := (P.dims (N := ⊤) fun _ _ _ => Submodule.mem_top).2
  rw [finrank_top, P.hM, top_inf_eq] at h
  omega

omit [FiniteDimensional (ZMod 2) M] in
theorem p₁_ne_zero : p₁ ≠ 0 := by
  rintro h
  have := P.hpp₁
  rw [h, polar_zero_right] at this
  exact zero_ne_one this

omit [FiniteDimensional (ZMod 2) M] in
theorem z_mem_fixGroup :
    (zElt hq e₁ f₁ e₂ f₂ : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
  mul_mem (S2.eichler_mem_fixGroup P.B.he₁ P.B.he₂') (S2.eichler_mem_fixGroup P.B.hf₁ P.B.hf₂')

omit [FiniteDimensional (ZMod 2) M] in
theorem z_cube (v : M) :
    ρ (zElt hq e₁ f₁ e₂ f₂) (ρ (zElt hq e₁ f₁ e₂ f₂) (ρ (zElt hq e₁ f₁ e₂ f₂) v)) = v := by
  have h3 : zElt hq e₁ f₁ e₂ f₂ ^ 3 = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    exact P.B.z_pow_three)
  have := congrArg (fun x => ρ x v) h3
  simpa only [pow_three, map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id_eq]
    using this

omit [FiniteDimensional (ZMod 2) M] P in
theorem rho_eichler_sq {u w : V} (huw : polar q u w = 0) (v : M) :
    ρ (eichlerElt hq u w) (ρ (eichlerElt hq u w) v) = v := by
  have h2 : eichlerElt hq u w * eichlerElt hq u w = 1 :=
    Subtype.ext (eichler_mul_self huw)
  have := congrArg (fun x => ρ x v) h2
  simpa only [map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id_eq] using this

omit [FiniteDimensional (ZMod 2) M] P in
theorem le_fixSpace {e : V} {x : omegaGroup q hq}
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) e) :
    A0 ρ p ⊓ fixOf ρ (radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) e :
      Set (V ≃ₗ[ZMod 2] V)) ≤ A0 ρ p ⊓ fixSpace (ρ x) := by
  rintro v ⟨hvA, hv⟩
  exact ⟨hvA, mem_fixSpace.mpr ((mem_fixOf ρ).mp hv x hx)⟩

theorem finrank_fix_z :
    finrank (ZMod 2) (A0 ρ p ⊓ fixSpace (ρ (zElt hq e₁ f₁ e₂ f₂)) : Submodule (ZMod 2) M) =
      2 := by
  have he₁0 := P.B.e₁_ne_zero
  have hf₂0 : f₂ ≠ 0 := by
    rintro h
    have := P.B.e₂f₂
    rw [h, polar_zero_right] at this
    exact zero_ne_one this
  have he₂0 : e₂ ≠ 0 := by
    rintro h
    have := P.B.e₂f₂
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have he₁f₂ : e₁ ≠ f₂ := by
    rintro h
    have := P.B.e₁f₁
    rw [h, P.B.f₂f₁] at this
    exact zero_ne_one this
  have haF : (eichlerElt hq e₁ e₂ : V ≃ₗ[ZMod 2] V) ∈
      fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
    S2.eichler_mem_fixGroup P.B.he₁ P.B.he₂'
  have ha'F : (eichlerElt hq f₁ f₂ : V ≃ₗ[ZMod 2] V) ∈
      fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
    S2.eichler_mem_fixGroup P.B.hf₁ P.B.hf₂'
  have hbF : (eichlerElt hq e₁ f₂ : V ≃ₗ[ZMod 2] V) ∈
      fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
    S2.eichler_mem_fixGroup P.B.he₁ P.B.hf₂'
  have hmem0 : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hF0 : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hdim0 : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * 3 := by
    rw [perp_bot, finrank_top, P.hV]
  have htop : OmegaInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) := fun _ _ _ _ => Submodule.mem_top
  have hF₁ := sup_span_pair_inf_perp_eq_bot hF0 (hmem0 p) (hmem0 p₁) P.hpp₁
  have hd₁ : finrank (ZMod 2) (perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) + 2 =
      finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) :=
    finrank_perp_sup_span_pair hq hF0 (hmem0 p) (hmem0 p₁) P.hpp₁
  rw [hdim0] at hd₁
  have h3 : 3 ≤ finrank (ZMod 2) (perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) := by omega
  obtain ⟨R1inv, R1dec⟩ := timmesfeld_2_1_b2 ρ hF0 (m := 3) le_rfl hdim0 htop (hmem0 p)
    (hmem0 p₁) P.hp0 P.hp P.hp₁ P.hpp₁ P.hD P.B.he₁ P.B.hf₁ he₁0 P.B.qe₁ P.B.qf₁ P.B.e₁f₁
  have hR1 : finrank (ZMod 2) (A0 ρ p) = 2 * finrank (ZMod 2) (A0 ρ p ⊓
      fixOf ρ (radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) e₁ : Set (V ≃ₗ[ZMod 2] V)) :
        Submodule (ZMod 2) M) := by
    have h := (S2.finrank_eq_two_mul ρ hF₁ h3 R1inv P.B.he₁ P.B.hf₁ he₁0
      P.B.f₁_ne_zero P.B.qe₁ P.B.qf₁ R1dec).2
    rw [top_inf_eq] at h
    exact h
  obtain ⟨R2inv, R2dec⟩ := timmesfeld_2_1_b2 ρ hF0 (m := 3) le_rfl hdim0 htop (hmem0 p)
    (hmem0 p₁) P.hp0 P.hp P.hp₁ P.hpp₁ P.hD P.B.hf₂' P.B.he₂' hf₂0 P.B.qf₂ P.B.qe₂ P.B.f₂e₂
  have hR2 : finrank (ZMod 2) (A0 ρ p) = 2 * finrank (ZMod 2) (A0 ρ p ⊓
      fixOf ρ (radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) f₂ : Set (V ≃ₗ[ZMod 2] V)) :
        Submodule (ZMod 2) M) := by
    have h := (S2.finrank_eq_two_mul ρ hF₁ h3 R2inv P.B.hf₂' P.B.he₂' hf₂0
      he₂0 P.B.qf₂ P.B.qe₂ R2dec).2
    rw [top_inf_eq] at h
    exact h
  rw [P.finrank_A0] at hR1 hR2
  have haR : (eichlerElt hq e₁ e₂ : V ≃ₗ[ZMod 2] V) ∈
      radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) e₁ :=
    ⟨eichler_mem_pointRadical P.B.qe₁ P.B.e₁e₂, haF⟩
  have hbR : (eichlerElt hq e₁ f₂ : V ≃ₗ[ZMod 2] V) ∈
      radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) e₁ :=
    ⟨eichler_mem_pointRadical P.B.qe₁ P.B.e₁f₂, hbF⟩
  have ha'R : (eichlerElt hq f₁ f₂ : V ≃ₗ[ZMod 2] V) ∈
      radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) f₂ := by
    refine ⟨?_, ha'F⟩
    change eichler q f₁ f₂ ∈ pointRadical q f₂
    rw [eichler_comm P.B.qf₁ P.B.qf₂ P.B.f₁f₂]
    exact eichler_mem_pointRadical P.B.qf₂ P.B.f₂f₁
  have hbR2 : (eichlerElt hq e₁ f₂ : V ≃ₗ[ZMod 2] V) ∈
      radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) f₂ := by
    refine ⟨?_, hbF⟩
    change eichler q e₁ f₂ ∈ pointRadical q f₂
    rw [eichler_comm P.B.qe₁ P.B.qf₂ P.B.e₁f₂]
    exact eichler_mem_pointRadical P.B.qf₂ P.B.f₂e₁
  refine finrank_inf_fixSpace_eq_two (Ta := ρ (eichlerElt hq e₁ e₂))
    (Ta' := ρ (eichlerElt hq f₁ f₂)) (Tb := ρ (eichlerElt hq e₁ f₂)) P.finrank_A0
    (map_mul ρ _ _) P.z_cube
    (fun v hv => mapsTo_A0 ρ P.hp0 P.hp _ (apply_p_of_mem_fixGroup P.z_mem_fixGroup) hv)
    (fun v hv => mapsTo_A0 ρ P.hp0 P.hp _ (apply_p_of_mem_fixGroup haF) hv)
    (fun v hv => mapsTo_A0 ρ P.hp0 P.hp _ (apply_p_of_mem_fixGroup ha'F) hv)
    (LinearEquiv.ext fun v => rho_eichler_sq (ρ := ρ) P.B.e₁e₂ v)
    (LinearEquiv.ext fun v => rho_eichler_sq (ρ := ρ) P.B.f₁f₂ v) (by omega) (by omega)
    (le_fixSpace haR) ((le_fixSpace hbR).trans inf_le_right) (le_fixSpace ha'R)
    ((le_fixSpace hbR2).trans inf_le_right) (fun h => ?_) (fun h => ?_)
  · have hz1 := P.faith _ P.z_mem_fixGroup fun v hv => mem_fixSpace.mp (h hv)
    have h' := P.B.z_e₁
    rw [show eichler q e₁ e₂ * eichler q f₁ f₂ = (zElt hq e₁ f₁ e₂ f₂ : V ≃ₗ[ZMod 2] V) from rfl,
      hz1] at h'
    exact he₁f₂ (by simpa using h')
  · have hb1 := P.faith _ hbF fun v hv => mem_fixSpace.mp (h hv)
    exact eichler_ne_one hq P.B.qe₁ P.B.e₁f₂
      (linearIndependent_pair_iff.mpr ⟨he₁0, hf₂0, he₁f₂⟩) hb1

theorem finrank_normKer_z :
    finrank (ZMod 2) (A0 ρ p ⊓ normKer (ρ (zElt hq e₁ f₁ e₂ f₂)) : Submodule (ZMod 2) M) =
      2 := by
  have hAz : ∀ v ∈ A0 ρ p, ρ (zElt hq e₁ f₁ e₂ f₂) v ∈ A0 ρ p := fun v hv =>
    mapsTo_A0 ρ P.hp0 P.hp _ (apply_p_of_mem_fixGroup P.z_mem_fixGroup) hv
  have hsum := ord3_finrank P.z_cube hAz
  rw [P.finrank_fix_z, P.finrank_A0] at hsum
  omega

end Plus6

end CFSG.LargeExtraspecial.S14
