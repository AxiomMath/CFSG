module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringsAbstract

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.QuasithinUnique.Setup.SL2Modules


section Gen

variable {F : Type*} [Field F] {G : Type*} [Group G] {k : Type*} [Field k] {V : Type*}
  [AddCommGroup V] [Module k V]

theorem fixSub_stable_of_hom (ρ : Representation k G V) (R : SL2 F →* G) (Q : Subgroup G)
    (hx : ∀ c : F, ∀ q ∈ Q, (R (uSL c))⁻¹ * q * R (uSL c) ∈ Q)
    (hx' : ∀ c : F, ∀ q ∈ Q, R (uSL c) * q * (R (uSL c))⁻¹ ∈ Q)
    (hy : ∀ c : F, ∀ q ∈ Q, (R (vSL c))⁻¹ * q * R (vSL c) ∈ Q)
    (hy' : ∀ c : F, ∀ q ∈ Q, R (vSL c) * q * (R (vSL c))⁻¹ ∈ Q)
    (g : SL2 F) {w : V} (hw : w ∈ fixSub ρ Q) : ρ (R g) w ∈ fixSub ρ Q := by
  let S : Subgroup (SL2 F) :=
    { carrier := {g | (∀ w ∈ fixSub ρ Q, ρ (R g) w ∈ fixSub ρ Q) ∧
        (∀ w ∈ fixSub ρ Q, ρ (R g)⁻¹ w ∈ fixSub ρ Q)}
      one_mem' := by simp
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [map_mul R, ← act_mul]
          exact ha1 _ (hb1 w hw)
        · rw [map_mul R, mul_inv_rev, ← act_mul]
          exact hb2 _ (ha2 w hw)
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [map_inv R]; exact ha2 w hw
        · rw [map_inv R, inv_inv]; exact ha1 w hw }
  have hmem : ∀ x : SL2 F, x ∈ S ↔ (∀ w ∈ fixSub ρ Q, ρ (R x) w ∈ fixSub ρ Q) ∧
      (∀ w ∈ fixSub ρ Q, ρ (R x)⁻¹ w ∈ fixSub ρ Q) := fun x => Iff.rfl
  have := mem_of_upper_lower S (MonoidHom.id _) (fun c => ?_) (fun c => ?_) g
  · exact ((hmem g).1 this).1 w hw
  · refine (hmem _).2 ⟨fun w hw => act_mem_fixSub ρ (hx c) hw, fun w hw => ?_⟩
    exact act_mem_fixSub ρ (by simpa using hx' c) hw
  · refine (hmem _).2 ⟨fun w hw => act_mem_fixSub ρ (hy c) hw, fun w hw => ?_⟩
    exact act_mem_fixSub ρ (by simpa using hy' c) hw

theorem vSL_eq_conj {F : Type*} [Field F] (c : F) :
    (vSL c : SL2 F) = WSL * uSL (-c) * WSL⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [vSL, uSL, WSL]

end Gen

section Main

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  (a : TwN)

include hf hK hσ in
theorem hatY_eq (c : orbitField TwistTag.E6 K σ a) :
    hatY hf hK σ hσ a c = (twistedE6CoverData hf hK σ hσ).nhat a *
      hatX hf hK σ hσ a (-c) * ((twistedE6CoverData hf hK σ hσ).nhat a)⁻¹ := by
  refine Subtype.ext ?_
  show minOrbitHom σ a (vSL c) = (((twistedE6CoverData hf hK σ hσ).nhat a :
    ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) * minOrbitHom σ a (uSL (-c)) *
      ((((twistedE6CoverData hf hK σ hσ).nhat a : ↥(TwistedE6.fixedGroup K σ)) :
        ↥(e6Data_valid.minGroup K)))⁻¹
  rw [nhat_coe hf hK σ hσ a, vSL_eq_conj, map_mul, map_mul, map_inv]

include hf hK hσ in
theorem hatX_norm (c : orbitField TwistTag.E6 K σ a) (q : ↥(TwistedE6.fixedGroup K σ))
    (hq : q ∈ (twistedE6CoverData hf hK σ hσ).datum.Us a) :
    (hatX hf hK σ hσ a c)⁻¹ * q * hatX hf hK σ hσ a c ∈
        (twistedE6CoverData hf hK σ hσ).datum.Us a ∧
      hatX hf hK σ hσ a c * q * (hatX hf hK σ hσ a c)⁻¹ ∈
        (twistedE6CoverData hf hK σ hσ).datum.Us a := by
  have hx : hatX hf hK σ hσ a c ∈ (twistedE6CoverData hf hK σ hσ).datum.X a :=
    (twistedE6CoverRankOne hf hK σ hσ).x_mem a c
  refine ⟨?_, (twistedE6CoverData hf hK σ hσ).datum.X_normUs a _ hx q hq⟩
  have := (twistedE6CoverData hf hK σ hσ).datum.X_normUs a _ (inv_mem hx) q hq
  simpa using this

include hf hK hσ in
theorem hatY_norm (c : orbitField TwistTag.E6 K σ a) (q : ↥(TwistedE6.fixedGroup K σ))
    (hq : q ∈ (twistedE6CoverData hf hK σ hσ).datum.Us a) :
    (hatY hf hK σ hσ a c)⁻¹ * q * hatY hf hK σ hσ a c ∈
        (twistedE6CoverData hf hK σ hσ).datum.Us a ∧
      hatY hf hK σ hσ a c * q * (hatY hf hK σ hσ a c)⁻¹ ∈
        (twistedE6CoverData hf hK σ hσ).datum.Us a := by
  set D := (twistedE6CoverData hf hK σ hσ).datum with hD
  set n := (twistedE6CoverData hf hK σ hσ).nhat a with hn
  have hnD : D.n a = n := rfl
  have h1 : n⁻¹ * q * n ∈ D.Us a := by
    have := D.n_normUs' a q hq
    rwa [hnD] at this
  have hn' : ∀ v ∈ D.Us a, n * v * n⁻¹ ∈ D.Us a := fun v hv => by
    have := D.n_normUs a v hv
    rwa [hnD] at this
  rw [hatY_eq hf K hK σ hσ a c]
  refine ⟨?_, ?_⟩
  · have e : (n * hatX hf hK σ hσ a (-c) * n⁻¹)⁻¹ * q * (n * hatX hf hK σ hσ a (-c) * n⁻¹) =
        n * ((hatX hf hK σ hσ a (-c))⁻¹ * (n⁻¹ * q * n) * hatX hf hK σ hσ a (-c)) * n⁻¹ := by
      group
    rw [e]
    exact hn' _ (hatX_norm hf K hK σ hσ a (-c) _ h1).1
  · have e : (n * hatX hf hK σ hσ a (-c) * n⁻¹) * q * (n * hatX hf hK σ hσ a (-c) * n⁻¹)⁻¹ =
        n * (hatX hf hK σ hσ a (-c) * (n⁻¹ * q * n) * (hatX hf hK σ hσ a (-c))⁻¹) * n⁻¹ := by
      group
    rw [e]
    exact hn' _ (hatX_norm hf K hK σ hσ a (-c) _ h1).2

include hf hK hσ in
theorem twStringOfHighest_holds : TwStringOfHighest hf K hK σ hσ := by
  intro k _ _ _ V _ _ ρ y χ J a hρ ht
  classical
  set C := twistedE6CoverData hf hK σ hσ with hC
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (twistedCover_split hf hK σ hσ k)
  let _ : Algebra (orbitField TwistTag.E6 K σ a) k :=
    ((algebraMap K k).comp (orbitField TwistTag.E6 K σ a).subtype).toAlgebra
  have hcard : Nat.card (orbitField TwistTag.E6 K σ a) = 2 ^ twNdig f a := by
    rw [card_orbitField_e6 hf hK σ hσ a]
    have h : (TwistTag.E6.orbit a).card = if a.val < 2 then 2 else 1 := by
      revert a; decide
    unfold twNdig
    split_ifs at h ⊢
    · rw [h, ← pow_mul, mul_comm]
    · rw [h, pow_one]
  have hFst : ∀ g : SL2 (orbitField TwistTag.E6 K σ a), ∀ w ∈ fixSub ρ (C.datum.Us a),
      ρ (Rhat hf hK σ hσ a g) w ∈ fixSub ρ (C.datum.Us a) := by
    intro g w hw
    refine fixSub_stable_of_hom ρ (Rhat hf hK σ hσ a) (C.datum.Us a) ?_ ?_ ?_ ?_ g hw
    · intro c q hq
      exact (hatX_norm hf K hK σ hσ a c q hq).1
    · intro c q hq
      exact (hatX_norm hf K hK σ hσ a c q hq).2
    · intro c q hq
      exact (hatY_norm hf K hK σ hσ a c q hq).1
    · intro c q hq
      exact (hatY_norm hf K hK σ hσ a c q hq).2
  have hfix : ∀ f0 ∈ fixSub ρ (C.datum.Us a),
      (∀ c : orbitField TwistTag.E6 K σ a, ρ (hatX hf hK σ hσ a c) f0 = f0) →
      ∃ c : k, f0 = c • y := by
    intro f0 hf0 hfu
    have hfU : f0 ∈ C.datum.fixU ρ := by
      intro u hu
      obtain ⟨x, hx, v, hv, rfl⟩ := C.datum.U_eq a u hu
      obtain ⟨c, rfl⟩ := (twistedE6CoverRankOne hf hK σ hσ).mem_lX_iff a |>.1 hx
      rw [← act_mul, hf0 v hv]
      exact hfu c
    exact C.datum.fixU_eq_smul hρ hμ hfU
  have hvu : ∀ c : orbitField TwistTag.E6 K σ a, ρ (hatX hf hK σ hσ a c) y = y := fun c =>
    ht.1 _ (C.datum.X_le a ((twistedE6CoverRankOne hf hK σ hσ).x_mem a c))
  have hεy : ∀ z : (orbitField TwistTag.E6 K σ a)ˣ,
      ρ (hatH hf hK σ hσ a z) y = χ (hatH hf hK σ hσ a z) • y := fun z =>
    ht.2.2.1 _ ((twistedE6CoverRankOne hf hK σ hσ).hh_mem a z)
  obtain ⟨J', hJ', hε, hfin, hemp, hwt⟩ := string_data hcard (ρ.comp (Rhat hf hK σ hσ a)) ht.2.1
    (fixSub ρ (C.datum.Us a))
    (fun g hg => ht.1 g (C.datum.Us_le a hg)) hFst hfix hvu
    (fun z => χ (hatH hf hK σ hσ a z)) hεy
  exact ⟨J', hJ', hε, hfin, hemp, hwt⟩

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
