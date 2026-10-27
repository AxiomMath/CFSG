module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KFrame
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KLift
public import CFSG.Dihedral.Glauberman.DicksonMaxTables

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem mul_sq_A4 : ∀ a b : alternatingGroup (Fin 4), a ^ 2 = 1 → b ^ 2 = 1 → (a * b) ^ 2 = 1 := by
  decide

abbrev cyc3A4 : alternatingGroup (Fin 4) :=
  ⟨swap 0 2 * swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem cyc3A4_fpf :
    ∀ g : alternatingGroup (Fin 4), g ^ 2 = 1 → g ≠ 1 → cyc3A4 * g * cyc3A4⁻¹ ≠ g := by
  decide

@[expose] def kleinA4 : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {g | g ^ 2 = 1}
  one_mem' := one_pow 2
  mul_mem' := fun {a b} ha hb => mul_sq_A4 a b ha hb
  inv_mem' := fun {a} ha => by
    have ha' : a ^ 2 = 1 := ha
    change a⁻¹ ^ 2 = 1
    rw [inv_pow, ha', inv_one]

instance decidableMemKleinA4 : DecidablePred (· ∈ kleinA4) := fun g =>
  decidable_of_iff (g ^ 2 = 1) Iff.rfl

theorem card_kleinA4 : Nat.card kleinA4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

omit [Finite X] [Finite F] in
theorem rho_eq_barX (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (g : X) : rho e g = e (barX L g) := by
  by_cases hg : g ∈ L
  · rw [rho_of_mem e hg, barX_of_mem hg]
  · simp [rho, barX, hg]

namespace Frame

variable {κ : X} (Fr : Frame A F κ)

@[expose] def QV : Subgroup (PSL2 F) := (Fr.V.subgroupOf L).map (rhoL Fr.e)

theorem rho_mem_QV {v : X} (hv : v ∈ Fr.V) : rho Fr.e v ∈ Fr.QV :=
  ⟨⟨v, (Fr.V_le_R hv).2⟩, hv, rhoL_apply _ _⟩

theorem exists_of_mem_QV {q : PSL2 F} (hq : q ∈ Fr.QV) : ∃ v ∈ Fr.V, rho Fr.e v = q := by
  obtain ⟨l, hl, rfl⟩ := hq
  exact ⟨l, hl, (rhoL_apply _ _).symm⟩

theorem QV_le_range : Fr.QV ≤ (psl2Sub Fr.K₀).range := by
  intro q hq
  obtain ⟨v, hv, rfl⟩ := Fr.exists_of_mem_QV hq
  exact (Fr.mem_V.mp hv).2

theorem card_QV (S : Gens A) : Nat.card Fr.QV = 4 := by
  obtain ⟨-, -, -, hcard, -⟩ := Fr.V_eq S
  have hVL : Fr.V ≤ L := Fr.V_le_R.trans inf_le_right
  have hinj : Function.Injective ((rhoL Fr.e).comp (Fr.V.subgroupOf L).subtype) := by
    intro a b h
    have h' : rho Fr.e (a : L) = rho Fr.e (b : L) := by
      rw [← rhoL_apply, ← rhoL_apply]
      exact h
    exact Subtype.ext (Subtype.ext (rho_injective Fr.e (Fr.V_le_R a.2) (Fr.V_le_R b.2) h'))
  rw [QV, ← Subgroup.range_subtype (Fr.V.subgroupOf L), ← MonoidHom.range_comp,
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv, hcard]

theorem card_le_four_of_le_range {Q : Subgroup (PSL2 F)} (hQ : IsPGroup 2 Q)
    (hQM : Q ≤ (psl2Sub Fr.K₀).range) : Nat.card Q ≤ 4 := by
  have hmap : (Q.comap (psl2Sub Fr.K₀)).map (psl2Sub Fr.K₀) = Q := by
    rw [Subgroup.map_comap_eq, inf_of_le_right hQM]
  have h2 : IsPGroup 2 (Q.comap (psl2Sub Fr.K₀)) :=
    hQ.comap_of_injective _ (psl2Sub_injective Fr.K₀)
  rw [← hmap, card_map_of_injective (psl2Sub_injective Fr.K₀)]
  exact Fr.card_le_four h2

theorem isSylowIn_of_card {Q : Subgroup (PSL2 F)} (hQ : IsPGroup 2 Q)
    (hQM : Q ≤ (psl2Sub Fr.K₀).range) (hQ4 : Nat.card Q = 4) :
    IsSylowIn Q (psl2Sub Fr.K₀).range := by
  refine ⟨hQM, hQ, fun P hPM hP hQP => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hQP (hQ4 ▸ Fr.card_le_four_of_le_range hP hPM)).symm

theorem exists_fpf_bar (S : Gens A) : ∃ y ∈ fieldCent Fr.σ, (∀ q ∈ Fr.QV, y * q * y⁻¹ ∈ Fr.QV) ∧
    ∀ q ∈ Fr.QV, q ≠ 1 → y * q * y⁻¹ ≠ q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : Fr.K₀) ≠ 0 := two_ne_zero_of_isOddPrimePower Fr.K₀_odd
  obtain ⟨H, ⟨φ⟩⟩ := CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup h2
  set ψ₀ : alternatingGroup (Fin 4) →* PSL2 F :=
    (psl2Sub Fr.K₀).comp (H.subtype.comp φ.symm.toMonoidHom) with hψ₀
  have hψ₀inj : Function.Injective ψ₀ :=
    (psl2Sub_injective Fr.K₀).comp ((subtype_injective H).comp φ.symm.injective)
  have hψ₀M : ∀ g, ψ₀ g ∈ (psl2Sub Fr.K₀).range := fun g => ⟨_, rfl⟩
  set V₀ : Subgroup (PSL2 F) := kleinA4.map ψ₀ with hV₀
  have hV₀4 : Nat.card V₀ = 4 := by rw [hV₀, card_map_of_injective hψ₀inj, card_kleinA4]
  have hV₀2 : IsPGroup 2 V₀ := IsPGroup.of_card (n := 2) (by rw [hV₀4]; norm_num)
  have hV₀M : V₀ ≤ (psl2Sub Fr.K₀).range := by
    rintro _ ⟨g, -, rfl⟩
    exact hψ₀M g
  have hQ2 : IsPGroup 2 Fr.QV :=
    ((A.isPGroup_T.to_le (Fr.V_le_R.trans inf_le_left)).comap_of_injective L.subtype
      (subtype_injective L)).map _
  obtain ⟨c, hcM, hc⟩ := IsSylowIn.exists_conj (Fr.isSylowIn_of_card hV₀2 hV₀M hV₀4)
    (Fr.isSylowIn_of_card hQ2 Fr.QV_le_range (Fr.card_QV S))
  have hMC : (psl2Sub Fr.K₀).range ≤ fieldCent Fr.σ := by
    rintro _ ⟨x, rfl⟩
    exact psl2Sub_mem_fieldCent Fr.mem_K₀ x
  refine ⟨c * ψ₀ cyc3A4 * c⁻¹, hMC (mul_mem (mul_mem hcM (hψ₀M _)) (inv_mem hcM)), ?_, ?_⟩
  · intro q hq
    rw [hc] at hq ⊢
    obtain ⟨_, ⟨g, hg, rfl⟩, rfl⟩ := hq
    have hg' : g ^ 2 = 1 := hg
    refine ⟨ψ₀ (cyc3A4 * g * cyc3A4⁻¹), ⟨_, ?_, rfl⟩, ?_⟩
    · change (cyc3A4 * g * cyc3A4⁻¹) ^ 2 = 1
      rw [conj_pow, hg', mul_one, mul_inv_cancel]
    · change c * ψ₀ (cyc3A4 * g * cyc3A4⁻¹) * c⁻¹ =
        c * ψ₀ cyc3A4 * c⁻¹ * (c * ψ₀ g * c⁻¹) * (c * ψ₀ cyc3A4 * c⁻¹)⁻¹
      rw [map_mul, map_mul, map_inv]
      group
  · intro q hq hq1 hfix
    rw [hc] at hq
    obtain ⟨_, ⟨g, hg, rfl⟩, rfl⟩ := hq
    have hg' : g ^ 2 = 1 := hg
    change c * ψ₀ g * c⁻¹ ≠ 1 at hq1
    change c * ψ₀ cyc3A4 * c⁻¹ * (c * ψ₀ g * c⁻¹) * (c * ψ₀ cyc3A4 * c⁻¹)⁻¹ =
      c * ψ₀ g * c⁻¹ at hfix
    have h1 : ψ₀ (cyc3A4 * g * cyc3A4⁻¹) = ψ₀ g := by
      rw [map_mul, map_mul, map_inv]
      have := congrArg (fun u => c⁻¹ * u * c) hfix
      calc ψ₀ cyc3A4 * ψ₀ g * (ψ₀ cyc3A4)⁻¹
          = c⁻¹ * (c * ψ₀ cyc3A4 * c⁻¹ * (c * ψ₀ g * c⁻¹) * (c * ψ₀ cyc3A4 * c⁻¹)⁻¹) * c := by
            group
        _ = ψ₀ g := by rw [this]; group
    have hg1 : g ≠ 1 := by
      rintro rfl
      apply hq1
      rw [map_one, mul_one, mul_inv_cancel]
    exact cyc3A4_fpf g hg' hg1 (hψ₀inj h1)

theorem exists_three (S : Gens A) : ∃ d ∈ L, d * κ = κ * d ∧ (∀ v ∈ Fr.V, d * v * d⁻¹ ∈ Fr.V) ∧
    ∀ v ∈ Fr.V, v ≠ 1 → d * v * d⁻¹ ≠ v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyC, hyN, hyfpf⟩ := Fr.exists_fpf_bar S
  obtain ⟨⟨g₀, hg₀⟩, hg₀y⟩ := QuotientGroup.mk_surjective (Fr.e.symm y)
  have hrho₀ : rho Fr.e g₀ = y := by
    rw [rho_of_mem Fr.e hg₀, hg₀y, MulEquiv.apply_symm_apply]
  have hVL : Fr.V ≤ L := Fr.V_le_R.trans inf_le_right
  have hV2 : IsPGroup 2 Fr.V := A.isPGroup_T.to_le (Fr.V_le_R.trans inf_le_left)
  obtain ⟨-, -, -, hcard, -⟩ := Fr.V_eq S
  have hVc : ∀ a ∈ Fr.V, ∀ b ∈ Fr.V, a * b = b * a := by
    intro a ha b hb
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := Fr.V)
      (by rw [hcard]; norm_num)
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hκN := le_normalizer (A := A) Fr.κ_C
  have hκg₀ : κ * g₀ * κ⁻¹ ∈ L := conj_mem_L (A := A) Fr.κ_C hg₀
  have hfix : barX L (κ * g₀ * κ⁻¹) = barX L g₀ := by
    apply Fr.e.injective
    rw [← rho_eq_barX, ← rho_eq_barX, hrho₀]
    have h := act_conj (A := A) Fr.e Fr.κ_C (L_le_C (A := A) hg₀)
    rw [act_of_mem_L Fr.e hκg₀, act_of_mem_L Fr.e hg₀, Fr.act_κ, hrho₀, conj_incl,
      semilinearAction_inr] at h
    rw [incl_injective F h]
    exact hyC
  have hnorm : ∀ v ∈ Fr.V, ∃ v' ∈ Fr.V, barX L (g₀ * v * g₀⁻¹) = barX L v' := by
    intro v hv
    obtain ⟨v', hv', hv'e⟩ := Fr.exists_of_mem_QV (hyN _ (Fr.rho_mem_QV hv))
    refine ⟨v', hv', Fr.e.injective ?_⟩
    rw [← rho_eq_barX, ← rho_eq_barX, hv'e, rho_mul Fr.e (mul_mem hg₀ (hVL hv)) (inv_mem hg₀),
      rho_mul Fr.e hg₀ (hVL hv), rho_inv Fr.e hg₀, hrho₀]
  obtain ⟨d, hdL, hdκ, hdV, hdbar⟩ := exists_lift hκN Fr.κ_sq hVL hV2
    (fun v hv => Fr.κ_comm v (Fr.V_le_R hv)) hVc hg₀ hfix hnorm
  refine ⟨d, hdL, hdκ, hdV, fun v hv hv1 hdv => ?_⟩
  have h1 := hdbar v hv
  rw [hdv] at h1
  have h2 := congrArg Fr.e h1
  rw [← rho_eq_barX, ← rho_eq_barX, rho_mul Fr.e (mul_mem hg₀ (hVL hv)) (inv_mem hg₀),
    rho_mul Fr.e hg₀ (hVL hv), rho_inv Fr.e hg₀, hrho₀] at h2
  have hv1' : rho Fr.e v ≠ 1 := fun h => hv1 (rho_eq_one Fr.e (Fr.V_le_R hv) h)
  exact hyfpf _ (Fr.rho_mem_QV hv) hv1' h2.symm

end Frame

end CFSG.ComponentClassification.HSFLit.L2K
