module

public import CFSG.LargeExtraspecial.AS35YSOmA
public import CFSG.LargeExtraspecial.AS35YSOmG
public import CFSG.LargeExtraspecial.AS35YSSym

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions AS35YR

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YS

theorem act0_pbar_fix_YS (hS : S.SixHyp) (hst : S.Asc512Standing) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {x : S.O} (hx : x ∈ S.PbarAsc g)
    (hxM : x ∈ S.Mbar) {v : V0_YS S}
    (hv : v ∈ commSpace (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL ⟨_, ht, htM, rfl⟩⟩)) :
    act0_YS hst ⟨x, hxM⟩ v = v := by
  obtain ⟨-, -, -, -, -, hcomm, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  obtain ⟨u, rfl⟩ := mem_commSpace_act0_YS hst _ hv
  rw [act0_YS_mk]
  congr 1
  exact Subtype.ext (hcomm x hx _ (sub_mem_commSpace _ _))

theorem act0_pbar_sub_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h : RadSing_YS S) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    {x : S.O} (hx : x ∈ S.PbarAsc g) (hxM : x ∈ S.Mbar) {v : V0_YS S}
    (hv : v ∈ fixSpace (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL ⟨_, ht, htM, rfl⟩⟩)) :
    act0_YS hst ⟨x, hxM⟩ v - v ∈
      commSpace (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL ⟨_, ht, htM, rfl⟩⟩) := by
  obtain ⟨-, -, -, -, -, -, hfix⟩ := S14.asc512PbarStmt G S hS g ht htM
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  induction v using Submodule.Quotient.induction_on with
  | _ u =>
    rw [mem_fixSpace, act0_YS_mk, mk_eq_mk_YS] at hv
    have hu : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u = 0 := by
      have hmem : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈
          fixW_YS S ⊓ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        ⟨hv, sub_mem_commSpace _ _⟩
      rwa [fixW_inf_commSpace_YS hS hst hnd htD, Submodule.mem_bot] at hmem
    have hu' : (u : S.Qt) ∈ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      mem_fixSpace.mpr (sub_eq_zero.mp hu)
    obtain ⟨u', hu'U, hu'e⟩ := exists_sub_eq_of_mem_commSpace_YS hS hst h htD (hfix x hx _ hu')
    rw [act0_YS_mk, ← Submodule.Quotient.mk_sub]
    have e : (⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) u, commU_YS_invariant hst hxM u.2⟩ - u : commU_YS S) =
        ⟨((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u',
          (commU_YS S).sub_mem (commU_YS_invariant hst (DbarAsc_subset_Mbar_YL htD) hu'U)
            hu'U⟩ :=
      Subtype.ext (by rw [Submodule.coe_sub]; exact hu'e.symm)
    rw [e]
    refine mem_commSpace.mpr ⟨Submodule.Quotient.mk ⟨u', hu'U⟩, ?_⟩
    rw [act0_YS_mk, ← Submodule.Quotient.mk_sub]
    rfl

theorem finrank_fixW_le_radU_YS (hW : ∀ w ∈ fixW_YS S, ∀ w' ∈ fixW_YS S, polar S.q w w' = 0) :
    finrank (ZMod 2) (fixW_YS S) ≤ finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hU : ∀ w ∈ fixW_YS S, w ∈ commU_YS S := fun w hw => mem_commU_YS.mpr (hW w hw)
  let f : fixW_YS S →ₗ[ZMod 2] AS35YS.radU S.q (commU_YS S) :=
    { toFun := fun w => ⟨⟨w, hU w w.2⟩, AS35YS.mem_radU.mpr fun u hu => by
        rw [polar_comm]
        exact mem_commU_YS.mp hu _ w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x x' hxx => ?_
  exact Subtype.ext (congrArg (fun z : AS35YS.radU S.q (commU_YS S) => ((z : commU_YS S) : S.Qt))
    hxx)

theorem act0_inj_pbar_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {x x' : S.O}
    (hx : x ∈ S.PbarAsc g) (hx' : x' ∈ S.PbarAsc g) (hxM : x ∈ S.Mbar) (hx'M : x' ∈ S.Mbar)
    (e : act0_YS hst ⟨x, hxM⟩ = act0_YS hst ⟨x', hx'M⟩) : x = x' := by
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hmem : x * x'⁻¹ ∈ S.PbarAsc g := mul_mem hx (inv_mem hx')
  have h1 : act0_YS hst ⟨x * x'⁻¹, hPM hmem⟩ = 1 := by
    have e2 : (⟨x * x'⁻¹, hPM hmem⟩ : S.Mbar) = ⟨x, hxM⟩ * (⟨x', hx'M⟩ : S.Mbar)⁻¹ := rfl
    rw [e2, map_mul, map_inv, e, mul_inv_cancel]
  exact mul_inv_eq_one.mp (act0_eq_one_of_pbar_YS hS hst h ht htM hmem _ h1)

theorem card_map_act0_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {A : Subgroup S.O}
    (hA : A ≤ S.PbarAsc g) :
    Nat.card ((A.subgroupOf S.Mbar).map (act0_YS hst)) = Nat.card A := by
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hinj : Function.Injective ((act0_YS hst).comp (A.subgroupOf S.Mbar).subtype) := by
    intro x x' e
    exact Subtype.ext (Subtype.ext (act0_inj_pbar_YS hS hst h ht htM
      (hA (mem_subgroupOf.mp x.2)) (hA (mem_subgroupOf.mp x'.2)) _ _ e))
  have e1 : (A.subgroupOf S.Mbar).map (act0_YS hst) =
      ((act0_YS hst).comp (A.subgroupOf S.Mbar).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (subgroupOfEquivOfLe (hA.trans hPM)).toEquiv

theorem pbar0_inU_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h : RadSing_YS S) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∀ p ∈ ((S.PbarAsc g).subgroupOf S.Mbar).map (act0_YS hst),
      (∀ v, q0_YS h (p v) = q0_YS h v) ∧
      (∀ v ∈ commSpace (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL ⟨_, ht, htM, rfl⟩⟩),
        p v = v) ∧
      ∀ v ∈ fixSpace (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL ⟨_, ht, htM, rfl⟩⟩),
        p v - v ∈
          commSpace (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL ⟨_, ht, htM, rfl⟩⟩) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxP := mem_subgroupOf.mp hx
  exact ⟨q0_act0_YS h hst x, fun v hv => act0_pbar_fix_YS hS hst ht htM hxP x.2 hv,
    fun v hv => act0_pbar_sub_YS hS hst hnd h ht htM hxP x.2 hv⟩

theorem normal_map_act0_of_YS (hst : S.Asc512Standing) {τ : S.O} {Y : Subgroup S.O}
    (hYnorm : ∀ c ∈ S.Mbar, c * τ = τ * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    {l : S.O} (hl : l ∈ S.LbarAsc) (hlt : l * τ = τ * l) {x : V0_YS S ≃ₗ[ZMod 2] V0_YS S}
    (hx : x ∈ (Y.subgroupOf S.Mbar).map (act0_YS hst)) :
    act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ * x * (act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩)⁻¹ ∈
      (Y.subgroupOf S.Mbar).map (act0_YS hst) := by
  obtain ⟨x₀, hx₀, hxe⟩ := hx
  have hmem := hYnorm l (LbarAsc_le_Mbar_YL hl) hlt _ (mem_subgroupOf.mp hx₀)
  refine ⟨⟨l, LbarAsc_le_Mbar_YL hl⟩ * x₀ * (⟨l, LbarAsc_le_Mbar_YL hl⟩ : S.Mbar)⁻¹,
    mem_subgroupOf.mpr hmem, ?_⟩
  rw [← act0_YS_conj, hxe]

theorem normal_map_act0_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) = 2 * Nat.card S.LbarAsc)
    [Nontrivial (V0_YS S)] {τ : S.O} (hτL : τ ∈ S.LbarAsc) {Y : Subgroup S.O}
    (hYnorm : ∀ c ∈ S.Mbar, c * τ = τ * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (g₀ : V0_YS S ≃ₗ[ZMod 2] V0_YS S) (hg₀ : ∀ v, q0_YS h (g₀ v) = q0_YS h v)
    (hev : Even (finrank (ZMod 2) (commSpace g₀)))
    (hcomm : g₀ * act0_YS hst ⟨τ, LbarAsc_le_Mbar_YL hτL⟩ =
      act0_YS hst ⟨τ, LbarAsc_le_Mbar_YL hτL⟩ * g₀) :
    ∀ x ∈ (Y.subgroupOf S.Mbar).map (act0_YS hst), g₀ * x * g₀⁻¹ ∈
      (Y.subgroupOf S.Mbar).map (act0_YS hst) := by
  obtain ⟨l, hl, hlg⟩ := exists_lbar_of_even_YS hS hst h hcard hg₀ hev
  have e1 : actL_YS hst ⟨l, hl⟩ * actL_YS hst ⟨τ, hτL⟩ =
      actL_YS hst ⟨τ, hτL⟩ * actL_YS hst ⟨l, hl⟩ := by
    rw [actL_YS_apply, actL_YS_apply, hlg]
    exact hcomm
  have e2 : actL_YS hst (⟨l, hl⟩ * ⟨τ, hτL⟩) = actL_YS hst (⟨τ, hτL⟩ * ⟨l, hl⟩) :=
    ((actL_YS hst).map_mul _ _).trans (e1.trans ((actL_YS hst).map_mul _ _).symm)
  have hlt : l * τ = τ * l := congrArg Subtype.val (actL_YS_injective hst e2)
  intro x hx
  have key := normal_map_act0_of_YS hst hYnorm hl hlt hx
  rwa [hlg] at key

theorem exists_ne_one_ne_YS {H : Type*} [Group H] [Finite H] {Z : Subgroup H} (τ : H)
    (hZ : 3 ≤ Nat.card Z) : ∃ y ∈ Z, y ≠ 1 ∧ y ≠ τ := by
  by_contra hcon
  push Not at hcon
  have hsub : (Z : Set H) ⊆ {1, τ} := by
    intro x hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hcon x hx h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, τ} : Set H).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : H) {τ}
    rwa [Set.ncard_singleton] at this
  rw [← Nat.card_coe_set_eq] at h1
  change Nat.card Z ≤ _ at h1
  omega

theorem omega_bounds_W_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (h : RadSing_YS S)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) = 2 * Nat.card S.LbarAsc)
    [Nontrivial (V0_YS S)] (hW0 : fixW_YS S ≠ ⊥) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) :
    2 * S.width - 3 ≤ 2 * finrank (ZMod 2) (V0_YS S) - 7 ∧
      (8 ≤ finrank (ZMod 2) (V0_YS S) →
        2 * finrank (ZMod 2) (V0_YS S) - 8 ≤ 1 + finrank (ZMod 2) (fixW_YS S)) ∧
      (finrank (ZMod 2) (V0_YS S) = 6 → 4 ≤ finrank (ZMod 2) (fixW_YS S) ∨
        (2 ≤ finrank (ZMod 2) (fixW_YS S) ∧
          ∀ w ∈ fixW_YS S, ∀ w' ∈ fixW_YS S, polar S.q w w' = 0)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (V0_YS S) := Module.finite_of_finite (ZMod 2)
  have : Finite (V0_YS S ≃ₗ[ZMod 2] V0_YS S) := finite_linearEquiv_YR
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have htL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure htD
  have hPcard := (S14.asc512PbarStmt G S hS g ht htM).2.2.1
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hWfix : fixW_YS S ≤ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    fun w hw => mem_fixSpace.mpr (hw _ htL)
  obtain ⟨Y, hYP, htY, hYcard, hYnorm, hYab⟩ := exists_pbar_iso_YS hS ht htM (fixW_YS S)
    (fun m hm w hw => fixW_YS_invariant hst hm hw) hWfix (fixW_inf_commSpace_YS hS hst hnd htD)
  have hW1 : 1 ≤ finrank (ZMod 2) (fixW_YS S) :=
    Nat.pos_of_ne_zero fun h0 => hW0 (Submodule.finrank_eq_zero.mp h0)
  have hWc : Nat.card (fixW_YS S) = 2 ^ finrank (ZMod 2) (fixW_YS S) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hZcard : Nat.card ((Y.subgroupOf S.Mbar).map (act0_YS hst)) =
      2 * 2 ^ finrank (ZMod 2) (fixW_YS S) := by
    rw [card_map_act0_YS hS hst h ht htM hYP, hYcard, hWc]
  have hP₀card : Nat.card (((S.PbarAsc g).subgroupOf S.Mbar).map (act0_YS hst)) =
      2 ^ (2 * S.width - 3) := by
    rw [card_map_act0_YS hS hst h ht htM le_rfl, hPcard]
  have h3 : 3 ≤ Nat.card ((Y.subgroupOf S.Mbar).map (act0_YS hst)) := by
    rw [hZcard]
    have : 2 ≤ 2 ^ finrank (ZMod 2) (fixW_YS S) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW1)
    omega
  obtain ⟨y, hyZ, hy1, hyτ⟩ := exists_ne_one_ne_YS
    (act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL htD⟩) h3
  have hZP : (Y.subgroupOf S.Mbar).map (act0_YS hst) ≤
      ((S.PbarAsc g).subgroupOf S.Mbar).map (act0_YS hst) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr (hYP (mem_subgroupOf.mp hx)), rfl⟩
  have hτZ : act0_YS hst ⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL htD⟩ ∈
      (Y.subgroupOf S.Mbar).map (act0_YS hst) :=
    ⟨⟨_, DbarAsc_subset_Mbar_YL htD⟩, mem_subgroupOf.mpr htY, rfl⟩
  obtain ⟨hb1, hb2, hb3⟩ := omega_bound_YS (q0_YS_nondegenerate h)
    (isTypeA_act0_YS hS hst h htD) (pbar0_inU_YS hS hst hnd h ht htM) hZP hτZ hyZ hy1 hyτ
    (fun g₀ hg₀ hev hc => normal_map_act0_YS hS hst h hcard htL hYnorm g₀ hg₀ hev hc)
  rw [hP₀card] at hb1
  refine ⟨(Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hb1, fun h8 => ?_, fun h6 => ?_⟩
  · have hb := hb2 h8
    rw [hZcard, ← pow_succ'] at hb
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hb
    omega
  · rcases hb3 h6 with h32 | ⟨h8', hab⟩
    · left
      rw [hZcard] at h32
      by_contra hlt
      push Not at hlt
      have : 2 * 2 ^ finrank (ZMod 2) (fixW_YS S) ≤ 2 * 2 ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    · right
      rw [hZcard] at h8'
      refine ⟨?_, hYab fun y hy y' hy' => ?_⟩
      · by_contra hlt
        push Not at hlt
        have : 2 * 2 ^ finrank (ZMod 2) (fixW_YS S) ≤ 2 * 2 ^ 1 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        omega
      · have e := hab _ ⟨⟨y, hPM (hYP hy)⟩, mem_subgroupOf.mpr hy, rfl⟩ _
          ⟨⟨y', hPM (hYP hy')⟩, mem_subgroupOf.mpr hy', rfl⟩
        have hm1 : y * y' ∈ S.PbarAsc g := mul_mem (hYP hy) (hYP hy')
        have hm2 : y' * y ∈ S.PbarAsc g := mul_mem (hYP hy') (hYP hy)
        refine act0_inj_pbar_YS hS hst h ht htM hm1 hm2 (hPM hm1) (hPM hm2) ?_
        have e1 : (⟨y * y', hPM hm1⟩ : S.Mbar) = ⟨y, hPM (hYP hy)⟩ * ⟨y', hPM (hYP hy')⟩ := rfl
        have e2 : (⟨y' * y, hPM hm2⟩ : S.Mbar) = ⟨y', hPM (hYP hy')⟩ * ⟨y, hPM (hYP hy)⟩ := rfl
        rw [e1, e2, map_mul, map_mul]
        exact e

theorem fixW_eq_bot_of_omega_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (h : RadSing_YS S)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) = 2 * Nat.card S.LbarAsc)
    (hN : finrank (ZMod 2) (V0_YS S) = 6 ∨ 8 ≤ finrank (ZMod 2) (V0_YS S)) :
    fixW_YS S = ⊥ := by
  have : Nontrivial (V0_YS S) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  by_contra hW0
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨hb1, hb2, hb3⟩ := omega_bounds_W_YS hS hst hnd h hcard hW0 ht htM
  obtain ⟨hsum, hRW⟩ := finrank_V0_add_YS (S := S)
  have hn3 := hS.three_le_width
  have hW1 : 1 ≤ finrank (ZMod 2) (fixW_YS S) :=
    Nat.pos_of_ne_zero fun h0 => hW0 (Submodule.finrank_eq_zero.mp h0)
  rcases hN with h6 | h8
  · rcases hb3 h6 with h4 | ⟨h2, hiso⟩
    · omega
    · have hR := finrank_fixW_le_radU_YS hiso
      omega
  · have := hb2 h8
    omega

end Setting

end CFSG.LargeExtraspecial
