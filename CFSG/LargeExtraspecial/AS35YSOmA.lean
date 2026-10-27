module

public import CFSG.LargeExtraspecial.AS35YSIrr
public import CFSG.LargeExtraspecial.AS35YRPOm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions AS35YR

namespace AS35YS

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem card_O_eq_two_mul_of_omega (hq : q.polarBilin.Nondegenerate) {X : Type} [Group X]
    {m : ℕ} (hL : LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1)
    (hdim : finrank (ZMod 2) V = 2 * m)
    (hdvd : Nat.card X ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup q)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) = 2 * Nat.card X := by
  obtain ⟨hn4, ε, hε, hLz⟩ : 4 ≤ m ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (Nat.card X : ℤ) =
        2 ^ (m * (m - 1)) * (2 ^ m - ε) * ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    rcases hL with hL | hL
    · obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      have := Fintype.ofFinite K
      have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
      have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K) hn4
      rw [hK, pow_one] at hz
      refine ⟨hn4, 1, Or.inl rfl, ?_⟩
      rw [Nat.card_congr e.toEquiv]
      exact_mod_cast hz
    · obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      have := Fintype.ofFinite K
      have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
      have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K)
        hn4 hirr
      rw [hK, pow_one] at hz
      refine ⟨hn4, -1, Or.inr rfl, ?_⟩
      rw [Nat.card_congr e.toEquiv, sub_neg_eq_add]
      exact_mod_cast hz
  have hdim' : finrank (ZMod 2) V = 2 * ((m - 1) + 1) := by
    rw [hdim, Nat.sub_add_cancel (by omega)]
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  obtain ⟨ε', hε', hO⟩ : ∃ ε' : ℤ, (ε' = 1 ∨ ε' = -1) ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) : ℤ) =
        2 * 2 ^ ((m - 1) * ((m - 1) + 1)) * (2 ^ ((m - 1) + 1) - ε') *
          ∏ i ∈ Finset.Icc 1 (m - 1), (((2 : ℤ) ^ 2) ^ i - 1) := by
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType q
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hq hdim'
        (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [h2] at h
      exact ⟨1, Or.inl rfl, h⟩
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hq hdim'
        (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [h2] at h
      exact ⟨-1, Or.inr rfl, h⟩
  have e1 : (m - 1) * ((m - 1) + 1) = m * (m - 1) := by
    rw [Nat.sub_add_cancel (by omega), mul_comm]
  have e2 : (m - 1) + 1 = m := Nat.sub_add_cancel (by omega)
  have e3 : ∏ i ∈ Finset.Icc 1 (m - 1), (((2 : ℤ) ^ 2) ^ i - 1) =
      ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
  rw [e1, e2, e3] at hO
  have hdvd' : (Nat.card X : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have hi1 := (Finset.mem_Icc.mp hi).1
    have : (2 : ℤ) ^ 2 ≤ 2 ^ (2 * i) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hN : (8 : ℤ) ≤ 2 ^ m := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
  have key := eq_two_mul_of_dvd_YR (pow_pos (by norm_num : (0 : ℤ) < 2) _) hP hN hε hε' hLz hO
    hdvd'
  exact_mod_cast key

theorem card_O_eq_two_mul_of_psl4 (hq : q.polarBilin.Nondegenerate) {X : Type} [Group X]
    (hL : LieModel X .PSL 4 2 1) (hdim : finrank (ZMod 2) V = 6)
    (hdvd : Nat.card X ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup q)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) = 2 * Nat.card X := by
  have hX : Nat.card X = 20160 := by
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL)).1 rfl
    rw [h1]
    decide
  rw [hX] at hdvd ⊢
  have hdim' : finrank (ZMod 2) V = 2 * (2 + 1) := by rw [hdim]
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType q
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hq hdim'
      (ε := 1) (Or.inl ⟨rfl, hp⟩)
    rw [h2] at h
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) = N at h hdvd ⊢
    norm_num [Finset.prod_Icc_succ_top] at h
    omega
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hq hdim'
      (ε := -1) (Or.inr ⟨rfl, hp⟩)
    rw [h2] at h
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) = N at h hdvd ⊢
    norm_num [Finset.prod_Icc_succ_top] at h
    omega

theorem mem_of_card_O_eq (hq : q.polarBilin.Nondegenerate) [Nontrivial V]
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hHΩ : H ≤ omegaGroup q hq)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) = 2 * Nat.card H)
    {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v, q (g v) = q v) (hev : Even (finrank (ZMod 2) (commSpace g))) :
    g ∈ H := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_YR
  set O := TauCeti.QuadraticMap.orthogonalGroup q with hO
  have hΩO : omegaGroup q hq ≤ O := omegaGroup_le q hq
  have hidx : ((omegaGroup q hq).subgroupOf O).index = 2 := relIndex_omegaGroup q hq
  have hcΩ : Nat.card ((omegaGroup q hq).subgroupOf O) * 2 = Nat.card O := by
    have := Subgroup.card_mul_index ((omegaGroup q hq).subgroupOf O)
    rwa [hidx] at this
  have hcΩ' : Nat.card ((omegaGroup q hq).subgroupOf O) = Nat.card (omegaGroup q hq) :=
    Nat.card_congr (subgroupOfEquivOfLe hΩO).toEquiv
  have heq : H = omegaGroup q hq := by
    refine Subgroup.eq_of_le_of_card_ge hHΩ ?_
    omega
  rw [heq]
  exact mem_omegaGroup.mpr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg, hev⟩

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YS

theorem act0_mem_omega_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S)
    {l : S.O} (hl : l ∈ S.LbarAsc) :
    act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ ∈ omegaGroup (q0_YS h) (q0_YS_nondegenerate h) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  induction hl using Subgroup.closure_induction with
  | mem d hd =>
    have hA := isTypeA_act0_YS hS hst h hd
    exact mem_omegaGroup.mpr ⟨act0_YS_mem_O h hst _, by rw [hA.2.2.2.1]; exact even_two⟩
  | one =>
    have e : (⟨1, LbarAsc_le_Mbar_YL (one_mem _)⟩ : S.Mbar) = 1 := rfl
    rw [e, map_one]
    exact one_mem _
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, LbarAsc_le_Mbar_YL (mul_mem ha hb)⟩ : S.Mbar) =
        ⟨a, LbarAsc_le_Mbar_YL ha⟩ * ⟨b, LbarAsc_le_Mbar_YL hb⟩ := rfl
    rw [e, map_mul]
    exact mul_mem iha ihb
  | inv a ha iha =>
    have e : (⟨a⁻¹, LbarAsc_le_Mbar_YL (inv_mem ha)⟩ : S.Mbar) =
        (⟨a, LbarAsc_le_Mbar_YL ha⟩ : S.Mbar)⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem iha

theorem exists_lbar_of_even_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) = 2 * Nat.card S.LbarAsc)
    [Nontrivial (V0_YS S)] {g : V0_YS S ≃ₗ[ZMod 2] V0_YS S} (hg : ∀ v, q0_YS h (g v) = q0_YS h v)
    (hev : Even (finrank (ZMod 2) (commSpace g))) :
    ∃ (l : S.O) (hl : l ∈ S.LbarAsc), act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ = g := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hle : (actL_YS hst).range ≤ omegaGroup (q0_YS h) (q0_YS_nondegenerate h) := by
    rintro _ ⟨l, rfl⟩
    rw [actL_YS_apply]
    exact act0_mem_omega_YS hS hst h l.2
  have hrc : Nat.card (actL_YS hst).range = Nat.card S.LbarAsc :=
    Nat.card_congr (MonoidHom.ofInjective (actL_YS_injective hst)).toEquiv.symm
  obtain ⟨l, hl⟩ := mem_of_card_O_eq (q0_YS_nondegenerate h) hle (by rw [hrc]; exact hcard) hg hev
  exact ⟨l, l.2, by rw [← hl, actL_YS_apply]⟩

theorem exists_sub_eq_of_mem_commSpace_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (h : RadSing_YS S) {d : S.O} (hd : d ∈ S.DbarAsc) {y : S.Qt}
    (hy : y ∈ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ u ∈ commU_YS S, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u = y := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set C := commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) with hC
  set N : Submodule (ZMod 2) S.Qt := (commU_YS S).map ((d : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hN
  have hNC : N ≤ C := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  have hA := isTypeA_act0_YS hS hst h hd
  have hAd := isTypeA_of_mem_DbarAsc_YL hS hd
  have hle : commSpace (act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩) ≤
      (N.comap (commU_YS S).subtype).map (AS35YS.radU S.q (commU_YS S)).mkQ := by
    intro z hz
    obtain ⟨u, rfl⟩ := mem_commSpace_act0_YS hst _ hz
    exact ⟨⟨_, (commU_YS S).sub_mem (commU_YS_invariant hst (DbarAsc_subset_Mbar_YL hd) u.2)
      u.2⟩, ⟨u, u.2, rfl⟩, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank (ZMod 2) ((N.comap (commU_YS S).subtype).map
      (AS35YS.radU S.q (commU_YS S)).mkQ) ≤ finrank (ZMod 2) (N.comap (commU_YS S).subtype) :=
    Submodule.finrank_map_le _ _
  have h3 : finrank (ZMod 2) (N.comap (commU_YS S).subtype) ≤ finrank (ZMod 2) N := by
    let f : N.comap (commU_YS S).subtype →ₗ[ZMod 2] N :=
      { toFun := fun x => ⟨((x : commU_YS S) : S.Qt), x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x x' hxx => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : S.Qt)) hxx))
  have h4 : finrank (ZMod 2) N = finrank (ZMod 2) C := by
    have h5 := Submodule.finrank_mono hNC
    rw [hA.2.2.2.1] at h1
    have h6 : 2 ≤ finrank (ZMod 2) N := (h1.trans h2).trans h3
    rw [hC, hAd.2.2.2.1] at h5 ⊢
    omega
  have hNe : N = C := Submodule.eq_of_le_of_finrank_eq hNC h4
  rw [← hNe] at hy
  obtain ⟨u, hu, rfl⟩ := hy
  exact ⟨u, hu, rfl⟩

theorem act0_eq_one_of_pbar_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S)
    {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {x : S.O}
    (hx : x ∈ S.PbarAsc g) (hxM : x ∈ S.Mbar) (h1 : act0_YS hst ⟨x, hxM⟩ = 1) : x = 1 := by
  obtain ⟨htP, hext, -, hcent, -, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  set P' := (S.PbarAsc g).subgroupOf S.Mbar with hP'
  set f : P' →* (V0_YS S ≃ₗ[ZMod 2] V0_YS S) := (act0_YS hst).comp P'.subtype with hf
  have hP2 : IsPGroup 2 P' := by
    have h0 := hext.1
    exact IsPGroup.of_equiv h0 (subgroupOfEquivOfLe hPM).symm
  have : Finite P' := Subtype.finite
  have : Group.IsNilpotent P' := hP2.isNilpotent
  have hker : f.ker = ⊥ := by
    by_contra hne
    have hnb := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ f.ker ⊓ center P', y ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hnb ((Subgroup.eq_bot_iff_forall _).mpr hc)
    obtain ⟨hyk, hyc⟩ := mem_inf.mp hy
    have hyP : ((y : S.Mbar) : S.O) ∈ S.PbarAsc g := mem_subgroupOf.mp y.2
    have hyc' : ∀ z ∈ S.PbarAsc g, ((y : S.Mbar) : S.O) * z = z * ((y : S.Mbar) : S.O) := by
      intro z hz
      have := mem_center_iff.mp hyc ⟨⟨z, hPM hz⟩, mem_subgroupOf.mpr hz⟩
      exact (congrArg (fun w : P' => ((w : S.Mbar) : S.O)) this).symm
    rcases hcent _ hyP hyc' with h0 | h0
    · exact hy1 (Subtype.ext (Subtype.ext h0))
    · have hA := isTypeA_act0_YS hS hst h htD
      apply hA.2.1
      have e : (⟨S.ρ ⟨_, htM⟩, DbarAsc_subset_Mbar_YL htD⟩ : S.Mbar) = (y : S.Mbar) :=
        Subtype.ext h0.symm
      rw [e]
      exact hyk
  have hxP : (⟨⟨x, hxM⟩, mem_subgroupOf.mpr hx⟩ : P') ∈ f.ker := h1
  rw [hker, mem_bot] at hxP
  exact congrArg (fun z : P' => ((z : S.Mbar) : S.O)) hxP

end Setting

end CFSG.LargeExtraspecial
