module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreSupport
public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplit
public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups

public section

namespace CFSG.Semidihedral.Principal.FieldFactorOneFixedCore

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem field_factor_one_torus_local_data (G : Type) [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (hSC : (S : Subgroup G) ≤ C t) (s : G) (hsS : s ∈ (S : Subgroup G)) (hs : orderOf s = 2)
    (hst : s ≠ t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap
          (nu t)).map (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    let L := CFSG.generalizedFitting (Gamma t)
    let T₀ := L.comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let V : Subgroup G := Subgroup.closure {t, s}
    let A₀ : Subgroup G := (N t).map (C t).subtype ⊓ Subgroup.centralizer {s}
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    let K : Subgroup G := M ⊓ C t
    let qe : ℕ := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    ∃ W : Subgroup G,
      (∀ x : G, x ∈ W ↔ x ∈ J.map (C t).subtype ∧ x * s = s * x ∧ Odd (orderOf x)) ∧
      IsCyclic W ∧ Nat.card W = qe / 2 ∧
      (∃ e : (V × A₀ × W) ≃* D, ∀ x : V × A₀ × W, (e x : G) = x.1 * x.2.1 * x.2.2) ∧
      (A₀.subgroupOf K).Normal ∧ ⁅(S : Subgroup G), A₀⁆ = ⊥ ∧
      ∃ d ∈ K, d ∉ D ∧ orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s ∧
        (∀ a ∈ A₀, d * a = a * d) ∧ (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
        ∀ x ∈ D, d * x * d⁻¹ * x ∈ V ⊔ A₀ := by
  intro L T₀ Y H₀ J V A₀ D M K qe
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsC : s ∈ C t := hSC hsS
  set sC : C t := ⟨s, hsC⟩ with hsCdef
  have hsC2 : orderOf sC = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hts : t ≠ s := fun h => hst h.symm
  have htc : ∀ y : C t, tInC t * y = y * tInC t := fun y =>
    (Subgroup.mem_center_iff.mp (tInC_central t) y).symm
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have htsc : t * s = s * t := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hVK : IsKleinFour V :=
    StationaryOddLocalization.actual_involution_pair_isKleinFour t s ht hs hsC hts
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hVmem : ∀ v ∈ V, v = 1 ∨ v = t ∨ v = s ∨ v = t * s :=
    fun v hv => mem_closure_pair_cases htsc ht2 hs2 hv
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ht2
    · exact hs2
    · rw [show t * s * (t * s) = (t * t) * (s * s) by rw [mul_assoc, ← mul_assoc s, ← htsc]; group,
        ht2, hs2, one_mul]
  have hDmem : ∀ x : G, x ∈ D ↔ x * t = t * x ∧ x * s = s * x := fun x =>
    mem_centralizer_closure_pair_iff
  have hDC : D ≤ C t := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((hDmem x).mp hx).1
  have hVD : V ≤ D := by
    intro v hv
    rw [hDmem]
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · simp
    · exact ⟨rfl, htsc⟩
    · exact ⟨htsc.symm, rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [mul_assoc, ← htsc]
      · rw [mul_assoc, hs2, mul_one, ← mul_assoc, ← htsc, mul_assoc, hs2, mul_one]
  obtain ⟨-, -, -, hCJcyc, -, Wc, hWcmem, hWccyc, hWccard, -, -, -, hWcN, -, hRY, hWA, hcommWA,
      d, hdJ, hd4, hd2, hds, hdinv⟩ :=
    CentralKernelTorusSplit.actual_central_odd_kernel_is_inverted_and_fixed_layer_torus_splits
      n hn S fS hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel sC hsC2 hsCt hcov
  obtain ⟨-, hJnormal, htJ, -, hJN, hYJN, -, -, -, -, -, -, -, -, -, -⟩ :=
    (Local.all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift n hn S fS
      hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1 hcov
  replace hJnormal : J.Normal := hJnormal
  replace htJ : tInC t ∈ J := htJ
  replace hJN : ⁅J, N t⁆ = ⊥ := hJN
  replace hYJN : Y = J ⊔ N t := hYJN
  have hJcomm : ∀ x ∈ J, ∀ y ∈ N t, x * y = y * x := by
    intro x hx y hy
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN hx
    exact (Subgroup.mem_centralizer_iff.mp h y hy).symm
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  obtain ⟨-, F, hF, hFfin, Aut, a, -, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG
      t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, -, hCD, -, -, -, -⟩ := hall sC hsC2 hsCt
  obtain ⟨eDV, heDV⟩ := hCD.lifted.direct_equiv
  have hRodd := hCD.lifted.odd_core_odd
  have hfour : (KleinFourOddKernel.fourSubgroup (tInC t) sC).map (C t).subtype = V :=
    StationaryOddLocalization.original_centralizer_four_subgroup_image t s hsC
  have hNamem : ∀ x : G, x ∈ (N t).map (C t).subtype ↔ ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ N t := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxN⟩
      exact ⟨⟨x, hx⟩, hxN, rfl⟩
  have hA₀mem : ∀ x : G, x ∈ A₀ ↔
      ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ N t ⊓ Subgroup.centralizer ({sC} : Set (C t)) := by
    intro x
    change x ∈ (N t).map (C t).subtype ⊓ Subgroup.centralizer {s} ↔ _
    constructor
    · rintro ⟨hxN, hxs⟩
      obtain ⟨hx, hxN⟩ := (hNamem x).mp hxN
      exact ⟨hx, hxN, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxs))⟩
    · rintro ⟨hx, hxN, hxs⟩
      exact ⟨(hNamem x).mpr ⟨hx, hxN⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hxs))⟩
  set W : Subgroup G := Wc.map (C t).subtype with hWdef
  have hWmem' : ∀ x : G, x ∈ W ↔ ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ Wc := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨x, hx⟩, hxW, rfl⟩
  have hWmem : ∀ x : G, x ∈ W ↔ x ∈ J.map (C t).subtype ∧ x * s = s * x ∧ Odd (orderOf x) := by
    intro x
    rw [hWmem']
    constructor
    · rintro ⟨hx, hxW⟩
      obtain ⟨⟨hxJ, hxs⟩, hodd⟩ := (hWcmem _).mp hxW
      refine ⟨⟨⟨x, hx⟩, hxJ, rfl⟩, congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hxs), ?_⟩
      rwa [Subgroup.orderOf_mk] at hodd
    · rintro ⟨⟨y, hyJ, rfl⟩, hys, hodd⟩
      refine ⟨y.2, ?_⟩
      change y ∈ Wc
      refine (hWcmem _).mpr ⟨⟨hyJ, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext hys)⟩, ?_⟩
      rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hodd
  have hWcyc : IsCyclic W := by
    have e := Wc.equivMapOfInjective (C t).subtype (C t).subtype_injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hWcard : Nat.card W = qe / 2 := by
    rw [hWdef, Subgroup.card_map_of_injective (C t).subtype_injective]
    exact hWccard
  have hNaodd : ∀ x ∈ (N t).map (C t).subtype, Odd (orderOf x) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    have h := Subgroup.orderOf_dvd_natCard (N t) hy
    exact hNodd.of_dvd_nat h
  have hA₀odd : ∀ x ∈ A₀, Odd (orderOf x) := fun x hx => hNaodd x hx.1
  have hWodd : ∀ x ∈ W, Odd (orderOf x) := fun x hx => ((hWmem x).mp hx).2.2
  have hA₀D : A₀ ≤ D := by
    intro x hx
    rw [hDmem]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mp hx.2⟩
    obtain ⟨hxC, -⟩ := (hNamem x).mp hx.1
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hWD : W ≤ D := by
    intro x hx
    rw [hDmem]
    obtain ⟨⟨y, -, rfl⟩, hys, -⟩ := (hWmem x).mp hx
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mp y.2, hys⟩
  have hVcommD : ∀ v ∈ V, ∀ x ∈ D, v * x = x * v := by
    intro v hv x hx
    exact (Subgroup.mem_centralizer_iff.mp hx v hv)
  have hA₀W : ∀ x ∈ A₀, ∀ w ∈ W, x * w = w * x := by
    intro x hx w hw
    obtain ⟨hxC, hxA⟩ := (hA₀mem x).mp hx
    obtain ⟨hwC, hwW⟩ := (hWmem' w).mp hw
    have h := (hcommWA _ hwW _ hxA).eq
    exact (congrArg Subtype.val h).symm
  have hWA₀ : ∀ x ∈ W, x ∈ A₀ → x = 1 := by
    intro x hxW hxA
    obtain ⟨hxC, hxW'⟩ := (hWmem' x).mp hxW
    obtain ⟨hxC', hxA'⟩ := (hA₀mem x).mp hxA
    have h : (⟨x, hxC⟩ : C t) ∈ Wc ⊓ (N t ⊓ Subgroup.centralizer ({sC} : Set (C t))) :=
      ⟨hxW', hxA'⟩
    rw [hWA, Subgroup.mem_bot] at h
    exact congrArg Subtype.val h
  have hinj : ∀ v ∈ V, ∀ x ∈ A₀, ∀ w ∈ W, v * x * w = 1 → v = 1 ∧ x = 1 ∧ w = 1 := by
    intro v hv x hx w hw h
    have hxw : x * w = v⁻¹ := by
      rw [mul_assoc] at h
      exact eq_inv_of_mul_eq_one_right h
    have hvsq : v⁻¹ * v⁻¹ = 1 := by rw [← mul_inv_rev, hVsq v hv, inv_one]
    have hsq : x ^ 2 * w ^ 2 = 1 := by
      have hc := hA₀W x hx w hw
      calc x ^ 2 * w ^ 2 = x * (x * w) * w := by rw [pow_two, pow_two]; group
        _ = x * (w * x) * w := by rw [hc]
        _ = (x * w) * (x * w) := by group
        _ = 1 := by rw [hxw, hvsq]
    have hx2 : x ^ 2 = 1 := by
      have hxW : x ^ 2 ∈ W := by
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact W.inv_mem (W.pow_mem hw 2)
      exact hWA₀ _ hxW (A₀.pow_mem hx 2)
    have hx1 : x = 1 := eq_one_of_sq_eq_one_of_odd (hA₀odd x hx) hx2
    have hw2 : w ^ 2 = 1 := by rwa [hx2, one_mul] at hsq
    have hw1 : w = 1 := eq_one_of_sq_eq_one_of_odd (hWodd w hw) hw2
    refine ⟨?_, hx1, hw1⟩
    rw [hx1, hw1, mul_one, mul_one] at h
    exact h
  have hsurj : ∀ x ∈ D, ∃ v ∈ V, ∃ y ∈ A₀, ∃ w ∈ W, x = v * y * w := by
    intro x hx
    have hxC : x ∈ C t := hDC hx
    have hxs : (⟨x, hxC⟩ : C t) ∈ KleinFourOddKernel.centralizer sC := by
      change (⟨x, hxC⟩ : C t) ∈ Subgroup.centralizer {sC}
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact Subtype.ext ((hDmem x).mp hx).2
    obtain ⟨⟨v, r⟩, hvr⟩ := eDV.surjective ⟨⟨x, hxC⟩, hxs⟩
    have hx' := heDV v r
    rw [hvr] at hx'
    have hvV : ((v : C t) : G) ∈ V := by
      rw [← hfour]
      exact Subgroup.mem_map_of_mem _ v.2
    have hrR : ((r : KleinFourOddKernel.centralizer sC) : C t) ∈
        (CFSG.pPrimeCore 2 (Subgroup.centralizer ({sC} : Set (C t)))).map
          (Subgroup.centralizer ({sC} : Set (C t))).subtype := by
      refine ⟨(r : KleinFourOddKernel.centralizer sC), ?_, rfl⟩
      have h := r.2
      change (r : KleinFourOddKernel.centralizer sC) ∈
        CFSG.piCore KleinFourOddKernel.oddPrimes (KleinFourOddKernel.centralizer sC) at h
      rwa [KleinFourOddKernel.piCore_odd_eq_pPrimeCore] at h
    have hrodd : Odd (orderOf ((r : KleinFourOddKernel.centralizer sC) : C t)) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hRodd.of_dvd_nat (orderOf_dvd_natCard r)
    have hrY : ((r : KleinFourOddKernel.centralizer sC) : C t) ∈ Y :=
      mem_of_index_two_of_odd_orderOf hY hrodd
    have hrWA : ((r : KleinFourOddKernel.centralizer sC) : C t) ∈
        Wc ⊔ (N t ⊓ Subgroup.centralizer ({sC} : Set (C t))) := by
      rw [← hRY]
      exact ⟨hrR, hrY⟩
    obtain ⟨w, hw, y, hy, hwy⟩ := exists_mul_of_mem_sup_of_commute
      (fun w hw y hy => (hcommWA w hw y hy).eq) hrWA
    refine ⟨(v : C t), hvV, (y : G), (hA₀mem _).mpr ⟨y.2, hy⟩, (w : G),
      (hWmem' _).mpr ⟨w.2, hw⟩, ?_⟩
    have hx'' : x = ((v : C t) : G) * (((w : C t) : G) * ((y : C t) : G)) := by
      have h := congrArg Subtype.val hx'
      rw [hwy] at h
      exact h
    rw [hx'', ← mul_assoc]
    have hc := (hcommWA w hw y hy).eq
    rw [mul_assoc, mul_assoc, show ((w : C t) : G) * ((y : C t) : G) =
      ((y : C t) : G) * ((w : C t) : G) from congrArg Subtype.val hc]
  have hDVAW : ∃ e : (V × A₀ × W) ≃* D, ∀ x : V × A₀ × W, (e x : G) = x.1 * x.2.1 * x.2.2 :=
    exists_mulEquiv_prod_three hVD hA₀D hWD (fun v hv x hx => hVcommD v hv x (hA₀D hx))
      (fun v hv w hw => hVcommD v hv w (hWD hw)) hA₀W hinj hsurj
  have hNanormal : ∀ g ∈ C t, ∀ x ∈ (N t).map (C t).subtype,
      g * x * g⁻¹ ∈ (N t).map (C t).subtype := by
    rintro g hg _ ⟨y, hy, rfl⟩
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (N t).Normal).conj_mem y hy ⟨g, hg⟩
  have hA₀K : (A₀.subgroupOf K).Normal := by
    constructor
    intro x hx k
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hkM : (k : G) ∈ M := k.2.1
    have hkC : (k : G) ∈ C t := k.2.2
    have hks : (k : G)⁻¹ * s * k ∈ V := by
      have h := (Subgroup.mem_normalizer_iff.mp (M.inv_mem hkM) s).mp hsV
      rwa [inv_inv] at h
    have hc := hVcommD _ hks _ (hA₀D hx)
    have hcs : ((k : G) * x * (k : G)⁻¹) * s = s * ((k : G) * x * (k : G)⁻¹) := by
      calc (k : G) * x * (k : G)⁻¹ * s = k * (x * ((k : G)⁻¹ * s * k)) * (k : G)⁻¹ := by
            group
        _ = k * (((k : G)⁻¹ * s * k) * x) * (k : G)⁻¹ := by rw [hc]
        _ = s * ((k : G) * x * (k : G)⁻¹) := by group
    exact Subgroup.mem_inf.mpr ⟨hNanormal _ hkC _ hx.1,
      Subgroup.mem_centralizer_singleton_iff.mpr hcs⟩
  have hsY : sC ∉ Y := by
    intro hsY
    have hsJ : sC ∈ J := by
      have h : sC ∈ J ⊔ N t := hYJN ▸ hsY
      exact EscapingLocalEigensubgroups.two_power_element_in_normal_factor J (N t) hNodd sC h 1
        (by rw [hsC2, pow_one])
    have hsCJ : sC ∈ J ⊓ Subgroup.centralizer ({sC} : Set (C t)) :=
      ⟨hsJ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have htCJ : tInC t ∈ J ⊓ Subgroup.centralizer ({sC} : Set (C t)) :=
      ⟨htJ, Subgroup.mem_centralizer_singleton_iff.mpr (htc sC)⟩
    have htC2 : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
    exact hsCt (eq_of_orderOf_eq_two_of_isCyclic hCJcyc hsCJ htCJ hsC2 htC2)
  have h2elt : ∀ g ∈ (S : Subgroup G), ∃ k : ℕ, orderOf g ∣ 2 ^ k := by
    intro g hg
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, hg⟩
    refine ⟨k, ?_⟩
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_of_pow_eq_one hk
  have hJA₀ : ∀ y : C t, y ∈ J → ∀ x ∈ A₀, (y : G) * x = x * y := by
    intro y hy x hx
    obtain ⟨hxC, hxA⟩ := (hA₀mem x).mp hx
    exact congrArg Subtype.val (hJcomm y hy _ hxA.1)
  have hS2J : ∀ g ∈ (S : Subgroup G), ∀ hgC : g ∈ C t, (⟨g, hgC⟩ : C t) ∈ Y →
      (⟨g, hgC⟩ : C t) ∈ J := by
    intro g hg hgC hgY
    obtain ⟨k, hk⟩ := h2elt g hg
    have h : (⟨g, hgC⟩ : C t) ∈ J ⊔ N t := hYJN ▸ hgY
    exact EscapingLocalEigensubgroups.two_power_element_in_normal_factor J (N t) hNodd _ h k
      (by rwa [Subgroup.orderOf_mk])
  have hSA₀ : ⁅(S : Subgroup G), A₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hgC : g ∈ C t := hSC hg
    by_cases hgY : (⟨g, hgC⟩ : C t) ∈ Y
    · exact (hJA₀ _ (hS2J g hg hgC hgY) x hx).symm
    · have hgsY : (⟨g, hgC⟩ : C t) * sC⁻¹ ∈ Y := mul_inv_mem_of_index_two hY hgY hsY
      have hgs : g * s⁻¹ ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem hg ((S : Subgroup G).inv_mem hsS)
      have hgsC : g * s⁻¹ ∈ C t := (C t).mul_mem hgC ((C t).inv_mem hsC)
      have hgsJ := hS2J (g * s⁻¹) hgs hgsC hgsY
      have h1 : g * s⁻¹ * x = x * (g * s⁻¹) := hJA₀ _ hgsJ x hx
      have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      calc x * g = x * (g * s⁻¹) * s := by group
        _ = g * s⁻¹ * x * s := by rw [← h1]
        _ = g * s⁻¹ * (x * s) := by group
        _ = g * s⁻¹ * (s * x) := by rw [hxs]
        _ = g * x := by group
  have hdC : (d : G) ∈ C t := d.2
  set dG : G := (d : G) with hdG
  have hdt : dG * t * dG⁻¹ = t := by
    have h' : t * dG = dG * t := congrArg Subtype.val (htc d)
    rw [← h', mul_inv_cancel_right]
  have hdsG : dG * s * dG⁻¹ = t * s := congrArg Subtype.val hds
  have hdM : dG ∈ M := mem_normalizer_closure_pair htsc ht2 hs2 hdt hdsG
  have hdK : dG ∈ K := ⟨hdM, hdC⟩
  have hdD : dG ∉ D := by
    intro h
    have h1 := ((hDmem dG).mp h).2
    have h2 : dG * s * dG⁻¹ = s := by rw [h1, mul_inv_cancel_right]
    rw [hdsG] at h2
    have ht1 : t = 1 := by
      calc t = t * s * s⁻¹ := by group
        _ = s * s⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel s
    rw [ht1, orderOf_one] at ht
    omega
  have hd4G : orderOf dG = 4 := by rw [hdG, Subgroup.orderOf_coe]; exact hd4
  have hd2G : dG ^ 2 = t := by
    have h := congrArg Subtype.val hd2
    rwa [SubgroupClass.coe_pow] at h
  have hdA : ∀ x ∈ A₀, dG * x = x * dG := hJA₀ d hdJ
  have hdW : ∀ w ∈ W, dG * w * dG⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨hwC, hwW⟩ := (hWmem' w).mp hw
    exact congrArg Subtype.val (hdinv _ hwW)
  have hdx : ∀ x ∈ D, dG * x * dG⁻¹ * x ∈ V ⊔ A₀ := by
    intro x hx
    obtain ⟨v, hv, a, ha, w, hw, rfl⟩ := hsurj x hx
    have hdv : dG * v * dG⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdM v).mp hv
    have hda : dG * a * dG⁻¹ = a := by rw [hdA a ha, mul_inv_cancel_right]
    have hdw : dG * w * dG⁻¹ = w⁻¹ := hdW w hw
    have h1 : w⁻¹ * v = v * w⁻¹ := (hVcommD v hv _ (D.inv_mem (hWD hw))).symm
    have h2 : a * v = v * a := (hVcommD v hv a (hA₀D ha)).symm
    have h3 : w⁻¹ * a = a * w⁻¹ := (hA₀W a ha _ (W.inv_mem hw)).symm
    have key : dG * (v * a * w) * dG⁻¹ * (v * a * w) = (dG * v * dG⁻¹) * v * (a * a) := by
      calc dG * (v * a * w) * dG⁻¹ * (v * a * w)
          = (dG * v * dG⁻¹) * (dG * a * dG⁻¹) * (dG * w * dG⁻¹) * (v * a * w) := by group
        _ = (dG * v * dG⁻¹) * a * (w⁻¹ * v) * a * w := by rw [hda, hdw]; group
        _ = (dG * v * dG⁻¹) * (a * v) * w⁻¹ * a * w := by rw [h1]; group
        _ = (dG * v * dG⁻¹) * v * a * (w⁻¹ * a) * w := by rw [h2]; group
        _ = (dG * v * dG⁻¹) * v * (a * a) := by rw [h3]; group
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (V.mul_mem hdv hv))
      (Subgroup.mem_sup_right (A₀.mul_mem ha ha))
  exact ⟨W, hWmem, hWcyc, hWcard, hDVAW, hA₀K, hSA₀, dG, hdK, hdD, hd4G, hd2G, hdsG, hdA, hdW,
    hdx⟩

end CFSG.Semidihedral.Principal.FieldFactorOneFixedCore
