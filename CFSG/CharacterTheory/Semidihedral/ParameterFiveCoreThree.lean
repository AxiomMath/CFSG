module

public import CFSG.CharacterTheory.Semidihedral.ParameterFiveGeneration
public import CFSG.CharacterTheory.Semidihedral.ParameterFiveThreeAction
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveCentralSplitting
public import CFSG.CharacterTheory.Semidihedral.OrderedPairLocalTransport
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusSylowFiveSupport

public section

namespace CFSG.Semidihedral.ParameterFive

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def ExtensionOfOrderBoundStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (_hindex : ∀ V : Subgroup G, V.index ≠ 2)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hLnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (_hbound : 2 * p ^ f * Nat.card G *
        Nat.card (C t ⊓ Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G) ^ 2 <
      5 * Nat.card (C t) ^ 3 * (p ^ f - 1))
    (θ : C t →* ℂˣ) (_hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (_hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c),
    ∃ lam : G →* ℂˣ, ∀ c : C t, lam c = θ c

theorem sd_four_r_sq_conj_s : r 4 ^ 2 * s 4 * (r 4 ^ 2)⁻¹ = z 4 * s 4 := by
  rw [r_pow_eq_element 4 (by norm_num) 2, s_eq_element 4 (by norm_num),
    conjugate_reflection_by_rotation, z_eq_element 4 (by norm_num), element_rotation_mul,
    element_eq_iff]
  refine ⟨?_, rfl⟩
  simp only [twist, half, modulus]
  decide

theorem sylow_le_centralizer {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) : (S : Subgroup G) ≤ C t := by
  obtain ⟨hzt, -⟩ := Principal.supplied_t_s_facts hn fS ht
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
  have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn)) (fS.symm ⟨x, hx⟩)
  have h' := congrArg (fun w => ((fS w : S) : G)) h
  simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'

theorem involution_isConj_of_le {G : Type} [Group G] [Finite G]
    (hG : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) {M : Subgroup G} (hCM : C t ≤ M) {η : G}
    (hηM : η ∈ M) (hη : η * (fS (s n) : G) * η⁻¹ = t) :
    ∀ x ∈ M, orderOf x = 2 → ∃ m ∈ M, m * t * m⁻¹ = x := by
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hSC := sylow_le_centralizer hn fS ht
  intro x hxM hx2
  obtain ⟨m, hmM, hmx⟩ := exists_conj_mem_sylow_of_le S (hSC.trans hCM) hxM (k := 1)
    (by rw [hx2, pow_one])
  have hyC : m⁻¹ * x * m ∈ C t := hSC hmx
  have hy2 : orderOf (m⁻¹ * x * m) = 2 := by
    rw [show m⁻¹ * x * m = m⁻¹ * x * m⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq]
    exact hx2
  by_cases hyt : m⁻¹ * x * m = t
  · refine ⟨m, hmM, ?_⟩
    rw [← hyt]
    group
  · let yC : C t := ⟨m⁻¹ * x * m, hyC⟩
    let sC : C t := ⟨(fS (s n) : G), hsC⟩
    have hyC2 : orderOf yC = 2 := by rw [Subgroup.orderOf_mk]; exact hy2
    have hsC2 : orderOf sC = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
    have hyCt : yC ≠ ActualFourGroupAlignment.actualInvolution t := fun h =>
      hyt (congrArg Subtype.val h)
    have hsCt : sC ≠ ActualFourGroupAlignment.actualInvolution t := fun h =>
      hst (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := ActualFourGroupAlignment.exists_actual_noncentral_involution_conjugator
      n hn S fS hG t ht2 sC yC hsC2 hyC2 hsCt hyCt
    have hc' : (c : G) * (fS (s n) : G) * (c : G)⁻¹ = m⁻¹ * x * m := congrArg Subtype.val hc
    refine ⟨m * c * η⁻¹, M.mul_mem (M.mul_mem hmM (hCM c.2)) (M.inv_mem hηM), ?_⟩
    have hs : η⁻¹ * t * η = (fS (s n) : G) := by rw [← hη]; group
    calc m * c * η⁻¹ * t * (m * c * η⁻¹)⁻¹ = m * ((c : G) * (η⁻¹ * t * η) * (c : G)⁻¹) * m⁻¹ := by
          group
      _ = x := by rw [hs, hc']; group

theorem centralizer_sup_zpowers_eq_top
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) {η : G}
    (hη : η * (fS (s n) : G) * η⁻¹ = t) : C t ⊔ Subgroup.zpowers η = ⊤ := by
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  apply eq_top_of_centralizer_le ht2 le_sup_left
    (involution_isConj_of_le hG hn S fS ht le_sup_left
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers η)) hη)
  · have hV := StationaryOddLocalization.actual_involution_pair_isKleinFour t (fS (s n) : G) ht2
      hs2 hsC hst.symm
    refine ⟨_, hV.card_four, fun x hx => ?_⟩
    have h := Monoid.pow_exponent_eq_one
      (⟨x, hx⟩ : Subgroup.closure ({t, (fS (s n) : G)} : Set G))
    rw [hV.exponent_two] at h
    exact congrArg Subtype.val h
  · intro hsol
    have : Group.IsSolvable (Gamma t) := inferInstance
    have : Group.IsSolvable (CFSG.generalizedFitting (Gamma t)) := inferInstance
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

theorem conj_not_mem_oddCore
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) {η : G}
    (hη : η * (fS (s n) : G) * η⁻¹ = t) (hN3 : Nat.card (N t) = 3) {u : G}
    (hu : u ∈ (N t).map (C t).subtype) (hu1 : u ≠ 1) :
    η * u * η⁻¹ ∉ (N t).map (C t).subtype := by
  intro hηu
  set N' := (N t).map (C t).subtype with hN'
  have hN'card : Nat.card N' = 3 := by
    rw [hN', Subgroup.card_map_of_injective (C t).subtype_injective, hN3]
  have hzu : Subgroup.zpowers u = N' := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu)
    rw [hN'card, Nat.card_zpowers]
    have hdvd : orderOf u ∣ 3 := hN'card ▸ Subgroup.orderOf_dvd_natCard N' hu
    have hne : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · omega
  have hηN : η ∈ Subgroup.normalizer (N' : Set G) := by
    apply Principal.TrivialCoreTorus.mem_normalizer_of_forall_conj_mem
    intro x hx
    rw [← hzu] at hx hηu ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : η * u ^ k * η⁻¹ = (η * u * η⁻¹) ^ k := by
      simp only [← MulAut.conj_apply, map_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ hηu k
  have hCN : C t ≤ Subgroup.normalizer (N' : Set G) := by
    intro c hc
    apply Principal.TrivialCoreTorus.mem_normalizer_of_forall_conj_mem
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (inferInstance : (N t).Normal).conj_mem y hy _, rfl⟩
  have htop : Subgroup.normalizer (N' : Set G) = ⊤ := by
    rw [eq_top_iff, ← centralizer_sup_zpowers_eq_top hGnonab hn S fS ht hnonab hη]
    exact sup_le hCN (Subgroup.zpowers_le.mpr hηN)
  have hnormal : N'.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with h | h
  · rw [h] at hu
    exact hu1 (Subgroup.mem_bot.mp hu)
  · have hG3 : Nat.card G = 3 := by rw [← Subgroup.card_top (G := G), ← h, hN'card]
    have : IsCyclic G := isCyclic_of_prime_card hG3
    obtain ⟨a, b, hab⟩ := hGnonab
    exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)

theorem conj_mem_centralizer_of_mem_normalizer {G : Type} [Group G] {T : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (hx : x ∈ Subgroup.centralizer (T : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ T := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
  have h := hx _ hv'
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * v := by group

theorem theta_conj_eq_of_mem_centralizer
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (fS : SemidihedralGroup 4 ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r 4) : G) ^ 2 ^ (4 - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hNZ : N t ≤ Subgroup.center (C t)) (hN3 : Nat.card (N t) = 3)
    (hC720 : Nat.card (C t) = 720)
    (hD36 : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s 4) : G)}) = 36)
    (Hs : Subgroup (C t)) (μ : Hs × N t ≃* C t) (hμ : ∀ x : Hs × N t, μ x = (x.1 : C t) * x.2)
    (θ : C t →* ℂˣ) (hθHs : ∀ h ∈ Hs, θ h = 1)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) {η : G}
    (hηT : η ∈ Subgroup.normalizer
      ((Subgroup.closure {t, (fS (s 4) : G)} : Subgroup G) : Set G))
    (hηt : η * t * η⁻¹ = t * (fS (s 4) : G)) (hηs : η * (fS (s 4) : G) * η⁻¹ = t) :
    ∀ c c' : C t, (c : G) ∈ Subgroup.centralizer
        ((Subgroup.closure {t, (fS (s 4) : G)} : Subgroup G) : Set G) →
      (c' : G) = η * c * η⁻¹ → θ c' = θ c := by
  intro c c' hc hc'
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set s₀ : G := (fS (s 4) : G) with hs₀
  obtain ⟨hzt, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts (le_refl 4) fS ht
  have hSC := sylow_le_centralizer (le_refl 4) fS ht
  set T : Subgroup G := Subgroup.closure {t, s₀} with hT
  set D : Subgroup G := Subgroup.centralizer (T : Set G) with hD
  have hTK : IsKleinFour T :=
    StationaryOddLocalization.actual_involution_pair_isKleinFour t s₀ ht2 hs2 hsC hst.symm
  have hts : s₀ * t = t * s₀ := Subgroup.mem_centralizer_singleton_iff.mp hsC
  have hmemD : ∀ x : G, x ∈ D ↔ x * t = t * x ∧ x * s₀ = s₀ * x := fun x =>
    Principal.FieldFactorOneFixedCore.mem_centralizer_closure_pair_iff
  have hDC : D ≤ C t := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hmemD x).mp hx).1
  have hDcard : Nat.card D = 36 := by
    have hDeq : D = C t ⊓ Subgroup.centralizer {s₀} := by
      ext x
      rw [hmemD, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
    rw [hDeq]
    exact hD36
  have hTS : T ≤ (S : Subgroup G) := by
    have htS : t ∈ (S : Subgroup G) := by
      rw [ht]
      exact Subgroup.pow_mem _ (fS (r 4)).property _
    rw [hT, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htS
    · exact (fS (s 4)).property
  obtain ⟨W₀', hW₀'⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 3 (n := 2)
    (by rw [hDcard]; norm_num)
  set W₀ : Subgroup G := W₀'.map D.subtype with hW₀
  have hW₀card : Nat.card W₀ = 9 := by
    rw [hW₀, Subgroup.card_map_of_injective D.subtype_injective, hW₀']
    norm_num
  have hW₀D : W₀ ≤ D := Subgroup.map_subtype_le _
  obtain ⟨hsup, hDab, hcube⟩ := klein_centralizer_thirtysix T W₀ hTK hDcard hW₀D hW₀card
  set N' : Subgroup G := (N t).map (C t).subtype with hN'
  have hN'card : Nat.card N' = 3 := by
    rw [hN', Subgroup.card_map_of_injective (C t).subtype_injective, hN3]
  have hN'comm : ∀ x ∈ N', ∀ y ∈ C t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h := Subgroup.mem_center_iff.mp (hNZ hx') ⟨y, hy⟩
    exact (congrArg Subtype.val h).symm
  have hN'D : N' ≤ D := fun x hx => (hmemD x).mpr
    ⟨hN'comm x hx t (Subgroup.mem_centralizer_singleton_iff.mpr rfl), hN'comm x hx s₀ hsC⟩
  have hN'3 : ∀ x ∈ N', x ^ 3 = 1 := fun x hx => by
    have h := Subgroup.orderOf_dvd_natCard N' hx
    rw [hN'card] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  obtain ⟨n₁, hn₁N, hn₁1⟩ : ∃ x ∈ N', x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : N' = ⊥ := (Subgroup.eq_bot_iff_forall N').mpr hcon
    rw [this, Subgroup.card_bot] at hN'card
    norm_num at hN'card
  have hn₁3 : n₁ ^ 3 = 1 := hN'3 n₁ hn₁N
  have hn₁o : orderOf n₁ = 3 := orderOf_eq_prime hn₁3 hn₁1
  have hzn : Subgroup.zpowers n₁ = N' := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hn₁N)
    rw [hN'card, Nat.card_zpowers, hn₁o]
  set Hs' : Subgroup G := Hs.map (C t).subtype with hHs'
  have hdec : ∀ x : C t, ∃ h ∈ Hs, ∃ m ∈ N t, x = h * m := fun x =>
    ⟨(μ.symm x).1, (μ.symm x).1.2, (μ.symm x).2, (μ.symm x).2.2, by
      rw [← hμ, μ.apply_symm_apply]⟩
  have hdisj : ∀ x ∈ N', x ∈ Hs' → x = 1 := by
    intro x hxN hxH
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hxN
    obtain ⟨h, hh, hhm⟩ := Subgroup.mem_map.mp hxH
    have hhm' : h = m := Subtype.ext hhm
    have e1 : μ (⟨h, hh⟩, 1) = μ (1, ⟨m, hm⟩) := by
      rw [hμ, hμ]
      simp [hhm']
    have e2 := congrArg Prod.fst (μ.injective e1)
    have e3 : h = 1 := congrArg Subtype.val e2
    change ((C t).subtype m) = 1
    rw [← hhm', e3, map_one]
  have hHscard : Nat.card Hs = 240 := by
    have h := Nat.card_congr μ.toEquiv
    rw [Nat.card_prod, hC720, hN3] at h
    omega
  have hHs'card : Nat.card Hs' = 240 := by
    rw [hHs', Subgroup.card_map_of_injective (C t).subtype_injective, hHscard]
  obtain ⟨w, hwW, hwN⟩ : ∃ w ∈ W₀, w ∉ N' := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show W₀ ≤ N' from hcon)
    rw [hW₀card, hN'card] at hle
    norm_num at hle
  obtain ⟨h, hh, m, hm, hwhm⟩ := hdec ⟨w, hDC (hW₀D hwW)⟩
  set k : G := (h : G) with hk
  have hmN' : (m : G) ∈ N' := ⟨m, hm, rfl⟩
  have hwk : w = k * m := congrArg Subtype.val hwhm
  have hkW : k ∈ W₀ := by
    have : k = w * (m : G)⁻¹ := by rw [hwk]; group
    rw [this]
    exact W₀.mul_mem hwW (W₀.inv_mem (hcube _ (hN'D hmN') (hN'3 _ hmN')))
  have hkH : k ∈ Hs' := ⟨h, hh, rfl⟩
  have hk1 : k ≠ 1 := by
    intro hk1
    apply hwN
    rw [hwk, hk1, one_mul]
    exact hmN'
  have hk3 : k ^ 3 = 1 := by
    have h9 : orderOf k ∣ 9 := hW₀card ▸ Subgroup.orderOf_dvd_natCard W₀ hkW
    have h240 : orderOf k ∣ 240 := hHs'card ▸ Subgroup.orderOf_dvd_natCard Hs' hkH
    have h3 : orderOf k ∣ 3 := by
      have := Nat.dvd_gcd h9 h240
      norm_num at this
      exact this
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hWH : ∀ x ∈ W₀, x ∈ Hs' → x ∈ Subgroup.zpowers k := by
    have hle : Subgroup.zpowers k ≤ W₀ ⊓ Hs' :=
      Subgroup.zpowers_le.mpr ⟨hkW, hkH⟩
    have hcard : Nat.card (W₀ ⊓ Hs' : Subgroup G) ≤ Nat.card (Subgroup.zpowers k) := by
      rw [Nat.card_zpowers, hko]
      have h9 : Nat.card (W₀ ⊓ Hs' : Subgroup G) ∣ 9 :=
        hW₀card ▸ Subgroup.card_dvd_of_le inf_le_left
      have h240 : Nat.card (W₀ ⊓ Hs' : Subgroup G) ∣ 240 :=
        hHs'card ▸ Subgroup.card_dvd_of_le inf_le_right
      have := Nat.dvd_gcd h9 h240
      norm_num at this
      exact Nat.le_of_dvd (by norm_num) this
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    intro x hxW hxH
    rw [heq]
    exact ⟨hxW, hxH⟩
  have hnk : Commute n₁ k := hN'comm n₁ hn₁N k (hDC (hW₀D hkW))
  have hind : ∀ i j : ℕ, n₁ ^ i * k ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    have hi : n₁ ^ i = (k ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hij
    have hiN : n₁ ^ i ∈ N' := N'.pow_mem hn₁N i
    have hiH : n₁ ^ i ∈ Hs' := by
      rw [hi]
      exact Hs'.inv_mem (Hs'.pow_mem hkH j)
    have h1 : n₁ ^ i = 1 := hdisj _ hiN hiH
    have h2 : k ^ j = 1 := by
      rw [h1] at hi
      exact (inv_eq_one.mp hi.symm)
    exact ⟨hn₁o ▸ orderOf_dvd_of_pow_eq_one h1, hko ▸ orderOf_dvd_of_pow_eq_one h2⟩
  have hcoord : ∀ x ∈ W₀, ∃ i j : ℕ, x = n₁ ^ i * k ^ j := by
    intro x hx
    obtain ⟨h', hh', m', hm', hxhm⟩ := hdec ⟨x, hDC (hW₀D hx)⟩
    have hm'N : (m' : G) ∈ N' := ⟨m', hm', rfl⟩
    have hx' : x = (h' : G) * m' := congrArg Subtype.val hxhm
    have hh'W : (h' : G) ∈ W₀ := by
      have : (h' : G) = x * (m' : G)⁻¹ := by rw [hx']; group
      rw [this]
      exact W₀.mul_mem hx (W₀.inv_mem (hcube _ (hN'D hm'N) (hN'3 _ hm'N)))
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hWH _ hh'W ⟨h', hh', rfl⟩))
    have hm'z : (m' : G) ∈ Subgroup.zpowers n₁ := hzn ▸ hm'N
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hm'z)
    refine ⟨i, j, ?_⟩
    rw [hx', ← hj, ← hi]
    exact (hnk.pow_pow i j).eq.symm
  have htT : t ∈ T := Subgroup.subset_closure (Set.mem_insert _ _)
  have hsT : s₀ ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hss : s₀ * s₀ = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have htst : t * s₀ * t = s₀ := by rw [mul_assoc, hts, ← mul_assoc, htt, one_mul]
  have hηD : ∀ x ∈ D, η * x * η⁻¹ ∈ D := fun x hx =>
    conj_mem_centralizer_of_mem_normalizer hηT hx
  set d : G := (fS (r 4) : G) ^ 2 with hd
  have hdS : d ∈ (S : Subgroup G) := Subgroup.pow_mem _ (fS (r 4)).property _
  have hdC : d ∈ C t := hSC hdS
  have hdt : d * t * d⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hdC]
    group
  have hds : d * s₀ * d⁻¹ = t * s₀ := by
    have h := congrArg (fun w => ((fS w : S) : G)) sd_four_r_sq_conj_s
    simp only [map_mul, map_pow, map_inv, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_inv] at h
    rw [hzt] at h
    exact h
  have hdts : d * (t * s₀) * d⁻¹ = s₀ := by
    have : d * (t * s₀) * d⁻¹ = (d * t * d⁻¹) * (d * s₀ * d⁻¹) := by group
    rw [this, hdt, hds, ← mul_assoc, htt, one_mul]
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := by
    apply Principal.TrivialCoreTorus.mem_normalizer_of_forall_conj_mem
    intro x hx
    rcases Principal.FieldFactorOneFixedCore.mem_closure_pair_cases hts.symm htt hss hx with
      rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact T.one_mem
    · rw [hdt]
      exact htT
    · rw [hds]
      exact T.mul_mem htT hsT
    · rw [hdts]
      exact hsT
  have hdD : ∀ x ∈ D, d * x * d⁻¹ ∈ D := fun x hx =>
    conj_mem_centralizer_of_mem_normalizer hdT hx
  have hn₁D : n₁ ∈ D := hN'D hn₁N
  have hkD : k ∈ D := hW₀D hkW
  have hdn : d * n₁ * d⁻¹ = n₁ := by
    rw [← hN'comm n₁ hn₁N d hdC]
    group
  have hconj3 : ∀ g x : G, x ^ 3 = 1 → (g * x * g⁻¹) ^ 3 = 1 := fun g x hx => by
    rw [← MulAut.conj_apply, ← map_pow, hx, map_one]
  obtain ⟨f, hdk⟩ : ∃ f : ℕ, d * k * d⁻¹ = k ^ f := by
    have hW : d * k * d⁻¹ ∈ W₀ := hcube _ (hdD k hkD) (hconj3 d k hk3)
    have hH : d * k * d⁻¹ ∈ Hs' := by
      obtain ⟨h'', hh'', m'', hm'', hdhm⟩ := hdec ⟨d, hdC⟩
      have hd' : d = (h'' : G) * m'' := congrArg Subtype.val hdhm
      have hmk : (m'' : G) * k = k * m'' := hN'comm _ ⟨m'', hm'', rfl⟩ k (hDC hkD)
      have : d * k * d⁻¹ = (h'' : G) * k * (h'' : G)⁻¹ := by
        rw [hd']
        calc (h'' : G) * m'' * k * ((h'' : G) * m'')⁻¹ =
            (h'' : G) * ((m'' : G) * k) * (m'' : G)⁻¹ * (h'' : G)⁻¹ := by group
          _ = (h'' : G) * (k * m'') * (m'' : G)⁻¹ * (h'' : G)⁻¹ := by rw [hmk]
          _ = (h'' : G) * k * (h'' : G)⁻¹ := by group
      rw [this]
      exact ⟨h'' * h * h''⁻¹, Hs.mul_mem (Hs.mul_mem hh'' hh) (Hs.inv_mem hh''), rfl⟩
    obtain ⟨f, hf⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hWH _ hW hH))
    exact ⟨f, hf.symm⟩
  obtain ⟨a, b, hηn⟩ := hcoord _ (hcube _ (hηD n₁ hn₁D) (hconj3 η n₁ hn₁3))
  obtain ⟨c₀, e, hηk⟩ := hcoord _ (hcube _ (hηD k hkD) (hconj3 η k hk3))
  have hηts : η * (t * s₀) * η⁻¹ = s₀ := by
    have : η * (t * s₀) * η⁻¹ = (η * t * η⁻¹) * (η * s₀ * η⁻¹) := by group
    rw [this, hηt, hηs, htst]
  have hcomm_of_conj : ∀ g x : G, g * x * g⁻¹ = x → g * x = x * g := fun g x h => by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  have hη3D : η ^ 3 ∈ D := by
    rw [hmemD, pow_three']
    constructor
    · apply hcomm_of_conj
      calc η * η * η * t * (η * η * η)⁻¹ = η * (η * (η * t * η⁻¹) * η⁻¹) * η⁻¹ := by group
        _ = t := by rw [hηt, hηts, hηs]
    · apply hcomm_of_conj
      calc η * η * η * s₀ * (η * η * η)⁻¹ = η * (η * (η * s₀ * η⁻¹) * η⁻¹) * η⁻¹ := by group
        _ = s₀ := by rw [hηs, hηt, hηts]
  have h3 : η ^ 3 * n₁ * (η ^ 3)⁻¹ = n₁ := by
    rw [hDab _ hη3D _ hn₁D]
    group
  have hdinv_t : d⁻¹ * t * d = t := by
    calc d⁻¹ * t * d = d⁻¹ * (d * t * d⁻¹) * d := by rw [hdt]
      _ = t := by group
  have hdinv_s : d⁻¹ * s₀ * d = t * s₀ := by
    calc d⁻¹ * s₀ * d = d⁻¹ * (d * (t * s₀) * d⁻¹) * d := by rw [hdts]
      _ = t * s₀ := by group
  have hcD : η * d * η * d⁻¹ ∈ D := by
    rw [hmemD]
    constructor
    · apply hcomm_of_conj
      calc η * d * η * d⁻¹ * t * (η * d * η * d⁻¹)⁻¹ =
          η * (d * (η * (d⁻¹ * t * d) * η⁻¹) * d⁻¹) * η⁻¹ := by group
        _ = t := by rw [hdinv_t, hηt, hdts, hηs]
    · apply hcomm_of_conj
      calc η * d * η * d⁻¹ * s₀ * (η * d * η * d⁻¹)⁻¹ =
          η * (d * (η * (d⁻¹ * s₀ * d) * η⁻¹) * d⁻¹) * η⁻¹ := by group
        _ = s₀ := by rw [hdinv_s, hηts, hds, hηts]
  have hrel : ∀ x ∈ D, (η * d * η) * x * (η * d * η)⁻¹ = d * x * d⁻¹ := by
    intro x hx
    have hdx : d * x * d⁻¹ ∈ D := hdD x hx
    have hc := hDab _ hcD _ hdx
    calc (η * d * η) * x * (η * d * η)⁻¹ =
        (η * d * η * d⁻¹) * (d * x * d⁻¹) * (η * d * η * d⁻¹)⁻¹ := by group
      _ = d * x * d⁻¹ := by rw [hc]; group
  have hb : ¬ 3 ∣ b := by
    intro h3b
    apply conj_not_mem_oddCore hGnonab (le_refl 4) S fS ht hnonab hηs hN3 hn₁N hn₁1
    rw [hηn]
    obtain ⟨q, hq⟩ := h3b
    rw [hq, pow_mul, hk3, one_pow, mul_one]
    exact N'.pow_mem hn₁N a
  have hWinv : ∀ x ∈ W₀, η * x * η⁻¹ * x⁻¹ ∈ Hs' := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := hcoord x hx
    exact (Subgroup.zpowers_le.mpr hkH) (conj_mul_inv_mem_zpowers hn₁3 hk3 hnk hind hηn hηk hdn
      hdk h3 (hrel n₁ hn₁D) (hrel k hkD) hb i j)
  have hTD : T ≤ D := fun x hx y hy =>
    congrArg Subtype.val (mul_comm_of_exponent_two hTK.exponent_two ⟨y, hy⟩ ⟨x, hx⟩)
  let ι : D →* C t := Subgroup.inclusion hDC
  let cη : D →* D :=
    { toFun := fun x => ⟨η * x * η⁻¹, hηD x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let ψ₁ : D →* ℂˣ := θ.comp ι
  let ψ₂ : D →* ℂˣ := θ.comp (ι.comp cη)
  have hT' : T.subgroupOf D ≤ MonoidHom.eqLocus ψ₁ ψ₂ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : η * (x : G) * η⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hηT x).mp hx
    change θ (ι x) = θ (ι (cη x))
    rw [hθS (ι x) (hTS hx), hθS (ι (cη x)) (hTS hx')]
  have hW' : W₀.subgroupOf D ≤ MonoidHom.eqLocus ψ₁ ψ₂ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨h₀, hh₀, hh₀eq⟩ := Subgroup.mem_map.mp (hWinv _ hx)
    have hsplit : ι (cη x) = h₀ * ι x := by
      apply Subtype.ext
      change η * (x : G) * η⁻¹ = (h₀ : G) * (x : G)
      rw [show ((C t).subtype h₀ : G) = (h₀ : G) from rfl] at hh₀eq
      rw [hh₀eq]
      group
    change θ (ι x) = θ (ι (cη x))
    rw [hsplit, map_mul, hθHs h₀ hh₀, one_mul]
  have htop : MonoidHom.eqLocus ψ₁ ψ₂ = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup D) = (T ⊔ W₀).subgroupOf D := by rw [hsup, Subgroup.subgroupOf_self]
      _ = T.subgroupOf D ⊔ W₀.subgroupOf D := Subgroup.subgroupOf_sup hTD hW₀D
      _ ≤ _ := sup_le hT' hW'
  have hmem : (⟨(c : G), hc⟩ : D) ∈ MonoidHom.eqLocus ψ₁ ψ₂ := htop ▸ Subgroup.mem_top _
  have e1 : ι ⟨(c : G), hc⟩ = c := Subtype.ext rfl
  have e2 : ι (cη ⟨(c : G), hc⟩) = c' := Subtype.ext hc'.symm
  have hmem' : θ (ι ⟨(c : G), hc⟩) = θ (ι (cη ⟨(c : G), hc⟩)) := hmem
  rw [e1, e2] at hmem'
  exact hmem'.symm

theorem theta_invariant_of_mem_normalizer
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (fS : SemidihedralGroup 4 ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r 4) : G) ^ 2 ^ (4 - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hNZ : N t ≤ Subgroup.center (C t)) (hN3 : Nat.card (N t) = 3)
    (hC720 : Nat.card (C t) = 720)
    (hD36 : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s 4) : G)}) = 36)
    (Hs : Subgroup (C t)) (μ : Hs × N t ≃* C t) (hμ : ∀ x : Hs × N t, μ x = (x.1 : C t) * x.2)
    (θ : C t →* ℂˣ) (hθHs : ∀ h ∈ Hs, θ h = 1)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) {η : G}
    (hηT : η ∈ Subgroup.normalizer
      ((Subgroup.closure {t, (fS (s 4) : G)} : Subgroup G) : Set G))
    (hηt : η * t * η⁻¹ = t * (fS (s 4) : G)) (hηs : η * (fS (s 4) : G) * η⁻¹ = t) :
    ∀ g ∈ Subgroup.normalizer ((Subgroup.closure {t, (fS (s 4) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s 4) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c := by
  have hE := theta_conj_eq_of_mem_centralizer hGnonab S fS ht hnonab hNZ hN3 hC720 hD36 Hs μ
    hμ θ hθHs hθS hηT hηt hηs
  set s₀ : G := (fS (s 4) : G) with hs₀
  set T : Subgroup G := Subgroup.closure {t, s₀} with hT
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts (le_refl 4) fS ht
  have hts : s₀ * t = t * s₀ := Subgroup.mem_centralizer_singleton_iff.mp hsC
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hss : s₀ * s₀ = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have htT : t ∈ T := Subgroup.subset_closure (Set.mem_insert _ _)
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; exact absurd ht2 (by norm_num)
  have hCconj : ∀ k ∈ C t, ∀ c c' : C t, (c' : G) = k * c * k⁻¹ → θ c' = θ c := by
    intro k hk c c' hc'
    have hc'' : c' = ⟨k, hk⟩ * c * ⟨k, hk⟩⁻¹ := Subtype.ext hc'
    rw [hc'', map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, inv_mul_cancel, one_mul]
  have hTmem : ∀ x ∈ Subgroup.centralizer (T : Set G), ∀ g ∈ Subgroup.normalizer (T : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := fun x hx g hg =>
    conj_mem_centralizer_of_mem_normalizer hg hx
  have hCT : Subgroup.centralizer (T : Set G) ≤ C t := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) t htT).symm
  intro g hg c c' hc hc'
  have hgt : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg t).mp htT
  have hgt1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hηinv : η⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).inv_mem hηT
  rcases Principal.FieldFactorOneFixedCore.mem_closure_pair_cases hts.symm htt hss hgt with
    h | h | h | h
  · exact absurd h hgt1
  ·
    have hgC : g ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h]
    exact hCconj g hgC c c' hc'
  ·
    set k := η⁻¹ * η⁻¹ * g with hk
    have hkt : k * t * k⁻¹ = t := by
      have hηts : η * (t * s₀) * η⁻¹ = s₀ := by
        have : η * (t * s₀) * η⁻¹ = (η * t * η⁻¹) * (η * s₀ * η⁻¹) := by group
        rw [this, hηt, hηs, mul_assoc, hts, ← mul_assoc, htt, one_mul]
      have e1 : η⁻¹ * s₀ * η = t * s₀ := by
        calc η⁻¹ * s₀ * η = η⁻¹ * (η * (t * s₀) * η⁻¹) * η := by rw [hηts]
          _ = t * s₀ := by group
      have e2 : η⁻¹ * (t * s₀) * η = t := by
        calc η⁻¹ * (t * s₀) * η = η⁻¹ * (η * t * η⁻¹) * η := by rw [hηt]
          _ = t := by group
      calc k * t * k⁻¹ = η⁻¹ * (η⁻¹ * (g * t * g⁻¹) * η) * η := by
            simp only [hk, mul_inv_rev, inv_inv, mul_assoc]
        _ = t := by rw [h, e1, e2]
    have hkC : k ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * t = k * t * k⁻¹ * k := by group
        _ = t * k := by rw [hkt]
    have hkN : k ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hηinv hηinv) hg
    have hc₁ : k * c * k⁻¹ ∈ Subgroup.centralizer (T : Set G) := hTmem _ hc k hkN
    set c₁ : C t := ⟨k * c * k⁻¹, hCT hc₁⟩ with hc₁def
    have hc₂ : η * c₁ * η⁻¹ ∈ Subgroup.centralizer (T : Set G) := hTmem _ hc₁ η hηT
    set c₂ : C t := ⟨η * c₁ * η⁻¹, hCT hc₂⟩ with hc₂def
    have e3 : θ c₂ = θ c₁ := hE c₁ c₂ hc₁ rfl
    have e4 : θ c' = θ c₂ := hE c₂ c' hc₂ (by
      rw [hc']
      show g * (c : G) * g⁻¹ = η * (η * (k * (c : G) * k⁻¹) * η⁻¹) * η⁻¹
      rw [hk]
      group)
    rw [e4, e3]
    exact hCconj k hkC c c₁ rfl
  ·
    set k := η⁻¹ * g with hk
    have hkt : k * t * k⁻¹ = t := by
      calc k * t * k⁻¹ = η⁻¹ * (g * t * g⁻¹) * η := by rw [hk]; group
        _ = η⁻¹ * (η * t * η⁻¹) * η := by rw [h, hηt]
        _ = t := by group
    have hkC : k ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * t = k * t * k⁻¹ * k := by group
        _ = t * k := by rw [hkt]
    have hkN : k ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).mul_mem hηinv hg
    have hc₁ : k * c * k⁻¹ ∈ Subgroup.centralizer (T : Set G) := hTmem _ hc k hkN
    set c₁ : C t := ⟨k * c * k⁻¹, hCT hc₁⟩ with hc₁def
    have e3 : θ c' = θ c₁ := hE c₁ c' hc₁ (by
      rw [hc']
      show g * (c : G) * g⁻¹ = η * (k * (c : G) * k⁻¹) * η⁻¹
      rw [hk]
      group)
    rw [e3]
    exact hCconj k hkC c c₁ rfl

theorem card_oddCore_eq_one_of_extension
    (hext : ExtensionOfOrderBoundStatement)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1) :
    Nat.card (N t) = 1 := by
  have : Fintype G := Fintype.ofFinite G
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hn4, -⟩ := Principal.simple_local_parameter_five_is_regular_with_exact_order hGnonab n
    hn S fS t ht hnonab hcentral hnc hmodel
  subst hn4
  obtain ⟨hNZ, hNcyc, hN13, -, -, -, -, -, -, hC240, -, hD12, -, hG126, -, -, hsplit⟩ :=
    Principal.simple_local_parameter_five_central_odd_core_and_actual_centralizer_splitting
      hGnonab 4 hn S fS t ht hnonab hcentral hnc hmodel
  rcases hN13 with hN1 | hN3
  · exact hN1
  exfalso
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨⟨μ, hμ⟩, -⟩ := hsplit ⟨_, hsC⟩ rfl
  have hC720 : Nat.card (C t) = 720 := by rw [hC240, hN3]
  have hD36 : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s 4) : G)}) = 36 := by
    rw [hD12, hN3]
  have hG378 : Nat.card G = 378000 := by rw [hG126, hN3]
  obtain ⟨u, hu1⟩ : ∃ u : N t, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (N t) := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    rw [Nat.card_unique] at hN3
    norm_num at hN3
  obtain ⟨ι, hι⟩ : ∃ ι : N t →* ℂˣ, ι u ≠ 1 := by
    let _ : CommGroup (N t) := IsCyclic.commGroup
    have : NeZero (Monoid.exponent (N t)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    exact CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (N t) ℂ hu1
  let π : C t →* N t := (MonoidHom.snd _ _).comp μ.symm.toMonoidHom
  let θ : C t →* ℂˣ := ι.comp π
  have hπHs : ∀ h ∈ _, π h = 1 := fun h hh => by
    have : μ.symm h = (⟨h, hh⟩, 1) := by
      apply μ.injective
      rw [μ.apply_symm_apply, hμ]
      simp
    change (μ.symm h).2 = 1
    rw [this]
  have hπN : ∀ m : N t, π m = m := fun m => by
    have : μ.symm m = (1, m) := by
      apply μ.injective
      rw [μ.apply_symm_apply, hμ]
      simp
    change (μ.symm m).2 = m
    rw [this]
  have hθHs : ∀ h ∈ _, θ h = 1 := fun h hh => by
    change ι (π h) = 1
    rw [hπHs h hh, map_one]
  have hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1 := by
    intro c hc
    obtain ⟨k, hk⟩ := (S.isPGroup') ⟨c, hc⟩
    have hck : c ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    have h1 : orderOf (π c) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hck, map_one])
    have h2 : orderOf (π c) ∣ 3 := hN3 ▸ orderOf_dvd_natCard (π c)
    have h3 : orderOf (π c) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
      · exact h
      · rw [h] at h1
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1) (by norm_num)
    change ι (π c) = 1
    rw [orderOf_eq_one_iff.mp h3, map_one]
  have hcomm : Commute t (fS (s 4) : G) := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  obtain ⟨η, hηT, hηt, hηs⟩ :=
    OrderedPairLocalTransport.original_ordered_pair_normalizer_conjugator 4 hn S fS t
      (fS (s 4) : G) (t * (fS (s 4) : G)) ht2 hs2 hcomm hst.symm (Or.inr rfl)
  have hθT := theta_invariant_of_mem_normalizer hGnonab S fS ht hnonab hNZ hN3 hC720 hD36 _ μ hμ
    θ hθHs hθS hηT hηt hηs
  obtain ⟨lam, hlam⟩ := hext G hG 4 hn S fS t ht hnonab hcentral hnc 5 1 Nat.prime_five
    (by decide) le_rfl hmodel (by rw [hG378, hC720, hD36]; norm_num) θ hθS hθT
  have hlam1 : ∀ g : G, lam g = 1 := fun g =>
    Abelianization.commutator_subset_ker lam Group.IsPerfect.mem_commutator
  apply hι
  have h := hlam ((N t).subtype u)
  rw [hlam1] at h
  have h' : θ ((N t).subtype u) = ι u := by
    change ι (π ((N t).subtype u)) = ι u
    rw [show (N t).subtype u = (u : C t) from rfl, hπN]
  rw [← h', ← h]

end CFSG.Semidihedral.ParameterFive
