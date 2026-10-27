module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Branch
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Prod CFSG.GH74.GLS.Stage1.Thm6.M12Facts
open scoped Pointwise

section BarFacts

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem m12_barFacts (h : Stage1M12 G z S) :
    (WBar z).Normal ∧ IsPGroup 2 ↥(WBar z) ∧ Nat.card (CentralizerBar z) = 192 ∧
      ∀ X : Subgroup (CentralizerBar z), Nat.card ↥X = 3 → ∀ w ∈ WBar z,
        (∀ x ∈ X, x * w = w * x) → w ∈ barOf z (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, B, hAB, hAq, hBq, hAn⟩ := h.W_shape
  obtain ⟨A₃, hA₃, -, hOres, hFst, hcomm, hfix⟩ := h.L_shape
  obtain ⟨hWn, ⟨eq⟩⟩ := h.quot
  obtain ⟨cA, hA8'⟩ := q8Like_of_equiv hAq.some
  obtain ⟨cB, hB8'⟩ := q8Like_of_equiv hBq.some
  have hAcard : Nat.card ↥A = 8 := by rw [Nat.card_congr hAq.some.toEquiv]; exact card_Q8
  have hBcard : Nat.card ↥B = 8 := by rw [Nat.card_congr hBq.some.toEquiv]; exact card_Q8
  have hWcard : Nat.card ↥(WBar z) = 32 := by
    have := card_sup_mul_card_inf hAB.2.1
    rw [hAB.1, hAB.2.2, hAcard, hBcard] at this
    omega
  have hWpg : IsPGroup 2 ↥(WBar z) := IsPGroup.of_card (n := 5) (by rw [hWcard]; norm_num)
  have hCcard : Nat.card (CentralizerBar z) = 192 := by
    have := Subgroup.card_mul_index (WBar z)
    rw [hWcard, Subgroup.index_eq_card, Nat.card_congr eq.toEquiv] at this
    rw [← this]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  refine ⟨hWn, hWpg, hCcard, ?_⟩
  intro X hX w hw hXw
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hA₃card : Nat.card ↥A₃ = 3 := by
    rw [Nat.card_congr hA₃.some.toEquiv]; simp [Nat.card_eq_fintype_card]
  have hidxA : ¬ 3 ∣ A₃.index := by
    have := Subgroup.card_mul_index A₃
    rw [hA₃card, hCcard] at this
    omega
  have hidxX : ¬ 3 ∣ X.index := by
    have := Subgroup.card_mul_index X
    rw [hX, hCcard] at this
    omega
  have hPA : IsPGroup 3 ↥A₃ := IsPGroup.of_card (n := 1) (by rw [hA₃card]; norm_num)
  have hPX : IsPGroup 3 ↥X := IsPGroup.of_card (n := 1) (by rw [hX]; norm_num)
  let YA : Sylow 3 (CentralizerBar z) := hPA.toSylow hidxA
  let YX : Sylow 3 (CentralizerBar z) := hPX.toSylow hidxX
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (CentralizerBar z) YA YX
  have hAX : ∀ a ∈ A₃, c * a * c⁻¹ ∈ X := by
    intro a ha
    have hmem : c * a * c⁻¹ ∈ ((c • YA : Sylow 3 (CentralizerBar z)) : Subgroup (CentralizerBar z)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj c) _ ha
    rw [hc] at hmem
    exact hmem
  have hw' : c⁻¹ * w * c ∈ WBar z := by
    have := hWn.conj_mem w hw c⁻¹
    simpa using this
  have hcomm' : ∀ a ∈ A₃, a * (c⁻¹ * w * c) = (c⁻¹ * w * c) * a := by
    intro a ha
    have h1 := hXw _ (hAX a ha)
    have h3 : c * a * c⁻¹ * w = w * (c * a * c⁻¹) := h1
    calc a * (c⁻¹ * w * c) = c⁻¹ * (c * a * c⁻¹ * w) * c := by group
      _ = c⁻¹ * (w * (c * a * c⁻¹)) * c := by rw [h3]
      _ = (c⁻¹ * w * c) * a := by group
  have hfx := hfix _ hw' hcomm'
  rw [barOf_zpowers z] at hfx
  rw [barOf_zpowers z]
  obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff).1 hfx
  have hcen := zBar_central z
  have hc' : Commute c (toBar z ⟨z, z_mem_Cen z⟩) := hcen c
  have hwn : w = toBar z ⟨z, z_mem_Cen z⟩ ^ n := by
    calc w = c * (c⁻¹ * w * c) * c⁻¹ := by group
      _ = c * (toBar z ⟨z, z_mem_Cen z⟩ ^ n) * c⁻¹ := by rw [hn]
      _ = toBar z ⟨z, z_mem_Cen z⟩ ^ n := (hc'.zpow_right n).mul_inv_cancel
  exact ⟨n, hwn.symm⟩

end BarFacts

theorem pPrimePCore_map_iso {H H' : Type*} [Group H] [Group H'] (p : ℕ) (e : H ≃* H') :
    (pPrimePCore p H).map e.toMonoidHom = pPrimePCore p H' := by
  have hN := CFSG.pPrimeCore_map_iso p e
  let ē : H ⧸ pPrimeCore p H ≃* H' ⧸ pPrimeCore p H' := QuotientGroup.congr _ _ e hN
  have hP : (pCore p (H ⧸ pPrimeCore p H)).map ē.toMonoidHom = pCore p (H' ⧸ pPrimeCore p H') :=
    CFSG.pCore_map_iso p ē
  ext x
  rw [Subgroup.mem_map_equiv]
  unfold pPrimePCore
  rw [Subgroup.mem_comap, Subgroup.mem_comap, ← hP, Subgroup.mem_map_equiv]
  have : ē.symm ((QuotientGroup.mk' (pPrimeCore p H')) x) =
      (QuotientGroup.mk' (pPrimeCore p H)) (e.symm x) := by
    apply ē.injective
    rw [MulEquiv.apply_symm_apply]
    have h1 := QuotientGroup.congr_mk (pPrimeCore p H) (pPrimeCore p H') e hN (e.symm x)
    have h2 : ē ((e.symm x : H) : H ⧸ pPrimeCore p H) = ((e (e.symm x) : H') : H' ⧸ pPrimeCore p H') := h1
    show (x : H' ⧸ pPrimeCore p H') = ē ((e.symm x : H) : H ⧸ pPrimeCore p H)
    rw [h2]
    simp
  rw [this]

theorem WC_eq_O22Of {G : Type} [Group G] (z : G) : WC z = O22Of (O2Of (Cen z)) := by
  let R : Subgroup ↥(Cen z) := oResidual 2 ↥(Cen z)
  let e : ↥R ≃* ↥(R.map (Cen z).subtype) :=
    R.equivMapOfInjective (Cen z).subtype (Cen z).subtype_injective
  have h1 := pPrimePCore_map_iso 2 e
  show ((pPrimePCore 2 ↥R).map R.subtype).map (Cen z).subtype =
    (pPrimePCore 2 ↥(R.map (Cen z).subtype)).map (R.map (Cen z).subtype).subtype
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

section OddCore

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem coprime_orderOf_of_mem_OddCore {a : G} (ha : a ∈ OddCore z) : Nat.Coprime 2 (orderOf a) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, rfl⟩ := ha
  have h1 : orderOf (⟨c, hc⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
    _root_.orderOf_dvd_natCard _
  have h2 : orderOf ((c : ↥(Cen z)) : G) = orderOf (⟨c, hc⟩ : ↥(pPrimeCore 2 ↥(Cen z))) := by
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_coe c
  show Nat.Coprime 2 (orderOf ((c : ↥(Cen z)) : G))
  rw [h2]
  exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card

theorem eq_one_of_two_pow_of_mem_OddCore {a : G} (ha : a ∈ OddCore z) {k : ℕ} (hk : a ^ (2 ^ k) = 1) :
    a = 1 := by
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf a) (2 ^ k) :=
    ((coprime_orderOf_of_mem_OddCore ha).symm).pow_right k
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h1)

omit [Finite G] in
theorem Cen_le_normalizer_OddCore (z : G) : Cen z ≤ normalizer ((OddCore z : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfwd : ∀ c ∈ Cen z, ∀ x ∈ OddCore z, c * x * c⁻¹ ∈ OddCore z := by
    intro c hc x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥(Cen z))).conj_mem y hy ⟨c, hc⟩
  intro c hc
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact hfwd c hc x hx
  · intro hx
    have h1 := hfwd c⁻¹ (inv_mem hc) _ hx
    have h3 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rw [h3] at h1
    exact h1

theorem stage2OddCoreM12_of_max (hctx : Stage2Ctx G z Kind.m12 S) (hmax : IsCoatom (Cen z))
    (hdir : IsInternalDirectProduct (OddCore z) (O2coreOf (O2Of (Cen z))) (WC z)) :
    pPrimeCore 2 ↥(Cen z) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h := stage1M12_of_stage1Data hctx.data
  obtain ⟨hWn, hWpg, hCcard, hfpf⟩ := m12_barFacts h
  obtain ⟨U, hUS, hU4, hUn, hzU, hUW, huniq, hAut⟩ := h.four_group
  have hz2 : orderOf z = 2 := hctx.central.1
  have hz1 : z ≠ 1 := by intro e; rw [e, orderOf_one] at hz2; omega
  have hSpg : IsPGroup 2 ↥S := hctx.sylow.isPGroup
  have hUC : U ≤ Cen z := hUS.trans hctx.S_le_Cen
  have hU2 : ∀ u ∈ U, ∃ k : ℕ, u ^ (2 ^ k) = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hSpg ⟨u, hUS hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hAU : ∀ a ∈ OddCore z, ∀ u ∈ U, a * u = u * a := by
    intro a ha u hu
    obtain ⟨hsup, hcomm, hinf⟩ := hdir
    have hfix : ∀ a' ∈ OddCore z, ∀ b' ∈ O2coreOf (O2Of (Cen z)), a' * b' * a'⁻¹ = b' := by
      intro a' ha' b' hb'
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm a' ha' b' hb'
    have hle : OddCore z ≤ normalizer ((O2coreOf (O2Of (Cen z)) : Subgroup G) : Set G) := by
      intro a' ha'
      rw [mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        rw [hfix a' ha' b hb]
        exact hb
      · intro hb
        have h1 := hfix a'⁻¹ (inv_mem ha') _ hb
        have h3 : a'⁻¹ * (a' * b * a'⁻¹) * a'⁻¹⁻¹ = b := by group
        rw [h3] at h1
        rw [h1]
        exact hb
    have hmem : u ∈ OddCore z ⊔ O2coreOf (O2Of (Cen z)) := by rw [hsup]; exact hUW hu
    have hmem' : u ∈ ((OddCore z : Subgroup G) : Set G) *
        ((O2coreOf (O2Of (Cen z)) : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
      exact hmem
    obtain ⟨a₁, ha₁, b₁, hb₁, hu1⟩ := Set.mem_mul.1 hmem'
    have hc1 : Commute a₁ b₁ := hcomm a₁ ha₁ b₁ hb₁
    obtain ⟨k, hk⟩ := hU2 u hu
    rw [← hu1, hc1.mul_pow] at hk
    have hpow : a₁ ^ (2 ^ k) ∈ OddCore z ⊓ O2coreOf (O2Of (Cen z)) := by
      refine ⟨pow_mem ha₁ _, ?_⟩
      have : a₁ ^ (2 ^ k) = (b₁ ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [this]
      exact (O2coreOf (O2Of (Cen z))).inv_mem ((O2coreOf (O2Of (Cen z))).pow_mem hb₁ _)
    rw [hinf] at hpow
    have ha1 : a₁ = 1 := eq_one_of_two_pow_of_mem_OddCore ha₁ (by simpa using hpow)
    rw [ha1, one_mul] at hu1
    rw [← hu1]
    exact hcomm a ha b₁ hb₁
  obtain ⟨g, hgN, hgz⟩ := exists_move_of_autOrd hU4 hzU hz1 hAut
  have hgU : ∀ u : G, u ∈ U ↔ g * u * g⁻¹ ∈ U := Subgroup.mem_normalizer_iff.1 hgN
  have hgU' : ∀ u ∈ U, g⁻¹ * u * g ∈ U := by
    intro u hu
    refine (hgU _).2 ?_
    have : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [this]
    exact hu
  have hcommU : ∀ a ∈ OddCore z, ∀ u ∈ U, (g * a * g⁻¹) * u = u * (g * a * g⁻¹) := by
    intro a ha u hu
    have h1 := hAU a ha _ (hgU' u hu)
    calc g * a * g⁻¹ * u = g * (a * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * a) * g⁻¹ := by rw [h1]
      _ = u * (g * a * g⁻¹) := by group
  have hgC : ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ Cen z := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcommU a ha z hzU
  obtain ⟨t, htU, htz⟩ : ∃ t ∈ U, t ∉ zpowers z := by
    by_contra hall
    push Not at hall
    have hle : U ≤ zpowers z := fun t ht => hall t ht
    have := Subgroup.card_le_of_le hle
    rw [hU4.2, Nat.card_zpowers, hz2] at this
    omega
  have key : ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z := by
    intro a ha
    let c : ↥(Cen z) := ⟨g * a * g⁻¹, hgC a ha⟩
    suffices hc : toBar z c = 1 by
      have hker : c ∈ pPrimeCore 2 ↥(Cen z) := by
        rw [← ker_toBar z]
        exact hc
      exact ⟨c, hker, rfl⟩
    by_contra hbar
    have hord_dvd : orderOf (toBar z c) ∣ orderOf a := by
      have h1 : orderOf (toBar z c) ∣ orderOf c := orderOf_map_dvd (toBar z) c
      have h2 : orderOf c = orderOf (g * a * g⁻¹) := (Subgroup.orderOf_coe c).symm
      have h3 : orderOf (g * a * g⁻¹) = orderOf a := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) a
        rw [MulAut.conj_apply] at this
        exact this
      rw [h2, h3] at h1
      exact h1
    have hcop : Nat.Coprime 2 (orderOf (toBar z c)) :=
      Nat.Coprime.coprime_dvd_right hord_dvd (coprime_orderOf_of_mem_OddCore ha)
    have hdvd192 : orderOf (toBar z c) ∣ 192 := by
      rw [← hCcard]; exact _root_.orderOf_dvd_natCard _
    have hdvd3 : orderOf (toBar z c) ∣ 3 := by
      have h64 : Nat.Coprime (orderOf (toBar z c)) 64 := by
        have : Nat.Coprime (orderOf (toBar z c)) (2 ^ 6) := (hcop.symm).pow_right 6
        simpa using this
      have : orderOf (toBar z c) ∣ 64 * 3 := by simpa using hdvd192
      exact h64.dvd_of_dvd_mul_left this
    have hne1 : orderOf (toBar z c) ≠ 1 := fun e => hbar (orderOf_eq_one_iff.1 e)
    have hord3 : orderOf (toBar z c) = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd3 with h1 | h1
      · exact absurd h1 hne1
      · exact h1
    have hX : Nat.card ↥(zpowers (toBar z c)) = 3 := by rw [Nat.card_zpowers, hord3]
    have htC : t ∈ Cen z := hUC htU
    have htW : toBar z ⟨t, htC⟩ ∈ WBar z := (mem_WC_iff z ⟨t, htC⟩).1 (hUW htU)
    have hcommt : toBar z c * toBar z ⟨t, htC⟩ = toBar z ⟨t, htC⟩ * toBar z c := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hcommU a ha t htU
    have hXt : ∀ x ∈ zpowers (toBar z c), x * toBar z ⟨t, htC⟩ = toBar z ⟨t, htC⟩ * x := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((Commute.zpow_left hcommt n) : Commute _ _).eq
    have hzt := hfpf _ hX _ htW hXt
    rw [barOf_zpowers z] at hzt
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hzt
    have hzC : z ∈ Cen z := z_mem_Cen z
    have hmem : (z ^ n)⁻¹ * t ∈ OddCore z := by
      have h1 : toBar z ((⟨z, hzC⟩ : ↥(Cen z)) ^ n)⁻¹ * toBar z ⟨t, htC⟩ = 1 := by
        rw [map_inv, map_zpow, hn, inv_mul_cancel]
      refine ⟨((⟨z, hzC⟩ : ↥(Cen z)) ^ n)⁻¹ * ⟨t, htC⟩, ?_, ?_⟩
      · rw [← ker_toBar z]
        simpa [map_mul, map_inv, map_zpow] using h1
      · simp
    have hmemU : (z ^ n)⁻¹ * t ∈ U := mul_mem (inv_mem (zpow_mem hzU n)) htU
    obtain ⟨k, hk⟩ := hU2 _ hmemU
    have h1 : (z ^ n)⁻¹ * t = 1 := eq_one_of_two_pow_of_mem_OddCore hmem hk
    apply htz
    have : t = z ^ n := by
      have := congrArg (fun x => z ^ n * x) h1
      simpa using this
    rw [this]
    exact zpow_mem (mem_zpowers z) n
  have hconj_le : (OddCore z).map (MulAut.conj g).toMonoidHom ≤ OddCore z := by
    rintro _ ⟨a, ha, rfl⟩
    exact key a ha
  have hconj_eq : (OddCore z).map (MulAut.conj g).toMonoidHom = OddCore z := by
    apply Subgroup.eq_of_le_of_card_ge hconj_le
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hgA : g ∈ normalizer ((OddCore z : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact key x hx
    · intro hx
      have : g * x * g⁻¹ ∈ (OddCore z).map (MulAut.conj g).toMonoidHom := by rw [hconj_eq]; exact hx
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h1
      rw [← this]
      exact hy
  rcases (hmax.le_iff.1 (Cen_le_normalizer_OddCore z)) with hN | hN
  ·
    have hnorm : (OddCore z).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    haveI := hnorm
    rcases (hctx.std.kps.1).eq_bot_or_eq_top_of_normal (OddCore z) with hbot | htop
    · apply hne
      have : (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype = ⊥ := hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥(Cen z))
        (Cen z).subtype_injective).1 this
    · have hzA : z ∈ OddCore z := by rw [htop]; exact mem_top z
      have := coprime_orderOf_of_mem_OddCore hzA
      rw [hz2] at this
      exact absurd this (by norm_num)
  ·
    rw [hN] at hgA
    have := Subgroup.mem_centralizer_singleton_iff.1 hgA
    apply hgz
    rw [this]
    group

end OddCore

theorem stage2OddCoreM12_of_thm4 (hex : ExistsEvenFStar) (h4 : Thm4.Ch4Thm4) :
    Prod.Stage2OddCoreM12 := by
  intro G _ _ z S hctx
  obtain ⟨M, hM, hev⟩ := hex G z Kind.m12 S hctx
  obtain ⟨-, hb, hc⟩ := h4 G z Kind.m12 S hctx M hM hev
  have hMC : M = Cen z := by
    by_contra hne
    have hlt : Cen z < M := lt_of_le_of_ne hM.2 (fun h => hne h.symm)
    rcases (hb hlt).1 with h | ⟨ε, h⟩ <;> cases h
  subst hMC
  have hdir := hc rfl
  rw [← WC_eq_O22Of z] at hdir
  exact stage2OddCoreM12_of_max hctx hM.1 hdir

end CFSG.GH74.GLS.Stage2.Final
