module

public import CFSG.CharacterTheory.Semidihedral.Principal.SelfcentralizingFourGroupAlternatives
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusNormalizerSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

theorem le_of_odd_card_of_relIndex_eq_two {G : Type*} [Group G] [Finite G] {K H U : Subgroup G}
    (h2 : K.relIndex H = 2) (hUH : U ≤ H) (hU : Odd (Nat.card U)) : U ≤ K := by
  have hKn : (K.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two h2
  have hdvd1 : (K.subgroupOf H).relIndex (U.subgroupOf H) ∣ 2 :=
    h2 ▸ Subgroup.relIndex_dvd_index_of_normal _ _
  have hdvd2 : (K.subgroupOf H).relIndex (U.subgroupOf H) ∣ Nat.card U := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
    exact Subgroup.index_dvd_card _
  have h1 : (K.subgroupOf H).relIndex (U.subgroupOf H) = 1 := by
    have hodd : ¬ 2 ∣ (K.subgroupOf H).relIndex (U.subgroupOf H) := fun h =>
      (Nat.not_even_iff_odd.mpr hU) (even_iff_two_dvd.mpr (h.trans hdvd2))
    have hle := Nat.le_of_dvd (by norm_num) hdvd1
    interval_cases h : (K.subgroupOf H).relIndex (U.subgroupOf H) <;> simp_all
  intro u hu
  have := Subgroup.relIndex_eq_one.mp h1 (show (⟨u, hUH hu⟩ : H) ∈ U.subgroupOf H from hu)
  exact this

theorem three_torus_centralizer_quotient_of_data
    {G : Type} [Group G] [Finite G] {t s₀ : G}
    (V W : Subgroup G) (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (hV : IsKleinFour V) (ht2 : orderOf t = 2) (hW3 : Nat.card W = 3)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G))
    (hdisj : Disjoint V W) (hD : Nat.card (Subgroup.centralizer (V : Set G)) = 12)
    (hCK : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W : Set G) =
      Subgroup.centralizer (V : Set G))
    {d : G} (hdC : d ∈ Subgroup.centralizer ({t} : Set G))
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹)
    (hVsyl : ∃ P : Sylow 2 (Subgroup.centralizer (W : Set G)),
      (P : Subgroup (Subgroup.centralizer (W : Set G))).map
        (Subgroup.centralizer (W : Set G)).subtype = V)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hMH : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hKM : Nat.card (Subgroup.centralizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 36)
    (hfus : ∀ v ∈ V, v ≠ 1 → ∃ g ∈ Subgroup.normalizer (V : Set G), g * t * g⁻¹ = v) :
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let π : K →* K ⧸ CFSG.pPrimeCore 2 K := QuotientGroup.mk' (CFSG.pPrimeCore 2 K)
    (CFSG.pPrimeCore 2 K).map K.subtype = W ∧ (CFSG.pPrimeCore 2 H).map H.subtype = W ∧
      (((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 36 ∧ Nat.card H = 72) ∨
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 180 ∧ Nat.card H = 360)) ∧
        ¬ ((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 36 ∧ Nat.card H = 72) ∧
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 180 ∧ Nat.card H = 360))) ∧
      (∃ P : Sylow 2 (K ⧸ CFSG.pPrimeCore 2 K), (P : Subgroup _) = (V.subgroupOf K).map π) ∧
      (∀ tK : K, (tK : G) = t → (V.subgroupOf K).map π = Subgroup.centralizer {π tK}) ∧
      ∀ w ∈ W, w ≠ 1 → Nat.card (Subgroup.centralizer ({w} : Set G)) ≤ 180 := by
  intro H K π
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWD : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  obtain ⟨-, -, -, hDK, hchar⟩ := klein_centralizer_twelve_core V W hV hD hWD hW3
  have hVD : V ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_left
  have htV : t ∈ V := hVdef ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := hVdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have hVK : V ≤ K := hVD.trans hDK
  have hWK : W ≤ K := hWD.trans hDK
  have htK : t ∈ K := hVK htV
  have hKc : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k := fun k hk w hw =>
    (Subgroup.mem_centralizer_iff.mp hk w hw).symm
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hdinv : ∀ w ∈ W, d⁻¹ * w * d = w⁻¹ := by
    intro w hw
    have h := hdW w⁻¹ (W.inv_mem hw)
    rw [inv_inv] at h
    calc d⁻¹ * w * d = d⁻¹ * (d * w⁻¹ * d⁻¹) * d := by rw [h]
      _ = w⁻¹ := by group
  have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have htrans : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ K, k * t * k⁻¹ = v := by
    intro v hv hv1
    obtain ⟨g, hgM, hg⟩ := hfus v hv hv1
    by_cases hgK : g ∈ K
    · exact ⟨g, hgK, hg⟩
    · refine ⟨g * d⁻¹, ?_, ?_⟩
      · have hgi := hinv g (hMH hgM) hgK
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 : (g * d⁻¹) * w * (g * d⁻¹)⁻¹ = w := by
          calc (g * d⁻¹) * w * (g * d⁻¹)⁻¹ = g * (d⁻¹ * w * d) * g⁻¹ := by group
            _ = g * w⁻¹ * g⁻¹ := by rw [hdinv w hw]
            _ = (g * w * g⁻¹)⁻¹ := by group
            _ = w := by rw [hgi w hw, inv_inv]
        calc w * (g * d⁻¹) = (g * d⁻¹) * w * (g * d⁻¹)⁻¹ * (g * d⁻¹) := by rw [h1]
          _ = (g * d⁻¹) * w := by group
      · have hdt' : d⁻¹ * t * d = t := by
          rw [mul_assoc, ← hdt, ← mul_assoc, inv_mul_cancel, one_mul]
        calc g * d⁻¹ * t * (g * d⁻¹)⁻¹ = g * (d⁻¹ * t * d) * g⁻¹ := by group
          _ = g * t * g⁻¹ := by rw [hdt']
          _ = v := hg
  set R' := CFSG.pPrimeCore 2 K with hR'def
  set R := R'.map K.subtype with hRdef
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRcard : Nat.card R = Nat.card R' := Subgroup.card_map_of_injective K.subtype_injective
  have hRodd : Odd (Nat.card R) :=
    hRcard ▸ Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hRnorm : ∀ k ∈ K, ∀ x ∈ R, k * x * k⁻¹ ∈ R := by
    intro k hk x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, (inferInstance : R'.Normal).conj_mem y hy _, rfl⟩
  have hWR : W ≤ R := by
    have hWn : (W.subgroupOf K).Normal := by
      refine ⟨fun x hx k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have h : (k : G) * x * (k : G)⁻¹ = x := by
        rw [hKc k k.2 x hx, mul_assoc, mul_inv_cancel, mul_one]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, h] using hx
    have hcardW : Nat.card (W.subgroupOf K) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv, hW3]
    have hle : W.subgroupOf K ≤ R' := le_sSup ⟨hWn, by rw [hcardW]; norm_num⟩
    intro w hw
    exact ⟨⟨w, hWK hw⟩, hle hw, rfl⟩
  have hRt : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ W := by
    intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxD : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [← hCK]
      exact Subgroup.mem_inf.mpr ⟨hxC, hRK hxR⟩
    apply hchar x hxD
    have h12 : orderOf x ∣ 12 := hD ▸ Subgroup.orderOf_dvd_natCard _ hxD
    have hodd : Odd (orderOf x) := Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hxR)
    have h3 : orderOf x ∣ 3 := by
      have hle := Nat.le_of_dvd (by norm_num) h12
      have hpos := orderOf_pos x
      interval_cases h : orderOf x <;>
        first | (exfalso; revert hodd; decide) | (exfalso; revert h12; decide) | norm_num
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have hRv : ∀ v ∈ V, v ≠ 1 → R ⊓ Subgroup.centralizer ({v} : Set G) ≤ W := by
    intro v hv hv1 x hx
    obtain ⟨k, hkK, hk⟩ := htrans v hv hv1
    obtain ⟨hxR, hxv⟩ := Subgroup.mem_inf.mp hx
    have hy : k⁻¹ * x * k ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := hRnorm k⁻¹ (K.inv_mem hkK) x hxR
        rwa [inv_inv] at h
      · rw [Subgroup.mem_centralizer_singleton_iff] at hxv ⊢
        rw [← hk] at hxv
        calc k⁻¹ * x * k * t = k⁻¹ * (x * (k * t * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * t * k⁻¹) * x) * k := by rw [hxv]
          _ = t * (k⁻¹ * x * k) := by group
    have hyW := hRt hy
    have hx' : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [hx', hKc k hkK _ hyW, mul_assoc, mul_inv_cancel, mul_one]
    exact hyW
  have hVN : V ≤ Subgroup.normalizer (R : Set G) := fun v hv => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hRnorm v (hVK hv) x, fun h => ?_⟩
    have h' := hRnorm v⁻¹ (K.inv_mem (hVK hv)) _ h
    simpa [mul_assoc] using h'
  let φ : V →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hVN)
  let : MulDistribMulAction V R := MulDistribMulAction.compHom R φ
  have : CFSG.IsElementaryAbelian 2 V :=
    { toIsMulCommutative := ⟨⟨mul_comm_of_exponent_two hV.exponent_two⟩⟩
      exponent_dvd_p := by rw [hV.exponent_two] }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := V) (H := R)
    (by rw [hV.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h))
  have hRW : R ≤ W := by
    intro x hx
    have hmem : (⟨x, hx⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
    rw [← hgen] at hmem
    have hle : (⨆ (a : V) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) R) ≤
        W.comap R.subtype := by
      refine iSup₂_le fun a ha => ?_
      intro y hy
      rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
      have hy' : (a : G) * (y : G) * (a : G)⁻¹ = y := by
        have h := congrArg Subtype.val hy
        exact h
      apply hRv a a.2 (fun h => ha (Subtype.ext h))
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * (y : G) * (a : G)⁻¹ * a := by rw [hy']
        _ = a * y := by group
    exact hle hmem
  have hReq : R = W := le_antisymm hRW hWR
  have hR'card : Nat.card R' = 3 := by rw [← hRcard, hReq, hW3]
  have hXK : Nat.card K = Nat.card (K ⧸ R') * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R', hR'card]
  have hWR' : ∀ w : K, (w : G) ∈ W → w ∈ R' := by
    intro w hw
    rw [← hReq] at hw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  have hR'W : ∀ w : K, w ∈ R' → (w : G) ∈ W := fun w hw => hReq ▸ ⟨w, hw, rfl⟩
  have hinj : Function.Injective (π.comp (V.subgroupOf K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hxW := hR'W _ hx
    have hxV : ((x : K) : G) ∈ V := x.2
    have h1 : ((x : K) : G) = 1 := Subgroup.disjoint_def.mp hdisj hxV hxW
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
  have hVbeq : (V.subgroupOf K).map π = (π.comp (V.subgroupOf K).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eV : V ≃* (V.subgroupOf K).map π :=
    ((Subgroup.subgroupOfEquivOfLe hVK).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr hVbeq.symm)
  have hVbcard : Nat.card ((V.subgroupOf K).map π) = 4 := by
    rw [← Nat.card_congr eV.toEquiv, hV.card_four]
  have hVbk : IsKleinFour ((V.subgroupOf K).map π) :=
    ⟨hVbcard, (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two⟩
  obtain ⟨P, hP⟩ := hVsyl
  have hPcard : Nat.card (P : Subgroup K) = 4 := by
    rw [← hV.card_four, ← hP, Subgroup.card_map_of_injective K.subtype_injective]
  have hPidx : 4 * (P : Subgroup K).index = Nat.card K := by
    rw [← hPcard]
    exact Subgroup.card_mul_index (P : Subgroup K)
  have hPodd := P.not_dvd_index
  have hVbidx : 4 * ((V.subgroupOf K).map π).index = Nat.card (K ⧸ R') := by
    rw [← hVbcard]
    exact Subgroup.card_mul_index ((V.subgroupOf K).map π)
  have hidx : (P : Subgroup K).index = 3 * ((V.subgroupOf K).map π).index := by
    have h : 4 * (P : Subgroup K).index = 4 * (3 * ((V.subgroupOf K).map π).index) := by
      rw [hPidx, hXK, ← hVbidx]
      ring
    omega
  have hVbodd : ¬ 2 ∣ ((V.subgroupOf K).map π).index := fun h =>
    hPodd (hidx ▸ Dvd.dvd.mul_left h 3)
  have hVbp : IsPGroup 2 ((V.subgroupOf K).map π) :=
    IsPGroup.of_card (n := 2) (by rw [hVbcard]; norm_num)
  let VbS : Sylow 2 (K ⧸ R') := hVbp.toSylow hVbodd
  have hVbS : (VbS : Subgroup (K ⧸ R')) = (V.subgroupOf K).map π := rfl
  let tK : K := ⟨t, htK⟩
  have htb1 : π tK ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have htW := hR'W tK h
    have := Subgroup.orderOf_dvd_natCard W htW
    rw [ht2, hW3] at this
    norm_num at this
  have htbV : π tK ∈ (V.subgroupOf K).map π := ⟨tK, htV, rfl⟩
  have hDmap : ((Subgroup.centralizer (V : Set G)).subgroupOf K).map π =
      (V.subgroupOf K).map π := by
    rw [← hsup, Subgroup.subgroupOf_sup hVK hWK, Subgroup.map_sup]
    have hWb : (W.subgroupOf K).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro w hw
      exact hWR' w hw
    rw [hWb, sup_bot_eq]
  have hCX : Subgroup.centralizer {π tK} = (V.subgroupOf K).map π := by
    apply le_antisymm
    · intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R' q
      rw [Subgroup.mem_centralizer_singleton_iff] at hq
      have hA : IsPGroup 2 (Subgroup.zpowers tK) := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one])
      let α : Subgroup.zpowers tK →* MulAut K := MulAut.conj.comp (Subgroup.zpowers tK).subtype
      have hcop : ¬ 2 ∣ Nat.card R' := by rw [hR'card]; norm_num
      obtain ⟨c, hc, hfix⟩ := (coprime_invariant_coset_fixed 2 hA α R' hcop g).2 (by
        intro a x hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
        have hcomm : Commute (π g) (π tK) := hq
        have hxg : π x = π g := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
          exact hx
        rw [← QuotientGroup.eq_one_iff]
        change π (g⁻¹ * ((a : K) * x * (a : K)⁻¹)) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxg, ← hk, map_zpow,
          ← (hcomm.zpow_right k).eq]
        group)
      have hct := hfix ⟨tK, Subgroup.mem_zpowers tK⟩
      change tK * c * tK⁻¹ = c at hct
      have hcD : (c : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [← hCK]
        refine Subgroup.mem_inf.mpr ⟨?_, c.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg (fun x : K => (x : G)) hct
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
        calc (c : G) * t = t * (c : G) * t⁻¹ * t := by rw [h]
          _ = t * c := by group
      have hgc : π g = π c := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact hc
      rw [hgc, ← hDmap]
      exact ⟨c, hcD, rfl⟩
    · intro q hq
      obtain ⟨v, hv, rfl⟩ := hq
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hvV : (v : G) ∈ V := hv
      have h := mul_comm_of_exponent_two hV.exponent_two (⟨v, hvV⟩ : V) ⟨t, htV⟩
      have h' : (v : G) * t = t * (v : G) := congrArg Subtype.val h
      simpa only [Subgroup.coe_mul] using h'
  have h3 := odd_core_free_selfcentralizing_four_group_involution_centralizer_three_alternatives
    (X := K ⧸ R') (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) VbS hVbk (π tK) htbV htb1 hCX
  obtain ⟨halt, -, -, -⟩ := h3
  have hK36 : 36 ≤ Nat.card K := hKM ▸ Subgroup.card_le_of_le inf_le_left
  have hHK : Nat.card H = 2 * Nat.card K := by
    have h := Subgroup.card_mul_index (K.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH').toEquiv] at h
    have hri : (K.subgroupOf H).index = 2 := hKH
    rw [hri] at h
    omega
  have hcases : (Nonempty ((K ⧸ R') ≃* alternatingGroup (Fin 4)) ∧ Nat.card K = 36 ∧
        Nat.card H = 72) ∨
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ R') .PSL 2 5 1 ∧
        Nat.card K = 180 ∧ Nat.card H = 360) := by
    rcases halt with h1 | h2 | h3
    · exfalso
      have h1' : (VbS : Subgroup (K ⧸ R')) = ⊤ := h1
      have hX4 : Nat.card (K ⧸ R') = 4 := by rw [← hVbcard, ← hVbS, h1', Subgroup.card_top]
      omega
    · obtain ⟨e⟩ := h2
      have hX12 : Nat.card (K ⧸ R') = 12 := by
        rw [Nat.card_congr e.toEquiv, alternatingGroup.card_of_card_eq_four (by simp)]
      exact Or.inl ⟨⟨e⟩, by omega, by omega⟩
    · exact Or.inr ⟨h3.2, by omega, by omega⟩
  have hH2 : (CFSG.pPrimeCore 2 H).map H.subtype = W := by
    have hUodd : Odd (Nat.card ((CFSG.pPrimeCore 2 H).map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    have hUH : (CFSG.pPrimeCore 2 H).map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hUK : (CFSG.pPrimeCore 2 H).map H.subtype ≤ K :=
      le_of_odd_card_of_relIndex_eq_two hKH hUH hUodd
    apply le_antisymm
    · have hUn : (((CFSG.pPrimeCore 2 H).map H.subtype).subgroupOf K).Normal := by
        refine ⟨fun x hx k => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        refine ⟨⟨k, hKH' k.2⟩ * y * ⟨k, hKH' k.2⟩⁻¹,
          (inferInstance : (CFSG.pPrimeCore 2 H).Normal).conj_mem y hy _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
        rw [hyx]
      have hUcard : Nat.card (((CFSG.pPrimeCore 2 H).map H.subtype).subgroupOf K) =
          Nat.card ((CFSG.pPrimeCore 2 H).map H.subtype) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
      have hle : ((CFSG.pPrimeCore 2 H).map H.subtype).subgroupOf K ≤ R' :=
        le_sSup ⟨hUn, by rw [hUcard]; exact Nat.coprime_two_left.mpr hUodd⟩
      intro u hu
      exact hR'W ⟨u, hUK hu⟩ (hle hu)
    · have hWH : W ≤ H := Subgroup.le_normalizer
      have hWn : (W.subgroupOf H).Normal := Subgroup.normal_in_normalizer
      have hcardW : Nat.card (W.subgroupOf H) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv, hW3]
      have hle : W.subgroupOf H ≤ CFSG.pPrimeCore 2 H :=
        le_sSup ⟨hWn, by rw [hcardW]; norm_num⟩
      intro w hw
      exact ⟨⟨w, hWH hw⟩, hle hw, rfl⟩
  have hbound : ∀ w ∈ W, w ≠ 1 → Nat.card (Subgroup.centralizer ({w} : Set G)) ≤ 180 := by
    intro w hw hw1
    have hw3 : orderOf w = 3 := orderOf_eq_prime_of_mem_of_card_eq hW3 hw hw1
    have hzw : Subgroup.zpowers w = W := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
      rw [hW3, Nat.card_zpowers, hw3]
    have hCw : Subgroup.centralizer ({w} : Set G) = K := by
      change _ = Subgroup.centralizer (W : Set G)
      rw [← hzw, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hCw]
    rcases hcases with h | h
    · rw [h.2.1]; norm_num
    · rw [h.2.1]
  refine ⟨hReq, hH2, ⟨hcases, fun h => by have := h.1.2.1; have := h.2.2.1; omega⟩,
    ⟨VbS, hVbS⟩, fun tK' htK' => ?_, hbound⟩
  have : tK' = tK := Subtype.ext htK'
  rw [this, hCX]

end CFSG.Semidihedral.Principal
