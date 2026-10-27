module

public import CFSG.LocalAnalysis.ABGTheoremB.Facts
import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
import CFSG.GroupTheory.ABGDGroups.LinearOddCyclic
public import Certificates.Certificate7
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PGL2 pGammaL2PSLRange pGammaL2PGLRange
  mem_pGammaL2PSLRange_iff)
open CFSG.ABGDGroups (IsLinearDecomposition linearCore)
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

private theorem ii34ab_le_oddCoreIn_of_subgroupOf {H Y : Subgroup G} (hYH : Y ≤ H)
    (h : Y.subgroupOf H ≤ CFSG.oddCore H) : Y ≤ oddCoreIn H :=
  fun y hy => ⟨⟨y, hYH hy⟩, h hy, rfl⟩

private theorem ii34ab_mem_normalizer_subgroupOf {H B : Subgroup G} {g : H}
    (h : (g : G) ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((B.subgroupOf H : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp h b

private theorem ii34ab_subgroupOf_le_normalizer {H A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup H) : Set H) :=
  fun _ ha => ii34ab_mem_normalizer_subgroupOf (h ha)

private theorem ii34ab_odd_card_subgroupOf {H Y : Subgroup G} (hYH : Y ≤ H)
    (hY : Odd (Nat.card Y)) : Odd (Nat.card (Y.subgroupOf H)) := by
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]

private theorem ii34ab_isKleinFour_map {H T : Subgroup G} [Finite G]
    (hT : IsKleinFour (T.subgroupOf H)) :
    IsKleinFour ((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H))) := by
  refine CFSG.ABGDGroups.isKleinFour_map_of_inf_ker_eq_bot _ hT ?_
  rw [QuotientGroup.ker_mk']
  apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
  rw [hT.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact (Nat.coprime_two_left.mpr (odd_card_oddCore H)).pow_left 2

private theorem ii34ab_mem_of_mul_self_mem {K : Subgroup G} {y : G} (hy : Odd (orderOf y))
    (h : y * y ∈ K) : y ∈ K := by
  obtain ⟨m, hm⟩ := hy
  have : y = (y * y) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [this]
  exact K.pow_mem h _

private theorem ii34ab_commutative_of_card_dvd_sq {r : ℕ} (hr : r.Prime) {Y : Subgroup G}
    (hY : Nat.card Y ∣ r ^ 2) : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hr).mp hY
  have hcomm : ∀ a b : Y, a * b = b * a := by
    interval_cases i
    · rw [pow_zero] at hcard
      intro a b
      have : Subsingleton Y := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact Subsingleton.elim _ _
    · have : IsCyclic Y := isCyclic_of_prime_card (by rw [hcard, pow_one])
      exact (IsCyclic.isMulCommutative (α := Y)).is_comm.comm
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm
  intro a ha b hb
  exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem ii34ab_mem_centralizer_of_isCyclic {Y : Subgroup G} (hY : IsCyclic Y) {g v : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hv : v ∈ Subgroup.normalizer (Y : Set G))
    (hgv : g * v * g⁻¹ = v⁻¹) (hvo : Odd (orderOf v)) :
    v ∈ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨⟨y₀, hy₀⟩, hgen⟩ := hY.exists_generator
  have hpow : ∀ y ∈ Y, ∃ j : ℤ, y = y₀ ^ j := by
    intro y hy
    obtain ⟨j, hj⟩ := hgen ⟨y, hy⟩
    refine ⟨j, ?_⟩
    have h1 := congrArg Subtype.val hj
    simpa using h1.symm
  obtain ⟨a, ha⟩ := hpow _ ((Subgroup.mem_normalizer_iff.mp hv y₀).mp hy₀)
  have hact : ∀ y ∈ Y, v * y * v⁻¹ = y ^ a := by
    intro y hy
    obtain ⟨j, rfl⟩ := hpow y hy
    rw [← conj_zpow, ha, ← zpow_mul, ← zpow_mul, mul_comm]
  have hsq : ∀ y ∈ Y, (v * v) * y * (v * v)⁻¹ = y := by
    intro y hy
    have hzY : g⁻¹ * y * g ∈ Y := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using h1
    have h1 : v⁻¹ * y * v = v * y * v⁻¹ := by
      calc v⁻¹ * y * v = (g * v * g⁻¹) * y * (g * v * g⁻¹)⁻¹ := by rw [hgv, inv_inv]
        _ = g * (v * (g⁻¹ * y * g) * v⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * y * g) ^ a * g⁻¹ := by rw [hact _ hzY]
        _ = (g * (g⁻¹ * y * g) * g⁻¹) ^ a := by rw [conj_zpow]
        _ = y ^ a := by group
        _ = v * y * v⁻¹ := (hact y hy).symm
    calc (v * v) * y * (v * v)⁻¹ = v * (v * y * v⁻¹) * v⁻¹ := by group
      _ = v * (v⁻¹ * y * v) * v⁻¹ := by rw [h1]
      _ = y := by group
  have hc : ∀ n : ℕ, ∀ y ∈ Y, (v * v) ^ n * y * ((v * v) ^ n)⁻¹ = y := by
    intro n
    induction n with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      calc (v * v) ^ (n + 1) * y * ((v * v) ^ (n + 1))⁻¹ =
          (v * v) ^ n * ((v * v) * y * (v * v)⁻¹) * ((v * v) ^ n)⁻¹ := by
            rw [pow_succ]; group
        _ = y := by rw [hsq y hy, ih y hy]
  obtain ⟨m, hm⟩ := hvo
  have hv' : v = (v * v) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf v + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hc (m + 1) y hy
  rw [← hv'] at h1
  calc y * v = v * y * v⁻¹ * v := by rw [h1]
    _ = v * y := by group

end Elementary

section Quotient

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
private theorem ii34ab_nonempty_comap_inl_mulEquiv {F : Type} [Field F]
    {A : Subgroup (PGammaL2 F)} (hA : A ≤ pGammaL2PGLRange F) :
    Nonempty (A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) ≃* A) :=
  ⟨((A.comap SemidirectProduct.inl).equivMapOfInjective _ SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hA))⟩

private theorem ii34ab_isCyclic_of_le_linearCore {F : Type} [Field F] [Finite F]
    {ι : K →* PGammaL2 F} {L E : Subgroup K} {S : Sylow 2 K} (hd : IsLinearDecomposition ι L E S)
    {T X : Subgroup K} (hT : IsKleinFour T) (hXT : T ≤ Subgroup.normalizer (X : Set K))
    (hX : Odd (Nat.card X)) (hXL : X ≤ linearCore ι) : IsCyclic X := by
  have hF := hd.isOddPrimePower_card
  have hTL : T ≤ L := by
    obtain ⟨P, hTP⟩ := (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hT).exists_le_sylow
    exact hTP.trans (hd.sylow_le P)
  have hXL₀ : X.map ι ≤ pGammaL2PSLRange F := (Subgroup.map_mono hXL).trans hd.map_linearCore.le
  have hTPGL : T.map ι ≤ pGammaL2PGLRange F := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · rw [ht1, map_one]
      exact Subgroup.one_mem _
    have h2 : orderOf t = 2 := by
      have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T)
      rw [hT.exponent_two] at h
      exact orderOf_eq_prime (by simpa using congrArg Subtype.val h) ht1
    exact hd.isStandardLayer.mem_pGLRange_of_orderOf_eq_two hF ⟨t, hTL ht, rfl⟩
      (by rw [orderOf_injective ι hd.injective, h2])
  set X₁ := (X.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) with hX₁
  set T₁ := (T.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) with hT₁
  have hXPGL : X.map ι ≤ pGammaL2PGLRange F :=
    hXL₀.trans CFSG.ABGDGroups.pGammaL2PSLRange_le_pGLRange
  obtain ⟨eX⟩ := ii34ab_nonempty_comap_inl_mulEquiv hXPGL
  obtain ⟨eT⟩ := ii34ab_nonempty_comap_inl_mulEquiv hTPGL
  let eX' : X ≃* X.map ι := X.equivMapOfInjective ι hd.injective
  let eT' : T ≃* T.map ι := T.equivMapOfInjective ι hd.injective
  have hX₁J : X₁ ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F _).mp (hXL₀ hx)
    exact ⟨y, SemidirectProduct.inl_injective hy⟩
  have hX₁odd : Odd (Nat.card X₁) := by
    rwa [Nat.card_congr eX.toEquiv, ← Nat.card_congr eX'.toEquiv]
  have hT₁four : IsKleinFour T₁ := by
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr eT.toEquiv, ← Nat.card_congr eT'.toEquiv]
      exact hT.card_four
    · rw [Monoid.exponent_eq_of_mulEquiv eT, ← Monoid.exponent_eq_of_mulEquiv eT']
      exact hT.exponent_two
  have hT₁X : T₁ ≤ Subgroup.normalizer (X₁ : Set (PGL2 F)) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    intro k hk
    have hN := Subgroup.le_normalizer_map ι
      (Subgroup.map_mono hXT (show SemidirectProduct.inl t ∈ T.map ι from ht))
    change SemidirectProduct.inl (t * k * t⁻¹) ∈ X.map ι
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp hk
  have hcyc := CFSG.ABGDGroups.pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer hF hX₁J hX₁odd
    hT₁four hT₁X
  exact (eX'.trans eX.symm).isCyclic.mpr hcyc

private theorem ii34ab_isCyclic_of_le_commutator (hK : IsDGroup K) (hO : CFSG.oddCore K = ⊥)
    {T Y : Subgroup K} (hT : IsKleinFour T) (hTY : T ≤ Subgroup.normalizer (Y : Set K))
    (hY : Odd (Nat.card Y)) (hYc : Y ≤ commutator K) : IsCyclic Y := by
  by_cases hW : ∃ n, HasWreathedSylow K n
  · obtain ⟨n, hn⟩ := hW
    rcases hK with ⟨hD, -⟩ | ⟨K', hK'⟩
    · exact (not_hasWreathedSylow_and_dihedral hn hD).elim
    · have hle := CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK' hn hT hY hTY
      rw [hO, le_bot_iff] at hle
      rw [hle]
      infer_instance
  · rcases CFSG.ABGDGroups.aSeven_or_linearDecomposition hK hO hW with he | hlin
    · obtain ⟨e⟩ := he
      exact CFSG.ABGDGroups.aSeven_isCyclic_of_odd_of_kleinFour e hT hY hTY
    · obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
      obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
      exact ii34ab_isCyclic_of_le_linearCore hd hT hTY hY (hYc.trans hd.commutator_le_linearCore)

private theorem ii34ab_commutative_of_linear {F : Type} [Field F] [Finite F]
    {ι : K →* PGammaL2 F} {L E : Subgroup K} {S : Sylow 2 K} (hd : IsLinearDecomposition ι L E S)
    {r : ℕ} (hr : r.Prime) {T Y : Subgroup K} (hT : IsKleinFour T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set K)) (hY : Odd (Nat.card Y))
    (hexp : ∀ y ∈ Y, y ^ r = 1) : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  have hF := hd.isOddPrimePower_card
  set ρ : K →* (F ≃+* F) := SemidirectProduct.rightHom.comp ι with hρ
  set Y₁ := Y ⊓ ρ.ker with hY₁
  have hY₁L₀ : Y₁ ≤ linearCore ι := by
    intro y hy
    have hright : (ι y).right = 1 := by
      have h1 : ρ y = 1 := hy.2
      rwa [hρ, MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right] at h1
    have hsq : ι y ^ 2 ∈ pGammaL2PSLRange F :=
      CFSG.ABGDGroups.sq_mem_pGammaL2PSLRange hF (by rw [hright, one_pow])
    have hodd : Odd (orderOf (ι y)) := by
      rw [orderOf_injective ι hd.injective]
      exact hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy.1)
    change ι y ∈ pGammaL2PSLRange F
    exact ii34ab_mem_of_mul_self_mem hodd (by rwa [← pow_two])
  have hTk : T ≤ Subgroup.normalizer ((ρ.ker : Subgroup K) : Set K) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hTY₁ : T ≤ Subgroup.normalizer (Y₁ : Set K) :=
    (le_inf hTY hTk).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hY₁odd : Odd (Nat.card Y₁) := hY.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hY₁cyc : IsCyclic Y₁ := ii34ab_isCyclic_of_le_linearCore hd hT hTY₁ hY₁odd hY₁L₀
  have hY₁card : Nat.card Y₁ ∣ r := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (hexp y y.2.1)
  set φ : Y →* (F ≃+* F) := ρ.comp Y.subtype with hφ
  have hker : φ.ker = Y₁.subgroupOf Y := by
    rw [hY₁, Subgroup.inf_subgroupOf_left, hφ, ← MonoidHom.comap_ker]
    rfl
  have hrange : Nat.card φ.range ∣ r := by
    have : IsCyclic (F ≃+* F) := CFSG.ABGDGroups.isCyclic_ringEquiv F
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun z => ?_
    obtain ⟨y, hy⟩ := z.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hy, ← map_pow, show y ^ r = 1 from Subtype.ext (hexp y y.2),
      map_one]
    rfl
  have hYcard : Nat.card Y ∣ r ^ 2 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y₁ ≤ Y)).toEquiv] at h1
    rw [← h1, pow_two]
    exact Nat.mul_dvd_mul hY₁card hrange
  exact ii34ab_commutative_of_card_dvd_sq hr hYcard

private theorem ii34ab_commutative_of_exponent (hK : IsDGroup K) (hO : CFSG.oddCore K = ⊥)
    {r : ℕ} (hr : r.Prime) {T Y : Subgroup K} (hT : IsKleinFour T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set K)) (hY : Odd (Nat.card Y))
    (hexp : ∀ y ∈ Y, y ^ r = 1) : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  by_cases hW : ∃ n, HasWreathedSylow K n
  · obtain ⟨n, hn⟩ := hW
    rcases hK with ⟨hD, -⟩ | ⟨K', hK'⟩
    · exact (not_hasWreathedSylow_and_dihedral hn hD).elim
    · have hle := CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK' hn hT hY hTY
      rw [hO, le_bot_iff] at hle
      intro a ha b hb
      rw [hle, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  · rcases CFSG.ABGDGroups.aSeven_or_linearDecomposition hK hO hW with he | hlin
    · obtain ⟨e⟩ := he
      have hcyc := CFSG.ABGDGroups.aSeven_isCyclic_of_odd_of_kleinFour e hT hY hTY
      intro a ha b hb
      exact congrArg Subtype.val
        ((IsCyclic.isMulCommutative (α := Y)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
      obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
      exact ii34ab_commutative_of_linear hd hr hT hTY hY hexp

end Quotient

namespace Setting

variable {G : Type} [Group G] [Finite G] (σ : Setting G)

theorem dGroup_exponent_commutator_le (_hσ : σ.IsValid) (_hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → IsPGroup r W → (∀ w ∈ W, w ^ r = 1) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ⁅W, W⁆ ≤ oddCoreIn H := by
  intro H hTH hDW W hWHN hW hexp hTW
  obtain ⟨hHD, hT, -⟩ := hDW
  have : Fact r.Prime := ⟨hr⟩
  have hWH : W ≤ H := hWHN.trans inf_le_left
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have hWodd : Odd (Nat.card W) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
    rw [hk]
    exact (hr.eq_two_or_odd'.resolve_left hr2).pow
  have hWbar : Odd (Nat.card ((W.subgroupOf H).map π)) :=
    (ii34ab_odd_card_subgroupOf hWH hWodd).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hTWbar : (σ.T.subgroupOf H).map π ≤
      Subgroup.normalizer (((W.subgroupOf H).map π : Subgroup _) : Set _) :=
    (Subgroup.map_mono (ii34ab_subgroupOf_le_normalizer hTW)).trans (Subgroup.le_normalizer_map π)
  have hexpbar : ∀ y ∈ (W.subgroupOf H).map π, y ^ r = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_pow, show w ^ r = 1 from Subtype.ext (hexp _ hw), map_one]
  have hcomm := ii34ab_commutative_of_exponent (CFSG.ABGDGroups.isDGroup_quotient_oddCore hHD)
    (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H) hr (ii34ab_isKleinFour_map hT)
    hTWbar hWbar hexpbar
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haH := hWH ha
  have hbH := hWH hb
  have h1 := hcomm (π ⟨a, haH⟩) ⟨⟨a, haH⟩, ha, rfl⟩ (π ⟨b, hbH⟩) ⟨⟨b, hbH⟩, hb, rfl⟩
  have hmem : ⁅(⟨a, haH⟩ : H), ⟨b, hbH⟩⁆ ∈ CFSG.oddCore H := by
    rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker, map_commutatorElement,
      ← hπ, commutatorElement_def, h1]
    group
  exact ⟨_, hmem, by simp [commutatorElement_def]⟩

theorem dGroup_le_oddCore_of_inverted (_hσ : σ.IsValid) (_hII : σ.ChapterIIFacts) :
    ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → Odd (Nat.card W) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ∀ v ∈ H ⊓ σ.N, Odd (orderOf v) →
          σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ → v ∈ Subgroup.normalizer (W : Set G) →
            W ≤ ⁅W, Subgroup.zpowers v⁆ → W ≤ oddCoreIn H := by
  intro H hTH hDW W hWHN hW hTW v hvHN hvo hinv hvW hWv
  obtain ⟨hHD, hT, -⟩ := hDW
  have hWH : W ≤ H := hWHN.trans inf_le_left
  have hvH : v ∈ H := hvHN.1
  have hx₂H : σ.x₂ ∈ H := hTH σ.x₂_mem_T
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  set v' : H := ⟨v, hvH⟩ with hv'
  set g' : H := ⟨σ.x₂, hx₂H⟩ with hg'
  have hW'v : W.subgroupOf H ≤ ⁅W.subgroupOf H, Subgroup.zpowers v'⁆ := by
    have h1 : (⁅W.subgroupOf H, Subgroup.zpowers v'⁆).map H.subtype = ⁅W, Subgroup.zpowers v⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hWH, MonoidHom.map_zpowers]
      rfl
    intro w hw
    have h2 : (w : G) ∈ (⁅W.subgroupOf H, Subgroup.zpowers v'⁆).map H.subtype := h1 ▸ hWv hw
    obtain ⟨y, hy, hyw⟩ := h2
    rwa [show w = y from Subtype.ext hyw.symm]
  set Wbar := (W.subgroupOf H).map π with hWbar
  set vbar := π v' with hvbar
  have hWbar_le : Wbar ≤ ⁅Wbar, Subgroup.zpowers vbar⁆ := by
    calc Wbar ≤ (⁅W.subgroupOf H, Subgroup.zpowers v'⁆).map π := Subgroup.map_mono hW'v
      _ = ⁅Wbar, Subgroup.zpowers vbar⁆ := by rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  have hWbar_comm : Wbar ≤ commutator (H ⧸ CFSG.oddCore H) := by
    refine hWbar_le.trans ?_
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hTWbar : (σ.T.subgroupOf H).map π ≤ Subgroup.normalizer (Wbar : Set _) :=
    (Subgroup.map_mono (ii34ab_subgroupOf_le_normalizer hTW)).trans (Subgroup.le_normalizer_map π)
  have hWbarodd : Odd (Nat.card Wbar) :=
    (ii34ab_odd_card_subgroupOf hWH hW).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hcyc := ii34ab_isCyclic_of_le_commutator (CFSG.ABGDGroups.isDGroup_quotient_oddCore hHD)
    (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H) (ii34ab_isKleinFour_map hT) hTWbar
    hWbarodd hWbar_comm
  have hgN : π g' ∈ Subgroup.normalizer (Wbar : Set _) :=
    hTWbar ⟨g', show (g' : G) ∈ σ.T from σ.x₂_mem_T, rfl⟩
  have hvN : vbar ∈ Subgroup.normalizer (Wbar : Set _) :=
    Subgroup.le_normalizer_map π ⟨v', ii34ab_mem_normalizer_subgroupOf hvW, rfl⟩
  have hgv : π g' * vbar * (π g')⁻¹ = vbar⁻¹ := by
    rw [hvbar, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hinv
  have hvbaro : Odd (orderOf vbar) :=
    hvo.of_dvd_nat ((orderOf_map_dvd π v').trans (by rw [hv', Subgroup.orderOf_mk]))
  have hcent := ii34ab_mem_centralizer_of_isCyclic hcyc hgN hvN hgv hvbaro
  have hbot : ⁅Wbar, Subgroup.zpowers vbar⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
      Subgroup.zpowers_le]
    exact hcent
  have hWbot : Wbar = ⊥ := le_bot_iff.mp (hbot ▸ hWbar_le)
  apply ii34ab_le_oddCoreIn_of_subgroupOf hWH
  rwa [hWbar, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hWbot

end Setting

end CFSG.ABGTheoremB
