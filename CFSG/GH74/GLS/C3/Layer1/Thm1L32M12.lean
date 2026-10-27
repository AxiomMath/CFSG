module

public import CFSG.GH74.KGroups.TwoM12Fixed
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Stable

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.Thm1P31c
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

section M12Inner

theorem inner_sq_eq_t
    {L : Type} [Group L] [Finite L] (h : CFSG.GH74.E2.Shape2M12 L) (σ : MulAut L) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {P : Subgroup L} (hP : ⁅P, P⁆ = P) (hP2 : 2 < Nat.card ↥P)
    (hPσ : ∀ x ∈ P, σ x = x) {t₁ : L} (ht₁2 : orderOf t₁ = 2) (ht₁c : t₁ ∈ center L) (u : L)
    (hu : ∀ x : L, σ x = u * x * u⁻¹) : u * u = t₁ := by
  obtain ⟨t, π, hc⟩ := CFSG.GH74.KGroups.TwoM12.exists_isCover h
  have hq : CFSG.Assembly.IsQuasisimple L := ⟨Group.isPerfect_def.1 h.1.1, h.1.2.1⟩
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 hc.orderOf_t).2
  have htt₁ : t₁ = t := by
    have hmem : t₁ ∈ zpowers t := hc.center_eq ▸ ht₁c
    rcases eq_one_or_eq_of_mem_zpowers hc.orderOf_t hmem with h1 | h1
    · exfalso
      rw [h1, orderOf_one] at ht₁2
      omega
    · exact h1
  subst htt₁
  have huu : u * u ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : σ (σ g) = g := by
      have := congrArg (fun f : MulAut L => f g) hσ2
      simpa using this
    rw [hu, hu] at h1
    have h2 : u * (u * g * u⁻¹) * u⁻¹ = g := h1
    calc g * (u * u) = (u * (u * g * u⁻¹) * u⁻¹) * (u * u) := by rw [h2]
      _ = (u * u) * g := by group
  have hPu : ∀ x ∈ P, x * u = u * x := by
    intro x hx
    have h1 := hPσ x hx
    rw [hu] at h1
    calc x * u = (u * x * u⁻¹) * u := by rw [h1]
      _ = u * x := by group
  rcases eq_one_or_eq_of_mem_zpowers hc.orderOf_t (hc.center_eq ▸ huu) with h1 | h1
  ·
    exfalso
    have hπuu : π u * π u = 1 := by rw [← map_mul, h1, map_one]
    have hπu1 : π u ≠ 1 := by
      intro h1'
      have hu_ker : u ∈ π.ker := h1'
      rw [hc.ker_eq, ← hc.center_eq] at hu_ker
      apply hσ1
      ext x
      rw [hu, MulAut.one_apply]
      have := Subgroup.mem_center_iff.1 hu_ker x
      calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [← this]
        _ = x := by group
    have hord : orderOf (π u) = 2 := orderOf_eq_prime (by rw [sq]; exact hπuu) hπu1
    obtain ⟨hfc, -, hlift0⟩ :=
      CFSG.ComponentClassification.M12Cover.m12_double_cover_involution_lift_orders hq
        hc.orderOf_t hc.center_eq π hc.surjective hc.ker_eq
    have hfour : CFSG.ComponentClassification.M12Cover.fixedCount (π u) = 4 := by
      rcases hfc _ hord with h4 | h0
      · exact h4
      · exfalso
        have hut := (hlift0 u hord h0).1
        rw [sq, h1] at hut
        exact ht1 hut.symm
    obtain ⟨g, hg⟩ := CFSG.ComponentClassification.M12Cover.conj_elemR_of_fixedCount_four (π u) hord hfour
    obtain ⟨g', rfl⟩ := hc.surjective g
    obtain ⟨hP', hPu', hcard⟩ := CFSG.GH74.KGroups.TwoM12.conj_data (u := u) g' hP hPu
    have hu' : π (g'⁻¹ * u * g') = CFSG.ComponentClassification.M12Cover.elemR := by
      rw [map_mul, map_mul, map_inv, ← hg]
      group
    have hle := CFSG.GH74.KGroups.TwoM12.card_le_two_of_comm_r hc hu' hP' hPu'
    rw [hcard] at hle
    omega
  · exact h1

end M12Inner

section M12Elim

@[expose] def M12OuterProp : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (L : Subgroup Z), CFSG.GH74.E2.Shape2M12 ↥L → ∀ s : Z, s * s = 1 →
    (∀ l ∈ L, s * l * s⁻¹ ∈ L) → (¬ ∃ u ∈ L, ∀ l ∈ L, s * l * s⁻¹ = u * l * u⁻¹) →
    ∀ P : Subgroup Z, P ≤ L → ⁅P, P⁆ = P → P ≠ ⊥ → (∀ x ∈ P, s * x * s⁻¹ = x) →
      ∀ g : Z, g * s = s * g → (∀ l ∈ L, g * l * g⁻¹ ∈ L) → (∀ p ∈ P, g * p * g⁻¹ ∈ P) →
        ∃ d ∈ P, ∀ p ∈ P, g * p * g⁻¹ = d * p * d⁻¹

variable {G : Type} [Group G] [Finite G] {x f : G} {Λ : Subgroup G}

structure KSide (K : Subgroup G) (x f : G) (Λ : Subgroup G) : Prop where
  hSF : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G),
    (∀ i ∈ Λ, c * i * c⁻¹ * i⁻¹ ∈ pPrimeCoreOf 2 Λ) → c ∈ CxK x K ∨ c * f ∈ CxK x K
  hinn : ∀ k ∈ K, k * f ∉ CxK x K
  hC : ∃ g ∈ K ⊓ centralizer ({f} : Set G), ∀ δ ∈ Λ, δ⁻¹ * g ∉ pPrimeCoreOf 2 K

theorem mem_pPrimeCoreOf_of_barMk_eq_one {Λ : Subgroup G} (hΛY : Λ ≤ centralizer ({f} : Set G))
    {a : G} (ha : a ∈ Λ) (h : barMk ↥(centralizer ({f} : Set G)) ⟨a, hΛY ha⟩ = 1) :
    a ∈ pPrimeCoreOf 2 Λ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥Λ →* barQ ↥(centralizer ({f} : Set G)) :=
    (barMk ↥(centralizer ({f} : Set G))).comp (Subgroup.inclusion hΛY)
  have hn : ψ.ker.Normal := MonoidHom.normal_ker ψ
  have hodd : Odd (Nat.card ψ.ker) := by
    let ι : ↥ψ.ker →* ↥(barMk ↥(centralizer ({f} : Set G))).ker :=
      ((Subgroup.inclusion hΛY).comp ψ.ker.subtype).codRestrict _ (fun m => m.2)
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 : (ι a).val = (ι b).val := congrArg Subtype.val hab
      apply Subtype.ext
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      exact h2
    exact Odd.of_dvd_nat TwoThin.odd_card_ker_barMk (Subgroup.card_dvd_of_injective ι hι)
  have hle : ψ.ker ≤ pPrimeCore 2 ↥Λ :=
    GroupTheory.le_pPrimeCore_of_normal hn (Nat.coprime_two_left.2 hodd)
  have hmem : (⟨a, ha⟩ : ↥Λ) ∈ pPrimeCore 2 ↥Λ := hle h
  exact ⟨⟨a, ha⟩, hmem, rfl⟩

theorem mem_pPrimeCoreOf_of_mem_CxK {K : Subgroup G} (hKcen : Subgroup.center (kBar K) = ⊥) {k : G}
    (hk : k ∈ K) (hkC : k ∈ CxK x K) : k ∈ pPrimeCoreOf 2 K := by
  have hsec : ∀ y ∈ K, ⁅y, k⁆ ∈ pPrimeCoreOf 2 K := fun y hy => hkC.2.2.2 y hy
  have hmem : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) ∈ Subgroup.center (kBar K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨hyk, h1⟩ := (IVK.Lifted.mem_pPrimeCoreOf_iff_hatMk K _).1 (hsec y hy)
    have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (⟨y, hy⟩ * ⟨k, hk⟩ * ⟨y, hy⟩⁻¹ * ⟨k, hk⟩⁻¹) = 1 := by
      have : (⟨⁅y, k⁆, hyk⟩ : ↥K) = ⟨y, hy⟩ * ⟨k, hk⟩ * ⟨y, hy⟩⁻¹ * ⟨k, hk⟩⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [← this]
      exact h1
    simp only [map_mul, map_inv] at h2
    have h3 : ⁅(QuotientGroup.mk' (pPrimeCore 2 ↥K)) ⟨y, hy⟩, (QuotientGroup.mk' (pPrimeCore 2 ↥K)) ⟨k, hk⟩⁆ = 1 := by
      rw [commutatorElement_def]
      exact h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  rw [hKcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact ⟨⟨k, hk⟩, hmem, rfl⟩

variable {E : YEnv G x f Λ} {L : Subgroup (barQ ↥(centralizer ({f} : Set G)))}

theorem Stable32.false_of_2M12
    (hO1 : M12OuterProp) (hG : C3Hyp G) (S : Stable32 E L) (hσ : S.sigma ≠ 1)
    (h2M : CFSG.GH74.E2.Shape2M12 ↥L) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G))
    (hKcen : Subgroup.center (kBar K) = ⊥)
    (hΛW : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G), ∀ a ∈ Λ, c * a * c⁻¹ ∈ Λ)
    (hΛK : Λ ≤ K) {r : ℕ} (hrodd : Odd r) (hr : HasL2Model (kBar Λ) (fun q => q = r))
    (hK : r = 5 → KSide K x f Λ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP60 : Nat.card ↥(Psub f Λ L) = 60 :=
    le_antisymm (CFSG.GH74.KGroups.TwoM12.card_le_sixty_of_fixed h2M S.sigma S.sigma_sq hσ
      S.P_perfect S.P_fixed) S.sixty_le_card_P
  have hΛ60 : Nat.card (kBar Λ) = 60 := by
    obtain ⟨φ, hφ, -⟩ := S.exists_phiP
    have hdvd : Nat.card (kBar Λ) ∣ Nat.card ↥(Psub f Λ L) :=
      Subgroup.card_dvd_of_surjective (f := φ) hφ
    rw [hP60] at hdvd
    exact le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) (sixty_le_card_of_hasL2Model_odd E.hΛU)
  have hr5 : r = 5 := by
    have h1 := Bk.two_mul_card_of_hasL2Model_eq hrodd hr
    rw [hΛ60] at h1
    obtain ⟨a, rfl⟩ := hrodd
    have hle : a ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have : (2 * 3 + 1) * ((2 * 3 + 1) ^ 2 - 1) ≤ (2 * a + 1) * ((2 * a + 1) ^ 2 - 1) := by
        apply Nat.mul_le_mul (by omega)
        apply Nat.sub_le_sub_right
        exact Nat.pow_le_pow_left (by omega) 2
      omega
    interval_cases a <;> omega
  have hKS := hK hr5
  have hwc : ∀ y : ↥(centralizer ({f} : Set G)), wY f * y = y * wY f := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2).symm
  have hc0c : ∀ y : barQ ↥(centralizer ({f} : Set G)),
      y * barMk ↥(centralizer ({f} : Set G)) (wY f) = barMk ↥(centralizer ({f} : Set G)) (wY f) * y :=
    fun y' => by
      obtain ⟨y, rfl⟩ := barMk_surjective (Y := ↥(centralizer ({f} : Set G))) y'
      rw [← map_mul, ← map_mul, hwc y]
  have hc0sq : barMk ↥(centralizer ({f} : Set G)) (wY f) * barMk ↥(centralizer ({f} : Set G)) (wY f) = 1 := by
    have := pow_orderOf_eq_one (barMk ↥(centralizer ({f} : Set G)) (wY f))
    rwa [orderOf_barMk_wY E.hf2, pow_two] at this
  have hc0L : barMk ↥(centralizer ({f} : Set G)) (wY f) ∈ L := by
    by_contra hnot
    have hRC : RankCertified ↥L 3 := (rank3_M12 h2M.2.2).of_quotient (center ↥L)
    exact not_rankCertified_three_of_gen4 (gen4_barQ hG.gen4 f) hc0c hc0sq hnot hRC
  let tL : ↥L := ⟨barMk ↥(centralizer ({f} : Set G)) (wY f), hc0L⟩
  have htL2 : orderOf tL = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_barMk_wY E.hf2
  have htLc : tL ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc0c g)
  have hsB2 : sbar x E.hxY * sbar x E.hxY = 1 := by
    have h2 : orderOf (sbar x E.hxY) = 2 := orderOf_sbar E.hx2 E.hxY
    have := pow_orderOf_eq_one (sbar x E.hxY)
    rwa [h2, pow_two] at this
  by_cases hin : ∃ u : ↥L, ∀ l : ↥L, S.sigma l = u * l * u⁻¹
  ·
    obtain ⟨u, hu⟩ := hin
    have hP2 : 2 < Nat.card ↥(Psub f Λ L) := by omega
    have hut : u * u = tL :=
      inner_sq_eq_t h2M S.sigma S.sigma_sq hσ S.P_perfect hP2 S.P_fixed htL2 htLc u hu
    let uB : barQ ↥(centralizer ({f} : Set G)) := (u : barQ ↥(centralizer ({f} : Set G)))
    have hut' : uB * uB = barMk ↥(centralizer ({f} : Set G)) (wY f) := congrArg Subtype.val hut
    have hsl : ∀ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ = uB * l * uB⁻¹ := fun l hl => by
      have h1 := congrArg (fun z : ↥L => (z : barQ ↥(centralizer ({f} : Set G)))) (hu ⟨l, hl⟩)
      exact h1
    have hsu : sbar x E.hxY * uB * (sbar x E.hxY)⁻¹ = uB := by
      rw [hsl uB u.2]
      group
    have huBs : sbar x E.hxY * uB = uB * sbar x E.hxY := by
      have := hsu
      calc sbar x E.hxY * uB = (sbar x E.hxY * uB * (sbar x E.hxY)⁻¹) * sbar x E.hxY := by group
        _ = uB * sbar x E.hxY := by rw [this]
    set cB : barQ ↥(centralizer ({f} : Set G)) := uB⁻¹ * sbar x E.hxY with hcB
    have hcBL : ∀ l ∈ L, cB * l * cB⁻¹ = l := by
      intro l hl
      calc cB * l * cB⁻¹ = uB⁻¹ * (sbar x E.hxY * l * (sbar x E.hxY)⁻¹) * uB := by rw [hcB]; group
        _ = uB⁻¹ * (uB * l * uB⁻¹) * uB := by rw [hsl l hl]
        _ = l := by group
    have huBs' : sbar x E.hxY * uB⁻¹ = uB⁻¹ * sbar x E.hxY := by
      calc sbar x E.hxY * uB⁻¹ = uB⁻¹ * (uB * sbar x E.hxY) * uB⁻¹ := by group
        _ = uB⁻¹ * (sbar x E.hxY * uB) * uB⁻¹ := by rw [huBs]
        _ = uB⁻¹ * sbar x E.hxY := by group
    have hcBs : cB * sbar x E.hxY = sbar x E.hxY * cB := by
      rw [hcB]
      calc uB⁻¹ * sbar x E.hxY * sbar x E.hxY = (sbar x E.hxY * uB⁻¹) * sbar x E.hxY := by rw [← huBs']
        _ = sbar x E.hxY * (uB⁻¹ * sbar x E.hxY) := by group
    have hcBsq : cB * cB = barMk ↥(centralizer ({f} : Set G)) (wY f) := by
      have h1 : cB * cB = uB⁻¹ * uB⁻¹ * (sbar x E.hxY * sbar x E.hxY) := by
        rw [hcB]
        calc uB⁻¹ * sbar x E.hxY * (uB⁻¹ * sbar x E.hxY)
            = uB⁻¹ * (sbar x E.hxY * uB⁻¹) * sbar x E.hxY := by group
          _ = uB⁻¹ * (uB⁻¹ * sbar x E.hxY) * sbar x E.hxY := by rw [huBs']
          _ = uB⁻¹ * uB⁻¹ * (sbar x E.hxY * sbar x E.hxY) := by group
      rw [h1, hsB2, mul_one]
      have h2 : uB⁻¹ * uB⁻¹ = (uB * uB)⁻¹ := by group
      rw [h2, hut']
      exact inv_eq_of_mul_eq_one_right hc0sq
    have hcBmem : cB ∈ centralizer ({barMk ↥(centralizer ({f} : Set G)) ⟨x, E.hxY⟩} :
        Set (barQ ↥(centralizer ({f} : Set G)))) := mem_centralizer_singleton_iff.2 hcBs
    obtain ⟨c₀, hc₀⟩ := TwoThin.barMkCentralizer_surjective E.hsO ⟨cB, hcBmem⟩
    have hy : TwoThin.barMkCentralizer E.hsO c₀ ^ (2 ^ 2) = 1 := by
      rw [hc₀]
      apply Subtype.ext
      show cB ^ (2 ^ 2) = 1
      have : cB ^ (2 ^ 2) = (cB * cB) * (cB * cB) := by
        rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
      rw [this, hcBsq]
      exact hc0sq
    obtain ⟨c₂, i, hc₂i, hc₂⟩ := Stage1.Thm6.Prod.exists_lift_pElement
      (TwoThin.barMkCentralizer E.hsO) Nat.prime_two c₀ hy
    set cY : ↥(centralizer ({f} : Set G)) := (c₂ : ↥(centralizer ({f} : Set G))) with hcY
    have hcYbar : barMk ↥(centralizer ({f} : Set G)) cY = cB := by
      have h1 := TwoThin.barMkCentralizer_apply E.hsO c₂
      rw [hc₂, hc₀] at h1
      exact h1.symm
    have hcYs : cY * ⟨x, E.hxY⟩ = ⟨x, E.hxY⟩ * cY := mem_centralizer_singleton_iff.1 c₂.2
    have hcYpow : cY ^ (2 ^ i) = 1 := by
      have := congrArg Subtype.val hc₂i
      simpa [Subgroup.coe_pow] using this
    have hwsq : wY f * wY f = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one f
      rwa [E.hf2, pow_two] at this
    have hcYsq : cY * cY = wY f := by
      have hzbar : barMk ↥(centralizer ({f} : Set G)) (cY * cY * (wY f)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hcYbar, hcBsq]
        group
      have hzmem : cY * cY * (wY f)⁻¹ ∈ pPrimeCore 2 ↥(centralizer ({f} : Set G)) := by
        rw [← TwoThin.ker_barMk]
        exact hzbar
      have hcomm : Commute (cY * cY) (wY f)⁻¹ := by
        have h1 : Commute cY (wY f) := (hwc cY).symm
        exact (h1.mul_left h1).inv_right
      have hN : (cY * cY * (wY f)⁻¹) ^ (2 ^ (i + 1)) = 1 := by
        rw [hcomm.mul_pow]
        have h1 : (cY * cY) ^ (2 ^ (i + 1)) = 1 := by
          rw [← pow_two, ← pow_mul, show 2 * 2 ^ (i + 1) = 2 ^ i * 4 by ring, pow_mul, hcYpow,
            one_pow]
        have h2 : ((wY f)⁻¹) ^ (2 ^ (i + 1)) = 1 := by
          rw [inv_pow, show 2 ^ (i + 1) = 2 * 2 ^ i by ring, pow_mul, pow_two, hwsq, one_pow,
            inv_one]
        rw [h1, h2, one_mul]
      have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({f} : Set G)))) :=
        TwoThin.odd_card_pPrimeCore _
      have hdvd1 : orderOf (cY * cY * (wY f)⁻¹) ∣ 2 ^ (i + 1) := orderOf_dvd_of_pow_eq_one hN
      have hdvd2 : orderOf (cY * cY * (wY f)⁻¹) ∣
          Nat.card ↥(pPrimeCore 2 ↥(centralizer ({f} : Set G))) := by
        have := orderOf_dvd_natCard (⟨cY * cY * (wY f)⁻¹, hzmem⟩ :
          ↥(pPrimeCore 2 ↥(centralizer ({f} : Set G))))
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (2 ^ (i + 1))
          (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({f} : Set G)))) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
      have hord : orderOf (cY * cY * (wY f)⁻¹) = 1 :=
        (Nat.Coprime.coprime_dvd_left hdvd1 hcop).eq_one_of_dvd hdvd2
      have := orderOf_eq_one_iff.1 hord
      exact mul_inv_eq_one.1 this
    set c : G := (cY : G) with hc
    have hcf : c ∈ centralizer ({f} : Set G) := cY.2
    have hcx : c ∈ centralizer ({x} : Set G) := by
      have := congrArg Subtype.val hcYs
      exact mem_centralizer_singleton_iff.2 this
    have hcW : c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) := ⟨hcx, hcf⟩
    have hcsq : c * c = f := congrArg Subtype.val hcYsq
    have hff : f * f = 1 := by
      have := pow_orderOf_eq_one f
      rwa [E.hf2, pow_two] at this
    have hyp : ∀ i' ∈ Λ, c * i' * c⁻¹ * i'⁻¹ ∈ pPrimeCoreOf 2 Λ := by
      intro i' hi'
      have hai : c * i' * c⁻¹ ∈ Λ := hΛW c hcW i' hi'
      have hz : c * i' * c⁻¹ * i'⁻¹ ∈ Λ := Λ.mul_mem hai (Λ.inv_mem hi')
      apply mem_pPrimeCoreOf_of_barMk_eq_one E.hΛY hz
      have hEq : (⟨c * i' * c⁻¹ * i'⁻¹, E.hΛY hz⟩ : ↥(centralizer ({f} : Set G))) =
          cY * ⟨i', E.hΛY hi'⟩ * cY⁻¹ * ⟨i', E.hΛY hi'⟩⁻¹ := by
        apply Subtype.ext
        simp [hc]
      rw [hEq, map_mul, map_mul, map_mul, map_inv, map_inv, hcYbar]
      have hmem : barMk ↥(centralizer ({f} : Set G)) ⟨i', E.hΛY hi'⟩ ∈ L :=
        S.hΛL ⟨⟨i', E.hΛY hi'⟩, Subgroup.mem_subgroupOf.2 hi', rfl⟩
      rw [hcBL _ hmem]
      group
    have hfC : f ∈ CxK x K → False := fun h => hKS.hinn 1 K.one_mem (by simpa using h)
    rcases hKS.hSF c hcW hyp with h | h
    · exact hfC (by rw [← hcsq]; exact (CxK x K).mul_mem h h)
    · apply hfC
      have hcomm : c * f = f * c := mem_centralizer_singleton_iff.1 hcf
      have : (c * f) * (c * f) = f := by
        calc (c * f) * (c * f) = c * (f * c) * f := by group
          _ = c * (c * f) * f := by rw [← hcomm]
          _ = (c * c) * (f * f) := by group
          _ = f := by rw [hcsq, hff, mul_one]
      rw [← this]
      exact (CxK x K).mul_mem h h
  ·
    have hout : ¬ ∃ u ∈ L, ∀ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ = u * l * u⁻¹ := by
      rintro ⟨u, huL, hu⟩
      apply hin
      refine ⟨⟨u, huL⟩, fun l => Subtype.ext ?_⟩
      exact hu l l.2
    obtain ⟨g, hgKf, hgC⟩ := hKS.hC
    have hgx : g ∈ centralizer ({x} : Set G) := hKC hgKf.1
    have hgW : g ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) := ⟨hgx, hgKf.2⟩
    have hginvW : g⁻¹ ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) :=
      Subgroup.inv_mem _ hgW
    set gB : barQ ↥(centralizer ({f} : Set G)) :=
      barMk ↥(centralizer ({f} : Set G)) ⟨g, hgKf.2⟩ with hgB
    have hgs : gB * sbar x E.hxY = sbar x E.hxY * gB := by
      rw [hgB, sbar, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.1 hgx
    have hPnorm : ∀ (h : G) (hhW : h ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)),
        ∀ p ∈ bar f Λ, barMk ↥(centralizer ({f} : Set G)) ⟨h, hhW.2⟩ * p *
          (barMk ↥(centralizer ({f} : Set G)) ⟨h, hhW.2⟩)⁻¹ ∈ bar f Λ := by
      intro h hhW p hp
      obtain ⟨a', ha', rfl⟩ := hp
      refine ⟨⟨h, hhW.2⟩ * a' * ⟨h, hhW.2⟩⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 (hΛW h hhW a'.1 (Subgroup.mem_subgroupOf.1 ha'))
      · simp
    have hPL : bar f Λ ≤ L := S.hΛL
    have hgP : ∀ p ∈ bar f Λ, gB * p * gB⁻¹ ∈ bar f Λ := hPnorm g hgW
    have hginvB : barMk ↥(centralizer ({f} : Set G)) ⟨g⁻¹, hginvW.2⟩ = gB⁻¹ := by
      rw [hgB, ← map_inv]
      rfl
    have hginvP : ∀ p ∈ bar f Λ, gB⁻¹ * p * gB ∈ bar f Λ := by
      intro p hp
      have := hPnorm g⁻¹ hginvW p hp
      rw [hginvB, inv_inv] at this
      exact this
    have hgL : ∀ l ∈ L, gB * l * gB⁻¹ ∈ L := by
      have hL'c : CFSG.IsComponent (L.map (MulAut.conj gB).toMonoidHom) :=
        LocalCores.isComponent_map_mulEquiv (MulAut.conj gB) S.hL
      rcases LocalCores.distinct_components_commute S.hL hL'c with hLL' | hcomm
      · intro l hl
        have : gB * l * gB⁻¹ ∈ L.map (MulAut.conj gB).toMonoidHom :=
          ⟨l, hl, by simp [MulAut.conj_apply]⟩
        rwa [← hLL'] at this
      · exfalso
        have hPL' : bar f Λ ≤ L.map (MulAut.conj gB).toMonoidHom := by
          intro p hp
          refine ⟨gB⁻¹ * p * gB, hPL (hginvP p hp), ?_⟩
          show gB * (gB⁻¹ * p * gB) * gB⁻¹ = p
          group
        have hcm : ⁅bar f Λ, bar f Λ⁆ ≤ ⁅L, L.map (MulAut.conj gB).toMonoidHom⁆ :=
          Subgroup.commutator_mono hPL hPL'
        rw [hcomm, E.bar_perfect] at hcm
        exact E.bar_ne_bot (le_bot_iff.1 hcm)
    have hsL : ∀ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ ∈ L := fun l hl =>
      (Subgroup.mem_normalizer_iff.1 S.hN l).1 hl
    obtain ⟨d, hdP, hd⟩ := hO1 (barQ ↥(centralizer ({f} : Set G))) L h2M (sbar x E.hxY) hsB2 hsL
      hout (bar f Λ) hPL E.bar_perfect E.bar_ne_bot E.bar_fixed gB hgs hgL hgP
    obtain ⟨δ', hδ', hδd⟩ := hdP
    have hδΛ : (δ' : G) ∈ Λ := Subgroup.mem_subgroupOf.1 hδ'
    have hδW : (δ' : G) ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) := E.hΛW hδΛ
    set g' : G := (δ' : G)⁻¹ * g with hg'
    have hg'K : g' ∈ K := K.mul_mem (K.inv_mem (hΛK hδΛ)) hgKf.1
    have hg'W : g' ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hδW) hgW
    have hyp : ∀ i ∈ Λ, g' * i * g'⁻¹ * i⁻¹ ∈ pPrimeCoreOf 2 Λ := by
      intro i hi
      have hai : g' * i * g'⁻¹ ∈ Λ := hΛW g' hg'W i hi
      have hz : g' * i * g'⁻¹ * i⁻¹ ∈ Λ := Λ.mul_mem hai (Λ.inv_mem hi)
      apply mem_pPrimeCoreOf_of_barMk_eq_one E.hΛY hz
      have hEq : (⟨g' * i * g'⁻¹ * i⁻¹, E.hΛY hz⟩ : ↥(centralizer ({f} : Set G))) =
          (δ'⁻¹ * ⟨g, hgKf.2⟩) * ⟨i, E.hΛY hi⟩ * (δ'⁻¹ * ⟨g, hgKf.2⟩)⁻¹ * ⟨i, E.hΛY hi⟩⁻¹ := by
        apply Subtype.ext
        simp [hg']
      have hpP : barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ ∈ bar f Λ :=
        ⟨⟨i, E.hΛY hi⟩, Subgroup.mem_subgroupOf.2 hi, rfl⟩
      rw [hEq]
      simp only [map_mul, map_inv, hδd]
      have h1 : (d⁻¹ * gB) * barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ * (d⁻¹ * gB)⁻¹ =
          barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ := by
        calc (d⁻¹ * gB) * barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ * (d⁻¹ * gB)⁻¹
            = d⁻¹ * (gB * barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ * gB⁻¹) * d := by group
          _ = d⁻¹ * (d * barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ * d⁻¹) * d := by
            rw [hd _ hpP]
          _ = barMk ↥(centralizer ({f} : Set G)) ⟨i, E.hΛY hi⟩ := by group
      rw [h1]
      group
    rcases hKS.hSF g' hg'W hyp with h | h
    · exact hgC (δ' : G) hδΛ (mem_pPrimeCoreOf_of_mem_CxK hKcen hg'K h)
    · exact hKS.hinn g' hg'K h

end M12Elim

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
