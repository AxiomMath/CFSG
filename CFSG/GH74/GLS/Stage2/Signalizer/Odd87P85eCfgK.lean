module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eU34
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eCfgMap
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem exists_five_lift {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B)
    (hf : Function.Surjective f) (b : B) (e : ℕ) (hb : b ^ (5 ^ e) = 1) :
    ∃ a : A, (∃ e' : ℕ, a ^ (5 ^ e') = 1) ∧ zpowers (f a) = zpowers b := by
  obtain ⟨a₀, rfl⟩ := hf b
  have hne : orderOf a₀ ≠ 0 := (orderOf_pos a₀).ne'
  obtain ⟨g, m, hm, hgm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 5 (by norm_num)
  refine ⟨a₀ ^ m, ⟨g, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hgm, pow_orderOf_eq_one]
  · rw [map_pow]
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
    · apply le_of_eq
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
      · rw [Nat.card_zpowers, Nat.card_zpowers]
        have hdvd : orderOf (f a₀) ∣ 5 ^ e := orderOf_dvd_of_pow_eq_one hb
        have hcop : Nat.Coprime (5 ^ e) m :=
          Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm)
        rw [Nat.Coprime.orderOf_pow (Nat.Coprime.coprime_dvd_left hdvd hcop)]

theorem card_map_le' {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H) (K : Subgroup G) :
    Nat.card (K.map f) ≤ Nat.card K :=
  Nat.card_le_card_of_surjective (f.subgroupMap K) (f.subgroupMap_surjective K)

theorem u34cfg_of_center {K : Type} [Group K] [Finite K] (hZ : IsPGroup 2 ↥(Subgroup.center K))
    (hU : LieModel (K ⧸ Subgroup.center K) .PSU 3 2 2) :
    ∃ (P : Subgroup K) (w : K), U34Cfg P w := by
  classical
  obtain ⟨Ph, wh, h2, hcard, hexp, hcen4, hcen, hw5, hwn, hcomm⟩ := u34_data hU
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  let P : Subgroup K := Ph.comap π
  have hmemP : ∀ x, x ∈ P ↔ π x ∈ Ph := fun x => Iff.rfl
  have hπ1 : ∀ x ∈ Subgroup.center K, π x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).mpr hx
  have hZP : Subgroup.center K ≤ P := fun x hx => by
    rw [hmemP, hπ1 x hx]; exact Ph.one_mem
  have hPmap : P.map π = Ph := Subgroup.map_comap_eq_self_of_surjective hπs Ph
  obtain ⟨w, ⟨e', hwe⟩, hwz⟩ := exists_five_lift π hπs wh 1 (by simpa using hw5)
  set c := Nat.card (Subgroup.center K) with hc
  have hcpos : 0 < c := Nat.card_pos
  have hPcard : Nat.card P = 64 * c := by
    let g : ↥P →* K ⧸ Subgroup.center K := π.comp P.subtype
    have hrange : g.range = Ph := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
    have hgker : g.ker = (Subgroup.center K).subgroupOf P := by
      ext x
      simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, π]
    have h1 := Subgroup.card_ker_mul_card_range g
    rw [hrange, hgker] at h1
    rw [← h1, hcard, mul_comm]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hπw : π w ∈ zpowers wh := hwz ▸ Subgroup.mem_zpowers _
  have hπwn : π w ∈ normalizer (Ph : Set (K ⧸ Subgroup.center K)) :=
    (Subgroup.zpowers_le.mpr hwn : zpowers wh ≤ normalizer (Ph : Set (K ⧸ Subgroup.center K))) hπw
  have hwP : w ∈ normalizer (P : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemP, hmemP, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hπwn (π x)
  have hcentral : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → ∀ q ∈ Ph, π x * q = q * π x := by
    intro x hxP hxc q hq
    rw [← hPmap] at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_mul, ← map_mul, hxc y hy]
  have hcenW : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → w * x * w⁻¹ = x := by
    intro x hxP hxc
    have hπx := hcentral x hxP hxc
    have hcomm1 : wh * π x = π x * wh := by
      have := (hcen (π x) hxP hπx).2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hπw
    have hcomm2 : π w * π x = π x * π w := by
      rw [← hj]
      exact ((Commute.zpow_left (show Commute wh (π x) from hcomm1) j)).eq
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, c₀ = w * x * w⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hc₀π : π c₀ = 1 := by
      have h1 : π w * π x * (π w)⁻¹ = π x := by
        rw [hcomm2, mul_assoc, mul_inv_cancel, mul_one]
      rw [hc₀]
      simp only [map_mul, map_inv]
      rw [h1, mul_inv_cancel]
    have hc₀Z : c₀ ∈ Subgroup.center K := by
      rw [← hker]; exact hc₀π
    have hc₀c : ∀ g : K, g * c₀ = c₀ * g := Subgroup.mem_center_iff.mp hc₀Z
    have hind : ∀ n : ℕ, w ^ n * x * (w ^ n)⁻¹ = c₀ ^ n * x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : w ^ (n + 1) * x * (w ^ (n + 1))⁻¹ = w * (w ^ n * x * (w ^ n)⁻¹) * w⁻¹ := by group
        rw [h1, ih]
        have h2 : w * (c₀ ^ n * x) * w⁻¹ = (w * c₀ ^ n * w⁻¹) * (w * x * w⁻¹) := by group
        have h3 : w * c₀ ^ n * w⁻¹ = c₀ ^ n := by
          have := (Commute.pow_right (show Commute w c₀ from hc₀c w) n).eq
          rw [this]; group
        have h4 : w * x * w⁻¹ = c₀ * x := by rw [hc₀]; group
        rw [h2, h3, h4, pow_succ, mul_assoc]
    have h5 := hind (5 ^ e')
    rw [hwe] at h5
    have h6 : c₀ ^ (5 ^ e') = 1 := by
      have : c₀ ^ (5 ^ e') * x = 1 * x := by
        rw [← h5]; simp
      exact mul_right_cancel this
    obtain ⟨s, hs⟩ := hZ ⟨c₀, hc₀Z⟩
    have hs' : c₀ ^ (2 ^ s) = 1 := by simpa using congrArg Subtype.val hs
    have h7 : c₀ ^ Nat.gcd (5 ^ e') (2 ^ s) = 1 := pow_gcd_eq_one.mpr ⟨h6, hs'⟩
    have h8 : Nat.gcd (5 ^ e') (2 ^ s) = 1 := Nat.Coprime.pow e' s (by norm_num)
    rw [h8, pow_one] at h7
    have : w * x * w⁻¹ * x⁻¹ = 1 := by rw [← hc₀]; exact h7
    exact mul_inv_eq_one.mp this
  have hordP : ∀ x ∈ P, 8 * orderOf x < Nat.card P := by
    intro x hxP
    have h1 : (π x) ^ 4 = 1 := hexp _ hxP
    have h2 : x ^ 4 ∈ Subgroup.center K := by
      rw [← hker, MonoidHom.mem_ker, map_pow]; exact h1
    have h3 : (x ^ 4) ^ c = 1 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center K) h2
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h4 : orderOf x ∣ 4 * c := orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact h3)
    have h5 : orderOf x ≤ 4 * c := Nat.le_of_dvd (by omega) h4
    rw [hPcard]; omega
  have hcomm_ge : 64 ≤ Nat.card ↥⁅P, zpowers w⁆ := by
    have h1 : (⁅P, zpowers w⁆).map π = Ph := by
      rw [Subgroup.map_commutator, hPmap, MonoidHom.map_zpowers, hwz, hcomm]
    have := card_map_le' π ⁅P, zpowers w⁆
    rw [h1, hcard] at this
    exact this
  have hcenter_or : 64 < Nat.card P ∨ (Nat.card P = 64 ∧ 4 ≤ Nat.card ↥(Subgroup.center ↥P) ∧
      ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x * x = 1) := by
    by_cases hc1 : c = 1
    · right
      have hZbot : Subgroup.center K = ⊥ := Subgroup.card_eq_one.mp (hc ▸ hc1)
      refine ⟨by rw [hPcard, hc1], ?_, ?_⟩
      · have hinj : Function.Injective (π.comp P.subtype) := by
          rw [injective_iff_map_eq_one]
          intro x hx
          have h1 : π (x : K) = 1 := hx
          have h2 : (x : K) ∈ Subgroup.center K := by rw [← hker]; exact h1
          rw [hZbot, Subgroup.mem_bot] at h2
          exact Subtype.ext h2
        have hrange : (π.comp P.subtype).range = Ph := by
          rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
        let e : ↥P ≃* ↥Ph := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
        have := Nat.card_congr (Subgroup.centerCongr e).toEquiv
        rw [this, hcen4]
      · intro x hxP hxc
        have := (hcen (π x) hxP (hcentral x hxP hxc)).1
        have h2 : x * x ∈ Subgroup.center K := by
          rw [← hker, MonoidHom.mem_ker, map_mul]; exact this
        rw [hZbot, Subgroup.mem_bot] at h2
        exact h2
    · left
      rw [hPcard]
      omega
  exact ⟨P, w, ⟨h2.comap_of_ker_isPGroup π (by rw [hker]; exact hZ), ⟨e', hwe⟩, hwP, hcenW, hcomm_ge, hordP,
    by omega, hcenter_or⟩⟩



theorem u34cfg_of_section {G : Type} [Group G] [Finite G] {H₀ : Subgroup G}
    (H₁ : Subgroup ↥H₀) [H₁.Normal] (hodd : Odd (Nat.card H₁))
    {K : Subgroup (↥H₀ ⧸ H₁)} (hZ : IsPGroup 2 ↥(Subgroup.center ↥K))
    (hU : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 2) :
    ∃ (P : Subgroup G) (w : G), U34Cfg P w := by
  classical
  obtain ⟨PK, wK, hK⟩ := u34cfg_of_center hZ hU
  have hH := hK.map_injective K.subtype K.subtype_injective
  obtain ⟨e, he⟩ := hH.five
  obtain ⟨P, w, hP2, hPmap, hinj, hwn, hw5, hwz⟩ :=
    lift_pair H₁ hodd (PK.map K.subtype) hH.two (K.subtype wK) hH.norm e he
  have hX := U34Cfg.of_lift (QuotientGroup.mk' H₁) hinj (kb := K.subtype wK)
    (by rw [hPmap]; exact hH) hwz hwn hw5 hP2
  exact ⟨P.map H₀.subtype, H₀.subtype w, hX.map_injective H₀.subtype H₀.subtype_injective⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
