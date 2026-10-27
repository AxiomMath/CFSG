module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSeven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndOddLayer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover

namespace EndB

section Transfer

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {y : G}

theorem bar_centralizer_equiv (hyM : y ∈ M) (hy2 : y ^ 2 = 1) :
    Nonempty (Bar (centralizer
        ({(QuotientGroup.mk ⟨y, hyM⟩ : ↥M ⧸ pPrimeCore 2 ↥M)} : Set (↥M ⧸ pPrimeCore 2 ↥M))) ≃*
      Bar (centralizer ({y} : Set G) ⊓ M)) ∧
    Nonempty (Bar (GSThmB.layerIn (centralizer
        ({(QuotientGroup.mk ⟨y, hyM⟩ : ↥M ⧸ pPrimeCore 2 ↥M)} : Set (↥M ⧸ pPrimeCore 2 ↥M)))) ≃*
      Bar (GSThmB.layerIn (centralizer ({y} : Set G) ⊓ M))) := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set y' : ↥M := ⟨y, hyM⟩ with hy'
  set Y' := centralizer ({y'} : Set ↥M) with hY'
  have hyy : y' * y' = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hy2, Subgroup.coe_one])
  have hCbar : centralizer ({π y'} : Set (↥M ⧸ pPrimeCore 2 ↥M)) = Y'.map π :=
    GSThmB.OddQuot.centralizer_singleton_map_eq hyy
  have hYmap : Y'.map M.subtype = centralizer ({y} : Set G) ⊓ M := map_subtype_centralizer_mk hyM
  refine ⟨?_, ?_⟩
  · change Nonempty (Bar (centralizer ({π y'} : Set (↥M ⧸ pPrimeCore 2 ↥M))) ≃* _)
    rw [hCbar, ← hYmap]
    obtain ⟨e₁⟩ := nonempty_bar_map_equiv π not_two_dvd_card_ker_mk' Y'
    obtain ⟨e₂⟩ := nonempty_bar_map_equiv M.subtype (not_two_dvd_card_ker_subtype M) Y'
    exact ⟨e₁.trans e₂.symm⟩
  · change Nonempty (Bar (GSThmB.layerIn (centralizer ({π y'} : Set (↥M ⧸ pPrimeCore 2 ↥M)))) ≃* _)
    rw [hCbar, ← hYmap, ← GSThmB.OddQuot.map_layerIn π not_two_dvd_card_ker_mk' Y',
      ← GSThmB.OddQuot.map_layerIn M.subtype (not_two_dvd_card_ker_subtype M) Y']
    obtain ⟨e₁⟩ := nonempty_bar_map_equiv π not_two_dvd_card_ker_mk' (GSThmB.layerIn Y')
    obtain ⟨e₂⟩ := nonempty_bar_map_equiv M.subtype (not_two_dvd_card_ker_subtype M)
      (GSThmB.layerIn Y')
    exact ⟨e₁.trans e₂.symm⟩

end Transfer

theorem exists_odd_lift {K Q : Type*} [Group K] [Group Q] [Finite K] (π : K →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center K) (hk2 : IsPGroup 2 π.ker) {e : K}
    {y : Q} (hy : Odd (orderOf y)) (hye : y * π e = π e * y) :
    ∃ yt : K, π yt = y ∧ Odd (orderOf yt) ∧ yt * e = e * yt := by
  obtain ⟨y₀, rfl⟩ := hπ y
  have hm0 : orderOf (π y₀) ≠ 0 := by
    obtain ⟨k, hk⟩ := hy
    omega
  have hker0 : y₀ ^ orderOf (π y₀) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hk2) ⟨_, hker0⟩
  rw [Subgroup.orderOf_mk] at ha
  have hcop : Nat.Coprime (2 ^ a) (orderOf (π y₀)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hy)
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hm0
  set yt := y₀ ^ (2 ^ a * c) with hyt
  have hπyt : π yt = π y₀ := by
    rw [hyt, map_pow]
    exact (pow_eq_pow_of_modEq (show 2 ^ a * c ≡ 1 [MOD orderOf (π y₀)] from hc)
      (pow_orderOf_eq_one _)).trans (pow_one _)
  have hytm : yt ^ orderOf (π y₀) = 1 := by
    rw [hyt, ← pow_mul, show 2 ^ a * c * orderOf (π y₀) = orderOf (π y₀) * 2 ^ a * c by ring,
      pow_mul, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
  have hodd : Odd (orderOf yt) := Odd.of_dvd_nat hy (orderOf_dvd_of_pow_eq_one hytm)
  refine ⟨yt, hπyt, hodd, ?_⟩
  set c₀ := yt * e * yt⁻¹ * e⁻¹ with hc₀
  have hc₀k : c₀ ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc₀, map_mul, map_mul, map_mul, map_inv, map_inv, hπyt]
    rw [show π y₀ * π e = π e * π y₀ from hye]
    group
  have hc₀z : c₀ ∈ center K := hker hc₀k
  have hstep : yt * e = c₀ * e * yt := by rw [hc₀]; group
  have hpow : ∀ n : ℕ, yt ^ n * e = c₀ ^ n * e * yt ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcz : yt * c₀ ^ n = c₀ ^ n * yt := (mem_center_iff.mp (pow_mem hc₀z n)) yt
      calc yt ^ (n + 1) * e = yt * (yt ^ n * e) := by rw [pow_succ', mul_assoc]
        _ = yt * (c₀ ^ n * e * yt ^ n) := by rw [ih]
        _ = (yt * c₀ ^ n) * (e * yt ^ n) := by group
        _ = (c₀ ^ n * yt) * (e * yt ^ n) := by rw [hcz]
        _ = c₀ ^ n * (yt * e) * yt ^ n := by group
        _ = c₀ ^ n * (c₀ * e * yt) * yt ^ n := by rw [hstep]
        _ = c₀ ^ (n + 1) * e * yt ^ (n + 1) := by rw [pow_succ, pow_succ']; group
  have h1 : c₀ ^ orderOf yt = 1 := by
    have := hpow (orderOf yt)
    rw [pow_orderOf_eq_one, one_mul, mul_one] at this
    calc c₀ ^ orderOf yt = c₀ ^ orderOf yt * e * e⁻¹ := by group
      _ = 1 := by rw [← this]; group
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hk2) ⟨c₀, hc₀k⟩
  rw [Subgroup.orderOf_mk] at hb
  have hdvd : orderOf c₀ ∣ orderOf yt := orderOf_dvd_of_pow_eq_one h1
  rw [hb] at hdvd
  have hb0 : b = 0 := by
    by_contra hb0
    have h2 : 2 ∣ 2 ^ b := dvd_pow_self 2 hb0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  rw [hb0, pow_zero, orderOf_eq_one_iff] at hb
  rw [hstep, hb, one_mul]

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem card_layer (hJ : JLayer hs π) :
    Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) =
      Nat.card P * Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  rw [← Subgroup.card_ker_mul_card_range π, hJ.ker, MonoidHom.range_eq_top.mpr hJ.surj,
    card_top, mul_comm]

theorem dvd_card_of_le (hJ : JLayer hs π)
    {C : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hEC : layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ C)
    (hβC : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ C) : 2 ^ 8 ∣ Nat.card C := by
  have hP : Nat.card P = 2 ^ 7 * 4725 := by rw [card_P]; norm_num
  by_cases hbE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
  ·
    have hz : (⟨_, hbE⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∈
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
      mem_center_iff.mpr fun g => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact mem_center_iff.mp (betaBar_mem_center (w ^ (orderOf w / 2) * t ^ i * z ^ j))
          (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    have hz1 : (⟨_, hbE⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≠ 1 :=
      fun h => hs.betaBar_ne_one (congrArg Subtype.val h)
    have hne : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥ := by
      intro h
      rw [h] at hz
      exact hz1 ((mem_bot).mp hz)
    have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have hc2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 :=
      le_antisymm hJ.center_le h2
    have hE2 : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 2 ^ 8 * 4725 := by
      rw [hJ.card_layer, hP, hc2]; ring
    exact (show 2 ^ 8 ∣ Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) by
      rw [hE2]; exact dvd_mul_right _ _).trans (Subgroup.card_dvd_of_le hEC)
  · have hβ1 := orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one
    have hdisj : Disjoint (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      rw [disjoint_iff, eq_bot_iff]
      intro g hg
      rcases eq_one_or_eq_of_mem_zpowers hβ1 (mem_inf.mp hg).2 with h | h
      · exact (mem_bot).mpr h
      · exact absurd (h ▸ (mem_inf.mp hg).1) hbE
    have hn : zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
        normalizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hcard := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn hdisj
    rw [Nat.card_zpowers, hβ1, hJ.card_layer, hP] at hcard
    have hle := sup_le hEC (zpowers_le.mpr hβC)
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hle)
    rw [hcard]
    exact ⟨4725 * Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))),
      by ring⟩

theorem false_of_dvd_centralizer
    (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (h256 : 2 ^ 8 ∣ Nat.card ↥(centralizer {(QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  obtain ⟨Ŝ, hŜ⟩ := exists_isSylowOf 2 (centralizer ({g * t * g⁻¹} : Set X) ⊓
    centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
  have hŜbar := isSylowOf_barOf_centralizer hτM hτ2 hŜ
  have hŜM : Ŝ ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hŜ.le.trans inf_le_right
  have hcard : 2 ^ 8 ≤ Nat.card Ŝ := by
    rw [← card_barOf hŜM hŜ.isPGroup, hŜbar.card_eq]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h256)
  have hŜ'H : Ŝ.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨s, hs', rfl⟩
    have hsτ : s * (g * t * g⁻¹) = (g * t * g⁻¹) * s :=
      mem_centralizer_singleton_iff.mp (hŜ.le hs').1
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * s * g * t = g⁻¹ * (s * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * s) * g := by rw [hsτ]
      _ = t * (g⁻¹ * s * g) := by group
  have hle := card_le_twoPart (hŜ.isPGroup.map _) hŜ'H
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hle
  have hS := hs.sylow.card_eq
  rw [twoPart] at hle
  have := hJ.card_S_le hcent
  omega

theorem not_conj_of_mem_pCore
    (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hτ : (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : False := by
  have hEC : layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      centralizer {(QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} := by
    intro l hl
    rw [mem_centralizer_singleton_iff]
    rw [← hs.centralizer_layer_eq hJ.h412] at hτ
    exact mem_centralizer_iff.mp hτ l hl
  have hβC : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      centralizer {(QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} :=
    mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (betaBar_mem_center _) _).symm
  exact hJ.false_of_dvd_centralizer hcent g hτM (hJ.dvd_card_of_le hEC hβC)

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
