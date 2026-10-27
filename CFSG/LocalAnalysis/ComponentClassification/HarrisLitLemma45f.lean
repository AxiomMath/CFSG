module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_conj_of_mem_coset_odd {N : Subgroup X} (hN : Odd (Nat.card N)) {x y : X}
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hxy : x⁻¹ * y ∈ N) :
    ∃ n ∈ N, n * x * n⁻¹ = y := by
  set m := x⁻¹ * y with hm
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
  have hinv : x * m * x⁻¹ = m⁻¹ := by
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
    calc x * m * x⁻¹ = y * x⁻¹ := by rw [hm]; group
      _ = y⁻¹ * x := by rw [hxi, hyi]
      _ = m⁻¹ := by rw [hm, mul_inv_rev, inv_inv]
  obtain ⟨k, hk⟩ : Odd (orderOf m) := by
    have hdvd : orderOf m ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk m hxy]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hN hdvd
  set m₀ := m ^ (k + 1) with hm₀
  have hm₀sq : m₀ ^ 2 = m := by
    rw [hm₀, ← pow_mul, show (k + 1) * 2 = orderOf m + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hinv₀ : x * m₀ * x⁻¹ = m₀⁻¹ := by
    rw [hm₀, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  refine ⟨m₀⁻¹, inv_mem (pow_mem hxy _), ?_⟩
  have h1 : x * m₀⁻¹ * x⁻¹ = m₀ := by
    rw [show x * m₀⁻¹ * x⁻¹ = (x * m₀ * x⁻¹)⁻¹ by group, hinv₀, inv_inv]
  calc m₀⁻¹ * x * m₀⁻¹⁻¹ = x * (x⁻¹ * m₀⁻¹ * x) * m₀ := by group
    _ = x * (x * m₀⁻¹ * x⁻¹) * m₀ := by rw [hxi]
    _ = x * m₀ ^ 2 := by rw [h1, sq, mul_assoc]
    _ = y := by rw [hm₀sq, hm]; group

theorem exists_conj_of_lieModel_psl2 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hY : Blueprint.LieModel Y .PSL 2 p f) {x y : Y} (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1)
    (hy1 : y ≠ 1) (hy2 : y ^ 2 = 1) : ∃ g : Y, g * x * g⁻¹ = y := by
  obtain ⟨hp, hf, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel hY
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩ (e x) (e y)
    ⟨fun h1 => hx1 (by simpa using congrArg e.symm h1), by rw [← map_pow, hx2, map_one]⟩
    ⟨fun h1 => hy1 (by simpa using congrArg e.symm h1), by rw [← map_pow, hy2, map_one]⟩
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]

variable {t : X} {L : Subgroup X} {p f : ℕ}

theorem mem_centralizerResidual_of_mk_mem {β d : X} (hd : d ∈ L ⊓ centralizer {β})
    (hd2 : d ^ 2 = 1) (hy : (QuotientGroup.mk ⟨d, hd.1⟩ : Bar L) ∈
      (barMap L (centralizerResidual_le_left (g := β))).range) :
    d ∈ centralizerResidual L β := by
  set K := centralizerResidual L β with hK
  obtain ⟨k, hk⟩ := hy
  rw [barMap_apply, QuotientGroup.eq] at hk
  set o := (k : X)⁻¹ * d with ho
  have hoO : o ∈ (pPrimeCore 2 ↥L).map L.subtype := ⟨_, hk, rfl⟩
  obtain ⟨n, hn⟩ : Odd (orderOf o) := by
    have hdvd : orderOf o ∣ Nat.card ((pPrimeCore 2 ↥L).map L.subtype) := by
      rw [← Subgroup.orderOf_mk o hoO]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_map_pPrimeCore L)) hdvd
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by rw [← sq, hd2])
  have hdN : d ∈ normalizer (K : Set X) := le_normalizer_centralizerResidual hd
  have ho2 : o ^ 2 ∈ K := by
    have h1 : d * (k : X)⁻¹ * d⁻¹ ∈ K := (mem_normalizer_iff.mp hdN _).mp (K.inv_mem k.2)
    have : o ^ 2 = (k : X)⁻¹ * (d * (k : X)⁻¹ * d⁻¹) := by
      rw [ho, sq, hdi]
      group
    rw [this]
    exact K.mul_mem (K.inv_mem k.2) h1
  have hoK : o ∈ K := by
    have h1 : o = (o ^ 2) ^ (n + 1) := by
      rw [← pow_mul, show 2 * (n + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [h1]
    exact K.pow_mem ho2 _
  rw [show d = (k : X) * o by rw [ho]; group]
  exact K.mul_mem k.2 hoK

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem exists_conj_of_rho_eq (hσ : Setup42 h hS w z) (i j : ℕ) {a b : X}
    (haH : a ∈ centralizer ({t} : Set X)) (hbH : b ∈ centralizer ({t} : Set X))
    (haL : a * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ ∈ L)
    (hbL : b * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ ∈ L) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hρ : h.rho ⟨a, haH⟩ = h.rho ⟨b, hbH⟩) :
    ∃ n ∈ (pPrimeCore 2 ↥L).map L.subtype, n * a * n⁻¹ = b := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have hβN : β ∈ normalizer (L : Set X) := hσ.beta_mem_normalizer i j
  have hcL : a⁻¹ * b ∈ L := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hβN) _).mp (L.mul_mem (L.inv_mem haL) hbL)
    rwa [show β⁻¹ * ((a * β⁻¹)⁻¹ * (b * β⁻¹)) * β⁻¹⁻¹ = a⁻¹ * b by group] at h1
  have hcρ : h.rho ⟨a⁻¹ * b, mul_mem (inv_mem haH) hbH⟩ = 1 := by
    show h.rho (⟨a, haH⟩⁻¹ * ⟨b, hbH⟩) = 1
    rw [map_mul, map_inv, hρ, inv_mul_cancel]
  have hcO : a⁻¹ * b ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    have h1 := h.rho_of_mem ⟨a⁻¹ * b, hcL⟩
    rw [show (⟨((⟨a⁻¹ * b, hcL⟩ : ↥L) : X), h.config.le_centralizer hcL⟩ :
        ↥(centralizer ({t} : Set X))) = ⟨a⁻¹ * b, mul_mem (inv_mem haH) hbH⟩ from rfl,
      hcρ] at h1
    have h2 : (QuotientGroup.mk ⟨a⁻¹ * b, hcL⟩ : Bar L) ∈ center (Bar L) := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (Bar L) => φ g) h1
      simp only [MulAut.one_apply, MulAut.conj_apply] at this
      calc g * QuotientGroup.mk ⟨a⁻¹ * b, hcL⟩ =
            QuotientGroup.mk ⟨a⁻¹ * b, hcL⟩ * g * (QuotientGroup.mk ⟨a⁻¹ * b, hcL⟩)⁻¹ *
              QuotientGroup.mk ⟨a⁻¹ * b, hcL⟩ := by rw [← this]
        _ = _ := by group
    rw [h.config.center_bar_eq_bot, mem_bot, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  exact exists_conj_of_mem_coset_odd
    (Nat.coprime_two_left.mp (coprime_card_map_pPrimeCore L)) ha2 hb2 hcO

theorem sq_mul_beta (hσ : Setup42 h hS w z) (i j : ℕ) {d : X} (hd : d ∈ S ⊓ L)
    (hd2 : d ^ 2 = 1) : (d * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ^ 2 = 1 := by
  have hc : Commute d (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    mem_centralizer_singleton_iff.mp (hσ.D_le_centralizer_beta i j hd)
  rw [hc.mul_pow, hd2, hσ.sq_eq_one_of_mem_X (beta_mem_X i j), one_mul]

theorem conj_beta_iff (hKC : AutPSL2CentralizerInput) (hFL : ∀ (Y : Type) [Group Y] [Finite Y] (p f
    : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 → Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut
    Y, IsFieldAutPSL2 k → ∀ y ∈ fixedPoints k, y ^ 2 = 1 → ((∃ g : Y, MulAut.conj g * k *
    (MulAut.conj g)⁻¹ = MulAut.conj y * k) ↔ (y = 1 ∨ y ∉ (perfectResidual ↥(fixedPoints k)).map
    (fixedPoints k).subtype)))
    (hσ : Setup42 h hS w z) (i j : ℕ) {d : X}
    (hd : d ∈ S ⊓ L) (hd2 : d ^ 2 = 1) :
    (∃ l ∈ L, l * (d * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * l⁻¹ =
        w ^ (orderOf w / 2) * t ^ i * z ^ j) ↔
      (d = 1 ∨ d ∉ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set K := centralizerResidual L β with hK
  have hβH := hσ.beta_mem_H i j
  have hβN := hσ.beta_mem_normalizer i j
  set κ := barAction L ⟨β, hβN⟩ with hκ
  have hdH : d ∈ centralizer ({t} : Set X) := hS.le hd.1
  have hdC : d ∈ L ⊓ centralizer {β} := hσ.D_le_CL i j hd
  set dbar : Bar L := QuotientGroup.mk ⟨d, hd.2⟩ with hdbar
  have hdfix : dbar ∈ fixedPoints κ := by
    rw [mem_fixedPoints, hκ, hdbar, barAction_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply]
    show β * d * β⁻¹ = d
    rw [← mem_centralizer_singleton_iff.mp hdC.2, mul_inv_cancel_right]
  have hdbar2 : dbar ^ 2 = 1 := by
    rw [hdbar, ← QuotientGroup.mk_pow,
      show (⟨d, hd.2⟩ : ↥L) ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, hd2]; rfl),
      QuotientGroup.mk_one]
  have hclass := hFL (Bar L) p f h.config.prime h.config.ne_two
    (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
    h.config.lieModel κ (hσ.isFieldAut_rho hKC i j hβH) dbar hdfix hdbar2
  have hrange := range_barMap_perfectResidual hβN (hσ.isPGroup_zpowers_beta i j)
  have hρdβ : h.rho ⟨d * β, mul_mem hdH hβH⟩ = MulAut.conj dbar * κ := by
    show h.rho (⟨d, hdH⟩ * ⟨β, hβH⟩) = _
    rw [map_mul, show (⟨d, hdH⟩ : ↥(centralizer ({t} : Set X))) =
      ⟨((⟨d, hd.2⟩ : ↥L) : X), h.config.le_centralizer hd.2⟩ from rfl, h.rho_of_mem, h.rho_apply]
  have hd1 : dbar = 1 ↔ d = 1 := by
    constructor
    · intro h1
      rw [hdbar, QuotientGroup.eq_one_iff] at h1
      have hdo : orderOf (⟨d, hd.2⟩ : ↥L) ∣ Nat.card (pPrimeCore 2 ↥L) := by
        rw [← Subgroup.orderOf_mk _ h1]
        exact orderOf_dvd_natCard _
      have h2 : orderOf (⟨d, hd.2⟩ : ↥L) ∣ 2 := orderOf_dvd_of_pow_eq_one
        (Subtype.ext (by rw [Subgroup.coe_pow, hd2]; rfl))
      have h3 := Nat.eq_one_of_dvd_coprimes
        (pPrimeCore_coprime_card (p := 2) (G := ↥L)) h2 hdo
      rw [orderOf_eq_one_iff] at h3
      exact congrArg Subtype.val h3
    · intro h1
      rw [hdbar]
      have : (⟨d, hd.2⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, QuotientGroup.mk_one]
  have hdK : dbar ∈ (perfectResidual ↥(fixedPoints κ)).map (fixedPoints κ).subtype ↔ d ∈ K := by
    rw [← hrange]
    constructor
    · exact mem_centralizerResidual_of_mk_mem hdC hd2
    · intro hdK'
      exact ⟨⟨d, hdK'⟩, rfl⟩
  rw [← hd1, ← hdK, ← hclass]
  constructor
  · rintro ⟨l, hl, hlβ⟩
    refine ⟨(QuotientGroup.mk ⟨l, hl⟩ : Bar L)⁻¹, ?_⟩
    have hlH : l ∈ centralizer ({t} : Set X) := h.config.le_centralizer hl
    have h1 := congrArg h.rho (show (⟨l, hlH⟩ : ↥(centralizer ({t} : Set X))) *
      ⟨d * β, mul_mem hdH hβH⟩ * ⟨l, hlH⟩⁻¹ = ⟨β, hβH⟩ from Subtype.ext hlβ)
    rw [map_mul, map_mul, map_inv, hρdβ, show (⟨l, hlH⟩ : ↥(centralizer ({t} : Set X))) =
      ⟨((⟨l, hl⟩ : ↥L) : X), h.config.le_centralizer hl⟩ from rfl, h.rho_of_mem] at h1
    have h1' : MulAut.conj (QuotientGroup.mk ⟨l, hl⟩ : Bar L) * (MulAut.conj dbar * κ) *
        (MulAut.conj (QuotientGroup.mk ⟨l, hl⟩ : Bar L))⁻¹ = κ := h1
    rw [map_inv, inv_inv]
    conv_lhs => rw [← h1']
    group
  · rintro ⟨g, hg⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective g
    have hlH : l ∈ centralizer ({t} : Set X) := h.config.le_centralizer hl
    have hρ : h.rho ⟨l⁻¹ * (d * β) * l, mul_mem (mul_mem (inv_mem hlH) (mul_mem hdH hβH)) hlH⟩ =
        h.rho ⟨β, hβH⟩ := by
      show h.rho (⟨l, hlH⟩⁻¹ * ⟨d * β, mul_mem hdH hβH⟩ * ⟨l, hlH⟩) = κ
      rw [map_mul, map_mul, map_inv, hρdβ, show (⟨l, hlH⟩ : ↥(centralizer ({t} : Set X))) =
        ⟨((⟨l, hl⟩ : ↥L) : X), h.config.le_centralizer hl⟩ from rfl, h.rho_of_mem, ← hg]
      group
    have haL : l⁻¹ * (d * β) * l * β⁻¹ ∈ L := by
      have h1 : β * l * β⁻¹ ∈ L := (mem_normalizer_iff.mp hβN l).mp hl
      rw [show l⁻¹ * (d * β) * l * β⁻¹ = l⁻¹ * d * (β * l * β⁻¹) by group]
      exact L.mul_mem (L.mul_mem (L.inv_mem hl) hd.2) h1
    have ha2 : (l⁻¹ * (d * β) * l) ^ 2 = 1 := by
      rw [show l⁻¹ * (d * β) * l = l⁻¹ * (d * β) * l⁻¹⁻¹ by rw [inv_inv], conj_pow,
        hσ.sq_mul_beta i j hd hd2, mul_one, mul_inv_cancel]
    obtain ⟨n, hnO, hn⟩ := hσ.exists_conj_of_rho_eq i j _ hβH haL
      (by rw [mul_inv_cancel]; exact one_mem L) ha2 (hσ.sq_eq_one_of_mem_X (beta_mem_X i j)) hρ
    have hnL : n ∈ L := map_subtype_le _ hnO
    refine ⟨n * l⁻¹, L.mul_mem hnL (L.inv_mem hl), ?_⟩
    calc n * l⁻¹ * (d * β) * (n * l⁻¹)⁻¹ = n * (l⁻¹ * (d * β) * l) * n⁻¹ := by group
      _ = β := hn

theorem conj_of_mem_Dstar (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) {d d' : X}
    (hd : d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hd' : d' ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hd1 : d ≠ 1) (hd2 : d ^ 2 = 1) (hd'1 : d' ≠ 1) (hd'2 : d' ^ 2 = 1) :
    ∃ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      k * (d * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * k⁻¹ =
        d' * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set K := centralizerResidual L β with hK
  have hL := hσ.lieModel_bar_K hFC hKC i j
  have hOodd : Odd (Nat.card ((pPrimeCore 2 ↥K).map K.subtype)) :=
    Nat.coprime_two_left.mp (coprime_card_map_pPrimeCore K)
  have himg : ∀ {x : X} (hx : x ∈ K), x ≠ 1 → x ^ 2 = 1 →
      (QuotientGroup.mk ⟨x, hx⟩ : Bar K) ≠ 1 ∧ (QuotientGroup.mk ⟨x, hx⟩ : Bar K) ^ 2 = 1 := by
    intro x hx hx1 hx2
    refine ⟨fun h1 => hx1 ?_, ?_⟩
    · rw [QuotientGroup.eq_one_iff] at h1
      have hdo : orderOf (⟨x, hx⟩ : ↥K) ∣ Nat.card (pPrimeCore 2 ↥K) := by
        rw [← Subgroup.orderOf_mk _ h1]
        exact orderOf_dvd_natCard _
      have h2 : orderOf (⟨x, hx⟩ : ↥K) ∣ 2 := orderOf_dvd_of_pow_eq_one
        (Subtype.ext (by rw [Subgroup.coe_pow, hx2]; rfl))
      have h3 := Nat.eq_one_of_dvd_coprimes
        (pPrimeCore_coprime_card (p := 2) (G := ↥K)) h2 hdo
      rw [orderOf_eq_one_iff] at h3
      exact congrArg Subtype.val h3
    · rw [← QuotientGroup.mk_pow,
        show (⟨x, hx⟩ : ↥K) ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, hx2]; rfl),
        QuotientGroup.mk_one]
  obtain ⟨h1a, h1b⟩ := himg hd.2 hd1 hd2
  obtain ⟨h2a, h2b⟩ := himg hd'.2 hd'1 hd'2
  obtain ⟨gbar, hgbar⟩ := exists_conj_of_lieModel_psl2 h.config.ne_two hL h1a h1b h2a h2b
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gbar
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hgbar
  set o : X := d'⁻¹ * ((g : X) * d * (g : X)⁻¹) with ho
  have hoO : o ∈ (pPrimeCore 2 ↥K).map K.subtype := by
    refine ⟨_, (pPrimeCore 2 ↥K).inv_mem hgbar, ?_⟩
    show ((((g : X) * d * (g : X)⁻¹)⁻¹ * d')⁻¹ : X) = o
    rw [ho]
    group
  have hgβ : (g : X) * β = β * g :=
    mem_centralizer_singleton_iff.mp (centralizerResidual_le g.2).2
  have hx2 : (d' * β) ^ 2 = 1 := hσ.sq_mul_beta i j hd'.1 hd'2
  have hy2 : ((g : X) * (d * β) * (g : X)⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hσ.sq_mul_beta i j hd.1 hd2, mul_one, mul_inv_cancel]
  have hxy : (d' * β)⁻¹ * ((g : X) * (d * β) * (g : X)⁻¹) ∈
      (pPrimeCore 2 ↥K).map K.subtype := by
    have hoβ : β⁻¹ * o * β = o := by
      have hoK : o ∈ K := map_subtype_le _ hoO
      rw [mul_assoc, mem_centralizer_singleton_iff.mp (centralizerResidual_le hoK).2,
        inv_mul_cancel_left]
    rw [show (d' * β)⁻¹ * ((g : X) * (d * β) * (g : X)⁻¹) = β⁻¹ * o * β by
      rw [ho, show (g : X) * (d * β) * (g : X)⁻¹ = (g : X) * d * (g : X)⁻¹ * ((g : X) * β *
        (g : X)⁻¹) by group, hgβ, mul_inv_cancel_right]
      group, hoβ]
    exact hoO
  obtain ⟨n, hnO, hn⟩ := exists_conj_of_mem_coset_odd hOodd hx2 hy2 hxy
  have hnK : n ∈ K := map_subtype_le _ hnO
  refine ⟨n⁻¹ * g, K.mul_mem (K.inv_mem hnK) g.2, ?_⟩
  rw [show n⁻¹ * (g : X) * (d * β) * (n⁻¹ * g)⁻¹ =
    n⁻¹ * ((g : X) * (d * β) * (g : X)⁻¹) * n by group, ← hn]
  group

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
