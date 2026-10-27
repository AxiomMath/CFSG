module

public import CFSG.GH74.GLS.C3.Layer1.U1aMain
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness
open scoped commutatorElement

variable {G : Type} [Group G] {M L T Q : Subgroup G}

theorem one_le_pRank_zpowers [Finite G] {y : G} (hy : orderOf y = 2) :
    1 ≤ CFSG.pRank 2 ↥(zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : ↥(zpowers y) := ⟨y, mem_zpowers y⟩
  have hg : orderOf g = 2 := by rw [Subgroup.orderOf_mk]; exact hy
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two (zpowers g)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 (zpowers g)).2
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary g hg))
    (k := 1) (by rw [Nat.card_zpowers, hg, pow_one])

theorem centralizer_le_gammaK [Finite G] {y : G} (hyQ : y ∈ Q) (hy : orderOf y = 2) :
    centralizer ({y} : Set G) ≤ gammaK 2 Q 1 := by
  have hcn : centralizer ({y} : Set G) ≤ normalizer (zpowers y : Set G) := by
    intro c hc
    rw [mem_centralizer_singleton_iff] at hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      have hcy : c * y * c⁻¹ = y := by
        calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [hc]
          _ = y := by group
      have : c * y ^ k * c⁻¹ = y ^ k := by
        calc c * y ^ k * c⁻¹ = (c * y * c⁻¹) ^ k := conj_zpow.symm
          _ = y ^ k := by rw [hcy]
      rw [this]
      exact mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro hh
      have hcy : c⁻¹ * y * c = y := by
        calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
          _ = c⁻¹ * (c * y) := by rw [hc]
          _ = y := by group
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hh
      have : h = (c⁻¹ * y * c) ^ k := by
        have hcj := conj_zpow (a := c⁻¹) (b := y) (i := k)
        simp only [inv_inv] at hcj
        calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
          _ = c⁻¹ * y ^ k * c := by rw [← hk]
          _ = (c⁻¹ * y * c) ^ k := hcj.symm
      rw [this, hcy]
      exact mem_zpowers_iff.mpr ⟨k, rfl⟩
  refine hcn.trans ?_
  unfold gammaK
  exact le_iSup₂_of_le (zpowers y) (zpowers_le.mpr hyQ)
    (le_iSup_of_le (one_le_pRank_zpowers hy) le_rfl)

theorem centralizer_le_of_sylow_pointwise [Finite G]
    {M W Q : Subgroup G} (hQ : IsSylowOf 2 Q W) (hWM : W ≤ M)
    (hpre : ∀ q ∈ Q, orderOf q = 2 → centralizer ({q} : Set G) ≤ M) :
    ∀ w ∈ W, orderOf w = 2 → centralizer ({w} : Set G) ≤ M := by
  intro w hwW hw2
  obtain ⟨k, hkW, hk⟩ := exists_conj_involution_mem hQ hwW hw2
  have hw'2 : orderOf (k⁻¹ * w * k) = 2 := (orderOf_conj_eq k).trans hw2
  have hcent := hpre (k⁻¹ * w * k) hk hw'2
  intro c hc
  have hc' : k⁻¹ * c * k ∈ centralizer ({k⁻¹ * w * k} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    calc k⁻¹ * c * k * (k⁻¹ * w * k) = k⁻¹ * (c * w) * k := by group
      _ = k⁻¹ * (w * c) * k := by rw [hc]
      _ = k⁻¹ * w * k * (k⁻¹ * c * k) := by group
  have hM1 : k⁻¹ * c * k ∈ M := hcent hc'
  have hkM : k ∈ M := hWM hkW
  have := M.mul_mem (M.mul_mem hkM hM1) (M.inv_mem hkM)
  simpa [mul_assoc] using this

theorem centralizer_le_of_gammaK [Finite G] (hQ : IsSylowOf 2 Q (CMK M L))
    (hpre : gammaK 2 Q 1 ≤ M) :
    ∀ y ∈ CMK M L, orderOf y = 2 → centralizer ({y} : Set G) ≤ M := by
  refine centralizer_le_of_sylow_pointwise hQ ?_ ?_
  · show CMK M L ≤ M
    exact inf_le_left
  · intro q hq hq2
    exact (centralizer_le_gammaK hq hq2).trans hpre

theorem mem_normalizer_of_norm (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {m : G} (hm : m ∈ M) :
    m ∈ normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hLnorm m hm h, fun hh => ?_⟩
  have := hLnorm m⁻¹ (M.inv_mem hm) _ hh
  simpa [mul_assoc] using this

theorem mem_normalizer_pPrimeCoreOf (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {m : G}
    (hm : m ∈ M) : m ∈ normalizer (pPrimeCoreOf 2 L : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥L)
    (mem_normalizer_of_norm hLnorm hm)

theorem pPrimeCoreOf_norm (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {m : G} (hm : m ∈ M)
    {n : G} (hn : n ∈ pPrimeCoreOf 2 L) : m * n * m⁻¹ ∈ pPrimeCoreOf 2 L :=
  ((Subgroup.mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf hLnorm hm) n).mp hn)

theorem mem_CMK_iff {c : G} :
    c ∈ CMK M L ↔ c ∈ M ∧ c ∈ normalizer (L : Set G) ∧ c ∈ normalizer (pPrimeCoreOf 2 L : Set G) ∧
      ∀ k ∈ L, ⁅k, c⁆ ∈ pPrimeCoreOf 2 L :=
  Iff.rfl

theorem Setup.ofConcrete [Finite G] (hM : M ≠ ⊤) (hLM : L ≤ M)
    (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hLn : ∃ a b : ↥L ⧸ pPrimeCore 2 ↥L, a * b ≠ b * a)
    (hQ : IsSylowOf 2 Q (CMK M L)) (hT : IsSylowOf 2 T M) (hQT : Q ≤ T)
    (hQ2 : 2 ≤ CFSG.pRank 2 ↥Q)
    (hpre : ∀ y ∈ CMK M L, orderOf y = 2 → centralizer ({y} : Set G) ≤ M) :
    Setup M L (pPrimeCoreOf 2 L) (CMK M L) Q T where
  M_ne_top := hM
  M_not_solvable := by
    intro hsolv
    have hLs' : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
    have hbar : Group.IsSolvable (↥L ⧸ pPrimeCore 2 ↥L) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    obtain ⟨a, b, hab⟩ := hLn
    have := hLs
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hbar) a b)
  L_le := hLM
  L_norm := hLnorm
  N_le := TwoThin.pPrimeCoreOf_le L
  N_odd := TwoThin.card_pPrimeCoreOf_odd L
  N_norm := fun m hm n hn => pPrimeCoreOf_norm hLnorm hm hn
  N_max := by
    intro N' hN'L hN'norm hN'odd
    have hN'n : (N'.subgroupOf L).Normal := ⟨fun a ha h => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using hN'norm (h : G) h.2 (a : G) ha⟩
    have hcop : Nat.Coprime 2 (Nat.card ↥(N'.subgroupOf L)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN'L).toEquiv]
      exact Nat.coprime_two_left.2 hN'odd
    have hle : N'.subgroupOf L ≤ pPrimeCore 2 ↥L :=
      CFSG.GroupTheory.le_pPrimeCore_of_normal hN'n hcop
    rw [← Subgroup.map_subgroupOf_eq_of_le hN'L]
    exact Subgroup.map_mono hle
  W_le := inf_le_left
  W_norm := by
    intro m hm w hw
    obtain ⟨hwM, hwL, hwN, hwc⟩ := mem_CMK_iff.mp hw
    refine mem_CMK_iff.mpr ⟨M.mul_mem (M.mul_mem hm hwM) (M.inv_mem hm), ?_, ?_, ?_⟩
    · exact (normalizer (L : Set G)).mul_mem
        ((normalizer (L : Set G)).mul_mem (mem_normalizer_of_norm hLnorm hm) hwL)
        ((normalizer (L : Set G)).inv_mem (mem_normalizer_of_norm hLnorm hm))
    · exact (normalizer (pPrimeCoreOf 2 L : Set G)).mul_mem
        ((normalizer (pPrimeCoreOf 2 L : Set G)).mul_mem (mem_normalizer_pPrimeCoreOf hLnorm hm) hwN)
        ((normalizer (pPrimeCoreOf 2 L : Set G)).inv_mem (mem_normalizer_pPrimeCoreOf hLnorm hm))
    · intro k hk
      have hk' : m⁻¹ * k * m ∈ L := by
        have := hLnorm m⁻¹ (M.inv_mem hm) k hk
        simpa using this
      have h1 := hwc _ hk'
      have h2 := pPrimeCoreOf_norm hLnorm hm h1
      have e : ⁅k, m * w * m⁻¹⁆ = m * ⁅m⁻¹ * k * m, w⁆ * m⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact h2
  W_comm := by
    intro w hw l hl
    obtain ⟨hwM, -, -, hwc⟩ := mem_CMK_iff.mp hw
    have h1 := hwc l⁻¹ (L.inv_mem hl)
    have h2 := pPrimeCoreOf_norm hLnorm (hLM hl) h1
    have e : l * ⁅l⁻¹, w⁆ * l⁻¹ = w * l * w⁻¹ * l⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [← e]
    exact h2
  W_full := by
    intro m hm hcomm
    refine mem_CMK_iff.mpr ⟨hm, mem_normalizer_of_norm hLnorm hm,
      mem_normalizer_pPrimeCoreOf hLnorm hm, fun k hk => ?_⟩
    have h1 := (pPrimeCoreOf 2 L).inv_mem (hcomm k hk)
    have e : (m * k * m⁻¹ * k⁻¹)⁻¹ = ⁅k, m⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h1
  LW := by
    intro v hvL hvW hv2
    obtain ⟨hvM, -, -, hvc⟩ := mem_CMK_iff.mp hvW
    have := hLs
    have hcenter : (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
        Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
      have h1 := hvc (x₀ : G) x₀.2
      obtain ⟨y₀, hy₀, hy₀eq⟩ := h1
      have h2 : x₀ * ⟨v, hvL⟩ * x₀⁻¹ * ⟨v, hvL⟩⁻¹ = y₀ := by
        apply Subtype.ext
        simpa [commutatorElement_def] using hy₀eq.symm
      have h3 : (QuotientGroup.mk (x₀ * ⟨v, hvL⟩ * x₀⁻¹ * ⟨v, hvL⟩⁻¹) :
          ↥L ⧸ pPrimeCore 2 ↥L) = 1 := by
        rw [h2]
        exact (QuotientGroup.eq_one_iff _).mpr hy₀
      have h4 : (QuotientGroup.mk x₀ : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk ⟨v, hvL⟩ *
          (QuotientGroup.mk x₀)⁻¹ * (QuotientGroup.mk ⟨v, hvL⟩)⁻¹ = 1 := by
        rw [← h3]; simp
      calc (QuotientGroup.mk x₀ : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk ⟨v, hvL⟩
          = ((QuotientGroup.mk x₀ * QuotientGroup.mk ⟨v, hvL⟩ * (QuotientGroup.mk x₀)⁻¹ *
              (QuotientGroup.mk ⟨v, hvL⟩)⁻¹) * (QuotientGroup.mk ⟨v, hvL⟩ * QuotientGroup.mk x₀))
            := by group
        _ = QuotientGroup.mk ⟨v, hvL⟩ * QuotientGroup.mk x₀ := by rw [h4, one_mul]
    have hcb : Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := by
      rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hLn
        have ha : a ∈ Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) := h ▸ Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    rw [hcb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcenter
    have hvN : v ∈ pPrimeCoreOf 2 L := ⟨⟨v, hvL⟩, hcenter, rfl⟩
    have hodd := TwoThin.card_pPrimeCoreOf_odd L
    have hdvd : orderOf (⟨v, hvN⟩ : ↥(pPrimeCoreOf 2 L)) ∣ Nat.card ↥(pPrimeCoreOf 2 L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hv2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  sylowQ := hQ
  sylowT := hT
  Q_le_T := hQT
  rankQ := exists_commuting_involutions hQ2
  preuniq := hpre

theorem exists_conj_inter_rank_two_normal_of_corZD [Finite G] (hCor : S_CorZD)
    (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a) (hM : M ≠ ⊤) (hLM : L ≤ M)
    (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hLn : ∃ a b : ↥L ⧸ pPrimeCore 2 ↥L, a * b ≠ b * a)
    (hQ : IsSylowOf 2 Q (CMK M L)) (hT : IsSylowOf 2 T M) (hQT : Q ≤ T)
    (hQ2 : 2 ≤ CFSG.pRank 2 ↥Q) (hpre : gammaK 2 Q 1 ≤ M) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) :=
  (Setup.ofConcrete hM hLM hLnorm hLs hLn hQ hT hQT hQ2
    (centralizer_le_of_gammaK hQ hpre)).exists_conj_inter hCor hG hnon

theorem exists_conj_inter_rank_two_normal_of_preuniq [Finite G] (hCor : S_CorZD)
    (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a) (hM : M ≠ ⊤) (hLM : L ≤ M)
    (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hLn : ∃ a b : ↥L ⧸ pPrimeCore 2 ↥L, a * b ≠ b * a)
    (hQ : IsSylowOf 2 Q (CMK M L)) (hQ2 : 2 ≤ CFSG.pRank 2 ↥Q)
    (hpre : ∀ y ∈ CMK M L, orderOf y = 2 → centralizer ({y} : Set G) ≤ M) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) := by
  have hQM : Q ≤ M := hQ.le.trans (inf_le_left : CMK M L ≤ M)
  obtain ⟨S, hS⟩ := (hQ.isPGroup.comap_subtype (K := M)).exists_le_sylow
  let T : Subgroup G := (S : Subgroup M).map M.subtype
  have hT : IsSylowOf 2 T M := ⟨S, rfl⟩
  have hQT : Q ≤ T := by
    intro q hq
    exact ⟨⟨q, hQM hq⟩, hS (show (⟨q, hQM hq⟩ : M) ∈ Q.subgroupOf M from hq), rfl⟩
  exact (Setup.ofConcrete hM hLM hLnorm hLs hLn hQ hT hQT hQ2 hpre).exists_conj_inter hCor hG hnon

end CFSG.GH74.GLS.C3.Layer1.U1a
