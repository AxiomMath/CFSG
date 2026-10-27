module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MSide
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Borel
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankThreeTheoremC (exists_orderOf_pow_eq zpowers_eq_of_orderOf_eq_of_isCyclic)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_primeCore_le_centralizer_layer [Fact p.Prime] (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) :
    CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)) ≤
      centralizer ((layerOf x : Subgroup G) : Set G) := by
  refine fr_lemmaQ hG hl (CFSG.AGLEmbedding.glbPrimeCore_coprime p (centralizer ({x} : Set G)))
    ((CFSG.AGLEmbedding.glbPrimeCore_le p _).trans (fr_layer_normal_in_centralizer x)) ?_
  intro g hg
  exact CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p (centralizer ({x} : Set G))
    (fr_P_le_centralizer hl hg.1)

theorem fr_cyclic_coprime_centralizes {H : Type*} [Group H] {p : ℕ} [hp : Fact p.Prime]
    {S : Subgroup H} [Finite S] (hS : IsPGroup p S) (hSc : IsCyclic S) {x : H} (hxS : x ∈ S)
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) {g : H} (hgN : g ∈ normalizer (S : Set H))
    (hgx : g * x * g⁻¹ = x) {m : ℕ} (hm : Nat.Coprime p m)
    (hgm : g ^ m ∈ centralizer (S : Set H)) : g ∈ centralizer (S : Set H) := by
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : S) ⟨b, hb⟩)
  have hfixx : ∀ t ∈ zpowers x, g * t * g⁻¹ = t := by
    intro t ht
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    rw [← conj_zpow, hgx]
  have key : ∀ e : ℕ, ∀ s ∈ S, orderOf s = p ^ e → g * s * g⁻¹ = s := by
    intro e
    induction e with
    | zero =>
      intro s _ hs
      rw [pow_zero, orderOf_eq_one_iff] at hs
      rw [hs]
      group
    | succ e ih =>
      intro s hsS hso
      have hsp : orderOf (s ^ p) = p ^ e := by
        rw [orderOf_pow_of_dvd hp.out.ne_zero (hso ▸ dvd_pow_self p (Nat.succ_ne_zero e)), hso,
          pow_succ, Nat.mul_div_cancel _ hp.out.pos]
      have hspS : s ^ p ∈ S := pow_mem hsS p
      have h1 : g * s ^ p * g⁻¹ = s ^ p := ih _ hspS hsp
      have hgsS : g * s * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgN s).mp hsS
      set t := g * s * g⁻¹ * s⁻¹ with ht
      have htS : t ∈ S := S.mul_mem hgsS (S.inv_mem hsS)
      have htp : t ^ p = 1 := by
        have hc : Commute (g * s * g⁻¹) s⁻¹ := hcomm _ hgsS _ (S.inv_mem hsS)
        have h2 : (g * s * g⁻¹) ^ p = s ^ p := by
          rw [conj_pow, h1]
        rw [ht, hc.mul_pow, inv_pow, h2, mul_inv_cancel]
      have htx : t ∈ zpowers x := by
        by_cases ht1 : t = 1
        · rw [ht1]; exact one_mem _
        · have hto : orderOf t = p := orderOf_eq_prime htp ht1
          rw [zpowers_eq_of_orderOf_eq_of_isCyclic hSc hxS htS (by rw [hxo, hto])]
          exact mem_zpowers t
      have hgt : g * t * g⁻¹ = t := hfixx t htx
      have hgst : g * s * g⁻¹ = t * s := by rw [ht]; group
      have hpow : ∀ r : ℕ, g ^ r * s * (g ^ r)⁻¹ = t ^ r * s := by
        intro r
        induction r with
        | zero => simp
        | succ r ihr =>
          have hgtr : g * t ^ r * g⁻¹ = t ^ r := by rw [← conj_pow, hgt]
          calc g ^ (r + 1) * s * (g ^ (r + 1))⁻¹ = g * (g ^ r * s * (g ^ r)⁻¹) * g⁻¹ := by group
            _ = g * (t ^ r * s) * g⁻¹ := by rw [ihr]
            _ = (g * t ^ r * g⁻¹) * (g * s * g⁻¹) := by group
            _ = t ^ (r + 1) * s := by rw [hgtr, hgst, pow_succ]; group
      have hgms : g ^ m * s * (g ^ m)⁻¹ = s := by
        have := mem_centralizer_iff.mp hgm s hsS
        rw [← this]
        group
      have htm : t ^ m = 1 := by
        have h2 := hpow m
        rw [hgms] at h2
        exact (mul_eq_right.mp h2.symm)
      have ht1 : t = 1 := by
        have hd : orderOf t = 1 := Nat.eq_one_of_dvd_coprimes hm (orderOf_dvd_of_pow_eq_one htp)
          (orderOf_dvd_of_pow_eq_one htm)
        exact orderOf_eq_one_iff.mp hd
      rw [hgst, ht1, one_mul]
  refine mem_centralizer_iff.mpr fun s hs => ?_
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨s, hs⟩
  have hso : orderOf s = p ^ e := by simpa using he
  have h := key e s hs hso
  calc s * g = (g * s * g⁻¹) * g := by rw [h]
    _ = g * s := by group

open CFSG.ABGLocalTools in
theorem fr_normalizer_le_centralizer_cyclic_sylow {H : Type*} [Group H] [Finite H] {p : ℕ}
    [hp : Fact p.Prime] (S : Sylow p H) (hSc : IsCyclic (S : Subgroup H)) {x : H}
    (hxS : x ∈ (S : Subgroup H)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hx : ∀ g ∈ normalizer ((S : Subgroup H) : Set H), g * x * g⁻¹ = x) :
    normalizer ((S : Subgroup H) : Set H) ≤ centralizer ((S : Subgroup H) : Set H) := by
  intro g hgN
  obtain ⟨c, m, hm, hcm, hmo, hpo⟩ := exists_orderOf_pow_eq p hp.out g
  have hSp : IsPGroup p (S : Subgroup H) := S.isPGroup'
  have hgmN : g ^ m ∈ normalizer ((S : Subgroup H) : Set H) := pow_mem hgN m
  have hW : IsPGroup p ↥(zpowers (g ^ m) ⊔ (S : Subgroup H)) :=
    IsPGroup.to_sup_of_normal_right' (IsPGroup.of_card (by rw [Nat.card_zpowers, hmo])) hSp
      (zpowers_le.mpr hgmN)
  have hSsyl : IsSylowOf p (S : Subgroup H) ⊤ :=
    isSylowOf_iff.2 ⟨le_top, S.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index⟩
  have hWS := hSsyl.eq_of_le le_sup_right le_top hW
  have hgmS : g ^ m ∈ (S : Subgroup H) :=
    hWS ▸ (le_sup_left : zpowers (g ^ m) ≤ zpowers (g ^ m) ⊔ (S : Subgroup H)) (mem_zpowers _)
  have hgmC : g ^ m ∈ centralizer ((S : Subgroup H) : Set H) :=
    mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : (S : Subgroup H)) ⟨g ^ m, hgmS⟩)
  have hgpN : g ^ (p ^ c) ∈ normalizer ((S : Subgroup H) : Set H) := pow_mem hgN _
  have hgpC : g ^ (p ^ c) ∈ centralizer ((S : Subgroup H) : Set H) :=
    fr_cyclic_coprime_centralizes hSp hSc hxS hx1 hxp hgpN (hx _ hgpN)
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
      (by
        rw [← pow_mul, ← hcm, pow_orderOf_eq_one]
        exact one_mem _)
  have hcop : IsCoprime ((p ^ c : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))
  obtain ⟨a, b, hab⟩ := hcop
  have hab' : ((p ^ c : ℕ) : ℤ) * a + (m : ℤ) * b = 1 := by linarith
  have hg : g = (g ^ (p ^ c)) ^ a * (g ^ m) ^ b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hab', zpow_one]
  have h := mul_mem (zpow_mem hgpC a) (zpow_mem hgmC b)
  rwa [← hg] at h

theorem fr_pComplement_le_primeCore [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {Y : Subgroup G}
    (hY : Y ≤ centralizer ({x} : Set G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G))
    (hYp : Nat.Coprime p (Nat.card Y)) :
    Y ≤ CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)) := by
  have hp : p.Prime := Fact.out
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := C ⊓ centralizer ((layerOf x : Subgroup G) : Set G) with hD
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hxD : x ∈ D := ⟨hxC, (fr_x_mem_Z0 hl).2⟩
  have hDC : D ≤ C := inf_le_left
  have hCD : C ≤ normalizer (D : Set G) := by
    have h1 : C ≤ normalizer (C : Set G) := le_normalizer
    have h2 : C ≤ normalizer ((centralizer ((layerOf x : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      (fr_layer_normal_in_centralizer x).trans (frN_normalizer_centralizer_le _)
    intro c hc
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1 hc, h2 hc⟩
  set x' : D := ⟨x, hxD⟩ with hx'
  have hx'o : orderOf x' = p := by
    rw [hx', Subgroup.orderOf_mk]
    exact hl.point.elem.2.1
  have hx'1 : x' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx'o
    exact hp.one_lt.ne hx'o
  have hx'p : x' ^ p = 1 := by
    rw [← hx'o]
    exact pow_orderOf_eq_one x'
  obtain ⟨S, hxS⟩ := (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o, pow_one]) :
    IsPGroup p (zpowers x')).exists_le_sylow
  have hx'S : x' ∈ (S : Subgroup D) := hxS (mem_zpowers x')
  have hSc : IsCyclic (S : Subgroup D) := by
    have hle : (S : Subgroup D).map D.subtype ≤
        centralizer ((zpowers x : Subgroup G) : Set G) ⊓
          centralizer ((layerOf x : Subgroup G) : Set G) := by
      rintro _ ⟨s, -, rfl⟩
      exact ⟨by rw [centralizer_zpowers_eq]; exact s.2.1, s.2.2⟩
    have hcyc := hl.cyclic _ hle (S.isPGroup'.map D.subtype)
    exact (Subgroup.equivMapOfInjective (S : Subgroup D) D.subtype D.subtype_injective).isCyclic.mpr
      hcyc
  have hNC : normalizer ((S : Subgroup D) : Set D) ≤ centralizer ((S : Subgroup D) : Set D) :=
    fr_normalizer_le_centralizer_cyclic_sylow S hSc hx'S hx'1 hx'p fun g _ => by
      refine Subtype.ext ?_
      have h := mem_centralizer_singleton_iff.mp g.2.1
      change (g : G) * x * (g : G)⁻¹ = x
      rw [h, mul_inv_cancel_right]
  set K : Subgroup D := (MonoidHom.transferSylow S hNC).ker with hK
  have hKc : K.IsComplement' (S : Subgroup D) := MonoidHom.ker_transferSylow_isComplement' S hNC
  have hpel : ∀ d : D, ¬ p ∣ orderOf d → d ∈ K := by
    intro d hd
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' (MonoidHom.transferSylow S hNC d)
    have hdvd : orderOf (MonoidHom.transferSylow S hNC d) ∣ orderOf d := orderOf_map_dvd _ d
    have hk0 : k = 0 := by
      by_contra hne
      exact hd ((dvd_pow_self p hne).trans (hk ▸ hdvd))
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact MonoidHom.mem_ker.mpr hk
  have hKcop : Nat.Coprime p (Nat.card K) := by
    have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hS0 : Nat.card (S : Subgroup D) ≠ 0 := Nat.card_pos.ne'
    have hfac := congrArg (fun n => n.factorization p) hKc.card_mul_card
    simp only [Nat.factorization_mul hK0 hS0, Finsupp.add_apply] at hfac
    rw [S.card_eq_multiplicity, hp.factorization_pow] at hfac
    have h0 : (Nat.card K).factorization p = 0 := by
      have : Finsupp.single p ((Nat.card D).factorization p) p = (Nat.card D).factorization p := by simp
      omega
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
    have := hp.factorization_pos_of_dvd hK0 hdvd
    omega
  set K' : Subgroup G := K.map D.subtype with hK'
  have hK'D : K' ≤ D := map_subtype_le K
  have hK'cop : Nat.Coprime p (Nat.card K') := by
    rw [hK', Subgroup.card_map_of_injective D.subtype_injective]
    exact hKcop
  have hmem : ∀ y : G, y ∈ D → ¬ p ∣ orderOf y → y ∈ K' := fun y hyD hy =>
    ⟨⟨y, hyD⟩, hpel ⟨y, hyD⟩ (by rwa [Subgroup.orderOf_mk]), rfl⟩
  have hnormK : C ≤ normalizer (K' : Set G) := by
    have key : ∀ c ∈ C, ∀ k ∈ K', c * k * c⁻¹ ∈ K' := by
      intro c hc k hk
      have hkD : k ∈ D := hK'D hk
      have hckD : c * k * c⁻¹ ∈ D := (mem_normalizer_iff.mp (hCD hc) k).mp hkD
      refine hmem _ hckD ?_
      have hord : orderOf (c * k * c⁻¹) = orderOf k := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      rw [hord]
      intro hdvd
      have h1 : orderOf k ∣ Nat.card K' := Subgroup.orderOf_dvd_natCard K' hk
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hK'cop) (hdvd.trans h1)
    intro c hc
    rw [mem_normalizer_iff]
    intro k
    refine ⟨key c hc k, fun hk => ?_⟩
    have := key c⁻¹ (inv_mem hc) _ hk
    simpa [mul_assoc] using this
  have hYK : Y ≤ K' := by
    intro y hy
    refine hmem y (hY hy) ?_
    intro hdvd
    have h1 : orderOf y ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hy
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hYp) (hdvd.trans h1)
  exact hYK.trans (CFSG.AGLEmbedding.le_glbPrimeCore (hK'D.trans hDC) hnormK hK'cop)

theorem fr_primeCore_inf_centralizer_le_centralizer_layer [Fact p.Prime] (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) :
    CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G) ≤
      centralizer ((layerOf x : Subgroup G) : Set G) := by
  set R : Subgroup G := CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G) with hR
  have hRp : Nat.Coprime p (Nat.card R) :=
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p M).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)
  have hRL : R ≤ normalizer ((layerOf x : Subgroup G) : Set G) :=
    inf_le_right.trans (fr_layer_normal_in_centralizer x)
  have hUR : frU P x ≤ normalizer (R : Set G) := by
    intro g hg
    have hgP : g ∈ (P : Subgroup G) := hg.1
    have hgM : g ∈ M := fr_P_le_M hl hgP
    have h1 : g ∈ normalizer ((CFSG.Open.GLBPrimeCore p M : Subgroup G) : Set G) :=
      CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M hgM
    have h2 : g ∈ normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) :=
      le_normalizer (fr_P_le_centralizer hl hgP)
    rw [hR]
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(h1 y).mp hy1, (h2 y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(h1 y).mpr hy1, (h2 y).mpr hy2⟩
  exact fr_lemmaQ hG hl hRp hRL hUR

theorem fr_primeCore_inf_centralizer_odd [Fact p.Prime] (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) :
    ¬ 2 ∣ Nat.card ↥(CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G)) := by
  intro h2
  have hodd := fr_centralizer_layer_odd hG hl
  have hdvd : Nat.card ↥(CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G)) ∣
      Nat.card (centralizer ((layerOf x : Subgroup G) : Set G)) :=
    Subgroup.card_dvd_of_le (fr_primeCore_inf_centralizer_le_centralizer_layer hG hl)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))

theorem fr_primeCore_centralizer_odd [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    ¬ 2 ∣ Nat.card ↥(CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G))) := by
  intro h2
  have hodd := fr_centralizer_layer_odd hG hl
  have hdvd : Nat.card ↥(CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G))) ∣
      Nat.card (centralizer ((layerOf x : Subgroup G) : Set G)) :=
    Subgroup.card_dvd_of_le (fr_primeCore_le_centralizer_layer hG hl)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))

theorem fr_primeCore_inf_centralizer_le [Fact p.Prime] (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) :
    CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G) ≤
      CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)) :=
  fr_pComplement_le_primeCore hG hl
    (le_inf inf_le_right (fr_primeCore_inf_centralizer_le_centralizer_layer hG hl))
    ((CFSG.AGLEmbedding.glbPrimeCore_coprime p M).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left))

theorem fr_pCore_inf_centralizer_eq_bot [Fact p.Prime] (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) :
    CFSG.Open.pCoreOf 2 M ⊓ centralizer ({x} : Set G) = ⊥ := by
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  have hTF : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.GLBPrimeCore p M :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pCoreOf_two_le_rankThreePrimeCore Fact.out hp2 M
  have hT2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hodd := fr_primeCore_inf_centralizer_odd hG hl
  rw [eq_bot_iff]
  intro t ht
  have htF : t ∈ CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G) := ⟨hTF ht.1, ht.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨t, ht.1⟩
  have hk' : orderOf t = 2 ^ k := by simpa using hk
  have hdvd : orderOf t ∣ Nat.card ↥(CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G)) := by
    have := Subgroup.orderOf_dvd_natCard _ htF
    simpa using this
  have hk0 : k = 0 := by
    by_contra hne
    exact hodd (dvd_trans (hk' ▸ dvd_pow_self 2 hne) hdvd)
  rw [hk0, pow_zero] at hk'
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hk')

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
