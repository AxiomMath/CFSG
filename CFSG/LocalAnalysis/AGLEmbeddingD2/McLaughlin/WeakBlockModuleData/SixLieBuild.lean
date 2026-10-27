module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeAutomizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.TRoute
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Single
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem irreducibleOn_of_subgroupOf {G : Type} [Group G] {H M R : Subgroup G} (hRH : R ≤ H)
    (h : IrreducibleOn ((H ⊓ M).subgroupOf H ⊓
      Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H)) (R.subgroupOf H)) :
    IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R := by
  intro W hWR hWN
  have hWH : W ≤ H := hWR.trans hRH
  have key : W.subgroupOf H = ⊥ ∨ W.subgroupOf H = R.subgroupOf H := by
    refine h (W.subgroupOf H)
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hWR (Subgroup.mem_subgroupOf.mp hx))) ?_
    intro n hn
    have hnHM : (n : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hn.1
    have hnR : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      by_cases hg : g ∈ H
      · have := (Subgroup.mem_normalizer_iff.mp hn.2) ⟨g, hg⟩
        simpa [Subgroup.mem_subgroupOf] using this
      · have hgR : g ∉ R := fun hgR => hg (hRH hgR)
        have h2 : (n : G) * g * (n : G)⁻¹ ∉ R := fun hh => by
          have hH' : (n : G) * g * (n : G)⁻¹ ∈ H := hRH hh
          apply hg
          have := H.mul_mem (H.mul_mem (H.inv_mem n.2) hH') n.2
          simpa [mul_assoc] using this
        exact ⟨fun hh => absurd hh hgR, fun hh => absurd hh h2⟩
    have hnW := hWN ⟨hnHM, hnR⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.mp hnW) (x : G)
    simpa [Subgroup.mem_subgroupOf] using this
  rcases key with h0 | h1
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le hWH, h0, Subgroup.map_bot]
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hWH, h1, Subgroup.map_subgroupOf_eq_of_le hRH]

@[expose] def PairOmega8S6Residue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    NineThreeTwo M (pCoreOf 2 H) L → 3 ≤ Open.pRank 3 L →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    IsOmegaEightPlus (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) → False

section Block

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem map_conj_eq_of_oneImage {S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = barM M L) {n : G} (hnM : n ∈ M)
    (hnS : n ∈ Subgroup.normalizer (S : Set G)) :
    L.map (MulAut.conj n).toMonoidHom = L :=
  (hL.toIsTwoPrimeComponent.map_conj hnM).eq_of_barM_eq hL.toIsTwoPrimeComponent
    (hk1 _ (hL.map_conj hnM hnS))

theorem mk_mem_normalizer_blocks {S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = barM M L) {n : G} (hnM : n ∈ M)
    (hnS : n ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
        Subgroup.normalizer
          (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hLn := map_conj_eq_of_oneImage hL hk1 hnM hnS
  have hSn : (Subgroup.normalizer (S : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.normalizer (S : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := Subgroup.normalizer (S : Set G)) hnS)
  refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  · have := barM_map_conj hnM L
    rw [hLn] at this
    exact this.symm
  · have := barM_map_conj hnM (Subgroup.normalizer (S : Set G) ⊓ L)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj n).injective, hSn, hLn] at this
    exact this.symm

omit [Finite G] in
theorem eq_one_of_mk_eq_one_of_isPGroup_three {R : Subgroup G} (hR : IsPGroup 3 R) {r : ↥M}
    (hr : (r : G) ∈ R) (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) r = 1) : r = 1 := by
  have hmem : r ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff r).mp h
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨r, hmem⟩
  obtain ⟨j, hj⟩ := hR ⟨(r : G), hr⟩
  have h2 : r ^ (2 ^ k) = 1 := congrArg (fun z : CFSG.pCore 2 ↥M => (z : ↥M)) hk
  have h3 : r ^ (3 ^ j) = 1 := Subtype.ext (congrArg (fun z : R => (z : G)) hj)
  have hd2 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hd3 : orderOf r ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) (3 ^ j) :=
    Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd2 hd3)

omit [Finite G] in
theorem comm_of_barM_comm {R : Subgroup G} (hR : IsPGroup 3 R) (hRM : R ≤ M)
    (h : ∀ x ∈ barM M R, ∀ x' ∈ barM M R, x * x' = x' * x) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  have hma : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, hRM ha⟩ ∈ barM M R :=
    mem_barM_iff.mpr ⟨⟨a, hRM ha⟩, ha, rfl⟩
  have hmb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hRM hb⟩ ∈ barM M R :=
    mem_barM_iff.mpr ⟨⟨b, hRM hb⟩, hb, rfl⟩
  have hc : (⟨a * b * a⁻¹ * b⁻¹, M.mul_mem (M.mul_mem (M.mul_mem (hRM ha) (hRM hb))
      (M.inv_mem (hRM ha))) (M.inv_mem (hRM hb))⟩ : ↥M) = ⟨a, hRM ha⟩ * ⟨b, hRM hb⟩ *
        ⟨a, hRM ha⟩⁻¹ * ⟨b, hRM hb⟩⁻¹ := rfl
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨a * b * a⁻¹ * b⁻¹, M.mul_mem
      (M.mul_mem (M.mul_mem (hRM ha) (hRM hb)) (M.inv_mem (hRM ha))) (M.inv_mem (hRM hb))⟩ :
        ↥M) = 1 := by
    rw [hc]
    simp only [map_mul, map_inv]
    rw [h _ hma _ hmb]
    simp
  have := eq_one_of_mk_eq_one_of_isPGroup_three hR (r := ⟨a * b * a⁻¹ * b⁻¹, _⟩)
    (R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h1
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val this
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h2, one_mul]

theorem exists_conj_mem_of_isPGroup_three {K R : Subgroup G} (hR : IsPGroup 3 R) (hRK : R ≤ K)
    (hidx : ¬ 3 ∣ R.relIndex K) {n : G} (hn : n ∈ K) (hn3 : IsPGroup 3 (Subgroup.zpowers n)) :
    ∃ g ∈ K, g * n * g⁻¹ ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R' : Subgroup ↥K := R.subgroupOf K with hR'
  have hR'p : IsPGroup 3 R' := hR.comap_of_injective K.subtype K.subtype_injective
  let QR : Sylow 3 ↥K := hR'p.toSylow hidx
  set z : ↥K := ⟨n, hn⟩ with hz
  have hz3 : IsPGroup 3 (Subgroup.zpowers z) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hn3
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers] at hk ⊢
    rwa [hz, Subgroup.orderOf_mk]
  obtain ⟨Q, hQ⟩ := hz3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K Q QR
  have hzQ : z ∈ (Q : Subgroup ↥K) := hQ (Subgroup.mem_zpowers z)
  have hmem : MulAut.conj g • z ∈ MulAut.conj g • (Q : Subgroup ↥K) :=
    Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) (Q : Subgroup ↥K) hzQ
  have hQR : MulAut.conj g • (Q : Subgroup ↥K) = (QR : Subgroup ↥K) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [hQR] at hmem
  have hQRc : (QR : Subgroup ↥K) = R' := rfl
  rw [hQRc, hR', Subgroup.mem_subgroupOf] at hmem
  exact ⟨g, g.2, by simpa [MulAut.smul_def, MulAut.conj_apply, hz] using hmem⟩

omit [Finite G] in
theorem card_barM_of_isPGroup_three {R : Subgroup G} (hR : IsPGroup 3 R) (hRM : R ≤ M) :
    Nat.card (barM M R) = Nat.card R := by
  set φ : ↥(R.subgroupOf M) →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (R.subgroupOf M).subtype with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨r, hr⟩ h
    have hr' : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have := eq_one_of_mk_eq_one_of_isPGroup_three hR hr' (by simpa [hφ] using h)
    exact Subtype.ext this
  have h1 : Nat.card (barM M R) = Nat.card φ.range := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [h1]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv)

omit [Finite G] in
theorem irreducibleOn_barM {H R : Subgroup G} (hirr : IrreducibleOn (H ⊓ M ⊓
      Subgroup.normalizer (R : Set G)) R) (hRM : R ≤ M) (N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hN : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hn⟩ ∈ N) :
    IrreducibleOn N (barM M R) := by
  intro W hWR hWN
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set W₀ : Subgroup G := R ⊓ (W.comap mk).map M.subtype with hW₀
  have hW₀R : W₀ ≤ R := inf_le_left
  have hmem : ∀ r : ↥M, (r : G) ∈ R → mk r ∈ W → (r : G) ∈ W₀ := fun r hr hw => ⟨hr, r, hw, rfl⟩
  have hmem' : ∀ r : G, r ∈ W₀ → ∃ hr : r ∈ M, mk ⟨r, hr⟩ ∈ W := by
    rintro r ⟨-, m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  have key : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ w : G, w ∈ W₀ →
      n * w * n⁻¹ ∈ W₀ := by
    intro n hn w hw
    have hnM : n ∈ M := hn.1.2
    obtain ⟨hwM, hwW⟩ := hmem' w hw
    have hnR : n * w * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn.2 w).mp (hW₀R hw)
    have hnwM : n * w * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hwM) (M.inv_mem hnM)
    refine hmem ⟨_, hnwM⟩ hnR ?_
    have e : mk ⟨n * w * n⁻¹, hnwM⟩ = mk ⟨n, hnM⟩ * mk ⟨w, hwM⟩ * (mk ⟨n, hnM⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    have hcn := Subgroup.mem_normalizer_iff.mp (hWN (hN n hn hnM)) (mk ⟨w, hwM⟩)
    exact hcn.mp hwW
  have hW₀n : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key n hn w, fun hw => ?_⟩
    have hn' : n⁻¹ ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G) := Subgroup.inv_mem _ hn
    have := key n⁻¹ hn' _ hw
    simpa [mul_assoc] using this
  rcases hirr W₀ hW₀R hW₀n with h0 | hR'
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨r, hrR, rfl⟩ := mem_barM_iff.mp (hWR hx)
    have : (r : G) ∈ W₀ := hmem r hrR hx
    rw [h0, Subgroup.mem_bot] at this
    have hr1 : r = 1 := Subtype.ext this
    rw [hr1, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hWR fun x hx => ?_
    obtain ⟨r, hrR, rfl⟩ := mem_barM_iff.mp hx
    have : (r : G) ∈ W₀ := hR' ▸ hrR
    obtain ⟨hr, hw⟩ := hmem' _ this
    exact hw

theorem barM_le_PL_of_irreducible (hpr : AGLPair 3 M H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hirr : IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R)
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ≠ 1 ∧ y ^ 3 = 1) :
    barM M R ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  have hRM : R ≤ M := hpr.le_M
  have hRH : R ≤ H := hpr.le_H
  set Eb := barM M R with hEb
  have hnS : ∀ n ∈ H ⊓ M, n ∈ Subgroup.normalizer (S : Set G) := fun n hn => by
    rw [hpr.normalizer_twoCore_H]
    exact hn.1
  have hN : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
      mk ⟨n, hn⟩ ∈ Subgroup.normalizer (Eb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro n hn hnM
    have hb := mk_mem_normalizer_blocks hL hk1 hnM (hnS n hn.1)
    refine ⟨⟨?_, hb.2⟩, hb.1⟩
    have hRn : R.map (MulAut.conj n).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have := barM_map_conj hnM R
    rw [hRn] at this
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm
  have hirrE := irreducibleOn_barM hirr hRM _ hN
  obtain ⟨y, hyP, hy1, hy3⟩ := hy
  obtain ⟨m, hmN, hmy⟩ := mem_barM_iff.mp hyP
  have hnH : (m : G) ∈ H := by
    have := hmN.1
    rwa [hpr.normalizer_twoCore_H] at this
  have hnK : (m : G) ∈ H ⊓ M := ⟨hnH, m.2⟩
  have hord0 : orderOf (m : G) ≠ 0 := (orderOf_pos (m : G)).ne'
  obtain ⟨e, m', hm', hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord0 3 (by norm_num)
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hord0 (by simpa using hom)
  have hn₃ord : orderOf ((m : G) ^ m') = 3 ^ e := by
    rw [orderOf_pow_of_dvd hm'0 (by rw [hom]; exact dvd_mul_left _ _), hom]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm'0)
  have hn₃3 : IsPGroup 3 (Subgroup.zpowers ((m : G) ^ m')) :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, hn₃ord])
  have hn₃K : (m : G) ^ m' ∈ H ⊓ M := (H ⊓ M).pow_mem hnK m'
  have hn₃PL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G) ^ m', hn₃K.2⟩ ∈ PL :=
    mem_barM_iff.mpr ⟨⟨(m : G) ^ m', hn₃K.2⟩,
      ⟨(Subgroup.normalizer (S : Set G)).pow_mem hmN.1 m', L.pow_mem hmN.2 m'⟩, rfl⟩
  have hmkn₃ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G) ^ m', hn₃K.2⟩ = y ^ m' := by
    rw [← hmy, ← map_pow]
    rfl
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hn₃ne : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G) ^ m', hn₃K.2⟩ ≠ 1 := by
    rw [hmkn₃]
    intro h
    exact hm' (hyord ▸ orderOf_dvd_of_pow_eq_one h)
  have hHM : ¬ H ≤ M := hpr.not_le
  obtain ⟨T, hT⟩ := hpr.isSylow
  have hR''T : R.subgroupOf H = (T : Subgroup ↥H) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hidx : ¬ 3 ∣ R.relIndex (H ⊓ M) := by
    intro hd
    have h1 := Subgroup.relIndex_mul_relIndex R (H ⊓ M) H (le_inf hRH hRM) inf_le_left
    have h2 : 3 ∣ R.relIndex H := by rw [← h1]; exact hd.mul_right _
    apply T.not_dvd_index
    have : R.relIndex H = (R.subgroupOf H).index := rfl
    rwa [this, hR''T] at h2
  obtain ⟨g, hgK, hgR⟩ := exists_conj_mem_of_isPGroup_three hpr.isPGroup_R (le_inf hRH hRM) hidx
    hn₃K hn₃3
  have hgb := mk_mem_normalizer_blocks hL hk1 hgK.2 (hnS g hgK)
  have hgM : g * (m : G) ^ m' * g⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hgK.2 hn₃K.2) (M.inv_mem hgK.2)
  have hy''E : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * (m : G) ^ m' * g⁻¹, hgM⟩ ∈ Eb :=
    mem_barM_iff.mpr ⟨⟨_, hgM⟩, hgR, rfl⟩
  have hconj : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * (m : G) ^ m' * g⁻¹, hgM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgK.2⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G) ^ m', hn₃K.2⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgK.2⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hy''P : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * (m : G) ^ m' * g⁻¹, hgM⟩ ∈ PL := by
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp hgb.2 _).mp hn₃PL
  have hy''ne : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * (m : G) ^ m' * g⁻¹, hgM⟩ ≠ 1 := by
    rw [hconj]
    intro h
    apply hn₃ne
    have := congrArg (fun z => (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgK.2⟩)⁻¹ * z *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgK.2⟩) h
    simpa [mul_assoc] using this
  have hWN : Subgroup.normalizer (Eb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
      Subgroup.normalizer (PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
      Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer ((Eb ⊓ PL : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro ν ⟨⟨h1, h2⟩, -⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp h1 x).mp hx1,
        (Subgroup.mem_normalizer_iff.mp h2 x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp h1 x).mpr hx1,
        (Subgroup.mem_normalizer_iff.mp h2 x).mpr hx2⟩
  rcases hirrE (Eb ⊓ PL) inf_le_left hWN with h0 | hE
  · exfalso
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * (m : G) ^ m' * g⁻¹, hgM⟩ ∈ Eb ⊓ PL :=
      ⟨hy''E, hy''P⟩
    rw [h0, Subgroup.mem_bot] at this
    exact hy''ne this
  · intro x hx
    have : x ∈ Eb ⊓ PL := hE ▸ hx
    exact this.2


theorem false_of_oneImage_five (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hAut : KFactStrongThreeAutomizer) (hSix : KFactBlockSixLie)
    {P : Sylow 3 G} {A : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hfive : IsFiveList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hpr := hctx.pair
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hfact
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  have hBH : Open.pRank 3 Bb ≤ 2 := (hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hPLB : PL ≤ Bb := barM_mono inf_le_left
  have hPLr : Open.pRank 3 PL ≤ 2 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hPLB).trans hBH
  have hSolv : BlockPLThreeSolv M S L :=
    d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair hctx.strong
      hctx.perf L hL
  obtain ⟨ho, hPel, hnoswap⟩ := hSix G M S L hpr.isKGroup.1 hpr.asc81bHyp hL h2 hSolv hfive
  obtain ⟨y, hyP, hy3, hyC⟩ := exists_order_three_noncentral hL.le (hthree L hL) hZ
  have hcommbar := hpr.commutative_barM_of_one_weakSBlock h84 h86 hX hH hthree hL hk1 ho
    ⟨y, hyP, hy3, hyC⟩ (fun T hT hT3 => hPel hPLr T hT hT3)
  have hRM : R ≤ M := hpr.le_M
  have hRH : R ≤ H := hpr.le_H
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a :=
    comm_of_barM_comm hpr.isPGroup_R hRM hcommbar
  have hHM : ¬ H ≤ M := hpr.not_le
  have hHne : H ≠ ⊤ := by
    obtain ⟨C, hC, hC2, hHC⟩ := hpr.maxTwoLocal_H.1
    rw [hHC]
    exact normalizer_ne_top_of_twoGroup hctx.glob.simple hctx.glob.nonab hC hC2
  have hR2 : Open.pRank 3 R = 2 := hctx.esc.pRank_eq
  obtain ⟨E0, hE0R, -, hE0c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) R
  have h3dvd : 3 ∣ Nat.card (H ⊓ M : Subgroup G) := by
    have h1 : 3 ∣ Nat.card E0 := by
      rw [hE0c, hR2]
      exact dvd_pow_self 3 (by norm_num)
    exact h1.trans (Subgroup.card_dvd_of_le (hE0R.trans (le_inf hRH hRM)))
  have hstr' := glbStronglyEmbedded_subgroupOf_inf hctx.strong hHM h3dvd
  have hKH : Open.IsKGroup ↥H :=
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hctx.glob.kProper H hHne)
  have hrN₀ : Open.pRank 3 ((H ⊓ M).subgroupOf H) = 2 := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three _ _
      inf_le_left]
    refine le_antisymm ?_ ?_
    · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 inf_le_left).trans hH.le
    · rw [← hR2]
      exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 (le_inf hRH hRM)
  have hR''le : R.subgroupOf H ≤ (H ⊓ M).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2, hRM (Subgroup.mem_subgroupOf.mp hx)⟩
  have hR''p : IsPGroup 3 (R.subgroupOf H) :=
    hpr.isPGroup_R.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨T, hT⟩ := hpr.isSylow
  have hR''T : R.subgroupOf H = (T : Subgroup ↥H) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hR''idx : ¬ 3 ∣ (R.subgroupOf H).relIndex ((H ⊓ M).subgroupOf H) := by
    intro hd
    refine T.not_dvd_index (hd.trans ?_)
    rw [hR''T] at hd ⊢
    exact Subgroup.relIndex_dvd_index_of_le (hR''T ▸ hR''le)
  have hRcomm' : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hRcomm (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G)
      (Subgroup.mem_subgroupOf.mp hb))
  obtain ⟨hel, h9, hirr⟩ := (hAut ↥H hKH ((H ⊓ M).subgroupOf H) hstr' hrN₀ (R.subgroupOf H)
    hR''le hR''p hR''idx).1 hRcomm'
  have hirrG : IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R :=
    irreducibleOn_of_subgroupOf hRH hirr
  have hRel : IsElemAbelian 3 R := by
    have := CFSG.RankThreeCoreUniqueness.Helpers.elementary_map_injective 3 (R.subgroupOf H)
      H.subtype H.subtype_injective hel
    rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at this
  have hR9 : Nat.card R = 9 := by
    rw [← h9]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv).symm
  set Eb := barM M R with hEb
  have hEbel : IsElemAbelian 3 Eb := CFSG.AGLEmbeddingD2.isElemAbelian_barM hRel
  have hEb9 : Nat.card Eb = 9 := (card_barM_of_isPGroup_three hpr.isPGroup_R hRM).trans hR9
  have hnS : ∀ n ∈ H ⊓ M, n ∈ Subgroup.normalizer (S : Set G) := fun n hn => by
    rw [hpr.normalizer_twoCore_H]
    exact hn.1
  have hN : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
      mk ⟨n, hn⟩ ∈ Subgroup.normalizer (Eb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro n hn hnM
    have hb := mk_mem_normalizer_blocks hL hk1 hnM (hnS n hn.1)
    refine ⟨⟨?_, hb.2⟩, hb.1⟩
    have hRn : R.map (MulAut.conj n).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have := barM_map_conj hnM R
    rw [hRn] at this
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm
  have hirrE := irreducibleOn_barM hirrG hRM _ hN
  have hEPL : Eb ≤ PL := barM_le_PL_of_irreducible hpr hL hk1 hirrG
    ⟨y, hyP, fun h => hyC (h ▸ Subgroup.one_mem _), hy3⟩
  have hord9 : ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), T ≤ PL → IsPGroup 3 T → Nat.card T ≤ 9 := by
    intro T hT hT3
    have hTel := hPel hPLr T hT hT3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT3
    have hkr : k ≤ Open.pRank 3 T := le_pRank_of_isElemAbelian h3 hTel hk
    have hTr : Open.pRank 3 T ≤ 2 :=
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hT).trans hPLr
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hTr)
      _ = 9 := by norm_num
  exact hnoswap Eb hEbel hEb9 hEPL hord9 hirrE

theorem lieOneImageResidue_of_omega (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hAut : KFactStrongThreeAutomizer) (hSix : KFactBlockSixLie)
    (hOm : PairOmega8S6Residue) : LieOneImageResidue := by
  intro G _ _ P M A H R hctx hev L hL hk1 h2 hr3 hZ hlist
  rcases isOmegaEightPlus_or_isFiveList hlist with hom | hfive
  · exact hOm G P M A H R hctx hev L hL hk1 h2 hr3 hZ hom
  · exact false_of_oneImage_five h93 hD2 hΛ hAut hSix hctx hL hk1 h2 hZ hfive

end Block

end CFSG.AGLEmbeddingD2.McLaughlin
