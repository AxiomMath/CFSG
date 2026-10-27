module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Signb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem l34Sign_eq_one_of_coprime {P : Sylow 3 G} {g : G} (hg : g ∈ (P : Subgroup G))
    {n : ℕ} (hn : Nat.Coprime 3 n) (hdvd : orderOf g ∣ n) : g = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨g, hg⟩
  rw [orderOf_mk] at hk
  rw [← orderOf_eq_one_iff]
  exact Nat.Coprime.eq_one_of_dvd (by rw [hk]; exact Nat.Coprime.pow_left k hn) hdvd

theorem l34Sign_eq_one_of_mem (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three)
    {P : Sylow 3 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J)
    (c : ↥(centralizer ({x} : Set G))) (hc : (c : G) ∈ (P : Subgroup G) ⊓ J)
    (h1 : l34Hom x J c = 1) : c = 1 := by
  set O := primeComplementCore (G := centralizer ({x} : Set G)) 3 with hO
  set D := reducedCentralizerOfJ x J with hD
  have hy : QuotientGroup.mk' O c ∈ r1sBar x J := ⟨c, mem_subgroupOf.mpr hc.2, rfl⟩
  have hyD : QuotientGroup.mk' O c ∈ D := by
    have h : QuotientGroup.mk' D.normalCore (QuotientGroup.mk' O c) = 1 := h1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
    exact normalCore_le D h
  have hy1 : QuotientGroup.mk' O c = 1 := by
    have h : QuotientGroup.mk' O c ∈ r1sBar x J ⊓ D := ⟨hy, hyD⟩
    rwa [l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ, mem_bot] at h
  have hcO : c ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
    exact hy1
  exact Subtype.ext (l34Sign_eq_one_of_coprime hc.1 (primeComplementCore_coprime 3)
    (by rw [orderOf_coe]; exact orderOf_dvd_natCard O hcO))

theorem l34Sign_card_inf (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  have hAC : A ≤ C := inf_le_right.trans hJ.le_centralizer
  set ψ : ↥A →* L34Quot x J := (l34Hom x J).comp (inclusion hAC) with hψ
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h : ((inclusion hAC a : ↥C) : G) = 1 :=
      congrArg Subtype.val (l34Sign_eq_one_of_mem hK1 hK2 hJ (inclusion hAC a) a.2 ha)
    exact Subtype.ext h
  have hr : ψ.range = l34Img x J A := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨inclusion hAC a, mem_subgroupOf.mpr a.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, mem_subgroupOf.mp hc⟩, rfl⟩
  rw [Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv, hr]
  exact (l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ).2.1

theorem l34Sign_centralizes (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK8 : KFactL34SylowCentralizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    {N : Subgroup G} (hN : Nat.Coprime 3 (Nat.card N)) {w : G}
    (hwC : w ∈ centralizer ({x} : Set G)) {u : G} (huA : u ∈ (P : Subgroup G) ⊓ J) (hu1 : u ≠ 1)
    (hwu : w * u = u * w) (hwA : ∀ a ∈ (P : Subgroup G) ⊓ J, (w * a * w⁻¹)⁻¹ * a ∈ N) :
    l34Img x J (zpowers w) ≤ centralizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
      Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  set K : Subgroup (L34Quot x J) := l34Img x J J with hK
  set T : Subgroup (L34Quot x J) := l34Img x J A with hT
  have hAC : A ≤ C := inf_le_right.trans hJ.le_centralizer
  obtain ⟨hKn, -, hKL⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨hTel, hT9, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  set φ := l34Hom x J with hφ
  set w' : ↥C := ⟨w, hwC⟩ with hw'
  set u' : ↥C := ⟨u, hAC huA⟩ with hu'
  have hmemT : ∀ c : ↥C, (c : G) ∈ A → φ c ∈ T := fun c hc => ⟨c, mem_subgroupOf.mpr hc, rfl⟩
  have huT : φ u' ∈ T := hmemT u' huA
  have hu'1 : φ u' ≠ 1 := fun h =>
    hu1 (congrArg Subtype.val (l34Sign_eq_one_of_mem hK1 hK2 hJ u' huA h))
  have hwu' : Commute (φ w') (φ u') := by
    change φ w' * φ u' = φ u' * φ w'
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hwu)
  have hTab : ∀ a ∈ T, ∀ b ∈ T, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hTel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTKcard : Nat.card ↥(T.subgroupOf K) = 3 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv, hT9]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hTKcard).exists_le_sylow
  have hTQ : T.subgroupOf K = Q :=
    eq_of_le_of_card_ge hQ (by rw [(hK2 ↥K hKL Q).1, hTKcard])
  have huQ : (⟨φ u', hTK huT⟩ : ↥K) ∈ (Q : Subgroup ↥K) := hQ (mem_subgroupOf.mpr huT)
  have hcent := hK8 ↥K hKL Q ⟨φ u', hTK huT⟩ huQ fun h => hu'1 (congrArg Subtype.val h)
  have hconj : ∀ t ∈ T, φ w' * t * (φ w')⁻¹ ∈ T := by
    intro t ht
    have hy : φ w' * t * (φ w')⁻¹ ∈ K := hKn.conj_mem t (hTK ht) (φ w')
    have hyc : (⟨φ w' * t * (φ w')⁻¹, hy⟩ : ↥K) ∈
        centralizer ({⟨φ u', hTK huT⟩} : Set ↥K) := by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext ((hwu'.mul_left (hTab t ht _ huT)).mul_left hwu'.inv_left)
    rw [hcent, ← hTQ] at hyc
    exact mem_subgroupOf.mp hyc
  have hcomm : ∀ c : ↥C, (c : G) ∈ A → Commute (φ c) (φ w') := by
    intro c hcA
    have hnN : (((w' * c * w'⁻¹)⁻¹ * c : ↥C) : G) ∈ N := hwA c hcA
    have hnT : φ ((w' * c * w'⁻¹)⁻¹ * c) ∈ T := by
      simp only [map_mul, map_inv]
      exact T.mul_mem (T.inv_mem (hconj _ (hmemT c hcA))) (hmemT c hcA)
    have hn1 : φ ((w' * c * w'⁻¹)⁻¹ * c) = 1 := by
      rw [← orderOf_eq_one_iff]
      have h9 : orderOf (φ ((w' * c * w'⁻¹)⁻¹ * c)) ∣ 3 ^ 2 := hT9 ▸ orderOf_dvd_natCard T hnT
      have hdN : orderOf (φ ((w' * c * w'⁻¹)⁻¹ * c)) ∣ Nat.card N :=
        (orderOf_map_dvd φ _).trans (by rw [← orderOf_coe]; exact orderOf_dvd_natCard N hnN)
      exact Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left h9 (Nat.Coprime.pow_left 2 hN)) hdN
    simp only [map_mul, map_inv] at hn1
    rw [inv_mul_eq_one] at hn1
    change φ c * φ w' = φ w' * φ c
    calc φ c * φ w' = φ w' * φ c * (φ w')⁻¹ * φ w' := by rw [hn1]
      _ = φ w' * φ c := by group
  rintro z ⟨c, hc, rfl⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp hc)
  have hck : c = w' ^ k := Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk.symm)
  rw [mem_centralizer_iff]
  rintro t ⟨c', hc', rfl⟩
  rw [hck, map_zpow]
  exact (hcomm c' (mem_subgroupOf.mp hc')).zpow_right k

theorem l34_stepH (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK8 : KFactL34SylowCentralizer) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) (hR3 : L34Remark 3 P M J) {U : Subgroup G}
    (_hU : IsElemAbelian 3 U) (_hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G))
    (hxU : x ∈ U) (hUJ : U ⊓ J ≠ ⊥) {S₁ : Subgroup G} (_hS₁ : IsPGroup 2 S₁)
    (hUS₁ : U ≤ normalizer (S₁ : Set G))
    (hG3 : Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) ≤ 2)
    (hG4 : S₁ ⊓ M ⊓ centralizer ({x} : Set G) = S₁ ⊓ centralizer (U : Set G))
    (hG5 : ∀ w ∈ S₁ ⊓ centralizer (U : Set G), w ≠ 1 →
      ¬ (l34Img x J (zpowers w) ≤ centralizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
        Subgroup (L34Quot x J)) : Set (L34Quot x J)))) :
    ∃ M₀ : Subgroup G, M₀ ≤ M ∧ (M₀.subgroupOf M).Normal ∧ M₀.relIndex M ≤ 2 ∧
      GLBPrimeCore 3 M ≤ M₀ ∧ (∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ M₀) ∧
      S₁ ⊓ M ⊓ M₀ = ⁅S₁ ⊓ M, zpowers x⁆ := by
  set N : Subgroup G := GLBPrimeCore 3 M with hN
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hNM : N ≤ M := glbPrimeCore_le 3 M
  have hMN : M ≤ normalizer (N : Set G) := le_normalizer_glbPrimeCore 3 M
  have hNcop : Nat.Coprime 3 (Nat.card N) := glbPrimeCore_coprime 3 M
  have hAN1 : ∀ a ∈ A, a ∈ N → a = 1 := fun a ha haN =>
    l34Sign_eq_one_of_coprime ha.1 hNcop (orderOf_dvd_natCard N haN)
  obtain ⟨χ, hχN, hχw⟩ := l34Sign_exists_sign ((inf_le_left.trans hPM).trans hMN) hR3 hMN
    (l34Sign_card_inf hS hU0 hK1 hK2 hp hM hgen hJ) hAN1
  obtain ⟨h1, h2, h3, h4, hmem⟩ := l34Sign_ker_facts χ
  set M₀ : Subgroup G := χ.ker.map M.subtype with hM₀
  have hkey : ∀ w ∈ S₁ ⊓ centralizer (U : Set G), w ≠ 1 → w ∉ M₀ := by
    intro w hw hw1 hwM₀
    have hw' : w ∈ S₁ ⊓ M ⊓ centralizer ({x} : Set G) := by
      rw [hG4]
      exact hw
    have hwM : w ∈ M := hw'.1.2
    have hw2 : w ^ 2 = 1 := by
      have hpos : 0 < Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) := Nat.card_pos
      have h12 : Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) ∣ 2 := by
        interval_cases h : Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) <;> norm_num
      exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _ hw).trans h12)
    obtain ⟨⟨u, hu⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hUJ
    have huA : u ∈ A := ⟨hUP hu.1, hu.2⟩
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hwu : w * u = u * w := (mem_centralizer_iff.mp hw.2 u hu.1).symm
    have hrho : ∃ a ∈ A, (w * a * w⁻¹)⁻¹ * a ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hG5 w hw hw1 (l34Sign_centralizes hS hU0 hK1 hK2 hK8 hp hM hgen hJ hNcop hw'.2 huA
        hu1' hwu hcon)
    have hχ := hχw ⟨w, hwM⟩ hw2 ⟨u, huA, hu1', hwu⟩ hrho
    rw [hmem w hwM, hχ] at hwM₀
    exact absurd hwM₀ (by decide)
  refine ⟨M₀, h1, h2, h3, fun n hn => (hmem n (hNM hn)).mpr (hχN ⟨n, hNM hn⟩ hn), h4, ?_⟩
  have hxM : x ∈ M := hPM (hUP hxU)
  apply le_antisymm
  · refine (l34Sign_le_commutator ?_ ?_).trans (commutator_mono inf_le_left le_rfl)
    · intro s hs
      refine ⟨⟨(mem_normalizer_iff.mp (hUS₁ hxU) s).mp hs.1.1,
        M.mul_mem (M.mul_mem hxM hs.1.2) (M.inv_mem hxM)⟩, ?_⟩
      have h := M₀.mul_mem (h4 x hxM s hs.1.2) hs.2
      rwa [inv_mul_cancel_right] at h
    · intro s hs hsx
      by_contra hs1
      have hsW : s ∈ S₁ ⊓ centralizer (U : Set G) := by
        rw [← hG4]
        exact ⟨hs.1, mem_centralizer_singleton_iff.mpr hsx⟩
      exact hkey s hsW hs1 hs.2
  · rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₂U : g₂ ∈ U := (zpowers_le.mpr hxU) hg₂
    have hg₂M : g₂ ∈ M := hPM (hUP hg₂U)
    rw [commutatorElement_def]
    have hS₁g : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ S₁ := by
      have h := S₁.mul_mem hg₁.1
        ((mem_normalizer_iff.mp (hUS₁ hg₂U) g₁⁻¹).mp (S₁.inv_mem hg₁.1))
      simpa only [mul_assoc] using h
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hS₁g, M.mul_mem (M.mul_mem (M.mul_mem hg₁.2 hg₂M)
      (M.inv_mem hg₁.2)) (M.inv_mem hg₂M)⟩, h4 g₁ hg₁.2 g₂ hg₂M⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
