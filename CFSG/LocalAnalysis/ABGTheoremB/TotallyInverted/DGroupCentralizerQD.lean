module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusInputs
public import CFSG.GroupTheory.ABGDGroups.LinearSignalizers
public import CFSG.GroupTheory.ABGDGroups.LinearOddCyclic
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
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
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusSetting

public noncomputable section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.QuasiDihedralFusion CFSG.ABGDGroups
open CFSG.GorensteinWalter (a7t a7u a7a a7v a7s a7S)

section ASeven

local notation "A₇" => alternatingGroup (Fin 7)

private def a7g₁ : A₇ := ⟨Equiv.swap (2 : Fin 7) 4 * Equiv.swap 3 5, by simp [Equiv.Perm.sign_mul]⟩

private def a7g₂ : A₇ := ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap 1 5, by simp [Equiv.Perm.sign_mul]⟩

private def a7c : Fin 3 → A₇ := ![a7a, a7g₁ * a7a * a7g₁⁻¹, a7g₂ * a7a * a7g₂⁻¹]

private theorem pow_three_eq_one_of_odd {M : Type*} [Monoid M] {x : M} (hx : Odd (orderOf x))
    (h12 : x ^ 12 = 1) : x ^ 3 = 1 := by
  have hdvd : orderOf x ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one h12
  have hcop : Nat.Coprime (orderOf x) 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_right.mpr hx).pow_right 2
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

private theorem a7S_involution_cases {v : A₇} (hv : v ∈ a7S) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) :
    v = a7t ∨ v = a7u ∨ v = a7t * a7u ∨ v = a7g₁ * a7t * a7g₁⁻¹ ∨ v = a7g₂ * a7t * a7g₂⁻¹ := by
  change v = 1 ∨ v = a7v ∨ v = a7v ^ 2 ∨ v = a7v ^ 3 ∨ v = a7s ∨ v = a7s * a7v ∨
    v = a7s * a7v ^ 2 ∨ v = a7s * a7v ^ 3 at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact absurd hv2 (by decide +kernel)
  · left; decide +kernel
  · exact absurd hv2 (by decide +kernel)
  · right; right; right; left; decide +kernel
  · right; left; decide +kernel
  · right; right; right; right; decide +kernel
  · right; right; left; decide +kernel

private theorem eq_of_commute_conj_a7t {g x : A₇} (hx : Odd (orderOf x))
    (hc : x * (g * a7t * g⁻¹) = g * a7t * g⁻¹ * x) :
    x = 1 ∨ x = g * a7a * g⁻¹ ∨ x = (g * a7a * g⁻¹) ^ 2 := by
  set y := g⁻¹ * x * g with hy
  have hxy : x = g * y * g⁻¹ := by rw [hy]; group
  have hyc : y * a7t = a7t * y := by
    rw [hy]
    calc g⁻¹ * x * g * a7t = g⁻¹ * (x * (g * a7t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a7t * g⁻¹ * x) * g := by rw [hc]
      _ = a7t * (g⁻¹ * x * g) := by group
  have hyo : orderOf y = orderOf x := by
    rw [hy, show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq]
  obtain ⟨h12, h3⟩ := (aSeven_centralizer_involution_a7V_certificate y).1 hyc
  rcases h3 (pow_three_eq_one_of_odd (hyo ▸ hx) h12) with h | h | h
  · left
    rw [hxy, h]
    group
  · right; left
    rw [hxy, h]
  · right; right
    rw [hxy, h, conj_pow]

private theorem exists_index_of_involution {v : A₇} (hv : v ∈ a7S) (hv1 : v ≠ 1)
    (hv2 : v ^ 2 = 1) :
    ∃ i : Fin 3, ∀ x : A₇, x * v = v * x → Odd (orderOf x) →
      x = 1 ∨ x = a7c i ∨ x = a7c i ^ 2 := by
  have hcert := aSeven_centralizer_involution_a7V_certificate
  rcases a7S_involution_cases hv hv1 hv2 with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, fun x hc hx => ((hcert x).1 hc).2
      (pow_three_eq_one_of_odd hx ((hcert x).1 hc).1)⟩
  · exact ⟨0, fun x hc hx => ((hcert x).2.1 hc).2
      (pow_three_eq_one_of_odd hx ((hcert x).2.1 hc).1)⟩
  · exact ⟨0, fun x hc hx => ((hcert x).2.2 hc).2
      (pow_three_eq_one_of_odd hx ((hcert x).2.2 hc).1)⟩
  · exact ⟨1, fun x hc hx => eq_of_commute_conj_a7t hx hc⟩
  · exact ⟨2, fun x hc hx => eq_of_commute_conj_a7t hx hc⟩

private theorem a7c_pair_certificate : ∀ i j : Fin 3, i ≠ j →
    (a7c i * (a7c j * a7c i * (a7c j)⁻¹)) ^ 2 = 1 ∧ a7c i * (a7c j * a7c i * (a7c j)⁻¹) ≠ 1 := by
  decide +kernel

private theorem a7c_pow_four : ∀ i : Fin 3, a7c i ^ 4 = a7c i := by
  decide +kernel

private theorem aSeven_exists_le_centralizer_of_le_a7S {T K : Subgroup A₇} (hT : IsKleinFour T)
    (hTS : T ≤ a7S) (hK : Odd (Nat.card K)) (hKT : T ≤ Subgroup.normalizer (K : Set A₇)) :
    ∃ v ∈ T, v ≠ 1 ∧ K ≤ Subgroup.centralizer ({v} : Set A₇) := by
  classical
  have hpow : ∀ v : T, v ^ 2 = 1 := fun v => by
    have h := Monoid.pow_exponent_eq_one v
    rwa [hT.exponent_two] at h
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two T K hpow hT.card_four
    (fun h => (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h)) hKT
  have hidx : ∀ v : T, v ≠ 1 → ∃ i : Fin 3, ∀ x : A₇, x * v = v * x → Odd (orderOf x) →
      x = 1 ∨ x = a7c i ∨ x = a7c i ^ 2 := fun v hv =>
    exists_index_of_involution (hTS v.2) (fun h => hv (Subtype.ext h))
      (by simpa using congrArg Subtype.val (hpow v))
  have hmem : ∀ (i : Fin 3) (x : A₇), x ∈ K → x ≠ 1 → (x = 1 ∨ x = a7c i ∨ x = a7c i ^ 2) →
      a7c i ∈ K := by
    rintro i x hxK hx1 (rfl | rfl | rfl)
    · exact absurd rfl hx1
    · exact hxK
    · rw [← a7c_pow_four i, show 4 = 2 * 2 by norm_num, pow_mul]
      exact K.pow_mem hxK 2
  have hpair : ∀ i j : Fin 3, i ≠ j → a7c i ∈ K → a7c j ∈ K → False := by
    intro i j hij hi hj
    obtain ⟨h2, h1⟩ := a7c_pair_certificate i j hij
    have hw : a7c i * (a7c j * a7c i * (a7c j)⁻¹) ∈ K :=
      K.mul_mem hi (K.mul_mem (K.mul_mem hj hi) (K.inv_mem hj))
    have hord : orderOf (a7c i * (a7c j * a7c i * (a7c j)⁻¹)) = 2 := orderOf_eq_prime h2 h1
    have h2K := Subgroup.orderOf_dvd_natCard K hw
    rw [hord] at h2K
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h2K)
  by_cases hne : ∃ v : T, v ≠ 1 ∧ K ⊓ Subgroup.centralizer ({(v : A₇)} : Set A₇) ≠ ⊥
  · obtain ⟨v, hv1, hvne⟩ := hne
    obtain ⟨i, hi⟩ := hidx v hv1
    obtain ⟨x, ⟨hxK, hxC⟩, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hvne
    have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hx := hi x hxv (hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hxK))
    have hciK : a7c i ∈ K := hmem i x hxK hx1 hx
    have hcv : a7c i * v = v * a7c i := by
      rcases hx with rfl | rfl | rfl
      · exact absurd rfl hx1
      · exact hxv
      · have hc : Commute (a7c i ^ 2) (v : A₇) := hxv
        rw [← a7c_pow_four i, show 4 = 2 * 2 by norm_num, pow_mul]
        exact (hc.pow_left 2).eq
    have hle : K ≤ Subgroup.zpowers (a7c i) := by
      refine hgen.le.trans (iSup₂_le fun w hw => ?_)
      rintro y ⟨hyK, hyC⟩
      obtain ⟨j, hj⟩ := hidx w hw
      have hy := hj y (Subgroup.mem_centralizer_singleton_iff.mp hyC)
        (hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hyK))
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      by_cases hij : i = j
      · subst hij
        rcases hy with h | h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers _
        · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      · exact (hpair i j hij hciK (hmem j y hyK hy1 hy)).elim
    refine ⟨v, v.2, fun h => hv1 (Subtype.ext h), hle.trans ?_⟩
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcv
  · push Not at hne
    have hbot : K = ⊥ := by
      rw [hgen]
      exact iSup₂_eq_bot.mpr hne
    have hT1 : 1 < Nat.card T := by rw [hT.card_four]; norm_num
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hT1
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : T)
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h), by rw [hbot]; exact bot_le⟩

theorem aSeven_exists_le_centralizer_of_kleinFour {H : Type} [Group H] [Finite H] (e : H ≃* A₇)
    {T K : Subgroup H} (hT : IsKleinFour T) (hK : Odd (Nat.card K))
    (hKT : T ≤ Subgroup.normalizer (K : Set H)) :
    ∃ v ∈ T, v ≠ 1 ∧ K ≤ Subgroup.centralizer ({v} : Set H) := by
  obtain ⟨S, hTS⟩ := (isPGroup_two_of_isKleinFour hT).exists_le_sylow
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_aSeven_map_sylow_eq e S
  have hT' : IsKleinFour (T.map φ.toMonoidHom) :=
    isKleinFour_map_of_inf_ker_eq_bot _ hT (by
      rw [eq_bot_iff]
      rintro x ⟨-, hx⟩
      exact Subgroup.mem_bot.mpr (φ.injective (hx.trans (map_one φ).symm)))
  obtain ⟨_, ⟨v, hvT, rfl⟩, hv1, hKv⟩ := aSeven_exists_le_centralizer_of_le_a7S hT'
    (hφ ▸ Subgroup.map_mono hTS)
    (by rwa [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective])
    ((Subgroup.map_mono hKT).trans (Subgroup.le_normalizer_map _))
  refine ⟨v, hvT, fun h => hv1 (by rw [h, map_one]), fun k hk => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hKv ⟨k, hk, rfl⟩)
  apply φ.injective
  simpa using h

end ASeven

section DGroup

variable {H : Type} [Group H] [Finite H]

theorem dGroup_exists_le_centralizer_of_oddCore_eq_bot (hH : IsDGroup H)
    (hO : CFSG.oddCore H = ⊥) {T : Subgroup H} (hT : IsKleinFour T) {Y : Subgroup H}
    (hYT : T ≤ Subgroup.normalizer (Y : Set H)) (hY : Odd (Nat.card Y)) :
    ∃ t ∈ T, t ≠ 1 ∧ Y ≤ Subgroup.centralizer ({t} : Set H) := by
  by_cases hW : ∃ n, HasWreathedSylow H n
  · obtain ⟨n, hn⟩ := hW
    have hYb : Y = ⊥ := by
      rcases hH with ⟨hD, -⟩ | ⟨K', hK'⟩
      · exact (not_hasWreathedSylow_and_dihedral hn hD).elim
      · have hle := wreathed_dGroup_odd_four_invariant_le_oddCore hK' hn hT hY hYT
        rwa [hO, le_bot_iff] at hle
    have hT1 : 1 < Nat.card T := by rw [hT.card_four]; norm_num
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hT1
    obtain ⟨⟨t, ht⟩, ht1⟩ := exists_ne (1 : T)
    exact ⟨t, ht, fun h => ht1 (Subtype.ext h), by rw [hYb]; exact bot_le⟩
  · rcases aSeven_or_linearDecomposition hH hO hW with he | hlin
    · obtain ⟨e⟩ := he
      exact aSeven_exists_le_centralizer_of_kleinFour e hT hY hYT
    · obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
      obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
      refine hd.exists_le_centralizer_of_kleinFour hT hYT ?_
      apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
      rw [hT.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_right.mpr hY).pow_right 2

theorem dGroup_exists_commutator_mem_oddCore (hH : IsDGroup H) {T : Subgroup H}
    (hT : IsKleinFour T) {Y : Subgroup H} (hYT : T ≤ Subgroup.normalizer (Y : Set H))
    (hY : Odd (Nat.card Y)) :
    ∃ t ∈ T, t ≠ 1 ∧ ∀ y ∈ Y, y * t * y⁻¹ * t⁻¹ ∈ CFSG.oddCore H := by
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  have hTπ : T ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hT.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr (odd_card_oddCore H)).pow_left 2
  obtain ⟨_, ⟨t, htT, rfl⟩, ht1, hYt⟩ := dGroup_exists_le_centralizer_of_oddCore_eq_bot
    (isDGroup_quotient_oddCore hH) (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H)
    (isKleinFour_map_of_inf_ker_eq_bot π hT hTπ)
    ((Subgroup.map_mono hYT).trans (Subgroup.le_normalizer_map π))
    (hY.of_dvd_nat (Subgroup.card_map_dvd Y π))
  refine ⟨t, htT, fun h => ht1 (by rw [h, map_one]), fun y hy => ?_⟩
  have hc : π y * π t = π t * π y :=
    Subgroup.mem_centralizer_singleton_iff.mp (hYt ⟨y, hy, rfl⟩)
  rw [← QuotientGroup.eq_one_iff]
  change π (y * t * y⁻¹ * t⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  group

end DGroup

variable {G : Type} [Group G] [Finite G]

theorem abg_II_5_7_input (σ : Setting G) : ABG_II_5_7_Input σ := by
  intro _ K hK T₁ hT₁K hT₁ Y hYK hY hYT
  let eT : T₁.subgroupOf K ≃* T₁ := Subgroup.subgroupOfEquivOfLe hT₁K
  have hT' : IsKleinFour (T₁.subgroupOf K) :=
    ⟨by rw [Nat.card_congr eT.toEquiv]; exact hT₁.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv eT]; exact hT₁.exponent_two⟩
  have hY' : Odd (Nat.card (Y.subgroupOf K)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
  have hYT' : T₁.subgroupOf K ≤ Subgroup.normalizer ((Y.subgroupOf K : Subgroup K) : Set K) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hYT (Subgroup.mem_subgroupOf.mp ht))) x
  obtain ⟨t, htT, ht1, hYt⟩ := dGroup_exists_commutator_mem_oddCore hK hT' hYT' hY'
  refine ⟨t, Subgroup.mem_subgroupOf.mp htT, fun h => ht1 (Subtype.ext h), fun y hy => ?_⟩
  exact ⟨_, hYt ⟨y, hYK hy⟩ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem abg_II_5_7_input_of {σ : Setting G} (_hσ : σ.IsValid) : ABG_II_5_7_Input σ :=
  abg_II_5_7_input σ

end CFSG.ABGTheoremB.TotallyInverted
