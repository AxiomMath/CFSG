module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Basics
public import CFSG.GroupTheory.PRankCoprimeQuotient
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.PSL3Four.F4
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_of_injective' {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) : pRank 2 X ≤ pRank 2 Y := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_top_le_of_injective (by norm_num) f hf

theorem pRank_le_of_le {H K : Subgroup G} (h : H ≤ K) : pRank 2 ↥H ≤ pRank 2 ↥K :=
  pRank_le_of_injective' (inclusion h) (inclusion_injective h)

theorem three_le_pRank_of_card_eight {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsElemTwo E) (h8 : Nat.card E = 8) : 3 ≤ pRank 2 X :=
  (hE.three_le_pRank h8.ge).trans (pRank_le_of_injective' E.subtype E.subtype_injective)

theorem three_le_pRank_of_eight {H E : Subgroup G} (hEH : E ≤ H) (hE : IsEightGroup E) :
    3 ≤ pRank 2 ↥H :=
  (hE.1.three_le_pRank hE.2.ge).trans (pRank_le_of_le hEH)

theorem exists_involution_commute_of_mem {H : Subgroup G} {t k : G} (ht : t * t = 1)
    (htH : t ∈ normalizer (H : Set G)) (hkH : k ∈ H) (hk : k * k = 1) (hk1 : k ≠ 1) :
    ∃ w ∈ H, w * w = 1 ∧ w ≠ 1 ∧ w * t = t * w := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk
  set k' := t * k * t⁻¹ with hk'
  have hk'H : k' ∈ H := (mem_normalizer_iff.mp htH k).mp hkH
  have hk'inv : k'⁻¹ = k' := by
    rw [hk', mul_inv_rev, mul_inv_rev, inv_inv, hkinv, htinv, mul_assoc]
  set r := k * k' with hr
  have hrH : r ∈ H := mul_mem hkH hk'H
  have htr : t * r * t⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hk'inv, hkinv, hk', htinv]
    calc t * (k * (t * k * t)) * t = t * k * t * k * (t * t) := by group
      _ = t * k * t * k := by rw [ht, mul_one]
  have hkr : k * r * k⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hk'inv, hkinv]
    calc k * (k * k') * k = (k * k) * k' * k := by group
      _ = k' * k := by rw [hk, one_mul]
  have hkrn : ∀ n : ℤ, k * r ^ n * k⁻¹ = r ^ (-n) := by
    intro n
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hkr, zpow_neg, inv_zpow]
  have htrn : ∀ n : ℤ, t * r ^ n * t⁻¹ = r ^ (-n) := by
    intro n
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htr, zpow_neg, inv_zpow]
  have hord := orderOf_pos r
  have hrn : r ^ (orderOf r : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  rcases Nat.even_or_odd (orderOf r) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hm0 : 0 < m := by omega
    refine ⟨r ^ m, pow_mem hrH m, ?_, ?_, ?_⟩
    · rw [← pow_add, ← hm, pow_orderOf_eq_one]
    · intro h
      have := orderOf_le_of_pow_eq_one hm0 h
      omega
    · have h1 := htrn m
      have h2 : r ^ (-(m : ℤ)) = r ^ (m : ℤ) := by
        rw [zpow_neg, inv_eq_iff_mul_eq_one, ← zpow_add, ← Nat.cast_add, ← hm, hrn]
      rw [zpow_natCast, h2, zpow_natCast] at h1
      calc r ^ m * t = (t * r ^ m * t⁻¹) * t := by rw [h1]
        _ = t * r ^ m := by group
  ·
    have h1 : r ^ (-((m : ℤ) + 1)) = r ^ (-(m : ℤ)) * r⁻¹ := by
      rw [neg_add, zpow_add, zpow_neg_one]
    refine ⟨k * r ^ (m + 1), mul_mem hkH (pow_mem hrH _), ?_, ?_, ?_⟩
    · calc k * r ^ (m + 1) * (k * r ^ (m + 1)) = (k * r ^ ((m + 1 : ℕ) : ℤ) * k⁻¹) *
            r ^ (m + 1) := by rw [hkinv, zpow_natCast]; group
        _ = 1 := by rw [hkrn, zpow_neg, zpow_natCast, inv_mul_cancel]
    · intro h
      have hkr' : k = (r ^ (m + 1))⁻¹ := eq_inv_of_mul_eq_one_left h
      have hk2 : orderOf k = 2 := orderOf_eq_prime (by rw [pow_two, hk]) hk1
      have hdvd : orderOf k ∣ orderOf r := orderOf_dvd_of_pow_eq_one (by
        rw [hkr', inv_pow, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, inv_one])
      rw [hk2, hm] at hdvd
      omega
    ·
      have hk'r : k' = k * r := by rw [hr, ← mul_assoc, hk, one_mul]
      have h2 : r ^ (-(m : ℤ)) = r ^ ((m : ℤ) + 1) := by
        rw [zpow_neg, inv_eq_iff_mul_eq_one, ← zpow_add]
        have : (m : ℤ) + ((m : ℤ) + 1) = (orderOf r : ℤ) := by rw [hm]; push_cast; ring
        rw [this, hrn]
      have h3 : t * (k * r ^ (m + 1)) * t⁻¹ = k * r ^ (m + 1) := by
        have e1 : t * (k * r ^ (m + 1)) * t⁻¹ =
            (t * k * t⁻¹) * (t * r ^ ((m + 1 : ℕ) : ℤ) * t⁻¹) := by
          rw [zpow_natCast]; group
        rw [e1, htrn, ← hk', hk'r]
        push_cast
        rw [h1, h2, ← zpow_natCast r (m + 1)]
        push_cast
        group
      calc k * r ^ (m + 1) * t = (t * (k * r ^ (m + 1)) * t⁻¹) * t := by rw [h3]
        _ = t * (k * r ^ (m + 1)) := by group

theorem exists_involution_commute_ne {X : Type*} [Group X] [Finite X] (h2 : 2 ≤ pRank 2 X)
    {k : X} (hk : k * k = 1) (hk1 : k ≠ 1) :
    ∃ w : X, w * w = 1 ∧ w ≠ 1 ∧ w ≠ k ∧ w * k = k * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hk2 : orderOf k = 2 := orderOf_eq_prime (by rw [pow_two, hk]) hk1
  have hkp : IsPGroup 2 (zpowers k) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk2,
    pow_one])
  obtain ⟨P, hkP⟩ := hkp.exists_le_sylow
  have hkP' : k ∈ (P : Subgroup X) := hkP (mem_zpowers k)
  have hPnt : Nontrivial ↥(P : Subgroup X) :=
    ⟨⟨⟨k, hkP'⟩, 1, fun h => hk1 (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial ↥(center ↥(P : Subgroup X)) := P.isPGroup'.center_nontrivial
  have h2Z : 2 ∣ Nat.card ↥(center ↥(P : Subgroup X)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(center ↥(P : Subgroup X)))).mp
      (P.isPGroup'.to_subgroup _)
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact absurd (Finite.one_lt_card_iff_nontrivial.mpr hZnt) (by rw [hn]; omega)
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥(P : Subgroup X))) 2 h2Z
  set z₀ : X := ((z : ↥(P : Subgroup X)) : X) with hz₀
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz, pow_two] at h
  have hz₀2 : z₀ * z₀ = 1 := by
    have h := congrArg (fun y : ↥(center ↥(P : Subgroup X)) => ((y : ↥(P : Subgroup X)) : X)) hzz
    simpa using h
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz₀c : ∀ p ∈ (P : Subgroup X), z₀ * p = p * z₀ := fun p hp =>
    congrArg Subtype.val ((mem_center_iff.mp z.2) ⟨p, hp⟩).symm
  have hz₀k : z₀ = k := by
    by_contra hne
    exact hno z₀ hz₀2 hz₀1 hne (hz₀c k hkP')
  obtain ⟨A, hA, hA4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
  have hAp : IsPGroup 2 A := by
    apply IsPGroup.of_card (n := 2)
    rw [hA4]
    norm_num
  obtain ⟨P₁, hAP₁⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P
  have hconj : ∀ a ∈ A, g * a * g⁻¹ ∈ (P : Subgroup X) := by
    intro a ha
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨a, hAP₁ ha, by
      rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h1 := hA.2 a ha
    rwa [pow_two] at h1
  have hex : ∃ a ∈ A, a ≠ 1 ∧ g * a * g⁻¹ ≠ k := by
    by_contra hall
    push Not at hall
    have hsub : (A : Set X) ⊆ {1, g⁻¹ * k * g} := by
      intro a ha
      by_cases ha1 : a = 1
      · exact Or.inl ha1
      · right
        show a = g⁻¹ * k * g
        rw [← hall a ha ha1]
        group
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hA4] at hle
    have := Set.ncard_insert_le (1 : X) ({g⁻¹ * k * g} : Set X)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨a, haA, ha1, hak⟩ := hex
  apply hno (g * a * g⁻¹) _ _ hak
  · rw [← hz₀k]
    exact hz₀c _ (hconj a haA) |>.symm
  · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hA2 a haA]; group
  · intro h
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

theorem x02M_mul_x01M_entry : ∀ d : F4, (x02M 1 * x01M d) 0 2 = 1 := by
  decide

theorem x02M_mul_x01M_ne_scalar (d e : F4) : x02M 1 * x01M d ≠ Matrix.scalar (Fin 3) e := by
  intro h
  have h1 := x02M_mul_x01M_entry d
  rw [h, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (show (0 : Fin 3) ≠ 2 by decide)] at h1
  exact zero_ne_one h1

theorem rhoS_x02_mul_ne_one (d : F4) : rhoS (x02S 1 * x01S d) ≠ 1 := by
  intro h
  have hker : x02S 1 * x01S d ∈ rhoSL.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val h
  rw [range_rhoSL.2, mem_scalars_iff] at hker
  obtain ⟨e, he⟩ := hker
  exact x02M_mul_x01M_ne_scalar d e he

theorem exists_eight_S : ∃ E : Subgroup S, IsElemTwo E ∧ Nat.card E = 8 := by
  set a := rhoS (x01S 1) with ha
  set b := rhoS (x01S ω) with hb
  set c := rhoS (x02S 1) with hc
  have hsq : ∀ d : F4, rhoS (x01S d) * rhoS (x01S d) = 1 := fun d => by
    rw [rhoS_x01_mul, CharTwo.add_self_eq_zero d, rhoS_x01_zero]
  have hb2 : b * b = 1 := hsq ω
  have ha2 : a * a = 1 := hsq 1
  have hc2 : c * c = 1 := by
    rw [hc, ← map_mul]
    rw [mul_eq_one_iff_eq_inv.mpr (x02S_inv 1).symm]
    exact map_one _
  have hb1 : b ≠ 1 := rhoS_x01_ne_one (by decide)
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two, hb2]) hb1
  have hab : a * b = b * a := by rw [ha, hb, rhoS_x01_mul, rhoS_x01_mul, add_comm]
  have hanb : a ∉ zpowers b := by
    intro h
    rcases (LocalB.mem_zpowers_iff_of_involution b a hb2').mp h with h1 | h1
    · exact rhoS_x01_ne_one (show (1 : F4) ≠ 0 by decide) h1
    · have : rhoS (x01S (1 + ω)) = 1 := by rw [← rhoS_x01_mul, ← ha, ← hb, h1, hb2]
      exact rhoS_x01_ne_one (show (1 + ω : F4) ≠ 0 by decide) this
  obtain ⟨hB, hBc⟩ := elemTwo_zpowers_sup ha2 (isElemTwo_zpowers hb2) (fun y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute a b from hab) i).eq) hanb
  have hBX : zpowers a ⊔ zpowers b ≤ rootX01 :=
    sup_le (zpowers_le.mpr (mem_rootX01.mpr ⟨1, rfl⟩)) (zpowers_le.mpr (mem_rootX01.mpr ⟨ω, rfl⟩))
  have hcX : ∀ y ∈ rootX01, c * y = y * c := by
    intro y hy
    obtain ⟨d, rfl⟩ := mem_rootX01.mp hy
    rw [hc, ← map_mul, ← map_mul, x02S_comm]
  have hcn : c ∉ zpowers a ⊔ zpowers b := by
    intro h
    obtain ⟨d, hd⟩ := mem_rootX01.mp (hBX h)
    apply rhoS_x02_mul_ne_one d
    rw [map_mul, ← hc, hd, hc2]
  obtain ⟨hE, hEc⟩ := elemTwo_zpowers_sup hc2 hB (fun y hy => hcX y (hBX hy)) hcn
  refine ⟨_, hE, ?_⟩
  rw [hEc, hBc, Nat.card_zpowers, hb2']

theorem exists_eight_quotient_of_l34 {L : Subgroup G} (h : IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) :
    ∃ E : Subgroup (↥L ⧸ pPrimeCore 2 ↥L), IsElemTwo E ∧ Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker, h3⟩ := exists_quotient_psl34 h
  by_cases hZ : π.ker = ⊥
  ·
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hZ
    obtain ⟨E₀, hE₀, h8⟩ := exists_eight_S
    refine ⟨E₀.comap π, ⟨fun x hx y hy => hinj ?_, fun x hx => hinj ?_⟩, ?_⟩
    · rw [map_mul, map_mul]
      exact hE₀.1 _ hx _ hy
    · rw [map_mul, map_one]
      exact hE₀.2 _ hx
    · have he : E₀.comap π ≃* (E₀.comap π).map π := equivMapOfInjective _ π hinj
      rw [Nat.card_congr he.toEquiv, map_comap_eq_self_of_surjective hπ, h8]
  ·
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
    have hzc : (z : ↥L ⧸ pPrimeCore 2 ↥L) ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := hker ▸ z.2
    obtain ⟨n, hn⟩ := UnbalancedGS.SwappedCentralProduct.pow_two_pow_eq_one_of_mem_center
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥L) 2) hzc
    have hdvd : orderOf (z : ↥L ⧸ pPrimeCore 2 ↥L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hz1 (Subtype.ext hm)
    have h2z : 2 ∣ Nat.card (zpowers (z : ↥L ⧸ pPrimeCore 2 ↥L)) := by
      rw [Nat.card_zpowers, hm]
      exact dvd_pow_self 2 hm0
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zpowers (z : ↥L ⧸ pPrimeCore 2 ↥L)))
      2 h2z
    set w₀ : ↥L ⧸ pPrimeCore 2 ↥L := z₀.1 with hw₀
    have hw₀2 : orderOf w₀ = 2 := by rw [hw₀, Subgroup.orderOf_coe, hz₀]
    have hw₀K : w₀ ∈ π.ker := (zpowers_le.mpr z.2) z₀.2
    have hw₀c : w₀ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := hker ▸ hw₀K
    have hw₀sq : w₀ * w₀ = 1 := by
      have h := pow_orderOf_eq_one w₀
      rwa [hw₀2, pow_two] at h
    have hw₀1 : w₀ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hw₀2
      exact absurd hw₀2 (by norm_num)
    obtain ⟨Y, hYK, hYab, y₁, hy₁, y₂, hy₂, h₁, h₂, hne₁, hne₂, hne⟩ :=
      exists_four_of_central hπ hker.le h3
    have hy₂o : orderOf y₂ = 2 := orderOf_eq_prime (by rw [pow_two, h₂]) hne₂
    have hy₁n : y₁ ∉ zpowers y₂ := by
      intro h
      rcases (LocalB.mem_zpowers_iff_of_involution y₂ y₁ hy₂o).mp h with h1 | h1
      · exact hne₁ h1
      · exact hne h1
    obtain ⟨hB, hBc⟩ := elemTwo_zpowers_sup h₁ (isElemTwo_zpowers h₂) (fun y hy => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute y₁ y₂ from hYab _ hy₁ _ hy₂) i).eq) hy₁n
    have hBY : zpowers y₁ ⊔ zpowers y₂ ≤ Y := sup_le (zpowers_le.mpr hy₁) (zpowers_le.mpr hy₂)
    have hw₀n : w₀ ∉ zpowers y₁ ⊔ zpowers y₂ := by
      intro h1
      have hm' : w₀ ∈ Y ⊓ π.ker := mem_inf.mpr ⟨hBY h1, hw₀K⟩
      rw [hYK] at hm'
      exact hw₀1 (mem_bot.mp hm')
    obtain ⟨hE, hEc⟩ := elemTwo_zpowers_sup hw₀sq hB
      (fun y _ => (mem_center_iff.mp hw₀c y).symm) hw₀n
    refine ⟨_, hE, ?_⟩
    rw [hEc, hBc, Nat.card_zpowers, hy₂o]

theorem three_le_pRank_of_l34 {L : Subgroup G} (h : IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) :
    3 ≤ pRank 2 ↥L := by
  obtain ⟨E, hE, h8⟩ := exists_eight_quotient_of_l34 h
  have h1 := three_le_pRank_of_card_eight hE h8
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥L) := by
    intro hd
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr hd)
  rwa [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd] at h1

omit [Finite G] in
theorem isEightGroup_conjugate {E : Subgroup G} (hE : IsEightGroup E) (g : G) :
    IsEightGroup (conjugate E g) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g⁻¹⁻¹ by group,
      hE.1.1 x hx y hy]
    group
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * (x * x) * g⁻¹⁻¹ by group,
      hE.1.2 x hx]
    group
  · rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hE.2]

theorem exists_conjugate_le_of_isSylowTwoIn {S H E : Subgroup G} (hS : IsSylowTwoIn S H)
    (hEH : E ≤ H) (hE : IsPGroup 2 E) : ∃ g ∈ H, conjugate E g ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, P, hP⟩ := hS
  have hE' : IsPGroup 2 (E.subgroupOf H) := hE.comap_of_injective _ (subtype_injective H) |>.to_le
    (by intro x hx; exact hx)
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨((h⁻¹ : H) : G), (h⁻¹ : H).2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmem : (⟨x, hEH hx⟩ : H) ∈ (Q : Subgroup H) := hQ hx
  have h1 : h * ⟨x, hEH hx⟩ * h⁻¹ ∈ (P : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨_, hmem, rfl⟩
  rw [hP, mem_subgroupOf] at h1
  simpa [MulAut.conj_apply, inv_inv] using h1

theorem false_of_eightGroup_le_coreActionKernel (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    {E : Subgroup G} (hE : IsEightGroup E) (hEK : E ≤ coreActionKernel L) : False := by
  have hQ := (l34Sec5Basics_of_inputs hS hU hheld hSol hGW G L t S T hset).1
  obtain ⟨-, -, -, hSyl, -, -, -⟩ := hset
  set K := coreActionKernel L with hK
  have hKN : K ≤ normalizer (L : Set G) := fun g hg => (mem_coreActionKernel.mp hg).1
  have hSylK : IsSylowTwoIn (S ⊓ K) K := by
    obtain ⟨hSN, P, hP⟩ := hSyl
    obtain ⟨R, hR⟩ := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSN
      ⟨P, hP⟩ hKN (normalizer_le_normalizer_coreActionKernel L)
    exact ⟨inf_le_right, R, hR⟩
  obtain ⟨g, -, hg⟩ := exists_conjugate_le_of_isSylowTwoIn hSylK hEK hE.1.isPGroup
  have h3 := three_le_pRank_of_eight hg (isEightGroup_conjugate hE g)
  omega

end CFSG.ComponentClassification.GrSLit.GrS5
