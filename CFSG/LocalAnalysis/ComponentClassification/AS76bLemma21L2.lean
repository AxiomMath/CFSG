module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Quot
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups

theorem isSolvable_of_odd_ker {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (χ : X →* Y) (hker : Odd (Nat.card χ.ker)) (hrange : IsPGroup 2 χ.range) :
    Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable χ.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hker
  have : Group.IsSolvable χ.range := by
    have := hrange.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range χ.ker.subtype χ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, range_subtype])

theorem isSolvable_of_odd_index {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    [Group.IsSolvable N] (hodd : Odd N.index) : Group.IsSolvable X := by
  have : Group.IsSolvable (X ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem sq_eq_one_multiplicative {n : ℕ} (x : Multiplicative (Fin n → ZMod 2)) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

theorem card_multiplicative_fin (n : ℕ) : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
  change Nat.card (Fin n → ZMod 2) = 2 ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_sl2_even {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).toEquiv]
  exact CFSG.Walter.psl2_even_card hn

theorem odd_sq_sub_one {n : ℕ} (hn : n ≠ 0) : Odd ((2 ^ n) ^ 2 - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
    (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn⟩, two_ne_zero⟩) odd_one

variable {G : Type} [Group G] [Finite G]

theorem factorization_le_of_caseD {K T Y : Subgroup G} {g : G} (hK : TightlyEmbedded K)
    (hg : g ∉ normalizer (K : Set G)) (hT : IsSylowOf 2 T (rightConjugate K g))
    (hTN : T ≤ normalizer (K : Set G)) (hY : Y = oUpperTwoPrime (K ⊔ T)) {n : ℕ} (hn : n ≠ 0)
    (φ : Y →* Multiplicative (Fin n → ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ) (hker : φ.ker = (oddCoreIn K).subgroupOf Y) :
    (Nat.card K).factorization 2 ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := (Nat.card K).factorization 2 with ha
  have hKT : K ⊓ T = ⊥ := by
    refine eq_bot_of_isPGroup_of_odd (hT.isPGroup.to_le inf_le_right) ?_
    exact (hK.2 g hg).of_dvd_nat (card_dvd_of_le (inf_le_inf_left K hT.le))
  have hT' : Nat.card T = 2 ^ a := by rw [hT.card_eq, rightConjugate_card]
  have hcardKT : Nat.card (K ⊔ T : Subgroup G) = Nat.card K * Nat.card T :=
    AschbacherTheorem3.card_sup_of_le_normalizer hTN hKT
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (K ⊔ T)
  have hSY : S ≤ Y := fun s hs => by
    obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hs⟩
    rw [hY]
    exact mem_oUpperTwoPrime (hS.le hs) (by simpa using congrArg Subtype.val hk)
  have h1 : 2 ^ (a + a) ∣ Nat.card (K ⊔ T : Subgroup G) := by
    rw [hcardKT, hT', pow_add]
    exact mul_dvd_mul (Nat.ordProj_dvd _ _) dvd_rfl
  have h2 : 2 ^ (a + a) ∣ Nat.card Y :=
    (pow_dvd_card_of_isSylowOf hS h1).trans (card_dvd_of_le hSY)
  have hkerodd : Odd (Nat.card φ.ker) := by
    rw [hker, ← card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype]
    exact (odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hcardY : Nat.card Y = (Nat.card φ.ker * ((2 ^ n) ^ 2 - 1)) * 2 ^ (n + n) := by
    rw [← Subgroup.card_ker_mul_card_range φ, MonoidHom.range_eq_top.mpr hφ, card_top,
      Nat.card_prod, card_multiplicative_fin, card_sl2_even hn, pow_add]
    ring
  rw [hcardY] at h2
  have hcop : Nat.Coprime (2 ^ (a + a)) (Nat.card φ.ker * ((2 ^ n) ^ 2 - 1)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (hkerodd.mul (odd_sq_sub_one hn)))
  have h3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
    (hcop.dvd_of_dvd_mul_left h2)
  omega

theorem lemma21_caseD {K R T Y : Subgroup G} {g : G} (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R) (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g)) (hTN : T ≤ normalizer (K : Set G))
    (hY : Y = oUpperTwoPrime (K ⊔ T)) {n : ℕ} (hn : 2 ≤ n)
    (φ : Y →* Multiplicative (Fin n → ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ) (hker : φ.ker = (oddCoreIn K).subgroupOf Y) :
    TightlyEmbedded (oddCoreIn K ⊔ R) ∧
      ∀ r ∈ R, r ≠ 1 → Group.IsSolvable (K ⊓ centralizer ({r} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  set K₂ := oUpperTwoPrime K with hK₂
  set a := (Nat.card K).factorization 2 with ha
  have han : a ≤ n := factorization_le_of_caseD hK hg hT hTN hY hn0 φ hφ hker
  have hRa : Nat.card R = 2 ^ a := hR.card_eq
  have hK₂K : K₂ ≤ K := oUpperTwoPrime_le K
  have hK₂Y : K₂ ≤ Y := by
    rw [hY]
    exact closure_mono fun x ⟨hx, k, hk⟩ => ⟨mem_sup_left hx, k, hk⟩
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := fun r hr => hRe.2 r hr
  have hRK₂ : R ≤ K₂ := fun r hr => mem_oUpperTwoPrime (hR.le hr) (n := 1) (by simpa using hR2 r hr)
  have hφO : ∀ y : Y, φ y = 1 ↔ (y : G) ∈ oddCoreIn K := fun y => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  let ψ : Y →* PSL(2, GaloisField 2 n) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.toMonoidHom.comp
      ((MonoidHom.snd _ _).comp φ)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, hy⟩ := hφ (1, CFSG.Walter.psl2MulEquivSL2OfCharTwo x)
    refine ⟨y, ?_⟩
    change (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm (φ y).2 = x
    rw [hy]
    exact MulEquiv.symm_apply_apply _ _
  have hψφ : ∀ y : Y, ψ y = 1 → φ y ^ 2 = 1 := by
    intro y hy
    have h2 : (φ y).2 = 1 := by simpa [ψ] using hy
    ext1
    · exact sq_eq_one_multiplicative _
    · simp [h2]
  have hL : IsSimpleGroup PSL(2, GaloisField 2 n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n hn0]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hcardL : Nat.card PSL(2, GaloisField 2 n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.Walter.psl2_even_card hn0
  have hK₂n : (K₂.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK₂Y).mpr ((hY.le.trans (oUpperTwoPrime_le _)).trans
      ((sup_le le_normalizer hTN).trans (normalizer_le_normalizer_oUpperTwoPrime K)))
  have hJn : ((K₂.subgroupOf Y).map ψ).Normal := hK₂n.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K₂.subgroupOf Y).map ψ) with hJ | hJ
  ·
    have hsq : ∀ k ∈ K₂, k ^ 2 ∈ oddCoreIn K := by
      intro k hk
      have hk1 : ψ ⟨k, hK₂Y hk⟩ = 1 := by
        have : ψ ⟨k, hK₂Y hk⟩ ∈ (K₂.subgroupOf Y).map ψ := ⟨⟨k, hK₂Y hk⟩, hk, rfl⟩
        rwa [hJ, mem_bot] at this
      have := (hφO (⟨k, hK₂Y hk⟩ ^ 2)).mp (by rw [map_pow]; exact hψφ _ hk1)
      simpa using this
    obtain ⟨hTE, hsolv⟩ := tightlyEmbedded_and_isSolvable_of_twoElements hK hR
      (twoElements_le_of_sq_mem hR hsq)
    exact ⟨hTE, fun r _ _ => Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : K ⊓ centralizer ({r} : Set G) ≤ K))⟩
  let ψ₂ : K₂.subgroupOf Y →* PSL(2, GaloisField 2 n) := ψ.comp (K₂.subgroupOf Y).subtype
  have hψ₂r : ψ₂.range = ⊤ := by rw [MonoidHom.range_comp, range_subtype, hJ]
  have hcardK₂ : Nat.card ψ₂.ker * Nat.card PSL(2, GaloisField 2 n) = Nat.card K₂ := by
    have h := Subgroup.card_ker_mul_card_range ψ₂
    rw [hψ₂r, card_top, Nat.card_congr (subgroupOfEquivOfLe hK₂Y).toEquiv] at h
    exact h
  have hRK₂s : IsSylowOf 2 R K₂ := hR.of_le hRK₂ hK₂K
  have hdvdK₂ : ∀ j, 2 ^ j ∣ Nat.card K₂ → j ≤ a := fun j hj => by
    have := pow_dvd_card_of_isSylowOf hRK₂s hj
    rw [hRa] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hna : n ≤ a := hdvdK₂ n (by
    rw [← hcardK₂, hcardL]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have hkerodd : Odd (Nat.card ψ₂.ker) := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp he
    have h := hdvdK₂ (n + 1) (by
      rw [← hcardK₂, hcardL, hm, pow_succ]
      exact ⟨m * ((2 ^ n) ^ 2 - 1), by ring⟩)
    omega
  have hkey : ∀ y : Y, (y : G) ∈ K₂ → ψ y = 1 → (y : G) ∈ oddCoreIn K := by
    intro y hyK hy
    have hx : (⟨y, hyK⟩ : K₂.subgroupOf Y) ∈ ψ₂.ker := hy
    have hdvd1 : orderOf (φ y) ∣ 2 := orderOf_dvd_of_pow_eq_one (hψφ y hy)
    have hdvd2 : orderOf (φ y) ∣ Nat.card ψ₂.ker := by
      let χ := φ.comp ((K₂.subgroupOf Y).subtype.comp ψ₂.ker.subtype)
      have h1 : χ ⟨_, hx⟩ = φ y := rfl
      rw [← h1]
      exact (orderOf_map_dvd χ _).trans (orderOf_dvd_natCard _)
    have h1 : orderOf (φ y) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hkerodd) hdvd1 hdvd2
    exact (hφO y).mp (orderOf_eq_one_iff.mp h1)
  have hRinj : ∀ ρ ∈ R, ∀ hρ : ρ ∈ Y, ψ ⟨ρ, hρ⟩ = 1 → ρ = 1 := by
    intro ρ hρR hρ h
    have : ρ ∈ oddCoreIn K ⊓ R := ⟨hkey ⟨ρ, hρ⟩ (hRK₂ hρR) h, hρR⟩
    rwa [oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at this
  have hinv : ∀ r ∈ R, r ≠ 1 → ∀ hr : r ∈ Y, orderOf (ψ ⟨r, hr⟩) = 2 := by
    intro r hrR hr1 hr
    refine orderOf_eq_prime ?_ fun h => hr1 (hRinj r hrR hr h)
    rw [← map_pow]
    have : (⟨r, hr⟩ : Y) ^ 2 = 1 := Subtype.ext (by simpa using hR2 r hrR)
    rw [this, map_one]
  have hU : ∀ r ∈ R, r ≠ 1 → ∀ hr : r ∈ Y,
      centralizer ({ψ ⟨r, hr⟩} : Set PSL(2, GaloisField 2 n)) = (R.subgroupOf Y).map ψ := by
    intro r hrR hr1 hr
    have hC := CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo (hinv r hrR hr1 hr)
    have hUC : (R.subgroupOf Y).map ψ ≤
        centralizer ({ψ ⟨r, hr⟩} : Set PSL(2, GaloisField 2 n)) := by
      rintro _ ⟨ρ, hρ, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h := congrArg Subtype.val
        (hRe.1.is_comm.comm ⟨ρ, mem_subgroupOf.mp hρ⟩ ⟨r, hrR⟩)
      simpa using h
    have hinj : Function.Injective (ψ.comp (R.subgroupOf Y).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      rintro ⟨⟨ρ, hρY⟩, hρR⟩ hρ
      have h := hRinj ρ (mem_subgroupOf.mp hρR) hρY hρ
      rw [mem_bot]
      exact Subtype.ext (Subtype.ext h)
    have hUcard : Nat.card ((R.subgroupOf Y).map ψ) = 2 ^ n := by
      rw [← range_subtype (R.subgroupOf Y), ← MonoidHom.range_comp,
        ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe (hRK₂.trans hK₂Y)).toEquiv, hRa,
        le_antisymm han hna]
    have hCcard : Nat.card (centralizer ({ψ ⟨r, hr⟩} : Set PSL(2, GaloisField 2 n))) ≤ 2 ^ n := by
      obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hC
      have h1 : 2 ^ c ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
        rw [← hc, ← hcardL]
        exact card_subgroup_dvd_card _
      have h2 := (Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr
        (odd_sq_sub_one hn0))).dvd_of_dvd_mul_right h1
      rw [hc]
      exact Nat.le_of_dvd (by positivity) h2
    exact (eq_of_le_of_card_ge hUC (hCcard.trans hUcard.ge)).symm
  have hTI : ∀ w ∈ normalizer (K : Set G), ∀ r ∈ R, r ≠ 1 → w * r * w⁻¹ ∈ R →
      w ∈ normalizer ((oddCoreIn K ⊔ R : Subgroup G) : Set G) := by
    intro w hw r hrR hr1 hwr
    have hR' : rightConjugate R w ≤ oddCoreIn K ⊔ R := by
      intro z hz
      rw [mem_rightConjugate_iff] at hz
      have hzK : z ∈ K := by
        have h := (mem_normalizer_iff.mp (inv_mem hw) _).mp (hR.le hz)
        simpa [mul_assoc] using h
      have hz2 : z ^ 2 = 1 := by
        have h := hR2 _ hz
        rw [conj_pow] at h
        simpa using h
      have hzK₂ : z ∈ K₂ := mem_oUpperTwoPrime hzK (n := 1) (by simpa using hz2)
      have hrY : r ∈ Y := hK₂Y (hRK₂ hrR)
      have hzY : z ∈ Y := hK₂Y hzK₂
      have hzr : z * r = r * z := by
        have h' : (w * z * w⁻¹) * (w * r * w⁻¹) = (w * r * w⁻¹) * (w * z * w⁻¹) :=
          congrArg Subtype.val (hRe.1.is_comm.comm ⟨_, hz⟩ ⟨_, hwr⟩)
        have : w * (z * r) * w⁻¹ = w * (r * z) * w⁻¹ := by
          calc w * (z * r) * w⁻¹ = (w * z * w⁻¹) * (w * r * w⁻¹) := by group
            _ = (w * r * w⁻¹) * (w * z * w⁻¹) := h'
            _ = w * (r * z) * w⁻¹ := by group
        simpa using this
      have hzC : ψ ⟨z, hzY⟩ ∈ centralizer ({ψ ⟨r, hrY⟩} : Set PSL(2, GaloisField 2 n)) := by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hzr
      rw [hU r hrR hr1 hrY] at hzC
      obtain ⟨⟨ρ, hρY⟩, hρR, hρz⟩ := hzC
      have hρR' : ρ ∈ R := mem_subgroupOf.mp hρR
      have hzρ : ψ (⟨z, hzY⟩ * (⟨ρ, hρY⟩ : Y)⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hρz, mul_inv_cancel]
      have hO' := hkey _ (K₂.mul_mem hzK₂ (K₂.inv_mem (hRK₂ hρR'))) hzρ
      have hzeq : z = (z * ρ⁻¹) * ρ := by group
      rw [hzeq]
      exact mul_mem (mem_sup_left (by simpa using hO')) (mem_sup_right hρR')
    have hwinv : w⁻¹ ∈ normalizer ((oddCoreIn K ⊔ R : Subgroup G) : Set G) :=
      mem_normalizer_of_map_conj_le (map_conj_le_of_map_conj_le (inv_mem hw) hR')
    simpa using inv_mem hwinv
  refine ⟨tightlyEmbedded_of_conj_mem hK (sup_le (oddCoreIn_le K) hR.le) hR le_sup_right hTI, ?_⟩
  intro r hrR hr1
  have hrY : r ∈ Y := hK₂Y (hRK₂ hrR)
  have hC₂Y : K₂ ⊓ (K ⊓ centralizer ({r} : Set G)) ≤ Y := inf_le_left.trans hK₂Y
  let χ : ↥(K₂ ⊓ (K ⊓ centralizer ({r} : Set G))) →* PSL(2, GaloisField 2 n) :=
    ψ.comp (Subgroup.inclusion hC₂Y)
  have hχker : Odd (Nat.card χ.ker) := by
    have hle : χ.ker.map (K₂ ⊓ (K ⊓ centralizer ({r} : Set G))).subtype ≤ oddCoreIn K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hkey (Subgroup.inclusion hC₂Y x) x.2.1 hx
    rw [← card_map_of_injective (Subgroup.subtype_injective _)]
    exact (odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le hle)
  have hχrange : IsPGroup 2 χ.range := by
    refine (CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo (hinv r hrR hr1 hrY)).to_le ?_
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change ψ (Subgroup.inclusion hC₂Y x) * ψ ⟨r, hrY⟩ = ψ ⟨r, hrY⟩ * ψ (Subgroup.inclusion hC₂Y x)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_mul, Subgroup.coe_inclusion]
    exact mem_centralizer_singleton_iff.mp x.2.2.2
  have hC₂solv : Group.IsSolvable ↥(K₂ ⊓ (K ⊓ centralizer ({r} : Set G))) :=
    isSolvable_of_odd_ker χ hχker hχrange
  have hC₂C : K₂ ⊓ (K ⊓ centralizer ({r} : Set G)) ≤ K ⊓ centralizer ({r} : Set G) :=
    inf_le_right
  have hC₂n : ((K₂ ⊓ (K ⊓ centralizer ({r} : Set G))).subgroupOf
      (K ⊓ centralizer ({r} : Set G))).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hC₂C).mpr fun c hc => ?_
    have hcK₂ : c ∈ normalizer (K₂ : Set G) :=
      normalizer_le_normalizer_oUpperTwoPrime K (le_normalizer hc.1)
    have hcC : c ∈ normalizer ((K ⊓ centralizer ({r} : Set G) : Subgroup G) : Set G) :=
      le_normalizer hc
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨(mem_normalizer_iff.mp hcK₂ x).mp hx1, (mem_normalizer_iff.mp hcC x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨(mem_normalizer_iff.mp hcK₂ x).mpr hx1, (mem_normalizer_iff.mp hcC x).mpr hx2⟩
  have : Group.IsSolvable ((K₂ ⊓ (K ⊓ centralizer ({r} : Set G))).subgroupOf
      (K ⊓ centralizer ({r} : Set G))) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hC₂C).toMonoidHom)
      (subgroupOfEquivOfLe hC₂C).injective
  refine isSolvable_of_odd_index ((K₂ ⊓ (K ⊓ centralizer ({r} : Set G))).subgroupOf
    (K ⊓ centralizer ({r} : Set G))) ?_
  change Odd ((K₂ ⊓ (K ⊓ centralizer ({r} : Set G))).relIndex (K ⊓ centralizer ({r} : Set G)))
  have hK₂n' : (K₂.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK₂K).mpr
      ((le_normalizer).trans (normalizer_le_normalizer_oUpperTwoPrime K))
  have hdvd : K₂.relIndex (K ⊓ centralizer ({r} : Set G)) ∣ K₂.relIndex K := by
    have h := relIndex_dvd_index_of_normal (H := K₂.subgroupOf K)
      (K := (K ⊓ centralizer ({r} : Set G)).subgroupOf K)
    rw [relIndex_subgroupOf (inf_le_left : K ⊓ centralizer ({r} : Set G) ≤ K)] at h
    exact h
  have hodd : Odd (K₂.relIndex K) := by
    refine Nat.not_even_iff_odd.mp fun he => (isSylowOf_iff.mp hR).2.2 ?_
    rw [← relIndex_mul_relIndex R K₂ K hRK₂ hK₂K]
    exact (even_iff_two_dvd.mp he).mul_left _
  rw [inf_relIndex_right]
  exact hodd.of_dvd_nat hdvd

end CFSG.ComponentClassification.AS76b
