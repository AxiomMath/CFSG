module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17Odd
public import CFSG.LocalAnalysis.ComponentClassification.AS81SL2Rigid
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Cent

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_oddCoreIn_of_caseD {K R T Y : Subgroup G} {g : G} (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R) (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g)) (hTN : T ≤ normalizer (K : Set G))
    (hY : Y = oUpperTwoPrime (K ⊔ T)) {n : ℕ} (hn : 2 ≤ n)
    (φ : Y →* Multiplicative (Fin n → ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ) (hker : φ.ker = (oddCoreIn K).subgroupOf Y)
    {c : G} (hcK : c ∈ K) (hc : Odd (orderOf c))
    (hcR : ∀ ρ ∈ R, c * ρ * c⁻¹ * ρ⁻¹ ∈ oddCoreIn K) : c ∈ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  set O := oddCoreIn K with hO
  set K₂ := oUpperTwoPrime K with hK₂
  set a := (Nat.card K).factorization 2 with ha
  have han : a ≤ n := factorization_le_of_caseD hK hg hT hTN hY hn0 φ hφ hker
  have hRa : Nat.card R = 2 ^ a := hR.card_eq
  have hK₂K : K₂ ≤ K := oUpperTwoPrime_le K
  have hK₂Y : K₂ ≤ Y := by
    rw [hY]
    exact closure_mono fun x ⟨hx, k, hk⟩ => ⟨mem_sup_left hx, k, hk⟩
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := fun r hr => hRe.2 r hr
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRK₂ : R ≤ K₂ := fun r hr =>
    mem_oUpperTwoPrime (hR.le hr) (n := 1) (by simpa using hR2 r hr)
  have hφO : ∀ y : Y, φ y = 1 ↔ (y : G) ∈ O := fun y => by
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
    have hsq : ∀ k ∈ K₂, k ^ 2 ∈ O := by
      intro k hk
      have hk1 : ψ ⟨k, hK₂Y hk⟩ = 1 := by
        have : ψ ⟨k, hK₂Y hk⟩ ∈ (K₂.subgroupOf Y).map ψ := ⟨⟨k, hK₂Y hk⟩, hk, rfl⟩
        rwa [hJ, mem_bot] at this
      have := (hφO (⟨k, hK₂Y hk⟩ ^ 2)).mp (by rw [map_pow]; exact hψφ _ hk1)
      simpa using this
    exact mem_oddCoreIn_of_twoElements hR hRc (twoElements_le_of_sq_mem hR hsq) hcK hc hcR
  let ψ₃ : ↥K₂ →* PSL(2, GaloisField 2 n) := ψ.comp (Subgroup.inclusion hK₂Y)
  have hψ₃ : Function.Surjective ψ₃ := by
    intro z
    have hz : z ∈ (K₂.subgroupOf Y).map ψ := by rw [hJ]; exact mem_top z
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨⟨y, mem_subgroupOf.mp hy⟩, rfl⟩
  have hcardK₂ : Nat.card ψ₃.ker * Nat.card PSL(2, GaloisField 2 n) = Nat.card K₂ := by
    have h := Subgroup.card_ker_mul_card_range ψ₃
    rw [MonoidHom.range_eq_top.mpr hψ₃, card_top] at h
    exact h
  have hRK₂s : IsSylowOf 2 R K₂ := hR.of_le hRK₂ hK₂K
  have hdvdK₂ : ∀ j, 2 ^ j ∣ Nat.card K₂ → j ≤ a := fun j hj => by
    have := pow_dvd_card_of_isSylowOf hRK₂s hj
    rw [hRa] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hna : n ≤ a := hdvdK₂ n (by
    rw [← hcardK₂, hcardL]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have hkerodd : Odd (Nat.card ψ₃.ker) := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp he
    have h := hdvdK₂ (n + 1) (by
      rw [← hcardK₂, hcardL, hm, pow_succ]
      exact ⟨m * ((2 ^ n) ^ 2 - 1), by ring⟩)
    omega
  have hkey : ∀ k : ↥K₂, ψ₃ k = 1 ↔ (k : G) ∈ O := by
    intro k
    constructor
    · intro hk
      have hdvd1 : orderOf (φ (Subgroup.inclusion hK₂Y k)) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (hψφ _ hk)
      have hdvd2 : orderOf (φ (Subgroup.inclusion hK₂Y k)) ∣ Nat.card ψ₃.ker := by
        let χ := φ.comp ((Subgroup.inclusion hK₂Y).comp ψ₃.ker.subtype)
        have h1 : χ ⟨k, hk⟩ = φ (Subgroup.inclusion hK₂Y k) := rfl
        rw [← h1]
        exact (orderOf_map_dvd χ _).trans (orderOf_dvd_natCard _)
      have h1 : orderOf (φ (Subgroup.inclusion hK₂Y k)) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hkerodd) hdvd1 hdvd2
      exact (hφO _).mp (orderOf_eq_one_iff.mp h1)
    · intro hk
      have h1 : φ (Subgroup.inclusion hK₂Y k) = 1 := (hφO _).mpr hk
      change (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm
        (φ (Subgroup.inclusion hK₂Y k)).2 = 1
      rw [h1]
      exact map_one _
  have hcK₂ : c ∈ normalizer (K₂ : Set G) :=
    normalizer_le_normalizer_oUpperTwoPrime K (le_normalizer hcK)
  set σ := normalizerConj hcK₂ with hσdef
  have hσa : ∀ k : ↥K₂, ((σ k : ↥K₂) : G) = c * k * c⁻¹ := fun k => by
    rw [hσdef, coe_normalizerConj_apply]
  have hσ : ψ₃.ker.map (σ : ↥K₂ →* ↥K₂) = ψ₃.ker := by
    have hle : ψ₃.ker.map (σ : ↥K₂ →* ↥K₂) ≤ ψ₃.ker := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ O := (hkey k).mp hk
      show ψ₃ (σ k) = 1
      rw [hkey, hσa]
      exact (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K hcK) k).mp hk'
    exact eq_of_le_of_card_ge hle (le_of_eq (card_map_of_injective σ.injective).symm)
  set α := descendAut ψ₃ hψ₃ σ hσ with hαdef
  have hαa : ∀ k : ↥K₂, α (ψ₃ k) = ψ₃ (σ k) := fun k => descendAut_apply ψ₃ hψ₃ σ hσ k
  have hσpow : ∀ m : ℕ, ∀ k : ↥K₂, (((σ ^ m) k : ↥K₂) : G) = c ^ m * k * (c ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      rw [pow_succ σ m, MulAut.mul_apply, ih, hσa]
      group
  have hαpow : ∀ m : ℕ, ∀ k : ↥K₂, (α ^ m) (ψ₃ k) = ψ₃ ((σ ^ m) k) := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      rw [pow_succ α m, MulAut.mul_apply, hαa, ih, pow_succ σ m, MulAut.mul_apply]
  have hαn : α ^ orderOf c = 1 := by
    ext x
    obtain ⟨k, rfl⟩ := hψ₃ x
    rw [hαpow, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hσpow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have hαodd : Odd (orderOf α) := hc.of_dvd_nat (orderOf_dvd_of_pow_eq_one hαn)
  set U := (R.subgroupOf K₂).map ψ₃ with hUdef
  have hinj : Function.Injective (ψ₃.comp (R.subgroupOf K₂).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨ρ, hρK₂⟩, hρR⟩ hρ
    have h1 : ρ ∈ O := (hkey ⟨ρ, hρK₂⟩).mp hρ
    have h2 : ρ ∈ O ⊓ R := ⟨h1, mem_subgroupOf.mp hρR⟩
    rw [oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at h2
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h2)
  have hUcard : Nat.card U = 2 ^ n := by
    rw [hUdef, ← range_subtype (R.subgroupOf K₂), ← MonoidHom.range_comp,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hRK₂).toEquiv, hRa, le_antisymm han hna]
  have hαU : ∀ u ∈ U, α u = u := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hαa]
    have hk' : (k : G) ∈ R := mem_subgroupOf.mp hk
    have hmem : ((σ k * k⁻¹ : ↥K₂) : G) ∈ O := by
      rw [coe_mul, hσa, coe_inv]
      exact hcR k hk'
    have h1 := (hkey (σ k * k⁻¹)).mpr hmem
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hα1 : α = 1 := psl2_aut_eq_one_of_fix hn hUcard hαodd hαU
  have hcK₂O : ∀ x ∈ K₂, c * x * c⁻¹ * x⁻¹ ∈ O := by
    intro x hx
    have h1 : ψ₃ (σ ⟨x, hx⟩) = ψ₃ ⟨x, hx⟩ := by rw [← hαa, hα1, MulAut.one_apply]
    have h2 : ψ₃ (σ ⟨x, hx⟩ * (⟨x, hx⟩ : ↥K₂)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hkey _).mp h2
    rwa [coe_mul, hσa, coe_inv] at h3
  have hconjO : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho =>
    (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K hk) o).mp ho
  have hK₂n' : K ≤ normalizer (K₂ : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_oUpperTwoPrime K)
  let D : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ x ∈ K₂, k * x * k⁻¹ * x⁻¹ ∈ O}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨K.mul_mem ha hb, fun x hx => ?_⟩
        have hbx : b * x * b⁻¹ ∈ K₂ := (mem_normalizer_iff.mp (hK₂n' hb) x).mp hx
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            (a * (b * x * b⁻¹) * a⁻¹ * (b * x * b⁻¹)⁻¹) * (b * x * b⁻¹ * x⁻¹) := by group
        rw [e]
        exact O.mul_mem (ha' _ hbx) (hb' x hx)
      one_mem' := ⟨K.one_mem, fun x _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact O.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨K.inv_mem ha, fun x hx => ?_⟩
        have hax : a⁻¹ * x * a ∈ K₂ := by
          have := (mem_normalizer_iff.mp (hK₂n' (K.inv_mem ha)) x).mp hx
          simpa using this
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
            (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
        rw [e]
        exact O.inv_mem (ha' _ hax) }
  have hcD : c ∈ D := ⟨hcK, hcK₂O⟩
  have hDK : D ≤ K := fun k hk => hk.1
  have hDn : K ≤ normalizer (D : Set G) := by
    intro y hy
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨k, ⟨hk, hk'⟩, rfl⟩
    refine ⟨K.mul_mem (K.mul_mem hy hk) (K.inv_mem hy), fun x hx => ?_⟩
    have hyx : y⁻¹ * x * y ∈ K₂ := by
      have := (mem_normalizer_iff.mp (hK₂n' (K.inv_mem hy)) x).mp hx
      simpa using this
    change y * k * y⁻¹ * x * (y * k * y⁻¹)⁻¹ * x⁻¹ ∈ O
    have e : y * k * y⁻¹ * x * (y * k * y⁻¹)⁻¹ * x⁻¹ =
        y * (k * (y⁻¹ * x * y) * k⁻¹ * (y⁻¹ * x * y)⁻¹) * y⁻¹ := by group
    rw [e]
    exact hconjO y hy _ (hk' _ hyx)
  have hDodd : Odd (Nat.card D) := by
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => ?_)
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 h2
    have hd2 : (d : G) ^ 2 = 1 := by
      have := pow_orderOf_eq_one d
      rw [hd] at this
      exact congrArg Subtype.val this
    have hdK₂ : (d : G) ∈ K₂ := mem_oUpperTwoPrime (hDK d.2) (n := 1) (by simpa using hd2)
    have hdO : (d : G) ∈ O := by
      by_contra hdO
      have hψd : ψ₃ ⟨d, hdK₂⟩ ≠ 1 := fun h => hdO ((hkey _).mp h)
      have hψd2 : orderOf (ψ₃ ⟨d, hdK₂⟩) = 2 := by
        refine orderOf_eq_prime ?_ hψd
        rw [← map_pow]
        have : (⟨d, hdK₂⟩ : ↥K₂) ^ 2 = 1 := Subtype.ext (by simpa using hd2)
        rw [this, map_one]
      have hC := CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo hψd2
      have htop : centralizer ({ψ₃ ⟨d, hdK₂⟩} : Set PSL(2, GaloisField 2 n)) = ⊤ := by
        rw [eq_top_iff]
        intro z _
        obtain ⟨x, rfl⟩ := hψ₃ z
        rw [mem_centralizer_singleton_iff]
        have h1 := (hkey (⟨d, hdK₂⟩ * x * (⟨d, hdK₂⟩ : ↥K₂)⁻¹ * x⁻¹)).mpr (by
          simpa using d.2.2 x x.2)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
        have : ψ₃ ⟨d, hdK₂⟩ * ψ₃ x = ψ₃ x * ψ₃ ⟨d, hdK₂⟩ := by
          calc ψ₃ ⟨d, hdK₂⟩ * ψ₃ x
              = ψ₃ ⟨d, hdK₂⟩ * ψ₃ x * (ψ₃ ⟨d, hdK₂⟩)⁻¹ * (ψ₃ x)⁻¹ * (ψ₃ x * ψ₃ ⟨d, hdK₂⟩) := by
                group
            _ = ψ₃ x * ψ₃ ⟨d, hdK₂⟩ := by rw [h1, one_mul]
        exact this.symm
      rw [htop] at hC
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hC
      rw [card_top, hcardL] at hk
      have hodd : Odd ((2 ^ n) ^ 2 - 1) := odd_sq_sub_one hn0
      have hdvd : (2 ^ n) ^ 2 - 1 ∣ 2 ^ k := ⟨2 ^ n, by rw [← hk]; ring⟩
      have h1 : (2 ^ n) ^ 2 - 1 = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
          dvd_rfl hdvd
      have h3 : 16 ≤ (2 ^ n) ^ 2 := by
        calc 16 = (2 ^ 2) ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hn) 2
      omega
    have h1 : orderOf (d : G) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hdO
    rw [Subgroup.orderOf_coe, hd] at h1
    exact absurd ((odd_card_oddCoreIn K).of_dvd_nat h1) (by decide)
  exact le_oddCoreIn_of_odd_normal hDK hDn hDodd hcD

theorem mem_oddCoreIn_of_commutator_mem (h4 : Asc75Theorem4) {K R : Subgroup G}
    (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R)
    (hF : IsSimpleGroup (CFSG.generalizedFitting G)) (hKn : ¬ K.Normal) {c : G} (hcK : c ∈ K)
    (hc : Odd (orderOf c)) (hcR : ∀ ρ ∈ R, c * ρ * c⁻¹ * ρ⁻¹ ∈ oddCoreIn K) :
    c ∈ oddCoreIn K := by
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  by_cases hA : twoPrimeLayerIn K = oddCoreIn K
  · exact mem_oddCoreIn_of_twoElements hR hRc (twoElements_le_of_layer_eq_bot hR hRe
      ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mp hA)) hcK hc hcR
  · rcases h4 G K hK hA with hB | ⟨h1, -⟩ | ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩
    · exact (false_of_normalIn_twoPrimeLayerIn_top hK hKn hF hA hB).elim
    · exact (false_of_pRank_twoPrimeLayerIn_eq_one hR hRe hA h1).elim
    · exact mem_oddCoreIn_of_caseD hK hR hRe hg hT hTN rfl hn φ hφ hker hcK hc hcR

theorem le_oddCoreIn_of_le_normalizer (h4 : Asc75Theorem4) {K R Y : Subgroup G}
    (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R)
    (hR4 : 2 ^ 2 ≤ Nat.card R) (hF : IsSimpleGroup (CFSG.generalizedFitting G))
    (hKn : ¬ K.Normal) (hYK : Y ≤ K) (hRY : R ≤ normalizer (Y : Set G))
    (hY : Odd (Nat.card Y)) : Y ≤ oddCoreIn K := by
  obtain ⟨hL, -⟩ := lemma21 h4 hK hR hRe hF hKn
  set O := oddCoreIn K with hO
  set L := O ⊔ R with hLdef
  have hRL : R ≤ L := le_sup_right
  have hYN : Y ≤ normalizer (L : Set G) := by
    refine le_of_forall_inf_centralizer_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one hRe.2)
      hR4
      (fun h2 => (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h2)) hRY ?_
    intro r hr hr1 y hy
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hL (hRL hr) hr1
      (hRe.2 r hr) (mem_centralizer_singleton_iff.mp hy.2)
  intro y hy
  have hyo : Odd (orderOf y) := hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
  refine mem_oddCoreIn_of_commutator_mem h4 hK hR hRe hF hKn (hYK hy) hyo fun ρ hρ => ?_
  have h1 : y * ρ * y⁻¹ * ρ⁻¹ ∈ L :=
    L.mul_mem ((mem_normalizer_iff.mp (hYN hy) ρ).mp (hRL hρ)) (L.inv_mem (hRL hρ))
  have h2 : y * ρ * y⁻¹ * ρ⁻¹ ∈ Y := by
    have e : y * ρ * y⁻¹ * ρ⁻¹ = y * (ρ * y⁻¹ * ρ⁻¹) := by group
    rw [e]
    exact Y.mul_mem hy ((mem_normalizer_iff.mp (hRY hρ) _).mp (Y.inv_mem hy))
  exact mem_oddCoreIn_of_mem_sup_of_odd hR.le hR.isPGroup h1
    (hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y h2))

end CFSG.ComponentClassification.AS81
