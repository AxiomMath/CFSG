module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Harada
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitDD

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup

variable {X : Type} [Group X]

theorem card_sq_eq_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card {g : G // g ^ 2 = x} = Nat.card {h : H // h ^ 2 = e x} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun g => by
    change g ^ 2 = x ↔ e g ^ 2 = e x
    rw [← map_pow, e.apply_eq_iff_eq])

@[expose] noncomputable def conjNormalizer {P : Subgroup X} {w : X}
    (hw : w ∈ normalizer (P : Set X)) :
    P ≃* P :=
  ((MulAut.conj w).subgroupMap P).trans (MulEquiv.subgroupCongr (by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (mem_normalizer_iff.mp hw p).mp hp
    · intro hg
      refine ⟨w⁻¹ * g * w, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem hw) g).mp hg
      rwa [inv_inv] at this))

theorem coe_conjNormalizer {P : Subgroup X} {w : X} (hw : w ∈ normalizer (P : Set X)) (g : P) :
    (conjNormalizer hw g : X) = w * g * w⁻¹ := rfl

namespace A7Data

variable [Finite X] {t : X} {L : Subgroup X} (A : A7Data t L)

theorem T_le_normalizer : A.T ≤ normalizer (L : Set X) :=
  A.T_le_centralizer.trans A.config.le_normalizer

theorem conj_mem_R {g r : X} (hg : g ∈ A.T) (hr : r ∈ A.R) : g * r * g⁻¹ ∈ A.R :=
  Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hr.1) (inv_mem hg),
    (mem_normalizer_iff.mp (A.T_le_normalizer hg) r).mp hr.2⟩

theorem conj_mem_K {g k : X} (hg : g ∈ A.T) (hk : k ∈ A.K) : g * k * g⁻¹ ∈ A.K :=
  Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hk.1) (inv_mem hg),
    (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L (A.T_le_normalizer hg))
      k).mp hk.2⟩

theorem commute_of_ψ_eq_c0 {g : X} (hg : g ∈ A.T) (hψ : A.ψ ⟨g, hg⟩ = c0) {r : X}
    (hr : r ∈ A.R) : g * r = r * g := by
  have hm := A.conj_mem_R hg hr
  have h := A.eq_of_ψ_eq hm hr (by
    have : (⟨g * r * g⁻¹, hm.1⟩ : A.T) = ⟨g, hg⟩ * ⟨r, hr.1⟩ * (⟨g, hg⟩)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hψ, ← c0_comm_of_mem_P0 (A.ψ_mem_P0 _),
      mul_inv_cancel_right])
  calc g * r = g * r * g⁻¹ * g := by group
    _ = r * g := by rw [h]

theorem eq_pow_of_mem_K (hK : Nat.card A.K = 4) {c : X} (hc : c ∈ A.K) (hco : orderOf c = 4)
    {x : X} (hx : x ∈ A.K) : ∃ j < 4, x = c ^ j := by
  classical
  have hle : zpowers c ≤ A.K := zpowers_le.mpr hc
  have heq : zpowers c = A.K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hK, Nat.card_zpowers, hco])
  rw [← heq, mem_zpowers_iff_mem_range_orderOf, hco] at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨j, Finset.mem_range.mp hj, rfl⟩

theorem exists_dihedral_partner (hK : Nat.card A.K = 4) {c : X} (hc : c ∈ A.K)
    (hco : orderOf c = 4) {i : X} (hi : i ∈ A.T) (hi2 : i ^ 2 = 1) (hic : c * i ≠ i * c) :
    ∃ k : X, ∃ hk : k ∈ A.T, k ^ 2 = 1 ∧ A.ψ ⟨k, hk⟩ = c0 ∧ k * c * k⁻¹ = c⁻¹ := by
  have hcK : ∀ x ∈ A.K, c * x = x * c := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := A.eq_pow_of_mem_K hK hc hco hx
    exact (Commute.self_pow c j).eq
  have hiR : A.ψ ⟨i, hi⟩ ∉ R0 := by
    intro h
    obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq h
    have hm : r⁻¹ * i ∈ A.T := mul_mem (inv_mem hr.1) hi
    have hk : r⁻¹ * i ∈ A.K := by
      rw [A.mem_K_iff hm]
      have : (⟨r⁻¹ * i, hm⟩ : A.T) = (⟨r, hr.1⟩ : A.T)⁻¹ * ⟨i, hi⟩ := rfl
      rw [this, map_mul, map_inv, hψr, inv_mul_cancel]
    apply hic
    calc c * i = c * r * (r⁻¹ * i) := by group
      _ = r * c * (r⁻¹ * i) := by rw [← A.commute_of_mem_R_of_mem_K hr hc]
      _ = r * (r⁻¹ * i) * c := by rw [mul_assoc, hcK _ hk, ← mul_assoc]
      _ = i * c := by group
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (mul_c0_mem_R0_of_not_mem (A.ψ_mem_P0 _) hiR)
  set k := r⁻¹ * i with hkdef
  have hkT : k ∈ A.T := mul_mem (inv_mem hr.1) hi
  have hψk : A.ψ ⟨k, hkT⟩ = c0 := by
    have : (⟨k, hkT⟩ : A.T) = (⟨r, hr.1⟩ : A.T)⁻¹ * ⟨i, hi⟩ := rfl
    rw [this, map_mul, map_inv, hψr, mul_inv_rev, inv_mul_cancel_right, show c0⁻¹ = c0 by decide]
  have hicK : i * c * i⁻¹ ∈ A.K := A.conj_mem_K hi hc
  have hkc' : k * c * k⁻¹ = i * c * i⁻¹ := by
    have h := A.commute_of_mem_R_of_mem_K (inv_mem hr) hicK
    calc k * c * k⁻¹ = r⁻¹ * (i * c * i⁻¹) * r := by rw [hkdef]; group
      _ = (i * c * i⁻¹) * r⁻¹ * r := by rw [h]
      _ = i * c * i⁻¹ := by group
  have hkc : k * c * k⁻¹ = c⁻¹ := by
    rw [hkc']
    obtain ⟨j, hj, hjc⟩ := A.eq_pow_of_mem_K hK hc hco hicK
    have ho : orderOf (i * c * i⁻¹) = 4 := by
      rw [show i * c * i⁻¹ = MulAut.conj i c from rfl, MulEquiv.orderOf_eq, hco]
    rw [hjc] at ho ⊢
    have hc4 : c ^ 4 = 1 := by rw [← hco, pow_orderOf_eq_one]
    interval_cases j
    · rw [pow_zero, orderOf_one] at ho; norm_num at ho
    · exfalso
      apply hic
      have h1 : i * c * i⁻¹ = c := by rw [hjc, pow_one]
      calc c * i = i * (i⁻¹ * c * i) := by group
        _ = i * (i * c * i⁻¹) := by
            rw [show i⁻¹ = i by rw [inv_eq_iff_mul_eq_one, ← pow_two, hi2]]
        _ = i * c := by rw [h1]
    · exfalso
      have h2 : (c ^ 2) ^ 2 = 1 := by rw [← pow_mul, hc4]
      have := orderOf_dvd_of_pow_eq_one h2
      rw [ho] at this
      norm_num at this
    · rw [eq_inv_iff_mul_eq_one, ← pow_succ, hc4]
  have hk2K : k ^ 2 ∈ A.K := by
    rw [A.mem_K_iff (pow_mem hkT 2)]
    have : (⟨k ^ 2, pow_mem hkT 2⟩ : A.T) = (⟨k, hkT⟩ : A.T) ^ 2 := rfl
    rw [this, map_pow, hψk]
    decide
  have hkr : k * r = r * k := A.commute_of_ψ_eq_c0 hkT hψk hr
  obtain ⟨j, hj, hjk⟩ := A.eq_pow_of_mem_K hK hc hco hk2K
  have hc4 : c ^ 4 = 1 := by rw [← hco, pow_orderOf_eq_one]
  have hkcj : k * c ^ j * k⁻¹ = (c⁻¹) ^ j := by
    rw [← conj_pow, hkc]
  have hcj : c ^ j = (c⁻¹) ^ j := by
    rw [← hkcj, ← hjk]
    group
  refine ⟨k, hkT, ?_, hψk, hkc⟩
  interval_cases j
  · rw [hjk, pow_zero]
  · exfalso
    rw [pow_one, pow_one] at hcj
    have : c ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [hcj]; rw [mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one this
    rw [hco] at this
    norm_num at this
  · exfalso
    have hc2t : c ^ 2 = t := by
      refine A.eq_t_of_mem_K (pow_mem hc 2) (by rw [← pow_mul, hc4]) ?_
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hco] at this
      norm_num at this
    have hik : i = r * k := by rw [hkdef]; group
    have h1 : i ^ 2 = r ^ 2 * t := by
      rw [hik, ← hc2t, ← hjk, pow_two, pow_two, pow_two]
      calc r * k * (r * k) = r * (k * r) * k := by group
        _ = r * (r * k) * k := by rw [hkr]
        _ = r * r * (k * k) := by group
    rw [hi2] at h1
    have htL : t ∈ L := by
      have : t = (r ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
      rw [this]
      exact inv_mem (pow_mem hr.2 2)
    exact A.t_not_mem_L htL
  · exfalso
    rw [show (c⁻¹) ^ 3 = c by
      rw [inv_pow, inv_eq_iff_mul_eq_one, ← pow_succ, hc4]] at hcj
    have : c ^ 2 = 1 := by
      have h3 : c ^ 3 * c = 1 := by rw [← pow_succ, hc4]
      rw [hcj] at h3
      rw [pow_two]; exact h3
    have := orderOf_dvd_of_pow_eq_one this
    rw [hco] at this
    norm_num at this

theorem commute_z {z : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = a0 ^ 2) {r : X}
    (hr : r ∈ A.R) : z * r = r * z := by
  have hm1 : z * r ∈ A.R := mul_mem hz hr
  have hm2 : r * z ∈ A.R := mul_mem hr hz
  refine A.eq_of_ψ_eq hm1 hm2 ?_
  have e1 : (⟨z * r, hm1.1⟩ : A.T) = ⟨z, hz.1⟩ * ⟨r, hr.1⟩ := rfl
  have e2 : (⟨r * z, hm2.1⟩ : A.T) = ⟨r, hr.1⟩ * ⟨z, hz.1⟩ := rfl
  rw [e1, e2, map_mul, map_mul, hψz]
  exact a0_sq_comm_of_mem_P0 (A.ψ_mem_P0 _)

omit [Finite X] in
theorem card_range_of_ψ_eq_c0 {k : X} (hk : k ∈ A.T) (hψk : A.ψ ⟨k, hk⟩ = c0) :
    Nat.card A.ψ.range = 16 := by
  have hle : A.ψ.range ≤ P0 := by rintro _ ⟨g, rfl⟩; exact A.ψ_mem_P0 g
  have hdvd : Nat.card A.ψ.range ∣ 16 := card_P0 ▸ Subgroup.card_dvd_of_le hle
  have hlt : R0 < A.ψ.range :=
    lt_of_le_of_ne A.R0_le_range fun h => c0_not_mem_R0 (h ▸ ⟨⟨k, hk⟩, hψk⟩)
  have h8 : 8 < Nat.card A.ψ.range := card_R0 ▸ Subgroup.card_lt_of_lt hlt
  have hmem : Nat.card A.ψ.range ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem exists_coords (hK : Nat.card A.K = 4) {c : X} (hc : c ∈ A.K) (hco : orderOf c = 4)
    {k : X} (hk : k ∈ A.T) (hk2 : k ^ 2 = 1) (hψk : A.ψ ⟨k, hk⟩ = c0)
    (hkc : k * c * k⁻¹ = c⁻¹) {z : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = a0 ^ 2) :
    ∃ φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4,
      φ ⟨z, hz.1⟩ = (r 2, 1) ∧ φ ⟨t, A.t_mem_T⟩ = (1, r 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₁ : Subgroup X := zpowers c ⊔ zpowers k with hK₁
  have hK₁T : K₁ ≤ A.T := sup_le (zpowers_le.mpr hc.1) (zpowers_le.mpr hk)
  have hkK : k ∉ A.K := by
    intro h
    have := (A.mem_K_iff hk).mp h
    rw [hψk] at this
    exact absurd this (by decide)
  have hψK₁ : ∀ x (hx : x ∈ K₁), A.ψ ⟨x, hK₁T hx⟩ ∈ zpowers c0 := by
    have hle : K₁.subgroupOf A.T ≤ (zpowers c0).comap A.ψ := by
      rw [subgroupOf_sup (zpowers_le.mpr hc.1) (zpowers_le.mpr hk)]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have hxK : (x : X) ∈ A.K := zpowers_le.mpr hc hx
        rw [mem_comap, (A.mem_K_iff x.2).mp hxK]
        exact one_mem _
      · obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (show (x : X) ∈ zpowers k from hx)
        have : x = (⟨k, hk⟩ : A.T) ^ n := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
        rw [mem_comap, this, map_zpow, hψk]
        exact zpow_mem (mem_zpowers c0) n
    intro x hx
    exact hle hx
  have hRK₁ : ∀ x ∈ A.R, x ∈ K₁ → x = 1 := by
    intro x hxR hxK
    have h1 := hψK₁ x hxK
    rcases eq_one_or_eq_of_mem_zpowers (by decide : c0 ^ 2 = 1) h1 with h2 | h2
    · have hxK' : x ∈ A.K := (A.mem_K_iff hxR.1).mpr h2
      have : x ∈ A.K ⊓ L := ⟨hxK', hxR.2⟩
      rwa [A.K_inf_L, mem_bot] at this
    · exact absurd (h2 ▸ A.ψ_mem_R0 hxR) c0_not_mem_R0
  have hcomm : ∀ a ∈ A.R, ∀ b ∈ K₁, a * b = b * a := by
    intro a ha b hb
    have hle : K₁ ≤ centralizer ({a} : Set X) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;>
        rw [mem_centralizer_singleton_iff]
      · exact (A.commute_of_mem_R_of_mem_K ha hc).symm
      · exact A.commute_of_ψ_eq_c0 hk hψk ha
    exact (mem_centralizer_singleton_iff.mp (hle hb)).symm
  set ρ : K₁ := ⟨c, mem_sup_left (mem_zpowers c)⟩
  set σ : K₁ := ⟨k, mem_sup_right (mem_zpowers k)⟩
  have hgen : (⊤ : Subgroup K₁) = zpowers ρ ⊔ zpowers σ := by
    apply Subgroup.map_injective K₁.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  have hσρ : σ ∉ zpowers ρ := by
    intro h
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
    have : k = c ^ n := by
      have := congrArg Subtype.val hn
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    exact hkK (this ▸ zpow_mem hc n)
  obtain ⟨eK₁⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen
    (Subtype.ext (by simpa using hk2)) (Subtype.ext (by simpa using hkc)) hσρ
  have hoρ : orderOf ρ = 4 := by rw [Subgroup.orderOf_mk, hco]
  rw [hoρ] at eK₁
  obtain ⟨eR⟩ := A.config.inf_L_mulEquiv_dihedral A.syl
  have hcardT : Nat.card A.T = 64 := by
    rw [A.card_T_eq, A.card_range_of_ψ_eq_c0 hk hψk, hK]
  have hcardK₁ : Nat.card K₁ = 8 := by
    rw [Nat.card_congr eK₁.toEquiv, DihedralGroup.nat_card]
  obtain ⟨φ, hφA, hφB⟩ := exists_prodDihedral_equiv (G := A.T) (A := A.R.subgroupOf A.T)
    (B := K₁.subgroupOf A.T)
    (by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_bot]
      exact Subtype.ext (hRK₁ x (mem_inf.mp hx).1 (mem_inf.mp hx).2))
    (fun a ha b hb => Subtype.ext (hcomm a ha b hb))
    (by
      rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A.R ≤ A.T)).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hK₁T).toEquiv, A.card_R, hcardK₁, hcardT])
    ((subgroupOfEquivOfLe (inf_le_left : A.R ≤ A.T)).trans eR)
    ((subgroupOfEquivOfLe hK₁T).trans eK₁)
  refine ⟨φ, ?_, ?_⟩
  · have h := hφA ⟨⟨z, hz.1⟩, hz⟩
    rw [h]
    congr 1
    simp only [MulEquiv.trans_apply]
    apply eq_r_two_of_central
    · intro d
      obtain ⟨y, rfl⟩ := eR.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (A.commute_z hz hψz y.2)
    · rw [← map_pow]
      have : z ^ 2 = 1 := A.sq_eq_one_of_mem_R hz (by rw [hψz]; decide)
      have h1 : (subgroupOfEquivOfLe (inf_le_left : A.R ≤ A.T) ⟨⟨z, hz.1⟩, hz⟩) ^ 2 = 1 :=
        Subtype.ext this
      rw [h1, map_one]
    · intro h1
      have := eR.injective (h1.trans (map_one eR).symm)
      have hz1 : z = 1 := congrArg Subtype.val this
      have h2 := hψz
      simp only [hz1] at h2
      rw [show (⟨1, _⟩ : A.T) = 1 from rfl, map_one] at h2
      exact absurd h2 (by decide)
  · have htK₁ : t ∈ K₁ := by
      have hc2t : c ^ 2 = t := by
        refine A.eq_t_of_mem_K (pow_mem hc 2)
          (by rw [← pow_mul, show 2 * 2 = orderOf c by rw [hco], pow_orderOf_eq_one]) ?_
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hco] at this
        norm_num at this
      rw [← hc2t]
      exact pow_mem (mem_sup_left (mem_zpowers c)) 2
    have h := hφB ⟨⟨t, A.t_mem_T⟩, htK₁⟩
    rw [h]
    congr 1
    simp only [MulEquiv.trans_apply]
    apply eq_r_two_of_central
    · intro d
      obtain ⟨y, rfl⟩ := eK₁.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (A.commute_t (hK₁T y.2)).symm
    · rw [← map_pow]
      have : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
      have h1 : (subgroupOfEquivOfLe hK₁T ⟨⟨t, A.t_mem_T⟩, htK₁⟩) ^ 2 = 1 := Subtype.ext this
      rw [h1, map_one]
    · intro h1
      have := eK₁.injective (h1.trans (map_one eK₁).symm)
      have ht1 : t = 1 := congrArg Subtype.val this
      have h2 := A.orderOf_t
      rw [ht1, orderOf_one] at h2
      exact absurd h2 (by norm_num)

omit [Finite X] in
theorem conj_zt_eq {z : X} (hz : z ∈ A.T) (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4)
    (hφz : φ ⟨z, hz⟩ = (r 2, 1)) (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) {w : X}
    (hw : w ∈ normalizer (A.T : Set X)) : w * (z * t) * w⁻¹ = z * t := by
  set ζ : A.T := ⟨z * t, mul_mem hz A.t_mem_T⟩ with hζ
  have hφζ : φ ζ = (r 2, r 2) := by
    have : ζ = ⟨z, hz⟩ * ⟨t, A.t_mem_T⟩ := rfl
    rw [this, map_mul, hφz, hφt]
    rfl
  set α := conjNormalizer hw with hα
  have hζc : ∀ g : A.T, ζ * g = g * ζ := fun g => φ.injective (by
    rw [map_mul, map_mul, hφζ, dd_r_two_r_two_central])
  have hcen : ∀ q, φ (α ζ) * q = q * φ (α ζ) := by
    intro q
    obtain ⟨g, rfl⟩ := φ.surjective q
    obtain ⟨g₁, rfl⟩ := α.surjective g
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hζc]
  have hne : φ (α ζ) ≠ 1 := by
    intro h
    have h1 : α ζ = 1 := φ.injective (h.trans (map_one φ).symm)
    have h2 : ζ = 1 := α.injective (h1.trans (map_one α).symm)
    have h3 := congrArg φ h2
    rw [hφζ, map_one] at h3
    exact absurd h3 (by decide)
  have hcard : Nat.card {p : DihedralGroup 4 × DihedralGroup 4 // p ^ 2 = φ (α ζ)} = 4 := by
    rw [← card_sq_eq_congr φ (α ζ), ← card_sq_eq_congr α ζ, card_sq_eq_congr φ ζ, hφζ,
      dd_card_sq_eq_both]
  have heq : φ (α ζ) = φ ζ := by
    rw [hφζ]
    rcases dd_eq_of_central _ hcen with h | h | h | h
    · exact absurd h hne
    · rw [h, dd_card_sq_eq_left] at hcard; norm_num at hcard
    · rw [h, dd_card_sq_eq_right] at hcard; norm_num at hcard
    · exact h
  have := congrArg Subtype.val (φ.injective heq)
  rw [coe_conjNormalizer] at this
  exact this

end A7Data

end CFSG.ComponentClassification.HSFLit
