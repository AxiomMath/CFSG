module

public import CFSG.LargeExtraspecial.S2OrthOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem eichler_mul_eichler_pow_five {p p₁ c d : V} (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hc : q c = 1) (hd : q d = 1) (hpp₁ : polar q p p₁ = 1) (hcd : polar q c d = 1)
    (hpc : polar q p c = 0) (hpd : polar q p d = 0) (hp₁c : polar q p₁ c = 0)
    (hp₁d : polar q p₁ d = 0) : (eichler q p₁ d * eichler q p c) ^ 5 = 1 := by
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  have hdc : polar q d c = 1 := by rw [polar_comm, hcd]
  have hcp : polar q c p = 0 := by rw [polar_comm, hpc]
  have hdp : polar q d p = 0 := by rw [polar_comm, hpd]
  have hcp₁ : polar q c p₁ = 0 := by rw [polar_comm, hp₁c]
  have hdp₁ : polar q d p₁ = 0 := by rw [polar_comm, hp₁d]
  have hpp : polar q p p = 0 := polar_self_eq_zero q p
  have hp₁p₁ : polar q p₁ p₁ = 0 := polar_self_eq_zero q p₁
  have hcc : polar q c c = 0 := polar_self_eq_zero q c
  have hdd : polar q d d = 0 := polar_self_eq_zero q d
  have hx : ∀ v, eichler q p₁ d v = v + polar q v p₁ • d + (polar q v d + polar q v p₁) • p₁ :=
    fun v => by rw [eichler_apply_zmod2 hp₁ hp₁d, hd, one_mul]
  have hy : ∀ v, eichler q p c v = v + polar q v p • c + (polar q v c + polar q v p) • p :=
    fun v => by rw [eichler_apply_zmod2 hp hpc, hc, one_mul]
  set r := eichler q p₁ d * eichler q p c with hr
  have hrv : ∀ v, r v = eichler q p₁ d (eichler q p c v) := fun v => rfl
  have hr0 : ∀ v, polar q v p = 0 → polar q v p₁ = 0 → polar q v c = 0 → polar q v d = 0 →
      r v = v := by
    intro v h1 h2 h3 h4
    rw [hrv, hy, h1, h3, zero_smul, add_zero, zero_add, zero_smul, add_zero, hx, h2, h4]
    simp
  have hrp : r p = p + p₁ + d := by
    rw [hrv, hy, hx]
    simp only [hpp, hpc, hpp₁, hpd, add_zero, zero_add, zero_smul]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have hrp₁ : r p₁ = p + p₁ + c + d := by
    rw [hrv, hy, hx]
    simp only [polar_add_left, hp₁p, hp₁c, hp₁p₁, hcp₁, hpp₁, hp₁d, hcd, hpd, add_zero, zero_add,
      one_smul]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have hrc : r c = p₁ + c := by
    rw [hrv, hy, hx]
    simp only [hcp, hcc, hcp₁, hcd, add_zero, zero_smul]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have hrd : r d = p + p₁ := by
    rw [hrv, hy, hx]
    simp only [polar_add_left, hdp, hdc, hdp₁, hpp₁, hdd, hpd, add_zero, zero_add, zero_smul,
      one_smul]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have h5 : ∀ v, (r ^ 5) v = r (r (r (r (r v)))) := fun v => by
    simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply]
  have h5p : (r ^ 5) p = p := by
    rw [h5]
    simp only [map_add, hrp, hrp₁, hrc, hrd]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have h5p₁ : (r ^ 5) p₁ = p₁ := by
    rw [h5]
    simp only [map_add, hrp, hrp₁, hrc, hrd]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have h5c : (r ^ 5) c = c := by
    rw [h5]
    simp only [map_add, hrp, hrp₁, hrc, hrd]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  have h5d : (r ^ 5) d = d := by
    rw [h5]
    simp only [map_add, hrp, hrp₁, hrc, hrd]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  ext v
  set s := polar q v p₁ • p + polar q v p • p₁ + polar q v d • c + polar q v c • d with hs
  have hw1 : polar q (v - s) p = 0 := by
    simp only [hs, polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, hpp, hp₁p, hcp,
      hdp, mul_zero, mul_one, add_zero, zero_add, sub_self]
  have hw2 : polar q (v - s) p₁ = 0 := by
    simp only [hs, polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, hpp₁, hp₁p₁, hcp₁,
      hdp₁, mul_zero, mul_one, add_zero, sub_self]
  have hw3 : polar q (v - s) c = 0 := by
    simp only [hs, polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, hpc, hp₁c, hcc,
      hdc, mul_zero, mul_one, add_zero, zero_add, sub_self]
  have hw4 : polar q (v - s) d = 0 := by
    simp only [hs, polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, hpd, hp₁d, hcd,
      hdd, mul_zero, mul_one, add_zero, zero_add, sub_self]
  have hrw : r (v - s) = v - s := hr0 _ hw1 hw2 hw3 hw4
  have h5w : (r ^ 5) (v - s) = v - s := by rw [h5, hrw, hrw, hrw, hrw, hrw]
  have h5s : (r ^ 5) s = s := by
    rw [hs, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h5p, h5p₁, h5c,
      h5d]
  have hv : v = s + (v - s) := by abel
  rw [hv, map_add, h5s, h5w, LinearEquiv.coe_one, id]

variable (q) in
@[expose] def IsMinusType (F : Submodule (ZMod 2) V) (m : ℕ) : Prop :=
  ∀ T : Submodule (ZMod 2) V, T ≤ perp q F → (∀ x ∈ T, q x = 0) → finrank (ZMod 2) T < m

variable [FiniteDimensional (ZMod 2) V]

theorem IsMinusType.sup_span_pair {F : Submodule (ZMod 2) V} {m : ℕ} (h : IsMinusType q F m)
    {p p₁ : V} (hpF : p ∈ perp q F) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) :
    IsMinusType q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) (m - 1) := by
  intro T hT hT0
  have hTp : ∀ t ∈ T, polar q t p = 0 := fun t ht => by
    rw [polar_comm]
    exact (mem_perp_sup_span_pair.mp (hT ht)).2.1
  have hpT : p ∉ T := by
    intro hpT
    have := (mem_perp_sup_span_pair.mp (hT hpT)).2.2
    rw [polar_comm, hpp₁] at this
    exact one_ne_zero this
  have hle : T ⊔ (ZMod 2) ∙ p ≤ perp q F := sup_le (hT.trans perp_sup_span_pair_le)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hpF)
  have hsing : ∀ x ∈ T ⊔ (ZMod 2) ∙ p, q x = 0 := by
    intro x hx
    obtain ⟨t, ht, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add_eq, hT0 t ht, map_smul_zmod2, hp, polar_smul_right, hTp t ht]
    simp
  have hinf : T ⊓ (ZMod 2) ∙ p = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxp⟩
    rcases mem_span_singleton_iff.mp hxp with rfl | rfl
    · exact Submodule.zero_mem _
    · exact absurd hxT hpT
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hpp₁
    exact zero_ne_one hpp₁
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T ((ZMod 2) ∙ p)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hp0] at h1
  have h2 := h _ hle hsing
  omega

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable {hq : q.polarBilin.Nondegenerate} (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem four_dvd_finrank_of_minus {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥)
    (hdim : finrank (ZMod 2) (perp q F) = 4) (hmin : IsMinusType q F 2)
    {N : Submodule (ZMod 2) M} (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ F N p p₁) : 4 ∣ finrank (ZMod 2) N := by
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  have hne : perp q K ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hKdim
    omega
  obtain ⟨c, hcK, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d, hdK, hdc⟩ := exists_mem_perp_polar_eq_one hq hK hcK hc0
  obtain ⟨hcF, hpc, hp₁c⟩ := mem_perp_sup_span_pair.mp hcK
  obtain ⟨hdF, hpd, hp₁d⟩ := mem_perp_sup_span_pair.mp hdK
  have hcd : polar q c d = 1 := by rw [polar_comm, hdc]
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hdc
    exact zero_ne_one hdc
  have hnonsing : ∀ e : V, e ∈ perp q F → e ≠ 0 → polar q p e = 0 → polar q p₁ e = 0 →
      q e = 1 := by
    intro e heF he0 hpe hp₁e
    refine (zmod2_eq_zero_or_eq_one _).resolve_left fun he => ?_
    have hli : LinearIndependent (ZMod 2) ![p, e] := by
      refine linearIndependent_pair_iff.mpr ⟨hp0, he0, ?_⟩
      rintro rfl
      rw [hp₁e] at hp₁p
      exact zero_ne_one hp₁p
    have hT := hmin (Submodule.span (ZMod 2) {p, e}) (by
      rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact hpF
      · exact heF) (fun x hx => map_eq_zero_of_mem_span_pair hp he hpe hx)
    rw [finrank_span_pair hli] at hT
    exact lt_irrefl _ hT
  have hc : q c = 1 := hnonsing c hcF hc0 hpc hp₁c
  have hd : q d = 1 := hnonsing d hdF hd0 hpd hp₁d
  have hyR : eichler q p c ∈ radFix q F p := (mem_radFix_iff hq hp0 hp hpF).mpr ⟨c, hcF, hpc, rfl⟩
  have hxR : eichler q p₁ d ∈ radFix q F p₁ :=
    (mem_radFix_iff hq hp₁0 hp₁ hp₁F).mpr ⟨d, hdF, hp₁d, rfl⟩
  have hne1 : ∀ {a e : V}, a ≠ 0 → q a = 0 → polar q a e = 0 → q e = 1 → eichler q a e ≠ 1 := by
    intro a e ha0 ha hae he h1
    rcases mem_span_singleton_iff.mp ((eichler_eq_one_iff hq ha0 ha hae).mp h1) with h | h
    · rw [h, map_zero] at he
      exact zero_ne_one he
    · rw [h, ha] at he
      exact zero_ne_one he
  set y : omegaGroup q hq := ⟨eichler q p c, eichler_mem_omegaGroup hq p c⟩ with hydef
  set x : omegaGroup q hq := ⟨eichler q p₁ d, eichler_mem_omegaGroup hq p₁ d⟩ with hxdef
  have hDx := (timmesfeld_2_1_b0 ρ hF (m := 2) le_rfl hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD x hxR
    (hne1 hp₁0 hp₁ hp₁d hd) (not_isTypeA_eichler hq hp₁0 hp₁ hp₁d hd)).1
  have hDy := (timmesfeld_2_1_b0 ρ hF (m := 2) le_rfl hdim hN hp₁F hpF hp₁0 hp₁ hp hp₁p hD.symm
    y hyR (hne1 hp0 hp hpc hc) (not_isTypeA_eichler hq hp0 hp hpc hc)).1
  have hxx : ρ x * ρ x = 1 := by
    rw [← map_mul, show x * x = 1 from Subtype.ext (eichler_mul_self hp₁d), map_one]
  have hyy : ρ y * ρ y = 1 := by
    rw [← map_mul, show y * y = 1 from Subtype.ext (eichler_mul_self hpc), map_one]
  have hxN : ∀ v ∈ N, ρ x v ∈ N := hN x hxR.2
  have hyN : ∀ v ∈ N, ρ y v ∈ N := hN y hyR.2
  have hxy : N ⊓ fixSpace (ρ x) ⊓ fixSpace (ρ y) = ⊥ := by
    rw [eq_bot_iff, ← hD.2]
    rintro v ⟨⟨hvN, hvx⟩, hvy⟩
    have h1 : v ∈ N ⊓ fixSpace (ρ x) := ⟨hvN, hvx⟩
    have h2 : v ∈ N ⊓ fixSpace (ρ y) := ⟨hvN, hvy⟩
    rw [hDx] at h1
    rw [hDy] at h2
    exact ⟨h2, h1⟩
  have hfix := inf_fixSpace_mul_eq_bot hxx hyy hxN hxy
  have h5 : (ρ x * ρ y) ^ 5 = 1 := by
    rw [← map_mul, ← map_pow]
    have : (x * y) ^ 5 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
      exact eichler_mul_eichler_pow_five hp hp₁ hc hd hpp₁ hcd hpc hpd hp₁c hp₁d)
    rw [this, map_one]
  exact four_dvd_finrank_of_pow_five_of_mapsTo h5 (fun v hv => hxN _ (hyN v hv)) hfix

theorem timmesfeld_2_1_b_dvd_minus : ∀ (m : ℕ) {F : Submodule (ZMod 2) V}
    {N : Submodule (ZMod 2) M} {p p₁ : V}, F ⊓ perp q F = ⊥ → 2 ≤ m →
    finrank (ZMod 2) (perp q F) = 2 * m → IsMinusType q F m → OmegaInvariant ρ F N →
    p ∈ perp q F → p₁ ∈ perp q F → p ≠ 0 → q p = 0 → q p₁ = 0 → polar q p p₁ = 1 →
    RadDecomp ρ F N p p₁ → 2 ^ m ∣ finrank (ZMod 2) N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F N p p₁ hF hm hdim hmin hN hpF hp₁F hp0 hp hp₁ hpp₁ hD
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  rcases Nat.lt_or_ge m 3 with h2 | h3
  · obtain rfl : m = 2 := by omega
    exact four_dvd_finrank_of_minus ρ hF (by omega) hmin hN hpF hp₁F hp0 hp hp₁ hpp₁ hD
  have htwo := (finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD).2
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  obtain ⟨p', hp'K, hp'0, hp'⟩ := exists_singular_mem_perp (q := q) (F := K) (by omega)
  obtain ⟨p₁', hp₁'K, hp₁', hpp₁'⟩ := exists_hyperbolic_partner hq hK hp'K hp'0 hp'
  obtain ⟨hW, hDW⟩ := timmesfeld_2_1_b2 ρ hF h3 hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hp'K hp₁'K
    hp'0 hp' hp₁' hpp₁'
  have := ih (m - 1) (by omega) hK (by omega) (by omega) (hmin.sup_span_pair hpF hp hpp₁) hW
    hp'K hp₁'K hp'0 hp' hp₁' hpp₁' hDW
  rw [htwo, show m = (m - 1) + 1 by omega, pow_succ, mul_comm]
  exact mul_dvd_mul_left 2 this

theorem timmesfeld_2_1_b_dvd_minus_omega {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m)
    (hmin : ∀ T : Submodule (ZMod 2) V, (∀ x ∈ T, q x = 0) → finrank (ZMod 2) T < m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    2 ^ m ∣ finrank (ZMod 2) M := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hD : RadDecomp ρ ⊥ ⊤ p p₁ := by
    rw [RadDecomp, radFix_bot, radFix_bot, top_inf_eq, top_inf_eq]
    exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  have h := timmesfeld_2_1_b_dvd_minus ρ m hF hm (by rw [perp_bot, finrank_top]; exact hdim)
    (fun T _ hT => hmin T hT) (fun g _ v _ => Submodule.mem_top)
    (by rw [perp_bot]; exact Submodule.mem_top) (by rw [perp_bot]; exact Submodule.mem_top) hp0
    hp hp₁ hpp₁ hD
  rwa [finrank_top] at h

end S2

end CFSG.LargeExtraspecial
