module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625c

public section

namespace CFSG.GH74.GLS.Th2.L625

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1

section Aut

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem card_le_four_of_sq_aut_odd (hF : L2Field F) (e : K ≃* L2 F)
    (hn : Odd (Nat.card ↥(fieldAutSub e))) (A : Subgroup (MulAut K)) (hsq : ∀ x ∈ A, x * x = 1) :
    Nat.card ↥A ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsElementaryAbelian 2 ↥A := Th2.Bal.isElementaryAbelian_two_of_sq A hsq
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨T', hT'⟩ := hA2.exists_le_sylow
  set φ : ↥A →* (F ≃+* F) := (fieldProj e).comp A.subtype with hφ
  have hker : Nat.card φ.ker ≤ 4 := by
    set X : Subgroup (MulAut K) := φ.ker.map A.subtype with hX
    have hXA : X ≤ A := by
      rintro _ ⟨a, _, rfl⟩
      exact a.2
    have hXG : X ≤ innDiagSub e := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_innDiagSub_iff e _).mpr (MonoidHom.mem_ker.mp ha)
    have hcard : Nat.card X = Nat.card φ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have := card_le_four_of_le_inf e hF T' X (hXA.trans hT') hXG
      (fun x hx y hy => hcomm x (hXA hx) y (hXA hy)) (fun x hx => hsq x (hXA hx))
    omega
  have hrange : Nat.card φ.range ≤ 1 := by
    have hcyc := ringAut_isCyclic F
    have hcyc' : IsCyclic φ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent φ.range ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show φ a ^ 2 = 1
      rw [← map_pow, pow_two]
      have := hsq a a.2
      rw [show a * a = 1 from Subtype.ext this, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    obtain ⟨ψ⟩ := (ivk_1_2e F hF K e).2.1
    have h2 : Nat.card φ.range ∣ Nat.card ↥(fieldAutSub e) := by
      rw [Nat.card_congr ψ.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card φ.range ∣ Nat.gcd 2 (Nat.card ↥(fieldAutSub e)) := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 2 (Nat.card ↥(fieldAutSub e)) = 1 :=
      (Nat.coprime_two_left.mpr hn)
    rw [h4] at h3
    exact Nat.le_of_dvd one_pos h3
  have h := Subgroup.card_ker_mul_card_range φ
  have hr0 : 0 < Nat.card φ.range := Nat.card_pos
  have : Nat.card ↥A = Nat.card φ.ker := by
    rw [← h]
    have : Nat.card φ.range = 1 := le_antisymm hrange hr0
    rw [this, mul_one]
  omega

theorem odd_card_fieldAutSub_of_not_eight_dvd (hF : L2Field F) (e : K ≃* L2 F)
    (h8 : ¬ 8 ∣ Nat.card K) : Odd (Nat.card ↥(fieldAutSub e)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨p, n, hp, -, -, hq⟩ := isOddPrimePower_of_L2Field hF
  have hn := (ivk_1_2e F hF K e).2.2 p n hp hq
  rw [hn] at hev
  obtain ⟨m, hm⟩ := hev
  have hqsq : Nat.card F = (p ^ m) ^ 2 := by
    rw [hq, ← pow_mul]
    congr 1
    omega
  have hrodd : Odd (p ^ m) := by
    have : Odd (Nat.card F) := hF.1
    rw [hqsq, pow_two] at this
    exact (Nat.odd_mul.mp this).1
  obtain ⟨m1, hm1⟩ := Nat.eight_dvd_sq_sub_one_of_odd hrodd
  have hq8 : 8 ∣ Nat.card F - 1 := ⟨m1, by rw [hqsq]; exact hm1⟩
  obtain ⟨c, hc⟩ := hq8
  have hodd : Odd (Nat.card F) := hF.1
  obtain ⟨k, hk⟩ := hodd
  have hq3 : 3 < Nat.card F := hF.2
  have hqc : Nat.card F = 8 * c + 1 := by omega
  have hcard : Nat.card K = Nat.card F * ((8 * c + 1) * (8 * c + 1) - 1) / 2 := by
    rw [card_eq_of_L2Field e hF, hqc, pow_two]
  have hexp : (8 * c + 1) * (8 * c + 1) - 1 = 16 * (c * (4 * c + 1)) := by
    have : (8 * c + 1) * (8 * c + 1) = 64 * c * c + 16 * c + 1 := by ring
    rw [this]
    have : 64 * c * c + 16 * c = 16 * (c * (4 * c + 1)) := by ring
    omega
  apply h8
  rw [hcard, hexp]
  refine ⟨Nat.card F * (c * (4 * c + 1)), ?_⟩
  have : Nat.card F * (16 * (c * (4 * c + 1))) / 2 = 8 * (Nat.card F * (c * (4 * c + 1))) := by
    have : Nat.card F * (16 * (c * (4 * c + 1))) = 2 * (8 * (Nat.card F * (c * (4 * c + 1)))) := by
      ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  exact this

end Aut

section Rank

variable {G : Type} [Group G] [Finite G]

theorem not_eight_dvd_card_of_twoPartCard {K : Subgroup G} (h : twoPartCard K = 4) :
    ¬ 8 ∣ Nat.card ↥K := by
  intro h8
  have h8' : 2 ^ 3 ∣ Nat.card ↥K := by simpa using h8
  have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h8'
  unfold twoPartCard at h
  have h2 : (Nat.card ↥K).factorization 2 = 2 :=
    Nat.pow_right_injective (le_refl 2) (by simpa using h)
  omega

theorem two_le_pRank_CxK_of_not_normal {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hnn : ¬ ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    2 ≤ pRank 2 ↥(CxK x K) := by
  obtain ⟨c, hc, k, hk, hkc⟩ : ∃ c ∈ centralizer ({x} : Set G), ∃ k ∈ K, c * k * c⁻¹ ∉ K := by
    by_contra h
    apply hnn
    intro c hc k hk
    by_contra hkc
    exact h ⟨c, hc, k, hk, hkc⟩
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (K.map (MulAut.conj c).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [Thm1.map_conj_eq_self_of_mem hc] at this
  have hne : K.map (MulAut.conj c).toMonoidHom ≠ K := by
    intro h
    apply hkc
    have hmem : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  have hle : K.map (MulAut.conj c).toMonoidHom ≤ CxK x K :=
    le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  obtain ⟨u, hu, v, hv, hu2, hv2, huv, hcomm⟩ :=
    U1a.exists_commuting_involutions (D := K) (Thm1.two_le_pRank_of_shape hshape)
  have hord : ∀ w : G, orderOf (c * w * c⁻¹) = orderOf w := fun w => by
    have := MulEquiv.orderOf_eq (MulAut.conj c) w
    simpa [MulAut.conj_apply] using this
  have hmemu : c * u * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
    ⟨u, hu, by simp [MulAut.conj_apply]⟩
  have hmemv : c * v * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
    ⟨v, hv, by simp [MulAut.conj_apply]⟩
  exact U1a.two_le_pRank_of_commute (hle hmemu) (hle hmemv) (by rw [hord, hu2]) (by rw [hord, hv2])
    (by
      calc c * u * c⁻¹ * (c * v * c⁻¹) = c * (u * v) * c⁻¹ := by group
        _ = c * (v * u) * c⁻¹ := by rw [hcomm]
        _ = c * v * c⁻¹ * (c * u * c⁻¹) := by group)
    (fun h => huv (by
      have := (MulAut.conj c).injective (a₁ := u) (a₂ := v) (by
        simpa [MulAut.conj_apply] using h)
      exact this))

theorem two_le_pRank_CxK_of_normal {x : G} {K : Subgroup G}
    (hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4)
    (hnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hbound : ∀ A : Subgroup (MulAut (kBar K)), (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 4) :
    2 ≤ pRank 2 ↥(CxK x K) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let ψ : ↥C →* MulAut (kBar K) := Back.actHom hnorm
  have hker : ψ.ker = (CxK x K).subgroupOf C := Back.actHom_ker hnorm
  obtain ⟨E, hEC, hEel, hErk⟩ := Th2.exists_elemAbelian_pRank C
  have hEcard : Nat.card ↥E = 16 := by
    rw [Back.card_eq_two_pow_pRank hEel, hErk, hG4]
    norm_num
  obtain ⟨hEcomm, hEsq⟩ := Back.forall_of_isElementaryAbelian hEel
  set E' : Subgroup ↥C := E.subgroupOf C with hE'
  have hE'card : Nat.card ↥E' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv).trans hEcard
  let ψE : ↥E' →* MulAut (kBar K) := ψ.comp E'.subtype
  have hEmem : ∀ k : ↥E', ((k : ↥C) : G) ∈ E := fun k => (Subgroup.mem_subgroupOf).mp k.2
  have hkk : ∀ k : ↥E', k * k = 1 := fun k =>
    Subtype.ext (Subtype.ext (hEsq _ (hEmem k)))
  have hRsq : ∀ a ∈ ψE.range, a * a = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← map_mul, hkk k, map_one]
  have hR := hbound ψE.range hRsq
  have hprod := Subgroup.card_ker_mul_card_range ψE
  have hker4 : 4 ≤ Nat.card ψE.ker := by
    rw [hE'card] at hprod
    by_contra hlt
    push Not at hlt
    have : Nat.card ψE.ker * Nat.card ψE.range ≤ 3 * 4 :=
      Nat.mul_le_mul (by omega) hR
    omega
  let ι : ↥E' →* G := C.subtype.comp E'.subtype
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext h)
  have hle : ψE.ker.map ι ≤ CxK x K := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ψ ((k : ↥E') : ↥C) = 1 := hk
    have h2 : ((k : ↥E') : ↥C) ∈ ψ.ker := h1
    rw [hker] at h2
    exact (Subgroup.mem_subgroupOf).mp h2
  have hel : IsElementaryAbelian 2 ↥(ψE.ker.map ι) := by
    refine Back.isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
      exact hEcomm _ (hEmem a) _ (hEmem b)
    · rintro _ ⟨a, -, rfl⟩
      exact hEsq _ (hEmem a)
  have hcard : Nat.card ↥(ψE.ker.map ι) = Nat.card ψE.ker :=
    Subgroup.card_map_of_injective hι
  have hpow := Back.card_eq_two_pow_pRank hel
  have hmono := Back.pRank_mono' hle
  by_contra hlt
  push Not at hlt
  have h1 : pRank 2 ↥(ψE.ker.map ι) ≤ 1 := by omega
  have h2 : 2 ^ pRank 2 ↥(ψE.ker.map ι) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
  omega

end Rank

end CFSG.GH74.GLS.Th2.L625

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2.L625

theorem b_625_rank_of (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) : B_625_rank := by
  intro G _ _ hG x y K hU h4
  have hlu : IsLocallyUnbalancing x y K := hU.1
  have hU2 : InU2 (kBar K) := h102 G hG x y K hlu
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hlu.1.2
  have hstar : pRank 2 ↥(centralizer ({x} : Set G)) = 4 := hU.2.2.1.2.trans hG.pRank_eq_four
  have h8 : ¬ 8 ∣ Nat.card (kBar K) := fun h =>
    not_eight_dvd_card_of_twoPartCard h4
      (h.trans (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K)))
  rcases hU2.2 with hL2 | ⟨⟨e7⟩⟩ | ⟨hl34, hel, hcard⟩
  · by_cases hnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
    · obtain ⟨p, f, hp, hf, hodd, hL⟩ := hL2
      obtain ⟨F, _, _, e0, hF, -⟩ := Th2.Bal.exists_l2Field_of_lieModel hodd hL
      have hn := odd_card_fieldAutSub_of_not_eight_dvd hF e0 h8
      exact two_le_pRank_CxK_of_normal hstar hnorm
        (fun A hsq => card_le_four_of_sq_aut_odd hF e0 hn A hsq)
    · exact two_le_pRank_CxK_of_not_normal hK (Or.inl hL2) hnorm
  · exfalso
    apply h8
    have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Nat.card_congr e7.toEquiv, h7]
    norm_num
  · exact absurd hl34 (fun hl => hL34 G hG.gen4 x K hlu.1.1 hlu.1.2 ⟨hl, hel, hcard⟩)

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS

theorem b_lemma625c1_of_thm1
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (h102 : B_ivk_10_2)
    (hfm : Th2.L625.ClassFM9) (hfour : B_thm1_four) : B_lemma625c1 :=
  b_lemma625c1_of h610 h720 h14 h103 hL34 hL29 h102 hfm hfour (b_625_rank_of h102 hL34)

end CFSG.GH74.GLS
