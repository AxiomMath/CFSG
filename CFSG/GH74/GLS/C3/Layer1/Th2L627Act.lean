module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Syl

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem twoPartCard_mono {H K : Subgroup G} (h : H ≤ K) : twoPartCard H ≤ twoPartCard K := by
  unfold twoPartCard
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (Subgroup.card_dvd_of_le h) 2

omit [Finite G] in
theorem CxK_conj_mem {t : G} {J : Subgroup G}
    (hnorm : ∀ c ∈ centralizer ({t} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J)
    {g : G} (hg : g ∈ centralizer ({t} : Set G)) {c : G} (hc : c ∈ CxK t J) :
    g * c * g⁻¹ ∈ CxK t J :=
  ⟨mul_mem (mul_mem hg hc.1) (Subgroup.inv_mem _ hg),
    PumpCalc.conj_mem_cSec (U1a.mem_normalizer_of_norm hnorm hg) hc.2⟩

theorem card_T_eq_eight_mul {t : G} {J T : Subgroup G}
    (hnorm : ∀ c ∈ centralizer ({t} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J)
    (h8 : twoPartCard (centralizer ({t} : Set G)) = 8 * twoPartCard (CxK t J))
    (hT : IsSylowOf 2 T (centralizer ({t} : Set G))) :
    Nat.card ↥T = 8 * Nat.card ↥(T ⊓ CxK t J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsSylowOf 2 (T ⊓ CxK t J) (CxK t J) :=
    hT.inf_of_le_normalizer inf_le_left (fun g hg => mem_normalizer_of_two_sided
      (fun c hc => CxK_conj_mem hnorm hg hc)
      (fun c hc => by simpa using CxK_conj_mem hnorm (Subgroup.inv_mem _ hg) hc))
  rw [← Th2.twoPartCard_eq_card_of_isSylowOf hT, ← Th2.twoPartCard_eq_card_of_isSylowOf hQ]
  exact h8



theorem commDisj_inf {t : G} {J T : Subgroup G} (hT2 : IsPGroup 2 ↥T) (hcen : CenterlessBar J) :
    Th2.CommDisj (T ⊓ J) (T ⊓ CxK t J) := by
  have hbot := C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J hT2
  refine ⟨fun p hp q hq => ?_, ?_⟩
  · have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 J := hq.2.2.2.2 p hp.2
    have h2 : ⁅p, q⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem hp.1 hq.1) (T.inv_mem hp.1)) (T.inv_mem hq.1)
    have h3 : ⁅p, q⁆ ∈ T ⊓ pPrimeCoreOf 2 J := ⟨h2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  · refine eq_bot_iff.2 fun p hp => ?_
    have hpO : p ∈ pPrimeCoreOf 2 J :=
      mem_pPrimeCoreOf_of_commutators hcen hp.1.2 (fun k hk => hp.2.2.2.2.2 k hk)
    have h3 : p ∈ T ⊓ pPrimeCoreOf 2 J := ⟨hp.1.1, hpO⟩
    rw [hbot] at h3
    exact h3


omit [Finite G] in
theorem CMK_eq_inf {t : G} {J T : Subgroup G} (hTC : T ≤ centralizer ({t} : Set G)) :
    CMK T J = T ⊓ CxK t J := by
  ext x
  constructor
  · rintro ⟨hxT, hxS⟩
    exact ⟨hxT, hTC hxT, hxS⟩
  · rintro ⟨hxT, hxC, hxS⟩
    exact ⟨hxT, hxS⟩

omit [Finite G] in
theorem actHom_eq_one_iff_mem {t : G} {J T : Subgroup G} (hTC : T ≤ centralizer ({t} : Set G))
    (hnormT : ∀ m ∈ T, ∀ l ∈ J, m * l * m⁻¹ ∈ J) {x : G} (hx : x ∈ T) :
    Back.actHom hnormT ⟨x, hx⟩ = 1 ↔ x ∈ CxK t J := by
  have h1 : (⟨x, hx⟩ : ↥T) ∈ (Back.actHom hnormT).ker ↔ x ∈ T ⊓ CxK t J := by
    rw [Back.actHom_ker hnormT, Subgroup.mem_subgroupOf, CMK_eq_inf hTC]
  rw [MonoidHom.mem_ker] at h1
  rw [h1]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

omit [Finite G] in
theorem card_range_actHom_mul {t : G} {J T : Subgroup G} (hTC : T ≤ centralizer ({t} : Set G))
    (hnormT : ∀ m ∈ T, ∀ l ∈ J, m * l * m⁻¹ ∈ J) :
    Nat.card (Back.actHom hnormT).range * Nat.card ↥(T ⊓ CxK t J) = Nat.card ↥T := by
  have h := Subgroup.card_ker_mul_card_range (Back.actHom hnormT)
  rw [Back.actHom_ker hnormT, CMK_eq_inf hTC,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ CxK t J ≤ T)).toEquiv] at h
  rw [← h, mul_comm]


theorem isD8_range_actHom {t : G} {J T : Subgroup G} (hTC : T ≤ centralizer ({t} : Set G))
    (hnormT : ∀ m ∈ T, ∀ l ∈ J, m * l * m⁻¹ ∈ J)
    (hAut : ∀ X : Subgroup (MulAut (kBar J)), Nat.card ↥X = 8 → IsD8 X)
    (hT8 : Nat.card ↥T = 8 * Nat.card ↥(T ⊓ CxK t J)) : IsD8 (Back.actHom hnormT).range := by
  apply hAut
  have h := card_range_actHom_mul hTC hnormT
  have hpos : 0 < Nat.card ↥(T ⊓ CxK t J) := Nat.card_pos
  rw [hT8] at h
  nlinarith

omit [Finite G] in
theorem isD8_of_inj_range {A : Type} [Group A] [Finite A] {T N : Subgroup G} (ψ : ↥T →* A)
    (hD : IsD8 ψ.range) (hNT : N ≤ T) (hN8 : Nat.card ↥N = 8)
    (hinj : ∀ n (hn : n ∈ N), ψ ⟨n, hNT hn⟩ = 1 → n = 1) : IsD8 N := by
  obtain ⟨e⟩ := hD
  let φ : ↥N →* A := ψ.comp (Subgroup.inclusion hNT)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    exact Subtype.ext (hinj n n.2 hn)
  have hle : φ.range ≤ ψ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, rfl⟩
  have hcard : Nat.card ψ.range = 8 := IsD8.card_eq ⟨e⟩
  have hcφ : Nat.card φ.range = 8 := by
    rw [← hN8]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have heq : φ.range = ψ.range := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcφ])
  exact ⟨(MonoidHom.ofInjective hφ).trans ((MulEquiv.subgroupCongr heq).trans e)⟩

theorem exists_central_involution_of_normal {H W : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) (hWH : W ≤ H) (hW1 : W ≠ ⊥) :
    ∃ v ∈ W, orderOf v = 2 ∧ ∀ h ∈ H, h * v = v * h := by
  obtain ⟨w, hwW, hw1, hwc⟩ := exists_central_of_normal hH hW hWH hW1
  have hzW : zpowers w ≤ W := zpowers_le.2 hwW
  have hzp : IsPGroup 2 ↥(zpowers w) := hH.to_le (hzW.trans hWH)
  have hzne : zpowers w ≠ ⊥ := by
    intro h
    exact hw1 (by simpa using (Subgroup.zpowers_eq_bot.1 h))
  obtain ⟨v, hvz, hv2⟩ := exists_involution_of_ne_bot hzp hzne
  refine ⟨v, hzW hvz, hv2, fun h hh => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hvz
  rw [← hk]
  exact ((show Commute h w from hwc h hh).zpow_right k).eq

omit [Finite G] in
theorem inf_conj_normal {T Q : Subgroup G} {a : G} (haN : a ∈ normalizer (T : Set G))
    (ha2 : a * a ∈ T) (hQn : ∀ τ ∈ T, ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) :
    ∀ h ∈ T ⊔ zpowers a, ∀ w ∈ Q ⊓ conjugate Q a, h * w * h⁻¹ ∈ Q ⊓ conjugate Q a := by
  have haT : ∀ τ ∈ T, a * τ * a⁻¹ ∈ T := fun τ hτ => (Subgroup.mem_normalizer_iff.1 haN τ).1 hτ
  have hWn : ∀ τ ∈ T, ∀ w ∈ Q ⊓ conjugate Q a, τ * w * τ⁻¹ ∈ Q ⊓ conjugate Q a := by
    intro τ hτ w hw
    refine Subgroup.mem_inf.2 ⟨hQn τ hτ w hw.1, ?_⟩
    rw [mem_conjugate_iff']
    have h1 := hQn (a * τ * a⁻¹) (haT τ hτ) _ (mem_conjugate_iff'.1 hw.2)
    have e : a * τ * a⁻¹ * (a * w * a⁻¹) * (a * τ * a⁻¹)⁻¹ = a * (τ * w * τ⁻¹) * a⁻¹ := by group
    rwa [e] at h1
  have hTnorm : T ≤ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) := fun τ hτ =>
    mem_normalizer_of_two_sided (hWn τ hτ)
      (fun w hw => by simpa using hWn τ⁻¹ (T.inv_mem hτ) w hw)
  have haW : a ∈ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) := by
    refine mem_normalizer_of_two_sided (fun w hw => Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      (fun w hw => Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact mem_conjugate_iff'.1 hw.2
    · rw [mem_conjugate_iff']
      have := hQn (a * a) ha2 w hw.1
      have e : a * (a * w * a⁻¹) * a⁻¹ = a * a * w * (a * a)⁻¹ := by group
      rw [e]; exact this
    · have := hQn (a * a)⁻¹ (T.inv_mem ha2) _ (mem_conjugate_iff'.1 hw.2)
      have e : (a * a)⁻¹ * (a * w * a⁻¹) * (a * a)⁻¹⁻¹ = a⁻¹ * w * a := by group
      rwa [e] at this
    · exact Sec4Core.mem_conj_of (a := a) Q hw.1
  have hHn : T ⊔ zpowers a ≤ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) :=
    sup_le hTnorm (zpowers_le.2 haW)
  exact fun h hh w hw => (Subgroup.mem_normalizer_iff.1 (hHn hh) w).1 hw

theorem card_le_sixteen {E : Subgroup G} (hG4 : pRank 2 G ≤ 4)
    (hE : CFSG.IsElementaryAbelian 2 ↥E) : Nat.card ↥E ≤ 16 := by
  rw [Back.card_eq_two_pow_pRank hE]
  have h1 : pRank 2 ↥E ≤ 4 := (pRank_le_top' E).trans hG4
  calc 2 ^ pRank 2 ↥E ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h1
    _ = 16 := by norm_num


end CFSG.GH74.GLS.Th2.L627
