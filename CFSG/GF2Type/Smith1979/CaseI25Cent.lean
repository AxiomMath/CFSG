module

public import CFSG.GF2Type.Smith1979.CaseI25Nu
public import CFSG.LargeExtraspecial.S111CNorm
public import CFSG.LargeExtraspecial.S14Cent
public import CFSG.LargeExtraspecial.S14C13Aut
public import CFSG.LargeExtraspecial.S7SevenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem factorization_two_11520 : (11520 : ℕ).factorization 2 = 8 := by
  have h : (11520 : ℕ) = 2 ^ 8 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_two_23040 : (23040 : ℕ).factorization 2 = 9 := by
  have h : (23040 : ℕ) = 2 ^ 9 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Sylow

variable (H : Hyp4 S g) (C : Cons311 S g)
include H C

theorem exists_sylow_le_NLbar :
    ∃ T : Subgroup S.O, S5.IsSylowTwoIn T S.Mbar ∧ S.Lbar g ≤ T ∧ T ≤ NLbar S g := by
  obtain ⟨P, hLP, hPN⟩ := S11.exists_sylow_le_normalizer H.conj_mem C
  have hTsyl : S5.IsSylowTwoIn ((P : Subgroup S.Mbar).map S.Mbar.subtype) S.Mbar := by
    have h1 : S5.IsSylowTwoIn (P : Subgroup S.Mbar) ⊤ :=
      ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
    have h2 := h1.map S.Mbar.subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h2
  exact ⟨_, hTsyl, hLP, fun x hx => ⟨hTsyl.le hx, hPN hx⟩⟩

end Sylow

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem mem_zpowers_of_fix_Vt {x : S.O} (hxM : x ∈ S.Mbar) (hxt : x * t = t * x)
    (hxV : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : x ∈ zpowers t := by
  obtain ⟨hs, hn⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6.ge
  have hperf := commutator_RmodN hs hn
  exact CFSG.LargeExtraspecial.S14.mem_zpowers_of_commute hCE H hNo C ht ht1 hVQ (Or.inl hΩ)
    fun r hr => (comm_of_fix_Vt H hN hperf hxM hxt hxV hr).symm

theorem mem_Lbar_of_centralizes {c : S.O} (hcM : c ∈ S.Mbar)
    (hc : ∀ l ∈ S.Lbar g, c * l = l * c) : c ∈ S.Lbar g := by
  obtain ⟨Q, hQ, -, hX, hE, hsing⟩ := hΩ.exists_form
  have ha0 := aV_ne_zero H ht
  have ha := CaseIClosure.Q_aV_eq_zero H ht hsing
  have hct : c * t = t * c := hc t ht
  have hcN : c ∈ normalizer (S.Lbar g : Set S.O) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => (hc h hh).symm)
  have hca := fix_of_mem_normalizer H hcN
  let y : CFSG.LargeExtraspecial.S14.Ct S t :=
    ⟨c, Subgroup.mem_inf.mpr ⟨hcM, mem_centralizer_singleton_iff.mpr hct⟩⟩
  have hφapp : ∀ w : Vt S g t,
      ((CFSG.LargeExtraspecial.S14.resC S g H.conj_mem t y w : Vt S g t) : S.Qt) =
        (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w := fun w => rfl
  have hφinv : ∀ w : Vt S g t,
      (((CFSG.LargeExtraspecial.S14.resC S g H.conj_mem t y)⁻¹ w : Vt S g t) : S.Qt) =
        ((c⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w :=
    coe_inv_apply_of_forall hφapp
  have hφO : CFSG.LargeExtraspecial.S14.resC S g H.conj_mem t y ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine O62.mem_orthogonalGroup_of_normalizes h6 hQ fun x hx => ?_
    have hmap := CFSG.LargeExtraspecial.S14.map_conj_resC_RmodN H.conj_mem y
    rw [← hX] at hx ⊢
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hφa : CFSG.LargeExtraspecial.S14.resC S g H.conj_mem t y (aV ht) = aV ht :=
    Subtype.ext hca
  have hcomm : ∀ u ∈ pointRadical Q (aV ht),
      CFSG.LargeExtraspecial.S14.resC S g H.conj_mem t y * u *
        (CFSG.LargeExtraspecial.S14.resC S g H.conj_mem t y)⁻¹ = u := by
    intro u hu
    rw [← hE] at hu
    obtain ⟨x, hx, hux⟩ := mem_LmodN.mp hu
    have e : c * x * c⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc x hx
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφapp, hux, hφinv, hux v]
    change ((c * x * c⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = _
    rw [e]
  have hφL := mem_pointRadical_of_commute hQ ha0 ha hφO hφa hcomm
  rw [← hE] at hφL
  obtain ⟨l, hl, hφl⟩ := mem_LmodN.mp hφL
  have hxM : l⁻¹ * c ∈ S.Mbar := mul_mem (inv_mem (S.Lbar_le_Mbar g hl)) hcM
  have hlt : Commute l t := Lbar_comm S H.conj_mem hl ht
  have hxt : (l⁻¹ * c) * t = t * (l⁻¹ * c) := by
    calc l⁻¹ * c * t = l⁻¹ * (c * t) := by group
      _ = l⁻¹ * (t * c) := by rw [hct]
      _ = (l⁻¹ * t) * c := by group
      _ = (t * l⁻¹) * c := by rw [hlt.inv_left.eq]
      _ = t * (l⁻¹ * c) := by group
  have hxV : ∀ v ∈ Vt S g t, ((l⁻¹ * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    have h1 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v := hφl ⟨v, hv⟩
    rw [coe_mul_apply, h1, inv_apply_apply_O]
  have hxz : l⁻¹ * c ∈ zpowers t :=
    mem_zpowers_of_fix_Vt hCE H hNo C ht ht1 hVQ hΩ hN h6 hxM hxt hxV
  have hcl : c = l * (l⁻¹ * c) := by group
  rw [hcl]
  exact mul_mem hl ((zpowers_le.mpr ht) hxz)

theorem permDelta_eq_one_iff_mem_Lbar (hΔ : (Delta S g t).ncard = 6) (n : NLbar S g) :
    permDelta S g t n = 1 ↔ (n : S.O) ∈ S.Lbar g := by
  rw [permDelta_eq_one_iff (closure_Delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ) ht n]
  constructor
  · intro h
    exact mem_Lbar_of_centralizes hCE H hNo C ht ht1 hVQ hΩ hN h6 n.2.1 h
  · intro hn l hl
    exact Lbar_comm S H.conj_mem hn hl

theorem ker_permDelta_eq (hΔ : (Delta S g t).ncard = 6) :
    (permDelta S g t).ker = (S.Lbar g).subgroupOf (NLbar S g) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact permDelta_eq_one_iff_mem_Lbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ n

theorem card_NLbar (hΔ : (Delta S g t).ncard = 6) :
    Nat.card (NLbar S g) = 11520 ∨ Nat.card (NLbar S g) = 23040 := by
  classical
  have hw : S.width = 6 := by
    rw [width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, h6]
  have hΔcard : Nat.card (Delta S g t) = 6 := (Nat.card_coe_set_eq _).trans hΔ
  have hkercard : Nat.card (permDelta S g t).ker = 32 := by
    rw [ker_permDelta_eq hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lbar_le_NLbar).toEquiv, C.card_Lbar, hw]
    norm_num
  have h1 := Subgroup.card_ker_mul_card_range (permDelta S g t)
  rw [hkercard] at h1
  have hnt : Nontrivial (Delta S g t) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hfact : Nat.factorial 6 = 720 := by decide
  rcases range_permDelta_eq hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ with h | h
  · left
    rw [h, nat_card_alternatingGroup, hΔcard, hfact] at h1
    omega
  · right
    rw [h, Subgroup.card_top, Nat.card_perm, hΔcard, hfact] at h1
    omega

theorem exists_sylow_two_card (hΔ : (Delta S g t).ncard = 6) :
    ∃ T : Subgroup S.O, S5.IsSylowTwoIn T S.Mbar ∧ S.Lbar g ≤ T ∧ T ≤ NLbar S g ∧
      (Nat.card T = 2 ^ 8 ∨ Nat.card T = 2 ^ 9) := by
  obtain ⟨T, hTsyl, hLT, hTN⟩ := exists_sylow_le_NLbar H C
  refine ⟨T, hTsyl, hLT, hTN, ?_⟩
  have hTN' : S5.IsSylowTwoIn T (NLbar S g) :=
    ⟨hTN, hTsyl.isPGroup, fun hd => hTsyl.not_dvd (by
      rw [← Subgroup.relIndex_mul_relIndex T (NLbar S g) S.Mbar hTN inf_le_left]
      exact Dvd.dvd.mul_right hd _)⟩
  have hcard := hTN'.card_eq
  rcases card_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ with h | h
  · left
    rw [hcard, h, factorization_two_11520]
  · right
    rw [hcard, h, factorization_two_23040]

end Context

end Case25

end CFSG.GF2Type.Smith1979
