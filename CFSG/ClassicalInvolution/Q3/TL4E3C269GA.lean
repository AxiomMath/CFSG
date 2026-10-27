module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269GU
public import CFSG.ClassicalInvolution.Q3.TL4E3Fin
public import CFSG.ClassicalInvolution.Q3.TL4MF163L2
public import CFSG.ClassicalInvolution.Q3.TL4SecIdRed
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace E3C269G

section Quot

variable {H : Type} [Group H] [Finite H]

theorem eq_one_of_mem_oddCore {w : H} (hw : w ∈ classicalInvolutionOddCore H)
    (hw2 : w * w = 1) : w = 1 := by
  have hodd := CFSG.ComponentClassification.OddCore.odd_card H
  have h1 : orderOf w ∣ Nat.card (classicalInvolutionOddCore H) :=
    Subgroup.orderOf_dvd_natCard _ hw
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h1
    exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hodd)

theorem centralizer_mk_le_map {t : H} (ht : t * t = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore H) t} :
        Set (H ⧸ classicalInvolutionOddCore H)) ≤
      (Subgroup.centralizer ({t} : Set H)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore H)) := by
  intro q hq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore H) q
  rw [Subgroup.mem_centralizer_singleton_iff] at hq
  have hc : Commute (QuotientGroup.mk' (classicalInvolutionOddCore H) y)
      (QuotientGroup.mk' (classicalInvolutionOddCore H) t) := hq
  have hA : IsPGroup 2 (Subgroup.zpowers t) := by
    have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨n, hn, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup
    (A := Subgroup.zpowers t) (N := classicalInvolutionOddCore H) hA
    (CFSG.ComponentClassification.OddCore.odd_card H)
    (fun a _ m hm => (classicalInvolutionOddCore_normal H).conj_mem m hm a) (x := y)
    (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have h1 : QuotientGroup.mk' (classicalInvolutionOddCore H)
          (y⁻¹ * (t ^ k * y * (t ^ k)⁻¹)) = 1 := by
        simp only [map_mul, map_inv, map_zpow]
        rw [← (hc.zpow_right k).eq]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1)
  refine ⟨y * n, ?_, (QuotientGroup.mk'_eq_mk' _).mpr ⟨n⁻¹, inv_mem hn, by group⟩⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 := hfix t (Subgroup.mem_zpowers t)
  calc y * n * t = t * (y * n) * t⁻¹ * t := by rw [h1]
    _ = t * (y * n) := by group

theorem centralizer_mk_conj_le_map {t : H} (ht : t * t = 1) (x : H) :
    Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore H) (x * t * x⁻¹)} :
        Set (H ⧸ classicalInvolutionOddCore H)) ≤
      (Subgroup.centralizer ({t} : Set H) ⊔ Subgroup.zpowers x).map
        (QuotientGroup.mk' (classicalInvolutionOddCore H)) := by
  intro q hq
  set π := QuotientGroup.mk' (classicalInvolutionOddCore H) with hπ
  have hq' : (π x)⁻¹ * q * π x ∈ Subgroup.centralizer ({π t} : Set (H ⧸ _)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
    rw [map_mul, map_mul, map_inv] at hq
    calc (π x)⁻¹ * q * π x * π t = (π x)⁻¹ * (q * (π x * π t * (π x)⁻¹)) * π x := by group
      _ = (π x)⁻¹ * ((π x * π t * (π x)⁻¹) * q) * π x := by rw [hq]
      _ = π t * ((π x)⁻¹ * q * π x) := by group
  obtain ⟨c, hc, hcq⟩ := centralizer_mk_le_map ht hq'
  refine ⟨x * c * x⁻¹, ?_, ?_⟩
  · exact mul_mem (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
      (Subgroup.mem_sup_left hc)) (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers x)))
  · rw [map_mul, map_mul, map_inv, hcq]
    group

theorem le_sup_oddCore {t : H} (ht : t * t = 1) (x : H)
    (hgen : Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore H) t} :
        Set (H ⧸ classicalInvolutionOddCore H)) ⊔
      Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore H) (x * t * x⁻¹)} :
        Set (H ⧸ classicalInvolutionOddCore H)) = ⊤) :
    ⊤ ≤ Subgroup.centralizer ({t} : Set H) ⊔ Subgroup.zpowers x ⊔
      classicalInvolutionOddCore H := by
  intro y _
  have h1 : (⊤ : Subgroup (H ⧸ classicalInvolutionOddCore H)) ≤
      (Subgroup.centralizer ({t} : Set H) ⊔ Subgroup.zpowers x).map
        (QuotientGroup.mk' (classicalInvolutionOddCore H)) := by
    rw [← hgen]
    exact sup_le ((centralizer_mk_le_map ht).trans (Subgroup.map_mono le_sup_left))
      (centralizer_mk_conj_le_map ht x)
  obtain ⟨k, hk, hky⟩ := h1 (Subgroup.mem_top (QuotientGroup.mk' _ y))
  obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' _).mp hky
  exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hz)

omit [Finite H] in
theorem le_sup_oddCoreOf {Y : Type} [Group Y] {X : Subgroup Y} (e : H ≃* ↥X) {t x : H}
    (h : ⊤ ≤ Subgroup.centralizer ({t} : Set H) ⊔ Subgroup.zpowers x ⊔
      classicalInvolutionOddCore H) :
    X ≤ X ⊓ Subgroup.centralizer ({(e t : Y)} : Set Y) ⊔ Subgroup.zpowers (e x : Y) ⊔
      oddCoreOf X := by
  set φ : H →* Y := X.subtype.comp e.toMonoidHom with hφ
  intro y hy
  have h2 := Subgroup.mem_map_of_mem φ (h (Subgroup.mem_top (e.symm ⟨y, hy⟩)))
  have hφy : φ (e.symm ⟨y, hy⟩) = y := by simp [hφ]
  rw [hφy, Subgroup.map_sup, Subgroup.map_sup] at h2
  have ha : (Subgroup.centralizer ({t} : Set H)).map φ ≤
      X ⊓ Subgroup.centralizer ({(e t : Y)} : Set Y) := by
    rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(e c).2, ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    show ((e c : X) : Y) * (e t : Y) = (e t : Y) * (e c : X)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  have hb : (Subgroup.zpowers x).map φ ≤ Subgroup.zpowers (e x : Y) := by
    rw [MonoidHom.map_zpowers]
    exact le_rfl
  have hc : (classicalInvolutionOddCore H).map φ ≤ oddCoreOf X := by
    rw [hφ, ← Subgroup.map_map, E3.map_oddCore_mulEquiv]
    exact le_rfl
  exact sup_le_sup (sup_le_sup ha hb) hc h2

theorem mk_conj_ne {t x : H} (ht : t * t = 1) (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hne : x * t * x⁻¹ ≠ t) :
    QuotientGroup.mk' (classicalInvolutionOddCore H) (x * t * x⁻¹) ≠
      QuotientGroup.mk' (classicalInvolutionOddCore H) t := by
  intro heq
  obtain ⟨z, hz, hzeq⟩ := (QuotientGroup.mk'_eq_mk' _).mp heq
  have hs2 : x * t * x⁻¹ * (x * t * x⁻¹) = 1 :=
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht, mul_one, mul_inv_cancel]
  have hzdef : z = (x * t * x⁻¹)⁻¹ * t := eq_inv_mul_iff_mul_eq.mpr hzeq
  have hinv : (x * t * x⁻¹)⁻¹ = x * t * x⁻¹ := inv_eq_of_mul_eq_one_right hs2
  have hz2 : z * z = 1 := by
    rw [hzdef, hinv]
    calc x * t * x⁻¹ * t * (x * t * x⁻¹ * t)
        = x * t * x⁻¹ * (t * (x * t * x⁻¹)) * t := by group
      _ = x * t * x⁻¹ * (x * t * x⁻¹ * t) * t := by rw [hcomm]
      _ = x * t * x⁻¹ * (x * t * x⁻¹) * (t * t) := by group
      _ = 1 := by rw [hs2, ht, one_mul]
  rw [eq_one_of_mem_oddCore hz hz2, mul_one] at hzeq
  exact hne hzeq

omit [Finite H] in
theorem mk_conj (t x : H) :
    QuotientGroup.mk' (classicalInvolutionOddCore H) (x * t * x⁻¹) =
      QuotientGroup.mk' (classicalInvolutionOddCore H) x *
        QuotientGroup.mk' (classicalInvolutionOddCore H) t *
          (QuotientGroup.mk' (classicalInvolutionOddCore H) x)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem le_sup_oddCoreOf_of_gen {Y : Type} [Group Y] {X : Subgroup Y} (e : H ≃* ↥X) {t x : H}
    (ht : t * t = 1) (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) (hne : x * t * x⁻¹ ≠ t)
    (hgen : ∀ s : H ⧸ classicalInvolutionOddCore H,
      QuotientGroup.mk' (classicalInvolutionOddCore H) t * s =
          s * QuotientGroup.mk' (classicalInvolutionOddCore H) t →
        s ≠ QuotientGroup.mk' (classicalInvolutionOddCore H) t →
          (∃ g, s = g * QuotientGroup.mk' (classicalInvolutionOddCore H) t * g⁻¹) →
            Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore H) t} :
                Set (H ⧸ classicalInvolutionOddCore H)) ⊔
              Subgroup.centralizer ({s} : Set (H ⧸ classicalInvolutionOddCore H)) = ⊤) :
    X ≤ X ⊓ Subgroup.centralizer ({(e t : Y)} : Set Y) ⊔ Subgroup.zpowers (e x : Y) ⊔
      oddCoreOf X := by
  refine le_sup_oddCoreOf e (le_sup_oddCore ht x (hgen _ ?_ (mk_conj_ne ht hcomm hne)
    ⟨QuotientGroup.mk' _ x, mk_conj t x⟩))
  rw [← map_mul, ← map_mul, hcomm]

end Quot

section Member

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

omit [Finite X] in
theorem exists_projectiveSL_equiv {p f : ℕ} (hl : LieModel X .PSL 3 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* projectiveSL 3 K) := by
  rcases hl with ⟨-, -, K, _, _, hK, ⟨e₀⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  rotate_left
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨(e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)⟩⟩

theorem mul_self_mem_of_index_le_two {N : Subgroup X} (hN : N.index ≤ 2) (g : X) :
    g * g ∈ N := by
  have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge N.index 2 with h | h
  · have h1 : N.index = 1 := by omega
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  · exact Subgroup.mul_self_mem_of_index_two (le_antisymm hN h) g

theorem sup_centralizer_of_e3Z2 (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hL2 : E3C269L2)
    (hm : EdgelessMember3 R S z) (hmu : MuZ2Member R) (hO2 : ¬ TightInO2 z)
    (hx : (¬ TightActs3 R z ∧ (Thm6Exit X ∨ TightTwisted X z)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    {s : X} (hzs : z * s = s * z) (hne : s ≠ z) (hconj : ∃ g : X, s = g * z * g⁻¹) :
    Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤ := by
  obtain ⟨hFs, hi, hX⟩ := hE3 X R S z hm hmu hO2 hx
  have := hFs
  obtain ⟨hTL3, hTU3, -, -, hTM12⟩ := hT X R S z hm hmu hFs (index_dvd_six_of_le_two hi)
  have hz2 : orderOf z = 2 := hm.datum.order
  have hs2 : orderOf s = 2 := by
    obtain ⟨g, rfl⟩ := hconj
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz2]
  rcases hX with ⟨p, f, hp, hp2, ⟨hf, hl⟩ | hl | hl⟩ | hm12
  · obtain ⟨ι, hι, -, hιz⟩ := MF163.exists_quat_of_member hm
    refine hL2 X hFs hi p f hp hp2 hf hl ι hι z s hιz ?_ hzs hne hconj
    rw [← hιz, show (QuaternionGroup.a 2 : QuaternionGroup 2) =
      QuaternionGroup.a 1 * QuaternionGroup.a 1 by decide, map_mul]
    exact mul_self_mem_of_index_le_two hi _
  · obtain ⟨-, hl'⟩ := hTL3 p f hl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_projectiveSL_equiv hl'
    have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
    refine sup_centralizer_eq_top_of_equiv e (sup_centralizer_eq_top_psl3 hodd ?_ ?_ ?_ ?_)
    · rw [MulEquiv.orderOf_eq]
      exact hz2
    · rw [MulEquiv.orderOf_eq]
      exact hs2
    · rw [← map_mul, ← map_mul, hzs]
    · exact fun h => hne (e.injective h).symm
  · obtain ⟨-, hl', -⟩ := hTU3 p f hl
    obtain ⟨-, hf, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hl'
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    refine sup_centralizer_eq_top_of_equiv e (sup_centralizer_eq_top_psu3 h hp2 ?_ ?_ ?_ ?_)
    · rw [MulEquiv.orderOf_eq]
      exact hz2
    · rw [MulEquiv.orderOf_eq]
      exact hs2
    · rw [← map_mul, ← map_mul, hzs]
    · exact fun h => hne (e.injective h).symm
  · exact absurd hm12 hTM12

end Member

end E3C269G

end CFSG.ClassicalInvolution.Q3.TL4
