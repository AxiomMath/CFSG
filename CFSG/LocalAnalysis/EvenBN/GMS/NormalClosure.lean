module

public import CFSG.LocalAnalysis.EvenBN.GMS.LayerSelection
public import CFSG.LocalAnalysis.SteinbergBNMiyamotoPrimaryLocalApplication
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.LocalAnalysis
open scoped MatrixGroups

section OddQuotient

variable {H : Type*} [Group H]

theorem normal_of_map_normal_of_le_centralizer {A R : Subgroup H} [R.Normal] [IsSimpleGroup A]
    (hRA : R ≤ centralizer (A : Set H))
    (hcomm : ∀ g : H, ⁅A, A.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hN : (A.map (QuotientGroup.mk' R)).Normal) : A.Normal := by
  set π := QuotientGroup.mk' R
  have hnorm : ∀ m : H, π m ∈ A.map π → ∀ x ∈ A, m * x * m⁻¹ ∈ A := by
    intro m hm x hx
    obtain ⟨a, ha, ham⟩ := hm
    have hr : a⁻¹ * m ∈ R := QuotientGroup.eq.mp ham
    have hrx : x * (a⁻¹ * m) = (a⁻¹ * m) * x := mem_centralizer_iff.mp (hRA hr) x hx
    have h1 : m * x * m⁻¹ = a * x * a⁻¹ := by
      calc m * x * m⁻¹ = a * ((a⁻¹ * m) * x) * (a⁻¹ * m)⁻¹ * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * m)) * (a⁻¹ * m)⁻¹ * a⁻¹ := by rw [hrx]
        _ = a * x * a⁻¹ := by group
    rw [h1]
    exact A.mul_mem (A.mul_mem ha hx) (A.inv_mem ha)
  have hconj : ∀ g : H, A ≤ A.map (MulAut.conj g).toMonoidHom := by
    intro g
    set A' := A.map (MulAut.conj g).toMonoidHom
    have hmemA' : ∀ y, y ∈ A' ↔ g⁻¹ * y * g ∈ A := by
      intro y
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using ha
      · intro hy
        exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hA'π : ∀ y ∈ A', π y ∈ A.map π := by
      intro y hy
      have h1 := hN.conj_mem (π (g⁻¹ * y * g)) (mem_map_of_mem π ((hmemA' y).mp hy)) (π g)
      simpa [map_mul, map_inv, mul_assoc] using h1
    have hA'norm : ∀ x ∈ A, ∀ y ∈ A', x * y * x⁻¹ ∈ A' := by
      intro x hx y hy
      rw [hmemA']
      have hgx : π (g⁻¹ * x * g) ∈ A.map π := by
        have h1 := hN.conj_mem (π x) (mem_map_of_mem π hx) (π g⁻¹)
        simpa [map_mul, map_inv, mul_assoc] using h1
      have h2 := hnorm _ hgx _ ((hmemA' y).mp hy)
      have h3 : g⁻¹ * (x * y * x⁻¹) * g = g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by
        group
      rw [h3]
      exact h2
    have hI : (A'.subgroupOf A).Normal := ⟨fun n hn a => by
      rw [mem_subgroupOf] at hn ⊢
      exact hA'norm a a.2 n hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A'.subgroupOf A) with hbot | htop
    · exfalso
      apply hcomm g
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have hcA : x * y * x⁻¹ * y⁻¹ ∈ A := by
        have h1 := hnorm y (hA'π y hy) x⁻¹ (A.inv_mem hx)
        have h2 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [h2]
        exact A.mul_mem hx h1
      have hcA' : x * y * x⁻¹ * y⁻¹ ∈ A' := A'.mul_mem (hA'norm x hx y hy) (A'.inv_mem hy)
      have hmem : (⟨_, hcA⟩ : A) ∈ A'.subgroupOf A := mem_subgroupOf.mpr hcA'
      rw [hbot, mem_bot] at hmem
      have hc : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hmem
      calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
        _ = x * y := by rw [hc, inv_one, one_mul]
    · exact subgroupOf_eq_top.mp htop
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨a, ha, hax⟩ := hconj g⁻¹ hx
  rw [← hax]
  simpa [MulAut.conj_apply, mul_assoc] using ha

theorem mem_of_map_mem_of_pow {A R : Subgroup H} [R.Normal] (hR : Odd (Nat.card R))
    (hRA : R ≤ centralizer (A : Set H)) (hAR : ∀ x ∈ A, x ∈ R → x = 1) {x : H} {e : ℕ}
    (hx : x ^ 2 ^ e = 1) (hxA : QuotientGroup.mk' R x ∈ A.map (QuotientGroup.mk' R)) :
    x ∈ A := by
  obtain ⟨a, ha, hax⟩ := hxA
  have hr : a⁻¹ * x ∈ R := QuotientGroup.eq.mp hax
  have hcomm : Commute a (a⁻¹ * x) := mem_centralizer_iff.mp (hRA hr) a ha
  have h1 : a ^ 2 ^ e * (a⁻¹ * x) ^ 2 ^ e = 1 := by
    rw [← hcomm.mul_pow, mul_inv_cancel_left, hx]
  have h2 : (a⁻¹ * x) ^ 2 ^ e = 1 := by
    refine hAR _ ?_ (pow_mem hr _)
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (pow_mem ha _)
  have h3 : a⁻¹ * x = 1 := by
    have hdvd1 : orderOf (a⁻¹ * x) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one h2
    have hdvd2 : orderOf (a⁻¹ * x) ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨_, hr⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ e) (Nat.card R) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hR)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have h4 : x = a := by rw [← mul_inv_cancel_left a x, h3, mul_one]
  rw [h4]
  exact ha

end OddQuotient

section Transfer

variable {H : Type*} [Group H]

theorem LocalFieldBound.map_quotient {A R : Subgroup H} [R.Normal] {t : H} {n : ℕ}
    (hCt : centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)) =
      (centralizer ({t} : Set H)).map (QuotientGroup.mk' R))
    (hF : LocalFieldBound A t n) :
    LocalFieldBound (A.map (QuotientGroup.mk' R)) (QuotientGroup.mk' R t) n := by
  set π := QuotientGroup.mk' R
  have hle : (A ⊔ centralizer (A : Set H)).map π ≤
      A.map π ⊔ centralizer ((A.map π : Subgroup (H ⧸ R)) : Set (H ⧸ R)) := by
    rw [Subgroup.map_sup]
    refine sup_le_sup_left ?_ _
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc a ha]
  refine ⟨fun x hx => ?_, fun hn2 => ?_⟩
  · rw [hCt] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow]
    exact hle (mem_map_of_mem π (hF.1 y hy))
  · rw [hCt]
    exact (map_mono (hF.2 hn2)).trans hle

variable [Finite H]

theorem not_central_sylow_map {R : Subgroup H} [R.Normal] {t : H} (ht : orderOf t = 2)
    (hinj2 : ∀ Q : Subgroup H, IsPGroup 2 Q → Set.InjOn (QuotientGroup.mk' R) (Q : Set H))
    (hCt : centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)) =
      (centralizer ({t} : Set H)).map (QuotientGroup.mk' R))
    (he : ∀ T : Sylow 2 H, t ∈ (T : Subgroup H) → ∃ x ∈ (T : Subgroup H), x * t ≠ t * x) :
    ∀ T : Sylow 2 (H ⧸ R), QuotientGroup.mk' R t ∈ (T : Subgroup (H ⧸ R)) →
      ∃ x ∈ (T : Subgroup (H ⧸ R)), x * QuotientGroup.mk' R t ≠ QuotientGroup.mk' R t * x := by
  set π := QuotientGroup.mk' R
  set C := centralizer ({t} : Set H)
  intro T htT
  by_contra hcon
  push Not at hcon
  have hTC : (T : Subgroup (H ⧸ R)) ≤ C.map π := by
    rw [← hCt]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hcon x hx)
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (π.subgroupMap_surjective C) 2 (T.subtype hTC)
  set P' : Subgroup H := (P : Subgroup C).map C.subtype with hP'
  have hP'C : P' ≤ C := map_subtype_le _
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  have hP'T : P'.map π = T := by
    have h1 := congrArg
      (fun S : Sylow 2 (C.map π) => (S : Subgroup (C.map π)).map (C.map π).subtype) hP
    simp only [Sylow.coe_mapSurjective, Sylow.coe_subtype] at h1
    rw [subgroupOf_map_subtype, inf_of_le_left hTC, map_map] at h1
    have hcomp : (C.map π).subtype.comp (π.subgroupMap C) = π.comp C.subtype :=
      MonoidHom.ext fun _ => rfl
    rw [hcomp] at h1
    rw [hP', map_map]
    exact h1
  obtain ⟨Q, hPQ⟩ := hP'2.exists_le_sylow
  have hQT : (Q : Subgroup H).map π = T :=
    T.is_maximal' (Q.isPGroup'.map π) (hP'T ▸ map_mono hPQ)
  have hcard : Nat.card (Q : Subgroup H) ≤ Nat.card P' := by
    rw [← card_map_of_injOn π Q fun a ha b hb hab => hinj2 Q Q.isPGroup' ha hb hab,
      ← card_map_of_injOn π P' fun a ha b hb hab => hinj2 P' hP'2 ha hb hab, hQT, hP'T]
  have hPQe : P' = Q := eq_of_le_of_card_ge hPQ hcard
  have hQC : (Q : Subgroup H) ≤ C := hPQe ▸ hP'C
  have htQ : t ∈ (Q : Subgroup H) := by
    have hz : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hle : (Q : Subgroup H) ≤ normalizer (zpowers t : Set H) := by
      rw [CFSG.SeitzReduction.RankOne.normalizer_zpowers_eq_centralizer_of_involution ht]
      exact hQC
    have hK := IsPGroup.to_sup_of_normal_right' Q.isPGroup' hz hle
    rw [← Q.is_maximal' hK le_sup_left]
    exact mem_sup_right (mem_zpowers t)
  obtain ⟨x, hxQ, hxt⟩ := he Q htQ
  exact hxt (mem_centralizer_singleton_iff.mp (hQC hxQ))

end Transfer

namespace LinearApp

variable {H : Type*} [Group H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}
  (h : GMSLinearLocalApplication A t U V D n)
include h

theorem isSimpleGroup : IsSimpleGroup A := by
  obtain ⟨hn, -, ⟨-, -, k, _, _, hk, ⟨φ⟩⟩, -⟩ := h
  have h2 := GMSK.two_eq_zero_of_card (K := k) (by omega) hk
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    GMSK.sl2_isSimpleGroup h2 (hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  exact φ.isSimpleGroup

theorem exists_mul_ne : ∃ x y : A, x * y ≠ y * x := by
  obtain ⟨-, -, ⟨-, -, k, _, _, -, ⟨φ⟩⟩, -⟩ := h
  obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
  exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩

theorem exists_four :
    ∃ E : Subgroup H, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨hn, -, ⟨-, -, k, _, _, hk, ⟨φ⟩⟩, -⟩ := h
  have h2 := GMSK.two_eq_zero_of_card (K := k) (by omega) hk
  obtain ⟨E, hE, hE4⟩ := GMSK.exists_elementaryAbelian_four h2
    (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
  set f : Multiplicative k →* H := A.subtype.comp (φ.symm.toMonoidHom.comp (GMSK.sl2Upper k))
  have hf : Function.Injective f :=
    A.subtype_injective.comp (φ.symm.injective.comp GMSK.sl2Upper_injective)
  have hEf : CFSG.IsElementaryAbelian 2 (E.map f) := CFSG.IsElementaryAbelian.map f
  refine ⟨E.map f, ?_, ⟨hEf.toIsMulCommutative, fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hf, hE4]⟩
  rintro _ ⟨x, -, rfl⟩
  exact (φ.symm (GMSK.sl2Upper k x)).2

variable [Finite H]

theorem card_le_two :
    ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2 := by
  obtain ⟨-, ht, -, ⟨htA, ⟨S, hS⟩, -, -⟩, -⟩ := h
  intro X hXC hX
  have hX' : IsPGroup 2 (X.subgroupOf (centralizer (A : Set H))) :=
    hX.of_equiv (subgroupOfEquivOfLe hXC).symm
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  have h1 : Nat.card (X.subgroupOf (centralizer (A : Set H))) ≤ Nat.card P := card_le_of_le hP
  have h2 : Nat.card P = Nat.card S := Nat.card_congr (Sylow.equiv P S).toEquiv
  have h3 : Nat.card (S : Subgroup (centralizer (A : Set H))) = 2 := by
    rw [hS, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr htA)).toEquiv,
      Nat.card_zpowers, ht]
  have h4 : Nat.card (X.subgroupOf (centralizer (A : Set H))) = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv
  have h5 : Nat.card (S : Subgroup (centralizer (A : Set H))) = Nat.card S := rfl
  omega

theorem U_ne_bot : U ≠ ⊥ := by
  obtain ⟨E, hEA, -, hE4⟩ := LinearApp.exists_four h
  obtain ⟨-, -, -, -, ⟨-, ⟨S, hS⟩, -⟩, -⟩ := h
  intro hU
  have h2 : 2 ∣ Nat.card A := by
    have h1 := card_dvd_of_le hEA
    rw [hE4] at h1
    exact (by norm_num : 2 ∣ 4).trans h1
  apply S.ne_bot_of_dvd_card h2
  rw [hS, hU, bot_subgroupOf]

theorem sylow_inf : ∃ S : Sylow 2 ↥(centralizer (A : Set H) ⊓ centralizer ({t} : Set H)),
    (S : Subgroup _).map (centralizer (A : Set H) ⊓ centralizer ({t} : Set H)).subtype =
      zpowers t :=
  GMSK.exists_sylow_inf_centralizer_eq_zpowers h.2.1 h.2.2.2.1.1 (LinearApp.card_le_two h)

theorem odd_quotient (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R)) :
    let θ : H →* H ⧸ R := QuotientGroup.mk' R
    Set.InjOn θ (A : Set H) ∧ (∀ Q : Subgroup H, IsPGroup 2 Q → Set.InjOn θ (Q : Set H)) ∧
      orderOf (θ t) = 2 ∧ A.map θ ≤ centralizer ({θ t} : Set (H ⧸ R)) ∧
      ((A.map θ).subgroupOf (centralizer ({θ t} : Set (H ⧸ R)))).Normal ∧
      centralizer ({θ t} : Set (H ⧸ R)) = (centralizer ({t} : Set H)).map θ ∧
      CFSG.Assembly.ComponentType.IsStandardSubgroup (A.map θ) ∧
      ∃ S : Sylow 2 (centralizer ((A.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R))),
        (S : Subgroup _).map (centralizer ((A.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R))).subtype =
          zpowers (θ t) := by
  intro θ
  have := LinearApp.isSimpleGroup h
  obtain ⟨hinj, hinj2, hθt, -, -, hAb, hAbn, hCt, -, hstd, hsyl, -⟩ :=
    SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      (LinearApp.exists_mul_ne h) (LinearApp.exists_four h) h.2.1 h.2.2.2.1.2.2.1 h.2.2.2.1.2.2.2
      (LinearApp.sylow_inf h) R hR
  exact ⟨hinj, hinj2, hθt, hAb, hAbn, hCt, hstd, hsyl⟩

theorem elementary :
    Group.IsPerfect (normalClosure (A : Set H)) ∧
      (∀ R : Subgroup H, R.Normal → Odd (Nat.card R) → ⁅R, normalClosure (A : Set H)⁆ = ⊥) ∧
      (centralizer (((normalClosure (A : Set H)).map
          (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)) :
            Subgroup (H ⧸ CFSG.Open.standardComponentOddCore H)) :
          Set (H ⧸ CFSG.Open.standardComponentOddCore H)) = ⊥ →
        centralizer (normalClosure (A : Set H) : Set H) = CFSG.Open.standardComponentOddCore H ∧
          (center (normalClosure (A : Set H))).map (normalClosure (A : Set H)).subtype =
            (CFSG.Open.standardComponentOddCore (normalClosure (A : Set H))).map
              (normalClosure (A : Set H)).subtype ∧
          (CFSG.Open.standardComponentOddCore (normalClosure (A : Set H))).map
              (normalClosure (A : Set H)).subtype =
            normalClosure (A : Set H) ⊓ CFSG.Open.standardComponentOddCore H ∧
          ∃ e : normalClosure (A : Set H) ⧸ center (normalClosure (A : Set H)) ≃*
              (normalClosure (A : Set H)).map
                (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)),
            ∀ x : normalClosure (A : Set H),
              (e (x : normalClosure (A : Set H) ⧸ center (normalClosure (A : Set H))) :
                H ⧸ CFSG.Open.standardComponentOddCore H) =
                QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H) x) := by
  have := LinearApp.isSimpleGroup h
  have hnab := LinearApp.exists_mul_ne h
  have hU1 := LinearApp.U_ne_bot h
  obtain ⟨-, ht, -, ⟨-, -, hAt, hAn⟩, ⟨hUA, -, hVea, -, htV, -, -, hcomm⟩, -⟩ := h
  have : IsElementaryAbelian 2 V := hVea
  exact ComponentInitial.elementary_involution_commutator_centralizes_odd_normal_core ht hnab
    hAt hAn htV (by rw [hcomm]; exact hU1) (by rw [hcomm]; exact hUA) rfl

theorem le_centralizer (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R)) :
    R ≤ centralizer (A : Set H) :=
  (commutator_eq_bot_iff_le_centralizer.mp ((LinearApp.elementary h).2.1 R inferInstance hR)).trans
    (centralizer_le subset_normalClosure)

theorem map_quotient (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R)) :
    GMSLinearLocalApplication (A.map (QuotientGroup.mk' R)) (QuotientGroup.mk' R t)
      (U.map (QuotientGroup.mk' R)) (V.map (QuotientGroup.mk' R))
      (D.map (QuotientGroup.mk' R)) n := by
  have hsimple := LinearApp.isSimpleGroup h
  have hRA := LinearApp.le_centralizer h R hR
  have hUt := h.le.2
  have hUV := h.le.1
  obtain ⟨hinjA, hinj2, hπt, hAbt, hAbn, hCt, hstdb, hsylb⟩ := LinearApp.odd_quotient h R hR
  obtain ⟨hn, ht, ⟨hstd, hnn, k, _, _, hk, ⟨φ⟩⟩, ⟨-, -, -, -⟩,
    ⟨hUA, ⟨SU, hSU⟩, hVea, hVcard, htV, hVA, hVt, hcomm⟩,
    ⟨hD, hDcyc, hDcard, hDU, hUD, hDV, hDt, hregU, hregV⟩, he⟩ := h
  set π := QuotientGroup.mk' R
  have : IsElementaryAbelian 2 V := hVea
  have hV2 : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 V
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hinjV : Set.InjOn π (V : Set H) := hinj2 V hV2
  have hAR : ∀ x ∈ A, x ∈ R → x = 1 := fun x hx hxR =>
    hinjA hx (one_mem A) (by rw [map_one]; exact (QuotientGroup.eq_one_iff x).mpr hxR)
  have hVU : ∀ x ∈ V, π x ∈ U.map π → x ∈ U := by
    rintro x hx ⟨u, hu, hux⟩
    rw [← hinjV (hUV hu) hx hux]
    exact hu
  have hDA : D ≤ A := hD.trans inf_le_left
  refine ⟨hn, hπt, ⟨hstdb,
      fun hN => hnn (normal_of_map_normal_of_le_centralizer hRA hstd.2.2.2.2 hN), k,
      inferInstance, inferInstance, hk, ⟨(MulEquiv.ofBijective (π.subgroupMap A)
        ⟨fun x y hxy => Subtype.ext (hinjA x.2 y.2 (congrArg Subtype.val hxy)),
          π.subgroupMap_surjective A⟩).symm.trans φ⟩⟩,
    ⟨mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hAbt hx),
      by
        obtain ⟨Sb, hSb⟩ := hsylb
        exact ⟨Sb, by
          rw [← hSb, Subgroup.subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]⟩,
      hAbt, hAbn⟩,
    ⟨map_mono hUA, ?_, CFSG.IsElementaryAbelian.map π, ?_,
      le_normalizer_map π (mem_map_of_mem π htV), ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, not_central_sylow_map ht hinj2 hCt he⟩
  · refine ⟨SU.mapSurjective (π.subgroupMap_surjective A), ?_⟩
    rw [Sylow.coe_mapSurjective, hSU]
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mem_subgroupOf.mpr (mem_map_of_mem π (mem_subgroupOf.mp ha))
    · intro hx
      obtain ⟨u, hu, hux⟩ := mem_subgroupOf.mp hx
      exact ⟨⟨u, hUA hu⟩, mem_subgroupOf.mpr hu, Subtype.ext hux⟩
  · rw [card_map_of_injOn π V fun a ha b hb hab => hinjV ha hb hab, hVcard]
  · refine le_antisymm (fun x hx => ?_) (le_inf (map_mono hUV) (map_mono hUA))
    obtain ⟨⟨v, hv, rfl⟩, hxA⟩ := mem_inf.mp hx
    obtain ⟨e, hve⟩ := hV2 ⟨v, hv⟩
    have hve' : v ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val hve
    have hvA := mem_of_map_mem_of_pow hR hRA hAR hve' hxA
    exact mem_map_of_mem π (by rw [← hVA]; exact mem_inf.mpr ⟨hv, hvA⟩)
  · refine le_antisymm (fun x hx => ?_) (le_inf (map_mono hUV) ?_)
    · obtain ⟨⟨v, hv, rfl⟩, hxt⟩ := mem_inf.mp hx
      have hW : IsPGroup 2 (zpowers t ⊔ V : Subgroup H) :=
        IsPGroup.to_sup_of_normal_right' hz hV2 (zpowers_le.mpr htV)
      have hvt : v * t = t * v := by
        apply hinj2 _ hW (mul_mem (mem_sup_right hv) (mem_sup_left (mem_zpowers t)))
          (mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hv))
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.mp hxt
      exact mem_map_of_mem π (by
        rw [← hVt]
        exact mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr hvt⟩)
    · rintro _ ⟨u, hu, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hUt hu)])
  · rw [← hcomm, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, by rw [map_mul, map_mul, map_mul, map_inv, map_inv]⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨π v, mem_map_of_mem π hv, by rw [map_mul, map_mul, map_mul, map_inv, map_inv]⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact mem_inf.mpr ⟨mem_map_of_mem π (mem_inf.mp (hD hd)).1,
      le_normalizer_map π (mem_map_of_mem π (mem_inf.mp (hD hd)).2)⟩
  · exact isCyclic_of_surjective (π.subgroupMap D) (π.subgroupMap_surjective D)
  · rw [card_map_of_injOn π D fun a ha b hb hab => hinjA (hDA ha) (hDA hb) hab, hDcard]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨d, hd, rfl⟩, ⟨u, hu, hud⟩⟩ := mem_inf.mp hx
    have hdu : u = d := hinjA (hUA hu) (hDA hd) hud
    have hd1 : d ∈ D ⊓ U := mem_inf.mpr ⟨hd, hdu ▸ hu⟩
    rw [hDU, mem_bot] at hd1
    rw [hd1, map_one]
    exact one_mem _
  · rw [← Subgroup.map_sup, hUD]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨haA, haN⟩ := mem_inf.mp ha
      exact mem_inf.mpr ⟨mem_map_of_mem π haA, le_normalizer_map π (mem_map_of_mem π haN)⟩
    · intro x hx
      obtain ⟨⟨a, haA, rfl⟩, haN⟩ := mem_inf.mp hx
      refine mem_map_of_mem π (mem_inf.mpr ⟨haA, mem_normalizer_iff.mpr fun u =>
        ⟨fun hu => ?_, fun hu => ?_⟩⟩)
      · have h1 : π (a * u * a⁻¹) ∈ U.map π := by
          rw [map_mul, map_mul, map_inv]
          exact (mem_normalizer_iff.mp haN (π u)).mp (mem_map_of_mem π hu)
        obtain ⟨u', hu', hu'e⟩ := h1
        rw [← hinjA (hUA hu') (A.mul_mem (A.mul_mem haA (hUA hu)) (A.inv_mem haA)) hu'e]
        exact hu'
      · have h1 : π u ∈ U.map π := by
          apply (mem_normalizer_iff.mp haN (π u)).mpr
          rw [← map_inv, ← map_mul, ← map_mul]
          exact mem_map_of_mem π hu
        obtain ⟨u', hu', hu'e⟩ := h1
        have huA : u ∈ A := by
          have h2 : u = a⁻¹ * (a * u * a⁻¹) * a := by group
          rw [h2]
          exact A.mul_mem (A.mul_mem (A.inv_mem haA) (hUA hu)) haA
        rw [← hinjA (hUA hu') huA hu'e]
        exact hu'
  · rintro _ ⟨d, hd, rfl⟩
    exact le_normalizer_map π (mem_map_of_mem π (hDV hd))
  · rintro _ ⟨d, hd, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hDt hd)])
  · rintro _ ⟨u, hu, rfl⟩ hu1 _ ⟨w, hw, rfl⟩ hw1
    have hu1' : u ≠ 1 := fun h1 => hu1 (by rw [h1, map_one])
    have hw1' : w ≠ 1 := fun h1 => hw1 (by rw [h1, map_one])
    obtain ⟨d, hd, hduniq⟩ := hregU u hu hu1' w hw hw1'
    refine ⟨⟨π d, mem_map_of_mem π d.2⟩, ?_, ?_⟩
    · change π d * π u * (π d)⁻¹ = π w
      rw [← map_inv, ← map_mul, ← map_mul, hd]
    · rintro ⟨_, d', hd', rfl⟩ hy
      have h1 : d' * u * d'⁻¹ = w := by
        apply hinjA (A.mul_mem (A.mul_mem (hDA hd') (hUA hu)) (A.inv_mem (hDA hd'))) (hUA hw)
        rw [map_mul, map_mul, map_inv]
        exact hy
      exact Subtype.ext (congrArg (fun z : D => π (z : H)) (hduniq ⟨d', hd'⟩ h1))
  · rintro _ ⟨v, hv, rfl⟩ hvU _ ⟨w, hw, rfl⟩ hwU
    have hvU' : v ∉ U := fun h1 => hvU (mem_map_of_mem π h1)
    have hwU' : w ∉ U := fun h1 => hwU (mem_map_of_mem π h1)
    obtain ⟨d, hd, hduniq⟩ := hregV v hv hvU' w hw hwU'
    refine ⟨⟨π d, mem_map_of_mem π d.2⟩, ?_, ?_⟩
    · change (π d * π v * (π d)⁻¹)⁻¹ * π w ∈ U.map π
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
      exact mem_map_of_mem π hd
    · rintro ⟨_, d', hd', rfl⟩ hy
      have hdv : d' * v * d'⁻¹ ∈ V := (mem_normalizer_iff.mp (hDV hd') v).mp hv
      have h1 : (d' * v * d'⁻¹)⁻¹ * w ∈ U := by
        apply hVU _ (V.mul_mem (V.inv_mem hdv) hw)
        rw [map_mul, map_inv, map_mul, map_mul, map_inv]
        exact hy
      exact Subtype.ext (congrArg (fun z : D => π (z : H)) (hduniq ⟨d', hd'⟩ h1))

end LinearApp

section Main

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}


theorem gms_linear_local_normal_closure_of_fieldBound
    (h : GMSLinearLocalApplication A t U V D n) (hF : LocalFieldBound A t n) :
    let R := CFSG.Open.standardComponentOddCore H
    let π : H →* H ⧸ R := QuotientGroup.mk' R
    let X := normalClosure (A : Set H)
    Set.InjOn π (A : Set H) ∧ Set.InjOn π (V : Set H) ∧ Set.InjOn π (zpowers t : Set H) ∧
      CFSG.Open.standardComponentIsStandard (A.map π) ∧ ¬ (A.map π).Normal ∧
      centralizer (X : Set H) = R ∧ Group.IsPerfect X ∧
      (center X).map X.subtype = X ⊓ R ∧
      (CFSG.Open.standardComponentOddCore X).map X.subtype = X ⊓ R ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
          ∃ (ψ : X ⧸ center X ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
            (∀ (a : A) (x : X), (x : H) = a → ψ (x : X ⧸ center X) = (α a, α a)) ∧
            ∀ (x y : X) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
              ψ (x : X ⧸ center X) = (y₁, y₂) → ψ (y : X ⧸ center X) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
          ∃ ψ : X ⧸ center X ≃* SL(2, k₂),
            (∀ x y : X, (y : H) = t⁻¹ * x * t →
              ((ψ (y : X ⧸ center X) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : X ⧸ center X) : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
            ∀ g : SL(2, k₂),
              g ∈ ((A.subgroupOf X).map (QuotientGroup.mk' (center X))).map ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      ∃ e : X ⧸ center X ≃* X.map π, ∀ x : X, (e (x : X ⧸ center X) : H ⧸ R) = π x := by
  intro R π X
  have hR : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore H
  obtain ⟨hinjA, hinj2, -, -, -, hCt, hstdb, -⟩ := LinearApp.odd_quotient h R hR
  obtain ⟨hperf, -, hfin⟩ := LinearApp.elementary h
  have happ := LinearApp.map_quotient h R hR
  have hS : LocalSetting (A.map π) (π t) (U.map π) (V.map π) (D.map π) n :=
    ⟨GMSK.standardComponentOddCore_quotient_eq_bot H, happ⟩
  obtain ⟨hCE, -, hEA, -, hXor⟩ := hS.layer_selection (hF.map_quotient hCt)
  have hXE : X.map π = CFSG.layer (H ⧸ R) := by
    rw [hEA, map_normalClosure _ _ (QuotientGroup.mk'_surjective R), ← coe_map]
  obtain ⟨hCX, hZ, hO, e, he⟩ := hfin (by rw [hXE]; exact hCE)
  have hAX : A ≤ X := le_normalClosure
  have hV2 : IsPGroup 2 V := @IsElementaryAbelian.isPGroup 2 V _ h.2.2.2.2.1.2.2.1
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.2.1, pow_one])
  refine ⟨hinjA, hinj2 V hV2, hinj2 _ hz, hstdb, happ.2.2.1.2.1, hCX, hperf, hZ.trans hO, hO, ?_,
    e, he⟩
  let e' : X ⧸ center X ≃* CFSG.layer (H ⧸ R) := e.trans (MulEquiv.subgroupCongr hXE)
  have he' : ∀ x : X, (e' (x : X ⧸ center X) : H ⧸ R) = π x := he
  have hconj : ∀ x y : X, (y : H) = t⁻¹ * x * t →
      ((e' (y : X ⧸ center X)) : H ⧸ R) = (π t)⁻¹ * (e' (x : X ⧸ center X)) * π t := by
    intro x y hyx
    rw [he', he', hyx, map_mul, map_mul, map_inv]
  let ιA : A ≃* A.map π := MulEquiv.ofBijective (π.subgroupMap A)
    ⟨fun x y hxy => Subtype.ext (hinjA x.2 y.2 (congrArg Subtype.val hxy)),
      π.subgroupMap_surjective A⟩
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 →
      (X ⧸ center X ≃* SL(2, k) × SL(2, k)) → (X ⧸ center X ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (isEmpty_mulEquiv_sl2_prod (k := k) (by have := h.1; omega) hk₂').false
      (ψ₂.symm.trans ψ₁)
  rcases hXor with ⟨⟨k, _, _, hk, ψ, α, hψA, hψt⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, hψt, hψA⟩, -⟩
  · refine Or.inl ⟨⟨k, inferInstance, inferInstance, hk, e'.trans ψ, ιA.trans α,
      fun a x hxa => ?_, fun x y y₁ y₂ hyx hx => ?_⟩, ?_⟩
    · exact hψA (ιA a) (e' x) (by rw [he', hxa]; rfl)
    · exact hψt (e' x) (e' y) y₁ y₂ (hconj x y hyx) hx
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂
        (e'.trans ψ) ψ₂
  · refine Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, e'.trans ψ,
      fun x y hyx => hψt (e' x) (e' y) (hconj x y hyx), fun g => ?_⟩, ?_⟩
    · rw [← hψA g, mem_map_equiv, mem_map_equiv, MulEquiv.symm_trans_apply]
      generalize ψ.symm g = z
      constructor
      · rintro ⟨x, hx, hxz⟩
        have hz' : z = e' (QuotientGroup.mk' (center X) x) := by
          rw [hxz, MulEquiv.apply_symm_apply]
        rw [mem_subgroupOf, hz', QuotientGroup.mk'_apply, he']
        exact mem_map_of_mem π (mem_subgroupOf.mp hx)
      · intro hzA
        obtain ⟨a, ha, haz⟩ := mem_subgroupOf.mp hzA
        refine ⟨⟨a, hAX ha⟩, mem_subgroupOf.mpr ha, ?_⟩
        rw [MulEquiv.eq_symm_apply, QuotientGroup.mk'_apply]
        exact Subtype.ext ((he' ⟨a, hAX ha⟩).trans haz)
    · rintro ⟨k, _, _, -, ψ₁, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ₁
        (e'.trans ψ)

theorem ctt_bn_gms_linear_local_normal_closure_of_fieldBound
    (h : MiyamotoPrimaryLinearApplication A t U V D n) (hF : LocalFieldBound A t n) :
    let R := CFSG.Open.standardComponentOddCore H
    let π : H →* H ⧸ R := QuotientGroup.mk' R
    let X := normalClosure (A : Set H)
    Set.InjOn π (A : Set H) ∧ Set.InjOn π (V : Set H) ∧ Set.InjOn π (zpowers t : Set H) ∧
      CFSG.Open.standardComponentIsStandard (A.map π) ∧ ¬ (A.map π).Normal ∧
      centralizer (X : Set H) = R ∧ Group.IsPerfect X ∧
      (center X).map X.subtype = X ⊓ R ∧
      (CFSG.Open.standardComponentOddCore X).map X.subtype = X ⊓ R ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
          ∃ (ψ : X ⧸ center X ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
            (∀ (a : A) (x : X), (x : H) = a → ψ (x : X ⧸ center X) = (α a, α a)) ∧
            ∀ (x y : X) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
              ψ (x : X ⧸ center X) = (y₁, y₂) → ψ (y : X ⧸ center X) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
          ∃ ψ : X ⧸ center X ≃* SL(2, k₂),
            (∀ x y : X, (y : H) = t⁻¹ * x * t →
              ((ψ (y : X ⧸ center X) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : X ⧸ center X) : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
            ∀ g : SL(2, k₂),
              g ∈ ((A.subgroupOf X).map (QuotientGroup.mk' (center X))).map ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      ∃ e : X ⧸ center X ≃* X.map π, ∀ x : X, (e (x : X ⧸ center X) : H ⧸ R) = π x :=
  gms_linear_local_normal_closure_of_fieldBound h.1 hF

end Main

end CFSG.LocalAnalysis.EvenBN.GMS
