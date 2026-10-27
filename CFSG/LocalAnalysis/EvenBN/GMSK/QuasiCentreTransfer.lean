module

public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem qcTransfer_injOn_two {F : Type*} [Group F] (R : Subgroup F) [R.Normal]
    (hR : Odd (Nat.card R)) (Q : Subgroup F) (hQ : IsPGroup 2 Q) :
    Set.InjOn (QuotientGroup.mk' R) (Q : Set F) := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ R := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hx) hy
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨_, h2⟩
  rw [Subgroup.orderOf_mk] at hk
  have h3 : orderOf (x⁻¹ * y) ∣ Nat.card R := by
    have := orderOf_dvd_natCard (⟨_, h1⟩ : R)
    rwa [Subgroup.orderOf_mk] at this
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h3))
  rw [hk0, pow_zero] at hk
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hk)

theorem qcTransfer_centralizer_eq_map {F : Type*} [Group F] [Finite F] (R : Subgroup F)
    [R.Normal] (hR : Odd (Nat.card R)) {a : F} (ha : orderOf a = 2) :
    centralizer ({QuotientGroup.mk' R a} : Set (F ⧸ R)) =
      (centralizer ({a} : Set F)).map (QuotientGroup.mk' R) := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hσ : Function.Involutive (MulAut.conj a) := fun x => by
    simp only [MulAut.conj_apply]
    calc a * (a * x * a⁻¹) * a⁻¹ = a ^ 2 * x * (a ^ 2)⁻¹ := by rw [pow_two]; group
      _ = x := by rw [ha2, one_mul, inv_one, mul_one]
  apply le_antisymm
  · intro q hq
    have hfix : MulAut.conj (QuotientGroup.mk' R a) q = q := by
      rw [MulAut.conj_apply]
      rw [mem_centralizer_singleton_iff] at hq
      rw [← hq, mul_inv_cancel_right]
    obtain ⟨c, hc, hcfix⟩ :=
      CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel (MulAut.conj a)
        (MulAut.conj (QuotientGroup.mk' R a)) hσ (QuotientGroup.mk' R)
        (QuotientGroup.mk'_surjective R)
        (by rw [QuotientGroup.ker_mk']; exact hR)
        (fun x => by simp only [MulAut.conj_apply, map_mul, map_inv]) q hfix
    refine ⟨c, ?_, hc⟩
    show c ∈ centralizer ({a} : Set F)
    rw [mem_centralizer_singleton_iff]
    rw [MulAut.conj_apply] at hcfix
    exact (mul_inv_eq_iff_eq_mul.mp hcfix).symm
  · rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc
    rw [mem_centralizer_singleton_iff, ← map_mul, hc, map_mul]

theorem qcTransfer_subgroupOf_le_center {H : Type} [Group H] [Finite H] {J : Subgroup H}
    (hJq : CFSG.Open.IsQuasisimple ↥J) {n : ℕ} (hJm : LieModel (↥J ⧸ center ↥J) .PSU 3 2 n)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R)) : R.subgroupOf J ≤ center J := by
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups_assembly hJq
    (inferInstance : (R.subgroupOf J).Normal) with h | h
  · exfalso
    have h2X : 2 ∣ Nat.card (↥J ⧸ center ↥J) := by
      have hf := factorization_two_card_of_lieModel_PSU3 hJm
      have hn := two_le_of_lieModel_PSU3 hJm
      have hpos : 0 < Nat.card (↥J ⧸ center ↥J) := Nat.card_pos
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').mpr (by omega)
    have h2J : 2 ∣ Nat.card J := h2X.trans (Subgroup.card_quotient_dvd_card _)
    have hJR : J ≤ R := fun x hx => by
      have : (⟨x, hx⟩ : J) ∈ R.subgroupOf J := h ▸ mem_top _
      exact this
    have h4 := Subgroup.card_dvd_of_le hJR
    exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr (h2J.trans h4))
  · exact h

theorem qcTransfer_centerQuotientEquiv {P Q : Type*} [Group P] [Group Q] (hP : Group.IsPerfect P)
    (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ center P) :
    Nonempty (P ⧸ center P ≃* Q ⧸ center Q) := by
  have hc : center P = ((QuotientGroup.mk' (center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem qcTransfer_card_le_two_of_sylow {F : Type*} [Group F] [Finite F] {B : Subgroup F} {a : F}
    (haB : a ∈ B) (ha : orderOf a = 2)
    (hsyl : ∃ S : Sylow 2 ↥(B ⊓ centralizer ({a} : Set F)),
      (S : Subgroup _).map (B ⊓ centralizer ({a} : Set F)).subtype = zpowers a) :
    ∀ Q : Subgroup F, IsPGroup 2 Q → Q ≤ B → Nat.card Q ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hsyl
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hzp : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have haCa : a ∈ centralizer ({a} : Set F) := mem_centralizer_singleton_iff.mpr rfl
  have hzB : zpowers a ≤ B := zpowers_le.mpr haB
  have stepA : ∀ Q : Subgroup F, IsPGroup 2 Q → zpowers a ≤ Q → Q ≤ B → Q = zpowers a := by
    intro Q hQ haQ hQB
    have hR : Q ⊓ centralizer ({a} : Set F) = zpowers a :=
      CFSG.LocalAnalysis.SteinbergBK.eq_of_sylow_map_le S hS (hQ.to_le inf_le_left)
        (le_inf haQ (zpowers_le.mpr haCa)) (inf_le_inf_right _ hQB)
    have haQ' : a ∈ Q := haQ (mem_zpowers a)
    have : Nontrivial Q := ⟨⟨⟨a, haQ'⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    have := hQ.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : center Q)
    have hcomm : ∀ q ∈ Q, q * (z : F) = (z : F) * q := fun q hq =>
      congrArg Subtype.val (mem_center_iff.mp z.2 ⟨q, hq⟩)
    have hzR : ((z : Q) : F) ∈ zpowers a :=
      hR ▸ ⟨(z : Q).2, mem_centralizer_singleton_iff.mpr (hcomm a haQ').symm⟩
    have hza : ((z : Q) : F) = a := by
      rcases CFSG.LocalAnalysis.SteinbergBK.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha
        hzR with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hz
      · exact h
    have hQC : Q ≤ centralizer ({a} : Set F) := by
      intro q hq
      rw [mem_centralizer_singleton_iff, ← hza]
      exact hcomm q hq
    rw [← hR, inf_eq_left.mpr hQC]
  have hzB' : IsPGroup 2 ((zpowers a).subgroupOf B) :=
    hzp.comap_of_injective B.subtype B.subtype_injective
  obtain ⟨Sa, hSa⟩ := hzB'.exists_le_sylow
  have hSaeq : (Sa : Subgroup B).map B.subtype = zpowers a := by
    apply stepA
    · exact Sa.isPGroup'.map B.subtype
    · intro x hx
      exact ⟨⟨x, hzB hx⟩, hSa (by rw [mem_subgroupOf]; exact hx), rfl⟩
    · exact map_subtype_le _
  have hcardSa : Nat.card (Sa : Subgroup B) = 2 := by
    rw [← card_map_of_injective B.subtype_injective, hSaeq, Nat.card_zpowers, ha]
  have hcardSyl : ∀ T : Sylow 2 B, Nat.card (T : Subgroup B) = 2 := by
    intro T
    rw [T.card_eq_multiplicity, ← Sa.card_eq_multiplicity, hcardSa]
  intro Q hQ hQB
  obtain ⟨T, hT⟩ := (hQ.comap_of_injective B.subtype B.subtype_injective).exists_le_sylow
  calc Nat.card Q = Nat.card (Q.subgroupOf B) :=
        (Nat.card_congr (subgroupOfEquivOfLe hQB).toEquiv).symm
    _ ≤ Nat.card (T : Subgroup B) := card_le_of_le hT
    _ = 2 := hcardSyl T

theorem quasi_transfer {H : Type} [Group H] [Finite H] {J : Subgroup H}
    (hJq : CFSG.Open.IsQuasisimple ↥J) {n : ℕ} (hJm : LieModel (↥J ⧸ center ↥J) .PSU 3 2 n)
    {t : H} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R)) :
    CFSG.Open.IsQuasisimple ↥(J.map (QuotientGroup.mk' R)) ∧
      LieModel (↥(J.map (QuotientGroup.mk' R)) ⧸ center ↥(J.map (QuotientGroup.mk' R)))
        .PSU 3 2 n ∧
      orderOf (QuotientGroup.mk' R t) = 2 ∧
      QuotientGroup.mk' R t ∈
        centralizer ((J.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R)) ∧
      ((J.map (QuotientGroup.mk' R)).subgroupOf
        (centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)))).Normal ∧
      (∀ P : Subgroup (H ⧸ R),
        P ≤ centralizer ((J.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R)) →
          IsPGroup 2 P → Nat.card P ≤ 2) ∧
      (center ↥(J.map (QuotientGroup.mk' R)) = ⊥ → (center ↥J).map J.subtype ≤ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJR : R.subgroupOf J ≤ center J := qcTransfer_subgroupOf_le_center hJq hJm R hR
  set θ : H →* H ⧸ R := QuotientGroup.mk' R with hθ
  have hperf : Group.IsPerfect J := ⟨hJq.1⟩
  let fJ : J →* J.map θ := θ.subgroupMap J
  have hfJsurj : Function.Surjective fJ := θ.subgroupMap_surjective J
  have hker : fJ.ker ≤ center J := by
    intro x hx
    apply hJR
    rw [mem_subgroupOf]
    have : θ x = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
    exact (QuotientGroup.eq_one_iff _).mp this
  have hcomap : (center (J.map θ)).comap fJ = center J :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperf fJ hfJsurj hker
  have hJbq : CFSG.IsQuasisimple (J.map θ) :=
    CFSG.LocalCores.isQuasisimple_of_surjective
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp hJq)
      fJ hfJsurj hker
  obtain ⟨e⟩ := qcTransfer_centerQuotientEquiv hperf fJ hfJsurj hker
  have hmodel : LieModel (↥(J.map θ) ⧸ center ↥(J.map θ)) .PSU 3 2 n :=
    LieModel.of_mulEquiv e hJm
  have hθeq : ∀ x y : H, θ x = θ y → x⁻¹ * y ∈ R := fun x y h => QuotientGroup.eq.mp h
  have hinj2 : ∀ Q : Subgroup H, IsPGroup 2 Q → Set.InjOn θ (Q : Set H) :=
    qcTransfer_injOn_two R hR
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hzt : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hθt : orderOf (θ t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro h
      apply ht1
      exact hinj2 (zpowers t) hzt (mem_zpowers t) (one_mem _) (by rw [h, map_one])
  have hJt : J ≤ centralizer ({t} : Set H) := fun j hj =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htJ j hj)
  have hCa : centralizer ({θ t} : Set (H ⧸ R)) = (centralizer ({t} : Set H)).map θ :=
    qcTransfer_centralizer_eq_map R hR ht
  have hJbC : J.map θ ≤ centralizer ({θ t} : Set (H ⧸ R)) := by
    rw [hCa]
    exact map_mono hJt
  have hconjJ : ∀ c ∈ centralizer ({t} : Set H), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    have := hJn.conj_mem ⟨j, hJt hj⟩ (mem_subgroupOf.mpr hj) ⟨c, hc⟩
    exact mem_subgroupOf.mp this
  have hJbn : ((J.map θ).subgroupOf (centralizer ({θ t} : Set (H ⧸ R)))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨j, hj, hjn⟩ := hn
    have hg : (g : H ⧸ R) ∈ (centralizer ({t} : Set H)).map θ := hCa ▸ g.2
    obtain ⟨c, hc, hcg⟩ := hg
    refine ⟨c * j * c⁻¹, hconjJ c hc j hj, ?_⟩
    change θ (c * j * c⁻¹) = (g : H ⧸ R) * (n : H ⧸ R) * (g : H ⧸ R)⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hjn]
  have hθtJ : θ t ∈ centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, mem_centralizer_iff.mp htJ j hj, map_mul]
  have hBb : centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R)) ⊓
      centralizer ({θ t} : Set (H ⧸ R)) =
        (centralizer (J : Set H) ⊓ centralizer ({t} : Set H)).map θ := by
    apply le_antisymm
    · rintro q ⟨hqJ, hqa⟩
      have hq : q ∈ (centralizer ({t} : Set H)).map θ := hCa ▸ hqa
      obtain ⟨c, hc, rfl⟩ := hq
      refine ⟨c, ⟨?_, hc⟩, rfl⟩
      let σ : J →* J :=
        { toFun := fun j => ⟨c * j * c⁻¹, hconjJ c hc j j.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun x y => Subtype.ext (by simp only [coe_mul]; group) }
      have hdisp : ∀ j : J, j⁻¹ * σ j ∈ center J := by
        intro j
        apply hJR
        rw [mem_subgroupOf]
        show (j : H)⁻¹ * (c * j * c⁻¹) ∈ R
        apply hθeq
        have h2 := mem_centralizer_iff.mp hqJ (θ j) ⟨j, j.2, rfl⟩
        rw [map_mul, map_mul, map_inv, ← h2, mul_inv_cancel_right]
      have hσid :=
        CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ
          hdisp
      show c ∈ centralizer (J : Set H)
      rw [mem_centralizer_iff]
      intro j hj
      have h3 : c * j * c⁻¹ = j := congrArg Subtype.val (DFunLike.congr_fun hσid ⟨j, hj⟩)
      calc j * c = c * j * c⁻¹ * c := by rw [h3]
        _ = c * j := by group
    · rintro _ ⟨c, ⟨hcJ, hca⟩, rfl⟩
      have hcJ' : c ∈ centralizer (J : Set H) := hcJ
      have hca' : c ∈ centralizer ({t} : Set H) := hca
      refine ⟨?_, ?_⟩
      · show θ c ∈ centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R))
        rw [mem_centralizer_iff]
        rintro _ ⟨j, hj, rfl⟩
        rw [← map_mul, mem_centralizer_iff.mp hcJ' j hj, map_mul]
      · show θ c ∈ centralizer ({θ t} : Set (H ⧸ R))
        rw [mem_centralizer_singleton_iff] at hca' ⊢
        rw [← map_mul, hca', map_mul]
  obtain ⟨S, hS⟩ := exists_sylow_inf_centralizer_eq_zpowers ht htJ hrank
  have hsylb : ∃ Sb : Sylow 2 ↥(centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R)) ⊓
      centralizer ({θ t} : Set (H ⧸ R))),
      (Sb : Subgroup _).map (centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R)) ⊓
        centralizer ({θ t} : Set (H ⧸ R))).subtype = zpowers (θ t) := by
    rw [hBb]
    let f : ↥(centralizer (J : Set H) ⊓ centralizer ({t} : Set H)) →*
        ↥((centralizer (J : Set H) ⊓ centralizer ({t} : Set H)).map θ) :=
      θ.subgroupMap _
    have hf : Function.Surjective f := θ.subgroupMap_surjective _
    refine ⟨S.mapSurjective hf, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : ((centralizer (J : Set H) ⊓ centralizer ({t} : Set H)).map θ).subtype.comp f =
        θ.comp (centralizer (J : Set H) ⊓ centralizer ({t} : Set H)).subtype :=
      MonoidHom.ext fun _ => rfl
    rw [hcomp, ← Subgroup.map_map, hS, MonoidHom.map_zpowers]
  have hrankb : ∀ P : Subgroup (H ⧸ R),
      P ≤ centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R)) → IsPGroup 2 P →
        Nat.card P ≤ 2 := fun P hP hP2 =>
    qcTransfer_card_le_two_of_sylow hθtJ hθt hsylb P hP2 hP
  have hlast : center ↥(J.map θ) = ⊥ → (center ↥J).map J.subtype ≤ R := by
    intro hZ
    rintro _ ⟨z, hz, rfl⟩
    have h1 : fJ z ∈ center ↥(J.map θ) := by
      have : z ∈ (center ↥(J.map θ)).comap fJ := hcomap ▸ hz
      exact this
    rw [hZ, mem_bot] at h1
    have h2 : θ z = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  exact ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJbq,
    hmodel, hθt, hθtJ, hJbn, hrankb, hlast⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
