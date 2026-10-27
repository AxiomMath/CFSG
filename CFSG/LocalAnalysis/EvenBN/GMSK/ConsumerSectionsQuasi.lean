module

public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSectionsBender
import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem quasisimple_involution_centralizer_odd_normal_quotient_standardness {F : Type*}
    [Group F] [Finite F] {J : Subgroup F} (hJq : CFSG.Open.IsQuasisimple J)
    {a : F} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set F))
    (hJn : (J.subgroupOf (centralizer ({a} : Set F))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (J : Set F) ⊓ centralizer ({a} : Set F)),
      (S : Subgroup _).map (centralizer (J : Set F) ⊓ centralizer ({a} : Set F)).subtype =
        zpowers a)
    (R : Subgroup F) [R.Normal] (hR : Odd (Nat.card R))
    (hZR : (center J).map J.subtype ≤ R) :
    let θ : F →* F ⧸ R := QuotientGroup.mk' R
    J ⊓ R = (center J).map J.subtype ∧
      (∃ e : J ⧸ center J ≃* J.map θ, ∀ j : J, ((e j : J.map θ) : F ⧸ R) = θ j) ∧
      (∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F)) ∧
      orderOf (θ a) = 2 ∧ IsSimpleGroup (J.map θ) ∧ (∃ x y : J.map θ, x * y ≠ y * x) ∧
      J.map θ ≤ centralizer ({θ a} : Set (F ⧸ R)) ∧
      ((J.map θ).subgroupOf (centralizer ({θ a} : Set (F ⧸ R)))).Normal ∧
      centralizer ({θ a} : Set (F ⧸ R)) = (centralizer ({a} : Set F)).map θ ∧
      centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
          centralizer ({θ a} : Set (F ⧸ R)) =
        (centralizer (J : Set F) ⊓ centralizer ({a} : Set F)).map θ ∧
      CFSG.Open.standardComponentIsStandard (J.map θ) ∧
      (∃ S : Sylow 2 (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))),
        (S : Subgroup _).map
          (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))).subtype = zpowers (θ a)) ∧
      (∀ S : Sylow 2 (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))),
        Nat.card S = 2) ∧
      ∀ b ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)), orderOf b = 2 →
        ∃ h ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)), h⁻¹ * θ a * h = b := by
  intro θ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := centralizer (J : Set F) ⊓ centralizer ({a} : Set F) with hB
  obtain ⟨S, hS⟩ := hsyl
  have hθeq : ∀ x y : F, θ x = θ y → x⁻¹ * y ∈ R := fun x y h => QuotientGroup.eq.mp h
  have hinj2 : ∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F) := by
    intro Q hQ x hx y hy hxy
    have h1 : x⁻¹ * y ∈ R := hθeq x y hxy
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
  have hZ : Odd (Nat.card (center J)) := by
    have h := Subgroup.card_dvd_of_le hZR
    rw [card_map_of_injective J.subtype_injective] at h
    exact hR.of_dvd_nat h
  have hE : ∃ E : Subgroup F, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨A, ⟨hAc, hA2⟩, hA4⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
        (CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp hJq)
          hZ)
    refine ⟨A.map J.subtype, map_subtype_le A, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      change (x : F) * y = y * x
      have h := congrArg Subtype.val (hAc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      change x * y = y * x at h
      rw [← coe_mul, ← coe_mul, h]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hA2 x hx, map_one]
    · rw [card_map_of_injective J.subtype_injective, hA4]
  have hJR : R.subgroupOf J ≤ center J := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups_assembly hJq
      (inferInstance : (R.subgroupOf J).Normal) with h | h
    · exfalso
      obtain ⟨E, hEJ, -, hE4⟩ := hE
      have hER : E ≤ R := fun x hx => by
        have : (⟨x, hEJ hx⟩ : J) ∈ R.subgroupOf J := h ▸ mem_top _
        exact this
      have h4 := Subgroup.card_dvd_of_le hER
      rw [hE4] at h4
      exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4))
    · exact h
  have hJRc : J ⊓ R = (center J).map J.subtype := by
    apply le_antisymm
    · rintro x ⟨hxJ, hxR⟩
      exact ⟨⟨x, hxJ⟩, hJR (mem_subgroupOf.mpr hxR), rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z.2, hZR ⟨z, hz, rfl⟩⟩
  let fJ : J →* J.map θ := θ.subgroupMap J
  have hfJsurj : Function.Surjective fJ := θ.subgroupMap_surjective J
  have hker : fJ.ker = center J := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      apply hJR
      rw [mem_subgroupOf]
      have : θ x = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro hx
      apply Subtype.ext
      show θ x = 1
      exact (QuotientGroup.eq_one_iff _).mpr (hZR ⟨x, hx, rfl⟩)
  let e : J ⧸ center J ≃* J.map θ :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fJ hfJsurj)
  obtain ⟨-, hJs, hJnab⟩ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp hJq
  have hJbsimple : IsSimpleGroup (J.map θ) := e.symm.isSimpleGroup
  have hJbnab : ∃ x y : J.map θ, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hJnab
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hθa : orderOf (θ a) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ha2, map_one]
    · intro h
      apply ha1
      exact hinj2 (zpowers a) hza (mem_zpowers a) (one_mem _) (by rw [h, map_one])
  have hσ : Function.Involutive (MulAut.conj a) := fun x => by
    simp only [MulAut.conj_apply]
    calc a * (a * x * a⁻¹) * a⁻¹ = a ^ 2 * x * (a ^ 2)⁻¹ := by rw [pow_two]; group
      _ = x := by rw [ha2, one_mul, inv_one, mul_one]
  have hCa : centralizer ({θ a} : Set (F ⧸ R)) = (centralizer ({a} : Set F)).map θ := by
    apply le_antisymm
    · intro q hq
      have hfix : MulAut.conj (θ a) q = q := by
        rw [MulAut.conj_apply]
        rw [mem_centralizer_singleton_iff] at hq
        rw [← hq, mul_inv_cancel_right]
      obtain ⟨c, hc, hcfix⟩ :=
        CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel (MulAut.conj a)
          (MulAut.conj (θ a)) hσ θ (QuotientGroup.mk'_surjective R)
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
  have hJbC : J.map θ ≤ centralizer ({θ a} : Set (F ⧸ R)) := by
    rw [hCa]
    exact map_mono hJa
  have hconjJ : ∀ c ∈ centralizer ({a} : Set F), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    have := hJn.conj_mem ⟨j, hJa hj⟩ (mem_subgroupOf.mpr hj) ⟨c, hc⟩
    exact mem_subgroupOf.mp this
  have hJbn : ((J.map θ).subgroupOf (centralizer ({θ a} : Set (F ⧸ R)))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨j, hj, hjn⟩ := hn
    have hg : (g : F ⧸ R) ∈ (centralizer ({a} : Set F)).map θ := hCa ▸ g.2
    obtain ⟨c, hc, hcg⟩ := hg
    refine ⟨c * j * c⁻¹, hconjJ c hc j hj, ?_⟩
    change θ (c * j * c⁻¹) = (g : F ⧸ R) * (n : F ⧸ R) * (g : F ⧸ R)⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hjn]
  have hperf : Group.IsPerfect J := ⟨hJq.1⟩
  have hBb : centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
      centralizer ({θ a} : Set (F ⧸ R)) = B.map θ := by
    apply le_antisymm
    · rintro q ⟨hqJ, hqa⟩
      have hq : q ∈ (centralizer ({a} : Set F)).map θ := hCa ▸ hqa
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
        show (j : F)⁻¹ * (c * j * c⁻¹) ∈ R
        apply hθeq
        have h2 := mem_centralizer_iff.mp hqJ (θ j) ⟨j, j.2, rfl⟩
        rw [map_mul, map_mul, map_inv, ← h2, mul_inv_cancel_right]
      have hσid :=
        CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ
          hdisp
      show c ∈ centralizer (J : Set F)
      rw [mem_centralizer_iff]
      intro j hj
      have h3 : c * j * c⁻¹ = j := congrArg Subtype.val (DFunLike.congr_fun hσid ⟨j, hj⟩)
      calc j * c = c * j * c⁻¹ * c := by rw [h3]
        _ = c * j := by group
    · rintro _ ⟨c, ⟨hcJ, hca⟩, rfl⟩
      have hcJ' : c ∈ centralizer (J : Set F) := hcJ
      have hca' : c ∈ centralizer ({a} : Set F) := hca
      refine ⟨?_, ?_⟩
      · show θ c ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))
        rw [mem_centralizer_iff]
        rintro _ ⟨j, hj, rfl⟩
        rw [← map_mul, mem_centralizer_iff.mp hcJ' j hj, map_mul]
      · show θ c ∈ centralizer ({θ a} : Set (F ⧸ R))
        rw [mem_centralizer_singleton_iff] at hca' ⊢
        rw [← map_mul, hca', map_mul]
  have hsylb : ∃ Sb : Sylow 2 ↥(centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
      centralizer ({θ a} : Set (F ⧸ R))),
      (Sb : Subgroup _).map (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
        centralizer ({θ a} : Set (F ⧸ R))).subtype = zpowers (θ a) := by
    rw [hBb]
    let f : B →* B.map θ := θ.subgroupMap B
    have hf : Function.Surjective f := θ.subgroupMap_surjective B
    refine ⟨S.mapSurjective hf, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : (B.map θ).subtype.comp f = θ.comp B.subtype := MonoidHom.ext fun _ => rfl
    rw [hcomp, ← Subgroup.map_map, hS, MonoidHom.map_zpowers]
  have hJbq : CFSG.Assembly.IsQuasisimple (J.map θ) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hJbnab)
  have hEb : ∃ Eb : Subgroup (F ⧸ R), Eb ≤ J.map θ ∧ CFSG.Assembly.IsElemAbelian 2 Eb ∧
      Nat.card Eb = 4 := by
    obtain ⟨E, hEJ, hEab, hE4⟩ := hE
    have hinjE := hinj2 E (IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num))
    refine ⟨E.map θ, map_mono hEJ, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
    · rintro ⟨_, e₁, he₁, rfl⟩ ⟨_, e₂, he₂, rfl⟩
      apply Subtype.ext
      change θ e₁ * θ e₂ = θ e₂ * θ e₁
      have h := congrArg Subtype.val (hEab.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
      change e₁ * e₂ = e₂ * e₁ at h
      rw [← map_mul, h, map_mul]
    · rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hEab.2 e he, map_one]
    · rw [← hE4]
      have hinj : Function.Injective (θ.subgroupMap E) := fun x y h =>
        Subtype.ext (hinjE x.2 y.2 (congrArg Subtype.val h))
      exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, θ.subgroupMap_surjective E⟩)).symm
  have haB : a ∈ B := by
    have : a ∈ (S : Subgroup B).map B.subtype := hS ▸ mem_zpowers a
    exact map_subtype_le _ this
  have haJb : θ a ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, mem_centralizer_iff.mp haB.1 j hj, map_mul]
  have hcompb : CFSG.Assembly.IsComponentOf (J.map θ) (centralizer ({θ a} : Set (F ⧸ R))) :=
    ⟨hJbC, CFSG.Assembly.IsSubnormal.step hJbC hJbn (CFSG.Assembly.IsSubnormal.refl _), hJbq⟩
  obtain ⟨⟨S₀, hS₀⟩, hconjb, hstd⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.quasisimple_involution_centralizer_order_two_standard hJbq hEb
      haJb hθa hcompb hsylb
  have hcard : ∀ S' : Sylow 2 (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))),
      Nat.card S' = 2 := fun S' => by
    rw [Nat.card_congr (Sylow.equiv S' S₀).toEquiv,
      ← card_map_of_injective (subtype_injective _), hS₀, Nat.card_zpowers, hθa]
  exact ⟨hJRc, ⟨e, fun _ => rfl⟩, hinj2, hθa, hJbsimple, hJbnab, hJbC, hJbn, hCa, hBb, hstd,
    ⟨S₀, hS₀⟩, hcard, hconjb⟩

theorem stdData_odd_quotient_of_quasisimple {T : StdType} (hiso : StdType.IsoInvariant T)
    {H : Type} [Group H] [Finite H] {J : Subgroup H} {n : ℕ}
    (hJq : CFSG.Open.IsQuasisimple J) (hJ : T n (J ⧸ center J)) {t : H} (ht : orderOf t = 2)
    (hJt : J ≤ centralizer ({t} : Set H))
    (hJn : (J.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (J : Set H) ⊓ centralizer ({t} : Set H)),
      (S : Subgroup _).map (centralizer (J : Set H) ⊓ centralizer ({t} : Set H)).subtype =
        zpowers t)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (hZR : (center J).map J.subtype ≤ R) :
    CFSG.Open.standardComponentIsStandard (J.map (QuotientGroup.mk' R)) ∧
      T n (J.map (QuotientGroup.mk' R)) ∧ orderOf (QuotientGroup.mk' R t) = 2 ∧
      QuotientGroup.mk' R t ∈
        centralizer ((J.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R)) ∧
      ¬ 2 ∣ (zpowers (QuotientGroup.mk' R t)).relIndex
        (centralizer ((J.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R))) ∧
      ∀ S : Sylow 2 (centralizer ((J.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) :
        Set (H ⧸ R))), Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := QuotientGroup.mk' R
  set C := centralizer ((J.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R))
  obtain ⟨-, ⟨e, -⟩, -, hθt, -, -, -, -, -, -, hstd, ⟨S₀, hS₀⟩, hcard, -⟩ :=
    quasisimple_involution_centralizer_odd_normal_quotient_standardness hJq ht hJt hJn hsyl R hR
      hZR
  have hsub : (zpowers (θ t)).subgroupOf C = S₀ := by
    rw [← hS₀, Subgroup.subgroupOf, comap_map_eq_self_of_injective (subtype_injective C)]
  have htC : θ t ∈ C := by
    have h : θ t ∈ (S₀ : Subgroup C).map C.subtype := by
      rw [hS₀]
      exact mem_zpowers _
    obtain ⟨x, -, hx⟩ := h
    exact hx ▸ x.2
  have hidx : ¬ 2 ∣ (zpowers (θ t)).relIndex C := by
    rw [Subgroup.relIndex, hsub]
    exact Sylow.not_dvd_index S₀
  exact ⟨hstd, hiso n _ _ e hJ, hθt, htC, hidx, hcard⟩

theorem sharpOutcomeU3_oddCore_quotient_of_quasisimple
    (hGMS : GMSUnitarySharpKRankOneStatement) {H : Type} [Group H] [Finite H]
    (hH : CFSG.SectionRank.IsKGroupCat H) {J : Subgroup H} {n : ℕ}
    (hJq : CFSG.Open.IsQuasisimple J) (hJ : LieModel (J ⧸ center J) .PSU 3 2 n) {t : H}
    (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hZR : (center J).map J.subtype ≤ CFSG.Open.standardComponentOddCore H)
    (hnn : ¬ (J.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))).Normal) :
    SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * n))
      (H ⧸ CFSG.Open.standardComponentOddCore H)
      (J.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)))
      (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H) t) := by
  have hJt : J ≤ centralizer ({t} : Set H) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htJ a ha)
  obtain ⟨hstd, hT, hθt, htC, hidx, -⟩ := stdData_odd_quotient_of_quasisimple isoInvariant_T_U3
    hJq (⟨two_le_of_lieModel_PSU3 hJ, hJ⟩ : T_U3 n (J ⧸ center J)) ht hJt hJn
    (exists_sylow_inf_centralizer_eq_zpowers ht htJ hrank) _
    (odd_card_standardComponentOddCore H) hZR
  exact hGMS _ (hH.quotient _) (standardComponentOddCore_quotient_eq_bot H) n _
    ⟨hT.1, hstd, hnn, hT.2⟩ _ hθt htC hidx

end CFSG.LocalAnalysis.EvenBN.GMSK
