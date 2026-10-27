module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNormalizesNoSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

namespace SolvNone

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

private theorem mem_zpowers_of_odd_of_symThree (σ : I₀ →* Y)
    (f : I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) {K : Subgroup Y}
    (hKO : ∀ n ∈ (CFSG.pCore 2 I₀).map σ, n ∈ K → n = 1) {y₀ : Y} (hy₀ : y₀ ∈ σ.range)
    (hy₀o : Odd (orderOf y₀)) (hy₀K : y₀ ∈ K) (hy₀1 : y₀ ≠ 1) {y : Y} (hy : y ∈ σ.range)
    (hyo : Odd (orderOf y)) (hyK : y ∈ K) : y ∈ zpowers y₀ := by
  have hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) := Or.inl ⟨f⟩
  obtain ⟨g₀, hg₀, rfl⟩ := exists_oUpperTwo_of_odd σ hy₀ hy₀o
  obtain ⟨g, hg, rfl⟩ := exists_oUpperTwo_of_odd σ hy hyo
  have hcube : ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀),
      f (x : I₀ ⧸ CFSG.pCore 2 I₀) ^ 3 = 1 := by
    intro x hx
    rw [← map_pow, ← QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two hb x hx), map_one]
  have hn0 : f (g₀ : I₀ ⧸ CFSG.pCore 2 I₀) ≠ 1 := by
    intro h
    have h1 : (g₀ : I₀ ⧸ CFSG.pCore 2 I₀) = 1 := f.injective (by rw [h, map_one])
    exact hy₀1 (hKO _ (Subgroup.mem_map_of_mem σ ((QuotientGroup.eq_one_iff _).mp h1)) hy₀K)
  by_cases hn : f (g : I₀ ⧸ CFSG.pCore 2 I₀) = 1
  · have h1 : (g : I₀ ⧸ CFSG.pCore 2 I₀) = 1 := f.injective (by rw [hn, map_one])
    rw [hKO _ (Subgroup.mem_map_of_mem σ ((QuotientGroup.eq_one_iff _).mp h1)) hyK]
    exact Subgroup.one_mem _
  rcases perm_three_eq_or_eq_sq _ _ (hcube g₀ hg₀) (hcube g hg) hn0 hn with h | h
  · have h' : (g₀ : I₀ ⧸ CFSG.pCore 2 I₀) = g := (f.injective h).symm
    have hm : g₀⁻¹ * g ∈ CFSG.pCore 2 I₀ := QuotientGroup.eq.mp h'
    have he : σ (g₀⁻¹ * g) = 1 := hKO _ (Subgroup.mem_map_of_mem σ hm) (by
      rw [map_mul, map_inv]
      exact K.mul_mem (K.inv_mem hy₀K) hyK)
    have : σ g = σ g₀ := by
      rw [map_mul, map_inv, inv_mul_eq_one] at he
      exact he.symm
    rw [this]
    exact mem_zpowers _
  · have h' : ((g₀ ^ 2 : I₀) : I₀ ⧸ CFSG.pCore 2 I₀) = g := by
      apply f.injective
      rw [h, QuotientGroup.mk_pow, map_pow]
    have hm : (g₀ ^ 2)⁻¹ * g ∈ CFSG.pCore 2 I₀ := QuotientGroup.eq.mp h'
    have he : σ ((g₀ ^ 2)⁻¹ * g) = 1 := hKO _ (Subgroup.mem_map_of_mem σ hm) (by
      rw [map_mul, map_inv, map_pow]
      exact K.mul_mem (K.inv_mem (K.pow_mem hy₀K 2)) hyK)
    have : σ g = σ g₀ ^ 2 := by
      rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at he
      exact he.symm
    rw [this]
    exact Subgroup.pow_mem _ (mem_zpowers _) 2

theorem le_centralizer_or_le_of_inner {K Y₀ : Subgroup Y} [K.Normal] (σ : I₀ →* Y)
    (hZ : Subgroup.center K = ⊥)
    (hinner : ∀ y ∈ σ.range, y ^ 3 = 1 → ∃ k ∈ K, ∃ c ∈ centralizer (K : Set Y), y = k * c)
    (hKcomm : ∀ Q : Subgroup Y, Q ≤ K →
      Q ≤ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ⊔
        centralizer (K : Set Y) →
      (∀ x ∈ Q, x ^ 3 = 1) → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hrkC : CFSG.pRank 3 (centralizer (K : Set Y)) ≤ 1)
    (hC : centralizer (K : Set Y) ≤ Y₀) (hO2 : pCoreOf 2 Y₀ ≤ centralizer (K : Set Y))
    (hker : Nat.Coprime 3 (Nat.card σ.ker)) (hσY : σ.range ≤ Y₀) (hσs : IsSubnormal σ.range Y₀)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
        centralizer (K : Set Y) ∨
      ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ K ∧
        ∃ y₀ ∈ K, y₀ ^ 3 = 1 ∧
          (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ zpowers y₀) := by
  by_cases hJ : (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (K : Set Y)
  · exact Or.inl hJ
  right
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hσC : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  have hrkC' : CFSG.Open.pRank 3 C ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrkC
  have hdec : ∀ y ∈ σ.range, Odd (orderOf y) →
      ∃ k ∈ K, ∃ c ∈ C, y = k * c ∧ k ^ 3 = 1 ∧ c ^ 3 = 1 := by
    intro y hy hodd
    have hy3 := pow_three_eq_one_of_mem_range_of_odd σ hb hy hodd
    obtain ⟨k, hk, c, hc, rfl⟩ := hinner y hy hy3
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc k hk
    have h1 : k ^ 3 * c ^ 3 = 1 := by rw [← Commute.mul_pow hkc 3]; exact hy3
    have hc3 : c ^ 3 = 1 := by
      have h2 : c ^ 3 ∈ K ⊓ C := by
        refine ⟨?_, Subgroup.pow_mem _ hc 3⟩
        rw [eq_inv_of_mul_eq_one_right h1]
        exact K.inv_mem (K.pow_mem hk 3)
      rwa [hKC, Subgroup.mem_bot] at h2
    refine ⟨k, hk, c, hc, rfl, ?_, hc3⟩
    rw [hc3, mul_one] at h1
    exact h1
  have hodd_of : ∀ u : I₀, (∃ m : ℕ, u ^ 3 ^ m = 1) → Odd (orderOf (σ u)) := by
    rintro u ⟨m, hm⟩
    have : (σ u) ^ 3 ^ m = 1 := by rw [← map_pow, hm, map_one]
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one this)
  by_cases hs3 : Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))
  · obtain ⟨f⟩ := hs3
    have hnoC : ∀ y₀ ∈ σ.range, Odd (orderOf y₀) → y₀ ∈ C → y₀ = 1 := by
      intro y₀ hy₀ hy₀o hy₀C
      by_contra hy₀1
      exact hJ (oUpperTwo_map_le_of_odd σ fun y' hy' hy'o =>
        mem_of_odd_of_symThree σ f hσC hy₀ hy₀o hy₀C hy₀1 hy' hy'o)
    have hallK : ∀ y ∈ σ.range, Odd (orderOf y) → y ∈ K := by
      intro y hy hodd
      obtain ⟨k, hk, c, hc, rfl, hk3, hc3⟩ := hdec y hy hodd
      obtain ⟨g, hg, hgy⟩ := exists_oUpperTwo_of_odd σ hy hodd
      have ha3 : f (g : I₀ ⧸ CFSG.pCore 2 I₀) ^ 3 = 1 := by
        rw [← map_pow, ← QuotientGroup.mk_pow,
          (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two (Or.inl ⟨f⟩) g hg), map_one]
      obtain ⟨τ, hτ⟩ := perm_three_exists_inv _ ha3
      obtain ⟨q, hq⟩ := f.surjective τ
      obtain ⟨t₀, rfl⟩ := QuotientGroup.mk_surjective q
      have hw : t₀ * g * t₀⁻¹ * g ∈ CFSG.pCore 2 I₀ := by
        rw [← QuotientGroup.eq_one_iff]
        apply f.injective
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          map_mul, map_mul, map_mul, map_inv, hq, hτ, map_one, inv_mul_cancel]
      set t : Y := σ t₀ with ht
      have htS : t ∈ σ.range := ⟨t₀, rfl⟩
      have htw : t * (k * c) * t⁻¹ * (k * c) ∈ C := by
        have h1 := hσC (Subgroup.mem_map_of_mem σ hw)
        rwa [map_mul, map_mul, map_mul, map_inv, hgy] at h1
      have htk : t * k * t⁻¹ = k⁻¹ := by
        have hcC : t * c * t⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem c hc t
        have hkK : t * k * t⁻¹ * k ∈ K :=
          K.mul_mem ((inferInstance : K.Normal).conj_mem k hk t) hk
        have hcomm : (t * c * t⁻¹) * k = k * (t * c * t⁻¹) :=
          (Subgroup.mem_centralizer_iff.mp hcC k hk).symm
        have hprod : t * (k * c) * t⁻¹ * (k * c) =
            (t * k * t⁻¹ * k) * (t * c * t⁻¹ * c) := by
          calc t * (k * c) * t⁻¹ * (k * c) = (t * k * t⁻¹) * ((t * c * t⁻¹) * k) * c := by group
            _ = (t * k * t⁻¹) * (k * (t * c * t⁻¹)) * c := by rw [hcomm]
            _ = (t * k * t⁻¹ * k) * (t * c * t⁻¹ * c) := by group
        have hkC : t * k * t⁻¹ * k ∈ C := by
          have h1 := C.mul_mem htw (C.inv_mem (C.mul_mem hcC hc))
          rwa [hprod, mul_inv_cancel_right] at h1
        have h1 : t * k * t⁻¹ * k ∈ K ⊓ C := ⟨hkK, hkC⟩
        rw [hKC, Subgroup.mem_bot] at h1
        exact eq_inv_of_mul_eq_one_left h1
      have hkY : k ∈ Y₀ := by
        have hke : k = (k * c) * c⁻¹ := by group
        rw [hke]
        exact Y₀.mul_mem (hσY hy) (Y₀.inv_mem (hC hc))
      obtain ⟨d, hd⟩ := exists_iterate_commutator_le_of_isSubnormal hσs (zpowers_le.mpr hkY)
      have hck : ⁅k, t⁆ = k⁻¹ := by
        rw [commutatorElement_def]
        calc k * t * k⁻¹ * t⁻¹ = k * (t * k * t⁻¹)⁻¹ := by group
          _ = k * k := by rw [htk, inv_inv]
          _ = k ^ 3 * k⁻¹ := by rw [pow_succ, pow_two, mul_inv_cancel_right]
          _ = k⁻¹ := by rw [hk3, one_mul]
      have hiter : ∀ n : ℕ, zpowers k ≤ (fun X : Subgroup Y => ⁅X, σ.range⁆)^[n] (zpowers k) := by
        intro n
        induction n with
        | zero => exact le_rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply']
          refine zpowers_le.mpr ?_
          have hm : ⁅k, t⁆ ∈ ⁅(fun X : Subgroup Y => ⁅X, σ.range⁆)^[n] (zpowers k), σ.range⁆ :=
            Subgroup.commutator_mem_commutator (ih (mem_zpowers k)) htS
          rw [hck] at hm
          simpa using Subgroup.inv_mem _ hm
      have hkS : k ∈ σ.range := hd (hiter d (mem_zpowers k))
      have hcS : c ∈ σ.range := by
        have hce : c = k⁻¹ * (k * c) := by group
        rw [hce]
        exact σ.range.mul_mem (σ.range.inv_mem hkS) hy
      have hco : Odd (orderOf c) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hc3)
      rw [hnoC c hcS hco hc, mul_one]
      exact hk
    have hJK : (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ K :=
      oUpperTwo_map_le_of_odd σ hallK
    obtain ⟨y₀, hy₀, hy₀o, hy₀1⟩ : ∃ y₀ ∈ σ.range, Odd (orderOf y₀) ∧ y₀ ≠ 1 := by
      by_contra hne
      push Not at hne
      exact hJ ((oUpperTwo_map_le_of_odd σ (K := ⊥) fun y hy hyo => by
        rw [Subgroup.mem_bot]
        exact hne y hy hyo).trans bot_le)
    have hKO : ∀ n ∈ (CFSG.pCore 2 I₀).map σ, n ∈ K → n = 1 := fun n hn hnK => by
      have h1 : n ∈ K ⊓ C := ⟨hnK, hσC hn⟩
      rwa [hKC, Subgroup.mem_bot] at h1
    refine ⟨hJK, y₀, hallK y₀ hy₀ hy₀o, pow_three_eq_one_of_mem_range_of_odd σ hb hy₀ hy₀o,
      oUpperTwo_map_le_of_odd σ fun y hy hyo => ?_⟩
    exact mem_zpowers_of_odd_of_symThree σ f hKO hy₀ hy₀o (hallK y₀ hy₀ hy₀o) hy₀1 hy hyo
      (hallK y hy hyo)
  ·
    exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨a, b, ha, hb3, hab⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNoSU.exists_cube_not_comm hb
        (not_nonempty_iff.mp hs3)
    have hH : IsPGroup 3
        (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀))) := by
      intro x
      exact ⟨1, Subtype.ext (by
        simpa using IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb x x.2)⟩
    have hmemH : ∀ z : I₀ ⧸ CFSG.pCore 2 I₀, z ^ 3 = 1 →
        z ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) :=
      fun z hz => Subgroup.subset_closure
        ⟨Subgroup.mem_top z, Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz)⟩
    obtain ⟨P₀⟩ : Nonempty (Sylow 3 I₀) := inferInstance
    set Pbar := P₀.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 I₀)) with hPbar
    have hHP : CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) ≤
        (Pbar : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) := by
      haveI := (normal_oUpperTwo_top :
        (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀))).Normal)
      have hsup := hH.to_sup_of_normal_left Pbar.isPGroup'
      have := Pbar.is_maximal' hsup le_sup_right
      rw [← this]
      exact le_sup_left
    have hlift : ∀ z : I₀ ⧸ CFSG.pCore 2 I₀, z ^ 3 = 1 →
        ∃ x ∈ (P₀ : Subgroup I₀), QuotientGroup.mk' (CFSG.pCore 2 I₀) x = z := by
      intro z hz
      have h1 := hHP (hmemH z hz)
      rw [hPbar, Sylow.coe_mapSurjective] at h1
      obtain ⟨x, hx, hxz⟩ := h1
      exact ⟨x, hx, hxz⟩
    obtain ⟨x, hx, hxa⟩ := hlift a ha
    obtain ⟨y, hy, hyb⟩ := hlift b hb3
    have hP3 : ∀ u ∈ (P₀ : Subgroup I₀).map σ, u ^ 3 = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      exact pow_three_eq_one_of_mem_range_of_odd σ hb ⟨u, rfl⟩
        (hodd_of u (by
          obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨u, hu⟩
          exact ⟨m, by simpa using congrArg Subtype.val hm⟩))
    have hPKC : (P₀ : Subgroup I₀).map σ ≤ K ⊔ C := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨u, hu⟩
      obtain ⟨k, hk, c, hc, he, -, -⟩ :=
        hdec (σ u) ⟨u, rfl⟩ (hodd_of u ⟨m, by simpa using congrArg Subtype.val hm⟩)
      rw [he]
      exact mul_mem_sup hk hc
    have hPJ : (P₀ : Subgroup I₀).map σ ≤
        (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ := by
      refine Subgroup.map_mono fun u hu => ?_
      obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨u, hu⟩
      have hum : u ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
      exact Subgroup.subset_closure ⟨Subgroup.mem_top u,
        Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hum)⟩
    have hcomm := commute_of_le_sup_centralizer hKC
      (fun Q hQK hQP h3 => hKcomm Q hQK (hQP.trans (sup_le_sup_right hPJ _)) h3) hrkC' hP3 hPKC
      (σ x) (Subgroup.mem_map_of_mem σ hx) (σ y) (Subgroup.mem_map_of_mem σ hy)
    set z := x * y * x⁻¹ * y⁻¹ with hz
    have hzP : z ∈ (P₀ : Subgroup I₀) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
        (Subgroup.inv_mem _ hy)
    have hzk : z ∈ σ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hz1 : z = 1 := by
      obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨z, hzP⟩
      have hm' : z ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h1 : orderOf z ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
      have h2 : orderOf z ∣ Nat.card σ.ker := by
        have := orderOf_dvd_natCard (⟨z, hzk⟩ : σ.ker)
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (3 ^ m) (Nat.card σ.ker) := Nat.Coprime.pow_left m hker
      have h3 : orderOf z ∣ 1 := by
        rw [← Nat.Coprime.gcd_eq_one hcop]
        exact Nat.dvd_gcd h1 h2
      rwa [Nat.dvd_one, orderOf_eq_one_iff] at h3
    apply hab
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    calc x * y = z * (y * x) := by rw [hz]; group
      _ = y * x := by rw [hz1, one_mul]

end SolvNone

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
