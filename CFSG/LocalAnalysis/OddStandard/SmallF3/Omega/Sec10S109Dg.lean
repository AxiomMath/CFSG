module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109De
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Df
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZNorm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_zpowers_val {H : Subgroup G} {c w : ↥H} (hw : w ∈ zpowers c) :
    (w : G) ∈ zpowers (c : G) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨i, by simp⟩

theorem sec10D_decomp [Finite G] {T : Subgroup G} {t z : G}
    (hT : IsSylow2Of T (centralizer ({z} : Set G))) (htT : t ∈ T) (hzT : z ∈ T)
    (hsc : IsStrClosedModZ t z T) (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t)
    (ht1 : t ≠ 1) (hz1 : z ≠ 1) (hne : t ≠ z) :
    ∀ h ∈ centralizer ({z} : Set G), ∃ o ∈ oddCoreIn (centralizer ({z} : Set G)),
      ∃ c ∈ hatCent t z, h = o * c := by
  intro h hh
  have hzH : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htH : t ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr htz
  have hiso := sec10D_isolated_mod hT htT hzT hsc ht2 hz2 htz
  have hc1 : (⟨z, hzH⟩ : ↥(centralizer ({z} : Set G))) ≠ 1 := fun h' =>
    hz1 (congrArg Subtype.val h')
  have hτ1 : (⟨t, htH⟩ : ↥(centralizer ({z} : Set G))) ∉
      zpowers (⟨z, hzH⟩ : ↥(centralizer ({z} : Set G))) := by
    intro hmem
    rcases sec10D_eq_one_or_of_mem_zpowers hz2 (mem_zpowers_val hmem) with h1 | h1
    · exact ht1 h1
    · exact hne h1
  obtain ⟨y, hy, k, hk, hxe⟩ := sec10D_zStar_abs (X := ↥(centralizer ({z} : Set G)))
    (c := ⟨z, hzH⟩) (τ := ⟨t, htH⟩) hc1 (Subtype.ext hz2)
    (fun x => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)) (Subtype.ext ht2) hτ1
    (fun x hx => by
      rcases hiso (x : G) x.2 (mem_zpowers_val hx) with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1))
    ⟨h, hh⟩
  refine ⟨(y : G), ⟨y, hy, rfl⟩, (k : G), ?_, congrArg Subtype.val hxe⟩
  refine sec10D_mem_hatCent k.2 ?_
  rcases hk with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

theorem sec10D_K0_contains [Finite G] (hK0 : Asc82Lemma10K0) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    K1 ≤ secK0 t z ∧ K2 ≤ secK0 t z ∧ oddCoreIn (centralizer ({t} : Set G)) ≤ secK0 t z := by
  have h := (hK0 G t L S z K1 K2 hctx).1
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    exact le_sup_of_le_left le_sup_right
  · rw [h]
    exact le_sup_right
  · rw [h]
    exact le_sup_of_le_left le_sup_left

theorem sec10D_oddC_le_oddK0 [Finite G] (hK0 : Asc82Lemma10K0) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ oddCoreIn (secK0 t z) :=
  CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes
    (sec10D_K0_contains hK0 hctx).2.2
    ((sec10D_K0_le t z).trans
      (inf_le_left.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)))
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn _)

theorem sec10D_K0_normalizes_K1O [Finite G] (hK0 : Asc82Lemma10K0) (hP5 : Asc82FactPockets5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ k ∈ secK0 t z, ∀ x ∈ K1 ⊔ oddCoreIn (secK0 t z),
      k * x * k⁻¹ ∈ K1 ⊔ oddCoreIn (secK0 t z) := by
  obtain ⟨-, hK2, -⟩ := sec10D_K0_contains hK0 hctx
  have hOle := sec10D_oddC_le_oddK0 hK0 hctx
  have hcomm : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  have hnA : K1 ⊔ oddCoreIn (secK0 t z) ≤
      Subgroup.normalizer (K1 ⊔ oddCoreIn (secK0 t z) : Subgroup G) := Subgroup.le_normalizer
  have hK2n1 : K2 ≤ Subgroup.normalizer K1 := by
    refine Subgroup.le_normalizer_iff.mpr (fun k hk x hx => ?_)
    have h : k * x = x * k := (hcomm x hx k hk).symm
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hK2nO : K2 ≤ Subgroup.normalizer (oddCoreIn (secK0 t z)) :=
    Subgroup.le_normalizer_iff.mpr (fun k hk n hn =>
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := secK0 t z) (hK2 hk) hn)
  have hK0le : secK0 t z ≤
      Subgroup.normalizer (K1 ⊔ oddCoreIn (secK0 t z) : Subgroup G) := by
    refine (hK0 G t L S z K1 K2 hctx).1.trans_le (sup_le (sup_le ?_ ?_) ?_)
    · exact (hOle.trans le_sup_right).trans hnA
    · exact le_sup_left.trans hnA
    · exact (le_inf hK2n1 hK2nO).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  exact Subgroup.le_normalizer_iff.mp hK0le

theorem sec10D_hatCent_normalizes_K0 [Finite G] (hK0 : Asc82Lemma10K0) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t) (ht1 : t ≠ 1) (hne : t ≠ z)
    {c : G} (hc : c ∈ hatCent t z) : ∀ x ∈ secK0 t z, c * x * c⁻¹ ∈ secK0 t z := by
  rw [(hK0 G t L S z K1 K2 hctx).2]
  exact sec10D_hatCent_normalizes ht2 hz2 htz ht1 hne hc

end CFSG.OddStandard.SmallF3.Omega
