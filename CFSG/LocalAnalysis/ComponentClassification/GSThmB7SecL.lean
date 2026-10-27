module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec59
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma56
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Setup
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

section Cover

theorem center_oddBar_eq_bot (hCov : CFSp4CoverInv) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {M J₀ : Subgroup X} (hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M))
    (hLie : Blueprint.LieModel ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M))
      .PSp 2 p f)
    {a : X} (ha : a * a = 1) (haM : a ∈ normalizer (M : Set X))
    (hJ0 : J₀ ≤ M ⊓ centralizer ({a} : Set X))
    (hJ0pc : IsPComponent 2 (J₀.subgroupOf (M ⊓ centralizer ({a} : Set X))))
    (hZ : center (↥J₀ ⧸ pPrimeCore 2 ↥J₀) = ⊥) :
    center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZM
  set N := normalizer (M : Set X) with hN
  have hMN : M ≤ N := le_normalizer
  have hON : (oddCoreIn M).subgroupOf N |>.Normal := by
    refine (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hMN)).mpr ?_
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M (pPrimeCore 2 M)
  set O := (oddCoreIn M).subgroupOf N with hO
  set π := QuotientGroup.mk' O with hπ
  have hkerπ : ¬ 2 ∣ Nat.card π.ker := by
    have hle : oddCoreIn M ≤ N := (map_subtype_le _).trans hMN
    rw [hπ, QuotientGroup.ker_mk', hO, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      oddCoreIn, card_map_of_injective M.subtype_injective]
    intro h2
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  set Yh := (M.subgroupOf N).map π with hYh
  let α : ↥M →* ↥Yh := (π.comp (inclusion hMN)).codRestrict Yh fun m =>
    mem_map_of_mem π (show inclusion hMN m ∈ M.subgroupOf N from m.2)
  have hα : Function.Surjective α := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hkerα : α.ker = pPrimeCore 2 ↥M := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro hm
      have h1 : π (inclusion hMN m) = 1 := congrArg Subtype.val hm
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf] at h1
      obtain ⟨m', hm', hmm'⟩ := mem_map.mp h1
      rwa [show m' = m from Subtype.ext hmm'] at hm'
    · intro hm
      apply Subtype.ext
      change π (inclusion hMN m) = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf]
      exact mem_map_of_mem _ hm
  let e : ↥Yh ≃* ↥M ⧸ pPrimeCore 2 ↥M := equivOfKerEq α (QuotientGroup.mk' _) hα
    (QuotientGroup.mk'_surjective _) (by rw [hkerα, QuotientGroup.ker_mk'])
  have hqY : IsQuasisimple ↥Yh := (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  have hZY : center ↥Yh ≠ ⊥ := by
    intro h1
    apply hZM
    rw [← Subgroup.card_eq_one] at h1 ⊢
    rw [← h1]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  have hLieY : Blueprint.LieModel (↥Yh ⧸ center ↥Yh) .PSp 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (GorensteinWalter.FieldTransport.quotientCenterMulEquiv e).symm hLie
  set t := π ⟨a, haM⟩ with ht_def
  have ht : t * t = 1 := by
    rw [ht_def, ← map_mul, show (⟨a, haM⟩ : ↥N) * ⟨a, haM⟩ = 1 from Subtype.ext ha, map_one]
  have hYn : Yh.Normal := (normal_in_normalizer (H := M)).map π (QuotientGroup.mk'_surjective _)
  have htN : t ∈ normalizer (Yh : Set (↥N ⧸ O)) := by
    rw [normalizer_eq_top_iff.mpr hYn]
    exact mem_top t
  have hJ0N : J₀ ≤ N := (hJ0.trans inf_le_left).trans hMN
  have hE2 : IsPGroup 2 (zpowers (⟨a, haM⟩ : ↥N)) := by
    intro w
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp w.2
    apply Subtype.ext
    have ha2 : (⟨a, haM⟩ : ↥N) ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext ha
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, one_zpow]
  have hMn : (M.subgroupOf N).Normal := normal_in_normalizer
  have hEY : zpowers (⟨a, haM⟩ : ↥N) ≤ normalizer ((M.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [normalizer_eq_top_iff.mpr hMn]
    exact le_top
  have hcent : Yh ⊓ centralizer ({t} : Set (↥N ⧸ O)) =
      ((M ⊓ centralizer ({a} : Set X)).subgroupOf N).map π := by
    have h1 : ((M.subgroupOf N) ⊓ centralizer ({(⟨a, haM⟩ : ↥N)} : Set ↥N)).map π =
        Yh ⊓ centralizer ({t} : Set (↥N ⧸ O)) := by
      have h2 := OddQuot.map_inf_centralizer π hE2 hEY
        (OddQuot.not_two_dvd_card_ker_domRestrict π hkerπ _)
      simp only [MonoidHom.map_zpowers, centralizer_zpowers_eq] at h2
      exact h2
    rw [← h1]
    congr 1
    ext w
    simp only [mem_inf, mem_subgroupOf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => ⟨fun h2 => congrArg Subtype.val h2,
      fun h2 => Subtype.ext h2⟩
  set M' := (J₀.subgroupOf N).map π with hM'
  have hJsub : J₀.subgroupOf N ≤ (M ⊓ centralizer ({a} : Set X)).subgroupOf N := fun w hw =>
    mem_subgroupOf.mpr (hJ0 (mem_subgroupOf.mp hw))
  have hJpcN : IsPComponent 2 ((J₀.subgroupOf N).subgroupOf
      ((M ⊓ centralizer ({a} : Set X)).subgroupOf N)) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (inf_le_left.trans hMN) 2
      Nat.prime_two).mpr hJ0pc
  have hM'pc := OddQuot.isPComponent_map π hkerπ hJsub hJpcN
  rw [← hcent] at hM'pc
  have hM'le : M' ≤ Yh ⊓ centralizer ({t} : Set (↥N ⧸ O)) := by
    rw [hcent]
    exact map_mono hJsub
  have hZM' : center (↥M' ⧸ pPrimeCore 2 ↥M') = ⊥ := by
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hkerπ (J₀.subgroupOf N)
    let e2 := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJ0N)
    let e3 := e1.symm.trans e2
    rw [← Subgroup.card_eq_one] at hZ ⊢
    rw [Nat.card_congr (Subgroup.centerCongr e3).toEquiv, hZ]
  exact hCov _ p f hp hp2 hf Yh hqY hZY hLieY t ht htN M' hM'le hM'pc hZM'

end Cover

section Main

theorem five_le_of_lieModel_psl_two {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Y .PSL 2 p f) : 5 ≤ p ^ f := by
  obtain ⟨⟨hp, hf, -, -, h23⟩, -⟩ := GSLit.statedClassicalModel_of_lieModel_psl_two h
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ p ^ f := (hp.two_le.lt_of_ne (Ne.symm hp2)).trans_le (Nat.le_self_pow (by omega) p)
  have hne : p ^ f ≠ 3 := fun h => h23 (by rw [h])
  obtain ⟨k, hk⟩ := hodd
  omega

theorem J0_le_Lay (h : Hyp52 X) (y : X) : J0 h y ≤ Lay h y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer (B0 h y : Set X) with hY
  have haY : h.a ∈ Y := mem_centralizer_iff.mpr fun _ hb =>
    h.comm_a (((inf_le_left : B0 h y ≤ h.B).trans h.B_le_S) hb)
  have hza : IsPGroup 2 (zpowers h.a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  have hA : IsPGroup 2 ((zpowers h.a).subgroupOf Y) := hza.comap_subtype
  have hcA : centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) =
      (centralizer ({h.a} : Set X) ⊓ Y).subgroupOf Y := by
    rw [B5a.centralizer_subgroupOf (zpowers_le.mpr haY), centralizer_zpowers_eq,
      inf_subgroupOf_right]
  have hJ0Y : J0 h y ≤ Y := (GSLit.fixedLayer_le_inf _ _).trans inf_le_right
  have hJ0a : J0 h y ≤ centralizer ({h.a} : Set X) :=
    ((GSLit.fixedLayer_le_inf _ _).trans inf_le_left).trans h.J_le
  have hJA : (J0 h y).subgroupOf Y ≤
      centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [hcA]
    intro j hj
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hJ0a (mem_subgroupOf.mp hj),
      hJ0Y (mem_subgroupOf.mp hj)⟩)
  have hJc : IsPComponent 2 (((J0 h y).subgroupOf Y).subgroupOf
      (centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y))) := by
    rw [hcA, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact Hyp52.isPComponent_secJ0 (h := h) (y := y)
  have hle : (J0 h y).subgroupOf Y ≤ pLayer ↥Y 2 := by
    have h1 : ((J0 h y).subgroupOf Y).subgroupOf
        (centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) ≤
        pLayer ↥(centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) 2 :=
      le_sSup hJc
    have h2 := map_mono (f := (centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) :
      Set ↥Y)).subtype) h1
    rw [map_subgroupOf_eq_of_le hJA] at h2
    exact h2.trans (ClassicalInvolution.l2PrimeBalance ↥Y _ hA)
  intro j hj
  exact ⟨⟨j, hJ0Y hj⟩, hle (mem_subgroupOf.mpr hj), rfl⟩

end Main

end Seven

end CFSG.ComponentClassification.GSThmB
