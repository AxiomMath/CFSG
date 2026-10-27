module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortLevi
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCore

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem twoCentralElt_short_ne_one : twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 ≠ 1 := by
  intro h
  have h' := congrFun (congrFun (congrArg (mat 3 K) h) (Sum.inl 1)) (Sum.inr 2)
  rw [mat_twoCentralElt_eq_add, map_one] at h'
  simp at h'

theorem le_centralizer_of_conj_eq_mul_three_short (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {g : G}
    (hg : g⁻¹ * t * g = t * ((e.symm (twoCentralElt 3 1 2 0 1) : L) : G))
    {φ' : StatedSp 3 K →* G} (hφ' : Function.Injective φ')
    (hφ'r : φ'.range = CFSG.conjugate L g)
    (hφ'z : φ' (twoCentralElt 3 1 2 0 1) = ((e.symm (twoCentralElt 3 1 2 0 1) : L) : G))
    {S : Subgroup G} (hSperf : ⁅S, S⁆ = S)
    (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSY : S ≤ centralizer (modelToG e (shortTorus K) : Set G))
    (hzS : ((e.symm (twoCentralElt 3 1 2 0 1) : L) : G) ∈ S)
    {B : Subgroup G} (hBperf : ⁅B, B⁆ = B) (hBL : B ≤ L)
    (hBz : B ≤ centralizer ({((e.symm (twoCentralElt 3 1 2 0 1) : L) : G)} : Set G))
    (hBY : B ≤ centralizer (modelToG e (shortTorus K) : Set G)) :
    S ≤ centralizer (B : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨κ, hκ⟩ := exists_units_ne_one (K := K) hK
  set x₁ : StatedSp 3 K := twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 with hx₁
  set z : G := ((e.symm x₁ : L) : G) with hz
  set Q := wRadical K (1 : Fin 3) 2 with hQ
  set M := a2Levi K 0 with hM
  set T := shortTorus K with hT
  set φ : StatedSp 3 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hΛ₀ : perfectCore (centralizer ({x₁} : Set (StatedSp 3 K))) = Q ⊔ M :=
    (perfectCore_centralizer_a2 (n := 0) hK).1
  have hΛ₀C : Q ⊔ M ≤ centralizer ({x₁} : Set (StatedSp 3 K)) := hΛ₀ ▸ perfectCore_le _
  have hzz : z * z = 1 := by
    rw [hz, ← L.coe_mul, ← map_mul, hx₁, twoCentralElt_mul, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, twoCentralElt_zero, map_one, L.coe_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have htz : z * t = t * z := mem_centralizer_iff.1 htC z (e.symm x₁).2
  have hw : z⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rw [hzinv, htz, ← hg, mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (EPilot.conjugate_le_centralizer_conj htC g hl)
  have hΛeq : perfectCore (L ⊓ centralizer ({z} : Set G)) =
      perfectCore (CFSG.conjugate L g ⊓ centralizer ({z} : Set G)) :=
    EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht (Or.inr hg) hw
  have hΛφ : (Q ⊔ M).map φ = perfectCore (L ⊓ centralizer ({z} : Set G)) := by
    rw [← hΛ₀, LinearPilot.map_perfectCore_centralizer_singleton hφ, hφr]
    rfl
  have hΛφ' : (Q ⊔ M).map φ' = perfectCore (CFSG.conjugate L g ⊓ centralizer ({z} : Set G)) := by
    rw [← hΛ₀, LinearPilot.map_perfectCore_centralizer_singleton hφ', hφ'r, hφ'z]
  have hΛ : (Q ⊔ M).map φ = (Q ⊔ M).map φ' := by rw [hΛφ, hΛφ', hΛeq]
  have hMbot : ∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hN2 =>
    eq_bot_of_normal_of_isPGroup_a2Levi (n := 0) hK N hN2
  have hXodd : ¬ 2 ∣ Nat.card (T.map φ) := by
    rw [Subgroup.card_map_of_injective hφ]
    exact not_two_dvd_card_shortTorus
  have hQp : IsPGroup 2 Q := isPGroup_wRadical one_ne_two_three
  have hMN : M ≤ normalizer (Q : Set (StatedSp 3 K)) :=
    spCoreLevi_le_normalizer_spCoreRadical (K := K) (n := 0) .a2
  have hQM : Disjoint Q M := disjoint_spCoreRadical_spCoreLevi (K := K) (n := 0) .a2
  obtain ⟨hQeq, ι, hspec, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ'
    hQp hQp hMbot hMbot hMN hMN hQM hQM hΛ shortTorus_le_a2Levi le_rfl hXodd
  set β : (Q ⊔ M : Subgroup (StatedSp 3 K)) ≃* (Q ⊔ M : Subgroup (StatedSp 3 K)) :=
    ((Q ⊔ M).equivMapOfInjective φ hφ).trans
      ((MulEquiv.subgroupCongr hΛ).trans ((Q ⊔ M).equivMapOfInjective φ' hφ').symm) with hβdef
  have hβφ : ∀ x : (Q ⊔ M : Subgroup (StatedSp 3 K)), φ' (β x) = φ x := by
    intro x
    have h1 : ((Q ⊔ M).equivMapOfInjective φ' hφ') (β x) =
        MulEquiv.subgroupCongr hΛ ((Q ⊔ M).equivMapOfInjective φ hφ x) := by
      rw [hβdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [coe_equivMapOfInjective_apply] at h2
    rw [h2]
    rfl
  have hβmem : ∀ x : (Q ⊔ M : Subgroup (StatedSp 3 K)),
      ((β x : StatedSp 3 K) ∈ Q ↔ (x : StatedSp 3 K) ∈ Q) := by
    intro x
    rw [← mem_map_iff_mem hφ' (K := Q), hβφ, ← hQeq, mem_map_iff_mem hφ]
  have hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_subgroupOf.2 ((hβmem y).2 (mem_subgroupOf.1 hy))
    · intro hx
      refine ⟨β.symm x, mem_subgroupOf.2 ?_, by simp⟩
      rw [← hβmem, MulEquiv.apply_symm_apply]
      exact mem_subgroupOf.1 hx
  have hιrel : ∀ m : M, ((ι m : M) : StatedSp 3 K)⁻¹ *
      (β (inclusion le_sup_right m) : StatedSp 3 K) ∈ Q := by
    intro m
    have h1 := hspec m
    have h3 : φ (m : StatedSp 3 K) = φ' (β (inclusion le_sup_right m)) :=
      (hβφ (inclusion le_sup_right m)).symm
    rw [hQeq, h3, ← map_inv φ', ← map_mul φ', mem_map_iff_mem hφ'] at h1
    exact h1
  obtain ⟨c, hcM, hc⟩ := exists_mem_a2Levi_conj_shortTorus hK β hβ ι hιrel
  rw [hQeq] at hq₀
  obtain ⟨q₀', hq₀'Q, rfl⟩ := hq₀
  set d : StatedSp 3 K := q₀' * c with hd
  have hdΛ : d ∈ Q ⊔ M := mul_mem (mem_sup_left hq₀'Q) (mem_sup_right hcM)
  have hdC : d ∈ centralizer ({x₁} : Set (StatedSp 3 K)) := hΛ₀C hdΛ
  set φ'' : StatedSp 3 K →* G := (MulAut.conj (φ' d)).toMonoidHom.comp φ' with hφ''def
  have hφ''apply : ∀ y, φ'' y = φ' (d * y * d⁻¹) := fun y => by
    simp [hφ''def, MulAut.conj_apply, map_mul, map_inv]
  have hφ'' : Function.Injective φ'' := (MulAut.conj (φ' d)).injective.comp hφ'
  have hφ''r : φ''.range = CFSG.conjugate L g := by
    rw [hφ''def, MonoidHom.range_comp, hφ'r]
    have hdL : φ' d ∈ CFSG.conjugate L g := hφ'r ▸ ⟨d, rfl⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hdL)
  have hφ''z : φ'' x₁ = z := by
    rw [hφ''apply, (mem_centralizer_singleton_iff.1 hdC : d * x₁ = x₁ * d), mul_inv_cancel_right,
      hφ'z]
  have hXle : T.map φ ≤ T.map φ'' := by
    intro x hx
    obtain ⟨_, ⟨_, ⟨_, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hXq hx
    refine ⟨c⁻¹ * (ι m : StatedSp 3 K) * c, hc m (mem_subgroupOf.1 hm), ?_⟩
    rw [hφ''apply]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype, hd]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hXeq : T.map φ = T.map φ'' := Subgroup.eq_of_le_of_card_ge hXle (by
    rw [Subgroup.card_map_of_injective hφ'', Subgroup.card_map_of_injective hφ])
  have hY : modelToG e T = T.map φ'' := by
    rw [UnitaryPilot.modelToG_def, Subgroup.map_map, ← hXeq]
  have hSL' : S ≤ CFSG.conjugate L g :=
    LinearPilot.perfect_le_conjugate_of_le_centralizer hset hOut htC ht g hSperf hSt
  have hcomm : ∀ y : StatedSp 3 K, φ'' y ∈ centralizer (modelToG e T : Set G) →
      y ∈ centralizer (T : Set (StatedSp 3 K)) := by
    intro y hy
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : φ'' w ∈ modelToG e T := by
      rw [hY]
      exact ⟨w, hw, rfl⟩
    have h1 := mem_centralizer_iff.1 hy (φ'' w) hw'
    apply hφ''
    rw [map_mul, map_mul]
    exact h1
  have hSsup : S ≤ (complSp K (0 : Fin 3)).map φ'' ⊔ (longRootSp2 K 3 (0 : Fin 3)).map φ'' := by
    rw [← Subgroup.map_sup, sup_comm]
    intro s hs
    have hsr : s ∈ φ''.range := hφ''r ▸ hSL' hs
    obtain ⟨y, rfl⟩ := hsr
    exact ⟨y, centralizer_shortTorus_le hκ (hcomm y (hSY hs)), rfl⟩
  have hAB : (complSp K (0 : Fin 3)).map φ'' ≤
      centralizer ((longRootSp2 K 3 (0 : Fin 3)).map φ'' : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (commute_of_mem_longRootSp2_of_mem_complSp hb ha).eq]
  have hzA : z ∈ (complSp K (0 : Fin 3)).map φ'' :=
    ⟨x₁, twoCentralElt_mem_complSp_zero, hφ''z⟩
  have hz1 : z ≠ 1 := by
    intro h
    apply twoCentralElt_short_ne_one (K := K)
    apply e.symm.injective
    apply Subtype.ext
    rw [map_one]
    exact h
  have hSA : S ≤ (complSp K (0 : Fin 3)).map φ'' :=
    LinearPilot.le_of_le_sup_of_commute hAB hSsup hSsimple hzS hzA hz1
  have hΛ'' : (Q ⊔ M).map φ'' = (Q ⊔ M).map φ' := by
    rw [hφ''def, ← Subgroup.map_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ⟨d, hdΛ, rfl⟩)
  have hBΛ : B ≤ (Q ⊔ M).map φ'' := by
    have h1 : B ≤ perfectCore (L ⊓ centralizer ({z} : Set G)) :=
      le_perfectCore_of_perfect (le_inf hBL hBz) hBperf
    rw [← hΛφ, hΛ, ← hΛ''] at h1
    exact h1
  set P := B.comap φ'' with hPdef
  have hBr : B ≤ φ''.range := hBΛ.trans (map_le_range _ _)
  have hPmap : P.map φ'' = B := Subgroup.map_comap_eq_self hBr
  have hPperf : ⁅P, P⁆ = P := by
    apply Subgroup.map_injective hφ''
    rw [Subgroup.map_commutator, hPmap, hBperf]
  have hPΛ : P ≤ centralizer ({x₁} : Set (StatedSp 3 K)) := fun y hy =>
    hΛ₀C ((mem_map_iff_mem hφ'').1 (hBΛ hy))
  have hPT : P ≤ centralizer (T : Set (StatedSp 3 K)) := fun y hy => hcomm y (hBY hy)
  have hPM := le_longRootSp2_of_perfect_of_le_centralizer_shortTorus hκ hPperf hPΛ hPT
  have hBM : B ≤ (longRootSp2 K 3 (0 : Fin 3)).map φ'' := by
    rw [← hPmap]
    exact Subgroup.map_mono hPM
  intro s hs
  rw [mem_centralizer_iff]
  intro b hb
  exact (mem_centralizer_iff.1 (hAB (hSA hs)) b (hBM hb))

end CFSG.SeitzReduction.SymplecticPilot
