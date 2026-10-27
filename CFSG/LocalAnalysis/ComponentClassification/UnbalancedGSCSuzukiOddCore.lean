module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace SuzukiOddCore

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI
open scoped commutatorElement

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem centralizer_suzukiSElt_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) {v : K} (hv : v ≠ 0) :
    centralizer ({suzukiSElt a K 0 v} : Set (suzukiGroup a K)) = suzukiU a K := by
  have htU := suzukiSElt_mem_suzukiU a K 0 v
  have htB := suzukiU_le_suzukiB a K htU
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_singleton_iff] at hg
    have hgB : g ∈ suzukiB a K := by
      by_contra hgB
      have hodd := (SuzukiModel.fusionStronglyEmbedded_suzukiB hK).2.2 g hgB
      have htmem : suzukiSElt a K 0 v ∈
          suzukiB a K ⊓ (suzukiB a K).map (MulAut.conj g⁻¹).toMonoidHom := by
        refine ⟨htB, suzukiSElt a K 0 v, htB, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [mul_assoc, ← hg, inv_mul_cancel_left]
      have h2 : 2 ∣ Nat.card (suzukiB a K ⊓ (suzukiB a K).map (MulAut.conj g⁻¹).toMonoidHom :
          Subgroup (suzukiGroup a K)) := by
        rw [← SuzukiModel.orderOf_suzukiSElt_zero hK hv, ← Subgroup.orderOf_mk _ htmem]
        exact orderOf_dvd_natCard _
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    obtain ⟨u, w, l, rfl⟩ := (mem_suzukiB_iff hK).1 hgB
    have hSt : suzukiSElt a K u w * suzukiSElt a K 0 v = suzukiSElt a K 0 v * suzukiSElt a K u w :=
      (suzukiSElt_zero_commute hK v u w).symm
    have hcomm : suzukiDElt a K l * suzukiSElt a K 0 v =
        suzukiSElt a K 0 v * suzukiDElt a K l := by
      have h1 : suzukiSElt a K u w * (suzukiDElt a K l * suzukiSElt a K 0 v) =
          suzukiSElt a K u w * (suzukiSElt a K 0 v * suzukiDElt a K l) := by
        calc suzukiSElt a K u w * (suzukiDElt a K l * suzukiSElt a K 0 v) =
            (suzukiSElt a K u w * suzukiDElt a K l) * suzukiSElt a K 0 v := by group
          _ = suzukiSElt a K 0 v * (suzukiSElt a K u w * suzukiDElt a K l) := hg
          _ = (suzukiSElt a K 0 v * suzukiSElt a K u w) * suzukiDElt a K l := by group
          _ = (suzukiSElt a K u w * suzukiSElt a K 0 v) * suzukiDElt a K l := by rw [hSt]
          _ = suzukiSElt a K u w * (suzukiSElt a K 0 v * suzukiDElt a K l) := by group
      exact mul_left_cancel h1
    have h2 : (suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 v * suzukiDElt a K l =
        suzukiSElt a K 0 v := by
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    rw [suzukiDElt_conj hK, suzukiSElt_inj] at h2
    have hl : (l : K) ^ (2 ^ (a + 1) + 1) = 1 ^ (2 ^ (a + 1) + 1) := by
      rw [one_pow]
      exact mul_right_cancel₀ hv (h2.2.trans (one_mul v).symm)
    have hl1 : l = 1 := Units.ext (pow_two_pow_succ_add_one_injective hK hl)
    rw [hl1, suzukiDElt_one, mul_one]
    exact suzukiSElt_mem_suzukiU a K u w
  · intro g hg
    rw [mem_centralizer_singleton_iff]
    obtain ⟨u, w, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    exact (suzukiSElt_zero_commute hK v u w).symm

theorem suzuki_involution_centralizer_sylow (hK : Nat.card K = 2 ^ (2 * a + 1))
    (t : suzukiGroup a K) (ht : orderOf t = 2) :
    ∃ S : Sylow 2 (suzukiGroup a K), (S : Subgroup (suzukiGroup a K)) = centralizer {t} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPU⟩ := SuzukiModel.exists_sylow_eq_suzukiU hK
  have htp : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S₀, hS₀⟩ := htp.exists_le_sylow
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P S₀
  have htS := hS₀ (mem_zpowers t)
  rw [CFSG.LocalAnalysis.ComponentInitial.coe_smul_sylow', hPU] at htS
  obtain ⟨u, huU, hut⟩ := htS
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hut
  have huord : orderOf u = 2 := by
    rw [← ht, ← hut]
    exact (orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective u).symm
  obtain ⟨v, hv, rfl⟩ :=
    (SuzukiModel.mem_suzukiB_and_orderOf_eq_two_iff hK).1 ⟨suzukiU_le_suzukiB a K huU, huord⟩
  refine ⟨x • P, ?_⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.coe_smul_sylow', hPU,
    ← centralizer_suzukiSElt_zero hK hv]
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hut,
    MulAut.conj_symm_apply]
  constructor
  · intro h
    calc y * (x * suzukiSElt a K 0 v * x⁻¹) =
        x * ((x⁻¹ * y * x) * suzukiSElt a K 0 v) * x⁻¹ := by group
      _ = x * (suzukiSElt a K 0 v * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
      _ = x * suzukiSElt a K 0 v * x⁻¹ * y := by group
  · intro h
    calc x⁻¹ * y * x * suzukiSElt a K 0 v =
        x⁻¹ * (y * (x * suzukiSElt a K 0 v * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * suzukiSElt a K 0 v * x⁻¹) * y) * x := by rw [h]
      _ = suzukiSElt a K 0 v * (x⁻¹ * y * x) := by group

theorem conjNormal_of_mem {X : Type*} [Group X] {F : Subgroup X} [F.Normal] {f : X}
    (hf : f ∈ F) :
    MulAut.conjNormal f = MulAut.conj (⟨f, hf⟩ : F) := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.conjNormal_apply, MulAut.conj_apply]
  rfl

end SuzukiOddCore

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI SuzukiOddCore
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner congr_conj)
open scoped commutatorElement

theorem catalog_suzuki_almost_simple_odd_core_vanishing {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (generalizedFitting X))
    (hnab : ∃ x y : generalizedFitting X, x * y ≠ y * x) {f : ℕ}
    (hSz : SuzukiModel (generalizedFitting X) 2 f) (z : X) (hz : orderOf z = 2) :
    z ∈ generalizedFitting X ∧
    (∃ S : Sylow 2 (generalizedFitting X), (S : Subgroup (generalizedFitting X)) =
      (centralizer ({z} : Set X)).subgroupOf (generalizedFitting X)) ∧
    oddCore (centralizer ({z} : Set X)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := generalizedFitting X with hFdef
  have hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  let ρ : X →* MulAut F := MulAut.conjNormal
  have hρ : ∀ (g : X) (x : F), ((ρ g x : F) : X) = g * x * g⁻¹ := fun g x =>
    MulAut.conjNormal_apply g x
  have hZF : center F = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center F) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have hy : y ∈ center F := h ▸ mem_top y
      exact hxy (mem_center_iff.mp hy x)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hgC : g ∈ centralizer (F : Set X) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut F => ((φ ⟨x, hx⟩ : F) : X)) hg
      simp only [hρ, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    have hgF : g ∈ F := centralizer_generalizedFitting_le X hgC
    have hgZ : (⟨g, hgF⟩ : F) ∈ center F :=
      mem_center_iff.mpr fun x => Subtype.ext (mem_centralizer_iff.mp hgC x x.2)
    rw [hZF, mem_bot] at hgZ
    rw [mem_bot]
    exact congrArg Subtype.val hgZ
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hSz
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have hρF : ∀ (x : X) (hx : x ∈ F), ρ x = MulAut.conj (⟨x, hx⟩ : F) := fun x hx =>
    conjNormal_of_mem hx
  have hcongr : ∀ x : X, MulAut.congr e.symm (MulAut.congr e (ρ x)) = ρ x := fun x => by
    refine MulEquiv.ext fun y => ?_
    simp [MulAut.congr_apply]
  have hzF : z ∈ F := by
    set β := MulAut.congr e (ρ z) with hβ
    have hβ2 : β ^ 2 = 1 := by
      rw [hβ, ← map_pow, ← map_pow, ← hz, pow_orderOf_eq_one, map_one, map_one]
    have hp : IsPGroup 2 (zpowers β) := by
      rintro ⟨y, k, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      change (β ^ k) ^ 2 ^ 1 = 1
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hβ2, one_zpow]
    obtain ⟨g, hg⟩ :=
      (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
        ha hK').2 _ hp (mem_zpowers β)
    have h1 : ρ z = ρ ((e.symm g : F) : X) := by
      rw [hρF _ (e.symm g).2, ← hcongr z, ← hβ, ← hg, congr_conj]
    have := hρinj h1
    rw [this]
    exact (e.symm g).2
  refine ⟨hzF, ?_⟩
  set z' : F := ⟨z, hzF⟩ with hz'
  have hz'ord : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk, hz]
  have hzt : orderOf (e z') = 2 := by rw [MulEquiv.orderOf_eq, hz'ord]
  obtain ⟨S, hS⟩ := suzuki_involution_centralizer_sylow hK' (e z') hzt
  have hCF : (centralizer ({z} : Set X)).subgroupOf F =
      (centralizer ({e z'} : Set (suzukiGroup a K))).map e.symm.toMonoidHom := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_map_equiv, MulEquiv.symm_symm,
      mem_centralizer_singleton_iff, ← map_mul, ← map_mul, e.injective.eq_iff]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  let S' : Sylow 2 F := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hS' : (S' : Subgroup F) = (centralizer ({z} : Set X)).subgroupOf F := by
    change (S : Subgroup (suzukiGroup a K)).map e.symm.toMonoidHom = _
    rw [hS, hCF]
  refine ⟨⟨S', hS'⟩, ?_⟩
  set Cz := centralizer ({z} : Set X) with hCz
  have hQp : IsPGroup 2 (Cz.subgroupOf F) := hS' ▸ S'.isPGroup'
  have hodd := CFSG.ComponentClassification.SmallLocal.odd_card_oddCore (H := Cz)
  have htriv : ∀ d : Cz, d ∈ oddCore Cz → (d : X) ∈ F → d = 1 := by
    intro d hd hdF
    obtain ⟨k, hk⟩ := hQp ⟨⟨d, hdF⟩, mem_subgroupOf.mpr d.2⟩
    have h1 : (d : X) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : Cz.subgroupOf F => ((y : F) : X)) hk
      simpa using this
    have h2 : orderOf d ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf d ∣ Nat.card (oddCore Cz) := Subgroup.orderOf_dvd_natCard _ hd
    have h4 : Nat.Coprime (2 ^ k) (Nat.card (oddCore Cz)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h2 h3)
  rw [eq_bot_iff]
  intro d hd
  rw [mem_bot]
  have hdcomm : ∀ q : X, q ∈ Cz → q ∈ F → (d : X) * q = q * d := by
    intro q hqC hqF
    set q' : Cz := ⟨q, hqC⟩
    have hc1 : ⁅d, q'⁆ ∈ oddCore Cz := by
      have h0 : ⁅d, q'⁆ = d * (q' * d⁻¹ * q'⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h0]
      exact mul_mem hd ((inferInstance : (oddCore Cz).Normal).conj_mem _ (inv_mem hd) q')
    have hc2 : ((⁅d, q'⁆ : Cz) : X) ∈ F := by
      rw [commutatorElement_def]
      simp only [coe_mul, coe_inv]
      exact mul_mem (hFn.conj_mem q hqF d) (inv_mem hqF)
    have h3 := htriv _ hc1 hc2
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact congrArg Subtype.val h3
  set β := MulAut.congr e (ρ d) with hβ
  have hβS : ∀ y ∈ (S : Subgroup (suzukiGroup a K)), β y = y := by
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : ((x : F) : X) ∈ Cz := by
      have : x ∈ (S' : Subgroup F) := ⟨e x, hy, e.symm_apply_apply x⟩
      rw [hS', mem_subgroupOf] at this
      exact this
    change e ((ρ d) (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [hρ, hdcomm _ hx x.2, mul_inv_cancel_right]
  set V := (CFSG.omega₁ (G := (S : Subgroup (suzukiGroup a K))) (p := 2)).map
    (S : Subgroup (suzukiGroup a K)).subtype with hV
  have hVS : V ≤ S := map_subtype_le _
  obtain ⟨b, hbS, hb⟩ := suzuki_rank_one_Sylow_layer_kernel ha hK' S V hV β
    (by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        change β y' ∈ (S : Subgroup (suzukiGroup a K))
        rw [hβS y' hy']
        exact hy'
      · intro hy
        exact ⟨y, hy, hβS y hy⟩)
    (fun v hv => hβS v (hVS hv))
    (fun x hx => by
      rw [hβS x hx, inv_mul_cancel]
      exact one_mem V)
  have h1 : ρ d = ρ ((e.symm b : F) : X) := by
    rw [hρF _ (e.symm b).2, ← hcongr d, ← hβ, hb, congr_conj]
  have hdb := hρinj h1
  exact htriv d hd (hdb ▸ (e.symm b).2)

end CFSG.ComponentClassification.UnbalancedGS
