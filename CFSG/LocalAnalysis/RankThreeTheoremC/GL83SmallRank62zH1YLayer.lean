module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1YComp
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbedding CFSG.LocalCores
open scoped commutatorElement

variable {B : Type} [Group B] [Finite B] {f : ℕ} {Q : Subgroup B}

theorem k631a_layer_acts {y : B} (hy : y ∈ layer B) (K : ComponentIndex B) :
    ∃ j ∈ K.1, ∀ k ∈ K.1, y * k * y⁻¹ = j * k * j⁻¹ := by
  obtain ⟨x, rfl⟩ := exists_layerMul_eq hy
  refine ⟨(x K : B), (x K).2, fun k hk => ?_⟩
  have hc := commute_layerMul_update x K hk
  rw [layerMul_eq_mul_update x K]
  set u := layerMul B (Function.update x K 1) with hu
  have h1 : u * k * u⁻¹ = k := by
    rw [← hc.eq]
    group
  calc ((x K : B) * u) * k * ((x K : B) * u)⁻¹ = (x K : B) * (u * k * u⁻¹) * (x K : B)⁻¹ := by
        group
    _ = (x K : B) * k * (x K : B)⁻¹ := by rw [h1]

theorem k631a_layer_eq_one (hZ : ∀ K : ComponentIndex B, Subgroup.center ↥K.1 = ⊥) {y : B}
    (hy : y ∈ layer B) (hc : ∀ K : ComponentIndex B, ∀ k ∈ K.1, y * k = k * y) : y = 1 := by
  obtain ⟨x, rfl⟩ := exists_layerMul_eq hy
  have hx : x = 1 := by
    funext K
    have hcK : x K ∈ Subgroup.center ↥K.1 := by
      rw [Subgroup.mem_center_iff]
      intro k
      have h1 : Commute (k : B) (layerMul B x) := (hc K k k.2).symm
      have h2 := (commute_layerMul_iff x K k.2).mp h1
      exact Subtype.ext h2.eq
    rw [hZ K, Subgroup.mem_bot] at hcK
    exact hcK
  rw [hx, map_one]

theorem k631a_Q_le_fstar (hInn : KFactInnerAction) (h : k631aBHyp f Q) :
    Q ≤ generalizedFitting B := by
  have := Fact.mk h.prime
  have hF : fittingSubgroup B ≤ Q := by
    rw [CFSG.Fitting_eq_pcore B f h.core]
    have := (CFSG.pCore_isPGroup (p := f) (G := B)).le_sylow_of_normal
      (h.pgroup.toSylow h.sylow)
    simpa using this
  intro q hq
  have hcomp : ∀ K : ComponentIndex B, ∃ g ∈ Q ⊓ K.1, ∀ k ∈ K.1, q * k * q⁻¹ = g * k * g⁻¹ :=
    fun K => k631a_inner hInn h K.2 hq
  choose g hgmem hg using hcomp
  let xs : ∀ K : ComponentIndex B, K.1 := fun K => ⟨g K, (hgmem K).2⟩
  have hεQ : layerMul B xs ∈ Q := layerMul_mem xs fun K => (hgmem K).1
  have hεL : layerMul B xs ∈ layer B := by
    rw [← layerMul_range]
    exact ⟨xs, rfl⟩
  have hz : ∀ K : ComponentIndex B, ∀ k ∈ K.1,
      (q * (layerMul B xs)⁻¹) * k * (q * (layerMul B xs)⁻¹)⁻¹ = k := by
    intro K k hk
    have hk' : (g K)⁻¹ * k * g K ∈ K.1 :=
      K.1.mul_mem (K.1.mul_mem (K.1.inv_mem (hgmem K).2) hk) (hgmem K).2
    have hu := commute_layerMul_update xs K hk'
    have he : layerMul B xs = g K * layerMul B (Function.update xs K 1) :=
      layerMul_eq_mul_update xs K
    set u := layerMul B (Function.update xs K 1) with hu_def
    have h1 : (g K * u)⁻¹ * k * (g K * u) = (g K)⁻¹ * k * g K := by
      calc (g K * u)⁻¹ * k * (g K * u) = u⁻¹ * ((g K)⁻¹ * k * g K) * u := by group
        _ = u⁻¹ * (u * ((g K)⁻¹ * k * g K)) := by rw [mul_assoc u⁻¹, ← hu.eq, ← mul_assoc]
        _ = (g K)⁻¹ * k * g K := by group
    rw [he]
    calc (q * (g K * u)⁻¹) * k * (q * (g K * u)⁻¹)⁻¹
        = q * ((g K * u)⁻¹ * k * (g K * u)) * q⁻¹ := by group
      _ = q * ((g K)⁻¹ * k * g K) * q⁻¹ := by rw [h1]
      _ = g K * ((g K)⁻¹ * k * g K) * (g K)⁻¹ := hg K _ hk'
      _ = k := by group
  have htQ : q * (layerMul B xs)⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem hεQ)
  have hle : generalizedFitting B ≤ centralizer ({q * (layerMul B xs)⁻¹} : Set B) := by
    refine sup_le (fun a ha => ?_) (sSup_le fun K hK => fun k hk => ?_)
    · rw [mem_centralizer_singleton_iff]
      have := h.comm.is_comm.comm (⟨q * (layerMul B xs)⁻¹, htQ⟩ : ↥Q) ⟨a, hF ha⟩
      have h1 : (q * (layerMul B xs)⁻¹) * a = a * (q * (layerMul B xs)⁻¹) :=
        congrArg Subtype.val this
      exact h1.symm
    · rw [mem_centralizer_singleton_iff]
      have := hz ⟨K, hK⟩ k hk
      calc k * (q * (layerMul B xs)⁻¹)
          = ((q * (layerMul B xs)⁻¹) * k * (q * (layerMul B xs)⁻¹)⁻¹) *
              (q * (layerMul B xs)⁻¹) := by rw [this]
        _ = (q * (layerMul B xs)⁻¹) * k := by group
  have htC : q * (layerMul B xs)⁻¹ ∈ centralizer (generalizedFitting B : Set B) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
  have htF := CFSG.centralizer_generalizedFitting_le B htC
  have e : q = (q * (layerMul B xs)⁻¹) * layerMul B xs := by group
  rw [e]
  exact Subgroup.mul_mem _ htF (Subgroup.mem_sup_right hεL)

theorem k631a_layer_le (hInn : KFactInnerAction) (h : k631aBHyp f Q) {Y₂ V : Subgroup B}
    (hY2 : IsPGroup 2 Y₂) (hVQ : V ≤ Q) (hYV : ⁅Y₂, V⁆ = Y₂) : Y₂ ≤ layer B := by
  have := Fact.mk h.prime
  have hN : (generalizedFitting B).Normal :=
    (generalized_fitting_characteristic (G := B)).2
  have : (layer B).Characteristic := layer_characteristic (G := B)
  have hLn : (layer B).Normal := inferInstance
  have hfs : Y₂ ≤ generalizedFitting B := by
    rw [← hYV]
    refine Subgroup.commutator_le.2 fun y hy v hv => ?_
    have hvF := k631a_Q_le_fstar hInn h (hVQ hv)
    rw [commutatorElement_def]
    exact mul_mem (hN.conj_mem v hvF y) (inv_mem hvF)
  have hFp : IsPGroup f (fittingSubgroup B) := by
    rw [CFSG.Fitting_eq_pcore B f h.core]
    exact CFSG.pCore_isPGroup
  intro y hy
  have hy' := hfs hy
  rw [generalizedFitting, ← SetLike.mem_coe, Subgroup.mul_normal] at hy'
  obtain ⟨a, ha, e, he, rfl⟩ := hy'
  obtain ⟨k, hk⟩ := k631a_exists_pow_eq_one hFp ha
  obtain ⟨m, hm⟩ := hY2 ⟨a * e, hy⟩
  have hm' : (a * e) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ m) (f ^ k) :=
    ((Nat.coprime_primes Nat.prime_two h.prime).2 (Ne.symm h.ne_two)).pow m k
  have e1 : QuotientGroup.mk' (layer B) (a * e) = QuotientGroup.mk' (layer B) a := by
    have he1 : QuotientGroup.mk' (layer B) e = 1 := (QuotientGroup.eq_one_iff e).2 he
    rw [map_mul, he1, mul_one]
  have h1 : QuotientGroup.mk' (layer B) (a * e) ^ 2 ^ m = 1 := by
    rw [← map_pow, hm', map_one]
  have h2 : QuotientGroup.mk' (layer B) (a * e) ^ f ^ k = 1 := by
    rw [e1, ← map_pow, hk, map_one]
  have h3 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2)
  exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3)

end CFSG.LocalAnalysis.RankThreeTheoremC
