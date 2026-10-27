module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpO2Blocks
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCPrimary CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCUnitary (unitaryCentralizer mem_unitaryCentralizer)

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem cast_ne_zero_of_odd {m : ℕ} (hm : Odd m) : (m : K) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hm
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
    Nat.cast_one]
  exact one_ne_zero

theorem eq_bot_of_le_centralizer_statedSp {z : StatedSp n K} (hz : Odd (orderOf z))
    {Q : Subgroup (StatedSp n K)} (hQ : Q ≤ Subgroup.centralizer {z}) (hQ2 : IsPGroup 2 Q)
    (hN : Subgroup.centralizer {z} ≤ Subgroup.normalizer (Q : Set (StatedSp n K))) : Q = ⊥ := by
  classical
  set m := orderOf z with hmdef
  have hzm : z ^ m = 1 := pow_orderOf_eq_one z
  have H := altPrimaryData_spLin (cast_ne_zero_of_odd hz) hzm
  set x := spLin n K z with hxdef
  have hxm : x ^ m = 1 := by rw [hxdef, ← map_pow, hzm, map_one]
  set Q' := Q.map (spLin n K) with hQ'def
  have hQ'2 : IsPGroup 2 Q' := hQ2.map _
  have hQx : ∀ g ∈ Q', Commute ((g : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
      Module.End K (Fin n ⊕ Fin n → K)) (x : Module.End K (Fin n ⊕ Fin n → K)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqz : q * z = z * q := Subgroup.mem_centralizer_singleton_iff.mp (hQ hq)
    change spEnd q * spEnd z = spEnd z * spEnd q
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hqz]
  have hQN : ∀ c ∈ unitaryCentralizer (spForm n K) x, ∀ g ∈ Q', c * g * c⁻¹ ∈ Q' := by
    intro c hc g hg
    obtain ⟨hcu, hcx⟩ := mem_unitaryCentralizer.mp hc
    obtain ⟨c₀, rfl⟩ : c ∈ (spLin n K).range := range_spLin.ge hcu
    have hc₀ : c₀ ∈ Subgroup.centralizer {z} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply spLin_injective
      rw [map_mul, map_mul]
      exact Units.ext hcx.eq
    obtain ⟨q, hq, rfl⟩ := hg
    refine ⟨c₀ * q * c₀⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hN hc₀) q).mp hq
  let F : Submodule K (Fin n ⊕ Fin n → K) :=
    { carrier := {v | ∀ g ∈ Q', ((g : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) v = v}
      add_mem' := fun hv hw g hg => by rw [map_add, hv g hg, hw g hg]
      zero_mem' := fun g _ => map_zero _
      smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg] }
  have hFC : ∀ c ∈ unitaryCentralizer (spForm n K) x, ∀ v ∈ F,
      ((c : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
        Module.End K (Fin n ⊕ Fin n → K)) v ∈ F := by
    intro c hc v hv g hg
    have h1 := hv _ (hQN c⁻¹ (inv_mem hc) g hg)
    rw [inv_inv, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply] at h1
    have h2 := congrArg ((c : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
      Module.End K (Fin n ⊕ Fin n → K)) h1
    rwa [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h2
  have hxC : x ∈ unitaryCentralizer (spForm n K) x :=
    mem_unitaryCentralizer.mpr ⟨H.isom, Commute.refl _⟩
  have hFa : ∀ a ∈ primaryFactors (x : Module.End K (Fin n ⊕ Fin n → K)),
      primaryComponent (x : Module.End K (Fin n ⊕ Fin n → K)) a ≤ F := by
    intro a ha
    obtain ⟨w, hw, hw0, hwfix⟩ := exists_ne_zero_fixed_of_isPGroup hQ'2
      (primaryComponent_ne_bot H.squarefree ha) fun g hg w hw =>
        apply_mem_primaryComponent (hQx g hg) hw
    have hW : F ⊓ primaryComponent (x : Module.End K (Fin n ⊕ Fin n → K)) a ≠ ⊥ := by
      intro hbot
      have h1 : w ∈ F ⊓ primaryComponent (x : Module.End K (Fin n ⊕ Fin n → K)) a :=
        ⟨hwfix, hw⟩
      rw [hbot, Submodule.mem_bot] at h1
      exact hw0 h1
    have hinv : ∀ c ∈ unitaryCentralizer (spForm n K) x,
        ∀ v ∈ F ⊓ primaryComponent (x : Module.End K (Fin n ⊕ Fin n → K)) a,
        ((c : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) v ∈
            F ⊓ primaryComponent (x : Module.End K (Fin n ⊕ Fin n → K)) a := by
      intro c hc v hv
      exact ⟨hFC c hc v hv.1,
        apply_mem_primaryComponent (mem_unitaryCentralizer.mp hc).2 hv.2⟩
    exact (primaryComponent_le_of_invariant H hz hxm ha inf_le_right hW
      (fun v hv => hinv x hxC v hv) hinv).trans inf_le_left
  have hFtop : ∀ v, v ∈ F := by
    intro v
    have hsum := congrArg (fun T : Module.End K (Fin n ⊕ Fin n → K) => T v)
      (sum_primaryProjection H.squarefree)
    simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
    rw [← hsum]
    exact F.sum_mem fun a ha => hFa a ha (primaryProjection_mem H.squarefree ha v)
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  apply spLin_injective
  rw [map_one]
  refine Units.ext (LinearMap.ext fun v => ?_)
  exact hFtop v _ ⟨q, hq, rfl⟩

end CFSG.ComponentClassification.RankTwoClassical
