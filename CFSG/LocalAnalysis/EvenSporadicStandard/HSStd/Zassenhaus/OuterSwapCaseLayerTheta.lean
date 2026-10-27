module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Theta

variable {K : Type*} [Group K] (σ : MulAut K)

@[expose] def thetaSub : Subgroup K where
  carrier := {x | x⁻¹ * σ x ∈ center K}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : x⁻¹ * σ x ∈ center K := hx
    have hy' : y⁻¹ * σ y ∈ center K := hy
    have h1 := (mem_center_iff.1 hx') y⁻¹
    have e : (x * y)⁻¹ * σ (x * y) = (x⁻¹ * σ x) * (y⁻¹ * σ y) := by
      calc (x * y)⁻¹ * σ (x * y) = y⁻¹ * (x⁻¹ * σ x) * σ y := by rw [map_mul]; group
        _ = (x⁻¹ * σ x) * y⁻¹ * σ y := by rw [h1]
        _ = _ := by group
    show (x * y)⁻¹ * σ (x * y) ∈ center K
    rw [e]
    exact mul_mem hx' hy'
  inv_mem' := by
    intro x hx
    have hx' : x⁻¹ * σ x ∈ center K := hx
    have h1 := (mem_center_iff.1 (inv_mem hx')) x
    have e : (x⁻¹)⁻¹ * σ x⁻¹ = (x⁻¹ * σ x)⁻¹ := by
      calc (x⁻¹)⁻¹ * σ x⁻¹ = x * (σ x)⁻¹ := by rw [map_inv]; group
        _ = x * (σ x)⁻¹ * x * x⁻¹ := by group
        _ = x * ((σ x)⁻¹ * x) * x⁻¹ := by group
        _ = (x * (x⁻¹ * σ x)⁻¹) * x⁻¹ := by group
        _ = ((x⁻¹ * σ x)⁻¹ * x) * x⁻¹ := by rw [h1]
        _ = (x⁻¹ * σ x)⁻¹ := by group
    show (x⁻¹)⁻¹ * σ x⁻¹ ∈ center K
    rw [e]
    exact inv_mem hx'

theorem mem_thetaSub_iff {x : K} : x ∈ thetaSub σ ↔ x⁻¹ * σ x ∈ center K := Iff.rfl

theorem center_le_thetaSub : center K ≤ thetaSub σ := by
  intro z hz
  rw [mem_thetaSub_iff]
  have : σ z ∈ center K := by
    have := map_center_eq_center σ
    rw [← this]
    exact ⟨z, hz, rfl⟩
  exact mul_mem (inv_mem hz) this

@[expose] def thetaHom : ↥(thetaSub σ) →* K :=
  MonoidHom.mk' (fun x => (x : K)⁻¹ * σ x) (by
    intro x y
    have hx' : (x : K)⁻¹ * σ x ∈ center K := x.2
    have h1 := (mem_center_iff.1 hx') (y : K)⁻¹
    calc ((x * y : ↥(thetaSub σ)) : K)⁻¹ * σ ((x * y : ↥(thetaSub σ)) : K)
        = (y : K)⁻¹ * ((x : K)⁻¹ * σ x) * σ y := by
          rw [Subgroup.coe_mul, map_mul]; group
      _ = ((x : K)⁻¹ * σ x) * (y : K)⁻¹ * σ y := by rw [h1]
      _ = _ := by group)

theorem thetaHom_apply (x : ↥(thetaSub σ)) : thetaHom σ x = (x : K)⁻¹ * σ x := rfl

theorem thetaHom_mem_center (x : ↥(thetaSub σ)) : thetaHom σ x ∈ center K := x.2

theorem thetaHom_eq_one_iff (x : ↥(thetaSub σ)) : thetaHom σ x = 1 ↔ σ x = x := by
  rw [thetaHom_apply, inv_mul_eq_one]
  exact eq_comm

theorem autCentralizer_le_thetaSub : autCentralizer σ ≤ thetaSub σ := by
  intro x hx
  have hx' : σ x = x := hx
  rw [mem_thetaSub_iff, hx']
  simp

theorem card_ker_thetaHom : Nat.card (thetaHom σ).ker = Nat.card (autCentralizer σ) := by
  refine Nat.card_congr (Equiv.mk (fun x => ⟨(x.1 : K), ?_⟩) (fun y => ⟨⟨y.1, autCentralizer_le_thetaSub σ y.2⟩, ?_⟩) ?_ ?_)
  · have := (thetaHom_eq_one_iff σ x.1).1 x.2
    exact this
  · rw [MonoidHom.mem_ker, thetaHom_eq_one_iff]
    exact y.2
  · intro x
    rfl
  · intro y
    rfl

end Theta

section Quot

variable {K : Type*} [Group K] (σ : MulAut K)

theorem mem_autCentralizer_sylowQuotAut_iff (x : K) :
    (x : K ⧸ center K) ∈ autCentralizer (sylowQuotAut σ) ↔ x ∈ thetaSub σ := by
  have h : (x : K ⧸ center K) ∈ autCentralizer (sylowQuotAut σ) ↔
      sylowQuotAut σ (x : K ⧸ center K) = x := Iff.rfl
  rw [h, sylowQuotAut_mk, mem_thetaSub_iff, eq_comm, QuotientGroup.eq]

@[expose] def thetaQuot : ↥(thetaSub σ) →* K ⧸ center K :=
  (QuotientGroup.mk' (center K)).comp (thetaSub σ).subtype

theorem range_thetaQuot : (thetaQuot σ).range = autCentralizer (sylowQuotAut σ) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  constructor
  · rintro ⟨w, hw⟩
    have : ((w : K) : K ⧸ center K) = (x : K ⧸ center K) := hw
    rw [← this, mem_autCentralizer_sylowQuotAut_iff]
    exact w.2
  · intro hx
    rw [mem_autCentralizer_sylowQuotAut_iff] at hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_thetaQuot : (thetaQuot σ).ker = (center K).subgroupOf (thetaSub σ) := by
  ext w
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact QuotientGroup.eq_one_iff _

theorem card_autCentralizer_sylowQuotAut_le [Finite K] :
    Nat.card (autCentralizer (sylowQuotAut σ)) ≤ Nat.card (autCentralizer σ) := by
  have h1 := Subgroup.card_ker_mul_card_range (thetaQuot σ)
  have h2 := Subgroup.card_ker_mul_card_range (thetaHom σ)
  have hk : Nat.card (thetaQuot σ).ker = Nat.card (center K) := by
    rw [ker_thetaQuot]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (center_le_thetaSub σ)).toEquiv
  have hr : Nat.card (thetaQuot σ).range = Nat.card (autCentralizer (sylowQuotAut σ)) := by
    rw [range_thetaQuot]
  have hc : Nat.card (thetaHom σ).range ≤ Nat.card (center K) := by
    have hle : (thetaHom σ).range ≤ center K := by
      rintro _ ⟨x, rfl⟩
      exact thetaHom_mem_center σ x
    exact Subgroup.card_le_of_le hle
  have hker := card_ker_thetaHom σ
  have hpos : 0 < Nat.card (center K) := Nat.card_pos
  rw [hk, hr] at h1
  rw [hker] at h2
  have h3 : Nat.card (center K) * Nat.card (autCentralizer (sylowQuotAut σ)) ≤
      Nat.card (center K) * Nat.card (autCentralizer σ) := by
    rw [h1, ← h2, mul_comm]
    exact Nat.mul_le_mul_right _ hc
  exact Nat.le_of_mul_le_mul_left h3 hpos

theorem sylowQuotAut_sq (hσ : σ * σ = 1) : sylowQuotAut σ * sylowQuotAut σ = 1 := by
  have h := congrArg (sylowQuotAutHom (M := K)) hσ
  rwa [map_mul, map_one] at h

end Quot

section Hyps

variable {K : Type*} [Group K] [Finite K] (σ : MulAut K)

omit [Finite K] in
theorem conj_fixed_of_mem_thetaSub {θ : K} (hθ : θ ∈ thetaSub σ) {x : K} (hx : σ x = x) :
    σ (θ * x * θ⁻¹) = θ * x * θ⁻¹ := by
  have hc : θ⁻¹ * σ θ ∈ center K := hθ
  set c := θ⁻¹ * σ θ with hcdef
  have hσθ : σ θ = θ * c := by rw [hcdef]; group
  have h1 := (mem_center_iff.1 hc) x
  rw [map_mul, map_mul, map_inv, hx, hσθ]
  calc θ * c * x * (θ * c)⁻¹ = θ * (c * x * c⁻¹) * θ⁻¹ := by group
    _ = θ * x * θ⁻¹ := by rw [← h1]; group

omit [Finite K] in
theorem conj_mem_of_mem_thetaSub (J : Subgroup K) (hJp : ⁅J, J⁆ = J)
    (hP1 : ∀ Q : Subgroup K, (∀ q ∈ Q, σ q = q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    (hJF : ∀ j ∈ J, σ j = j) {θ : K} (hθ : θ ∈ thetaSub σ) {j : K} (hj : j ∈ J) :
    θ * j * θ⁻¹ ∈ J := by
  have hperf : ⁅J.map (MulAut.conj θ).toMonoidHom, J.map (MulAut.conj θ).toMonoidHom⁆ =
      J.map (MulAut.conj θ).toMonoidHom := by
    rw [← Subgroup.map_commutator, hJp]
  have hle := hP1 (J.map (MulAut.conj θ).toMonoidHom) (by
    rintro q ⟨j', hj', rfl⟩
    exact conj_fixed_of_mem_thetaSub σ hθ (hJF j' hj')) hperf
  exact hle ⟨j, hj, by simp [MulAut.conj_apply]⟩

omit [Finite K] in
theorem theta_hyps (hZ : IsPGroup 2 (center K)) (J : Subgroup K)
    (hJF : ∀ j ∈ J, σ j = j) (hJp : ⁅J, J⁆ = J) (hJZ : J ⊓ center K = ⊥)
    (hP1 : ∀ Q : Subgroup K, (∀ q ∈ Q, σ q = q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    (hP2 : ∀ w : K, σ w = w → w * w ∈ J) (e : ↥J ≃* alternatingGroup (Fin 8)) :
    ∃ D : Subgroup ↥(autCentralizer (sylowQuotAut σ)), D.Normal ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 8)) ∧
      ∀ x : ↥(autCentralizer (sylowQuotAut σ)), ∃ n : ℕ, x ^ (2 ^ n) ∈ D := by
  set A := autCentralizer (sylowQuotAut σ) with hA
  set Jb : Subgroup (K ⧸ center K) := J.map (QuotientGroup.mk' (center K)) with hJb
  have hJbA : Jb ≤ A := by
    rintro _ ⟨j, hj, rfl⟩
    exact (mem_autCentralizer_sylowQuotAut_iff σ j).2 (autCentralizer_le_thetaSub σ (hJF j hj))
  have hinj : Function.Injective ((QuotientGroup.mk' (center K)).comp J.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : K) ∈ center K := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : K) ∈ J ⊓ center K := ⟨x.2, hx1⟩
    rw [hJZ, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hrange : ((QuotientGroup.mk' (center K)).comp J.subtype).range = Jb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eJ : ↥J ≃* ↥Jb :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨Jb.subgroupOf A, ?_, ?_, ?_⟩
  · refine ⟨fun d hd g => ?_⟩
    rw [mem_subgroupOf] at hd ⊢
    obtain ⟨j, hj, hjd⟩ := hd
    obtain ⟨θ, hθg⟩ := QuotientGroup.mk_surjective (g : K ⧸ center K)
    have hθ : θ ∈ thetaSub σ := (mem_autCentralizer_sylowQuotAut_iff σ θ).1 (by
      rw [hθg]; exact g.2)
    refine ⟨θ * j * θ⁻¹, conj_mem_of_mem_thetaSub σ J hJp hP1 hJF hθ hj, ?_⟩
    show (QuotientGroup.mk (θ * j * θ⁻¹) : K ⧸ center K) = (g : K ⧸ center K) * (d : K ⧸ center K) *
      (g : K ⧸ center K)⁻¹
    rw [← hθg, ← hjd]
    simp
  · exact ⟨((Subgroup.subgroupOfEquivOfLe hJbA).trans eJ.symm).trans e⟩
  · intro x
    obtain ⟨θ, hθx⟩ := QuotientGroup.mk_surjective (x : K ⧸ center K)
    have hθ : θ ∈ thetaSub σ := (mem_autCentralizer_sylowQuotAut_iff σ θ).1 (by
      rw [hθx]; exact x.2)
    obtain ⟨m, hm⟩ := hZ ⟨thetaHom σ ⟨θ, hθ⟩, thetaHom_mem_center σ ⟨θ, hθ⟩⟩
    have hm' : thetaHom σ (⟨θ, hθ⟩ ^ (2 ^ m)) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hm
      simpa using this
    have hfix : σ (θ ^ (2 ^ m)) = θ ^ (2 ^ m) := by
      have := (thetaHom_eq_one_iff σ (⟨θ, hθ⟩ ^ (2 ^ m))).1 hm'
      simpa using this
    have hJm : θ ^ (2 ^ (m + 1)) ∈ J := by
      have := hP2 _ hfix
      rwa [← pow_two, ← pow_mul, ← pow_succ] at this
    refine ⟨m + 1, ?_⟩
    rw [mem_subgroupOf]
    refine ⟨θ ^ (2 ^ (m + 1)), hJm, ?_⟩
    show (QuotientGroup.mk (θ ^ (2 ^ (m + 1))) : K ⧸ center K) = ((x ^ (2 ^ (m + 1)) : A) : K ⧸ center K)
    rw [Subgroup.coe_pow, ← hθx]
    simp

end Hyps

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
