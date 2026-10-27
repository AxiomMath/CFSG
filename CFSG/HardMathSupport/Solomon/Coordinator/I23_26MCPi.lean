module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCComp
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCDiag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y] {K E : Subgroup Y}

theorem mc_exists_noncomm {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    ∃ u v : Q, u * v ≠ v * u := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun y => h y x
  have := hq.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [QuotientGroup.eq]
  rw [hc]
  exact Subgroup.mem_top _

@[expose] def mcPi (K E : Subgroup Y) : Subgroup Y :=
  ⨆ (e : Y) (_ : e ∈ E), GLBConj e K

theorem mc_le_pi {e : Y} (he : e ∈ E) : GLBConj e K ≤ mcPi K E :=
  le_iSup₂ (f := fun (e : Y) (_ : e ∈ E) => GLBConj e K) e he

theorem mc_pi_le_normalizer (hK : IsComponentOf K ⊤) (e : Y) :
    mcPi K E ≤ Subgroup.normalizer (GLBConj e K : Set Y) := by
  refine iSup₂_le fun f hf => ?_
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (mc_isComponentOf_gLBConj hK f)
      (mc_isComponentOf_gLBConj hK e) with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · intro x hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have : x * n * x⁻¹ = n := by rw [h x hx n hn]; group
    rw [this]
    exact hn

theorem mc_pi_decomp (hK : IsComponentOf K ⊤) {e : Y} (he : e ∈ E) {p : Y} (hp : p ∈ mcPi K E) :
    ∃ k ∈ GLBConj e K, ∃ a ∈ mcPi K E, (∀ y ∈ GLBConj e K, y * a = a * y) ∧ p = k * a := by
  have hle : mcPi K E ≤ GLBConj e K ⊔ Subgroup.centralizer (GLBConj e K : Set Y) := by
    refine iSup₂_le fun f hf => ?_
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (mc_isComponentOf_gLBConj hK f)
        (mc_isComponentOf_gLBConj hK e) with h | h
    · rw [h]; exact le_sup_left
    · exact le_sup_of_le_right fun x hx =>
        Subgroup.mem_centralizer_iff.2 fun y hy => (h x hx y hy).symm
  have hmem : p ∈ ((GLBConj e K ⊔ Subgroup.centralizer (GLBConj e K : Set Y) : Subgroup Y) : Set Y) :=
    hle hp
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (GLBConj e K) _
    (Subgroup.centralizer_le_normalizer _)] at hmem
  obtain ⟨x, hx, a, ha, rfl⟩ := hmem
  refine ⟨x, hx, a, ?_, fun y hy => (Subgroup.mem_centralizer_iff.1 ha y hy), rfl⟩
  have := (mcPi K E).mul_mem ((mcPi K E).inv_mem (mc_le_pi he hx)) hp
  rwa [inv_mul_cancel_left] at this

theorem mc_pi_central {z : Y} (hz : z ∈ mcPi K E) (hc : ∀ e ∈ E, ∀ y ∈ GLBConj e K, y * z = z * y)
    {p : Y} (hp : p ∈ mcPi K E) : p * z = z * p := by
  have hle : mcPi K E ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine iSup₂_le fun e he x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc e he x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hp)

@[expose] def mcA (K E : Subgroup Y) (e : Y) : Subgroup ↥(mcPi K E) :=
  (Subgroup.centralizer (GLBConj e K : Set Y)).subgroupOf (mcPi K E)

theorem mem_mcA {e : Y} {x : ↥(mcPi K E)} :
    x ∈ mcA K E e ↔ ∀ y ∈ GLBConj e K, y * (x : Y) = x * y := by
  unfold mcA
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  rfl

theorem mcA_normal (hK : IsComponentOf K ⊤) (e : Y) : (mcA K E e).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rw [mem_mcA] at ha ⊢
  intro y hy
  have hy' : (g : Y)⁻¹ * y * g ∈ GLBConj e K := by
    have h1 := (Subgroup.mem_normalizer_iff.1
      (mc_pi_le_normalizer hK e ((mcPi K E).inv_mem g.2)) y).1 hy
    simpa using h1
  have h2 := ha _ hy'
  have hco : ((g * a * g⁻¹ : ↥(mcPi K E)) : Y) = (g : Y) * (a : Y) * (g : Y)⁻¹ := rfl
  rw [hco]
  calc y * ((g : Y) * a * (g : Y)⁻¹)
      = g * (((g : Y)⁻¹ * y * g) * a) * (g : Y)⁻¹ := by group
    _ = g * (a * ((g : Y)⁻¹ * y * g)) * (g : Y)⁻¹ := by rw [h2]
    _ = ((g : Y) * a * (g : Y)⁻¹) * y := by group

theorem mc_hmax (hK : IsComponentOf K ⊤) {e : Y} (he : e ∈ E) (N : Subgroup ↥(mcPi K E))
    [hN : N.Normal] (hAN : mcA K E e ≤ N) : N = mcA K E e ∨ N = ⊤ := by
  have hKe := mc_isComponentOf_gLBConj hK e
  let N' : Subgroup Y := N.map (mcPi K E).subtype
  have hN'mem : ∀ x : Y, x ∈ N' ↔ ∃ h : x ∈ mcPi K E, (⟨x, h⟩ : ↥(mcPi K E)) ∈ N := by
    intro x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n.2, hn⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have hN'conj : ∀ p ∈ mcPi K E, ∀ m ∈ N', p * m * p⁻¹ ∈ N' := by
    intro p hp m hm
    obtain ⟨hmP, hmN⟩ := (hN'mem m).1 hm
    refine (hN'mem _).2 ⟨(mcPi K E).mul_mem ((mcPi K E).mul_mem hp hmP) ((mcPi K E).inv_mem hp),
      ?_⟩
    exact hN.conj_mem _ hmN ⟨p, hp⟩
  let M0 : Subgroup ↥(GLBConj e K) := (N' ⊓ GLBConj e K).subgroupOf (GLBConj e K)
  have hM0 : M0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro m u hm hu
    exact ⟨hN'conj u (mc_le_pi he hu) m hm.1,
      (GLBConj e K).mul_mem ((GLBConj e K).mul_mem hu hm.2) ((GLBConj e K).inv_mem hu)⟩
  rcases mc_normal_le_center_or_top hKe.2.2 M0 with hc | htop
  · left
    refine le_antisymm (fun n hn => ?_) hAN
    rw [mem_mcA]
    have hperf : ⁅GLBConj e K, GLBConj e K⁆ = GLBConj e K := mc_commutator_eq_of_qs hKe.2.2
    have hnorm : ∀ u ∈ GLBConj e K, (n : Y)⁻¹ * u * n ∈ GLBConj e K := by
      intro u hu
      have := Subgroup.mem_normalizer_iff.1
        (mc_pi_le_normalizer hK e ((mcPi K E).inv_mem n.2)) u
      simpa using this.1 hu
    have hz : ∀ u ∈ GLBConj e K, ∀ v ∈ GLBConj e K,
        v * (u⁻¹ * ((n : Y)⁻¹ * u * n)) = (u⁻¹ * ((n : Y)⁻¹ * u * n)) * v := by
      intro u hu v hv
      have hzK : u⁻¹ * ((n : Y)⁻¹ * u * n) ∈ GLBConj e K :=
        (GLBConj e K).mul_mem ((GLBConj e K).inv_mem hu) (hnorm u hu)
      have hzN : u⁻¹ * ((n : Y)⁻¹ * u * n) ∈ N' := by
        have h0 : ((n : Y)⁻¹) ∈ N' := (hN'mem _).2 ⟨(mcPi K E).inv_mem n.2, N.inv_mem hn⟩
        have h1 := hN'conj u⁻¹ ((mcPi K E).inv_mem (mc_le_pi he hu)) _ h0
        have h2 : (n : Y) ∈ N' := (hN'mem _).2 ⟨n.2, hn⟩
        have := N'.mul_mem h1 h2
        simpa [mul_assoc] using this
      have hzM : (⟨_, hzK⟩ : ↥(GLBConj e K)) ∈ M0 := Subgroup.mem_subgroupOf.2 ⟨hzN, hzK⟩
      have := Subgroup.mem_center_iff.1 (hc hzM) ⟨v, hv⟩
      exact congrArg Subtype.val this
    intro y hy
    exact (mc_commute_of_perfect hperf hnorm hz y hy).symm
  · right
    have hKN : GLBConj e K ≤ N' := fun x hx => by
      have : (⟨x, hx⟩ : ↥(GLBConj e K)) ∈ M0 := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).1
    rw [eq_top_iff]
    intro q _
    obtain ⟨k, hk, a, haP, hac, hq⟩ := mc_pi_decomp hK he q.2
    obtain ⟨hkP, hkN⟩ := (hN'mem k).1 (hKN hk)
    have haN : (⟨a, haP⟩ : ↥(mcPi K E)) ∈ N := hAN (mem_mcA.2 fun y hy => hac y hy)
    have : q = ⟨k, hkP⟩ * ⟨a, haP⟩ := Subtype.ext hq
    rw [this]
    exact N.mul_mem hkN haN

theorem mc_hnab (hK : IsComponentOf K ⊤) {e : Y} (he : e ∈ E) :
    ¬ ⁅(⊤ : Subgroup ↥(mcPi K E)), (⊤ : Subgroup ↥(mcPi K E))⁆ ≤ mcA K E e := by
  intro h
  have hKe := mc_isComponentOf_gLBConj hK e
  have hperf := mc_commutator_eq_of_qs hKe.2.2
  have hle : ⁅GLBConj e K, GLBConj e K⁆ ≤ Subgroup.centralizer (GLBConj e K : Set Y) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    have := h (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨u, mc_le_pi he hu⟩ : ↥(mcPi K E)))
      (Subgroup.mem_top (⟨v, mc_le_pi he hv⟩ : ↥(mcPi K E))))
    rw [mem_mcA] at this
    exact Subgroup.mem_centralizer_iff.2 fun y hy => this y hy
  rw [hperf] at hle
  obtain ⟨u, v, huv⟩ := mc_exists_noncomm hKe.2.2
  exact huv (Subtype.ext (Subgroup.mem_centralizer_iff.1 (hle v.2) u.1 u.2))

end CFSG.HardMathSupport.Solomon.Coordinator
