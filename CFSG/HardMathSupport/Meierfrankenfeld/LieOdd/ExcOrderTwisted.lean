module

public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrderG2F4

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_le_three_pow_of_cube {ι : Type} [Fintype ι] {P : ι → Type}
    [∀ i, CommGroup (P i)] [∀ i, Finite (P i)] [∀ i, IsCyclic (P i)] {A : Type} [Group A]
    (ψ : (∀ i, P i) →* A) (hψ : Function.Surjective ψ) (h3 : ∀ a : A, a ^ 3 = 1) :
    Nat.card A ≤ 3 ^ Fintype.card ι := by
  classical
  choose c hc using fun i => IsCyclic.exists_generator (α := P i)
  let F : (ι → Fin 3) → A := fun m => ψ (fun i => c i ^ (m i : ℕ))
  have hF : Function.Surjective F := by
    intro a
    obtain ⟨u, rfl⟩ := hψ a
    have hk : ∀ i, ∃ k : ℕ, c i ^ k = u i := fun i =>
      Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hc i (u i)))
    choose k hk using hk
    refine ⟨fun i => ⟨k i % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    have hu : u = (fun i => c i ^ (k i % 3)) * (fun i => (c i ^ (k i / 3)) ^ 3) := by
      funext i
      rw [Pi.mul_apply, ← pow_mul, ← pow_add, Nat.mod_add_div', hk]
    have : ψ (fun i => (c i ^ (k i / 3)) ^ 3) = 1 := by
      have : (fun i => (c i ^ (k i / 3)) ^ 3) = (fun i => c i ^ (k i / 3)) ^ 3 := rfl
      rw [this, map_pow, h3]
    show ψ (fun i => c i ^ (k i % 3)) = ψ u
    rw [hu, map_mul, this, mul_one]
  have := Nat.card_le_card_of_surjective F hF
  simpa using this

theorem card_mulAut_le_of_center_eq_bot {S : Type} [Group S] [Finite S]
    (hS : Subgroup.center S = ⊥) {b N : ℕ} (hout : Nat.card (Outer S) ≤ b)
    (hord : Nat.card S ≤ N) : Nat.card (MulAut S) ≤ b * N := by
  have : Finite (MulAut S) :=
    Finite.of_injective (fun σ : MulAut S => (σ : S → S)) DFunLike.coe_injective
  rw [CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hS, mul_comm]
  exact Nat.mul_le_mul hout hord

theorem ordTrialityD4_le (q : ℕ) (hq : 2 ≤ q) : ordTrialityD4 q ≤ q ^ 28 := by
  unfold ordTrialityD4
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  set x := q ^ 2 with hx
  have h4 : 4 ≤ x := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have e1 : q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) =
      q ^ 12 * ((x ^ 4 + x ^ 2 + 1) * (x ^ 3 - 1) * (x - 1)) := by
    rw [hx]
    have : (q ^ 2) ^ 3 = q ^ 6 := by ring
    have h : (q ^ 2) ^ 4 = q ^ 8 := by ring
    have h' : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [this, h, h']
    ring
  have e2 : q ^ 28 = q ^ 12 * x ^ 8 := by rw [hx]; ring
  rw [e1, e2]
  refine Nat.mul_le_mul_left _ ?_
  have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [hx3, (by omega : 1 ≤ x)]
  nlinarith [pow_pos (show (0 : ℤ) < x by positivity) 6, pow_pos (show (0 : ℤ) < x by positivity) 4,
    pow_pos (show (0 : ℤ) < x by positivity) 2, mul_nonneg (show (0 : ℤ) ≤ x - 1 by
      have : (4 : ℤ) ≤ x := by exact_mod_cast h4
      linarith) (show (0 : ℤ) ≤ x ^ 6 + 2 * x ^ 4 + 2 * x ^ 2 + 1 by positivity)]

theorem ordTwistedE6_le (q : ℕ) (hq : 2 ≤ q) : ordTwistedE6 q ≤ 2 * q ^ 78 := by
  unfold ordTwistedE6
  refine (Nat.div_le_self _ _).trans ?_
  have h12 : q ^ 12 - 1 ≤ q ^ 12 := Nat.sub_le _ _
  have h8 : q ^ 8 - 1 ≤ q ^ 8 := Nat.sub_le _ _
  have h1 : (q ^ 9 + 1) * (q ^ 2 - 1) ≤ q ^ 11 := by
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h29 : q ^ 2 ≤ q ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
    zify [h2]
    have : (q : ℤ) ^ 11 = q ^ 9 * q ^ 2 := by ring
    zify at h29
    nlinarith
  have h2 : (q ^ 5 + 1) * (q ^ 6 - 1) ≤ 2 * q ^ 11 := by
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h56 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
    have h5 : q ^ 5 + 1 ≤ 2 * q ^ 5 := by omega
    calc (q ^ 5 + 1) * (q ^ 6 - 1) ≤ (2 * q ^ 5) * q ^ 6 :=
          Nat.mul_le_mul h5 (Nat.sub_le _ _)
      _ = 2 * q ^ 11 := by ring
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)
      = q ^ 36 * (q ^ 12 - 1) * (q ^ 8 - 1) * ((q ^ 9 + 1) * (q ^ 2 - 1)) *
        ((q ^ 5 + 1) * (q ^ 6 - 1)) := by ring
    _ ≤ q ^ 36 * q ^ 12 * q ^ 8 * q ^ 11 * (2 * q ^ 11) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h12) h8) h1) h2
    _ = 2 * q ^ 78 := by ring

section Groups

set_option linter.unusedSectionVars false


theorem center_graphFixedRootGroup_E6_eq_bot {k : Type} [Field k] [Finite k] (σ : k →+* k) :
    Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 k σ) = ⊥ := by
  let σe : k ≃+* k := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  exact exceptional_fixed_center_trivial TwistTag.E6 k σe

theorem card_mulAut_twistedGroup_le {K : Type} [Field K] [Finite K] {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = (p ^ e) ^ 3) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ e)) :
    Nat.card (MulAut ↥(twistedGroup σ)) ≤ 3 * e * (p ^ e) ^ 28 := by
  have hK3 : Nat.card K = p ^ (3 * e) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Fact.out
      (by omega) hK3
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hq : 2 ≤ p ^ e :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hmap := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup (σ := σ) hchar hq hK hσ
  let eC : twistedGroup σ ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
    (Subgroup.equivMapOfInjective (twistedGroup σ) (adjointGroup d4 K).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap)
  let σe : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσe : σe.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσe' : ∀ c, σe c = c ^ (p ^ e) := hσ
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcardK, -⟩ :=
    odd_triality_exact_automorphism_normal_form Fact.out hp2 he K hK σe hσe'
  have hZ := center_graphFixedRootGroup_eq_bot (σ := σ) (t := TwistTag.D4)
    (Finite.surjective_of_injective σ.injective)
  have hout : Nat.card (Outer (graphFixedRootGroup TwistTag.D4 K σ)) = 3 * e :=
    (card_outer_eq_of_surjective_ker Θ hsurj hker).trans hcardK
  have hord : Nat.card (graphFixedRootGroup TwistTag.D4 K σ) ≤ (p ^ e) ^ 28 := by
    rw [CFSG.ClassicalInvolution.card_graphFixedRootGroup_D4_of_ne_two Fact.out hp2 he hK σ hσ]
    exact ordTrialityD4_le _ hq
  rw [Nat.card_congr (MulAut.congr eC).toEquiv]
  exact card_mulAut_le_of_center_eq_bot hZ hout.le hord

theorem card_mulAut_graphFixedE6_le {k : Type} [Field k] [Finite k] {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hk : Nat.card k = (p ^ e) ^ 2) (σ : k →+* k)
    (hσ : ∀ c, σ c = c ^ (p ^ e)) :
    Nat.card (MulAut ↥(graphFixedRootGroup TwistTag.E6 k σ)) ≤ 324 * e * (p ^ e) ^ 78 := by
  classical
  have hk2 : Nat.card k = p ^ (2 * e) := by rw [hk, ← pow_mul, mul_comm]
  have hq : 2 ≤ p ^ e :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  let σe : k ≃+* k := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσe : σe.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσe' : ∀ c, σe c = c ^ (p ^ e) := hσ
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, hsurj, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form Fact.out hp2 he k hk σe hσe'
  have hle : inner (twistedE6RootGroup k σe) ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  set Φ := QuotientGroup.lift (inner (twistedE6RootGroup k σe)) Θ hle with hΦ
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hle α⟩
  have hcube' : ∀ x ∈ Φ.ker, x ^ 3 = 1 := by
    intro x hx
    rw [QuotientGroup.ker_lift, hker] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  have : Finite (twistedE6RootGroup k σe) := Subtype.finite
  have : Finite (Outer (twistedE6RootGroup k σe)) := by
    have : Finite (MulAut (twistedE6RootGroup k σe)) := MulEquiv.finite_left
    infer_instance
  have hcardA : Nat.card (RingAut k) = 2 * e :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Fact.out k hk2).1
  have hOut : Nat.card (Outer (twistedE6RootGroup k σe)) = Nat.card Φ.ker * (2 * e) := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj,
      Subgroup.card_top, hcardA]
  let ψ0 : ((a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 k σe.toRingHom a)ˣ) →*
      Outer (twistedE6RootGroup k σe) :=
    (QuotientGroup.mk' (inner (twistedE6RootGroup k σe))).comp
      (compatDiagAutHom TwistTag.E6 k σe.toRingHom)
  have hdiag : ∀ u, compatDiagAutHom TwistTag.E6 k σe.toRingHom u ∈ Θ.ker := fun u => by
    rw [hker]
    exact (le_sup_right : twistedE6Diag k σe ≤ _) ⟨u, rfl⟩
  have hψ0 : ∀ u, ψ0 u ∈ Φ.ker := fun u => by
    rw [MonoidHom.mem_ker]
    change Φ (QuotientGroup.mk _) = 1
    rw [hΦ, QuotientGroup.lift_mk]
    exact hdiag u
  let ψ := ψ0.codRestrict Φ.ker hψ0
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    have hα : α ∈ Θ.ker := by
      rw [MonoidHom.mem_ker]
      have := (MonoidHom.mem_ker.1 hx)
      rwa [hΦ, QuotientGroup.lift_mk] at this
    rw [hker] at hα
    obtain ⟨y, hy, z, ⟨u, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hα
    refine ⟨u, Subtype.ext ?_⟩
    change ψ0 u = QuotientGroup.mk (y * _)
    simp only [ψ0, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).2 hy, one_mul]
  have h3 : ∀ a : Φ.ker, a ^ 3 = 1 := fun a => Subtype.ext (hcube' a a.2)
  have hker81 : Nat.card Φ.ker ≤ 81 := by
    have := card_le_three_pow_of_cube ψ hψ h3
    rw [Fintype.card_fin] at this
    have hr : TwistTag.E6.foldedTag.rank = 4 := by decide
    rw [hr] at this
    simpa using this
  have hZ := center_graphFixedRootGroup_E6_eq_bot σ
  have hout : Nat.card (Outer (graphFixedRootGroup TwistTag.E6 k σ)) ≤ 81 * (2 * e) := by
    have h : Nat.card (Outer (graphFixedRootGroup TwistTag.E6 k σ)) =
        Nat.card Φ.ker * (2 * e) := hOut
    rw [h]
    exact Nat.mul_le_mul_right _ hker81
  have hord : Nat.card (graphFixedRootGroup TwistTag.E6 k σ) ≤ 2 * (p ^ e) ^ 78 := by
    rw [CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 Fact.out he hk σ hσ]
    exact ordTwistedE6_le _ hq
  have := card_mulAut_le_of_center_eq_bot hZ hout hord
  calc _ ≤ 81 * (2 * e) * (2 * (p ^ e) ^ 78) := this
    _ = 324 * e * (p ^ e) ^ 78 := by ring

end Groups

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
