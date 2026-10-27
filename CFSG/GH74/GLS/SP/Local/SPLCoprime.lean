module

public import Mathlib.GroupTheory.PGroup

import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddQuotientFixedPointFree
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

@[expose] def kleinFourSubgroup {G : Type*} [Group G] (z t : G) (hz : z * z = 1) (ht : t * t = 1)
    (hzt : z * t = t * z) : Subgroup G where
  carrier := {g | g = 1 ∨ g = z ∨ g = t ∨ g = z * t}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h1 : z * (z * t) = t := by rw [← mul_assoc, hz, one_mul]
    have h2 : t * (z * t) = z := by rw [← mul_assoc, ← hzt, mul_assoc, ht, mul_one]
    have h3 : z * t * z = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz, one_mul]
    have h4 : z * t * t = z := by rw [mul_assoc, ht, mul_one]
    have h5 : z * t * (z * t) = 1 := by rw [← mul_assoc, h3, ht]
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [h1, h2, h3, h4, h5, hz, ht, hzt.symm]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · simp
    · simp [hz']
    · simp [ht']
    · right; right; right
      rw [mul_inv_rev, hz', ht', hzt.symm]

section Klein

variable {G : Type*} [Group G] {z t : G} {hz : z * z = 1} {ht : t * t = 1} {hzt : z * t = t * z}

theorem mem_kleinFourSubgroup {g : G} :
    g ∈ kleinFourSubgroup z t hz ht hzt ↔ g = 1 ∨ g = z ∨ g = t ∨ g = z * t := Iff.rfl

theorem kleinFourSubgroup_mul_self {g : G} (hg : g ∈ kleinFourSubgroup z t hz ht hzt) :
    g * g = 1 := by
  have h3 : z * t * z = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz, one_mul]
  have h5 : z * t * (z * t) = 1 := by rw [← mul_assoc, h3, ht]
  rcases mem_kleinFourSubgroup.mp hg with rfl | rfl | rfl | rfl
  · exact mul_one _
  · exact hz
  · exact ht
  · exact h5

theorem kleinFourSubgroup_conj_mem {V : Subgroup G} (hzV : ∀ v ∈ V, z * v * z⁻¹ ∈ V)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) {g : G} (hg : g ∈ kleinFourSubgroup z t hz ht hzt) {v : G}
    (hv : v ∈ V) : g * v * g⁻¹ ∈ V := by
  rcases mem_kleinFourSubgroup.mp hg with rfl | rfl | rfl | rfl
  · simpa using hv
  · exact hzV v hv
  · exact htV v hv
  · have : z * t * v * (z * t)⁻¹ = z * (t * v * t⁻¹) * z⁻¹ := by group
    rw [this]
    exact hzV _ (htV v hv)

theorem kleinFourSubgroup_le_normalizer {V : Subgroup G} (hzV : ∀ v ∈ V, z * v * z⁻¹ ∈ V)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    kleinFourSubgroup z t hz ht hzt ≤ normalizer (V : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => kleinFourSubgroup_conj_mem hzV htV hg hv, fun hv => ?_⟩
  have h := kleinFourSubgroup_conj_mem hzV htV ((kleinFourSubgroup z t hz ht hzt).inv_mem hg) hv
  have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
  rwa [e] at h

theorem card_kleinFourSubgroup (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hzt1 : z ≠ t) :
    Nat.card ↥(kleinFourSubgroup z t hz ht hzt) = 4 := by
  have hset : ((kleinFourSubgroup z t hz ht hzt : Subgroup G) : Set G) = {1, z, t, z * t} := by
    ext g
    simp [mem_kleinFourSubgroup]
  have h1 : (1 : G) ≠ z * t := by
    intro h
    have : z = t⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    exact hzt1 (this.trans (inv_eq_of_mul_eq_one_right ht))
  have h2 : z ≠ z * t := fun h => ht1 (mul_eq_left.mp h.symm)
  have h3 : t ≠ z * t := fun h => hz1 (mul_eq_right.mp h.symm)
  rw [show Nat.card ↥(kleinFourSubgroup z t hz ht hzt) =
      Nat.card ↥((kleinFourSubgroup z t hz ht hzt : Subgroup G) : Set G) from rfl,
    Nat.card_coe_set_eq, hset]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h3]
  · simp [hzt1, h2]
  · simp [hz1.symm, ht1.symm, h1]

end Klein

theorem commute_of_inverted {G : Type} [Group G] (P Y : Subgroup G) (hPodd : Odd (Nat.card ↥P))
    (hY : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Y) (hYc : ∀ y ∈ Y, ∀ x ∈ P, y * x = x * y)
    (z : G) (hzP : ∀ v ∈ P, z * v * z⁻¹ ∈ P) (hzY : ∀ y ∈ Y, z * y * z⁻¹ = y)
    (x y : G) (hx : x ∈ P) (hy : y ∈ P) (hzx : z * x * z⁻¹ = x) (hzy : z * y * z⁻¹ = y⁻¹) :
    x * y = y * x := by
  set c : G := x * y * x⁻¹ * y⁻¹ with hc
  have hcY : c ∈ Y := hY x hx y hy
  have hcP : c ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  have _ : z * c * z⁻¹ ∈ P := hzP c hcP
  have hzc : z * c * z⁻¹ = c := hzY c hcY
  have h1 : z * c * z⁻¹ = x * y⁻¹ * x⁻¹ * y := by
    have e : z * c * z⁻¹ =
        (z * x * z⁻¹) * (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ * (z * y * z⁻¹)⁻¹ := by
      rw [hc]; group
    rw [e, hzx, hzy]; group
  have hcy : c * y = y * c := hYc c hcY y hy
  have hcy' : c⁻¹ * y = y * c⁻¹ := (show Commute c y from hcy).inv_left
  have hcyc : c * y = x * y * x⁻¹ := by rw [hc]; group
  have key : c = c⁻¹ := by
    calc c = x * y⁻¹ * x⁻¹ * y := by rw [← hzc, h1]
      _ = (x * y * x⁻¹)⁻¹ * y := by group
      _ = (c * y)⁻¹ * y := by rw [hcyc]
      _ = y⁻¹ * c⁻¹ * y := by rw [mul_inv_rev]
      _ = c⁻¹ := by rw [mul_assoc, hcy', ← mul_assoc, inv_mul_cancel, one_mul]
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [key]; exact inv_mul_cancel c
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
  have hordP : orderOf c ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hcP
  have hcop : Nat.Coprime 2 (Nat.card P) := hPodd.coprime_two_left
  have hone : orderOf c = 1 := by
    have := Nat.dvd_gcd hord2 hordP
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at this
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hone
  rw [hc] at hc1
  have h3 : x * y * x⁻¹ = y := mul_inv_eq_one.mp hc1
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h3]

theorem commutator_le_of_fixedPointFree {G : Type} [Group G] [Finite G] (P Y : Subgroup G)
    (hPodd : Odd (Nat.card ↥P)) (hYP : Y ≤ P) (hYc : ∀ y ∈ Y, ∀ x ∈ P, y * x = x * y)
    (t : G) (ht : t * t = 1) (htP : ∀ v ∈ P, t * v * t⁻¹ ∈ P)
    (hfix : ∀ v ∈ P, t * v = v * t → v ∈ Y) :
    ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Y := by
  classical
  intro a ha b hb
  by_cases ht1 : t = 1
  · have hPY : ∀ v ∈ P, v ∈ Y := fun v hv => hfix v hv (by rw [ht1, one_mul, mul_one])
    exact hPY _ (P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb))
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htt : ∀ v : G, t * (t * v * t⁻¹) * t⁻¹ = v := by
    intro v
    rw [ht']
    calc t * (t * v * t) * t = (t * t) * v * (t * t) := by group
      _ = v := by rw [ht]; group
  have htnormP : t ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro v
    refine ⟨fun hv => htP v hv, fun hv => ?_⟩
    have := htP _ hv
    rwa [htt] at this
  have htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    intro y hy
    have hyP := hYP hy
    have hty := htP y hyP
    have hw : y * (t * y * t⁻¹) ∈ Y := by
      refine hfix _ (P.mul_mem hyP hty) ?_
      have hfixw : t * (y * (t * y * t⁻¹)) * t⁻¹ = y * (t * y * t⁻¹) := by
        calc t * (y * (t * y * t⁻¹)) * t⁻¹ = (t * y * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹) := by group
          _ = (t * y * t⁻¹) * y := by rw [htt]
          _ = y * (t * y * t⁻¹) := (hYc y hy _ hty).symm
      exact mul_inv_eq_iff_eq_mul.mp hfixw
    have : t * y * t⁻¹ = y⁻¹ * (y * (t * y * t⁻¹)) := by group
    rw [this]
    exact Y.mul_mem (Y.inv_mem hy) hw
  have htnormY : t ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff]
    intro v
    refine ⟨fun hv => htY v hv, fun hv => ?_⟩
    have := htY _ hv
    rwa [htt] at this
  have hIsInv : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨ht1, by rw [pow_two]; exact ht⟩
  have hDnormal : (Y.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hc := hYc _ hn (g : G) g.2
    have : ((g * n * g⁻¹ : P) : G) = (n : G) := by
      push_cast
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hn
  have hfixedlemma :=
    CFSG.GorensteinWalter.fixedPointFree_quotient_of_odd_solvable_and_fixedPoints_le
      P Y hYP hDnormal htnormP htnormY hIsInv (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hPodd) hPodd
      (fun v hv => hfix v hv.1 (mem_centralizer_singleton_iff.mp hv.2).symm)
  let N : Subgroup ↥P := Y.subgroupOf P
  have : N.Normal := hDnormal
  let c : ↥P →* ↥P :=
    { toFun := fun v => ⟨t * v * t⁻¹, htP v v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hcN : N ≤ N.comap c := fun n hn => by
    rw [mem_comap, mem_subgroupOf]
    exact htY n hn
  let φ : ↥P ⧸ N →* ↥P ⧸ N := QuotientGroup.map N N c hcN
  have hφinv : Function.Involutive φ := by
    intro q
    refine QuotientGroup.induction_on q fun k => ?_
    simp only [φ, QuotientGroup.map_mk]
    congr 1
    exact Subtype.ext (htt k)
  have hφfp : MonoidHom.FixedPointFree φ := by
    intro q
    refine QuotientGroup.induction_on q fun k hk => ?_
    have hk' : (QuotientGroup.mk (c k) : ↥P ⧸ N) = QuotientGroup.mk k := hk
    have hmem := QuotientGroup.eq.mp hk'.symm
    rw [mem_subgroupOf] at hmem
    have hkY : (k : G) ∈ Y := by
      refine hfixedlemma k ?_
      have h1 : (k : G)⁻¹ * (t * (k : G) * t⁻¹) ∈ Y := by simpa [c] using hmem
      have h2 := hYc _ h1 (k : G) k.2
      have : t * (k : G) * t⁻¹ * (k : G)⁻¹ = (k : G)⁻¹ * (t * (k : G) * t⁻¹) := by
        calc t * (k : G) * t⁻¹ * (k : G)⁻¹
            = (k : G) * ((k : G)⁻¹ * (t * (k : G) * t⁻¹)) * (k : G)⁻¹ := by group
          _ = ((k : G)⁻¹ * (t * (k : G) * t⁻¹)) * (k : G) * (k : G)⁻¹ := by rw [← h2]
          _ = (k : G)⁻¹ * (t * (k : G) * t⁻¹) := by group
      rw [this]; exact h1
    exact (QuotientGroup.eq_one_iff k).mpr (mem_subgroupOf.mpr hkY)
  have hcomm := hφfp.commute_all_of_involutive hφinv
    (QuotientGroup.mk ⟨a, ha⟩ : ↥P ⧸ N) (QuotientGroup.mk ⟨b, hb⟩ : ↥P ⧸ N)
  have hone : (QuotientGroup.mk
      (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥P) : ↥P ⧸ N) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hcomm.eq]
    group
  have := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hone)
  simpa using this

open CFSG.DisconnectedInvolutionGraph.Helpers in
theorem exists_pgroup_containing_fixed_points {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hVodd : Odd (Nat.card ↥V)) (z t : G) (hz : z * z = 1) (ht : t * t = 1) (hzt : z * t = t * z)
    (hzV : ∀ v ∈ V, z * v * z⁻¹ ∈ V) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (p : ℕ) (hp : p.Prime) (X X' : Subgroup G) (hXV : X ≤ V) (hX'V : X' ≤ V)
    (hXp : IsPGroup p ↥X) (hX'p : IsPGroup p ↥X')
    (hXz : ∀ x ∈ X, z * x * z⁻¹ ∈ X) (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hX'fix : ∀ x ∈ X', (z * t) * x = x * (z * t))
    (hfixzt : ∀ v ∈ V, (z * t) * v = v * (z * t) → v ∈ X') :
    ∃ P : Subgroup G, P ≤ V ∧ IsPGroup p ↥P ∧ X ≤ P ∧ X' ≤ P ∧
      (∀ v ∈ P, z * v * z⁻¹ ∈ P) ∧ (∀ v ∈ P, t * v * t⁻¹ ∈ P) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G := kleinFourSubgroup z t hz ht hzt with hK
  have hKnorm : K ≤ normalizer (V : Set G) := kleinFourSubgroup_le_normalizer hzV htV
  have : K.Normalizes V := ⟨hKnorm⟩
  have hKp : IsPGroup 2 ↥K := fun g =>
    ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa [pow_two] using kleinFourSubgroup_mul_self g.2)⟩
  have hcop : ¬ 2 ∣ Nat.card ↥V := hVodd.not_two_dvd_nat
  have hXVp : IsPGroup p ↥(X.subgroupOf V) := hXp.comap_subtype
  have hXVinv : InvariantSubgroup (A := ↥K) (X.subgroupOf V) := by
    intro a v hv
    rw [mem_subgroupOf] at hv ⊢
    change (a : G) * (v : G) * (a : G)⁻¹ ∈ X
    rcases mem_kleinFourSubgroup.mp a.2 with h | h | h | h
    · rw [h]; simpa using hv
    · rw [h]; exact hXz _ hv
    · rw [h]; exact hXt _ hv
    · rw [h]
      have e : z * t * (v : G) * (z * t)⁻¹ = z * (t * (v : G) * t⁻¹) * z⁻¹ := by group
      rw [e]; exact hXz _ (hXt _ hv)
  obtain ⟨Q, hXQ, hQinv⟩ := coprime_pgroup_invariant_sylow_containment 2 p hKp hcop
    (X.subgroupOf V) hXVp hXVinv
  have huK : z * t ∈ K := mem_kleinFourSubgroup.mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hBK : zpowers (z * t) ≤ K := zpowers_le.mpr huK
  have hBnorm : zpowers (z * t) ≤ normalizer (V : Set G) := hBK.trans hKnorm
  have : (zpowers (z * t)).Normalizes V := ⟨hBnorm⟩
  have hBp : IsPGroup 2 ↥(zpowers (z * t)) := fun g =>
    ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa [pow_two] using kleinFourSubgroup_mul_self (hBK g.2))⟩
  have hQinvB : InvariantSubgroup (A := ↥(zpowers (z * t))) (Q : Subgroup ↥V) :=
    fun b v hv => hQinv ⟨b, hBK b.2⟩ v hv
  obtain ⟨F, hF⟩ := coprime_pgroup_fixed_sylow 2 p hBp hcop Q hQinvB
  have hFp : IsPGroup p ↥(FixedPoints.subgroup ↥(zpowers (z * t)) ↥V) := by
    intro w
    have hw := (FixedPoints.mem_subgroup (zpowers (z * t)) V (w : V)).mp w.2
      ⟨z * t, mem_zpowers _⟩
    have hw' : z * t * ((w : V) : G) * (z * t)⁻¹ = ((w : V) : G) :=
      congrArg Subtype.val hw
    have hcomm : (z * t) * ((w : V) : G) = ((w : V) : G) * (z * t) :=
      mul_inv_eq_iff_eq_mul.mp hw'
    obtain ⟨k, hk⟩ := hX'p ⟨((w : V) : G), hfixzt _ (w : V).2 hcomm⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hFtop : (F : Subgroup ↥(FixedPoints.subgroup ↥(zpowers (z * t)) ↥V)) = ⊤ :=
    (F.is_maximal' (hFp.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hFle : ∀ w : ↥V, w ∈ FixedPoints.subgroup ↥(zpowers (z * t)) ↥V →
      w ∈ (Q : Subgroup ↥V) := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ↥(FixedPoints.subgroup ↥(zpowers (z * t)) ↥V)) ∈
        (F : Subgroup ↥(FixedPoints.subgroup ↥(zpowers (z * t)) ↥V)) := by
      rw [hFtop]; exact mem_top _
    rw [hF] at h1
    exact mem_subgroupOf.mp h1
  refine ⟨(Q : Subgroup ↥V).map V.subtype, Subgroup.map_subtype_le _,
    Q.isPGroup'.map V.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hXV hx⟩, hXQ (mem_subgroupOf.mpr hx), rfl⟩
  · intro x hx
    refine ⟨⟨x, hX'V hx⟩, hFle _ ?_, rfl⟩
    rw [FixedPoints.mem_subgroup]
    intro b
    apply Subtype.ext
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.2
    have hc : Commute (z * t) x := hX'fix x hx
    change (b : G) * x * (b : G)⁻¹ = x
    rw [← hn]
    exact (hc.zpow_left n).mul_inv_cancel
  · rintro v ⟨w, hw, rfl⟩
    exact ⟨(⟨z, mem_kleinFourSubgroup.mpr (Or.inr (Or.inl rfl))⟩ : ↥K) • w,
      hQinv _ w hw, rfl⟩
  · rintro v ⟨w, hw, rfl⟩
    exact ⟨(⟨t, mem_kleinFourSubgroup.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ : ↥K) • w,
      hQinv _ w hw, rfl⟩

theorem klein_generation {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hVodd : Odd (Nat.card ↥V)) (z t : G) (hz : z * z = 1) (ht : t * t = 1)
    (hzt : z * t = t * z) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hzt1 : z ≠ t)
    (hzV : ∀ v ∈ V, z * v * z⁻¹ ∈ V) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    V ≤ Subgroup.closure ((V ⊓ Subgroup.centralizer {z} : Subgroup G) ∪
        (V ⊓ Subgroup.centralizer {t} : Subgroup G) ∪
        (V ⊓ Subgroup.centralizer {z * t} : Subgroup G) : Set G) := by
  have hgen :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
      Nat.prime_two (kleinFourSubgroup z t hz ht hzt) V
      (fun m => Subtype.ext (by simpa [pow_two] using kleinFourSubgroup_mul_self m.2))
      (by rw [card_kleinFourSubgroup hz1 ht1 hzt1]; norm_num) hVodd.not_two_dvd_nat
      (kleinFourSubgroup_le_normalizer hzV htV)
  refine hgen.le.trans (iSup_le fun m => iSup_le fun hm => ?_)
  rcases mem_kleinFourSubgroup.mp m.2 with h | h | h | h
  · exact absurd (Subtype.ext h) hm
  · rw [h]
    exact fun x hx => subset_closure (Or.inl (Or.inl hx))
  · rw [h]
    exact fun x hx => subset_closure (Or.inl (Or.inr hx))
  · rw [h]
    exact fun x hx => subset_closure (Or.inr hx)

end CFSG.GH74.GLS.SP.Local
