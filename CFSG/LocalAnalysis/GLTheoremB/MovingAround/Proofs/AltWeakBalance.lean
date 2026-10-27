module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltWeakBalance

open Equiv Equiv.Perm
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open scoped commutatorElement

section PermFacts

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def orbSub (σ : Perm α) : Subgroup (Perm α) where
  carrier := {u | u * σ = σ * u ∧ ∀ x, ∃ k : ℕ, u x = (σ ^ k) x}
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨by rw [mul_assoc, hv, ← mul_assoc, hu, mul_assoc], fun x => ?_⟩
    obtain ⟨j, hj⟩ := hv' x
    obtain ⟨k, hk⟩ := hu' x
    refine ⟨k + j, ?_⟩
    have hc : u * σ ^ j = σ ^ j * u := (Commute.pow_right (hu : Commute u σ) j).eq
    calc (u * v) x = u ((σ ^ j) x) := by rw [Perm.mul_apply, hj]
      _ = (σ ^ j) (u x) := by rw [← Perm.mul_apply, hc, Perm.mul_apply]
      _ = (σ ^ (k + j)) x := by rw [hk, ← Perm.mul_apply, ← pow_add, add_comm]
  one_mem' := ⟨by rw [one_mul, mul_one], fun x => ⟨0, by simp⟩⟩
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨?_, fun x => ?_⟩
    · calc u⁻¹ * σ = u⁻¹ * (σ * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * σ) * u⁻¹ := by rw [hu]
        _ = σ * u⁻¹ := by group
    · obtain ⟨k, hk⟩ := hu' (u⁻¹ x)
      have h1 : (σ ^ k) (u⁻¹ x) = x := by rw [← hk]; simp
      have hN : 0 < orderOf σ := orderOf_pos σ
      refine ⟨(orderOf σ - 1) * k, ?_⟩
      have h2 : σ ^ ((orderOf σ - 1) * k) * σ ^ k = 1 := by
        have : (orderOf σ - 1) * k + k = orderOf σ * k := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hN]
        rw [← pow_add, this, pow_mul, pow_orderOf_eq_one, one_pow]
      calc u⁻¹ x = (σ ^ ((orderOf σ - 1) * k) * σ ^ k) (u⁻¹ x) := by rw [h2]; rfl
        _ = (σ ^ ((orderOf σ - 1) * k)) x := by rw [Perm.mul_apply, h1]

theorem pow_apply_of_mem_orbSub {σ u : Perm α} (hu : u ∈ orbSub σ) {x : α} {k : ℕ}
    (hk : u x = (σ ^ k) x) : ∀ m : ℕ, (u ^ m) x = (σ ^ (m * k)) x
  | 0 => by simp
  | m + 1 => by
    have hc : u ^ m * σ ^ k = σ ^ k * u ^ m := (Commute.pow_pow (hu.1 : Commute u σ) m k).eq
    rw [pow_succ, Perm.mul_apply, hk, ← Perm.mul_apply, hc, Perm.mul_apply,
      pow_apply_of_mem_orbSub hu hk m, ← Perm.mul_apply, ← pow_add]
    congr 2
    ring

theorem pow_eq_one_of_mem_orbSub {p : ℕ} {σ u : Perm α} (hσ : σ ^ p = 1) (hu : u ∈ orbSub σ) :
    u ^ p = 1 := by
  ext x
  obtain ⟨k, hk⟩ := hu.2 x
  rw [pow_apply_of_mem_orbSub hu hk p, pow_mul, hσ, one_pow]

theorem conj_mem_orbSub {σ c u : Perm α} (hc : c * σ = σ * c) (hu : u ∈ orbSub σ) :
    c * u * c⁻¹ ∈ orbSub σ := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : Commute c σ := hc
    have h2 : Commute u σ := hu.1
    exact ((h1.mul_left h2).mul_left h1.inv_left).eq
  · obtain ⟨k, hk⟩ := hu.2 (c⁻¹ x)
    refine ⟨k, ?_⟩
    have hck : c * σ ^ k = σ ^ k * c := (Commute.pow_right (hc : Commute c σ) k).eq
    rw [Perm.mul_apply, Perm.mul_apply, hk, ← Perm.mul_apply, hck, Perm.mul_apply]
    simp

theorem cycleOf_mem_orbSub (σ : Perm α) (x : α) : σ.cycleOf x ∈ orbSub σ := by
  refine ⟨?_, fun y => ?_⟩
  · ext y
    rw [Perm.mul_apply, Perm.mul_apply, Perm.cycleOf_apply, Perm.cycleOf_apply]
    by_cases h : σ.SameCycle x y
    · rw [if_pos (Perm.sameCycle_apply_right.2 h), if_pos h]
    · rw [if_neg (mt Perm.sameCycle_apply_right.1 h), if_neg h]
  · by_cases h : σ.SameCycle x y
    · exact ⟨1, by rw [Perm.cycleOf_apply, if_pos h, pow_one]⟩
    · exact ⟨0, by rw [Perm.cycleOf_apply, if_neg h, pow_zero]; rfl⟩

theorem sign_eq_one_of_pow_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : Perm α}
    (hg : g ^ p = 1) : Perm.sign g = 1 := by
  have h1 : (Perm.sign g) ^ p = 1 := by rw [← map_pow, hg, map_one]
  rcases Int.units_eq_one_or (Perm.sign g) with h | h
  · exact h
  · rw [h, (hp.odd_of_ne_two hp2).neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem orderOf_cycleOf_eq {p : ℕ} (hp : p.Prime) {σ : Perm α} (hσ : σ ^ p = 1) {y : α}
    (hy : σ y ≠ y) : orderOf (σ.cycleOf y) = p := by
  have h1 : orderOf (σ.cycleOf y) ∣ p :=
    (orderOf_cycleOf_dvd_orderOf σ y).trans (orderOf_dvd_of_pow_eq_one hσ)
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) (isCycle_cycleOf σ hy).ne_one
  · exact h

theorem apply_eq_self_of_comm_cycleOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ τ : Perm α}
    (hσ : σ ^ p = 1) (hτσ : τ * σ = σ * τ) {e : ℕ} (hτ : τ ^ 2 ^ e = 1) {y : α} (hy : σ y ≠ y)
    (hc : ∃ e' : ℕ, ⁅τ, σ.cycleOf y⁆ ^ 2 ^ e' = 1) : τ y = y := by
  obtain ⟨e', he'⟩ := hc
  have hcop : ∀ j : ℕ, Nat.Coprime p (2 ^ j) := fun j =>
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hcU : σ.cycleOf y ∈ orbSub σ := cycleOf_mem_orbSub σ y
  have hw : ⁅τ, σ.cycleOf y⁆ ∈ orbSub σ := by
    rw [commutatorElement_def]
    exact (orbSub σ).mul_mem (conj_mem_orbSub hτσ hcU) ((orbSub σ).inv_mem hcU)
  have hw1 : ⁅τ, σ.cycleOf y⁆ = 1 :=
    orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop e')
      (orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_orbSub hσ hw)) (orderOf_dvd_of_pow_eq_one he'))
  have hτc : τ * σ.cycleOf y = σ.cycleOf y * τ := commutatorElement_eq_one_iff_mul_comm.1 hw1
  have hsame : σ.SameCycle y (τ y) := by
    by_contra hs
    apply hy
    have h1 : σ.cycleOf y (τ y) = τ y := cycleOf_apply_of_not_sameCycle hs
    have h2 : σ.cycleOf y (τ y) = σ (τ y) := by
      calc σ.cycleOf y (τ y) = (σ.cycleOf y * τ) y := rfl
        _ = (τ * σ.cycleOf y) y := by rw [hτc]
        _ = τ (σ.cycleOf y y) := rfl
        _ = τ (σ y) := by rw [cycleOf_apply_self]
        _ = (τ * σ) y := rfl
        _ = (σ * τ) y := by rw [hτσ]
        _ = σ (τ y) := rfl
    have h3 : τ (σ y) = τ y := by
      calc τ (σ y) = (τ * σ) y := rfl
        _ = (σ * τ) y := by rw [hτσ]
        _ = σ (τ y) := rfl
        _ = σ.cycleOf y (τ y) := h2.symm
        _ = τ y := h1
    exact τ.injective h3
  obtain ⟨k, -, hk⟩ := hsame.exists_pow_eq'
  have hpow : ∀ j : ℕ, (τ ^ j) y = (σ ^ (j * k)) y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc' : τ ^ j * σ ^ k = σ ^ k * τ ^ j := (Commute.pow_pow (hτσ : Commute τ σ) j k).eq
      rw [pow_succ, Perm.mul_apply, ← hk, ← Perm.mul_apply, hc', Perm.mul_apply, ih,
        ← Perm.mul_apply, ← pow_add]
      congr 2
      ring
  have h2e : (σ.cycleOf y ^ (2 ^ e * k)) y = y := by
    rw [cycleOf_pow_apply_self, ← hpow, hτ]
    rfl
  have hc2 : σ.cycleOf y ^ (2 ^ e * k) = 1 :=
    (isCycle_cycleOf σ hy).pow_eq_one_iff.2 ⟨y, by rw [cycleOf_apply_self]; exact hy, h2e⟩
  have hpk : p ∣ k := by
    have h1 := orderOf_dvd_of_pow_eq_one hc2
    rw [orderOf_cycleOf_eq hp hσ hy] at h1
    exact (hcop e).dvd_of_dvd_mul_left h1
  obtain ⟨j, rfl⟩ := hpk
  rw [← hk, pow_mul, hσ, one_pow]
  rfl

theorem apply_eq_self_of_ncard_lt {p : ℕ} (hp : p.Prime) {g : Perm α} (hg : g ^ p = 1) {S : Set α}
    (hS : ∀ j ∈ S, g j ∈ S) (hcard : S.ncard < p) {j : α} (hj : j ∈ S) : g j = j := by
  by_contra hgj
  have hcyc : (g.cycleOf j).IsCycle := isCycle_cycleOf g hgj
  have hsupp : ((g.cycleOf j).support : Set α) ⊆ S := by
    intro z hz
    rw [Finset.mem_coe, mem_support_cycleOf_iff] at hz
    obtain ⟨k, -, hk⟩ := hz.1.exists_pow_eq'
    rw [← hk]
    clear hk
    induction k with
    | zero => simpa using hj
    | succ k ih => rw [pow_succ', Perm.mul_apply]; exact hS _ ih
  have h1 : (g.cycleOf j).support.card ≤ S.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsupp (Set.toFinite S)
  rw [← hcyc.orderOf, orderOf_cycleOf_eq hp hg hgj] at h1
  omega

end PermFacts

section Transport

variable {Y : Type*} [Group Y] {n : ℕ}

@[expose] noncomputable def autPerm (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6) :
    MulAut Y ≃* Perm (Fin n) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 h6)).symm

theorem autPerm_spec (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    (φ : MulAut Y) (y : Y) :
    ((e (φ y) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      autPerm e h5 h6 φ * (e y : Perm (Fin n)) * (autPerm e h5 h6 φ)⁻¹ := by
  have h1 : MulAut.conjNormal (H := alternatingGroup (Fin n)) (autPerm e h5 h6 φ) =
      MulAut.congr e φ := by
    have := (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 h6)).apply_symm_apply
      (MulAut.congr e φ)
    exact this
  have h2 := congrArg (fun ψ : MulAut (alternatingGroup (Fin n)) =>
    ((ψ (e y) : alternatingGroup (Fin n)) : Perm (Fin n))) h1
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  exact h2.symm

theorem autPerm_eq (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6) {φ : MulAut Y}
    {g : Perm (Fin n)}
    (hg : ∀ y : Y, ((e (φ y) : alternatingGroup (Fin n)) : Perm (Fin n)) = g * (e y : Perm (Fin n)) * g⁻¹) :
    autPerm e h5 h6 φ = g := by
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  obtain ⟨y, rfl⟩ := e.surjective a
  rw [← autPerm_spec, hg]

theorem autPerm_conj (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6) (k : Y) :
    autPerm e h5 h6 (MulAut.conj k) = (e k : Perm (Fin n)) :=
  autPerm_eq e h5 h6 fun y => by simp [MulAut.conj_apply]

theorem autPerm_symm_mem_innerAut (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    {u : Perm (Fin n)} (hu : u ∈ alternatingGroup (Fin n)) : (autPerm e h5 h6).symm u ∈ innerAut Y := by
  refine ⟨e.symm ⟨u, hu⟩, ?_⟩
  apply (autPerm e h5 h6).injective
  rw [MulEquiv.apply_symm_apply, autPerm_conj, MulEquiv.apply_symm_apply]

variable [Finite Y]

theorem apply_eq_self_of_mem_pCoreOf (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup (MulAut Y)} (hH : innerAut Y ≤ H)
    {d x : MulAut Y} (hd : d ^ p = 1)
    (hx : x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut Y)))) {y : Fin n}
    (hy : autPerm e h5 h6 d y ≠ y) : autPerm e h5 h6 x y = y := by
  haveI : Finite (MulAut Y) := Finite.of_equiv _ (autPerm e h5 h6).symm.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Θ := autPerm e h5 h6 with hΘ
  set C : Subgroup (MulAut Y) := H ⊓ Subgroup.centralizer ({d} : Set (MulAut Y)) with hC
  have hP : IsPGroup 2 ↥(pCoreOf 2 C) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hxC : x ∈ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C hx
  have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hxC).2
  have hσ : Θ d ^ p = 1 := by rw [← map_pow, hd, map_one]
  have hτσ : Θ x * Θ d = Θ d * Θ x := by rw [← map_mul, ← map_mul, hxd]
  obtain ⟨e₀, he₀⟩ := hP ⟨x, hx⟩
  have hτ : Θ x ^ 2 ^ e₀ = 1 := by
    have h1 : x ^ 2 ^ e₀ = 1 := by simpa using congrArg Subtype.val he₀
    rw [← map_pow, h1, map_one]
  refine apply_eq_self_of_comm_cycleOf hp hp2 hσ hτσ hτ hy ?_
  set c : Perm (Fin n) := (Θ d).cycleOf y with hc
  have hcσ : c * Θ d = Θ d * c := (cycleOf_mem_orbSub (Θ d) y).1
  have hcp : c ^ p = 1 := orderOf_dvd_iff_pow_eq_one.1
    ((orderOf_cycleOf_dvd_orderOf _ _).trans (orderOf_dvd_of_pow_eq_one hσ))
  have hcA : c ∈ alternatingGroup (Fin n) :=
    Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow_prime hp hp2 hcp)
  have hĉH : Θ.symm c ∈ H := hH (autPerm_symm_mem_innerAut e h5 h6 hcA)
  have hĉd : Θ.symm c * d = d * Θ.symm c := by
    apply Θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcσ
  have hĉC : Θ.symm c ∈ C :=
    Subgroup.mem_inf.2 ⟨hĉH, Subgroup.mem_centralizer_singleton_iff.2 hĉd⟩
  have hcomm : ⁅x, Θ.symm c⁆ ∈ pCoreOf 2 C := by
    rw [commutatorElement_def]
    have h1 : Θ.symm c * x⁻¹ * (Θ.symm c)⁻¹ ∈ pCoreOf 2 C :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hĉC) x⁻¹).1 ((pCoreOf 2 C).inv_mem hx)
    have h2 := (pCoreOf 2 C).mul_mem hx h1
    simpa only [mul_assoc] using h2
  obtain ⟨e₁, he₁⟩ := hP ⟨_, hcomm⟩
  refine ⟨e₁, ?_⟩
  have h1 : ⁅x, Θ.symm c⁆ ^ 2 ^ e₁ = 1 := by simpa using congrArg Subtype.val he₁
  have h2 : ⁅Θ x, c⁆ = Θ ⁅x, Θ.symm c⁆ := by
    rw [map_commutatorElement, MulEquiv.apply_symm_apply]
  rw [h2, ← map_pow, h1, map_one]

theorem comm_of_mem_pCoreOf (e : Y ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup (MulAut Y)} (hH : innerAut Y ≤ H)
    {d b x : MulAut Y} (hd : d ^ p = 1) (hb : b ^ p = 1) (hbd : b * d = d * b)
    (hfix : {j : Fin n | autPerm e h5 h6 d j = j}.ncard < p)
    (hx : x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut Y)))) : x * b = b * x := by
  set Θ := autPerm e h5 h6 with hΘ
  have hx1 : ∀ j, Θ d j ≠ j → Θ x j = j := fun j hj =>
    apply_eq_self_of_mem_pCoreOf e h5 h6 hp hp2 hH hd hx hj
  have hdb : Θ d * Θ b = Θ b * Θ d := by rw [← map_mul, ← map_mul, hbd]
  have hbS : ∀ j ∈ {j : Fin n | Θ d j = j}, Θ b j ∈ {j : Fin n | Θ d j = j} := by
    intro j hj
    have hj' : Θ d j = j := hj
    show Θ d (Θ b j) = Θ b j
    rw [← Perm.mul_apply, hdb, Perm.mul_apply, hj']
  have hbp : Θ b ^ p = 1 := by rw [← map_pow, hb, map_one]
  have hdisj : Perm.Disjoint (Θ x) (Θ b) := by
    intro j
    by_cases hj : Θ d j = j
    · exact Or.inr (apply_eq_self_of_ncard_lt hp hbp hbS hfix hj)
    · exact Or.inl (hx1 j hj)
  apply Θ.injective
  rw [map_mul, map_mul]
  exact hdisj.commute.eq

end Transport

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltWeakBalance

end
