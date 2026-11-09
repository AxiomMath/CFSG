module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct

public section

namespace CFSG.Certificates.Kernel.SylowClass

open Pointwise MulAction

theorem mem_conj_list_of_sylow {K : Type*} [Group K] [Finite K] {p a m : ℕ} [hp : Fact p.Prime]
    (P : Subgroup K) (hK : Nat.card K = p ^ a * m) (hP : Nat.card P = p ^ a) (hm : ¬ p ∣ m)
    (e : K) (hPe : ∀ y ∈ P, y * e = e * y)
    (hcls : ∀ y ∈ P, y ^ p = 1 → y ≠ 1 → ∃ d : K, d * e * d⁻¹ = y)
    (cs : List K) (hnd : (cs.map fun c => c * e * c⁻¹).Nodup) (hlen : cs.length = m)
    (x : K) (hx : x ^ p = 1) (hx1 : x ≠ 1) : ∃ c ∈ cs, c * e * c⁻¹ = x := by
  classical
  have hidx : P.index = m := by
    have h := P.card_mul_index
    rw [hP, hK] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos a) h
  let S : Sylow p K := (IsPGroup.of_card hP).toSylow (by rw [hidx]; exact hm)
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hx hx1
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S Q
  have hxQ : x ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨b, hb, hbx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hbx
  have hbS : b ∈ P := hb
  have hb1 : b ^ p = 1 := by
    have : (g * b * g⁻¹) ^ p = 1 := by rw [hbx]; exact hx
    rwa [conj_pow, mul_inv_eq_one, mul_eq_left] at this
  have hbn : b ≠ 1 := by
    rintro rfl
    apply hx1
    rw [← hbx]
    group
  obtain ⟨d, hd⟩ := hcls b hbS hb1 hbn
  have hfin : Finite (ConjAct K) := inferInstanceAs (Finite K)
  have hO : (orbit (ConjAct K) e).ncard ≤ m := by
    rw [← index_stabilizer]
    have h1 := (stabilizer (ConjAct K) e).index_mul_card
    have h2 : p ^ a ≤ Nat.card (stabilizer (ConjAct K) e) := by
      rw [← hP]
      have hmem : ∀ y : P, ConjAct.toConjAct (y : K) ∈ stabilizer (ConjAct K) e := fun y => by
        rw [mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
          hPe _ y.2, mul_inv_cancel_right]
      refine Nat.card_le_card_of_injective
        (fun y : P => (⟨ConjAct.toConjAct (y : K), hmem y⟩ : stabilizer (ConjAct K) e)) ?_
      intro y z h
      simpa using h
    have hc : Nat.card (ConjAct K) = Nat.card K := rfl
    rw [hc, hK] at h1
    have h3 : (stabilizer (ConjAct K) e).index * p ^ a ≤ p ^ a * m :=
      h1 ▸ Nat.mul_le_mul_left _ h2
    rw [Nat.mul_comm] at h3
    exact Nat.le_of_mul_le_mul_left h3 (pow_pos hp.out.pos a)
  let T : Set K := {z | z ∈ cs.map fun c => c * e * c⁻¹}
  have hT : T ⊆ orbit (ConjAct K) e := by
    rintro z hz
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hz
    refine ⟨ConjAct.toConjAct c, ?_⟩
    change ConjAct.toConjAct c • e = _
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  have hTn : T.ncard = m := by
    have : T = ((cs.map fun c => c * e * c⁻¹).toFinset : Set K) := by ext; simp [T]
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map, hlen]
  have hEq : T = orbit (ConjAct K) e :=
    Set.eq_of_subset_of_ncard_le hT (by rw [hTn]; exact hO) (Set.toFinite _)
  have hxO : x ∈ orbit (ConjAct K) e :=
    ⟨ConjAct.toConjAct (g * d), by
      change ConjAct.toConjAct (g * d) • e = x
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← hbx, ← hd]
      group⟩
  rw [← hEq] at hxO
  obtain ⟨c, hc, hcx⟩ := List.mem_map.1 hxO
  exact ⟨c, hc, hcx⟩

end CFSG.Certificates.Kernel.SylowClass
