module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial
open scoped commutatorElement

section Orbits

private theorem dvd_natCard_of_forall_dvd_ncard_orbit {H α : Type*} [Group H] [MulAction H α]
    [Finite α] {n : ℕ} (h : ∀ x : α, n ∣ (MulAction.orbit H x).ncard) : n ∣ Nat.card α := by
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient H α)
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' H α), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  induction ω using Quotient.inductionOn with
  | h x =>
    rw [Nat.card_coe_set_eq]
    change n ∣ (MulAction.orbitRel.Quotient.orbit (Quotient.mk'' x)).ncard
    rw [MulAction.orbitRel.Quotient.orbit_mk (G := H) x]
    exact h x

end Orbits

section Conj

variable {G : Type*} [Group G]

theorem card_conj_eq_index [Finite G] (S : Setting G) :
    Nat.card {x : G | IsConj S.z x} = S.M.index := by
  have h1 : (MulAction.stabilizer (ConjAct G) S.z).index =
      (MulAction.orbit (ConjAct G) S.z).ncard := MulAction.index_stabilizer _ _
  have h2 : MulAction.orbit (ConjAct G) S.z = {x : G | IsConj S.z x} := by
    ext x
    rw [Set.mem_setOf_eq, isConj_comm]
    exact ConjAct.mem_orbit_conjAct
  have h3 : Nat.card (centralizer {S.z} : Subgroup G) =
      Nat.card (MulAction.stabilizer (ConjAct G) S.z) :=
    Subgroup.nat_card_centralizer_nat_card_stabilizer S.z
  have h4 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.toConjAct.toEquiv.symm
  have h5 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) S.z)
  have h6 := Subgroup.card_mul_index S.M
  have hpos : 0 < Nat.card S.M := Nat.card_pos
  rw [h2] at h1
  rw [Nat.card_coe_set_eq, ← h1]
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h6, h3, h5, h4]

private def qIncl (S : Setting G) : S.Q →* G := S.M.subtype.comp S.Q.subtype

private theorem mem_M_qIncl (S : Setting G) (q : S.Q) : qIncl S q ∈ S.M := (q : S.M).2

private theorem qIncl_mem_QG (S : Setting G) (q : S.Q) : qIncl S q ∈ S.QG := S.coe_mem_QG q

private theorem qIncl_injective (S : Setting G) : Function.Injective (qIncl S) :=
  S.M.subtype_injective.comp S.Q.subtype_injective

private def conjOutside (S : Setting G) : Set G := {x | IsConj S.z x ∧ x ∉ S.QG}

private theorem conj_mem_conjOutside (S : Setting G) (q : S.Q) {x : G} (hx : x ∈ conjOutside S) :
    qIncl S q * x * (qIncl S q)⁻¹ ∈ conjOutside S := by
  refine ⟨hx.1.trans (isConj_iff.2 ⟨qIncl S q, rfl⟩), fun h => hx.2 ?_⟩
  have := S.conj_mem_QG (S.M.inv_mem (mem_M_qIncl S q)) h
  simpa [mul_assoc] using this

private instance instMulActionConjOutside (S : Setting G) : MulAction S.Q (conjOutside S) where
  smul q x := ⟨qIncl S q * x * (qIncl S q)⁻¹, conj_mem_conjOutside S q x.2⟩
  one_smul x := Subtype.ext (by
    change qIncl S 1 * (x : G) * (qIncl S 1)⁻¹ = x
    simp)
  mul_smul q r x := Subtype.ext (by
    change qIncl S (q * r) * (x : G) * (qIncl S (q * r))⁻¹ =
      qIncl S q * (qIncl S r * (x : G) * (qIncl S r)⁻¹) * (qIncl S q)⁻¹
    simp [mul_assoc])

private theorem mem_stabilizer_conjOutside (S : Setting G) (x : conjOutside S) (q : S.Q) :
    q ∈ MulAction.stabilizer S.Q x ↔ qIncl S q * x * (qIncl S q)⁻¹ = x := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  rfl

variable [Finite G]

private theorem four_dvd_index_of_ne (S : Setting G) (K : Subgroup S.Q) (h1 : K.index ≠ 1)
    (h2 : K.index ≠ 2) : 4 ∣ K.index := by
  have hK : K.index ∣ 2 ^ (1 + 2 * S.width) := S.card_Q_eq ▸ K.index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hK
  rcases j with _ | _ | j
  · exact absurd (by simpa using hj) h1
  · exact absurd (by simpa using hj) h2
  · rw [hj]
    exact ⟨2 ^ j, by ring⟩

private theorem zQ_mem_of_index_eq_two (S : Setting G) {K : Subgroup S.Q} (hK : K.index = 2) :
    S.zQ ∈ K := by
  have hcomm : commutator S.Q ≤ K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h : ⁅a, b⁆ = a * a * (a⁻¹ * b * (a⁻¹ * b)) * (b * b)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact K.mul_mem (K.mul_mem (K.mul_self_mem_of_index_two hK a)
      (K.mul_self_mem_of_index_two hK _)) (K.inv_mem (K.mul_self_mem_of_index_two hK b))
  exact hcomm (S.extraspecial.2.1 ▸ S.zQ_mem_center)

private theorem four_dvd_index_of_not_mem_M (S : Setting G) (x : conjOutside S)
    (hx : (x : G) ∉ S.M) : 4 ∣ (MulAction.stabilizer S.Q x).index := by
  have hz : S.zQ ∉ MulAction.stabilizer S.Q x := by
    intro h
    rw [mem_stabilizer_conjOutside] at h
    exact hx (S.mem_M_iff.2 (mul_inv_eq_iff_eq_mul.1 h).symm)
  refine four_dvd_index_of_ne S _ (fun h => hz ?_) (fun h => hz (zQ_mem_of_index_eq_two S h))
  rw [Subgroup.index_eq_one.1 h]
  exact Subgroup.mem_top _

open Module CFSG.RankThree.OrthogonalInvolutions in
private theorem four_dvd_index_of_mem_M (S : Setting G) (x : conjOutside S) (hxM : (x : G) ∈ S.M)
    (h2 : 2 ≤ finrank (ZMod 2)
      (commSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    4 ∣ (MulAction.stabilizer S.Q x).index := by
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  set K := MulAction.stabilizer S.Q x with hKdef
  set W := fixSpace σ with hW
  have hmem : ∀ k : K, qIncl S k ∈ S.clPre W := by
    intro k
    refine ⟨qIncl_mem_QG S k, ?_⟩
    rw [hW, mem_fixSpace, hσ, S.ρ_cl ⟨x, hxM⟩ (qIncl_mem_QG S k)]
    have hk := (mem_stabilizer_conjOutside S x k).1 k.2
    have hc : (x : G) * qIncl S k * (x : G)⁻¹ = qIncl S k := by
      rw [← mul_inv_eq_iff_eq_mul.1 hk, mul_inv_cancel_right]
    exact congrArg S.cl hc
  have hinj : Function.Injective (fun k : K => (⟨qIncl S k, hmem k⟩ : S.clPre W)) := by
    intro k l hkl
    have h : qIncl S k = qIncl S l := congrArg (fun w : S.clPre W => (w : G)) hkl
    exact Subtype.ext (qIncl_injective S h)
  have hle : Nat.card K ≤ Nat.card (S.clPre W) := Nat.card_le_card_of_injective _ hinj
  have hd : finrank (ZMod 2) (commSpace σ) + finrank (ZMod 2) W = finrank (ZMod 2) S.Qt :=
    finrank_commSpace_add_finrank_fixSpace σ
  have hcardQ : Nat.card S.Q = 2 * 2 ^ finrank (ZMod 2) S.Qt := by
    rw [← S.card_QG_eq_card_Q, S.card_QG_eq, S.card_Qt]
  have hcardW : Nat.card (S.clPre W) = 2 * 2 ^ finrank (ZMod 2) W := by
    rw [S.card_clPre, S.card_submodule]
  have hpow : 2 ^ finrank (ZMod 2) W * 4 ≤ 2 ^ finrank (ZMod 2) S.Qt := by
    calc 2 ^ finrank (ZMod 2) W * 4 = 2 ^ (finrank (ZMod 2) W + 2) := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod := Subgroup.card_mul_index K
  have h4 : 4 ≤ K.index := by
    by_contra hlt
    have hpos : 0 < 2 ^ finrank (ZMod 2) W := pow_pos (by norm_num) _
    rw [not_le] at hlt
    have hle' : Nat.card K ≤ 2 * 2 ^ finrank (ZMod 2) W := hcardW ▸ hle
    nlinarith [Nat.mul_le_mul hle' (Nat.le_of_lt_succ hlt)]
  exact four_dvd_index_of_ne S K (by omega) (by omega)

theorem card_conj_mod_four (S : Setting G)
    (h2 : ∀ y : G, IsConj S.z y → (hyM : y ∈ S.M) → y ∉ S.QG →
      2 ≤ Module.finrank (ZMod 2)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace
          ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    Nat.card {x : G | IsConj S.z x} % 4 = Nat.card {x : G | IsConj S.z x ∧ x ∈ S.QG} % 4 := by
  have hdvd : 4 ∣ Nat.card (conjOutside S) := by
    refine dvd_natCard_of_forall_dvd_ncard_orbit (H := S.Q) fun x => ?_
    rw [← MulAction.index_stabilizer S.Q x]
    by_cases hxM : (x : G) ∈ S.M
    · exact four_dvd_index_of_mem_M S x hxM (h2 x x.2.1 hxM x.2.2)
    · exact four_dvd_index_of_not_mem_M S x hxM
  have hsplit : Nat.card {x : G | IsConj S.z x} =
      Nat.card {x : G | IsConj S.z x ∧ x ∈ S.QG} + Nat.card (conjOutside S) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact (Set.ncard_inter_add_ncard_diff_eq_ncard {x : G | IsConj S.z x} (S.QG : Set G)).symm
  omega

end Conj

end CFSG.GF2Type.Smith1980Orth
