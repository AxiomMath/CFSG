module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
import CFSG.Sporadic.Catalog.Finiteness
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Open

instance finite_carrier_B : Finite (NativeSporadic.Carrier .B) :=
  CFSG.Sporadic.Catalog.finite_carrier_of_ne_M .B (by decide)

noncomputable def elemQPowHom {q : ℕ} [NeZero q] {C : Type*} [CommGroup C] {r : ℕ}
    (v : Fin r → C) (hv : ∀ i, v i ^ q = 1) :
    (Fin r → Multiplicative (ZMod q)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

open scoped IsMulCommutative in
theorem exists_elemAbelian_of_commuting_pow {G : Type*} [Group G] {q : ℕ} [NeZero q] {r : ℕ}
    (u : Fin r → G) (hpow : ∀ i, u i ^ q = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → ZMod q, a ≠ 0 →
      (List.ofFn fun i => u i ^ (a i).val).prod ≠ 1) :
    ∃ E : Subgroup G, IsElemAbelian q E ∧ Nat.card E = q ^ r := by
  set C := Subgroup.closure (Set.range u)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ q = 1 := fun i => Subtype.ext (by simpa [v] using hpow i)
  let φ : (Fin r → Multiplicative (ZMod q)) →* G := C.subtype.comp (elemQPowHom v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, elemQPowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  refine CFSG.SectionRank.exists_isElemAbelian_of_injective (p := q) (k := r) mul_comm
    (fun a => ?_) ?_ φ ?_
  · funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · simp
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => Multiplicative.toAdd (a i)) (fun h0 => hne ?_) ha
    funext i
    exact Multiplicative.toAdd.injective (congrFun h0 i)

open CFSG.Monster.B.Pinned in
theorem three_le_pRank_of_commData {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {n : ℕ} {q : Fin n → G} {z : G} {M : Matrix (Fin n) (Fin n) (ZMod p)}
    (hD : CommData p q z M) {i j : Fin n} (hij : i ≠ j) (hM : M i j = 0) :
    3 ≤ Open.pRank p (⊤ : Subgroup G) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hn, e, he, -⟩ := hD.quotient_equiv
  have hz5 : z ^ p = 1 := by rw [← hD.orderOf_z]; exact pow_orderOf_eq_one z
  have c01 : Commute z (q i) := (hD.comm_z i).symm
  have c02 : Commute z (q j) := (hD.comm_z j).symm
  have c12 : Commute (q i) (q j) := by
    have h1 : bcomm (q i) (q j) = 1 := by rw [hD.bcomm_q i j, hM]; simp
    exact bcomm_eq_one_iff.1 h1
  let u : Fin 3 → G := ![z, q i, q j]
  have hpow : ∀ k, u k ^ p = 1 := by
    intro k
    fin_cases k
    · exact hz5
    · exact hD.pow_q i
    · exact hD.pow_q j
  have hcomm : ∀ a b : Fin 3, Commute (u a) (u b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact Commute.refl _
    · exact c01
    · exact c02
    · exact c01.symm
    · exact Commute.refl _
    · exact c12
    · exact c02.symm
    · exact c12.symm
    · exact Commute.refl _
  have hker : ∀ a : Fin 3 → ZMod p, a ≠ 0 → (List.ofFn fun k => u k ^ (a k).val).prod ≠ 1 := by
    intro a ha h
    apply ha
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h
    have hQ : (⟨z, hD.mem_z⟩ : Subgroup.closure (Set.range q)) ^ (a 0).val *
        (qQ q i ^ (a 1).val * qQ q j ^ (a 2).val) = 1 := by
      apply Subtype.ext
      simpa [u] using h
    let ψ : (Subgroup.closure (Set.range q)) →* Multiplicative (Fin n → ZMod p) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (zQ q z))
    have hψz : ψ ⟨z, hD.mem_z⟩ = 1 := by
      have hmem : (⟨z, hD.mem_z⟩ : Subgroup.closure (Set.range q)) ∈ zQ q z :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers z)
      change e (QuotientGroup.mk (⟨z, hD.mem_z⟩ : Subgroup.closure (Set.range q))) = 1
      rw [(QuotientGroup.eq_one_iff _).2 hmem, map_one]
    have hψq : ∀ k, ψ (qQ q k) = Multiplicative.ofAdd (Pi.single k 1) := fun k => he k
    have h2 := congrArg ψ hQ
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hψz, hψq, hψq, map_one] at h2
    simp only [one_pow, one_mul] at h2
    have h3 := congrArg Multiplicative.toAdd h2
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_one] at h3
    have ha1 : a 1 = 0 := by
      have hi : (a 1).val • (Pi.single i (1 : ZMod p) : Fin n → ZMod p) i +
          (a 2).val • (Pi.single j (1 : ZMod p) : Fin n → ZMod p) i = 0 := congrFun h3 i
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_zero, add_zero, nsmul_eq_mul,
        mul_one, ZMod.natCast_zmod_val] at hi
      exact hi
    have ha2 : a 2 = 0 := by
      have hj : (a 1).val • (Pi.single i (1 : ZMod p) : Fin n → ZMod p) j +
          (a 2).val • (Pi.single j (1 : ZMod p) : Fin n → ZMod p) j = 0 := congrFun h3 j
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, smul_zero, zero_add,
        nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at hj
      exact hj
    have ha0 : a 0 = 0 := by
      rw [ha1, ha2, ZMod.val_zero, pow_zero, pow_zero, mul_one] at hQ
      have hz : z ^ (a 0).val = 1 := by
        have := congrArg Subtype.val hQ
        simpa using this
      have hdvd : p ∣ (a 0).val := by
        have := orderOf_dvd_of_pow_eq_one hz
        rwa [hD.orderOf_z] at this
      exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
    funext k
    fin_cases k
    · exact ha0
    · exact ha1
    · exact ha2
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_of_commuting_pow u hpow hcomm hker
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hE hc

end CFSG.AGLEmbedding
