module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ComponentClassification.SolMax.FiveFHe

open CFSG Subgroup
open scoped commutatorElement

@[expose] def HasOddA (Y A : Type*) [Group Y] [Group A] : Prop :=
  ∃ S : Subgroup Y, S.IsSubnormal ∧ ⁅S, S⁆ = S ∧
    ∃ ρ : S →* A, Function.Surjective ρ ∧ Odd (Nat.card ρ.ker)

theorem HasOddA.of_mulEquiv {Y Y' A : Type*} [Group Y] [Group Y'] [Group A] (e : Y ≃* Y')
    (h : HasOddA Y A) : HasOddA Y' A := by
  obtain ⟨S, hS, hSp, ρ, hρ, hodd⟩ := h
  let eS : S ≃* S.map e.toMonoidHom := S.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨S.map e.toMonoidHom, hS.map e.surjective, ?_, ρ.comp eS.symm.toMonoidHom,
    hρ.comp eS.symm.surjective, ?_⟩
  · rw [← map_commutator, hSp]
  · have hk : (ρ.comp eS.symm.toMonoidHom).ker = ρ.ker.map eS.toMonoidHom := by
      ext x
      rw [mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
      rfl
    rw [hk, card_map_of_injective eS.injective]
    exact hodd

theorem card_eq_card_ker_mul {S A : Type*} [Group S] [Group A] {ρ : S →* A}
    (hρ : Function.Surjective ρ) : Nat.card S = Nat.card ρ.ker * Nat.card A := by
  rw [← Subgroup.card_mul_index ρ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ,
    card_top]

theorem not_hasOddA_of_not_dvd {Y A : Type*} [Group Y] [Group A] [Finite Y]
    (hA : Nat.card A = 60) (h5 : ¬ 5 ∣ Nat.card Y) : ¬ HasOddA Y A := by
  rintro ⟨S, -, -, ρ, hρ, -⟩
  apply h5
  have h1 := card_eq_card_ker_mul hρ
  rw [hA] at h1
  have h2 : 5 ∣ Nat.card S := ⟨Nat.card ρ.ker * 12, by rw [h1]; ring⟩
  exact h2.trans (card_subgroup_dvd_card S)

theorem not_hasOddA_of_quasisimple {Y D A : Type*} [Group Y] [Group D] [Group A]
    (ι : D →* Y) (hι : Function.Injective ι) (hD : IsQuasisimple D)
    (hperf : ∀ S : Subgroup Y, ⁅S, S⁆ = S → S ≤ ι.range) (hA : ∃ a b : A, a * b ≠ b * a)
    (hcard : ∀ k : ℕ, Nat.card D = k * Nat.card A → ¬ Odd k) : ¬ HasOddA Y A := by
  rintro ⟨S, hS, hSp, ρ, hρ, hodd⟩
  have hSι := hperf S hSp
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hD (hS.comap ι) with h | h
  ·
    have hSr : S = ι.range := le_antisymm hSι fun x ⟨d, hd⟩ => by
      have hdS : d ∈ S.comap ι := h ▸ mem_top d
      rw [mem_comap, hd] at hdS
      exact hdS
    refine hcard (Nat.card ρ.ker) ?_ hodd
    rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, ← hSr]
    exact card_eq_card_ker_mul hρ
  ·
    obtain ⟨a, b, hab⟩ := hA
    obtain ⟨x, rfl⟩ := hρ a
    obtain ⟨y, rfl⟩ := hρ b
    apply hab
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨dx, hdx⟩ := hSι x.2
    obtain ⟨dy, hdy⟩ := hSι y.2
    have hdxS : dx ∈ S.comap ι := by
      rw [mem_comap, hdx]
      exact x.2
    have hc := mem_center_iff.1 (h hdxS) dy
    apply Subtype.ext
    change (x : Y) * y = y * x
    rw [← hdx, ← hdy, ← map_mul, ← map_mul, hc]

theorem le_pPrimeCore_of_isSubnormal_odd {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : N.IsSubnormal) (hodd : Odd (Nat.card N)) : N ≤ pPrimeCore 2 Y := by
  have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hN
  have htop : pPrimeCore 2 N = ⊤ := by
    apply le_antisymm le_top
    apply le_sSup
    exact ⟨normal_top, by
      rw [card_top]
      exact Nat.coprime_two_left.mpr hodd⟩
  rw [htop, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1

theorem exists_mulEquiv_of_hasOddA {Y A : Type*} [Group Y] [Group A] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) (h : HasOddA Y A) :
    ∃ S : Subgroup Y, S.IsSubnormal ∧ Nonempty (S ≃* A) := by
  obtain ⟨S, hS, -, ρ, hρ, hodd⟩ := h
  refine ⟨S, hS, ⟨MulEquiv.ofBijective ρ ⟨?_, hρ⟩⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  have hsn : (ρ.ker.map S.subtype).IsSubnormal := (ρ.normal_ker.isSubnormal).trans' hS
  have hle := le_pPrimeCore_of_isSubnormal_odd hsn
    (by rwa [card_map_of_injective S.subtype_injective])
  rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ S.subtype_injective] at hle
  exact hle

theorem card_mul_card_dvd_of_commute {Y : Type*} [Group Y] [Finite Y] {H K : Subgroup Y}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hdisj : H ⊓ K = ⊥) :
    Nat.card H * Nat.card K ∣ Nat.card Y := by
  have hcomm' : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hcomm m.1 m.2 n.1 n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hcomm') := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype]
    exact disjoint_iff.2 hdisj
  rw [← Nat.card_prod]
  exact Subgroup.card_dvd_of_injective _ hinj

theorem normal_of_isSubnormal_simple {Y : Type*} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : S.IsSubnormal) [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hdvd : ¬ Nat.card S * Nat.card S ∣ Nat.card Y) : S.Normal := by
  obtain ⟨hQ, hZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup hnab
  refine ⟨fun n hn g => ?_⟩
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'
  have hc : IsComponent S' :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv
      (S.equivMapOfInjective _ (MulAut.conj g).injective) hQ, hS.map (MulAut.conj g).surjective⟩
  have hcard : Nat.card S' = Nat.card S := card_map_of_injective (MulAut.conj g).injective
  have hmem : g * n * g⁻¹ ∈ S' := ⟨n, hn, rfl⟩
  rcases LocalCores.component_subnormal_subgroup hc hS with hle | hcomm
  · exact hle hmem
  · exfalso
    apply hdvd
    have hc' : ∀ x ∈ S', ∀ y ∈ S, x * y = y * x := fun x hx y hy => by
      have h1 : ⁅x, y⁆ ∈ ⁅S', S⁆ := commutator_mem_commutator hx hy
      rw [hcomm, mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hdisj : S' ⊓ S = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxS', hxS⟩
      have hxZ : (⟨x, hxS⟩ : S) ∈ center S :=
        mem_center_iff.2 fun y => Subtype.ext (hc' x hxS' y y.2).symm
      rw [hZ, mem_bot] at hxZ
      exact mem_bot.2 (congrArg Subtype.val hxZ)
    have h1 := card_mul_card_dvd_of_commute hc' hdisj
    rwa [hcard] at h1

theorem exists_mul_ne_of_card_sixty {A : Type*} [Group A] [IsSimpleGroup A]
    (hA : Nat.card A = 60) : ∃ a b : A, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have : Fintype A := Fintype.ofFinite A
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := A) 5
    (by rw [← Nat.card_eq_fintype_card, hA]; norm_num)
  have hn : (zpowers x).Normal := ⟨fun n hn g => by
    rw [h g n, mul_inv_cancel_right]
    exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with h1 | h1
  · rw [zpowers_eq_bot] at h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  · have h2 := congrArg (fun H : Subgroup A => Nat.card H) h1
    simp only [Nat.card_zpowers, hx, card_top, hA] at h2
    norm_num at h2

end CFSG.ComponentClassification.SolMax.FiveFHe
