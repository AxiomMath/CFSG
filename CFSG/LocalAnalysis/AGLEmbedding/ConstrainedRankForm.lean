module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalRankTwo
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

variable {S : Type*} [Group S]

theorem prime_mul_card_le_of_lt [Finite S] {p : ℕ} [Fact p.Prime] {H K : Subgroup S}
    (hK : IsPGroup p K) (hHK : H < K) : p * Nat.card H ≤ Nat.card K := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hK
  have hdvd : Nat.card H ∣ p ^ m := hm ▸ Subgroup.card_dvd_of_le hHK.le
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjm : j < m := by
    refine lt_of_le_of_ne hj fun hjm => hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le ?_)
    rw [hm, hjeq, hjm]
  rw [hm, hjeq, ← pow_succ']
  exact Nat.pow_le_pow_right hp.pos hjm

theorem isElemAbelian_zpowers {p : ℕ} {a : S} (ha : a ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha

theorem exists_commutator_monoidHom (hcomm : commutator S ≤ Subgroup.center S) (a : S) :
    ∃ γ : S →* S, ∀ x, γ x = ⁅a, x⁆ := by
  refine ⟨{ toFun := fun x => ⁅a, x⁆
            map_one' := commutatorElement_one_right a
            map_mul' := fun x y => ?_ }, fun _ => rfl⟩
  have hc := Subgroup.mem_center_iff.mp
    (hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top y))) x
  change ⁅a, x * y⁆ = ⁅a, x⁆ * ⁅a, y⁆
  simp only [commutatorElement_def] at hc ⊢
  calc a * (x * y) * a⁻¹ * (x * y)⁻¹ = a * x * a⁻¹ * x⁻¹ * (x * (a * y * a⁻¹ * y⁻¹)) * x⁻¹ := by
        group
    _ = a * x * a⁻¹ * x⁻¹ * (a * y * a⁻¹ * y⁻¹ * x) * x⁻¹ := by rw [hc]
    _ = a * x * a⁻¹ * x⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group

theorem exists_large_power_kernel [Finite S] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcomm : commutator S ≤ Subgroup.center S) (hpow : ∀ s : S, s ^ p ∈ Subgroup.center S)
    (hlarge : p ^ 4 ≤ Nat.card (S ⧸ Subgroup.center S)) :
    ∃ φ : S →* S, (∀ x, φ x = x ^ p) ∧ φ.ker.index ≤ Nat.card (Subgroup.center S) ∧
      p ^ 4 ≤ Nat.card φ.ker := by
  obtain ⟨φ, hφ⟩ := odd_prime_class_two_power_monoidHom p hp2 hcomm hpow
  have hindex : φ.ker.index ≤ Nat.card (Subgroup.center S) := by
    rw [Subgroup.index_ker]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    exact hpow x
  refine ⟨φ, hφ, hindex, Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := Subgroup.center S))⟩
  calc p ^ 4 * Nat.card (Subgroup.center S)
      ≤ Nat.card (S ⧸ Subgroup.center S) * Nat.card (Subgroup.center S) :=
        Nat.mul_le_mul_right _ hlarge
    _ = Nat.card φ.ker * φ.ker.index := by
        rw [φ.ker.card_mul_index,
          Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)]
    _ ≤ Nat.card φ.ker * Nat.card (Subgroup.center S) := Nat.mul_le_mul_left _ hindex

theorem card_center_quotient_lt_pow_four [Finite S] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hS : IsPGroup p S) (hcyc : IsCyclic (Subgroup.center S))
    (hcomm : commutator S ≤ Subgroup.center S) (hpow : ∀ s : S, s ^ p ∈ Subgroup.center S)
    (hrank : pRank p (⊤ : Subgroup S) ≤ 2) :
    Nat.card (S ⧸ Subgroup.center S) < p ^ 4 := by
  have hp := (Fact.out : p.Prime)
  by_contra hlarge
  rw [not_lt] at hlarge
  have hnt : Nontrivial S := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    calc 1 < p ^ 4 := Nat.one_lt_pow (by norm_num) hp.one_lt
      _ ≤ Nat.card (S ⧸ Subgroup.center S) := hlarge
      _ ≤ Nat.card S := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)]
          exact Nat.le_mul_of_pos_right _ Nat.card_pos
  obtain ⟨φ, hφ, hΩindex, hΩcard⟩ := exists_large_power_kernel hp2 hcomm hpow hlarge
  have hmemΩ : ∀ x, x ∈ φ.ker ↔ x ^ p = 1 := fun x => by rw [MonoidHom.mem_ker, hφ]
  have hNcard : Nat.card (centralPrimeTorsion p S) = p :=
    centralPrimeTorsion_card_eq_prime_of_cyclic_center p hS hcyc hnt
  have hmemN := mem_centralPrimeTorsion (source := S) p
  have hNnormal : (centralPrimeTorsion p S).Normal := by
    have : (centralPrimeTorsion p S).Characteristic := centralPrimeTorsion_characteristic p
    infer_instance
  obtain ⟨a, haΩ, haZ⟩ : ∃ a ∈ φ.ker, a ∉ Subgroup.center S := by
    by_contra hnone
    push Not at hnone
    have hle : φ.ker ≤ centralPrimeTorsion p S :=
      fun x hx => (hmemN x).mpr ⟨hnone x hx, (hmemΩ x).mp hx⟩
    have hcard := (hΩcard.trans (Subgroup.card_le_of_le hle)).trans_eq hNcard
    have hlt : p < p ^ 4 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd hcard (not_le.mpr hlt)
  have hap : a ^ p = 1 := (hmemΩ a).mp haΩ
  obtain ⟨γ, hγ⟩ := exists_commutator_monoidHom hcomm a
  have hγindex : γ.ker.index ≤ p := by
    rw [Subgroup.index_ker, ← hNcard]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    rw [hγ]
    refine (hmemN _).mpr ⟨hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top x)), ?_⟩
    rw [← class_two_commutator_pow_left hcomm, hap, commutatorElement_one_left]
  have hTcard : p ^ 3 ≤ Nat.card (φ.ker ⊓ γ.ker : Subgroup S) := by
    have hTindex : (φ.ker ⊓ γ.ker).index ≤ φ.ker.index * p :=
      Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ hγindex)
    have hmul : Nat.card φ.ker * φ.ker.index ≤
        Nat.card (φ.ker ⊓ γ.ker : Subgroup S) * p * φ.ker.index := by
      calc Nat.card φ.ker * φ.ker.index
          = Nat.card (φ.ker ⊓ γ.ker : Subgroup S) * (φ.ker ⊓ γ.ker).index := by
            rw [Subgroup.card_mul_index, Subgroup.card_mul_index]
        _ ≤ Nat.card (φ.ker ⊓ γ.ker : Subgroup S) * (φ.ker.index * p) :=
            Nat.mul_le_mul_left _ hTindex
        _ = _ := by ring
    have hle := Nat.le_of_mul_le_mul_right hmul
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    refine Nat.le_of_mul_le_mul_right ?_ hp.pos
    rw [← pow_succ]
    exact hΩcard.trans hle
  have hDcard : Nat.card (Subgroup.zpowers a ⊔ centralPrimeTorsion p S : Subgroup S) ≤ p * p := by
    have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S) (centralPrimeTorsion p S)
      (Subgroup.zpowers a ⊔ centralPrimeTorsion p S) bot_le le_sup_right
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
      Subgroup.relIndex_sup_right] at h
    rw [← h, hNcard]
    apply Nat.mul_le_mul_left
    have hdvd := (centralPrimeTorsion p S).relIndex_dvd_card (Subgroup.zpowers a)
    rw [Nat.card_zpowers] at hdvd
    exact Nat.le_of_dvd hp.pos (hdvd.trans (orderOf_dvd_of_pow_eq_one hap))
  obtain ⟨b, hbT, hbD⟩ : ∃ b ∈ (φ.ker ⊓ γ.ker : Subgroup S),
      b ∉ (Subgroup.zpowers a ⊔ centralPrimeTorsion p S : Subgroup S) := by
    by_contra hnone
    push Not at hnone
    have hle := hTcard.trans ((Subgroup.card_le_of_le hnone).trans hDcard)
    have hlt : p * p < p ^ 3 := by
      rw [← sq]
      exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd hle (not_le.mpr hlt)
  have hbp : b ^ p = 1 := (hmemΩ b).mp hbT.1
  have hab : Commute a b := by
    have hb : b ∈ γ.ker := hbT.2
    rw [MonoidHom.mem_ker, hγ] at hb
    exact commutatorElement_eq_one_iff_mul_comm.mp hb
  have hNcentral : ∀ x ∈ centralPrimeTorsion p S, ∀ y : S, y * x = x * y :=
    fun x hx y => Subgroup.mem_center_iff.mp ((hmemN x).mp hx).1 y
  have hDel : IsElemAbelian p (Subgroup.zpowers a ⊔ centralPrimeTorsion p S) :=
    elementary_abelian_sup_of_commuting p (isElemAbelian_zpowers hap)
      (centralPrimeTorsion_elementary p)
      fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => (hNcentral y hy x).symm
  have hcommb : Subgroup.zpowers a ⊔ centralPrimeTorsion p S ≤
      Subgroup.centralizer (Subgroup.zpowers b : Set S) := by
    apply sup_le
    · intro x hx
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((hab.zpow_left k).zpow_right m).eq.symm
    · exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun y _ => hNcentral x hx y
  have hEel := elementary_abelian_sup_of_commuting p hDel (isElemAbelian_zpowers hbp) hcommb
  have hND : centralPrimeTorsion p S < Subgroup.zpowers a ⊔ centralPrimeTorsion p S := by
    refine lt_of_le_of_ne le_sup_right fun h => haZ ((hmemN a).mp ?_).1
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hDE : Subgroup.zpowers a ⊔ centralPrimeTorsion p S <
      Subgroup.zpowers a ⊔ centralPrimeTorsion p S ⊔ Subgroup.zpowers b := by
    refine lt_of_le_of_ne le_sup_left fun h => hbD ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hEcard : p * (p * p) ≤ Nat.card
      (Subgroup.zpowers a ⊔ centralPrimeTorsion p S ⊔ Subgroup.zpowers b : Subgroup S) := by
    have hD := prime_mul_card_le_of_lt (hS.to_subgroup _) hND
    rw [hNcard] at hD
    exact (Nat.mul_le_mul_left p hD).trans (prime_mul_card_le_of_lt (hS.to_subgroup _) hDE)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hS.to_subgroup
    (Subgroup.zpowers a ⊔ centralPrimeTorsion p S ⊔ Subgroup.zpowers b))
  have hk3 : 3 ≤ k := by
    rw [hk] at hEcard
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    calc p ^ 3 = p * (p * p) := by ring
      _ ≤ p ^ k := hEcard
  have hkrank : k ≤ pRank p (⊤ : Subgroup S) :=
    le_csSup (pRank_bddAbove p hp ⊤) ⟨_, le_top, hEel, hk⟩
  omega

theorem exists_card_center_quotient_eq_pow_add_self [Finite S] {p : ℕ} [Fact p.Prime]
    (hS : IsPGroup p S) (hcyc : IsCyclic (Subgroup.center S)) (hnt : Nontrivial S)
    (hcomm : commutator S ≤ Subgroup.center S) (hpow : ∀ s : S, s ^ p ∈ Subgroup.center S) :
    ∃ n, Nat.card (S ⧸ Subgroup.center S) = p ^ (n + n) := by
  let : IsMulCommutative (S ⧸ Subgroup.center S) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let : CommGroup (S ⧸ Subgroup.center S) := IsMulCommutative.instCommGroup
  let := class_two_prime_center_quotient_module p hpow
  obtain ⟨form, halt, hnd, _⟩ :=
    cyclic_center_prime_quotient_has_nondegenerate_alternating_form p hS hcyc hnt hcomm hpow
  obtain ⟨n, hn⟩ := alternating_nondegenerate_form_finrank_even form halt hnd
  refine ⟨n, ?_⟩
  rw [← hn, FiniteField.pow_finrank_eq_natCard p (Additive (S ⧸ Subgroup.center S))]
  rfl

theorem card_center_quotient_eq_one_or_sq [Finite S] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hS : IsPGroup p S) (hcyc : IsCyclic (Subgroup.center S))
    (hcomm : commutator S ≤ Subgroup.center S) (hpow : ∀ s : S, s ^ p ∈ Subgroup.center S)
    (hrank : pRank p (⊤ : Subgroup S) ≤ 2) :
    Nat.card (S ⧸ Subgroup.center S) = 1 ∨ Nat.card (S ⧸ Subgroup.center S) = p ^ 2 := by
  rcases subsingleton_or_nontrivial S with hsub | hnt
  · exact Or.inl Nat.card_unique
  obtain ⟨n, hn⟩ := exists_card_center_quotient_eq_pow_add_self hS hcyc hnt hcomm hpow
  have hlt := card_center_quotient_lt_pow_four hp2 hS hcyc hcomm hpow hrank
  rw [hn] at hlt ⊢
  have hn2 : n + n < 4 := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hlt
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · exact Or.inl (pow_zero p)
  · exact Or.inr rfl

end CFSG.AGLEmbedding
