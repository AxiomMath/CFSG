module

public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.Steps.GoldTypeBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReeJ1

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups

namespace GoldType

section Elementary

theorem mul_comm_of_sq_eq_one {G : Type*} [Group G] {T : Subgroup G} (h : ∀ t ∈ T, t ^ 2 = 1)
    {a b : G} (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := by
  have hab := h _ (T.mul_mem ha hb)
  have ha2 := h a ha
  have hb2 := h b hb
  rw [sq] at hab ha2 hb2
  rw [mul_eq_one_iff_eq_inv.mp hab, mul_inv_rev, inv_eq_of_mul_eq_one_right ha2,
    inv_eq_of_mul_eq_one_right hb2]

variable {K : Type} [Group K] [Finite K]

theorem exists_mul_ne_mul_of_four_dvd [IsSimpleGroup K] (h4 : 4 ∣ Nat.card K) :
    ∃ a b : K, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hc
  push Not at hc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (dvd_trans (by norm_num) h4)
  have hN : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
  · have hx1 : x = 1 := by
      have hx' : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rwa [h, Subgroup.mem_bot] at hx'
    rw [hx1, orderOf_one] at hx
    omega
  · have hcard : Nat.card K = 2 := by
      rw [← Subgroup.card_top (G := K), ← h, Nat.card_zpowers, hx]
    rw [hcard] at h4
    norm_num at h4

theorem sylow_of_psl2_odd {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (e : K ≃* PSL(2, GaloisField p f)) (T : Sylow 2 K) :
    Nat.card (T : Subgroup K) = 4 ∧ (∀ t ∈ (T : Subgroup K), t ^ 2 = 1) ∧
      ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x ≠ 1 → y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n⁻¹ * x * n = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite PSL(2, GaloisField p f) := Finite.of_equiv K e.toEquiv
  set T' : Sylow 2 PSL(2, GaloisField p f) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT' : (T' : Subgroup _) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hV := CFSG.Walter.psl2_odd_sylow_two_isKleinFour hp hf h8 T'
  have hcard : Nat.card (T : Subgroup K) = 4 := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, ← hT']
    exact hV.card_four
  have hexp : ∀ t ∈ (T : Subgroup K), t ^ 2 = 1 := by
    intro t ht
    have hmem : e t ∈ (T' : Subgroup _) := by rw [hT']; exact ⟨t, ht, rfl⟩
    have h := Monoid.pow_exponent_eq_one (⟨e t, hmem⟩ : (T' : Subgroup _))
    rw [hV.exponent_two] at h
    apply e.injective
    rw [map_pow, map_one]
    simpa using congrArg Subtype.val h
  refine ⟨hcard, hexp, fun x hx y hy hx1 hy1 => ?_⟩
  have : IsMulCommutative (T : Subgroup K) :=
    ⟨⟨fun a b => Subtype.ext (mul_comm_of_sq_eq_one hexp a.2 b.2)⟩⟩
  have hord : ∀ z ∈ (T : Subgroup K), z ≠ 1 → orderOf (e z) = 2 := fun z hz hz1 =>
    orderOf_eq_prime (by rw [← map_pow, hexp z hz, map_one]) (by simpa using hz1)
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.Walter.psl2_odd_isConj_of_orderOf_eq_two hp hf (hord x hx hx1) (hord y hy hy1))
  have hg : (e.symm c⁻¹)⁻¹ * x * e.symm c⁻¹ = y := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv, hc]
  obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem T x (e.symm c⁻¹) hx (hg ▸ hy)
  exact ⟨n, hn, hgn.symm.trans hg⟩

theorem sylow_of_ree_or_j1
    [IsSimpleGroup K]
    (h : (∃ m : ℕ, 1 ≤ m ∧ Nat.card K = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (K ≃* goldschmidtJ1)) (T : Sylow 2 K) :
    (∃ a b : K, a * b ≠ b * a) ∧ Nat.card (T : Subgroup K) = 8 ∧
      IsMulCommutative (T : Subgroup K) ∧ ∀ t ∈ (T : Subgroup K), t ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata : (∃ u, Odd u ∧ Nat.card K = 8 * u) ∧ Nat.card K ≠ 2520 ∧
      ∀ p k : ℕ, p.Prime → Odd p → 1 ≤ k → Nat.card K ≠ p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
    rcases h with ⟨m, hm1, hm⟩ | he
    · rw [hm]
      exact ⟨CFSG.ComponentClassification.WalterSchur.ordRee_eq_eight_mul m,
        CFSG.ComponentClassification.WalterSchur.ordRee_ne_2520 m, fun p k hp hpodd hk =>
          CFSG.ComponentClassification.WalterSchur.ordRee_ne_psl2 hm1 hp hpodd hk⟩
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv,
        CFSG.ComponentClassification.WalterSchur.goldschmidtJ1_eq_walterJ1,
        CFSG.Walter.J1Props.card_walterJ1]
      exact ⟨⟨21945, by decide, by norm_num⟩, by norm_num, fun p k _ _ _ =>
        CFSG.ComponentClassification.WalterSchur.j1_ne_psl2 _⟩
  obtain ⟨⟨u, hu, hu8⟩, hA7, hL2⟩ := hdata
  have hnonab := exists_mul_ne_mul_of_four_dvd (K := K) ⟨2 * u, by rw [hu8]; ring⟩
  have hT8 : Nat.card (T : Subgroup K) = 8 := by
    rw [T.card_eq_multiplicity, hu8,
      CFSG.ComponentClassification.WalterSchur.factorization_two_eight_mul hu]
    norm_num
  have hTc :=
    CFSG.ComponentClassification.WalterSchur.isMulCommutative_of_card_eight hnonab T hT8 hA7 hL2
  refine ⟨hnonab, hT8, hTc, fun t ht => ?_⟩
  rw [sq]
  exact CFSG.ComponentClassification.WalterSchur.mul_self_eq_one_of_abelian_card_eight hnonab T
    hTc hT8 t ht

theorem elementary_of_clauses
    [IsSimpleGroup K]
    (hK : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (K ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card K = ordRee (3 ^ (2 * m + 1))) ∨ Nonempty (K ≃* goldschmidtJ1))
    (T : Sylow 2 K) :
    IsMulCommutative (T : Subgroup K) ∧ (∀ t ∈ (T : Subgroup K), t ^ 2 = 1) ∧
      4 ≤ Nat.card (T : Subgroup K) ∧
      ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x ≠ 1 → y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n⁻¹ * x * n = y := by
  rcases hK with ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ | h
  · obtain ⟨hcard, hexp, htrans⟩ := sylow_of_psl2_odd hpo hf h8 e T
    exact ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_sq_eq_one hexp a.2 b.2)⟩⟩, hexp,
      hcard.ge, htrans⟩
  · obtain ⟨hnonab, hT8, hTc, hexp⟩ := sylow_of_ree_or_j1 h T
    refine ⟨hTc, hexp, by omega, fun x hx y hy hx1 hy1 => ?_⟩
    obtain ⟨n, hn, hxy⟩ :=
      (CFSG.Walter.sylow_two_card_eight_transitive hnonab T hTc hT8).1 x hx hx1 y hy hy1
    exact ⟨n⁻¹, (Subgroup.normalizer _).inv_mem hn, by rw [inv_inv]; exact hxy⟩

end Elementary

end GoldType

open GoldType

theorem N11a
    : S_N11a := by
  intro K _ _ _ hK T _
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h
  · have hTc := isMulCommutative_of_psl2_even (by omega) e T
    exact ⟨fun _ t ht => sq_eq_one_of_bender_of_comm (Or.inl ⟨f, by omega, ⟨e⟩⟩) T hTc ht,
      fun h => absurd hTc h⟩
  · exact ⟨fun hTc t ht => sq_eq_one_of_bender_of_comm (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)) T hTc ht,
      fun _ => Or.inl ⟨n, hn, ⟨e⟩⟩⟩
  · exact ⟨fun hTc t ht => sq_eq_one_of_bender_of_comm (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)) T hTc ht,
      fun _ => Or.inr ⟨f, hf, ⟨e⟩⟩⟩
  · obtain ⟨hTc, hexp, -, -⟩ := elementary_of_clauses h T
    exact ⟨fun _ => hexp, fun h => absurd hTc h⟩

theorem N11b
    : S_N11b := by
  intro K _ _ _ hK T _
  rcases hK with ⟨f, hf, he⟩ | ⟨n, hn, he⟩ | ⟨f, hf, he⟩ | h
  · exact omega1_props_of_bender (Or.inl ⟨f, by omega, he⟩) T
  · exact omega1_props_of_bender (Or.inr (Or.inr ⟨n, hn, he⟩)) T
  · exact omega1_props_of_bender (Or.inr (Or.inl ⟨f, hf, he⟩)) T
  · obtain ⟨-, hexp, h4, htrans⟩ := elementary_of_clauses h T
    rw [omega1_eq_self hexp]
    exact ⟨h4, htrans⟩

theorem N11c : S_N11c := by
  intro K _ _ hK T
  have hKB : fusionIsBenderGroup K := by
    rcases hK with ⟨n, hn, he⟩ | ⟨f, hf, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨f, hf, he⟩)
  exact ⟨omega1_eq_sylowCenter_of_bender hKB T, commutator_le_sylowCenter_of_bender hKB T⟩

theorem N12 :
    ∀ (X : Type) [Group X] [Finite X], fusionIsBenderGroup X → ∀ S : Sylow 2 X,
      Subgroup.centralizer ((S : Subgroup X) : Set X) ≤ (S : Subgroup X) :=
  fun _ _ _ hX S => centralizer_le_of_bender hX S

end CFSG.Goldschmidt
