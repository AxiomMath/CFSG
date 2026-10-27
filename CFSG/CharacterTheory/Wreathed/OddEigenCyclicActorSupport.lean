module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralTransferKernel
public import CFSG.CharacterTheory.Wreathed.BrauerWongFocal
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public section

namespace CFSG.Wreathed.OddEigenCyclicActor

open scoped Pointwise

universe u v

theorem oddCore_map_equiv_le {X : Type u} {Y : Type v} [Group X] [Group Y] [Finite X]
    (f : X ≃* Y) :
    (CFSG.oddCore X).map f.toMonoidHom ≤ CFSG.oddCore Y := by
  apply le_sSup
  refine ⟨Subgroup.Normal.map inferInstance _ f.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective f.injective]
  exact CFSG.Wreathed.weakClosure_oddCore_card X

theorem normal_two_complement_subgroupOf {H : Type u} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hodd : Odd (Nat.card N)) (hidx : ∃ k : ℕ, N.index = 2 ^ k) (L : Subgroup H) :
    ∃ M : Subgroup L, M.Normal ∧ Odd (Nat.card M) ∧ ∃ k : ℕ, M.index = 2 ^ k := by
  refine ⟨N.subgroupOf L, Subgroup.Normal.subgroupOf inferInstance L, ?_, ?_⟩
  · apply hodd.of_dvd_nat
    rw [← Subgroup.inf_subgroupOf_right N L,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ L ≤ L)).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  · obtain ⟨k, hk⟩ := hidx
    have hdvd : N.relIndex L ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_index_of_normal N L
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩

theorem normal_two_complement_of_equiv {X : Type u} {Y : Type v} [Group X] [Group Y]
    (f : X ≃* Y) (h : ∃ M : Subgroup X, M.Normal ∧ Odd (Nat.card M) ∧ ∃ k : ℕ, M.index = 2 ^ k) :
    ∃ M : Subgroup Y, M.Normal ∧ Odd (Nat.card M) ∧ ∃ k : ℕ, M.index = 2 ^ k := by
  obtain ⟨M, hM, hodd, k, hk⟩ := h
  refine ⟨M.map f.toMonoidHom, Subgroup.Normal.map hM _ f.surjective, ?_, k, ?_⟩
  · rw [Subgroup.card_map_of_injective f.injective]
    exact hodd
  · rw [show f.toMonoidHom = (f : X →* Y) from rfl, Subgroup.index_map_equiv, hk]

theorem sylow_quaternion_of_equiv {X : Type u} {Y : Type v} [Group X] [Group Y] [Finite X]
    [Finite Y] (n : ℕ) (f : X ≃* Y)
    (h : ∀ P : Sylow 2 X, Nonempty ((P : Subgroup X) ≃* Original.Y (2 ^ n)) ∧
      Nat.card P = 2 * 2 ^ n) :
    ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* Original.Y (2 ^ n)) ∧
      Nat.card P = 2 * 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P
  let P' : Sylow 2 X := P.mapSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  obtain ⟨⟨g⟩, hcard⟩ := h P'
  have e1 : (P : Subgroup Y) ≃* (P' : Subgroup X) :=
    ((P : Subgroup Y).equivMapOfInjective _ f.symm.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)
  exact ⟨⟨e1.trans g⟩, (Nat.card_congr e1.toEquiv).trans hcard⟩

theorem no_index_two_of_equiv {X : Type u} {Y : Type v} [Group X] [Group Y] (f : X ≃* Y)
    (h : ¬ ∃ K₀ : Subgroup X, K₀.Normal ∧ K₀.index = 2) :
    ¬ ∃ K₀ : Subgroup Y, K₀.Normal ∧ K₀.index = 2 := by
  rintro ⟨K₀, hK₀, hidx⟩
  exact h ⟨K₀.comap f.toMonoidHom, hK₀.comap _,
    (Subgroup.index_comap_of_surjective K₀ f.surjective).trans hidx⟩

theorem involution_factorization_of_equiv {X : Type u} {Y : Type v} [Group X] [Group Y]
    [Finite X] (f : X ≃* Y)
    (h : ∀ i : X, orderOf i = 2 → CFSG.oddCore X ⊔ Subgroup.centralizer ({i} : Set X) = ⊤) :
    ∀ i : Y, orderOf i = 2 → CFSG.oddCore Y ⊔ Subgroup.centralizer ({i} : Set Y) = ⊤ := by
  intro i hi
  have hi' : orderOf (f.symm i) = 2 := by rw [MulEquiv.orderOf_eq]; exact hi
  have htop := h (f.symm i) hi'
  apply eq_top_iff.mpr
  intro y _
  have hy : f.symm y ∈ CFSG.oddCore X ⊔ Subgroup.centralizer ({f.symm i} : Set X) :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨o, ho, c, hc, hoc⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  have hfo : f o ∈ CFSG.oddCore Y := oddCore_map_equiv_le f ⟨o, ho, rfl⟩
  have hfc : f c ∈ Subgroup.centralizer ({i} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have h1 := congrArg f hc
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1
  have hyeq : y = f o * f c := by
    rw [← map_mul, hoc, MulEquiv.apply_symm_apply]
  rw [hyeq]
  exact Subgroup.mul_mem_sup hfo hfc

theorem mem_oddCore_of_inverted_of_factorization {K : Type u} [Group K] [Finite K] (i u : K)
    (hfac : CFSG.oddCore K ⊔ Subgroup.centralizer ({i} : Set K) = ⊤)
    (hu : Odd (orderOf u)) (hinv : i * u * i⁻¹ = u⁻¹) : u ∈ CFSG.oddCore K := by
  let π := QuotientGroup.mk' (CFSG.oddCore K)
  have hcen : ∀ k : K, π k * π i = π i * π k := by
    intro k
    have hk : k ∈ CFSG.oddCore K ⊔ Subgroup.centralizer ({i} : Set K) := hfac ▸ Subgroup.mem_top k
    obtain ⟨o, ho, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    have hci : c * i = i * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [map_mul, hπo, one_mul, ← map_mul, ← map_mul, hci]
  have hπu : π u = (π u)⁻¹ := by
    have h1 := congrArg π hinv
    rw [map_mul, map_mul, map_inv, ← hcen u, mul_assoc, mul_inv_cancel, mul_one, map_inv] at h1
    exact h1
  have hsq : π u ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hπu]
    exact mul_inv_cancel _
  have hdvd2 : orderOf (π u) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hdvdu : orderOf (π u) ∣ orderOf u := orderOf_map_dvd π u
  have hone : orderOf (π u) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · rw [h] at hdvdu
      exact absurd (even_iff_two_dvd.mpr hdvdu) (Nat.not_even_iff_odd.mpr hu)
  exact (QuotientGroup.eq_one_iff u).mp (orderOf_eq_one_iff.mp hone)

theorem mem_oddCore_of_normal_two_complement {K : Type u} [Group K] [Finite K]
    (h : ∃ M : Subgroup K, M.Normal ∧ Odd (Nat.card M) ∧ ∃ k : ℕ, M.index = 2 ^ k)
    (u : K) (hu : Odd (orderOf u)) : u ∈ CFSG.oddCore K := by
  obtain ⟨M, hM, hodd, hidx⟩ := h
  have huM : u ∈ M := BrauerWong.mem_of_odd_of_two_power_index M hidx u hu
  exact (le_sSup ⟨hM, hodd⟩ : M ≤ CFSG.oddCore K) huM

theorem centralizer_inf_eq_bot {G : Type u} [Group G] [Finite G] (E A : Subgroup G)
    (hE : E ≠ ⊥) (hEodd : Odd (Nat.card E)) (hAc : IsCyclic A) {n : ℕ}
    (hAcard : Nat.card A = 2 ^ n) (a : G) (haA : a ∈ A) (ha2 : orderOf a = 2)
    (hinv : ∀ x ∈ E, a * x * a⁻¹ = x⁻¹) :
    Subgroup.centralizer (E : Set G) ⊓ A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haK : a ∉ Subgroup.centralizer (E : Set G) := by
    intro haK
    apply hE
    rw [eq_bot_iff]
    intro x hx
    have h1 : a * x * a⁻¹ = x := by
      rw [(Subgroup.mem_centralizer_iff.mp haK x hx).symm, mul_inv_cancel_right]
    have h2 : x = x⁻¹ := h1.symm.trans (hinv x hx)
    have hx2 : x ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h2]
      exact mul_inv_cancel x
    have hxodd : Odd (orderOf x) := hEodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard E hx)
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hone : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hxodd
        exact absurd hxodd (by decide)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  by_contra hne
  have hp : IsPGroup 2 (Subgroup.centralizer (E : Set G) ⊓ A : Subgroup G) :=
    (IsPGroup.of_card hAcard).to_le inf_le_right
  have hdvd : 2 ∣ Nat.card (Subgroup.centralizer (E : Set G) ⊓ A : Subgroup G) := by
    rcases hp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hbA : (b : G) ∈ A := b.property.2
  have hb2 : orderOf (⟨b, hbA⟩ : A) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hb
  have ha2' : orderOf (⟨a, haA⟩ : A) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ha2
  have hba : (⟨b, hbA⟩ : A) = ⟨a, haA⟩ :=
    CFSG.Semidihedral.Principal.eq_of_orderOf_eq_two_of_isCyclic hb2 ha2'
  apply haK
  have h := b.property.1
  rwa [show (b : G) = a from congrArg Subtype.val hba] at h

end CFSG.Wreathed.OddEigenCyclicActor
