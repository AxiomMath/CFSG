module

public import CFSG.Dihedral.FourgroupFixedOrder
public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.BrauerLinearThree

open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_pow_eq_of_odd_orderOf {x : G} (hx : Odd (orderOf x)) : ∃ k : ℕ, (x ^ 2) ^ k = x := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]

theorem mem_of_sq_mem {H : Subgroup G} {x : G} (hx : Odd (orderOf x)) (h : x ^ 2 ∈ H) : x ∈ H := by
  obtain ⟨k, hk⟩ := exists_pow_eq_of_odd_orderOf hx
  rw [← hk]
  exact H.pow_mem h k

theorem eq_one_of_sq_eq_one_of_odd {x : G} (hx : Odd (orderOf x)) (h : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := exists_pow_eq_of_odd_orderOf hx
  rw [← hk, h, one_pow]

theorem odd_orderOf_of_mem {H : Subgroup G} [Finite H] (hH : Odd (Nat.card H)) {x : G}
    (hx : x ∈ H) : Odd (orderOf x) := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : H)
  rw [Subgroup.orderOf_mk] at h
  exact hH.of_dvd_nat h

theorem inv_eq_of_fixedPointFree_involution {H : Subgroup G} [Finite H] {t : G} (ht : t * t = 1)
    (hnorm : ∀ h ∈ H, t * h * t⁻¹ ∈ H)
    (hfree : ∀ h ∈ H, t * h * t⁻¹ = h → h = 1) : ∀ h ∈ H, t * h * t⁻¹ = h⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let σ : H →* H :=
    { toFun := fun h => ⟨t * h * t⁻¹, hnorm h h.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hσ : Function.Involutive σ := by
    intro h
    apply Subtype.ext
    change t * (t * h * t⁻¹) * t⁻¹ = h
    rw [ht']
    calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
      _ = h := by rw [ht]; group
  have hfp : MonoidHom.FixedPointFree σ := by
    intro h hh
    apply Subtype.ext
    exact hfree h h.2 (congrArg Subtype.val hh)
  intro h hh
  have := congrFun (hfp.coe_eq_inv_of_involutive hσ) ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem mem_normalizer_of_involution {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    (hM : ∀ m ∈ M, t * m * t⁻¹ ∈ M) : t ∈ Subgroup.normalizer (M : Set G) := by
  have h2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h2
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact hM m
  · intro hm
    have := hM _ hm
    rw [ht'] at this
    have e : m = t * (t * m * t) * t := by
      calc m = (t * t) * m * (t * t) := by rw [h2]; group
        _ = t * (t * m * t) * t := by group
    rw [e]
    exact this

theorem card_mul_card_sq_eq_of_four [Finite G] {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) (M : Subgroup G) (hM : Odd (Nat.card M))
    (hMa : ∀ m ∈ M, a * m * a⁻¹ ∈ M) (hMb : ∀ m ∈ M, b * m * b⁻¹ ∈ M) :
    Nat.card M *
        Nat.card (M ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} : Subgroup G) ^ 2 =
      Nat.card (M ⊓ Subgroup.centralizer {a} : Subgroup G) *
        Nat.card (M ⊓ Subgroup.centralizer {b} : Subgroup G) *
        Nat.card (M ⊓ Subgroup.centralizer {a * b} : Subgroup G) := by
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
  have hdisj : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    rw [Subgroup.disjoint_def]
    intro x hxa hxb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxb
    have hai : a ^ i = 1 ∨ a ^ i = a := by
      have := zpow_mod_orderOf a i
      rw [ha] at this
      simp only [Nat.cast_ofNat] at this
      rcases Int.emod_two_eq_zero_or_one i with h | h
      · left; rw [← this, h, zpow_zero]
      · right; rw [← this, h, zpow_one]
    have hbj : b ^ j = 1 ∨ b ^ j = b := by
      have := zpow_mod_orderOf b j
      rw [hb] at this
      simp only [Nat.cast_ofNat] at this
      rcases Int.emod_two_eq_zero_or_one j with h | h
      · left; rw [← this, h, zpow_zero]
      · right; rw [← this, h, zpow_one]
    rcases hai with h | h
    · exact h
    · rw [h] at hj ⊢
      rcases hbj with h' | h'
      · exact absurd (hj.symm.trans h') ha1
      · exact absurd (hj.symm.trans h') hne
  let V := Subgroup.closure ({a, b} : Set G)
  have hV : IsKleinFour V :=
    CFSG.Wreathed.isKleinFour_closure_pair ha hb hab hdisj
  have hsolv : Group.IsSolvable M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hM
  have hnorm : CFSG.DihedralBlueprint.NormalizedBy M V := by
    rw [CFSG.DihedralBlueprint.NormalizedBy, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact mem_normalizer_of_involution ha hMa
    · rw [Set.mem_singleton_iff.mp hx]
      exact mem_normalizer_of_involution hb hMb
  have haV : a ∈ V := Subgroup.subset_closure (Set.mem_insert a _)
  have hbV : b ∈ V := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have h := CFSG.DihedralBlueprint.ambient_fourgroup_fixed_order_identity V M hV hM hsolv hnorm
    a b haV hbV ha1 hb1 hne
  have hcV : (M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) =
      M ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := by
    rw [Subgroup.centralizer_closure, inf_assoc]
    congr 1
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [hcV] at h
  exact h


theorem exists_sylow_le_of_factorization_eq {H : Type} [Group H] [Finite H] (r : ℕ)
    [Fact r.Prime] (A : Subgroup H)
    (hA : (Nat.card A).factorization r = (Nat.card H).factorization r) :
    ∃ R : Sylow r H, (R : Subgroup H) ≤ A := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) r
    (Nat.ordProj_dvd (Nat.card A) r)
  refine ⟨Sylow.ofCard (K.map A.subtype) ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hK, hA]
  · rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le K

theorem sylow_normal_of_complement_without_fusion {H : Type} [Group H] [Finite H] {p : ℕ}
    [hp : Fact p.Prime] (A : Subgroup H) (hAp : Nat.Coprime p (Nat.card A)) {k : ℕ}
    (hcard : Nat.card H = Nat.card A * p ^ k)
    (hfus : ∀ a ∈ A, ∀ g : H, g * a * g⁻¹ ∈ A → g * a * g⁻¹ = a) (P : Sylow p H) :
    (P : Subgroup H).Normal := by
  classical
  have hK : ∀ r ∈ (Nat.card A).primeFactors, ∃ K : Subgroup H, K.Normal ∧
      ¬ r ∣ Nat.card K ∧ (P : Subgroup H) ≤ K := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have : Fact r.Prime := ⟨hrp⟩
    have hrne : r ≠ p := by
      rintro rfl
      exact hrp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hAp (Nat.dvd_of_mem_primeFactors hr))
    have hfac : (Nat.card A).factorization r = (Nat.card H).factorization r := by
      rw [hcard, Nat.factorization_mul (Nat.card_pos (α := A)).ne' (pow_pos hp.out.pos k).ne',
        Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hp.out.factorization,
        Finsupp.single_apply, ite_eq_right hrne.symm]
      simp
    obtain ⟨R, hRA⟩ := exists_sylow_le_of_factorization_eq r A hfac
    have hR : Subgroup.normalizer (R : Set H) ≤ Subgroup.centralizer (R : Set H) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hnx : n * x * n⁻¹ ∈ (R : Subgroup H) := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
      have := hfus x (hRA hx) n (hRA hnx)
      calc x * n = (n * x * n⁻¹) * n := by rw [this]
        _ = n * x := by group
    have hcomp := MonoidHom.ker_transferSylow_isComplement' R hR
    refine ⟨(MonoidHom.transferSylow R hR).ker, MonoidHom.normal_ker _, ?_, ?_⟩
    · intro hdvd
      have hmul := hcomp.card_mul_card
      have hRcard := R.card_eq_multiplicity
      set e := (Nat.card H).factorization r with he
      obtain ⟨c, hc⟩ := hdvd
      have h1 : r ^ (e + 1) ∣ Nat.card H := ⟨c, by rw [← hmul, hRcard, hc, pow_succ]; ring⟩
      exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hrp h1
    ·
      intro x hx
      rw [MonoidHom.mem_ker]
      have hxp : x ^ (p ^ (Nat.card H).factorization p) = 1 := by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup H))
        rw [Subgroup.orderOf_mk, P.card_eq_multiplicity] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      have hyr : (MonoidHom.transferSylow R hR x) ^ (r ^ (Nat.card H).factorization r) = 1 := by
        have := orderOf_dvd_natCard (MonoidHom.transferSylow R hR x)
        rw [R.card_eq_multiplicity] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      have hyp : (MonoidHom.transferSylow R hR x) ^ (p ^ (Nat.card H).factorization p) = 1 := by
        rw [← map_pow, hxp, map_one]
      have hcop : Nat.Coprime (p ^ (Nat.card H).factorization p)
          (r ^ (Nat.card H).factorization r) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hp.out hrp).mpr hrne.symm)
      have := pow_gcd_eq_one.mpr ⟨hyp, hyr⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
  choose K hKn hKr hPK using hK
  let L : Subgroup H := ⨅ r, ⨅ (hr : r ∈ (Nat.card A).primeFactors), K r hr
  have hLn : L.Normal := by
    apply Subgroup.normal_iInf_normal
    intro r
    apply Subgroup.normal_iInf_normal
    intro hr
    exact hKn r hr
  have hPL : (P : Subgroup H) ≤ L := le_iInf₂ hPK
  have hLK : ∀ r (hr : r ∈ (Nat.card A).primeFactors), L ≤ K r hr := fun r hr =>
    iInf₂_le r hr
  have hLcop : Nat.Coprime (Nat.card L) (Nat.card A) := by
    apply Nat.coprime_of_dvd
    intro r hr hrL hrA
    have hmem : r ∈ (Nat.card A).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr, hrA, (Nat.card_pos (α := A)).ne'⟩
    exact hKr r hmem (hrL.trans (Subgroup.card_dvd_of_le (hLK r hmem)))
  have hLdvd : Nat.card L ∣ p ^ k := by
    have h1 : Nat.card L ∣ Nat.card A * p ^ k := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card L
    exact hLcop.dvd_of_dvd_mul_left h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hLdvd
  have hLp : IsPGroup p L := IsPGroup.of_card hj
  have hLP : L = P := P.is_maximal' hLp hPL
  rw [← hLP]
  exact hLn

end CFSG.BrauerLinearThree
