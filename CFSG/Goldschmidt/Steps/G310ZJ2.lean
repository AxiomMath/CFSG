module

public import CFSG.Goldschmidt.Steps.G310ZJ

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open CFSG.Glauberman

section Power

variable {Q : Type*} [Group Q]

theorem exists_pow_mul_eq {L : Subgroup Q} {q l : Q} (hq : q ∈ Subgroup.normalizer (L : Set Q))
    (hl : l ∈ L) : ∀ m : ℕ, ∃ l' ∈ L, (q * l) ^ m = q ^ m * l' := by
  intro m
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', h⟩ := ih
    have h1 : q⁻¹ * l' * q ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hq) l').mp hl'
      simpa using this
    refine ⟨q⁻¹ * l' * q * l, L.mul_mem h1 hl, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem le_centralizer_of_inf_eq_bot {R L N : Subgroup Q} (hLR : L ≤ R)
    (hRL : R ≤ Subgroup.normalizer (L : Set Q)) (hRN : R ≤ Subgroup.normalizer (N : Set Q))
    (hNR : N ≤ R) (hNL : N ⊓ L = ⊥) : N ≤ Subgroup.centralizer (L : Set Q) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : n * l * n⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRL (hNR hn)) l).mp hl) (L.inv_mem hl)
  have h2 : n * l * n⁻¹ * l⁻¹ ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hRN (hLR hl)) n⁻¹).mp (N.inv_mem hn)
    have h3 := N.mul_mem hn this
    rwa [show n * (l * n⁻¹ * l⁻¹) = n * l * n⁻¹ * l⁻¹ by group] at h3
  have h3 : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L := ⟨h2, h1⟩
  rw [hNL, Subgroup.mem_bot] at h3
  calc l * n = (n * l * n⁻¹ * l⁻¹)⁻¹ * n * l := by group
    _ = n * l := by rw [h3, inv_one, one_mul]

end Power

section Map

variable {X : Type*} [Group X] [Finite X] {Q : Type*} [Group Q] [Finite Q]

omit [Finite X] [Finite Q] in
theorem eq_one_of_odd_of_two {K S : Subgroup X} (hK : Odd (Nat.card K)) (hS : IsPGroup 2 S)
    {x : X} (hxK : x ∈ K) (hxS : x ∈ S) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hS ⟨x, hxS⟩
  have h2 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h1 : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
  obtain ⟨i, -, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2)
  rcases i with _ | i
  · rw [pow_zero, orderOf_eq_one_iff] at hix
    exact hix
  · exfalso
    rw [hix] at h1
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr ((dvd_pow_self 2
      (Nat.succ_ne_zero i)).trans h1))

theorem zj_normal_of_map
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup X}
    (hPp : IsPGroup p P) (ρ : X →* Q) (Lq : Subgroup Q)
    (hker : ρ.ker ≤ goldschmidtOddCore X) (hsyl : fusionIsSylowIn p P (P ⊔ ρ.ker))
    (hrange : ρ.range = Lq ⊔ P.map ρ) (hPL : P.map ρ ≤ Subgroup.normalizer (Lq : Set Q))
    (hsimple : ∀ N : Subgroup Q, N ≤ Lq → Lq ≤ Subgroup.normalizer (N : Set Q) →
      N = ⊥ ∨ N = Lq)
    (hinv : ∃ t ∈ Lq, t ≠ 1 ∧ t ^ 2 = 1)
    (hcent : ρ.range ⊓ Subgroup.centralizer (Lq : Set Q) ≤ P.map ρ)
    (hab : ∀ S : Subgroup Q, S ≤ Lq → IsPGroup 2 S → IsMulCommutative S)
    (hd : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X) :
    (ZJ P).Normal := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ρ.range with hR
  set O := goldschmidtOddCore X with hOdef
  have hOodd : Odd (Nat.card O) := SStarTransport.odd_card_goldschmidtOddCore X
  have hLR : Lq ≤ R := by rw [hrange]; exact le_sup_left
  have hRL : R ≤ Subgroup.normalizer (Lq : Set Q) := by
    rw [hrange]
    exact sup_le Subgroup.le_normalizer hPL
  have hmapN : ∀ N : Subgroup X, N.Normal → R ≤ Subgroup.normalizer (N.map ρ : Set Q) := by
    rintro N hN _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨x * n * x⁻¹, hN.conj_mem n hn x, by simp⟩
    · rintro ⟨n, hn, hny⟩
      refine ⟨x⁻¹ * n * x, ?_, ?_⟩
      · have := hN.conj_mem n hn x⁻¹
        simpa using this
      · rw [map_mul, map_mul, map_inv, hny]
        group
  have hdich : ∀ N : Subgroup X, N.Normal → N.map ρ ⊓ Lq = ⊥ ∨ Lq ≤ N.map ρ := by
    intro N hN
    rcases hsimple (N.map ρ ⊓ Lq) inf_le_right
      (le_normalizer_inf (hLR.trans (hmapN N hN)) Subgroup.le_normalizer) with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ inf_le_left)
  have hsmall : ∀ N : Subgroup X, N.Normal → N.map ρ ⊓ Lq = ⊥ → N ≤ P ⊔ ρ.ker := by
    intro N hN h n hn
    have h1 := le_centralizer_of_inf_eq_bot hLR hRL (hmapN N hN) (Subgroup.map_le_range ρ N) h
    have h2 : ρ n ∈ P.map ρ := hcent ⟨⟨n, rfl⟩, h1 ⟨n, hn, rfl⟩⟩
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq] at h2
    exact h2
  have hkerodd : Odd (Nat.card ρ.ker) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hker)
  have hPK : ¬ 2 ∣ Nat.card (P ⊔ ρ.ker : Subgroup X) := by
    refine not_two_dvd_card_sup hp hp2 hPp ?_
      (fun h => (Nat.not_even_iff_odd.mpr hkerodd) (even_iff_two_dvd.mpr h))
    rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker ρ)]
    exact le_top
  have hPKodd : Odd (Nat.card (P ⊔ ρ.ker : Subgroup X)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hPK)
  obtain ⟨t, htL, ht1, ht2⟩ := hinv
  have ht_odd : ∀ K : Subgroup Q, Odd (Nat.card K) → t ∉ K := by
    intro K hK htK
    have h1 : orderOf t ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K htK
    have h2 : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    rw [h2] at h1
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h1)
  have ht_p : ∀ K : Subgroup Q, IsPGroup p K → t ∉ K := by
    intro K hK htK
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    exact ht_odd K (by rw [hn]; exact (hp.odd_of_ne_two hp2).pow) htK
  have h2 : CFSG.Walter.HasAbelianSylowTwo X := by
    intro S
    have hSL : (S : Subgroup X).map ρ ≤ Lq := by
      rintro _ ⟨s, hs, rfl⟩
      have hsR : ρ s ∈ P.map ρ ⊔ Lq := by
        rw [sup_comm, ← hrange]
        exact ⟨s, rfl⟩
      obtain ⟨q, hq, l, hl, hql⟩ := exists_mul_of_mem_sup hPL hsR
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
      have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨l', hl', hpow⟩ := exists_pow_mul_eq (hPL hq) hl (2 ^ k)
      have h1 : q ^ 2 ^ k * l' = 1 := by rw [← hpow, hql, ← map_pow, hsk, map_one]
      have hqk : q ^ 2 ^ k ∈ Lq := by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Lq.inv_mem hl'
      obtain ⟨n, hn⟩ := (hPp.map ρ) ⟨q, hq⟩
      have hqn : q ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hq' : q ∈ Subgroup.zpowers (q ^ 2 ^ k) := by
        rw [mem_zpowers_pow_iff]
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hqn)
        rw [hi]
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      rw [← hql]
      exact Lq.mul_mem (Subgroup.zpowers_le.mpr hqk hq') hl
    have hab' := hab _ hSL (S.isPGroup'.map ρ)
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hcomm : ρ ((a : X) * b) = ρ ((b : X) * a) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hab'.is_comm.comm ⟨ρ a, a, a.2, rfl⟩ ⟨ρ b, b, b.2, rfl⟩)
    have h1 : ((b : X) * a)⁻¹ * ((a : X) * b) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
    have h2 : ((b : X) * a)⁻¹ * ((a : X) * b) ∈ (S : Subgroup X) :=
      (S : Subgroup X).mul_mem ((S : Subgroup X).inv_mem
        ((S : Subgroup X).mul_mem b.2 a.2)) ((S : Subgroup X).mul_mem a.2 b.2)
    have h3 := eq_one_of_odd_of_two hkerodd S.isPGroup' h1 h2
    rw [inv_mul_eq_one] at h3
    simp only [Subgroup.coe_mul]
    exact h3.symm
  have hb : ∀ B : Subgroup X, B.Normal → IsPGroup p B → B ≤ P := by
    intro B hBn hBp
    have hBsmall : B.map ρ ⊓ Lq = ⊥ := by
      rcases hdich B hBn with h | h
      · exact h
      · exact absurd (h htL) (ht_p _ (hBp.map ρ))
    have h1 := hsmall B hBn hBsmall
    have hPB : P ≤ Subgroup.normalizer (B : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hBn]
      exact le_top
    have h2 : IsPGroup p (B ⊔ P : Subgroup X) := by
      rw [sup_comm]
      exact hPp.to_sup_of_normal_right' hBp hPB
    have h3 := hsyl.2.2 (B ⊔ P) (sup_le h1 le_sup_left) h2 le_sup_right
    exact le_sup_left.trans h3.le
  have hc : fusionIsSylowIn p (P ⊓ O) O := by
    have hOsmall : O.map ρ ⊓ Lq = ⊥ := by
      rcases hdich O inferInstance with h | h
      · exact h
      · exact absurd (h htL) (ht_odd _ (hOodd.of_dvd_nat (Subgroup.card_map_dvd O ρ)))
    have hOle := hsmall O inferInstance hOsmall
    have hOn : (O.subgroupOf (P ⊔ ρ.ker)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mpr (by
        rw [Subgroup.normalizer_eq_top_iff.mpr (goldschmidtOddCore_normal X)]
        exact le_top)
    obtain ⟨S, hS⟩ := SStarTransport.exists_sylow_subgroupOf_of_normal hsyl hOle hOn
    refine SStarTransport.isSylowIn_of_sylow inf_le_right S ?_
    rw [hS]
    ext x
    simp [Subgroup.mem_subgroupOf]
  have he : ∀ N N' : Subgroup X, N.Normal → N'.Normal → N' ≤ N →
      (∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ N') → N ≤ O ∨ (⊤ : Subgroup X) ≤ N' ⊔ O ⊔ P := by
    intro N N' hN hN' _ hpow
    rcases hdich N hN with h | h
    · left
      have h1 := hsmall N hN h
      exact le_sSup ⟨hN, hPKodd.of_dvd_nat (Subgroup.card_dvd_of_le h1)⟩
    · right
      rcases hdich N' hN' with h' | h'
      · exfalso
        obtain ⟨x, hx, hxt⟩ := h htL
        obtain ⟨k, hk⟩ := hpow x hx
        have h1 : t ^ p ^ k ∈ N'.map ρ ⊓ Lq := ⟨⟨_, hk, by rw [map_pow, hxt]⟩, Lq.pow_mem htL _⟩
        rw [h', Subgroup.mem_bot] at h1
        have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
        obtain ⟨m, hm⟩ := hodd
        have : t ^ p ^ k = t := by
          rw [hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
        exact ht1 (this ▸ h1)
      · intro x _
        have hxR : ρ x ∈ (N' ⊔ P).map ρ := by
          rw [Subgroup.map_sup]
          have : ρ x ∈ R := ⟨x, rfl⟩
          rw [hrange] at this
          exact (sup_le_sup_right h' _) this
        rw [← Subgroup.mem_comap, Subgroup.comap_map_eq] at hxR
        refine (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
          (hker.trans (le_sup_right.trans le_sup_left))) hxR
  exact zj_normal_of_core hp2 h2 hPp hb hc hd he

end Map

end CFSG.Goldschmidt.G310
