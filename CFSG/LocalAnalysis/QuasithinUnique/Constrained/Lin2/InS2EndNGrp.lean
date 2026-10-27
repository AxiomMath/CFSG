module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.QuasithinUnique.Lin2.EndN

variable {G : Type*} [Group G]

theorem mem_closure_primePow [Finite G] (X : Subgroup G) (g : G) (hg : g ∈ X) :
    g ∈ Subgroup.closure {x : G | x ∈ X ∧ ∃ p k : ℕ, p.Prime ∧ orderOf x = p ^ k} := by
  suffices h : ∀ m : ℕ, ∀ g : G, g ∈ X → orderOf g = m →
      g ∈ Subgroup.closure {x : G | x ∈ X ∧ ∃ p k : ℕ, p.Prime ∧ orderOf x = p ^ k} from
    h _ g hg rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro g hg hm
    by_cases h1 : m = 1
    · have : g = 1 := orderOf_eq_one_iff.1 (hm.trans h1)
      rw [this]
      exact Subgroup.one_mem _
    have hm0 : m ≠ 0 := by rw [← hm]; exact (orderOf_pos g).ne'
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨a, m', hpm', hmm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
    have ha : a ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hmm
      exact hpm' (hmm ▸ hpm)
    have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hmm; exact hm0 hmm
    by_cases hm'1 : m' = 1
    · refine Subgroup.subset_closure ⟨hg, p, a, hp, ?_⟩
      rw [hm, hmm, hm'1, mul_one]
    have hcop : Nat.Coprime (p ^ a) m' :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm')
    obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder hcop 1 0
    obtain ⟨f, hf1, hf2⟩ := Nat.chineseRemainder hcop 0 1
    have hm'e : m' ∣ e := (Nat.modEq_zero_iff_dvd).1 he2
    have hpf : p ^ a ∣ f := (Nat.modEq_zero_iff_dvd).1 hf1
    have hge : (g ^ e) ^ (p ^ a) = 1 := by
      rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hm, hmm, mul_comm e]
      exact Nat.mul_dvd_mul_left _ hm'e
    have hgf : (g ^ f) ^ m' = 1 := by
      rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hm, hmm]
      exact Nat.mul_dvd_mul_right hpf _
    have hge' : orderOf (g ^ e) ∣ p ^ a := orderOf_dvd_iff_pow_eq_one.2 hge
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hge'
    have hgeX : g ^ e ∈ X := X.pow_mem hg e
    have hgfX : g ^ f ∈ X := X.pow_mem hg f
    have hfm : orderOf (g ^ f) < m := by
      have h2 : orderOf (g ^ f) ≤ m' := Nat.le_of_dvd (Nat.pos_of_ne_zero hm'0)
        (orderOf_dvd_iff_pow_eq_one.2 hgf)
      have h3 : 2 ≤ p ^ a := by
        calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero ha)
      have h4 : 0 < m' := Nat.pos_of_ne_zero hm'0
      rw [hmm]
      nlinarith
    have hmod : e + f ≡ 1 [MOD m] := by
      rw [hmm]
      refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨?_, ?_⟩
      · calc e + f ≡ 1 + 0 [MOD p ^ a] := Nat.ModEq.add he1 hf1
          _ = 1 := by rw [add_zero]
      · calc e + f ≡ 0 + 1 [MOD m'] := Nat.ModEq.add he2 hf2
          _ = 1 := by rw [zero_add]
    have hgg : g = g ^ e * g ^ f := by
      rw [← pow_add]
      have : g ^ (e + f) = g ^ 1 := by
        rw [pow_eq_pow_iff_modEq, hm]
        exact hmod
      rw [this, pow_one]
    rw [hgg]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hgeX, p, j, hp, hj⟩) ?_
    exact ih _ hfm (g ^ f) hgfX rfl

theorem prime_dvd_card_modPCore {L : Subgroup G} {g : G} (hg : g ∈ L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hord : orderOf g = p) : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact p.Prime := ⟨hp⟩
  set g' : ↥L := ⟨g, hg⟩ with hg'
  have hord' : orderOf g' = p := by rw [hg', Subgroup.orderOf_mk, hord]
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπ1 : π g' ≠ 1 := by
    intro h
    have hmem : g' ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff g').1 h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨g', hmem⟩
    have h2 : orderOf g' ∣ 2 ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have := congrArg (fun z : CFSG.pCore 2 ↥L => (z : ↥L)) hk
      simpa using this
    rw [hord'] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  have hπp : π g' ^ p = 1 := by rw [← map_pow, ← hord', pow_orderOf_eq_one, map_one]
  have hπo : orderOf (π g') = p := orderOf_eq_prime hπp hπ1
  rw [← hπo]
  exact orderOf_dvd_natCard _

end CFSG.QuasithinUnique.Lin2.EndN
