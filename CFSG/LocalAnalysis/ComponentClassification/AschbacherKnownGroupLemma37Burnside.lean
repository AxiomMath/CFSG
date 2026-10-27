module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Components

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

theorem conj_eq_of_odd {S : Subgroup G} (hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {h : G}
    (hN : ∀ s ∈ S, h * s * h⁻¹ ∈ S) {β : ℕ} (hβ : Odd β) (hhβ : h ^ β = 1)
    (hinv : ∀ s ∈ S, s ^ 2 = 1 → h * s * h⁻¹ = s) :
    ∀ k : ℕ, ∀ s ∈ S, s ^ 2 ^ k = 1 → h * s * h⁻¹ = s := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    rw [pow_zero, pow_one] at hs
    rw [hs]
    group
  | succ k ih =>
    intro s hs hsk
    have hs2 : h * s ^ 2 * h⁻¹ = s ^ 2 := by
      refine ih _ (pow_mem hs 2) ?_
      rw [← pow_mul, ← pow_succ']
      exact hsk
    set w := s⁻¹ * (h * s * h⁻¹) with hw
    have hwS : w ∈ S := S.mul_mem (S.inv_mem hs) (hN s hs)
    have hcomm : s⁻¹ * (h * s * h⁻¹) = (h * s * h⁻¹) * s⁻¹ :=
      hSab _ (S.inv_mem hs) _ (hN s hs)
    have hw2 : w ^ 2 = 1 := by
      have h1 : (h * s * h⁻¹) ^ 2 = s ^ 2 := by rw [conj_pow, hs2]
      calc w ^ 2 = s⁻¹ * (h * s * h⁻¹) * (s⁻¹ * (h * s * h⁻¹)) := by rw [hw, pow_two]
        _ = s⁻¹ * ((h * s * h⁻¹) * s⁻¹) * (h * s * h⁻¹) := by group
        _ = s⁻¹ * (s⁻¹ * (h * s * h⁻¹)) * (h * s * h⁻¹) := by rw [hcomm]
        _ = s⁻¹ * s⁻¹ * (h * s * h⁻¹) ^ 2 := by rw [pow_two]; group
        _ = 1 := by rw [h1, pow_two]; group
    have hwh : h * w * h⁻¹ = w := hinv w hwS hw2
    have hpow : ∀ j : ℕ, h ^ j * s * (h ^ j)⁻¹ = s * w ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have hwj : h * w ^ j * h⁻¹ = w ^ j := by rw [← conj_pow, hwh]
        calc h ^ (j + 1) * s * (h ^ (j + 1))⁻¹ = h * (h ^ j * s * (h ^ j)⁻¹) * h⁻¹ := by
              rw [pow_succ']; group
          _ = h * (s * w ^ j) * h⁻¹ := by rw [ihj]
          _ = (h * s * h⁻¹) * (h * w ^ j * h⁻¹) := by group
          _ = (s * w) * w ^ j := by rw [hwj, hw]; group
          _ = s * w ^ (j + 1) := by rw [pow_succ']; group
    have h1 := hpow β
    rw [hhβ, one_mul, inv_one, mul_one] at h1
    obtain ⟨l, rfl⟩ := hβ
    have hwl : w ^ (2 * l + 1) = w := by
      rw [pow_succ, pow_mul, hw2, one_pow, one_mul]
    rw [hwl] at h1
    have hw1 : w = 1 := by
      have := congrArg (s⁻¹ * ·) h1
      simpa using this.symm
    calc h * s * h⁻¹ = s * w := by rw [hw]; group
      _ = s := by rw [hw1, mul_one]

theorem mem_sup_involution {a e : G} (he2 : e ^ 2 = 1) (hae : a * e = e * a) {g : G} :
    g ∈ zpowers a ⊔ zpowers e ↔ g ∈ zpowers a ∨ e⁻¹ * g ∈ zpowers a := by
  refine mem_sup_zpowers_iff (mem_normalizer_of_comm fun h hh => ?_)
    (by rw [he2]; exact one_mem _)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
  exact ((Commute.zpow_left hae k)).eq.symm

theorem not_abelian_sylow_cyclic_times_two [Finite G] {A : Subgroup G} [Group.IsPerfect A]
    (S₀ : Sylow 2 A) {a e : G} {n : ℕ} (hn : 2 ≤ n)
    (ha : a ∈ (S₀ : Subgroup A).map A.subtype) (he : e ∈ (S₀ : Subgroup A).map A.subtype)
    (hao : orderOf a = 2 ^ n) (he2 : e ^ 2 = 1) (hea : e ∉ zpowers a) (hae : a * e = e * a)
    (hcard : Nat.card ((S₀ : Subgroup A).map A.subtype) = 2 ^ (n + 1)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := (S₀ : Subgroup A).map A.subtype with hS
  have hecomm : ∀ h ∈ zpowers a, e * h = h * e := by
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left hae k)).eq.symm
  have hle : zpowers a ⊔ zpowers e ≤ S := sup_le (zpowers_le.2 ha) (zpowers_le.2 he)
  have hcard' : Nat.card (zpowers a ⊔ zpowers e : Subgroup G) = 2 ^ (n + 1) := by
    rw [card_sup_involution he2 hecomm hea, Nat.card_zpowers, hao, pow_succ']
  have hSeq : zpowers a ⊔ zpowers e = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard'])
  have hmemS : ∀ s ∈ S, s ∈ zpowers a ∨ e⁻¹ * s ∈ zpowers a := fun s hs =>
    (mem_sup_involution he2 hae).1 (hSeq ▸ hs)
  have hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    rw [← hSeq] at hx hy
    have key : ∀ g ∈ zpowers a ⊔ zpowers e, ∃ k : ℤ, g = a ^ k ∨ g = e * a ^ k := by
      intro g hg
      rcases (mem_sup_involution he2 hae).1 hg with h' | h'
      · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h'
        exact ⟨k, Or.inl hk.symm⟩
      · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h'
        exact ⟨k, Or.inr (by rw [hk]; group)⟩
    obtain ⟨i, hi | hi⟩ := key x hx <;> obtain ⟨j, hj | hj⟩ := key y hy <;> rw [hi, hj]
    · exact (Commute.zpow_zpow_self a i j).eq
    · rw [← mul_assoc, ← (hecomm _ (zpow_mem (mem_zpowers a) i)), mul_assoc,
        (Commute.zpow_zpow_self a i j).eq, ← mul_assoc]
    · rw [mul_assoc, (Commute.zpow_zpow_self a i j).eq, ← mul_assoc,
        hecomm _ (zpow_mem (mem_zpowers a) j), mul_assoc]
    · calc e * a ^ i * (e * a ^ j) = e * (a ^ i * e) * a ^ j := by group
        _ = e * (e * a ^ i) * a ^ j := by rw [hecomm _ (zpow_mem (mem_zpowers a) i)]
        _ = e * e * (a ^ i * a ^ j) := by group
        _ = e * e * (a ^ j * a ^ i) := by rw [(Commute.zpow_zpow_self a i j).eq]
        _ = e * (e * a ^ j) * a ^ i := by group
        _ = e * (a ^ j * e) * a ^ i := by rw [hecomm _ (zpow_mem (mem_zpowers a) j)]
        _ = e * a ^ j * (e * a ^ i) := by group
  set z := a ^ 2 ^ (n - 1) with hz
  have hzA : z ∈ zpowers a := pow_mem (mem_zpowers a) _
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega, ← hao]
    exact pow_orderOf_eq_one a
  have hz1 : z ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hao] at this
    have := Nat.le_of_dvd (by positivity) this
    have : 2 ^ n ≤ 2 ^ (n - 1) := this
    have := Nat.pow_le_pow_iff_right (by norm_num : 1 < 2) |>.1 this
    omega
  have hcyc : IsCyclic (zpowers a) := inferInstance
  have hinvA : ∀ w ∈ zpowers a, w ^ 2 = 1 → w ≠ 1 → w = z := fun w hw hw2 hw1 =>
    TwoGroup.involution_unique_of_isCyclic hcyc hw hzA hw2 hw1 hz2 hz1
  have hezc : e * z = z * e := hecomm z hzA
  have hinvS : ∀ s ∈ S, s ^ 2 = 1 → s ≠ 1 → s = z ∨ s = e ∨ s = e * z := by
    intro s hs hs2 hs1
    rcases hmemS s hs with h | h
    · exact Or.inl (hinvA s h hs2 hs1)
    · set w := e⁻¹ * s with hw
      have hsw : s = e * w := by rw [hw]; group
      have hw2 : w ^ 2 = 1 := by
        have hew : e * w = w * e := hecomm w h
        have : s ^ 2 = e ^ 2 * w ^ 2 := by
          rw [hsw, pow_two, pow_two, pow_two]
          calc e * w * (e * w) = e * (w * e) * w := by group
            _ = e * (e * w) * w := by rw [hew]
            _ = e * e * (w * w) := by group
        rw [hs2, he2, one_mul] at this
        exact this.symm
      by_cases hw1 : w = 1
      · right; left
        rw [hsw, hw1, mul_one]
      · right; right
        rw [hsw, hinvA w h hw2 hw1]
  have hsq : ∀ s ∈ S, s ^ 2 ∈ zpowers a := by
    intro s hs
    rcases hmemS s hs with h | h
    · exact pow_mem h 2
    · have hs' : s = e * (e⁻¹ * s) := by group
      have hew : e * (e⁻¹ * s) = (e⁻¹ * s) * e := hecomm _ h
      rw [hs', pow_two]
      have : e * (e⁻¹ * s) * (e * (e⁻¹ * s)) = e ^ 2 * (e⁻¹ * s) ^ 2 := by
        rw [pow_two, pow_two]
        calc e * (e⁻¹ * s) * (e * (e⁻¹ * s)) = e * ((e⁻¹ * s) * e) * (e⁻¹ * s) := by group
          _ = e * (e * (e⁻¹ * s)) * (e⁻¹ * s) := by rw [hew]
          _ = e * e * ((e⁻¹ * s) * (e⁻¹ * s)) := by group
      rw [this, he2, one_mul]
      exact pow_mem h 2
  set T : Subgroup A := (S₀ : Subgroup A) with hT
  have hTS : ∀ t : A, t ∈ T ↔ (t : G) ∈ S := by
    intro t
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t', ht', ht't⟩
      have : t' = t := Subtype.ext ht't
      rwa [← this]
  have hnorm : normalizer (T : Set A) ≤ centralizer (T : Set A) := by
    intro g hg
    have hgS : ∀ s ∈ S, (g : G) * s * (g : G)⁻¹ ∈ S := by
      rintro _ ⟨t, ht, rfl⟩
      have := (mem_normalizer_iff.1 hg t).1 ht
      exact (hTS _).1 this
    obtain ⟨α, β, hβodd, hαβ⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have hg2T : g ^ β ∈ T := by
      have hp : IsPGroup 2 (zpowers (g ^ β)) := by
        rw [IsPGroup.iff_card, Nat.card_zpowers]
        have hdvd : orderOf (g ^ β) ∣ 2 ^ α := by
          apply orderOf_dvd_of_pow_eq_one
          rw [← pow_mul, mul_comm, ← hαβ, pow_orderOf_eq_one]
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        exact ⟨i, hi⟩
      have hle : zpowers (g ^ β) ≤ normalizer (T : Set A) := zpowers_le.2 (pow_mem hg β)
      have hQ := S₀.isPGroup'.to_sup_of_normal_left' hp hle
      have heq : T ⊔ zpowers (g ^ β) = T := S₀.is_maximal' hQ le_sup_left
      rw [← heq]
      exact mem_sup_right (mem_zpowers _)
    set h : G := (g : G) ^ 2 ^ α with hh
    have hhβ : h ^ β = 1 := by
      rw [hh, ← pow_mul, ← hαβ, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hhS : ∀ s ∈ S, h * s * h⁻¹ ∈ S := by
      intro s hs
      have : ∀ j : ℕ, (g : G) ^ j * s * ((g : G) ^ j)⁻¹ ∈ S := by
        intro j
        induction j with
        | zero => simpa using hs
        | succ j ih =>
          have := hgS _ ih
          rw [pow_succ']
          simpa [mul_assoc] using this
      exact this _
    have hhinvS : ∀ s ∈ S, h⁻¹ * s * h ∈ S := by
      intro s hs
      have hinv : h⁻¹ = h ^ (β - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hβodd.pos, hhβ]
      have : ∀ j : ℕ, h ^ j * s * (h ^ j)⁻¹ ∈ S := by
        intro j
        induction j with
        | zero => simpa using hs
        | succ j ih =>
          have := hhS _ ih
          rw [pow_succ']
          simpa [mul_assoc] using this
      have h1 := this (β - 1)
      rw [← hinv, inv_inv] at h1
      exact h1
    have hhz : h * z * h⁻¹ = z := by
      have hz' : z = (a ^ 2 ^ (n - 2)) ^ 2 := by
        rw [hz, ← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega]
      have hw : h * a ^ 2 ^ (n - 2) * h⁻¹ ∈ S := hhS _ (pow_mem ha _)
      have hmem : h * z * h⁻¹ ∈ zpowers a := by
        rw [hz', ← conj_pow]
        exact hsq _ hw
      refine hinvA _ hmem (by rw [conj_pow, hz2]; group) ?_
      intro h1
      apply hz1
      calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    have hhe : h * e * h⁻¹ = e := by
      have he1 : e ≠ 1 := fun h1 => hea (h1 ▸ one_mem _)
      have hmem : h * e * h⁻¹ ∈ S := hhS e he
      have h2 : (h * e * h⁻¹) ^ 2 = 1 := by rw [conj_pow, he2]; group
      have h1 : h * e * h⁻¹ ≠ 1 := by
        intro h1
        apply he1
        calc e = h⁻¹ * (h * e * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      rcases hinvS _ hmem h2 h1 with h3 | h3 | h3
      · exfalso
        apply hea
        have : e = z := by
          calc e = h⁻¹ * (h * e * h⁻¹) * h := by group
            _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [h3, hhz]
            _ = z := by group
        rw [this]
        exact hzA
      · exact h3
      · exfalso
        have hj : ∀ j : ℕ, h ^ j * e * (h ^ j)⁻¹ = e * z ^ j := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            have hzj : h * z ^ j * h⁻¹ = z ^ j := by rw [← conj_pow, hhz]
            calc h ^ (j + 1) * e * (h ^ (j + 1))⁻¹ = h * (h ^ j * e * (h ^ j)⁻¹) * h⁻¹ := by
                  rw [pow_succ']; group
              _ = (h * e * h⁻¹) * (h * z ^ j * h⁻¹) := by rw [ih]; group
              _ = e * z * z ^ j := by rw [h3, hzj]
              _ = e * z ^ (j + 1) := by rw [pow_succ']; group
        have := hj β
        rw [hhβ, one_mul, inv_one, mul_one] at this
        obtain ⟨l, rfl⟩ := hβodd
        rw [pow_succ, pow_mul, hz2, one_pow, one_mul] at this
        apply hz1
        have := congrArg (e⁻¹ * ·) this
        simpa using this.symm
    have hhinv : ∀ s ∈ S, s ^ 2 = 1 → h * s * h⁻¹ = s := by
      intro s hs hs2
      by_cases hs1 : s = 1
      · rw [hs1]; group
      rcases hinvS s hs hs2 hs1 with h1 | h1 | h1 <;> rw [h1]
      · exact hhz
      · exact hhe
      · calc h * (e * z) * h⁻¹ = (h * e * h⁻¹) * (h * z * h⁻¹) := by group
          _ = e * z := by rw [hhe, hhz]
    have hhcen : ∀ s ∈ S, h * s * h⁻¹ = s := by
      intro s hs
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 (S₀.isPGroup'.map A.subtype) ⟨s, hs⟩
      refine conj_eq_of_odd hSab hhS hβodd hhβ hhinv k s hs ?_
      rw [Subgroup.orderOf_mk] at hk
      rw [← hk]
      exact pow_orderOf_eq_one s
    rw [mem_centralizer_iff]
    intro t ht
    have htS : (t : G) ∈ S := (hTS t).1 ht
    have hc1 : Commute ((g : G) ^ β) (t : G) := by
      have h1 := hSab _ ((hTS _).1 hg2T) _ htS
      rw [Subgroup.coe_pow] at h1
      exact h1
    have hc2 : Commute h (t : G) := by
      have h1 := hhcen _ htS
      calc h * t = (h * t * h⁻¹) * h := by group
        _ = t * h := by rw [h1]
    have hcop : IsCoprime (β : ℤ) ((2 : ℤ) ^ α) := by
      have : Nat.Coprime β (2 ^ α) := Nat.Coprime.pow_right α (Nat.coprime_two_right.2 hβodd)
      exact_mod_cast Nat.isCoprime_iff_coprime.2 this
    obtain ⟨u, v, huv⟩ := hcop
    have hgform : (g : G) = ((g : G) ^ β) ^ u * h ^ v := by
      rw [hh, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
      conv_lhs => rw [← zpow_one (g : G)]
      congr 1
      push_cast
      linarith
    apply Subtype.ext
    change (t : G) * g = g * t
    rw [hgform]
    exact ((hc1.zpow_left u).mul_left (hc2.zpow_left v)).eq.symm
  let _ : CommGroup T :=
    { (inferInstance : Group T) with
      mul_comm := fun x y => Subtype.ext (Subtype.ext (hSab _ ((hTS _).1 x.2) _ ((hTS _).1 y.2))) }
  let transfer : A →* T := MonoidHom.transferSylow S₀ hnorm
  have hkernel : transfer.ker = ⊤ := TwoRankLowerBound.Helpers.ker_eq_top_of_perfect A T transfer
  have hcomplement := MonoidHom.ker_transferSylow_isComplement' S₀ hnorm
  change transfer.ker.IsComplement' T at hcomplement
  rw [hkernel] at hcomplement
  have hbot : T = ⊥ := Subgroup.isComplement'_top_left.mp hcomplement
  have : Nat.card S = 1 := by
    rw [hS, Subgroup.card_map_of_injective A.subtype_injective]
    rw [hbot, Subgroup.card_bot]
  rw [hcard] at this
  have := Nat.one_lt_two_pow (n := n + 1) (by omega)
  omega


end Lemma37

end CFSG.ComponentClassification.AschbacherKnownGroup
