module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Rigid

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem mul_centralElt_sq (hc : PartC T Q P₁ e u) {x : G} (hxx : x * x = e) :
    x * e * (x * e) = e := by
  calc x * e * (x * e) = x * x * (e * e) := by
        rw [mul_assoc x e (x * e), ← mul_assoc e x e, ← hc.commute_centralElt x]; group
    _ = e := by rw [hxx, hc.centralElt_mul_self, mul_one]

theorem false_of_not_isCyclic_of_three_le [Finite G] (hperf : Group.IsPerfect G)
    (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁) (S : Sylow 2 G) (hST : (S : Subgroup G) = T)
    {c : G} {n : ℕ} (hcP : Subgroup.zpowers c = P₁) (hco : orderOf c = 2 ^ n) (hn : 3 ≤ n)
    (hce : c ^ 2 ^ (n - 1) = e) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y = e)
    (hyi : ∀ p ∈ P₁, y * p * y⁻¹ = p⁻¹) : False := by
  have he := hc.commute_centralElt
  have hcP₁ : c ∈ P₁ := hcP ▸ Subgroup.mem_zpowers c
  have hcT : c ∈ T := hc.right_le hcP₁
  have hNT := hc.normalizer_le_normalizer_zpowers_of_isCyclic hcyc
  have hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    Subgroup.le_normalizer.trans hNT
  obtain ⟨v, hvQ, hvv, hyv, hfix⟩ := hc.exists_inv_conj hyT hy (hyy ▸ hc.mem_right)
  have hTv := hc.le_normalizer_zpowers_of_inv hyT hy hvQ hvv hyv
  have hfus := hc.conj_not_mem_zpowers S hST hnorm hNT hvQ hvv hTv
  obtain ⟨j, hjQ, hjv⟩ : ∃ j ∈ Q, j * v * j⁻¹ = v * e := by
    obtain ⟨m, hm, hm1, hm2⟩ := hc.outer y hyT hy
    obtain ⟨hmm, -, -⟩ := hc.moved_facts hyT hm hm1
    have hmv : m ≠ v := fun h => hm2 (by rw [h, hyv, hc.inv_eq_mul_centralElt hvv])
    have hmve : m ≠ v * e := fun h => hm2 (by
      rw [h, hc.conj_mul_centralElt, hyv, hc.inv_eq_mul_centralElt hvv])
    have h := hc.anticomm hm hvQ hmm hvv (fun h => hmv h.symm)
      (fun h => hmve (by rw [h, hc.mul_centralElt_mul_centralElt]))
    refine ⟨m, hm, ?_⟩
    rw [h, mul_assoc v m e, he m]
    group
  have hc'P : c ^ 2 ^ (n - 3) ∈ P₁ := P₁.pow_mem hcP₁ _
  have hc'c' : c ^ 2 ^ (n - 3) * c ^ 2 ^ (n - 3) = u ∨
      c ^ 2 ^ (n - 3) * c ^ 2 ^ (n - 3) = u * e := by
    refine hc.eq_of_mem_right_of_isCyclic hcyc (P₁.mul_mem hc'P hc'P) ?_
    rw [← pow_add, ← pow_add, ← hce]
    congr 1
    rw [show n - 1 = n - 3 + 2 by omega, pow_add]
    ring
  have hrig : ∀ x ∈ T, x ∉ Q ⊔ P₁ → x * x = e → ∀ g : G, g * x * g⁻¹ ≠ u :=
    fun x hxT hx hxx g => hc.conj_ne_self_of_isCyclic hcyc S hST hnorm hyT hy hyy hyi hvQ hvv
      hfix hTv hjQ hjv hc'P hc'c' hxT hx hxx g
  have hcQ : ∀ q ∈ Q, q * c = c * q := fun q hq => hc.commute q hq c hcP₁
  have hccQ : ∀ q ∈ Q, q * (c * c) = c * c * q := fun q hq => by
    rw [← mul_assoc, hcQ q hq, mul_assoc, hcQ q hq, ← mul_assoc]
  have hyc : y * c * y⁻¹ = c⁻¹ := hyi c hcP₁
  have hczpow : ∀ l : ℤ, (c * c) ^ l = c ^ (2 * l) := fun l => by rw [zpow_mul, zpow_two]
  set A := qPowSubgroup Q (c * c) hccQ with hA
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    rintro _ ⟨q, hq, l, rfl⟩
    refine ⟨y * q * y⁻¹, hc.normal_left y hyT q hq, -l, ?_⟩
    have h1 : y * (c * c) * y⁻¹ = (c * c)⁻¹ := by
      rw [show y * (c * c) * y⁻¹ = (y * c * y⁻¹) * (y * c * y⁻¹) by group, hyc]
      group
    calc y * (q * (c * c) ^ l) * y⁻¹ = (y * q * y⁻¹) * (y * (c * c) ^ l * y⁻¹) := by group
      _ = (y * q * y⁻¹) * (c * c) ^ (-l) := by rw [← conj_zpow, h1, inv_zpow, zpow_neg]
  have hyyA : y * y ∈ A := ⟨e, hc.mem_left, 0, by rw [zpow_zero, mul_one, hyy]⟩
  set K := twoCosets A y hyA hyyA with hK
  have hAs : ∀ a ∈ A, a ∈ Q ⊔ P₁ := by
    rintro _ ⟨q, hq, l, rfl⟩
    exact mul_mem_sup hq (P₁.zpow_mem (P₁.mul_mem hcP₁ hcP₁) l)
  have hyQP : ∀ x ∈ Q ⊔ P₁, x * y ∉ Q ⊔ P₁ ∧ x * y⁻¹ ∉ Q ⊔ P₁ := fun x hx =>
    ⟨fun h => hy (by simpa using (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem hx) h),
      fun h => hy (by simpa using (Q ⊔ P₁).inv_mem ((Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem hx) h))⟩
  have hqcs : ∀ q ∈ Q, ∀ i : ℤ, q * c ^ i ∈ Q ⊔ P₁ := fun q hq i =>
    mul_mem_sup hq (P₁.zpow_mem hcP₁ i)
  have hpar : ∀ k : ℤ, c ^ k ∈ Q → Even k := by
    intro k hk
    have h2 : c ^ (k * 2) = 1 := by
      rw [zpow_mul]
      rcases hc.mem_inf _ hk (hcP ▸ Subgroup.zpow_mem_zpowers c k) with h | h <;> rw [h]
      · exact one_zpow 2
      · rw [zpow_two, hc.centralElt_mul_self]
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hco] at h3
    push_cast at h3
    have h4 : (2 : ℤ) ^ 2 ∣ k * 2 := (pow_dvd_pow 2 (by omega)).trans h3
    exact even_iff_two_dvd.mpr (by omega)
  have hA_iff : ∀ q ∈ Q, ∀ i : ℤ, q * c ^ i ∈ A ↔ Even i := by
    intro q hq i
    constructor
    · rintro ⟨q', hq', l, hql⟩
      have h1 : c ^ (2 * l - i) = q'⁻¹ * q := by
        calc c ^ (2 * l - i) = q'⁻¹ * (q' * (c * c) ^ l) * (c ^ i)⁻¹ := by
              rw [hczpow, zpow_sub]; group
          _ = q'⁻¹ * q := by rw [← hql]; group
      have h2 := hpar _ (h1 ▸ Q.mul_mem (Q.inv_mem hq') hq)
      have h3 : Even (2 * l) := even_two_mul l
      have h4 : i = 2 * l - (2 * l - i) := by ring
      rw [h4]
      exact h3.sub h2
    · rintro ⟨l, rfl⟩
      exact ⟨q, hq, l, by rw [hczpow, two_mul]⟩
  have hK_iff1 : ∀ q ∈ Q, ∀ i : ℤ, q * c ^ i ∈ K ↔ Even i := by
    intro q hq i
    rw [mem_twoCosets, hA_iff q hq i]
    exact ⟨fun h => h.resolve_right fun h' => (hyQP _ (hqcs q hq i)).2 (hAs _ h'), Or.inl⟩
  have hK_iff2 : ∀ q ∈ Q, ∀ i : ℤ, q * c ^ i * y ∈ K ↔ Even i := by
    intro q hq i
    rw [mem_twoCosets, mul_inv_cancel_right, hA_iff q hq i]
    exact ⟨fun h => h.resolve_left fun h' => (hyQP _ (hqcs q hq i)).1 (hAs _ h'), Or.inr⟩
  have hdec : ∀ t ∈ T, ∃ q ∈ Q, ∃ i : ℤ, t = q * c ^ i ∨ t = q * c ^ i * y := by
    intro t ht
    obtain ⟨q, hq, w, hw, rfl⟩ := hc.exists_mul_eq_of_mem hyT hy ht
    rcases (hc.mem_sup_zpowers_iff hyT (hyy ▸ hc.mem_right)).mp hw with h | h <;>
      rw [← hcP] at h <;> obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
    · exact ⟨q, hq, i, Or.inl (by rw [hi])⟩
    · exact ⟨q, hq, i, Or.inr (by rw [hi]; group)⟩
  have hKT : K ≤ T := by
    rintro x (⟨q, hq, l, rfl⟩ | ⟨q, hq, l, hql⟩)
    · exact T.mul_mem (hc.left_le hq) (T.zpow_mem (T.mul_mem hcT hcT) l)
    · rw [show x = x * y⁻¹ * y by group, hql]
      exact T.mul_mem (T.mul_mem (hc.left_le hq) (T.zpow_mem (T.mul_mem hcT hcT) l)) hyT
  have hcK : c ∉ K := by
    have h := hK_iff1 1 Q.one_mem 1
    rw [one_mul, zpow_one] at h
    rw [h]
    exact Int.not_even_one
  have hcos : ∀ t ∈ T, t ∉ K → t * c ∈ K := by
    intro t ht htK
    obtain ⟨q, hq, i, rfl | rfl⟩ := hdec t ht
    · rw [hK_iff1 q hq i] at htK
      rw [mul_assoc, ← zpow_add_one, hK_iff1 q hq (i + 1)]
      exact Int.even_add_one.mpr htK
    · rw [hK_iff2 q hq i] at htK
      have h : q * c ^ i * y * c = q * c ^ (i - 1) * y := by
        calc q * c ^ i * y * c = q * c ^ i * (y * c * y⁻¹) * y := by group
          _ = q * c ^ (i - 1) * y := by rw [hyc, zpow_sub_one]; group
      rw [h, hK_iff2 q hq (i - 1)]
      exact Int.even_sub_one.mpr htK
  set M := 2 ^ (n - 1) with hM
  have hqM : ∀ q ∈ Q, q ^ M = 1 := fun q hq => by
    rw [hM, show n - 1 = n - 3 + 2 by omega, pow_add, mul_comm, pow_mul,
      show (2 : ℕ) ^ 2 = 4 by norm_num, hc.pow_four_eq_one_left hq, one_pow]
  have hcm : ∀ m : ℤ, (c ^ m) ^ M = e ^ m := fun m => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hce]
  have hpow1 : ∀ q ∈ Q, ∀ i : ℤ, (q * c ^ i) ^ M = e ^ i := fun q hq i => by
    rw [((show Commute q c from hcQ q hq).zpow_right i).mul_pow, hqM q hq, one_mul, hcm]
  have hsq2 : ∀ q ∈ Q, ∀ i : ℤ, q * c ^ i * y * (q * c ^ i * y) = 1 ∨
      q * c ^ i * y * (q * c ^ i * y) = e ∨ q * c ^ i * y * (q * c ^ i * y) = v ∨
      q * c ^ i * y * (q * c ^ i * y) = v * e := by
    intro q hq i
    have h1 : y * c ^ i * y⁻¹ = c ^ (-i) := by rw [← conj_zpow, hyc, inv_zpow, zpow_neg]
    have h2 : c ^ i * (y * q * y⁻¹) = (y * q * y⁻¹) * c ^ i :=
      ((show Commute (y * q * y⁻¹) c from hcQ _ (hc.normal_left y hyT q hq)).zpow_right i).eq.symm
    have h3 : q * c ^ i * y * (q * c ^ i * y) = q * (y * q * y⁻¹) * e := by
      calc q * c ^ i * y * (q * c ^ i * y) =
            q * (c ^ i * (y * q * y⁻¹)) * (y * c ^ i * y⁻¹) * (y * y) := by group
        _ = q * (y * q * y⁻¹) * e := by rw [h2, h1, hyy]; group
    rw [h3]
    rcases hc.mul_conj_mem hyT (hyy ▸ hc.mem_right) hfix hq with h | h | h | h <;> rw [h]
    · exact Or.inr (Or.inl (one_mul e))
    · exact Or.inl hc.centralElt_mul_self
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (hc.mul_centralElt_mul_centralElt v)))
  have heven : ∀ l : ℤ, e ^ (2 * l) = 1 := fun l => by
    rw [zpow_mul, zpow_two, hc.centralElt_mul_self, one_zpow]
  have hodd : ∀ l : ℤ, e ^ (2 * l + 1) = e := fun l => by rw [zpow_add_one, heven, one_mul]
  have heT : e ∈ T := hc.right_le hc.mem_right
  have hev : e ∈ Subgroup.zpowers v := by
    rw [← hvv]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v)
  have hcond : ∀ (m : ℤ) (a : G), a⁻¹ * c ^ m * a ∈ (S : Subgroup G) →
      (c ^ m ∈ K ↔ a⁻¹ * c ^ m * a ∈ K) := by
    intro m a ha
    rw [hST] at ha
    have hcmK : c ^ m ∈ K ↔ Even m := by
      have h := hK_iff1 1 Q.one_mem m
      rwa [one_mul] at h
    rw [hcmK]
    have hconj : ∀ x : G, a * (a⁻¹ * x * a) * a⁻¹ = x := fun x => by group
    obtain ⟨q, hq, i, hsi | hsi⟩ := hdec _ ha
    · rw [hsi, hK_iff1 q hq i]
      have hsM : (a⁻¹ * c ^ m * a) ^ M = e ^ m := by
        rw [show (a⁻¹ * c ^ m * a) ^ M = a⁻¹ * (c ^ m) ^ M * a by
          simpa using conj_pow (a := a⁻¹) (b := c ^ m) (i := M), hcm,
          hc.conj_eq_of_mem_zpowers_centralElt (Subgroup.zpow_mem_zpowers e m)]
      have h1 : e ^ i = e ^ m := by rw [← hpow1 q hq i, ← hsi, hsM]
      obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' m <;> obtain ⟨l', rfl | rfl⟩ := Int.even_or_odd' i
      · exact ⟨fun _ => even_two_mul l', fun _ => even_two_mul l⟩
      · rw [hodd, heven] at h1
        exact absurd h1 hc.centralElt_ne_one
      · rw [heven, hodd] at h1
        exact absurd h1.symm hc.centralElt_ne_one
      · exact ⟨fun h => absurd h (Int.not_even_two_mul_add_one l),
          fun h => absurd h (Int.not_even_two_mul_add_one l')⟩
    · exfalso
      set s := a⁻¹ * c ^ m * a with hs
      have hsQ : s ∉ Q ⊔ P₁ := by rw [hsi]; exact (hyQP _ (hqcs q hq i)).1
      rcases hsi ▸ hsq2 q hq i with h | h | h | h
      · have hs1 : s ≠ 1 := fun h' => hsQ (h' ▸ (Q ⊔ P₁).one_mem)
        exact hsQ (hc.involution_mem s ha (orderOf_eq_prime (by rw [pow_two]; exact h) hs1))
      · have h2 : c ^ m * c ^ m = e := by
          rw [← hconj (c ^ m * c ^ m), show a⁻¹ * (c ^ m * c ^ m) * a = s * s by rw [hs]; group,
            h, hc.conj_centralElt]
        rcases hc.eq_of_mem_right_of_isCyclic hcyc (P₁.zpow_mem hcP₁ m) h2 with h3 | h3
        · exact hrig s ha hsQ h a (by rw [hs, hconj, h3])
        · have hse : s * e * (s * e) = e := by
            calc s * e * (s * e) = s * s * (e * e) := by
                  rw [mul_assoc s e (s * e), ← mul_assoc e s e, ← he s]; group
              _ = e := by rw [h, hc.centralElt_mul_self, mul_one]
          refine hrig (s * e) (T.mul_mem ha heT) (fun h' => hsQ ?_) hse a ?_
          · simpa [hc.mul_centralElt_mul_centralElt] using
              (Q ⊔ P₁).mul_mem h' (Subgroup.mem_sup_right hc.mem_right)
          · rw [hc.conj_mul_centralElt, hs, hconj, h3, hc.mul_centralElt_mul_centralElt]
      all_goals
        have hsv : s * s ∈ Subgroup.zpowers v := by
          rw [h]
          first
            | exact Subgroup.mem_zpowers v
            | exact mul_centralElt_mem_zpowers hvv
        have h4 : s * s * (s * s) = e := by
          rw [h]
          first
            | exact hvv
            | exact hc.mul_centralElt_sq hvv
        have h5 : c ^ m * c ^ m * (c ^ m * c ^ m) = e := by
          rw [← hconj (c ^ m * c ^ m * (c ^ m * c ^ m)),
            show a⁻¹ * (c ^ m * c ^ m * (c ^ m * c ^ m)) * a = s * s * (s * s) by rw [hs]; group,
            h4, hc.conj_centralElt]
        have hmem : a⁻¹ * (c ^ m * c ^ m) * a ∈ Subgroup.zpowers v := by
          rw [show a⁻¹ * (c ^ m * c ^ m) * a = s * s by rw [hs]; group]
          exact hsv
        rcases hc.eq_of_mem_right_of_isCyclic hcyc (P₁.mul_mem (P₁.zpow_mem hcP₁ m)
          (P₁.zpow_mem hcP₁ m)) h5 with h6 | h6 <;> rw [h6] at hmem
        · exact hfus a⁻¹ (by rwa [inv_inv])
        · refine hfus a⁻¹ ?_
          rw [inv_inv]
          have h7 := Subgroup.mul_mem _ hmem hev
          rwa [hc.inv_conj_mul_centralElt, hc.mul_centralElt_mul_centralElt] at h7
  exact false_of_relIndex_eq_two hperf S (hST ▸ hKT)
    (hST ▸ relIndex_eq_two_of_mul_mem hcT hcK hcos) (hST ▸ hcT) hcK hcond

theorem false_of_isCyclic_of_isSylow [Finite G] (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁)
    (S : Sylow 2 G) (hST : (S : Subgroup G) = T) (hperf : Group.IsPerfect G) : False := by
  obtain ⟨c, n, hcP, hco, hn, hce⟩ := hc.exists_generator hcyc
  by_cases hT : T ≤ Q ⊔ P₁
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact hc.false_of_le_sup_of_zpowers_eq hperf hcyc S hST hT (hc.zpowers_self_eq_right hcP hco)
    · exact hc.false_of_le_sup_of_three_le hperf S hST hT hcP hco hn3 hce
  · obtain ⟨y, hyT, hy, hyy⟩ := hc.exists_mul_self_mem hT
    by_cases hPc : IsCyclic (P₁ ⊔ Subgroup.zpowers y : Subgroup G)
    · exact hc.false_of_isCyclic_sup hperf hcyc S hST hyT hy hyy hPc
    · obtain ⟨hyy', hyi⟩ := hc.mul_self_eq_and_inv_of_not_isCyclic hcyc hyT hy hyy hPc
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · obtain rfl : n = 2 := by omega
        exact hc.false_of_not_isCyclic_of_zpowers_eq hperf S hST hyT hy hyy'
          (hc.zpowers_self_eq_right hcP hco)
      · exact hc.false_of_not_isCyclic_of_three_le hperf hcyc S hST hcP hco hn3 hce hyT hy hyy'
          hyi

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
