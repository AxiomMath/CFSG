module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem Sec174.eq_add_one_of_dvd_three_mul {q c : ℕ} (hq : 4 ≤ q) (hc : c ≡ 1 [MOD q])
    (hc1 : c ≠ 1) (hdvd : c ∣ 3 * (q + 1)) : c = q + 1 := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hdvd
  have hmod : c % q = 1 := by
    have := hc; unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨m, hm⟩ := hdvd
  have hcq := Nat.div_add_mod c q
  rw [hmod] at hcq
  set k := c / q with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hcq; omega
    · exact h
  have hcle : c ≤ 3 * (q + 1) := Nat.le_of_dvd (by omega) ⟨m, hm⟩
  have hk3 : k ≤ 3 := by nlinarith
  have hm3 : m ≤ 3 := by nlinarith
  interval_cases k <;> interval_cases m <;> omega

theorem Sec174.exists_pgroup_lt_normalizer {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact (Nat.Prime p)] (R Q : Subgroup G) (hQ : IsPGroup p Q) (hlt : R < Q) :
    ∃ E : Subgroup G, R < E ∧ IsPGroup p E ∧ E ≤ Q ⊓ normalizer (R : Set G) := by
  let W := R.subgroupOf Q
  let N := normalizer (W : Set Q)
  have hmap : W.map Q.subtype = R := Subgroup.map_subgroupOf_eq_of_le hlt.le
  have _ : Group.IsNilpotent Q := hQ.isNilpotent
  have hstrict : W < N := by
    apply lt_of_le_of_ne Subgroup.le_normalizer
    intro heq
    have htop : W = ⊤ :=
      normalizerCondition_iff_only_full_group_self_normalizing.mp
        Group.normalizerCondition_of_isNilpotent W heq.symm
    have hequal : R = Q := by
      apply le_antisymm hlt.le
      intro x hx
      have hW : (⟨x, hx⟩ : Q) ∈ W := by rw [htop]; trivial
      exact hW
    exact hlt.ne hequal
  refine ⟨N.map Q.subtype, ?_, (hQ.to_subgroup N).map Q.subtype, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_subtype_lt_map_subtype.mpr hstrict
  · refine le_inf (Subgroup.map_subtype_le N) ?_
    have h := Subgroup.le_normalizer_map Q.subtype (H := W)
    rw [hmap] at h
    exact h

theorem Sec174.card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl

theorem Sec174.le_of_card_dvd {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {π : G →* Equiv.Perm (Fin 3)} (hπk : π.ker = T) {A : Subgroup G}
    (hdiv3 : T.relIndex A ∣ 3)
    (hN2 : ∀ x : G, Odd (orderOf x) → (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A)
    (hTo : ∀ x ∈ T, Odd (orderOf x))
    (hG : Nat.card G = 6 * Nat.card T)
    (hAdvd : Nat.card A ∣ Nat.card T) : A ≤ T := by
  by_contra hAT
  have h3 : T.relIndex A = 3 := by
    have hne : T.relIndex A ≠ 1 := fun h => hAT (Subgroup.relIndex_eq_one.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
    · exact absurd h hne
    · exact h
  have hAT3 : (A ⊓ T).relIndex A = 3 := by rw [inf_comm, Subgroup.inf_relIndex_right]; exact h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R⟩ : Nonempty (Sylow 3 ↥A) := inferInstance
  set R' : Subgroup G := (R : Subgroup ↥A).map A.subtype with hR'
  have hR'A : R' ≤ A := Subgroup.map_subtype_le _
  have hR'p : IsPGroup 3 R' := R.isPGroup'.map A.subtype
  have hR'idx : ¬ 3 ∣ R'.relIndex A := by
    have : R'.subgroupOf A = R := Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
    rw [Subgroup.relIndex, this]
    exact R.not_dvd_index
  have hR'T : ¬ R' ≤ T := by
    intro h
    apply hR'idx
    have hle : R' ≤ A ⊓ T := le_inf hR'A h
    rw [← Subgroup.relIndex_mul_relIndex R' (A ⊓ T) A hle inf_le_left, hAT3]
    exact dvd_mul_left 3 _
  have hAsup : A ≤ R' ⊔ (A ⊓ T) := by
    have hle1 : A ⊓ T ≤ R' ⊔ (A ⊓ T) := le_sup_right
    have hle2 : R' ⊔ (A ⊓ T) ≤ A := sup_le hR'A inf_le_left
    have h := Subgroup.relIndex_mul_relIndex (A ⊓ T) (R' ⊔ (A ⊓ T)) A hle1 hle2
    rw [hAT3] at h
    have hne : (A ⊓ T).relIndex (R' ⊔ (A ⊓ T)) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hR'T (le_sup_left.trans (h1.trans inf_le_right))
    have h2 : (R' ⊔ (A ⊓ T)).relIndex A = 1 := by
      have hd : (R' ⊔ (A ⊓ T)).relIndex A ∣ 3 := Dvd.intro_left _ h
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h' | h'
      · exact h'
      · exfalso; rw [h'] at h; apply hne; omega
    exact Subgroup.relIndex_eq_one.mp h2
  have hπR : Nat.card ↥(R'.map π) = 3 := by
    have h1 : T.relIndex R' = Nat.card ↥(R'.map π) := by
      rw [← hπk]; exact Subgroup.relIndex_ker R' π
    have h2 : T.relIndex A = Nat.card ↥(A.map π) := by
      rw [← hπk]; exact Subgroup.relIndex_ker A π
    have hd : Nat.card ↥(R'.map π) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (Subgroup.map_mono (f := π) hR'A)
      rwa [← h2, h3] at this
    have hne : Nat.card ↥(R'.map π) ≠ 1 := by
      rw [← h1]; intro h; exact hR'T (Subgroup.relIndex_eq_one.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨Q, hRQ⟩ := hR'p.exists_le_sylow
  obtain ⟨k, hk⟩ := hR'p.exists_card_eq
  have hQcard : 3 ^ (k + 1) ∣ Nat.card (Q : Subgroup G) := by
    apply Q.pow_dvd_card_of_pow_dvd_card
    rw [hG, pow_succ, ← hk]
    obtain ⟨m, hm⟩ := (Subgroup.card_dvd_of_le hR'A).trans hAdvd
    exact ⟨2 * m, by rw [hm]; ring⟩
  have hRQlt : R' < Q := by
    refine lt_of_le_of_ne hRQ fun h => ?_
    rw [← h, hk] at hQcard
    have := Nat.le_of_dvd (by positivity) hQcard
    have h1 := Nat.one_le_pow k 3 (by norm_num)
    rw [pow_succ] at this
    omega
  have hπQ : (Q : Subgroup G).map π = R'.map π := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hRQ)
    rw [hπR]
    obtain ⟨j, hj⟩ := (Q.isPGroup'.map π).exists_card_eq
    have h6 : Nat.card ↥((Q : Subgroup G).map π) ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card ((Q : Subgroup G).map π)
      rwa [Sec174.card_perm_fin_three] at this
    rw [hj] at h6 ⊢
    have : j ≤ 1 := by
      by_contra hj1
      have h9 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega : 2 ≤ j)).trans h6
      norm_num at h9
    interval_cases j <;> norm_num
  obtain ⟨E, hRE, hEp, hEle⟩ := Sec174.exists_pgroup_lt_normalizer 3 R' Q Q.isPGroup' hRQlt
  have hEA : E ≤ A := by
    intro y hy
    have hyQ : y ∈ (Q : Subgroup G) := (Subgroup.mem_inf.mp (hEle hy)).1
    have hyN : y ∈ normalizer (R' : Set G) := (Subgroup.mem_inf.mp (hEle hy)).2
    have hπy : π y ∈ R'.map π := by rw [← hπQ]; exact Subgroup.mem_map_of_mem π hyQ
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp hπy
    set f := r⁻¹ * y with hf
    have hfT : f ∈ T := by
      rw [← hπk, MonoidHom.mem_ker, hf, map_mul, map_inv, hry, inv_mul_cancel]
    have hfN : ∀ x ∈ R', f * x * f⁻¹ ∈ R' := by
      intro x hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hyN x).mp hx
      have h2 := R'.mul_mem (R'.mul_mem (R'.inv_mem hr) h1) hr
      rwa [show r⁻¹ * (y * x * y⁻¹) * r = f * x * f⁻¹ by rw [hf]; group] at h2
    have hfA : ∀ a ∈ A, f * a * f⁻¹ ∈ A := by
      intro a ha
      have hle : (R' ⊔ (A ⊓ T)).map (MulAut.conj f).toMonoidHom ≤ R' ⊔ (A ⊓ T) := by
        rw [Subgroup.map_sup]
        apply sup_le_sup
        · rintro _ ⟨x, hx, rfl⟩
          exact hfN x hx
        · rintro _ ⟨x, hx, rfl⟩
          show f * x * f⁻¹ ∈ A ⊓ T
          rw [hTc f hfT x (Subgroup.mem_inf.mp hx).2, mul_assoc, mul_inv_cancel, mul_one]
          exact hx
      exact (sup_le hR'A inf_le_left) (hle ⟨a, hAsup ha, rfl⟩)
    have hfA' : f ∈ A := hN2 f (hTo f hfT) hfA
    have : y = r * f := by rw [hf]; group
    rw [this]
    exact A.mul_mem (hR'A hr) hfA'
  have hEsub : IsPGroup 3 (E.subgroupOf A) := hEp.comap_of_injective A.subtype A.subtype_injective
  have hRE' : (R : Subgroup ↥A) ≤ E.subgroupOf A := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hRE.le ⟨x, hx, rfl⟩)
  have heq := R.is_maximal' hEsub hRE'
  apply hRE.not_ge
  intro y hy
  have : (⟨y, hEA hy⟩ : ↥A) ∈ E.subgroupOf A := Subgroup.mem_subgroupOf.mpr hy
  rw [heq] at this
  exact ⟨_, this, rfl⟩

theorem Sec174.frame_contra {G : Type*} [Group G] [Finite G] {T : Subgroup G} [T.Normal]
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hTodd : Odd (Nat.card T))
    {π : G →* Equiv.Perm (Fin 3)} (hπs : Function.Surjective π) (hπk : π.ker = T)
    {s : G} (hs2 : s * s = 1) {q : ℕ} (hq : 4 ≤ q)
    (hTcard : Nat.card T = (q + 1) * Nat.card ↥(T ⊓ centralizer ({s} : Set G)))
    {A : Subgroup G} (hA : Odd (Nat.card A)) (hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A)
    (hN : ∀ x : G, (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A ∨ x * s ∈ A)
    (hCT : A ⊓ centralizer ({s} : Set G) ≤ T)
    (hc1 : (centralizer ({s} : Set G)).relIndex A ≡ 1 [MOD q])
    (hc2 : (centralizer ({s} : Set G)).relIndex A ≠ 1) : False := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsq : ∀ x : G, x * s ∈ A → x * x ∈ A := by
    intro x hx
    have h1 := A.mul_mem hx (hsA _ hx)
    rwa [hsi, show x * s * (s * (x * s) * s) = x * (s * s) * x * (s * s) by group, hs2,
      mul_one, mul_one] at h1
  have hmem_of_sq : ∀ {H : Subgroup G} {x : G}, Odd (orderOf x) → x * x ∈ H → x ∈ H := by
    intro H x hodd hx2
    obtain ⟨m, hm⟩ := hodd
    have h1 : x = (x * x) ^ (m + 1) := by
      have h2 : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
      calc x = x * x ^ (2 * m + 1) := by rw [h2, mul_one]
        _ = (x * x) ^ (m + 1) := by
          rw [← pow_two, ← pow_mul, ← pow_succ']
          congr 1
    rw [h1]
    exact H.pow_mem hx2 (m + 1)
  have hN2 : ∀ x : G, Odd (orderOf x) → (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A := by
    intro x hodd hx
    rcases hN x hx with h | h
    · exact h
    · exact hmem_of_sq hodd (hsq x h)
  have hTo : ∀ x ∈ T, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hTodd (Subgroup.orderOf_dvd_natCard T hx)
  have hG : Nat.card G = 6 * Nat.card T := by
    have h1 : Nat.card (G ⧸ π.ker) = 6 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv,
        Sec174.card_perm_fin_three]
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [h1, hπk] at h2
    exact h2
  have hdiv3 : T.relIndex A ∣ 3 := by
    have h1 : T.relIndex A = Nat.card ↥(A.map π) := by
      rw [← hπk]; exact Subgroup.relIndex_ker A π
    have h6 : Nat.card ↥(A.map π) ∣ 2 * 3 := by
      have := Subgroup.card_subgroup_dvd_card (A.map π)
      rwa [Sec174.card_perm_fin_three] at this
    have hcop : Nat.Coprime (Nat.card ↥(A.map π)) 2 := by
      have hodd : Odd (Nat.card ↥(A.map π)) := Odd.of_dvd_nat hA (Subgroup.card_map_dvd A π)
      exact Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by
        rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd))
    rw [h1]
    exact hcop.dvd_of_dvd_mul_left h6
  set C : Subgroup G := centralizer ({s} : Set G) with hC
  set Cs : Subgroup G := T ⊓ C with hCs
  have hCsT : Cs.relIndex T = q + 1 := by
    have h1 := Subgroup.relIndex_mul_card Cs T
    rw [show Cs ⊓ T = Cs from inf_eq_left.mpr inf_le_left, hTcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hdivq : C.relIndex (A ⊓ T) ∣ q + 1 := by
    set N : Subgroup T := Cs.subgroupOf T with hNdef
    set H : Subgroup T := (A ⊓ T).subgroupOf T with hHdef
    have hNn : N.Normal := ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hTc _ g.2 _ n.2, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]; exact hn⟩
    have h1 := Subgroup.relIndex_sup_left H N
    have h2 := Subgroup.relIndex_mul_relIndex N (N ⊔ H) ⊤ le_sup_left le_top
    rw [Subgroup.relIndex_top_right N] at h2
    have h3 : N.index = q + 1 := hCsT
    have h4 : N.relIndex H = Cs.relIndex (A ⊓ T) := Subgroup.relIndex_subgroupOf inf_le_right
    have h5 : Cs.relIndex (A ⊓ T) = C.relIndex (A ⊓ T) := by
      rw [← Subgroup.inf_relIndex_right Cs, ← Subgroup.inf_relIndex_right C (A ⊓ T)]
      congr 1
      ext x
      constructor
      · intro hx
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2,
          (Subgroup.mem_inf.mp hx).2⟩
      · intro hx
        obtain ⟨hxC, hxAT⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxAT).2, hxC⟩,
          hxAT⟩
    rw [← h5, ← h4, ← h1, ← h3, ← h2]
    exact dvd_mul_right _ _
  have hcmul : C.relIndex A = C.relIndex (A ⊓ T) * T.relIndex A := by
    have h1 := Subgroup.relIndex_inf_mul_relIndex C T A
    rw [inf_comm T A] at h1
    rw [h1, ← Subgroup.inf_relIndex_right (C ⊓ T), ← Subgroup.inf_relIndex_right C A]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨hxC, hxA⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxC, hCT (Subgroup.mem_inf.mpr ⟨hxA, hxC⟩)⟩,
        hxA⟩
    · intro hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1,
        (Subgroup.mem_inf.mp hx).2⟩
  have hc : C.relIndex A = q + 1 := by
    refine Sec174.eq_add_one_of_dvd_three_mul hq hc1 hc2 ?_
    rw [hcmul, mul_comm 3]
    exact mul_dvd_mul hdivq hdiv3
  have hAdvd : Nat.card A ∣ Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card C A
    rw [hc] at h1
    rw [← h1, hTcard]
    refine mul_dvd_mul_left _ (Subgroup.card_dvd_of_le ?_)
    intro x hx
    obtain ⟨hxC, hxA⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hCT (Subgroup.mem_inf.mpr ⟨hxA, hxC⟩), hxC⟩
  have hAT : A ≤ T := Sec174.le_of_card_dvd hTc hπk hdiv3 hN2 hTo hG hAdvd
  have hTA : T ≤ A := fun f hf => hN2 f (hTo f hf) fun a ha => by
    rw [hTc f hf a (hAT ha), mul_assoc, mul_inv_cancel, mul_one]; exact ha
  have hsqπ : ∀ x : G, π x * π x = 1 := by
    intro x
    have hxN : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha =>
      hTA ((‹T.Normal›).conj_mem a (hAT ha) x)
    have hx2 : x * x ∈ T := by
      rcases hN x hxN with h | h
      · exact T.mul_mem (hAT h) (hAT h)
      · have h1 := T.mul_mem (hAT h) ((‹T.Normal›).conj_mem _ (hAT h) s)
        rwa [show x * s * (s * (x * s) * s⁻¹) = x * (s * s) * x by group, hs2, mul_one] at h1
    rw [← map_mul]
    rw [← hπk] at hx2
    exact hx2
  have : ¬ ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 := by decide
  exact this fun σ => by
    obtain ⟨x, rfl⟩ := hπs σ
    exact hsqπ x

end CFSG.GH74.Uniqueness
