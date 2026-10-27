module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.QuasithinUnique.DS

variable {P : Type*} [Group P] [Finite P]

structure DSData (R : Subgroup P) : Prop where
  two : IsPGroup 2 P
  cyclic : IsCyclic R
  index_two : R.index = 2
  four_le : 4 ≤ Nat.card R
  cent : ∀ g : P, g ∉ R → ∀ r ∈ R, g * r = r * g → r * r = 1

variable {R : Subgroup P}

omit [Finite P] in
theorem DSData.normal (h : DSData R) : R.Normal := Subgroup.normal_of_index_eq_two h.index_two

theorem DSData.exists_invol (h : DSData R) :
    ∃ z ∈ R, z ≠ 1 ∧ z * z = 1 ∧ ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = z := by
  obtain ⟨g, hg⟩ := h.cyclic.exists_generator
  have hR2 : IsPGroup 2 R := h.two.to_subgroup R
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 := h.four_le
    omega
  have hord : orderOf g = 2 ^ k := by
    rw [← hk]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  set z : P := ((g : P)) ^ (2 ^ (k - 1)) with hz
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hzR : z ∈ R := R.pow_mem g.2 _
  have hz1 : z ≠ 1 := by
    intro h1
    have h1' : g ^ (2 ^ (k - 1)) = 1 := Subtype.ext h1
    have := orderOf_dvd_of_pow_eq_one h1'
    rw [hord] at this
    have hpos : 0 < 2 ^ (k - 1) := by positivity
    have := Nat.le_of_dvd hpos this
    omega
  have hzz : z * z = 1 := by
    rw [hz, ← pow_add, ← two_mul, ← h2k]
    have : (g : P) ^ (2 ^ k) = ((g ^ (2 ^ k) : ↥R) : P) := rfl
    rw [this, ← hord, pow_orderOf_eq_one]
    rfl
  refine ⟨z, hzR, hz1, hzz, ?_⟩
  intro r hrR hr2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨r, hrR⟩)
  have hri : r = (g : P) ^ i := by
    have := congrArg Subtype.val hi
    simpa using this.symm
  have h2i : (g : P) ^ (2 * i) = 1 := by
    rw [two_mul, zpow_add, ← hri]; exact hr2
  have h2i' : g ^ (2 * i) = 1 := Subtype.ext (by simpa using h2i)
  have hdvd : ((2 ^ k : ℕ) : ℤ) ∣ 2 * i := by
    rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr h2i'
  have hdvd' : ((2 ^ (k - 1) : ℕ) : ℤ) ∣ i := by
    rw [h2k] at hdvd
    push_cast at hdvd ⊢
    have h2ne : (2 : ℤ) ≠ 0 := by norm_num
    exact (mul_dvd_mul_iff_left h2ne).mp (by simpa [mul_comm] using hdvd)
  obtain ⟨j, hj⟩ := hdvd'
  have : r = z ^ j := by
    rw [hri, hj, zpow_mul, hz, zpow_natCast]
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · left
    rw [this]
    obtain ⟨m, hm⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
    rw [hm, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
    rw [this]; simp
  · right
    rw [this]
    obtain ⟨m, hm⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
    rw [this]; simp

noncomputable def DSData.z (h : DSData R) : P := Classical.choose h.exists_invol

theorem DSData.z_mem (h : DSData R) : h.z ∈ R := (Classical.choose_spec h.exists_invol).1

theorem DSData.z_ne_one (h : DSData R) : h.z ≠ 1 := (Classical.choose_spec h.exists_invol).2.1

theorem DSData.z_mul_self (h : DSData R) : h.z * h.z = 1 :=
  (Classical.choose_spec h.exists_invol).2.2.1

theorem DSData.eq_one_or_eq_z (h : DSData R) {r : P} (hr : r ∈ R) (hr2 : r * r = 1) :
    r = 1 ∨ r = h.z := (Classical.choose_spec h.exists_invol).2.2.2 r hr hr2

omit [Finite P] in
theorem DSData.mem_of_central (h : DSData R) {c : P} (hc : ∀ p : P, c * p = p * c) : c ∈ R := by
  by_contra hcR
  obtain ⟨g, hg⟩ := h.cyclic.exists_generator
  have h1 : (g : P) * (g : P) = 1 := h.cent c hcR g.1 g.2 (hc g)
  have h2 : g * g = 1 := Subtype.ext h1
  have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h2)
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 : orderOf g = Nat.card R := orderOf_eq_card_of_forall_mem_zpowers hg
  have := h.four_le
  omega

omit [Finite P] in
theorem card_le_mul_inf_of_index_two (hR : R.index = 2) (C : Subgroup P) :
    Nat.card C ≤ Nat.card ↥(C ⊓ R) * 2 := by
  have hnorm : R.Normal := Subgroup.normal_of_index_eq_two hR
  have h1 := Subgroup.card_mul_index ((C ⊓ R).subgroupOf C)
  have h2 : Nat.card ↥((C ⊓ R).subgroupOf C) = Nat.card ↥(C ⊓ R) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ R ≤ C)).toEquiv
  have h3 : ((C ⊓ R).subgroupOf C).index = R.relIndex C := by
    rw [← Subgroup.relIndex, Subgroup.inf_relIndex_left]
  have h4 : R.relIndex C ∣ 2 := hR ▸ Subgroup.relIndex_dvd_index_of_normal R C
  have h5 : R.relIndex C ≤ 2 := Nat.le_of_dvd (by norm_num) h4
  rw [h2, h3] at h1
  calc Nat.card C = Nat.card ↥(C ⊓ R) * R.relIndex C := h1.symm
    _ ≤ Nat.card ↥(C ⊓ R) * 2 := Nat.mul_le_mul_left _ h5

theorem DSData.card_le_two_of_sq (h : DSData R) (D : Subgroup P) (hDR : D ≤ R)
    (hD : ∀ r ∈ D, r * r = 1) : Nat.card D ≤ 2 := by
  have hsub : (D : Set P) ⊆ {1, h.z} := by
    intro r hr
    rcases h.eq_one_or_eq_z (hDR hr) (hD r hr) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have h1 : Nat.card D = Set.ncard (D : Set P) := Nat.card_coe_set_eq (D : Set P)
  rw [h1]
  calc Set.ncard (D : Set P) ≤ Set.ncard ({1, h.z} : Set P) := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp

theorem DSData.card_centralizer_le (h : DSData R) {g : P} (hg : g ∉ R) :
    Nat.card (Subgroup.centralizer ({g} : Set P)) ≤ 4 := by
  have h1 := card_le_mul_inf_of_index_two h.index_two (Subgroup.centralizer ({g} : Set P))
  have h2 : Nat.card ↥(Subgroup.centralizer ({g} : Set P) ⊓ R) ≤ 2 := by
    refine h.card_le_two_of_sq _ inf_le_right fun r hr => ?_
    refine h.cent g hg r hr.2 ?_
    exact Subgroup.mem_centralizer_iff.mp hr.1 g (by simp)
  omega

structure IsFour (E : Subgroup P) : Prop where
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  sq : ∀ x ∈ E, x * x = 1
  card : Nat.card E = 4

omit [Finite P] in
theorem DSData.comm (h : DSData R) {x y : P} (hx : x ∈ R) (hy : y ∈ R) : x * y = y * x := by
  have := h.cyclic
  have h1 : (⟨x, hx⟩ : R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    (IsMulCommutative.is_comm (M := ↥R)).comm _ _
  exact congrArg Subtype.val h1

theorem DSData.exists_not_mem_four (h : DSData R) {E : Subgroup P} (hE : IsFour E) :
    ∃ g ∈ E, g ∉ R := by
  by_contra hcon
  push Not at hcon
  have := h.card_le_two_of_sq E (fun x hx => hcon x hx) hE.sq
  have := hE.card
  omega

theorem DSData.mem_of_commutes_four (h : DSData R) {E : Subgroup P} (hE : IsFour E) {c : P}
    (hc : ∀ e ∈ E, c * e = e * c) : c ∈ E := by
  obtain ⟨g, hgE, hgR⟩ := h.exists_not_mem_four hE
  have hle : E ≤ Subgroup.centralizer ({g} : Set P) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    rw [hg']
    exact hE.comm g hgE e he
  have hcard := h.card_centralizer_le hgR
  have heq : E = Subgroup.centralizer ({g} : Set P) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hE.card]; exact hcard)
  rw [heq]
  rw [Subgroup.mem_centralizer_iff]
  intro g' hg'
  rw [Set.mem_singleton_iff] at hg'
  rw [hg']
  exact (hc g hgE).symm

theorem DSData.z_mem_four (h : DSData R) {E : Subgroup P} (hE : IsFour E) : h.z ∈ E := by
  have h1 := card_le_mul_inf_of_index_two h.index_two E
  by_contra hz
  have hall : ∀ r ∈ E ⊓ R, r = 1 := by
    intro r hr
    rcases h.eq_one_or_eq_z hr.2 (hE.sq r hr.1) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hr.1) hz
  have hbot : E ⊓ R = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
  have : Nat.card ↥(E ⊓ R) = 1 := by rw [hbot]; exact Subgroup.card_bot
  have := hE.card
  omega

theorem DSData.card_elemAbelian_le (h : DSData R) {E : Subgroup P}
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have h1 := card_le_mul_inf_of_index_two h.index_two E
  have h2 : Nat.card ↥(E ⊓ R) ≤ 2 :=
    h.card_le_two_of_sq _ inf_le_right fun r hr => hsq r hr.1
  omega

omit [Finite P] in
theorem DSData.commutator_mem (h : DSData R) (a b : P) : a * b * a⁻¹ * b⁻¹ ∈ R := by
  have hR := h.index_two
  have key : ∀ x : P, x⁻¹ ∈ R ↔ x ∈ R := fun x => R.inv_mem_iff
  rw [Subgroup.mul_mem_iff_of_index_two hR]
  rw [Subgroup.mul_mem_iff_of_index_two hR, Subgroup.mul_mem_iff_of_index_two hR, key, key]
  tauto

theorem DSData.z_mem_commutator (h : DSData R) {Q : Subgroup P} (hQ : ¬ Q ≤ R) {ρ : P}
    (hρQ : ρ ∈ Q) (hρR : ρ ∈ R) (hρ : ρ * ρ ≠ 1) : h.z ∈ ⁅Q, Q⁆ := by
  have hQ' : ∃ e ∈ Q, e ∉ R := by
    by_contra hcon; push Not at hcon; exact hQ hcon
  obtain ⟨e, heQ, heR⟩ := hQ'
  set c : P := e * ρ * e⁻¹ * ρ⁻¹ with hc
  have hcQ : c ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator heQ hρQ
  have hcR : c ∈ R := h.commutator_mem e ρ
  have hc1 : c ≠ 1 := by
    intro h1
    apply hρ
    have hcomm : e * ρ = ρ * e := by
      have : e * ρ * e⁻¹ = ρ := by
        calc e * ρ * e⁻¹ = (e * ρ * e⁻¹ * ρ⁻¹) * ρ := by group
          _ = ρ := by rw [← hc, h1, one_mul]
      calc e * ρ = e * ρ * e⁻¹ * e := by group
        _ = ρ * e := by rw [this]
    exact h.cent e heR ρ hρR hcomm
  obtain ⟨k, hk⟩ := h.two c
  have hord : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨s, hs, hos⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hos
      exact hc1 (orderOf_eq_one_iff.mp hos)
    · exact h0
  set c' : P := c ^ 2 ^ (s - 1) with hc'
  have hc'R : c' ∈ R := R.pow_mem hcR _
  have hc'Q : c' ∈ ⁅Q, Q⁆ := Subgroup.pow_mem _ hcQ _
  have hc'2 : c' * c' = 1 := by
    rw [hc', ← pow_add, ← two_mul, ← pow_succ']
    have : s - 1 + 1 = s := by omega
    rw [this, ← hos]; exact pow_orderOf_eq_one c
  have hc'1 : c' ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hos] at this
    have hle := Nat.le_of_dvd (by positivity) this
    have : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rcases h.eq_one_or_eq_z hc'R hc'2 with h1 | h1
  · exact absurd h1 hc'1
  · rw [← h1]; exact hc'Q

theorem commutative_of_card_le_four_type {B : Type*} [Group B] [Finite B] (hB2 : IsPGroup 2 B)
    (h4 : Nat.card B ≤ 4) : ∀ x y : B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hB2.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  interval_cases k
  · have : Nat.card B = 1 := by simpa using hk
    have : Subsingleton B := (Nat.card_eq_one_iff_unique.mp this).1
    intro x y; exact Subsingleton.elim _ _
  · have : Nat.card B = 2 := by simpa using hk
    have : IsCyclic B := isCyclic_of_prime_card this
    intro x y; exact (IsMulCommutative.is_comm (M := B)).comm x y
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := B) (by simpa using hk)
    intro x y; exact (IsMulCommutative.is_comm (M := B)).comm x y

omit [Finite P] in
theorem commutative_of_card_le_four {B : Subgroup P} (hB2 : IsPGroup 2 B) [Finite B]
    (h4 : Nat.card B ≤ 4) : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  exact congrArg Subtype.val (commutative_of_card_le_four_type hB2 h4 ⟨a, ha⟩ ⟨b, hb⟩)

theorem commutator_le_of_card_le {S N : Subgroup P} (hN : N ≤ S)
    (hnorm : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hS2 : IsPGroup 2 S)
    (hcard : Nat.card S ≤ 4 * Nat.card N) : ⁅S, S⁆ ≤ N := by
  have hN' : (N.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN]
    intro n s hn hs
    exact hnorm s hs n hn
  have hQ2 : IsPGroup 2 (↥S ⧸ N.subgroupOf S) := hS2.to_quotient (N.subgroupOf S)
  have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf S)
  have hc2 : Nat.card (N.subgroupOf S) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hQcard : Nat.card (↥S ⧸ N.subgroupOf S) ≤ 4 := by
    rw [hc2] at hc1
    have : Nat.card (↥S ⧸ N.subgroupOf S) * Nat.card N ≤ 4 * Nat.card N := by
      rw [← hc1]; exact hcard
    exact Nat.le_of_mul_le_mul_right this hpos
  have hcomm := commutative_of_card_le_four_type hQ2 hQcard
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have h1 : (QuotientGroup.mk (⟨b⁻¹, S.inv_mem hb⟩ : ↥S) : ↥S ⧸ N.subgroupOf S) *
      QuotientGroup.mk (⟨a⁻¹, S.inv_mem ha⟩ : ↥S) =
      QuotientGroup.mk (⟨a⁻¹, S.inv_mem ha⟩ : ↥S) * QuotientGroup.mk (⟨b⁻¹, S.inv_mem hb⟩ : ↥S) :=
    hcomm _ _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  have h2 := Subgroup.mem_subgroupOf.mp h1
  have h3 : ((((⟨b⁻¹, S.inv_mem hb⟩ : ↥S) * ⟨a⁻¹, S.inv_mem ha⟩)⁻¹ *
      ((⟨a⁻¹, S.inv_mem ha⟩ : ↥S) * ⟨b⁻¹, S.inv_mem hb⟩) : ↥S) : P) = a * b * a⁻¹ * b⁻¹ := by
    show ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) : P) = _
    group
  rw [h3] at h2
  exact h2

theorem DSData.central_in_nonabelian (h : DSData R) {B : Subgroup P}
    (hB : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) {c : P}
    (hc : ∀ b ∈ B, b * c = c * b) : c = 1 ∨ c = h.z := by
  obtain ⟨g, hgB, hgR⟩ : ∃ g ∈ B, g ∉ R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, b, hb, hab⟩ := hB
    exact hab (h.comm (hcon a ha) (hcon b hb))
  by_cases hcR : c ∈ R
  · exact h.eq_one_or_eq_z hcR (h.cent g hgR c hcR (hc g hgB))
  · exfalso
    have hsq : ∀ r ∈ B ⊓ R, r * r = 1 := fun r hr => h.cent c hcR r hr.2 (hc r hr.1).symm
    have h2 : Nat.card ↥(B ⊓ R) ≤ 2 := h.card_le_two_of_sq _ inf_le_right hsq
    have h3 := card_le_mul_inf_of_index_two h.index_two B
    have h4 : Nat.card B ≤ 4 := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := hB
    exact hab (commutative_of_card_le_four (h.two.to_subgroup B) h4 a ha b hb)

theorem DSData.abelian_centralizer (h : DSData R) (h8 : 8 ≤ Nat.card R) {B : Subgroup P}
    (h4 : 4 ≤ Nat.card B)
    (hidx : (Subgroup.centralizer (B : Set P)).index ≤ 2) :
    B ≤ R ∧ Subgroup.centralizer (B : Set P) = R := by
  have hBR : B ≤ R := by
    by_contra hcon
    obtain ⟨g, hgB, hgR⟩ : ∃ g ∈ B, g ∉ R := by
      by_contra h'
      push Not at h'
      exact hcon h'
    have hle : Subgroup.centralizer (B : Set P) ≤ Subgroup.centralizer ({g} : Set P) :=
      Subgroup.centralizer_le (by simpa using hgB)
    have h1 := h.card_centralizer_le hgR
    have h2 := Subgroup.card_le_of_le hle
    have h3 := Subgroup.card_mul_index (Subgroup.centralizer (B : Set P))
    have h5 := Subgroup.card_mul_index R
    rw [h.index_two] at h5
    have h6 : Nat.card (Subgroup.centralizer (B : Set P)) * (Subgroup.centralizer (B : Set P)).index
        ≤ 4 * 2 := Nat.mul_le_mul (h2.trans h1) hidx
    omega
  refine ⟨hBR, le_antisymm ?_ ?_⟩
  · intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc
    by_contra hcR
    have : ∃ b ∈ B, b * b ≠ 1 := by
      by_contra hno
      push Not at hno
      have := h.card_le_two_of_sq B hBR hno
      omega
    obtain ⟨b, hbB, hb⟩ := this
    exact hb (h.cent c hcR b (hBR hbB) (hc b hbB).symm)
  · intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.comm (hBR hb) hr

omit [Finite P] in
theorem exists_zpow_inv (k : ℕ) {w : ℤ} (hw : w % 2 = 1) :
    ∃ w' : ℤ, ∀ r : P, r ^ (2 ^ k) = 1 → r ^ (w * w') = r := by
  have hcop : IsCoprime w ((2 : ℤ) ^ k) := by
    have : IsCoprime w 2 := ⟨1, (1 - w) / 2, by omega⟩
    exact this.pow_right
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, fun r hr => ?_⟩
  have h1 : r ^ (w * u) = r ^ (1 - v * 2 ^ k) := by congr 1; linarith
  have h2 : r ^ ((2 : ℤ) ^ k) = 1 := by
    have : (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast]; exact hr
  have h3 : r ^ (v * (2 : ℤ) ^ k) = 1 := by
    rw [mul_comm, zpow_mul, h2, one_zpow]
  rw [h1, zpow_sub, zpow_one, h3, inv_one, mul_one]

theorem DSData.exists_conj_four (h : DSData R) {Q : Subgroup P} (hQ : Q.index = 2)
    (hQR : ¬ Q ≤ R) {E E' : Subgroup P} (hE : IsFour E) (hE' : IsFour E') (hEQ : E ≤ Q)
    (hE'Q : E' ≤ Q) : ∃ p ∈ R, ∀ x ∈ E, p * x * p⁻¹ ∈ E' := by
  have hz : h.z ∈ E := h.z_mem_four hE
  have hz' : h.z ∈ E' := h.z_mem_four hE'
  obtain ⟨a, haE, haR⟩ := h.exists_not_mem_four hE
  obtain ⟨a', ha'E', ha'R⟩ := h.exists_not_mem_four hE'
  have hR2 : IsPGroup 2 R := h.two.to_subgroup R
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  obtain ⟨g, hg⟩ := h.cyclic.exists_generator
  have hordg : orderOf g = 2 ^ k := by
    rw [← hk]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hgk : (g : P) ^ (2 ^ k) = 1 := by
    have : g ^ (2 ^ k) = 1 := by rw [← hordg]; exact pow_orderOf_eq_one g
    simpa using congrArg Subtype.val this
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 := h.four_le
    omega
  have hRk : ∀ r ∈ R, r ^ (2 ^ k) = 1 := by
    intro r hr
    have := pow_card_eq_one' (G := ↥R) (x := ⟨r, hr⟩)
    rw [hk] at this
    simpa using congrArg Subtype.val this
  have huR : a⁻¹ * a' ∈ R := (Subgroup.mul_mem_iff_of_index_two h.index_two).mpr
    ⟨fun h1 => absurd (R.inv_mem_iff.mp h1) haR, fun h1 => absurd h1 ha'R⟩
  have huQ : a⁻¹ * a' ∈ Q := Q.mul_mem (Q.inv_mem (hEQ haE)) (hE'Q ha'E')
  obtain ⟨r₀, hr₀R, hr₀⟩ : ∃ r₀ ∈ R, a⁻¹ * a' = r₀ * r₀ := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a⁻¹ * a', huR⟩)
    have hi' : (g : P) ^ i = a⁻¹ * a' := by simpa using congrArg Subtype.val hi
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · obtain ⟨j, hj⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
      refine ⟨(g : P) ^ j, R.zpow_mem g.2 j, ?_⟩
      rw [← hi', hj, two_mul, zpow_add]
    · exfalso
      obtain ⟨w', hw'⟩ := exists_zpow_inv (P := P) k h1
      have hgQ : (g : P) ∈ Q := by
        have := hw' g hgk
        rw [zpow_mul, hi'] at this
        rw [← this]; exact Q.zpow_mem huQ w'
      have hRQ : R ≤ Q := by
        intro r hr
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨r, hr⟩)
        have : (g : P) ^ j = r := by simpa using congrArg Subtype.val hj
        rw [← this]; exact Q.zpow_mem hgQ j
      have c1 := Subgroup.card_mul_index R
      have c2 := Subgroup.card_mul_index Q
      rw [h.index_two] at c1
      rw [hQ] at c2
      have : R = Q := Subgroup.eq_of_le_of_card_ge hRQ (by omega)
      exact hQR this.ge
  have hnorm := h.normal
  let φ : ↥R →* ↥R :=
    { toFun := fun r => ⟨a⁻¹ * (r : P) * a, by
        have := hnorm.conj_mem (r : P) r.2 a⁻¹
        simpa using this⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show a⁻¹ * ((x : P) * y) * a = a⁻¹ * x * a * (a⁻¹ * y * a)
        group }
  have hcyc := h.cyclic
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ
  have hconj : ∀ r ∈ R, a⁻¹ * r * a = r ^ m := by
    intro r hr
    have h1 := congrArg Subtype.val (hm ⟨r, hr⟩)
    have h2 : ((φ ⟨r, hr⟩ : ↥R) : P) = a⁻¹ * r * a := rfl
    rw [h2] at h1
    simpa using h1
  set r4 : P := (g : P) ^ (2 ^ (k - 2)) with hr4
  have hr4R : r4 ∈ R := R.pow_mem g.2 _
  have hr4_4 : r4 ^ 4 = 1 := by
    rw [hr4, ← pow_mul]
    have : 2 ^ (k - 2) * 4 = 2 ^ k := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4, ← pow_add]; congr 1; omega
    rw [this]; exact hgk
  have hr4_2 : r4 * r4 ≠ 1 := by
    intro h1
    have h2 : (g : P) ^ (2 ^ (k - 1)) = 1 := by
      rw [← h1, hr4, ← pow_add, ← two_mul, ← pow_succ']
      congr 2; omega
    have h3 : g ^ (2 ^ (k - 1)) = 1 := Subtype.ext (by simpa using h2)
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hordg] at h4
    have h5 := Nat.le_of_dvd (by positivity) h4
    have h6 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hmod : r4 ^ m = r4 ^ (m % 4) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 4, zpow_add, zpow_mul]
    have : r4 ^ (4 : ℤ) = 1 := by
      have := hr4_4
      rw [← zpow_natCast] at this
      simpa using this
    rw [this]; simp
  have haiR : a⁻¹ ∉ R := fun h1 => haR (R.inv_mem_iff.mp h1)
  have hm3 : m % 4 = 3 := by
    have hc := hconj r4 hr4R
    rw [hmod] at hc
    have hcases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · exfalso
      rw [h0, zpow_zero] at hc
      apply hr4_2
      have : r4 = 1 := by
        calc r4 = a * (a⁻¹ * r4 * a) * a⁻¹ := by group
          _ = 1 := by rw [hc]; group
      rw [this, one_mul]
    · exfalso
      rw [h1, zpow_one] at hc
      apply hr4_2
      refine h.cent a⁻¹ haiR r4 hr4R ?_
      calc a⁻¹ * r4 = a⁻¹ * r4 * a * a⁻¹ := by group
        _ = r4 * a⁻¹ := by rw [hc]
    · exfalso
      rw [h2] at hc
      apply hr4_2
      have h4 : a⁻¹ * (r4 * r4) * a = 1 := by
        calc a⁻¹ * (r4 * r4) * a = (a⁻¹ * r4 * a) * (a⁻¹ * r4 * a) := by group
          _ = r4 ^ (2 : ℤ) * r4 ^ (2 : ℤ) := by rw [hc]
          _ = r4 ^ 4 := by
            rw [← zpow_add]; norm_num
          _ = 1 := hr4_4
      calc r4 * r4 = a * (a⁻¹ * (r4 * r4) * a) * a⁻¹ := by group
        _ = 1 := by rw [h4]; group
    · exact h3
  set w : ℤ := (m - 1) / 2 with hw
  have hwodd : w % 2 = 1 := by omega
  have hm1 : m - 1 = 2 * w := by omega
  obtain ⟨w', hw'⟩ := exists_zpow_inv (P := P) k hwodd
  set p : P := r₀ ^ w' with hp
  have hpR : p ∈ R := R.zpow_mem hr₀R w'
  have hpa : p * a * p⁻¹ = a' := by
    have h1 := hconj p hpR
    have h2 : p * a = a * p ^ m := by
      calc p * a = a * (a⁻¹ * p * a) := by group
        _ = a * p ^ m := by rw [h1]
    have h3 : p ^ (m - 1) = r₀ * r₀ := by
      rw [hm1, hp, ← zpow_mul]
      have : w' * (2 * w) = (w * w') * 2 := by ring
      rw [this, zpow_mul, hw' r₀ (hRk r₀ hr₀R), zpow_two]
    calc p * a * p⁻¹ = a * p ^ m * p⁻¹ := by rw [h2]
      _ = a * (p ^ m * p⁻¹) := by rw [mul_assoc]
      _ = a * p ^ (m - 1) := by rw [zpow_sub_one]
      _ = a * (r₀ * r₀) := by rw [h3]
      _ = a * (a⁻¹ * a') := by rw [hr₀]
      _ = a' := by group
  have hpz : p * h.z * p⁻¹ = h.z := by
    rw [h.comm hpR h.z_mem]; group
  refine ⟨p, hpR, ?_⟩
  intro x hx
  by_cases hxR : x ∈ R
  · rcases h.eq_one_or_eq_z hxR (hE.sq x hx) with h1 | h1
    · rw [h1]; simp
    · rw [h1, hpz]; exact hz'
  · have hxa : x * a⁻¹ ∈ R := (Subgroup.mul_mem_iff_of_index_two h.index_two).mpr
      ⟨fun h1 => absurd h1 hxR, fun h1 => absurd (R.inv_mem_iff.mp h1) haR⟩
    rcases h.eq_one_or_eq_z hxa (hE.sq _ (E.mul_mem hx (E.inv_mem haE))) with h1 | h1
    · rw [mul_inv_eq_one.mp h1, hpa]; exact ha'E'
    · have hx' : x = h.z * a := by
        calc x = (x * a⁻¹) * a := by group
          _ = h.z * a := by rw [h1]
      rw [hx']
      have hfin : p * (h.z * a) * p⁻¹ = h.z * a' := by
        calc p * (h.z * a) * p⁻¹ = (p * h.z * p⁻¹) * (p * a * p⁻¹) := by group
          _ = h.z * a' := by rw [hpz, hpa]
      rw [hfin]
      exact E'.mul_mem hz' ha'E'

theorem DSData.pow_half_eq_one (h : DSData R) {Q : Subgroup P} (hQ : Q.index = 2) (hQR : ¬ Q ≤ R)
    (h8 : 8 ≤ Nat.card R) {q : P} (hq : q ∈ Q) : q ^ (Nat.card R / 2) = 1 := by
  have hR2 : IsPGroup 2 R := h.two.to_subgroup R
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hhalf : Nat.card R / 2 = 2 ^ (k - 1) := by
    rw [hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    simp
  by_cases hqR : q ∈ R
  ·
    have hc1 := Subgroup.card_mul_index R
    have hc2 := Subgroup.card_mul_index Q
    rw [h.index_two] at hc1
    rw [hQ] at hc2
    have hQR' : Nat.card Q = Nat.card R := by omega
    have h3 := card_le_mul_inf_of_index_two h.index_two Q
    have hne : Q ⊓ R ≠ R := by
      intro heq
      have hRQ : R ≤ Q := by rw [← heq]; exact inf_le_left
      have : R = Q := Subgroup.eq_of_le_of_card_ge hRQ (by omega)
      exact hQR this.ge
    have hlt : Nat.card ↥(Q ⊓ R) < Nat.card R := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_right hne)
    have hdvd : Nat.card ↥(Q ⊓ R) ∣ Nat.card R := Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < Nat.card ↥(Q ⊓ R) := Nat.card_pos
    have hc2' : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with hc' | hc'
      · interval_cases c
        · omega
        · omega
      · exact hc'
    have hY : Nat.card ↥(Q ⊓ R) = Nat.card R / 2 := by
      have : Nat.card R ≤ 2 * Nat.card ↥(Q ⊓ R) := by omega
      rw [hc] at this ⊢
      have hc3 : c ≤ 2 := by
        by_contra hgt
        push Not at hgt
        nlinarith
      have : c = 2 := by omega
      subst this
      omega
    have := pow_card_eq_one' (G := ↥(Q ⊓ R)) (x := ⟨q, hq, hqR⟩)
    rw [hY] at this
    simpa using congrArg Subtype.val this
  · have hq2R : q * q ∈ R := Subgroup.mul_self_mem_of_index_two h.index_two q
    have hcomm : q * (q * q) = (q * q) * q := by group
    have h4 : (q * q) * (q * q) = 1 := h.cent q hqR (q * q) hq2R hcomm
    have hq4 : q ^ 4 = 1 := by
      calc q ^ 4 = (q * q) * (q * q) := by simp [pow_succ, mul_assoc]
        _ = 1 := h4
    have h4dvd : 4 ∣ 2 ^ (k - 1) := by
      have : 2 ^ 2 ∣ 2 ^ (k - 1) := pow_dvd_pow 2 (by omega)
      simpa using this
    obtain ⟨c, hc⟩ := h4dvd
    rw [hhalf, hc, pow_mul, hq4, one_pow]

end CFSG.QuasithinUnique.DS
