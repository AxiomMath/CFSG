module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem inf_sup_le_of_odd [Finite G] {S K O : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hP : Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card ↥K).factorization 2)
    (hO : Odd (Nat.card ↥O)) (hKO : K ≤ normalizer (O : Set G)) :
    S ⊓ (K ⊔ O) ≤ K := by
  have hcard := Sec4.M.card_sup_mul_card_inf hKO
  have hOK : Odd (Nat.card ↥(O ⊓ K)) :=
    hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hT : IsPGroup 2 ↥(S ⊓ (K ⊔ O)) := hS.to_inf_left
  have hsub : S ⊓ K ≤ S ⊓ (K ⊔ O) := inf_le_inf_left _ le_sup_left
  have hKO' : Nat.card ↥(K ⊔ O) = Nat.card ↥(O ⊔ K) := by rw [sup_comm]
  have hfact : (Nat.card ↥(O ⊔ K)).factorization 2 = (Nat.card ↥K).factorization 2 := by
    have h1 : (Nat.card ↥(O ⊔ K) * Nat.card ↥(O ⊓ K)).factorization 2 =
        (Nat.card ↥O * Nat.card ↥K).factorization 2 := by rw [hcard]
    have hne1 : Nat.card ↥(O ⊔ K) ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card ↥(O ⊓ K) ≠ 0 := Nat.card_pos.ne'
    have hne3 : Nat.card ↥O ≠ 0 := Nat.card_pos.ne'
    have hne4 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hne1 hne2, Nat.factorization_mul hne3 hne4] at h1
    simp only [Finsupp.add_apply] at h1
    have h2 : (Nat.card ↥(O ⊓ K)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h; exact (Nat.not_even_iff_odd.mpr hOK) (even_iff_two_dvd.mpr h))
    have h3 : (Nat.card ↥O).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h; exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h))
    omega
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  have hdvd : Nat.card ↥(S ⊓ (K ⊔ O)) ∣ Nat.card ↥(K ⊔ O) := Subgroup.card_dvd_of_le inf_le_right
  have hle : Nat.card ↥(S ⊓ (K ⊔ O)) ≤ Nat.card ↥(S ⊓ K) := by
    rw [hP, hn]
    rw [hn] at hdvd
    have h5 : n ≤ (Nat.card ↥(K ⊔ O)).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
    rw [hKO', hfact] at h5
    exact Nat.pow_le_pow_right (by norm_num) h5
  have heq : S ⊓ K = S ⊓ (K ⊔ O) := Subgroup.eq_of_le_of_card_ge hsub hle
  rw [← heq]
  exact inf_le_right

theorem forall_comm_mem_sup {C N K₁ K₂ : Subgroup G} {c : G} (hK₁ : K₁ ≤ C) (hK₂ : K₂ ≤ C)
    (hN : ∀ x ∈ C, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (h₁ : ∀ k ∈ K₁, ⁅k, c⁆ ∈ N) (h₂ : ∀ k ∈ K₂, ⁅k, c⁆ ∈ N) :
    ∀ k ∈ K₁ ⊔ K₂, ⁅k, c⁆ ∈ N := by
  intro k hk
  rw [← Subgroup.closure_eq K₁, ← Subgroup.closure_eq K₂, ← Subgroup.closure_union] at hk
  have key : k ∈ C ∧ ⁅k, c⁆ ∈ N := by
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨hK₁ hx, h₁ x hx⟩
      · exact ⟨hK₂ hx, h₂ x hx⟩
    | one => exact ⟨C.one_mem, by simp⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨C.mul_mem ihx.1 ihy.1, ?_⟩
      have e : ⁅x * y, c⁆ = x * ⁅y, c⁆ * x⁻¹ * ⁅x, c⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem (hN x ihx.1 _ ihy.2) ihx.2
    | inv x hx ihx =>
      refine ⟨C.inv_mem ihx.1, ?_⟩
      have e : ⁅x⁻¹, c⁆ = x⁻¹ * ⁅x, c⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hN x⁻¹ (C.inv_mem ihx.1) _ (N.inv_mem ihx.2)
  exact key.2

theorem core52 [Finite G] {P Q X : Subgroup G} {a : G}
    (hX : IsPGroup 2 ↥X) (hPQ : P ≤ Q) (hQX : Q ≤ X) (haX : a ∈ X) (ha2 : a * a = 1)
    (haQ : a ∉ Q) (hne : Q ≠ P)
    (hcyc : ∃ _ : (P.subgroupOf X).Normal, IsCyclic (↥X ⧸ P.subgroupOf X)) : False := by
  obtain ⟨hN, hC⟩ := hcyc
  set N : Subgroup ↥X := P.subgroupOf X with hNdef
  have : N.Normal := hN
  let π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N
  have hmemN : ∀ y : ↥X, π y = 1 → (y : G) ∈ P := fun y hy =>
    (QuotientGroup.eq_one_iff y).1 hy
  set ā : ↥X ⧸ N := π ⟨a, haX⟩ with hā
  have hā1 : ā ≠ 1 := by
    intro h
    exact haQ (hPQ (hmemN _ h))
  have hā2 : ā * ā = 1 := by
    rw [hā, ← map_mul]
    have : (⟨a, haX⟩ * ⟨a, haX⟩ : ↥X) = 1 := Subtype.ext ha2
    rw [this, map_one]
  set Q' : Subgroup (↥X ⧸ N) := (Q.subgroupOf X).map π with hQ'
  have hXq : IsPGroup 2 (↥X ⧸ N) := IsPGroup.of_surjective hX π (QuotientGroup.mk'_surjective N)
  have hQ'nt : Nontrivial ↥Q' := by
    obtain ⟨q, hq, hqP⟩ : ∃ q ∈ Q, q ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm (fun q hq => hcon q hq) hPQ)
    refine ⟨⟨⟨π ⟨q, hQX hq⟩, ⟨⟨q, hQX hq⟩, hq, rfl⟩⟩, 1, ?_⟩⟩
    intro h
    have h' : π ⟨q, hQX hq⟩ = 1 := congrArg Subtype.val h
    exact hqP (hmemN _ h')
  have hQ'2 : IsPGroup 2 ↥Q' := hXq.to_subgroup _
  have h2dvd : 2 ∣ Nat.card ↥Q' := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ'2
    have h1 : 1 < Nat.card ↥Q' := (Finite.one_lt_card_iff_nontrivial).2 hQ'nt
    have : n ≠ 0 := by
      rintro rfl
      rw [hn] at h1
      simp at h1
    rw [hn]; exact dvd_pow_self 2 this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q') 2 h2dvd
  set hq : ↥X ⧸ N := (h : ↥X ⧸ N) with hhq
  have hh2 : hq * hq = 1 := by
    have := pow_orderOf_eq_one h
    rw [hh] at this
    have h3 : ((h ^ 2 : ↥Q') : ↥X ⧸ N) = 1 := by rw [this]; rfl
    simpa [pow_two] using h3
  have hh1 : hq ≠ 1 := by
    intro h1
    have : h = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hh
    omega
  have hsol : hq = ā := by
    by_contra hne'
    have hc := hC
    classical
    have : Fintype (↥X ⧸ N) := Fintype.ofFinite _
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥X ⧸ N) (n := 2) (by norm_num)
    have hsub : ({1, ā, hq} : Finset (↥X ⧸ N)) ⊆ Finset.univ.filter (fun x => x ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl
      · simp
      · simpa [pow_two] using hā2
      · simpa [pow_two] using hh2
    have hcard := Finset.card_le_card hsub
    have h3 : ({1, ā, hq} : Finset (↥X ⧸ N)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; exact fun h' => hne' h'.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h' => hā1 h'.symm, fun h' => hh1 h'.symm⟩
    omega
  have hmem : ā ∈ Q' := by rw [← hsol]; exact h.2
  obtain ⟨q, hq', hqa⟩ := Subgroup.mem_map.1 hmem
  have hqa' : π q = π ⟨a, haX⟩ := hqa
  have hqm : q⁻¹ * ⟨a, haX⟩ ∈ N := by
    rw [← QuotientGroup.eq]
    exact hqa'
  have hq'' : (q : G) ∈ Q := hq'
  have hP' : (q : G)⁻¹ * a ∈ P := hqm
  have := Q.mul_mem hq'' (hPQ hP')
  exact haQ (by simpa using this)

theorem relIndex_centralizer_le_two [Finite G] {S : Subgroup G} {x z : G}
    (hz : ∀ s ∈ S, s * z * s⁻¹ = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hn : ∀ s ∈ S, s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x * z) :
    (S ⊓ centralizer ({x} : Set G)).relIndex S ≤ 2 := by
  classical
  set H : Subgroup ↥S := (S ⊓ centralizer ({x} : Set G)).subgroupOf S with hH
  have hmem : ∀ s : ↥S, s ∈ H ↔ (s : G) * x * (s : G)⁻¹ = x := by
    intro s
    rw [hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨_, h⟩
      rw [h]; group
    · intro h
      refine ⟨s.2, ?_⟩
      calc (s : G) * x = ((s : G) * x * (s : G)⁻¹) * (s : G) := by group
        _ = x * (s : G) := by rw [h]
  have hxz : x * z ≠ x := by
    intro h
    apply hz1
    have := congrArg (fun w => x⁻¹ * w) h
    simpa using this
  show H.index ≤ 2
  by_cases hQ : H = ⊤
  · rw [hQ, Subgroup.index_top]; norm_num
  · obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ↥S, s₀ ∉ H := by
      by_contra hcon
      push Not at hcon
      exact hQ (eq_top_iff.2 fun s _ => hcon s)
    have h2 : H.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨s₀, fun b => ?_⟩
      have hs₀' : (s₀ : G) * x * (s₀ : G)⁻¹ = x * z := by
        rcases hn s₀ s₀.2 with h | h
        · exact absurd ((hmem s₀).2 h) hs₀
        · exact h
      have hbs : ((b * s₀ : ↥S) : G) * x * ((b * s₀ : ↥S) : G)⁻¹ =
          (b : G) * (x * z) * (b : G)⁻¹ := by
        rw [← hs₀']
        simp only [Subgroup.coe_mul, mul_inv_rev]; group
      have hbz : (b : G) * (x * z) * (b : G)⁻¹ = ((b : G) * x * (b : G)⁻¹) * z := by
        calc (b : G) * (x * z) * (b : G)⁻¹ =
            ((b : G) * x * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by group
          _ = _ := by rw [hz b b.2]
      rcases hn b b.2 with h | h
      · have h1 : b ∈ H := (hmem b).2 h
        have h3 : b * s₀ ∉ H := by
          intro h4
          have := (hmem _).1 h4
          rw [hbs, hbz, h] at this
          exact hxz this
        exact Or.inr ⟨h1, h3⟩
      · have h1 : b ∉ H := by
          intro h4
          have := (hmem _).1 h4
          rw [h] at this
          exact hxz this
        have h3 : b * s₀ ∈ H := by
          rw [hmem, hbs, hbz, h]
          calc x * z * z = x * (z * z) := by group
            _ = x := by rw [hz2, mul_one]
        exact Or.inl ⟨h3, h1⟩
    rw [h2]

theorem conj_mem_sup_of {A B : Subgroup G} {c : G} (hA : ∀ w ∈ A, c * w * c⁻¹ ∈ A)
    (hB : ∀ w ∈ B, c * w * c⁻¹ ∈ B) {w : G} (hw : w ∈ A ⊔ B) : c * w * c⁻¹ ∈ A ⊔ B := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact mem_sup_left (hA x hx)
    · exact mem_sup_right (hB x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [this]; exact mul_mem hx hy
  | inv x _ hx =>
    have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hx

theorem conj_mem_commutator_self {C : Subgroup G} {c : G} (hc : c ∈ C) {w : G}
    (hw : w ∈ ⁅C, C⁆) : c * w * c⁻¹ ∈ ⁅C, C⁆ := by
  rw [Subgroup.commutator_def] at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨c * g₁ * c⁻¹, C.mul_mem (C.mul_mem hc hg₁) (C.inv_mem hc), c * g₂ * c⁻¹,
      C.mul_mem (C.mul_mem hc hg₂) (C.inv_mem hc), ?_⟩
    simp only [commutatorElement_def]; group
  | one => simp
  | mul x y _ _ hx hy =>
    have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [this]; exact mul_mem hx hy
  | inv x _ hx =>
    have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hx

theorem isCyclic_of_le' {P Q : Subgroup G} (h : P ≤ Q) (hQ : IsCyclic ↥Q) : IsCyclic ↥P := by
  have := hQ
  have : IsCyclic ↥(P.subgroupOf Q) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe h).surjective

theorem mem_or_mul_inv_mem {Q : Subgroup G} {b : G} (hb : b ∈ normalizer (Q : Set G))
    (hb2 : b * b ∈ Q) {x : G} (hx : x ∈ Q ⊔ zpowers b) : x ∈ Q ∨ x * b⁻¹ ∈ Q := by
  have hnorm : zpowers b ≤ normalizer (Q : Set G) := zpowers_le.2 hb
  rw [sup_comm] at hx
  obtain ⟨y, hy, q, hq, rfl⟩ := Sec4.M.mem_sup_of_le_normalizer hnorm hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  have hb2k : b ^ (2 * (n / 2)) ∈ Q := by
    rw [zpow_mul, zpow_two]
    exact zpow_mem hb2 _
  have hbq : b * q * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hb q).1 hq
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
  · left
    have : b ^ n = b ^ (2 * (n / 2)) := by
      conv_lhs => rw [hn, h]
      simp
    rw [this]
    exact mul_mem hb2k hq
  · right
    have : b ^ n = b ^ (2 * (n / 2)) * b := by
      conv_lhs => rw [hn, h]
      simp [zpow_add]
    rw [this]
    have e : b ^ (2 * (n / 2)) * b * q * b⁻¹ = b ^ (2 * (n / 2)) * (b * q * b⁻¹) := by group
    rw [e]
    exact mul_mem hb2k hbq

theorem isSolvable_of_conj_le {H : Subgroup G} {g : G} {L : Subgroup G}
    (hL : Group.IsSolvable ↥L) (hH : ∀ h ∈ H, g⁻¹ * h * g ∈ L) : Group.IsSolvable ↥H := by
  let f : ↥H →* ↥L :=
    { toFun := fun h => ⟨g⁻¹ * (h : G) * g, hH h h.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk] at this
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel this)
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem exists_mem_normalizer_not_mem [Finite G] {T W : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hWT : W ≤ T) (hne : W ≠ T) :
    ∃ n ∈ T, n ∉ W ∧ (∀ w ∈ W, n * w * n⁻¹ ∈ W) ∧ ∀ w ∈ W, n⁻¹ * w * n ∈ W := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  set W' : Subgroup ↥T := W.subgroupOf T with hW'
  have hW'top : W' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm hWT
    intro t ht
    have : (⟨t, ht⟩ : ↥T) ∈ W' := by rw [h]; trivial
    exact this
  have hlt := hNC W' hW'top
  obtain ⟨n, hn, hnW⟩ := IsConcreteLE.exists_of_lt hlt
  have hn' := Subgroup.mem_normalizer_iff.1 hn
  refine ⟨(n : G), n.2, hnW, ?_, ?_⟩
  · intro w hw
    exact (hn' ⟨w, hWT hw⟩).1 hw
  · intro w hw
    have hwT : n⁻¹ * (⟨w, hWT hw⟩ : ↥T) * n ∈ W' := by
      have := (hn' (n⁻¹ * ⟨w, hWT hw⟩ * n)).2
      have e : n * (n⁻¹ * (⟨w, hWT hw⟩ : ↥T) * n) * n⁻¹ = ⟨w, hWT hw⟩ := by group
      rw [e] at this
      exact this hw
    exact hwT

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
