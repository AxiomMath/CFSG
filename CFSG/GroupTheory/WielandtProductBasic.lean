module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory.WielandtProduct

open Subgroup

variable {G : Type*} [Group G]

noncomputable def sylowOf (A : Subgroup G) (p : ℕ) : Subgroup G :=
  ((Classical.arbitrary (Sylow p A) : Sylow p A) : Subgroup A).map A.subtype

variable {A B K : Subgroup G} {p q : ℕ}

theorem sylowOf_le : sylowOf A p ≤ A := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem isPGroup_sylowOf : IsPGroup p (sylowOf A p) :=
  (Classical.arbitrary (Sylow p A)).isPGroup'.map A.subtype

theorem isPGroup_zpowers_of_pow_eq_one [Fact p.Prime] {x : G} {k : ℕ} (hk : x ^ p ^ k = 1) :
    IsPGroup p (zpowers x) := by
  obtain ⟨m, hm⟩ := (exists_orderOf_eq_prime_pow_iff (x := x) (p := p)).2 ⟨k, hk⟩
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem mem_sylowOf_iff [Finite G] [Fact p.Prime] [Group.IsNilpotent A] {x : G} :
    x ∈ sylowOf A p ↔ x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1 := by
  constructor
  · intro hx
    refine ⟨sylowOf_le hx, ?_⟩
    obtain ⟨k, hk⟩ := isPGroup_sylowOf (A := A) (p := p) ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hxA, k, hk⟩
    have hP : IsPGroup p (zpowers (⟨x, hxA⟩ : A)) :=
      isPGroup_zpowers_of_pow_eq_one (k := k) (by ext; simpa using hk)
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    have hU := Sylow.unique_of_normal Q inferInstance
    have hQ' : Q = Classical.arbitrary (Sylow p A) := Subsingleton.elim _ _
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    rw [← hQ']
    exact hQ (mem_zpowers _)

theorem le_sylowOf_of_isPGroup [Finite G] [Fact p.Prime] [Group.IsNilpotent A]
    {P : Subgroup G} (hP : IsPGroup p P) (hPA : P ≤ A) : P ≤ sylowOf A p := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact mem_sylowOf_iff.2 ⟨hPA hx, k, by simpa using congrArg Subtype.val hk⟩

theorem mem_sylowOf_of_orderOf_eq [Finite G] [Fact p.Prime] [Group.IsNilpotent A] {x : G}
    (hxA : x ∈ A) (hx : orderOf x = p) : x ∈ sylowOf A p :=
  mem_sylowOf_iff.2 ⟨hxA, 1, by rw [pow_one, ← hx, pow_orderOf_eq_one]⟩

theorem card_sylowOf [Finite G] [Fact p.Prime] :
    Nat.card (sylowOf A p) = p ^ (Nat.card A).factorization p := by
  rw [sylowOf, Subgroup.card_map_of_injective A.subtype_injective]
  exact Sylow.card_eq_multiplicity _

theorem le_normalizer_sylowOf [Finite G] [Fact p.Prime] [Group.IsNilpotent A] :
    A ≤ normalizer (sylowOf A p : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxA, k, hk⟩ := mem_sylowOf_iff.1 hx
    refine mem_sylowOf_iff.2 ⟨A.mul_mem (A.mul_mem ha hxA) (A.inv_mem ha), k, ?_⟩
    rw [conj_pow, hk]
    group
  · intro hx
    obtain ⟨hxA, k, hk⟩ := mem_sylowOf_iff.1 hx
    refine mem_sylowOf_iff.2 ⟨?_, k, ?_⟩
    · have := A.mul_mem (A.mul_mem (A.inv_mem ha) hxA) ha
      simpa [mul_assoc] using this
    · have h2 : (a * x * a⁻¹) ^ p ^ k = a * x ^ p ^ k * a⁻¹ := conj_pow
      rw [hk] at h2
      have : x ^ p ^ k = a⁻¹ * 1 * a := by
        rw [h2]
        group
      simpa using this

theorem commute_of_mem_sylowOf [Finite G] [Fact p.Prime] [Group.IsNilpotent A] {x y : G}
    (hx : x ∈ sylowOf A p) (hy : y ∈ A) (hpy : ¬ p ∣ orderOf y) : Commute x y := by
  have hxA := sylowOf_le hx
  obtain ⟨-, k, hk⟩ := mem_sylowOf_iff.1 hx
  have hcop : (orderOf (⟨x, hxA⟩ : A)).Coprime (orderOf (⟨y, hy⟩ : A)) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    obtain ⟨m, hm⟩ := (exists_orderOf_eq_prime_pow_iff (x := x) (p := p)).2 ⟨k, hk⟩
    rw [hm]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpy)
  exact Subtype.ext_iff.mp (Group.IsNilpotent.commute_of_orderOf_coprime hcop)

theorem commute_of_mem_sylowOf_of_ne [Finite G] [Fact p.Prime] [Fact q.Prime]
    [Group.IsNilpotent A] (hpq : p ≠ q) {x y : G} (hx : x ∈ sylowOf A p)
    (hy : y ∈ sylowOf A q) : Commute x y := by
  refine commute_of_mem_sylowOf hx (sylowOf_le hy) fun hdvd => hpq ?_
  obtain ⟨-, k, hk⟩ := mem_sylowOf_iff.1 hy
  obtain ⟨m, hm⟩ := (exists_orderOf_eq_prime_pow_iff (x := y) (p := q)).2 ⟨k, hk⟩
  rw [hm] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
    ((Nat.Prime.dvd_of_dvd_pow Fact.out hdvd))

theorem le_of_forall_sylowOf_le [Finite G] (h : ∀ p : ℕ, p.Prime → sylowOf A p ≤ K) :
    A ≤ K := by
  have hidx : (K.subgroupOf A).index = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hq hdvd
    have : Fact q.Prime := ⟨hq⟩
    let P := Classical.arbitrary (Sylow q A)
    have hPK : (P : Subgroup A) ≤ K.subgroupOf A := fun y hy => h q hq ⟨y, hy, rfl⟩
    exact P.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hPK))
  intro x hx
  have htop := Subgroup.index_eq_one.mp hidx
  have hmem : (⟨x, hx⟩ : A) ∈ K.subgroupOf A := by
    rw [htop]
    trivial
  exact hmem

theorem eq_top_of_forall_sylow_le {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (h : ∀ p : ℕ, p.Prime → ∃ P : Sylow p X, (P : Subgroup X) ≤ K) : K = ⊤ := by
  apply Subgroup.index_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hdvd
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP⟩ := h q hq
  exact P.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hP))

theorem isNilpotent_of_le (hKA : K ≤ A) [Group.IsNilpotent A] : Group.IsNilpotent K :=
  Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKA)

theorem sylowOf_inf [Finite G] [Fact p.Prime] [Group.IsNilpotent A] :
    sylowOf (A ⊓ K) p = sylowOf A p ⊓ K := by
  have := isNilpotent_of_le (inf_le_left : A ⊓ K ≤ A)
  ext x
  rw [mem_sylowOf_iff, mem_inf, mem_inf, mem_sylowOf_iff]
  tauto

theorem le_centralizer_of_mem_sylowOf [Finite G] [Fact p.Prime] [Group.IsNilpotent A] {z : G}
    (hz : z ∈ sylowOf A p) (hzc : ∀ y ∈ sylowOf A p, Commute z y) :
    A ≤ centralizer ({z} : Set G) := by
  refine le_of_forall_sylowOf_le fun r hr => ?_
  have : Fact r.Prime := ⟨hr⟩
  intro y hy
  rw [mem_centralizer_singleton_iff]
  by_cases hrp : r = p
  · subst hrp
    exact (hzc y hy).eq.symm
  · refine (commute_of_mem_sylowOf_of_ne (A := A) (Ne.symm hrp) hz hy).eq.symm

theorem card_eq_mul_of_forall_mul [Finite G] (hAB : A ⊓ B = ⊥)
    (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) :
    Nat.card G = Nat.card A * Nat.card B := by
  let f : A × B → G := fun x => (x.1 : G) * x.2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [f] at h
      have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h]
        group
      have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hAB, mem_bot] at hmem
      have ha : a = a' := Subtype.ext (by
        rw [inv_mul_eq_one] at hmem
        exact hmem.symm)
      subst ha
      have hb : b = b' := Subtype.ext (mul_left_cancel h)
      rw [hb]
    · intro g
      obtain ⟨a, ha, b, hb, rfl⟩ := hmul g
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective f hf).symm

theorem forall_mul_swap (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) :
    ∀ g : G, ∃ b ∈ B, ∃ a ∈ A, g = b * a := by
  intro g
  obtain ⟨a, ha, b, hb, h⟩ := hmul g⁻¹
  exact ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, by rw [← mul_inv_rev, ← h, inv_inv]⟩


theorem factorized_of_forall (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) {F : Subgroup G}
    (hF : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ F → a ∈ F) :
    ∀ x ∈ F, ∃ a ∈ A ⊓ F, ∃ b ∈ B ⊓ F, x = a * b := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hmul x
  have haF := hF a ha b hb hx
  exact ⟨a, ⟨ha, haF⟩, b, ⟨hb, by simpa using F.mul_mem (F.inv_mem haF) hx⟩, rfl⟩

theorem factorized_of_le (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) {F : Subgroup G}
    (hAF : A ≤ F) : ∀ x ∈ F, ∃ a ∈ A ⊓ F, ∃ b ∈ B ⊓ F, x = a * b :=
  factorized_of_forall hmul fun _ ha _ _ _ => hAF ha

theorem mem_normalizer_of_forall_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  let f : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simpa [f] using this
  have hsurj := Finite.surjective_of_injective hf
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := hsurj ⟨_, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  exact this ▸ y.2

theorem factorized_normalizer [Finite G] (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    {H : Subgroup G}
    (hH : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ normalizer (H : Set G) → ∀ x ∈ H, a * x * a⁻¹ ∈ H) :
    ∀ x ∈ normalizer (H : Set G), ∃ a ∈ A ⊓ normalizer (H : Set G),
      ∃ b ∈ B ⊓ normalizer (H : Set G), x = a * b :=
  factorized_of_forall hmul fun a ha b hb hab =>
    mem_normalizer_of_forall_conj_mem (hH a ha b hb hab)

theorem factorized_normalizer_sup [Finite G] (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    {A₀ B₀ : Subgroup G} (hA₀ : A ≤ normalizer (A₀ : Set G))
    (hB₀ : B ≤ normalizer (B₀ : Set G)) :
    ∀ x ∈ normalizer ((A₀ ⊔ B₀ : Subgroup G) : Set G),
      ∃ a ∈ A ⊓ normalizer ((A₀ ⊔ B₀ : Subgroup G) : Set G),
      ∃ b ∈ B ⊓ normalizer ((A₀ ⊔ B₀ : Subgroup G) : Set G), x = a * b := by
  refine factorized_normalizer hmul fun a ha b hb hab => ?_
  let M : Subgroup G := (A₀ ⊔ B₀).comap (MulAut.conj a).toMonoidHom
  have hM : ∀ z, z ∈ M ↔ a * z * a⁻¹ ∈ A₀ ⊔ B₀ := fun z => Iff.rfl
  have hle : A₀ ⊔ B₀ ≤ M := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [hM]
      exact mem_sup_left (((mem_normalizer_iff.mp (hA₀ ha)) z).mp hz)
    · rw [hM]
      have hz' : b⁻¹ * z * b ∈ B₀ := by
        have := ((mem_normalizer_iff.mp (hB₀ (B.inv_mem hb))) z).mp hz
        simpa using this
      have := ((mem_normalizer_iff.mp hab) (b⁻¹ * z * b)).mp (mem_sup_right hz')
      simpa [mul_assoc] using this
  exact fun x hx => (hM x).mp (hle hx)

theorem sup_eq_top_of_le_normalizer [IsSimpleGroup G]
    (hmul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) {X : Subgroup G} (hX : X ≠ ⊥)
    (hBX : B ≤ normalizer (X : Set G)) : A ⊔ X = ⊤ := by
  have hle : normalClosure (X : Set G) ≤ A ⊔ X := by
    rw [normalClosure, closure_le]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    obtain ⟨a, ha, b, hb, rfl⟩ := hmul c
    have hbx : b * x * b⁻¹ ∈ X := ((mem_normalizer_iff.mp (hBX hb)) x).mp hx
    have : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [SetLike.mem_coe, this]
    exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right hbx)) (mem_sup_left (inv_mem ha))
  have hne : normalClosure (X : Set G) ≠ ⊥ := by
    intro h
    exact hX (le_bot_iff.mp (h ▸ le_normalClosure))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure (X : Set G)) with h | h
  · exact absurd h hne
  · exact top_le_iff.mp (h ▸ hle)

theorem forall_mem_sup_of_swap {S T : Subgroup G}
    (h : ∀ t ∈ T, ∀ s ∈ S, ∃ s' ∈ S, ∃ t' ∈ T, t * s = s' * t') :
    ∀ x ∈ S ⊔ T, ∃ s ∈ S, ∃ t ∈ T, x = s * t := by
  let M : Subgroup G :=
    { carrier := {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}
      one_mem' := ⟨1, S.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨s, hs, t, ht, rfl⟩ ⟨s₁, hs₁, t₁, ht₁, rfl⟩
        obtain ⟨s', hs', t', ht', he⟩ := h t ht s₁ hs₁
        refine ⟨s * s', S.mul_mem hs hs', t' * t₁, T.mul_mem ht' ht₁, ?_⟩
        rw [show s * t * (s₁ * t₁) = s * (t * s₁) * t₁ by group, he]
        group
      inv_mem' := by
        rintro _ ⟨s, hs, t, ht, rfl⟩
        obtain ⟨s', hs', t', ht', he⟩ := h t⁻¹ (T.inv_mem ht) s⁻¹ (S.inv_mem hs)
        exact ⟨s', hs', t', ht', by rw [mul_inv_rev, he]⟩ }
  have hle : S ⊔ T ≤ M := sup_le (fun s hs => ⟨s, hs, 1, T.one_mem, by simp⟩)
    (fun t ht => ⟨1, S.one_mem, t, ht, by simp⟩)
  exact fun x hx => hle hx

theorem coprime_card_of_isPGroup [Finite G] [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {S T : Subgroup G} (hS : IsPGroup p S) (hT : IsPGroup q T) :
    Nat.Coprime (Nat.card S) (Nat.card T) := by
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  rw [ha, hb]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Fact.out).2 hpq)

theorem card_sup_eq_mul [Finite G] [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {S T : Subgroup G} (hS : IsPGroup p S) (hT : IsPGroup q T)
    (hST : ∀ x ∈ S ⊔ T, ∃ s ∈ S, ∃ t ∈ T, x = s * t) :
    Nat.card (S ⊔ T : Subgroup G) = Nat.card S * Nat.card T := by
  apply le_antisymm
  · let f : S × T → (S ⊔ T : Subgroup G) := fun x => ⟨x.1 * x.2, mul_mem_sup x.1.2 x.2.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := hST x hx
      exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective f hf
  · apply Nat.le_of_dvd Nat.card_pos
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_card_of_isPGroup hpq hS hT)
      (Subgroup.card_dvd_of_le le_sup_left) (Subgroup.card_dvd_of_le le_sup_right)

theorem le_or_le_of_isPGroup [Finite G] {r : ℕ} [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] (hpq : p ≠ q) {S T N : Subgroup G} (hS : IsPGroup p S) (hT : IsPGroup q T)
    (hST : ∀ x ∈ S ⊔ T, ∃ s ∈ S, ∃ t ∈ T, x = s * t) (hN : N ≤ S ⊔ T)
    (hNn : S ⊔ T ≤ normalizer (N : Set G)) (hNr : IsPGroup r N) (hNb : N ≠ ⊥) :
    N ≤ S ∨ N ≤ T := by
  have hcard := card_sup_eq_mul hpq hS hT hST
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  have hrN : r ∣ Nat.card N := by
    rcases hNr.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hNb
    · exact h
  have hrST : r ∣ p ^ a * q ^ b := by
    rw [← ha, ← hb, ← hcard]
    exact hrN.trans (Subgroup.card_dvd_of_le hN)
  have hrpq : r = p ∨ r = q := by
    rcases (Nat.Prime.dvd_mul Fact.out).1 hrST with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
        ((Nat.Prime.dvd_of_dvd_pow Fact.out h)))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
        ((Nat.Prime.dvd_of_dvd_pow Fact.out h)))
  rcases hrpq with rfl | rfl
  · left
    have hK : IsPGroup r (N ⊔ S : Subgroup G) :=
      hNr.to_sup_of_normal_left' hS (le_sup_left.trans hNn)
    have hKle : N ⊔ S ≤ S ⊔ T := sup_le hN le_sup_left
    obtain ⟨m, hm⟩ := hK.exists_card_eq
    have hdvd : Nat.card (N ⊔ S : Subgroup G) ∣ Nat.card S * Nat.card T :=
      hcard ▸ Subgroup.card_dvd_of_le hKle
    have hcop : Nat.Coprime (Nat.card (N ⊔ S : Subgroup G)) (Nat.card T) := by
      rw [hm, hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Fact.out).2 hpq)
    have hle : Nat.card (N ⊔ S : Subgroup G) ≤ Nat.card S :=
      Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)
    have heq : S = N ⊔ S := Subgroup.eq_of_le_of_card_ge le_sup_right hle
    exact heq ▸ le_sup_left
  · right
    have hK : IsPGroup r (N ⊔ T : Subgroup G) :=
      hNr.to_sup_of_normal_left' hT (le_sup_right.trans hNn)
    have hKle : N ⊔ T ≤ S ⊔ T := sup_le hN le_sup_right
    obtain ⟨m, hm⟩ := hK.exists_card_eq
    have hdvd : Nat.card (N ⊔ T : Subgroup G) ∣ Nat.card S * Nat.card T :=
      hcard ▸ Subgroup.card_dvd_of_le hKle
    have hcop : Nat.Coprime (Nat.card (N ⊔ T : Subgroup G)) (Nat.card S) := by
      rw [hm, ha]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Fact.out).2 (Ne.symm hpq))
    have hle : Nat.card (N ⊔ T : Subgroup G) ≤ Nat.card T :=
      Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left hdvd)
    have heq : T = N ⊔ T := Subgroup.eq_of_le_of_card_ge le_sup_right hle
    exact heq ▸ le_sup_left

section Automizer

open scoped Pointwise

variable {X : Type*} [Group X]

theorem mem_conj_smul_iff {g x : X} {H : Subgroup X} :
    x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem mem_smul_sylow_iff {g x : X} {P : Sylow p X} :
    x ∈ g • P ↔ g⁻¹ * x * g ∈ P := by
  change x ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (P : Subgroup X)
  rw [Sylow.coe_subgroup_smul, mem_conj_smul_iff]

theorem isPGroup_automizer_of_le [Finite X] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (S : Sylow p X) (R : Sylow q X) (H : Subgroup X)
    (hSR : ∀ s ∈ (S : Subgroup X), ∀ r ∈ (R : Subgroup X), Commute s r)
    (hRH : normalizer (R : Set X) ≤ H)
    (hH : ∀ h ∈ H, ∃ k : ℕ, ∀ s ∈ (S : Subgroup X), Commute (h ^ p ^ k) s)
    (Q : Subgroup X) (hQS : Q ≤ S) :
    IsPGroup p (normalizer (Q : Set X) ⧸
      (centralizer (Q : Set X)).subgroupOf (normalizer (Q : Set X))) := by
  intro z
  induction z using QuotientGroup.induction_on with
  | H y =>
  have hRC : (R : Subgroup X) ≤ centralizer (Q : Set X) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro u hu
    exact (hSR u (hQS hu) r hr).eq
  have hyR : ((y : X) • R : Sylow q X) ≤ centralizer (Q : Set X) := by
    intro r hr
    rw [Sylow.coe_subgroup_smul, mem_conj_smul_iff] at hr
    rw [mem_centralizer_iff]
    intro u hu
    have hyu : (y : X)⁻¹ * u * y ∈ Q := by
      have := (mem_normalizer_iff.mp (inv_mem y.2) u).mp hu
      simpa using this
    have hc := (hSR _ (hQS hyu) _ hr).eq
    have : u * r = r * u := by
      have h1 : (y : X) * ((y : X)⁻¹ * u * y * ((y : X)⁻¹ * r * y)) * (y : X)⁻¹ =
          (y : X) * ((y : X)⁻¹ * r * y * ((y : X)⁻¹ * u * y)) * (y : X)⁻¹ := by rw [hc]
      simpa [mul_assoc] using h1
    exact this
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer (Q : Set X))
    (R.subtype hRC) (((y : X) • R).subtype hyR)
  rw [Sylow.smul_subtype] at hc
  have hc' : (c : X) • R = (y : X) • R := Sylow.subtype_injective hc
  have hmemN : (c : X)⁻¹ * y ∈ normalizer (R : Set X) := by
    rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, ← hc', inv_smul_smul]
  obtain ⟨k, hk⟩ := hH _ (hRH hmemN)
  refine ⟨k, ?_⟩
  have hcN : (c : X) ∈ normalizer (Q : Set X) := centralizer_le_normalizer _ c.2
  have hcy : ((c : X)⁻¹ * y) ∈ normalizer (Q : Set X) :=
    mul_mem (inv_mem hcN) y.2
  have hcinvN : (c : X)⁻¹ ∈ normalizer (Q : Set X) := inv_mem hcN
  have hmk : (QuotientGroup.mk y : normalizer (Q : Set X) ⧸
      (centralizer (Q : Set X)).subgroupOf (normalizer (Q : Set X))) =
      QuotientGroup.mk (⟨(c : X)⁻¹ * y, hcy⟩ : normalizer (Q : Set X)) := by
    have hsplit : (⟨(c : X)⁻¹ * y, hcy⟩ : normalizer (Q : Set X)) =
        ⟨(c : X)⁻¹, hcinvN⟩ * y := rfl
    rw [hsplit, QuotientGroup.mk_mul]
    have h1 : (QuotientGroup.mk (⟨(c : X)⁻¹, hcinvN⟩ : normalizer (Q : Set X)) :
        normalizer (Q : Set X) ⧸
          (centralizer (Q : Set X)).subgroupOf (normalizer (Q : Set X))) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact inv_mem c.2
    rw [h1, one_mul]
  rw [hmk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf,
    Subgroup.coe_pow]
  rw [mem_centralizer_iff]
  intro u hu
  exact (hk u (hQS hu)).eq.symm

theorem isPGroup_automizer [Finite X] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (S : Sylow p X) (R : Sylow q X) (H : Subgroup X)
    (hSR : ∀ s ∈ (S : Subgroup X), ∀ r ∈ (R : Subgroup X), Commute s r)
    (hRH : normalizer (R : Set X) ≤ H)
    (hH : ∀ h ∈ H, ∃ k : ℕ, ∀ s ∈ (S : Subgroup X), Commute (h ^ p ^ k) s)
    (Q : Subgroup X) (hQ : IsPGroup p Q) :
    IsPGroup p (normalizer (Q : Set X) ⧸
      (centralizer (Q : Set X)).subgroupOf (normalizer (Q : Set X))) := by
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X S P
  have hconj : ∀ a b : X, Commute (g⁻¹ * a * g) (g⁻¹ * b * g) → Commute a b := by
    intro a b hab
    have h2 := hab.map (MulAut.conj g)
    simpa [MulAut.conj_apply, mul_assoc] using h2
  refine isPGroup_automizer_of_le (g • S) (g • R) (MulAut.conj g • H) ?_ ?_ ?_ Q hQP
  · intro s hs r hr
    rw [Sylow.coe_subgroup_smul, mem_conj_smul_iff] at hs hr
    exact hconj s r (hSR _ hs _ hr)
  · intro x hx
    rw [mem_conj_smul_iff]
    apply hRH
    rw [mem_set_normalizer_iff] at hx ⊢
    intro r
    have h1 := hx (g * r * g⁻¹)
    simp only [SetLike.mem_coe, mem_smul_sylow_iff] at h1 ⊢
    have e1 : g⁻¹ * (g * r * g⁻¹) * g = r := by group
    have e2 : g⁻¹ * (x * (g * r * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * r * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro h hh
    rw [mem_conj_smul_iff] at hh
    obtain ⟨k, hk⟩ := hH _ hh
    refine ⟨k, fun s hs => ?_⟩
    rw [Sylow.coe_subgroup_smul, mem_conj_smul_iff] at hs
    apply hconj
    have e : g⁻¹ * h ^ p ^ k * g = (g⁻¹ * h * g) ^ p ^ k := by
      rw [show g⁻¹ * h * g = g⁻¹ * h * g⁻¹⁻¹ by group, conj_pow]
      group
    rw [e]
    exact hk _ hs

end Automizer

theorem prod_pow_apply_eq_one {V : Type*} [CommGroup V] {p : ℕ} (γ : MulAut V)
    (hγ : γ ^ p = 1) (hfpf : ∀ w : V, γ w = w → w = 1) (v : V) :
    ∏ k ∈ Finset.range p, (γ ^ k) v = 1 := by
  apply hfpf
  rw [map_prod]
  have h1 := Finset.prod_range_succ' (fun k => (γ ^ k) v) p
  have h2 := Finset.prod_range_succ (fun k => (γ ^ k) v) p
  rw [h2, hγ] at h1
  simp only [pow_zero, MulAut.one_apply] at h1
  have h3 : ∏ k ∈ Finset.range p, γ ((γ ^ k) v) = ∏ k ∈ Finset.range p, (γ ^ (k + 1)) v := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [pow_succ', MulAut.mul_apply]
  rw [h3]
  exact (mul_right_cancel h1).symm

theorem eq_one_of_fixedPointFree_sq {V : Type*} [CommGroup V] [Finite V] {p : ℕ} (hp : p.Prime)
    (hV : Nat.Coprime p (Nat.card V)) (α β : MulAut V) (hαβ : Commute α β) (hα : α ^ p = 1)
    (hβ : β ^ p = 1)
    (hfpf : ∀ i j : ℕ, i < p → j < p → (i ≠ 0 ∨ j ≠ 0) → ∀ w : V, (α ^ i * β ^ j) w = w → w = 1)
    (v : V) : v = 1 := by
  have hp1 : 1 < p := hp.one_lt
  have hA : ∀ j < p, ∏ k ∈ Finset.range p, ((α * β ^ j) ^ k) v = 1 := by
    intro j hj
    refine prod_pow_apply_eq_one _ ?_ ?_ v
    · rw [(hαβ.pow_right j).mul_pow, hα, ← pow_mul, mul_comm, pow_mul, hβ, one_pow, one_mul]
    · intro w hw
      exact hfpf 1 j hp1 hj (Or.inl one_ne_zero) w (by simpa using hw)
  have hB : ∀ k, 0 < k → k < p → ∏ j ∈ Finset.range p, ((β ^ k) ^ j) v = 1 := by
    intro k hk0 hkp
    refine prod_pow_apply_eq_one _ ?_ ?_ v
    · rw [← pow_mul, mul_comm, pow_mul, hβ, one_pow]
    · intro w hw
      exact hfpf 0 k (by omega) hkp (Or.inr hk0.ne') w (by simpa using hw)
  have hprod : ∏ j ∈ Finset.range p, ∏ k ∈ Finset.range p, ((α * β ^ j) ^ k) v = 1 :=
    Finset.prod_eq_one fun j hj => hA j (Finset.mem_range.1 hj)
  have hexp : ∀ j k : ℕ, ((α * β ^ j) ^ k) v = (α ^ k) (((β ^ k) ^ j) v) := by
    intro j k
    rw [(hαβ.pow_right j).mul_pow, MulAut.mul_apply, ← pow_mul, ← pow_mul, mul_comm j k]
  simp_rw [hexp] at hprod
  rw [Finset.prod_comm] at hprod
  simp_rw [← map_prod] at hprod
  have hsplit := Finset.prod_range_succ'
    (fun k => (α ^ k) (∏ j ∈ Finset.range p, ((β ^ k) ^ j) v)) (p - 1)
  rw [Nat.sub_add_cancel hp1.le] at hsplit
  rw [hsplit] at hprod
  have hrest : ∏ k ∈ Finset.range (p - 1), (α ^ (k + 1)) (∏ j ∈ Finset.range p,
      ((β ^ (k + 1)) ^ j) v) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    rw [hB (k + 1) (Nat.succ_pos k) (by have := Finset.mem_range.1 hk; omega), map_one]
  rw [hrest, one_mul] at hprod
  simp only [pow_zero, one_pow, MulAut.one_apply, Finset.prod_const, Finset.card_range] at hprod
  have hdvd : orderOf v ∣ p := orderOf_dvd_of_pow_eq_one hprod
  have hdvd' : orderOf v ∣ Nat.card V := orderOf_dvd_natCard v
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hV hdvd hdvd')

end CFSG.GroupTheory.WielandtProduct
