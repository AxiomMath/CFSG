module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.Solomon75

open scoped commutatorElement

theorem eq_one_of_mem_of_mem_odd {G : Type*} [Group G] (L V : Subgroup G)
    (hL : Odd (Nat.card L)) (hV : IsPGroup 2 V) {x : G} (hxV : x ∈ V) (hxL : x ∈ L) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨x, hxV⟩
  have h1 : x ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h2 : x ^ Nat.card L = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := L) (x := ⟨x, hxL⟩))
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card L) :=
    (Nat.coprime_two_left.2 hL).pow_left k
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem map_eq_one_of_mul_eq_one_aux {G : Type*} [Group G] {Q : Type*} [Group Q] (π : G →* Q)
    (P Pp : Subgroup G) (hc : ∀ (a : P) (b : Pp), Commute (π a) (π b))
    {A : Type*} [Group A] (f : P →* A) (hf : Function.Surjective f)
    (hN : ∀ a : P, π a = 1 → f a = 1)
    (hZ : ∀ a : A, (∀ b, a * b = b * a) → a = 1)
    (a : P) (b : Pp) (hab : π a * π b = 1) : f a = 1 := by
  apply hZ
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have hax : Commute (π a) (π x) := by
    have h : π a = (π b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    rw [h]
    exact (hc x b).symm.inv_left
  have h1 : π ((⁅a, x⁆ : P) : G) = 1 := by
    show π ⁅(a : G), (x : G)⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hax
  have h3 := hN _ h1
  rw [map_commutatorElement] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem card_mul_le_card_quotient_of_comm_mod {G : Type*} [Group G] [Finite G]
    (N₀ : Subgroup G) [N₀.Normal] (P₁ P₂ : Subgroup G)
    (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, ⁅a, b⁆ ∈ N₀)
    {A₁ A₂ : Type*} [Group A₁] [Group A₂] [Finite A₁] [Finite A₂]
    (f₁ : P₁ →* A₁) (f₂ : P₂ →* A₂)
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂)
    (hN₁ : ∀ a : P₁, (a : G) ∈ N₀ → f₁ a = 1) (hN₂ : ∀ b : P₂, (b : G) ∈ N₀ → f₂ b = 1)
    (hZ₁ : ∀ a : A₁, (∀ b, a * b = b * a) → a = 1)
    (hZ₂ : ∀ a : A₂, (∀ b, a * b = b * a) → a = 1) :
    Nat.card A₁ * Nat.card A₂ ≤ Nat.card (G ⧸ N₀) := by
  let π : G →* G ⧸ N₀ := QuotientGroup.mk' N₀
  have hc : ∀ (a : P₁) (b : P₂), Commute (π a) (π b) := by
    intro a b
    have h' : π ⁅(a : G), (b : G)⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm a a.2 b b.2)
    rw [map_commutatorElement] at h'
    exact commutatorElement_eq_one_iff_mul_comm.1 h'
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : P₁ × P₂ →* G ⧸ N₀, ∀ u, Θ u = π u.1 * π u.2 :=
    ⟨(π.comp P₁.subtype).noncommCoprod (π.comp P₂.subtype) hc, fun u => rfl⟩
  have hF : Function.Surjective (f₁.prodMap f₂) := hf₁.prodMap hf₂
  have hΘF : ∀ u : P₁ × P₂, Θ u = 1 → (f₁.prodMap f₂) u = 1 := by
    rintro ⟨a, b⟩ hu
    rw [hΘ] at hu
    have h₁ : f₁ a = 1 :=
      map_eq_one_of_mul_eq_one_aux π P₁ P₂ hc f₁ hf₁
        (fun a ha => hN₁ a ((QuotientGroup.eq_one_iff _).1 ha)) hZ₁ a b hu
    have h₂ : f₂ b = 1 :=
      map_eq_one_of_mul_eq_one_aux π P₂ P₁ (fun b a => (hc a b).symm) f₂ hf₂
        (fun b hb => hN₂ b ((QuotientGroup.eq_one_iff _).1 hb)) hZ₂ b a (mul_eq_one_comm.1 hu)
    exact Prod.ext h₁ h₂
  have hΘF' : ∀ u v : P₁ × P₂, Θ u = Θ v → (f₁.prodMap f₂) u = (f₁.prodMap f₂) v := by
    intro u v h
    have h1 : Θ (u⁻¹ * v) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hΘF _ h1
    rwa [map_mul, map_inv, inv_mul_eq_one] at h2
  have hinj : Function.Injective (fun z : A₁ × A₂ => Θ (Function.surjInv hF z)) := by
    intro z z' h
    have h1 := hΘF' _ _ h
    rwa [Function.surjInv_eq hF, Function.surjInv_eq hF] at h1
  calc Nat.card A₁ * Nat.card A₂ = Nat.card (A₁ × A₂) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card (G ⧸ N₀) := Nat.card_le_card_of_injective _ hinj

theorem card_mul_le_two_part_of_comm_mod {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : Odd (Nat.card L)) (V₁ V₂ : Subgroup G)
    (hV₁ : IsPGroup 2 V₁) (hV₂ : IsPGroup 2 V₂) (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, ⁅a, b⁆ ∈ L) :
    Nat.card V₁ * Nat.card V₂ ≤
      2 ^ (Nat.card G).factorization 2 * Nat.card (Subgroup.center V₁) := by
  let π : G →* G ⧸ L := QuotientGroup.mk' L
  have hπ : ∀ x : G, π x = 1 ↔ x ∈ L := fun x => QuotientGroup.eq_one_iff x
  have hcommπ : ∀ (a : V₁) (b : V₂), Commute (π a) (π b) := by
    intro a b
    have h : π ⁅(a : G), (b : G)⁆ = 1 := (hπ _).2 (hcomm a a.2 b b.2)
    rw [map_commutatorElement] at h
    exact commutatorElement_eq_one_iff_commute.1 h
  let Θ : V₁ × V₂ →* G ⧸ L :=
    (π.comp V₁.subtype).noncommCoprod (π.comp V₂.subtype) hcommπ
  have hΘ : ∀ a : V₁, ∀ b : V₂, Θ (a, b) = π a * π b := fun a b => rfl
  have hker : Nat.card Θ.ker ≤ Nat.card (Subgroup.center V₁) := by
    have hmem : ∀ p : Θ.ker, p.1.1 ∈ Subgroup.center V₁ := by
      rintro ⟨⟨a, b⟩, hab⟩
      have h1 : π a * π b = 1 := (hΘ a b).symm.trans (MonoidHom.mem_ker.1 hab)
      have h2 : π a = (π b)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [Subgroup.mem_center_iff]
      intro x
      have hc : Commute (π x) (π a) := by
        rw [h2]
        exact (hcommπ x b).inv_right
      have hxa : ⁅(x : G), (a : G)⁆ ∈ L := by
        rw [← hπ, map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.2 hc
      have hxaV : ⁅(x : G), (a : G)⁆ ∈ V₁ := by
        rw [commutatorElement_def]
        exact V₁.mul_mem (V₁.mul_mem (V₁.mul_mem x.2 a.2) (V₁.inv_mem x.2)) (V₁.inv_mem a.2)
      have h3 := eq_one_of_mem_of_mem_odd L V₁ hL hV₁ hxaV hxa
      have h4 : Commute (x : G) (a : G) := commutatorElement_eq_one_iff_commute.1 h3
      exact Subtype.ext h4.eq
    let f : Θ.ker → Subgroup.center V₁ := fun p => ⟨p.1.1, hmem p⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
      have ha : a = a' := congrArg Subtype.val h
      subst ha
      have h1 : π a * π b = 1 := (hΘ a b).symm.trans (MonoidHom.mem_ker.1 hab)
      have h1' : π a * π b' = 1 := (hΘ a b').symm.trans (MonoidHom.mem_ker.1 hab')
      have h5 : π b = π b' := mul_left_cancel (h1.trans h1'.symm)
      have h6 : (b : G)⁻¹ * b' ∈ L := QuotientGroup.eq.1 h5
      have h7 : (b : G)⁻¹ * b' ∈ V₂ := V₂.mul_mem (V₂.inv_mem b.2) b'.2
      have h8 := eq_one_of_mem_of_mem_odd L V₂ hL hV₂ h7 h6
      have h9 : (b : G) = b' := inv_mul_eq_one.1 h8
      have h10 : b = b' := Subtype.ext h9
      subst h10
      rfl
    exact Nat.card_le_card_of_injective f hf
  have hrange : Nat.card Θ.range ≤ 2 ^ (Nat.card G).factorization 2 := by
    obtain ⟨m, hm⟩ := hV₁.exists_card_eq
    obtain ⟨n, hn⟩ := hV₂.exists_card_eq
    have hdvd : Nat.card Θ.range ∣ 2 ^ (m + n) := by
      have := Subgroup.card_ker_mul_card_range Θ
      rw [Nat.card_prod, hm, hn, ← pow_add] at this
      exact Dvd.intro_left _ this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hdvdG : 2 ^ j ∣ Nat.card G := by
      rw [← hj]
      exact (Subgroup.card_subgroup_dvd_card Θ.range).trans (Subgroup.card_quotient_dvd_card L)
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    rw [hj]
    exact Nat.pow_le_pow_right Nat.two_pos
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hG0).1 hdvdG)
  calc Nat.card V₁ * Nat.card V₂ = Nat.card Θ.ker * Nat.card Θ.range := by
        rw [Subgroup.card_ker_mul_card_range Θ, Nat.card_prod]
    _ ≤ Nat.card (Subgroup.center V₁) * 2 ^ (Nat.card G).factorization 2 :=
        Nat.mul_le_mul hker hrange
    _ = 2 ^ (Nat.card G).factorization 2 * Nat.card (Subgroup.center V₁) := mul_comm _ _

theorem two_pow_factorization_card_le {n : ℕ} (hn : n ≤ 11) (Q : Subgroup (Equiv.Perm (Fin n))) :
    2 ^ (Nat.card Q).factorization 2 ≤ 256 := by
  have hdvd : Nat.card Q ∣ n.factorial := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
  have hdvd2 : Nat.card Q ∣ (11).factorial := hdvd.trans (Nat.factorial_dvd_factorial hn)
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have h8 : (Nat.card Q).factorization 2 ≤ 8 := by
    by_contra hcon
    push Not at hcon
    have h9 : 2 ^ 9 ∣ Nat.card Q :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hQ0).2 hcon
    have h10 : 2 ^ 9 ∣ (11).factorial := h9.trans hdvd2
    revert h10
    decide
  calc 2 ^ (Nat.card Q).factorization 2 ≤ 2 ^ 8 := Nat.pow_le_pow_right Nat.two_pos h8
    _ = 256 := by norm_num

theorem factorial_succ_lt_sq {b : ℕ} (hb : 5 ≤ b) :
    (b + 1).factorial < b.factorial / 2 * (b.factorial / 2) := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ b hb ih =>
    obtain ⟨c, hc⟩ : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hdiv : b.factorial / 2 = c := by omega
    rw [hdiv] at ih
    have h1 : (b + 1).factorial = 2 * ((b + 1) * c) := by
      rw [Nat.factorial_succ, hc]; ring
    have h2 : (b + 1).factorial / 2 = (b + 1) * c := by omega
    have h3 : (b + 1 + 1).factorial = (b + 2) * (2 * ((b + 1) * c)) := by
      rw [Nat.factorial_succ (b + 1), h1]
    rw [h2, h3]
    rw [h1] at ih
    have hc0 : 0 < c := by
      have := Nat.factorial_pos b
      omega
    have hc2 : 2 * (b + 1) < c := by
      by_contra hcon
      push Not at hcon
      nlinarith [Nat.mul_le_mul_right c hcon]
    have hd : 2 * (b + 2) < (b + 1) * c := by nlinarith
    have hd0 : 0 < (b + 1) * c := Nat.mul_pos (by omega) hc0
    calc (b + 2) * (2 * ((b + 1) * c)) = (2 * (b + 2)) * ((b + 1) * c) := by ring
      _ < ((b + 1) * c) * ((b + 1) * c) := Nat.mul_lt_mul_of_pos_right hd hd0

theorem center_eq_one_of_simple_not_solvable {S : Type*} [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) (a : S) (ha : ∀ b, a * b = b * a) : a = 1 := by
  by_contra hne
  have hmem : a ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun b => (ha b).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · rw [h] at hmem
    exact hne (Subgroup.mem_bot.1 hmem)
  · refine hns (Group.isSolvable_of_comm fun x y => ?_)
    have hx : x ∈ Subgroup.center S := by
      rw [h]
      exact Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.1 hx y).symm

theorem isSolvable_range_of_ker_le {T S R : Type*} [Group T] [Group S] [Group R]
    (p : T →* S) (ψ : T →* R) [Group.IsSolvable ψ.range] (h : ∀ t, ψ t = 1 → p t = 1) :
    Group.IsSolvable p.range := by
  let Θ : T →* S × R := p.prod ψ
  let e : Θ.range →* ψ.range :=
    ((MonoidHom.snd S R).comp Θ.range.subtype).codRestrict ψ.range (by
      rintro ⟨_, t, rfl⟩
      exact ⟨t, rfl⟩)
  have he : Function.Injective e := by
    rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ hee
    have h1 : ψ t = ψ t' := congrArg Subtype.val hee
    have h2 : ψ (t⁻¹ * t') = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := h _ h2
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact Subtype.ext (Prod.ext h3 h1)
  have : Group.IsSolvable Θ.range := Group.isSolvable_of_isSolvable_injective he
  let q : Θ.range →* p.range :=
    ((MonoidHom.fst S R).comp Θ.range.subtype).codRestrict p.range (by
      rintro ⟨_, t, rfl⟩
      exact ⟨t, rfl⟩)
  have hq : Function.Surjective q := by
    rintro ⟨_, t, rfl⟩
    exact ⟨⟨(p t, ψ t), t, rfl⟩, rfl⟩
  exact Group.isSolvable_of_surjective hq

theorem le_ker_of_odd_card {P : Type*} [Group P] {S : Type*} [Group S] [IsSimpleGroup S]
    (he : Even (Nat.card S)) (f : P →* S) (hf : Function.Surjective f)
    (K : Subgroup P) [K.Normal] (hK : Odd (Nat.card K)) : K ≤ f.ker := by
  have : (K.map f).Normal := Subgroup.Normal.map ‹K.Normal› f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map f) with h | h
  · exact (Subgroup.map_eq_bot_iff K).1 h
  · have h1 : Nat.card (K.map f) ∣ Nat.card K := Subgroup.card_map_dvd K f
    rw [h, Subgroup.card_top] at h1
    exact absurd he (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hK h1))

theorem le_ker_of_solvable_range {P : Type*} [Group P] {S : Type*} [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) (f : P →* S) (hf : Function.Surjective f)
    (N : Subgroup P) [N.Normal] {Q : Type*} [Group Q] (ψ : N →* Q) [Group.IsSolvable ψ.range]
    (h : ∀ t : N, ψ t = 1 → f t = 1) : N ≤ f.ker := by
  have : (N.map f).Normal := Subgroup.Normal.map ‹N.Normal› f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h' | h'
  · exact (Subgroup.map_eq_bot_iff N).1 h'
  · exfalso
    have := isSolvable_range_of_ker_le (f.comp N.subtype) ψ h
    have hrange : (f.comp N.subtype).range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact h'
    refine hns (Group.isSolvable_of_surjective (f := (f.comp N.subtype).range.subtype) ?_)
    intro s
    refine ⟨⟨s, ?_⟩, rfl⟩
    rw [hrange]
    exact Subgroup.mem_top s

theorem map_eq_one_of_mem_sup_odd_solvable {G : Type*} [Group G] (L K : Subgroup G)
    [L.Normal] [K.Normal] (hK : Group.IsSolvable K) (hL : Odd (Nat.card L))
    (P : Subgroup G) {S : Type*} [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) (he : Even (Nat.card S))
    (f : P →* S) (hf : Function.Surjective f) :
    ∀ a : P, (a : G) ∈ L ⊔ K → f a = 1 := by
  have hA : ∀ a : P, (a : G) ∈ L → f a = 1 := by
    intro a ha
    have : (L.comap P.subtype).Normal := Subgroup.Normal.comap ‹L.Normal› P.subtype
    exact le_ker_of_odd_card he f hf (L.comap P.subtype)
      (Odd.of_dvd_nat hL
        (Subgroup.card_comap_dvd_of_injective L P.subtype P.subtype_injective)) ha
  let π : G →* G ⧸ L := QuotientGroup.mk' L
  have : Group.IsSolvable (K.map π) := Group.isSolvable_of_surjective (π.subgroupMap_surjective K)
  have : (L ⊔ K).Normal := Subgroup.sup_normal L K
  have : ((L ⊔ K).comap P.subtype).Normal := Subgroup.Normal.comap ‹(L ⊔ K).Normal› P.subtype
  let N : Subgroup P := (L ⊔ K).comap P.subtype
  let ψ : N →* G ⧸ L := π.comp (P.subtype.comp N.subtype)
  have hψ : ψ.range ≤ K.map π := by
    rintro _ ⟨t, rfl⟩
    have ht : ((t : P) : G) ∈ L ⊔ K := t.2
    obtain ⟨l, hl, k, hk, hlk⟩ := Subgroup.mem_sup_of_normal_left.1 ht
    refine ⟨k, hk, ?_⟩
    have hπl : π l = 1 := (QuotientGroup.eq_one_iff l).2 hl
    show π k = π ((t : P) : G)
    rw [← hlk, map_mul, hπl, one_mul]
  have : Group.IsSolvable ψ.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hψ)
      (Subgroup.inclusion_injective hψ)
  intro a ha
  exact le_ker_of_solvable_range hns f hf N ψ
    (fun t ht => hA t ((QuotientGroup.eq_one_iff _).1 ht)) ha

theorem card_mul_le_factorial_of_solvable_ker {G : Type*} [Group G] [Finite G]
    {β : Type*} [Fintype β] [DecidableEq β]
    (Φ : G →* Equiv.Perm β) (hΦ : Group.IsSolvable Φ.ker)
    (L : Subgroup G) [L.Normal] (hL : Odd (Nat.card L))
    (P₁ P₂ : Subgroup G) (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, ⁅a, b⁆ ∈ L)
    {S₁ S₂ : Type*} [Group S₁] [Group S₂] [Finite S₁] [Finite S₂]
    [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hns₁ : ¬ Group.IsSolvable S₁) (hns₂ : ¬ Group.IsSolvable S₂)
    (he₁ : Even (Nat.card S₁)) (he₂ : Even (Nat.card S₂))
    (f₁ : P₁ →* S₁) (f₂ : P₂ →* S₂)
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂) :
    Nat.card S₁ * Nat.card S₂ ≤ (Fintype.card β).factorial := by
  have : Φ.ker.Normal := Φ.normal_ker
  have : (L ⊔ Φ.ker).Normal := Subgroup.sup_normal L Φ.ker
  have hN₁ : ∀ a : P₁, (a : G) ∈ L ⊔ Φ.ker → f₁ a = 1 :=
    map_eq_one_of_mem_sup_odd_solvable L Φ.ker hΦ hL P₁ hns₁ he₁ f₁ hf₁
  have hN₂ : ∀ b : P₂, (b : G) ∈ L ⊔ Φ.ker → f₂ b = 1 :=
    map_eq_one_of_mem_sup_odd_solvable L Φ.ker hΦ hL P₂ hns₂ he₂ f₂ hf₂
  have hcomm' : ∀ a ∈ P₁, ∀ b ∈ P₂, ⁅a, b⁆ ∈ L ⊔ Φ.ker :=
    fun a ha b hb => Subgroup.mem_sup_left (hcomm a ha b hb)
  have h1 := card_mul_le_card_quotient_of_comm_mod (L ⊔ Φ.ker) P₁ P₂ hcomm' f₁ f₂ hf₁ hf₂
    hN₁ hN₂ (center_eq_one_of_simple_not_solvable hns₁) (center_eq_one_of_simple_not_solvable hns₂)
  have h2 : Nat.card (G ⧸ (L ⊔ Φ.ker)) ≤ Nat.card (G ⧸ Φ.ker) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le le_sup_right)
  have h3 : Nat.card (G ⧸ Φ.ker) = Nat.card Φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
  have h4 : Nat.card Φ.range ≤ Nat.card (Equiv.Perm β) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h5 : Nat.card (Equiv.Perm β) = (Fintype.card β).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  calc Nat.card S₁ * Nat.card S₂ ≤ Nat.card (G ⧸ (L ⊔ Φ.ker)) := h1
    _ ≤ Nat.card (G ⧸ Φ.ker) := h2
    _ = Nat.card Φ.range := h3
    _ ≤ Nat.card (Equiv.Perm β) := h4
    _ = (Fintype.card β).factorial := h5

end CFSG.OddStandard.Solomon75
