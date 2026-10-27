module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLift

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

section Lists

variable {X : Type*} [Group X]

theorem subgroupOfList_exists [Finite X] (L : List X) (h1 : (1 : X) ∈ L)
    (hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) : ∃ H : Subgroup X, ∀ x, x ∈ H ↔ x ∈ L := by
  have hpow : ∀ x ∈ L, ∀ n : ℕ, x ^ n ∈ L := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  have hinv : ∀ x ∈ L, x⁻¹ ∈ L := by
    intro x hx
    have hpos := orderOf_pos x
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel hpos,
        pow_orderOf_eq_one]
    rw [this]
    exact hpow x hx _
  exact ⟨{ carrier := {x | x ∈ L}
           one_mem' := h1
           mul_mem' := fun {a b} ha hb => hmul a ha b hb
           inv_mem' := fun {x} hx => hinv x hx }, fun x => Iff.rfl⟩

theorem card_of_list {H : Subgroup X} {L : List X} (hL : L.Nodup) (h : ∀ x, x ∈ H ↔ x ∈ L) :
    Nat.card ↥H = L.length := by
  classical
  have h1 : Nat.card ↥H = Nat.card {x // x ∈ L.toFinset} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (h x).trans List.mem_toFinset.symm)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]

theorem mem_normalizer_of_lists (A : Subgroup X) (Al : List X) (hA : ∀ y, y ∈ A ↔ y ∈ Al)
    (g : X) : g ∈ Subgroup.normalizer (A : Set X) ↔
      ∀ a ∈ Al, g * a * g⁻¹ ∈ Al ∧ g⁻¹ * a * g ∈ Al := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h a ha
    have haA : a ∈ A := (hA a).2 ha
    refine ⟨(hA _).1 ((h a).1 haA), (hA _).1 ((h _).2 ?_)⟩
    simpa [mul_assoc] using haA
  · intro h y
    rw [hA, hA]
    constructor
    · intro hy
      exact (h y hy).1
    · intro hy
      have := (h _ hy).2
      simpa [mul_assoc] using this

theorem not_dvd_chi0_of_lt {m : ℕ} (h0 : 0 < m) (hm : m < 60) :
    ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ m) := by
  intro n hn hd
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ 4 ^ n := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h60 : 60 ≤ 2 ^ n * (4 ^ n - 1) := by
    calc 60 = 4 * 15 := by norm_num
      _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 (by omega)
  have := Nat.le_of_dvd h0 hd
  omega

theorem goodLocal_of_lists [Finite X] [DecidableEq X] (Kx : Subgroup X) (Kl : List X)
    (hK : ∀ x, x ∈ Kx ↔ x ∈ Kl) (hKnd : Kl.Nodup) (Ql : List X) (hQnd : Ql.Nodup)
    (hQK : ∀ q ∈ Ql, q ∈ Kl) (h1 : (1 : X) ∈ Ql) (hmul : ∀ p ∈ Ql, ∀ q ∈ Ql, p * q ∈ Ql)
    (hnorm : ∀ k ∈ Kl, ∀ q ∈ Ql, k * q * k⁻¹ ∈ Ql) {a : ℕ} (h2 : ∀ q ∈ Ql, q ^ (2 ^ a) = 1)
    (hcent : ∀ y ∈ Kl, (∀ q ∈ Ql, y * q = q * y) → y ∈ Ql)
    (hA3 : ∀ b ∈ Kl, b ≠ 1 → b ^ 3 = 1 →
      4 < (Ql.map fun q => q * b * q⁻¹ * b⁻¹).dedup.length)
    (hN : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ Kl.length / Ql.length)) :
    GoodLocal Kx := by
  classical
  obtain ⟨Qx, hQx⟩ := subgroupOfList_exists Ql h1 hmul
  have hQxK : Qx ≤ Kx := fun x hx => (hK x).2 (hQK x ((hQx x).1 hx))
  let Q : Subgroup ↥Kx := Qx.subgroupOf Kx
  have hmemQ : ∀ y : ↥Kx, y ∈ Q ↔ (y : X) ∈ Ql := fun y =>
    Subgroup.mem_subgroupOf.trans (hQx _)
  have hQN : Q.Normal := ⟨fun n hn g => by
    rw [hmemQ] at hn ⊢
    exact hnorm (g : X) ((hK _).1 g.2) (n : X) hn⟩
  have hQ2 : IsPGroup 2 Q := by
    intro g
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    have := h2 _ ((hmemQ _).1 g.2)
    simpa using this
  have hcent' : ∀ y : ↥Kx, (∀ q ∈ Q, y * q = q * y) → y ∈ Q := by
    intro y hy
    rw [hmemQ]
    refine hcent _ ((hK _).1 y.2) fun q hq => ?_
    have hqK : q ∈ Kx := (hK q).2 (hQK q hq)
    have := hy ⟨q, hqK⟩ ((hmemQ _).2 hq)
    exact congrArg Subtype.val this
  have hA3' : ∀ b : ↥Kx, orderOf b = 3 → 4 < Nat.card ↥⁅Q, Subgroup.zpowers b⁆ := by
    intro b hb
    have hb1 : (b : X) ≠ 1 := by
      intro h
      have : b = 1 := Subtype.ext h
      rw [this, orderOf_one] at hb
      omega
    have hb3 : (b : X) ^ 3 = 1 := by
      have := pow_orderOf_eq_one b
      rw [hb] at this
      exact congrArg Subtype.val this
    have h := hA3 _ ((hK _).1 b.2) hb1 hb3
    set H : Subgroup ↥Kx := ⁅Q, Subgroup.zpowers b⁆ with hH
    have hcard : Nat.card (H.map Kx.subtype) = Nat.card H :=
      Subgroup.card_map_of_injective Kx.subtype_injective
    have hsub : ((Ql.map fun q => q * (b : X) * q⁻¹ * (b : X)⁻¹).toFinset : Set X) ⊆
        (H.map Kx.subtype : Set X) := by
      intro y hy
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      have hqK : q ∈ Kx := (hK q).2 (hQK q hq)
      refine ⟨⁅(⟨q, hqK⟩ : ↥Kx), b⁆, ?_, ?_⟩
      · exact Subgroup.commutator_mem_commutator ((hmemQ _).2 hq) (Subgroup.mem_zpowers b)
      · simp [commutatorElement_def]
    have hfin : (H.map Kx.subtype : Set X).Finite := Set.toFinite _
    have h3 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, List.card_toFinset] at h3
    have h4 : Nat.card ↥(H.map Kx.subtype : Set X) = Nat.card (H.map Kx.subtype) := rfl
    omega
  have hN' : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ Nat.card (↥Kx ⧸ Q)) := by
    intro n hn
    have hKc : Nat.card ↥Kx = Kl.length := card_of_list hKnd hK
    have hQc : Nat.card ↥Q = Ql.length := by
      rw [← card_of_list hQnd hQx]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQxK).toEquiv
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    rw [hKc, hQc] at hprod
    have hpos : 0 < Ql.length := List.length_pos_of_mem h1
    have : Nat.card (↥Kx ⧸ Q) = Kl.length / Ql.length := by
      rw [hprod, Nat.mul_div_cancel _ hpos]
    rw [this]
    exact hN n hn
  exact @GoodLocal.of_data X _ Kx _ Q hQN hQ2 hcent' hA3' hN'

end Lists

section Canonical

variable {X : Type*} [Group X]

@[expose] def canonZ (S : Subgroup X) : Subgroup X := S ⊓ Subgroup.centralizer (S : Set X)

@[expose] def commSet (S : Subgroup X) : Set X :=
  {c | ∃ s ∈ S, ∃ t ∈ S, c = s * t * s⁻¹ * t⁻¹}

@[expose] def canonC (S : Subgroup X) : Subgroup X := S ⊓ Subgroup.centralizer (commSet S)

theorem mem_canonZ {S : Subgroup X} {x : X} :
    x ∈ canonZ S ↔ x ∈ S ∧ ∀ s ∈ S, s * x = x * s := by
  simp only [canonZ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem mem_canonC {S : Subgroup X} {x : X} :
    x ∈ canonC S ↔ x ∈ S ∧ ∀ s ∈ S, ∀ t ∈ S, (s * t * s⁻¹ * t⁻¹) * x = x * (s * t * s⁻¹ * t⁻¹) := by
  simp only [canonC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, commSet]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h s hs t ht
    exact h _ ⟨s, hs, t, ht, rfl⟩
  · rintro h c ⟨s, hs, t, ht, rfl⟩
    exact h s hs t ht

theorem canonZ_map (α : X ≃* X) (S : Subgroup X) :
    (canonZ S).map α.toMonoidHom = canonZ (S.map α.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy : y ∈ canonZ S := hy
    rw [mem_canonZ] at hy
    rw [mem_canonZ]
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    show α s * α y = α y * α s
    rw [← map_mul, ← map_mul, hy.2 s hs]
  · intro hx
    rw [mem_canonZ] at hx
    obtain ⟨⟨y, hy, rfl⟩, h⟩ := hx
    refine ⟨y, ?_, rfl⟩
    show y ∈ canonZ S
    rw [mem_canonZ]
    refine ⟨hy, fun s hs => ?_⟩
    have := h (α s) ⟨s, hs, rfl⟩
    apply α.injective
    simpa using this

theorem canonC_map (α : X ≃* X) (S : Subgroup X) :
    (canonC S).map α.toMonoidHom = canonC (S.map α.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy : y ∈ canonC S := hy
    rw [mem_canonC] at hy
    rw [mem_canonC]
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have := hy.2 s hs t ht
    have := congrArg α this
    simpa using this
  · intro hx
    rw [mem_canonC] at hx
    obtain ⟨⟨y, hy, rfl⟩, h⟩ := hx
    refine ⟨y, ?_, rfl⟩
    show y ∈ canonC S
    rw [mem_canonC]
    refine ⟨hy, fun s hs t ht => ?_⟩
    have := h (α s) ⟨s, hs, rfl⟩ (α t) ⟨t, ht, rfl⟩
    apply α.injective
    simpa using this

theorem canonical_normalizer (F : Subgroup X → Subgroup X)
    (hF : ∀ (α : X ≃* X) (S : Subgroup X), (F S).map α.toMonoidHom = F (S.map α.toMonoidHom))
    {S : Subgroup X} (α : MulAut X) (hα : S.map α.toMonoidHom = S) :
    (Subgroup.normalizer (F S : Set X)).map α.toMonoidHom = Subgroup.normalizer (F S : Set X) := by
  rw [Subgroup.map_equiv_normalizer_eq (F S) α, hF α S, hα]

end Canonical

section Pair

@[expose] def LocalPair (X : Type) [Group X] : Prop :=
  ∃ S₀ K₁ K₂ : Subgroup X, IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧
    (∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → K₁.map α.toMonoidHom = K₁) ∧
    (∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → K₂.map α.toMonoidHom = K₂) ∧
    K₁ ≠ ⊤ ∧ K₂ ≠ ⊤ ∧ K₁ ⊔ K₂ = ⊤ ∧ GoodLocal K₁ ∧ GoodLocal K₂

theorem pairsFor_of_localPair (s : TauCeti.SporadicName)
    [Finite (NativeSporadic.Carrier s)] (h : LocalPair (NativeSporadic.Carrier s)) :
    PairsFor (TypeSporadic s) := by
  intro G _ _ L R hq hty hR hRN hS
  obtain ⟨e⟩ := hty
  obtain ⟨S₀, K₁, K₂, hS₀, hS₀i, hinv₁, hinv₂, hne₁, hne₂, hsup, hg₁, hg₂⟩ := h
  let θ0 : ↥L →* NativeSporadic.Carrier s :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hθ0 : Function.Surjective θ0 := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ0.ker = CFSG.pCore 2 ↥L := by
    ext x
    simp [θ0]
  exact pairConclusion_of_local_pair hRN hS θ0 hθ0 hker S₀ hS₀ hS₀i K₁ K₂ hinv₁ hinv₂ hne₁ hne₂
    hsup hg₁ hg₂

end Pair

end CFSG.QuasithinUnique.Vol2Native.L239
