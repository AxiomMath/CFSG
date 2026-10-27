module

public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.GH74.Uniqueness.SU.SU7Gen

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup
open scoped Pointwise

theorem exists_norm_lift {X Q : Type*} [Group X] [Finite X] [Group Q] {O S₀ : Subgroup X}
    [O.Normal] (hOodd : Odd (Nat.card O)) (hS₀ : IsPGroup 2 S₀) (ψ : X →* Q)
    (hOk : O ≤ ψ.ker) (hk : ψ.ker ≤ S₀ ⊔ O) (c₀ : X)
    (hc₀ : ∀ s ∈ S₀, ψ (c₀ * s * c₀⁻¹) ∈ S₀.map ψ) :
    ∃ n : X, (∀ s ∈ S₀, n * s * n⁻¹ ∈ S₀) ∧ ψ n = ψ c₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sg : Subgroup X := S₀.map (MulAut.conj c₀).toMonoidHom with hSg
  have hSgle : Sg ≤ S₀ ⊔ O := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨s', hs', hss'⟩ := hc₀ s hs
    have h1 : s'⁻¹ * (c₀ * s * c₀⁻¹) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hss', inv_mul_cancel]
    have h2 := hk h1
    have e : (MulAut.conj c₀).toMonoidHom s = s' * (s'⁻¹ * (c₀ * s * c₀⁻¹)) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [e]
    exact (S₀ ⊔ O).mul_mem (Subgroup.mem_sup_left hs') h2
  have hSgp : IsPGroup 2 Sg := hS₀.map _
  have hidx : ¬ 2 ∣ S₀.relIndex (S₀ ⊔ O) := by
    rw [Gen.relIndex_sup_odd O hS₀ hOodd]
    have := Nat.odd_iff.1 hOodd
    omega
  obtain ⟨y, hy, hyS⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2) hSgle hSgp
    le_sup_left hS₀ hidx
  have hn₂ : y⁻¹ * c₀ ∈ normalizer (S₀ : Set X) := by
    apply Gen.mem_normalizer_of_conj_le
    intro s hs
    have := hyS (c₀ * s * c₀⁻¹) ⟨s, hs, by simp [MulAut.conj_apply]⟩
    have e : y⁻¹ * c₀ * s * (y⁻¹ * c₀)⁻¹ = y⁻¹ * (c₀ * s * c₀⁻¹) * y := by group
    rw [e]; exact this
  obtain ⟨s₁, hs₁, o₁, ho₁, hyso⟩ := Subgroup.mem_sup_of_normal_right.1 hy
  have hψy : ψ y = ψ s₁ := by
    rw [← hyso, map_mul, MonoidHom.mem_ker.1 (hOk ho₁), mul_one]
  refine ⟨s₁ * (y⁻¹ * c₀), fun s hs => ?_, ?_⟩
  · have h1 : (y⁻¹ * c₀) * s * (y⁻¹ * c₀)⁻¹ ∈ S₀ := (mem_normalizer_iff.1 hn₂ s).1 hs
    have e : s₁ * (y⁻¹ * c₀) * s * (s₁ * (y⁻¹ * c₀))⁻¹ =
        s₁ * ((y⁻¹ * c₀) * s * (y⁻¹ * c₀)⁻¹) * s₁⁻¹ := by group
    rw [e]
    exact S₀.mul_mem (S₀.mul_mem hs₁ h1) (S₀.inv_mem hs₁)
  · rw [map_mul, map_mul, map_inv, hψy]
    group

theorem exists_odd_pow {X Q : Type*} [Group X] [Finite X] [Group Q] (ψ : X →* Q) {n : X}
    (h3 : ψ n * ψ n * ψ n = 1) :
    ∃ j : ℕ, Odd (orderOf (n ^ j)) ∧ (ψ (n ^ j) = ψ n ∨ ψ (n ^ j) = (ψ n)⁻¹) := by
  have hm : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨k, m', hm', hmk⟩ := Nat.exists_eq_two_pow_mul_odd hm
  refine ⟨2 ^ k, ?_, ?_⟩
  · have h2k : 2 ^ k ≠ 0 := by positivity
    rw [orderOf_pow' n h2k, hmk]
    have : Nat.gcd (2 ^ k * m') (2 ^ k) = 2 ^ k := Nat.gcd_eq_right (Dvd.intro m' rfl)
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm'
  · have h3' : (ψ n) ^ 3 = 1 := by rw [pow_succ, pow_two]; exact h3
    rw [map_pow, pow_eq_pow_mod _ h3']
    have h3k : ¬ 3 ∣ 2 ^ k := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by omega
    rcases hmod with h | h
    · left; rw [h, pow_one]
    · right; rw [h]
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]; exact h3'

theorem nonempty_mulEquiv_prod {G : Type*} [Group G] {H₀ C₁ : Subgroup G}
    (hcomm : ∀ a ∈ H₀, ∀ c ∈ C₁, a * c = c * a) (hdisj : H₀ ⊓ C₁ = ⊥) :
    Nonempty (↥(H₀ ⊔ C₁) ≃* ↥H₀ × ↥C₁) := by
  let f : ↥H₀ × ↥C₁ →* ↥(H₀ ⊔ C₁) :=
    MonoidHom.noncommCoprod (Subgroup.inclusion le_sup_left) (Subgroup.inclusion le_sup_right)
      (fun a c => Subtype.ext (hcomm a a.2 c c.2))
  have hf : ∀ a : ↥H₀, ∀ c : ↥C₁, ((f (a, c) : ↥(H₀ ⊔ C₁)) : G) = (a : G) * c := fun a c => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, c⟩ h
    have h1 : (a : G) * c = 1 := by rw [← hf]; exact congrArg Subtype.val h
    have h2 : (a : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : G) ∈ H₀ ⊓ C₁ := ⟨a.2, by rw [h2]; exact C₁.inv_mem c.2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have ha1 : a = 1 := Subtype.ext h3
    have hc1 : (c : G) = 1 := by rw [h3, one_mul] at h1; exact h1
    exact Prod.ext ha1 (Subtype.ext hc1)
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := SU5.mem_sup_of_commute hcomm hg
    exact ⟨(⟨a, ha⟩, ⟨c, hc⟩), Subtype.ext (hf ⟨a, ha⟩ ⟨c, hc⟩)⟩
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

theorem exists_hom_complement {Gt : Type*} [Group Gt] {Tb Hh : Subgroup Gt}
    (hHn : ∀ h ∈ Hh, ∀ t ∈ Tb, h * t * h⁻¹ ∈ Tb) (hdisj : Tb ⊓ Hh = ⊥) :
    ∃ ν : ↥(Tb ⊔ Hh) →* ↥Hh, Function.Surjective ν ∧
      ∀ p : ↥(Tb ⊔ Hh), ν p = 1 ↔ (p : Gt) ∈ Tb := by
  classical
  have hHN : Hh ≤ normalizer (Tb : Set Gt) := fun h hh => by
    rw [mem_normalizer_iff]
    intro t
    refine ⟨hHn h hh t, fun ht => ?_⟩
    have := hHn h⁻¹ (Hh.inv_mem hh) _ ht
    simpa [mul_assoc] using this
  have hPN : Tb ⊔ Hh ≤ normalizer (Tb : Set Gt) := sup_le Subgroup.le_normalizer hHN
  set P : Subgroup Gt := Tb ⊔ Hh with hP
  have hTP : Tb ≤ P := le_sup_left
  have hHP : Hh ≤ P := le_sup_right
  have hTn : (Tb.subgroupOf P).Normal := ⟨fun n hn g => by
    have hn' : (n : Gt) ∈ Tb := hn
    exact (mem_normalizer_iff.1 (hPN g.2) n).1 hn'⟩
  have hcompl : (Hh.subgroupOf P).IsComplement' (Tb.subgroupOf P) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro p hpH hpT
      have hpH' : (p : Gt) ∈ Hh := hpH
      have hpT' : (p : Gt) ∈ Tb := hpT
      have : (p : Gt) ∈ Tb ⊓ Hh := ⟨hpT', hpH'⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · apply Set.eq_univ_of_forall
      intro p
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right Hh Tb hHN
      have hp : (p : Gt) ∈ (Hh : Set Gt) * (Tb : Set Gt) := by
        rw [← hset, sup_comm]; exact p.2
      obtain ⟨h, hh, t, ht, hht⟩ := Set.mem_mul.1 hp
      exact Set.mem_mul.2 ⟨⟨h, hHP hh⟩, hh, ⟨t, hTP ht⟩, ht, Subtype.ext hht⟩
  let e := hcompl.QuotientMulEquiv
  let ν : ↥P →* ↥Hh := (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Tb.subgroupOf P)))
  have hν : ∀ p : ↥P, ν p = (Subgroup.subgroupOfEquivOfLe hHP)
      (e (QuotientGroup.mk' (Tb.subgroupOf P) p)) := fun p => rfl
  refine ⟨ν, ?_, ?_⟩
  · exact (Subgroup.subgroupOfEquivOfLe hHP).surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  · intro p
    rw [hν]
    constructor
    · intro h
      have h1 : e (QuotientGroup.mk' (Tb.subgroupOf P) p) = 1 :=
        (MulEquiv.map_eq_one_iff _).1 h
      have h2 : QuotientGroup.mk' (Tb.subgroupOf P) p = 1 := (MulEquiv.map_eq_one_iff e).1 h1
      exact (QuotientGroup.eq_one_iff p).1 h2
    · intro hp
      have h1 : QuotientGroup.mk' (Tb.subgroupOf P) p = 1 := (QuotientGroup.eq_one_iff p).2 hp
      rw [h1, map_one, map_one]

theorem commute_of_pow {G : Type*} [Group G] {x y : G} {m : ℕ} (hxy : Commute (x ^ m) y)
    (hcop : Nat.Coprime m (orderOf x)) : Commute x y := by
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← ha]
  exact hxy.pow_left a

theorem exists_orderOf_eq_two_pow {Gt : Type*} [Group Gt] {Tb : Subgroup Gt}
    (hT2 : IsPGroup 2 Tb) {t : Gt} (ht : t ∈ Tb) : ∃ k : ℕ, orderOf t = 2 ^ k := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT2 ⟨t, ht⟩
  refine ⟨k, ?_⟩
  have : orderOf (⟨t, ht⟩ : ↥Tb) = 2 ^ k := by simpa using hk
  rwa [Subgroup.orderOf_mk] at this

theorem cent_le_of_three_elt {Gt : Type*} [Group Gt] [Finite Gt] {Tb Hh Ub : Subgroup Gt}
    (hT2 : IsPGroup 2 Tb)
    (hHn : ∀ h ∈ Hh, ∀ t ∈ Tb, h * t * h⁻¹ ∈ Tb) (hUT : Ub ≤ Tb)
    (hUc : ∀ u ∈ Ub, ∀ t ∈ Tb, u * t = t * u)
    (hcard : Nat.card ↥(centralizer (Ub : Set Gt) ⊓ Hh) = 1 ∨
      Nat.card ↥(centralizer (Ub : Set Gt) ⊓ Hh) = 3)
    {b : Gt} (hb : b ∈ Tb ⊔ Hh) (hbodd : Odd (orderOf b)) (hbU : ∀ u ∈ Ub, b * u = u * b)
    (hbT : ∃ y ∈ Tb, b * y * b⁻¹ ≠ y) :
    Nat.card ↥(centralizer (Ub : Set Gt) ⊓ Hh) = 3 ∧
    ∀ c ∈ Tb ⊔ Hh, (∀ y ∈ Tb, c * y = y * c) → c ∈ Tb := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHN : Hh ≤ normalizer (Tb : Set Gt) := fun h hh => by
    rw [mem_normalizer_iff]
    intro t
    refine ⟨hHn h hh t, fun ht => ?_⟩
    have := hHn h⁻¹ (Hh.inv_mem hh) _ ht
    simpa [mul_assoc] using this
  have hdecomp : ∀ p ∈ Tb ⊔ Hh, ∃ t ∈ Tb, ∃ h ∈ Hh, p = t * h := by
    intro p hp
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right Hh Tb hHN
    have hp' : p ∈ (Hh : Set Gt) * (Tb : Set Gt) := by
      rw [← hset, sup_comm]; exact hp
    obtain ⟨h, hh, t, ht, rfl⟩ := Set.mem_mul.1 hp'
    exact ⟨h * t * h⁻¹, hHn h hh t ht, h, hh, by group⟩
  have hC₁ : ∀ t ∈ Tb, ∀ h ∈ Hh, (∀ u ∈ Ub, (t * h) * u = u * (t * h)) →
      h ∈ centralizer (Ub : Set Gt) ⊓ Hh := by
    intro t ht h hh hp
    refine ⟨mem_centralizer_iff.2 (fun u hu => ?_), hh⟩
    have h1 := hp u hu
    have h2 : Commute u t := hUc u hu t ht
    have h3 : t⁻¹ * u = u * t⁻¹ := h2.inv_right.eq.symm
    have : h * u = u * h := by
      calc h * u = t⁻¹ * ((t * h) * u) := by group
        _ = t⁻¹ * (u * (t * h)) := by rw [h1]
        _ = (t⁻¹ * u) * (t * h) := by group
        _ = (u * t⁻¹) * (t * h) := by rw [h3]
        _ = u * h := by group
    exact this.symm
  have hC₁3 : ∀ h ∈ centralizer (Ub : Set Gt) ⊓ Hh, h * h * h = 1 := by
    intro h hh
    have h1 : (⟨h, hh⟩ : ↥(centralizer (Ub : Set Gt) ⊓ Hh)) ^
        Nat.card ↥(centralizer (Ub : Set Gt) ⊓ Hh) = 1 := pow_card_eq_one'
    rcases hcard with hc | hc
    · rw [hc, pow_one] at h1
      have : h = 1 := congrArg Subtype.val h1
      rw [this]; simp
    · rw [hc, pow_three'] at h1
      exact congrArg Subtype.val h1
  obtain ⟨t', ht', h', hh', hbeq⟩ := hdecomp b hb
  have hh'C : h' ∈ centralizer (Ub : Set Gt) ⊓ Hh :=
    hC₁ t' ht' h' hh' (fun u hu => by rw [← hbeq]; exact hbU u hu)
  obtain ⟨k', hk'⟩ := exists_orderOf_eq_two_pow hT2 ht'
  have hh'1 : h' ≠ 1 := by
    intro h1'
    rw [h1', mul_one] at hbeq
    have hb2 : orderOf b = 2 ^ k' := by rw [hbeq]; exact hk'
    have hb1 : orderOf b = 1 := by
      have hk0 : k' = 0 := by
        by_contra hne
        rw [hb2] at hbodd
        exact (Nat.not_even_iff_odd.2 hbodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
      rw [hb2, hk0, pow_zero]
    have hb1' : b = 1 := orderOf_eq_one_iff.1 hb1
    obtain ⟨y, hy, hne⟩ := hbT
    apply hne
    rw [hb1']; group
  have hc3 : Nat.card ↥(centralizer (Ub : Set Gt) ⊓ Hh) = 3 := by
    rcases hcard with hc1 | hc3
    · exfalso
      have : Subsingleton ↥(centralizer (Ub : Set Gt) ⊓ Hh) :=
        (Nat.card_eq_one_iff_unique.1 hc1).1
      exact hh'1 (congrArg Subtype.val
        (Subsingleton.elim (⟨h', hh'C⟩ : ↥(centralizer (Ub : Set Gt) ⊓ Hh)) 1))
    · exact hc3
  refine ⟨hc3, ?_⟩
  intro c hc hcT
  obtain ⟨t, ht, h, hh, rfl⟩ := hdecomp c hc
  have hhC : h ∈ centralizer (Ub : Set Gt) ⊓ Hh := hC₁ t ht h hh (fun u hu => hcT u (hUT hu))
  have hy1 : ∀ y ∈ Tb, h * y * h⁻¹ = t⁻¹ * y * t := by
    intro y hy
    calc h * y * h⁻¹ = t⁻¹ * ((t * h) * y) * h⁻¹ := by group
      _ = t⁻¹ * (y * (t * h)) * h⁻¹ := by rw [hcT y hy]
      _ = t⁻¹ * y * t := by group
  have ht3 : ∀ y ∈ Tb, (t * t * t) * y = y * (t * t * t) := by
    intro y hy
    have m1 : t⁻¹ * y * t ∈ Tb := Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) hy) ht
    have m2 : t⁻¹ * (t⁻¹ * y * t) * t ∈ Tb :=
      Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) m1) ht
    have key : t⁻¹ * (t⁻¹ * (t⁻¹ * y * t) * t) * t = y := by
      calc t⁻¹ * (t⁻¹ * (t⁻¹ * y * t) * t) * t
          = h * (h * (h * y * h⁻¹) * h⁻¹) * h⁻¹ := by
            rw [hy1 y hy, hy1 _ m1, hy1 _ m2]
        _ = (h * h * h) * y * (h * h * h)⁻¹ := by group
        _ = y := by rw [hC₁3 h hhC]; group
    calc (t * t * t) * y = (t * t * t) * (t⁻¹ * (t⁻¹ * (t⁻¹ * y * t) * t) * t) := by rw [key]
      _ = y * (t * t * t) := by group
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hT2 ht
  have htcomm : ∀ y ∈ Tb, Commute t y := fun y hy =>
    commute_of_pow (m := 3) (by rw [pow_three']; exact ht3 y hy)
      (by rw [hk]; exact Nat.Coprime.pow_right k (by norm_num))
  have hhcent : ∀ y ∈ Tb, h * y = y * h := by
    intro y hy
    have e : h * y * h⁻¹ = y := by
      rw [hy1 y hy]
      have := (htcomm y hy).eq
      calc t⁻¹ * y * t = t⁻¹ * (y * t) := by group
        _ = t⁻¹ * (t * y) := by rw [← this]
        _ = y := by group
    calc h * y = (h * y * h⁻¹) * h := by group
      _ = y * h := by rw [e]
  by_cases h1 : h = 1
  · rw [h1, mul_one]; exact ht
  · exfalso
    have hgen := mem_zpowers_of_prime_card (p := 3) hc3
      (g := (⟨h, hhC⟩ : ↥(centralizer (Ub : Set Gt) ⊓ Hh)))
      (g' := (⟨h', hh'C⟩ : ↥(centralizer (Ub : Set Gt) ⊓ Hh)))
      (fun hh => h1 (congrArg Subtype.val hh))
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgen
    have hj' : h ^ j = h' := congrArg Subtype.val hj
    have hh'cent : ∀ y ∈ Tb, h' * y = y * h' := by
      intro y hy
      rw [← hj']
      exact ((show Commute h y from hhcent y hy).zpow_left j).eq
    have hbact : ∀ y ∈ Tb, b * y * b⁻¹ = t' * y * t'⁻¹ := by
      intro y hy
      rw [hbeq]
      calc t' * h' * y * (t' * h')⁻¹ = t' * (h' * y) * h'⁻¹ * t'⁻¹ := by group
        _ = t' * (y * h') * h'⁻¹ * t'⁻¹ := by rw [hh'cent y hy]
        _ = t' * y * t'⁻¹ := by group
    have hit : ∀ i : ℕ, ∀ y ∈ Tb, b ^ i * y * (b ^ i)⁻¹ = t' ^ i * y * (t' ^ i)⁻¹ := by
      intro i
      induction i with
      | zero => intro y hy; simp
      | succ i ih =>
        intro y hy
        have hmem : t' ^ i * y * (t' ^ i)⁻¹ ∈ Tb :=
          Tb.mul_mem (Tb.mul_mem (Tb.pow_mem ht' i) hy) (Tb.inv_mem (Tb.pow_mem ht' i))
        calc b ^ (i + 1) * y * (b ^ (i + 1))⁻¹ = b * (b ^ i * y * (b ^ i)⁻¹) * b⁻¹ := by group
          _ = b * (t' ^ i * y * (t' ^ i)⁻¹) * b⁻¹ := by rw [ih y hy]
          _ = t' * (t' ^ i * y * (t' ^ i)⁻¹) * t'⁻¹ := hbact _ hmem
          _ = t' ^ (i + 1) * y * (t' ^ (i + 1))⁻¹ := by group
    have ht'comm : ∀ y ∈ Tb, Commute t' y := by
      intro y hy
      have h1 := hit (orderOf b) y hy
      rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h1
      have h2 : Commute (t' ^ orderOf b) y := by
        show t' ^ orderOf b * y = y * t' ^ orderOf b
        calc t' ^ orderOf b * y
            = (t' ^ orderOf b * y * (t' ^ orderOf b)⁻¹) * t' ^ orderOf b := by group
          _ = y * t' ^ orderOf b := by rw [← h1]
      exact commute_of_pow h2
        (by rw [hk']; exact Nat.Coprime.pow_right k' (Nat.coprime_two_right.2 hbodd))
    obtain ⟨y, hy, hne⟩ := hbT
    apply hne
    rw [hbact y hy]
    have := (ht'comm y hy).eq
    calc t' * y * t'⁻¹ = (t' * y) * t'⁻¹ := rfl
      _ = (y * t') * t'⁻¹ := by rw [this]
      _ = y := by group

end CFSG.GH74.Uniqueness.SU.SU7.Gen
