module

public import CFSG.CGT.Stroth77.Section223Frame

public section

namespace CFSG.CGT.Stroth77.S223

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hmap : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  have hEq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

theorem mem_sup_zpowers_iff {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hsq : a * a ∈ K) {b : G} :
    b ∈ K ⊔ Subgroup.zpowers a ↔ b ∈ K ∨ ∃ k ∈ K, b = k * a := by
  constructor
  · intro hb
    have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.zpowers_le]
      exact ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K _ hle] at hb
    obtain ⟨k, hk, y, hy, rfl⟩ := hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h2 : a ^ (2 : ℤ) ∈ K := by rw [zpow_two]; exact hsq
    have hj : a ^ j = (a ^ (2 : ℤ)) ^ (j / 2) * a ^ (j % 2) := by
      rw [← zpow_mul, ← zpow_add]
      congr 1
      omega
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left
      rw [hj, h0, zpow_zero, mul_one]
      exact mul_mem hk (zpow_mem h2 _)
    · right
      refine ⟨k * (a ^ (2 : ℤ)) ^ (j / 2), mul_mem hk (zpow_mem h2 _), ?_⟩
      rw [hj, h1, zpow_one, mul_assoc]
  · rintro (hb | ⟨k, hk, rfl⟩)
    · exact Subgroup.mem_sup_left hb
    · exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))

theorem card_sup_zpowers_two [Finite G] {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hsq : a * a ∈ K) (haK : a ∉ K) :
    Nat.card (K ⊔ Subgroup.zpowers a : Subgroup G) = 2 * Nat.card K := by
  have h2 : K.relIndex (K ⊔ Subgroup.zpowers a) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a), fun b hb => ?_⟩
    rcases (mem_sup_zpowers_iff ha hsq).1 hb with hbK | ⟨k, hk, rfl⟩
    · refine Or.inr ⟨hbK, fun hba => haK ?_⟩
      have := mul_mem (inv_mem hbK) hba
      simpa using this
    · refine Or.inl ⟨?_, fun hka => haK ?_⟩
      · rw [mul_assoc]
        exact mul_mem hk hsq
      · have := mul_mem (inv_mem hk) hka
        simpa using this
  have h3 := Subgroup.relIndex_mul_card (H := K) (K := K ⊔ Subgroup.zpowers a)
  rw [h2, inf_eq_left.2 le_sup_left] at h3
  exact h3.symm

theorem exists_mem_sq_comm_mem [Finite G] {P B N : Subgroup G} (hP : IsPGroup 2 P)
    (hBN : B < N) (hNP : N ≤ P) (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) :
    ∃ d ∈ N, d ∉ B ∧ d * d ∈ B ∧ ∀ x ∈ P, d⁻¹ * x⁻¹ * d * x ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBP : B ≤ P := hBN.le.trans hNP
  have hB'n : (B.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPB
  have hN'n : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hQ : IsPGroup 2 (P ⧸ B.subgroupOf P) := hP.to_quotient _
  have hQnil : Group.IsNilpotent (P ⧸ B.subgroupOf P) := hQ.isNilpotent
  set N' := (N.subgroupOf P).map (QuotientGroup.mk' (B.subgroupOf P)) with hN'
  have hN'nn : N'.Normal := hN'n.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hnN, hnB⟩ := SetLike.exists_of_lt hBN
  have hN'ne : N' ≠ ⊥ := by
    intro h
    have hmem : (QuotientGroup.mk' (B.subgroupOf P) ⟨n, hNP hnN⟩) ∈ N' :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnN)
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hnB hmem
  set H := N' ⊓ Subgroup.center (P ⧸ B.subgroupOf P) with hH
  have hHne : H ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  have hHp : IsPGroup 2 H := hQ.to_subgroup H
  have hHnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne
  obtain ⟨k, hk⟩ := hHp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.card H = 1 := by rw [hk, pow_zero]
    exact (Finite.one_lt_card_iff_nontrivial.mpr hHnt).ne' h1
  have h2 : 2 ∣ Nat.card H := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨⟨y, hy⟩, hy2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy2' : orderOf y = 2 := by
    rw [← hy2]
    exact Subgroup.orderOf_coe ⟨y, hy⟩
  obtain ⟨hyN, hyZ⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨d, hdN, rfl⟩ := Subgroup.mem_map.mp hyN
  refine ⟨d, Subgroup.mem_subgroupOf.mp hdN, ?_, ?_, ?_⟩
  · intro hdB
    have h1 : QuotientGroup.mk' (B.subgroupOf P) d = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hdB
    rw [h1, orderOf_one] at hy2'
    exact absurd hy2' (by norm_num)
  · have h1 : QuotientGroup.mk' (B.subgroupOf P) (d * d) = 1 := by
      rw [map_mul, ← pow_two, ← hy2', pow_orderOf_eq_one]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro x hx
    have hc := Subgroup.mem_center_iff.mp hyZ (QuotientGroup.mk' (B.subgroupOf P) ⟨x, hx⟩)
    have hcomm : ∀ (a b : P ⧸ B.subgroupOf P), a * b = b * a → a⁻¹ * b⁻¹ * a * b = 1 := by
      intro a b hab
      calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (a * b) := by group
        _ = a⁻¹ * b⁻¹ * (b * a) := by rw [hab]
        _ = 1 := by group
    have h1 : QuotientGroup.mk' (B.subgroupOf P) (d⁻¹ * ⟨x, hx⟩⁻¹ * d * ⟨x, hx⟩) = 1 := by
      simp only [map_mul, map_inv]
      exact hcomm _ _ hc.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1

@[expose] noncomputable def sylowEquiv [Finite G] (X : Subgroup G) :
    {Q : Subgroup G // IsSylowIn 2 X Q} ≃ Sylow 2 X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  { toFun := fun Q => IsPGroup.toSylow (P := Q.1.subgroupOf X)
      (Q.2.2.1.comap_of_injective X.subtype Subtype.val_injective |>.to_le le_rfl)
      Q.2.2.2
    invFun := fun P => ⟨(P : Subgroup X).map X.subtype,
      ⟨Subgroup.map_subtype_le _, P.2.map _, by
        rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
        exact P.not_dvd_index⟩⟩
    left_inv := fun Q => Subtype.ext (by
      change (Q.1.subgroupOf X).map X.subtype = Q.1
      exact Subgroup.map_subgroupOf_eq_of_le Q.2.1)
    right_inv := fun P => Sylow.ext (by
      change ((P : Subgroup X).map X.subtype).subgroupOf X = P
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]) }

theorem coe_sylowEquiv [Finite G] (X : Subgroup G) (Q : {Q : Subgroup G // IsSylowIn 2 X Q}) :
    ((sylowEquiv X Q : Sylow 2 X) : Subgroup X) = Q.1.subgroupOf X := rfl

theorem odd_card_isSylowIn [Finite G] (X : Subgroup G) :
    Odd (Nat.card {Q : Subgroup G // IsSylowIn 2 X Q}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_congr (sylowEquiv X), Nat.odd_iff]
  exact card_sylow_modEq_one 2 X

theorem exists_conj_of_isSylowIn [Finite G] {X Q₁ Q₂ : Subgroup G} (h₁ : IsSylowIn 2 X Q₁)
    (h₂ : IsSylowIn 2 X Q₂) : ∃ x ∈ X, ∀ y : G, y ∈ Q₂ ↔ x⁻¹ * y * x ∈ Q₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X (sylowEquiv X ⟨Q₁, h₁⟩) (sylowEquiv X ⟨Q₂, h₂⟩)
  refine ⟨k, k.2, fun y => ?_⟩
  have hQ₂ : Q₂ = ((sylowEquiv X).symm (sylowEquiv X ⟨Q₂, h₂⟩)).1 := by
    rw [Equiv.symm_apply_apply]
  constructor
  · intro hy
    have hyX : y ∈ X := h₂.1 hy
    have hmem : (⟨y, hyX⟩ : X) ∈ ((sylowEquiv X ⟨Q₂, h₂⟩ : Sylow 2 X) : Subgroup X) :=
      Subgroup.mem_subgroupOf.mpr hy
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, coe_sylowEquiv, Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  · intro hy
    have hyX : y ∈ X := by
      have := mul_mem (mul_mem k.2 (h₁.1 hy)) (inv_mem k.2)
      simpa [mul_assoc] using this
    have hmem : (⟨y, hyX⟩ : X) ∈ ((sylowEquiv X ⟨Q₂, h₂⟩ : Sylow 2 X) : Subgroup X) := by
      rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply, coe_sylowEquiv, Subgroup.mem_subgroupOf]
      simpa using hy
    rw [coe_sylowEquiv, Subgroup.mem_subgroupOf] at hmem
    exact hmem

theorem card_eq_of_isSylowIn [Finite G] {X Q₁ Q₂ : Subgroup G} (h₁ : IsSylowIn 2 X Q₁)
    (h₂ : IsSylowIn 2 X Q₂) : Nat.card Q₂ = Nat.card Q₁ := by
  obtain ⟨x, -, hx⟩ := exists_conj_of_isSylowIn h₁ h₂
  have hQ : Q₂ = Q₁.map (MulAut.conj x).toMonoidHom := by
    ext y
    rw [hx y, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨x⁻¹ * y * x, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
  rw [hQ, Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem exists_fixed_of_involutive {α : Type*} [Finite α] (f : α → α)
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Function.End α := f
  have hf2 : F ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext a
    exact hf a
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf2
  by_contra hno
  have hfix : Fintype.card (Function.fixedPoints F) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨a, ha⟩ => hno ⟨a, ha⟩⟩
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  rw [Nat.odd_iff] at hodd
  rw [Nat.ModEq, Nat.zero_mod, hodd] at hmod
  exact absurd hmod (by norm_num)

theorem two_pow_eq_of_mul_odd {a b o₁ o₂ : ℕ} (h : 2 ^ a * o₁ = 2 ^ b * o₂) (h₁ : Odd o₁)
    (h₂ : Odd o₂) : a = b := by
  have key : ∀ {a b o₁ o₂ : ℕ}, 2 ^ a * o₁ = 2 ^ b * o₂ → Odd o₁ → a < b → False := by
    intro a b o₁ o₂ h h₁ hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    rw [show a + c + 1 = a + (c + 1) by ring, pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [h', pow_succ, mul_assoc] at h₁
    exact Nat.not_odd_iff_even.mpr ((even_two_mul _).mul_left _) h₁
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key h h₁ hab).elim
  · exact hab
  · exact (key h.symm h₂ hab).elim

theorem exists_mul_eq_of_isSylowIn [Finite G] {X Q O : Subgroup G} (hQ : IsSylowIn 2 X Q)
    (hOX : O ≤ X) (hXO : X ≤ Subgroup.normalizer (O : Set G)) (hOodd : Odd (Nat.card O))
    (hpow : ∀ x ∈ X, ∃ n : ℕ, x ^ (2 ^ n) ∈ O) :
    ∀ x ∈ X, ∃ q ∈ Q, ∃ o ∈ O, x = q * o := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (O.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr hXO
  have hquot : IsPGroup 2 (X ⧸ O.subgroupOf X) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨n, hxn⟩ := hpow x x.2
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hxn
  obtain ⟨b, hb⟩ := hquot.exists_card_eq
  obtain ⟨a, ha⟩ := hQ.2.1.exists_card_eq
  have hOc : Nat.card (O.subgroupOf X) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX).toEquiv
  have hQc : Nat.card (Q.subgroupOf X) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.1).toEquiv
  have hXcard : Nat.card X = 2 ^ b * Nat.card O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf X), hb, hOc]
  have hXcard' : Nat.card X = Q.relIndex X * 2 ^ a := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := X)
    rw [inf_of_le_left hQ.1, ha] at h
    exact h.symm
  have hodd2 : Odd (Q.relIndex X) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hQ.2.2)
  have hab : a = b := by
    have e : 2 ^ a * Q.relIndex X = 2 ^ b * Nat.card O := by rw [mul_comm, ← hXcard', hXcard]
    exact two_pow_eq_of_mul_odd e hodd2 hOodd
  have hc1 : Nat.card (Q.subgroupOf X) * Nat.card (O.subgroupOf X) = Nat.card X := by
    rw [hQc, hOc, ha, hab, hXcard]
  have hc2 : Nat.Coprime (Nat.card (Q.subgroupOf X)) (Nat.card (O.subgroupOf X)) := by
    rw [hQc, hOc, ha]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hOodd)
  have hcompl := Subgroup.isComplement'_of_coprime hc1 hc2
  intro x hx
  obtain ⟨⟨q, o⟩, hqo⟩ := hcompl.existsUnique ⟨x, hx⟩ |>.exists
  refine ⟨q.1, Subgroup.mem_subgroupOf.mp q.2, o.1, Subgroup.mem_subgroupOf.mp o.2, ?_⟩
  have := congrArg Subtype.val hqo
  simpa using this.symm

theorem isSylowIn_of_card_eq [Finite G] {X Q P : Subgroup G} (hQ : IsSylowIn 2 X Q)
    (hPX : P ≤ X) (hP : IsPGroup 2 P) (hcard : Nat.card P = Nat.card Q) : IsSylowIn 2 X P := by
  refine ⟨hPX, hP, fun h => hQ.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := P) (K := X)
  have h2 := Subgroup.relIndex_mul_card (H := Q) (K := X)
  rw [inf_of_le_left hPX] at h1
  rw [inf_of_le_left hQ.1] at h2
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have heq : P.relIndex X = Q.relIndex X := by
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  rwa [← heq]

theorem le_of_isSylowIn [Finite G] {X Q P : Subgroup G} (hQ : IsSylowIn 2 X Q) (hQP : Q ≤ P)
    (hPX : P ≤ X) (hP : IsPGroup 2 P) : P ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.relIndex_eq_one]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : Q.relIndex P ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card Q P
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rcases k with _ | k
  · simpa using hk
  · exfalso
    apply hQ.2.2
    rw [← Subgroup.relIndex_mul_relIndex Q P X hQP hPX, hk, pow_succ]
    exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

theorem card_le_of_isSylowIn [Finite G] {X Q P : Subgroup G} (hQ : IsSylowIn 2 X Q)
    (hPX : P ≤ X) (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card Q := by
  obtain ⟨Q', hQ', hPQ'⟩ := exists_isSylowIn_ge hPX hP
  rw [← card_eq_of_isSylowIn hQ hQ']
  exact Subgroup.card_le_of_le hPQ'

theorem odd_card_fixed_of_involutive {α : Type*} [Finite α] (f : α → α)
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : Odd (Nat.card {a // f a = a}) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Function.End α := f
  have hf2 : F ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext a
    exact hf a
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf2
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  rw [Nat.odd_iff] at hodd ⊢
  have e : Nat.card (Function.fixedPoints F) = Nat.card {a // f a = a} := rfl
  rw [← e, ← hodd]
  exact hmod.symm

theorem mem_map_conj {Q : Subgroup G} {g y : G} :
    y ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ Q := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem isSylowIn_map_conj [Finite G] {X Q : Subgroup G} (hQ : IsSylowIn 2 X Q) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    IsSylowIn 2 X (Q.map (MulAut.conj g).toMonoidHom) := by
  refine isSylowIn_of_card_eq hQ ?_ (hQ.2.1.map _)
    (Subgroup.card_map_of_injective (MulAut.conj g).injective)
  intro y hy
  rw [mem_map_conj] at hy
  have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hg) _).mp (hQ.1 hy)
  simpa [mul_assoc] using this

theorem exists_isSylowIn_mem_normalizer [Finite G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hg2 : g * g = 1) :
    ∃ Q : Subgroup G, IsSylowIn 2 X Q ∧ g ∈ Subgroup.normalizer (Q : Set G) := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let f : {Q : Subgroup G // IsSylowIn 2 X Q} → {Q : Subgroup G // IsSylowIn 2 X Q} :=
    fun Q => ⟨Q.1.map (MulAut.conj g).toMonoidHom, isSylowIn_map_conj Q.2 hg⟩
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hf : Function.Involutive f := by
    intro Q
    apply Subtype.ext
    change (Q.1.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = Q.1
    ext y
    rw [mem_map_conj, mem_map_conj, hginv]
    rw [show g * (g * y * g) * g = (g * g) * y * (g * g) by group, hg2, one_mul, mul_one]
  obtain ⟨Q, hQ⟩ := exists_fixed_of_involutive f hf (odd_card_isSylowIn X)
  refine ⟨Q.1, Q.2, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  exact congrArg Subtype.val hQ

theorem exists_isSylowIn_mem_normalizer₂ [Finite G] {X : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hg2 : g * g = 1)
    (hh : h ∈ Subgroup.normalizer (X : Set G)) (hh2 : h * h = 1) (hgh : g * h = h * g) :
    ∃ Q : Subgroup G, IsSylowIn 2 X Q ∧ g ∈ Subgroup.normalizer (Q : Set G) ∧
      h ∈ Subgroup.normalizer (Q : Set G) := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let f : {Q : Subgroup G // IsSylowIn 2 X Q} → {Q : Subgroup G // IsSylowIn 2 X Q} :=
    fun Q => ⟨Q.1.map (MulAut.conj g).toMonoidHom, isSylowIn_map_conj Q.2 hg⟩
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh2
  have hf : Function.Involutive f := by
    intro Q
    apply Subtype.ext
    change (Q.1.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = Q.1
    ext y
    rw [mem_map_conj, mem_map_conj, hginv]
    rw [show g * (g * y * g) * g = (g * g) * y * (g * g) by group, hg2, one_mul, mul_one]
  have hodd := odd_card_fixed_of_involutive f hf (odd_card_isSylowIn X)
  let f' : {Q // f Q = Q} → {Q // f Q = Q} := fun Q =>
    ⟨⟨Q.1.1.map (MulAut.conj h).toMonoidHom, isSylowIn_map_conj Q.1.2 hh⟩, by
      apply Subtype.ext
      change (Q.1.1.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        Q.1.1.map (MulAut.conj h).toMonoidHom
      have hQ : Q.1.1.map (MulAut.conj g).toMonoidHom = Q.1.1 := congrArg Subtype.val Q.2
      have hQg : ∀ z : G, z ∈ Q.1.1 ↔ g⁻¹ * z * g ∈ Q.1.1 := fun z => by
        conv_lhs => rw [← hQ]
        exact mem_map_conj
      ext y
      rw [mem_map_conj, mem_map_conj, mem_map_conj]
      have e2 : h⁻¹ * (g⁻¹ * y * g) * h = g⁻¹ * (h⁻¹ * y * h) * g := by
        rw [hginv, hhinv]
        calc h * (g * y * g) * h = (h * g) * y * (g * h) := by group
          _ = (g * h) * y * (h * g) := by rw [hgh]
          _ = g * (h * y * h) * g := by group
      rw [e2, ← hQg]⟩
  have hf' : Function.Involutive f' := by
    intro Q
    apply Subtype.ext
    apply Subtype.ext
    change (Q.1.1.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h).toMonoidHom = Q.1.1
    ext y
    rw [mem_map_conj, mem_map_conj, hhinv]
    rw [show h * (h * y * h) * h = (h * h) * y * (h * h) by group, hh2, one_mul, mul_one]
  obtain ⟨Q, hQ⟩ := exists_fixed_of_involutive f' hf' hodd
  refine ⟨Q.1.1, Q.1.2, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  · exact congrArg Subtype.val Q.2
  · exact congrArg (fun Q : {Q // f Q = Q} => Q.1.1) hQ

end CFSG.CGT.Stroth77.S223
