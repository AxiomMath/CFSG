module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type*} [Group G]

theorem conj_mem_of_normal_subgroupOf {M D₀ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) {m x : G} (hm : m ∈ M) (hx : x ∈ D₀) :
    m * x * m⁻¹ ∈ D₀ := by
  have h := hD₀n.conj_mem (⟨x, hD₀M hx⟩ : M) (Subgroup.mem_subgroupOf.mpr hx) ⟨m, hm⟩
  simpa [Subgroup.mem_subgroupOf] using h

theorem pow_card_eq_one_of_mem [Finite G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ^ Nat.card H = 1 := by
  have h : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h

theorem exists_mul_mem_of_mem_sup {M D₀ P₀ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) {n : G} (hn : n ∈ P₀ ⊔ D₀) :
    ∃ d ∈ D₀, ∃ p ∈ P₀, n = d * p := by
  let S : Subgroup G :=
    { carrier := {x | ∃ d ∈ D₀, ∃ p ∈ P₀, x = d * p}
      mul_mem' := by
        rintro _ _ ⟨d₁, hd₁, p₁, hp₁, rfl⟩ ⟨d₂, hd₂, p₂, hp₂, rfl⟩
        refine ⟨d₁ * (p₁ * d₂ * p₁⁻¹), D₀.mul_mem hd₁ (conj_mem_of_normal_subgroupOf hD₀M hD₀n
          (hP₀M hp₁) hd₂), p₁ * p₂, P₀.mul_mem hp₁ hp₂, ?_⟩
        group
      one_mem' := ⟨1, D₀.one_mem, 1, P₀.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨d, hd, p, hp, rfl⟩
        refine ⟨p⁻¹ * d⁻¹ * p * 1, ?_, p⁻¹, P₀.inv_mem hp, ?_⟩
        · simpa using conj_mem_of_normal_subgroupOf hD₀M hD₀n (M.inv_mem (hP₀M hp))
            (D₀.inv_mem hd)
        · group }
  have hS : P₀ ⊔ D₀ ≤ S := by
    refine sup_le (fun p hp => ⟨1, D₀.one_mem, p, hp, by group⟩) (fun d hd => ⟨d, hd, 1,
      P₀.one_mem, by group⟩)
  exact hS hn

theorem mem_of_pow_two_pow_eq_one_of_mem_sup {M D₀ P₀ : Subgroup G} [Finite G]
    (hD₀M : D₀ ≤ M) (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M)
    (hP₀ : Nat.card P₀ = 3) {n : G} (hn : n ∈ P₀ ⊔ D₀) {k : ℕ} (hk : n ^ 2 ^ k = 1) :
    n ∈ D₀ := by
  obtain ⟨d, hd, p, hp, rfl⟩ := exists_mul_mem_of_mem_sup hD₀M hD₀n hP₀M hn
  have hNM : P₀ ⊔ D₀ ≤ M := sup_le hP₀M hD₀M
  have hp3 : p ^ 3 = 1 := by
    have h : (⟨p, hp⟩ : P₀) ^ 3 = 1 := by
      rw [← hP₀]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val h
  have : (D₀.subgroupOf (P₀ ⊔ D₀)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_of_normal_subgroupOf hD₀M hD₀n (hNM g.2) hx
  set x : ↥(P₀ ⊔ D₀) := ⟨d * p, hn⟩ with hxdef
  set y : ↥(P₀ ⊔ D₀) := ⟨p, (le_sup_left : P₀ ≤ P₀ ⊔ D₀) hp⟩ with hydef
  have hxk : x ^ 2 ^ k = 1 := Subtype.ext hk
  set q : ↥(P₀ ⊔ D₀) ⧸ (D₀.subgroupOf (P₀ ⊔ D₀)) := QuotientGroup.mk x with hqdef
  have hq1 : q ^ 2 ^ k = 1 := by
    rw [hqdef, ← QuotientGroup.mk_pow, hxk]
    rfl
  have hqy : q = QuotientGroup.mk y := by
    rw [hqdef, QuotientGroup.eq]
    have hmem : (x⁻¹ * y : ↥(P₀ ⊔ D₀)) ∈ D₀.subgroupOf (P₀ ⊔ D₀) := by
      rw [Subgroup.mem_subgroupOf]
      have hc := conj_mem_of_normal_subgroupOf hD₀M hD₀n (M.inv_mem (hP₀M hp)) (D₀.inv_mem hd)
      have heq : ((x⁻¹ * y : ↥(P₀ ⊔ D₀)) : G) = p⁻¹ * d⁻¹ * p⁻¹⁻¹ := by
        show (d * p)⁻¹ * p = p⁻¹ * d⁻¹ * p⁻¹⁻¹
        group
      rw [heq]
      exact hc
    exact hmem
  have hq3 : q ^ 3 = 1 := by
    rw [hqy, ← QuotientGroup.mk_pow]
    have : y ^ 3 = 1 := Subtype.ext (by simpa using hp3)
    rw [this]
    rfl
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hq1
  have h2 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hone : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num)) h1 h2
  have hq : q = 1 := orderOf_eq_one_iff.mp hone
  have hxK : x ∈ D₀.subgroupOf (P₀ ⊔ D₀) := (QuotientGroup.eq_one_iff x).mp hq
  exact Subgroup.mem_subgroupOf.mp hxK

theorem normal_subgroupOf_sup {M D₀ P₀ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) :
    (D₀.subgroupOf (P₀ ⊔ D₀)).Normal := by
  have hNM : P₀ ⊔ D₀ ≤ M := sup_le hP₀M hD₀M
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simpa using conj_mem_of_normal_subgroupOf hD₀M hD₀n (hNM g.2) hx

theorem relIndex_sup_eq_three [Finite G] {M D₀ P₀ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) :
    D₀.relIndex (P₀ ⊔ D₀) = 3 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hP₀]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : P₀ => (QuotientGroup.mk ⟨p, (le_sup_left : P₀ ≤ P₀ ⊔ D₀) p.2⟩ :
      ↥(P₀ ⊔ D₀) ⧸ (D₀.subgroupOf (P₀ ⊔ D₀)))) ⟨?_, ?_⟩)).symm
  ·
    rintro ⟨p, hp⟩ ⟨p', hp'⟩ hpp
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hpp
    have hx : p⁻¹ * p' ∈ D₀ := by simpa using hpp
    have hxP : p⁻¹ * p' ∈ P₀ := P₀.mul_mem (P₀.inv_mem hp) hp'
    have h3 : (p⁻¹ * p') ^ 3 = 1 := by
      rw [← hP₀]
      exact pow_card_eq_one_of_mem hxP
    have hD : (p⁻¹ * p') ^ Nat.card D₀ = 1 := pow_card_eq_one_of_mem hx
    have hone : orderOf (p⁻¹ * p') = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
        (orderOf_dvd_of_pow_eq_one hD)
    have hxone : p⁻¹ * p' = 1 := orderOf_eq_one_iff.mp hone
    exact Subtype.ext (inv_mul_eq_one.mp hxone)
  ·
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, hd, p, hp, hap⟩ := exists_mul_mem_of_mem_sup hD₀M hD₀n hP₀M a.2
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show p⁻¹ * (a : G) ∈ D₀
    rw [hap]
    have heq : p⁻¹ * (d * p) = p⁻¹ * d * p⁻¹⁻¹ := by group
    rw [heq]
    exact conj_mem_of_normal_subgroupOf hD₀M hD₀n (M.inv_mem (hP₀M hp)) hd

theorem card_sup_eq_three_mul [Finite G] {M D₀ P₀ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) :
    Nat.card (P₀ ⊔ D₀ : Subgroup G) = 3 * Nat.card D₀ := by
  have h := Subgroup.relIndex_mul_card (H := D₀) (K := P₀ ⊔ D₀)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_eq_three hD₀M hD₀n hP₀M hP₀ hcop] at h
  exact h.symm

theorem inf_eq_bot_of_isPGroup_two_of_card_three [Finite G] {R P : Subgroup G}
    (hR : IsPGroup 2 R) (hP : Nat.card P = 3) : R ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxP⟩
  obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one_of_mem (H := P) hxP
    rwa [hP] at h
  have hone : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num))
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

theorem exists_mul_of_inf_eq_bot_of_card_mul [Finite G] {A B Y : Subgroup G} (hA : A ≤ Y)
    (hB : B ≤ Y) (hAB : A ⊓ B = ⊥) (hcard : Nat.card A * Nat.card B = Nat.card Y)
    {y : G} (hy : y ∈ Y) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  let f : A × B → Y := fun p => ⟨p.1.1 * p.2.1, Y.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have inj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h' : a * b = a' * b' := congrArg Subtype.val h
    have hx : a'⁻¹ * a = b' * b⁻¹ := by
      rw [show a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ by group, h',
        show a'⁻¹ * (a' * b') * b⁻¹ = b' * b⁻¹ by group]
    have hmem : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha, by rw [hx]; exact B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    obtain rfl : a' = a := inv_mul_eq_one.mp hmem
    obtain rfl : b = b' := mul_left_cancel h'
    rfl
  have hf : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨inj, by rw [Nat.card_prod, hcard]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hf.2 ⟨y, hy⟩
  exact ⟨a.1, a.2, b.1, b.2, (congrArg Subtype.val hab).symm⟩

theorem isPGroup_two_subgroupOf {D₀ D₂ : Subgroup G} (hD₂p : IsPGroup 2 D₂) :
    IsPGroup 2 (D₂.subgroupOf D₀) := by
  intro g
  obtain ⟨k, hk⟩ := hD₂p ⟨(g : G), Subgroup.mem_subgroupOf.mp g.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

theorem exists_normalizer_frattini [Finite G] {N D₀ D₂ : Subgroup G} (hD₀N : D₀ ≤ N)
    (hD₀n : (D₀.subgroupOf N).Normal) (hD₂ : D₂ ≤ D₀) (hD₂p : IsPGroup 2 D₂)
    (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index) {n : G} (hn : n ∈ N) :
    ∃ d ∈ D₀, d⁻¹ * n ∈ Subgroup.normalizer (D₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := D₂.map (MulAut.conj n).toMonoidHom with hKdef
  have hKmem : ∀ z : G, z ∈ K ↔ n⁻¹ * z * n ∈ D₂ := by
    intro z
    rw [hKdef, Subgroup.mem_map_equiv]
    simp
  have hKD : K ≤ D₀ := by
    intro z hz
    have h := conj_mem_of_normal_subgroupOf hD₀N hD₀n hn (hD₂ ((hKmem z).mp hz))
    have e : n * (n⁻¹ * z * n) * n⁻¹ = z := by group
    rwa [e] at h
  have hKp : IsPGroup 2 K := hD₂p.map (MulAut.conj n).toMonoidHom
  have hcardK : Nat.card K = Nat.card D₂ := by
    rw [hKdef]
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hidx : (K.subgroupOf D₀).index = (D₂.subgroupOf D₀).index := by
    have h1 := Subgroup.index_mul_card (H := K.subgroupOf D₀)
    have h2 := Subgroup.index_mul_card (H := D₂.subgroupOf D₀)
    have c1 : Nat.card (K.subgroupOf D₀) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv
    have c2 : Nat.card (D₂.subgroupOf D₀) = Nat.card D₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₂).toEquiv
    rw [c1, hcardK] at h1
    rw [c2] at h2
    have hpos : 0 < Nat.card D₂ := Nat.card_pos
    have : (K.subgroupOf D₀).index * Nat.card D₂ = (D₂.subgroupOf D₀).index * Nat.card D₂ := by
      rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hKi : ¬ 2 ∣ (K.subgroupOf D₀).index := by rwa [hidx]
  let S : Sylow 2 D₀ := (isPGroup_two_subgroupOf hD₂p).toSylow hD₂i
  let T : Sylow 2 D₀ := (isPGroup_two_subgroupOf hKp).toSylow hKi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥D₀) S T
  have hS : ∀ x : ↥D₀, x ∈ (S : Subgroup D₀) ↔ (x : G) ∈ D₂ := fun x =>
    (IsPGroup.mem_toSylow _ _).trans Subgroup.mem_subgroupOf
  have hT : ∀ x : ↥D₀, x ∈ (T : Subgroup D₀) ↔ (x : G) ∈ K := fun x =>
    (IsPGroup.mem_toSylow _ _).trans Subgroup.mem_subgroupOf
  have hact : ∀ x : ↥D₀, (((MulAut.conj g)⁻¹ • x : ↥D₀) : G) = (g : G)⁻¹ * (x : G) * (g : G) :=
    fun x => rfl
  have hcore : ∀ z ∈ D₀, (g : G)⁻¹ * z * (g : G) ∈ D₂ ↔ z ∈ K := by
    intro z hz
    have h1 := hT ⟨z, hz⟩
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      hS, hact] at h1
    exact h1
  refine ⟨g, g.2, ?_⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  have hwconj : ((g : G)⁻¹ * n) * h * ((g : G)⁻¹ * n)⁻¹ = (g : G)⁻¹ * (n * h * n⁻¹) * (g : G) := by
    group
  rw [hwconj]
  constructor
  · intro hh
    have hh0 : h ∈ D₀ := hD₂ hh
    have hz0 : n * h * n⁻¹ ∈ D₀ := conj_mem_of_normal_subgroupOf hD₀N hD₀n hn hh0
    have hzK : n * h * n⁻¹ ∈ K := (hKmem _).mpr (by
      have e : n⁻¹ * (n * h * n⁻¹) * n = h := by group
      rw [e]; exact hh)
    exact (hcore _ hz0).mpr hzK
  · intro hu
    have hwN : n⁻¹ * (g : G) ∈ N := N.mul_mem (N.inv_mem hn) (hD₀N g.2)
    have hh0 : h ∈ D₀ := by
      have h1 := conj_mem_of_normal_subgroupOf hD₀N hD₀n hwN (hD₂ hu)
      have e : (n⁻¹ * (g : G)) * ((g : G)⁻¹ * (n * h * n⁻¹) * (g : G)) * (n⁻¹ * (g : G))⁻¹ = h := by
        group
      rwa [e] at h1
    have hz0 : n * h * n⁻¹ ∈ D₀ := conj_mem_of_normal_subgroupOf hD₀N hD₀n hn hh0
    have hzK := (hcore _ hz0).mp hu
    have h2 := (hKmem _).mp hzK
    have e : n⁻¹ * (n * h * n⁻¹) * n = h := by group
    rwa [e] at h2

open scoped Pointwise in
theorem set_mul_eq_mul_of_normalizes [Finite G] {R Q P : Subgroup G} (hR : IsPGroup 2 R)
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hPQ : P ≤ Q) (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3 * Nat.card ↥(R ⊓ Q)) :
    (P : Set G) * (R : Set G) = (R : Set G) * (P : Set G) := by
  have hRP : R ⊓ P = ⊥ := inf_eq_bot_of_isPGroup_two_of_card_three hR hP
  have hAB : (R ⊓ Q) ⊓ P = ⊥ := by
    rw [eq_bot_iff] at hRP ⊢
    intro x hx
    exact hRP ⟨hx.1.1, hx.2⟩
  have hRS : R ≤ R ⊔ Q := le_sup_left
  have hQS : Q ≤ R ⊔ Q := le_sup_right
  have hcard : Nat.card ↥(R ⊓ Q) * Nat.card P = Nat.card Q := by
    rw [hP, hQ, mul_comm]
  have key : ∀ y ∈ R ⊔ Q, ∃ r ∈ R, ∃ p ∈ P, y = r * p := by
    intro y hy
    have hy' : y ∈ (↑(R ⊔ Q) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R Q hRQ] at hy'
    obtain ⟨r, hr, q, hq, hyq⟩ := hy'
    obtain ⟨d, hd, p, hp, hqdp⟩ :=
      exists_mul_of_inf_eq_bot_of_card_mul inf_le_right hPQ hAB hcard hq
    refine ⟨r * d, R.mul_mem hr hd.1, p, hp, ?_⟩
    rw [← hyq, hqdp, mul_assoc]
  ext y
  constructor
  · rintro ⟨p, hp, r, hr, rfl⟩
    have hy : p * r ∈ R ⊔ Q :=
      (R ⊔ Q).mul_mem (hQS (hPQ hp)) (hRS hr)
    obtain ⟨r', hr', p', hp', hEq⟩ := key _ hy
    exact ⟨r', hr', p', hp', hEq.symm⟩
  · rintro ⟨r, hr, p, hp, rfl⟩
    have hy : (r * p)⁻¹ ∈ R ⊔ Q :=
      (R ⊔ Q).inv_mem ((R ⊔ Q).mul_mem (hRS hr) (hQS (hPQ hp)))
    obtain ⟨r', hr', p', hp', hEq⟩ := key _ hy
    refine ⟨p'⁻¹, P.inv_mem hp', r'⁻¹, R.inv_mem hr', ?_⟩
    show p'⁻¹ * r'⁻¹ = r * p
    rw [← mul_inv_rev, ← hEq, inv_inv]

theorem card_sup_mul_card_inf [Finite G] {A K : Subgroup G}
    (hK : (K.subgroupOf (A ⊔ K)).Normal) :
    Nat.card (A ⊔ K : Subgroup G) * Nat.card (A ⊓ K : Subgroup G) =
      Nat.card A * Nat.card K := by
  have hAL : A ≤ A ⊔ K := le_sup_left
  have hKL : K ≤ A ⊔ K := le_sup_right
  set L : Subgroup G := A ⊔ K with hLdef
  set A' : Subgroup L := A.subgroupOf L with hA'
  set K' : Subgroup L := K.subgroupOf L with hK'
  have : K'.Normal := hK
  have hsup : A' ⊔ K' = ⊤ := by
    rw [hA', hK', ← Subgroup.subgroupOf_sup hAL hKL, hLdef, Subgroup.subgroupOf_self]
  have key : K'.relIndex ⊤ = K'.relIndex A' := by
    rw [← hsup, Subgroup.relIndex_sup_right]
  have e1 : K'.index * Nat.card K' = Nat.card L := Subgroup.index_mul_card K'
  have e2 : K'.relIndex A' * Nat.card (K' ⊓ A' : Subgroup L) = Nat.card A' :=
    Subgroup.relIndex_mul_card K' A'
  have cK' : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have cA' : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have cI : Nat.card (K' ⊓ A' : Subgroup L) = Nat.card (A ⊓ K : Subgroup G) := by
    have hEq : K' ⊓ A' = (A ⊓ K : Subgroup G).subgroupOf L := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, hA', hK']
      exact and_comm
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans le_sup_left : A ⊓ K ≤ L)).toEquiv
  have hidx : K'.index = K'.relIndex A' := (Subgroup.relIndex_top_right K').symm.trans key
  have main : Nat.card L * Nat.card (K' ⊓ A' : Subgroup L) =
      Nat.card A' * Nat.card K' := by
    calc Nat.card L * Nat.card (K' ⊓ A' : Subgroup L)
        = (K'.index * Nat.card K') * Nat.card (K' ⊓ A' : Subgroup L) := by rw [e1]
      _ = (K'.relIndex A' * Nat.card (K' ⊓ A' : Subgroup L)) * Nat.card K' := by
          rw [hidx]; ring
      _ = Nat.card A' * Nat.card K' := by rw [e2]
  rw [cI, cA', cK'] at main
  exact main

def sigmaOf (P₀ D₀ D₂ : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (D₂ : Set G) ⊓ (P₀ ⊔ D₀)

theorem conj_mem_normalizer_set {S : Set G} {g x : G} (hg : g ∈ Subgroup.normalizer S)
    (hx : x ∈ Subgroup.normalizer S) : g * x * g⁻¹ ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff] at hg hx ⊢
  intro h
  have e1 := hg (x * (g⁻¹ * h * g) * x⁻¹)
  have e2 := hx (g⁻¹ * h * g)
  have e3 := hg (g⁻¹ * h * g)
  have q1 : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
  have q2 : g * x * g⁻¹ * h * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * h * g) * x⁻¹) * g⁻¹ := by
    group
  rw [q1] at e3
  rw [q2, ← e1, ← e2, e3]

theorem sup_sigmaOf_eq {M D₀ P₀ D₂ : Subgroup G} [Finite G] (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hD₂D₀ : D₂ ≤ D₀)
    (hD₂p : IsPGroup 2 D₂) (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index) :
    sigmaOf P₀ D₀ D₂ ⊔ D₀ = P₀ ⊔ D₀ := by
  apply le_antisymm
  · exact sup_le inf_le_right le_sup_right
  · intro n hn
    obtain ⟨d, hd, hdn⟩ := exists_normalizer_frattini (N := P₀ ⊔ D₀) le_sup_right
      (normal_subgroupOf_sup hD₀M hD₀n hP₀M) (hD₂D₀) hD₂p hD₂i hn
    have hD₀S : D₀ ≤ P₀ ⊔ D₀ := le_sup_right
    have hσS : sigmaOf P₀ D₀ D₂ ≤ sigmaOf P₀ D₀ D₂ ⊔ D₀ := le_sup_left
    have hD₀σ : D₀ ≤ sigmaOf P₀ D₀ D₂ ⊔ D₀ := le_sup_right
    have hs : d⁻¹ * n ∈ sigmaOf P₀ D₀ D₂ :=
      Subgroup.mem_inf.mpr ⟨hdn, (P₀ ⊔ D₀).mul_mem ((P₀ ⊔ D₀).inv_mem (hD₀S hd)) hn⟩
    have : n = d * (d⁻¹ * n) := by group
    rw [this]
    exact (sigmaOf P₀ D₀ D₂ ⊔ D₀).mul_mem (hD₀σ hd) (hσS hs)

theorem card_sigmaOf_eq [Finite G] {M D₀ P₀ D₂ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hD₂D₀ : D₂ ≤ D₀)
    (hD₂p : IsPGroup 2 D₂) (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index) :
    Nat.card (sigmaOf P₀ D₀ D₂) = 3 * Nat.card ↥(sigmaOf P₀ D₀ D₂ ⊓ D₀) := by
  have hsig := sup_sigmaOf_eq (M := M) hD₀M hD₀n hP₀M hD₂D₀ hD₂p hD₂i
  have hnorm : (D₀.subgroupOf (sigmaOf P₀ D₀ D₂ ⊔ D₀)).Normal := by
    rw [hsig]
    exact normal_subgroupOf_sup hD₀M hD₀n hP₀M
  have h := card_sup_mul_card_inf hnorm
  rw [hsig, card_sup_eq_three_mul hD₀M hD₀n hP₀M hP₀ hcop] at h
  have hpos : 0 < Nat.card D₀ := Nat.card_pos
  have key : Nat.card (sigmaOf P₀ D₀ D₂) * Nat.card D₀ =
      (3 * Nat.card ↥(sigmaOf P₀ D₀ D₂ ⊓ D₀)) * Nat.card D₀ := by
    rw [← h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem not_three_dvd_card_inf_of_coprime [Finite G] {D₀ S : Subgroup G}
    (hcop : Nat.Coprime 3 (Nat.card D₀)) : ¬ 3 ∣ Nat.card ↥(S ⊓ D₀) := by
  intro h
  have h1 : Nat.card ↥(S ⊓ D₀) ∣ Nat.card D₀ := Subgroup.card_dvd_of_le inf_le_right
  have h3 : 3 ∣ Nat.card D₀ := dvd_trans h h1
  have := Nat.Coprime.eq_one_of_dvd hcop h3
  omega

theorem normal_subgroupOf_of_le_normalizer_set {Y D : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (D : Set G)) : (D.subgroupOf Y).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hg : (g : G) ∈ Subgroup.normalizer (D : Set G) := hY g.2
  rw [Subgroup.mem_set_normalizer_iff] at hg
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (hg x).mp hx

theorem le_normalizer_set_self (D : Subgroup G) : D ≤ Subgroup.normalizer (D : Set G) := by
  intro x hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  exact ⟨fun hh => D.mul_mem (D.mul_mem hx hh) (D.inv_mem hx),
    fun hh => by simpa [mul_assoc] using D.mul_mem (D.mul_mem (D.inv_mem hx) hh) hx⟩

theorem card_sup_eq_three_mul_of_normalizes [Finite G] {σ D₂ P : Subgroup G}
    (hσ : σ ≤ Subgroup.normalizer (D₂ : Set G)) (hP : P ≤ σ) (hP3 : Nat.card P = 3)
    (hD₂p : IsPGroup 2 D₂) :
    Nat.card (P ⊔ D₂ : Subgroup G) = 3 * Nat.card D₂ := by
  have hPN : P ⊔ D₂ ≤ Subgroup.normalizer (D₂ : Set G) :=
    sup_le (hP.trans hσ) (le_normalizer_set_self D₂)
  have h := card_sup_mul_card_inf (normal_subgroupOf_of_le_normalizer_set hPN)
  rw [inf_comm, inf_eq_bot_of_isPGroup_two_of_card_three hD₂p hP3, Subgroup.card_bot, hP3]
    at h
  simpa using h

theorem exists_le_card_three_of_three_dvd [Finite G] {S : Subgroup G} (h3 : 3 ∣ Nat.card S) :
    ∃ P : Subgroup G, P ≤ S ∧ Nat.card P = 3 := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 3 (n := 1)
    (by rw [pow_one]; exact h3)
  refine ⟨K.map S.subtype, ?_, ?_⟩
  · rintro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK, pow_one]

theorem exists_mem_omega [Finite G] {M D₀ P₀ D₂ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hD₂D₀ : D₂ ≤ D₀)
    (hD₂p : IsPGroup 2 D₂) (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index) :
    ∃ Y : Subgroup G, Y ≤ sigmaOf P₀ D₀ D₂ ∧ D₂ ≤ Y ∧ (D₂.subgroupOf Y).Normal ∧
      Nat.card Y = 3 * Nat.card D₂ := by
  have hσeq := card_sigmaOf_eq (M := M) hD₀M hD₀n hP₀M hP₀ hcop hD₂D₀ hD₂p hD₂i
  have h3 : 3 ∣ Nat.card (sigmaOf P₀ D₀ D₂) := ⟨_, hσeq⟩
  obtain ⟨P, hPσ, hP3⟩ := exists_le_card_three_of_three_dvd h3
  have hσN : sigmaOf P₀ D₀ D₂ ≤ Subgroup.normalizer (D₂ : Set G) := inf_le_left
  have hD₂σ : D₂ ≤ sigmaOf P₀ D₀ D₂ :=
    le_inf (le_normalizer_set_self D₂) (hD₂D₀.trans le_sup_right)
  refine ⟨P ⊔ D₂, sup_le hPσ hD₂σ, le_sup_right, ?_, ?_⟩
  · exact normal_subgroupOf_of_le_normalizer_set
      (sup_le (hPσ.trans hσN) (le_normalizer_set_self D₂))
  · exact card_sup_eq_three_mul_of_normalizes hσN hPσ hP3 hD₂p

theorem inf_sup_eq_inf_of_isPGroup_two [Finite G] {M D₀ P₀ R : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hR : IsPGroup 2 R) :
    R ⊓ (P₀ ⊔ D₀) = R ⊓ D₀ := by
  have hNM : P₀ ⊔ D₀ ≤ M := sup_le hP₀M hD₀M
  set T : Subgroup G := R ⊓ (P₀ ⊔ D₀) with hT
  have hTN : T ≤ P₀ ⊔ D₀ := inf_le_right
  have hTM : T ≤ M := hTN.trans hNM
  have hnorm : (D₀.subgroupOf (T ⊔ D₀)).Normal := normal_subgroupOf_sup hD₀M hD₀n hTM
  have h1 := card_sup_mul_card_inf hnorm
  have hTD : T ⊓ D₀ = R ⊓ D₀ := by
    ext x
    simp only [hT, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxR, _⟩, hxD⟩
      exact ⟨hxR, hxD⟩
    · rintro ⟨hxR, hxD⟩
      have hD₀N : D₀ ≤ P₀ ⊔ D₀ := le_sup_right
      exact ⟨⟨hxR, hD₀N hxD⟩, hxD⟩
  rw [hTD] at h1
  have hpos : 0 < Nat.card D₀ := Nat.card_pos
  have hK : Nat.card ↥(T ⊔ D₀) ∣ 3 * Nat.card D₀ := by
    rw [← card_sup_eq_three_mul hD₀M hD₀n hP₀M hP₀ hcop]
    exact Subgroup.card_dvd_of_le (sup_le hTN le_sup_right)
  have hDK : Nat.card D₀ ∣ Nat.card ↥(T ⊔ D₀) := Subgroup.card_dvd_of_le le_sup_right
  obtain ⟨c, hc⟩ := hDK
  have hcdvd : c ∣ 3 := by
    have : Nat.card D₀ * c ∣ Nat.card D₀ * 3 := by
      rw [← hc, mul_comm]
      exact hK
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  have h3T : ¬ 3 ∣ Nat.card ↥T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    intro h3
    have hdvd : Nat.card ↥T ∣ Nat.card ↥R := Subgroup.card_dvd_of_le inf_le_left
    have h32 : 3 ∣ 2 ^ n := by
      rw [← hn]
      exact h3.trans hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    omega
  rcases (Nat.dvd_prime Nat.prime_three).mp hcdvd with hc1 | hc3
  ·
    rw [hc, hc1, mul_one] at h1
    have hcard : Nat.card ↥T * Nat.card D₀ = Nat.card ↥(R ⊓ D₀) * Nat.card D₀ := by
      rw [← h1]
      ring
    have hTc : Nat.card ↥T = Nat.card ↥(R ⊓ D₀) := Nat.eq_of_mul_eq_mul_right hpos hcard
    have hle : R ⊓ D₀ ≤ T := le_inf inf_le_left (inf_le_right.trans le_sup_right)
    exact (Subgroup.eq_of_le_of_card_ge hle hTc.le).symm
  ·
    rw [hc, hc3] at h1
    have hcard : Nat.card ↥T * Nat.card D₀ = (3 * Nat.card ↥(R ⊓ D₀)) * Nat.card D₀ := by
      rw [← h1]
      ring
    have hTc : Nat.card ↥T = 3 * Nat.card ↥(R ⊓ D₀) := Nat.eq_of_mul_eq_mul_right hpos hcard
    exact absurd ⟨_, hTc⟩ h3T

open scoped Pointwise in
theorem exists_conj_map_eq_of_card_three [Finite G] {σ P Q : Subgroup G} (hPσ : P ≤ σ)
    (hQσ : Q ≤ σ) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) {m : ℕ}
    (hσm : Nat.card σ = 3 * m) (hm : ¬ 3 ∣ m) :
    ∃ g ∈ σ, Subgroup.map (MulAut.conj g).toMonoidHom P = Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPc : Nat.card (P.subgroupOf σ) = 3 := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPσ).toEquiv
  have hQc : Nat.card (Q.subgroupOf σ) = 3 := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQσ).toEquiv
  have hPp : IsPGroup 3 (P.subgroupOf σ) := IsPGroup.of_card (n := 1) (by rw [hPc]; norm_num)
  have hQp : IsPGroup 3 (Q.subgroupOf σ) := IsPGroup.of_card (n := 1) (by rw [hQc]; norm_num)
  have hPi : ¬ 3 ∣ (P.subgroupOf σ).index := by
    have h := Subgroup.index_mul_card (H := P.subgroupOf σ)
    rw [hPc, hσm] at h
    have hidx : (P.subgroupOf σ).index = m := by omega
    rw [hidx]
    exact hm
  have hQi : ¬ 3 ∣ (Q.subgroupOf σ).index := by
    have h := Subgroup.index_mul_card (H := Q.subgroupOf σ)
    rw [hQc, hσm] at h
    have hidx : (Q.subgroupOf σ).index = m := by omega
    rw [hidx]
    exact hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq σ
    (hPp.toSylow hPi) (hQp.toSylow hQi)
  have hcoe : MulAut.conj g • (P.subgroupOf σ) = Q.subgroupOf σ := by
    have := congrArg (fun S : Sylow 3 σ => (S : Subgroup σ)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
  refine ⟨g, g.2, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyσ : (⟨y, hPσ hy⟩ : σ) ∈ P.subgroupOf σ := Subgroup.mem_subgroupOf.mpr hy
    have hmem : MulAut.conj g • (⟨y, hPσ hy⟩ : σ) ∈ MulAut.conj g • P.subgroupOf σ :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hyσ
    rw [hcoe, Subgroup.mem_subgroupOf] at hmem
    simpa [MulAut.smul_def] using hmem
  · intro hx
    have hxσ : (⟨x, hQσ hx⟩ : σ) ∈ Q.subgroupOf σ := Subgroup.mem_subgroupOf.mpr hx
    rw [← hcoe, Subgroup.mem_smul_pointwise_iff_exists] at hxσ
    obtain ⟨z, hz, hzx⟩ := hxσ
    refine ⟨z, Subgroup.mem_subgroupOf.mp hz, ?_⟩
    have := congrArg Subtype.val hzx
    simpa [MulAut.smul_def] using this

theorem map_conj_eq_of_mem_normalizer {D : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    Subgroup.map (MulAut.conj g).toMonoidHom D = D :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

theorem exists_conj_map_eq_of_mem_omega [Finite G] {M D₀ P₀ D₂ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hD₂D₀ : D₂ ≤ D₀)
    (hD₂p : IsPGroup 2 D₂) (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index)
    {Y Y' : Subgroup G}
    (hY : Y ≤ sigmaOf P₀ D₀ D₂) (hYD : D₂ ≤ Y) (hYn : (D₂.subgroupOf Y).Normal)
    (hYc : Nat.card Y = 3 * Nat.card D₂)
    (hY' : Y' ≤ sigmaOf P₀ D₀ D₂) (hY'D : D₂ ≤ Y') (hY'n : (D₂.subgroupOf Y').Normal)
    (hY'c : Nat.card Y' = 3 * Nat.card D₂) :
    ∃ g ∈ sigmaOf P₀ D₀ D₂, Subgroup.map (MulAut.conj g).toMonoidHom Y' = Y := by
  have hσeq := card_sigmaOf_eq (M := M) hD₀M hD₀n hP₀M hP₀ hcop hD₂D₀ hD₂p hD₂i
  have hm := not_three_dvd_card_inf_of_coprime (S := sigmaOf P₀ D₀ D₂) hcop
  obtain ⟨P, hPY, hP3⟩ := exists_le_card_three_of_three_dvd (S := Y) ⟨Nat.card ↥D₂, hYc⟩
  obtain ⟨P', hP'Y', hP'3⟩ :=
    exists_le_card_three_of_three_dvd (S := Y') ⟨Nat.card ↥D₂, hY'c⟩
  have hYN : Y ≤ Subgroup.normalizer (D₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYD).mp hYn
  have hY'N : Y' ≤ Subgroup.normalizer (D₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hY'D).mp hY'n
  have hPD : Nat.card ↥(P ⊔ D₂ : Subgroup G) = 3 * Nat.card D₂ :=
    card_sup_eq_three_mul_of_normalizes hYN hPY hP3 hD₂p
  have hP'D : Nat.card ↥(P' ⊔ D₂ : Subgroup G) = 3 * Nat.card D₂ :=
    card_sup_eq_three_mul_of_normalizes hY'N hP'Y' hP'3 hD₂p
  have hYeq : P ⊔ D₂ = Y :=
    Subgroup.eq_of_le_of_card_ge (sup_le hPY hYD)
      (le_of_eq (by rw [hPD, hYc]))
  have hY'eq : P' ⊔ D₂ = Y' :=
    Subgroup.eq_of_le_of_card_ge (sup_le hP'Y' hY'D)
      (le_of_eq (by rw [hP'D, hY'c]))
  have hPσ : P ≤ sigmaOf P₀ D₀ D₂ := hPY.trans hY
  have hP'σ : P' ≤ sigmaOf P₀ D₀ D₂ := hP'Y'.trans hY'
  have hσm : Nat.card (sigmaOf P₀ D₀ D₂) = 3 * Nat.card ↥(sigmaOf P₀ D₀ D₂ ⊓ D₀) := hσeq
  obtain ⟨g, hgσ, hgP⟩ := exists_conj_map_eq_of_card_three hP'σ hPσ hP'3 hP3 hσm hm
  refine ⟨g, hgσ, ?_⟩
  have hgN : g ∈ Subgroup.normalizer (D₂ : Set G) :=
    (Subgroup.mem_inf.mp hgσ).1
  have hDfix := map_conj_eq_of_mem_normalizer hgN
  rw [← hY'eq, ← hYeq, Subgroup.map_sup, hgP, hDfix]

theorem mem_normalizer_set_inf {A B : Subgroup G} {r : G}
    (hA : r ∈ Subgroup.normalizer (A : Set G)) (hB : r ∈ Subgroup.normalizer (B : Set G)) :
    r ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff] at hA hB ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hA h) (hB h)

theorem map_conj_le_sigmaOf {P₀ D₀ D₂ Y : Subgroup G} {h : G}
    (hN : ∀ y ∈ P₀ ⊔ D₀, h * y * h⁻¹ ∈ P₀ ⊔ D₀)
    (hh : h ∈ Subgroup.normalizer (D₂ : Set G))
    (hY : Y ≤ sigmaOf P₀ D₀ D₂) :
    Subgroup.map (MulAut.conj h).toMonoidHom Y ≤ sigmaOf P₀ D₀ D₂ := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ Subgroup.normalizer (D₂ : Set G) ⊓ (P₀ ⊔ D₀) := hY hy
  have hyN := Subgroup.mem_inf.mp hy'
  show h * y * h⁻¹ ∈ Subgroup.normalizer (D₂ : Set G) ⊓ (P₀ ⊔ D₀)
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh hyN.1) (inv_mem hh), hN y hyN.2⟩

theorem le_map_conj_of_mem_normalizer {D Y : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (hDY : D ≤ Y) :
    D ≤ Subgroup.map (MulAut.conj h).toMonoidHom Y := by
  intro d hd
  have hmem : d ∈ Subgroup.map (MulAut.conj h).toMonoidHom D := by
    rw [map_conj_eq_of_mem_normalizer hh]
    exact hd
  obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp hmem
  exact Subgroup.mem_map.mpr ⟨x, hDY hx, hxd⟩

theorem normal_subgroupOf_map_conj {D Y : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (hDY : D ≤ Y)
    (hYn : (D.subgroupOf Y).Normal) :
    (D.subgroupOf (Subgroup.map (MulAut.conj h).toMonoidHom Y)).Normal := by
  have hYN : Y ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).mp hYn
  have hDY' := le_map_conj_of_mem_normalizer hh hDY
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hDY').mpr ?_
  rintro _ ⟨y, hy, rfl⟩
  show h * y * h⁻¹ ∈ Subgroup.normalizer (D : Set G)
  exact mul_mem (mul_mem hh (hYN hy)) (inv_mem hh)

theorem card_map_conj {Y : Subgroup G} (h : G) :
    Nat.card ↥(Subgroup.map (MulAut.conj h).toMonoidHom Y) = Nat.card ↥Y :=
  Subgroup.card_map_of_injective (MulAut.conj h).injective

theorem orbit_ncard_dvd_index {H : Type*} [Group H] {X : Type*} [MulAction H X]
    (D : Subgroup H) {x : X} (hD : D ≤ MulAction.stabilizer H x) :
    (MulAction.orbit H x).ncard ∣ D.index := by
  have h := Subgroup.index_dvd_of_le hD
  rwa [MulAction.index_stabilizer] at h

theorem not_two_dvd_index_D2_sigma [Finite G] {M D₀ P₀ D₂ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hD₂D₀ : D₂ ≤ D₀)
    (hD₂p : IsPGroup 2 D₂) (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index) :
    ¬ 2 ∣ (D₂.subgroupOf (sigmaOf P₀ D₀ D₂)).index := by
  have hD₂σ : D₂ ≤ sigmaOf P₀ D₀ D₂ := by
    show D₂ ≤ Subgroup.normalizer (D₂ : Set G) ⊓ (P₀ ⊔ D₀)
    exact le_inf (le_normalizer_set_self D₂) (hD₂D₀.trans le_sup_right)
  have hD₂S : D₂ ≤ sigmaOf P₀ D₀ D₂ ⊓ D₀ := le_inf hD₂σ hD₂D₀
  have hσc := card_sigmaOf_eq (M := M) hD₀M hD₀n hP₀M hP₀ hcop hD₂D₀ hD₂p hD₂i
  have hDpos : 0 < Nat.card ↥D₂ := Nat.card_pos
  have hDσ : Nat.card ↥(D₂.subgroupOf (sigmaOf P₀ D₀ D₂)) = Nat.card ↥D₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₂σ).toEquiv
  have hidx : (D₂.subgroupOf (sigmaOf P₀ D₀ D₂)).index * Nat.card ↥D₂ =
      Nat.card ↥(sigmaOf P₀ D₀ D₂) := by
    rw [← hDσ]
    exact Subgroup.index_mul_card (H := D₂.subgroupOf (sigmaOf P₀ D₀ D₂))
  have hS : D₂.relIndex (sigmaOf P₀ D₀ D₂ ⊓ D₀) * Nat.card ↥D₂ =
      Nat.card ↥(sigmaOf P₀ D₀ D₂ ⊓ D₀) := by
    have := Subgroup.relIndex_mul_card D₂ (sigmaOf P₀ D₀ D₂ ⊓ D₀)
    rwa [inf_eq_left.mpr hD₂S] at this
  have hr : (D₂.subgroupOf (sigmaOf P₀ D₀ D₂)).index =
      3 * D₂.relIndex (sigmaOf P₀ D₀ D₂ ⊓ D₀) := by
    have h1 : (D₂.subgroupOf (sigmaOf P₀ D₀ D₂)).index * Nat.card ↥D₂ =
        (3 * D₂.relIndex (sigmaOf P₀ D₀ D₂ ⊓ D₀)) * Nat.card ↥D₂ := by
      rw [hidx, hσc, ← hS]
      ring
    exact Nat.eq_of_mul_eq_mul_right hDpos h1
  have hdvd : D₂.relIndex (sigmaOf P₀ D₀ D₂ ⊓ D₀) ∣ D₂.relIndex D₀ := by
    have := Subgroup.relIndex_mul_relIndex D₂ (sigmaOf P₀ D₀ D₂ ⊓ D₀) D₀ hD₂S
      (inf_le_right : sigmaOf P₀ D₀ D₂ ⊓ D₀ ≤ D₀)
    exact ⟨_, this.symm⟩
  intro h2
  rw [hr] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
  · norm_num at h3
  · exact hD₂i (h3.trans hdvd)

def omegaFam (P₀ D₀ D₂ : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ sigmaOf P₀ D₀ D₂ ∧ D₂ ≤ Y ∧ (D₂.subgroupOf Y).Normal ∧ Nat.card Y = 3 * Nat.card D₂}

open scoped Pointwise in
theorem conj_smul_eq_map (g : G) (Y : Subgroup G) :
    (MulAut.conj g : MulAut G) • Y = Subgroup.map (MulAut.conj g).toMonoidHom Y := by
  rw [Subgroup.pointwise_smul_def]
  rfl

open scoped Pointwise in
theorem not_two_dvd_card_omegaFam [Finite G] {M D₀ P₀ D₂ : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hD₂D₀ : D₂ ≤ D₀)
    (hD₂p : IsPGroup 2 D₂) (hD₂i : ¬ 2 ∣ (D₂.subgroupOf D₀).index)
    {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ omegaFam P₀ D₀ D₂) :
    ¬ 2 ∣ Nat.card ↥(omegaFam P₀ D₀ D₂) := by
  have hY₀' : Y₀ ≤ sigmaOf P₀ D₀ D₂ ∧ D₂ ≤ Y₀ ∧ (D₂.subgroupOf Y₀).Normal ∧
      Nat.card Y₀ = 3 * Nat.card D₂ := hY₀
  obtain ⟨hY₀σ, hD₂Y₀, hY₀n, hY₀c⟩ := hY₀'
  let _ : MulAction (sigmaOf P₀ D₀ D₂) (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp
      (sigmaOf P₀ D₀ D₂).subtype)
  have hstab : D₂.subgroupOf (sigmaOf P₀ D₀ D₂) ≤
      MulAction.stabilizer (sigmaOf P₀ D₀ D₂) Y₀ := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    have hxD : (x : G) ∈ D₂ := Subgroup.mem_subgroupOf.mp hx
    show (MulAut.conj (x : G) : MulAut G) • Y₀ = Y₀
    rw [conj_smul_eq_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_set_self Y₀ (hD₂Y₀ hxD))
  have hsame : MulAction.orbit (sigmaOf P₀ D₀ D₂) Y₀ = omegaFam P₀ D₀ D₂ := by
    ext Y
    constructor
    · rintro ⟨g, hg⟩
      rw [← hg]
      show (MulAut.conj (g : G) : MulAut G) • Y₀ ∈ omegaFam P₀ D₀ D₂
      rw [conj_smul_eq_map]
      have hgσ := Subgroup.mem_inf.mp g.2
      have hh : (g : G) ∈ Subgroup.normalizer (D₂ : Set G) := hgσ.1
      have hN : ∀ y ∈ P₀ ⊔ D₀, (g : G) * y * (g : G)⁻¹ ∈ P₀ ⊔ D₀ :=
        fun y hy => mul_mem (mul_mem hgσ.2 hy) (inv_mem hgσ.2)
      refine ⟨map_conj_le_sigmaOf hN hh hY₀σ, le_map_conj_of_mem_normalizer hh hD₂Y₀,
        normal_subgroupOf_map_conj hh hD₂Y₀ hY₀n, ?_⟩
      rw [card_map_conj]
      exact hY₀c
    · intro hY
      obtain ⟨hYσ, hD₂Y, hYn, hYc⟩ := hY
      obtain ⟨g, hgσ, hgY⟩ := exists_conj_map_eq_of_mem_omega hD₀M hD₀n hP₀M hP₀ hcop hD₂D₀
        hD₂p hD₂i hYσ hD₂Y hYn hYc hY₀σ hD₂Y₀ hY₀n hY₀c
      refine ⟨⟨g, hgσ⟩, ?_⟩
      show (MulAut.conj g : MulAut G) • Y₀ = Y
      rw [conj_smul_eq_map]
      exact hgY
  have hidx := orbit_ncard_dvd_index (D₂.subgroupOf (sigmaOf P₀ D₀ D₂)) hstab
  rw [hsame] at hidx
  rw [Nat.card_coe_set_eq]
  intro h
  exact not_two_dvd_index_D2_sigma hD₀M hD₀n hP₀M hP₀ hcop hD₂D₀ hD₂p hD₂i (h.trans hidx)

theorem le_normalizer_inf_of_normal {M D₀ R : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hRM : R ≤ M) :
    R ≤ Subgroup.normalizer ((R ⊓ D₀ : Subgroup G) : Set G) := by
  intro r hr
  have hM : M ≤ Subgroup.normalizer (D₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD₀M).mp hD₀n
  exact mem_normalizer_set_inf (le_normalizer_set_self R hr) (hM (hRM hr))

theorem mem_omegaFam_map_conj {P₀ D₀ D₂ Y : Subgroup G} {h : G}
    (hN : ∀ y ∈ P₀ ⊔ D₀, h * y * h⁻¹ ∈ P₀ ⊔ D₀)
    (hh : h ∈ Subgroup.normalizer (D₂ : Set G)) (hY : Y ∈ omegaFam P₀ D₀ D₂) :
    Subgroup.map (MulAut.conj h).toMonoidHom Y ∈ omegaFam P₀ D₀ D₂ := by
  have hY' : Y ≤ sigmaOf P₀ D₀ D₂ ∧ D₂ ≤ Y ∧ (D₂.subgroupOf Y).Normal ∧
      Nat.card Y = 3 * Nat.card D₂ := hY
  obtain ⟨hYσ, hD₂Y, hYn, hYc⟩ := hY'
  refine ⟨map_conj_le_sigmaOf hN hh hYσ, le_map_conj_of_mem_normalizer hh hD₂Y,
    normal_subgroupOf_map_conj hh hD₂Y hYn, ?_⟩
  rw [card_map_conj]
  exact hYc

open scoped Pointwise in
theorem exists_normalized_omega [Finite G] {M D₀ P₀ Rc : Subgroup G} (hD₀M : D₀ ≤ M)
    (hD₀n : (D₀.subgroupOf M).Normal) (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hcop : Nat.Coprime 3 (Nat.card D₀)) (hRcM : Rc ≤ M) (hRc : IsPGroup 2 Rc)
    (hNn : ((P₀ ⊔ D₀).subgroupOf M).Normal)
    (hD₂i : ¬ 2 ∣ ((Rc ⊓ D₀).subgroupOf D₀).index) :
    ∃ Y : Subgroup G, Y ≤ sigmaOf P₀ D₀ (Rc ⊓ D₀) ∧ Rc ⊓ D₀ ≤ Y ∧
      ((Rc ⊓ D₀).subgroupOf Y).Normal ∧ Nat.card Y = 3 * Nat.card ↥(Rc ⊓ D₀) ∧
      Rc ≤ Subgroup.normalizer (Y : Set G) := by
  have hD₂p : IsPGroup 2 (Rc ⊓ D₀ : Subgroup G) := IsPGroup.to_le hRc inf_le_left
  obtain ⟨Y₀, hY₀σ, hD₂Y₀, hY₀n, hY₀c⟩ :=
    exists_mem_omega hD₀M hD₀n hP₀M hP₀ hcop (inf_le_right : Rc ⊓ D₀ ≤ D₀) hD₂p hD₂i
  have hY₀Ω : Y₀ ∈ omegaFam P₀ D₀ (Rc ⊓ D₀) := ⟨hY₀σ, hD₂Y₀, hY₀n, hY₀c⟩
  have hodd := not_two_dvd_card_omegaFam hD₀M hD₀n hP₀M hP₀ hcop
    (inf_le_right : Rc ⊓ D₀ ≤ D₀) hD₂p hD₂i hY₀Ω
  have hMN : M ≤ Subgroup.normalizer ((P₀ ⊔ D₀ : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hP₀M hD₀M)).mp hNn
  let act : MulAction Rc (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp Rc.subtype)
  let S : SubMulAction Rc (Subgroup G) :=
    { carrier := omegaFam P₀ D₀ (Rc ⊓ D₀)
      smul_mem' := fun c Y hY => by
        have hcM : (c : G) ∈ M := hRcM c.2
        have hN : ∀ y ∈ P₀ ⊔ D₀, (c : G) * y * (c : G)⁻¹ ∈ P₀ ⊔ D₀ :=
          fun y hy => (Subgroup.mem_set_normalizer_iff.mp (hMN hcM) y).mp hy
        show (MulAut.conj (c : G) : MulAut G) • Y ∈ omegaFam P₀ D₀ (Rc ⊓ D₀)
        rw [conj_smul_eq_map]
        exact mem_omegaFam_map_conj hN (le_normalizer_inf_of_normal hD₀M hD₀n hRcM c.2) hY }
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hfix := hRc.card_modEq_card_fixedPoints S
  have hmodd : ¬ 2 ∣ Nat.card S := hodd
  obtain ⟨Ys, hYs⟩ : (MulAction.fixedPoints Rc S).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hE
    apply hmodd
    have h0 : Nat.card (MulAction.fixedPoints Rc S) = 0 := by rw [hE]; simp
    have h2 : Nat.card (MulAction.fixedPoints Rc S) ≡ 0 [MOD 2] := by rw [h0]
    exact (Nat.modEq_zero_iff_dvd).mp (hfix.trans h2)
  have hfixY : ∀ r : Rc, r • Ys = Ys := MulAction.mem_fixedPoints.mp hYs
  have hYsΩ : (Ys : Subgroup G) ∈ omegaFam P₀ D₀ (Rc ⊓ D₀) := Ys.2
  have hYs' : (Ys : Subgroup G) ≤ sigmaOf P₀ D₀ (Rc ⊓ D₀) ∧ Rc ⊓ D₀ ≤ (Ys : Subgroup G) ∧
      ((Rc ⊓ D₀).subgroupOf (Ys : Subgroup G)).Normal ∧
      Nat.card (Ys : Subgroup G) = 3 * Nat.card ↥(Rc ⊓ D₀) := hYsΩ
  refine ⟨(Ys : Subgroup G), hYs'.1, hYs'.2.1, hYs'.2.2.1, hYs'.2.2.2, ?_⟩
  intro r hr
  have hmap : (MulAut.conj r : MulAut G) • (Ys : Subgroup G) = (Ys : Subgroup G) :=
    congrArg Subtype.val (hfixY ⟨r, hr⟩)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr ((conj_smul_eq_map r _).symm.trans hmap)

open scoped Pointwise in
theorem exists_permutable_order_three_of_normal [Finite G] {M D₀ P₀ Rc : Subgroup G}
    (hD₀M : D₀ ≤ M) (hD₀n : (D₀.subgroupOf M).Normal) (hD₀cop : Nat.Coprime 3 (Nat.card D₀))
    (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hNn : ((P₀ ⊔ D₀).subgroupOf M).Normal)
    (hRcM : Rc ≤ M) (hRc : IsPGroup 2 Rc)
    (hsyl : ¬ 2 ∣ ((Rc ⊓ D₀).subgroupOf D₀).index) :
    ∃ P₁ : Subgroup G, P₁ ≤ P₀ ⊔ D₀ ∧ Nat.card P₁ = 3 ∧ (P₁ : Set G) * Rc = Rc * P₁ := by
  obtain ⟨Y, hYσ, hD₂Y, hYn, hYc, hRcN⟩ :=
    exists_normalized_omega hD₀M hD₀n hP₀M hP₀ hD₀cop hRcM hRc hNn hsyl
  have hYsub : Y ≤ P₀ ⊔ D₀ := hYσ.trans (show sigmaOf P₀ D₀ (Rc ⊓ D₀) ≤ P₀ ⊔ D₀ from inf_le_right)
  obtain ⟨P₁, hP₁Y, hP₁3⟩ := exists_le_card_three_of_three_dvd (S := Y) ⟨_, hYc⟩
  have hRY : Rc ⊓ Y = Rc ⊓ D₀ := by
    apply le_antisymm
    · calc Rc ⊓ Y ≤ Rc ⊓ (P₀ ⊔ D₀) := inf_le_inf le_rfl hYsub
        _ = Rc ⊓ D₀ := inf_sup_eq_inf_of_isPGroup_two hD₀M hD₀n hP₀M hP₀ hD₀cop hRc
    · exact le_inf inf_le_left hD₂Y
  have hQ : Nat.card Y = 3 * Nat.card ↥(Rc ⊓ Y) := by
    rw [hRY]
    exact hYc
  exact ⟨P₁, hP₁Y.trans hYsub, hP₁3, set_mul_eq_mul_of_normalizes hRc hRcN hP₁Y hP₁3 hQ⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
