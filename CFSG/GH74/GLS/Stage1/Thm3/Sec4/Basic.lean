module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cj (H : Subgroup G) (g : G) : Subgroup G := H.comap (MulAut.conj g).toMonoidHom

@[simp] theorem mem_cj {H : Subgroup G} {g x : G} : x ∈ cj H g ↔ g * x * g⁻¹ ∈ H := Iff.rfl

theorem cj_card (g : G) (H : Subgroup G) : Nat.card (cj H g) = Nat.card H :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv (by intro a; simp))

theorem cj_mono {g : G} {H K : Subgroup G} (h : H ≤ K) : cj H g ≤ cj K g :=
  fun _ ha => h ha

theorem cj_inf (g : G) (H K : Subgroup G) : cj (H ⊓ K) g = cj H g ⊓ cj K g := by
  ext a; simp

theorem cj_cj (g h : G) (H : Subgroup G) : cj (cj H g) h = cj H (g * h) := by
  ext a; simp [mul_assoc]

theorem cj_one (H : Subgroup G) : cj H 1 = H := by ext a; simp

theorem cj_cj_inv (g : G) (H : Subgroup G) : cj (cj H g) g⁻¹ = H := by
  rw [cj_cj]; simp [cj_one]

theorem cj_inv_cj (g : G) (H : Subgroup G) : cj (cj H g⁻¹) g = H := by
  rw [cj_cj]; simp [cj_one]

theorem cj_centralizer (g x : G) :
    cj (Subgroup.centralizer ({x} : Set G)) g = Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := by
  ext a
  simp only [mem_cj, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h' : x * (g * a * g⁻¹) = g * a * g⁻¹ * x := h
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * x) * g := by rw [h']
      _ = a * (g⁻¹ * x * g) := by group
  · intro h
    have h' : g⁻¹ * x * g * a = a * (g⁻¹ * x * g) := h
    calc x * (g * a * g⁻¹) = g * (g⁻¹ * x * g * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h']
      _ = g * a * g⁻¹ * x := by group

@[expose] def Syl2In (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup 2 ↥P ∧ ¬ 2 ∣ P.relIndex H

noncomputable def toSylow {P H : Subgroup G} (h : Syl2In P H) : Sylow 2 ↥H :=
  (h.2.1.comap_subtype (K := H)).toSylow h.2.2

theorem coe_toSylow {P H : Subgroup G} (h : Syl2In P H) :
    ((toSylow h : Subgroup ↥H)) = P.subgroupOf H := by
  unfold toSylow
  exact IsPGroup.toSylow_coe _ _

theorem mem_toSylow {P H : Subgroup G} (h : Syl2In P H) {a : G} (ha : a ∈ H) :
    a ∈ P ↔ (⟨a, ha⟩ : ↥H) ∈ (toSylow h : Subgroup ↥H) := by
  rw [coe_toSylow]
  rfl

theorem syl2In_cj {P H : Subgroup G} (h : Syl2In P H) (g : G) : Syl2In (cj P g) (cj H g) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  refine ⟨fun a ha => h.1 ha, h.2.1.comap_of_injective _ hinj, ?_⟩
  have : (cj P g).relIndex (cj H g) = P.relIndex H := by
    unfold cj
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hsurj]
  rw [this]
  exact h.2.2

theorem Syl2In.exists_conj [Finite G] {P₁ P₂ H : Subgroup G} (h₁ : Syl2In P₁ H)
    (h₂ : Syl2In P₂ H) : ∃ c ∈ H, P₂ = cj P₁ c := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (toSylow h₁) (toSylow h₂)
  refine ⟨((g⁻¹ : ↥H) : G), (g⁻¹ : ↥H).2, ?_⟩
  ext a
  have hc : ∀ a : G, (((g⁻¹ : ↥H) : G) * a * ((g⁻¹ : ↥H) : G)⁻¹ ∈ P₁ → a ∈ H) := by
    intro a ha
    have h1 : ((g⁻¹ : ↥H) : G) * a * ((g⁻¹ : ↥H) : G)⁻¹ ∈ H := h₁.1 ha
    have := H.mul_mem (H.mul_mem (H.inv_mem (g⁻¹ : ↥H).2) h1) (g⁻¹ : ↥H).2
    simpa [mul_assoc] using this
  by_cases ha : a ∈ H
  · rw [mem_cj, mem_toSylow h₂ ha, ← hg, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h1 : ((g⁻¹ : ↥H) : G) * a * ((g⁻¹ : ↥H) : G)⁻¹ ∈ H := by
      exact H.mul_mem (H.mul_mem (g⁻¹ : ↥H).2 ha) (H.inv_mem (g⁻¹ : ↥H).2)
    rw [mem_toSylow h₁ h1]
    simp
    exact Iff.rfl
  · constructor
    · intro h; exact absurd (h₂.1 h) ha
    · intro h; exact absurd (hc a h) ha

theorem Syl2In.card_eq [Finite G] {P₁ P₂ H : Subgroup G} (h₁ : Syl2In P₁ H)
    (h₂ : Syl2In P₂ H) : Nat.card P₁ = Nat.card P₂ := by
  obtain ⟨c, _, hc⟩ := h₁.exists_conj h₂
  rw [hc, cj_card]

theorem Syl2In.eq_of_le [Finite G] {P H Q : Subgroup G} (h : Syl2In P H) (hQ : IsPGroup 2 ↥Q)
    (hPQ : P ≤ Q) (hQH : Q ≤ H) : Q = P := by
  have key := (toSylow h).is_maximal' (Q := Q.subgroupOf H) (hQ.comap_subtype (K := H))
    (by rw [coe_toSylow h]; exact fun a ha => hPQ ha)
  rw [coe_toSylow] at key
  have := Subgroup.subgroupOf_inj.1 key
  rwa [inf_eq_left.2 hQH, inf_eq_left.2 h.1] at this

theorem exists_syl2In_ge [Finite G] {A H : Subgroup G} (hA : IsPGroup 2 ↥A) (hAH : A ≤ H) :
    ∃ P : Subgroup G, Syl2In P H ∧ A ≤ P := by
  obtain ⟨Sy, hSy⟩ := (hA.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(Sy : Subgroup ↥H).map H.subtype, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := ha
    exact b.2
  · exact Sy.isPGroup'.map H.subtype
  · have hs : ((Sy : Subgroup ↥H).map H.subtype).relIndex H = (Sy : Subgroup ↥H).index := by
      unfold Subgroup.relIndex Subgroup.subgroupOf
      rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hs]
    exact Sylow.not_dvd_index Sy
  · intro a ha
    have : (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H := ha
    exact ⟨_, hSy this, rfl⟩

theorem two_pow_mul_odd_inj {a b M M' : ℕ} (h : 2 ^ a * M = 2 ^ b * M') (hM : Odd M)
    (hM' : Odd M') : a = b := by
  have hc : ∀ c : ℕ, Odd c → Nat.Coprime (2 ^ a) c ∧ Nat.Coprime (2 ^ b) c := fun c hc =>
    ⟨Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hc), Nat.Coprime.pow_left _
      (Nat.coprime_two_left.2 hc)⟩
  have h1 : 2 ^ a ∣ 2 ^ b := by
    have : 2 ^ a ∣ 2 ^ b * M' := ⟨M, h.symm⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right (hc M' hM').1 this)
  have h2 : 2 ^ b ∣ 2 ^ a := by
    have : 2 ^ b ∣ 2 ^ a * M := ⟨M', h⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right (hc M hM).2 this)
  have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.1 h1
  have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.1 h2
  omega

theorem Syl2In.card_eq_pow_mul [Finite G] {P H : Subgroup G} (h : Syl2In P H) :
    ∃ a m : ℕ, Nat.card P = 2 ^ a ∧ Odd m ∧ Nat.card H = 2 ^ a * m := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.2.1
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_eq_left.2 h.1] at h1
  refine ⟨a, P.relIndex H, ha, ?_, ?_⟩
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h.2.2 |> fun h => by omega)
  · rw [← h1, ha]; ring

theorem Syl2In.inf_normal [Finite G] {P H N : Subgroup G} (h : Syl2In P H) (hNH : N ≤ H)
    (hN : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : Syl2In (P ⊓ N) N := by
  have hp : IsPGroup 2 ↥(P ⊓ N) := h.2.1.to_inf_left
  obtain ⟨Q', hQ', hle⟩ := exists_syl2In_ge hp (inf_le_right : P ⊓ N ≤ N)
  have hQ'p : IsPGroup 2 ↥Q' := hQ'.2.1
  obtain ⟨P', hP', hQ'P'⟩ := exists_syl2In_ge hQ'p (hQ'.1.trans hNH)
  obtain ⟨c, hcH, hc⟩ := h.exists_conj hP'
  have hcN : cj N c = N := by
    ext a
    simp only [mem_cj]
    constructor
    · intro ha
      have := hN c⁻¹ (H.inv_mem hcH) _ ha
      simpa [mul_assoc] using this
    · intro ha
      exact hN c hcH a ha
  have hcard : Nat.card ↥(P' ⊓ N) = Nat.card ↥(P ⊓ N) := by
    rw [hc, ← hcN, ← cj_inf, cj_card, hcN]
  have hQle : Q' ≤ P' ⊓ N := le_inf hQ'P' hQ'.1
  have hcard1 : Nat.card ↥Q' ≤ Nat.card ↥(P ⊓ N) := by
    rw [← hcard]; exact Subgroup.card_le_of_le hQle
  have heq : P ⊓ N = Q' := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_)
    exact hcard1
  rw [heq]; exact hQ'

theorem mem_sup_of_le_normalizer {A B : Subgroup G} (hnorm : A ≤ Subgroup.normalizer (B : Set G))
    {y : G} (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hy' : y ∈ (↑(A ⊔ B) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G}
    (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have : a * b * a⁻¹ = b := by rw [hc a ha b hb]; group
      rwa [this]
    · intro hb
      have h1 := hc a ha _ hb
      have : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [h1]
          _ = b := by group
      rwa [this] at hb
  exact mem_sup_of_le_normalizer hnorm hy

theorem le_normalizer_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h : b * x * b⁻¹ = x := by rw [← hc x hx b hb]; group
    rwa [h]
  · intro hx
    have hcomm := hc _ hx b hb
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
        _ = b * x * b⁻¹ := by group
    rwa [this]

theorem card_sup_mul_card_inf {A B : Subgroup G} (h : B ≤ normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  set M := B ⊔ A with hM
  have hBM : B ≤ M := le_sup_left
  have hAM : A ≤ M := le_sup_right
  have : (A.subgroupOf M).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have hsup : B.subgroupOf M ⊔ A.subgroupOf M = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup B A)
  have h1 := Subgroup.relIndex_sup_right (H := B.subgroupOf M) (K := A.subgroupOf M)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBM] at h1
  have h2 := Subgroup.card_mul_index (A.subgroupOf M)
  have h3 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  rw [h1, h3] at h2
  have h4 := Subgroup.relIndex_mul_card A B
  rw [sup_comm] at hM
  rw [← hM, ← h2, mul_assoc, h4]

theorem conj_mem_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) {n : G} (hn : n ∈ A) : x * n * x⁻¹ ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc hx
  have hbn : b * n = n * b := (hc n hn b hb).symm
  have : a * b * n * (a * b)⁻¹ = a * n * a⁻¹ := by
    calc a * b * n * (a * b)⁻¹ = a * (b * n) * b⁻¹ * a⁻¹ := by group
      _ = a * (n * b) * b⁻¹ * a⁻¹ := by rw [hbn]
      _ = a * n * a⁻¹ := by group
  rw [this]
  exact A.mul_mem (A.mul_mem ha hn) (A.inv_mem ha)

theorem conj_mem_of_commute' {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) {n : G} (hn : n ∈ B) : x * n * x⁻¹ ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc hx
  have hm : b * n * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hn) (B.inv_mem hb)
  have h3 : a * (b * n * b⁻¹) = (b * n * b⁻¹) * a := hc a ha _ hm
  have : a * b * n * (a * b)⁻¹ = b * n * b⁻¹ := by
    calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
      _ = (b * n * b⁻¹) * a * a⁻¹ := by rw [h3]
      _ = b * n * b⁻¹ := by group
  rw [this]; exact hm

theorem Syl2In.eq_sup_of_normalizing [Finite G] {A B P : Subgroup G}
    (hBA : B ≤ normalizer (A : Set G))
    (hnA : ∀ x ∈ A ⊔ B, ∀ n ∈ A, x * n * x⁻¹ ∈ A) (hnB : ∀ x ∈ A ⊔ B, ∀ n ∈ B, x * n * x⁻¹ ∈ B)
    (h : Syl2In P (A ⊔ B)) (hcP : ∀ a ∈ P ⊓ A, ∀ b ∈ P ⊓ B, a * b = b * a) :
    P = (P ⊓ A) ⊔ (P ⊓ B) := by
  have hnAB : ∀ x ∈ A ⊔ B, ∀ n ∈ A ⊓ B, x * n * x⁻¹ ∈ A ⊓ B := fun x hx n hn =>
    ⟨hnA x hx n hn.1, hnB x hx n hn.2⟩
  have hA := h.inf_normal (le_sup_left : A ≤ A ⊔ B) hnA
  have hB := h.inf_normal (le_sup_right : B ≤ A ⊔ B) hnB
  have hAB := h.inf_normal ((inf_le_left : A ⊓ B ≤ A).trans le_sup_left) hnAB
  have e12 : (P ⊓ A) ⊓ (P ⊓ B) = P ⊓ (A ⊓ B) := by
    ext x; simp only [mem_inf]; tauto
  obtain ⟨a, m, hPa, hm, hHm⟩ := h.card_eq_pow_mul
  obtain ⟨a₁, m₁, hP₁a, hm₁, hAm⟩ := hA.card_eq_pow_mul
  obtain ⟨a₂, m₂, hP₂a, hm₂, hBm⟩ := hB.card_eq_pow_mul
  obtain ⟨d, m₃, hP₁₂a, hm₃, hABm⟩ := hAB.card_eq_pow_mul
  have c1 := card_sup_mul_card_inf hBA
  have c2 := card_sup_mul_card_inf (le_normalizer_of_commute hcP)
  rw [e12] at c2
  rw [hHm, hABm, hAm, hBm] at c1
  rw [hP₁₂a, hP₁a, hP₂a] at c2
  have hexp : a + d = a₁ + a₂ := by
    have : 2 ^ (a + d) * (m * m₃) = 2 ^ (a₁ + a₂) * (m₁ * m₂) := by
      rw [pow_add, pow_add]
      calc 2 ^ a * 2 ^ d * (m * m₃) = (2 ^ a * m) * (2 ^ d * m₃) := by ring
        _ = (2 ^ a₁ * m₁) * (2 ^ a₂ * m₂) := c1
        _ = _ := by ring
    exact two_pow_mul_odd_inj this (hm.mul hm₃) (hm₁.mul hm₂)
  have hcard : Nat.card ↥P ≤ Nat.card ↥((P ⊓ A) ⊔ (P ⊓ B)) := by
    have h2d : 0 < 2 ^ d := by positivity
    have : Nat.card ↥((P ⊓ A) ⊔ (P ⊓ B)) * 2 ^ d = 2 ^ a * 2 ^ d := by
      rw [c2, ← pow_add, ← pow_add, hexp]
    have := Nat.eq_of_mul_eq_mul_right h2d this
    rw [hPa, this]
  have hle : (P ⊓ A) ⊔ (P ⊓ B) ≤ P := sup_le inf_le_left inf_le_left
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Syl2In.eq_sup_of_commute [Finite G] {A B P : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (h : Syl2In P (A ⊔ B)) :
    P = (P ⊓ A) ⊔ (P ⊓ B) :=
  Syl2In.eq_sup_of_normalizing (le_normalizer_of_commute hc)
    (fun _ hx _ hn => conj_mem_of_commute hc hx hn) (fun _ hx _ hn => conj_mem_of_commute' hc hx hn)
    h (fun _ ha _ hb => hc _ ha.2 _ hb.2)

open scoped commutatorElement

@[expose] def secCent (K M : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ normalizer (K : Set G) ∧ c ∈ normalizer (M : Set G) ∧ ∀ k ∈ K, ⁅k, c⁆ ∈ M}
  one_mem' := ⟨one_mem _, one_mem _, fun k _ => by simp⟩
  mul_mem' := by
    rintro c d ⟨hcK, hcM, hc⟩ ⟨hdK, hdM, hd⟩
    refine ⟨mul_mem hcK hdK, mul_mem hcM hdM, fun k hk => ?_⟩
    have h1 : ⁅k, c * d⁆ = ⁅k, c⁆ * (c * ⁅k, d⁆ * c⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact M.mul_mem (hc k hk) ((mem_normalizer_iff.mp hcM _).mp (hd k hk))
  inv_mem' := by
    rintro c ⟨hcK, hcM, hc⟩
    refine ⟨inv_mem hcK, inv_mem hcM, fun k hk => ?_⟩
    have h1 : ⁅k, c⁻¹⁆ = c⁻¹ * (⁅k, c⁆)⁻¹ * c⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (mem_normalizer_iff.mp (inv_mem hcM) _).mp (M.inv_mem (hc k hk))

theorem mem_secCent {K M : Subgroup G} {c : G} :
    c ∈ secCent K M ↔ c ∈ normalizer (K : Set G) ∧ c ∈ normalizer (M : Set G) ∧
      ∀ k ∈ K, ⁅k, c⁆ ∈ M := Iff.rfl

@[expose] def ZsM (O : Subgroup G → Subgroup G) (X : Subgroup G) : Subgroup G := X ⊓ secCent X (O X)

structure IsOddCore (X N : Subgroup G) : Prop where
  le : N ≤ X
  normal : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N
  odd : Odd (Nat.card ↥N)
  max : ∀ M : Subgroup G, M ≤ X → (∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) → Odd (Nat.card ↥M) →
    M ≤ N

@[expose] def Rk1 (H : Subgroup G) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → b * b = 1 → a * b = b * a → a = 1 ∨ b = 1 ∨ a = b

theorem IsOddCore.le_of_le_odd {X N M O' : Subgroup G} (h : IsOddCore X N) (hM : M ≤ X)
    (hMn : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hMO : M ≤ O') (hO' : Odd (Nat.card ↥O')) :
    M ≤ N :=
  h.max M hM hMn (Odd.of_dvd_nat hO' (Subgroup.card_dvd_of_le hMO))

theorem IsOddCore.conj_mem {X N : Subgroup G} (h : IsOddCore X N) {c : G}
    (hc : ∀ x ∈ X, c * x * c⁻¹ ∈ X) (hc' : ∀ x ∈ X, c⁻¹ * x * c ∈ X) {n : G} (hn : n ∈ N) :
    c * n * c⁻¹ ∈ N := by
  have hM : cj N c⁻¹ ≤ N := by
    refine h.max _ ?_ ?_ ?_
    · intro a ha
      have h1 : c⁻¹ * a * c ∈ N := by simpa [mem_cj] using ha
      have := hc _ (h.le h1)
      simpa [mul_assoc] using this
    · intro x hx m hm
      have hm' : c⁻¹ * m * c ∈ N := by simpa [mem_cj] using hm
      have := h.normal _ (hc' x hx) _ hm'
      simp only [mem_cj]
      have e : c⁻¹ * (x * m * x⁻¹) * c⁻¹⁻¹ =
          (c⁻¹ * x * c) * (c⁻¹ * m * c) * (c⁻¹ * x * c)⁻¹ := by group
      rw [e]; exact this
    · rw [cj_card]; exact h.odd
  have : c * n * c⁻¹ ∈ cj N c⁻¹ := by simpa [mem_cj, mul_assoc] using hn
  exact hM this

theorem inf_eq_bot_of_pgroup_odd [Finite G] {A N : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hN : Odd (Nat.card ↥N)) : A ⊓ N = ⊥ := by
  apply disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hA
  rw [ha]
  exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hN)

theorem exists_sq_eq_of_unique_inv {Y : Subgroup G} {z : G} (hY : IsPGroup 2 ↥Y)
    (huniq : ∀ x ∈ Y, x * x = 1 → x = 1 ∨ x = z) {y : G} (hy : y ∈ Y)
    (hyz : y ∉ Subgroup.zpowers z) : ∃ w ∈ Y, w * w = z := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hY) ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := by simpa using hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hlt : k < 2 := not_le.mp hlt
    interval_cases k
    · have : y = 1 := orderOf_eq_one_iff.mp (by simpa using hk')
      exact hyz (this ▸ Subgroup.one_mem _)
    · have hy2 : y * y = 1 := by
        have := pow_orderOf_eq_one y
        rw [hk'] at this
        simpa [sq] using this
      rcases huniq y hy hy2 with h | h
      · exact hyz (h ▸ Subgroup.one_mem _)
      · exact hyz (h ▸ Subgroup.mem_zpowers z)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
  refine ⟨y ^ (2 ^ j), Y.pow_mem hy _, ?_⟩
  have hww : y ^ (2 ^ j) * y ^ (2 ^ j) = y ^ (2 ^ (j + 1)) := by
    rw [← pow_add, pow_succ]; congr 1; ring
  have hw1 : y ^ (2 ^ (j + 1)) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hk']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw2 : y ^ (2 ^ (j + 1)) * y ^ (2 ^ (j + 1)) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    have : 2 ^ (j + 1 + 1) = orderOf y := by rw [hk']; ring
    rw [this]; exact pow_orderOf_eq_one y
  have hmem : y ^ (2 ^ (j + 1)) ∈ Y := Y.pow_mem hy _
  rcases huniq _ hmem hw2 with h | h
  · exact absurd h hw1
  · rw [hww]; exact h

theorem exists_mem_comm_mod {D M N : Subgroup G} (hD : IsPGroup 2 ↥D) [Finite G]
    (hND : N ≤ D) (hMc : ∀ m ∈ M, ∀ d ∈ D, m * d = d * m)
    (hNn : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hne : ∃ n ∈ N, n ∉ M) :
    ∃ y ∈ N, y ∉ M ∧ ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ ∈ M := by
  set M' : Subgroup ↥D := M.subgroupOf D with hM'
  have hMn : M'.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ M := hn
    have : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [← hMc n hn' g g.2]; simp
    show ((g * n * g⁻¹ : ↥D) : G) ∈ M
    simpa [this] using hn'⟩
  set N' : Subgroup ↥D := N.subgroupOf D with hN'
  have hNn' : N'.Normal := ⟨fun n hn g => by
    have := hNn (g : G) g.2 (n : G) hn
    show ((g * n * g⁻¹ : ↥D) : G) ∈ N
    simpa using this⟩
  have hΓ : IsPGroup 2 (↥D ⧸ M') :=
    IsPGroup.of_surjective hD (QuotientGroup.mk' M') (QuotientGroup.mk'_surjective M')
  have hΓn : Group.IsNilpotent (↥D ⧸ M') := hΓ.isNilpotent
  set N'' : Subgroup (↥D ⧸ M') := N'.map (QuotientGroup.mk' M') with hN''
  have hN''n : N''.Normal := hNn'.map _ (QuotientGroup.mk'_surjective M')
  have hne'' : N'' ≠ ⊥ := by
    obtain ⟨n, hnN, hnM⟩ := hne
    intro hbot
    have hmem : QuotientGroup.mk' M' (⟨n, hND hnN⟩ : ↥D) ∈ N'' := Subgroup.mem_map_of_mem _ hnN
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hnM hmem
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne''
  obtain ⟨γ, hγ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc
  have hγN : (γ : ↥D ⧸ M') ∈ N'' := γ.2.1
  have hγC : (γ : ↥D ⧸ M') ∈ Subgroup.center (↥D ⧸ M') := γ.2.2
  obtain ⟨δ, hδN, hδ⟩ := Subgroup.mem_map.1 hγN
  refine ⟨(δ : G), hδN, ?_, ?_⟩
  · intro hδM
    apply hγ1
    apply Subtype.ext
    rw [← hδ, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hδM
  · intro d hd
    have h1 := Subgroup.mem_center_iff.1 hγC (QuotientGroup.mk' M' ⟨d, hd⟩)
    rw [← hδ] at h1
    have h2 : QuotientGroup.mk' M' (δ * ⟨d, hd⟩ * δ⁻¹ * ⟨d, hd⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2

theorem card_zpowers_of_sq {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 2 := by
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hx2 hx1

theorem isPGroup_zpowers_of_sq {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    IsPGroup 2 ↥(Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [card_zpowers_of_sq hx hx1]; norm_num)

theorem mem_zpowers_of_sq {x y : G} (hx : x * x = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, add_zero, zpow_mul, hx2, one_zpow]
    · right
      rw [hk, h1, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem cj_zpowers_of_comm {z c : G} (hz : z * z = 1) (hc : c * z = z * c) :
    cj (Subgroup.zpowers z) c = Subgroup.zpowers z := by
  have h1 : c * z * c⁻¹ = z := by rw [hc]; group
  ext x
  rw [mem_cj, mem_zpowers_of_sq hz, mem_zpowers_of_sq hz]
  constructor
  · rintro (h | h)
    · left
      have : x = c⁻¹ * (c * x * c⁻¹) * c := by group
      rw [this, h]; group
    · right
      have h2 : c⁻¹ * z * c = z := by
        calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
          _ = c⁻¹ * (c * z) := by rw [hc]
          _ = z := by group
      have : x = c⁻¹ * (c * x * c⁻¹) * c := by group
      rw [this, h, h2]
  · rintro (h | h)
    · left; rw [h]; group
    · right; rw [h, h1]

theorem mem_normalizer_of_both {X : Subgroup G} {g : G} (h1 : ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, g⁻¹ * x * g ∈ X) : g ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h1 x
  · intro hx
    have := h2 _ hx
    simpa [mul_assoc] using this

theorem orderOf_two_iff {t : G} : orderOf t = 2 ↔ t * t = 1 ∧ t ≠ 1 := by
  rw [orderOf_eq_prime_iff, pow_two]

theorem secCent_of_central {X M : Subgroup G} (hM : M ≤ X) {c : G} (hc : ∀ k ∈ X, c * k = k * c) :
    c ∈ secCent X M := by
  have hn : ∀ x ∈ X, c * x * c⁻¹ = x := by
    intro x hx; rw [hc x hx]; group
  refine ⟨?_, ?_, ?_⟩
  · refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · rw [hn x hx]; exact hx
    · have := hn x hx
      have h2 : c⁻¹ * x * c = x := by
        calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
          _ = c⁻¹ * (c * x) := by rw [← hc x hx]
          _ = x := by group
      rw [h2]; exact hx
  · refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · rw [hn x (hM hx)]; exact hx
    · have h2 : c⁻¹ * x * c = x := by
        calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
          _ = c⁻¹ * (c * x) := by rw [← hc x (hM hx)]
          _ = x := by group
      rw [h2]; exact hx
  · intro k hk
    have : ⁅k, c⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [← hc k hk]; group
    rw [this]; exact one_mem _

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
