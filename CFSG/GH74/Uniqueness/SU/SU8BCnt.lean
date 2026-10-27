module

public import CFSG.GH74.Uniqueness.SU.SU8BDefs
public import CFSG.GH74.Uniqueness.SU.SU8Burn

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU4
  CFSG.GH74.Uniqueness.SU.SU8.Setup CFSG.GH74.Uniqueness.SU.SU8.Burn
open scoped Pointwise

namespace CaseBCnt

variable {G : Type} [Group G] {z : G} {L A V₀ : Subgroup G}

theorem pow_conj_mem {B : Subgroup G} {g : G} (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) (j : ℕ) :
    ∀ b ∈ B, g ^ j * b * (g ^ j)⁻¹ ∈ B := by
  induction j with
  | zero => intro b hb; simpa using hb
  | succ j ih =>
    intro b hb
    have := hB _ (ih b hb)
    have e : g * (g ^ j * b * (g ^ j)⁻¹) * g⁻¹ = g ^ (j + 1) * b * (g ^ (j + 1))⁻¹ := by
      rw [pow_succ']; group
    rw [← e]; exact this

theorem pow_conj_eq (x g : G) (j : ℕ) : (x⁻¹ * g * x) ^ j = x⁻¹ * g ^ j * x := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, ih, pow_succ]; group

theorem dichotomy (cb : CaseB L A V₀ z) {g₀ : G}
    (htr : ∀ a ∈ A, a ∉ V₀ → ∀ b ∈ A, b ∉ V₀ → ∃ j : ℕ, g₀ ^ j * a * (g₀ ^ j)⁻¹ * b⁻¹ ∈ V₀)
    {B : Subgroup G} (hBA : B ≤ A) (hBinv : ∀ b ∈ B, g₀ * b * g₀⁻¹ ∈ B) (hnot : ¬ B ≤ V₀) :
    ∀ a ∈ A, ∃ b ∈ B, ∃ c ∈ V₀, a = b * c := by
  intro a ha
  by_cases haV : a ∈ V₀
  · exact ⟨1, B.one_mem, a, haV, by simp⟩
  · obtain ⟨b₀, hb₀, hb₀V⟩ := Set.not_subset.mp hnot
    obtain ⟨j, hj⟩ := htr b₀ (hBA hb₀) hb₀V a ha haV
    have hb' : g₀ ^ j * b₀ * (g₀ ^ j)⁻¹ ∈ B := pow_conj_mem hBinv j b₀ hb₀
    have hc : a * (g₀ ^ j * b₀ * (g₀ ^ j)⁻¹)⁻¹ ∈ V₀ := by
      have h1 := V₀.inv_mem hj
      have : (g₀ ^ j * b₀ * (g₀ ^ j)⁻¹ * a⁻¹)⁻¹ = a * (g₀ ^ j * b₀ * (g₀ ^ j)⁻¹)⁻¹ := by group
      rwa [this] at h1
    refine ⟨g₀ ^ j * b₀ * (g₀ ^ j)⁻¹, hb', _, hc, ?_⟩
    have hcomm := cb.A_comm _ (hBA hb') _ (cb.V₀_le hc)
    rw [hcomm]; group

theorem mem_V₀_iff (cb : CaseB L A V₀ z) {a : G} :
    a ∈ V₀ ↔ a ∈ A ∧ ∀ g ∈ L ⊓ normalizer (A : Set G), g * a * g⁻¹ = a := by
  constructor
  · intro ha
    exact ⟨cb.V₀_le ha, fun g hg => cb.act_C g hg a ha⟩
  · rintro ⟨haA, hfix⟩
    by_contra hna
    obtain ⟨g₀, hg₀, -, -, hfpf, -, -⟩ := cb.gen
    apply hfpf a haA hna 1 one_pos (by norm_num)
    rw [pow_one, hfix g₀ hg₀, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem conj_mem_V₀ (cb : CaseB L A V₀ z) {x : G} (hxN : x ∈ normalizer (A : Set G))
    (hxL : x ∈ normalizer (L : Set G)) {c : G} (hc : c ∈ V₀) : x * c * x⁻¹ ∈ V₀ := by
  rw [mem_V₀_iff cb]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hxN c).mp (cb.V₀_le hc), fun g hg => ?_⟩
  have hgL : x⁻¹ * g * x ∈ L := by
    have h1 := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem hxL) g).mp hg.1
    simpa using h1
  have hgN : x⁻¹ * g * x ∈ normalizer (A : Set G) :=
    (normalizer (A : Set G)).mul_mem
      ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hxN) hg.2) hxN
  have h2 := cb.act_C _ ⟨hgL, hgN⟩ c hc
  calc g * (x * c * x⁻¹) * g⁻¹ = x * ((x⁻¹ * g * x) * c * (x⁻¹ * g * x)⁻¹) * x⁻¹ := by group
    _ = x * c * x⁻¹ := by rw [h2]

section Finite

variable [Finite G]

theorem mem_normalizer_V₀ (cb : CaseB L A V₀ z) {x : G} (hxN : x ∈ normalizer (A : Set G))
    (hxL : x ∈ normalizer (L : Set G)) : x ∈ normalizer (V₀ : Set G) :=
  mem_normalizer_of_conj_le (fun _ hc => conj_mem_V₀ cb hxN hxL hc)

theorem conj_eq_of_ne_bot (cb : CaseB L A V₀ z)
    (hTI : ∀ g v : G, v ∈ V₀ → v ≠ 1 → g * v * g⁻¹ ∈ V₀ → g ∈ normalizer (L : Set G))
    {x₁ x₂ : G} (h₁ : x₁ ∈ normalizer (A : Set G)) (h₂ : x₂ ∈ normalizer (A : Set G)) {w : G}
    (hw1 : w ≠ 1) (hw₁ : w ∈ conjSub x₁ V₀) (hw₂ : w ∈ conjSub x₂ V₀) :
    x₂⁻¹ * x₁ ∈ normalizer (V₀ : Set G) := by
  obtain ⟨e₁, he₁, rfl⟩ := mem_conjSub.mp hw₁
  obtain ⟨e₂, he₂, he⟩ := mem_conjSub.mp hw₂
  have he1 : e₁ ≠ 1 := fun h => hw1 (by rw [h]; group)
  have hmem : (x₂⁻¹ * x₁) * e₁ * (x₂⁻¹ * x₁)⁻¹ ∈ V₀ := by
    have : (x₂⁻¹ * x₁) * e₁ * (x₂⁻¹ * x₁)⁻¹ = e₂ := by
      calc (x₂⁻¹ * x₁) * e₁ * (x₂⁻¹ * x₁)⁻¹ = x₂⁻¹ * (x₁ * e₁ * x₁⁻¹) * x₂ := by group
        _ = x₂⁻¹ * (x₂ * e₂ * x₂⁻¹) * x₂ := by rw [← he]
        _ = e₂ := by group
    rw [this]; exact he₂
  have hxL : x₂⁻¹ * x₁ ∈ normalizer (L : Set G) := hTI _ e₁ he₁ he1 hmem
  exact mem_normalizer_V₀ cb
    ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem h₂) h₁) hxL

theorem fixed_imp (cb : CaseB L A V₀ z)
    (hTI : ∀ g v : G, v ∈ V₀ → v ≠ 1 → g * v * g⁻¹ ∈ V₀ → g ∈ normalizer (L : Set G))
    {g₀ : G}
    (htr : ∀ a ∈ A, a ∉ V₀ → ∀ b ∈ A, b ∉ V₀ → ∃ j : ℕ, g₀ ^ j * a * (g₀ ^ j)⁻¹ * b⁻¹ ∈ V₀)
    {x : G} (hx : x ∈ normalizer (A : Set G))
    (hy : x⁻¹ * g₀ * x ∈ normalizer (V₀ : Set G)) : x ∈ normalizer (V₀ : Set G) := by
  set B := conjSub x V₀ with hB
  have hBA : B ≤ A := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_conjSub.mp hw
    exact (Subgroup.mem_normalizer_iff.mp hx e).mp (cb.V₀_le he)
  have hBinv : ∀ b ∈ B, g₀ * b * g₀⁻¹ ∈ B := by
    intro b hb
    obtain ⟨e, he, rfl⟩ := mem_conjSub.mp hb
    have h2 : (x⁻¹ * g₀ * x) * e * (x⁻¹ * g₀ * x)⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp hy e).mp he
    refine mem_conjSub.mpr ⟨_, h2, ?_⟩
    group
  by_cases hBV : B ≤ V₀
  · exact mem_normalizer_of_conj_le (fun c hc => hBV (mem_conjSub.mpr ⟨c, hc, rfl⟩))
  · exfalso
    have hBinf : ∀ w ∈ B, w ∈ V₀ → w = 1 := by
      intro w hwB hwV
      by_contra hw1
      obtain ⟨e, he, rfl⟩ := mem_conjSub.mp hwB
      have he1 : e ≠ 1 := fun h => hw1 (by rw [h]; group)
      have hxL : x ∈ normalizer (L : Set G) := hTI x e he he1 hwV
      exact hBV (fun w hw => by
        obtain ⟨e', he', rfl⟩ := mem_conjSub.mp hw
        exact conj_mem_V₀ cb hx hxL he')
    have hdich := dichotomy cb htr hBA hBinv hBV
    have hBcard : Nat.card B = Nat.card V₀ :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    let f : ↥B × ↥V₀ → ↥A := fun p => ⟨p.1 * p.2, A.mul_mem (hBA p.1.2) (cb.V₀_le p.2.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ ⟨⟨b', hb'⟩, ⟨c', hc'⟩⟩ h
        have h1 : b * c = b' * c' := congrArg Subtype.val h
        have h2 : b'⁻¹ * b = c' * c⁻¹ := by
          calc b'⁻¹ * b = b'⁻¹ * (b * c) * c⁻¹ := by group
            _ = b'⁻¹ * (b' * c') * c⁻¹ := by rw [h1]
            _ = c' * c⁻¹ := by group
        have h3 : b'⁻¹ * b = 1 := hBinf _ (B.mul_mem (B.inv_mem hb') hb)
          (h2 ▸ V₀.mul_mem hc' (V₀.inv_mem hc))
        have hbb : b = b' := (inv_mul_eq_one.mp h3).symm
        subst hbb
        have hcc : c = c' := mul_left_cancel h1
        subst hcc
        rfl
      · rintro ⟨a, ha⟩
        obtain ⟨b, hb, c, hc, rfl⟩ := hdich a ha
        exact ⟨(⟨b, hb⟩, ⟨c, hc⟩), rfl⟩
    have hAcard : Nat.card A = Nat.card B * Nat.card V₀ := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
    have hV₀pos : 0 < Nat.card V₀ := Nat.card_pos
    have hV₀8 : Nat.card V₀ = 8 := by
      have h1 := cb.card_A
      rw [hAcard, hBcard] at h1
      have : Nat.card V₀ * Nat.card V₀ = Nat.card V₀ * 8 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hV₀pos this
    have hyL : x⁻¹ * g₀ * x ∈ normalizer (L : Set G) :=
      hTI _ z cb.z_mem cb.z_ne ((Subgroup.mem_normalizer_iff.mp hy z).mp cb.z_mem)
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₀ ⊓ L, u ≠ 1 := by
      have h1 : V₀ ⊓ L ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).mp cb.inf_gt
      obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp h1)
      exact ⟨u, hu, fun h => hu1 (Subtype.ext h)⟩
    obtain ⟨w, hwV, hwL⟩ : ∃ w ∈ V₀, w ∉ L := by
      by_contra hcon
      push Not at hcon
      have hle : V₀ ≤ V₀ ⊓ L := fun w hw => ⟨hw, hcon w hw⟩
      have := Subgroup.card_le_of_le hle
      have h4 := cb.inf_le
      omega
    have hxuA : x * u * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hx u).mp (cb.V₀_le hu.1)
    have hxwA : x * w * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hx w).mp (cb.V₀_le hwV)
    have hxuB : x * u * x⁻¹ ∈ B := mem_conjSub.mpr ⟨u, hu.1, rfl⟩
    have hxwB : x * w * x⁻¹ ∈ B := mem_conjSub.mpr ⟨w, hwV, rfl⟩
    have hw1 : w ≠ 1 := fun h => hwL (h ▸ L.one_mem)
    have hxuV : x * u * x⁻¹ ∉ V₀ := fun h => hu1 (by
      have := hBinf _ hxuB h
      have h2 : u = x⁻¹ * (x * u * x⁻¹) * x := by group
      rw [h2, this]; group)
    have hxwV : x * w * x⁻¹ ∉ V₀ := fun h => hw1 (by
      have := hBinf _ hxwB h
      have h2 : w = x⁻¹ * (x * w * x⁻¹) * x := by group
      rw [h2, this]; group)
    obtain ⟨j, hj⟩ := htr _ hxuA hxuV _ hxwA hxwV
    have hjB : g₀ ^ j * (x * u * x⁻¹) * (g₀ ^ j)⁻¹ ∈ B := pow_conj_mem hBinv j _ hxuB
    have h1 := hBinf _ (B.mul_mem hjB (B.inv_mem hxwB)) hj
    have h2 : g₀ ^ j * (x * u * x⁻¹) * (g₀ ^ j)⁻¹ = x * w * x⁻¹ := mul_inv_eq_one.mp h1
    have hyjL : x⁻¹ * g₀ ^ j * x ∈ normalizer (L : Set G) := by
      rw [← pow_conj_eq]; exact pow_mem hyL j
    have hweq : (x⁻¹ * g₀ ^ j * x) * u * (x⁻¹ * g₀ ^ j * x)⁻¹ = w := by
      calc (x⁻¹ * g₀ ^ j * x) * u * (x⁻¹ * g₀ ^ j * x)⁻¹
          = x⁻¹ * (g₀ ^ j * (x * u * x⁻¹) * (g₀ ^ j)⁻¹) * x := by group
        _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [h2]
        _ = w := by group
    apply hwL
    rw [← hweq]
    exact (Subgroup.mem_normalizer_iff.mp hyjL u).mp hu.2

theorem count_main (cb : CaseB L A V₀ z)
    (hTI : ∀ g v : G, v ∈ V₀ → v ≠ 1 → g * v * g⁻¹ ∈ V₀ → g ∈ normalizer (L : Set G))
    (hirr : ¬ normalizer (A : Set G) ≤ normalizer (V₀ : Set G))
    (hodd : Odd ((normalizer (V₀ : Set G)).relIndex (normalizer (A : Set G)))) :
    Nat.card V₀ = 2 ∧ Nat.card A = 16 ∧
      ∀ u ∈ A, u ≠ 1 → ∃ x ∈ normalizer (A : Set G), x * z * x⁻¹ = u := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N : Subgroup G := normalizer (A : Set G) with hN
  set N₀' : Subgroup ↥N := (normalizer (V₀ : Set G)).subgroupOf N with hN₀'
  obtain ⟨g₀, hg₀, ⟨e, he⟩, h7, hfpf, htr, hact⟩ := cb.gen
  have hg₀N : g₀ ∈ N := hg₀.2
  let n₀ : ↥N := ⟨g₀, hg₀N⟩
  let Γ : Subgroup ↥N := Subgroup.zpowers n₀
  have hΓ7 : IsPGroup 7 Γ := by
    have hord : orderOf n₀ ∣ 7 ^ e :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using he))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  have hΓle : Γ ≤ N₀' := by
    rw [Subgroup.zpowers_le]
    show (n₀ : G) ∈ normalizer (V₀ : Set G)
    exact mem_normalizer_of_conj_le (fun c hc => by rw [cb.act_C g₀ hg₀ c hc]; exact hc)
  have hfixed : MulAction.fixedPoints ↥Γ (↥N ⧸ N₀') = {QuotientGroup.mk 1} := by
    ext i
    constructor
    · intro hi
      induction i using QuotientGroup.induction_on with
      | H x =>
        have h1 : (⟨n₀, Subgroup.mem_zpowers n₀⟩ : ↥Γ) • (QuotientGroup.mk x : ↥N ⧸ N₀') =
            QuotientGroup.mk x := hi ⟨n₀, Subgroup.mem_zpowers n₀⟩
        have h2 : (QuotientGroup.mk (n₀ * x) : ↥N ⧸ N₀') = QuotientGroup.mk x := h1
        have h3 := QuotientGroup.eq.mp h2
        have h4 : x⁻¹ * n₀ * x ∈ N₀' := by
          have := N₀'.inv_mem h3
          have e1 : ((n₀ * x)⁻¹ * x)⁻¹ = x⁻¹ * n₀ * x := by group
          rwa [e1] at this
        have hy : (x : G)⁻¹ * g₀ * (x : G) ∈ normalizer (V₀ : Set G) := by
          have := Subgroup.mem_subgroupOf.mp h4
          simpa using this
        have hxn : (x : G) ∈ normalizer (V₀ : Set G) := fixed_imp cb hTI htr x.2 hy
        rw [Set.mem_singleton_iff]
        apply QuotientGroup.eq.mpr
        have : x ∈ N₀' := Subgroup.mem_subgroupOf.mpr hxn
        simpa using N₀'.inv_mem this
    · intro hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      intro γ
      have h1 : (γ : ↥N) ∈ N₀' := hΓle γ.2
      show (QuotientGroup.mk ((γ : ↥N) * 1) : ↥N ⧸ N₀') = QuotientGroup.mk 1
      apply QuotientGroup.eq.mpr
      simpa using N₀'.inv_mem h1
  have hmod : Nat.card (↥N ⧸ N₀') ≡ Nat.card (MulAction.fixedPoints ↥Γ (↥N ⧸ N₀')) [MOD 7] :=
    hΓ7.card_modEq_card_fixedPoints (α := ↥N ⧸ N₀')
  have hfixcard : Nat.card (MulAction.fixedPoints ↥Γ (↥N ⧸ N₀')) = 1 := by
    rw [hfixed]; simp
  rw [hfixcard] at hmod
  have hIidx : Nat.card (↥N ⧸ N₀') = (normalizer (V₀ : Set G)).relIndex N := rfl
  have hI1 : 1 < Nat.card (↥N ⧸ N₀') := by
    have hne : Nat.card (↥N ⧸ N₀') ≠ 1 := by
      intro h1
      apply hirr
      have : N₀' = ⊤ := Subgroup.index_eq_one.mp h1
      intro x hx
      have : (⟨x, hx⟩ : ↥N) ∈ N₀' := by rw [this]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    have : Nat.card (↥N ⧸ N₀') ≠ 0 := Nat.card_pos.ne'
    omega
  have hIodd : Odd (Nat.card (↥N ⧸ N₀')) := by rw [hIidx]; exact hodd
  have hI15 : 15 ≤ Nat.card (↥N ⧸ N₀') := by
    have h1 : Nat.card (↥N ⧸ N₀') % 7 = 1 := by
      have := hmod
      unfold Nat.ModEq at this
      omega
    have h2 := Nat.odd_iff.mp hIodd
    omega
  let r : (↥N ⧸ N₀') → ↥N := fun i => Quotient.out i
  have hr : ∀ i, (QuotientGroup.mk (r i) : ↥N ⧸ N₀') = i := fun i => Quotient.out_eq i
  have hdisj : ∀ i j : (↥N ⧸ N₀'), i ≠ j → ∀ w ∈ conjSub ((r i : ↥N) : G) V₀,
      w ∈ conjSub ((r j : ↥N) : G) V₀ → w = 1 := by
    intro i j hij w hwi hwj
    by_contra hw1
    have h1 := conj_eq_of_ne_bot cb hTI (r i).2 (r j).2 hw1 hwi hwj
    apply hij
    rw [← hr i, ← hr j]
    apply QuotientGroup.eq.mpr
    have h1' : (r j)⁻¹ * (r i) ∈ N₀' := Subgroup.mem_subgroupOf.mpr (by simpa using h1)
    simpa using N₀'.inv_mem h1'
  have hineq := card_le_of_disjoint_conj (S := A) (Q := V₀) (fun i : ↥N ⧸ N₀' => ((r i : ↥N) : G))
    (fun i => (r i).2) cb.V₀_le hdisj
  have hv2 : 2 ≤ Nat.card V₀ := by
    have h1 : 1 < Nat.card V₀ := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro h
      have hz := cb.z_mem
      rw [h, Subgroup.mem_bot] at hz
      exact cb.z_ne hz
    omega
  have hAv := cb.card_A
  have hv : Nat.card V₀ = 2 := by
    have h1 : 15 * (Nat.card V₀ - 1) ≤ Nat.card (↥N ⧸ N₀') * (Nat.card V₀ - 1) :=
      Nat.mul_le_mul_right _ hI15
    omega
  have hA16 : Nat.card A = 16 := by omega
  have hI15' : Nat.card (↥N ⧸ N₀') = 15 := by
    have h1 : Nat.card (↥N ⧸ N₀') * (Nat.card V₀ - 1) ≤ Nat.card A - 1 := hineq
    rw [hv, hA16] at h1
    omega
  refine ⟨hv, hA16, ?_⟩
  let F : (↥N ⧸ N₀') → {u : ↥A // u ≠ 1} := fun i =>
    ⟨⟨((r i : ↥N) : G) * z * ((r i : ↥N) : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (r i).2 z).mp (cb.V₀_le cb.z_mem)⟩, by
      intro h
      have h1 : ((r i : ↥N) : G) * z * ((r i : ↥N) : G)⁻¹ = 1 := congrArg Subtype.val h
      apply cb.z_ne
      calc z = ((r i : ↥N) : G)⁻¹ * (((r i : ↥N) : G) * z * ((r i : ↥N) : G)⁻¹) *
            ((r i : ↥N) : G) := by group
        _ = 1 := by rw [h1]; group⟩
  have hFinj : Function.Injective F := by
    intro i j hij
    by_contra hne
    have h1 : ((r i : ↥N) : G) * z * ((r i : ↥N) : G)⁻¹ =
        ((r j : ↥N) : G) * z * ((r j : ↥N) : G)⁻¹ := by
      have := congrArg (fun s : {u : ↥A // u ≠ 1} => ((s.1 : ↥A) : G)) hij
      simpa [F] using this
    have hw1 : ((r i : ↥N) : G) * z * ((r i : ↥N) : G)⁻¹ ≠ 1 := by
      intro h
      apply cb.z_ne
      calc z = ((r i : ↥N) : G)⁻¹ * (((r i : ↥N) : G) * z * ((r i : ↥N) : G)⁻¹) *
            ((r i : ↥N) : G) := by group
        _ = 1 := by rw [h]; group
    exact hw1 (hdisj i j hne _ (mem_conjSub.mpr ⟨z, cb.z_mem, rfl⟩)
      (mem_conjSub.mpr ⟨z, cb.z_mem, h1.symm⟩))
  have hcardA : Nat.card {u : ↥A // u ≠ 1} = 15 := by
    rw [card_subtype_ne_one, hA16]
  have hFbij : Function.Bijective F :=
    hFinj.bijective_of_nat_card_le (by rw [hcardA, hI15'])
  intro u hu hu1
  obtain ⟨i, hi⟩ := hFbij.2 ⟨⟨u, hu⟩, fun h => hu1 (congrArg Subtype.val h)⟩
  refine ⟨((r i : ↥N) : G), (r i).2, ?_⟩
  have := congrArg (fun s : {u : ↥A // u ≠ 1} => ((s.1 : ↥A) : G)) hi
  simpa [F] using this

end Finite

end CaseBCnt

end CFSG.GH74.Uniqueness.SU.SU8
