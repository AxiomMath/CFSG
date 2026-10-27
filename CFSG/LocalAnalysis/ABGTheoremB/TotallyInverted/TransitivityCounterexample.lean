module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityLocal

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec10

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def Good (σ : Setting G) (r : ℕ) (U V : Subgroup G) : Prop :=
  (∃ c ∈ σ.C, conjSub c U = V) ∨ σ.Ps r 1 ≤ U ⊓ V ∨ σ.Ps r 2 ≤ U ⊓ V

@[expose] noncomputable def mu (σ : Setting G) (U V : Subgroup G) : ℕ :=
  (Nat.card G + 1) * (Nat.card G - Nat.card (U ⊓ V ⊓ σ.C : Subgroup G)) +
    (Nat.card G - Nat.card (U ⊓ V : Subgroup G))

theorem mem_signalizers_iff {H X R : Subgroup G} {p : ℕ} :
    R ∈ signalizers H X p ↔ R ≤ H ∧ IsPGroup p R ∧ X ≤ Subgroup.normalizer (R : Set G) ∧
      R ⊓ X = ⊥ := Iff.rfl

variable [Finite G] {σ : Setting G} {r : ℕ}

theorem mu_lt_of_lt {U V U' V' : Subgroup G}
    (h : Nat.card (U ⊓ V ⊓ σ.C : Subgroup G) < Nat.card (U' ⊓ V' ⊓ σ.C : Subgroup G)) :
    mu σ U' V' < mu σ U V := by
  have h1 := Subgroup.card_le_card_group (U' ⊓ V' ⊓ σ.C)
  unfold mu
  set N := Nat.card G
  set a := Nat.card (U ⊓ V ⊓ σ.C : Subgroup G)
  set a' := Nat.card (U' ⊓ V' ⊓ σ.C : Subgroup G)
  set b := Nat.card (U ⊓ V : Subgroup G)
  set b' := Nat.card (U' ⊓ V' : Subgroup G)
  have e1 : N - a' + 1 ≤ N - a := by omega
  calc (N + 1) * (N - a') + (N - b') < (N + 1) * (N - a') + (N + 1) := by omega
    _ = (N + 1) * (N - a' + 1) := by ring
    _ ≤ (N + 1) * (N - a) := Nat.mul_le_mul_left _ e1
    _ ≤ (N + 1) * (N - a) + (N - b) := Nat.le_add_right _ _

theorem mu_lt_of_le_of_lt {U V U' V' : Subgroup G}
    (h₁ : Nat.card (U ⊓ V ⊓ σ.C : Subgroup G) ≤ Nat.card (U' ⊓ V' ⊓ σ.C : Subgroup G))
    (h₂ : Nat.card (U ⊓ V : Subgroup G) < Nat.card (U' ⊓ V' : Subgroup G)) :
    mu σ U' V' < mu σ U V := by
  have h3 := Subgroup.card_le_card_group (U' ⊓ V')
  unfold mu
  set N := Nat.card G
  set a := Nat.card (U ⊓ V ⊓ σ.C : Subgroup G)
  set a' := Nat.card (U' ⊓ V' ⊓ σ.C : Subgroup G)
  set b := Nat.card (U ⊓ V : Subgroup G)
  set b' := Nat.card (U' ⊓ V' : Subgroup G)
  have e1 : N - a' ≤ N - a := by omega
  calc (N + 1) * (N - a') + (N - b') ≤ (N + 1) * (N - a) + (N - b') :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ e1) _
    _ < (N + 1) * (N - a) + (N - b) := by omega

omit [Finite G] in
theorem good_of_good_conjSub {c : G} (hc : c ∈ σ.C) {U V : Subgroup G}
    (h : Good σ r U (conjSub c V)) : Good σ r U V := by
  rcases h with ⟨c', hc', h⟩ | h | h
  · exact Or.inl ⟨c⁻¹ * c', σ.C.mul_mem (σ.C.inv_mem hc) hc', by
      rw [conjSub_mul, h, conjSub_inv_conjSub]⟩
  · refine Or.inr (Or.inl (le_inf (h.trans inf_le_left) ?_))
    rw [← conjSub_le_conjSub_iff (g := c), conjSub_Ps_of_mem_C r hc]
    exact h.trans inf_le_right
  · refine Or.inr (Or.inr (le_inf (h.trans inf_le_left) ?_))
    rw [← conjSub_le_conjSub_iff (g := c), conjSub_Ps_of_mem_C r hc]
    exact h.trans inf_le_right

theorem Ps_zero_le_of_mem_maximals (Δ : Data σ r) {R₁ : Subgroup G}
    (hR₁ : R₁ ∈ maximals (signalizers σ.N σ.C r)) : σ.Ps r 0 ≤ R₁ := by
  have h := Δ.lemma71 0
  have hN : σ.Ns 0 = σ.N := rfl
  rw [hN] at h
  rw [h] at hR₁
  split_ifs at hR₁ with hq
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR₁
    rcases hR₁ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_left
  · rw [Set.mem_singleton_iff] at hR₁
    rw [hR₁]

omit [Finite G] in
theorem C_le_normalizer_T : σ.C ≤ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) :=
  Subgroup.centralizer_le_normalizer _

omit [Finite G] in
theorem conjSub_mem_maximals_of_mem_C {c : G} (hc : c ∈ σ.C) {W : Subgroup G}
    (hW : W ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)) :
    conjSub c W ∈ maximals (signalizersPerm ⊤ σ.T σ.C r) := by
  have h := conjSub_mem_maximals (g := c) (conjSub_eq_self (C_le_normalizer_T hc))
    (conjSub_eq_self (Subgroup.le_normalizer hc)) hW
  rwa [conjSub_top] at h

omit [Finite G] in
theorem inf_mem_signalizersPerm {U H : Subgroup G} {p : ℕ}
    (hU : U ∈ signalizersPerm ⊤ σ.T σ.C p) (hCH : σ.C ≤ H) (hTH : σ.T ≤ H) :
    U ⊓ H ∈ signalizersPerm H σ.T σ.C p := by
  obtain ⟨-, hUp, hTU, hUT, hperm⟩ := mem_signalizersPerm_iff.mp hU
  rw [mem_signalizersPerm_iff]
  refine ⟨inf_le_right, hUp.to_le inf_le_left, fun t ht => mem_normalizer_inf (hTU ht)
    (Subgroup.le_normalizer (hTH ht)), le_bot_iff.mp (hUT ▸ inf_le_inf_right _ inf_le_left), ?_⟩
  ext g
  constructor
  · rintro ⟨u, hu, c, hc, rfl⟩
    have : u * c ∈ (U : Set G) * (σ.C : Set G) := ⟨u, hu.1, c, hc, rfl⟩
    rw [hperm] at this
    obtain ⟨c', hc', u', hu', huc⟩ := this
    have hu'H : u' ∈ H := by
      have : u' = c'⁻¹ * (u * c) := by rw [← huc]; group
      rw [this]
      exact H.mul_mem (H.inv_mem (hCH hc')) (H.mul_mem hu.2 (hCH hc))
    exact ⟨c', hc', u', ⟨hu', hu'H⟩, huc⟩
  · rintro ⟨c, hc, u, hu, rfl⟩
    have : c * u ∈ (σ.C : Set G) * (U : Set G) := ⟨c, hc, u, hu.1, rfl⟩
    rw [← hperm] at this
    obtain ⟨u', hu', c', hc', huc⟩ := this
    have hu'H : u' ∈ H := by
      have : u' = c * u * c'⁻¹ := by rw [← huc]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (hCH hc) hu.2) (H.inv_mem (hCH hc'))
    exact ⟨u', ⟨hu', hu'H⟩, c', hc', huc⟩

theorem exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hB : IsPGroup p B) (hAB : A < B) :
    ∃ y ∈ B, y ∉ A ∧ y ∈ Subgroup.normalizer (A : Set G) := by
  have : Group.IsNilpotent B := hB.isNilpotent
  have hlt : A.subgroupOf B < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hAB.ne
    apply le_antisymm hAB.le
    intro x hx
    have : (⟨x, hx⟩ : B) ∈ A.subgroupOf B := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨y, hyN, hyA⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (A.subgroupOf B) hlt)
  refine ⟨y, y.2, hyA, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ B
  · have := (Subgroup.mem_normalizer_iff.mp hyN) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · have h1 : g ∉ A := fun h => hg (hAB.le h)
    have h2 : (y : G) * g * (y : G)⁻¹ ∉ A := by
      intro h
      apply hg
      have := B.mul_mem (B.mul_mem (B.inv_mem y.2) (hAB.le h)) y.2
      simpa [mul_assoc] using this
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem star_facts (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ) {U : Subgroup G}
    (hU : U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)) (hU1 : U ≠ ⊥) :
    IsSylowOf r (U ⊓ σ.C) σ.C ∧ U = pCoreIn r (U ⊔ σ.C) ⊔ (U ⊓ σ.C) ∧
      pCoreIn r (U ⊔ σ.C) ⊓ σ.C = ⊥ ∧
      ∀ u ∈ U, ∀ t ∈ σ.T, u * t * u⁻¹ * t⁻¹ ∈ pCoreIn r (U ⊔ σ.C) := by
  have := fact_prime Δ
  have hU' := mem_maximals_of_le hU (le_sup_left : U ≤ U ⊔ σ.C)
  have hO := homni (U ⊔ σ.C) le_sup_right U hU'
  obtain ⟨-, hUp, -, -, -⟩ := mem_signalizersPerm_iff.mp hU.1
  have hUO : U ≤ oddCoreIn (U ⊔ σ.C) :=
    le_oddCoreIn_of_hasNormalPComplement hO.part_v.1 le_sup_left
      (odd_card_of_isPGroup (odd_r Δ) hUp)
  have hOne : oddCoreIn (U ⊔ σ.C) ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUO))
  have heq := hO.part_iii_a hOne
  set Us := pCoreIn r (U ⊔ σ.C) with hUsdef
  have hNUs : ∀ {g : G}, g ∈ U ⊔ σ.C → g ∈ Subgroup.normalizer (Us : Set G) := fun hg =>
    le_normalizer_pCoreIn r _ hg
  have hUsC : Us ⊓ σ.C = ⊥ := by
    rw [← le_bot_iff, ← Δ.Op_C]
    apply le_pCoreIn inf_le_right
    · intro c hc
      exact mem_normalizer_inf (hNUs (Subgroup.mem_sup_right hc)) (Subgroup.le_normalizer hc)
    · exact (isPGroup_pCoreIn r _).to_le inf_le_left
  refine ⟨?_, heq, hUsC, ?_⟩
  · obtain ⟨R₀, hR₀, hR₀U⟩ := hO.part_ii_a
    have := hR₀.eq_of_le (le_inf hR₀U hR₀.le) inf_le_right (hUp.to_le inf_le_left)
    rw [this]
    exact hR₀
  · intro u hu t ht
    have hPN : U ⊓ σ.C ≤ Subgroup.normalizer (Us : Set G) := fun p hp =>
      hNUs (Subgroup.mem_sup_right hp.2)
    rw [heq, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Us (U ⊓ σ.C) hPN]
      at hu
    obtain ⟨a, ha, p, hp, rfl⟩ := hu
    have htp : p * t * p⁻¹ = t := by
      rw [← (Subgroup.mem_centralizer_iff.mp hp.2) t ht]
      group
    have htUs : t ∈ Subgroup.normalizer (Us : Set G) :=
      hNUs (Subgroup.mem_sup_right (σ.T_le_C hσ ht))
    have e : a * p * t * (a * p)⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by
      calc a * p * t * (a * p)⁻¹ * t⁻¹ = a * (p * t * p⁻¹) * a⁻¹ * t⁻¹ := by group
        _ = a * (t * a⁻¹ * t⁻¹) := by rw [htp]; group
    rw [e]
    exact Us.mul_mem ha ((Subgroup.mem_normalizer_iff.mp htUs _).mp (Us.inv_mem ha))

theorem lt_inf_normalizer [Fact r.Prime] {U V P Us Rs : Subgroup G} (hUeq : U = Us ⊔ P)
    (hPC : P ≤ σ.C) (hUsC : Us ⊓ σ.C = ⊥) (hRsUs : Rs ≤ Us) (hUV : U ⊓ V = P ⊔ Rs)
    (hPRs : P ≤ Subgroup.normalizer (Rs : Set G)) (hUs : IsPGroup r Us) (hUV' : ¬ U ≤ V) :
    U ⊓ V < U ⊓ Subgroup.normalizer (Rs : Set G) := by
  have hle : U ⊓ V ≤ U ⊓ Subgroup.normalizer (Rs : Set G) :=
    le_inf inf_le_left (hUV ▸ sup_le hPRs Subgroup.le_normalizer)
  have hUsUV : ∀ y ∈ Us, y ∈ U ⊓ V → y ∈ Rs := by
    intro y hyUs hyUV
    rw [hUV, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Rs hPRs] at hyUV
    obtain ⟨p, hp, z, hz, rfl⟩ := hyUV
    have hpUs : p ∈ Us := by
      have := Us.mul_mem hyUs (Us.inv_mem (hRsUs hz))
      simpa using this
    have hp1 : p ∈ Us ⊓ σ.C := ⟨hpUs, hPC hp⟩
    rw [hUsC, Subgroup.mem_bot] at hp1
    dsimp only
    rw [hp1, one_mul]
    exact hz
  have hlt : Rs < Us := by
    refine lt_of_le_of_ne hRsUs fun h => hUV' ?_
    rw [hUeq, ← h]
    have h1 : Rs ≤ U ⊓ V := hUV ▸ le_sup_right
    have h2 : P ≤ U ⊓ V := hUV ▸ le_sup_left
    exact (sup_le h1 h2).trans inf_le_right
  obtain ⟨y, hyUs, hyRs, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hUs hlt
  have hyU : y ∈ U := by rw [hUeq]; exact Subgroup.mem_sup_left hyUs
  refine lt_of_le_of_ne hle fun h => hyRs (hUsUV y hyUs ?_)
  rw [h]
  exact ⟨hyU, hyN⟩

theorem no_common_overgroup (h92 : NotPGroupP σ r) {R₁ U V A B X : Subgroup G}
    (hP₁R₁ : σ.Ps r 0 ≤ R₁) (hU : U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r))
    (hV : V ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)) (hR₁U : R₁ ≤ U) (hR₁V : R₁ ≤ V)
    (hbad : ¬ Good σ r U V)
    (IH : ∀ U' ∈ maximals (signalizersPerm ⊤ σ.T σ.C r),
      ∀ V' ∈ maximals (signalizersPerm ⊤ σ.T σ.C r), R₁ ≤ U' → R₁ ≤ V' →
        mu σ U' V' < mu σ U V → Good σ r U' V')
    (hAU : A ≤ U) (hBV : B ≤ V) (hA : U ⊓ V < A) (hB : U ⊓ V < B)
    (hX : X ∈ signalizersPerm ⊤ σ.T σ.C r) (hAX : A ≤ X) (hBX : B ≤ X) : False := by
  obtain ⟨X', hX', hXX'⟩ := exists_mem_maximals_ge hX
  have hR₁X' : R₁ ≤ X' := (le_inf hR₁U hR₁V).trans (hA.le.trans (hAX.trans hXX'))
  have hUX : U ⊓ V < U ⊓ X' := lt_of_lt_of_le hA (le_inf hAU (hAX.trans hXX'))
  have hXV : U ⊓ V < X' ⊓ V := lt_of_lt_of_le hB (le_inf (hBX.trans hXX') hBV)
  have hgUX : Good σ r U X' := IH U hU X' hX' hR₁U hR₁X' (mu_lt_of_le_of_lt
    (Subgroup.card_le_of_le (inf_le_inf_right _ hUX.le)) (Subgroup.card_lt_of_lt hUX))
  have hgXV : Good σ r X' V := IH X' hX' V hV hR₁X' hR₁V (mu_lt_of_le_of_lt
    (Subgroup.card_le_of_le (inf_le_inf_right _ hXV.le)) (Subgroup.card_lt_of_lt hXV))
  have hUX' : σ.Ps r 1 ≤ U ⊓ X' ∨ σ.Ps r 2 ≤ U ⊓ X' := by
    rcases hgUX with ⟨c, hc, hcUX⟩ | h | h
    · exfalso
      rcases hgXV with ⟨c', hc', hcXV⟩ | h | h
      · exact hbad (Or.inl ⟨c' * c, σ.C.mul_mem hc' hc, by rw [conjSub_mul, hcUX, hcXV]⟩)
      · refine hbad (Or.inr (Or.inl (le_inf ?_ (h.trans inf_le_right))))
        rw [← conjSub_le_conjSub_iff (g := c), conjSub_Ps_of_mem_C r hc, hcUX]
        exact h.trans inf_le_left
      · refine hbad (Or.inr (Or.inr (le_inf ?_ (h.trans inf_le_right))))
        rw [← conjSub_le_conjSub_iff (g := c), conjSub_Ps_of_mem_C r hc, hcUX]
        exact h.trans inf_le_left
    · exact Or.inl h
    · exact Or.inr h
  have hXV' : σ.Ps r 1 ≤ X' ⊓ V ∨ σ.Ps r 2 ≤ X' ⊓ V := by
    rcases hgXV with ⟨c, hc, hcXV⟩ | h | h
    · exfalso
      rcases hUX' with h | h
      · refine hbad (Or.inr (Or.inl (le_inf (h.trans inf_le_left) ?_)))
        rw [← hcXV, ← conjSub_Ps_of_mem_C r hc 1]
        exact conjSub_mono (h.trans inf_le_right)
      · refine hbad (Or.inr (Or.inr (le_inf (h.trans inf_le_left) ?_)))
        rw [← hcXV, ← conjSub_Ps_of_mem_C r hc 2]
        exact conjSub_mono (h.trans inf_le_right)
    · exact Or.inl h
    · exact Or.inr h
  have hP₁X : σ.Ps r 0 ≤ X' := hP₁R₁.trans hR₁X'
  apply h92
  obtain ⟨-, hXp, -, -, -⟩ := mem_signalizersPerm_iff.mp hX'.1
  apply hXp.to_le
  rcases hUX' with h₁ | h₁ <;> rcases hXV' with h₂ | h₂
  · exact absurd (Or.inr (Or.inl (le_inf (h₁.trans inf_le_left) (h₂.trans inf_le_right))))
      hbad
  · exact sup_le (sup_le hP₁X (h₁.trans inf_le_right)) (h₂.trans inf_le_left)
  · exact sup_le (sup_le hP₁X (h₂.trans inf_le_left)) (h₁.trans inf_le_right)
  · exact absurd (Or.inr (Or.inr (le_inf (h₁.trans inf_le_left) (h₂.trans inf_le_right))))
      hbad

omit [Finite G] in
theorem conjSub_lt_conjSub {g : G} {A B : Subgroup G} (h : A < B) : conjSub g A < conjSub g B :=
  lt_of_le_of_ne (conjSub_mono h.le) fun he => h.ne (conjSub_injective g he)

theorem not_conj_of_overgroups [Fact r.Prime] (h92 : NotPGroupP σ r)
    {R₁ U V P Rs X Y : Subgroup G} (hR₁ : R₁ ∈ maximals (signalizers σ.N σ.C r))
    (hP₁R₁ : σ.Ps r 0 ≤ R₁) (hU : U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r))
    (hV : V ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)) (hR₁U : R₁ ≤ U) (hR₁V : R₁ ≤ V)
    (hbad : ¬ Good σ r U V)
    (IH : ∀ U' ∈ maximals (signalizersPerm ⊤ σ.T σ.C r),
      ∀ V' ∈ maximals (signalizersPerm ⊤ σ.T σ.C r), R₁ ≤ U' → R₁ ≤ V' →
        mu σ U' V' < mu σ U V → Good σ r U' V')
    (hPU : U ⊓ σ.C = P) (hPsyl : IsSylowOf r P σ.C) (hUV : U ⊓ V = P ⊔ Rs)
    (hCRs : σ.C ≤ Subgroup.normalizer (Rs : Set G))
    (hA : U ⊓ V < U ⊓ Subgroup.normalizer (Rs : Set G))
    (hB : U ⊓ V < V ⊓ Subgroup.normalizer (Rs : Set G))
    (hX : X ∈ signalizersPerm (Subgroup.normalizer (Rs : Set G)) σ.T σ.C r)
    (hY : Y ∈ signalizersPerm (Subgroup.normalizer (Rs : Set G)) σ.T σ.C r)
    (hUX : U ⊓ Subgroup.normalizer (Rs : Set G) ≤ X)
    (hVY : V ⊓ Subgroup.normalizer (Rs : Set G) ≤ Y) :
    ¬ ∃ c ∈ σ.C, conjSub c Y = X := by
  rintro ⟨c, hc, hcYX⟩
  set H := Subgroup.normalizer (Rs : Set G) with hH
  have hPUV : P ≤ U ⊓ V := hUV ▸ le_sup_left
  obtain ⟨-, hXp, -, -, -⟩ := mem_signalizersPerm_iff.mp hX
  obtain ⟨-, hYp, -, -, -⟩ := mem_signalizersPerm_iff.mp hY
  have hXC : X ⊓ σ.C = P := hPsyl.eq_of_le (le_inf ((hPUV.trans hA.le).trans hUX) hPsyl.le)
    inf_le_right (hXp.to_le inf_le_left)
  have hYC : Y ⊓ σ.C = P := hPsyl.eq_of_le (le_inf ((hPUV.trans hB.le).trans hVY) hPsyl.le)
    inf_le_right (hYp.to_le inf_le_left)
  have hcC : conjSub c σ.C = σ.C := conjSub_eq_self (Subgroup.le_normalizer hc)
  have hcP : conjSub c P = P := by
    calc conjSub c P = conjSub c (Y ⊓ σ.C) := by rw [hYC]
      _ = X ⊓ σ.C := by rw [conjSub_inf, hcYX, hcC]
      _ = P := hXC
  have hcRs : conjSub c Rs = Rs := conjSub_eq_self (hCRs hc)
  have hcH : conjSub c H = H := by
    rw [hH, conjSub_normalizer, hcRs]
  have hcUV : conjSub c (U ⊓ V) = U ⊓ V := by rw [hUV, conjSub_sup, hcP, hcRs]
  have hV' := conjSub_mem_maximals_of_mem_C hc hV
  have hR₁V' : R₁ ≤ conjSub c V := by
    rw [← conjSub_eq_self ((mem_signalizers_iff.mp hR₁.1).2.2.1 hc)]
    exact conjSub_mono hR₁V
  have hbad' : ¬ Good σ r U (conjSub c V) := fun h => hbad (good_of_good_conjSub hc h)
  have hUVle : U ⊓ V ≤ U ⊓ conjSub c V :=
    le_inf inf_le_left (hcUV ▸ conjSub_mono inf_le_right)
  have hUV'C : U ⊓ conjSub c V ⊓ σ.C = U ⊓ V ⊓ σ.C := by
    apply le_antisymm
    · calc U ⊓ conjSub c V ⊓ σ.C ≤ U ⊓ σ.C := inf_le_inf_right _ inf_le_left
        _ = P := hPU
        _ ≤ U ⊓ V ⊓ σ.C := le_inf hPUV hPsyl.le
    · exact inf_le_inf_right _ hUVle
  have hUV'eq : U ⊓ conjSub c V = U ⊓ V := by
    by_contra hne
    have hlt : U ⊓ V < U ⊓ conjSub c V := lt_of_le_of_ne hUVle (Ne.symm hne)
    exact hbad' (IH U hU _ hV' hR₁U hR₁V' (mu_lt_of_le_of_lt (hUV'C ▸ le_rfl)
      (Subgroup.card_lt_of_lt hlt)))
  have hmu : mu σ U (conjSub c V) = mu σ U V := by unfold mu; rw [hUV'eq]
  have hBc : conjSub c (V ⊓ H) = conjSub c V ⊓ H := by rw [conjSub_inf, hcH]
  refine no_common_overgroup h92 hP₁R₁ hU hV' hR₁U hR₁V' hbad'
    (fun U' hU' V'' hV'' h1 h2 hlt => IH U' hU' V'' hV'' h1 h2 (hmu ▸ hlt))
    (inf_le_left : U ⊓ H ≤ U) (inf_le_left : conjSub c V ⊓ H ≤ conjSub c V)
    (hUV'eq ▸ hA) ?_ (signalizersPerm_mono le_top hX) hUX ?_
  · rw [hUV'eq, ← hcUV, ← hBc]
    exact conjSub_lt_conjSub hB
  · rw [← hBc, ← hcYX]
    exact conjSub_mono hVY

theorem exists_comp_not_mem (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ)
    {R₁ X Y P Rs : Subgroup G} (hR₁ : R₁ ∈ maximals (signalizers σ.N σ.C r))
    (hR₁Rs : R₁ ≤ Rs) (hRs : IsPGroup r Rs) (hCRs : σ.C ≤ Subgroup.normalizer (Rs : Set G))
    (hX : X ∈ maximals (signalizersPerm (Subgroup.normalizer (Rs : Set G)) σ.T σ.C r))
    (hY : Y ∈ maximals (signalizersPerm (Subgroup.normalizer (Rs : Set G)) σ.T σ.C r))
    (hR₁X : R₁ ≤ X) (hXC : X ⊓ σ.C = P) (hPY : P ≤ Y)
    (hXY : ¬ ∃ c ∈ σ.C, conjSub c X = Y) :
    ∃ j : Fin 3, j ≠ 0 ∧ ∃ u ∈ comp σ X j, u ∉ oddCoreIn (Subgroup.normalizer (Rs : Set G)) := by
  have := fact_prime Δ
  by_contra hcon
  push Not at hcon
  set H := Subgroup.normalizer (Rs : Set G) with hH
  set O := oddCoreIn H with hO
  have hRsO : Rs ≤ O := CFSG.ABGTheoremB.le_oddCoreIn Subgroup.le_normalizer le_rfl
    (odd_card_of_isPGroup (odd_r Δ) hRs)
  have hP₁R₁ := Ps_zero_le_of_mem_maximals Δ hR₁
  have hOne : O ≠ ⊥ := fun h =>
    Ps_zero_ne_bot Δ (le_bot_iff.mp (h ▸ (hP₁R₁.trans (hR₁Rs.trans hRsO))))
  obtain ⟨hR₁N, hR₁p, hCR₁, hR₁C⟩ := mem_signalizers_iff.mp hR₁.1
  obtain ⟨hXH, hXp, hTX, -, -⟩ := mem_signalizersPerm_iff.mp hX.1
  have hXodd : Odd (Nat.card X) := odd_card_of_isPGroup (odd_r Δ) hXp
  have hXO := homni H hCRs X hX
  obtain ⟨V₀, hV₀, hCV₀, -⟩ := hXO.part_i_b 0
  have hV₀X : V₀ ≤ X := fun v hv => by
    rw [← SetLike.mem_coe, hV₀] at hv
    exact hv.1
  have hV₀sig : V₀ ∈ signalizers σ.N σ.C r := by
    refine ⟨fun v hv => ?_, hXp.to_le hV₀X, hCV₀, ?_⟩
    · rw [← SetLike.mem_coe, hV₀] at hv
      rw [Setting.mem_N_iff]
      exact hv.2.1.symm
    · rw [eq_bot_iff]
      intro v hv
      have hvc : v ∈ comp σ X 0 := by rw [← hV₀]; exact hv.1
      obtain ⟨hvX, -, hinv⟩ := hvc
      have hinv' : σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ := hinv
      have hcomm : σ.x₂ * v * σ.x₂⁻¹ = v := by
        rw [(Subgroup.mem_centralizer_iff.mp hv.2) σ.x₂ σ.x₂_mem_T]
        group
      rw [Subgroup.mem_bot]
      apply eq_one_of_eq_inv_of_odd hXodd hvX
      rw [← hinv']
      exact hcomm.symm
  have hR₁odd : Odd (Nat.card R₁) := odd_card_of_isPGroup (odd_r Δ) hR₁p
  have hR₁V₀ : R₁ ≤ V₀ := by
    intro u hu
    have h0 := subset_comp_zero hσ hR₁odd ((σ.T_le_C hσ).trans hCR₁) hR₁N hR₁C hu
    rw [← SetLike.mem_coe, hV₀]
    exact ⟨hR₁X hu, h0.2⟩
  have hV₀R₁ : V₀ = R₁ := hR₁.2 V₀ hV₀sig hR₁V₀
  have hcomp : ∀ i, comp σ X i ⊆ O := by
    intro i u hu
    by_cases hi : i = 0
    · subst hi
      rw [← hV₀, hV₀R₁] at hu
      exact hRsO (hR₁Rs hu)
    · exact hcon i hi u hu
  have hXle : X ≤ P ⊔ O := hXC ▸ le_sup_of_comp_le hσ hXodd hTX hcomp
  obtain ⟨m, hmMH, hm⟩ := hXO.part_iv hOne Y hY
  have hmO : conjSub m⁻¹ O = O := conjSub_oddCoreIn (H.inv_mem hmMH.2)
  have hYle : Y ≤ conjSub m⁻¹ P ⊔ O := by
    rw [← hmO, ← conjSub_sup, ← conjSub_inv_conjSub m Y, hm]
    exact conjSub_mono hXle
  have hPO : P ⊔ O ≤ conjSub m⁻¹ P ⊔ O := sup_le (hPY.trans hYle) le_sup_right
  have hcard : Nat.card (conjSub m⁻¹ P ⊔ O : Subgroup G) = Nat.card (P ⊔ O : Subgroup G) := by
    have e : conjSub m⁻¹ P ⊔ O = conjSub m⁻¹ (P ⊔ O) := by rw [conjSub_sup, hmO]
    rw [e, card_conjSub]
  have heq : P ⊔ O = conjSub m⁻¹ P ⊔ O := Subgroup.eq_of_le_of_card_ge hPO hcard.le
  have hYX : Y ≤ X ⊔ O := by
    rw [← heq] at hYle
    exact hYle.trans (sup_le_sup_right (hXC ▸ inf_le_left) _)
  exact hXY (exists_conj_of_le_sup_oddCoreIn hσ homni hCRs hOne hX hY hYX)

theorem false_of_minimal (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (h92 : NotPGroupP σ r) (hQ : QGroupFourFusion G)
    (hD : DGroupFourFusion G) {R₁ U V : Subgroup G}
    (hR₁ : R₁ ∈ maximals (signalizers σ.N σ.C r))
    (hU : U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r))
    (hV : V ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)) (hR₁U : R₁ ≤ U) (hR₁V : R₁ ≤ V)
    (hbad : ¬ Good σ r U V)
    (IH : ∀ U' ∈ maximals (signalizersPerm ⊤ σ.T σ.C r),
      ∀ V' ∈ maximals (signalizersPerm ⊤ σ.T σ.C r), R₁ ≤ U' → R₁ ≤ V' →
        mu σ U' V' < mu σ U V → Good σ r U' V') : False := by
  have := fact_prime Δ
  have hodd := odd_r Δ
  have hP₁R₁ := Ps_zero_le_of_mem_maximals Δ hR₁
  have hR₁ne : R₁ ≠ ⊥ := fun h => Ps_zero_ne_bot Δ (le_bot_iff.mp (h ▸ hP₁R₁))
  have hUne : U ≠ ⊥ := fun h => hR₁ne (le_bot_iff.mp (h ▸ hR₁U))
  have hVne : V ≠ ⊥ := fun h => hR₁ne (le_bot_iff.mp (h ▸ hR₁V))
  obtain ⟨hUsyl, hUeq, hUsC, hUcomm⟩ := star_facts hσ Δ homni hU hUne
  obtain ⟨hVsyl, hVeq, hVsC, hVcomm⟩ := star_facts hσ Δ homni hV hVne
  obtain ⟨hR₁N, hR₁p, hCR₁, hR₁C⟩ := mem_signalizers_iff.mp hR₁.1
  obtain ⟨-, hUp, hTU, -, -⟩ := mem_signalizersPerm_iff.mp hU.1
  obtain ⟨-, hVp, hTV, -, -⟩ := mem_signalizersPerm_iff.mp hV.1
  have hPeq : U ⊓ σ.C = V ⊓ σ.C := by
    obtain ⟨c, hcC, hc⟩ := exists_mem_conjSub_eq hVsyl hUsyl
    have hV' := conjSub_mem_maximals_of_mem_C hcC hV
    have hR₁V' : R₁ ≤ conjSub c V := by
      rw [← conjSub_eq_self (hCR₁ hcC)]
      exact conjSub_mono hR₁V
    have hV'C : conjSub c V ⊓ σ.C = U ⊓ σ.C := by
      rw [← hc, conjSub_inf, conjSub_eq_self (Subgroup.le_normalizer hcC)]
    have hUV'C : U ⊓ conjSub c V ⊓ σ.C = U ⊓ σ.C := by
      rw [inf_assoc, hV'C, ← inf_assoc, inf_idem]
    have hge : Nat.card (U ⊓ σ.C : Subgroup G) ≤ Nat.card (U ⊓ V ⊓ σ.C : Subgroup G) := by
      by_contra hlt
      push Not at hlt
      apply hbad
      apply good_of_good_conjSub hcC
      apply IH U hU _ hV' hR₁U hR₁V'
      apply mu_lt_of_lt
      rw [hUV'C]
      exact hlt
    have heq : U ⊓ V ⊓ σ.C = U ⊓ σ.C :=
      Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ inf_le_left) hge
    have hUCV : U ⊓ σ.C ≤ V ⊓ σ.C := by
      rw [← heq]
      exact inf_le_inf_right _ inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hUCV (by rw [hUsyl.card_eq, hVsyl.card_eq])
  set P := U ⊓ σ.C with hPdef
  set Us := pCoreIn r (U ⊔ σ.C) with hUsdef
  set Vs := pCoreIn r (V ⊔ σ.C) with hVsdef
  set Rs := Us ⊓ Vs with hRsdef
  have hPU : P ≤ U := inf_le_left
  have hPV : P ≤ V := hPeq ▸ inf_le_left
  have hPC : P ≤ σ.C := inf_le_right
  have hUsU : Us ≤ U := le_sup_left.trans hUeq.ge
  have hVsV : Vs ≤ V := le_sup_left.trans hVeq.ge
  have hRsUV : Rs ≤ U ⊓ V := inf_le_inf hUsU hVsV
  have hRsp : IsPGroup r Rs := (isPGroup_pCoreIn r _).to_le inf_le_left
  have hCRs : σ.C ≤ Subgroup.normalizer (Rs : Set G) := fun c hc =>
    mem_normalizer_inf (le_normalizer_pCoreIn r _ (Subgroup.mem_sup_right hc))
      (le_normalizer_pCoreIn r _ (Subgroup.mem_sup_right hc))
  have hcommR : ∀ k ∈ U ⊓ V, ∀ t ∈ σ.T, k * t * k⁻¹ * t⁻¹ ∈ Rs := fun k hk t ht =>
    ⟨hUcomm k hk.1 t ht, hVcomm k hk.2 t ht⟩
  have hUVodd : Odd (Nat.card (U ⊓ V : Subgroup G)) :=
    odd_card_of_isPGroup hodd (hUp.to_le inf_le_left)
  have hTUV : σ.T ≤ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (hTU ht) (hTV ht)
  have hUVC : U ⊓ V ⊓ σ.C = P := by
    rw [inf_right_comm, ← hPdef]
    exact inf_eq_left.mpr hPV
  have hUVeq : U ⊓ V = P ⊔ Rs := by
    apply le_antisymm
    · have := le_sup_of_comp_le hσ hUVodd hTUV fun i u hu => mem_of_mem_comp hUVodd hcommR hu
      rwa [hUVC] at this
    · exact sup_le (le_inf hPU hPV) hRsUV
  have hR₁odd : Odd (Nat.card R₁) := odd_card_of_isPGroup hodd hR₁p
  have hR₁Rs : R₁ ≤ Rs := le_of_comp_le_of_inf_C hσ hR₁odd ((σ.T_le_C hσ).trans hCR₁) hR₁C
    fun i u hu => mem_of_mem_comp hR₁odd
      (fun k hk t ht => hcommR k ⟨hR₁U hk, hR₁V hk⟩ t ht) hu
  have hP₁Rs : σ.Ps r 0 ≤ Rs := hP₁R₁.trans hR₁Rs
  set H := Subgroup.normalizer (Rs : Set G) with hH
  have hPRs : P ≤ H := hPC.trans hCRs
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCRs
  have hUnV : ¬ U ≤ V := fun h =>
    hbad (Or.inl ⟨1, σ.C.one_mem, by rw [conjSub_one]; exact (hU.2 V hV.1 h).symm⟩)
  have hVnU : ¬ V ≤ U := fun h =>
    hbad (Or.inl ⟨1, σ.C.one_mem, by rw [conjSub_one]; exact hV.2 U hU.1 h⟩)
  have hVeq' : V = Vs ⊔ P := by rw [hPeq]; exact hVeq
  have hA : U ⊓ V < U ⊓ H := lt_inf_normalizer hUeq hPC hUsC inf_le_left hUVeq hPRs
    (isPGroup_pCoreIn r _) hUnV
  have hB : U ⊓ V < V ⊓ H := by
    have := lt_inf_normalizer hVeq' hPC hVsC inf_le_right (by rw [inf_comm]; exact hUVeq) hPRs
      (isPGroup_pCoreIn r _) hVnU
    rwa [inf_comm V U] at this
  obtain ⟨X, hX, hUX⟩ := exists_mem_maximals_ge (inf_mem_signalizersPerm hU.1 hCRs hTH)
  obtain ⟨Y, hY, hVY⟩ := exists_mem_maximals_ge (inf_mem_signalizersPerm hV.1 hCRs hTH)
  have h106 := not_conj_of_overgroups h92 hR₁ hP₁R₁ hU hV hR₁U hR₁V hbad IH rfl hUsyl hUVeq
    hCRs hA hB hX.1 hY.1 hUX hVY
  have hXY : ¬ ∃ c ∈ σ.C, conjSub c X = Y := by
    rintro ⟨c, hc, hcXY⟩
    exact h106 ⟨c⁻¹, σ.C.inv_mem hc, by rw [← hcXY, conjSub_inv_conjSub]⟩
  have hPUV : P ≤ U ⊓ V := le_inf hPU hPV
  obtain ⟨-, hXp, -, -, -⟩ := mem_signalizersPerm_iff.mp hX.1
  have hXC : X ⊓ σ.C = P := hUsyl.eq_of_le (le_inf ((hPUV.trans hA.le).trans hUX) hPC)
    inf_le_right (hXp.to_le inf_le_left)
  have hPY : P ≤ Y := (hPUV.trans hB.le).trans hVY
  have hR₁X : R₁ ≤ X := ((le_inf hR₁U hR₁V).trans hA.le).trans hUX
  have h107 := exists_comp_not_mem hσ Δ homni hR₁ hR₁Rs hRsp hCRs hX hY hR₁X hXC hPY hXY
  have hc : Config σ r Rs X Y :=
    ⟨hRsp, hP₁Rs, hCRs, fun h => hbad (Or.inr (Or.inl (h.trans hRsUV))),
      fun h => hbad (Or.inr (Or.inr (h.trans hRsUV))), hX, hY, hXY, h107⟩
  exact hc.false hσ hF Δ homni h92 hQ hD

end CFSG.ABGTheoremB.TotallyInverted.Sec10
