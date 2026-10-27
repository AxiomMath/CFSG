module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaWords
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsOddBC

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G]

theorem conj_mul_conj_mod {a b s ζ : G} (hζ : ζ * ζ = 1) (hbζ : b * ζ * b⁻¹ = ζ)
    (ha : a * s * a⁻¹ = s ∨ a * s * a⁻¹ = s * ζ) (hb : b * s * b⁻¹ = s ∨ b * s * b⁻¹ = s * ζ) :
    b * a * s * (b * a)⁻¹ = s ∨ b * a * s * (b * a)⁻¹ = s * ζ := by
  rw [show b * a * s * (b * a)⁻¹ = b * (a * s * a⁻¹) * b⁻¹ by group]
  rcases ha with ha | ha <;> rw [ha]
  · exact hb
  · rw [show b * (s * ζ) * b⁻¹ = b * s * b⁻¹ * (b * ζ * b⁻¹) by group, hbζ]
    rcases hb with hb | hb <;> rw [hb]
    · exact Or.inr rfl
    · exact Or.inl (by rw [mul_assoc, hζ, mul_one])

theorem conj_inv_conj_mod {a s ζ : G} (hζ : ζ * ζ = 1) (haζ : a * ζ * a⁻¹ = ζ)
    (ha : a * s * a⁻¹ = s ∨ a * s * a⁻¹ = s * ζ) :
    a⁻¹ * s * a⁻¹⁻¹ = s ∨ a⁻¹ * s * a⁻¹⁻¹ = s * ζ := by
  rw [inv_inv]
  rcases ha with ha | ha
  · left
    calc a⁻¹ * s * a = a⁻¹ * (a * s * a⁻¹) * a := by rw [ha]
      _ = s := by group
  · right
    have h1 : a * (s * ζ) * a⁻¹ = s := by
      rw [show a * (s * ζ) * a⁻¹ = a * s * a⁻¹ * (a * ζ * a⁻¹) by group, ha, haζ, mul_assoc, hζ,
        mul_one]
    calc a⁻¹ * s * a = a⁻¹ * (a * (s * ζ) * a⁻¹) * a := by rw [h1]
      _ = s * ζ := by group

@[expose] noncomputable def e1NBar (Z : Subgroup G) [Z.Normal] (u m y x : G) :
    Subgroup (G ⧸ Z) :=
  e1M0 Z (u * (x * u * x⁻¹)) ⊓ Subgroup.normalizer (e1RBar Z u m y x : Set (G ⧸ Z))

@[expose] noncomputable def e1KBar (Z : Subgroup G) [Z.Normal] (u m y x : G) :
    Subgroup (G ⧸ Z) :=
  e1RBar Z u m y x ⊔
    (e1M0 Z (u * (x * u * x⁻¹)) ⊓ Subgroup.centralizer (e1RBar Z u m y x : Set (G ⧸ Z)))

variable {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

omit hb [Finite G] in
theorem conj_mem_of_mem_e1NBar {n : G ⧸ Z} (hn : n ∈ e1NBar Z u m y x) :
    ∀ s ∈ e1RBar Z u m y x, n * s * n⁻¹ ∈ e1RBar Z u m y x :=
  fun s hs => (Subgroup.mem_normalizer_iff.mp hn.2 s).mp hs

theorem conj_forty_of_mem_e1NBar {n : G ⧸ Z} (hn : n ∈ e1NBar Z u m y x) :
    n * caseC3Word Z u m y x 40 * n⁻¹ = caseC3Word Z u m y x 40 :=
  hb.conj_forty_of_normalizes (conj_mem_of_mem_e1NBar hn)

theorem forty_mul_self : caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 = 1 :=
  hb.caseC3Word_mul_self_eq_one_iff.mpr c3Mul_forty_forty

theorem conj_of_mem_e1RBar {r s : G ⧸ Z} (hr : r ∈ e1RBar Z u m y x)
    (hs : s ∈ e1RBar Z u m y x) :
    r * s * r⁻¹ = s ∨ r * s * r⁻¹ = s * caseC3Word Z u m y x 40 := by
  have hz : caseC3Word Z u m y x 40 * r = r * caseC3Word Z u m y x 40 :=
    (hb.forall_commute_e1RBar_iff hb.forty_mem_e1RBar).mpr (Or.inr rfl) r hr
  rcases hb.commute_or_of_mem_e1RBar hr hs with h | h <;> rw [h]
  · exact Or.inl (mul_inv_cancel_right s r)
  · right
    rw [mul_assoc s r, ← hz]
    group

theorem e1RBar_le_e1NBar : e1RBar Z u m y x ≤ e1NBar Z u m y x :=
  le_inf hb.e1RBar_le_e1M0 (Subgroup.le_normalizer)

omit hb [Finite G] in
theorem e1NBar_le_e1M0 : e1NBar Z u m y x ≤ e1M0 Z (u * (x * u * x⁻¹)) := inf_le_left

omit hb [Finite G] in
theorem centralizer_le_e1NBar :
    e1M0 Z (u * (x * u * x⁻¹)) ⊓ Subgroup.centralizer (e1RBar Z u m y x : Set (G ⧸ Z)) ≤
      e1NBar Z u m y x := by
  refine fun c hc => ⟨hc.1, Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [← Subgroup.mem_centralizer_iff.mp hc.2 s hs, mul_inv_cancel_right]
    exact hs
  · have h := Subgroup.mem_centralizer_iff.mp hc.2 _ hs
    have h' : c * s = c * (c * s * c⁻¹) := by rw [← h]; group
    rw [mul_left_cancel h']
    exact hs

theorem e1KBar_le_e1NBar : e1KBar Z u m y x ≤ e1NBar Z u m y x :=
  sup_le hb.e1RBar_le_e1NBar centralizer_le_e1NBar

theorem e1RBar_le_normalizer : e1RBar Z u m y x ≤ Subgroup.normalizer
    ((e1M0 Z (u * (x * u * x⁻¹)) ⊓ Subgroup.centralizer (e1RBar Z u m y x : Set (G ⧸ Z)) :
      Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) := by
  have key : ∀ r ∈ e1RBar Z u m y x, ∀ c ∈ e1M0 Z (u * (x * u * x⁻¹)) ⊓
      Subgroup.centralizer (e1RBar Z u m y x : Set (G ⧸ Z)),
      r * c * r⁻¹ ∈ e1M0 Z (u * (x * u * x⁻¹)) ⊓
        Subgroup.centralizer (e1RBar Z u m y x : Set (G ⧸ Z)) := by
    intro r hr c hc
    refine ⟨(e1M0 Z _).mul_mem ((e1M0 Z _).mul_mem (hb.e1RBar_le_e1M0 hr) hc.1)
      ((e1M0 Z _).inv_mem (hb.e1RBar_le_e1M0 hr)), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have h := Subgroup.mem_centralizer_iff.mp hc.2 (r⁻¹ * s * r)
      ((e1RBar Z u m y x).mul_mem ((e1RBar Z u m y x).mul_mem
        ((e1RBar Z u m y x).inv_mem hr) hs) hr)
    calc s * (r * c * r⁻¹) = r * (r⁻¹ * s * r * c) * r⁻¹ := by group
      _ = r * c * r⁻¹ * s := by rw [h]; group
  intro r hr
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨key r hr c, fun hc => ?_⟩
  have h := key r⁻¹ ((e1RBar Z u m y x).inv_mem hr) _ hc
  rwa [show r⁻¹ * (r * c * r⁻¹) * r⁻¹⁻¹ = c by group] at h

theorem exists_of_mem_e1KBar {k : G ⧸ Z} (hk : k ∈ e1KBar Z u m y x) :
    ∃ r ∈ e1RBar Z u m y x, ∃ c ∈ e1M0 Z (u * (x * u * x⁻¹)) ⊓
      Subgroup.centralizer (e1RBar Z u m y x : Set (G ⧸ Z)), r * c = k := by
  have h : k ∈ ((e1KBar Z u m y x : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) := hk
  rw [e1KBar, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hb.e1RBar_le_normalizer] at h
  obtain ⟨r, hr, c, hc, hrc⟩ := h
  exact ⟨r, hr, c, hc, hrc⟩

theorem exists_mul_of_mem_e1NBar (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {n : G ⧸ Z}
    (hn : n ∈ e1NBar Z u m y x) :
    ∃ r ∈ e1RBar Z u m y x, ∃ c ∈ e1NBar Z u m y x, (∃ k, Odd k ∧ c ^ k = 1) ∧ n = r * c := by
  obtain ⟨a, b, hb', hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  obtain ⟨α, β, hαβ⟩ : IsCoprime ((2 ^ a : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb'))
  have hnb : n ^ b ∈ e1RBar Z u m y x := by
    refine hb.mem_e1RBar_of_pow_eq_one S' hS' ((e1M0 Z _).pow_mem hn.1 b)
      ((Subgroup.normalizer _).pow_mem hn.2 b) (k := a) ?_
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  refine ⟨(n ^ b) ^ β, (e1RBar Z u m y x).zpow_mem hnb β, (n ^ 2 ^ a) ^ α,
    (e1NBar Z u m y x).zpow_mem ((e1NBar Z u m y x).pow_mem hn _) α, ⟨b, hb', ?_⟩, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, ← hord,
      pow_orderOf_eq_one, one_zpow]
  · have h1 : (b : ℤ) * β + ((2 ^ a : ℕ) : ℤ) * α = 1 := by linear_combination hαβ
    calc n = n ^ ((b : ℤ) * β + ((2 ^ a : ℕ) : ℤ) * α) := by rw [h1, zpow_one]
      _ = (n ^ b) ^ β * (n ^ 2 ^ a) ^ α := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

theorem mem_e1KBar_of_conj (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {n : G ⧸ Z}
    (hn : n ∈ e1NBar Z u m y x) {r₀ : G ⧸ Z} (hr₀ : r₀ ∈ e1RBar Z u m y x)
    (hrr : r₀ * r₀ = 1) (hr1 : r₀ ≠ 1) (hrz : r₀ ≠ caseC3Word Z u m y x 40)
    (hnr : n * r₀ * n⁻¹ = r₀ ∨ n * r₀ * n⁻¹ = r₀ * caseC3Word Z u m y x 40) :
    n ∈ e1KBar Z u m y x := by
  obtain ⟨r, hr, c, hc, ⟨k, hk, hck⟩, rfl⟩ := hb.exists_mul_of_mem_e1NBar S' hS' hn
  have hri := (e1RBar Z u m y x).inv_mem hr
  have hcr : c * r₀ * c⁻¹ = r₀ ∨ c * r₀ * c⁻¹ = r₀ * caseC3Word Z u m y x 40 := by
    have h := conj_mul_conj_mod hb.forty_mul_self
      (hb.conj_forty_of_mem_e1NBar (hb.e1RBar_le_e1NBar hri)) hnr (hb.conj_of_mem_e1RBar hri hr₀)
    rwa [inv_mul_cancel_left] at h
  have hcomm := hb.commute_of_odd hk hck (conj_mem_of_mem_e1NBar hc) hr₀ hrr hr1 hrz hcr
  exact Subgroup.mul_mem_sup hr
    ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun s hs => (hcomm s hs).symm⟩

theorem mem_e1KBar_iff (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {n : G ⧸ Z} :
    n ∈ e1KBar Z u m y x ↔ n ∈ e1NBar Z u m y x ∧ ∀ s ∈ e1RBar Z u m y x,
      n * s * n⁻¹ = s ∨ n * s * n⁻¹ = s * caseC3Word Z u m y x 40 := by
  refine ⟨fun hn => ⟨hb.e1KBar_le_e1NBar hn, fun s hs => ?_⟩, fun ⟨hn, h⟩ => ?_⟩
  · obtain ⟨r, hr, c, hc, rfl⟩ := hb.exists_of_mem_e1KBar hn
    rw [show r * c * s * (r * c)⁻¹ = r * (c * s * c⁻¹) * r⁻¹ by group,
      ← Subgroup.mem_centralizer_iff.mp hc.2 s hs, mul_inv_cancel_right]
    exact hb.conj_of_mem_e1RBar hr hs
  · have h32 : e1Sing 32 := by decide
    obtain ⟨hR, hrr, hr1, hrz⟩ := hb.sing_iff.mpr h32
    exact hb.mem_e1KBar_of_conj S' hS' hn hR hrr hr1 hrz (h _ hR)

theorem normal_e1KBar (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) :
    ((e1KBar Z u m y x).subgroupOf (e1NBar Z u m y x)).Normal := by
  refine ⟨fun a ha b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  obtain ⟨-, ha'⟩ := (hb.mem_e1KBar_iff S' hS').mp ha
  have hbab : (b : G ⧸ Z) * a * (b : G ⧸ Z)⁻¹ ∈ e1NBar Z u m y x :=
    (e1NBar Z u m y x).mul_mem ((e1NBar Z u m y x).mul_mem b.2 (hb.e1KBar_le_e1NBar ha))
      ((e1NBar Z u m y x).inv_mem b.2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine (hb.mem_e1KBar_iff S' hS').mpr ⟨hbab, fun s hs => ?_⟩
  have hs' : (b : G ⧸ Z)⁻¹ * s * (b : G ⧸ Z)⁻¹⁻¹ ∈ e1RBar Z u m y x :=
    conj_mem_of_mem_e1NBar ((e1NBar Z u m y x).inv_mem b.2) s hs
  rw [inv_inv] at hs'
  rw [show (b : G ⧸ Z) * a * (b : G ⧸ Z)⁻¹ * s * ((b : G ⧸ Z) * a * (b : G ⧸ Z)⁻¹)⁻¹ =
    (b : G ⧸ Z) * ((a : G ⧸ Z) * ((b : G ⧸ Z)⁻¹ * s * b) * (a : G ⧸ Z)⁻¹) * (b : G ⧸ Z)⁻¹ by
    group]
  rcases ha' _ hs' with h | h <;> rw [h]
  · left
    group
  · right
    rw [show (b : G ⧸ Z) * ((b : G ⧸ Z)⁻¹ * s * b * caseC3Word Z u m y x 40) * (b : G ⧸ Z)⁻¹ =
      s * ((b : G ⧸ Z) * caseC3Word Z u m y x 40 * (b : G ⧸ Z)⁻¹) by group,
      hb.conj_forty_of_mem_e1NBar b.2]

theorem conj_of_mem_e1NBar_of_not_typeD (htype : ¬ ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {n : G ⧸ Z} (hn : n ∈ e1NBar Z u m y x)
    {s : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x) :
    n * s * n⁻¹ = s ∨ n * s * n⁻¹ = s * caseC3Word Z u m y x 40 := by
  obtain ⟨r, hr, c, hc, ⟨k, hk, hck⟩, rfl⟩ := hb.exists_mul_of_mem_e1NBar S' hS' hn
  have hcomm := hb.commute_of_odd_of_not_typeD htype hk hck (conj_mem_of_mem_e1NBar hc)
  rw [show r * c * s * (r * c)⁻¹ = r * (c * s * c⁻¹) * r⁻¹ by group, hcomm s hs,
    mul_inv_cancel_right]
  exact hb.conj_of_mem_e1RBar hr hs

theorem e1KBar_eq_of_not_typeD (htype : ¬ ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) :
    e1KBar Z u m y x = e1NBar Z u m y x :=
  le_antisymm hb.e1KBar_le_e1NBar fun _ hn => (hb.mem_e1KBar_iff S' hS').mpr
    ⟨hn, fun _ hs => hb.conj_of_mem_e1NBar_of_not_typeD htype S' hS' hn hs⟩

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
