module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction

section Max

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

structure BlockOrbits (M : Subgroup (Equiv.Perm (Fin n))) (B₀ : Finset (Fin n))
    (H R₁ R₂ : List (Finset (Fin n))) (c₁ c₂ : ℕ) : Prop where
  orbit_iff : ∀ B, B ∈ MulAction.orbit ↥M B₀ ↔ B ∈ H
  nodup : H.Nodup
  nodup₁ : R₁.Nodup
  nodup₂ : R₂.Nodup
  sub₁ : ∀ B ∈ R₁, B ∈ H
  sub₂ : ∀ B ∈ R₂, B ∈ H
  notB₁ : B₀ ∉ R₁
  notB₂ : B₀ ∉ R₂
  cover : ∀ B ∈ H, B ≠ B₀ → B ∈ R₁ ∨ B ∈ R₂
  lev₁ : ∀ B ∈ H, B ≠ B₀ → (B ∈ R₁ ↔ (B ∩ B₀).card = c₁)
  lev₂ : ∀ B ∈ H, B ≠ B₀ → (B ∈ R₂ ↔ (B ∩ B₀).card = c₂)

theorem BlockOrbits.card_orbit {B₀ : Finset (Fin n)} {H R₁ R₂ : List (Finset (Fin n))}
    {c₁ c₂ : ℕ} (h : BlockOrbits M B₀ H R₁ R₂ c₁ c₂) :
    (MulAction.orbit ↥M B₀).ncard = H.length := by
  have : MulAction.orbit ↥M B₀ = ↑H.toFinset := by
    ext B
    rw [h.orbit_iff, List.coe_toFinset]
    rfl
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup h.nodup]

theorem BlockOrbits.card_stab {B₀ : Finset (Fin n)} {H R₁ R₂ : List (Finset (Fin n))}
    {c₁ c₂ : ℕ} (h : BlockOrbits M B₀ H R₁ R₂ c₁ c₂) :
    (stabilizer ↥M B₀).index = H.length := by
  rw [index_stabilizer, h.card_orbit]

theorem orbit_stab_eq {B₀ : Finset (Fin n)} {H R : List (Finset (Fin n))} {c : ℕ}
    (horb : ∀ B, B ∈ orbit ↥M B₀ ↔ B ∈ H) (hsub : ∀ B ∈ R, B ∈ H) (hnot : B₀ ∉ R)
    (hlev : ∀ B ∈ H, B ≠ B₀ → (B ∈ R ↔ (B ∩ B₀).card = c))
    (hsame : ∀ B ∈ R, ∀ B' ∈ R, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    {B' : Finset (Fin n)} (hB' : B' ∈ R) :
    orbit ↥(stabilizer ↥M B₀) B' = {B | B ∈ R} := by
  ext B
  constructor
  · rintro ⟨q, rfl⟩
    have hqB₀ : (q : ↥M) • B₀ = B₀ := q.2
    obtain ⟨y, hy⟩ := (horb B').2 (hsub B' hB')
    have hy' : y • B₀ = B' := hy
    have hqH : (q : ↥M) • B' ∈ H := by
      rw [← horb]
      refine ⟨(q : ↥M) * y, ?_⟩
      show ((q : ↥M) * y) • B₀ = (q : ↥M) • B'
      rw [mul_smul, hy']
    have hne' : B' ≠ B₀ := fun h => hnot (h ▸ hB')
    have hne : (q : ↥M) • B' ≠ B₀ := by
      intro h
      apply hne'
      have h1 : (q : ↥M)⁻¹ • B₀ = B₀ := by
        rw [inv_smul_eq_iff]
        exact hqB₀.symm
      have h2 : B' = (q : ↥M)⁻¹ • ((q : ↥M) • B') := (inv_smul_smul _ _).symm
      rw [h] at h2
      exact h2.trans h1
    have hlevB : ((q : ↥M) • B' ∩ B₀).card = (B' ∩ B₀).card := by
      have : (q : ↥M) • B' ∩ B₀ = (q : ↥M) • (B' ∩ B₀) := by
        rw [Finset.smul_finset_inter, hqB₀]
      rw [this, Finset.card_smul_finset]
    exact (hlev _ hqH hne).2 (hlevB.trans ((hlev B' (hsub B' hB') hne').1 hB'))
  · intro hB
    obtain ⟨q, hq, hqB⟩ := hsame B' hB' B hB
    exact ⟨⟨q, hq⟩, hqB⟩

theorem card_orbit_stab {B₀ : Finset (Fin n)} {H R : List (Finset (Fin n))} {c : ℕ}
    (horb : ∀ B, B ∈ orbit ↥M B₀ ↔ B ∈ H) (hsub : ∀ B ∈ R, B ∈ H) (hnot : B₀ ∉ R)
    (hlev : ∀ B ∈ H, B ≠ B₀ → (B ∈ R ↔ (B ∩ B₀).card = c))
    (hsame : ∀ B ∈ R, ∀ B' ∈ R, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    (hnd : R.Nodup) {B' : Finset (Fin n)} (hB' : B' ∈ R) :
    Nat.card (orbit ↥(stabilizer ↥M B₀) B') = R.length := by
  rw [orbit_stab_eq horb hsub hnot hlev hsame hB', Nat.card_coe_set_eq]
  have : ({B | B ∈ R} : Set (Finset (Fin n))) = ↑R.toFinset := (List.coe_toFinset R).symm
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem eq_of_sylow_fix {B₀ : Finset (Fin n)} {H R₁ R₂ : List (Finset (Fin n))} {c₁ c₂ : ℕ}
    (h : BlockOrbits M B₀ H R₁ R₂ c₁ c₂)
    (hsame₁ : ∀ B ∈ R₁, ∀ B' ∈ R₁, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    (hsame₂ : ∀ B ∈ R₂, ∀ B' ∈ R₂, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    {e Kc : ℕ} (hKc : Nat.card (stabilizer ↥M B₀) = Kc) (hd₁ : ¬ 2 ^ e ∣ Kc / R₁.length)
    (hd₂ : ¬ 2 ^ e ∣ Kc / R₂.length) {S : Subgroup ↥M} (hSK : S ≤ stabilizer ↥M B₀)
    (hS : 2 ^ e ∣ Nat.card S) {B : Finset (Fin n)} (hB : B ∈ H) (hfix : S ≤ stabilizer ↥M B) :
    B = B₀ := by
  by_contra hne
  have hle : S.subgroupOf (stabilizer ↥M B₀) ≤ stabilizer ↥(stabilizer ↥M B₀) B := by
    intro s hs
    rw [mem_stabilizer_iff]
    exact mem_stabilizer_iff.1 (hfix hs)
  have hdvd : 2 ^ e ∣ Nat.card (stabilizer ↥(stabilizer ↥M B₀) B) := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hle)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    exact hS
  have key : ∀ (R : List (Finset (Fin n))) (c : ℕ),
      (∀ B ∈ R, B ∈ H) → B₀ ∉ R → (∀ B ∈ H, B ≠ B₀ → (B ∈ R ↔ (B ∩ B₀).card = c)) →
      (∀ B ∈ R, ∀ B' ∈ R, ∃ q ∈ stabilizer ↥M B₀, q • B = B') → R.Nodup → B ∈ R →
      ¬ 2 ^ e ∣ Kc / R.length → False := by
    intro R c hsub hnot hlev hsame hnd hBR hd
    have hcard := card_orbit_stab h.orbit_iff hsub hnot hlev hsame hnd hBR
    have hmul := card_orbit_mul_card_stabilizer (Γ := ↥(stabilizer ↥M B₀)) B
    rw [hcard, hKc] at hmul
    have hpos : 0 < R.length := List.length_pos_of_mem hBR
    have : Kc / R.length = Nat.card (stabilizer ↥(stabilizer ↥M B₀) B) := by
      rw [← hmul]
      exact Nat.mul_div_cancel_left _ hpos
    rw [this] at hd
    exact hd hdvd
  rcases h.cover B hB hne with hR | hR
  · exact key R₁ c₁ h.sub₁ h.notB₁ h.lev₁ hsame₁ h.nodup₁ hR hd₁
  · exact key R₂ c₂ h.sub₂ h.notB₂ h.lev₂ hsame₂ h.nodup₂ hR hd₂

theorem card_orbit_overgroup {B₀ : Finset (Fin n)} {Y : Subgroup ↥M}
    (hY : stabilizer ↥M B₀ ≤ Y) {N : ℕ} (hN : (stabilizer ↥M B₀).index = N) :
    (orbit ↥Y B₀).ncard * Y.index = N := by
  have h1 := index_stabilizer ↥Y B₀
  have h2 : stabilizer ↥Y B₀ = (stabilizer ↥M B₀).subgroupOf Y := by
    ext z
    rfl
  rw [h2] at h1
  have h3 := Subgroup.relIndex_mul_index hY
  rw [← hN, ← h3, Subgroup.relIndex]
  rw [← h1]

theorem le_ncard_orbit_overgroup {B₀ : Finset (Fin n)} {Y : Subgroup ↥M}
    (hY : stabilizer ↥M B₀ ≤ Y) {R : List (Finset (Fin n))} (hnot : B₀ ∉ R) (hnd : R.Nodup)
    (hsame : ∀ B ∈ R, ∀ B' ∈ R, ∃ q ∈ stabilizer ↥M B₀, q • B = B') {B : Finset (Fin n)}
    (hBR : B ∈ R) (hBY : B ∈ orbit ↥Y B₀) : R.length + 1 ≤ (orbit ↥Y B₀).ncard := by
  obtain ⟨y, hy⟩ := hBY
  have hsub : ((insert B₀ R.toFinset : Finset (Finset (Fin n))) : Set (Finset (Fin n))) ⊆
      orbit ↥Y B₀ := by
    intro B' hB'
    rw [Finset.mem_coe, Finset.mem_insert, List.mem_toFinset] at hB'
    rcases hB' with rfl | hB'
    · exact ⟨1, one_smul _ _⟩
    · obtain ⟨q, hq, hqB⟩ := hsame B hBR B' hB'
      refine ⟨⟨q, hY hq⟩ * y, ?_⟩
      show (⟨q, hY hq⟩ * y : ↥Y) • B₀ = B'
      rw [mul_smul]
      have : y • B₀ = B := hy
      rw [this]
      exact hqB
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simpa using hnot),
    List.toFinset_card_of_nodup hnd] at h1
  exact h1

theorem stab_maximal {B₀ : Finset (Fin n)} {H R₁ R₂ : List (Finset (Fin n))} {c₁ c₂ : ℕ}
    (h : BlockOrbits M B₀ H R₁ R₂ c₁ c₂)
    (hsame₁ : ∀ B ∈ R₁, ∀ B' ∈ R₁, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    (hsame₂ : ∀ B ∈ R₂, ∀ B' ∈ R₂, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    (harith : ∀ d ∈ List.range H.length, d ∣ H.length → d < 1 + R₁.length ∧ d < 1 + R₂.length)
    (Y : Subgroup ↥M) (hY : stabilizer ↥M B₀ ≤ Y) :
    Y = stabilizer ↥M B₀ ∨ Y = ⊤ := by
  by_cases hfix : ∀ y ∈ Y, y • B₀ = B₀
  · left
    exact le_antisymm (fun y hy => mem_stabilizer_iff.2 (hfix y hy)) hY
  · right
    push Not at hfix
    obtain ⟨y, hyY, hyne⟩ := hfix
    have hmul := card_orbit_overgroup hY h.card_stab
    have hNpos : 0 < H.length := List.length_pos_of_mem ((h.orbit_iff B₀).1 (mem_orbit_self B₀))
    have hyH : y • B₀ ∈ H := (h.orbit_iff _).1 ⟨y, rfl⟩
    have hyY' : y • B₀ ∈ orbit ↥Y B₀ := ⟨⟨y, hyY⟩, rfl⟩
    have hlow : ∀ d, d = (orbit ↥Y B₀).ncard → H.length ≤ d := by
      intro d hd
      have hdvd : d ∣ H.length := ⟨Y.index, by rw [hd, ← hmul]⟩
      by_contra hlt
      push Not at hlt
      have := harith d (List.mem_range.2 hlt) hdvd
      rcases h.cover _ hyH hyne with hR | hR
      · have := le_ncard_orbit_overgroup hY h.notB₁ h.nodup₁ hsame₁ hR hyY'
        omega
      · have := le_ncard_orbit_overgroup hY h.notB₂ h.nodup₂ hsame₂ hR hyY'
        omega
    have hle : (orbit ↥Y B₀).ncard ≤ H.length := by
      have : orbit ↥Y B₀ ⊆ orbit ↥M B₀ := by
        rintro _ ⟨z, rfl⟩
        exact ⟨(z : ↥M), rfl⟩
      rw [← h.card_orbit]
      exact Set.ncard_le_ncard this (Set.toFinite _)
    have heq : (orbit ↥Y B₀).ncard = H.length := le_antisymm hle (hlow _ rfl)
    rw [heq] at hmul
    have : Y.index = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hNpos (hmul.trans (mul_one _).symm)
      exact this
    exact Subgroup.index_eq_one.1 this

end Max

end CFSG.QuasithinUnique.Vol2Native.L239
