module

public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseBLam
public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseBHyp
public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseBN

public section

namespace CFSG.GH74.Generic.BProg.B2.WeakSigCaseB

open CFSG Subgroup CFSG.GH74.Generic.BProg.B2.WeakSigGen

section Core

variable {Y : Type} [Group Y]

theorem lam_eq_bot_of_forall [Finite Y] {L W : Subgroup Y} (hLs : IsSimpleGroup ↥L)
    (hLeven : 2 ∣ Nat.card ↥L) (hodd : Odd (Nat.card ↥(lam L W)))
    (hn : ∀ c ∈ L, c ∈ normalizer (lam L W : Set Y)) : lam L W = ⊥ := by
  have hnorm : ((lam L W).subgroupOf L).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact (mem_normalizer_iff.mp (hn g g.2) n).mp hn'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((lam L W).subgroupOf L) with h | h
  · refine le_bot_iff.mp fun l hl => ?_
    have : (⟨l, lam_le hl⟩ : ↥L) ∈ (lam L W).subgroupOf L := hl
    rw [h, Subgroup.mem_bot] at this
    have h2 : l = 1 := congrArg Subtype.val this
    rw [h2]; exact Subgroup.one_mem _
  · exfalso
    have hLle : L ≤ lam L W := by
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ (lam L W).subgroupOf L := by rw [h]; trivial
      exact this
    have h2 : 2 ∣ Nat.card ↥(lam L W) := hLeven.trans (Subgroup.card_dvd_of_le hLle)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem mem_centralizer_of_ne [Finite Y] {L L' : Subgroup Y} (hL : IsComponent L)
    (hL' : IsComponent L') (hne : L ≠ L') {v : Y} (hv : v ∈ L') : v ∈ centralizer (L : Set Y) := by
  rw [mem_centralizer_iff]
  intro y hy
  exact commute_of_ne hL hL' hne y hy v hv

theorem mem_normalizer_of_mem_centralizer {L : Subgroup Y} {v : Y}
    (hv : v ∈ centralizer (L : Set Y)) : v ∈ normalizer (L : Set Y) := by
  rw [mem_normalizer_iff]
  intro b
  have hcomm := mem_centralizer_iff.mp hv
  constructor
  · intro hb
    have : v * b * v⁻¹ = b := by rw [← hcomm b hb]; group
    rw [this]; exact hb
  · intro hb
    have h1 : v⁻¹ * (v * b * v⁻¹) * v = v * b * v⁻¹ := by
      have := hcomm (v * b * v⁻¹) hb
      calc v⁻¹ * (v * b * v⁻¹) * v = v⁻¹ * ((v * b * v⁻¹) * v) := by group
        _ = v⁻¹ * (v * (v * b * v⁻¹)) := by rw [this]
        _ = v * b * v⁻¹ := by group
    have h2 : v * b * v⁻¹ = b := by
      calc v * b * v⁻¹ = v⁻¹ * (v * b * v⁻¹) * v := h1.symm
        _ = b := by group
    rw [h2] at hb; exact hb

theorem caseB_core [Finite Y] {L D W : Subgroup Y} {s : Y} (hLc : IsComponent L)
    (hcen : ∀ l ∈ L, (∀ y ∈ L, y * l = l * y) → l = 1) (hLs : IsSimpleGroup ↥L)
    (hLeven : 2 ∣ Nat.card ↥L) (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hk : pRank 2 ↥D = 2 ∨ pRank 2 ↥D = 3) (hW : Odd (Nat.card ↥W))
    (hDW : D ≤ normalizer (W : Set Y))
    (hC : ∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
      centralizer (E : Set Y) ≤ normalizer (W : Set Y))
    (hsD : s ∈ D) (hs : s ∉ normalizer (L : Set Y))
    (hO : ∀ d ∈ D, d ∈ normalizer (L : Set Y) ∨ d * s ∈ normalizer (L : Set Y))
    (hdata : ∃ E₁ : Subgroup Y, E₁ ≤ D ⊓ normalizer (L : Set Y) ∧
      pRank 2 ↥(D ⊓ normalizer (L : Set Y)) - 1 ≤ pRank 2 ↥E₁ ∧
      ∃ c ∈ L, c ∈ centralizer (E₁ : Set Y) ∧ (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧
        ∃ y ∈ L, y * c ≠ c * y)
    (hA : ∀ D' W' : Subgroup Y, CFSG.IsElementaryAbelian 2 ↥D' →
      (pRank 2 ↥D' = 2 ∨ pRank 2 ↥D' = 3) → Odd (Nat.card ↥W') → D' ≤ normalizer (L : Set Y) →
      D' ≤ normalizer (W' : Set Y) →
      (∀ E : Subgroup Y, E ≤ D' → pRank 2 ↥D' - 1 ≤ pRank 2 ↥E → ∀ x ∈ L,
        x ∈ centralizer (E : Set Y) → x ∈ normalizer (W' : Set Y)) →
      W' ≤ centralizer (L : Set Y)) :
    W ≤ centralizer (L : Set Y) := by
  obtain ⟨hD₀, hrk⟩ := rank_D₀ hD hsD hs hO
  set D₀ : Subgroup Y := D ⊓ normalizer (L : Set Y) with hD₀def
  have hss : s * s = 1 := (forall_of_isElementaryAbelian hD).2 s hsD
  have hne : L ≠ conjugate L s := fun h => hs (conjugate_eq_self_iff.mp h.symm)
  have hL₂ : IsComponent (conjugate L s) := isComponent_conjugate hLc s
  have hxprop : ∀ E₀ : Subgroup Y, E₀ ≤ D₀ → pRank 2 ↥D ≤ pRank 2 ↥E₀ + 2 → ∀ c ∈ L,
      c ∈ centralizer (E₀ : Set Y) → c * (s * c * s⁻¹) ∈ normalizer (W : Set Y) ∧
        c * (s * c * s⁻¹) ∈ normalizer (L : Set Y) ∧
        ∀ y ∈ L, c * (s * c * s⁻¹) * y * (c * (s * c * s⁻¹))⁻¹ = c * y * c⁻¹ := by
    intro E₀ hE₀ hr c hc hcE
    have hvm : s * c * s⁻¹ ∈ conjugate L s := by
      rw [mem_conjugate_iff]
      have : s * (s * c * s⁻¹) * s⁻¹ = c := by
        calc s * (s * c * s⁻¹) * s⁻¹ = (s * s) * c * (s * s)⁻¹ := by group
          _ = c := by rw [hss]; simp
      rw [this]; exact hc
    have hvc : s * c * s⁻¹ ∈ centralizer (L : Set Y) := mem_centralizer_of_ne hLc hL₂ hne hvm
    refine ⟨x_mem_normalizer hLc hD hss hsD hs hE₀ hr hC hc hcE, ?_, ?_⟩
    · exact (normalizer (L : Set Y)).mul_mem (Subgroup.le_normalizer hc)
        (mem_normalizer_of_mem_centralizer hvc)
    · intro y hy
      have hcomm := mem_centralizer_iff.mp hvc y hy
      have : (s * c * s⁻¹) * y * (s * c * s⁻¹)⁻¹ = y := by rw [← hcomm]; group
      calc c * (s * c * s⁻¹) * y * (c * (s * c * s⁻¹))⁻¹
          = c * ((s * c * s⁻¹) * y * (s * c * s⁻¹)⁻¹) * c⁻¹ := by group
        _ = c * y * c⁻¹ := by rw [this]
  obtain ⟨E₁, hE₁, hr₁, c₁, hc₁L, hc₁E, hc₁2, hc₁n⟩ := hdata
  have hWL : W ≤ normalizer (L : Set Y) := by
    obtain ⟨hxW, -, -⟩ := hxprop E₁ hE₁ (by omega) c₁ hc₁L hc₁E
    exact normalizes_of_diag hLc hW hss hs hc₁L hc₁2 hc₁n hxW
  have hΛodd : Odd (Nat.card ↥(lam L W)) := odd_card_lam hcen hW
  have hD₀L : D₀ ≤ normalizer (L : Set Y) := inf_le_right
  have hΛD₀ : D₀ ≤ normalizer (lam L W : Set Y) :=
    fun d hd => mem_normalizer_lam hd.2 (hDW hd.1)
  have hcΛ : ∀ E₀ : Subgroup Y, E₀ ≤ D₀ → pRank 2 ↥D ≤ pRank 2 ↥E₀ + 2 → ∀ c ∈ L,
      c ∈ centralizer (E₀ : Set Y) → c ∈ normalizer (lam L W : Set Y) := by
    intro E₀ hE₀ hr c hc hcE
    obtain ⟨hxW, hxL, hxy⟩ := hxprop E₀ hE₀ hr c hc hcE
    have hxΛ := mem_normalizer_lam hxL hxW
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h1 := (mem_normalizer_iff.mp hxΛ b).mp hb
      rwa [hxy b (lam_le hb)] at h1
    · intro hcb
      have hbL : b ∈ L := by
        have h2 : c⁻¹ * (c * b * c⁻¹) * c ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem hc) (lam_le hcb)) hc
        have h3 : c⁻¹ * (c * b * c⁻¹) * c = b := by group
        rwa [h3] at h2
      rw [← hxy b hbL] at hcb
      exact (mem_normalizer_iff.mp hxΛ b).mpr hcb
  have hΛbot : lam L W = ⊥ := by
    rcases hk with hk2 | hk3
    · refine lam_eq_bot_of_forall hLs hLeven hΛodd (fun c hc => hcΛ ⊥ bot_le (by omega) c hc ?_)
      rw [mem_centralizer_iff]
      intro h hh
      have := Subgroup.mem_bot.mp hh
      subst this
      simp
    · have hr2 : pRank 2 ↥D₀ = 2 := by omega
      have hcent := hA D₀ (lam L W) hD₀ (Or.inl hr2) hΛodd hD₀L hΛD₀
        (fun E hE hr x hx hxE => hcΛ E hE (by omega) x hx hxE)
      refine le_bot_iff.mp fun l hl => ?_
      have hl1 := hcen l (lam_le hl) (fun y hy => mem_centralizer_iff.mp (hcent hl) y hy)
      rw [hl1]; exact Subgroup.one_mem _
  have hcomm : ∀ E₀ : Subgroup Y, E₀ ≤ D₀ → pRank 2 ↥D ≤ pRank 2 ↥E₀ + 2 → ∀ c ∈ L,
      c ∈ centralizer (E₀ : Set Y) → ∀ w ∈ W, c * w = w * c := by
    intro E₀ hE₀ hr c hc hcE w hw
    obtain ⟨hxW, -, hxy⟩ := hxprop E₀ hE₀ hr c hc hcE
    have hm := lam_comm_mem hWL hxW hc hxy hw
    rw [hΛbot, Subgroup.mem_bot] at hm
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hm)
  rcases hk with hk2 | hk3
  · intro w hw
    rw [mem_centralizer_iff]
    intro l hl
    refine hcomm ⊥ bot_le (by omega) l hl ?_ w hw
    rw [mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_bot.mp hh
    subst this
    simp
  · have hr2 : pRank 2 ↥D₀ = 2 := by omega
    refine hA D₀ W hD₀ (Or.inl hr2) hW hD₀L (fun d hd => hDW hd.1) ?_
    intro E hE hr x hx hxE
    exact mem_normalizer_of_mem_centralizer
      (mem_centralizer_iff.mpr fun w hw => (hcomm E hE (by omega) x hx hxE w hw).symm)

end Core

end CFSG.GH74.Generic.BProg.B2.WeakSigCaseB
