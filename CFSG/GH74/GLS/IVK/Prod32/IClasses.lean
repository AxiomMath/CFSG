module

public import CFSG.GH74.GLS.IVK.Prod32.Basic

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CFSG.GH74.GLS.IVK.Prod3

section CiSec

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}


omit [Finite H] in
theorem mem_sup_cent_iff {K N : Subgroup H} (hKn : K.Normal) (hKN : K ≤ N) {g g' : H} (hg : g ∈ N)
    (hg' : g' ∈ N) :
    g⁻¹ * g' ∈ K ⊔ (N ⊓ centralizer ({a} : Set H)) ↔
      ConjUnder K (g * a * g⁻¹) (g' * a * g'⁻¹) := by
  constructor
  · intro hm
    obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.1 hm
    have hca : c * a * c⁻¹ = a := by
      have := (Subgroup.mem_centralizer_singleton_iff.1 hc.2)
      calc c * a * c⁻¹ = a * c * c⁻¹ := by rw [← this]
        _ = a := by group
    have hg'eq : g' = g * k * c := by
      calc g' = g * (g⁻¹ * g') := by group
        _ = g * (k * c) := by rw [hkc]
        _ = g * k * c := by group
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · exact hKn.conj_mem k hk g
    · rw [hg'eq]
      calc g * k * g⁻¹ * (g * a * g⁻¹) * (g * k * g⁻¹)⁻¹ = g * k * a * k⁻¹ * g⁻¹ := by group
        _ = g * k * (c * a * c⁻¹) * k⁻¹ * g⁻¹ := by rw [hca]
        _ = g * k * c * a * (g * k * c)⁻¹ := by group
  · rintro ⟨k, hk, hkeq⟩
    set k₀ := g⁻¹ * k * g with hk₀
    have hk₀K : k₀ ∈ K := by
      have := hKn.conj_mem k hk g⁻¹
      simpa using this
    have hcomm : (k₀⁻¹ * (g⁻¹ * g')) * a * (k₀⁻¹ * (g⁻¹ * g'))⁻¹ = a := by
      have h1 : k₀ * a * k₀⁻¹ = g⁻¹ * g' * a * (g⁻¹ * g')⁻¹ := by
        calc k₀ * a * k₀⁻¹ = g⁻¹ * (k * (g * a * g⁻¹) * k⁻¹) * g := by rw [hk₀]; group
          _ = g⁻¹ * (g' * a * g'⁻¹) * g := by rw [hkeq]
          _ = g⁻¹ * g' * a * (g⁻¹ * g')⁻¹ := by group
      calc (k₀⁻¹ * (g⁻¹ * g')) * a * (k₀⁻¹ * (g⁻¹ * g'))⁻¹
          = k₀⁻¹ * (g⁻¹ * g' * a * (g⁻¹ * g')⁻¹) * k₀ := by group
        _ = k₀⁻¹ * (k₀ * a * k₀⁻¹) * k₀ := by rw [h1]
        _ = a := by group
    have hcN : k₀⁻¹ * (g⁻¹ * g') ∈ N := by
      refine N.mul_mem (N.inv_mem (hKN hk₀K)) (N.mul_mem (N.inv_mem hg) hg')
    have hcC : k₀⁻¹ * (g⁻¹ * g') ∈ centralizer ({a} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : (k₀⁻¹ * (g⁻¹ * g')) * a = a * (k₀⁻¹ * (g⁻¹ * g')) := by
        calc (k₀⁻¹ * (g⁻¹ * g')) * a
            = ((k₀⁻¹ * (g⁻¹ * g')) * a * (k₀⁻¹ * (g⁻¹ * g'))⁻¹) * (k₀⁻¹ * (g⁻¹ * g')) := by group
          _ = a * (k₀⁻¹ * (g⁻¹ * g')) := by rw [hcomm]
      exact e
    have : g⁻¹ * g' = k₀ * (k₀⁻¹ * (g⁻¹ * g')) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk₀K ⟨hcN, hcC⟩


theorem exists_pow_of_isPGroup_le {T₁ : Subgroup H} {T : Subgroup H} (hT : IsPGroup 2 ↥T) (hle : T₁ ≤ T) :
    ∃ n : ℕ, Nat.card ↥T₁ = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hT.to_le hle).exists_card_eq

theorem prod3_Ci (h : Hyp H K₁ K₂ z T a) (hCe : ∀ g : H, ⁅g, a⁆ ∈ K₁ ⊔ K₂)
    (hg : ∃ b ∈ invCoset (K₁ ⊔ K₂) a, ¬ ConjUnder (K₁ ⊔ K₂) a b ∧
      ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ConjUnder (K₁ ⊔ K₂) a u ∨ ConjUnder (K₁ ⊔ K₂) b u) :
    Ci T K₁ K₂ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  set K := K₁ ⊔ K₂ with hK
  have hKn : K.Normal := h.setting.normal
  set T₁ := T1 T K₁ with hT₁
  set N := K ⊔ T₁ with hN
  set C := centralizer ({a} : Set H) with hC
  have hKN : K ≤ N := le_sup_left
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [h.a_ord, pow_two] at this
    exact this
  obtain ⟨b, hbI, hbna, hbcov⟩ := hg
  have h1 : (K ⊔ (N ⊓ C)).relIndex N ≤ 2 := by
    set M'' : Subgroup ↥N := (K ⊔ (N ⊓ C)).subgroupOf N with hM''
    have hNmem : ∀ g : ↥N, (g : H) * a * (g : H)⁻¹ ∈ invCoset K a := by
      intro g
      refine ⟨⟨(g : H) * a * (g : H)⁻¹ * a⁻¹, ?_, by group⟩, ?_⟩
      · have : ⁅(g : H), a⁆ ∈ K := hCe g
        simpa [commutatorElement_def] using this
      · calc (g : H) * a * (g : H)⁻¹ * ((g : H) * a * (g : H)⁻¹) = (g : H) * (a * a) * (g : H)⁻¹ := by group
          _ = 1 := by rw [ha2]; group
    have hconj_trans : ∀ {x y w : H}, ConjUnder K x y → ConjUnder K y w → ConjUnder K x w := by
      rintro x y w ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
      exact ⟨k₂ * k₁, K.mul_mem hk₂ hk₁, by rw [← h₂, ← h₁]; group⟩
    have hconj_symm : ∀ {x y : H}, ConjUnder K x y → ConjUnder K y x := by
      rintro x y ⟨k, hk, hkxy⟩
      exact ⟨k⁻¹, K.inv_mem hk, by rw [← hkxy]; group⟩
    let ψ : ↥N → Bool := fun g => decide (ConjUnder K a ((g : H) * a * (g : H)⁻¹))
    have hψ_iff : ∀ g g' : ↥N, ψ g = ψ g' ↔
        ConjUnder K ((g : H) * a * (g : H)⁻¹) ((g' : H) * a * (g' : H)⁻¹) := by
      intro g g'
      constructor
      · intro hψ
        by_cases p : ConjUnder K a ((g : H) * a * (g : H)⁻¹)
        · have p' : ConjUnder K a ((g' : H) * a * (g' : H)⁻¹) := by
            by_contra p'
            simp [ψ, p, p'] at hψ
          exact hconj_trans (hconj_symm p) p'
        · have p' : ¬ ConjUnder K a ((g' : H) * a * (g' : H)⁻¹) := by
            intro p'
            simp [ψ, p, p'] at hψ
          have hb1 := (hbcov _ (hNmem g)).resolve_left p
          have hb2 := (hbcov _ (hNmem g')).resolve_left p'
          exact hconj_trans (hconj_symm hb1) hb2
      · intro hc
        by_cases p : ConjUnder K a ((g : H) * a * (g : H)⁻¹)
        · have p' : ConjUnder K a ((g' : H) * a * (g' : H)⁻¹) := hconj_trans p hc
          simp [ψ, p, p']
        · have p' : ¬ ConjUnder K a ((g' : H) * a * (g' : H)⁻¹) :=
            fun p' => p (hconj_trans p' (hconj_symm hc))
          simp [ψ, p, p']
    have hcrit : ∀ g g' : ↥N, g⁻¹ * g' ∈ M'' ↔
        ConjUnder K ((g : H) * a * (g : H)⁻¹) ((g' : H) * a * (g' : H)⁻¹) := by
      intro g g'
      rw [hM'', Subgroup.mem_subgroupOf]
      exact mem_sup_cent_iff hKn hKN g.2 g'.2
    let f : (↥N ⧸ M'') → Bool := Quotient.lift ψ (fun g g' hgg' => by
      exact (hψ_iff g g').2 ((hcrit g g').1 (QuotientGroup.leftRel_apply.1 hgg')))
    have hfinj : Function.Injective f := by
      intro x y
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      rename_i g g'
      intro hfg
      apply Quotient.sound
      exact QuotientGroup.leftRel_apply.2 ((hcrit g g').2 ((hψ_iff g g').1 hfg))
    have hcard : Nat.card (↥N ⧸ M'') ≤ Nat.card Bool := Nat.card_le_card_of_injective f hfinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
    exact hcard
  have h2 : K ⊔ (N ⊓ C) = K ⊔ (T₁ ⊓ C) := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      set G₀ := N ⊓ C with hG₀
      set W := T₁ ⊓ C with hW
      have hWle : W ≤ G₀ := inf_le_inf_right C (le_sup_right : T₁ ≤ N)
      have hext : CFSG.ABGLocalTools.IsSylowOf 2 W (C ⊓ N) := h.extr
      have hext' : CFSG.ABGLocalTools.IsSylowOf 2 W G₀ := by rwa [hG₀, inf_comm]
      obtain ⟨-, -, hodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hext'
      set N₀ := K ⊓ G₀ with hN₀
      have hN₀le : N₀ ≤ G₀ := inf_le_right
      set A₀ := N₀ ⊔ W with hA₀
      have hA₀le : A₀ ≤ G₀ := sup_le hN₀le hWle
      have hWA : W ≤ A₀ := le_sup_right
      have hN₀A : N₀ ≤ A₀ := le_sup_left
      have e1 := Subgroup.relIndex_mul_relIndex W A₀ G₀ hWA hA₀le
      have hodd1 : ¬ 2 ∣ A₀.relIndex G₀ := fun hd => hodd (e1 ▸ Dvd.dvd.mul_left hd _)
      have e2 := Subgroup.relIndex_mul_relIndex N₀ A₀ G₀ hN₀A hA₀le
      have hKG : N₀.relIndex G₀ = K.relIndex (K ⊔ G₀) := by
        rw [Subgroup.relIndex_sup_left, hN₀]
        exact Subgroup.inf_relIndex_right K G₀
      have hKGN : K.relIndex (K ⊔ G₀) ∣ K.relIndex N := by
        have hle : K ⊔ G₀ ≤ N := sup_le hKN inf_le_left
        have := Subgroup.relIndex_mul_relIndex K (K ⊔ G₀) N le_sup_left hle
        exact Dvd.intro _ this
      have hKT : K.relIndex N ∣ Nat.card ↥T₁ := by
        have : K.relIndex N = K.relIndex T₁ := by
          rw [hN, Subgroup.relIndex_sup_left]
        rw [this]
        exact Subgroup.relIndex_dvd_card K T₁
      obtain ⟨n, hn⟩ := exists_pow_of_isPGroup_le (T := T) (T₁ := T₁)
        (CFSG.ABGLocalTools.IsSylowOf.isPGroup h.sylow) inf_le_left
      have hdiv : N₀.relIndex G₀ ∣ 2 ^ n := by
        rw [hKG]; exact (hKGN.trans hKT).trans (by rw [hn])
      have hA₀G : A₀.relIndex G₀ ∣ 2 ^ n := (Dvd.intro_left _ e2).trans hdiv
      have : A₀.relIndex G₀ = 1 := by
        rcases (Nat.dvd_prime_pow Nat.prime_two).1 hA₀G with ⟨i, -, hi⟩
        rcases i with _ | i
        · simpa using hi
        · exfalso; exact hodd1 (by rw [hi]; exact dvd_pow_self 2 (Nat.succ_ne_zero i))
      have hGA : G₀ ≤ A₀ := by
        have := (Subgroup.relIndex_eq_one).1 this
        exact this
      exact le_trans hGA (sup_le (le_trans inf_le_left le_sup_left) le_sup_right)
    · exact sup_le_sup_left (inf_le_inf_right C (le_sup_right : T₁ ≤ N)) K
  show (K ⊔ (T₁ ⊓ C)).relIndex (K ⊔ T₁) ≤ 2
  rw [← h2]
  exact h1

end CiSec



end CFSG.GH74.GLS.IVK.Prod3
