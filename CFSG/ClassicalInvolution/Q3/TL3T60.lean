module

public import CFSG.ClassicalInvolution.Q3.TL3T50

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

@[expose] def centMembers {G : Type} [Group G] (Ω : Set (Subgroup G)) (u : G) :
    Set (Subgroup G) :=
  {M | M ∈ Ω ∧ ∀ m ∈ M, m * u = u * m}

theorem exists_lift_pow_five {H W : Type*} [Group H] [Group W] (ψ : H →* W)
    (hk : IsPGroup 2 ψ.ker) (x : H) (hx : ψ x ^ 5 = 1) : ∃ t : H, ψ t = ψ x ∧ t ^ 5 = 1 := by
  have h5 : x ^ 5 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hx]
  obtain ⟨a, ha⟩ := hk ⟨x ^ 5, h5⟩
  have ha' : x ^ (5 * 2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_mul]
    exact this
  have h16 : 16 ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  refine ⟨x ^ (16 ^ a), ?_, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hx, h16, pow_one]
  · rw [← pow_mul, show 16 ^ a * 5 = (5 * 2 ^ a) * 8 ^ a by
      rw [show (16 : ℕ) = 2 * 8 by norm_num, mul_pow]; ring, pow_mul, ha', one_pow]

theorem fin5_facts :
    (finRotate 5) ^ 5 = 1 ∧ Equiv.Perm.sign (finRotate 5) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) = 1 ∧
      finRotate 5 * (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) ≠
        (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) * finRotate 5 := by
  decide

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.exists_pow_five_not_comm (I : AEIdent P n) (hn : 5 ≤ n)
    (hk : IsPGroup 2 I.φ.ker) : ∃ x : ↥(pSpan P), x ^ 5 = 1 ∧ ∃ w : ↥(pSpan P), x * w ≠ w * x := by
  obtain ⟨h1, h2, h3, h4⟩ := fin5_facts
  set c : Fin 5 ↪ Fin n := Fin.castLEEmb hn with hc
  set σ := extPerm c (finRotate 5) with hσ
  set τ := extPerm c (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) with hτ
  have hσA : σ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ, sign_extPerm, h2]
  have hτA : τ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, hτ, sign_extPerm, h3]
  have hrange : ∀ {ρ : Equiv.Perm (Fin n)}, ρ ∈ alternatingGroup (Fin n) →
      ∃ x : ↥(pSpan P), I.φ x = mkQ n (ofPerm ρ) := by
    intro ρ hρ
    have : mkQ n (ofPerm ρ) ∈ I.φ.range := by
      rw [I.range_eq]
      exact mem_aeModel_ofPerm hρ
    exact this
  obtain ⟨x₀, hx₀⟩ := hrange hσA
  obtain ⟨w, hw⟩ := hrange hτA
  have hx5 : I.φ x₀ ^ 5 = 1 := by
    rw [hx₀, ← map_pow, ofPerm_pow, hσ, ← map_pow, h1, map_one, ofPerm_one, map_one]
  obtain ⟨x, hx, hx1⟩ := exists_lift_pow_five I.φ hk x₀ hx5
  refine ⟨x, hx1, w, fun hxw => h4 (extPerm_injective c ?_)⟩
  have e := congrArg (fun y => permQ n (I.φ y)) hxw
  simp only [map_mul, hx, hx₀, hw, permQ_mkQ] at e
  have hστ : σ * τ = τ * σ := e
  calc extPerm c (finRotate 5 * (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2)) = σ * τ :=
        map_mul _ _ _
    _ = τ * σ := hστ
    _ = extPerm c ((Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) * finRotate 5) :=
        (map_mul _ _ _).symm

theorem AEIdent.exists_pow_three_norm {Δ : Set (Subgroup G)} [Finite G] (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hn : 5 ≤ n) (I : AEIdent P n)
    (hk : IsPGroup 2 I.φ.ker) {L : Subgroup G} (hL : L ∈ P) :
    ∃ y : ↥(pSpan P), y ^ 3 = 1 ∧ conjSub (y : G) L = L ∧ ¬ ∀ l ∈ L, (y : G) * l = l * y := by
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  obtain ⟨y₀, hy₀, -⟩ := I.exists_y hΩ h2 hPΔ hinv hn hk hL hlab
  have hy3 : I.φ y₀ ^ 3 = 1 := by rw [hy₀]; exact yBar_pow_three α h
  obtain ⟨y, hy, hy1⟩ := TC.Thin.exists_lift_pow_three I.φ hk y₀ hy3
  rw [hy₀] at hy
  refine ⟨y, hy1, I.conjSub_eq_of_map_eq_yBar hΩ h2 hPΔ hinv hn hk hL hlab hy, fun hc => ?_⟩
  obtain ⟨x, hx, hne⟩ := yBar_not_comm_memBar hn α h b
  rw [← hlab] at hx
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
  apply hne
  rw [← hy, ← map_mul, ← map_mul]
  exact congrArg I.φ (Subtype.ext (hc l hl))

variable [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

omit [Finite G] in
theorem conjSub_mem_centMembers_of_comm {u x : G} (hxu : x * u = u * x) {L : Subgroup G}
    (hL : L ∈ centMembers Ω u) : conjSub x L ∈ centMembers Ω u := by
  refine ⟨hS.cex.hyp.conjInvariant x L hL.1, fun m hm => ?_⟩
  rw [mem_conjSub_iff] at hm
  have e := hL.2 _ hm
  have hxu' : x⁻¹ * u = u * x⁻¹ :=
    calc x⁻¹ * u = x⁻¹ * (u * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * u) * x⁻¹ := by rw [hxu]
      _ = u * x⁻¹ := by group
  calc m * u = x * (x⁻¹ * m * x) * (x⁻¹ * u) := by group
    _ = x * (x⁻¹ * m * x) * (u * x⁻¹) := by rw [hxu']
    _ = x * ((x⁻¹ * m * x) * u) * x⁻¹ := by group
    _ = x * (u * (x⁻¹ * m * x)) * x⁻¹ := by rw [e]
    _ = (x * u) * (x⁻¹ * m * x) * x⁻¹ := by group
    _ = (u * x) * (x⁻¹ * m * x) * x⁻¹ := by rw [hxu]
    _ = u * m := by group

omit [Finite G] hS in
theorem pSpan_centMembers_le (u : G) :
    pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
  pSpan_le fun _ hM m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hM.2 m hm)

omit [Finite G] in
theorem conjSub_mem_centMembers (u : G) {L : Subgroup G} (hL : L ∈ centMembers Ω u) {x : G}
    (hx : x ∈ pSpan (centMembers Ω u)) : conjSub x L ∈ centMembers Ω u :=
  hS.conjSub_mem_centMembers_of_comm
    (Subgroup.mem_centralizer_singleton_iff.mp (pSpan_centMembers_le u hx)) hL

theorem card_pSpan_centMembers_lt {u : G} (hu1 : u ≠ 1) :
    Nat.card ↥(pSpan (centMembers Ω u)) < Nat.card G := by
  have hCt : Subgroup.centralizer ({u} : Set G) ≠ ⊤ := by
    intro htop
    apply hu1
    have hzc : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rw [hS.center, Subgroup.mem_bot] at hzc
    exact hzc
  have hlt' : pSpan (centMembers Ω u) < ⊤ :=
    lt_of_le_of_lt (pSpan_centMembers_le u) (lt_top_iff_ne_top.mpr hCt)
  have := Subgroup.card_lt_of_lt hlt'
  rwa [Subgroup.card_top] at this

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
