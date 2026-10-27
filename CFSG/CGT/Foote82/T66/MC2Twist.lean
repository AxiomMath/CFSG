module

public import CFSG.CGT.Foote82.T66.MC2Alt
public import CFSG.CGT.Foote82.T66.MC2Perm
import CFSG.Quasithin.Background.G11Basic
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11 Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem cfix_conj (g x : GLV V) :
    cfix (g * x * g⁻¹) = (cfix x).map (g : V →ₗ[ZMod 2] V) := by
  ext v
  rw [mem_cfix, Submodule.mem_map]
  change g (x (g.symm v)) = v ↔ ∃ u, u ∈ cfix x ∧ g u = v
  constructor
  · intro hv
    refine ⟨g.symm v, mem_cfix.2 ?_, g.apply_symm_apply v⟩
    apply g.injective
    rw [hv, g.apply_symm_apply]
  · rintro ⟨u, hu, rfl⟩
    rw [mem_cfix] at hu
    rw [g.symm_apply_apply, hu]

theorem cfix_le_of_fpf {L : Subgroup (GLV V)} (x y : ↥L)
    (hx : ∀ v, (x : GLV V) ((x : GLV V) ((x : GLV V) v)) = v)
    (hxy : (x : GLV V) * y = y * x) (hy : ∀ q, rhoT L y q = q → q = 0) :
    cfix (y : GLV V) ≤ cfix (x : GLV V) := by
  intro w hw
  rw [mem_cfix] at hw ⊢
  set w₂ := (x : GLV V) ((x : GLV V) w) - (x : GLV V) w with hw₂
  have hw₂c : w₂ ∈ comm1 (x : GLV V) := mem_comm1.2 ⟨(x : GLV V) w, rfl⟩
  have hw₂A : w₂ ∈ commSpace L ⊤ := comm1_le_commSpace x.2 hw₂c
  have hc : ∀ v, (y : GLV V) ((x : GLV V) v) = (x : GLV V) ((y : GLV V) v) := fun v => by
    have h := congrArg (fun f : GLV V => f v) hxy
    simp only [LinearEquiv.mul_apply] at h
    exact h.symm
  have hyw₂ : (y : GLV V) w₂ = w₂ := by
    rw [hw₂, map_sub, hc, hc, hw]
  have hq := hy (Submodule.Quotient.mk ⟨w₂, hw₂A⟩) (by
    rw [rhoT_mk]
    congr 1
    exact Subtype.ext hyw₂)
  have hC : w₂ ∈ fixedSpace L :=
    (Submodule.Quotient.mk_eq_zero ((fixedSpace L).comap (commSpace L ⊤).subtype)).1 hq
  have hw₂0 : w₂ = 0 := by
    have : w₂ ∈ cfix (x : GLV V) ⊓ comm1 (x : GLV V) := ⟨mem_cfix.2 (hC x x.2), hw₂c⟩
    rwa [cfix_inf_comm1 hx] at this
  exact (x : GLV V).injective (sub_eq_zero.1 hw₂0)

theorem conj_c3 {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) (a b c : α) :
    g * c3 a b c * g⁻¹ = c3 (g a) (g b) (g c) := by
  rw [c3, c3, Equiv.swap_apply_apply g a b, Equiv.swap_apply_apply g a c]
  group

theorem exists_alt_map6 {m : ℕ} (hm : 8 ≤ m) {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : Fin m}
    (ha : [a₁, a₂, a₃, a₄, a₅, a₆].Nodup) (hb : [b₁, b₂, b₃, b₄, b₅, b₆].Nodup) :
    ∃ g ∈ alternatingGroup (Fin m), g a₁ = b₁ ∧ g a₂ = b₂ ∧ g a₃ = b₃ ∧ g a₄ = b₄ ∧
      g a₅ = b₅ ∧ g a₆ = b₆ := by
  have h6 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin m)) (Fin m) 6 := by
    have := alternatingGroup.isMultiplyPretransitive (α := Fin m)
    exact MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin m) - 2) (by simp; omega)
      (by simp)
  let ea : Fin 6 ↪ Fin m := ⟨[a₁, a₂, a₃, a₄, a₅, a₆].get, List.nodup_iff_injective_get.1 ha⟩
  let eb : Fin 6 ↪ Fin m := ⟨[b₁, b₂, b₃, b₄, b₅, b₆].get, List.nodup_iff_injective_get.1 hb⟩
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.1 h6) ea eb
  have hgi : ∀ i, (g : Perm (Fin m)) (ea i) = eb i := fun i => by
    have := DFunLike.congr_fun hg i
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, Perm.smul_def] using this
  exact ⟨g, g.2, hgi 0, hgi 1, hgi 2, hgi 3, hgi 4, hgi 5⟩

theorem finite_end : Finite (V →ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V →ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective

theorem card_end_le (h : Module.finrank (ZMod 2) V ≤ 4) :
    Nat.card (V →ₗ[ZMod 2] V) ≤ 2 ^ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_end (V := V)
  rw [← FiniteField.pow_finrank_eq_natCard 2 (V →ₗ[ZMod 2] V), Module.finrank_linearMap]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem twist_false {G L : Subgroup (GLV V)} {m : ℕ} (hm : 9 ≤ m)
    {ψ : ↥G ≃* alternatingGroup (Fin m)} {F : Set (Fin m)} (hd : AltData G L ψ F)
    (hirr : IsIrr G ⊤) (hdim : Module.finrank (ZMod 2) (TildeV L) ≤ 4)
    {a b c d e f : Fin m} (hn : [a, b, c, d, e, f].Nodup) {ℓ₀ ℓ₁ : ↥L}
    (h₀ : hd.jL ℓ₀ = c3 a b c) (h₁ : hd.jL ℓ₁ = c3 d e f)
    (hf₀ : ∀ q, rhoT L ℓ₀ q = q → q = 0) (hf₁ : ∀ q, rhoT L ℓ₁ q = q → q = 0) : False := by
  have hn' := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hn'
  obtain ⟨⟨hab, hac, -, -, -⟩, ⟨hbc, -, -, -⟩, -, ⟨hde, hdf⟩, hef⟩ := hn'
  have hcomm : ℓ₀ * ℓ₁ = ℓ₁ * ℓ₀ := hd.jL_injective (by
    rw [map_mul, map_mul, h₀, h₁]
    exact c3_commute hn)
  have hcube : ∀ {ℓ : ↥L} {x y z : Fin m}, x ≠ y → x ≠ z → y ≠ z → hd.jL ℓ = c3 x y z →
      ∀ v, (ℓ : GLV V) ((ℓ : GLV V) ((ℓ : GLV V) v)) = v := by
    intro ℓ x y z hxy hxz hyz hℓ v
    have h3 : ℓ ^ 3 = 1 := hd.jL_injective (by
      rw [map_pow, hℓ, map_one]
      exact c3_pow_three hxy hxz hyz)
    have h3' : (ℓ : GLV V) ^ 3 = 1 := by rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
    have h := congrArg (fun g : GLV V => g v) h3'
    simp only [pow_three] at h
    exact h
  have hC : cfix (ℓ₀ : GLV V) = cfix (ℓ₁ : GLV V) :=
    le_antisymm (cfix_le_of_fpf ℓ₁ ℓ₀ (hcube hde hdf hef h₁)
        (congrArg Subtype.val hcomm.symm) hf₀)
      (cfix_le_of_fpf ℓ₀ ℓ₁ (hcube hab hac hbc h₀) (congrArg Subtype.val hcomm) hf₁)
  have P3 : ∀ (g₁ g₂ : ↥G) (x₁ x₂ x₃ x₄ x₅ x₆ : Fin m), [x₁, x₂, x₃, x₄, x₅, x₆].Nodup →
      iota ψ g₁ = c3 x₁ x₂ x₃ → iota ψ g₂ = c3 x₄ x₅ x₆ →
      cfix (g₁ : GLV V) = cfix (g₂ : GLV V) := by
    intro g₁ g₂ x₁ x₂ x₃ x₄ x₅ x₆ hx hg₁ hg₂
    obtain ⟨σ, hσA, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_alt_map6 (by omega) hn hx
    set k : ↥G := ψ.symm ⟨σ, hσA⟩ with hk
    have hιk : iota ψ k = σ := iota_symm ψ hσA
    have hk₁ : k * Subgroup.inclusion hd.le ℓ₀ * k⁻¹ = g₁ := iota_injective ψ (by
      rw [map_mul, map_mul, map_inv, hιk, hg₁]
      change σ * hd.jL ℓ₀ * σ⁻¹ = _
      rw [h₀, conj_c3, e₁, e₂, e₃])
    have hk₂ : k * Subgroup.inclusion hd.le ℓ₁ * k⁻¹ = g₂ := iota_injective ψ (by
      rw [map_mul, map_mul, map_inv, hιk, hg₂]
      change σ * hd.jL ℓ₁ * σ⁻¹ = _
      rw [h₁, conj_c3, e₄, e₅, e₆])
    rw [← hk₁, ← hk₂]
    change cfix ((k : GLV V) * (ℓ₀ : GLV V) * (k : GLV V)⁻¹) =
      cfix ((k : GLV V) * (ℓ₁ : GLV V) * (k : GLV V)⁻¹)
    rw [cfix_conj, cfix_conj, hC]
  have P4 : ∀ (g₁ g₂ : ↥G) (x₁ x₂ x₃ y₁ y₂ y₃ : Fin m), [x₁, x₂, x₃].Nodup →
      [y₁, y₂, y₃].Nodup → iota ψ g₁ = c3 x₁ x₂ x₃ → iota ψ g₂ = c3 y₁ y₂ y₃ →
      cfix (g₁ : GLV V) = cfix (g₂ : GLV V) := by
    classical
    intro g₁ g₂ x₁ x₂ x₃ y₁ y₂ y₃ hx hy hg₁ hg₂
    set S : Finset (Fin m) := Finset.univ \ {x₁, x₂, x₃, y₁, y₂, y₃} with hS
    have hScard : 3 ≤ S.card := by
      have h1 : ({x₁, x₂, x₃, y₁, y₂, y₃} : Finset (Fin m)).card ≤ 6 := Finset.card_le_six
      have h2 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m))
        {x₁, x₂, x₃, y₁, y₂, y₃}
      rw [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h2
      rw [hS]
      omega
    obtain ⟨z, hz, hzS⟩ := exists_injective_fin (k := 3) hScard
    have hzS' : ∀ i, z i ∉ ({x₁, x₂, x₃, y₁, y₂, y₃} : Finset (Fin m)) := fun i =>
      (Finset.mem_sdiff.1 (hzS i)).2
    have hz01 : z 0 ≠ z 1 := fun h => absurd (hz h) (by decide)
    have hz02 : z 0 ≠ z 2 := fun h => absurd (hz h) (by decide)
    have hz12 : z 1 ≠ z 2 := fun h => absurd (hz h) (by decide)
    set g₃ : ↥G := ψ.symm ⟨c3 (z 0) (z 1) (z 2), c3_mem_alternatingGroup hz01 hz02 hz12⟩
    have hg₃ : iota ψ g₃ = c3 (z 0) (z 1) (z 2) := iota_symm ψ _
    have hnz : ∀ (w₁ w₂ w₃ : Fin m), [w₁, w₂, w₃].Nodup →
        (∀ i, z i ∉ ({w₁, w₂, w₃} : Finset (Fin m))) → [w₁, w₂, w₃, z 0, z 1, z 2].Nodup := by
      intro w₁ w₂ w₃ hw hzw
      have h0 := hzw 0
      have h1 := hzw 1
      have h2 := hzw 2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h0 h1 h2
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true] at hw ⊢
      refine ⟨⟨hw.1.1, hw.1.2, ?_, ?_, ?_⟩, ⟨hw.2, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨hz01, hz02⟩, hz12⟩
      all_goals first
        | exact fun h => h0.1 h.symm | exact fun h => h1.1 h.symm | exact fun h => h2.1 h.symm
        | exact fun h => h0.2.1 h.symm | exact fun h => h1.2.1 h.symm
        | exact fun h => h2.2.1 h.symm | exact fun h => h0.2.2 h.symm
        | exact fun h => h1.2.2 h.symm | exact fun h => h2.2.2 h.symm
    have hzx : ∀ i, z i ∉ ({x₁, x₂, x₃} : Finset (Fin m)) := fun i h => by
      apply hzS' i
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with h | h | h <;> simp [h]
    have hzy : ∀ i, z i ∉ ({y₁, y₂, y₃} : Finset (Fin m)) := fun i h => by
      apply hzS' i
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with h | h | h <;> simp [h]
    rw [P3 g₁ g₃ _ _ _ _ _ _ (hnz _ _ _ hx hzx) hg₁ hg₃,
      P3 g₂ g₃ _ _ _ _ _ _ (hnz _ _ _ hy hzy) hg₂ hg₃]
  have hinv : Invariant G (cfix (ℓ₀ : GLV V)) := by
    intro g hg v hv
    set g' : ↥G := ⟨g, hg⟩
    have hconj : iota ψ (g' * Subgroup.inclusion hd.le ℓ₀ * g'⁻¹) =
        c3 (iota ψ g' a) (iota ψ g' b) (iota ψ g' c) := by
      rw [map_mul, map_mul, map_inv]
      change iota ψ g' * hd.jL ℓ₀ * (iota ψ g')⁻¹ = _
      rw [h₀, conj_c3]
    have hdist : [iota ψ g' a, iota ψ g' b, iota ψ g' c].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact ⟨⟨fun h => hab ((iota ψ g').injective h), fun h => hac ((iota ψ g').injective h)⟩,
        fun h => hbc ((iota ψ g').injective h)⟩
    have hP := P4 (g' * Subgroup.inclusion hd.le ℓ₀ * g'⁻¹) (Subgroup.inclusion hd.le ℓ₀) _ _ _
      a b c hdist (by simp [hab, hac, hbc]) hconj h₀
    have : g v ∈ cfix ((g : GLV V) * (ℓ₀ : GLV V) * (g : GLV V)⁻¹) := by
      rw [cfix_conj]
      exact ⟨v, hv, rfl⟩
    exact hP ▸ this
  rcases CFSG.Quasithin.G11.IsIrr.eq_bot_or_eq hirr hinv le_top with h0 | h0
  ·
    have hx0 := hcube hab hac hbc h₀
    have htop : comm1 (ℓ₀ : GLV V) = ⊤ := by
      rw [← cfix_sup_comm1 hx0, h0, bot_sup_eq]
    have hdimV : Module.finrank (ZMod 2) V ≤ 4 := by
      have h1 := finrank_comm1_le ℓ₀ hx0
      rw [htop, finrank_top] at h1
      exact h1.trans ((Submodule.finrank_le _).trans hdim)
    have hcardG : Nat.card ↥G ≤ 2 ^ 16 := by
      have := finite_end (V := V)
      refine le_trans (Nat.card_le_card_of_injective (fun g : ↥G => ((g : GLV V) : V →ₗ[ZMod 2] V))
        fun g₁ g₂ h => Subtype.ext (LinearEquiv.toLinearMap_injective h)) (card_end_le hdimV)
    rw [Nat.card_congr ψ.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_alternatingGroup_fin (by omega)] at hcardG
    have h9 : Nat.factorial 9 ≤ m.factorial := Nat.factorial_le hm
    have : Nat.factorial 9 = 362880 := by decide
    omega
  ·
    have h1 : (ℓ₀ : GLV V) = 1 := LinearEquiv.ext fun v => mem_cfix.1 (h0 ▸ Submodule.mem_top)
    have h1' : hd.jL ℓ₀ = 1 := by
      have : ℓ₀ = 1 := Subtype.ext h1
      rw [this, map_one]
    have h2 : c3 a b c a = c := by
      rw [c3, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
    rw [← h₀, h1'] at h2
    exact hac h2
end MC2

end CFSG.CGT.Foote82
