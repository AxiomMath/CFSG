module

public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints
public import CFSG.GH74.GLS.Stage4.T2SL2Defs
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Order.CompletePartialOrder
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped TensorProduct

namespace CFSG.GH74.GLS.Stage4.Rest

section SL2Aux

variable {F : Type} [Field F]

theorem sl2Dinv_conj_sl2U (s : Fˣ) (c : F) :
    (sl2D s)⁻¹ * sl2U c * sl2D s = sl2U (((s⁻¹ : Fˣ) : F) ^ 2 * c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, pow_two]
  field_simp

theorem sl2U_pow (c : F) (n : ℕ) : sl2U c ^ n = sl2U (n • c) := by
  induction n with
  | zero => simp [sl2U_zero]
  | succ n ih => rw [pow_succ, ih, ← sl2U_add, succ_nsmul]

theorem uSub_eq {x : SL2 F} (hx : x ∈ uSub F) : ∃ c, x = sl2U c := by
  refine ⟨(x : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  obtain ⟨h00, h11, h10⟩ := hx
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]

theorem sl2U_mem_uSub (c : F) : sl2U c ∈ uSub F := by
  simp [uSub]

end SL2Aux

theorem sl2_cross_dim :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → 5 ≤ Nat.card F →
      ¬ p ∣ Nat.card F →
        ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
          (ρ : Representation (ZMod p) (Matrix.SpecialLinearGroup (Fin 2) F) V), Function.Injective ρ →
            (Nat.card F - 1) / 2 ≤ Module.finrank (ZMod p) V := by
  intro p hp hp2 F _ _ hodd h5 hpq V _ _ _ ρ hρ
  classical
  have hFact : Fact p.Prime := ⟨hp⟩
  let K : Subgroup (SL2 F) := uSub F
  let E := AlgebraicClosure (ZMod p)
  let W := E ⊗[ZMod p] V
  let ρE : Representation E (SL2 F) W := baseChangeRep E ρ
  have hW : Module.finrank E W = Module.finrank (ZMod p) V := Module.finrank_baseChange
  let f : K → Module.End E W := fun k => ρE k
  have hKcomm : ∀ k l : K, k * l = l * k := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := uSub_eq hx
    obtain ⟨d, rfl⟩ := uSub_eq hy
    apply Subtype.ext
    show sl2U c * sl2U d = sl2U d * sl2U c
    rw [← sl2U_add, ← sl2U_add, add_comm]
  have hcomm : ∀ k l : K, Commute (f k) (f l) := by
    intro k l
    show ρE k * ρE l = ρE l * ρE k
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hKcomm k l)
  have hq0 : ((Nat.card F : ℕ) : E) ≠ 0 := by
    intro h
    exact hpq ((CharP.cast_eq_zero_iff E p _).1 h)
  have hss : ∀ k : K, Module.End.IsFinitelySemisimple (f k) := by
    intro k
    apply isFinitelySemisimple_of_pow_eq_one (m := Nat.card F)
    · show ρE k ^ Nat.card F = 1
      rw [← map_pow]
      have : (k : SL2 F) ^ Nat.card F = 1 := by
        obtain ⟨c, hc⟩ := uSub_eq k.2
        rw [hc, sl2U_pow, card_nsmul_eq_zero', sl2U_zero]
      rw [this, map_one]
    · exact hq0
  obtain ⟨hind, htop⟩ := iSupIndep_iInf_eigenspace_and_iSup_eq_top f hcomm hss
  set Vχ : (K → E) → Submodule E W := fun χ => ⨅ k, Module.End.eigenspace (f k) (χ k) with hVχ
  have hmemVχ : ∀ (χ : K → E) (v : W), v ∈ Vχ χ ↔ ∀ k : K, ρE k v = χ k • v := by
    intro χ v
    simp only [hVχ, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, f]
  have hconj : ∀ (s : Fˣ) (k : K), (sl2D s)⁻¹ * (k : SL2 F) * sl2D s ∈ K := by
    intro s k
    obtain ⟨c, hc⟩ := uSub_eq k.2
    rw [hc, sl2Dinv_conj_sl2U]
    exact sl2U_mem_uSub _
  let act : Fˣ → (K → E) → (K → E) := fun s χ k =>
    χ ⟨(sl2D s)⁻¹ * (k : SL2 F) * sl2D s, hconj s k⟩
  have hmaps : ∀ (s : Fˣ) (χ : K → E), ∀ v ∈ Vχ χ, ρE (sl2D s) v ∈ Vχ (act s χ) := by
    intro s χ v hv
    rw [hmemVχ] at hv ⊢
    intro k
    have h1 : ρE k (ρE (sl2D s) v) = ρE (sl2D s) (ρE ((sl2D s)⁻¹ * (k : SL2 F) * sl2D s) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    have h2 : ρE ((sl2D s)⁻¹ * (k : SL2 F) * sl2D s) v =
        χ ⟨(sl2D s)⁻¹ * (k : SL2 F) * sl2D s, hconj s k⟩ • v :=
      hv ⟨(sl2D s)⁻¹ * (k : SL2 F) * sl2D s, hconj s k⟩
    rw [h1, h2, map_smul]
  have hne : ∀ (s : Fˣ) (χ : K → E), Vχ χ ≠ ⊥ → Vχ (act s χ) ≠ ⊥ := by
    intro s χ hχ hbot
    apply hχ
    rw [eq_bot_iff]
    intro v hv
    have h1 := hmaps s χ v hv
    rw [hbot, Submodule.mem_bot] at h1
    have h2 := congrArg (ρE (sl2D s)⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h2
    exact (Submodule.mem_bot E).mpr h2
  let I := {χ : K → E // Vχ χ ≠ ⊥}
  have hIfin : Finite I := by
    have := hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  have hmult : ∀ (χ : K → E), Vχ χ ≠ ⊥ → ∀ k l : K, χ (k * l) = χ k * χ l := by
    intro χ hχ k l
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    rw [hmemVχ] at hv
    have h1 : ρE ((k * l : K) : SL2 F) v = χ (k * l) • v := hv _
    have h2 : ρE ((k * l : K) : SL2 F) v = (χ k * χ l) • v := by
      rw [show ((k * l : K) : SL2 F) = (k : SL2 F) * l from rfl, map_mul, Module.End.mul_apply,
        hv l, map_smul, hv k, smul_smul, mul_comm]
    have := h1.symm.trans h2
    exact (smul_left_injective E hv0 this).symm.symm
  have hnontriv : ∃ χ₀ : K → E, Vχ χ₀ ≠ ⊥ ∧ ∃ k₀ : K, χ₀ k₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : ∀ (w : W) (k : K), ρE k w = w := by
      intro w k
      have hw : w ∈ ⨆ χ, Vχ χ := by rw [htop]; trivial
      refine Submodule.iSup_induction (fun χ => Vχ χ) (motive := fun w => ρE k w = w) hw ?_ ?_ ?_
      · intro χ w hwχ
        by_cases hbot : Vχ χ = ⊥
        · rw [hbot, Submodule.mem_bot] at hwχ
          rw [hwχ, map_zero]
        · rw [hmemVχ] at hwχ
          rw [hwχ k, hcon χ hbot k, one_smul]
      · simp
      · intro x y hx hy
        rw [map_add, hx, hy]
    have hinv : Representation.invariants (ρE.comp K.subtype) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      rw [Representation.mem_invariants]
      intro k
      exact h1 w k
    have hdim := finrank_invariants_baseChange (E := E) (ρ.comp K.subtype)
    have hdim' : Module.finrank (ZMod p) (Representation.invariants (ρ.comp K.subtype)) =
        Module.finrank (ZMod p) V := by
      rw [← hdim, ← hW]
      have : Representation.invariants ((baseChangeRep E ρ).comp K.subtype) = ⊤ := hinv
      show Module.finrank E (Representation.invariants ((baseChangeRep E ρ).comp K.subtype)) = _
      rw [this, finrank_top]
    have htop' : Representation.invariants (ρ.comp K.subtype) = ⊤ :=
      Submodule.eq_top_of_finrank_eq hdim'
    have hk : ρ (sl2U (1 : F)) = 1 := by
      ext v
      have : v ∈ Representation.invariants (ρ.comp K.subtype) := by rw [htop']; trivial
      rw [Representation.mem_invariants] at this
      exact this ⟨sl2U 1, sl2U_mem_uSub 1⟩
    have := hρ (hk.trans (map_one ρ).symm)
    have h01 := sl2U_injective (this.trans sl2U_zero.symm)
    exact one_ne_zero h01
  obtain ⟨χ₀, hχ₀, k₀, hk₀⟩ := hnontriv
  let g : F → E := fun c => χ₀ ⟨sl2U c, sl2U_mem_uSub c⟩
  have hg_add : ∀ c d : F, g (c + d) = g c * g d := by
    intro c d
    have := hmult χ₀ hχ₀ ⟨sl2U c, sl2U_mem_uSub c⟩ ⟨sl2U d, sl2U_mem_uSub d⟩
    simp only [g]
    rw [← this]
    congr 1
    apply Subtype.ext
    exact sl2U_add c d
  have hg_one : g 0 = 1 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ₀
    rw [hmemVχ] at hv
    have h1 := hv ⟨sl2U 0, sl2U_mem_uSub 0⟩
    have h2 : ρE (sl2U (0 : F)) v = v := by rw [sl2U_zero, map_one]; rfl
    have : (g 0) • v = (1 : E) • v := by
      rw [one_smul]
      exact h1.symm.trans h2
    exact smul_left_injective E hv0 this
  have hg_ne : ∀ c, g c ≠ 0 := by
    intro c h0
    have := hg_add c (-c)
    rw [add_neg_cancel, hg_one, h0, zero_mul] at this
    exact one_ne_zero this
  have hg_triv : (∀ d : F, g d = 1) → False := by
    intro hall
    obtain ⟨c₀, hc₀⟩ := uSub_eq k₀.2
    apply hk₀
    have : k₀ = ⟨sl2U c₀, sl2U_mem_uSub c₀⟩ := Subtype.ext hc₀
    rw [this]
    exact hall c₀
  let ψ : Fˣ → I := fun s => ⟨act s χ₀, hne s χ₀ hχ₀⟩
  have hfib : ∀ s s' : Fˣ, ψ s = ψ s' → s' = s ∨ s' = -s := by
    intro s s' hss'
    have h1 : act s χ₀ = act s' χ₀ := congrArg Subtype.val hss'
    have hgg : ∀ c : F, g (((s⁻¹ : Fˣ) : F) ^ 2 * c) = g (((s'⁻¹ : Fˣ) : F) ^ 2 * c) := by
      intro c
      have := congrFun h1 ⟨sl2U c, sl2U_mem_uSub c⟩
      simp only [act] at this
      have e1 : (⟨(sl2D s)⁻¹ * (⟨sl2U c, sl2U_mem_uSub c⟩ : K) * sl2D s, hconj s ⟨sl2U c, sl2U_mem_uSub c⟩⟩ : K) =
          ⟨sl2U (((s⁻¹ : Fˣ) : F) ^ 2 * c), sl2U_mem_uSub _⟩ :=
        Subtype.ext (sl2Dinv_conj_sl2U s c)
      have e2 : (⟨(sl2D s')⁻¹ * (⟨sl2U c, sl2U_mem_uSub c⟩ : K) * sl2D s', hconj s' ⟨sl2U c, sl2U_mem_uSub c⟩⟩ : K) =
          ⟨sl2U (((s'⁻¹ : Fˣ) : F) ^ 2 * c), sl2U_mem_uSub _⟩ :=
        Subtype.ext (sl2Dinv_conj_sl2U s' c)
      rw [e1, e2] at this
      exact this
    set a : F := ((s⁻¹ : Fˣ) : F) ^ 2 with ha
    set a' : F := ((s'⁻¹ : Fˣ) : F) ^ 2 with ha'
    by_cases haa : a = a'
    ·
      have hs : (s : F) ^ 2 = (s' : F) ^ 2 := by
        have h1 : ((s⁻¹ : Fˣ) : F) = (s : F)⁻¹ := by simp
        have h2 : ((s'⁻¹ : Fˣ) : F) = (s' : F)⁻¹ := by simp
        rw [ha, ha', h1, h2] at haa
        have hs0 : (s : F) ≠ 0 := s.ne_zero
        have hs0' : (s' : F) ≠ 0 := s'.ne_zero
        field_simp at haa
        exact haa.symm
      have : ((s' : F) / s) ^ 2 = 1 := by
        have hs0 : (s : F) ≠ 0 := s.ne_zero
        field_simp
        exact hs.symm
      have h2 : ((s' : F) / s) * ((s' : F) / s) = 1 := by rw [← pow_two]; exact this
      rcases mul_self_eq_one_iff.1 h2 with h | h
      · left
        apply Units.ext
        have hs0 : (s : F) ≠ 0 := s.ne_zero
        field_simp at h
        exact h
      · right
        apply Units.ext
        have hs0 : (s : F) ≠ 0 := s.ne_zero
        field_simp at h
        simpa using h
    · exfalso
      apply hg_triv
      intro d
      have hsub : a - a' ≠ 0 := sub_ne_zero.2 haa
      have e : g (a * (d / (a - a'))) = g ((a - a') * (d / (a - a')) ) * g (a' * (d / (a - a'))) := by
        rw [← hg_add]
        congr 1
        ring
      have h2 := hgg (d / (a - a'))
      rw [h2] at e
      have h3 : g ((a - a') * (d / (a - a'))) = 1 := by
        have hne0 := hg_ne (a' * (d / (a - a')))
        have : g ((a - a') * (d / (a - a'))) * g (a' * (d / (a - a'))) = 1 * g (a' * (d / (a - a'))) := by
          rw [← e, one_mul]
        exact mul_right_cancel₀ hne0 this
      rw [mul_div_cancel₀ _ hsub] at h3
      exact h3
  have : Fintype I := Fintype.ofFinite I
  have : Fintype F := Fintype.ofFinite F
  have hcardI : Fintype.card I ≤ Module.finrank E W := by
    choose w hw hw0 using fun χ : I => Submodule.exists_mem_ne_zero_of_ne_bot χ.2
    have hli : LinearIndependent E w :=
      iSupIndep.linearIndependent (fun χ : I => Vχ χ.1) (hind.comp Subtype.val_injective) hw hw0
    exact hli.fintype_card_le_finrank
  have hunits : Fintype.card Fˣ ≤ 2 * (Finset.image ψ Finset.univ).card := by
    have := Finset.card_le_mul_card_image (f := ψ) Finset.univ 2 (by
      intro b hb
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hb
      calc (Finset.filter (fun a => ψ a = ψ s) Finset.univ).card ≤ ({s, -s} : Finset Fˣ).card := by
            apply Finset.card_le_card
            intro a ha
            have := hfib s a (Finset.mem_filter.1 ha).2.symm
            rcases this with h | h
            · simp [h]
            · simp [h]
        _ ≤ 2 := Finset.card_le_two)
    simpa using this
  have hF : Fintype.card Fˣ = Nat.card F - 1 := by
    rw [Fintype.card_units, Nat.card_eq_fintype_card]
  have hfin : Nat.card F - 1 ≤ 2 * Module.finrank (ZMod p) V := by
    rw [← hF, ← hW]
    calc Fintype.card Fˣ ≤ 2 * (Finset.image ψ Finset.univ).card := hunits
      _ ≤ 2 * Fintype.card I := by
        apply Nat.mul_le_mul_left
        calc (Finset.image ψ Finset.univ).card ≤ (Finset.univ : Finset I).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = Fintype.card I := Finset.card_univ
      _ ≤ 2 * Module.finrank E W := Nat.mul_le_mul_left _ hcardI
  exact Nat.div_le_of_le_mul (by omega)

end CFSG.GH74.GLS.Stage4.Rest
