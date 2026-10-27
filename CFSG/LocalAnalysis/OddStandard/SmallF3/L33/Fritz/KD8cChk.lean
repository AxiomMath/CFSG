module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cTr

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem ofCode_codeMC : ∀ a : MC, ofCode (codeMC a) = a ∧ ofCode (256 + codeMC a) = a ∧
    codeMC a < 256 := by
  decide +kernel

theorem ofCodeE_codeE {D : ExtData MC} (x : Ext D) : ofCodeE (codeE x) = x := by
  obtain ⟨a, e⟩ := x
  obtain ⟨h1, h2, h3⟩ := ofCode_codeMC a
  have k0 : (256 * 0 + codeMC a) / 256 = 0 := by omega
  have k1 : (256 * 1 + codeMC a) / 256 = 1 := by omega
  cases e
  · refine Ext.ext ?_ ?_
    · show ofCode (256 * 0 + codeMC a) = a
      rw [mul_zero, zero_add, h1]
    · show ((256 * 0 + codeMC a) / 256 % 2 == 1) = false
      rw [k0]
      rfl
  · refine Ext.ext ?_ ?_
    · show ofCode (256 * 1 + codeMC a) = a
      rw [mul_one, h2]
    · show ((256 * 1 + codeMC a) / 256 % 2 == 1) = true
      rw [k1]
      rfl

theorem conj_comm_iff' {G : Type*} [Group G] (c g x : G) :
    c * g * c⁻¹ * (c * x * c⁻¹) = c * x * c⁻¹ * (c * g * c⁻¹) ↔ g * x = x * g := by
  constructor
  · intro h
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  · intro h
    calc c * g * c⁻¹ * (c * x * c⁻¹) = c * (g * x) * c⁻¹ := by group
      _ = c * (x * g) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * (c * g * c⁻¹) := by group

theorem ccE_conj {D : ExtData MC} (c x : Ext D) : ccE (c * x * c⁻¹) = ccE x := by
  classical
  unfold ccE
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv
    fun g => (conj_comm_iff' c g x).symm)).symm

@[expose] def vB (bs n : ℕ) : Multiplicative (ZMod 2) :=
  if bs.testBit n then Multiplicative.ofAdd 1 else 1

theorem exists_chi0 (bs : ℕ) (hpc : MC.PcX (vB bs 0) (vB bs 1) (vB bs 2) (vB bs 3) (vB bs 4)
    (vB bs 5) (vB bs 6) (vB bs 7))
    (hnf : ∀ a : MC, nfProd [vB bs 0, vB bs 1, vB bs 2, vB bs 3, vB bs 4, vB bs 5, vB bs 6,
      vB bs 7] (MC.nfBits a) = if chi0B bs a then Multiplicative.ofAdd 1 else 1) :
    ∃ χ₀ : MC →* Multiplicative (ZMod 2),
      ∀ a, χ₀ a = if chi0B bs a then Multiplicative.ofAdd 1 else 1 := by
  obtain ⟨ι, h1, h2, h3, h4, h5, h6, h7, h8⟩ := MC.exists_hom hpc
  refine ⟨ι, fun a => ?_⟩
  conv_lhs => rw [MC.nf_spec a]
  rw [map_nfProd]
  simp only [MC.gens, List.map_cons, List.map_nil, h1, h2, h3, h4, h5, h6, h7, h8]
  exact hnf a

theorem z2_conj : ∀ a b : Multiplicative (ZMod 2), a * b * a⁻¹ = b := by decide

theorem exists_chi {j : Fin 8} (hj3 : j ≠ 3) (hj4 : j ≠ 4) (i : Fin 2) (bs : ℕ) (qb : Bool)
    {χ₀ : MC →* Multiplicative (ZMod 2)}
    (hχ₀ : ∀ a, χ₀ a = if chi0B bs a then Multiplicative.ofAdd 1 else 1)
    (hφ : ∀ a : MC, chi0B bs (phiR j a) = chi0B bs a) (hs : chi0B bs (sR j i) = false) :
    ∃ χ : Ext (D j hj3 hj4 i) →* Multiplicative (ZMod 2),
      ∀ x, χ x = if chiB bs qb x then Multiplicative.ofAdd 1 else 1 := by
  have hq : ∀ b, (if qb then Multiplicative.ofAdd (1 : ZMod 2) else 1) * χ₀ b *
      (if qb then Multiplicative.ofAdd (1 : ZMod 2) else 1)⁻¹ = χ₀ ((D j hj3 hj4 i).φ b) := by
    intro b
    rw [z2_conj]
    show χ₀ b = χ₀ (phiR j b)
    rw [hχ₀, hχ₀, hφ]
  have hsq : (if qb then Multiplicative.ofAdd (1 : ZMod 2) else 1) *
      (if qb then Multiplicative.ofAdd (1 : ZMod 2) else 1) = χ₀ (D j hj3 hj4 i).s := by
    show _ = χ₀ (sR j i)
    rw [z2_sq, hχ₀, hs]
    rfl
  refine ⟨Ext.lift χ₀ _ hq hsq, fun x => ?_⟩
  obtain ⟨a, e⟩ := x
  show (χ₀ a * bif e then (if qb then Multiplicative.ofAdd (1 : ZMod 2) else 1) else 1) =
    if (chi0B bs a ^^ (qb && e)) then Multiplicative.ofAdd 1 else 1
  rw [hχ₀]
  cases qb <;> cases e <;> cases chi0B bs a <;> decide

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2} (W : T.Lift)

theorem nt_seed {q0 : Bool} (hq0 : q0 = true → ¬ ConjTo t (K.ι MC.w₂)) {r : Ext W.D'}
    (hr : seedB q0 r = true) : ¬ ConjTo t (W.ψ r) := by
  simp only [seedB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true,
    beq_iff_eq] at hr
  obtain ⟨he, h⟩ := hr
  rcases h with (h | h) | ⟨hq, h⟩
  · exact W.nt_F he (Or.inl h)
  · exact W.nt_F he (Or.inr h)
  · rw [W.ψ_e0 he]
    have ha : r.a = MC.w₂ := by
      rw [← (ofCode_codeMC r.a).1, h]
      decide +kernel
    rw [ha]
    exact hq0 hq

theorem chi_ne_one {bs : ℕ} {qb : Bool} {χ : Ext W.D' →* Multiplicative (ZMod 2)}
    (hχ : ∀ x, χ x = if chiB bs qb x then Multiplicative.ofAdd 1 else 1) (x : Ext W.D') :
    χ x ≠ 1 ↔ chiB bs qb x = true := by
  rw [hχ]
  cases chiB bs qb x <;> decide

theorem conjTo_of_conj_eq {c y : Ext W.D'} (h : c * y * c⁻¹ = Ext.incl W.D' MC.t ∨
    c * y * c⁻¹ = Ext.incl W.D' MC.u) : ConjTo t (W.ψ y) := by
  rw [← conjTo_conj_iff (W.ψ c), ← map_inv, ← map_mul, ← map_mul]
  rcases h with h | h
  · rw [h, W.ψ_incl, K.ι_t]
    exact ⟨1, by group⟩
  · rw [h]
    exact W.conjTo_u

theorem false_of_checkA [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) {bs : ℕ}
    {qb q0 : Bool} {reps : List ℕ} {tab g cg : ℕ} {χ : Ext W.D' →* Multiplicative (ZMod 2)}
    (hχ : ∀ x, χ x = if chiB bs qb x then Multiplicative.ofAdd 1 else 1)
    (hq0 : q0 = true → ¬ ConjTo t (K.ι MC.w₂))
    (hc : checkA W.D' bs qb q0 reps tab g cg = true) : False := by
  simp only [checkA, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hreps, h2⟩, h3⟩, hg⟩, hg4⟩, hgt⟩ := hc
  have hrep : ∀ r : Ext W.D', codeE r ∈ reps → ¬ ConjTo t (W.ψ r) := fun r hr => by
    have := hreps _ hr
    rw [ofCodeE_codeE] at this
    exact W.nt_seed hq0 this
  refine W.false_of_A137 hnonab χ (fun x hx2 hx => ?_) (fun x hx hx2 hx4 => ?_)
    (g := ofCodeE g) ((W.chi_ne_one hχ _).mpr hg) hg4 (W.conjTo_of_conj_eq hgt)
  · have hx1 : x ≠ 1 := by
      rintro rfl
      exact hx (map_one χ)
    exact W.nt_conj _ _ (hrep _ (h2 x hx2 hx1 ((W.chi_ne_one hχ x).mp hx)))
  · have hx' : chiB bs qb x = false := by
      have := (W.chi_ne_one hχ x).not.mp (not_not.mpr hx)
      simpa using this
    exact W.nt_conj _ _ (hrep _ (h3 x hx' hx2 hx4))

theorem false_of_checkE [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) {bs : ℕ}
    {qb : Bool} {reps : List ℕ} {tab : ℕ} {χ : Ext W.D' →* Multiplicative (ZMod 2)}
    (hχ : ∀ x, χ x = if chiB bs qb x then Multiplicative.ofAdd 1 else 1)
    (hc : checkE W.D' bs qb reps tab = true) : False := by
  simp only [checkE, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    at hc
  obtain ⟨⟨⟨hu64, hu⟩, hreps⟩, hall⟩ := hc
  refine W.false_of_ext hnonab χ hu64 ((W.chi_ne_one hχ _).mpr hu) fun x hx2 hx64 hx => ?_
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
    exact fun ⟨c, hc⟩ => SD.t_ne_one (A := A) (by
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group)
  have hne : chiB bs qb x ≠ chiB bs qb W.uh := by
    intro h
    apply hx
    rw [hχ, hχ, h]
  have hr := hall x hx2 hx1 hne
  set r := conjE tab x * x * (conjE tab x)⁻¹ with hrdef
  have hrc := hreps _ hr
  rw [ofCodeE_codeE] at hrc
  refine W.nt_conj (conjE tab x) x ?_
  rw [← hrdef]
  have hcc : ccE r = ccE x := ccE_conj _ _
  rcases hrc with (hs | hcc64) | hcnt
  · exact W.nt_seed (q0 := false) (fun h => absurd h (by decide)) hs
  · exact W.nt_card (by omega)
  · exact W.nt_cnt (by omega) hu64 hcnt

end Lift

end T2

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
