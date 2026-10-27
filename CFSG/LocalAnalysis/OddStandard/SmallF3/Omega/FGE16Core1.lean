module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Wt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

section Action

variable (B : Subgroup (OGroup Q))

@[expose] def fgT (g : ↥B) : Module.End (ZMod 3) V :=
  ((g : OGroup Q) : V ≃ₗ[ZMod 3] V).toLinearMap

theorem fgT_mul (g h : ↥B) : fgT B (g * h) = fgT B g * fgT B h :=
  LinearMap.ext fun _ => rfl

theorem fgT_one : fgT B 1 = 1 :=
  LinearMap.ext fun _ => rfl

theorem fgT_injective : Function.Injective (fgT B) := by
  intro g g' h
  exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => LinearMap.congr_fun h v))

theorem fgT_map (g : ↥B) (v : V) : Q (fgT B g v) = Q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (g : OGroup Q).2 v

theorem fgT_polar (g : ↥B) (x y : V) :
    QuadraticMap.polar Q (fgT B g x) (fgT B g y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]
  rw [← map_add, fgT_map, fgT_map, fgT_map]

theorem fgT_sq (hB : IsElemAb2 B 4) (g : ↥B) : fgT B g * fgT B g = 1 := by
  have h : g * g = 1 := Subtype.ext (by simpa [pow_two] using hB.1.2 g g.2)
  rw [← fgT_mul, h, fgT_one]

theorem fgT_comm (hB : IsElemAb2 B 4) (g h : ↥B) : Commute (fgT B g) (fgT B h) := by
  have h' : g * h = h * g := hB.1.1.is_comm.comm g h
  show fgT B g * fgT B h = fgT B h * fgT B g
  rw [← fgT_mul, ← fgT_mul, h']

end Action

section Weights

variable (B : Subgroup (OGroup Q)) [Fintype ↥B] [DecidableEq ↥B]

theorem fgT_eq_of_weights (hB : IsElemAb2 B 4) (g g' : ↥B)
    (h : ∀ χ : ↥B → ZMod 3, fgWt (fgT B) χ ≠ ⊥ → χ g = χ g') : g = g' := by
  have hle : ∀ χ : ↥B → ZMod 3, fgWt (fgT B) χ ≤ LinearMap.eqLocus (fgT B g) (fgT B g') := by
    intro χ
    by_cases hχ : fgWt (fgT B) χ = ⊥
    · rw [hχ]
      exact bot_le
    · intro v hv
      rw [LinearMap.mem_eqLocus]
      rw [mem_fgWt] at hv
      rw [hv g, hv g', h χ hχ]
  have htop : LinearMap.eqLocus (fgT B g) (fgT B g') = ⊤ := by
    apply top_le_iff.mp
    rw [← fgWt_iSup_eq_top (fgT B) (fgT_sq B hB) (fgT_comm B hB)]
    exact iSup_le hle
  have hg : fgT B g = fgT B g' := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.eqLocus (fgT B g) (fgT B g') := by
      rw [htop]
      trivial
    exact LinearMap.mem_eqLocus.mp hv
  exact fgT_injective B hg

theorem fg_four_le_card_weights (hB : IsElemAb2 B 4) :
    4 ≤ (Finset.univ.filter (fun χ : ↥B → ZMod 3 => fgWt (fgT B) χ ≠ ⊥)).card := by
  set W := Finset.univ.filter (fun χ : ↥B → ZMod 3 => fgWt (fgT B) χ ≠ ⊥) with hW
  have hWmem : ∀ χ : ↥W, fgWt (fgT B) χ.1 ≠ ⊥ := fun χ => by
    exact (Finset.mem_filter.mp (show χ.1 ∈ Finset.univ.filter
      (fun χ : ↥B → ZMod 3 => fgWt (fgT B) χ ≠ ⊥) from χ.2)).2
  let Φ : ↥B → (↥W → {u : ZMod 3 // u * u = 1}) := fun g χ =>
    ⟨χ.1 g, fgWt_sq (fgT B) (fgT_sq B hB) (hWmem χ) g⟩
  have hΦ : Function.Injective Φ := by
    intro g g' h
    apply fgT_eq_of_weights B hB g g'
    intro χ hχ
    have h1 := congrFun h ⟨χ, by simp [hW, hχ]⟩
    exact congrArg Subtype.val h1
  have hcard := Fintype.card_le_of_injective Φ hΦ
  rw [Fintype.card_fun, Fintype.card_coe] at hcard
  have h2 : Fintype.card {u : ZMod 3 // u * u = 1} = 2 := by decide
  rw [h2] at hcard
  have h16 : Fintype.card ↥B = 16 := by
    rw [← Nat.card_eq_fintype_card, hB.2]
    norm_num
  rw [h16] at hcard
  by_contra hlt
  push_neg at hlt
  have h3 : 2 ^ W.card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem fgWt_polar_eq_zero (hB : IsElemAb2 B 4) {χ χ' : ↥B → ZMod 3}
    (hχ : fgWt (fgT B) χ ≠ ⊥) (hχ' : fgWt (fgT B) χ' ≠ ⊥) (hne : χ ≠ χ') {x y : V}
    (hx : x ∈ fgWt (fgT B) χ) (hy : y ∈ fgWt (fgT B) χ') : QuadraticMap.polar Q x y = 0 := by
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ χ' g := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have h1 := fgWt_sq (fgT B) (fgT_sq B hB) hχ g
  have h2 := fgWt_sq (fgT B) (fgT_sq B hB) hχ' g
  have hmul : χ g * χ' g = -1 := by
    revert h1 h2 hg
    generalize χ g = a
    generalize χ' g = b
    revert a b
    decide
  have hx' := (mem_fgWt (fgT B)).mp hx g
  have hy' := (mem_fgWt (fgT B)).mp hy g
  have hp := fgT_polar B g x y
  rw [hx', hy', QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_smul,
    hmul, smul_eq_mul] at hp
  revert hp
  generalize QuadraticMap.polar Q x y = p
  revert p
  decide

end Weights

end CFSG.OddStandard.SmallF3.Omega
