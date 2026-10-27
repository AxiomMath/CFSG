module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFrame
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSimple

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.M1b (evalE)

@[expose] def tableRels (α k : ℕ) : List (ℕ × Tm) := if α = 2 then act2Rels k else actRels α k

theorem tableRels_fst : ∀ α < 3, ∀ k < 3, (tableRels α k).map Prod.fst = List.range 7 := by
  decide

theorem gRels_fst : ∀ α < 3, (gRels α).map Prod.fst = List.range 7 := by decide

theorem tmLt_tableRels {α : ℕ} (hα : α < 3) {k : ℕ} (hk : k < 3) :
    ∀ e ∈ tableRels α k, tmLt 7 e.2 := by
  have hv : ∀ i k : ℕ, i < 7 → tmLt 7 (Tm.pw (Tm.var i) k) :=
    fun i k hi => tmLt_pw (a := Tm.var i) (by simpa [tmLt] using hi) k
  intro e he
  interval_cases α <;> interval_cases k <;>
    simp (config := {decide := true}) only [tableRels, actRels, act2Rels, ite_true, ite_false,
      List.mem_cons, List.mem_nil_iff, or_false] at he <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tmLt, vt, vpi, vtau, vmu, vlam, vze, vxi, hv]

theorem tmLt_gRels {α : ℕ} (hα : α < 3) : ∀ e ∈ gRels α, tmLt 7 e.2 := by
  have hv : ∀ i k : ℕ, i < 7 → tmLt 7 (Tm.pw (Tm.var i) k) :=
    fun i k hi => tmLt_pw (a := Tm.var i) (by simpa [tmLt] using hi) k
  intro e he
  interval_cases α <;>
    simp (config := {decide := true}) only [gRels, ite_true, ite_false,
      List.mem_cons, List.mem_nil_iff, or_false] at he <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tmLt, Tm.prod, vt, vpi, vtau, vmu, vlam, vze, vxi, hv]

@[expose] def ActTable {H : Type} [Group H] (α k : ℕ) (σ : H →* H) (x : Fin 7 → H) : Prop :=
  ∀ e ∈ tableRels α k, σ (natFam x e.1) = evalE (natFam x) e.2

@[expose] def GTable {H : Type} [Group H] (α : ℕ) (γ : H →* H) (x : Fin 7 → H) : Prop :=
  ∀ e ∈ gRels α, γ (natFam x e.1) = evalE (natFam x) e.2

namespace Rep

variable {M : RegModel} {H : Type} [Group H]

theorem evalT_spec (R : Rep M H) (x : Fin 7 → H) (hx : ∀ j : Fin 7, R.pt (x j) = M.g j.val) :
    ∀ {τ : Tm}, tmLt 7 τ → M.evalT τ = R.pt (evalE (natFam x) τ)
  | .var i, hτ => by
    have hi : i < 7 := hτ
    have := hx ⟨i, hi⟩
    simp only [RegModel.evalT, evalE, natFam, Fin.ofNat, Nat.mod_eq_of_lt hi]
    exact this.symm
  | .one, _ => by simp only [RegModel.evalT, evalE]; exact R.pt_one.symm
  | .mul a b, hτ => by
    simp only [RegModel.evalT, evalE]
    rw [R.pt_mul, evalT_spec R x hx hτ.1, evalT_spec R x hx hτ.2]
  | .inv a, hτ => by
    simp only [RegModel.evalT, evalE]
    rw [R.pt_inv, evalT_spec R x hx (show tmLt 7 a from hτ)]

end Rep

theorem find_get {rels : List (ℕ × Tm)} (h : rels.map Prod.fst = List.range 7) {j : ℕ}
    (hj : j < 7) : ∃ τ : Tm, (j, τ) ∈ rels ∧ rels.find? (fun e => e.1 == j) = some (j, τ) := by
  have hlen : rels.length = 7 := by simpa using congrArg List.length h
  have hfst : ∀ i (hi : i < rels.length), (rels[i]).1 = i := fun i hi => by
    have h1 : (rels.map Prod.fst)[i]'(by simpa using hi) = (rels[i]).1 := List.getElem_map _
    have h2 := List.getElem_of_eq h (by simpa using hi)
    rw [h1] at h2
    simpa using h2
  have hjl : j < rels.length := by omega
  have he : rels[j] = (j, (rels[j]).2) := Prod.ext (hfst j hjl) rfl
  refine ⟨(rels[j]).2, he ▸ List.getElem_mem hjl, ?_⟩
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, j, hjl, he, fun j' hj' => ?_⟩
  have := hfst j' (by omega)
  simp [this]
  omega

namespace Rep

variable {M : RegModel} {H : Type} [Group H]

theorem tabImgs_get (R : Rep M H) (x : Fin 7 → H) (hx : ∀ j : Fin 7, R.pt (x j) = M.g j.val)
    {α k : ℕ} (hα : α < 3) (hk : k < 3) (σ : H →* H) (hσ : ActTable α k σ x) :
    ∀ j : Fin 7, R.pt (σ (x j)) = (M.tabImgs α k)[j.val]! := by
  intro j
  obtain ⟨τ, hmem, hfind⟩ := find_get (tableRels_fst α hα k hk) j.2
  have hτ : tmLt 7 τ := tmLt_tableRels hα hk (j.val, τ) hmem
  have h1 := hσ (j.val, τ) hmem
  rw [natFam_fin] at h1
  have h2 : (M.tabImgs α k)[j.val]! = M.evalT τ := by
    unfold RegModel.tabImgs
    rw [getElem!_range_map_of_lt _ j.2]
    show (match (tableRels α k).find? (fun e => e.1 == j.val) with
      | some e => M.evalT e.2 | none => 0) = _
    rw [hfind]
  rw [h1, h2, R.evalT_spec x hx hτ]

theorem gImgs_get (R : Rep M H) (x : Fin 7 → H) (hx : ∀ j : Fin 7, R.pt (x j) = M.g j.val)
    {α : ℕ} (hα : α < 3) (γ : H →* H) (hγ : GTable α γ x) :
    ∀ j : Fin 7, R.pt (γ (x j)) = (M.gImgs α)[j.val]! := by
  intro j
  obtain ⟨τ, hmem, hfind⟩ := find_get (gRels_fst α hα) j.2
  have hτ : tmLt 7 τ := tmLt_gRels hα (j.val, τ) hmem
  have h1 := hγ (j.val, τ) hmem
  rw [natFam_fin] at h1
  have h2 : (M.gImgs α)[j.val]! = M.evalT τ := by
    unfold RegModel.gImgs
    rw [getElem!_range_map_of_lt _ j.2, hfind]
  rw [h1, h2, R.evalT_spec x hx hτ]

end Rep

end CFSG.OddStandard.ChengHeld.Model
