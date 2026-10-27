module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AY

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

theorem comm_of_perm_eq_one {n : ℕ} {a b : Wr n} (ha : a.perm = 1) (hb : b.perm = 1) :
    a * b = b * a := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec, ha, hb]
    show a.vec i + b.vec i = b.vec i + a.vec i
    exact add_comm _ _
  · rw [mul_perm, mul_perm, ha, hb]

theorem exists_three_elt {p : Fin 5} {ι : Fin 4 ↪ Fin 5} (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) :
    ∃ w : Wr 5, w ∈ aeSub 5 ∧ mkQ 5 w ^ 3 = 1 ∧
      mkQ 5 w * mkQ 5 (embed ι w0) = mkQ 5 (embed ι w0) * mkQ 5 w ∧
      mkQ 5 w * zBar (miss p) (card_miss p) ≠ zBar (miss p) (card_miss p) * mkQ 5 w ∧
      (mkQ 5 w * zBar (miss p) (card_miss p) * (mkQ 5 w)⁻¹) * zBar (miss p) (card_miss p) =
        zBar (miss p) (card_miss p) * (mkQ 5 w * zBar (miss p) (card_miss p) * (mkQ 5 w)⁻¹) := by
  classical
  have hne : ∀ i, ι i ≠ p := fun i h => (hι (ι i)).mp ⟨i, rfl⟩ h
  have hinj : ∀ i j, i ≠ j → ι i ≠ ι j := fun i j hij h => hij (ι.injective h)
  have h23 : ι 2 ≠ ι 3 := hinj 2 3 (by decide)
  have h3p : ι 3 ≠ p := hne 3
  have h2p : ι 2 ≠ p := hne 2
  set σ : Equiv.Perm (Fin 5) := threeCycle (ι 2) (ι 3) p with hσ
  have hσ0 : σ (ι 0) = ι 0 :=
    threeCycle_of_ne (hinj 0 2 (by decide)) (hinj 0 3 (by decide)) (hne 0)
  have hσ1 : σ (ι 1) = ι 1 :=
    threeCycle_of_ne (hinj 1 2 (by decide)) (hinj 1 3 (by decide)) (hne 1)
  have hσp : σ p = ι 2 := threeCycle_thd
  have hσs2 : σ.symm (ι 2) = p := (Equiv.symm_apply_eq σ).mpr hσp.symm
  have hσs0 : σ.symm (ι 0) = ι 0 := (Equiv.symm_apply_eq σ).mpr hσ0.symm
  set z : Wr 5 := zOf (emb (miss p) (card_miss p)) with hz
  have hzbar : zBar (miss p) (card_miss p) = mkQ 5 z := rfl
  have hmem : ∀ y : Fin 5, y ∈ Set.range (emb (miss p) (card_miss p)) ↔ y ≠ p := by
    intro y
    rw [range_emb]
    simp [miss]
  have hz1 : ∀ y, y ≠ p → z.vec y = 1 := fun y hy => by
    rw [hz, zOf_vec_apply, if_pos ((hmem y).mpr hy)]
  have hz0 : z.vec p = 0 := by
    rw [hz, zOf_vec_apply, if_neg (fun h => (hmem p).mp h rfl)]
  have hzp : z.perm = 1 := zOf_perm _
  rw [hzbar]
  refine ⟨ofPerm σ, ofPerm_threeCycle_mem h23 h3p, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ofPerm_pow, threeCycle_cubed h23 h3p h2p, ofPerm_one, map_one]
  · rw [← map_mul, ← map_mul, ofPerm_comm_embed_w0 ι hσ0 hσ1]
  · intro h
    rcases comm_or_of_mkQ_comm h with h1 | h1
    · have h2 := congrFun (congrArg Wr.vec h1) (ι 2)
      rw [mul_vec, mul_vec] at h2
      have e1 : (ofPerm σ).vec (ι 2) = 0 := rfl
      have e2 : (ofPerm σ).vec (z.perm.symm (ι 2)) = 0 := rfl
      have e3 : (ofPerm σ).perm = σ := rfl
      rw [e1, e2, e3, hσs2, hz0, hz1 (ι 2) h2p] at h2
      exact absurd h2 (by decide)
    · have h2 := congrFun (congrArg Wr.vec h1) (ι 0)
      rw [mul_vec, mul_vec, mul_vec] at h2
      have e1 : (ofPerm σ).vec (ι 0) = 0 := rfl
      have e2 : (ofPerm σ).vec (z.perm.symm (ι 0)) = 0 := rfl
      have e3 : (ofPerm σ).perm = σ := rfl
      have e4 : (allOnes 5).vec (((z * ofPerm σ).perm).symm (ι 0)) = 1 := rfl
      rw [e1, e2, e3, e4, hσs0] at h2
      generalize z.vec (ι 0) = a at h2
      revert a
      decide
  · have hpa : (ofPerm σ * z * (ofPerm σ)⁻¹).perm = 1 := by
      rw [ofPerm_conj_perm, hzp]
      group
    have hc := comm_of_perm_eq_one hpa hzp
    simpa only [← map_inv, ← map_mul] using congrArg (mkQ 5) hc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AY
