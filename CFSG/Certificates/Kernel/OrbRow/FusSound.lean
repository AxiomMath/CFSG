module

public import Certificates.Data.Kernel.OrbRow.Fus
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import CFSG.Certificates.Kernel.OrbRow.WordRep

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw.Orb

theorem mem_dgtWord {k l : ℕ} (h : l ∈ dgtWord k) : l < 4 := by
  simp only [dgtWord, List.mem_append, List.mem_replicate] at h
  omega

theorem dgtWord_prod {G : Type*} [Monoid G] (d : ℕ → G) (k : ℕ) :
    ((dgtWord k).map d).prod =
      d 0 ^ (k % 3) * (d 1 ^ (k / 3 % 3) * (d 2 ^ (k / 9 % 3) * d 3 ^ (k / 27 % 3))) := by
  simp only [dgtWord, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]

theorem fusK_idx {n w m : ℕ} {D H : List ℕ} {XA XB : ℕ} {FI FC FE : List ℕ} {k : ℕ}
    (h : fusK n w m D H XA XB FI FC FE k = true) : getS FI k < lenS H := by
  unfold fusK at h
  rw [strictB_apply, strictB_apply, strictB_apply, strictB_apply, strictB_apply] at h
  exact Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 h).1

theorem fusK_sound {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {D H : List ℕ}
    {XA XB : ℕ} {FI FC FE : List ℕ} {k : ℕ}
    (h : fusK n w (mask w) D H XA XB FI FC FE k = true) {d : ℕ → Equiv.Perm (Fin n)}
    (hd : ∀ i < 4, PRep n w (getS D i) (d i)) {xa xb : Equiv.Perm (Fin n)}
    (hxa : PRep n w XA xa) (hxb : PRep n w XB xb) {g : Equiv.Perm (Fin n)}
    (hg : PRep n w (getS H (getS FI k)) g) :
    getS FI k < lenS H ∧ (getS FC k = 0 → g * ((dgtWord k).map d).prod * g⁻¹ = xa ^ getS FE k) ∧
      (getS FC k ≠ 0 → g * ((dgtWord k).map d).prod * g⁻¹ = xb ^ getS FE k) ∧
      (getS FE k = 1 ∨ getS FE k = 2) := by
  unfold fusK at h
  rw [strictB_apply, strictB_apply, strictB_apply, strictB_apply, strictB_apply] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h
  have hn32 : n < 2 ^ 32 := lt_trans hn (by norm_num)
  have hgi := prep_inv h5 hg
  have hdk := posWordK_rep hn hw (G := getS D) (σ := d) (wd := dgtWord k)
    (fun l hl => hd l (mem_dgtWord hl))
  have hl := prep_pcomp hn32 hg (prep_pcomp hn32 hdk hgi)
  rw [Nat.eq_of_beq_eq_true h6] at hl
  have he : getS FE k = 1 ∨ getS FE k = 2 := by
    have e1 : 1 ≤ getS FE k := Nat.le_of_ble_eq_true h3
    have e2 : getS FE k ≤ 2 := Nat.le_of_ble_eq_true h4
    omega
  have hc : ∀ (c : ℕ) (x : Equiv.Perm (Fin n)), PRep n w c x →
      PRep n w (posWordK n w (fun _ => c) (List.replicate (getS FE k) 0)) (x ^ getS FE k) := by
    intro c x hx
    have := posWordK_rep hn hw (G := fun _ => c) (σ := fun _ => x)
      (wd := List.replicate (getS FE k) 0) (fun _ _ => hx)
    rwa [List.map_replicate, List.prod_replicate] at this
  refine ⟨Nat.le_of_ble_eq_true h1, fun h0 => ?_, fun h0 => ?_, he⟩
  · have e : Nat.beq (getS FC k) 0 = true := by rw [h0]; rfl
    rw [e] at hl
    rw [mul_assoc]
    exact prep_unique hl (hc XA xa hxa)
  · have e : Nat.beq (getS FC k) 0 = false := by
      cases hb : Nat.beq (getS FC k) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h0
    rw [e] at hl
    rw [mul_assoc]
    exact prep_unique hl (hc XB xb hxb)

end CFSG.KC.OrbRow

end
