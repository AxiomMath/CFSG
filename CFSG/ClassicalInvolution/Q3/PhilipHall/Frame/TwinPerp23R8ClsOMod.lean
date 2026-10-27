module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

theorem zOf_miss_vec (c y : Fin 5) :
    (zOf (emb (miss c) (card_miss c))).vec y = if y = c then 0 else 1 := by
  have h : y ∈ Set.range (emb (miss c) (card_miss c)) ↔ y ≠ c := by
    rw [range_emb]
    simp [miss]
  rw [zOf_vec_apply]
  by_cases hy : y = c
  · rw [if_neg (fun h' => (h.mp h') hy), if_pos hy]
  · rw [if_pos (h.mpr hy), if_neg hy]

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 8192 in
theorem triple_aux : ∀ a b c d e x : Fin 5, a ≠ b → a ≠ c → b ≠ c → d ≠ e → a ≠ d → a ≠ e → b ≠ d → b ≠ e →
    c ≠ d → c ≠ e → ((if x = a then 0 else 1) + (if x = b then 0 else 1) + (if x = c then 0 else 1) : ZMod 2) =
      (if x = d then 0 else 1) + (if x = e then 0 else 1) := by
  decide +kernel

theorem zBar_triple {a b c d e : Fin 5} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hde : d ≠ e) (had : a ≠ d)
    (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) :
    zBar (miss a) (card_miss a) * zBar (miss b) (card_miss b) * zBar (miss c) (card_miss c) =
      zBar (miss d) (card_miss d) * zBar (miss e) (card_miss e) := by
  unfold zBar
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  have hp : ∀ c : Fin 5, (zOf (emb (miss c) (card_miss c))).perm = 1 := fun c => zOf_perm _
  have hv : ∀ (w w' : Wr 5), w.perm = 1 → ∀ x, (w * w').vec x = w.vec x + w'.vec x := by
    intro w w' hw x
    rw [mul_vec, hw]
    rfl
  have hp2 : ∀ c d : Fin 5, (zOf (emb (miss c) (card_miss c)) * zOf (emb (miss d) (card_miss d))).perm = 1 := by
    intro c d
    rw [mul_perm, hp, hp, mul_one]
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [hv _ _ (hp2 a b), hv _ _ (hp a), hv _ _ (hp d), zOf_miss_vec, zOf_miss_vec, zOf_miss_vec, zOf_miss_vec,
      zOf_miss_vec]
    exact triple_aux a b c d e x hab hac hbc hde had hae hbd hbe hcd hce
  · rw [mul_perm, mul_perm, mul_perm, hp, hp, hp, hp, hp]
    simp

theorem three_conj_prod {p : Fin 5} {ι : Fin 4 ↪ Fin 5} (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) :
    zBar (miss p) (card_miss p) *
      (mkQ 5 (ofPerm (threeCycle (ι 2) (ι 3) p)) * zBar (miss p) (card_miss p) *
        (mkQ 5 (ofPerm (threeCycle (ι 2) (ι 3) p)))⁻¹) *
      (mkQ 5 (ofPerm (threeCycle (ι 2) (ι 3) p)) ^ 2 * zBar (miss p) (card_miss p) *
        (mkQ 5 (ofPerm (threeCycle (ι 2) (ι 3) p)) ^ 2)⁻¹) = mkQ 5 (embed ι w0) := by
  have hne : ∀ i, ι i ≠ p := fun i h => (hι (ι i)).mp ⟨i, rfl⟩ h
  have hinj : ∀ i j, i ≠ j → ι i ≠ ι j := fun i j hij h => hij (ι.injective h)
  set σ : Equiv.Perm (Fin 5) := threeCycle (ι 2) (ι 3) p with hσ
  have h1 : mkQ 5 (ofPerm σ) * zBar (miss p) (card_miss p) * (mkQ 5 (ofPerm σ))⁻¹ =
      zBar (miss (ι 2)) (card_miss _) := by
    rw [zBar_conj_miss]
    have e : (ofPerm σ).perm p = ι 2 := threeCycle_thd
    rw [e]
  have h2 : mkQ 5 (ofPerm σ) ^ 2 * zBar (miss p) (card_miss p) * (mkQ 5 (ofPerm σ) ^ 2)⁻¹ =
      zBar (miss (ι 3)) (card_miss _) := by
    have hc : mkQ 5 (ofPerm σ) ^ 2 * zBar (miss p) (card_miss p) * (mkQ 5 (ofPerm σ) ^ 2)⁻¹ =
        mkQ 5 (ofPerm σ) * (mkQ 5 (ofPerm σ) * zBar (miss p) (card_miss p) * (mkQ 5 (ofPerm σ))⁻¹) *
          (mkQ 5 (ofPerm σ))⁻¹ := by
      rw [pow_two, mul_inv_rev]
      group
    rw [hc, h1, zBar_conj_miss]
    have e : (ofPerm σ).perm (ι 2) = ι 3 := threeCycle_fst (hinj 2 3 (by decide)) (hne 2)
    rw [e]
  rw [h1, h2, ClsM.mkQ_embed_w0 ι]
  exact zBar_triple (hne 2).symm (hne 3).symm (hinj 2 3 (by decide)) (hinj 0 1 (by decide)) (hne 0).symm
    (hne 1).symm (hinj 2 0 (by decide)) (hinj 2 1 (by decide)) (hinj 3 0 (by decide)) (hinj 3 1 (by decide))

theorem exists_three_elt_prod {p : Fin 5} {ι : Fin 4 ↪ Fin 5} (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) :
    ∃ w : Wr 5, w ∈ aeSub 5 ∧ mkQ 5 w ^ 3 = 1 ∧
      mkQ 5 w * mkQ 5 (embed ι w0) = mkQ 5 (embed ι w0) * mkQ 5 w ∧
      mkQ 5 w * zBar (miss p) (card_miss p) ≠ zBar (miss p) (card_miss p) * mkQ 5 w ∧
      (mkQ 5 w * zBar (miss p) (card_miss p) * (mkQ 5 w)⁻¹) * zBar (miss p) (card_miss p) =
        zBar (miss p) (card_miss p) * (mkQ 5 w * zBar (miss p) (card_miss p) * (mkQ 5 w)⁻¹) ∧
      zBar (miss p) (card_miss p) * (mkQ 5 w * zBar (miss p) (card_miss p) * (mkQ 5 w)⁻¹) *
        (mkQ 5 w ^ 2 * zBar (miss p) (card_miss p) * (mkQ 5 w ^ 2)⁻¹) = mkQ 5 (embed ι w0) := by
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
  refine ⟨ofPerm σ, ofPerm_threeCycle_mem h23 h3p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ofPerm_pow, threeCycle_cubed h23 h3p h2p, ofPerm_one, map_one]
  · rw [← map_mul, ← map_mul, ofPerm_comm_embed_w0 ι hσ0 hσ1]
  · rw [hzbar]
    intro h
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
  · rw [hzbar]
    have hpa : (ofPerm σ * z * (ofPerm σ)⁻¹).perm = 1 := by
      rw [ofPerm_conj_perm, hzp]
      group
    have hc := AY.comm_of_perm_eq_one hpa hzp
    simpa only [← map_inv, ← map_mul] using congrArg (mkQ 5) hc
  · exact three_conj_prod hι

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
