module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWAe5Sylow

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod

@[expose] def vpair (p s : Fin 5) : Wr 5 :=
  ofVec fun j => (if j = p then 1 else 0) + (if j = s then 1 else 0)

theorem vpair_mem_evenVec {p s : Fin 5} (h : p ≠ s) : vpair p s ∈ evenVec 5 := by
  rw [mem_evenVec]
  refine ⟨rfl, ?_⟩
  revert p s
  decide

theorem ofVec_conj {n : ℕ} (v : Fin n → ZMod 2) (x : Wr n) :
    ofVec v * x * (ofVec v)⁻¹ = ofVec (fun i => v i + v (x.perm.symm i)) * x := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (v i + x.vec ((1 : Equiv.Perm (Fin n)).symm i)) + v (((1 : Equiv.Perm (Fin n)) * x.perm).symm i) =
      (v i + v (x.perm.symm i)) + x.vec ((1 : Equiv.Perm (Fin n)).symm i)
    have e : ((1 : Equiv.Perm (Fin n)) * x.perm).symm i = x.perm.symm i := rfl
    rw [e]
    ring
  · show (1 * x.perm) * (1 : Equiv.Perm (Fin n))⁻¹ = 1 * x.perm
    simp

theorem ofVec_mul_comm_iff {n : ℕ} (d : Fin n → ZMod 2) (a : Wr n) :
    ofVec d * a = a * ofVec d ↔ ∀ j, d j = d (a.perm.symm j) := by
  constructor
  · intro h j
    have := congrFun (congrArg Wr.vec h) j
    have e1 : (ofVec d * a).vec j = d j + a.vec j := rfl
    have e2 : (a * ofVec d).vec j = a.vec j + d (a.perm.symm j) := rfl
    rw [e1, e2] at this
    have h3 : d j + a.vec j = d (a.perm.symm j) + a.vec j := by rw [this]; ring
    exact add_right_cancel h3
  · intro h
    refine Wr.ext (funext fun j => ?_) rfl
    show d j + a.vec j = a.vec j + d (a.perm.symm j)
    rw [← h j]
    ring

theorem perm_ne_of_sq_eq_zOf {ι : Fin 4 ↪ Fin 5} {a : Wr 5} (ha : a * a = zOf ι) {s : Fin 5}
    (hs : s ∈ Set.range ι) : a.perm s ≠ s := by
  classical
  intro hfix
  have h1 := congrFun (congrArg Wr.vec ha) s
  rw [mul_vec, zOf_vec_apply] at h1
  have e : a.perm.symm s = s := by
    rw [Equiv.symm_apply_eq]
    exact hfix.symm
  rw [e, if_pos hs, zmod_two_add_self] at h1
  exact absurd h1 (by decide)

theorem perm_eq_of_conj_comm {ι : Fin 4 ↪ Fin 5} {p : Fin 5} (hp : p ∉ Set.range ι)
    {a₁ a₂ : Wr 5} (h₁ : SupportedOn a₁ (Set.range ι)) (h₂ : SupportedOn a₂ (Set.range ι))
    (h12 : a₁ * a₂ = a₂ * a₁) (hsq₁ : a₁ * a₁ = zOf ι) (hsq₂ : a₂ * a₂ = zOf ι)
    (hc : ∀ i : Fin 4, mkQ 5 (vpair p (ι i) * a₁ * (vpair p (ι i))⁻¹) * mkQ 5 a₂ =
      mkQ 5 a₂ * mkQ 5 (vpair p (ι i) * a₁ * (vpair p (ι i))⁻¹)) :
    a₁.perm = a₂.perm := by
  classical
  have hp₁ : a₁.perm p = p := (h₁ p hp).2
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    set s := ι i with hs
    have hsr : s ∈ Set.range ι := ⟨i, rfl⟩
    set d : Fin 5 → ZMod 2 := fun j => ((if j = p then 1 else 0) + (if j = s then 1 else 0)) +
      ((if a₁.perm.symm j = p then 1 else 0) + (if a₁.perm.symm j = s then 1 else 0)) with hd
    have hv : vpair p s * a₁ * (vpair p s)⁻¹ = ofVec d * a₁ := ofVec_conj _ a₁
    have hXs : SupportedOn (ofVec d * a₁) (Set.range ι) := by
      intro y hy
      refine ⟨?_, ?_⟩
      · show d y + a₁.vec ((1 : Equiv.Perm (Fin 5)).symm y) = 0
        have e : a₁.perm.symm y = y := h₁.perm_symm hy
        have e2 : d y = 0 := by
          simp only [hd, e]
          ring_nf
          exact zmod_two_add_self _
        have e3 : (1 : Equiv.Perm (Fin 5)).symm y = y := rfl
        rw [e2, e3, (h₁ y hy).1, zero_add]
      · exact (h₁ y hy).2
    have hXc : ofVec d * a₁ * a₂ = a₂ * (ofVec d * a₁) := by
      have hcs := hc i
      rw [hv] at hcs
      exact comm_of_mkQ_comm_of_supportedOn (le_refl 5) hXs h₂ hcs
    have hdc : ofVec d * a₂ = a₂ * ofVec d := by
      have h3 : (ofVec d * a₂) * a₁ = (a₂ * ofVec d) * a₁ := by
        calc (ofVec d * a₂) * a₁ = ofVec d * (a₂ * a₁) := by rw [mul_assoc]
          _ = ofVec d * (a₁ * a₂) := by rw [h12]
          _ = ofVec d * a₁ * a₂ := by rw [mul_assoc]
          _ = a₂ * (ofVec d * a₁) := hXc
          _ = (a₂ * ofVec d) * a₁ := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hinv := (ofVec_mul_comm_iff d a₂).mp hdc (a₂.perm s)
    rw [Equiv.symm_apply_apply] at hinv
    have hps : p ≠ s := fun h => hp ⟨i, h.symm⟩
    have hσ₁s : a₁.perm s ≠ s := perm_ne_of_sq_eq_zOf hsq₁ hsr
    have hσ₂s : a₂.perm s ≠ s := perm_ne_of_sq_eq_zOf hsq₂ hsr
    have hp₂ : a₂.perm p = p := (h₂ p hp).2
    have hσ₂p : a₂.perm s ≠ p := fun h => hps (a₂.perm.injective (h.trans hp₂.symm)).symm
    have hsymp : ∀ j, a₁.perm.symm j = p ↔ j = p := fun j => by
      rw [Equiv.symm_apply_eq, hp₁]
    have hsyms : ∀ j, a₁.perm.symm j = s ↔ j = a₁.perm s := fun j => by
      rw [Equiv.symm_apply_eq]
    have hds : d s = 1 := by
      simp only [hd, hsymp, hsyms, hps.symm, hσ₁s.symm, if_true, if_false]
      decide
    have hdσ : d (a₂.perm s) = if a₂.perm s = a₁.perm s then 1 else 0 := by
      simp only [hd, hsymp, hsyms, hσ₂p, hσ₂s, if_true, if_false]
      ring
    rw [hdσ, hds] at hinv
    by_contra hne
    have hne' : ¬ a₂.perm s = a₁.perm s := fun h => hne h.symm
    rw [if_neg hne'] at hinv
    exact absurd hinv (by decide)
  · rw [(h₁ x hx).2, (h₂ x hx).2]

theorem exists_pair_of_weight_two {p : Fin 5} {w : Fin 5 → ZMod 2} (hwp : w p = 0)
    (hsum : ∑ i, w i = 0) (h0 : w ≠ 0) (h1 : w ≠ fun i => if i = p then 0 else 1) :
    ∃ q r : Fin 5, q ≠ r ∧ q ≠ p ∧ r ≠ p ∧ ∀ y, w y = if (y = q ∨ y = r) then 1 else 0 := by
  classical
  set S : Finset (Fin 5) := Finset.univ.filter (fun y => w y = 1) with hS
  have hz : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
  have hw01 : ∀ y, w y = if y ∈ S then 1 else 0 := by
    intro y
    by_cases h : w y = 1
    · simp [hS, h]
    · simp [hS, h, hz _ h]
  have hpS : p ∉ S := by simp [hS, hwp]
  have hcard : (S.card : ZMod 2) = 0 := by
    have : ∑ y, w y = (S.card : ZMod 2) := by
      calc ∑ y, w y = ∑ y : Fin 5, (if y ∈ S then (1 : ZMod 2) else 0) :=
            Finset.sum_congr rfl fun y _ => hw01 y
        _ = (S.card : ZMod 2) := by
            rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← this]
    exact hsum
  have heven : Even S.card := (ZMod.natCast_eq_zero_iff_even).mp hcard
  have hSsub : S ⊆ Finset.univ.erase p := fun y hy =>
    Finset.mem_erase.mpr ⟨fun h => hpS (h ▸ hy), Finset.mem_univ y⟩
  have hle : S.card ≤ 4 := by
    have := Finset.card_le_card hSsub
    simpa using this
  have hne0 : S.card ≠ 0 := by
    intro h
    apply h0
    funext y
    rw [hw01 y, Finset.card_eq_zero.mp h]
    simp
  have hne4 : S.card ≠ 4 := by
    intro h
    apply h1
    have hSeq : S = Finset.univ.erase p :=
      Finset.eq_of_subset_of_card_le hSsub (by simp [h])
    funext y
    rw [hw01 y, hSeq]
    by_cases hy : y = p <;> simp [hy]
  have h2 : S.card = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨q, r, hqr, hSqr⟩ := Finset.card_eq_two.mp h2
  have hq : q ∈ S := by rw [hSqr]; simp
  have hr : r ∈ S := by rw [hSqr]; simp
  refine ⟨q, r, hqr, fun h => hpS (h ▸ hq), fun h => hpS (h ▸ hr), fun y => ?_⟩
  rw [hw01 y, hSqr]
  simp

theorem exists_two_others : ∀ p q r : Fin 5, p ≠ q → p ≠ r → q ≠ r →
    ∃ s s' : Fin 5, s ≠ s' ∧ s ≠ p ∧ s ≠ q ∧ s ≠ r ∧ s' ≠ p ∧ s' ≠ q ∧ s' ≠ r := by
  decide

theorem eq_of_ne_of_distinct : ∀ p q r s s' : Fin 5, p ≠ q → p ≠ r → p ≠ s → p ≠ s' → q ≠ r →
    q ≠ s → q ≠ s' → r ≠ s → r ≠ s' → s ≠ s' → ∀ y : Fin 5, y ≠ p → y = q ∨ y = r ∨ y = s ∨ y = s' := by
  decide

theorem exists_embed_w0 {ι₀ : Fin 4 ↪ Fin 5} {p : Fin 5} (hp : ∀ y, y ∈ Set.range ι₀ ↔ y ≠ p)
    {a : Wr 5} (hsupp : SupportedOn a (Set.range ι₀)) (hperm : a.perm = 1) (hw : wsum a = 0)
    (h0 : a ≠ 1) (hz : a ≠ zOf ι₀) :
    ∃ ι : Fin 4 ↪ Fin 5, Set.range ι = Set.range ι₀ ∧ a = embed ι w0 := by
  classical
  have hpn : p ∉ Set.range ι₀ := fun h => (hp p).mp h rfl
  have hwp : a.vec p = 0 := (hsupp p hpn).1
  have hne0 : a.vec ≠ 0 := by
    intro h
    apply h0
    exact Wr.ext (by rw [h]; rfl) hperm
  have hneind : a.vec ≠ (fun i => if i = p then 0 else 1) := by
    intro h
    apply hz
    refine Wr.ext ?_ (hperm.trans (zOf_perm ι₀).symm)
    funext y
    rw [h, zOf_vec_apply]
    beta_reduce
    by_cases hy : y = p
    · have hyn : y ∉ Set.range ι₀ := fun h' => (hp y).mp h' hy
      rw [if_neg hyn, if_pos hy]
    · have hyr : y ∈ Set.range ι₀ := (hp y).mpr hy
      rw [if_pos hyr, if_neg hy]
  obtain ⟨q, r, hqr, hqp, hrp, hval⟩ := exists_pair_of_weight_two hwp hw hne0 hneind
  obtain ⟨s, s', hss', hsp, hsq, hsr, hs'p, hs'q, hs'r⟩ :=
    exists_two_others p q r (Ne.symm hqp) (Ne.symm hrp) hqr
  have hinj : Function.Injective ![q, r, s, s'] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  let ι : Fin 4 ↪ Fin 5 := ⟨![q, r, s, s'], hinj⟩
  have hιp : ∀ i, ι i ≠ p := by
    intro i
    fin_cases i <;> simp [ι, hqp, hrp, hsp, hs'p]
  have hιr : ∀ y, y ≠ p → ∃ i, ι i = y := by
    intro y hy
    rcases eq_of_ne_of_distinct p q r s s' (Ne.symm hqp) (Ne.symm hrp) (Ne.symm hsp) (Ne.symm hs'p) hqr
      (Ne.symm hsq) (Ne.symm hs'q) (Ne.symm hsr) (Ne.symm hs'r) hss' y hy with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  refine ⟨ι, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (hp _).mpr (hιp i)
    · intro hy
      exact hιr y ((hp y).mp hy)
  · refine Wr.ext ?_ (by rw [hperm, embed_perm]; exact (embedPerm_one ι).symm)
    funext y
    rw [hval y]
    have h01 : (y = q ∨ y = r) ↔ (y = ι 0 ∨ y = ι 1) := Iff.rfl
    by_cases hy : y = q ∨ y = r
    · rw [if_pos hy]
      exact ((embed_w0_vec_eq_one_iff ι y).mpr (h01.mp hy)).symm
    · rw [if_neg hy]
      have h1 : (embed ι w0).vec y ≠ 1 := fun h => hy (h01.mpr ((embed_w0_vec_eq_one_iff ι y).mp h))
      generalize (embed ι w0).vec y = r at h1 ⊢
      revert r
      decide

theorem memAt_le_aeSub {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memAt α h b ≤ aeSub n := by
  cases b
  · exact memKStar_le_aeSub _
  · exact memK_le_aeSub _

theorem vec_of_conj_comm {X : Type*} [Group X] (ψ : X →* AEQ 5) {p : Fin 5} {b₁ b₂ : Bool} {k₁ k₂ : X}
    (hk₁ : ψ k₁ ∈ memBar (miss p) (card_miss p) b₁) (hk₂ : ψ k₂ ∈ memBar (miss p) (card_miss p) b₂)
    (hsq₁ : ψ (k₁ * k₁) = zBar (miss p) (card_miss p))
    (hsq₂ : ψ (k₂ * k₂) = zBar (miss p) (card_miss p)) (h12 : k₁ * k₂ = k₂ * k₁)
    (hc : ∀ i : Fin 4, ∃ s : X, ψ s = mkQ 5 (vpair p (emb (miss p) (card_miss p) i)) ∧
      (s * k₁ * s⁻¹) * k₂ = k₂ * (s * k₁ * s⁻¹)) :
    ∃ a₁ a₂ : Wr 5, SupportedOn a₁ (Set.range (emb (miss p) (card_miss p))) ∧
      SupportedOn a₂ (Set.range (emb (miss p) (card_miss p))) ∧ ψ k₁ = mkQ 5 a₁ ∧ ψ k₂ = mkQ 5 a₂ ∧
      a₁ ∈ aeSub 5 ∧ a₂ ∈ aeSub 5 ∧ (a₁ * a₂).perm = 1 ∧ (a₁⁻¹ * a₂).perm = 1 := by
  obtain ⟨a₁, ha₁, hψ₁⟩ := hk₁
  obtain ⟨a₂, ha₂, hψ₂⟩ := hk₂
  set ι₀ := emb (miss p) (card_miss p) with hι₀
  have hs₁ : SupportedOn a₁ (Set.range ι₀) := supportedOn_of_mem_memAt ha₁
  have hs₂ : SupportedOn a₂ (Set.range ι₀) := supportedOn_of_mem_memAt ha₂
  have hpn : p ∉ Set.range ι₀ := by
    rw [hι₀, range_emb]
    simp [miss]
  have hsq₁' : a₁ * a₁ = zOf ι₀ := by
    refine mkQ_inj_of_supportedOn (le_refl 5) (hs₁.mul hs₁) (zOf_supportedOn ι₀) ?_
    rw [map_mul, hψ₁, ← map_mul, hsq₁]
    rfl
  have hsq₂' : a₂ * a₂ = zOf ι₀ := by
    refine mkQ_inj_of_supportedOn (le_refl 5) (hs₂.mul hs₂) (zOf_supportedOn ι₀) ?_
    rw [map_mul, hψ₂, ← map_mul, hsq₂]
    rfl
  have h12' : a₁ * a₂ = a₂ * a₁ := by
    refine mkQ_inj_of_supportedOn (le_refl 5) (hs₁.mul hs₂) (hs₂.mul hs₁) ?_
    rw [map_mul, map_mul, hψ₁, hψ₂, ← map_mul, ← map_mul, h12]
  have hc' : ∀ i : Fin 4, mkQ 5 (vpair p (ι₀ i) * a₁ * (vpair p (ι₀ i))⁻¹) * mkQ 5 a₂ =
      mkQ 5 a₂ * mkQ 5 (vpair p (ι₀ i) * a₁ * (vpair p (ι₀ i))⁻¹) := by
    intro i
    obtain ⟨s, hsψ, hsc⟩ := hc i
    have h1 := congrArg ψ hsc
    simp only [map_mul, map_inv] at h1
    rw [hsψ, ← hψ₁, ← hψ₂] at h1
    simpa only [map_mul, map_inv] using h1
  have hperm := perm_eq_of_conj_comm hpn hs₁ hs₂ h12' hsq₁' hsq₂' hc'
  have hσ : a₁.perm * a₁.perm = 1 := by
    have := congrArg Wr.perm hsq₁'
    rwa [mul_perm, zOf_perm] at this
  refine ⟨a₁, a₂, hs₁, hs₂, hψ₁.symm, hψ₂.symm, memAt_le_aeSub _ _ _ ha₁, memAt_le_aeSub _ _ _ ha₂, ?_, ?_⟩
  · rw [mul_perm, ← hperm]
    exact hσ
  · rw [mul_perm, inv_perm, ← hperm]
    exact inv_mul_cancel _

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
