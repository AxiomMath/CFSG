module

public import CFSG.Certificates.Kernel.HNLocal.Defs
import CFSG.Certificates.Kernel.HNLocal.Row
import CFSG.Certificates.Kernel.HNLocal.Gat
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.HNLocal.TreePf

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord CFSG.KS.HNLocal Matrix Finset

private theorem cm_M {CM3 M : Nat} (hcm : cmOK CM3 M = true) : M = 2 ^ 399 - 1 := by
  unfold cmOK at hcm
  have h := Nat.eq_of_beq_eq_true (GatPf.bAnd_iff.1 hcm).2
  rw [h]
  show (1 <<< 399) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem rm_eq {L H CM RM ONE LV HV : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) : RM = 2 ^ 1729 - 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRM, -⟩ := consts_facts hc
  rw [hRM]

private theorem z5 {v : Nat} (hv : v < 5) : ((v : Nat) : ZMod 5) = 0 ↔ v = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    omega
  · intro h
    rw [h]
    exact dvd_zero 5

private theorem reindex {S : Finset ℕ} {rk : ℕ → ℕ} {n : ℕ} (hmap : ∀ t ∈ S, rk t < n)
    (f : ℕ → ℕ) : ∑ t ∈ S, f t * 2 ^ (1729 * rk t) =
      ∑ q ∈ range n, (∑ t ∈ S.filter (fun t => rk t = q), f t) * 2 ^ (1729 * q) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := rk) (t := range n)
    (fun t ht => mem_range.2 (hmap t ht))]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun t ht => ?_
  rw [(mem_filter.1 ht).2]

private theorem fiber {S : Finset ℕ} {rk : ℕ → ℕ} (hinj : Set.InjOn rk S) {t0 : ℕ}
    (ht0 : t0 ∈ S) (f : ℕ → ℕ) : ∑ t ∈ S.filter (fun t => rk t = rk t0), f t = f t0 :=
  sum_eq_single_of_mem t0 (mem_filter.2 ⟨ht0, rfl⟩) fun b hb hne =>
    absurd (hinj (mem_filter.1 hb).1 ht0 (mem_filter.1 hb).2) hne

private theorem fiber_lt {S : Finset ℕ} {rk : ℕ → ℕ} (hinj : Set.InjOn rk S) {f : ℕ → ℕ} {B : ℕ}
    (hf : ∀ t, f t < B) (q : ℕ) : ∑ t ∈ S.filter (fun t => rk t = q), f t < B := by
  by_cases hex : ∃ t0 ∈ S, rk t0 = q
  · obtain ⟨t0, ht0, rfl⟩ := hex
    rw [fiber hinj ht0]
    exact hf t0
  · rw [Finset.sum_eq_zero fun t ht => absurd ⟨t, (mem_filter.1 ht).1, (mem_filter.1 ht).2⟩ hex]
    exact lt_of_le_of_lt (Nat.zero_le _) (hf 0)

private theorem rk_strict {P : ℕ → Prop} [DecidablePred P] {t1 t2 : ℕ} (h12 : t1 < t2)
    (hP : P t1) : ((range t1).filter P).card < ((range t2).filter P).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset_filter _
    (Finset.range_subset_range.2 h12.le))]
  exact ⟨t1, mem_filter.2 ⟨mem_range.2 h12, hP⟩, fun h => by simp at h⟩

private theorem rk_inj (h cnt ℓ : ℕ) :
    Set.InjOn (fun t => ((range t).filter fun t' => childF h t' % 2 = ℓ).card)
      ((range cnt).filter fun t => childF h t % 2 = ℓ) := by
  intro t1 h1 t2 h2 heq
  have h1' := (mem_filter.1 (Finset.mem_coe.1 h1)).2
  have h2' := (mem_filter.1 (Finset.mem_coe.1 h2)).2
  simp only at heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := rk_strict (P := fun t' => childF h t' % 2 = ℓ) hlt h1'
    omega
  · have := rk_strict (P := fun t' => childF h t' % 2 = ℓ) hlt h2'
    omega

private theorem row_lemma {L H CM RM ONE LV HV CM3 M MS G n : Nat} {MSF : Nat → Nat}
    {a b : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hmsf : msfOK MS MSF = true) (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G)
    (ha : ∀ q < n, a q < 2 ^ 399) (hb : ∀ q < n, b q < 2 ^ 399)
    (he : mulC L H CM3 RM (∑ q ∈ range n, a q * 2 ^ (1729 * q)) G =
      spreadM MSF (∑ q ∈ range n, b q * 2 ^ (1729 * q)))
    {q : Nat} (hq : q < n) (hpos : 0 < b q) : CCanon (b q) ∧ cvec (b q) = (OM G)ᵀ *ᵥ cvec (a q) := by
  have hRM := rm_eq hc
  have hZ := RowPf.spreadM_eq hms hmsf rfl hb
  have hspr : ∀ y < 2 ^ 399, spread MS y < 2 ^ 1729 := by
    intro y hy
    rw [RowPf.spread_eq hms hy]
    have := pk_lt (w := 13) (n := 133) (g := fun l => y / 2 ^ (3 * l) % 8)
      (fun _ _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    unfold pk at this
    exact this
  have hg : ∀ s < n, (if s < 133 then spread MS (b s) else b s) < 2 ^ 1729 := fun s hs => by
    split
    · exact hspr _ (hb s hs)
    · exact lt_of_lt_of_le (hb s hs) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hlane : lane 1729 (spreadM MSF (∑ q ∈ range n, b q * 2 ^ (1729 * q))) q =
      if q < 133 then spread MS (b q) else b q := by
    rw [hZ]
    have := lane_pk (w := 1729) (n := n) (s := q)
      (g := fun s => if s < 133 then spread MS (b s) else b s) hg hq
    unfold pk at this
    exact this
  have hrow : ∀ Y, rowL RM Y q = lane 1729 Y q := by
    intro Y
    rw [GatPf.rowL_eq, hRM, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  by_cases h133 : q < 133
  · have h1 : spread MS (b q) = rowL RM (mulC L H CM3 RM (∑ q ∈ range n, a q * 2 ^ (1729 * q)) G) q := by
      rw [hrow, he, hlane, if_pos h133]
    exact RowPf.spread_eq_rowL hc hms hcm rfl ha hG h133 hq (hb q hq) h1
  · have hcan := RowPf.mulC_canon hc hcm rfl ha hG
    have h0 : lane 1729 (mulC L H CM3 RM (∑ q ∈ range n, a q * 2 ^ (1729 * q)) G) q = 0 := by
      unfold lane
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hcan.1 (Nat.pow_le_pow_right (by norm_num)
        (by omega))), Nat.zero_mod]
    rw [he, hlane, if_neg h133] at h0
    omega

private theorem label_abs {L H CM RM ONE LV HV CM3 M MS G n : Nat} {MSF : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hmsf : msfOK MS MSF = true) (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G)
    {S : Finset ℕ} {rk : ℕ → ℕ} (hmap : ∀ t ∈ S, rk t < n) (hinj : Set.InjOn rk S)
    {p x : ℕ → ℕ} (hp : ∀ t, p t < 2 ^ 399) (hx : ∀ t, x t < 2 ^ 399)
    (he : mulC L H CM3 RM (∑ t ∈ S, p t * 2 ^ (1729 * rk t)) G =
      spreadM MSF (∑ t ∈ S, x t * 2 ^ (1729 * rk t)))
    {t : ℕ} (ht : t ∈ S) (hpos : 0 < x t) : CCanon (x t) ∧ cvec (x t) = (OM G)ᵀ *ᵥ cvec (p t) := by
  rw [reindex hmap p, reindex hmap x] at he
  have h := row_lemma (a := fun q => ∑ t ∈ S.filter (fun t => rk t = q), p t)
    (b := fun q => ∑ t ∈ S.filter (fun t => rk t = q), x t) hc hms hmsf hcm hG
    (fun q _ => fiber_lt hinj hp q) (fun q _ => fiber_lt hinj hx q) he (hmap t ht)
    (by beta_reduce; rw [fiber hinj ht]; exact hpos)
  beta_reduce at h
  rw [fiber hinj ht, fiber hinj ht] at h
  exact h

private theorem label_case {L H CM RM ONE LV HV CM3 M MS G h cnt ℓ : Nat} {MSF : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hmsf : msfOK MS MSF = true) (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G)
    {p x : ℕ → ℕ} (hp : ∀ t, p t < 2 ^ 399) (hx : ∀ t, x t < 2 ^ 399)
    (he : mulC L H CM3 RM (∑ t ∈ (range cnt).filter (fun t => childF h t % 2 = ℓ), p t *
        2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card)) G =
      spreadM MSF (∑ t ∈ (range cnt).filter (fun t => childF h t % 2 = ℓ), x t *
        2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card)))
    {t : ℕ} (ht : t < cnt) (hℓ : childF h t % 2 = ℓ) (hpos : 0 < x t) :
    CCanon (x t) ∧ cvec (x t) = (OM G)ᵀ *ᵥ cvec (p t) := by
  have e : ∀ f : ℕ → ℕ, ∑ t ∈ (range cnt).filter (fun t => childF h t % 2 = ℓ), f t *
        2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card) =
      ∑ t ∈ (range cnt).filter (fun t => childF h t % 2 = ℓ), f t *
        2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = ℓ).card) :=
    fun f => sum_congr rfl fun t ht => by rw [(mem_filter.1 ht).2]
  rw [e, e] at he
  exact label_abs (rk := fun t => ((range t).filter fun t' => childF h t' % 2 = ℓ).card) hc hms
    hmsf hcm hG (fun t' ht' => rk_strict (mem_range.1 (mem_filter.1 ht').1) (mem_filter.1 ht').2)
    (rk_inj h cnt ℓ) hp hx he (mem_filter.2 ⟨mem_range.2 ht, hℓ⟩) hpos

private theorem mod_zero_iff (x w : Nat) : ∀ k, x % 2 ^ (w * k) = 0 ↔
    ∀ l < k, x / 2 ^ (w * l) % 2 ^ w = 0
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul, Nat.add_eq_zero_iff, mod_zero_iff x w k]
    simp only [Nat.mul_eq_zero, (Nat.two_pow_pos _).ne', false_or]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact h1 l hl
      · exact h2
    · intro h
      exact ⟨fun l hl => h l (by omega), h k (by omega)⟩

private theorem row1 (Y r : Nat) : Y / 2 ^ (1729 * r) % 2 ^ 728 = 0 ↔
    ∀ l < 56, lane 13 Y (133 * r + l) = 0 := by
  rw [show (728 : ℕ) = 13 * 56 by norm_num, mod_zero_iff]
  refine forall₂_congr fun l _ => ?_
  unfold lane
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 1729 * r + 13 * l = 13 * (133 * r + l) by ring]

private theorem row2 (Y r : Nat) : Y / 2 ^ (1729 * r + 728) % 2 ^ 832 = 0 ↔
    ∀ l < 64, lane 13 Y (133 * r + (56 + l)) = 0 := by
  rw [show (832 : ℕ) = 13 * 64 by norm_num, mod_zero_iff]
  refine forall₂_congr fun l _ => ?_
  unfold lane
  rw [Nat.div_div_eq_div_mul, ← pow_add,
    show 1729 * r + 728 + 13 * l = 13 * (133 * r + (56 + l)) by ring]

private theorem fix_iff {L H CM RM ONE LV HV CM3 M GFC C r : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hG : Canon 5 133 13 GFC) (hr : r < 133) (l : Nat) (hl : l < 133) :
    lane 13 (mulC L H CM3 RM (leafA M C 133) GFC) (133 * r + l) = 0 ↔
      ((OM GFC)ᵀ *ᵥ cvec (recC M C r)) ⟨l, hl⟩ = 0 := by
  rw [RowPf.mulC_lane (a := recC M C) hc hcm (RowPf.leafA_eq hcm C 133)
    (fun r _ => RowPf.recC_lt hcm C r) hG hr hl, RowPf.mulVec_cvec]
  simp only [hr, if_true]
  exact (z5 (Nat.mod_lt _ (by norm_num))).symm

private theorem fix1 {L H CM RM ONE LV HV CM3 M GFC C r : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hG : Canon 5 133 13 GFC) (hr : r < 133) :
    mulC L H CM3 RM (leafA M C 133) GFC / 2 ^ (1729 * r) % 2 ^ 728 = 0 ↔
      ∀ i : Fin 133, i.val < 56 → ((OM GFC)ᵀ *ᵥ cvec (recC M C r)) i = 0 := by
  rw [row1]
  constructor
  · intro h i hi
    exact (fix_iff hc hcm hG hr i.val i.isLt).1 (h i hi)
  · intro h l hl
    exact (fix_iff hc hcm hG hr l (by omega)).2 (h ⟨l, by omega⟩ hl)

private theorem fix2 {L H CM RM ONE LV HV CM3 M GFC C r : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hG : Canon 5 133 13 GFC) (hr : r < 133) :
    mulC L H CM3 RM (leafA M C 133) GFC / 2 ^ (1729 * r + 728) % 2 ^ 832 = 0 ↔
      ∀ i : Fin 133, 56 ≤ i.val → i.val < 120 → ((OM GFC)ᵀ *ᵥ cvec (recC M C r)) i = 0 := by
  rw [row2]
  constructor
  · intro h i h1 h2
    have := h (i.val - 56) (by omega)
    rw [show 56 + (i.val - 56) = i.val by omega] at this
    exact (fix_iff hc hcm hG hr i.val i.isLt).1 this
  · intro h l hl
    exact (fix_iff hc hcm hG hr (56 + l) (by omega)).2
      (h ⟨56 + l, by omega⟩ (by simp) (by simp; omega))

theorem treeLeaf_sound' {L H CM RM ONE LV HV CM3 M MS : Nat} {XC TD MSF : Nat → Nat}
    {N GA GB GFC j : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hmsf : msfOK MS MSF = true) (hcm : cmOK CM3 M = true) (hGA : Canon 5 133 13 GA)
    (hGB : Canon 5 133 13 GB) (hGF : Canon 5 133 13 GFC)
    (h : treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j < 2 ^ 50) :
    TD j % 2 ^ 21 + TD j / 2 ^ 21 % 512 = TD (j + 1) % 2 ^ 21 ∧
      ((∀ i < TD (j + 1) % 2 ^ 21 / 133, XC i < 2 ^ 53200) →
        (∀ t < TD j / 2 ^ 21 % 512, 0 < recX XC M (TD j % 2 ^ 21 + t)) →
        ∀ t < TD j / 2 ^ 21 % 512, ∃ r < 133, 133 * j + r < TD j % 2 ^ 21 + t ∧
        CCanon (recX XC M (TD j % 2 ^ 21 + t)) ∧
        (cvec (recX XC M (TD j % 2 ^ 21 + t)) = (OM GA)ᵀ *ᵥ cvec (recX XC M (133 * j + r)) ∨
          cvec (recX XC M (TD j % 2 ^ 21 + t)) = (OM GB)ᵀ *ᵥ cvec (recX XC M (133 * j + r)))) ∧
      treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j =
        ((Finset.range (min (N - 133 * j) 133)).filter fun r => ∀ i : Fin 133, i.val < 56 →
            ((OM GFC)ᵀ *ᵥ cvec (recX XC M (133 * j + r))) i = 0).card +
          2 ^ 24 * ((Finset.range (min (N - 133 * j) 133)).filter fun r => ∀ i : Fin 133,
            56 ≤ i.val → i.val < 120 → ((OM GFC)ᵀ *ᵥ cvec (recX XC M (133 * j + r))) i = 0).card := by
  have hM := cm_M hcm
  obtain ⟨hchain, hcnt, hch, hgat, hval⟩ := GatPf.treeLeaf_unfold h
  refine ⟨hchain, ?_, ?_⟩
  · have hg := GatPf.gat_spec hM hgat
    obtain ⟨hEA, hEB⟩ := GatPf.bAnd_iff.1 hg
    have hEA' := Nat.eq_of_beq_eq_true hEA
    have hEB' := Nat.eq_of_beq_eq_true hEB
    intro H1 H2 t ht
    have hcf := GatPf.childrenOK_spec hch t (Nat.zero_le _) (by omega)
    generalize hcdef : TD j % 2 ^ 21 = c at *
    generalize hcndef : TD j / 2 ^ 21 % 512 = cnt at *
    generalize hc'def : TD (j + 1) % 2 ^ 21 = c' at *
    refine ⟨childF (TD j) t / 2, hcf.1, hcf.2, ?_⟩
    have hxe : recC M (chunk3 XC c) t = recX XC M (c + t) :=
      GatPf.chunk3_rec hM (by omega) fun i _ hi2 =>
        H1 i (lt_of_lt_of_le hi2 (Nat.div_le_div_right (by omega)))
    have hpos : 0 < recC M (chunk3 XC c) t := hxe ▸ H2 t ht
    rw [← hxe, RowPf.recX_eq XC M j _ hcf.1]
    have hp : ∀ t, recC M (XC j) (childF (TD j) t / 2) < 2 ^ 399 :=
      fun t => RowPf.recC_lt hcm _ _
    have hx : ∀ t, recC M (chunk3 XC c) t < 2 ^ 399 := fun t => RowPf.recC_lt hcm _ _
    rcases Nat.mod_two_eq_zero_or_one (childF (TD j) t) with h0 | h1
    · obtain ⟨a1, a2⟩ := label_case hc hms hmsf hcm hGA hp hx hEA' ht h0 hpos
      exact ⟨a1, Or.inl a2⟩
    · obtain ⟨a1, a2⟩ := label_case hc hms hmsf hcm hGB hp hx hEB' ht h1 hpos
      exact ⟨a1, Or.inr a2⟩
  · rw [hval, GatPf.fixRows_spec (rm_eq hc)]
    have k1 : (range (min (N - 133 * j) 133)).filter (fun r =>
        mulC L H CM3 RM (leafA M (XC j) 133) GFC / 2 ^ (1729 * r) % 2 ^ 728 = 0) =
        (range (min (N - 133 * j) 133)).filter (fun r => ∀ i : Fin 133, i.val < 56 →
          ((OM GFC)ᵀ *ᵥ cvec (recX XC M (133 * j + r))) i = 0) :=
      Finset.filter_congr fun r hr => by
        have hr' : r < 133 := by have := mem_range.1 hr; omega
        rw [RowPf.recX_eq XC M j r hr']
        exact fix1 hc hcm hGF hr'
    have k2 : (range (min (N - 133 * j) 133)).filter (fun r =>
        mulC L H CM3 RM (leafA M (XC j) 133) GFC / 2 ^ (1729 * r + 728) % 2 ^ 832 = 0) =
        (range (min (N - 133 * j) 133)).filter (fun r => ∀ i : Fin 133, 56 ≤ i.val →
          i.val < 120 → ((OM GFC)ᵀ *ᵥ cvec (recX XC M (133 * j + r))) i = 0) :=
      Finset.filter_congr fun r hr => by
        have hr' : r < 133 := by have := mem_range.1 hr; omega
        rw [RowPf.recX_eq XC M j r hr']
        exact fix2 hc hcm hGF hr'
    rw [k1, k2]

end CFSG.KS.HNLocal.TreePf

end
