module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermSix

public section

namespace CFSG.KS.Sp6I

open CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {Γ : Type*} [Group Γ] {n : Nat}

theorem eElt_mem_closure {k : Nat} (v : Fin k → Γ) (c : Fin k → ZMod 2) :
    eElt v c ∈ Subgroup.closure (Set.range v) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

theorem exists_eElt_of_mem_closure {k : Nat} {v : Fin k → Γ} (hsq : ∀ i, v i * v i = 1)
    (hc : ∀ i j, Commute (v i) (v j)) {x : Γ} (hx : x ∈ Subgroup.closure (Set.range v)) :
    ∃ c, eElt v c = x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨Pi.single i 1, eElt_single v i⟩
  | one => exact ⟨0, eElt_zero v⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, eElt_add hsq hc c d⟩
  | inv x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c, ?_⟩
    rw [eq_comm, inv_eq_iff_mul_eq_one, ← eElt_add hsq hc, add_self_zmod2, eElt_zero]

theorem map_conj_one (K : Subgroup Γ) : K.map (MulAut.conj (1 : Γ)).toMonoidHom = K := by
  convert Subgroup.map_id K
  ext x
  simp

theorem map_conj_mul' (a b : Γ) (K : Subgroup Γ) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_eq_of_le [Finite Γ] {g : Γ} {K : Subgroup Γ}
    (h : K.map (MulAut.conj g).toMonoidHom ≤ K) : K.map (MulAut.conj g).toMonoidHom = K :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem perm_of_mem_closure [Finite Γ] {D : Nat → Subgroup Γ} {S₀ : Set Γ}
    (hS : ∀ x ∈ S₀, ∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj x).toMonoidHom = D s) {g : Γ}
    (hg : g ∈ Subgroup.closure S₀) :
    ∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj g).toMonoidHom = D s := by
  have hmul : ∀ x y : Γ, (∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj x).toMonoidHom = D s) →
      (∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj y).toMonoidHom = D s) →
      ∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj (x * y)).toMonoidHom = D s := by
    intro x y hx hy r hr
    obtain ⟨s, hs, hys⟩ := hy r hr
    obtain ⟨t, ht, hxt⟩ := hx s hs
    exact ⟨t, ht, by rw [map_conj_mul', hys, hxt]⟩
  have hpow : ∀ x : Γ, (∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj x).toMonoidHom = D s) →
      ∀ m : Nat, ∀ r < 6, ∃ s < 6, (D r).map (MulAut.conj (x ^ m)).toMonoidHom = D s := by
    intro x hx m
    induction m with
    | zero => exact fun r hr => ⟨r, hr, by rw [pow_zero, map_conj_one]⟩
    | succ m ih => exact pow_succ x m ▸ hmul _ _ ih hx
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact fun r hr => ⟨r, hr, map_conj_one _⟩
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx =>
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel (orderOf_pos x),
        pow_orderOf_eq_one]
    rw [e]
    exact hpow x hx _

variable {n : Nat}

theorem getD_map_spanTabs {ds : List (List Table)} (hdl : ds.length = 6) {s : Nat} (hs : s < 6) :
    (ds.map (spanTabs n)).getD s [] = spanTabs n (ds.getD s []) := by
  have hs' : s < ds.length := by rw [hdl]; exact hs
  rw [List.getD_eq_getElem _ _ (by simpa using hs'), List.getD_eq_getElem _ _ hs',
    List.getElem_map]

theorem sixTestS_false_of_gens (hn : n < 2 ^ 32) {l : Nat} {w : Fin l → Equiv.Perm (Fin n)}
    {ws : List Table}
    (hws : List.Forall₂ (Rep n) ws (List.ofFn w)) {ds : List (List Table)} (hdl : ds.length = 6)
    {k : Nat → Nat} {d : (r : Nat) → Fin (k r) → Equiv.Perm (Fin n)}
    (hds : ∀ r < 6, List.Forall₂ (Rep n) (ds.getD r []) (List.ofFn (d r)))
    (hdsq : ∀ r < 6, ∀ i, d r i * d r i = 1) (hdc : ∀ r < 6, ∀ i j, Commute (d r i) (d r j))
    {H : Subgroup (Equiv.Perm (Fin n))} {S₀ : Set (Equiv.Perm (Fin n))}
    (hS : ∀ x ∈ S₀, ∀ r < 6, ∃ s < 6, (Subgroup.closure (Set.range (d r))).map
      (MulAut.conj x).toMonoidHom = Subgroup.closure (Set.range (d s)))
    (hK : ∀ g ∈ H, (∀ i, ∃ c, g * w i * g⁻¹ = eElt w c) → g ∈ Subgroup.closure S₀)
    (hsep : ∀ a b : Equiv.Perm (Fin n), a ∈ Subgroup.closure (Set.range w) →
      b ∈ Subgroup.closure (Set.range w) →
      (∀ r < 6, a ∈ Subgroup.closure (Set.range (d r)) ↔ b ∈ Subgroup.closure (Set.range (d r))) →
        a = b)
    (hcent : ∀ g ∈ H, ∀ T, Rep n T g → (∀ i, g * w i = w i * g) → ∃ c, eElt w c = g)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H) {T : Table} (hT : Rep n T g) :
    sixTestS n ws (spanTabs n ws) ds (ds.map (spanTabs n)) T = false := by
  set D : Nat → Subgroup (Equiv.Perm (Fin n)) := fun r => Subgroup.closure (Set.range (d r))
    with hD
  have hcj : ∀ r < 6, ∀ s < 6, conjIn n (ds.getD r []) ((ds.map (spanTabs n)).getD s []) T =
      true ↔ (D r).map (MulAut.conj g).toMonoidHom ≤ D s := by
    intro r hr s hs
    rw [getD_map_spanTabs hdl hs, conjIn_spanTabs, conjSpanIn_iff hn (hds r hr) (hds s hs) hT]
    constructor
    · intro h
      rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨c, hc⟩ := h i
      change g * d r i * g⁻¹ ∈ D s
      rw [hc]
      exact eElt_mem_closure _ c
    · intro h i
      exact exists_eElt_of_mem_closure (hdsq s hs) (hdc s hs)
        (h ⟨d r i, Subgroup.subset_closure (Set.mem_range_self i), rfl⟩) |>.imp fun c hc => hc.symm
  unfold sixTestS
  rw [Bool.and_eq_false_iff]
  by_cases hN : conjIn n ws (spanTabs n ws) T = true
  · right
    have hN' : ∀ i, ∃ c, g * w i * g⁻¹ = eElt w c := by
      rw [conjIn_spanTabs, conjSpanIn_iff hn hws hws hT] at hN
      exact hN
    have hP := perm_of_mem_closure hS (hK g hg hN')
    rw [Bool.or_eq_false_iff, Bool.not_eq_false', List.all_eq_true]
    refine ⟨fun r hr => ?_, ?_⟩
    · obtain ⟨s, hs, hrs⟩ := hP r (List.mem_range.mp hr)
      exact List.any_eq_true.mpr ⟨s, List.mem_range.mpr hs,
        (hcj r (List.mem_range.mp hr) s hs).mpr hrs.le⟩
    · rw [Bool.and_eq_false_iff, Bool.not_eq_false', or_iff_not_imp_left, Bool.not_eq_false,
        List.all_eq_true]
      intro hfix
      have hfix' : ∀ r < 6, (D r).map (MulAut.conj g).toMonoidHom = D r := fun r hr =>
        map_conj_eq_of_le ((hcj r hr r hr).mp (hfix r (List.mem_range.mpr hr)))
      have hcomm : ∀ i, g * w i = w i * g := by
        intro i
        obtain ⟨c, hc⟩ := hN' i
        have hx : g * w i * g⁻¹ = w i := by
          refine hsep _ _ (by rw [hc]; exact eElt_mem_closure w c)
            (Subgroup.subset_closure (Set.mem_range_self i)) fun r hr => ?_
          change g * w i * g⁻¹ ∈ D r ↔ w i ∈ D r
          constructor
          · intro hm
            rw [← hfix' r hr] at hm
            obtain ⟨y, hy, hyx⟩ := hm
            have : y = w i := by
              simpa [MulAut.conj_apply] using hyx
            rw [← this]
            exact hy
          · intro hm
            rw [← hfix' r hr]
            exact ⟨w i, hm, rfl⟩
        have h2 : g * w i * g⁻¹ * g = w i * g := by rw [hx]
        rwa [inv_mul_cancel_right] at h2
      obtain ⟨c, hc⟩ := hcent g hg T hT hcomm
      rw [inSp_spanTabs, inSpanT_iff hn hws hT]
      exact ⟨c, hc⟩
  · left
    exact Bool.eq_false_iff.mpr hN

end CFSG.KS.Sp6I

end
