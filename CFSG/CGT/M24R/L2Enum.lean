
module

public import CFSG.CGT.M24R.L2EnumBase

public import CFSG.CGT.M24R.L2Tab

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

section Ctx

theorem ctxCheck_spec : (mkCtx ()).ld.size = 65536 ∧ (mkCtx ()).codes.length = 322560 ∧
    ∀ c ∈ (mkCtx ()).codes, codeOf ((mkCtx ()).tab c) = c := by
  have h := Certificates.certificate21193.2.1
  simp only [ctxCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ctx_lt {m : ℕ} (hm : m < 65536) :
    (mkCtx ()).lt[m]! = wTab (((mkCtx ()).ld[m]!).getD []) := by
  have hs := ctxCheck_spec.1
  show ((mkCtx ()).ld.map fun o => wTab (o.getD []))[m]! = _
  exact getElem!_map_of_lt _ _ (by rw [hs]; exact hm)

theorem isTab_tab {c : ℕ} (hc : c < 1048576) : IsTab ((mkCtx ()).tab c) (el c) := by
  have h1 := ctx_tt (Nat.mod_lt c (by norm_num : 0 < 16))
  have h2 := ctx_lt (m := c / 16) (by omega)
  unfold Ctx8.tab el Ctx8.word
  rw [h1, h2, n8_append]
  exact (isTab_wTab _).mul (isTab_wTab _)

theorem el_injOn {c c' : ℕ} (hc : c ∈ (mkCtx ()).codes) (hc' : c' ∈ (mkCtx ()).codes)
    (h : el c = el c') : c = c' := by
  have h1 : IsTab ((mkCtx ()).tab c) (el c) := isTab_tab (mem_codes.1 hc).1
  have h2 : IsTab ((mkCtx ()).tab c') (el c) := h ▸ isTab_tab (mem_codes.1 hc').1
  have := table_eq_of_rep h1 h2 (tab_size _) (tab_size _)
  rw [← ctxCheck_spec.2.2 c hc, ← ctxCheck_spec.2.2 c' hc', this]

theorem el_surj (hcard : Nat.card N8 = 322560) (x : N8) :
    ∃ c ∈ (mkCtx ()).codes, x = el c := by
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hL : (mkCtx ()).codes.length = 322560 := ctxCheck_spec.2.1
  let F : Fin (mkCtx ()).codes.length → N8 := fun i => el (mkCtx ()).codes[i]
  have hinj : Function.Injective F := by
    intro i j hij
    have := el_injOn (List.getElem_mem _) (List.getElem_mem _) hij
    exact Fin.ext ((codes_nodup.getElem_inj_iff).1 this)
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_fin, hL, hcard])
  obtain ⟨i, hi⟩ := hbij.2 x
  exact ⟨_, List.getElem_mem _, hi.symm⟩

theorem π8_injective (hcard : Nat.card N8 = 322560) :
    Function.Injective (π8 : N8 →* Equiv.Perm (Fin 16)) := by
  intro x y hxy
  obtain ⟨c, hc, rfl⟩ := el_surj hcard x
  obtain ⟨c', hc', rfl⟩ := el_surj hcard y
  have h1 : IsTab ((mkCtx ()).tab c) (el c) := isTab_tab (mem_codes.1 hc).1
  have h2 : Rep 16 ((mkCtx ()).tab c') (π8 (el c)) := by
    rw [hxy]
    exact isTab_tab (mem_codes.1 hc').1
  have := table_eq_of_rep h1 h2 (tab_size _) (tab_size _)
  rw [← ctxCheck_spec.2.2 c hc, ← ctxCheck_spec.2.2 c' hc', this]

theorem IsTab.eq_of_eq (hcard : Nat.card N8 = 322560) {X : Table} {x y : N8} (hx : IsTab X x)
    (hy : IsTab X y) : x = y :=
  π8_injective hcard (perm_eq_of_rep hx hy)

theorem IsTab.eq_iff (hcard : Nat.card N8 = 322560) {X Y : Table} {x y : N8} (hX : IsTab X x)
    (hY : IsTab Y y) (hXs : X.size = 16) (hYs : Y.size = 16) : X = Y ↔ x = y := by
  constructor
  · rintro rfl
    exact hX.eq_of_eq hcard hY
  · rintro rfl
    exact table_eq_of_rep hX hY hXs hYs

theorem IsTab.beq_iff (hcard : Nat.card N8 = 322560) {X Y : Table} {x y : N8} (hX : IsTab X x)
    (hY : IsTab Y y) (hXs : X.size = 16) (hYs : Y.size = 16) : (X == Y) = true ↔ x = y := by
  rw [beq_iff_eq]
  exact hX.eq_iff hcard hY hXs hYs

theorem IsTab.commT_iff (hcard : Nat.card N8 = 322560) {X Y : Table} {x y : N8} (hX : IsTab X x)
    (hY : IsTab Y y) : commT X Y = true ↔ x * y = y * x :=
  (hX.mul hY).beq_iff hcard (hY.mul hX) (compT_size _ _) (compT_size _ _)

end Ctx

end CFSG.CGT.M24R
