module

public import Certificates.Data.Kernel.PermCent.Sp6E4Twin
public import CFSG.Certificates.Kernel.PermCent.Sp6BSound
public import Certificates.Data.E189E4tCheck

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6E

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.Certificates.Kernel.PkCV.Sp6B

theorem map_cOf_ev (l : List (Equiv.Perm (Fin 36))) : (l.map cOf).map ev = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun σ _ => ev_cOf σ

theorem rep2_ev : sp6Rep2 = ev r2C := by rw [r2C.eq_1, ev_cOf]

theorem rho_ev : rho () = ev iC := by rw [iC.eq_1, ev_cOf]

theorem jay_ev : jay () = ev jC := by rw [jC.eq_1, ev_cOf]

theorem ngWit_ev : ngWit () = ngWitC.map ev := by rw [ngWitC.eq_1, map_cOf_ev]

theorem E2_ev : enumeration sp6CentQ2 = E2.map ev := by
  rw [E2.eq_1]
  exact enum_ev _

theorem getD_ev1 (W : List (CV 36)) (k : Nat) : (W.map ev).getD k 1 = ev (W.getD k 1) := by
  rw [one_eq_ev, getD_ev]

theorem twin_ev : twin () = ev (wsC.getD 11 1) := by rw [twin.eq_1, ws_ev, getD_ev1]

theorem norms_ev (L : List (CV 36)) (i j h : CV 36) :
    norms (L.map ev) (ev i) (ev j) (ev h) = normsC L i j h := by
  rw [norms.eq_1, normsC.eq_1]
  simp only [ev_inv', ev_mul', decide_mem_map_ev]

theorem all_range_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    (List.range l.length).all (fun k => p (l.getD k d)) = l.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := h k (List.mem_range.2 hk)
    rwa [List.getD_eq_getElem _ _ hk] at this
  · intro h k hk
    have hk' := List.mem_range.1 hk
    rw [List.getD_eq_getElem _ _ hk']
    exact h _ (List.getElem_mem hk')

theorem any_range_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    (List.range l.length).any (fun k => p (l.getD k d)) = l.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, h⟩
    have hk' := List.mem_range.1 hk
    rw [List.getD_eq_getElem _ _ hk'] at h
    exact ⟨_, List.getElem_mem hk', h⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact ⟨k, List.mem_range.2 hk, by rwa [List.getD_eq_getElem _ _ hk]⟩

theorem goodWit_ev (r i j t x : CV 36) :
    goodWit (ev r) (ev i) (ev j) (ev t) (ev x) = goodWitC r i j t x := by
  simp only [goodWit.eq_1, goodWitC.eq_1, commGens.eq_1, commGensC.eq_1, ev_inv', ev_mul',
    decide_ev_eq]

theorem tCheck_ev (L : List (CV 36)) (r i j : CV 36) (W : List (CV 36)) :
    tCheck (L.map ev) (ev r) (ev i) (ev j) (W.map ev) = tT L r i j W W := by
  rw [tCheck.eq_1, tT.eq_1, List.length_map]
  simp only [getD_ev1]
  refine (all_range_getD W 1 fun w =>
    memberOK (L.map ev) (ev r) (ev i) (ev j) (W.map ev) (ev w * ev r * (ev w)⁻¹)).trans ?_
  congr 1
  funext w
  rw [ev_inv', ev_mul', ev_mul', memberOK.eq_1, relevantT.eq_1, List.length_map]
  simp only [getD_ev1, ev_mul', decide_ev_eq, norms_ev]
  congr 1
  refine (any_range_getD W 1 fun x => goodWit (ev r) (ev i) (ev j) (ev (w * r * w⁻¹)) (ev x)).trans ?_
  congr 1
  funext x
  exact goodWit_ev r i j _ x

end CFSG.Certificates.Kernel.PkCV.Sp6E

end
