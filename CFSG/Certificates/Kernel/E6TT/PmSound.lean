module

public import Certificates.Data.Kernel.E6TT.Pm
public import CFSG.Certificates.Kernel.E6TT.WeylSound

public section

namespace CFSG.KC.E6TT

open Certificates.Data.E6TableT (Vec iform roots)
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus (twistInner)
open CFSG.StandardType.TablePThreeKG (classSet)

local notation "ip" => CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6)

theorem inK_congr {H : List Nat} {f g : Vec → Vec} (h : (pmD H).map f = (pmD H).map g) :
    inK H f = inK H g := by
  unfold pmD at h
  unfold inK
  rw [h]

theorem negV_eq_map : ∀ x : Vec, negV x = x.map Int.neg
  | [] => rfl
  | a :: x => by
    change Int.neg a :: negV x = Int.neg a :: x.map Int.neg
    rw [negV_eq_map x]

theorem negV_ofFn (a : Fin Tag.E6.rank → ℤ) : negV (List.ofFn a) = List.ofFn (-a) := by
  rw [negV_eq_map, List.map_ofFn]
  rfl

theorem pmK_sound {l : List Vec}
    (hroot : ∀ x ∈ l, x ∈ roots ()) {H : List Nat} {O : List (List Nat)}
    (hc : classK l H O = true) (hpm : pmK l H = true)
    {σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hadd : ∀ a b, σ (a + b) = σ a + σ b)
    (hmaps : ∀ γ ∈ classSet l, σ γ ∈ classSet l) (hip : ∀ x y, ip (σ x) (σ y) = ip x y) :
    twistInner (classSet l) σ ∨ twistInner (classSet l) (fun x => -σ x) := by
  obtain ⟨hΔl, -, -, -⟩ := classK_spec hc
  unfold pmK at hpm
  obtain ⟨h2, hpm⟩ := bAnd_true hpm
  obtain ⟨hne, hall⟩ := bAnd_true hpm
  have hr : H.getD 0 0 = 2 := Nat.eq_of_beq_eq_true h2
  set d0 : Vec := digs 3 3 (H.getD 2 0) 6 with hd0
  set d1 : Vec := digs 3 3 (Nat.shiftRight (H.getD 2 0) 18) 6 with hd1
  have hD : pmD H = [d0, d1] := by
    unfold pmD
    rw [hr]
    rfl
  have hD' : vecs (H.getD 2 0) (H.getD 0 0) = [d0, d1] := hD
  rw [hD] at hne hall
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hne hall
  have hne' : d1 ≠ d0 := by
    intro h
    rw [h, beq_self_eq_true] at hne
    exact absurd hne (by decide)
  have hm0 : d0 ∈ vecs (H.getD 2 0) (H.getD 0 0) := by rw [hD']; exact List.mem_cons_self
  have hm1 : d1 ∈ vecs (H.getD 2 0) (H.getD 0 0) := by
    rw [hD']; exact List.mem_cons_of_mem _ List.mem_cons_self
  have h60 : d0.length = 6 := length_of_mem_vecs _ _ _ hm0
  have h61 : d1.length = 6 := length_of_mem_vecs _ _ _ hm1
  set x : Vec := List.ofFn (σ (toV d0)) with hx
  set y : Vec := List.ofFn (σ (toV d1)) with hy
  have hxl : x ∈ l := hmaps _ (mem_classSet_toV h60 (hΔl _ hm0))
  have hyl : y ∈ l := hmaps _ (mem_classSet_toV h61 (hΔl _ hm1))
  have hpair : iform x y = iform d0 d1 := by
    rw [iform_eq_ip (length_ofFn6 _) (length_ofFn6 _), toV_ofFn, toV_ofFn, hip,
      ← iform_eq_ip h60 h61]
  have h := List.all_eq_true.1 (List.all_eq_true.1 hall x hxl) y hyl
  have hb : (iform x y == iform d0 d1) = true := beq_iff_eq.2 hpair
  rw [hb] at h
  have hb10 : (d1 == d0) = false := beq_eq_false_iff_ne.2 hne'
  cases hp : inK H (pmMap d0 x y)
  ·
    rw [hp] at h
    right
    have hneg : inK H (pmMap d0 (negV x) (negV y)) = true := h
    refine inK_sound hroot hc (σ := fun z => -σ z) (fun a b => by rw [hadd, neg_add])
      (f := fun z => List.ofFn (-σ (toV z))) (fun γ => by rw [toV_ofFn]) ?_
    rw [← hneg]
    apply inK_congr
    rw [hD]
    simp only [List.map_cons, List.map_nil, pmMap, beq_self_eq_true, hb10, hx, hy, negV_ofFn]
  · left
    refine inK_sound hroot hc hadd (f := fun z => List.ofFn (σ (toV z))) (fun γ => by rw [toV_ofFn])
      ?_
    rw [← hp]
    apply inK_congr
    rw [hD]
    simp only [List.map_cons, List.map_nil, pmMap, beq_self_eq_true, hb10, hx, hy]

theorem pmAll_spec : ∀ {cl : List (List Vec)} {Hs : List (List Nat)}, pmAll cl Hs = true →
    ∀ j < cl.length, pmK (cl.getD j []) (Hs.getD j []) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | l :: cl, [], h, _, _ => absurd h (by simp [pmAll])
  | l :: cl, H :: Hs, h, j, hj => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases j with _ | j
    · exact h1
    · exact pmAll_spec h2 j (by simpa using hj)

end CFSG.KC.E6TT

end
