module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDVec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

noncomputable def sec5c_phi (L B : Subgroup G) (r : G) (i : Fin 6) (fr : NFrame Q (Fin 6) 1)
    (φc : ↥L →* omegaGroup hQ) (v : Fin 6 → ZMod 2) : G :=
  (if ∑ j, v j = 0 then 1 else r) *
    (sec5c_liftL L B φc (fr.signChange (sec5c_supp (v + (∑ j, v j) • Pi.single i 1))) : G)

theorem sec5c_sum_ev (i : Fin 6) (v : Fin 6 → ZMod 2) :
    ∑ j, (v + (∑ j, v j) • (Pi.single i 1 : Fin 6 → ZMod 2)) j = 0 := by
  rw [sec5c_sum_add]
  have h2 : ∑ j, (Pi.single i (1 : ZMod 2) : Fin 6 → ZMod 2) j = 1 := by
    simp [Finset.sum_pi_single']
  have h1 : ∑ j, ((∑ j, v j) • (Pi.single i 1 : Fin 6 → ZMod 2)) j = ∑ j, v j := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h2, mul_one]
  rw [h1]
  exact CharTwo.add_self_eq_zero _

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem ev_mem (v : Fin 6 → ZMod 2) :
    fr.signChange (sec5c_supp (v + (∑ j, v j) • Pi.single i 1)) ∈ ffB0 fr :=
  signChange_mem_ffB0 fr
    ((sec5c_isEvenVec_iff _).mp (sec5c_sum_ev i v))

theorem phi_even {v : Fin 6 → ZMod 2} (hv : IsEvenVec v) :
    sec5c_phi L B r i fr φc v = (sec5c_liftL L B φc (fr.signChange (sec5c_supp v)) : G) := by
  have hv' : ∑ j, v j = 0 := hv
  unfold sec5c_phi
  rw [if_pos hv', hv', zero_smul, add_zero, one_mul]

theorem phi_odd {v : Fin 6 → ZMod 2} (hv : ¬ IsEvenVec v) :
    sec5c_phi L B r i fr φc v =
      r * (sec5c_liftL L B φc (fr.signChange (sec5c_supp (v + Pi.single i 1))) : G) := by
  have hv' : ∑ j, v j ≠ 0 := hv
  have h1 : ∑ j, v j = 1 := by
    generalize ∑ j, v j = a at hv'
    revert a
    decide
  unfold sec5c_phi
  rw [if_neg hv', h1, one_smul]

theorem phi_zero : sec5c_phi L B r i fr φc 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 6 → ZMod 2) := by simp [IsEvenVec]
  rw [h.phi_even h0, sec5c_supp_zero, fr.signChange_empty, h.liftL_one]
  rfl

private theorem ite_add (a b : ZMod 2) :
    (if a + b = 0 then (1 : G) else r) =
      (if a = 0 then (1 : G) else r) * (if b = 0 then (1 : G) else r) := by
  have hr := h.r_sq
  have hab : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases hab a with rfl | rfl <;> rcases hab b with rfl | rfl <;> simp [hr, h11, h10]

private theorem ite_comm (a : ZMod 2) {g : OGroup Q} (hg : g ∈ ffB0 fr) :
    (if a = 0 then (1 : G) else r) * (sec5c_liftL L B φc g : G) =
      (sec5c_liftL L B φc g : G) * (if a = 0 then (1 : G) else r) := by
  by_cases ha : a = 0
  · simp [ha]
  · simp only [if_neg ha]
    exact h.r_comm_liftL hg

theorem phi_add (v w : Fin 6 → ZMod 2) :
    sec5c_phi L B r i fr φc (v + w) = sec5c_phi L B r i fr φc v * sec5c_phi L B r i fr φc w := by
  have hev : v + w + (∑ j, (v + w) j) • (Pi.single i 1 : Fin 6 → ZMod 2) =
      (v + (∑ j, v j) • Pi.single i 1) + (w + (∑ j, w j) • Pi.single i 1) := by
    rw [sec5c_sum_add, add_smul]
    abel
  unfold sec5c_phi
  rw [hev, sec5c_supp_add, ← fr.signChange_mul,
    h.liftL_mul (h.ev_mem v) (h.ev_mem w), sec5c_sum_add, ite_add h]
  simp only [Subgroup.coe_mul]
  calc (if ∑ j, v j = 0 then (1 : G) else r) * (if ∑ j, w j = 0 then (1 : G) else r) *
        ((sec5c_liftL L B φc (fr.signChange (sec5c_supp (v + (∑ j, v j) • Pi.single i 1))) : G) *
          (sec5c_liftL L B φc
            (fr.signChange (sec5c_supp (w + (∑ j, w j) • Pi.single i 1))) : G))
      = (if ∑ j, v j = 0 then (1 : G) else r) *
          ((if ∑ j, w j = 0 then (1 : G) else r) *
            (sec5c_liftL L B φc
              (fr.signChange (sec5c_supp (v + (∑ j, v j) • Pi.single i 1))) : G)) *
          (sec5c_liftL L B φc (fr.signChange (sec5c_supp (w + (∑ j, w j) • Pi.single i 1))) : G) :=
        by group
    _ = (if ∑ j, v j = 0 then (1 : G) else r) *
          ((sec5c_liftL L B φc
              (fr.signChange (sec5c_supp (v + (∑ j, v j) • Pi.single i 1))) : G) *
            (if ∑ j, w j = 0 then (1 : G) else r)) *
          (sec5c_liftL L B φc (fr.signChange (sec5c_supp (w + (∑ j, w j) • Pi.single i 1))) : G) :=
        by rw [ite_comm h _ (h.ev_mem v)]
    _ = _ := by group

theorem phi_sq (v : Fin 6 → ZMod 2) :
    sec5c_phi L B r i fr φc v * sec5c_phi L B r i fr φc v = 1 := by
  rw [← h.phi_add, show v + v = 0 from funext fun j => CharTwo.add_self_eq_zero (v j)]
  exact h.phi_zero

theorem phi_eq_one {u : Fin 6 → ZMod 2} (hu : sec5c_phi L B r i fr φc u = 1) : u = 0 := by
  by_cases he : IsEvenVec u
  · rw [h.phi_even he] at hu
    have h1 : sec5c_liftL L B φc (fr.signChange (sec5c_supp u)) = 1 := Subtype.ext hu
    have hg := h.map_liftL (signChange_mem_ffB0 fr ((sec5c_isEvenVec_iff u).mp he))
    rw [h1] at hg
    have hg' : fr.signChange (sec5c_supp u) = fr.signChange ∅ := by
      rw [fr.signChange_empty, ← hg]
      simp
    exact sec5c_supp_injective ((fr.signChange_injective hg').trans sec5c_supp_zero.symm)
  · rw [h.phi_odd he] at hu
    exfalso
    apply h.r_not_mem
    have hl : (sec5c_liftL L B φc (fr.signChange (sec5c_supp (u + Pi.single i 1))) : G) ∈ L :=
      Subtype.mem _
    rw [eq_inv_of_mul_eq_one_left hu]
    exact L.inv_mem hl

theorem phi_inj {v w : Fin 6 → ZMod 2}
    (hvw : sec5c_phi L B r i fr φc v = sec5c_phi L B r i fr φc w) : v = w := by
  have h1 : sec5c_phi L B r i fr φc (v + w) = 1 := by
    rw [h.phi_add, ← hvw]
    exact h.phi_sq v
  have h2 := h.phi_eq_one h1
  funext j
  exact CharTwo.add_eq_zero.mp (congrFun h2 j)

theorem phi_mem_L_iff (v : Fin 6 → ZMod 2) :
    sec5c_phi L B r i fr φc v ∈ L ↔ IsEvenVec v := by
  by_cases he : IsEvenVec v
  · rw [h.phi_even he]
    exact iff_of_true (Subtype.mem _) he
  · rw [h.phi_odd he]
    refine iff_of_false (fun hm => h.r_not_mem ?_) he
    exact (Subgroup.mul_mem_cancel_right L (Subtype.mem _)).mp hm

theorem phi_mem_A (v : Fin 6 → ZMod 2) : sec5c_phi L B r i fr φc v ∈ zpowers r ⊔ B := by
  unfold sec5c_phi
  refine mul_mem ?_ (Subgroup.mem_sup_right (h.liftL_mem (h.ev_mem v)))
  split_ifs
  · exact one_mem _
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers r)

noncomputable def phiHom : Multiplicative (Fin 6 → ZMod 2) →* G where
  toFun v := sec5c_phi L B r i fr φc (Multiplicative.toAdd v)
  map_one' := h.phi_zero
  map_mul' a b := h.phi_add _ _

theorem phi_vec {J : Finset (Fin 6)} (hJ : Even J.card) :
    sec5c_phi L B r i fr φc (sec5c_vec J) = (sec5c_liftL L B φc (fr.signChange J) : G) := by
  have he : IsEvenVec (sec5c_vec J) := by
    rw [sec5c_isEvenVec_iff, sec5c_supp_vec]
    exact hJ
  rw [h.phi_even he, sec5c_supp_vec]

theorem phi_single : sec5c_phi L B r i fr φc (Pi.single i 1) = r := by
  have hodd : ¬ IsEvenVec (Pi.single i 1 : Fin 6 → ZMod 2) := by
    unfold IsEvenVec
    rw [Finset.sum_pi_single']
    simp
  rw [h.phi_odd hodd, show (Pi.single i 1 : Fin 6 → ZMod 2) + Pi.single i 1 = 0 from
    funext fun j => CharTwo.add_self_eq_zero _, sec5c_supp_zero, fr.signChange_empty, h.liftL_one]
  simp

theorem phi_single' (j : Fin 6) :
    sec5c_phi L B r i fr φc (Pi.single j 1) =
      r * (sec5c_liftL L B φc (fr.signChange (symmDiff {j} {i})) : G) := by
  have hodd : ¬ IsEvenVec (Pi.single j 1 : Fin 6 → ZMod 2) := by
    unfold IsEvenVec
    rw [Finset.sum_pi_single']
    simp
  rw [h.phi_odd hodd, sec5c_supp_add, sec5c_supp_single, sec5c_supp_single]

theorem mem_A_iff {x : G} :
    x ∈ zpowers r ⊔ B ↔ ∃ v, sec5c_phi L B r i fr φc v = x := by
  constructor
  · intro hx
    have hle : zpowers r ⊔ B ≤ (h.phiHom).range := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact ⟨Multiplicative.ofAdd (Pi.single i 1), h.phi_single⟩
      · intro b hb
        have hbL : b ∈ L := h.B_le hb
        obtain ⟨J, hJ, hφ⟩ := (mem_ffB0_iff fr).mp (h.B_map ⟨b, hbL⟩ hb)
        refine ⟨Multiplicative.ofAdd (sec5c_vec J), ?_⟩
        change sec5c_phi L B r i fr φc (sec5c_vec J) = b
        rw [h.phi_vec hJ, ← hφ]
        exact congrArg Subtype.val (h.liftL_unique (b := ⟨b, hbL⟩) hb)
    obtain ⟨v, hv⟩ := hle hx
    exact ⟨Multiplicative.toAdd v, hv⟩
  · rintro ⟨v, rfl⟩
    exact h.phi_mem_A v

theorem A_sq {x : G} (hx : x ∈ zpowers r ⊔ B) : x * x = 1 := by
  obtain ⟨v, rfl⟩ := (h.mem_A_iff).mp hx
  exact h.phi_sq v

theorem A_comm {x y : G} (hx : x ∈ zpowers r ⊔ B) (hy : y ∈ zpowers r ⊔ B) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := (h.mem_A_iff).mp hx
  obtain ⟨w, rfl⟩ := (h.mem_A_iff).mp hy
  rw [← h.phi_add, ← h.phi_add, add_comm]

theorem A_inf_L {x : G} (hx : x ∈ zpowers r ⊔ B) (hxL : x ∈ L) : x ∈ B := by
  obtain ⟨v, rfl⟩ := (h.mem_A_iff).mp hx
  have he := (h.phi_mem_L_iff v).mp hxL
  rw [h.phi_even he]
  exact h.liftL_mem (signChange_mem_ffB0 fr ((sec5c_isEvenVec_iff v).mp he))

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega
