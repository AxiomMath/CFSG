module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeHyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Quiet
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylHull
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp22Wyl

namespace WylFrame

section BGroup

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y} {z : Y}
  (F : WylFrame Ω W z) (c : Q3CL.Thompson.Ctx Ω W) (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

@[expose] def B : Subgroup Y := Subgroup.closure ({z, F.a 0 * F.a 1, F.a 2 * F.a 3} : Set Y)

include F c hc

theorem a_mul_sq (i j : Fin 4) : (F.a i * F.a j) * (F.a i * F.a j) = 1 := by
  have hij : F.a j * F.a i = F.a i * F.a j := hc _ (F.a_mem_W j) _ (F.a_mem_W i)
  calc (F.a i * F.a j) * (F.a i * F.a j) = F.a i * (F.a j * F.a i) * F.a j := by group
    _ = F.a i * (F.a i * F.a j) * F.a j := by rw [hij]
    _ = (F.a i * F.a i) * (F.a j * F.a j) := by group
    _ = 1 := by rw [F.a_sq i, F.a_sq j]; exact F.z_sq

theorem a_mul_mem_W (i j : Fin 4) : F.a i * F.a j ∈ W := W.mul_mem (F.a_mem_W i) (F.a_mem_W j)

theorem a_mul_ne {i j : Fin 4} (hij : i ≠ j) :
    F.a i * F.a j ≠ 1 ∧ F.a i * F.a j ≠ z := by
  have key : ∀ w, (w = 1 ∨ w = z) → F.a i * F.a j ≠ w := by
    intro w hw hprod
    have hwK : w ∈ (F.ρ j).K := by
      rcases hw with rfl | rfl
      · exact (F.ρ j).K.one_mem
      · exact (F.hz j).mem
    have hai : F.a i ∈ (F.ρ j).K := by
      have e : F.a i = w * (F.a j)⁻¹ := by rw [← hprod]; group
      rw [e]
      exact (F.ρ j).K.mul_mem hwK ((F.ρ j).K.inv_mem (F.a_mem_K j))
    have hle1 : Subgroup.zpowers (F.a i) ≤ (F.ρ i).K := Subgroup.zpowers_le.mpr (F.a_mem_K i)
    have hle2 : Subgroup.zpowers (F.a i) ≤ (F.ρ j).K := Subgroup.zpowers_le.mpr hai
    have hP : IsPGroup 2 (Subgroup.zpowers (F.a i)) :=
      (F.ρ i).hRK.2.1.to_le (Subgroup.zpowers_le.mpr (F.ha i).1.1)
    have hcard := Sec6Gen.card_le_two_of_le_inf c.hΩ (F.ρ i).hK (F.ρ j).hK
      (F.hne i j hij) hP hle1 hle2
    rw [Nat.card_zpowers, (F.ha i).2] at hcard
    omega
  exact ⟨key 1 (Or.inl rfl), key z (Or.inr rfl)⟩

theorem u'_ne_u : F.a 2 * F.a 3 ≠ F.a 0 * F.a 1 := fun h => by
  have : F.t' = 1 := by
    rw [F.hrel]
    calc F.a 0 * F.a 1 * F.a 2 * F.a 3 = (F.a 0 * F.a 1) * (F.a 2 * F.a 3) := by group
      _ = (F.a 0 * F.a 1) * (F.a 0 * F.a 1) := by rw [h]
      _ = 1 := F.a_mul_sq c hc 0 1
  exact F.t'_ne_one this

theorem u'_ne_zu : F.a 2 * F.a 3 ≠ z * (F.a 0 * F.a 1) := fun h => by
  apply F.t'_ne_z
  rw [F.hrel]
  have hzu : z * (F.a 0 * F.a 1) = (F.a 0 * F.a 1) * z :=
    hc z (F.z_mem_W c) _ (F.a_mul_mem_W c hc 0 1)
  calc F.a 0 * F.a 1 * F.a 2 * F.a 3 = (F.a 0 * F.a 1) * (F.a 2 * F.a 3) := by group
    _ = (F.a 0 * F.a 1) * (z * (F.a 0 * F.a 1)) := by rw [h]
    _ = (F.a 0 * F.a 1) * ((F.a 0 * F.a 1) * z) := by rw [hzu]
    _ = z := by
        rw [← mul_assoc, F.a_mul_sq c hc 0 1, one_mul]

theorem u_mul_u' : (F.a 0 * F.a 1) * (F.a 2 * F.a 3) = F.t' := by
  rw [F.hrel]; group

theorem B_elemAbelian : IsElemAbelian 2 F.B ∧ Nat.card F.B = 8 := by
  have hcomm : ∀ a ∈ ({z, F.a 0 * F.a 1, F.a 2 * F.a 3} : Set Y),
      ∀ b ∈ ({z, F.a 0 * F.a 1, F.a 2 * F.a 3} : Set Y), a * b = b * a := by
    have hW : ∀ a ∈ ({z, F.a 0 * F.a 1, F.a 2 * F.a 3} : Set Y), a ∈ W := by
      intro a ha
      rcases ha with rfl | rfl | rfl
      · exact F.z_mem_W c
      · exact F.a_mul_mem_W c hc 0 1
      · exact F.a_mul_mem_W c hc 2 3
    intro a ha b hb
    exact hc a (hW a ha) b (hW b hb)
  have hsq : ∀ a ∈ ({z, F.a 0 * F.a 1, F.a 2 * F.a 3} : Set Y), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact F.z_sq
    · exact F.a_mul_sq c hc 0 1
    · exact F.a_mul_sq c hc 2 3
  have hcl := ChainFrame.commutes_closure hcomm
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcl _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rw [pow_two]
    exact ChainFrame.sq_closure hsq hcomm x hx
  · obtain ⟨h01, h01z⟩ := F.a_mul_ne c hc (show (0 : Fin 4) ≠ 1 by decide)
    obtain ⟨h23, h23z⟩ := F.a_mul_ne c hc (show (2 : Fin 4) ≠ 3 by decide)
    exact ChainFrame.card_closure_triple_eq_eight (hsq z (by simp)) (hsq _ (by simp))
      (hsq _ (by simp)) (hcomm z (by simp) _ (by simp)) (hcomm z (by simp) _ (by simp))
      (hcomm _ (by simp) _ (by simp)) F.z_ne_one h01 h01z h23 h23z (F.u'_ne_u c hc)
      (F.u'_ne_zu c hc)

end BGroup

section Hyp


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}
  (h : PerpHypR r n Y R S t) (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
  (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

include h F c hc

theorem mem_twinSet (i : Fin 4) :
    (F.ρ i).K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
  ⟨(F.ρ i).hK, t, Inner.isUniqueInvolution_core h.core.datum, F.hz i⟩

theorem tq_prod {i j k : Fin 4} (hik : i ≠ k) (hjk : j ≠ k) :
    F.a i * F.a j ∈ Balance.Bootstrap.trivialOnQuot (F.ρ k).K :=
  (Balance.Bootstrap.trivialOnQuot (F.ρ k).K).mul_mem
    (A7T22.le_trivialOnQuot_of_twin h.core.hyp (F.ρ i).hK (F.ρ k).hK (F.hne i k hik) (F.hz i)
      (F.hz k) (F.a_mem_K i))
    (A7T22.le_trivialOnQuot_of_twin h.core.hyp (F.ρ j).hK (F.ρ k).hK (F.hne j k hjk) (F.hz j)
      (F.hz k) (F.a_mem_K j))

theorem tq_z (k : Fin 4) : t ∈ Balance.Bootstrap.trivialOnQuot (F.ρ k).K :=
  ExactLayer.mem_trivialOnQuot_of_le_centralizer (isUniqueInvolution_le_centralizer (F.hz k))

theorem z_mem_B : t ∈ F.B := Subgroup.subset_closure (by simp)

theorem u_mem_B : F.a 0 * F.a 1 ∈ F.B := Subgroup.subset_closure (by simp)

theorem u'_mem_B : F.a 2 * F.a 3 ∈ F.B := Subgroup.subset_closure (by simp)

theorem t'_mem_B : F.t' ∈ F.B := by
  rw [← F.u_mul_u' c hc]
  exact F.B.mul_mem (F.u_mem_B h c hc) (F.u'_mem_B h c hc)

theorem mul_sq_of_mem_W {x y : Y} (hx : x ∈ W) (hy : y ∈ W) (hx2 : x * x = 1) (hy2 : y * y = 1) :
    (x * y) * (x * y) = 1 := by
  have hxy : y * x = x * y := hc y hy x hx
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx2, hy2, one_mul]

theorem hyp51At_twin (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) {cc : Y}
    (hcB : cc ∈ F.B) (hc2 : cc * cc = 1) (hc1 : cc ≠ 1) (hct : t ≠ cc)
    (htc : t ∈ Subgroup.centralizer ({cc} : Set Y)) {i j : Fin 4} (hij : i ≠ j)
    (hci : cc ∈ Balance.Bootstrap.trivialOnQuot (F.ρ i).K)
    (hcj : cc ∈ Balance.Bootstrap.trivialOnQuot (F.ρ j).K) : Hyp51At F.B cc :=
  Perp22.hyp51At_of_twinPair h4 hT h (F.B_elemAbelian c hc).1 hcB (F.z_mem_B h c hc) hc2 hc1 hct htc
    (F.mem_twinSet h c hc i) (F.mem_twinSet h c hc j) (F.hne j i (Ne.symm hij)) hci hcj

theorem z_mul_ne_one {u : Y} (hu : u ≠ t) : t * u ≠ 1 := fun h' => by
  have h1 : u = t⁻¹ := eq_inv_of_mul_eq_one_right h'
  exact hu (h1.trans (inv_eq_of_mul_eq_one_right F.z_sq))

theorem z_ne_z_mul {u : Y} (hu : u ≠ 1) : t ≠ t * u := fun h' => by
  have : t * u = t * 1 := by rw [mul_one]; exact h'.symm
  exact hu (mul_left_cancel this)

theorem z_mem_cent_z_mul {u : Y} (hu : u ∈ W) : t ∈ Subgroup.centralizer ({t * u} : Set Y) := by
  have hzu : t * u = u * t := hc t (F.z_mem_W c) u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc t * (t * u) = t * (u * t) := by rw [hzu]
    _ = (t * u) * t := by group

theorem hyp51At_z : Hyp51At F.B t :=
  Perp24.hyp51At_of_commute (F.B_elemAbelian c hc).1 (F.z_mem_B h c hc) F.z_ne_one
    (F.t'_mem_B h c hc) F.t'_ne_one F.t'_ne_z (t'_mem_centralizer F c hc)
    (fun L hL y hy => Perp24.commute_of_tightInO2 (tightInO2_t' h F c hc) hL y hy)

theorem hyp51At_t' : Hyp51At F.B F.t' := by
  obtain ⟨h1, h2, -, -⟩ := F.swap_k c hc 0
  have hzt'C : t ∈ Subgroup.centralizer ({F.t'} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (F.zt' c hc)
  have hin := Perp23.Three.tightInO2_conj' ((F.ρ 0).r * F.σ.r * (F.ρ 0).r⁻¹) t F.t' F.t' t h1 h2
    (t'_mem_centralizer F c hc) hzt'C (tightInO2_t' h F c hc)
  exact Perp24.hyp51At_of_commute (F.B_elemAbelian c hc).1 (F.t'_mem_B h c hc) F.t'_ne_one
    (F.z_mem_B h c hc) F.z_ne_one F.t'_ne_z.symm hzt'C
    (fun L hL y hy => Perp24.commute_of_tightInO2 hin hL y hy)

theorem hyp51At_zt' : Hyp51At F.B (t * F.t') := by
  obtain ⟨-, -, h3, h4⟩ := F.swap_k c hc 0
  have hzC : t ∈ Subgroup.centralizer ({t * F.t'} : Set Y) :=
    F.z_mem_cent_z_mul h c hc (F.t'_mem_W c)
  have hin := Perp23.Three.tightInO2_conj'
    ((F.ρ 0).r * ((F.ρ 0).r * F.σ.r * (F.ρ 0).r⁻¹)) t (t * F.t') F.t' t h3 h4
    (t'_mem_centralizer F c hc) hzC (tightInO2_t' h F c hc)
  exact Perp24.hyp51At_of_commute (F.B_elemAbelian c hc).1
    (F.B.mul_mem (F.z_mem_B h c hc) (F.t'_mem_B h c hc)) (F.z_mul_ne_one h c hc F.t'_ne_z)
    (F.z_mem_B h c hc) F.z_ne_one (F.z_ne_z_mul h c hc F.t'_ne_one) hzC
    (fun L hL y hy => Perp24.commute_of_tightInO2 hin hL y hy)

theorem hyp51_B (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) : Hyp51 F.B := by
  obtain ⟨hEl, hcard⟩ := F.B_elemAbelian c hc
  obtain ⟨h01, h01z⟩ := F.a_mul_ne c hc (show (0 : Fin 4) ≠ 1 by decide)
  obtain ⟨h23, h23z⟩ := F.a_mul_ne c hc (show (2 : Fin 4) ≠ 3 by decide)
  have hsq01 := F.a_mul_sq c hc 0 1
  have hsq23 := F.a_mul_sq c hc 2 3
  have hu : F.a 0 * F.a 1 ∈ W := F.a_mul_mem_W c hc 0 1
  have hu' : F.a 2 * F.a 3 ∈ W := F.a_mul_mem_W c hc 2 3
  have hzW : t ∈ W := F.z_mem_W c
  have hsqz : (t * (F.a 0 * F.a 1)) * (t * (F.a 0 * F.a 1)) = 1 :=
    mul_sq_of_mem_W h F c hc hzW hu F.z_sq hsq01
  have hsqz' : (t * (F.a 2 * F.a 3)) * (t * (F.a 2 * F.a 3)) = 1 :=
    mul_sq_of_mem_W h F c hc hzW hu' F.z_sq hsq23
  refine ⟨hEl, hcard, fun x hx hx1 => ?_⟩
  rcases ChainFrame.mem_closure_eight F.z_sq hsq01 hsq23 (hc _ hzW _ hu) (hc _ hzW _ hu')
      (hc _ hu _ hu') hx with h' | h' | h' | h' | h' | h' | h' | h'
  · exact absurd h' hx1
  · rw [h']; exact F.hyp51At_z h c hc
  · rw [h']
    exact F.hyp51At_twin h c hc h4 hT (F.u_mem_B h c hc) hsq01 h01 h01z.symm
      (Subgroup.mem_centralizer_singleton_iff.mpr (hc _ hzW _ hu)) (show (2 : Fin 4) ≠ 3 by decide)
      (F.tq_prod h c hc (by decide) (by decide)) (F.tq_prod h c hc (by decide) (by decide))
  · rw [h']
    exact F.hyp51At_twin h c hc h4 hT (F.u'_mem_B h c hc) hsq23 h23 h23z.symm
      (Subgroup.mem_centralizer_singleton_iff.mpr (hc _ hzW _ hu')) (show (0 : Fin 4) ≠ 1 by decide)
      (F.tq_prod h c hc (by decide) (by decide)) (F.tq_prod h c hc (by decide) (by decide))
  · rw [h']
    exact F.hyp51At_twin h c hc h4 hT (F.B.mul_mem (F.z_mem_B h c hc) (F.u_mem_B h c hc)) hsqz
      (F.z_mul_ne_one h c hc h01z) (F.z_ne_z_mul h c hc h01) (F.z_mem_cent_z_mul h c hc hu)
      (show (2 : Fin 4) ≠ 3 by decide)
      ((Balance.Bootstrap.trivialOnQuot _).mul_mem (F.tq_z h c hc 2)
        (F.tq_prod h c hc (by decide) (by decide)))
      ((Balance.Bootstrap.trivialOnQuot _).mul_mem (F.tq_z h c hc 3)
        (F.tq_prod h c hc (by decide) (by decide)))
  · rw [h']
    exact F.hyp51At_twin h c hc h4 hT (F.B.mul_mem (F.z_mem_B h c hc) (F.u'_mem_B h c hc)) hsqz'
      (F.z_mul_ne_one h c hc h23z) (F.z_ne_z_mul h c hc h23) (F.z_mem_cent_z_mul h c hc hu')
      (show (0 : Fin 4) ≠ 1 by decide)
      ((Balance.Bootstrap.trivialOnQuot _).mul_mem (F.tq_z h c hc 0)
        (F.tq_prod h c hc (by decide) (by decide)))
      ((Balance.Bootstrap.trivialOnQuot _).mul_mem (F.tq_z h c hc 1)
        (F.tq_prod h c hc (by decide) (by decide)))
  · rw [h', F.u_mul_u' c hc]; exact F.hyp51At_t' h c hc
  · rw [h', F.u_mul_u' c hc]; exact F.hyp51At_zt' h c hc

end Hyp

end WylFrame

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
