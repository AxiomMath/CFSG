module

public import CFSG.ClassicalInvolution.Q3.TL4OddZTR

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Seven

variable {G : Type} [Group G]

theorem hyp51_of_seven {t u v : G} (ht : t * t = 1) (hu : u * u = 1) (hv : v * v = 1)
    (htu : t * u = u * t) (htv : t * v = v * t) (huv : u * v = v * u)
    (hE : IsElemAbelian 2 (Subgroup.closure ({t, u, v} : Set G)))
    (h8 : Nat.card ↥(Subgroup.closure ({t, u, v} : Set G)) = 8)
    (vt : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) t)
    (vu : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) u)
    (vv : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) v)
    (vuv : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) (u * v))
    (vtu : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) (t * u))
    (vtv : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) (t * v))
    (vtuv : Hyp51At (Subgroup.closure ({t, u, v} : Set G)) (t * (u * v))) :
    Hyp51 (Subgroup.closure ({t, u, v} : Set G)) := by
  refine ⟨hE, h8, fun c hc hc1 => ?_⟩
  rcases mem_closure_three_cases hv htv huv hc with h | ⟨e, he, rfl⟩
  · rcases T3CII.closure_pair_cases ht hu htu h with rfl | rfl | rfl | rfl
    · exact absurd rfl hc1
    · exact vt
    · exact vu
    · exact vtu
  · rcases T3CII.closure_pair_cases ht hu htu he with rfl | rfl | rfl | rfl
    · rwa [one_mul]
    · exact vtv
    · exact vuv
    · rwa [mul_assoc]

theorem closure_three_swap (t u v : G) :
    Subgroup.closure ({t, v, u} : Set G) = Subgroup.closure ({t, u, v} : Set G) := by
  rw [Set.pair_comm v u]

theorem closure_three_mul {t u v : G} (hu : u * u = 1) :
    Subgroup.closure ({t, u * v, u} : Set G) = Subgroup.closure ({t, u, v} : Set G) := by
  have ht₁ : t ∈ Subgroup.closure ({t, u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hu₁ : u ∈ Subgroup.closure ({t, u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hv₁ : v ∈ Subgroup.closure ({t, u, v} : Set G) := Subgroup.subset_closure (by simp)
  have ht₂ : t ∈ Subgroup.closure ({t, u * v, u} : Set G) := Subgroup.subset_closure (by simp)
  have huv₂ : u * v ∈ Subgroup.closure ({t, u * v, u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hu₂ : u ∈ Subgroup.closure ({t, u * v, u} : Set G) := Subgroup.subset_closure (by simp)
  have hv₂ : v ∈ Subgroup.closure ({t, u * v, u} : Set G) := by
    have h := Subgroup.mul_mem _ hu₂ huv₂
    rwa [← mul_assoc, hu, one_mul] at h
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact ht₁
    · exact Subgroup.mul_mem _ hu₁ hv₁
    · exact hu₁
  · rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact ht₂
    · exact hu₂
    · exact hv₂

end Seven

section Frames

variable {Y : Type} [Group Y]

structure Z2FrameAt (R : Subgroup Y) (t : Y) (J J₂ J₃ : Subgroup Y) (u v : Y) : Prop where
  memJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  memJ₂ : J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  memJ₃ : J₃ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  invJ : IsUniqueInvolution J u
  invJ₂ : IsUniqueInvolution J₂ v
  invJ₃ : IsUniqueInvolution J₃ (u * v)
  comm : u * v = v * u
  ne : v ≠ u
  ne_mul : v ≠ t * u

namespace Z2FrameAt

variable {R : Subgroup Y} {t : Y} {J J₂ J₃ : Subgroup Y} {u v : Y}

theorem ne_mul_self (hF : Z2FrameAt R t J J₂ J₃ u v) : u ≠ u * v := by
  intro e
  apply hF.invJ₂.ne_one
  have e' : u * 1 = u * v := by rw [mul_one]; exact e
  exact (mul_left_cancel e').symm

theorem swap (hF : Z2FrameAt R t J J₂ J₃ u v) (hne : u ≠ t * v) :
    Z2FrameAt R t J₂ J J₃ v u where
  memJ := hF.memJ₂
  memJ₂ := hF.memJ
  memJ₃ := hF.memJ₃
  invJ := hF.invJ₂
  invJ₂ := hF.invJ
  invJ₃ := by rw [← hF.comm]; exact hF.invJ₃
  comm := hF.comm.symm
  ne := hF.ne.symm
  ne_mul := hne

theorem rot (hF : Z2FrameAt R t J J₂ J₃ u v) (hu : u * u = 1) (hne1 : u ≠ u * v)
    (hne2 : u ≠ t * (u * v)) : Z2FrameAt R t J₃ J J₂ (u * v) u where
  memJ := hF.memJ₃
  memJ₂ := hF.memJ
  memJ₃ := hF.memJ₂
  invJ := hF.invJ₃
  invJ₂ := hF.invJ
  invJ₃ := by
    have e : u * v * u = v := by rw [hF.comm, mul_assoc, hu, mul_one]
    rw [e]
    exact hF.invJ₂
  comm := by rw [mul_assoc, ← hF.comm]
  ne := hne1
  ne_mul := hne2

end Z2FrameAt

end Frames

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J J₂ J₃ : Subgroup Y} {u v : Y}

namespace Z2FrameAt

theorem comm_tu (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen hL.datum.isUniqueInvolution_core hF.memJ
    hF.invJ

theorem comm_tv (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    t * v = v * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen hL.datum.isUniqueInvolution_core hF.memJ₂
    hF.invJ₂

theorem ne_tu (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) : t ≠ u :=
  fun h => hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (h ▸ hF.invJ))

theorem ne_tv (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) : t ≠ v :=
  fun h => hF.memJ₂.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ₂.1 (h ▸ hF.invJ₂))

theorem not_mem_closure (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    v ∉ Subgroup.closure ({t, u} : Set Y) := by
  have ht := hL.datum.isUniqueInvolution_core
  intro hmem
  rcases T3CII.closure_pair_cases ht.sq hF.invJ.sq (hF.comm_tu hL) hmem with h | h | h | h
  · exact hF.invJ₂.ne_one h
  · exact hF.ne_tv hL h.symm
  · exact hF.ne h
  · exact hF.ne_mul h

theorem isElemAbelian (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    IsElemAbelian 2 (Subgroup.closure ({t, u, v} : Set Y)) :=
  T8T.isElemAbelian_closure_three hL.datum.isUniqueInvolution_core.sq hF.invJ.sq hF.invJ₂.sq
    (hF.comm_tu hL) (hF.comm_tv hL) hF.comm

theorem natCard (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    Nat.card ↥(Subgroup.closure ({t, u, v} : Set Y)) = 8 := by
  have ht := hL.datum.isUniqueInvolution_core
  exact T8T.natCard_closure_three ht.sq hF.invJ.sq hF.invJ₂.sq (hF.comm_tu hL) (hF.comm_tv hL)
    hF.comm ht.ne_one hF.invJ.ne_one (hF.ne_tu hL) hF.invJ₂.ne_one (hF.not_mem_closure hL)

theorem ne_mul' (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    u ≠ t * v := by
  intro e
  apply hF.ne_mul
  rw [e, ← mul_assoc, hL.datum.isUniqueInvolution_core.sq, one_mul]

theorem ne_mul_mul (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    u ≠ t * (u * v) := by
  intro e
  apply hF.ne_tv hL
  have ht := hL.datum.isUniqueInvolution_core
  have e1 : u = u * (t * v) := by
    rw [← mul_assoc, ← hF.comm_tu hL, mul_assoc]
    exact e
  have e2 : u * 1 = u * (t * v) := by rw [mul_one]; exact e1
  have e3 : 1 = t * v := mul_left_cancel e2
  calc t = t * 1 := (mul_one t).symm
    _ = t * (t * v) := by rw [← e3]
    _ = v := by rw [← mul_assoc, ht.sq, one_mul]

end Z2FrameAt

end Cit3

section Cit3b


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J J₂ J₃ : Subgroup Y} {u v : Y}

namespace Z2FrameAt

theorem hyp51At_mul (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t)
    (hF : Z2FrameAt R t J J₂ J₃ u v) :
    Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) (t * u) ∧
      Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) (t * v) ∧
        Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) (t * (u * v)) := by
  have hE := hF.isElemAbelian hL
  have htB : t ∈ Subgroup.closure ({t, u, v} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({t, u, v} : Set Y) := Subgroup.subset_closure (by simp)
  have hvB : v ∈ Subgroup.closure ({t, u, v} : Set Y) := Subgroup.subset_closure (by simp)
  exact ⟨hyp51At_mul_of_edge h4 htw hOm hL hF.memJ hF.invJ hE htB huB,
    hyp51At_mul_of_edge h4 htw hOm hL hF.memJ₂ hF.invJ₂ hE htB hvB,
    hyp51At_mul_of_edge h4 htw hOm hL hF.memJ₃ hF.invJ₃ hE htB (Subgroup.mul_mem _ huB hvB)⟩

theorem hyp51 (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t)
    (hF : Z2FrameAt R t J J₂ J₃ u v)
    (vt : ∀ (J J₂ J₃ : Subgroup Y) (u v : Y), Z2FrameAt R t J J₂ J₃ u v →
      Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) t)
    (vu : ∀ (J J₂ J₃ : Subgroup Y) (u v : Y), Z2FrameAt R t J J₂ J₃ u v →
      Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) u) :
    Hyp51 (Subgroup.closure ({t, u, v} : Set Y)) := by
  have ht := hL.datum.isUniqueInvolution_core
  obtain ⟨vtu, vtv, vtuv⟩ := hF.hyp51At_mul h4 htw hOm hL
  have hv' := vu _ _ _ _ _ (hF.swap (hF.ne_mul' hL))
  rw [closure_three_swap] at hv'
  have huv' := vu _ _ _ _ _ (hF.rot hF.invJ.sq hF.ne_mul_self (hF.ne_mul_mul hL))
  rw [closure_three_mul hF.invJ.sq] at huv'
  exact hyp51_of_seven ht.sq hF.invJ.sq hF.invJ₂.sq (hF.comm_tu hL) (hF.comm_tv hL) hF.comm
    (hF.isElemAbelian hL) (hF.natCard hL) (vt _ _ _ _ _ hF) (vu _ _ _ _ _ hF) hv' huv' vtu vtv
    vtuv

end Z2FrameAt

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4
