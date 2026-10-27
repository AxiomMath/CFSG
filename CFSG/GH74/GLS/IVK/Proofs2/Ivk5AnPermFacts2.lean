module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnHeis
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

section Model

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10)

include h7 h10

theorem rbar_add (a b : F4c) : rbar m (a + b) = rbar m a * rbar m b := by
  revert a b
  interval_cases m <;> decide

theorem sbar_add (a b : F4c) : sbar m (a + b) = sbar m a * sbar m b := by
  revert a b
  interval_cases m <;> decide

theorem wbar_add (a b : F4c) : wbar m (a + b) = wbar m a * wbar m b := by
  revert a b
  interval_cases m <;> decide

theorem wbar_rbar (c a : F4c) : wbar m c * rbar m a = rbar m a * wbar m c := by
  revert c a
  interval_cases m <;> decide

theorem wbar_sbar (c b : F4c) : wbar m c * sbar m b = sbar m b * wbar m c := by
  revert c b
  interval_cases m <;> decide

theorem rbar_sbar (a b : F4c) : rbar m a * sbar m b = wbar m (a * b) * (sbar m b * rbar m a) := by
  revert a b
  interval_cases m <;> decide

@[expose] def permHeis : HeisData (Perm (Fin (m + 1))) where
  r := rbar m
  s := sbar m
  w := wbar m
  r_add := rbar_add m h7 h10
  s_add := sbar_add m h7 h10
  w_add := wbar_add m h7 h10
  wr := wbar_rbar m h7 h10
  ws := wbar_sbar m h7 h10
  comm := rbar_sbar m h7 h10

@[expose] def Sh : UT3 F4c →* Perm (Fin (m + 1)) := (permHeis m h7 h10).hom

theorem Sfun_ker (x : UT3 F4c) : Sfun m x = 1 → x = 1 ∨ x = ⟨0, 0, omegaC⟩ := by
  revert x
  interval_cases m <;> decide +kernel

theorem Sfun_conj_c3 (x : UT3 F4c) : ∃ y, c3 m * Sfun m x * (c3 m)⁻¹ = Sfun m y := by
  revert x
  interval_cases m <;> decide +kernel

theorem Sfun_cent_c3 (x : UT3 F4c) :
    c3 m * Sfun m x = Sfun m x * c3 m → Sfun m x = 1 ∨ Sfun m x = tb m := by
  revert x
  interval_cases m <;> decide +kernel

theorem Sfun_conj_vp (h9 : 9 ≤ m) (x : UT3 F4c) : ∃ y, vp m * Sfun m x * (vp m)⁻¹ = Sfun m y := by
  revert x
  interval_cases m <;> first | omega | decide +kernel

theorem ub_xb2_mem_range : ∃ x, Sfun m x = ub m * xb2 m := by
  interval_cases m <;> decide +kernel

theorem Sh_comm_gen : ub m ∈ Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) ∧
    vb m ∈ Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) ∧
    xb1 m ∈ Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) ∧
    xb2 m ∈ Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) ∧
    tb m ∈ Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) := by
  have hmem : ∀ x : UT3 F4c, ⁅Sh m h7 h10 x, c3 m⁆ ∈
      Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) :=
    fun x => Subgroup.subset_closure ⟨x, rfl⟩
  let xa : UT3 F4c := ⟨0, ⟨0, 1⟩, 0⟩
  let xb : UT3 F4c := ⟨⟨0, 1⟩, ⟨0, 1⟩, 0⟩
  let xc : UT3 F4c := ⟨0, ⟨1, 0⟩, 0⟩
  let xd : UT3 F4c := ⟨⟨1, 1⟩, ⟨1, 0⟩, 0⟩
  let xe : UT3 F4c := ⟨0, ⟨1, 1⟩, 0⟩
  have e1 : ⁅Sh m h7 h10 xa, c3 m⁆ * ⁅Sh m h7 h10 xb, c3 m⁆ = ub m := by
    show ⁅Sfun m xa, c3 m⁆ * ⁅Sfun m xb, c3 m⁆ = ub m
    interval_cases m <;> decide +kernel
  have e2 : ⁅Sh m h7 h10 xc, c3 m⁆ * ⁅Sh m h7 h10 xd, c3 m⁆ = vb m := by
    show ⁅Sfun m xc, c3 m⁆ * ⁅Sfun m xd, c3 m⁆ = vb m
    interval_cases m <;> decide +kernel
  have e3 : ⁅Sh m h7 h10 xe, c3 m⁆ = xb1 m := by
    show ⁅Sfun m xe, c3 m⁆ = xb1 m
    interval_cases m <;> decide +kernel
  have e4 : ⁅Sh m h7 h10 xc, c3 m⁆ = xb2 m := by
    show ⁅Sfun m xc, c3 m⁆ = xb2 m
    interval_cases m <;> decide +kernel
  have e5 : ⁅Sh m h7 h10 xb, c3 m⁆ * ⁅Sh m h7 h10 xb, c3 m⁆ = tb m := by
    show ⁅Sfun m xb, c3 m⁆ * ⁅Sfun m xb, c3 m⁆ = tb m
    interval_cases m <;> decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← e1]; exact Subgroup.mul_mem _ (hmem _) (hmem _)
  · rw [← e2]; exact Subgroup.mul_mem _ (hmem _) (hmem _)
  · rw [← e3]; exact hmem _
  · rw [← e4]; exact hmem _
  · rw [← e5]; exact Subgroup.mul_mem _ (hmem _) (hmem _)

theorem fix_gens (i : Fin (m + 1)) (hi : 8 ≤ i.val) :
    ub m i = i ∧ vb m i = i ∧ xb1 m i = i ∧ xb2 m i = i ∧ tb m i = i ∧ c3 m i = i := by
  revert i
  interval_cases m <;> decide +kernel

theorem fix_of_mem_closure (i : Fin (m + 1)) (hi : 8 ≤ i.val) :
    ∀ g ∈ Subgroup.closure ({ub m, vb m, xb1 m, xb2 m, tb m, c3 m} : Set (Perm (Fin (m + 1)))), g i = i := by
  intro g hg
  have hf := fix_gens m h7 h10 i hi
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hf.1
    · exact hf.2.1
    · exact hf.2.2.1
    · exact hf.2.2.2.1
    · exact hf.2.2.2.2.1
    · exact hf.2.2.2.2.2
  | one => rfl
  | mul x y _ _ hx hy => simp [Perm.mul_apply, hy, hx]
  | inv x _ hx =>
    have : x⁻¹ i = i := by
      rw [Perm.inv_eq_iff_eq]
      exact hx.symm
    exact this

theorem vp_moves (h9 : 9 ≤ m) : vp m (Fin.ofNat (m + 1) 8) ≠ Fin.ofNat (m + 1) 8 := by
  interval_cases m <;> first | omega | decide

theorem o3_moves (hm : m = 10) : o3 m (Fin.ofNat (m + 1) 8) ≠ Fin.ofNat (m + 1) 8 := by
  subst hm
  decide

end Model

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
