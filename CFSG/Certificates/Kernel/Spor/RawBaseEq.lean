module

public import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.PackFld
import all CFSG.Certificates.Kernel.U6Sec3.ProdAll
import all CFSG.Certificates.Kernel.J2Enum.Group

public section

namespace CFSG.KS.Raw.BaseEq

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Certificates CFSG.Certificates.ChainArrays
open CFSG.KC.J2Enum.GrpPf

theorem groupN {n w kS kO nb BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {D : List (List ℤ)}
    {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    (∀ γ ∈ Raw.Orb.Gen n S kO,
      (∀ t < nb, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1) ∧
    (∀ X, canonK n w (mask w) (n * w) X = true →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 X = true →
        ∃ γ ∈ Raw.Orb.Gen n S kO, Raw.Orb.PRep n w X γ) ∧
    ∀ t < nb, pg w (mask w) BP t < n := by
  have hp := (Raw.Orb.head_facts hh).1
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbt : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hraw := Raw.Orb.rawChainOK_of_K (chunks := 1) hb hh hl hNS hs
  have hF := chainCheckFacts hraw
  obtain ⟨hk, hH⟩ := Raw.Orb.rawHeadOK_of hb hh
  have hd := Raw.Orb.hd_of_head hk hH
  have hGH : Raw.Orb.Gen n S kO = CFSG.KC.U6Sec3.ProdPf.H n S base 0 := by
    apply le_antisymm
    · rw [Raw.Orb.Gen, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨j.val, by have := j.2; omega, fixesFirst_zero _ _, rfl⟩
    · rw [CFSG.KC.U6Sec3.ProdPf.H, Subgroup.closure_le]
      rintro _ ⟨j, hj, -, rfl⟩
      exact Raw.Orb.S_mem_Gen hd j hj
  refine ⟨fun γ hγ hfix => ?_, fun X hX h => ?_, fun t ht => hbt t ht ▸ hbl t ht⟩
  · rw [hGH] at hγ
    have ha : Rep n (Array.ofFn (n := n) fun i => (γ i : ℕ)) γ := fun z =>
      getElem!_ofFn_nat _ z.2
    have hsA := CFSG.KC.U6Sec3.ProdPf.sift_complete hF base.size 0 (by simp) _ _ ha hγ
    have key : ∀ (x : ℕ) (h1 : x < n) (y : ℕ) (h2 : y < n), x = y →
        (γ ⟨y, h2⟩ = ⟨y, h2⟩ → γ ⟨x, h1⟩ = ⟨x, h1⟩) := by
      rintro x h1 y h2 rfl
      exact id
    refine eq_one_of_siftA hF base.size 0 (by simp) _ _ ha hsA fun t _ ht hb' => ?_
    rw [hbs] at ht
    exact key _ hb' _ (hbt t ht ▸ hb') (hbt t ht) (hfix t ht _)
  · obtain ⟨-, -, hX0, hXr⟩ := PF.canon_facts hX
    have hr : allN n (fun i => Nat.blt (pg w (mask w) X i) n) = true :=
      PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (hXr i hi)
    have hsA := siftK_sound hb hp hl rfl hr h
    obtain ⟨γ, hγ⟩ := rep_of_siftA hF base.size 0 (by simp) _
      (fun i hi => by rw [Raw.Orb.unpack_get hi]; exact hXr i hi) hsA
    refine ⟨γ, ?_, fun z => by rw [← Raw.Orb.unpack_get z.2]; exact hγ z⟩
    rw [hGH]
    exact CFSG.KC.U6Sec3.ProdPf.mem_of_sift hF (Nat.zero_le _) hγ hsA

theorem eq_of_baseN {n w kS kO nb BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {D : List (List ℤ)}
    {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    {g h : Equiv.Perm (Fin n)} (hg : g ∈ Raw.Orb.Gen n S kO) (hh' : h ∈ Raw.Orb.Gen n S kO)
    (e : ∀ t < nb, ∀ hb : pg w (mask w) BP t < n, g ⟨_, hb⟩ = h ⟨_, hb⟩) : g = h := by
  have h1 := (groupN hb hh hl hNS hs).1 (h⁻¹ * g)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh') hg) fun t ht hb' => by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact e t ht hb'
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end CFSG.KS.Raw.BaseEq

end
