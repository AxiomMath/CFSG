module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusSetup5
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

variable {V : Type} [CommGroup V]

theorem PlusCoord.plusSide {Y G : Subgroup (MulAut V)} {n : ℕ} (c : PlusCoord Y n) (hn : 2 ≤ n)
    (hYG : Y ≤ G) : PlusSide G Y c.fac₁ c.fac₂ n where
  hn := hn
  yg := hYG
  dy := c.fac₁_le
  by_ := c.fac₂_le
  sup := c.fac₁_sup_fac₂
  inf := c.fac₁_inf_fac₂
  comm := c.fac_comm
  dsl := ⟨c.fac₁Equiv⟩
  bsl := ⟨c.swap.fac₁Equiv⟩
  vsup := c.sup
  vinf := c.inf
  cD := c.commV_fac₁
  fD := c.fixV_fac₁
  cdec := fun _ hx => c.exists_decomp_centralizer hYG hx
  ctriv := fun _ hz ⟨_, hk⟩ => c.trivial_on_commV (Subgroup.mem_inf.mp hz).2 hk
  faith := fun _ hy h => c.eq_one_of_forall_commV hy h
  rootfix := fun _ hb hb2 hb1 _ hβ hcomm _ hv => by
    obtain ⟨B, rfl, hN, hN0⟩ := c.exists_of_involution hb hb2 hb1
    obtain ⟨B', rfl⟩ := hβ
    exact c.rootfix_of hN hN0 hcomm hv
  fixb := fun _ hb hb2 hb1 => by
    obtain ⟨B, rfl, hN, hN0⟩ := c.exists_of_involution hb hb2 hb1
    exact ⟨c.fixV_zpowers_eq hN hN0 hb2, c.commV_zpowers_inf, c.commV_zpowers_le⟩
  natE := fun _ hb hb2 hb1 => by
    obtain ⟨B, rfl, hN, hN0⟩ := c.exists_of_involution hb hb2 hb1
    exact c.natE_of hN hN0 hb2

theorem exists_plusSide [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G Y : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (hYG : Y ≤ G) (hΩ : IsNatSectionBy (omegaPlusAct n) Y (commV Y) ⊥) :
    ∃ D B : Subgroup (MulAut V), PlusSide G Y D B n ∧ PlusSide G Y B D n := by
  obtain ⟨C, hCfix, hCinf, hCsup⟩ := exists_complement_of_plusSection hV hn hΩ
  obtain ⟨hinv, θ, φ, hφ⟩ := TwoEight.natSection_equiv hΩ
  have hW : fixV Y = C := fixV_eq_of_complement θ φ hφ hCfix hCsup
  let c : PlusCoord Y n :=
    { θ := θ
      φ := φ
      mapsTo := hinv
      act := hφ
      sup := by rw [hW]; exact hCsup
      inf := by rw [hW]; exact hCinf }
  exact ⟨c.fac₁, c.fac₂, c.plusSide hn hYG, c.swap.plusSide hn hYG⟩

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
