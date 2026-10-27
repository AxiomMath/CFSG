module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Family
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Struct

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

theorem i112_commFam (hL : IsComponentOf L ⊤) : CommFam (i112Fam B L) :=
  i112_pairwise_commute hL

theorem i112_centre_J_eq (hL : IsComponentOf L ⊤) :
    i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) =
      ⨆ M : ↥(i112Orbit B L), (M : Subgroup X) ⊓ Subgroup.centralizer (M : Set X) := by
  have := Fintype.ofFinite ↥(i112Orbit B L)
  have h := (i112_commFam (B := B) hL).centreIn_iSup_eq_iSup
  rw [i112_iSup_fam] at h
  exact h

theorem i112_centre_J_inf_eq (hL : IsComponentOf L ⊤) (M : ↥(i112Orbit B L)) :
    (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ (M : Subgroup X) =
      (M : Subgroup X) ⊓ Subgroup.centralizer (M : Set X) := by
  have h := (i112_commFam (B := B) hL).centreIn_iSup_inf_eq M
  rw [i112_iSup_fam] at h
  exact h

theorem i112_isElemAbelian_centre_J (hL : IsComponentOf L ⊤)
    (hexp : ∀ M ∈ i112Orbit B L, ∀ z ∈ M ⊓ Subgroup.centralizer (M : Set X), z ^ p = 1) :
    IsElemAbelian p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) := by
  have hcomm : ∀ a b : X, a ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) →
      b ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) → a * b = b * a :=
    fun a b ha hb => (Subgroup.mem_centralizer_iff.1 hb.2 a ha.1)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a b a.2 b.2)⟩⟩, fun x hx => ?_⟩
  have hx' := hx
  rw [i112_centre_J_eq hL] at hx'
  refine (Subgroup.iSup_induction
    (fun M : ↥(i112Orbit B L) => (M : Subgroup X) ⊓ Subgroup.centralizer (M : Set X)) hx'
    (C := fun x => x ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) ∧ x ^ p = 1)
    (fun M y hy => ⟨?_, hexp M M.2 y hy⟩) ⟨Subgroup.one_mem _, one_pow p⟩ ?_).2
  · have := (i112_centre_J_inf_eq hL M).symm ▸ hy
    exact (Subgroup.mem_inf.1 this).1
  · rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
    exact ⟨Subgroup.mul_mem _ ha hb, by rw [Commute.mul_pow (hcomm a b ha hb) p, hpa, hpb, one_mul]⟩

end

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
