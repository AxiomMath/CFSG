module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Nrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128SplC

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_alt1 {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    {Y Xt Z : Subgroup (MulAut ↥V)} {τ : MulAut ↥V} (hZY : Z ≤ Y) (hXZ : Xt ≤ Z) (hτY : τ ∈ Y)
    (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) (hA5 : Nonempty (↥Xt ≃* ↥(alternatingGroup (Fin 5))))
    (hcomm : ∀ x ∈ Xt, τ * x = x * τ) (hfix : ∀ u : ↥V, (∀ x ∈ Xt, x u = u) → u = 1)
    (hZn : (Z.subgroupOf Y).Normal)
    (hZc : ∀ z ∈ Z, ∀ o ∈ oddCore ↥Y, z * (o : MulAut ↥V) = (o : MulAut ↥V) * z)
    (hidx : (Z.subgroupOf Y ⊔ oddCore ↥Y).index = 2) (hS : Sec128SplitNat V Z) :
    Sec128WrNat V Y ∧ Sec128WrAct V Y := by
  obtain ⟨V1, V2, hsn⟩ := hS
  obtain ⟨φ1, φ2, ρ, hspl, hρ⟩ := sec128_splitNatOn_spl hV hsn
  have hρZ : ∀ p, ρ p ∈ Z := fun p => hρ ▸ ⟨p, rfl⟩
  have hO : oddCore ↥Y = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun o ho => ?_
    have h1 : (o : MulAut ↥V) = 1 :=
      hspl.cent_one fun p => (hZc (ρ p) (hρZ p) o ho).symm
    exact Subtype.ext h1
  have hidx' : (Z.subgroupOf Y).index = 2 := by
    rw [hO, sup_bot_eq] at hidx
    exact hidx
  have hρY : ρ.range ≤ Y := by
    rw [hρ]
    exact hZY
  have hidx2 : (ρ.range.subgroupOf Y).index = 2 := by
    rw [hρ]
    exact hidx'
  have hZn' : ∀ p, ∃ p', τ * ρ p * τ⁻¹ = ρ p' := by
    intro p
    have hmem : (⟨τ, hτY⟩ : ↥Y) * ⟨ρ p, hZY (hρZ p)⟩ * (⟨τ, hτY⟩ : ↥Y)⁻¹ ∈ Z.subgroupOf Y :=
      hZn.conj_mem _ (Subgroup.mem_subgroupOf.mpr (hρZ p)) _
    have hmem' : τ * ρ p * τ⁻¹ ∈ Z := Subgroup.mem_subgroupOf.mp hmem
    rw [← hρ] at hmem'
    obtain ⟨p', hp'⟩ := hmem'
    exact ⟨p', hp'.symm⟩
  have hXt : ∀ x ∈ Xt, ∃ p, ρ p = x := fun x hx => by
    have : x ∈ ρ.range := by
      rw [hρ]
      exact hXZ hx
    exact this
  obtain ⟨hA, hB, hnz⟩ := hspl.swap hτ1 hZn' hXt hA5 hcomm hfix
  have ht : Sec128Tw ρ V1 V2 τ := ⟨hτ2, hA, hB, hnz, hspl.swap_sub hτ2 hA hB⟩
  refine ⟨⟨Z, V1, V2, τ, hZY, hidx', hsn, hτY, ?_, ht.sub⟩,
    sec128_wrAct_of hspl ht hτY hρY hidx2⟩
  intro hτZ
  rw [← hρ] at hτZ
  obtain ⟨p, hp⟩ := hτZ
  exact hnz p hp.symm

end CFSG.OddStandard.SmallF3.Omega
