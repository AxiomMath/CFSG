module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinSL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinSimul
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinConj
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinTors

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

theorem lin_exists_frame {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {Q : Type} [Group Q] (θ : Q ≃* LinPSL d F) {Bbar : Subgroup Q} (hB : IsElemAbelian p Bbar) :
    ∃ (ψ : Q ≃* LinPSL d F) (A : Subgroup (GL (Fin d) F)), LinDiagFrame p d F ψ Bbar A := by
  have hB' : IsElemAbelian p (Bbar.map θ.toMonoidHom) := lin_isElemAbelian_map _ hB
  obtain ⟨A₀, hA₀S, hA₀e, hA₀B⟩ := lin_lift_torsion h hB'
  obtain ⟨g, hg⟩ := lin_simul_diag h hA₀e
  obtain ⟨φ, hφ⟩ := lin_conj_psl (F := F) g
  have hconj : ∀ a : GL (Fin d) F, (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := fun a => rfl
  refine ⟨θ.trans φ, A₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hconj]
    exact lin_conj_mem_SL g (hA₀S ha)
  · exact lin_isElemAbelian_map _ hA₀e
  · rintro _ ⟨a, ha, rfl⟩ i j hij
    rw [hconj]
    exact hg a ha i j hij
  · ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : θ b ∈ Bbar.map θ.toMonoidHom := ⟨b, hb, rfl⟩
      rw [← hA₀B] at hb'
      obtain ⟨s, hs, hsb⟩ := hb'
      have hsS : (s : GL (Fin d) F) ∈ A₀ := hs
      refine ⟨⟨g * s * g⁻¹, lin_conj_mem_SL g s.2⟩, ?_, ?_⟩
      · show g * (s : GL (Fin d) F) * g⁻¹ ∈ A₀.map (MulAut.conj g).toMonoidHom
        exact ⟨s, hsS, rfl⟩
      · have h1 := hφ s ⟨g * s * g⁻¹, lin_conj_mem_SL g s.2⟩ rfl
        have h2 : θ b = LinMk d F s := hsb.symm
        show LinMk d F ⟨g * s * g⁻¹, _⟩ = φ (θ b)
        rw [h2]
        exact h1.symm
    · rintro ⟨s', hs', rfl⟩
      obtain ⟨a, ha, has⟩ := hs'
      have haS : a ∈ LinSL d F := hA₀S ha
      have hmem : LinMk d F ⟨a, haS⟩ ∈ (A₀.subgroupOf (LinSL d F)).map (LinMk d F) :=
        ⟨⟨a, haS⟩, ha, rfl⟩
      rw [hA₀B] at hmem
      obtain ⟨b, hb, hbs⟩ := hmem
      refine ⟨b, hb, ?_⟩
      have h1 := hφ ⟨a, haS⟩ s' (by rw [← hconj a]; exact has.symm)
      have h2 : θ b = LinMk d F ⟨a, haS⟩ := hbs
      show φ (θ b) = LinMk d F s'
      rw [h2]
      exact h1

theorem lin_frame_eq {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {Q : Type} [Group Q] {ψ : Q ≃* LinPSL d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : LinDiagFrame p d F ψ Bbar A)
    (hcard : p ^ (d - 1) ≤ Nat.card Bbar) :
    Bbar.map ψ.toMonoidHom = LinTorsionImage p d F := by
  obtain ⟨hD_SL, _hD_ea, hD_card, hD_scal⟩ :=
    lin_diagTorsion_data (p := p) (d := d) (F := F) h
  have hA_le_D : A ≤ LinDiagTorsion p d F := by
    intro a ha
    exact Subgroup.subset_closure ⟨hfr.1 ha, hfr.2.1.2 a ha, hfr.2.2.1 a ha⟩
  have hAD : A.subgroupOf (LinSL d F) ≤ (LinDiagTorsion p d F).subgroupOf (LinSL d F) :=
    fun _ hx => hA_le_D hx
  have hinj : Set.InjOn (LinMk d F)
      (((LinDiagTorsion p d F).subgroupOf (LinSL d F)) : Set (↥(LinSL d F))) := by
    intro x hx y hy hxy
    have hz : x * y⁻¹ ∈ (LinDiagTorsion p d F).subgroupOf (LinSL d F) :=
      Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)
    have hLin : LinMk d F (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hscal : ((x * y⁻¹ : ↥(LinSL d F)) : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F :=
      (QuotientGroup.eq_one_iff
        (N := (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F)) (x * y⁻¹)).mp hLin
    have hz1 : ((x * y⁻¹ : ↥(LinSL d F)) : GL (Fin d) F) = 1 := hD_scal _ hz hscal
    exact eq_of_mul_inv_eq_one (Subtype.ext hz1)
  have hDsub_card :
      Nat.card ((LinDiagTorsion p d F).subgroupOf (LinSL d F)) = p ^ (d - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_SL).toEquiv, hD_card]
  have hDmap_card :
      Nat.card (((LinDiagTorsion p d F).subgroupOf (LinSL d F)).map (LinMk d F))
        = p ^ (d - 1) := by
    calc
      Nat.card (((LinDiagTorsion p d F).subgroupOf (LinSL d F)).map (LinMk d F))
          = Nat.card ((LinDiagTorsion p d F).subgroupOf (LinSL d F)) :=
            Nat.card_congr (Equiv.Set.imageOfInjOn (LinMk d F) _ hinj).symm
      _ = p ^ (d - 1) := hDsub_card
  have hBcard : Nat.card (Bbar.map ψ.toMonoidHom) = Nat.card Bbar :=
    Subgroup.card_map_of_injective ψ.injective
  change Bbar.map ψ.toMonoidHom
    = ((LinDiagTorsion p d F).subgroupOf (LinSL d F)).map (LinMk d F)
  rw [hfr.2.2.2]
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hAD) ?_
  calc
    Nat.card (((LinDiagTorsion p d F).subgroupOf (LinSL d F)).map (LinMk d F))
        = p ^ (d - 1) := hDmap_card
    _ ≤ Nat.card Bbar := hcard
    _ = Nat.card (Bbar.map ψ.toMonoidHom) := hBcard.symm
    _ = Nat.card ((A.subgroupOf (LinSL d F)).map (LinMk d F)) := by rw [hfr.2.2.2]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
