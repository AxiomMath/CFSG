module

public import CFSG.Quasithin.Background.F918H3
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem autSub_finset_sup {U : Subgroup W} {Y : Subgroup (MulAut W)}
    (s : Finset (Subgroup (MulAut W))) :
    (∀ H ∈ s, H ≤ Y) → Y ≤ stabSub U →
    autSub (s.sup (fun H => H)) U = s.sup (fun H => autSub H U) := by
  classical
  revert s
  intro s
  induction s using Finset.induction with
  | empty =>
    intro _ hst
    show autSub (⊥ : Subgroup (MulAut W)) U = ⊥
    rw [autSub_eq_map_resHomOn (K := ⊥) (H := Y) bot_le hst, Subgroup.bot_subgroupOf,
      Subgroup.map_bot]
  | insert H s hH ih =>
    intro hle hst
    rw [Finset.sup_insert, Finset.sup_insert,
      CFSG.CGT.PushingUpLit.BHS.autSub_sup ((hle H (Finset.mem_insert_self H s)).trans hst)
        ((Finset.sup_le fun K hK => hle K (Finset.mem_insert_of_mem hK)).trans hst)]
    rw [ih (fun K hK => hle K (Finset.mem_insert_of_mem hK)) hst]

theorem iSup_autSub_eq {U : Subgroup W} {Y : Subgroup (MulAut W)}
    {Δ : Set (Subgroup (MulAut W))} (hfin : Δ.Finite) (hle : ∀ H ∈ Δ, H ≤ Y)
    (hgen : (⨆ H ∈ Δ, H) = Y) (hst : Y ≤ stabSub U) :
    (⨆ H ∈ Δ, autSub H U) = autSub Y U := by
  classical
  have hgen' : hfin.toFinset.sup (fun H => H) = Y := by
    rw [Finset.sup_eq_iSup]
    simp only [hfin.mem_toFinset]
    exact hgen
  have hsup := autSub_finset_sup (U := U) (Y := Y) hfin.toFinset
    (fun H hH => hle H ((hfin.mem_toFinset).mp hH)) hst
  calc (⨆ H ∈ Δ, autSub H U)
      = hfin.toFinset.sup (fun H => autSub H U) := by
        rw [Finset.sup_eq_iSup]
        simp only [hfin.mem_toFinset]
    _ = autSub (hfin.toFinset.sup (fun H => H)) U := hsup.symm
    _ = autSub Y U := by rw [hgen']

theorem ker_resHomOn_eq {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)}
    {U : Subgroup W} (hstab : Y ≤ stabSub U) :
    (resHomOn U hstab).ker = (Y ⊓ centSub U).subgroupOf Y := by
  ext x
  simp only [resHomOn, MonoidHom.mem_ker, MonoidHom.comp_apply, ker_resHom,
    Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have h' : (Subgroup.inclusion hstab x) ∈ (resHom U).ker := by simpa using h
    rwa [ker_resHom, Subgroup.mem_subgroupOf] at h'
  · rintro ⟨-, h⟩
    show (Subgroup.inclusion hstab x) ∈ (resHom U).ker
    rw [ker_resHom, Subgroup.mem_subgroupOf]
    exact h

end CFSG.GroupTheory
