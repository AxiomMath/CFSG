module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGA5
public import CFSG.Sporadic.SmallOddCore.J2Local

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore

theorem card_centralizer_dvd_of_J2
    {G : Type} [Group G] (hG : Blueprint.NativeSporadic.IsSporadic G .J2) (t : G)
    (ht : orderOf t = 2) : Nat.card ↥(centralizer ({t} : Set G)) ∣ 1920 := by
  have hG' : Nonempty (G ≃* Blueprint.NativeSporadic.J2) := hG
  obtain ⟨e⟩ := hG'
  set θ : G ≃* ↥j2P := e.trans j2PermEquiv
  set u : Equiv.Perm (Fin 315) := (θ t : Equiv.Perm (Fin 315)) with hudef
  have huP : u ∈ j2P := (θ t).2
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  have hc : Nat.card ↥(centralizer ({t} : Set G)) =
      Nat.card ↥(j2P ⊓ centralizer ({u} : Set (Equiv.Perm (Fin 315)))) := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective,
      map_centralizer_equiv θ t,
      ← Subgroup.card_map_of_injective (f := j2P.subtype) j2P.subtype_injective,
      map_centralizer_subtype]
    rfl
  obtain ⟨-, -, -, hrows, hcover, -, hshape, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, hug⟩ := hcover u (j2P_le_j2R huP) hu2
  obtain ⟨-, -, hrouter, -, hcard, -⟩ := hrows r hr
  have hrP : tp 315 r.rep ∈ j2P := by
    have : tp 315 r.rep = g⁻¹ * u * g := by rw [hug]; group
    rw [this]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) huP) hg
  have hrout : r.outer = false := by
    by_contra hne
    exact (hrouter.1 (by simpa using hne)) hrP
  have hr0 : r.centOrder = 240 ∨ r.centOrder = 1920 := by
    have hm : (r.outer, r.classSize, r.centOrder) ∈
        j2Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map_of_mem hr
    rw [hshape] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨h, -, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · rw [hrout] at h
      exact absurd h (by decide)
    · exact Or.inl h
    · exact Or.inr h
  have hmap := map_conj_inf_centralizer j2P hg ({tp 315 r.rep} : Set (Equiv.Perm (Fin 315)))
  have hgu : (MulAut.conj g).toMonoidHom (tp 315 r.rep) = u := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hug.symm
  rw [Set.image_singleton, hgu] at hmap
  have hconj : Nat.card ↥(j2P ⊓ centralizer ({u} : Set (Equiv.Perm (Fin 315)))) =
      r.centOrder := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  rw [hc, hconj]
  rcases hr0 with h | h
  · rw [h]; norm_num
  · rw [h]

theorem footeKnownQuot_J2
    (G : Type) [Group G] [Finite G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .J2) : FooteKnownQuot G 5 := fun L hL => by
  obtain ⟨t, ht2, hLC, -⟩ := hL.1
  exact (center_eq_bot_and_nonempty_alt5 hL ((Subgroup.card_dvd_of_le hLC).trans
    (card_centralizer_dvd_of_J2 hG t ht2)) (eq_of_isSmallOrder_dvd (q₁ := 16) (by norm_num)
      (by norm_num) (by decide) (by norm_num) (by norm_num))).2

end CFSG.ComponentClassification.FooteLit.KG
