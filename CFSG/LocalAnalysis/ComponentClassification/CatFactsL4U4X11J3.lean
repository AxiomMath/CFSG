module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Ord
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

theorem card_inf_centralizer_conj {M : Type*} [Group M] {P : Subgroup M} {g : M} (hg : g ∈ P)
    (x : M) : Nat.card ↥(P ⊓ centralizer ({g * x * g⁻¹} : Set M)) =
      Nat.card ↥(P ⊓ centralizer ({x} : Set M)) := by
  have e : (P ⊓ centralizer ({x} : Set M)).map (MulAut.conj g).toMonoidHom =
      P ⊓ centralizer ({g * x * g⁻¹} : Set M) := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzP, hz⟩, rfl⟩
      refine ⟨P.mul_mem (P.mul_mem hg hzP) (P.inv_mem hg), ?_⟩
      calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
        _ = g * (x * z) * g⁻¹ := by rw [hz]
        _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
    · rintro ⟨hyP, hy⟩
      refine ⟨g⁻¹ * y * g, ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hyP) hg, ?_⟩, by group⟩
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
  rw [← e, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem KConf.not_j3
    {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (h : KConf G N) : ¬ Blueprint.NativeSporadic.IsSporadic ↥N .J3 := by
  rintro ⟨ψ⟩
  obtain ⟨hNn, hC, -, b, K, hb, hKN, hKb, -, hKm⟩ := h
  have : N.Normal := hNn
  set θ : ↥N ≃* j3P := ψ.trans Sporadic.Schreier.j3PermEquiv
  set ι := j3_autModel.embed N θ
  have hinj : Function.Injective ι := j3_autModel.embed_injective N θ hC
  have hcard : Nat.card ↥(N ⊓ centralizer ({b} : Set G)) =
      Nat.card ↥(j3P ⊓ centralizer ({ι b} : Set (Equiv.Perm (Fin 6156)))) :=
    Nat.card_congr (j3_autModel.centralizerEquiv N θ hC b).toEquiv
  have hbR : ι b ∈ j3R := j3_autModel.embed_mem N θ b
  have hb2 : orderOf (ι b) = 2 := by rw [orderOf_injective ι hinj, hb]
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, hgt⟩ := hcover (ι b) hbR hb2
  obtain ⟨-, -, -, -, hcr, -⟩ := hrows r hr
  have hcent : r.centOrder = 1920 ∨ r.centOrder = 2448 := by
    have hm := List.mem_map_of_mem (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder))
      hr
    rw [hmap] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h1⟩ | ⟨-, -, h1⟩
    · exact Or.inl h1
    · exact Or.inr h1
  rw [hgt, card_inf_centralizer_conj hg, hcr] at hcard
  have h1 : 25920 ∣ Nat.card K := by
    rw [← card_of_lieModel_psp_four_three hKm]
    exact Subgroup.card_quotient_dvd_card _
  have h2 := h1.trans (Subgroup.card_dvd_of_le (le_inf hKN hKb))
  rw [hcard] at h2
  rcases hcent with h3 | h3 <;> rw [h3] at h2 <;> norm_num at h2

end CFSG.ComponentClassification.GSThmB.X11
