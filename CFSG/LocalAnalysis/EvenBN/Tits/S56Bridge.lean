module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_rho_P0_mem_twoF4S (hd : d.Hyp) {c : G} (hcP : c ∈ d.s56P0)
    (hcC : c ∈ centralizer ({d.t} : Set G)) :
    (d.ρ ⟨c, hcC⟩ : Equiv.Perm (Fin 1755)) ∈ CFSG.Quasithin.twoF4S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : centralizer ({d.t} : Set G) →* Equiv.Perm (Fin 1755) := titsA.subtype.comp d.ρ with hf
  have hRp : IsPGroup 2 (d.s56P0.subgroupOf (centralizer ({d.t} : Set G))) :=
    (s56_P0_isPGroup d).comap_subtype
  set X : Subgroup (Equiv.Perm (Fin 1755)) :=
    (d.s56P0.subgroupOf (centralizer ({d.t} : Set G))).map f
  have hXp : IsPGroup 2 X := hRp.map f
  set H : Subgroup (Equiv.Perm (Fin 1755)) := CFSG.Quasithin.twoF4N ⊓ f.range with hH
  set Q : Subgroup (Equiv.Perm (Fin 1755)) := CFSG.Quasithin.twoF4S ⊓ f.range with hQ
  have hQH : Q ≤ H := inf_le_inf_right _ CFSG.Quasithin.twoF4S_le_twoF4N
  have hQp : IsPGroup 2 Q :=
    (IsPGroup.of_card (n := 12) (by rw [Model.card_twoF4S.1]; norm_num) :
      IsPGroup 2 CFSG.Quasithin.twoF4S).to_le inf_le_left
  have hXH : X ≤ H := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_inf.2 ⟨hd.s56_rho_mem_twoF4N (mem_inf.2 ⟨s56_P0_le_N d hr, r.2⟩), ⟨r, rfl⟩⟩
  have hconj : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    intro h hh x hx
    obtain ⟨hN, g, rfl⟩ := mem_inf.1 hh
    obtain ⟨r, hr, rfl⟩ := hx
    have hgN : (g : G) ∈ d.N := by
      refine (hd.mem_normalizer_tSup_iff Model.parrottF_le_titsD g.2).2 ?_
      rw [← Model.titsA_inf_normalizer_parrottF] at hN
      exact (mem_inf.1 hN).2
    exact ⟨g * r * g⁻¹, s56_N_conj_P0 d hgN hr, by simp only [map_mul, map_inv]⟩
  have hcard : Nat.card H = Nat.card Q * 3 := by
    rcases hd.range_ρ with hR | hR
    · have hr : f.range = titsD := by
        rw [hf, MonoidHom.range_comp, hR, Subgroup.map_subgroupOf_eq_of_le titsD_le_titsA]
      rw [hH, hQ, hr, Model.card_twoF4N.2.1, Model.card_twoF4S.2, titsQN_facts.2.2.2,
        titsQS_facts.2.2.2]
    · have hr : f.range = titsA := by
        rw [hf, MonoidHom.range_comp, hR, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [hH, hQ, hr, inf_of_le_left Model.twoF4N_le_titsA,
        inf_of_le_left (CFSG.Quasithin.twoF4S_le_twoF4N.trans Model.twoF4N_le_titsA),
        Model.card_twoF4N.1, Model.card_twoF4S.1]
  have hXQ : X ≤ Q := le_of_isPGroup_of_conj hQH hXH hQp hXp hcard (by norm_num) hconj
  exact (mem_inf.1 (hXQ ⟨⟨c, hcC⟩, hcP, rfl⟩)).1

theorem Hyp.s56_rho_P0_mem_hatC (h49 : d.Thm49Statement) (hd : d.Hyp) {c : G}
    (hcP : c ∈ d.s56P0) (hcC : c ∈ centralizer ({d.t} : Set G)) :
    (d.ρ ⟨c, hcC⟩ : Equiv.Perm (Fin 1755)) ∈ Model.hatC := by
  have _ := h49
  obtain ⟨hyNC, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  have hyC : d.s56Y ∈ centralizer ({d.t} : Set G) := (mem_inf.1 hyNC).2
  have hyD : Model.nlocY ∈ titsD := titsN_le_titsD Model.nlocY_facts.1
  have hcP' : d.s56Y⁻¹ * c * d.s56Y ∈ d.s56P0 := by
    have := s56_N_conj_P0 d (inv_mem hyN) hcP
    rwa [inv_inv] at this
  have hcC' : d.s56Y⁻¹ * c * d.s56Y ∈ centralizer ({d.t} : Set G) :=
    mul_mem (mul_mem (inv_mem hyC) hcC) hyC
  have hρy : (d.ρ ⟨d.s56Y, hyC⟩ : Equiv.Perm (Fin 1755)) = Model.nlocY := hd.ρ_lift hyD
  have hρ : (d.ρ ⟨d.s56Y⁻¹ * c * d.s56Y, hcC'⟩ : Equiv.Perm (Fin 1755)) =
      Model.nlocY⁻¹ * (d.ρ ⟨c, hcC⟩ : Equiv.Perm (Fin 1755)) * Model.nlocY := by
    have e : (⟨d.s56Y⁻¹ * c * d.s56Y, hcC'⟩ : centralizer ({d.t} : Set G)) =
        ⟨d.s56Y, hyC⟩⁻¹ * ⟨c, hcC⟩ * ⟨d.s56Y, hyC⟩ := rfl
    rw [e, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρy]
  exact Model.mem_hatC_of_conj (hd.s56_rho_P0_mem_twoF4S hcP hcC) (by
    rw [← hρ]
    exact hd.s56_rho_P0_mem_twoF4S hcP' hcC')

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
