module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6P6c
public import CFSG.Quasithin.Background.C48Asm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem y6_quot_of_sup {G Q : Type} [Group G] [Group Q] {N K C : Subgroup G} (hKN : K ≤ N)
    (hKn : (K.subgroupOf N).Normal) (hCN : C ≤ N) (hsup : N = C ⊔ K) (ψ : ↥C →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = K.subgroupOf C) :
    ∃ φ : ↥N →* Q, Function.Surjective φ ∧ φ.ker = K.subgroupOf N ∧
      ∀ c : ↥C, φ ⟨(c : G), hCN c.2⟩ = ψ c := by
  have hCK : C ≤ normalizer (K : Set G) := fun c hc =>
    Subgroup.le_normalizer_of_normal_subgroupOf hKN (hCN hc)
  obtain ⟨α, hs, hk, hext⟩ := CFSG.Quasithin.C48.exists_hom_sup ψ hψ hCK hker
  subst hsup
  exact ⟨α, hs, hk, hext⟩

theorem y6_quotIso_blockStab {G : Type} [Group G] {N M C : Subgroup G} (hMN : M ≤ N)
    (φ : ↥N →* Equiv.Perm (Fin 6)) (hker : φ.ker = C.subgroupOf N)
    (hcard : Nat.card ↥((M.subgroupOf N).map φ) = 72) :
    ∃ ψ : ↥M →* ↥blockStab, Function.Surjective ψ ∧ ψ.ker = C.subgroupOf M := by
  obtain ⟨σ, hσ⟩ := y6_order72_conj hcard
  set ρ : ↥M →* Equiv.Perm (Fin 6) := φ.comp (Subgroup.inclusion hMN) with hρdef
  have hρrange : ρ.range = (M.subgroupOf N).map φ := by
    rw [hρdef, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hmem : ∀ m : ↥M, (MulAut.conj σ⁻¹).toMonoidHom (ρ m) ∈ blockStab := by
    intro m
    have hm : ρ m ∈ (M.subgroupOf N).map φ := by
      rw [← hρrange]
      exact MonoidHom.mem_range.mpr ⟨m, rfl⟩
    rw [hσ] at hm
    obtain ⟨b, hb, hbm⟩ := Subgroup.mem_map.mp hm
    have hbm' : (MulAut.conj σ⁻¹).toMonoidHom (ρ m) = b := by
      rw [← hbm]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hbm']
    exact hb
  set f : ↥M →* Equiv.Perm (Fin 6) :=
    (MulAut.conj σ⁻¹).toMonoidHom.comp ρ with hfdef
  have hf_mem : ∀ m : ↥M, f m ∈ blockStab := by
    intro m
    rw [hfdef]
    exact hmem m
  refine ⟨f.codRestrict blockStab hf_mem, ?_, ?_⟩
  ·
    intro b
    have hb : (MulAut.conj σ).toMonoidHom b ∈ ρ.range := by
      rw [hρrange, hσ]
      exact Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hb
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change f m = (b : Equiv.Perm (Fin 6))
    rw [hfdef]
    rw [MonoidHom.comp_apply, hm]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  ·
    rw [MonoidHom.ker_codRestrict]
    have hfker : f.ker = ρ.ker := by
      rw [hfdef]
      ext m
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact MulEquiv.map_eq_one_iff (MulAut.conj σ⁻¹)
    have hρker : ρ.ker = C.subgroupOf M := by
      rw [hρdef]
      ext m
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h' : Subgroup.inclusion hMN m ∈ φ.ker := MonoidHom.mem_ker.mpr h
        rw [hker] at h'
        simpa [Subgroup.mem_subgroupOf] using h'
      · intro hm
        have h' : Subgroup.inclusion hMN m ∈ φ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          simpa using hm
        exact MonoidHom.mem_ker.mp h'
    rw [hfker, hρker]

end CFSG.OddStandard.HigherRank.YamadaG23
