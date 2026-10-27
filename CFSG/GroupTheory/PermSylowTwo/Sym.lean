module

public import CFSG.GroupTheory.PermSylowTwo.SymCore

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm CFSG.QuasithinUnique

theorem isSylowTwoOf_map_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {S A : Subgroup G} (h : IsSylowTwoOf S A) :
    IsSylowTwoOf (S.map f) (A.map f) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, ?_⟩
  show ¬ 2 ∣ (S.map f).relIndex (A.map f)
  rw [Subgroup.relIndex_map_map_of_injective S A hf]
  exact h.2.2

theorem map_cond_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {S H : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (S : Set G)) :
    ¬ 3 ∣ Nat.card (H.map f) ∨
      H.map f ≤ Subgroup.normalizer ((S.map f : Subgroup G') : Set G') := by
  rcases h3 with h3 | h3
  · left
    rwa [Subgroup.card_map_of_injective hf]
  · right
    calc H.map f ≤ (Subgroup.normalizer (S : Set G)).map f := Subgroup.map_mono h3
      _ ≤ Subgroup.normalizer ((S.map f : Subgroup G') : Set G') :=
        Subgroup.le_normalizer_map (H := S) f

theorem isSylowTwoOf_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    {S A : Subgroup G} (h : IsSylowTwoOf S A) :
    IsSylowTwoOf (S.map φ.toMonoidHom) (A.map φ.toMonoidHom) :=
  isSylowTwoOf_map_of_injective φ.injective h

theorem exists_isSylowTwoOf_top (G : Type*) [Group G] [Finite G] :
    ∃ R : Subgroup G, IsSylowTwoOf R ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := G)
  refine ⟨S, le_top, S.isPGroup', ?_⟩
  show ¬ 2 ∣ (S : Subgroup G).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact S.not_dvd_index

theorem exists_mem_conj_ge {G : Type*} [Group G] [Finite G] {A S F : Subgroup G}
    (hS : IsSylowTwoOf S A) (hFA : F ≤ A) (hF : IsPGroup 2 F) :
    ∃ g ∈ A, F ≤ S.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 ↥A := hS.2.1.comap_subtype.toSylow hS.2.2
  obtain ⟨Q, hQ⟩ := hF.comap_subtype (K := A) |>.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq ↥A S' Q
  refine ⟨(a : G), a.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hFA hx⟩ : ↥A) ∈ (Q : Subgroup ↥A) :=
    hQ (Subgroup.mem_subgroupOf.mpr hx)
  rw [← ha, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hxQ
  obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.mp hxQ
  refine Subgroup.mem_map.mpr ⟨(s : G), Subgroup.mem_subgroupOf.mp hs, ?_⟩
  simpa using congrArg Subtype.val hsa

theorem isPGroup_two_of_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (ψ : G ≃* G')
    {H : Subgroup G} (h : IsPGroup 2 (H.map ψ.toMonoidHom)) : IsPGroup 2 H :=
  h.of_equiv (Subgroup.equivMapOfInjective H ψ.toMonoidHom ψ.injective).symm

theorem isPGroup_two_of_sylow_le (α : Type) [Fintype α] [DecidableEq α]
    {P H : Subgroup (Perm α)} (hP : IsSylowTwoOf P ⊤) (hPH : P ≤ H)
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (P : Set (Perm α))) : IsPGroup 2 H := by
  classical
  suffices ∀ m, ∀ (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = m →
      ∀ P H : Subgroup (Perm α), IsSylowTwoOf P ⊤ → P ≤ H →
      (¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (P : Set (Perm α))) → IsPGroup 2 H from
    this _ α rfl P H hP hPH h3
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro α _ _ hcard P H hP hPH h3
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    ·
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp (hcard.trans hm0)
      haveI : Subsingleton (Perm α) := ⟨fun f g => by ext x; exact (IsEmpty.false x).elim⟩
      exact fun g => ⟨0, by
        have h1 : g = 1 := Subsingleton.elim _ _
        rw [h1, one_pow]⟩
    ·
      have hm2 : m / 2 < m := by
        rcases Nat.lt_or_ge 1 m with hm1 | hm1
        · exact Nat.div_lt_self hmpos (by norm_num)
        · have h1 : m = 1 := by omega
          subst h1
          norm_num
      let β := Fin (m / 2)
      let γ := Fin (m % 2)
      let Ω := (β × Bool) ⊕ γ
      have hγ : Subsingleton γ := by
        rw [show γ = Fin (m % 2) from rfl, Fin.subsingleton_iff_le_one]
        have := Nat.mod_lt m (by norm_num : 0 < 2)
        omega
      haveI : Subsingleton γ := hγ
      have hcardΩ : Fintype.card Ω = m := by
        have h := Nat.div_add_mod m 2
        simp only [Ω, β, γ, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
          Fintype.card_fin]
        omega
      let e : α ≃ Ω := Fintype.equivOfCardEq (hcard.trans hcardΩ.symm)
      let ψ : Perm α ≃* Perm Ω := Equiv.permCongrHom e
      let P' : Subgroup (Perm Ω) := P.map ψ.toMonoidHom
      let H' : Subgroup (Perm Ω) := H.map ψ.toMonoidHom
      have hP' : IsSylowTwoOf P' ⊤ := by
        have h := isSylowTwoOf_map_mulEquiv ψ hP
        rwa [Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective] at h
      have hPH' : P' ≤ H' := Subgroup.map_mono hPH
      have h3' : ¬ 3 ∣ Nat.card H' ∨ H' ≤ Subgroup.normalizer (P' : Set (Perm Ω)) :=
        map_cond_of_injective (f := ψ.toMonoidHom) (S := P) ψ.injective h3
      have hmain : ∀ P₀ H₀ : Subgroup (Perm Ω), IsSylowTwoOf P₀ ⊤ → P₀ ≤ H₀ →
          (¬ 3 ∣ Nat.card H₀ ∨ H₀ ≤ Subgroup.normalizer (P₀ : Set (Perm Ω))) →
          IsPGroup 2 H₀ := by
        intro P₀ H₀ hP₀ hP₀H₀ h3₀
        obtain ⟨R, hR⟩ := exists_isSylowTwoOf_top (Perm β)
        let F : Subgroup (Perm Ω) :=
          pairSwaps β γ ⊔ R.map ((pairCent β γ).subtype.comp (pairLift β γ))
        have hF : IsPGroup 2 F := isPGroup_two_pairSwaps_sup hR.2.1
        obtain ⟨g, -, hgF⟩ := exists_mem_conj_ge (A := ⊤) hP₀ le_top hF
        let P₁ : Subgroup (Perm Ω) := P₀.map (MulAut.conj g).toMonoidHom
        let H₁ : Subgroup (Perm Ω) := H₀.map (MulAut.conj g).toMonoidHom
        have hP₁ : IsSylowTwoOf P₁ ⊤ := by
          have h := isSylowTwoOf_map_mulEquiv (MulAut.conj g) hP₀
          rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h
        have hP₁H₁ : P₁ ≤ H₁ := Subgroup.map_mono hP₀H₀
        have h3₁ : ¬ 3 ∣ Nat.card H₁ ∨ H₁ ≤ Subgroup.normalizer (P₁ : Set (Perm Ω)) :=
          map_cond_of_injective (f := (MulAut.conj g).toMonoidHom) (S := P₀)
            (MulAut.conj g).injective h3₀
        have hH₁ : IsPGroup 2 H₁ :=
          isPGroup_two_of_pairing (β := β) (γ := γ)
            (fun P₂ H₂ hP₂ hP₂H₂ h3₂ =>
              ih (m / 2) hm2 β (Fintype.card_fin (m / 2)) P₂ H₂ hP₂ hP₂H₂ h3₂)
            hP₁ (le_sup_left.trans hgF) hR (le_sup_right.trans hgF) hP₁H₁ h3₁
        exact isPGroup_two_of_map_mulEquiv (MulAut.conj g) hH₁
      have hH' : IsPGroup 2 H' := hmain P' H' hP' hPH' h3'
      exact isPGroup_two_of_map_mulEquiv ψ hH'

end CFSG.GroupTheory.PermSylowTwo
