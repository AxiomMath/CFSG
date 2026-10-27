module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace L29GW

section Transport

theorem cyclic_or_dihedral_of_surj_odd_ker {A B : Type} [Group A] [Finite A] [Group B]
    (ψ : A →* B) (hψ : Function.Surjective ψ) (hk : Odd (Nat.card ψ.ker))
    (hA : ∀ P : Sylow 2 A, IsCyclic ↥P ∨ IsDihedral ↥P) :
    ∀ S : Sylow 2 B, IsCyclic ↥S ∨ IsDihedral ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  obtain ⟨S₀, rfl⟩ := Sylow.mapSurjective_surjective hψ 2 S
  have hinj := injective_on_pgroup ψ hk (S₀ : Subgroup A) S₀.isPGroup'
  let e₁ : ↥(S₀ : Subgroup A) ≃* ↥(ψ.comp (S₀ : Subgroup A).subtype).range :=
    MonoidHom.ofInjective hinj
  have hr : (ψ.comp (S₀ : Subgroup A).subtype).range = (S₀ : Subgroup A).map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcoe : ((S₀.mapSurjective hψ : Sylow 2 B) : Subgroup B) = (S₀ : Subgroup A).map ψ :=
    Sylow.coe_mapSurjective hψ S₀
  let e : ↥(S₀ : Subgroup A) ≃* ↥((S₀.mapSurjective hψ : Sylow 2 B) : Subgroup B) :=
    (e₁.trans (MulEquiv.subgroupCongr hr)).trans (MulEquiv.subgroupCongr hcoe.symm)
  rcases hA S₀ with hc | hd
  · exact Or.inl (e.isCyclic.mp hc)
  · exact Or.inr (isDihedral_congr e.symm hd)

end Transport

section Setup

variable {Y : Type} [Group Y] [Finite Y]

theorem quotient_setup (hns : ¬ Group.IsSolvable Y)
    (hD : ∀ P : Sylow 2 ↥(oResidual 2 Y), IsCyclic ↥P ∨ IsDihedral ↥P) :
    ∃ (M : Subgroup (Y ⧸ pPrimeCore 2 Y)) (_ : M.Normal),
      IsPGroup 2 ((Y ⧸ pPrimeCore 2 Y) ⧸ M) ∧ ¬ Group.IsSolvable ↥M ∧
        ∀ S : Sylow 2 ↥M, IsCyclic ↥S ∨ IsDihedral ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Y := pPrimeCore 2 Y with hN
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hNsol : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  set H : Subgroup Y := oResidual 2 Y with hH
  have hHn : H.Normal := Stage1.Thm6.Prod.oResidual_normal 2 Y
  set M : Subgroup (Y ⧸ N) := H.map π with hM
  have hMn : M.Normal := Subgroup.Normal.map hHn π hπs
  have hHM : H ≤ M.comap π := fun h hh => ⟨h, hh, rfl⟩
  have hYH : IsPGroup 2 (Y ⧸ H) := by
    obtain ⟨b, hb⟩ := (L29Burnside.exists_index_oResidual_two (H := Y))
    exact IsPGroup.of_card (n := b) (by rw [← Subgroup.index, hb])
  have hDM : IsPGroup 2 ((Y ⧸ N) ⧸ M) :=
    hYH.of_surjective (QuotientGroup.map H M π hHM)
      (QuotientGroup.map_surjective_of_surjective H M π
        ((QuotientGroup.mk_surjective).comp hπs) hHM)
  refine ⟨M, hMn, hDM, ?_, ?_⟩
  ·
    intro hMs
    have hDMs : Group.IsSolvable ((Y ⧸ N) ⧸ M) := by
      have : Group.IsNilpotent ((Y ⧸ N) ⧸ M) := hDM.isNilpotent
      infer_instance
    have hDs : Group.IsSolvable (Y ⧸ N) :=
      Group.isSolvable_of_ker_le_range M.subtype (QuotientGroup.mk' M) (by
        rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    exact hns (Group.isSolvable_of_ker_le_range N.subtype π (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  ·
    let ψ : ↥H →* ↥M := (π.comp H.subtype).codRestrict M fun h => ⟨h.1, h.2, rfl⟩
    have hψs : Function.Surjective ψ := by
      rintro ⟨m, h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    have hker : Odd (Nat.card ψ.ker) := by
      let φ : ↥ψ.ker →* ↥N := ((H.subtype).comp ψ.ker.subtype).codRestrict N fun g => by
        have h1 : ψ g = 1 := g.2
        have h2 : π (g : H) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hinj : Function.Injective φ := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : ↥N => (t : Y)) hab
      exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_injective φ hinj)
    exact cyclic_or_dihedral_of_surj_odd_ker ψ hψs hker hD

end Setup

end L29GW

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
