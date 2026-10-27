
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryTransfer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {J : Subgroup G} {x : G}

theorem exists_lift_fixed (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1)
    {F : Subgroup (Jhat J)} (hF : IsPGroup 2 F) (hFfix : ∀ e ∈ F, betaHat J hxN e = e) :
    ∃ (E : Subgroup G) (hEJ : E ≤ J ⊓ centralizer {x}) (θ : ↥E ≃* ↥F),
      ∀ u : E, (θ u : Jhat J) = jq J ⟨u, (hEJ u.2).1⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := (F.comap (jq J)).map J.subtype ⊓ centralizer {x} with hM
  have hMJ : M ≤ J ⊓ centralizer {x} := by
    rintro g ⟨⟨j, -, rfl⟩, hgx⟩
    exact ⟨j.2, hgx⟩
  have hMF : ∀ g (hg : g ∈ M), jq J ⟨g, (hMJ hg).1⟩ ∈ F := by
    rintro g ⟨⟨j, hj, rfl⟩, -⟩
    exact hj
  let ψ : ↥M →* ↥F :=
    { toFun := fun m => ⟨jq J ⟨m, (hMJ m.2).1⟩, hMF m m.2⟩
      map_one' := Subtype.ext (map_one (jq J))
      map_mul' := fun a b => Subtype.ext (by
        show jq J ⟨(a : G) * b, _⟩ = jq J ⟨a, _⟩ * jq J ⟨b, _⟩
        rw [← map_mul]
        rfl) }
  have hψ : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    obtain ⟨j, hje, hjx⟩ := exists_fixed_lift hxN hx2 (hFfix e he)
    have hjc : (j : G) ∈ centralizer {x} := by
      apply mem_centralizer_of_conj_eq
      have := congrArg Subtype.val hjx
      rwa [coe_conjJ] at this
    have hjF : j ∈ F.comap (jq J) := by rw [mem_comap, hje]; exact he
    have hjM : (j : G) ∈ M := ⟨⟨j, hjF, rfl⟩, hjc⟩
    exact ⟨⟨j, hjM⟩, Subtype.ext hje⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 ↥M))
  set E : Subgroup G := (T : Subgroup ↥M).map M.subtype with hE
  have hEM : E ≤ M := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hEJ : E ≤ J ⊓ centralizer {x} := hEM.trans hMJ
  have hE2 : IsPGroup 2 E := T.isPGroup'.map M.subtype
  let θ' : ↥E →* ↥F :=
    { toFun := fun u => ⟨jq J ⟨u, (hEJ u.2).1⟩, hMF u (hEM u.2)⟩
      map_one' := Subtype.ext (map_one (jq J))
      map_mul' := fun a b => Subtype.ext (by
        show jq J ⟨(a : G) * b, _⟩ = jq J ⟨a, _⟩ * jq J ⟨b, _⟩
        rw [← map_mul]
        rfl) }
  have hinj : Function.Injective θ' := by
    intro a b hab
    exact Subtype.ext (eq_of_jq_eq (hEJ.trans inf_le_left) hE2 a.2 b.2
      (congrArg Subtype.val hab))
  have htop := (T.mapSurjective hψ).is_maximal' (hF.to_subgroup ⊤) le_top
  have hsurj : Function.Surjective θ' := by
    intro f
    have hf : f ∈ ((T.mapSurjective hψ : Sylow 2 ↥F) : Subgroup ↥F) := by
      rw [← htop]
      trivial
    rw [Sylow.coe_mapSurjective] at hf
    obtain ⟨t, ht, rfl⟩ := hf
    exact ⟨⟨t, ⟨t, ht, rfl⟩⟩, rfl⟩
  exact ⟨E, hEJ, MulEquiv.ofBijective θ' ⟨hinj, hsurj⟩, fun u => rfl⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
