module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NormalTwoGroupWr
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SymThreeLift

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open

theorem eq_top_of_alt_odd {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) {t : Perm Ω} (ht : t ∈ H) (hs : sign t = -1) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases hg : sign g = 1
  · exact hA (mem_alternatingGroup.2 hg)
  · have hg' : sign g = -1 := by
      rcases Int.units_eq_one_or (sign g) with h | h
      · exact absurd h hg
      · exact h
    have h1 : g * t ∈ alternatingGroup Ω := by
      rw [mem_alternatingGroup, map_mul, hg', hs]; rfl
    have h2 : g = (g * t) * t⁻¹ := by group
    rw [h2]
    exact H.mul_mem (hA h1) (H.inv_mem ht)

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G} {r s : ℕ}

theorem theta_S_le_Wr (hA : Asc81bHyp M S) (hSM : S ≤ M) (θ : ↥M →* Perm (OmegaE r s))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (hr1 : 1 ≤ r)
    (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs : s = 0 ∨ s = 1 ∨ s = 3 ∨ 5 ≤ s) :
    ∀ m : ↥M, (m : G) ∈ S → θ m ∈ Wr r s := by
  classical
  let i₀ : Fin r := ⟨0, hr1⟩
  have hWR : Wr r s ≤ θ.range := by
    rw [← hW]
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  have hAltR : alternatingGroup (OmegaE r s) ≤ θ.range := fun x hx => by
    obtain ⟨m, hm⟩ := hAlt x hx
    exact ⟨m, hm⟩
  have htW : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) ∈ Wr r s := by
    have h := embL_blockTransp r s i₀ false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i₀, swap_mem_blockFix rfl, rfl⟩
  have hrange : θ.range = ⊤ :=
    eq_top_of_alt_odd hAltR (hWR htW) (sign_swap (by simp))
  have hnormS : ∀ m : ↥M, θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) →
      (m : G) ∈ Subgroup.normalizer (S : Set G) := fun m hm =>
    mem_normalizer_of_theta_normalizes hA le_rfl hSM θ hker m (by rw [hW]; exact hm)
  let U : Subgroup (Perm (OmegaE r s)) := (S.subgroupOf M).map θ
  have hU2 : IsPGroup 2 U := (hA.twoRadical.isPGroup.comap_subtype (K := M)).map θ
  have hUN : ∀ g ∈ U, g ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← hW]
    exact theta_mem_normalizer_W θ m (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hm))
  have hnorm : ∀ h ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))), ∀ u ∈ U,
      h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    obtain ⟨m, rfl⟩ : h ∈ θ.range := by rw [hrange]; trivial
    obtain ⟨n, hn, rfl⟩ := hu
    have hmN : (m : G) ∈ Subgroup.normalizer (S : Set G) := hnormS m hh
    refine ⟨m * n * m⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    have hnS : (n : G) ∈ S := Subgroup.mem_subgroupOf.1 hn
    have := (Subgroup.mem_normalizer_iff.1 hmN (n : G)).1 hnS
    simpa using this
  have hUW := normal_isPGroup_le_Wr hr hs U hU2 hUN hnorm
  intro m hm
  exact hUW ⟨m, Subgroup.mem_subgroupOf.2 hm, rfl⟩

theorem sym3P_eq_S (hA : Asc81bHyp M S) (hSM : S ≤ M) (θ : ↥M →* Perm (OmegaE r s))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs : s = 1 ∨ s = 3 ∨ 5 ≤ s) :
    sym3P M θ = S := by
  have h1 := (sym3_facts hA.twoRadical.isPGroup hSM θ hker hAlt hW ⟨0, hr1⟩ ⟨0, hs1⟩).2.1
  refine le_antisymm h1 fun x hx => ?_
  have hxM : x ∈ M := hSM hx
  exact ⟨⟨x, hxM⟩, theta_S_le_Wr hA hSM θ hker hAlt hW hr1 hr (by omega) ⟨x, hxM⟩ hx, rfl⟩


@[expose] def HasSym3LiftS (S L M : Subgroup G) : Prop :=
  ∃ Y : Subgroup G, S ≤ Y ∧ Y ≤ M ∧ ¬ 2 ∣ S.relIndex Y ∧
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Perm (Fin 3)) ∧ ¬ Y ≤ Subgroup.normalizer (S : Set G) ∧
    ∃ y : G, y ∈ L ∧ y ∈ Y ∧ Odd (orderOf y) ∧ y ∉ pCoreOf 2 M

theorem exists_sym3_liftS {L : Subgroup G} (hA : Asc81bHyp M S) (hSM : S ≤ M) (hLM : L ≤ M)
    (θ : ↥M →* Perm (OmegaE r s)) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAltL : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ l : ↥L, θ ⟨l, hLM l.2⟩ = x)
    (hcore : ∀ m : ↥M, (m : G) ∈ pCoreOf 2 M → θ m = 1)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs : s = 1 ∨ s = 3 ∨ 5 ≤ s) :
    HasSym3LiftS S L M := by
  have hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x := fun x hx => by
    obtain ⟨l, hl⟩ := hAltL x hx
    exact ⟨⟨l, hLM l.2⟩, hl⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    sym3_facts hA.twoRadical.isPGroup hSM θ hker hAlt hW ⟨0, hr1⟩ ⟨0, hs1⟩
  obtain ⟨hN, y, hy⟩ := sym3_lift ⟨0, hr1⟩ ⟨0, hs1⟩ hLM θ hAltL hcore hW
  have hP := sym3P_eq_S hA hSM θ hker hAlt hW hr1 hs1 hr hs
  rw [hP] at h3 h4
  exact ⟨sym3Y M ⟨0, hr1⟩ ⟨0, hs1⟩ θ, h3, Subgroup.map_subtype_le _, h4, h5, hN, y, hy⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
