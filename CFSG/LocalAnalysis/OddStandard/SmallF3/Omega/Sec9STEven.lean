module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STFr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod
public import TauCeti.Data.Finset.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def IsEvenFrame {n : ℕ} (b : Module.Basis (Fin n) (ZMod 3) V)
    (Ft : Subgroup (OGroup Q)) : Prop :=
  (∀ g ∈ Ft, ∃ S : Finset (Fin n), Even S.card ∧
      ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ S then (-1 : ZMod 3) else 1) • b i) ∧
    ∀ S : Finset (Fin n), Even S.card → ∃ g ∈ Ft,
      ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ S then (-1 : ZMod 3) else 1) • b i

theorem IsEvenFrame.mem_iff {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft) {g : OGroup Q} :
    g ∈ Ft ↔ ∃ S : Finset (Fin n), Even S.card ∧
      ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ S then (-1 : ZMod 3) else 1) • b i := by
  constructor
  · intro hg
    exact hb.1 g hg
  · rintro ⟨S, hS, hgS⟩
    obtain ⟨g', hg'mem, hg'act⟩ := hb.2 S hS
    have hgg' : g = g' := by
      apply Subtype.ext
      exact b.ext' fun i => by rw [hgS i, hg'act i]
    rw [hgg']
    exact hg'mem

theorem sec9t_exists_evenFrame (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    (F : Subgroup (ProjSim Q)) (hF16 : Nat.card F = 2 ^ 4)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4) :
    ∃ b : Module.Basis (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) V,
      IsEvenFrame b (F.comap (phiSim Q)) := by
  classical
  let Ft : Subgroup (OGroup Q) := F.comap (phiSim Q)
  let E := ↥Ft
  have hlift' : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f := by
    intro f hf hne
    obtain ⟨t, htt, htf, -, -⟩ := hlift f hf hne
    exact ⟨t, htt, htf⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  haveI : Finite (OGroup Q) :=
    Finite.of_injective (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) Subtype.val_injective
  haveI : Finite E := Finite.of_injective (Subtype.val : E → OGroup Q) Subtype.val_injective
  haveI : Fintype E := Fintype.ofFinite E
  let ρ : E →* (V ≃ₗ[ZMod 3] V) :=
    (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup Q)).comp (Subgroup.subtype Ft)
  have hρ : Function.Injective ρ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hE : ∀ g : E, g * g = 1 := by
    intro g
    apply Subtype.ext
    exact sec9e_comap_sq F hlift' (g : OGroup Q) g.2
  obtain ⟨b, A, hAinj, hAcard, hAeig⟩ := sec9t_exists_frame ρ hρ hE
  have hAcard' : ∀ g : E, (A g).card = invDim (g : OGroup Q) := by
    intro g
    rw [hAcard g]
    rfl
  have hAeven : ∀ g : E, Even (A g).card := by
    intro g
    rw [hAcard' g]
    exact sec9e_invDim_even hQ h6 F hF16 hlift (g : OGroup Q) g.2
  have hcardE : Nat.card E = 2 ^ 5 := by
    have hc : Nat.card (F.comap (phiSim Q)) = Nat.card F * 2 :=
      sec9e_card_comap (by rw [h6]; norm_num) F hlift'
    change Nat.card (F.comap (phiSim Q)) = 2 ^ 5
    rw [hc, hF16]
    norm_num
  let Evens : Finset (Finset (Fin (Module.finrank (ZMod 3) V))) :=
    Finset.univ.filter (fun S => Even S.card)
  let 𝒜 : Finset (Finset (Fin (Module.finrank (ZMod 3) V))) := Finset.univ.image A
  have hcardA : 𝒜.card = 2 ^ 5 := by
    change (Finset.univ.image A).card = 2 ^ 5
    rw [Finset.card_image_of_injective _ hAinj, Finset.card_univ,
      Fintype.card_eq_nat_card, hcardE]
  have hEvens5 : Evens.card = 2 ^ 5 := by
    have h := TauCeti.card_even_card_finset (ι := Fin (Module.finrank (ZMod 3) V))
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_fin] at h
    have h5 : Module.finrank (ZMod 3) V - 1 = 5 := by omega
    rw [h5] at h
    exact h
  have hsub : 𝒜 ⊆ Evens := by
    intro S hS
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAeven g⟩
  have hAE : 𝒜 = Evens :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hEvens5, hcardA])
  refine ⟨b, ?_, ?_⟩
  · intro g hg
    refine ⟨A ⟨g, hg⟩, hAeven ⟨g, hg⟩, ?_⟩
    intro i
    exact hAeig ⟨g, hg⟩ i
  · intro S hS
    have hSEvens : S ∈ Evens := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
    have hS𝒜 : S ∈ 𝒜 := by rw [hAE]; exact hSEvens
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hS𝒜
    refine ⟨(g : OGroup Q), g.2, ?_⟩
    intro i
    rw [← hg]
    exact hAeig g i

end CFSG.OddStandard.SmallF3.Omega
