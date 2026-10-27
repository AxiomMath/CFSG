module

public import CFSG.LargeExtraspecial.A2ModFrFLie

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open Module CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS CFSG.Blueprint.Chevalley
  CFSG.RankThree.OrthogonalInvolutions CFSG.Open


theorem card_rootGroup_f4Datum (K : Type) [Field K] {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ (Adjoint.f4Datum K).roots) :
    Nat.card ((Adjoint.f4Datum K).rootGroup γ) = Nat.card K := by
  have hγ' := Adjoint.mem_adjDatum_roots.1 hγ
  refine (Nat.card_eq_of_bijective (fun c : K => (⟨Adjoint.xPar _ γ c, Adjoint.xPar_mem hγ' c⟩ :
    (Adjoint.f4Datum K).rootGroup γ)) ⟨fun c d h => Adjoint.xPar_injective hγ'
      (congrArg Subtype.val h), fun x => ?_⟩).symm
  obtain ⟨c, hc⟩ := (Adjoint.mem_rootGroup_iff hγ' x.1).1 x.2
  exact ⟨c, Subtype.ext hc⟩

variable {G : Type} [Group G] {R : Set (Subgroup G)} {D : Set G} {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ : G →* (V ≃ₗ[ZMod 2] V)}

theorem false_of_f4Datum [Finite G] {K : Type} [Field K]
    {nW : Fin (Tag.rank .F4) → adjointGroup .F4 K}
    {H : Fin (Tag.rank .F4) → Subgroup (adjointGroup .F4 K)}
    (hct : IsCTGroupDatum (coxeterMatrix (Adjoint.f4Datum K).isFiniteType).toCoxeterSystem
      (weylAction (Adjoint.f4Datum K).isFiniteType) (Adjoint.f4Datum K).roots
      (Adjoint.f4Datum K).rootGroup nW H)
    (hext : SteinbergExtras (Adjoint.f4Datum K) nW H) {i₀ : Fin (Tag.rank .F4)} (hi₀ : i₀.val < 2)
    (pg : ∀ γ ∈ (Adjoint.f4Datum K).roots, IsPGroup 2 ((Adjoint.f4Datum K).rootGroup γ))
    (Ψ : adjointGroup .F4 K →* G) (surj : Function.Surjective Ψ)
    (ker : Ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (mem : ((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)).map Ψ ∈ R)
    (opp : Opposite (((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)).map Ψ)
      (((Adjoint.f4Datum K).rootGroup (-Pi.single i₀ 1)).map Ψ))
    (hR : IsRootClass R) (hiso : NoIsolated R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hA : A2Action D Q ρ) : False := by
  let F : F4Frame G R :=
    ⟨adjointGroup .F4 K, (Adjoint.f4Datum K).isFiniteType, (Adjoint.f4Datum K).rootGroup, nW, H,
      hct, hext, i₀, hi₀, pg, Ψ, surj, ker, mem, opp⟩
  have hroot : ∀ i : Fin 4, (Pi.single i 1 : Fin 4 → ℤ) ∈ (Adjoint.f4Datum K).roots := fun i =>
    (RootSystem.ofCartan F.hA ∅).single_mem i
  obtain ⟨d, -, hE⟩ := hRD _ mem
  have h2 : Nat.card (((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)).map Ψ) = 2 :=
    card_eq_two_of_mem hR mem hE
  have hinj : Function.Injective
      (Ψ.comp ((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)).subtype) := fun x y h =>
    Subtype.ext (F.eq_of_map_eq (γ := Pi.single i₀ 1) (hroot i₀) x.2 y.2 h)
  have hcardX : Nat.card ((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)) = 2 := by
    have e : ((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)).map Ψ =
        (Ψ.comp ((Adjoint.f4Datum K).rootGroup (Pi.single i₀ 1)).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h2, e]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hK : Nat.card K = 2 := (card_rootGroup_f4Datum K (hroot i₀)).symm.trans hcardX
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K)
  have hΨ : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact ker
  have hcard : Nat.card G = ordF4 2 := by
    rw [← Nat.card_eq_of_bijective Ψ ⟨hΨ, surj⟩,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK]
  have hm : Nat.card (F.X a2v) ≤ 2 := (card_rootGroup_f4Datum K (a2v_mem_roots F.hA)).trans_le
    hK.le
  exact F.false_of_a2Action hR hRD hDc hiso hA hm (by norm_num) (by norm_num)
    (by rw [hcard, ordF4_two_eq]; decide) thirteen_not_dvd

end CFSG.LargeExtraspecial.A2Mod.FrF
