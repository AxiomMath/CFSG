module

public import CFSG.Goldschmidt75.B1Comp
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Goldschmidt.Steps.G41
public import CFSG.Goldschmidt.Steps.IHConseq
public import CFSG.Goldschmidt.Steps.Red2
public import CFSG.Goldschmidt75.B1TypeII
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem ih_all
    (n : ℕ) : IH n := fun Z _ _ _ => coreStatement Z

theorem map_component_eq {K : Subgroup H} (hK : IsComponentOf K ⊤) {x : H}
    (hxK : x ∈ K) (hxC : x ∉ centralizer (K : Set H)) (α : MulAut H) (hα : α x = x) :
    K.map α.toMonoidHom = K := by
  by_contra hne
  have hK' := SStarTransport.isComponentOf_top_map_mulEquiv α hK
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne K _ hK hK' (Ne.symm hne)
  apply hxC
  rw [mem_centralizer_iff]
  intro y hy
  have hxK' : x ∈ K.map α.toMonoidHom := ⟨x, hxK, hα⟩
  have h := commutator_mem_commutator hy hxK'
  rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem fix_component
    (S : Sylow 2 H) {A : Subgroup H} (hcore : CoreHyp H S A)
    {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ] (Φ : Λ →* MulAut H)
    (hfix : ∀ l, ∀ a ∈ A, Φ l a = a) {K : Subgroup H} (hK : IsComponentOf K ⊤) (l : Λ) :
    ∀ y ∈ K, Φ l y = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htype, hind⟩ := N21_of N19 _ (ih_all _) H S A hcore K hK (Nat.lt_succ_self _)
  have hcov := N17_of N11b H S A K hcore.le hcore.comm hcore.closed hcore.oddCore hK htype hind
  have hgold := G41.isGoldType_of_component S hcore.comm hK htype hind hcov
  obtain ⟨x, hxA, hxK, hxC⟩ := exists_mem_inf_not_mem_centralizer S hcore hK hcov
  have hinv : ∀ β ∈ Φ.range, ∀ y ∈ K, β y ∈ K := by
    rintro _ ⟨μ, rfl⟩ y hy
    have h := map_component_eq hK hxK hxC (Φ μ) (hfix μ x hxA)
    have h2 : (Φ μ) y ∈ K.map (Φ μ).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at h2
  set ρ : Λ →* MulAut K := (G3b.restrictAut K Φ.range hinv).comp Φ.rangeRestrict with hρ
  set Ψ : Λ →* MulAut (K ⧸ center K) := (quotCenterHom K).comp ρ with hΨ
  have : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  have hKperf : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hZQ : center (K ⧸ center K) = ⊥ := center_eq_bot_of_simple
  have htypeQ : IsGoldTypeI (K ⧸ center K) ∨ IsTypeL2Odd (K ⧸ center K) ∨
      IsTypeJR (K ⧸ center K) := by
    rcases hgold with hI | ⟨-, hL | hJ⟩
    · exact Or.inl (isGoldTypeI_quotient_center hI hZQ)
    · exact Or.inr (Or.inl hL)
    · exact Or.inr (Or.inr hJ)
  obtain ⟨SL, hSL⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  set SLh : Sylow 2 (K ⧸ center K) := SL.mapSurjective (QuotientGroup.mk'_surjective _)
    with hSLh
  have hfixΩ : ∀ μ, ∀ z ∈ Omega1 (SLh : Subgroup (K ⧸ center K)), Ψ μ z = z := by
    intro μ z hz
    have hle : Omega1 (SLh : Subgroup (K ⧸ center K)) ≤
        (Ψ μ).toMonoidHom.eqLocus (MonoidHom.id _) := by
      refine (closure_le _).mpr ?_
      rintro w ⟨hw, hw2⟩
      rw [hSLh, Sylow.coe_mapSurjective] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      have htS : (t : H) ∈ (S : Subgroup H) ⊓ K := by
        rw [← hSL]
        exact ⟨t, ht, rfl⟩
      have ht2 : (t : H) ^ 2 ∈ centralizer (K : Set H) := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw2
        rw [mem_centralizer_iff]
        intro y hy
        have h' := congrArg Subtype.val (mem_center_iff.1 hw2 ⟨y, hy⟩)
        simpa using h'
      obtain ⟨a, ha, hat⟩ := hind.2 t htS ht2
      obtain ⟨x', hx', hax'⟩ := hcov a ha
      have hx'K : x' ∈ K := (mem_inf.mp hx').2
      have hmk : QuotientGroup.mk' (center K) ⟨x', hx'K⟩ = QuotientGroup.mk' (center K) t := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_center_iff]
        intro k
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hk : (x' : H) * k * x'⁻¹ ∈ K := K.mul_mem (K.mul_mem hx'K k.2) (K.inv_mem hx'K)
        have h3 : (t : H)⁻¹ * (x' * k * x'⁻¹) * t = k := by
          rw [← hat _ hk, hax' _ hk]
          group
        calc (k : H) * (x'⁻¹ * t) = x'⁻¹ * t * ((t : H)⁻¹ * (x' * k * x'⁻¹) * t) := by group
          _ = x'⁻¹ * t * k := by rw [h3]
      show Ψ μ (QuotientGroup.mk' (center K) t) = QuotientGroup.mk' (center K) t
      rw [← hmk]
      show ((ρ μ ⟨x', hx'K⟩ : K) : K ⧸ center K) = ((⟨x', hx'K⟩ : K) : K ⧸ center K)
      congr 1
      exact Subtype.ext (hfix μ x' (mem_inf.mp hx').1)
    exact hle hz
  have hΨ1 := action_eq_one_of_type hZQ htypeQ SLh Ψ hfixΩ l
  have hρ1 : ρ l = 1 := by
    apply CFSG.GorensteinWalter.perfect_central_automorphism_eq hKperf
    intro y
    have h := congrArg (fun β : MulAut (K ⧸ center K) => β (y : K ⧸ center K)) hΨ1
    change ((ρ l y : K) : K ⧸ center K) = (y : K ⧸ center K) at h
    rw [QuotientGroup.eq] at h
    have h' : ρ l y * y⁻¹ = y * ((ρ l y)⁻¹ * y)⁻¹ * y⁻¹ := by group
    rw [MulAut.one_apply, h']
    exact (inferInstance : (center K).Normal).conj_mem _ (inv_mem h) y
  intro y hy
  have h := congrArg (fun β : MulAut K => ((β ⟨y, hy⟩ : K) : H)) hρ1
  exact h

theorem fix_of_coreHyp
    (S : Sylow 2 H) {A : Subgroup H} (hcore : CoreHyp H S A)
    {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ] (Φ : Λ →* MulAut H)
    (hfix : ∀ l, ∀ a ∈ A, Φ l a = a) (l : Λ) : Φ l = 1 := by
  obtain ⟨h1, h2, -⟩ :=
    coreStatement H S A hcore.le hcore.comm hcore.closed hcore.gen hcore.oddCore
  have hO2 : CFSG.Open.pCore 2 H ≤ A := by
    rw [h2]
    exact le_sup_left
  have hE : goldschmidtLayer H ≤ (Φ l).toMonoidHom.eqLocus (MonoidHom.id H) :=
    sSup_le fun K hK y hy => fix_component S hcore Φ hfix hK l y hy
  have hF : (⊤ : Subgroup H) ≤ (Φ l).toMonoidHom.eqLocus (MonoidHom.id H) := by
    rw [← h1]
    exact sup_le (fun y hy => hfix l y (hO2 hy)) hE
  ext y
  exact hF (mem_top y)

end CFSG.Goldschmidt75
