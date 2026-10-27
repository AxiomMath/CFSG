module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
open CFSG.ClassicalInvolution.Nobq (eq_one_or_eq_of_natCard_eq_two)

abbrev TLGrpEquiv (F F' : Type*) [Group F] [Group F'] : Type _ := F ≃* F'

@[expose] def TwinPairAt {F : Type} [Group F] (z : F) : Prop :=
  ∃ (X₁ X₂ : Subgroup F) (u₁ u₂ : F), orderOf z = 2 ∧ Group.IsSolvable ↥X₁ ∧
    Group.IsSolvable ↥X₂ ∧ CFSG.Open.IsSubnormal X₁ (Subgroup.centralizer ({z} : Set F)) ∧
    CFSG.Open.IsSubnormal X₂ (Subgroup.centralizer ({z} : Set F)) ∧ u₁ ∈ X₁ ∧ u₂ ∈ X₂ ∧
    orderOf u₁ = 4 ∧ orderOf u₂ = 4 ∧ u₁ * u₁ = z ∧ u₂ * u₂ = z ∧ u₂ ∉ Subgroup.zpowers u₁

theorem twinPair_iff_exists {F : Type} [Group F] : TwinPair F ↔ ∃ z : F, TwinPairAt z :=
  ⟨fun ⟨z, X₁, X₂, u₁, u₂, h⟩ => ⟨z, X₁, X₂, u₁, u₂, h⟩,
    fun ⟨z, X₁, X₂, u₁, u₂, h⟩ => ⟨z, X₁, X₂, u₁, u₂, h⟩⟩

theorem TwinPairAt.map {F G : Type} [Group F] [Group G] (ψ : F ≃* G) {z : F}
    (h : TwinPairAt z) : TwinPairAt (ψ z) := by
  obtain ⟨X₁, X₂, u₁, u₂, hz, hs₁, hs₂, hn₁, hn₂, hu₁, hu₂, ho₁, ho₂, hq₁, hq₂, hne⟩ := h
  have hc : (Subgroup.centralizer ({z} : Set F)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ z} : Set G) := by
    simpa using map_centralizer_mulEquiv ψ.symm (ψ z)
  have hsolv : ∀ X : Subgroup F, Group.IsSolvable ↥X → Group.IsSolvable ↥(X.map ψ.toMonoidHom) :=
    fun X hX => by
      haveI := hX
      exact solvable_of_surjective
        (f := (Subgroup.equivMapOfInjective X ψ.toMonoidHom ψ.injective).toMonoidHom)
        (Subgroup.equivMapOfInjective X ψ.toMonoidHom ψ.injective).surjective
  refine ⟨X₁.map ψ.toMonoidHom, X₂.map ψ.toMonoidHom, ψ u₁, ψ u₂, ?_, hsolv _ hs₁, hsolv _ hs₂,
    ?_, ?_, Subgroup.mem_map_of_mem _ hu₁, Subgroup.mem_map_of_mem _ hu₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hz
  · rw [← hc]; exact hn₁.map ψ.toMonoidHom
  · rw [← hc]; exact hn₂.map ψ.toMonoidHom
  · rw [MulEquiv.orderOf_eq]; exact ho₁
  · rw [MulEquiv.orderOf_eq]; exact ho₂
  · rw [← map_mul, hq₁]
  · rw [← map_mul, hq₂]
  · intro hmem
    apply hne
    have hmem' : ψ.toMonoidHom u₂ ∈ (Subgroup.zpowers u₁).map ψ.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      exact hmem
    exact (Subgroup.mem_map_iff_mem ψ.injective).1 hmem'

theorem not_twinPair_of_quasi {F G : Type} [Group F] [Group G] [Finite G] (e : TLGrpEquiv F G)
    (z₀ : G) (hz₀ : orderOf z₀ = 2) {Q : Type} [Group Q]
    (e₀ : TLGrpEquiv ↥(Subgroup.centralizer ({z₀} : Set G)) Q) (hq : CFSG.Open.IsQuasisimple Q)
    (hcen : Nat.card (Subgroup.center Q) = 2)
    (hcov : ∀ z : G, orderOf z = 2 → ∃ c : G, c * z₀ * c⁻¹ = z) : ¬ TwinPair F := by
  intro hF
  obtain ⟨z, hz⟩ := twinPair_iff_exists.mp hF
  have hG : TwinPairAt (e z) := hz.map e
  obtain ⟨c, hc⟩ := hcov (e z) (by
    obtain ⟨-, -, -, -, h2, -⟩ := hG
    exact h2)
  have hG' : TwinPairAt ((MulAut.conj c⁻¹ : MulAut G) (e z)) := hG.map (MulAut.conj c⁻¹)
  have hconj : (MulAut.conj c⁻¹ : MulAut G) (e z) = z₀ := by
    rw [← hc, MulAut.conj_apply]
    group
  rw [hconj] at hG'
  obtain ⟨X₁, X₂, u₁, u₂, -, hs₁, -, hn₁, -, hu₁, -, ho₁, -, hq₁, -, -⟩ := hG'
  set C₀ := Subgroup.centralizer ({z₀} : Set G) with hC₀
  have hqC : CFSG.IsQuasisimple ↥C₀ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm (isQuasisimple_of_open hq)
  have hcomm := commute_of_solvable_subnormal (CFSG.Open.IsSubnormal.refl C₀) hqC hn₁ hs₁
  have hu₁C : u₁ ∈ C₀ := hn₁.le hu₁
  have hz₀C : z₀ ∈ C₀ := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcentU : (⟨u₁, hu₁C⟩ : ↥C₀) ∈ Subgroup.center ↥C₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2 u₁ hu₁)
  have hcentZ : (⟨z₀, hz₀C⟩ : ↥C₀) ∈ Subgroup.center ↥C₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hZcard : Nat.card (Subgroup.center ↥C₀) = 2 := by
    have h1 : Nat.card ↥((Subgroup.center ↥C₀).map e₀.toMonoidHom) =
        Nat.card ↥(Subgroup.center ↥C₀) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective _ e₀.toMonoidHom e₀.injective).toEquiv).symm
    rw [center_map_equiv e₀] at h1
    omega
  have hz1 : z₀ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz₀
    omega
  have hz1' : (⟨⟨z₀, hz₀C⟩, hcentZ⟩ : Subgroup.center ↥C₀) ≠ 1 := fun h1 => hz1 (by
    simpa using congrArg (fun w : Subgroup.center ↥C₀ => ((w : ↥C₀) : G)) h1)
  rcases eq_one_or_eq_of_natCard_eq_two hZcard hz1' ⟨_, hcentU⟩ with h1 | h1
  · have : u₁ = 1 := by simpa using congrArg (fun w : Subgroup.center ↥C₀ => ((w : ↥C₀) : G)) h1
    rw [this, orderOf_one] at ho₁
    omega
  · have hu : u₁ = z₀ := by
      simpa using congrArg (fun w : Subgroup.center ↥C₀ => ((w : ↥C₀) : G)) h1
    have hzz : z₀ * z₀ = 1 := by
      have := pow_orderOf_eq_one z₀
      rwa [hz₀, pow_two] at this
    rw [hu, hzz] at hq₁
    exact hz1 hq₁.symm

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
