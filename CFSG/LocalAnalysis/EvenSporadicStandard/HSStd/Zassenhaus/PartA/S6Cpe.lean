module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6Gen
public import CFSG.Walter.Bender1970.S3.FStar
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
public import CFSG.Open.FusionDefs

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem s6_fitting_eq (P : Subgroup G) (hodd : Open.fusionOddCore ↥P = ⊥) :
    CFSG.fittingSubgroupOf P = Open.pCoreOf 2 P := by
  have hp : CFSG.pPrimeCore 2 ↥P = ⊥ := by
    rw [← hodd]
    unfold Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  unfold CFSG.fittingSubgroupOf
  rw [CFSG.Fitting_eq_pcore ↥P 2 hp, s6_pCoreOf_eq]

theorem s6_perm_sq {X : Type*} [Finite X] (hX : Nat.card X ≤ 4) (σ : Equiv.Perm X) {x y : X}
    (hxy : x ≠ y) (hx : σ x = x) (hy : σ y = y) : σ * σ = 1 := by
  classical
  have := Fintype.ofFinite X
  have hsub : σ.support ⊆ (Finset.univ.erase x).erase y := by
    intro z hz
    rw [Equiv.Perm.mem_support] at hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hz (h ▸ hy), fun h => hz (h ▸ hx)⟩
  have hcard : σ.support.card ≤ 2 := by
    have h1 := Finset.card_le_card hsub
    have h2 : ((Finset.univ.erase x).erase y).card = Fintype.card X - 2 := by
      rw [Finset.card_erase_of_mem (by simpa using hxy.symm), Finset.card_erase_of_mem (by simp),
        Finset.card_univ]
      omega
    have h3 : Fintype.card X ≤ 4 := by simpa [Nat.card_eq_fintype_card] using hX
    omega
  have hne := Equiv.Perm.card_support_ne_one σ
  have hcases : σ.support.card = 0 ∨ σ.support.card = 2 := by omega
  rcases hcases with h | h
  · rw [Equiv.Perm.card_support_eq_zero.1 h, mul_one]
  · obtain ⟨a, b, -, rfl⟩ := Equiv.Perm.card_support_eq_two.1 h
    exact Equiv.swap_mul_self a b

theorem s6_cpe (P : Subgroup G) (hodd : Open.fusionOddCore ↥P = ⊥) {u : G}
    (huF : u ∈ Open.pCoreOf 2 P) (hu1 : u ≠ 1) (huP : ∀ p ∈ P, p * u = u * p)
    (hF4 : Nat.card ↥(Open.pCoreOf 2 P) ≤ 4) :
    P ⊓ centralizer (CFSG.GorensteinWalter.componentLayerOf P : Set G) ≤ Open.pCoreOf 2 P := by
  classical
  set F := Open.pCoreOf 2 P with hF
  set E := CFSG.GorensteinWalter.componentLayerOf P with hE
  set R := P ⊓ centralizer (E : Set G) with hR
  have hFit : CFSG.fittingSubgroupOf P = F := s6_fitting_eq P hodd
  have hEn := CFSG.GorensteinWalter.componentLayerOf_isNormalIn P
  have stepA : ∀ x ∈ R, (∀ f ∈ F, x * f = f * x) → x ∈ F := by
    intro x hx hcomm
    have hxP : x ∈ P := hx.1
    have hxE : ∀ e ∈ E, e * x = x * e := fun e he => mem_centralizer_iff.1 hx.2 e he
    have hle : CFSG.GorensteinWalter.generalizedFittingSubgroupOf P ≤ centralizer ({x} : Set G) := by
      show CFSG.fittingSubgroupOf P ⊔ E ≤ _
      refine sup_le ?_ ?_
      · rw [hFit]
        intro f hf
        exact mem_centralizer_singleton_iff.2 (hcomm f hf).symm
      · intro e he
        exact mem_centralizer_singleton_iff.2 (hxE e he)
    have hxc : x ∈ centralizer (CFSG.GorensteinWalter.generalizedFittingSubgroupOf P : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.1 (hle hh)
    have hxF : x ∈ CFSG.GorensteinWalter.generalizedFittingSubgroupOf P :=
      CFSG.GorensteinWalter.centralizer_intersection_fstar_le_fstar P ⟨hxc, hxP⟩
    have := CFSG.Walter.generalizedFittingSubgroupOf_inf_centralizer_le P ⟨hxF, hx.2⟩
    rwa [hFit] at this
  have hRn : ∀ g ∈ P, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    refine ⟨P.mul_mem (P.mul_mem hg hr.1) (P.inv_mem hg), ?_⟩
    show g * r * g⁻¹ ∈ centralizer (E : Set G)
    rw [mem_centralizer_iff]
    intro e he
    have he' : g⁻¹ * e * g⁻¹⁻¹ ∈ E := hEn.2 g⁻¹ (P.inv_mem hg) e he
    have hc := mem_centralizer_iff.1 hr.2 _ he'
    rw [inv_inv] at hc
    calc e * (g * r * g⁻¹) = g * ((g⁻¹ * e * g) * r) * g⁻¹ := by group
      _ = g * (r * (g⁻¹ * e * g)) * g⁻¹ := by rw [hc]
      _ = g * r * g⁻¹ * e := by group
  have hRF : ∀ r ∈ R, ∀ f ∈ F, r * f * r⁻¹ ∈ F := fun r hr f hf => s6_pCoreOf_conj hr.1 hf
  have hF2 : ∀ f ∈ F, ∃ k : ℕ, f ^ (2 ^ k) = 1 := fun f hf => s6_pCoreOf_two hf
  let θ : R →* Equiv.Perm F :=
    { toFun := fun r =>
        { toFun := fun f => ⟨r * f * r⁻¹, hRF r r.2 f f.2⟩
          invFun := fun f => ⟨r⁻¹ * f * r, by
            have := hRF r⁻¹ (R.inv_mem r.2) f f.2
            simpa using this⟩
          left_inv := fun f => Subtype.ext (by simp [mul_assoc])
          right_inv := fun f => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by
        ext f
        simp
      map_mul' := fun a b => by
        ext f
        simp [mul_assoc] }
  have hθ : ∀ r : R, ∀ f : F, ((θ r f : F) : G) = r * f * r⁻¹ := fun r f => rfl
  have hker : ∀ r : R, r ∈ θ.ker → (r : G) ∈ F := by
    intro r hr
    apply stepA r r.2
    intro f hf
    have h1 : θ r ⟨f, hf⟩ = ⟨f, hf⟩ := by
      have := MonoidHom.mem_ker.1 hr
      rw [this]
      rfl
    have h2 : (r : G) * f * (r : G)⁻¹ = f := congrArg Subtype.val h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hKp : IsPGroup 2 θ.ker := by
    intro x
    obtain ⟨k, hk⟩ := hF2 _ (hker x.1 x.2)
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hFcard : Nat.card F ≤ 4 := hF4
  have hRange : IsPGroup 2 θ.range := by
    intro σ
    obtain ⟨r, hr⟩ := σ.2
    refine ⟨1, Subtype.ext ?_⟩
    have hu : (⟨u, huF⟩ : F) ≠ ⟨1, F.one_mem⟩ := fun h => hu1 (congrArg Subtype.val h)
    have hfix : ∀ f : F, (∀ p ∈ P, p * (f : G) = (f : G) * p) → θ r f = f := fun f hf =>
      Subtype.ext (by
        rw [hθ, show ((r⁻¹ : R) : G) = (r : G)⁻¹ from rfl, mul_inv_eq_iff_eq_mul]
        exact hf r r.2.1)
    have h := s6_perm_sq hFcard (θ r) hu
      (hfix ⟨u, huF⟩ (fun p hp => huP p hp)) (hfix ⟨1, F.one_mem⟩ (fun p hp => by simp))
    show (σ : Equiv.Perm F) ^ (2 ^ 1) = 1
    rw [← hr, pow_one, pow_two]
    have h' : θ r * θ r = 1 := h
    exact h'
  obtain ⟨a, ha⟩ := hKp.exists_card_eq
  obtain ⟨b, hb⟩ := hRange.exists_card_eq
  have hcardR : Nat.card R = 2 ^ (b + a) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, hb, ha, pow_add]
  have hR2 : ∀ x ∈ R, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    refine ⟨b + a, ?_⟩
    have h1 := pow_card_eq_one' (G := R) (x := ⟨x, hx⟩)
    rw [hcardR] at h1
    exact congrArg Subtype.val h1
  exact s6_le_pCoreOf inf_le_left hRn hR2


end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
