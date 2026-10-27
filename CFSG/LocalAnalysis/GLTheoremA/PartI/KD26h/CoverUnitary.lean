module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Cover
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

private theorem kd26h_cu_mulEquiv_of_closed {K H X : Type} [Group K] [Finite K] [Group H]
    [Finite H] [Group X] (hKperf : commutator K = ⊤) (π : H →* X) (hπ : Function.Surjective π)
    (ρ : K →* X) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center K)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (η : E →* H), Function.Surjective η →
      η.ker ≤ Subgroup.center E → ∃ s : H →* E, ∀ g, η (s g) = g)
    (hker : Nat.card π.ker = Nat.card ρ.ker) :
    ∃ φ : H ≃* K, ∀ g, ρ (φ g) = π g := by
  let P : Subgroup (K × H) :=
    MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _))
  let pr : P →* H := (MonoidHom.snd _ _).comp P.subtype
  have hpr : Function.Surjective pr := fun g => by
    obtain ⟨k, hk⟩ := hρ (π g)
    exact ⟨⟨(k, g), hk⟩, rfl⟩
  have hprk : pr.ker ≤ Subgroup.center P := by
    intro x hx
    have hx2 : (x : K × H).2 = 1 := hx
    have hxP : ρ (x : K × H).1 = π (x : K × H).2 := x.2
    have hx1 : (x : K × H).1 ∈ Subgroup.center K := by
      refine hρker ?_
      rw [MonoidHom.mem_ker, hxP, hx2, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.1 hx1 _
    · show (y : K × H).2 * (x : K × H).2 = (x : K × H).2 * (y : K × H).2
      rw [hx2, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ := hsec P pr hpr hprk
  let φ : H →* K := (MonoidHom.fst _ _).comp (P.subtype.comp σ)
  have hφρ : ∀ g, ρ (φ g) = π g := by
    intro g
    have h1 : ρ ((σ g : K × H).1) = π ((σ g : K × H).2) := (σ g).2
    have h2 : (σ g : K × H).2 = g := hσ g
    rw [h2] at h1
    exact h1
  have hφsurj : Function.Surjective φ := by
    have hsup : φ.range ⊔ Subgroup.center K = ⊤ := by
      rw [eq_top_iff]
      intro k _
      obtain ⟨g, hg⟩ := hπ (ρ k)
      have hz : (φ g)⁻¹ * k ∈ Subgroup.center K := by
        refine hρker ?_
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφρ, hg, inv_mul_cancel]
      have hk : k = φ g * ((φ g)⁻¹ * k) := by group
      rw [hk]
      exact Subgroup.mul_mem_sup ⟨g, rfl⟩ hz
    exact MonoidHom.range_eq_top.1
      ((CFSG.SectionRank.perfect_central_supplement (Group.isPerfect_def.2 hKperf)).1 _ hsup)
  exact ⟨MulEquiv.ofBijective φ (bijective_of_cover π hπ ρ hρ φ hφsurj hφρ hker), hφρ⟩

theorem exists_mulEquiv_su_of_cover
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {ℓ f : ℕ} {F : Type} [Field F]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hq : (p, ℓ ^ f) ≠ (3, 2))
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU p (ℓ ^ f) F))
    (hZ : Nat.card (Subgroup.center K) = p) :
    ∃ φ : ↥(StatedSU p (ℓ ^ f) F) ≃* K,
      ∀ g : ↥(StatedSU p (ℓ ^ f) F),
        e (QuotientGroup.mk (φ g)) = (QuotientGroup.mk g : StatedProj (StatedSU p (ℓ ^ f) F)) := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : Finite F := h.finite
  haveI : CharP F ℓ := h.charP
  have hF : Nat.card F = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpodd : ¬ Even p := fun he => hp2 ((Nat.Prime.even_iff hp).1 he)
  set π : ↥(StatedSU p (ℓ ^ f) F) →* StatedProj (StatedSU p (ℓ ^ f) F) :=
    QuotientGroup.mk' ((StatedScalars (Fin p) F).subgroupOf (StatedSU p (ℓ ^ f) F)) with hπdef
  set ρ : K →* StatedProj (StatedSU p (ℓ ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hρdef
  have hρker : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπker : π.ker = (StatedScalars (Fin p) F).subgroupOf (StatedSU p (ℓ ^ f) F) :=
    QuotientGroup.ker_mk' _
  have hker : Nat.card π.ker = Nat.card ρ.ker := by
    rw [hρker, hπker, hZ,
      (CFSG.LinearGroups.unitary_scalar_kernel h.prime hF (n := p) hp.one_le).2.2,
      Nat.gcd_eq_left hpq]
  obtain ⟨φ, hφ⟩ := kd26h_cu_mulEquiv_of_closed hK.1 π (QuotientGroup.mk'_surjective _) ρ
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hρker.le
    (fun E _ _ η hη hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hF h.one_le
        hp3 hpodd hq hη hcen) hker
  exact ⟨φ, hφ⟩

end CFSG.LocalAnalysis.GLTheoremA
