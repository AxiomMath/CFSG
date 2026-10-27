module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Descend

public section

namespace CFSG.LieType.SeitzGeneration.CoverDerivedPreimage

open CFSG.ComponentClassification.CatalogueBCentralQuotient
open CFSG.ComponentClassification.Helpers

@[expose] noncomputable def coverPi {K G : Type} [Group K] [Group G]
    (θ : K ⧸ Subgroup.center K ≃* G) : K →* G :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))

theorem coverPi_surjective {K G : Type} [Group K] [Group G]
    (θ : K ⧸ Subgroup.center K ≃* G) : Function.Surjective (coverPi θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))

theorem coverPi_ker {K G : Type} [Group K] [Group G]
    (θ : K ⧸ Subgroup.center K ≃* G) :
    (coverPi θ).ker = Subgroup.center K :=
  (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center K)) θ.toMonoidHom
    θ.injective).trans (QuotientGroup.ker_mk' _)

theorem derivedPreimage_isQuasisimple {K C : Type} [Group K] [Group C]
    (π : K →* C) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {J : Subgroup C} (hJ : CFSG.Open.IsQuasisimple J) :
    CFSG.Open.IsQuasisimple (derivedPreimage π J) := by
  have hJn : CFSG.IsQuasisimple J :=
    ⟨⟨hJ.1⟩, hJ.2, quasisimple_central_quotient_nonabelian J hJ⟩
  let H : Subgroup K := J.comap π
  let f : H →* J := preimageRestriction π J
  have hf : Function.Surjective f := preimageRestriction_surjective π hπ J
  have hfk : f.ker ≤ Subgroup.center H := preimageRestriction_kernel_central π hker J
  have hperf : CFSG.IsQuasisimple (commutator H) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hfk hJn
  have hiso : (commutator H) ≃* derivedPreimage π J :=
    Subgroup.equivMapOfInjective (commutator H) H.subtype H.subtype_injective
  have hq : CFSG.IsQuasisimple (derivedPreimage π J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv hiso hperf
  exact ⟨hq.1.commutator_eq_top, hq.2.1⟩

theorem derivedPreimage_centerQuotientEquiv {K C : Type} [Group K] [Group C]
    (π : K →* C) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {J : Subgroup C} [Group.IsPerfect J] :
    Nonempty (derivedPreimage π J ⧸ Subgroup.center (derivedPreimage π J) ≃*
      J ⧸ Subgroup.center J) := by
  haveI hperfD : Group.IsPerfect (derivedPreimage π J) :=
    derivedPreimage_perfect π hπ hker J
  have hle : derivedPreimage π J ≤ J.comap π := by
    rw [derivedPreimage_eq_commutator]
    exact Subgroup.commutator_le_self (J.comap π)
  let f : derivedPreimage π J →* J :=
    { toFun := fun x => ⟨π (x : K), Subgroup.mem_comap.1 (hle x.2)⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : K) (b : K)) }
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : C) ∈ (derivedPreimage π J).map π := by
      rw [derivedPreimage_map π hπ J]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfk : f.ker ≤ Subgroup.center (derivedPreimage π J) := by
    intro x hx
    have hx1 : π (x : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxZ : (x : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.2 hx1)
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using
      (Subgroup.mem_center_iff.1 hxZ (z : K))
  exact ⟨CFSG.HardMathSupport.Dickson.Sec6.I1431.centerQuotEquiv hperfD f hf hfk⟩

theorem comap_map_eq_of_map_eq {K C : Type} [Group K] [Group C]
    (π : K →* C) {J : Subgroup C} {ε : MulAut K} {δ : MulAut C}
    (hεδ : ∀ g ∈ J.comap π, π (ε g) = δ (π g))
    (hεδ' : ∀ g ∈ J.comap π, π (ε⁻¹ g) = δ⁻¹ (π g))
    (hJ : J.map δ.toMonoidHom = J) :
    (J.comap π).map ε.toMonoidHom = J.comap π := by
  have hJ' : J.map δ.symm.toMonoidHom = J := by
    have h := congrArg (Subgroup.map δ.symm.toMonoidHom) hJ
    rw [Subgroup.map_map] at h
    simpa using h.symm
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_comap]
    change π (ε g) ∈ J
    rw [hεδ g hg]
    exact hJ ▸ Subgroup.mem_map_of_mem δ.toMonoidHom hg
  · intro x hx
    refine Subgroup.mem_map.2 ⟨ε⁻¹ x, ?_, by simp⟩
    rw [Subgroup.mem_comap]
    change π (ε⁻¹ x) ∈ J
    rw [hεδ' x hx]
    exact hJ' ▸ Subgroup.mem_map_of_mem δ.symm.toMonoidHom hx

theorem derivedPreimage_map_of_map_eq {K C : Type} [Group K] [Group C]
    (π : K →* C) {J : Subgroup C} {ε : MulAut K} {δ : MulAut C}
    (hεδ : ∀ g ∈ J.comap π, π (ε g) = δ (π g))
    (hεδ' : ∀ g ∈ J.comap π, π (ε⁻¹ g) = δ⁻¹ (π g))
    (hJ : J.map δ.toMonoidHom = J) :
    (derivedPreimage π J).map ε.toMonoidHom = derivedPreimage π J := by
  rw [derivedPreimage_eq_commutator, Subgroup.map_commutator,
    comap_map_eq_of_map_eq π hεδ hεδ' hJ]

theorem derivedPreimage_fixed {K C : Type} [Group K] [Group C]
    (π : K →* C) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {J : Subgroup C} [Group.IsPerfect J] {ε : MulAut K} {δ : MulAut C}
    (hεδ : ∀ g ∈ J.comap π, π (ε g) = δ (π g)) (hfix : ∀ y ∈ J, δ y = y) :
    ∀ x ∈ derivedPreimage π J, ε x = x := by
  haveI : Group.IsPerfect (derivedPreimage π J) :=
    derivedPreimage_perfect π hπ hker J
  have hle : derivedPreimage π J ≤ J.comap π := by
    rw [derivedPreimage_eq_commutator]
    exact Subgroup.commutator_le_self (J.comap π)
  let inc : derivedPreimage π J →* K := (derivedPreimage π J).subtype
  let εinc : derivedPreimage π J →* K := ε.toMonoidHom.comp inc
  have hcomp : π.comp inc = π.comp εinc := by
    ext x
    change π (x : K) = π (ε (x : K))
    rw [hεδ (x : K) (hle x.2)]
    exact (hfix (π (x : K)) (Subgroup.mem_comap.1 (hle x.2))).symm
  have heq : inc = εinc :=
    CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker hcomp
  intro x hx
  have h := congrArg (fun f : derivedPreimage π J →* K => f ⟨x, hx⟩) heq
  exact h.symm

theorem map_mem_centralizer_of_conj_fixed {K C : Type} [Group K] [Group C]
    (π : K →* C) (hπ : Function.Surjective π) {J : Subgroup C} [Group.IsPerfect J]
    {k : K} (hfix : ∀ x ∈ derivedPreimage π J, k * x * k⁻¹ = x) :
    π k ∈ Subgroup.centralizer (J : Set C) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hjm : j ∈ (derivedPreimage π J).map π := by
    rw [derivedPreimage_map π hπ J]
    exact hj
  obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.1 hjm
  have h := congrArg (fun z : K => π z) (hfix x hx)
  rw [map_mul, map_mul, map_inv, hxj] at h
  have h' : π k * j = j * π k := by
    have := congrArg (fun t => t * π k) h
    simpa [mul_assoc] using this
  exact h'.symm

theorem exists_conj_eq_on_derivedPreimage {K C : Type} [Group K] [Group C]
    (π : K →* C) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {J : Subgroup C} [Group.IsPerfect J] {k : K} {y : C} (hy : y ∈ J)
    (h : ∀ g ∈ J.comap π, π (k * g * k⁻¹) = y * π g * y⁻¹) :
    ∃ y' ∈ derivedPreimage π J,
      ∀ x ∈ derivedPreimage π J, k * x * k⁻¹ = y' * x * y'⁻¹ := by
  classical
  obtain ⟨y', hy'D, hy'π⟩ := Subgroup.mem_map.1 (by
    rw [derivedPreimage_map π hπ J]
    exact hy)
  refine ⟨y', hy'D, ?_⟩
  let H : Subgroup K := J.comap π
  have hmem : ∀ p : H,
      (y' * (p : K) * y'⁻¹)⁻¹ * (k * (p : K) * k⁻¹) ∈ Subgroup.center K := by
    intro p
    refine hker (MonoidHom.mem_ker.2 ?_)
    rw [map_mul, map_inv]
    have h1 : π (k * (p : K) * k⁻¹) = y * π (p : K) * y⁻¹ := h (p : K) p.2
    have h2 : π (y' * (p : K) * y'⁻¹) = y * π (p : K) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, hy'π]
    rw [h1, h2, inv_mul_cancel]
  let ψ : H →* Subgroup.center K :=
    { toFun := fun p => ⟨(y' * (p : K) * y'⁻¹)⁻¹ * (k * (p : K) * k⁻¹), hmem p⟩
      map_one' := by
        ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        set c : K := (y' * (a : K) * y'⁻¹)⁻¹ * (k * (a : K) * k⁻¹) with hcdef
        have hc : ∀ g : K, c * g = g * c :=
          fun g => (Subgroup.mem_center_iff.1 (hmem a) g).symm
        change (y' * ((a : K) * (b : K)) * y'⁻¹)⁻¹ *
            (k * ((a : K) * (b : K)) * k⁻¹) =
          c * ((y' * (b : K) * y'⁻¹)⁻¹ * (k * (b : K) * k⁻¹))
        calc (y' * ((a : K) * (b : K)) * y'⁻¹)⁻¹ *
              (k * ((a : K) * (b : K)) * k⁻¹)
            = (y' * (b : K) * y'⁻¹)⁻¹ * c * (k * (b : K) * k⁻¹) := by
              rw [hcdef]; group
          _ = (y' * (b : K) * y'⁻¹)⁻¹ * ((k * (b : K) * k⁻¹) * c) := by
              rw [show (y' * (b : K) * y'⁻¹)⁻¹ * c * (k * (b : K) * k⁻¹) =
                (y' * (b : K) * y'⁻¹)⁻¹ * (c * (k * (b : K) * k⁻¹)) by group]
              rw [hc (k * (b : K) * k⁻¹)]
          _ = c * ((y' * (b : K) * y'⁻¹)⁻¹ * (k * (b : K) * k⁻¹)) := by
              rw [show (y' * (b : K) * y'⁻¹)⁻¹ * ((k * (b : K) * k⁻¹) * c) =
                ((y' * (b : K) * y'⁻¹)⁻¹ * (k * (b : K) * k⁻¹)) * c by group]
              rw [← hc ((y' * (b : K) * y'⁻¹)⁻¹ * (k * (b : K) * k⁻¹))] }
  have hDker : commutator H ≤ ψ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2
      (Subgroup.mem_center_iff.1 (ψ a).2 (ψ b)).symm
  intro x hx
  dsimp only [H, derivedPreimage] at hx
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.1 hx
  have h1 := hDker hd
  rw [MonoidHom.mem_ker] at h1
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_one] at h2
  rw [← hdx]
  exact (inv_mul_eq_one.mp h2).symm

end CFSG.LieType.SeitzGeneration.CoverDerivedPreimage

end
