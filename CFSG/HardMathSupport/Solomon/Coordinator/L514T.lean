module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

section Core

variable {G : Type*} [Group G] [Finite G] {K X : Subgroup G}

@[expose] noncomputable def l514t_barXMap {J X : Subgroup G} (hJX : J ≤ X) : ↥J →* ↥(barX 3 X J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Subgroup.inclusion hJX)).codRestrict
    (barX 3 X J) (fun x => ⟨⟨x, hJX x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)

omit [Finite G] in
theorem l514t_barXMap_surjective {J X : Subgroup G} (hJX : J ≤ X) : Function.Surjective (l514t_barXMap hJX) := by
  rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
  exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩

theorem l514t_barXMap_ker_le_core {J X : Subgroup G} (hJX : J ≤ X) :
    (l514t_barXMap hJX).ker ≤ GLAPPrimeCore 3 ↥J := by
  set K := (l514t_barXMap hJX).ker with hK
  have hmem : ∀ x ∈ K, (x : G) ∈ GLAPPrimeCoreOf 3 X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h3 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) ⟨(x : G), hJX x.2⟩ = 1 :=
      congrArg Subtype.val hx
    exact (mem_gLAPPrimeCoreOf_iff 3 X _).2 ⟨hJX x.2, (QuotientGroup.eq_one_iff _).1 h3⟩
  have hle : K.map J.subtype ≤ GLAPPrimeCoreOf 3 X := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x hx
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (K.map J.subtype) = Nat.card K :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 (card_gLAPPrimeCoreOf_coprime 3 X)
  exact le_sSup (show K ∈ {N : Subgroup ↥J | N.Normal ∧ Nat.Coprime 3 (Nat.card N)} from
    ⟨inferInstance, hcop⟩)

theorem l514t_barXMap_comap_core (hXK : X ≤ K) :
    (GLAPPrimeCore 3 ↥(barX 3 K X)).comap (l514t_barXMap hXK) = GLAPPrimeCore 3 ↥X := by
  set f := l514t_barXMap hXK with hf
  have hfs : Function.Surjective f := l514t_barXMap_surjective hXK
  apply le_antisymm
  · set O := GLAPPrimeCore 3 ↥(barX 3 K X) with hO
    set M := O.comap f with hM
    have hMn : M.Normal := (GLAPPrimeCore.normal 3 _).comap f
    have hkerM : f.ker ≤ M := fun x hx => by
      rw [hM, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
      exact one_mem _
    let φ : ↥M →* ↥O := (f.comp M.subtype).codRestrict O (fun x => x.2)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hfs y
      exact ⟨⟨x, hy⟩, rfl⟩
    have h1 : Nat.card ↥M = Nat.card ↥O * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    have h2 : Nat.card φ.ker ∣ Nat.card f.ker := by
      have hle : φ.ker.map M.subtype ≤ f.ker := by
        rintro _ ⟨x, hx, rfl⟩
        have : φ x = 1 := hx
        exact congrArg Subtype.val this
      have := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective M.subtype_injective] at this
    have hcopf : Nat.Coprime 3 (Nat.card f.ker) :=
      (coprime_card_gLAPPrimeCore_aux 3 ↥X).coprime_dvd_right
        (Subgroup.card_dvd_of_le (l514t_barXMap_ker_le_core hXK))
    have hcop : Nat.Coprime 3 (Nat.card ↥M) := by
      rw [h1]
      exact Nat.Coprime.mul_right (coprime_card_gLAPPrimeCore_aux 3 _)
        (hcopf.coprime_dvd_right h2)
    exact le_sSup ⟨hMn, hcop⟩
  · intro x hx
    exact map_gLAPPrimeCore_le' 3 f hfs (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)

@[expose] noncomputable def l514t_coreQuotEquiv (hXK : X ≤ K) :
    (↥X ⧸ GLAPPrimeCore 3 ↥X) ≃* (↥(barX 3 K X) ⧸ GLAPPrimeCore 3 ↥(barX 3 K X)) :=
  let g : ↥X →* (↥(barX 3 K X) ⧸ GLAPPrimeCore 3 ↥(barX 3 K X)) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(barX 3 K X))).comp (l514t_barXMap hXK)
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp (l514t_barXMap_surjective hXK)
  have hk : g.ker = GLAPPrimeCore 3 ↥X := by
    rw [← l514t_barXMap_comap_core hXK]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective g hg)

theorem l514t_coreQuotEquiv_mk (hXK : X ≤ K) (x : ↥X) :
    l514t_coreQuotEquiv hXK (QuotientGroup.mk x) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥(barX 3 K X)) (l514t_barXMap hXK x) := rfl

theorem l514t_map_coreQuotEquiv_barX (hXK : X ≤ K) {J : Subgroup G} (hJX : J ≤ X) :
    (barX 3 X J).map (l514t_coreQuotEquiv hXK).toMonoidHom = barX 3 (barX 3 K X) (barX 3 K J) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.1 hx
    refine ⟨l514t_barXMap hXK x, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ⟨⟨x, hXK x.2⟩, Subgroup.mem_subgroupOf.2 hxJ, rfl⟩
  · rintro ⟨⟨z, hzF⟩, hz, rfl⟩
    obtain ⟨⟨j, hjK⟩, hj, hjz⟩ := Subgroup.mem_subgroupOf.1 hz
    have hjJ : j ∈ J := Subgroup.mem_subgroupOf.1 hj
    refine ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨j, hJX hjJ⟩,
      ⟨⟨j, hJX hjJ⟩, Subgroup.mem_subgroupOf.2 hjJ, rfl⟩, ?_⟩
    show QuotientGroup.mk' _ (l514t_barXMap hXK ⟨j, hJX hjJ⟩ : ↥(barX 3 K X)) = _
    congr 1
    exact Subtype.ext hjz

theorem l514t_map_coreQuotEquiv_top (hXK : X ≤ K) :
    (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)).map (l514t_coreQuotEquiv hXK).toMonoidHom = ⊤ :=
  Subgroup.map_top_of_surjective _ (l514t_coreQuotEquiv hXK).surjective

theorem l514t_exists_comp_of_bar (hXK : X ≤ K) {S : Subgroup (barOf 3 K)}
    (hS : GLAPComponent 3 (barX 3 K X) S) :
    ∃ J : Subgroup G, GLAPComponent 3 X J ∧
      (barX 3 X J).map (l514t_coreQuotEquiv hXK).toMonoidHom = barX 3 (barX 3 K X) S := by
  have h1 : IsComponentOf (barX 3 (barX 3 K X) S) ⊤ := hS.2.2.1
  have h2 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (l514t_coreQuotEquiv hXK).symm h1
  rw [Subgroup.map_top_of_surjective _ (l514t_coreQuotEquiv hXK).symm.surjective] at h2
  obtain ⟨J, hJ, hJb⟩ := exists_glaPComponent_barX_eq X h2
  refine ⟨J, hJ, ?_⟩
  rw [hJb, Subgroup.map_map]
  ext y
  simp

theorem l514t_exists_bar_of_comp (hXK : X ≤ K) {J : Subgroup G} (hJ : GLAPComponent 3 X J) :
    ∃ S : Subgroup (barOf 3 K), GLAPComponent 3 (barX 3 K X) S ∧
      (barX 3 X J).map (l514t_coreQuotEquiv hXK).toMonoidHom = barX 3 (barX 3 K X) S := by
  have h1 : IsComponentOf (barX 3 X J) ⊤ := hJ.2.2.1
  have h2 : IsComponentOf ((barX 3 X J).map (l514t_coreQuotEquiv hXK).toMonoidHom) ⊤ := by
    have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (l514t_coreQuotEquiv hXK) h1
    have ht := l514t_map_coreQuotEquiv_top hXK
    rw [show (↑(l514t_coreQuotEquiv hXK) : _ →* _) = (l514t_coreQuotEquiv hXK).toMonoidHom from rfl, ht] at this
    exact this
  obtain ⟨S, hS, hSb⟩ := exists_glaPComponent_barX_eq (barX 3 K X) h2
  exact ⟨S, hS, hSb.symm⟩

theorem l514t_noComp_transfer (hXK : X ≤ K) (h : ∀ S : Subgroup (barOf 3 K), ¬ GLAPComponent 3 (barX 3 K X) S)
    (J : Subgroup G) : ¬ GLAPComponent 3 X J := fun hJ => by
  obtain ⟨S, hS, -⟩ := l514t_exists_bar_of_comp hXK hJ
  exact h S hS

theorem l514t_comp_unique_transfer (hXK : X ≤ K) {S : Subgroup (barOf 3 K)}
    (hS : GLAPComponent 3 (barX 3 K X) S)
    (hu : ∀ S' : Subgroup (barOf 3 K), GLAPComponent 3 (barX 3 K X) S' → S' = S) :
    ∃ J₀ : Subgroup G, GLAPComponent 3 X J₀ ∧ (∀ J, GLAPComponent 3 X J → J = J₀) ∧
      Nonempty (barOf 3 J₀ ≃* barOf 3 S) := by
  obtain ⟨J₀, hJ₀, hJ₀b⟩ := l514t_exists_comp_of_bar hXK hS
  refine ⟨J₀, hJ₀, fun J hJ => ?_, ?_⟩
  · obtain ⟨S', hS', hS'b⟩ := l514t_exists_bar_of_comp hXK hJ
    rw [hu S' hS'] at hS'b
    refine glaPComponent_uniqueAux hJ hJ₀ ?_
    apply Subgroup.map_injective (f := (l514t_coreQuotEquiv hXK).toMonoidHom) (l514t_coreQuotEquiv hXK).injective
    exact hS'b.trans hJ₀b.symm
  · have hp : Nat.Prime 3 := Nat.prime_three
    have e1 := barXEquiv hp hJ₀.2.1
    have e3 := barXEquiv hp hS.2.1
    have e2 : ↥(barX 3 X J₀) ≃* ↥(barX 3 (barX 3 K X) S) :=
      ((barX 3 X J₀).equivMapOfInjective _ (l514t_coreQuotEquiv hXK).injective).trans
        (MulEquiv.subgroupCongr hJ₀b)
    exact ⟨(e1.trans e2).trans e3.symm⟩

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
