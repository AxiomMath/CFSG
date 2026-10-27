module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ClassicalInvolution.Q3.TL3Omega
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
public import CFSG.ClassicalInvolution.Asc77.AscSixAEmpty

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def tightCore (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ R ∧ IsPGroup 2 (Subgroup.zpowers x)}

omit [Finite G] in
theorem tightCore_le (R : Subgroup G) : tightCore R ≤ R :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem conjSub_tightCore (R : Subgroup G) (n : G) :
    conjSub n (tightCore R) = tightCore (conjSub n R) := by
  unfold tightCore conjSub
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxR, hx2⟩, rfl⟩
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _
  · rintro ⟨⟨x, hxR, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxR, ?_⟩, rfl⟩
    rw [← MonoidHom.map_zpowers] at hy2
    let e := Subgroup.equivMapOfInjective (Subgroup.zpowers x) (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective
    exact hy2.of_injective e.toMonoidHom e.injective

omit [Finite G] in
theorem conjSub_tightCore_of_mem_normalizer {R : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (R : Set G)) : conjSub n (tightCore R) = tightCore R := by
  rw [conjSub_tightCore, tl3_conjSub_eq_of_mem_normalizer hn]

variable {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.isUniqueInvolution_core (h : TightDatum R S t) :
    IsUniqueInvolution (tightCore R) t := by
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order]; norm_num)
  refine ⟨Subgroup.subset_closure ⟨h.mem_right, ht2⟩, ?_, ?_, ?_⟩
  · intro h1
    have := h.order
    rw [h1, orderOf_one] at this
    norm_num at this
  · rw [← pow_two]
    exact h.order ▸ pow_orderOf_eq_one t
  · intro y hy hyy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
      exact h.eq_of_orderOf_eq_two (tightCore_le R hy) hord

omit [Finite G] in
theorem TightDatum.le_normalizer_core (h : TightDatum R S t) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (tightCore R : Set G) :=
  fun _ hc =>
    mem_normalizer_of_conjSub_eq (conjSub_tightCore_of_mem_normalizer (h.le_normalizer hc))

theorem TightDatum.twinSet_eq (h : TightDatum R S t) :
    twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R} := by
  have huniq := h.isUniqueInvolution_core
  ext J
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨g, rfl⟩, z, hz, hzJ⟩
    have e1 : z = t := hz.eq huniq
    subst e1
    have e2 := hzJ.eq (huniq.conj g)
    have hcomm : g * z = z * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [← e2]
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact conjSub_tightCore_of_mem_normalizer (h.le_normalizer hg)
  · rintro rfl
    exact ⟨CoreAssembly.mem_conjClass_self _, t, huniq, huniq⟩

theorem TightDatum.hypOmegaGen (h : TightDatum R S t) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore R)) :=
  hypOmegaGen_of_datum S h.quat h.mem h.order h.cent h.normal

theorem TightDatum.aEmpty_core (h : TightDatum R S t) :
    AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  intro J hJ hJn zK zJ hzK hzJ
  by_contra hcon
  have hΩ := h.hypOmegaGen
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hInA : InA (CoreAssembly.conjClass (tightCore R)) (tightCore R) J :=
    ⟨hJ, hJn, zK, zJ, hzK, hzJ, hcon⟩
  obtain ⟨u, v, r, t', Kstar, ustar, rstar, -, -, -, -, -, -, -, -, -, -, -, hne, htw, -⟩ :=
    Sec6Gen.l6_4ThreeGen G _ hΩ _ hK J hJ.1 hInA zK zJ hzK hzJ _ _ rfl rfl
  have hmem : Kstar ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [htw]
    exact Or.inr rfl
  rw [h.twinSet_eq] at hmem
  exact hne hmem

theorem TightDatum.aEmpty (h : TightDatum R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), AEmpty (CoreAssembly.conjClass (tightCore R)) J :=
  aEmpty_forall_of_transitive h.hypOmegaGen.conjInvariant
    (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) h.aEmpty_core

end CFSG.ClassicalInvolution.Q3
