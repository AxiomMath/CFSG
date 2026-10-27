module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreLayer

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ComponentClassification
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem oddQuot_facts {J : Subgroup F} {t : F} (hJ : IsClassical2A7 ⊤ J t) :
    CFSG.IsQuasisimple (↥J ⧸ CFSG.pPrimeCore 2 ↥J) ∧
      CFSG.pPrimeCore 2 (↥J ⧸ CFSG.pPrimeCore 2 ↥J) = ⊥ := by
  have e := QuotientGroup.quotientMulEquivOfEq (CatalogueBAlternating.primeCore_two_eq_oddCore ↥J)
  refine ⟨?_, ?_⟩
  · exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv e hJ.witness.1)
  · have h1 := CFSG.pPrimeCore_map_iso 2 e
    rw [CatalogueBAlternating.primeCore_two_eq_oddCore (↥J ⧸ componentClassificationOddCore ↥J),
      OddCore.quotient_corefree ↥J] at h1
    exact (Subgroup.map_injective e.injective) (by rw [h1, Subgroup.map_bot])

theorem exists_trivial_action_lift {J : Subgroup F} {t z : F} (hJ : IsClassical2A7 ⊤ J t)
    (hzJ : z ∈ Subgroup.normalizer (J : Set F)) (hz2 : z * z = 1)
    (hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) :
    ∃ J₀ : Subgroup F, J₀ ≤ J ∧ (∀ x ∈ J₀, z * x * z⁻¹ = x) ∧ ⁅J₀, J₀⁆ = J₀ ∧
      CFSG.IsQuasisimple (J₀ ⧸ CFSG.pPrimeCore 2 J₀) ∧
      (J₀.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set F))).IsSubnormal ∧
      ∀ x ∈ J, z * x * z⁻¹ = x → IsPGroup 2 (Subgroup.zpowers x) → x ∈ J₀ := by
  classical
  obtain ⟨hJq, hJcore⟩ := oddQuot_facts hJ
  let σ : MulAut ↥J := J.normalizerMonoidHom ⟨z, hzJ⟩
  have hσapp : ∀ x : ↥J, ((σ x : ↥J) : F) = z * (x : F) * z⁻¹ := fun x => rfl
  have hσσ : ∀ x : ↥J, σ (σ x) = x := fun x => by
    apply Subtype.ext
    rw [hσapp, hσapp]
    calc z * (z * (x : F) * z⁻¹) * z⁻¹ = (z * z) * (x : F) * (z * z)⁻¹ := by group
      _ = x := by rw [hz2]; group
  have hJperf : Group.IsPerfect ↥J := hJ.perfect
  have hbarperf : Group.IsPerfect (↥J ⧸ CFSG.pPrimeCore 2 ↥J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  have hTperf : ⁅(⊤ : Subgroup (↥J ⧸ CFSG.pPrimeCore 2 ↥J)), ⊤⁆ = ⊤ :=
    hbarperf.commutator_eq_top
  have hTfix : ∀ y ∈ (⊤ : Subgroup (↥J ⧸ CFSG.pPrimeCore 2 ↥J)), AscFusion.oddQuotAut σ y = y := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [AscFusion.oddQuotAut_mk, QuotientGroup.eq]
    have hmem : ⁅z, (x : F)⁻¹⁆ ∈ oddCoreOf J := hζ _ (J.inv_mem x.2)
    obtain ⟨hmemJ, hmemO⟩ := mem_oddCoreOf_iff.mp hmem
    have e : (σ x)⁻¹ * x = ⟨⁅z, (x : F)⁻¹⁆, hmemJ⟩ := by
      apply Subtype.ext
      simp [hσapp, commutatorElement_def, mul_assoc]
    rw [e, CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact hmemO
  have hTnorm : ∀ y : ↥J ⧸ CFSG.pPrimeCore 2 ↥J, AscFusion.oddQuotAut σ y = y →
      ∀ t ∈ (⊤ : Subgroup (↥J ⧸ CFSG.pPrimeCore 2 ↥J)), y * t * y⁻¹ ∈ (⊤ : Subgroup _) :=
    fun _ _ _ _ => Subgroup.mem_top _
  obtain ⟨L, hLfix, hLperf, hLmap, hLsub, hL2⟩ :=
    AscFusion.exists_perfect_lift_fixed σ hσσ hTperf hTfix hTnorm
  have hT : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥J ⧸ CFSG.pPrimeCore 2 ↥J)) :=
    AscFusion.isQuasisimple_of_mulEquiv Subgroup.topEquiv hJq
  have hTcore : CFSG.pPrimeCore 2 ↥(⊤ : Subgroup (↥J ⧸ CFSG.pPrimeCore 2 ↥J)) = ⊥ := by
    have h1 := CFSG.pPrimeCore_map_iso 2
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥J ⧸ CFSG.pPrimeCore 2 ↥J)) ≃* _)
    rw [hJcore] at h1
    exact (Subgroup.map_injective Subgroup.topEquiv.injective) (by rw [h1, Subgroup.map_bot])
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pPrimeCore 2 ↥L) :=
    AscFusion.isQuasisimple_oddQuot_of_lift hLmap hT hTcore
  set J₀ : Subgroup F := L.map J.subtype with hJ₀
  have hJ₀J : J₀ ≤ J := Subgroup.map_subtype_le _
  refine ⟨J₀, hJ₀J, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : σ x = x := hLfix hx
    have h2 := congrArg Subtype.val h1
    rw [hσapp] at h2
    exact h2
  · rw [hJ₀, ← Subgroup.map_commutator, hLperf]
  · let e : ↥L ≃* ↥J₀ := L.equivMapOfInjective J.subtype J.subtype_injective
    exact AscFusion.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (CFSG.pPrimeCore 2 ↥L) (CFSG.pPrimeCore 2 ↥J₀) e
        (CFSG.pPrimeCore_map_iso 2 e)).symm hLq
  · set C : Subgroup F := J ⊓ Subgroup.centralizer ({z} : Set F) with hC
    have hFJ : ∀ x : ↥(AscFusion.fixSub σ), ((x : ↥J) : F) ∈ C := by
      intro x
      refine ⟨x.1.2, ?_⟩
      have h2 := congrArg Subtype.val (show σ (x : ↥J) = x from x.2)
      rw [hσapp] at h2
      show ((x : ↥J) : F) ∈ Subgroup.centralizer ({z} : Set F)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((x : ↥J) : F) * z = (z * ((x : ↥J) : F) * z⁻¹) * z := by rw [h2]
        _ = z * ((x : ↥J) : F) := by group
    let ι : ↥(AscFusion.fixSub σ) →* ↥C :=
      (J.subtype.comp (AscFusion.fixSub σ).subtype).codRestrict C hFJ
    have hrange : ι.range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxJ : (x : F) ∈ J := x.2.1
      have hxz : (x : F) * z = z * (x : F) :=
        Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      refine ⟨⟨⟨x, hxJ⟩, ?_⟩, rfl⟩
      show σ ⟨x, hxJ⟩ = ⟨x, hxJ⟩
      apply Subtype.ext
      rw [hσapp]
      calc z * (x : F) * z⁻¹ = (x : F) * z * z⁻¹ := by rw [hxz]
        _ = x := by group
    have hsn := AscFusion.isSubnormal_map_of_isSubnormal_range ι hLsub
      (by rw [hrange]; exact Subgroup.IsSubnormal.top)
    have hid : (L.subgroupOf (AscFusion.fixSub σ)).map ι = J₀.subgroupOf C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : ↥J), hy, rfl⟩
      · intro hx
        obtain ⟨ℓ, hℓ, hℓx⟩ := hx
        exact ⟨⟨ℓ, hLfix hℓ⟩, hℓ, Subtype.ext hℓx⟩
    rwa [hid] at hsn
  · intro x hxJ hxz hx2
    have hxfix : (⟨x, hxJ⟩ : ↥J) ∈ AscFusion.fixSub σ := by
      show σ ⟨x, hxJ⟩ = ⟨x, hxJ⟩
      apply Subtype.ext
      rw [hσapp]
      exact hxz
    have hx2' : IsPGroup 2 (Subgroup.zpowers (⟨x, hxJ⟩ : ↥J)) := by
      obtain ⟨n, hn⟩ := hx2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, show orderOf (⟨x, hxJ⟩ : ↥J) = orderOf x from
        (Subgroup.orderOf_coe (⟨x, hxJ⟩ : ↥J)).symm, ← hn, Nat.card_zpowers]
    exact ⟨⟨x, hxJ⟩, hL2 ⟨x, hxJ⟩ hxfix hx2' (Subgroup.mem_top _), rfl⟩

theorem mem_normalizer_of_trivial_action {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {J : Subgroup F} {t : F} (hJ : IsClassical2A7 ⊤ J t) (htz : t * z = z * t)
    (hzJ : z ∈ Subgroup.normalizer (J : Set F)) (hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) {v : F}
    (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v) :
    v ∈ Subgroup.normalizer (K : Set F) := by
  classical
  obtain ⟨J₀, hJ₀J, hJ₀fix, hJ₀perf, hJ₀qs, hJ₀sub, hJ₀2⟩ :=
    exists_trivial_action_lift hJ hzJ hK.mul_self hζ
  have hvJ₀ : v ∈ J₀ := by
    refine hJ₀2 v hvJ ?_ hv2
    calc z * v * z⁻¹ = (v * z) * z⁻¹ := by rw [hvz]
      _ = v := by group
  set Ct : Subgroup F := Subgroup.centralizer ({t} : Set F) with hCt
  set R : Subgroup F := Ct ⊓ Subgroup.centralizer ({z} : Set F) with hR
  have hJ₀R : J₀ ≤ R := by
    intro x hx
    refine ⟨hJ.le_centralizer (hJ₀J hx), ?_⟩
    show x ∈ Subgroup.centralizer ({z} : Set F)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hJ₀fix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hJsn : (J.subgroupOf Ct).IsSubnormal := subnormal_subgroupOf_centralizer hJ
  have hJsnR : (J.subgroupOf R).IsSubnormal := by
    have h1 := hJsn.comap (Subgroup.inclusion (inf_le_left : R ≤ Ct))
    have h2 : (J.subgroupOf Ct).comap (Subgroup.inclusion (inf_le_left : R ≤ Ct)) =
        J.subgroupOf R := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  set C : Subgroup F := J ⊓ Subgroup.centralizer ({z} : Set F) with hC
  have hCR : ∀ x : ↥C, ((x : ↥C) : F) ∈ R := fun x => ⟨hJ.le_centralizer x.2.1, x.2.2⟩
  let ι : ↥C →* ↥R := C.subtype.codRestrict R hCR
  have hrange : ι.range = J.subgroupOf R := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2.1
    · intro hx
      exact ⟨⟨x, ⟨hx, x.2.2⟩⟩, rfl⟩
  have hsnR : (J₀.subgroupOf R).IsSubnormal := by
    have hsn := AscFusion.isSubnormal_map_of_isSubnormal_range ι hJ₀sub
      (by rw [hrange]; exact hJsnR)
    have hid : (J₀.subgroupOf C).map ι = J₀.subgroupOf R := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxJ₀ : (x : F) ∈ J₀ := hx
        exact ⟨⟨x, ⟨hJ₀J hxJ₀, x.2.2⟩⟩, hxJ₀, rfl⟩
    rwa [hid] at hsn
  exact le_normalizer_of_balance (isUniqueInvolution hJ).sq (isUniqueInvolution hJ).ne_one
    htz.symm hJ₀R hsnR hJ₀perf hJ₀qs hK hvJ₀

end CFSG.ClassicalInvolution.A7Core
