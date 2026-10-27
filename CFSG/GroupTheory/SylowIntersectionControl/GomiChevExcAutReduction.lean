module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAut
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcInvolution
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
public import CFSG.GroupTheory.PCoreOfInvolution
public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.SubgroupCoefficients

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.PerfectAutomorphisms

private theorem map_map_mk'_onCenterQuotient {L : Type} [Group L] (α : MulAut L)
    (H : Subgroup L) :
    (H.map α.toMonoidHom).map (QuotientGroup.mk' (center L)) =
      (H.map (QuotientGroup.mk' (center L))).map (onCenterQuotient α).toMonoidHom := by
  have hcomp : (QuotientGroup.mk' (center L)).comp α.toMonoidHom =
      (onCenterQuotient α).toMonoidHom.comp (QuotientGroup.mk' (center L)) := by
    ext x
    exact (onCenterQuotient_apply_mk α x).symm
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem onCenterQuotient_conj {L : Type} [Group L] (k : L) :
    onCenterQuotient (MulAut.conj k) = MulAut.conj (QuotientGroup.mk' (center L) k) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_inv,
    ← map_mul]

private theorem onCenterQuotient_mul_self {L : Type} [Group L] {α : MulAut L}
    (hα2 : α * α = 1) : onCenterQuotient α * onCenterQuotient α = 1 := by
  show centerQuotientHom L α * centerQuotientHom L α = 1
  rw [← map_mul, hα2, map_one]

private theorem onCenterQuotient_not_conj {L : Type} [Group L] [Group.IsPerfect L]
    {α : MulAut L} (h : ∀ ℓ : L, α ≠ MulAut.conj ℓ) :
    ∀ k : L ⧸ center L, onCenterQuotient α ≠ MulAut.conj k := by
  intro k hk
  obtain ⟨k', hk'⟩ := QuotientGroup.mk'_surjective (center L) k
  have hconj := onCenterQuotient_conj k'
  have h1 : onCenterQuotient (α * (MulAut.conj k')⁻¹) = 1 := by
    show centerQuotientHom L (α * (MulAut.conj k')⁻¹) = 1
    rw [map_mul, map_inv]
    change onCenterQuotient α * (onCenterQuotient (MulAut.conj k'))⁻¹ = 1
    rw [hconj, hk', hk]
    exact mul_inv_cancel _
  have h2 : α * (MulAut.conj k')⁻¹ = 1 := onCenterQuotient_eq_one_imp _ h1
  exact h k' (mul_inv_eq_one.mp h2)

private theorem isGomiAtom_comap_map_ne_top {L : Type} [Group L]
    (hZ : (Nat.card (center L)).Coprime 2) {α : MulAut L} {U : Subgroup L}
    (hU : IsSylowOf 2 U ⊤)
    (hA : ∀ A : Subgroup L, IsGomiAtom ⊤ U A → A ⊔ A.map α.toMonoidHom ≠ ⊤) :
    ∀ Ā : Subgroup (L ⧸ center L),
      IsGomiAtom ⊤ (U.map (QuotientGroup.mk' (center L))) Ā →
        Ā ⊔ Ā.map (onCenterQuotient α).toMonoidHom ≠ ⊤ := by
  intro Ā hAtom
  let A : Subgroup L := Ā.comap (QuotientGroup.mk' (center L))
  have hAtomA : IsGomiAtom ⊤ U A :=
    (isGomiAtom_top_comap_mk'_iff (center L) le_rfl hZ hU.isPGroup Ā).2 hAtom
  have hmap : (A ⊔ A.map α.toMonoidHom).map (QuotientGroup.mk' (center L)) =
      Ā ⊔ Ā.map (onCenterQuotient α).toMonoidHom := by
    have hAπ : A.map (QuotientGroup.mk' (center L)) = Ā :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center L)) Ā
    rw [Subgroup.map_sup, hAπ, map_map_mk'_onCenterQuotient α A, hAπ]
  have hP : normalizer (U : Set L) ≤ A ⊔ A.map α.toMonoidHom :=
    ((isGomiAtom_top_iff_covBy U A).1 hAtomA).le.trans le_sup_left
  rw [← hmap]
  intro htop
  exact hA A hAtomA ((map_mk'_eq_top_iff_of_normalizer_le (center L) le_rfl hP).1 htop)

private theorem pCoreOf_eqLocus_ne_bot_of_conj {L : Type} [Group L] [Finite L]
    (hZ : (Nat.card (center L)).Coprime 2) {ℓ : L}
    (hℓ1 : MulAut.conj ℓ ≠ 1) (hℓ2' : MulAut.conj ℓ * MulAut.conj ℓ = 1) :
    pCoreOf 2 ((MulAut.conj ℓ).toMonoidHom.eqLocus (MonoidHom.id L)) ≠ ⊥ := by
  have hℓ : ℓ ∉ center L := by
    intro hℓc
    apply hℓ1
    ext x
    rw [MulAut.conj_apply]
    change ℓ * x * ℓ⁻¹ = x
    have hcomm : x * ℓ = ℓ * x := Subgroup.mem_center_iff.mp hℓc x
    calc ℓ * x * ℓ⁻¹ = (x * ℓ) * ℓ⁻¹ := by rw [hcomm]
      _ = x := by group
  have hℓ2 : ℓ ^ 2 ∈ center L := by
    have hconj2 : MulAut.conj (ℓ ^ 2) = 1 := by rw [map_pow, pow_two, hℓ2']
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun f : MulAut L => f x) hconj2
    rw [MulAut.conj_apply] at h
    change ℓ ^ 2 * x * (ℓ ^ 2)⁻¹ = x at h
    calc x * ℓ ^ 2 = (ℓ ^ 2 * x * (ℓ ^ 2)⁻¹) * ℓ ^ 2 := by rw [h]
      _ = ℓ ^ 2 * x := by group
  have hEqLocus : (MulAut.conj ℓ).toMonoidHom.eqLocus (MonoidHom.id L) =
      centralizer ({ℓ} : Set L) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    change MulAut.conj ℓ x = x ↔ x * ℓ = ℓ * x
    rw [MulAut.conj_apply]
    constructor
    · intro h
      calc x * ℓ = (ℓ * x * ℓ⁻¹) * ℓ := by rw [h]
        _ = ℓ * x := by group
    · intro h
      calc ℓ * x * ℓ⁻¹ = (x * ℓ) * ℓ⁻¹ := by rw [h]
        _ = x := by group
  rw [hEqLocus]
  exact pCoreOf_centralizer_ne_bot_of_sq_mem_center hZ hℓ hℓ2

private theorem map_eqLocus_subgroupConjugation {G : Type} [Group G] (L : Subgroup G) (z : G)
    (hzL : z ∈ normalizer (L : Set G)) :
    ((CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL).toMonoidHom.eqLocus
        (MonoidHom.id ↥L)).map L.subtype = L ⊓ centralizer ({z} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change (y : G) ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' : ((CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL y : ↥L) : G) =
        z * (y : G) * z⁻¹ := rfl
    have hz : z * (y : G) * z⁻¹ = (y : G) := by
      rw [← hy']
      exact congrArg Subtype.val hy
    calc (y : G) * z = (z * (y : G) * z⁻¹) * z := by rw [hz]
      _ = z * (y : G) := by group
  · rintro ⟨hxL, hxz⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    apply Subtype.ext
    have hxz' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxz
    change z * x * z⁻¹ = x
    calc z * x * z⁻¹ = (x * z) * z⁻¹ := by rw [← hxz']
      _ = x := by group

private theorem map_sup_subgroupConjugation {G : Type} [Group G] (L : Subgroup G) (z : G)
    (hzL : z ∈ normalizer (L : Set G)) (A : Subgroup ↥L) :
    (A ⊔ A.map
        (CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL).toMonoidHom).map
        L.subtype =
      A.map L.subtype ⊔ (A.map L.subtype).map (MulAut.conj z).toMonoidHom := by
  have hcomp : L.subtype.comp
        (CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL).toMonoidHom =
      (MulAut.conj z).toMonoidHom.comp L.subtype := by
    ext x
    rfl
  rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem subgroupConjugation_ne_one {G : Type} [Group G] (L : Subgroup G) (z : G)
    (hzL : z ∈ normalizer (L : Set G)) (hzC : z ∉ centralizer (L : Set G)) :
    CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL ≠ 1 := by
  intro h1
  apply hzC
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hfix : CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL ⟨x, hx⟩ =
      ⟨x, hx⟩ := by rw [h1]; rfl
  have hv : ((CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL ⟨x, hx⟩ : ↥L) : G) =
      z * x * z⁻¹ := rfl
  rw [hfix] at hv
  have hz' : z * x * z⁻¹ = x := hv.symm
  calc x * z = (z * x * z⁻¹) * z := by rw [hz']
    _ = z * x := by group

private theorem subgroupConjugation_mul_self {G : Type} [Group G] (L : Subgroup G) (z : G)
    (hzL : z ∈ normalizer (L : Set G)) (hz2 : z ^ 2 ∈ centralizer (L : Set G)) :
    CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL *
      CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL = 1 := by
  ext x
  change z * (z * (x : G) * z⁻¹) * z⁻¹ = (x : G)
  have hcomm : z ^ 2 * (x : G) = (x : G) * z ^ 2 :=
    (Subgroup.mem_centralizer_iff.mp hz2 (x : G) x.2).symm
  calc z * (z * (x : G) * z⁻¹) * z⁻¹ = z ^ 2 * (x : G) * (z ^ 2)⁻¹ := by
        rw [sq]; group
    _ = (x : G) * z ^ 2 * (z ^ 2)⁻¹ := by rw [hcomm]
    _ = (x : G) := by group

private theorem subgroupConjugation_map_subgroupOf {G : Type} [Group G] (L U : Subgroup G)
    (z : G) (hzL : z ∈ normalizer (L : Set G)) (hzU : z ∈ normalizer (U : Set G)) :
    (U.subgroupOf L).map
        (CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL).toMonoidHom =
      U.subgroupOf L := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hzU (y : G)).mp hy
  · intro x hx
    refine Subgroup.mem_map.mpr
      ⟨(CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL)⁻¹ x, ?_, ?_⟩
    · have hxG : (x : G) ∈ U := hx
      have hinv :
          (((CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL)⁻¹ x : ↥L) : G) =
            z⁻¹ * (x : G) * z := rfl
      change (((CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL)⁻¹ x : ↥L) : G) ∈ U
      rw [hinv]
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hzU) (x : G)).mp hxG
    · exact MulEquiv.apply_symm_apply _ x

theorem pCoreOf_eqLocus_ne_bot_of_gomiExcAutFixed {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (hZ : (Nat.card (center L)).Coprime 2)
    (hK : GomiExcAutFixed (L ⧸ center L)) {α : MulAut L} (hα1 : α ≠ 1) (hα2 : α * α = 1)
    {U : Subgroup L} (hU : IsSylowOf 2 U ⊤) (hαU : U.map α.toMonoidHom = U)
    (hA : ∀ A : Subgroup L, IsGomiAtom ⊤ U A → A ⊔ A.map α.toMonoidHom ≠ ⊤) :
    pCoreOf 2 (α.toMonoidHom.eqLocus (MonoidHom.id L)) ≠ ⊥ := by
  by_cases hin : ∃ ℓ : L, α = MulAut.conj ℓ
  · obtain ⟨ℓ, rfl⟩ := hin
    exact pCoreOf_eqLocus_ne_bot_of_conj hZ hα1 hα2
  · have hSylow : IsSylowOf 2 (U.map (QuotientGroup.mk' (center L))) ⊤ :=
      isSylowOf_top_map_of_surjective (QuotientGroup.mk'_surjective (center L)) hU
    have hfixU : (U.map (QuotientGroup.mk' (center L))).map (onCenterQuotient α).toMonoidHom =
        U.map (QuotientGroup.mk' (center L)) := by
      rw [← map_map_mk'_onCenterQuotient α U, hαU]
    exact pCoreOf_eqLocus_ne_bot_of_quotient (center L) le_rfl hZ hα2
      (onCenterQuotient_apply_mk α)
      (hK (onCenterQuotient α) (U.map (QuotientGroup.mk' (center L)))
        (onCenterQuotient_mul_self hα2) (onCenterQuotient_not_conj (not_exists.mp hin))
        hSylow hfixU (isGomiAtom_comap_map_ne_top hZ hU hA))

theorem gomiChevExcInvolution_of_gomiExcAutFixed
    (h : ∀ (K : Type) [Group K] [Finite K], IsGomiChevExceptional K → GomiExcAutFixed K) :
    GomiChevExcInvolution := by
  intro G _ _ L U z hL hK hU hzL hzU hzC hz2 hA
  let : Group.IsPerfect ↥L := hL.1.1
  have hZ : (Nat.card (center ↥L)).Coprime 2 := IsGomiChevTwo.coprime_card_center hL
  let α : MulAut ↥L := CFSG.BrauerThirdMainTheorem.Helpers.subgroupConjugation L z hzL
  have hα1 : α ≠ 1 := subgroupConjugation_ne_one L z hzL hzC
  have hα2 : α * α = 1 := subgroupConjugation_mul_self L z hzL hz2
  have hU' : IsSylowOf 2 (U.subgroupOf L) ⊤ := (isSylowOf_top_subgroupOf_iff hU.le).2 hU
  have hαU' : (U.subgroupOf L).map α.toMonoidHom = U.subgroupOf L :=
    subgroupConjugation_map_subgroupOf L U z hzL hzU
  have hatoms : ∀ A' : Subgroup ↥L, IsGomiAtom ⊤ (U.subgroupOf L) A' →
      A' ⊔ A'.map α.toMonoidHom ≠ ⊤ := by
    intro A' h
    have hmap := (isGomiAtom_map_subtype_iff L (U.subgroupOf L) A').2 h
    rw [Subgroup.map_subgroupOf_eq_of_le hU.le] at hmap
    have hh := hA (A'.map L.subtype) hmap
    intro htop
    have hsq : (A' ⊔ A'.map α.toMonoidHom).map L.subtype =
        A'.map L.subtype ⊔ (A'.map L.subtype).map (MulAut.conj z).toMonoidHom :=
      map_sup_subgroupConjugation L z hzL A'
    rw [htop] at hsq
    apply hh
    rw [← hsq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have core : pCoreOf 2 (α.toMonoidHom.eqLocus (MonoidHom.id ↥L)) ≠ ⊥ :=
    pCoreOf_eqLocus_ne_bot_of_gomiExcAutFixed hZ (h (↥L ⧸ center ↥L) hK)
      hα1 hα2 hU' hαU' hatoms
  have hEqLocus : (α.toMonoidHom.eqLocus (MonoidHom.id ↥L)).map L.subtype =
      L ⊓ centralizer ({z} : Set G) :=
    map_eqLocus_subgroupConjugation L z hzL
  have hcore := pCoreOf_map_of_injective 2 L.subtype L.subtype_injective
    (α.toMonoidHom.eqLocus (MonoidHom.id ↥L))
  rw [hEqLocus] at hcore
  rw [hcore]
  exact fun hbot => core ((Subgroup.map_eq_bot_iff_of_injective
    (pCoreOf 2 (α.toMonoidHom.eqLocus (MonoidHom.id ↥L))) L.subtype_injective).1 hbot)

end CFSG.GroupTheory
