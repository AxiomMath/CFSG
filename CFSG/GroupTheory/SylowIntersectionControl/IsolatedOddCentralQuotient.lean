module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCoprimeMap
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTrichotomyLocal
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSylow

public section

namespace CFSG.GroupTheory

open Subgroup

open scoped commutatorElement

private theorem frattini_normalizer_map {G Γ : Type*} [Group G] [Group Γ] [Finite G]
    {ψ : G →* Γ} (hψ : Function.Surjective ψ) {H : Subgroup G} (hH : IsPGroup 2 H)
    (hodd : ¬ 2 ∣ H.relIndex ψ.ker) :
    normalizer ((H.map ψ : Subgroup Γ) : Set Γ) = (normalizer (H : Set G)).map ψ := by
  refine CFSG.OddStandard.HigherRank.YamadaG23.lit_normalizer_map (A := H) ψ hψ hH ?_
  rw [sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal]
  exact hodd

private theorem map_le_centralizer_top {L Q : Type*} [Group L] [Group Q] {f : L →* Q}
    (hf : Function.Surjective f) {H M : Subgroup L}
    (hcomm : ∀ k ∈ H, ∀ x : L, ⁅k, x⁆ ∈ M) (hMK : M ≤ f.ker) :
    H.map f ≤ Subgroup.centralizer (⊤ : Set Q) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hc := hMK (hcomm k hk x)
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

private theorem coprime_card_ker_lift {G Γ : Type*} [Group G] [Finite G] [Group Γ]
    {ψ : G →* Γ} {H K : Subgroup G} (hHK : H ≤ K)
    [(H.subgroupOf K ⊓ (ψ.comp K.subtype).ker).Normal]
    (hodd : ¬ 2 ∣ H.relIndex ψ.ker) :
    Nat.Coprime (Nat.card (QuotientGroup.lift (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker)
      (ψ.comp K.subtype) inf_le_right).ker) 2 := by
  have hφker : (ψ.comp K.subtype).ker = (K ⊓ ψ.ker).subgroupOf K := by
    rw [Subgroup.inf_subgroupOf_left]
    ext x
    simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hMdef : H.subgroupOf K ⊓ (ψ.comp K.subtype).ker = (H ⊓ ψ.ker).subgroupOf K := by
    rw [hφker, Subgroup.inf_subgroupOf_left]
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hcard : Nat.card (QuotientGroup.lift (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker)
      (ψ.comp K.subtype) inf_le_right).ker = (H ⊓ ψ.ker).relIndex (K ⊓ ψ.ker) := by
    have hker2 : (QuotientGroup.lift (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker)
        (ψ.comp K.subtype) inf_le_right).ker = (ψ.comp K.subtype).ker.map
        (QuotientGroup.mk' (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker)) :=
      QuotientGroup.ker_lift (N := H.subgroupOf K ⊓ (ψ.comp K.subtype).ker)
        (φ := ψ.comp K.subtype) (HN := inf_le_right)
    rw [hker2, ← Subgroup.relIndex_ker (f := (QuotientGroup.mk' (H.subgroupOf K ⊓
        (ψ.comp K.subtype).ker) : ↥K →* _)) (K := (ψ.comp K.subtype).ker),
      QuotientGroup.ker_mk', hMdef, hφker, Subgroup.relIndex_subgroupOf inf_le_left]
  have hdvd : (H ⊓ ψ.ker).relIndex (K ⊓ ψ.ker) ∣ H.relIndex ψ.ker := by
    have h1 : (H ⊓ ψ.ker).relIndex (K ⊓ ψ.ker) ∣ (H ⊓ ψ.ker).relIndex ψ.ker :=
      ⟨_, (Subgroup.relIndex_mul_relIndex (H ⊓ ψ.ker) (K ⊓ ψ.ker) ψ.ker
        (inf_le_inf hHK le_rfl) inf_le_right).symm⟩
    rwa [Subgroup.inf_relIndex_right] at h1
  rw [Nat.coprime_two_right]
  exact Nat.not_even_iff_odd.mp fun he => hodd (he.two_dvd.trans (hcard.symm ▸ hdvd))

private theorem ker_lift_le_centralizer {G Γ : Type*} [Group G] [Group Γ] {ψ : G →* Γ}
    {H K : Subgroup G} (hKN : K ≤ normalizer (H : Set G))
    [(H.subgroupOf K ⊓ (ψ.comp K.subtype).ker).Normal]
    (hcent : ⁅ψ.ker ⊓ normalizer (H : Set G), normalizer (H : Set G)⁆ ≤ H) :
    (⊤ : Subgroup (↥K ⧸ (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker))) ⊓
      (QuotientGroup.lift (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker) (ψ.comp K.subtype)
        inf_le_right).ker ≤ Subgroup.centralizer ⊤ := by
  let M : Subgroup ↥K := H.subgroupOf K ⊓ (ψ.comp K.subtype).ker
  let f : ↥K →* ↥K ⧸ M := QuotientGroup.mk' M
  let f₂ : (↥K ⧸ M) →* Γ := QuotientGroup.lift M (ψ.comp K.subtype) inf_le_right
  have hφker : (ψ.comp K.subtype).ker = (K ⊓ ψ.ker).subgroupOf K := by
    rw [Subgroup.inf_subgroupOf_left]
    ext x
    simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hMdef : M = (H ⊓ ψ.ker).subgroupOf K := by
    rw [show M = H.subgroupOf K ⊓ (ψ.comp K.subtype).ker from rfl, hφker,
      Subgroup.inf_subgroupOf_left]
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hcomm : ∀ k ∈ (ψ.comp K.subtype).ker, ∀ x : ↥K, ⁅k, x⁆ ∈ M := by
    intro k hk x
    have hkψ : ψ (k : G) = 1 := MonoidHom.mem_ker.mp hk
    rw [hMdef, Subgroup.mem_subgroupOf]
    refine ⟨hcent (Subgroup.commutator_mem_commutator ⟨MonoidHom.mem_ker.mpr hkψ, hKN k.2⟩
      (hKN x.2)), ?_⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [show (↑⁅k, x⁆ : G) = ⁅(k : G), (x : G)⁆ from rfl, map_commutatorElement, hkψ]
    simp
  have hker : f₂.ker = (ψ.comp K.subtype).ker.map f :=
    QuotientGroup.ker_lift (N := M) (φ := ψ.comp K.subtype) (HN := inf_le_right)
  rw [inf_eq_right.mpr le_top,
    show QuotientGroup.lift (H.subgroupOf K ⊓ (ψ.comp K.subtype).ker) (ψ.comp K.subtype)
      inf_le_right = f₂ from rfl, hker]
  exact map_le_centralizer_top (QuotientGroup.mk'_surjective M) hcomm
    (le_of_eq (QuotientGroup.ker_mk' M).symm)

private theorem isPIsolatedOver_quotient_coprime_central {L Γ : Type*} [Group L] [Finite L]
    [Group Γ] [Finite Γ] {φ : L →* Γ} {H : Subgroup L} [hHn : H.Normal]
    (h : IsPIsolatedOver 2 (⊤ : Subgroup L) H) (hH : IsPGroup 2 H)
    (hcop : Nat.Coprime (Nat.card
      (QuotientGroup.lift (H ⊓ φ.ker) φ inf_le_right).ker) 2)
    (hcent : (⊤ : Subgroup (L ⧸ (H ⊓ φ.ker))) ⊓
      (QuotientGroup.lift (H ⊓ φ.ker) φ inf_le_right).ker ≤ Subgroup.centralizer ⊤) :
    IsPIsolatedOver 2 ((⊤ : Subgroup L).map φ) (H.map φ) := by
  let M : Subgroup L := H ⊓ φ.ker
  let f : L →* L ⧸ M := QuotientGroup.mk' M
  let f₂ : (L ⧸ M) →* Γ := QuotientGroup.lift M φ inf_le_right
  have hMp : IsPGroup 2 M := hH.to_le inf_le_left
  have h3 : IsPIsolatedOver 2 (⊤ : Subgroup (L ⧸ M)) (H.map f) := by
    have h1 := (isPIsolatedOver_map_iff (p := 2) (f := f) (QuotientGroup.mk'_surjective M)
      (by rw [QuotientGroup.ker_mk']; exact hMp)
      (by rw [QuotientGroup.ker_mk']; exact inf_le_left) le_top).mpr h
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)] at h1
  have hbarN : (H.map f).Normal := hHn.map f (QuotientGroup.mk'_surjective M)
  have hp : 2 ∣ (H.map f).relIndex (⊤ : Subgroup (L ⧸ M)) :=
    IsPIsolatedOver.dvd_relIndex h3 (hH.map f) le_top
      (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hbarN).symm)
  have hfinal := IsPIsolatedOver.map_of_coprime_ker (p := 2) (φ := f₂) hcop h3 (hH.map f)
    (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hbarN).symm) le_top le_top
    (by simp) hp hcent
  have hcomp : f₂.comp f = φ := QuotientGroup.lift_comp_mk' (N := M) φ inf_le_right
  have hmap1 : (⊤ : Subgroup (L ⧸ M)).map f₂ = (⊤ : Subgroup L).map φ := by
    rw [← Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective M), Subgroup.map_map,
      hcomp]
  have hmap2 : (H.map f).map f₂ = H.map φ := by
    rw [Subgroup.map_map, hcomp]
  rw [hmap1, hmap2] at hfinal
  exact hfinal

private theorem isPIsolatedOver_map_of_odd_central_aux {G Γ : Type*} [Group G] [Group Γ]
    [Finite G] [Finite Γ] {ψ : G →* Γ} {H : Subgroup G}
    (h : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hH : IsPGroup 2 H)
    (hodd : ¬ 2 ∣ H.relIndex ψ.ker)
    (hcent : ⁅ψ.ker ⊓ normalizer (H : Set G), normalizer (H : Set G)⁆ ≤ H) :
    IsPIsolatedOver 2 ((normalizer (H : Set G)).map ψ) (H.map ψ) := by
  let K : Subgroup G := normalizer (H : Set G)
  let Ht : Subgroup ↥K := H.subgroupOf K
  let φ : ↥K →* Γ := ψ.comp K.subtype
  have hHt : IsPGroup 2 Ht := hH.comap_subtype
  have hHtN : Ht.Normal :=
    (normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hK : IsPIsolatedOver 2 (⊤ : Subgroup ↥K) Ht := by
    have h1 := (isPIsolatedOver_subgroupOf_iff (p := 2) (H := H) (K := K) (K' := K)
      Subgroup.le_normalizer le_rfl).2 h
    simpa only [Subgroup.subgroupOf_self] using h1
  have hcop : Nat.Coprime (Nat.card
      (QuotientGroup.lift (Ht ⊓ φ.ker) φ inf_le_right).ker) 2 :=
    coprime_card_ker_lift (K := K) (H := H) Subgroup.le_normalizer hodd
  have hcent' : (⊤ : Subgroup (↥K ⧸ (Ht ⊓ φ.ker))) ⊓
      (QuotientGroup.lift (Ht ⊓ φ.ker) φ inf_le_right).ker ≤ Subgroup.centralizer ⊤ :=
    ker_lift_le_centralizer (K := K) (H := H) le_rfl hcent
  have hfinal := isPIsolatedOver_quotient_coprime_central (φ := φ) hK hHt hcop hcent'
  have hmap1 : (⊤ : Subgroup ↥K).map φ = K.map ψ := by
    rw [show φ = ψ.comp K.subtype from rfl, ← Subgroup.map_map, Subgroup.map_top,
      Subgroup.range_subtype]
  have hmap2 : Ht.map φ = H.map ψ := by
    rw [show φ = ψ.comp K.subtype from rfl, show Ht = H.subgroupOf K from rfl,
      ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr Subgroup.le_normalizer]
  rw [hmap1, hmap2] at hfinal
  exact hfinal

theorem IsPIsolatedOver.normalizer_map_of_odd_central {G Γ : Type*} [Group G] [Group Γ]
    [Finite G] [Finite Γ] {ψ : G →* Γ} (hψ : Function.Surjective ψ) {H : Subgroup G}
    (hH : IsPGroup 2 H) (h : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hodd : ¬ 2 ∣ H.relIndex ψ.ker)
    (hcent : ⁅ψ.ker ⊓ normalizer (H : Set G), normalizer (H : Set G)⁆ ≤ H) :
    IsPIsolatedOver 2 (normalizer ((H.map ψ : Subgroup Γ) : Set Γ)) (H.map ψ) := by
  rw [frattini_normalizer_map (ψ := ψ) (H := H) hψ hH hodd]
  exact isPIsolatedOver_map_of_odd_central_aux h hH hodd hcent

end CFSG.GroupTheory
