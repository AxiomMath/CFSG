module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HatA6Concl
public import CFSG.Quasithin.Vol2.KGFactC31HeSx

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB
open scoped IsMulCommutative

variable {A : Type} [Group A] [Finite A] {ι : A →* Equiv.Perm (Fin 8330)}

namespace He

theorem Emb.isSporadic
    (hι : Emb ⊤ ι) : IsSporadic .He A := by
  have hrange : ι.range = CFSG.Sporadic.HeldB.heP := by
    rw [MonoidHom.range_eq_map, hι.mapS]
  have e : A ≃* ↥CFSG.Sporadic.HeldB.heP :=
    (MonoidHom.ofInjective hι.inj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨e.trans CFSG.Sporadic.HeldB.heEquivP.symm⟩

private theorem isElemAbelian_comap
    (hι : Emb ⊤ ι) :
    IsElemAbelian 2 ((eSub basis_E).comap ι) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hι.inj ?_)⟩⟩, fun x hx => hι.inj ?_⟩
  · change ι ((a : A) * (b : A)) = ι ((b : A) * (a : A))
    rw [map_mul, map_mul]
    exact eSub_comm basis_E _ _ (Subgroup.mem_comap.mp a.2) (Subgroup.mem_comap.mp b.2)
  · rw [map_pow, map_one, sq]
    exact eSub_sq basis_E _ (Subgroup.mem_comap.mp hx)

private theorem comap_le_normalizer_E
    (hι : Emb ⊤ ι) :
    lGrp.comap ι ≤
      Subgroup.normalizer (((eSub basis_E).comap ι : Subgroup A) : Set A) :=
  comap_le_normalizer (Ls_le.trans inf_le_right)

private theorem card_comap_E
    (hι : Emb ⊤ ι) :
    Nat.card ((eSub basis_E).comap ι) = 64 := by
  rw [hι.card_comap E_le_heP, card_eSub]
  norm_num

theorem normal_comap
    (hι : Emb ⊤ ι) :
    (((eSub basis_E).comap ι).subgroupOf (lGrp.comap ι)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.comap_mono E_le_Ls)).mpr
    (comap_le_normalizer_E hι)

theorem isHat_comap
    (hι : Emb ⊤ ι)
    (hperf : ⁅lGrp, lGrp⁆ = lGrp)
    [(((eSub basis_E).comap ι).subgroupOf (lGrp.comap ι)).Normal] :
    CFSG.Quasithin.IsHat (↥(lGrp.comap ι) ⧸
      ((eSub basis_E).comap ι).subgroupOf (lGrp.comap ι))
      ↥(alternatingGroup (Fin 6)) := by
  have hLsP : lGrp ≤ CFSG.Sporadic.HeldB.heP := Ls_le.trans inf_le_left
  obtain ⟨ψ₀, hψs, hψk, hψR⟩ := ls_alt_data hperf
  let M : Subgroup A := lGrp.comap ι
  let R : Subgroup A := (eSub basis_E).comap ι
  have hmap : M.map ι = lGrp := hι.map_comap hLsP
  let e : ↥lGrp ≃* ↥M :=
    ((M.equivMapOfInjective ι hι.inj).trans (MulEquiv.subgroupCongr hmap)).symm
  have he : ∀ x : ↥M,
      ((e.symm x : ↥lGrp) : Equiv.Perm (Fin 8330)) = ι x := fun _ => rfl
  let ψ : ↥M →* ↥(alternatingGroup (Fin 6)) := ψ₀.comp e.symm.toMonoidHom
  have hψsurj : Function.Surjective ψ := hψs.comp e.symm.surjective
  have hψker : ψ.ker = ψ₀.ker.map e.toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      show ψ₀ (e.symm (e z)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact hz
  have hψk' : Nat.card ψ.ker = 192 := by
    rw [hψker, Subgroup.card_map_of_injective e.injective, hψk]
  have hRle : R.subgroupOf M ≤ ψ.ker := by
    intro x hx
    change (x : A) ∈ (eSub basis_E).comap ι at hx
    rw [Subgroup.mem_comap] at hx
    rw [MonoidHom.mem_ker]
    show ψ₀ (e.symm x) = 1
    exact hψR _ (by rw [he]; exact E_le_bFix hx)
  haveI hRn : (R.subgroupOf M).Normal := normal_comap hι
  let φ : ↥M ⧸ R.subgroupOf M →* ↥(alternatingGroup (Fin 6)) :=
    QuotientGroup.lift _ ψ hRle
  have hφs : Function.Surjective φ := by
    intro σ
    obtain ⟨x, hx⟩ := hψsurj σ
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]; exact hx⟩
  have hRc : Nat.card R = 64 := card_comap_E hι
  have hRM : R ≤ M := Subgroup.comap_mono E_le_Ls
  have hRMc : Nat.card (R.subgroupOf M) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hRc]
  have hcM : Nat.card M = 69120 := by
    change Nat.card ↥(lGrp.comap ι) = 69120
    rw [hι.card_comap hLsP, card_Ls]
  have hcq : Nat.card (↥M ⧸ R.subgroupOf M) = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf M)
    rw [hcM, hRMc] at h1
    omega
  have hφk : Nat.card φ.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      M24.card_alt6, hcq] at h1
    omega
  have hcommM : commutator ↥M = ⊤ := by
    have hcommLs : commutator ↥lGrp = ⊤ := by
      apply Subgroup.map_injective lGrp.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, hperf]
    have h1 : Subgroup.map e.toMonoidHom (commutator ↥lGrp) =
        commutator ↥M := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [hcommLs, Subgroup.map_top_of_surjective _ e.surjective] at h1
    exact h1.symm
  have hperfQ : commutator (↥M ⧸ R.subgroupOf M) = ⊤ := by
    rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (R.subgroupOf M)), ← Subgroup.map_commutator,
      ← _root_.commutator_def, hcommM]
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact isHat_of_surj (CFSG.Quasithin.H13.alternatingGroup_nonabelian (by norm_num))
    hperfQ φ hφs hφk

theorem centralizer_comap_le
    (hι : Emb ⊤ ι) :
    Subgroup.centralizer (((eSub basis_E).comap ι : Subgroup A) : Set A) ≤
      (eSub basis_E).comap ι := by
  intro x hx
  refine mem_E_of_cent (hι.mem_heAutGroup x) fun i => ?_
  change ι x * vW5 i = vW5 i * ι x
  obtain ⟨r, -, hr⟩ := hι.exists_of_mem (E_le_heP (vW5_mem_E i))
  have hrR : r ∈ (eSub basis_E).comap ι := by
    rw [Subgroup.mem_comap, hr]
    exact vW5_mem_E i
  rw [← hr, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx r hrR]

theorem irr_comap
    (hι : Emb ⊤ ι)
    (hperf : ⁅lGrp, lGrp⁆ = lGrp)
    {W : Subgroup A} (hWV : W ≤ (eSub basis_E).comap ι)
    (hLW : lGrp.comap ι ≤ Subgroup.normalizer (W : Set A)) :
    W = ⊥ ∨ W = (eSub basis_E).comap ι := by
  let M : Subgroup A := lGrp.comap ι
  let R : Subgroup A := (eSub basis_E).comap ι
  have hEA : IsElemAbelian 2 R := isElemAbelian_comap hι
  have hLV : M ≤ Subgroup.normalizer (R : Set A) := comap_le_normalizer_E hι
  have hVc : Nat.card R = 64 := card_comap_E hι
  have hC : M ⊓ Subgroup.centralizer (R : Set A) ≤ R :=
    inf_le_right.trans (centralizer_comap_le hι)
  haveI : (R.subgroupOf M).Normal := normal_comap hι
  have hhat : CFSG.Quasithin.IsHat (↥M ⧸ R.subgroupOf M) ↥(alternatingGroup (Fin 6)) :=
    isHat_comap hι hperf
  exact irr_of_hat hEA hLV hVc hC hhat hWV hLW

end He

theorem conclK_he_ref
    (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι)
    (hperf : ⁅lGrp, lGrp⁆ = lGrp)
    (MK : Subgroup A) :
    ConclK A (lGrp.comap ι) ((eSub basis_E).comap ι) MK := by
  have hLsP : lGrp ≤ CFSG.Sporadic.HeldB.heP := Ls_le.trans inf_le_left
  have hmap : (lGrp.comap ι).map ι = lGrp :=
    hι.map_comap hLsP
  have hperf' : ⁅lGrp.comap ι, lGrp.comap ι⁆ =
      lGrp.comap ι := by
    apply Subgroup.map_injective hι.inj
    rw [Subgroup.map_commutator, hmap, hperf]
  haveI : (((eSub basis_E).comap ι).subgroupOf
      (lGrp.comap ι)).Normal := He.normal_comap hι
  exact conclK_of_isHatA6 (Or.inr (He.Emb.isSporadic hι))
    (He.isElemAbelian_comap hι) (Subgroup.comap_mono E_le_Ls)
    (He.comap_le_normalizer_E hι) (He.card_comap_E hι)
    (inf_le_right.trans (He.centralizer_comap_le hι)) hperf'
    (He.isHat_comap hι hperf) MK

end CFSG.SectionRank.QTK.Insp443

end
