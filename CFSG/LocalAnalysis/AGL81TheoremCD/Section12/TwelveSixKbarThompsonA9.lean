module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarThompsonCount
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9Local
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalMax
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSolv
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltCase

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarThompson

open Equiv Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
open CFSG.AGLEmbedding.A9Local

private theorem card_nrm_dvd : Nat.card nrm ∣ 1296 := by
  have hfun : Nat.card (ZMod 3 → Perm (ZMod 3)) = 216 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_perm, ZMod.card]
    rfl
  have hperm : Nat.card (Perm (ZMod 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card]
    rfl
  have h1 : Nat.card blockHom.ker ∣ 216 := by
    have h := Subgroup.card_dvd_of_injective innerHom innerHom_injective
    rwa [hfun] at h
  have h2 : Nat.card blockHom.range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card blockHom.range
    rwa [hperm] at h
  have h3 : Nat.card nrm = Nat.card blockHom.ker * Nat.card blockHom.range := by
    rw [← Subgroup.index_ker, card_mul_index]
  rw [h3]
  exact Nat.mul_dvd_mul h1 h2

private theorem card_nrm_inf_dvd :
    Nat.card (nrm ⊓ alternatingGroup Pt : Subgroup (Perm Pt)) ∣ 648 := by
  let s : nrm →* ℤˣ := Perm.sign.comp nrm.subtype
  have hs : Function.Surjective s := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one s⟩
    · exact ⟨⟨NrmMax.negAll, NrmMax.negAll_mem_nrm⟩, NrmMax.sign_negAll⟩
  have hidx : s.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hmap : s.ker.map nrm.subtype = nrm ⊓ alternatingGroup Pt := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Perm.mem_alternatingGroup.2 hy⟩
    · rintro ⟨hx, hxA⟩
      exact ⟨⟨x, hx⟩, Perm.mem_alternatingGroup.1 hxA, rfl⟩
  have h := card_mul_index s.ker
  rw [hidx, ← card_map_of_injective nrm.subtype_injective, hmap] at h
  have hd := card_nrm_dvd
  rw [← h, show (1296 : ℕ) = 648 * 2 by norm_num] at hd
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hd

theorem alt9_facts {Y : Type} [Group Y] [Finite Y] (e : Y ≃* alternatingGroup (Fin 9))
    (P : Sylow 3 Y) :
    Nonempty (↥(P : Subgroup Y) ≃* W3) ∧
      Nat.card (normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y)) ∣ 648 ∧
      ∀ B : Subgroup Y, normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) ≤ B →
        B = normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) ∨ B = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P9 : Sylow 3 (alternatingGroup (Fin 9)) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP9 : (P9 : Subgroup (alternatingGroup (Fin 9))) = (P : Subgroup Y).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  obtain ⟨e9⟩ := sylow_alt_W3 (n := 9) (by norm_num) (by norm_num) P9
  let eW : ↥(P : Subgroup Y) ≃* W3 :=
    (e.subgroupMap (P : Subgroup Y)).trans ((MulEquiv.subgroupCongr hP9.symm).trans e9)
  let ι : Y →* Perm Pt :=
    eqPt.permCongrHom.toMonoidHom.comp ((alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom)
  have hι : Function.Injective ι :=
    eqPt.permCongrHom.injective.comp (Subtype.val_injective.comp e.injective)
  have hιA : ι.range = alternatingGroup Pt := by
    ext τ
    constructor
    · rintro ⟨y, rfl⟩
      rw [Perm.mem_alternatingGroup]
      show Perm.sign (eqPt.permCongr ((e y : alternatingGroup (Fin 9)) : Perm (Fin 9))) = 1
      rw [Perm.sign_permCongr]
      exact Perm.mem_alternatingGroup.1 (e y).2
    · intro hτ
      have hσ : eqPt.permCongrHom.symm τ ∈ alternatingGroup (Fin 9) := by
        rw [Perm.mem_alternatingGroup] at hτ ⊢
        rw [← hτ]
        exact Perm.sign_permCongr eqPt.symm τ
      refine ⟨e.symm ⟨_, hσ⟩, ?_⟩
      show eqPt.permCongrHom ((e (e.symm ⟨_, hσ⟩) : alternatingGroup (Fin 9)) : Perm (Fin 9)) = τ
      rw [MulEquiv.apply_symm_apply]
      exact eqPt.permCongrHom.apply_symm_apply τ
  obtain ⟨g, hg⟩ := exists_conj_le_sylowT (P.isPGroup'.map ι)
  let φ : Y →* Perm Pt := (MulAut.conj g).toMonoidHom.comp ι
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp hι
  have hφP : (P : Subgroup Y).map φ = sylowT := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hg _ ⟨y, hy, rfl⟩
    · rw [card_sylowT, card_map_of_injective hφ, card_of_equiv eW]
  have hφA : φ.range = alternatingGroup Pt := by
    rw [MonoidHom.range_comp, hιA]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (alternatingGroup.normal (α := Pt)).conj_mem y hy g
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · simpa using (alternatingGroup.normal (α := Pt)).conj_mem x hx g⁻¹
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  let e₀ : ↥sylowT ≃* W3 :=
    (MulEquiv.subgroupCongr hφP).symm.trans
      ((equivMapOfInjective (P : Subgroup Y) φ hφ).symm.trans eW)
  have hJ₀ : CFSG.Open.thompsonSubgroup sylowT = baseGroup := by
    rw [thompsonSubgroup_eq_baseIn e₀]
    refine (eq_baseIn_of_comm e₀ baseGroup_le_sylowT ?_ ?_).symm
    · intro a ha b hb
      exact congrArg Subtype.val (isElemAbelian_baseGroup.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · simp [card_baseGroup]
  have hJ : (CFSG.Open.thompsonSubgroup (P : Subgroup Y)).map φ = baseGroup := by
    rw [CFSG.map_ambientMaxCardThompson_of_injective φ _
      (hφ.comp (P : Subgroup Y).subtype_injective), hφP]
    exact hJ₀
  obtain ⟨hc, hm⟩ := normalizer_facts_of_embedding φ hφ hJ (by rw [hφA]; exact card_nrm_inf_dvd)
    (by
      rw [hφA]
      intro M h1 h2
      rcases le_nrm_or_eq (Y := alternatingGroup Pt) le_rfl (by rwa [inf_comm]) h2 with h | h
      · exact Or.inl (le_antisymm (le_inf h h2) h1)
      · exact Or.inr h)
  exact ⟨⟨eW⟩, hc, hm⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarThompson
