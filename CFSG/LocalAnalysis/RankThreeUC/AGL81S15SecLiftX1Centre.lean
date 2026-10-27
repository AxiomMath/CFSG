module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbExtra

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

variable {X : Type} [Group X]

theorem uCore_le_gnV (M T : Subgroup X) : uCore M T ≤ gnV T := by
  rw [uCore_eq_iSup_omegaOneCenterOf]
  refine iSup_le fun m => ?_
  rintro _ ⟨z, hz, rfl⟩
  show (m : X) * z * (m : X)⁻¹ ∈
    Subgroup.normalClosure (CFSG.Quasithin.omegaOneCenterOf T : Set X)
  exact Subgroup.normalClosure_normal.conj_mem z (Subgroup.subset_normalClosure hz) (m : X)

theorem gnC_le_centralizer_uCore (M T : Subgroup X) :
    gnC T ≤ Subgroup.centralizer (uCore M T : Set X) :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (uCore_le_gnV M T))

theorem le_gnC_of_normal {T N : Subgroup X} (hN : N.Normal)
    (h : N ≤ Subgroup.centralizer (CFSG.Quasithin.omegaOneCenterOf T : Set X)) : N ≤ gnC T := by
  haveI := hN
  have h2 : gnV T ≤ Subgroup.centralizer (N : Set X) :=
    Subgroup.normalClosure_le_normal fun z hz => Subgroup.le_centralizer_iff.mp h hz
  exact Subgroup.le_centralizer_iff.mpr h2

private theorem mem_of_toStar_eq {T L M : Subgroup X} {k x : X}
    (hk : k ∈ L ⊓ Subgroup.centralizer (uCore M T : Set X)) (hx : x ∈ L)
    (he : toStar T k = toStar T x) : x ∈ L ⊓ Subgroup.centralizer (uCore M T : Set X) := by
  have he' : (k : X ⧸ gnC T) = x := he
  have hc : k⁻¹ * x ∈ gnC T := QuotientGroup.eq.mp he'
  have h := (L ⊓ Subgroup.centralizer (uCore M T : Set X)).mul_mem hk
    ⟨L.mul_mem (L.inv_mem hk.1) hx, gnC_le_centralizer_uCore M T hc⟩
  rwa [mul_inv_cancel_left] at h

theorem inf_centralizer_uCore_le_comap_centralizer {T L M : Subgroup X}
    (hLn : L.Normal) (hLM : L ≤ M) (hq : CFSG.Open.IsQuasisimple ↥(L.map (toStar T))) :
    L ⊓ Subgroup.centralizer (uCore M T : Set X) ≤
      (Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T))).comap (toStar T) := by
  set K := L ⊓ Subgroup.centralizer (uCore M T : Set X) with hKdef
  set Ls := L.map (toStar T) with hLsdef
  let ρ : ↥L →* ↥Ls := (toStar T).subgroupMap L
  have hρs : Function.Surjective ρ := (toStar T).subgroupMap_surjective L
  have hρv : ∀ x : ↥L, ((ρ x : ↥Ls) : X ⧸ gnC T) = toStar T x := fun _ => rfl
  have hKZ : K ≤ Subgroup.centralizer (CFSG.Quasithin.omegaOneCenterOf T : Set X) :=
    inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (omegaOneCenterOf_le_uCore M T)))
  have hKn : (K.subgroupOf L).Normal := by
    refine ⟨fun k hk l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨-, hkC⟩ := hk
    have hkC' : (k : X) ∈ Subgroup.centralizer (uCore M T : Set X) := hkC
    refine ⟨(l * k * l⁻¹ : ↥L).2, ?_⟩
    show ((l * k * l⁻¹ : ↥L) : X) ∈ Subgroup.centralizer (uCore M T : Set X)
    have hcoe : ((l * k * l⁻¹ : ↥L) : X) = (l : X) * k * (l : X)⁻¹ := by simp
    rw [hcoe, Subgroup.mem_centralizer_iff]
    intro u hu
    have hl : (l : X) ∈ Subgroup.normalizer (uCore M T : Set X) :=
      le_normalizer_uCore M T (hLM l.2)
    have hu' : (l : X)⁻¹ * u * l ∈ uCore M T := (Subgroup.mem_normalizer_iff''.mp hl u).mp hu
    have h := Subgroup.mem_centralizer_iff.mp hkC' _ hu'
    calc u * ((l : X) * k * (l : X)⁻¹) = l * (((l : X)⁻¹ * u * l) * k) * (l : X)⁻¹ := by group
      _ = l * (k * ((l : X)⁻¹ * u * l)) * (l : X)⁻¹ := by rw [h]
      _ = (l : X) * k * (l : X)⁻¹ * u := by group
  set Kb : Subgroup ↥Ls := (K.subgroupOf L).map ρ with hKbdef
  have hKbn : Kb.Normal := hKn.map ρ hρs
  have hKbtop : Kb ≠ ⊤ := by
    intro htop
    have hLK : L ≤ K := fun x hx => by
      obtain ⟨k, hk, hkx⟩ : ρ ⟨x, hx⟩ ∈ Kb := by rw [htop]; exact Subgroup.mem_top _
      exact mem_of_toStar_eq (Subgroup.mem_subgroupOf.mp hk) hx
        (by rw [← hρv, hkx]; exact hρv ⟨x, hx⟩)
    have hLC : L ≤ gnC T := le_gnC_of_normal hLn (hLK.trans hKZ)
    have hbot : Ls = ⊥ := by
      rw [hLsdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hLC
    have hnt : Nontrivial ↥Ls := by
      obtain ⟨a, b, hab⟩ := hq.2.toNontrivial.exists_pair_ne
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨a, b, fun h => hab (by rw [h])⟩
    exact (Subgroup.nontrivial_iff_ne_bot Ls).mp hnt hbot
  have hKbc : Kb ≤ Subgroup.center ↥Ls := by
    rcases liftOf_central_ext_aux1 hq hKbn with h | h
    · exact h
    · exact absurd h hKbtop
  intro k hk
  exact (CFSG.AGLEmbedding.mem_center_subtype_iff (ρ ⟨k, hk.1⟩)).mp
    (hKbc ⟨⟨k, hk.1⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩)

theorem inf_centralizer_uCore_le_gnC_of_le {T L M : Subgroup X} (hLn : L.Normal)
    (hLM : L ≤ M) (hq : CFSG.Open.IsQuasisimple ↥(L.map (toStar T)))
    (hZ : L ⊓ (Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T))).comap (toStar T) ≤
      Subgroup.centralizer (uCore M T : Set X)) :
    L ⊓ Subgroup.centralizer (uCore M T : Set X) ≤ gnC T := by
  haveI := hLn
  haveI : (L.map (toStar T)).Normal := hLn.map (toStar T) (QuotientGroup.mk'_surjective _)
  haveI hCn : (Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T))).Normal := inferInstance
  haveI : ((Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T))).comap (toStar T)).Normal :=
    hCn.comap _
  have hZhn :
      (L ⊓ (Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T))).comap (toStar T)).Normal :=
    inferInstance
  have hZhC := le_gnC_of_normal hZhn (hZ.trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (omegaOneCenterOf_le_uCore M T))))
  exact (le_inf inf_le_left (inf_centralizer_uCore_le_comap_centralizer hLn hLM hq)).trans hZhC

end CFSG.LocalAnalysis.RankThreeUC.S15
