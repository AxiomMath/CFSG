module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLTwoEight
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Product

variable {X : Type*} [Group X]

private theorem map_proj_ne_top {p : ℕ} [Fact p.Prime] [Finite X] [IsSimpleGroup X]
    (hpX : p ∣ Nat.card X) {H : Subgroup (X × X)} (S : Sylow p (X × X))
    (hSH : (S : Subgroup (X × X)) ≤ H) (π π' : X × X →* X) (ι : X →* X × X)
    (hπι : ∀ a, π (ι a) = a) (hπ'ι : ∀ a, π' (ι a) = 1) (hker : ∀ y, π' y = 1 → ι (π y) = y)
    (hconj : ∀ h a, h * ι a * h⁻¹ = ι (π h * a * (π h)⁻¹)) (hH : ¬ π'.ker ≤ H) :
    H.map π ≠ ⊤ := by
  intro htop
  set N : Subgroup X := H.comap ι with hNdef
  have hN : N.Normal := ⟨fun a ha x => by
    obtain ⟨h, hh, rfl⟩ := mem_map.mp (htop ▸ mem_top x : x ∈ H.map π)
    show ι (π h * a * (π h)⁻¹) ∈ H
    rw [← hconj]
    exact H.mul_mem (H.mul_mem hh ha) (H.inv_mem hh)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  ·
    obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S π'.ker
    have hcard : Nat.card π'.ker = Nat.card X :=
      Nat.card_congr
        { toFun := fun y => π y
          invFun := fun x => ⟨ι x, MonoidHom.mem_ker.mpr (hπ'ι x)⟩
          left_inv := fun y => Subtype.ext (hker y (MonoidHom.mem_ker.mp y.2))
          right_inv := fun x => hπι x }
    obtain ⟨⟨y, hyP⟩, hy1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (P.ne_bot_of_dvd_card (hcard ▸ hpX))
    have hyS : (y : X × X) ∈ (S : Subgroup (X × X)) ⊓ π'.ker := hP ▸ mem_map_of_mem _ hyP
    have hyι : ι (π y) = y := hker y (MonoidHom.mem_ker.mp y.2)
    have hyN : π y ∈ N := by
      show ι (π y) ∈ H
      rw [hyι]
      exact hSH hyS.1
    rw [hb, mem_bot] at hyN
    apply hy1
    refine Subtype.ext (Subtype.ext ?_)
    simp only [OneMemClass.coe_one]
    rw [← hyι, hyN, map_one]
  · refine hH fun y hy => ?_
    rw [← hker y (MonoidHom.mem_ker.mp hy)]
    exact (ht ▸ mem_top (π y) : π y ∈ N)

theorem isSolvable_of_le_prod {p : ℕ} [Fact p.Prime] [Finite X] [IsSimpleGroup X]
    (hpX : p ∣ Nat.card X) (hsol : ∀ H : Subgroup X, H ≠ ⊤ → Group.IsSolvable H)
    {H : Subgroup (X × X)} (S : Sylow p (X × X)) (hSH : (S : Subgroup (X × X)) ≤ H)
    (h₁ : ¬ (MonoidHom.snd X X).ker ≤ H) (h₂ : ¬ (MonoidHom.fst X X).ker ≤ H) :
    Group.IsSolvable H := by
  haveI := hsol _ (map_proj_ne_top hpX S hSH (MonoidHom.fst X X) (MonoidHom.snd X X)
    (MonoidHom.inl X X) (fun _ => rfl) (fun _ => rfl)
    (fun y hy => Prod.ext rfl (by simpa using hy.symm))
    (fun h a => Prod.ext (by simp) (by simp)) h₁)
  haveI := hsol _ (map_proj_ne_top hpX S hSH (MonoidHom.snd X X) (MonoidHom.fst X X)
    (MonoidHom.inr X X) (fun _ => rfl) (fun _ => rfl)
    (fun y hy => Prod.ext (by simpa using hy.symm) rfl)
    (fun h a => Prod.ext (by simp) (by simp)) h₂)
  let f : H →* H.map (MonoidHom.fst X X) × H.map (MonoidHom.snd X X) :=
    ((MonoidHom.fst X X).subgroupMap H).prod ((MonoidHom.snd X X).subgroupMap H)
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
  have h1 := congrArg (fun z => ((z.1 : X), (z.2 : X))) hxy
  simp only [f, MonoidHom.prod_apply, MonoidHom.subgroupMap_apply_coe, MonoidHom.coe_fst,
    MonoidHom.coe_snd, Prod.mk.injEq] at h1
  exact Subtype.ext (Prod.ext h1.1 h1.2)

end Product

private theorem isComponentOf_top_of_le {Y : Type*} [Group Y] {K L : Subgroup Y} [K.Normal]
    (hLK : L ≤ K) (hLn : (L.subgroupOf K).Normal) (hL : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : IsComponentOf L ⊤ := by
  haveI := hL
  haveI : Group.IsPerfect L := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top L hnab⟩
  exact ⟨le_top, IsSubnormal.step hLK hLn (IsSubnormal.step le_top inferInstance
    (IsSubnormal.refl ⊤)), CFSG.ComponentClassification.Quasisimple.simple_of_perfect L⟩

private theorem isComponentOf_factor {Y X : Type*} [Group Y] [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) {K : Subgroup Y} [K.Normal] (e : K ≃* X × X)
    (ι : X →* X × X) (hι : Function.Injective ι) (hιn : ι.range.Normal) :
    IsComponentOf ((ι.range.map e.symm.toMonoidHom).map K.subtype) ⊤ := by
  set M : Subgroup K := ι.range.map e.symm.toMonoidHom with hM
  have hMn : M.Normal := hιn.map _ e.symm.surjective
  have hsub : ((M.map K.subtype).subgroupOf K) = M :=
    comap_map_eq_self_of_injective K.subtype_injective M
  let φ : X ≃* M.map K.subtype :=
    (MonoidHom.ofInjective hι).trans ((equivMapOfInjective ι.range e.symm.toMonoidHom
      e.symm.injective).trans (equivMapOfInjective M K.subtype K.subtype_injective))
  haveI : IsSimpleGroup (M.map K.subtype) := φ.symm.isSimpleGroup
  have hMn' : ((M.map K.subtype).subgroupOf K).Normal := by rw [hsub]; exact hMn
  refine isComponentOf_top_of_le (map_subtype_le M) hMn' inferInstance ?_
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨φ a, φ b, fun h => hab (φ.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem threeFourTwoLTwoEightSq_holds : ThreeFourTwoLTwoEightSq := by
  intro q d hq2 hq3 hd
  obtain ⟨hs, hnab, hout⟩ := lTwoEight_catalog_facts hq2 hq3 hd
  haveI := hs
  haveI := finite_lTwoEight hq2 hq3 hd
  have hZ := CFSG.ComponentClassification.Helpers.center_eq_bot _ hnab
  have hSC : CFSG.ComponentClassification.AutL2Facts.SimpleCentreless
      (TauCeti.CFSGIndex.lie d).Group := by
    refine ⟨fun N hN => by haveI := hN; exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N,
      fun z hz => ?_, ?_⟩
    · have hz' : z ∈ center (TauCeti.CFSGIndex.lie d).Group :=
        mem_center_iff.mpr fun g => (hz g).symm
      rwa [hZ, mem_bot] at hz'
    · obtain ⟨a, b, hab⟩ := hnab
      by_cases ha : a = 1
      · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
      · exact ⟨a, ha⟩
  refine threeFourTwoNoneAt_of_forall_of_center_eq_bot ?_
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c167_frame_outer_square_solvable hSC hout) ?_
  · rw [Subgroup.center_prod, hZ, bot_prod_bot]
  intro Y _ _ K Y₀ E R hp _ hKn hKX _ _ hcomp _ _ _ _ hRY₀ J hJ hJ1 hJp _ _
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨e⟩ := hKX
  set X := (TauCeti.CFSGIndex.lie d).Group
  set H : Subgroup (X × X) := (Y₀.subgroupOf K).map e.toMonoidHom with hHdef
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have he : Function.Surjective e.toMonoidHom := e.surjective
  have hSH : ((T.mapSurjective he : Sylow 3 (X × X)) : Subgroup (X × X)) ≤ H := by
    rw [Sylow.coe_mapSurjective]
    refine map_mono fun t ht => mem_subgroupOf.mpr (hRY₀ ?_)
    have h : (t : Y) ∈ (R : Subgroup Y) ⊓ K := hT ▸ mem_map_of_mem K.subtype ht
    exact h.1
  have hfac : ∀ (ι : X →* X × X), Function.Injective ι → ι.range.Normal → ¬ ι.range ≤ H := by
    intro ι hι hιn hle
    refine hcomp _ (isComponentOf_factor hnab e ι hι hιn) (map_subtype_le _) ?_
    rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨k, hk, hkx⟩ := mem_map.mp (hle ⟨x, rfl⟩)
    have hk' : e.symm.toMonoidHom (ι x) = k := by
      rw [← hkx]
      exact e.symm_apply_apply k
    rw [hk']
    exact mem_subgroupOf.mp hk
  have hrange₁ : (MonoidHom.inl X X).range = (MonoidHom.snd X X).ker := by
    ext y
    refine ⟨?_, fun hy => ⟨y.1, Prod.ext rfl (MonoidHom.mem_ker.mp hy).symm⟩⟩
    rintro ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr rfl
  have hrange₂ : (MonoidHom.inr X X).range = (MonoidHom.fst X X).ker := by
    ext y
    refine ⟨?_, fun hy => ⟨y.2, Prod.ext (MonoidHom.mem_ker.mp hy).symm rfl⟩⟩
    rintro ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr rfl
  have h₁ : ¬ (MonoidHom.snd X X).ker ≤ H := by
    rw [← hrange₁]
    exact hfac _ (fun a b h => congrArg Prod.fst h) (hrange₁ ▸ inferInstance)
  have h₂ : ¬ (MonoidHom.fst X X).ker ≤ H := by
    rw [← hrange₂]
    exact hfac _ (fun a b h => congrArg Prod.snd h) (hrange₂ ▸ inferInstance)
  have h3X : 3 ∣ Nat.card X := by rw [card_lTwoEight hq2 hq3 hd]; norm_num
  haveI hHsol : Group.IsSolvable H := isSolvable_of_le_prod h3X
    (lTwoEight_isSolvable_of_ne_top hq2 hq3 hd) _ hSH h₁ h₂
  have hKH : Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
    let f : (K ⊓ Y₀ : Subgroup Y) →* H :=
      { toFun := fun x => ⟨e ⟨x, x.2.1⟩, mem_map_of_mem _ (mem_subgroupOf.mpr x.2.2)⟩
        map_one' := Subtype.ext (map_one e)
        map_mul' := fun x y => Subtype.ext (map_mul e ⟨x, x.2.1⟩ ⟨y, y.2.1⟩) }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have h1 : (⟨x, x.2.1⟩ : K) = ⟨y, y.2.1⟩ := e.injective (congrArg Subtype.val hxy)
    have h2 : (x : Y) = y := congrArg (fun z : K => (z : Y)) h1
    exact Subtype.ext h2
  haveI : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective (inclusion_injective hJ)
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJp
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  exact Group.IsPerfect.not_isSolvable J inferInstance

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
