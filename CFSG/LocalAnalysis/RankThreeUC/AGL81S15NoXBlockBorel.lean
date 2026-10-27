module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic
public import CFSG.Quasithin.Background.C1PackA4

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.GN
open scoped commutatorElement

@[expose] def borelPre {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (Ls : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  ((Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) ⊓ Ls) ⊔
    gnImg T T).comap (toStar T)

theorem noXBlock_borelPre {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (hLI : ∀ x ∈ Subgroup.centralizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) ⊓ Ls, Odd (orderOf x) → ∀ l ∈ Ls, x * l = l * x)
    (hA3 : ∀ (K : Subgroup X),
      K ≤ borelPre T Ls →
      (K.subgroupOf (borelPre T Ls)).IsSubnormal →
      CFSG.AGLEmbedding.InClassXBlock K →
      ¬ K ≤ gnC T →
      gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype →
      CFSG.QuasithinUnique.IsAltType K 3 → False)
    (Y : Subgroup X) (hY : Y ≤ borelPre T Ls)
    (hsub : CFSG.Open.IsSubnormal Y (borelPre T Ls))
    (hblock : CFSG.AGLEmbedding.InClassXBlock Y) : False := by
  classical
  set U : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ Ls with hU
  set B : Subgroup (X ⧸ gnC T) :=
    Subgroup.normalizer (U : Set (X ⧸ gnC T)) ⊓ Ls with hB
  set J : Subgroup X := B.comap (toStar T) with hJ
  set X₁ : Subgroup X := borelPre T Ls with hX₁
  have hsurj : Function.Surjective (toStar T) := QuotientGroup.mk'_surjective (gnC T)
  haveI : Finite (X ⧸ gnC T) := Finite.of_surjective (toStar T) hsurj
  have hJmap : J.map (toStar T) = B :=
    Subgroup.map_comap_eq_self_of_surjective hsurj B
  have hX₁map : X₁.map (toStar T) = B ⊔ gnImg T T := by
    rw [hX₁]
    exact Subgroup.map_comap_eq_self_of_surjective hsurj (B ⊔ gnImg T T)
  have hJker : gnC T ≤ J := by
    have h := MonoidHom.ker_le_comap (toStar T) B
    rwa [QuotientGroup.ker_mk'] at h
  have hX₁_eq_sup : X₁ = J ⊔ T := by
    apply le_antisymm
    · intro x hx
      have hx' : toStar T x ∈ B ⊔ gnImg T T := by
        rw [← hX₁map]
        exact ⟨x, hx, rfl⟩
      have hx'' : toStar T x ∈ (J ⊔ T).map (toStar T) := by
        rw [Subgroup.map_sup, hJmap]
        simpa only [gnImg] using hx'
      obtain ⟨y, hy, hyx⟩ := hx''
      have hdiff : y⁻¹ * x ∈ gnC T := by
        have h1 : toStar T (y⁻¹ * x) = 1 := by
          rw [map_mul, map_inv, hyx]
          simp
        exact (QuotientGroup.eq_one_iff (y⁻¹ * x)).mp h1
      have hdiffJ : y⁻¹ * x ∈ J := hJker hdiff
      have e : x = y * (y⁻¹ * x) := by group
      rw [e]
      exact (J ⊔ T).mul_mem hy (Subgroup.mem_sup_left hdiffJ)
    · refine sup_le ?_ ?_
      · intro x hx
        exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.mem_comap.mp hx))
      · intro t ht
        exact Subgroup.mem_comap.mpr
          (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (toStar T) ht))
  have hTleX₁ : T ≤ X₁ := hX₁_eq_sup ▸ le_sup_right
  have hJleX₁ : J ≤ X₁ := hX₁_eq_sup ▸ le_sup_left
  have hkerX₁ : gnC T ≤ X₁ := hJker.trans hJleX₁
  have hTU : gnImg T T ≤ Subgroup.normalizer (U : Set (X ⧸ gnC T)) := by
    refine (le_inf (Subgroup.le_normalizer) hinv).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hTN_U : gnImg T T ≤
      Subgroup.normalizer ((Subgroup.normalizer (U : Set (X ⧸ gnC T))) :
        Set (X ⧸ gnC T)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmapU : U.map (MulAut.conj t) = U :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hTU ht)
    have hmapU' : U.map (MulAut.conj t).toMonoidHom = U := hmapU
    have h := Subgroup.map_equiv_normalizer_eq (H := U) (f := MulAut.conj t)
    rwa [hmapU'] at h
  have hTB : gnImg T T ≤ Subgroup.normalizer (B : Set (X ⧸ gnC T)) :=
    (le_inf hTN_U hinv).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTJ : T ≤ Subgroup.normalizer (J : Set X) := by
    rw [hJ, ← Subgroup.comap_normalizer_eq_of_surjective B hsurj]
    intro t ht
    exact hTB (Subgroup.mem_map_of_mem (toStar T) ht)
  have hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ X₁ :=
    (pCoreOf_le_gnC hX).trans hkerX₁
  have hT2 : IsPGroup 2 T := hX.sylow.2.1
  have hTstar2 : IsPGroup 2 (gnImg T T) := hT2.map _
  have hU_le_Tstar : U ≤ gnImg T T := by
    intro u hu
    exact (Subgroup.mem_inf.mp hu).1
  have hU2 : IsPGroup 2 U := hTstar2.to_le hU_le_Tstar
  by_cases hYC : Y ≤ gnC T
  · have hsubM : (Y.subgroupOf X₁).IsSubnormal :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hY).1 hsub
    have hYsubC : (Y.subgroupOf (gnC T)).IsSubnormal :=
      CFSG.QuasithinUnique.Vol2Native.L239.isSubnormal_subgroupOf_of_le hYC hkerX₁ hsubM
    have hYgnC : CFSG.Open.IsSubnormal Y (gnC T) :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hYC).2 hYsubC
    have hgnCtop : CFSG.Open.IsSubnormal (gnC T) ⊤ :=
      CFSG.Open.IsSubnormal.of_mathlib (gnC_normal T).isSubnormal
    exact hX.noXBlock Y (hYgnC.trans hgnCtop) hblock
  · have hsubM : (Y.subgroupOf X₁).IsSubnormal :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hY).1 hsub
    have hblock2 : CFSG.QuasithinUnique.IsBlock2 X₁ Y := ⟨hblock.1, hY, hsubM⟩
    have hYleSup : Y ≤ J ⊔ T := by
      rw [← hX₁_eq_sup]
      exact hY
    have hYJ : Y ≤ J :=
      CFSG.QuasithinUnique.Vol2Native.L239.le_of_isShort2_of_le_sup hT2 hTJ hblock.1 hYleSup
    have hYstarB : gnImg T Y ≤ B := by
      rw [gnImg]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact Subgroup.mem_comap.mp (hYJ hk)
    have hB_le_Ls : B ≤ Ls := by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).2
    have hYstarLs : gnImg T Y ≤ Ls := hYstarB.trans hB_le_Ls
    have hYstarSup : gnImg T Y ≤ B ⊔ gnImg T T :=
      fun y hy => Subgroup.mem_sup_left (hYstarB hy)
    have hYstarSubOpen : CFSG.Open.IsSubnormal (gnImg T Y) (B ⊔ gnImg T T) := by
      have hmap := CFSG.Open.IsSubnormal.map (toStar T) hsub
      rw [hX₁map] at hmap
      simpa [gnImg] using hmap
    have hYstarSub : ((gnImg T Y).subgroupOf (B ⊔ gnImg T T)).IsSubnormal :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hYstarSup).1 hYstarSubOpen
    have hYstarOdd : gnImg T Y ≤
        Subgroup.closure {x : X ⧸ gnC T | x ∈ gnImg T Y ∧ Odd (orderOf x)} :=
      gnImg_le_closure_odd
        (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.le_closure_odd_of_isShort2 hblock.1)
    have hB_le_NU : B ≤ Subgroup.normalizer (U : Set (X ⧸ gnC T)) := by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).1
    have hU_le_sup : U ≤ B ⊔ gnImg T T := fun u hu =>
      Subgroup.mem_sup_right (hU_le_Tstar hu)
    have hH_le_NU : B ⊔ gnImg T T ≤ Subgroup.normalizer (U : Set (X ⧸ gnC T)) :=
      sup_le hB_le_NU hTU
    have hU_NYstar : U ≤ Subgroup.normalizer (gnImg T Y : Set (X ⧸ gnC T)) :=
      le_normalizer_of_isSubnormal_of_odd (H := B ⊔ gnImg T T) (K := gnImg T Y) (R := U)
        hYstarSup hYstarSub hYstarOdd hU_le_sup hH_le_NU hU2
    have hYstar_NU : gnImg T Y ≤ Subgroup.normalizer (U : Set (X ⧸ gnC T)) :=
      hYstarB.trans hB_le_NU
    have hcomm : ⁅U, gnImg T Y⁆ = ⊥ :=
      commutator_gnImg_eq_bot_q hX hQH hblock2 hU2 hYstar_NU hU_NYstar
    have hYstarCU : gnImg T Y ≤ Subgroup.centralizer (U : Set (X ⧸ gnC T)) := by
      have hcomm' : ⁅gnImg T Y, U⁆ = ⊥ := by
        rw [Subgroup.commutator_comm, hcomm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm'
    have hYstarCent : gnImg T Y ≤ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
      refine hYstarOdd.trans ?_
      rw [Subgroup.closure_le]
      rintro x ⟨hxY, hxodd⟩
      change x ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hLI x ⟨hYstarCU hxY, hYstarLs hxY⟩ hxodd l hl).symm
    have hYstarZ : gnImg T Y ≤ (Subgroup.center ↥Ls).map Ls.subtype := by
      intro y hy
      refine Subgroup.mem_map.mpr ⟨⟨y, hYstarLs hy⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hYstarCent hy) (l : X ⧸ gnC T) l.2
    have hYCinf : Y ⊓ gnC T ≤ pCoreOf 2 Y :=
      inf_gnC_le_pCoreOf_q hX hQH hblock2 hYC
    have hcommC : ⁅Y, Y⁆ ≤ gnC T := by
      have hstarComm : ⁅gnImg T Y, gnImg T Y⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_iff.mp (hYstarCent hx) y (hYstarLs hy)
      have hmap : (⁅Y, Y⁆).map (toStar T) = ⁅gnImg T Y, gnImg T Y⁆ := by
        rw [Subgroup.map_commutator]
        rfl
      have hle : ⁅Y, Y⁆ ≤ (toStar T).ker := by
        rw [← Subgroup.map_eq_bot_iff (f := toStar T), hmap, hstarComm]
      rwa [QuotientGroup.ker_mk'] at hle
    have hcommP : ⁅Y, Y⁆ ≤ pCoreOf 2 Y :=
      (le_inf (Subgroup.commutator_le_self Y) hcommC).trans hYCinf
    have hcommSub : _root_.commutator ↥Y ≤ CFSG.pCore 2 ↥Y := by
      rw [← CFSG.Quasithin.C1Pack.pCoreOf_subgroupOf_self Y]
      change _root_.commutator ↥Y ≤ (pCoreOf 2 Y).comap Y.subtype
      rw [← Subgroup.map_le_iff_le_comap (f := Y.subtype)
        (K := _root_.commutator ↥Y) (H := pCoreOf 2 Y)]
      rw [Subgroup.map_subtype_commutator]
      exact hcommP
    have hcommQuot : IsMulCommutative (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommSub
    have hcard3 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 3 := by
      rcases hblock.1.2.2.2.1 with hq | h3
      · exfalso
        obtain ⟨a, b, hab⟩ := hq.2.2
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        refine hab ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (QuotientGroup.mk' (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)))
          (hcommQuot.is_comm.comm a' b')
      · exact h3
    have hAlt : CFSG.QuasithinUnique.IsAltType Y 3 :=
      CFSG.Quasithin.C1Pack.isAltType_three_of_card_three hblock.1 hcard3
    exact hA3 Y hY hsubM hblock hYC hYstarZ hAlt

end CFSG.LocalAnalysis.RankThreeUC.S15
