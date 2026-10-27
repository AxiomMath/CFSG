module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockSubtype
public import CFSG.ClassicalGroups.SpecialLinear.ComponentBorelQuotient
public import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanInBorel
public import CFSG.GroupTheory.HallTwoPrimeAbelian
public import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15AssemblyHall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15CartanProduct
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bLinBorel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bYsolv
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15X1FactorSolvable

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem k517_4b_rank_ge_three_of_cartan_hall
    {Y : Type} [Group Y] [Finite Y] (hY : Group.IsSolvable Y)
    (C N Hc B : Subgroup Y) (hB : B.Normal)
    (hsup : (C : Set Y) * (N : Set Y) = Set.univ)
    (hHcpi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc)
    (hHallB : ∀ H : Subgroup Y,
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H → H ≤ B)
    (hBcomm : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B))
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (h3 : 3 ≤ CFSG.Open.pRank q Hc)
    (φ : Y →* (X ⧸ gnC T)) (hφ : Function.Injective φ)
    (hC : ∀ H : Subgroup Y, IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H →
      (H ⊓ C).map φ ≤ gnA T T₁ Ls)
    (hN : ∀ H : Subgroup Y, IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H →
      (H ⊓ N).map φ ≤ gnA T T₂ Ls) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  obtain ⟨H, hHall, hfac, hH3⟩ :=
    exists_isHallSubgroup_twoPrime_of_cartan (Y := Y) hY hsup hq hq2 hHcpi h3
  have hHB : H ≤ B := hHallB H hHall
  have hHcomm : IsMulCommutative ↥H :=
    isMulCommutative_of_isHallSubgroup_of_quotient_pCore hB hHall hHB hBcomm
  have hfac' : H.map φ = (H ⊓ C).map φ ⊔ (H ⊓ N).map φ := by
    conv_lhs => rw [hfac]
    rw [Subgroup.map_sup]
  have hH3' : 3 ≤ CFSG.Open.pRank q (H.map φ) :=
    hH3.trans (CFSG.SectionRank.pRank_le_map hq.one_lt φ hφ H)
  have hHcomm' : ∀ a ∈ H.map φ, ∀ b ∈ H.map φ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simpa using congrArg (fun x : ↥H => φ (x : Y))
      (hHcomm.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  have hC' : (H ⊓ C).map φ ≤ gnA T T₁ Ls := hC H hHall
  have hN' : (H ⊓ N).map φ ≤ gnA T T₂ Ls := hN H hHall
  exact one_lt_mS_of_cartan_product (H := H.map φ)
    (C := (H ⊓ C).map φ) (N := (H ⊓ N).map φ)
    hq hHcomm' hfac' hC' hN' hH3'

theorem k517_4b_rank_ge_three_of_X1_of_isSolvable_gnImg_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False)
    (hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)))
    {Hc B : Subgroup ↥(gnImg T (borelPre T Ls))} (hB : B.Normal)
    (hHcpi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc)
    (h3 : 3 ≤ CFSG.Open.pRank q Hc)
    (hHallB : ∀ H : Subgroup ↥(gnImg T (borelPre T Ls)),
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H → H ≤ B)
    (hBcomm : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B))
    (hBLs : B ≤ Ls.subgroupOf (gnImg T (borelPre T Ls))) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  let Y : Subgroup (X ⧸ gnC T) := gnImg T (borelPre T Ls)
  let φ : ↥(borelPre T Ls) →* ↥Y :=
    ((toStar T).comp (Subgroup.subtype (borelPre T Ls))).codRestrict Y
      (fun x => Subgroup.mem_map_of_mem (toStar T) x.2)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hT1Y : T₁ ≤ borelPre T Ls :=
    (hGood.pair.le_center.trans (CFSG.Quasithin.A4.omegaOneCenterOf_le T)).trans
      (t_le_borelPre hX)
  have hCX : (Subgroup.centralizer
      (T₁.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls))).map
      (Subgroup.subtype (borelPre T Ls)) ≤ Subgroup.centralizer (T₁ : Set X) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htY : t ∈ borelPre T Ls := hT1Y ht
    have hmem : (⟨t, htY⟩ : ↥(borelPre T Ls)) ∈ T₁.subgroupOf (borelPre T Ls) := by
      rw [Subgroup.mem_subgroupOf]
      exact ht
    simpa using congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hc ⟨t, htY⟩ hmem)
  have hT2Y : T₂ ≤ borelPre T Ls :=
    hGood.pair.le₂.trans (t_le_borelPre hX)
  have hNX : (Subgroup.normalizer
      (T₂.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls))).map
      (Subgroup.subtype (borelPre T Ls)) ≤ Subgroup.normalizer (T₂ : Set X) := by
    rw [normalizer_map_subgroupOf_eq (borelPre T Ls) T₂ hT2Y]
    exact inf_le_left
  let C : Subgroup ↥Y :=
    (Subgroup.centralizer (T₁.subgroupOf (borelPre T Ls) :
      Set ↥(borelPre T Ls))).map φ
  let N : Subgroup ↥Y :=
    (Subgroup.normalizer (T₂.subgroupOf (borelPre T Ls) :
      Set ↥(borelPre T Ls))).map φ
  have hcomp : (Subgroup.subtype Y).comp φ =
      (toStar T).comp (Subgroup.subtype (borelPre T Ls)) := by
    ext x
    rfl
  have hCmap : C.map (Subgroup.subtype Y) ≤
      gnImg T (Subgroup.centralizer (T₁ : Set X)) := by
    dsimp only [C]
    rw [Subgroup.map_map, hcomp]
    calc
      (Subgroup.centralizer (T₁.subgroupOf (borelPre T Ls) :
          Set ↥(borelPre T Ls))).map
          ((toStar T).comp (Subgroup.subtype (borelPre T Ls))) =
          ((Subgroup.centralizer (T₁.subgroupOf (borelPre T Ls) :
            Set ↥(borelPre T Ls))).map (Subgroup.subtype (borelPre T Ls))).map
            (toStar T) := by rw [Subgroup.map_map]
      _ ≤ (Subgroup.centralizer (T₁ : Set X)).map (toStar T) := Subgroup.map_mono hCX
  have hNmap : N.map (Subgroup.subtype Y) ≤
      gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
    dsimp only [N]
    rw [Subgroup.map_map, hcomp]
    calc
      (Subgroup.normalizer (T₂.subgroupOf (borelPre T Ls) :
          Set ↥(borelPre T Ls))).map
          ((toStar T).comp (Subgroup.subtype (borelPre T Ls))) =
          ((Subgroup.normalizer (T₂.subgroupOf (borelPre T Ls) :
            Set ↥(borelPre T Ls))).map (Subgroup.subtype (borelPre T Ls))).map
            (toStar T) := by rw [Subgroup.map_map]
      _ ≤ (Subgroup.normalizer (T₂ : Set X)).map (toStar T) := Subgroup.map_mono hNX
  have hsup : (C : Set ↥Y) * (N : Set ↥Y) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      obtain ⟨x, rfl⟩ := hφsurj y
      have hx : x ∈ (Subgroup.centralizer
          (T₁.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls)) :
            Set ↥(borelPre T Ls)) *
          (Subgroup.normalizer
            (T₂.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls)) :
            Set ↥(borelPre T Ls)) := by
        rw [borelPre_factors_of_isSolvable_gnImg hX hGood hNB hsolvY]
        exact Set.mem_univ x
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      have hmem : φ a * φ b ∈ (C : Set ↥Y) * (N : Set ↥Y) :=
        Set.mul_mem_mul (Subgroup.mem_map_of_mem φ ha) (Subgroup.mem_map_of_mem φ hb)
      simpa [map_mul, ← hab] using hmem
  have hHLs : ∀ H : Subgroup ↥Y,
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H → H ≤ B →
      H.map (Subgroup.subtype Y) ≤ Ls := by
    intro H _ hHB
    rintro _ ⟨h, hh, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hBLs (hHB hh))
  have hC : ∀ H : Subgroup ↥Y,
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H →
      (H ⊓ C).map (Subgroup.subtype Y) ≤ gnA T T₁ Ls := by
    intro H hHall
    rw [gnA]
    refine le_inf ?_ ?_
    · calc
        (H ⊓ C).map (Subgroup.subtype Y) ≤ C.map (Subgroup.subtype Y) :=
          Subgroup.map_mono inf_le_right
        _ ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) := hCmap
        _ ≤ gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
          Subgroup.map_mono (Subgroup.centralizer_le_normalizer (T₁ : Set X))
    · exact (Subgroup.map_mono inf_le_left).trans
        (hHLs H hHall (hHallB H hHall))
  have hN : ∀ H : Subgroup ↥Y,
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H →
      (H ⊓ N).map (Subgroup.subtype Y) ≤ gnA T T₂ Ls := by
    intro H hHall
    rw [gnA]
    refine le_inf ?_ ?_
    · exact (Subgroup.map_mono inf_le_right).trans hNmap
    · exact (Subgroup.map_mono inf_le_left).trans
        (hHLs H hHall (hHallB H hHall))
  exact k517_4b_rank_ge_three_of_cartan_hall (Y := ↥Y) hsolvY C N Hc B hB hsup
    hHcpi hHallB hBcomm hq hq2 h3 (Subgroup.subtype Y) Subtype.coe_injective hC hN

theorem k517_4b_lin_of_setting_of_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hq : q.Prime) (hq2 : q ≠ 2)
    {m : ℕ} (hm : 3 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.A m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃*
      (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1)
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls)
    (hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False)
    (hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)))
    {B : Subgroup ↥(gnImg T (borelPre T Ls))} (hB : B.Normal)
    (hHallB : ∀ H : Subgroup ↥(gnImg T (borelPre T Ls)),
      IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H → H ≤ B)
    (hBcomm : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B))
    (hBLs : B ≤ Ls.subgroupOf (gnImg T (borelPre T Ls))) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  obtain ⟨HcLs, hHcpi, hHc3, hHcnorm⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_cartan_in_borel_of_linear_component
      hLs.1.2.2 m (by omega) Q hQ hv e (by omega) hq hq2 hqQ hUmax
  have hsurj : Function.Surjective (toStar T) := QuotientGroup.mk'_surjective (gnC T)
  have hYmap : gnImg T (borelPre T Ls) = Subgroup.normalizer
      ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) ⊓ Ls ⊔ gnImg T T := by
    rw [gnImg, borelPre, Subgroup.map_comap_eq_self_of_surjective hsurj]
  have hHcN : HcLs.map Ls.subtype ≤
      Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) := by
    have hsub : (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) ≤ Ls := inf_le_right
    have hHcN' : HcLs ≤
        (Subgroup.normalizer (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T))).subgroupOf Ls := by
      rw [Subgroup.subgroupOf_normalizer_eq hsub, ← hU]
      exact hHcnorm
    calc
      HcLs.map Ls.subtype ≤
          ((Subgroup.normalizer (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T))).subgroupOf Ls).map
            Ls.subtype := Subgroup.map_mono hHcN'
      _ = Subgroup.normalizer (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) ⊓ Ls :=
        Subgroup.subgroupOf_map_subtype _ Ls
      _ ≤ Subgroup.normalizer (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) := inf_le_left
  have hHcY : ∀ x ∈ HcLs, (x : X ⧸ gnC T) ∈ gnImg T (borelPre T Ls) := by
    intro x hx
    have hx' : (x : X ⧸ gnC T) ∈
        Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
          Set (X ⧸ gnC T)) ⊓ Ls :=
      Subgroup.mem_inf.mpr
        ⟨hHcN (Subgroup.mem_map_of_mem Ls.subtype hx), (x : ↥Ls).2⟩
    rw [hYmap]
    exact Subgroup.mem_sup_left hx'
  let HcY : Subgroup ↥(gnImg T (borelPre T Ls)) :=
    (HcLs.map Ls.subtype).subgroupOf (gnImg T (borelPre T Ls))
  let g : ↥HcLs →* ↥HcY :=
    { toFun := fun x =>
        ⟨⟨(x : X ⧸ gnC T), hHcY x x.2⟩, Subgroup.mem_map_of_mem Ls.subtype x.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥HcY =>
      ((z : ↥(gnImg T (borelPre T Ls))) : X ⧸ gnC T)) hab
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have hker : ¬ q ∣ Nat.card ↥(MonoidHom.ker g) := by
    have hbot : MonoidHom.ker g = ⊥ := MonoidHom.ker_eq_bot g hginj
    have hcard : Nat.card ↥(MonoidHom.ker g) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [hcard]
    exact hq.not_dvd_one
  have htransfer : CFSG.Open.pRank q (⊤ : Subgroup ↥HcY) =
      CFSG.Open.pRank q (⊤ : Subgroup ↥HcLs) := by
    rw [← Subgroup.map_top_of_surjective g hgsurj]
    exact CFSG.pRank_map_eq_of_not_dvd_card_ker g hgsurj hq hker ⊤
  have h3Y : 3 ≤ CFSG.Open.pRank q HcY := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup HcY, htransfer,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup HcLs]
    exact hHc3
  have hHcpiY : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} HcY := by
    intro p hp
    refine hHcpi p ?_
    have hc : Nat.card ↥HcY = Nat.card ↥HcLs :=
      (Nat.card_congr (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩).toEquiv).symm
    rw [← hc]
    exact hp
  exact k517_4b_rank_ge_three_of_X1_of_isSolvable_gnImg_hall hX hGood hq hq2 hNB hsolvY
    (Hc := HcY) (B := B) hB hHcpiY h3Y hHallB hBcomm hBLs

theorem k517_4b_lin_of_top_of_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ} (hLs : GNYComponent T T₁ T₂ Ls)
    (hq : q.Prime) (hq2 : q ≠ 2)
    {m : ℕ} (hm : 3 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.A m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃*
      (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1) (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hne : ¬ (m = 2 ∧ Q.card = 4) := by
    rintro ⟨rfl, -⟩
    omega
  have hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)) :=
    isSolvable_gnImg_borelPre_of_linear_component hX hLs hTinv hm1 hQ e hUmax hU hne
  have hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False :=
    noXBlock_borelPre_subtype hX hLs.1 hTinv m (by omega) Q hQ hv e
  let P : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ Ls
  let Bstar : Subgroup (X ⧸ gnC T) := Subgroup.normalizer (P : Set (X ⧸ gnC T)) ⊓ Ls
  let Y : Subgroup (X ⧸ gnC T) := gnImg T (borelPre T Ls)
  let BY : Subgroup ↥Y := Bstar.subgroupOf Y
  have hY : Y = Bstar ⊔ gnImg T T := by
    dsimp only [Y, Bstar, P]
    rw [gnImg_borelPre_eq_sup]
  have hBstar_le_Y : Bstar ≤ Y := by rw [hY]; exact le_sup_left
  have hT_le_Y : gnImg T T ≤ Y := by rw [hY]; exact le_sup_right
  have hTnormP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)) :=
    (le_inf Subgroup.le_normalizer hTinv).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTnorm : gnImg T T ≤ Subgroup.normalizer (Bstar : Set (X ⧸ gnC T)) :=
    (le_inf (hTnormP.trans (Subgroup.le_normalizer
      (H := Subgroup.normalizer (P : Set (X ⧸ gnC T))))) hTinv).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hYnorm : Y ≤ Subgroup.normalizer (Bstar : Set (X ⧸ gnC T)) := by
    rw [hY]
    exact sup_le Subgroup.le_normalizer hTnorm
  have hB : BY.Normal := by
    dsimp only [BY]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
  haveI : BY.Normal := hB
  have hT2 : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map (QuotientGroup.mk' (gnC T))
  let q' : ↥(gnImg T T) →* (↥Y ⧸ BY) :=
    (QuotientGroup.mk' BY).comp (Subgroup.inclusion hT_le_Y)
  have hq'surj : Function.Surjective q' := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective BY z
    have hysup : (y : X ⧸ gnC T) ∈ (↑(Bstar ⊔ gnImg T T) : Set (X ⧸ gnC T)) :=
      hY.le y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Bstar (gnImg T T) hTnorm] at hysup
    obtain ⟨b, hb, t, ht, hbt⟩ := Set.mem_mul.mp hysup
    have hbY : b ∈ Y := hBstar_le_Y hb
    have hbBY : (⟨b, hbY⟩ : ↥Y) ∈ BY := by
      dsimp only [BY]
      exact Subgroup.mem_subgroupOf.mpr hb
    have hy_eq : y = (⟨b, hbY⟩ : ↥Y) * Subgroup.inclusion hT_le_Y ⟨t, ht⟩ := by
      apply Subtype.ext
      exact hbt.symm
    refine ⟨⟨t, ht⟩, ?_⟩
    show QuotientGroup.mk' BY (Subgroup.inclusion hT_le_Y ⟨t, ht⟩) = QuotientGroup.mk' BY y
    rw [hy_eq, map_mul]
    have hb1 : QuotientGroup.mk' BY (⟨b, hbY⟩ : ↥Y) = 1 :=
      (QuotientGroup.eq_one_iff (N := BY) (x := (⟨b, hbY⟩ : ↥Y))).mpr hbBY
    rw [hb1, one_mul]
  have hquot : IsPGroup 2 (↥Y ⧸ BY) := hT2.of_surjective q' hq'surj
  have hHallB : ∀ H : Subgroup ↥Y, IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H →
      H ≤ BY := fun H hH => le_of_isHallSubgroup_of_quotient_isPGroup BY hquot hH
  let N : Subgroup ↥Ls := Subgroup.normalizer (U : Set ↥Ls)
  have hcommN : IsMulCommutative (↥N ⧸ CFSG.pCore 2 ↥N) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_normalizer_quotient_pCore_of_linear_component
      hLs.1.2.2 m hm1 Q hQ hv e hne hUmax
  have hNmap : N.map Ls.subtype = Bstar := by
    dsimp only [N, Bstar, P]
    rw [hU]
    exact normalizer_map_subgroupOf_eq Ls (gnImg T T ⊓ Ls) inf_le_right
  let f1 : ↥N →* ↥Bstar :=
    (Ls.subtype.comp N.subtype).codRestrict Bstar (fun x => by
      rw [← hNmap]
      exact Subgroup.mem_map_of_mem Ls.subtype x.2)
  have hf1 : Function.Surjective f1 := by
    intro b
    have hb : (b : X ⧸ gnC T) ∈ N.map Ls.subtype := by
      rw [hNmap]
      exact b.2
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hb
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxval
  have hcommBstar : IsMulCommutative (↥Bstar ⧸ CFSG.pCore 2 ↥Bstar) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective f1 hf1 hcommN
  let f2 : ↥Bstar →* ↥BY :=
    (Subgroup.inclusion hBstar_le_Y).codRestrict BY (fun y => by
      dsimp only [BY]
      exact Subgroup.mem_subgroupOf.mpr y.2)
  have hf2 : Function.Surjective f2 := by
    intro y
    refine ⟨⟨(y : ↥Y).val, Subgroup.mem_subgroupOf.mp y.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hcommBY : IsMulCommutative (↥BY ⧸ CFSG.pCore 2 ↥BY) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective f2 hf2
      hcommBstar
  have hBstarLs : Bstar ≤ Ls := by
    dsimp only [Bstar]
    exact inf_le_right
  have hBLs : BY ≤ Ls.subgroupOf Y := by
    dsimp only [BY]
    exact Subgroup.subgroupOf_mono Y hBstarLs
  exact k517_4b_lin_of_setting_of_hall hX hGood hLs hq hq2 hm hQ e hU2 hUmax hqQ hU hNB hsolvY
    (B := BY) hB hHallB hcommBY hBLs

end CFSG.LocalAnalysis.RankThreeUC.S15

end
