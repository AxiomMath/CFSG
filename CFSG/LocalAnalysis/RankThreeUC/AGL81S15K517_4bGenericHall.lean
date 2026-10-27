module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bLinHall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem k517_4b_normalizer_data_of_mulCommutative
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls}
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls)
    (hcomm : IsMulCommutative
      (↥(Subgroup.normalizer (U : Set ↥Ls)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set ↥Ls)))) :
    let Y : Subgroup (X ⧸ gnC T) := gnImg T (borelPre T Ls)
    let Bstar : Subgroup (X ⧸ gnC T) :=
      Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) ⊓ Ls
    let BY : Subgroup ↥Y := Bstar.subgroupOf Y
    BY.Normal ∧
      (∀ H : Subgroup ↥Y, IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H → H ≤ BY) ∧
      IsMulCommutative (↥BY ⧸ CFSG.pCore 2 ↥BY) := by
  classical
  let P : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ Ls
  let Bstar : Subgroup (X ⧸ gnC T) := Subgroup.normalizer (P : Set (X ⧸ gnC T)) ⊓ Ls
  let Y : Subgroup (X ⧸ gnC T) := gnImg T (borelPre T Ls)
  let BY : Subgroup ↥Y := Bstar.subgroupOf Y
  have hY : Y = Bstar ⊔ gnImg T T := by
    dsimp only [Y, Bstar, P]
    rw [gnImg_borelPre_eq_sup]
  have hBstar_le_Y : Bstar ≤ Y := by rw [hY]; exact le_sup_left
  have hT_le_Y : gnImg T T ≤ Y := by rw [hY]; exact le_sup_right
  have hTnorm : gnImg T T ≤ Subgroup.normalizer (Bstar : Set (X ⧸ gnC T)) := by
    have htP : ∀ t ∈ gnImg T T,
        t ∈ Subgroup.normalizer (P : Set (X ⧸ gnC T)) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff'']
      intro z
      constructor
      · intro hz
        obtain ⟨hzT, hzL⟩ := Subgroup.mem_inf.mp hz
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact (gnImg T T).mul_mem ((gnImg T T).mul_mem ((gnImg T T).inv_mem ht) hzT) ht
        · exact (Subgroup.mem_normalizer_iff''.mp (hTinv ht) z).mp hzL
      · intro hz
        obtain ⟨hzT, hzL⟩ := Subgroup.mem_inf.mp hz
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : t * (t⁻¹ * z * t) * t⁻¹ ∈ gnImg T T :=
            (gnImg T T).mul_mem ((gnImg T T).mul_mem ht hzT) ((gnImg T T).inv_mem ht)
          have hzEq : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
          rwa [hzEq] at h1
        · exact (Subgroup.mem_normalizer_iff''.mp (hTinv ht) z).mpr hzL
    intro t ht
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      obtain ⟨hxN, hxL⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.normalizer (P : Set (X ⧸ gnC T))).mul_mem
          ((Subgroup.normalizer (P : Set (X ⧸ gnC T))).mul_mem
            ((Subgroup.normalizer (P : Set (X ⧸ gnC T))).inv_mem (htP t ht)) hxN)
          (htP t ht)
      · exact (Subgroup.mem_normalizer_iff''.mp (hTinv ht) x).mp hxL
    · intro hx
      obtain ⟨hxN, hxL⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ Subgroup.normalizer (P : Set (X ⧸ gnC T)) :=
          (Subgroup.normalizer (P : Set (X ⧸ gnC T))).mul_mem
            ((Subgroup.normalizer (P : Set (X ⧸ gnC T))).mul_mem (htP t ht) hxN)
            ((Subgroup.normalizer (P : Set (X ⧸ gnC T))).inv_mem (htP t ht))
        have hxEq : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        rwa [hxEq] at h1
      · exact (Subgroup.mem_normalizer_iff''.mp (hTinv ht) x).mpr hxL
  have hYnorm : Y ≤ Subgroup.normalizer (Bstar : Set (X ⧸ gnC T)) := by
    rw [hY]
    exact sup_le Subgroup.le_normalizer hTnorm
  have hB : BY.Normal := by
    dsimp only [BY]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
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
  have hHallB : ∀ H : Subgroup ↥Y, IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H → H ≤ BY := by
    haveI : BY.Normal := hB
    exact fun H hH => le_of_isHallSubgroup_of_quotient_isPGroup BY hquot hH
  let N : Subgroup ↥Ls := Subgroup.normalizer (U : Set ↥Ls)
  have hcommN : IsMulCommutative (↥N ⧸ CFSG.pCore 2 ↥N) := hcomm
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
  exact ⟨hB, hHallB, hcommBY⟩


theorem k517_4b_of_setting_of_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hq : q.Prime) (hq2 : q ≠ 2)
    {U : Subgroup ↥Ls}
    (hHc : ∃ Hc : Subgroup ↥Ls, Hc ≤ Subgroup.normalizer (U : Set ↥Ls) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧ 3 ≤ CFSG.Open.pRank q Hc)
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
  obtain ⟨HcLs, hHcnorm, hHcpi, hHc3⟩ := hHc
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


end CFSG.LocalAnalysis.RankThreeUC.S15

end
