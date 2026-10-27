module

public import CFSG.GroupTheory.SolvableTransport
public import CFSG.ClassicalGroups.SpecialLinear.ComponentBorelSolvable
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem gnImg_borelPre_eq_sup {Ls : Subgroup (X ⧸ gnC T)} :
    gnImg T (borelPre T Ls) =
      (Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
          Set (X ⧸ gnC T)) ⊓ Ls) ⊔ gnImg T T := by
  rw [gnImg, borelPre, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (gnC T))]

theorem isSolvable_gnImg_borelPre_of_borel
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls)
    (hB : Group.IsSolvable ↥(Subgroup.normalizer (U : Set ↥Ls))) :
    Group.IsSolvable ↥(gnImg T (borelPre T Ls)) := by
  classical
  let P : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ Ls
  let Bstar : Subgroup (X ⧸ gnC T) := Subgroup.normalizer (P : Set (X ⧸ gnC T)) ⊓ Ls
  have hBstar_eq : Bstar = (Subgroup.normalizer (U : Set ↥Ls)).map Ls.subtype := by
    have hcomap : (Subgroup.normalizer (P : Set (X ⧸ gnC T))).subgroupOf Ls =
        Subgroup.normalizer (U : Set ↥Ls) := by
      change (Subgroup.normalizer P).comap Ls.subtype = Subgroup.normalizer U
      rw [Subgroup.comap_normalizer_eq_of_le_range (H := P) (f := Ls.subtype) (by
        rw [Subgroup.range_subtype]
        exact inf_le_right)]
      rw [show P.comap Ls.subtype = U from hU.symm]
    rw [← hcomap, Subgroup.subgroupOf_map_subtype]
  have hBstar_solv : Group.IsSolvable ↥Bstar := by
    rw [hBstar_eq]
    refine Group.isSolvable_of_surjective
      (f := (Ls.subtype.comp (Subgroup.normalizer (U : Set ↥Ls)).subtype).codRestrict
        ((Subgroup.normalizer (U : Set ↥Ls)).map Ls.subtype)
        (fun x => Subgroup.mem_map_of_mem Ls.subtype x.2)) ?_
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hT2 : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map (QuotientGroup.mk' (gnC T))
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
  have hYsolv : Group.IsSolvable ↥(Bstar ⊔ gnImg T T) :=
    CFSG.GroupTheory.isSolvable_sup_of_isPGroup_of_le_normalizer hBstar_solv hT2 hTnorm
  rwa [gnImg_borelPre_eq_sup]

theorem isSolvable_gnImg_borelPre_of_linear_component
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {m : ℕ} (hm : 1 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.A m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃*
      (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup ↥Ls} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls)
    (hne : ¬ (m = 2 ∧ Q.card = 4)) :
    Group.IsSolvable ↥(gnImg T (borelPre T Ls)) :=
  isSolvable_gnImg_borelPre_of_borel hX hTinv hU
    (CFSG.ClassicalGroups.SpecialLinear.isSolvable_normalizer_sylow_of_component
      hLs.1.2.2 m hm Q hQ hv e hne hUmax)

theorem normalizer_map_subgroupOf_eq {Xs : Type} [Group Xs] (Ls P : Subgroup Xs) (hP : P ≤ Ls) :
    (Subgroup.normalizer (P.subgroupOf Ls : Set ↥Ls)).map Ls.subtype =
      Subgroup.normalizer (P : Set Xs) ⊓ Ls := by
  have hcomap : (Subgroup.normalizer (P : Set Xs)).subgroupOf Ls =
      Subgroup.normalizer (P.subgroupOf Ls : Set ↥Ls) := by
    change (Subgroup.normalizer P).comap Ls.subtype = Subgroup.normalizer (P.subgroupOf Ls)
    rw [Subgroup.comap_normalizer_eq_of_le_range (H := P) (f := Ls.subtype)
      (by rw [Subgroup.range_subtype]; exact hP)]
    rfl
  rw [← hcomap, Subgroup.subgroupOf_map_subtype]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
