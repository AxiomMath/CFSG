module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftXEmbed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped commutatorElement

section Tools

variable {G : Type} [Group G]

theorem map_subtype_map_conj {X : Subgroup G} (K' : Subgroup ↥X) (t : ↥X) :
    (K'.map (MulAut.conj t).toMonoidHom).map X.subtype =
      (K'.map X.subtype).map (MulAut.conj (t : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_normalizer_of_subgroupOf {A K X : Subgroup G} (hAX : A ≤ X) (hKX : K ≤ X)
    (h : K.subgroupOf X ≤ Subgroup.normalizer ((A.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    K ≤ Subgroup.normalizer (A : Set G) := fun k hk =>
  (mem_normalizer_subgroupOf_iff hAX ⟨k, hKX hk⟩).1 (h hk)

end Tools

section Main

theorem evenSL2BlockOutput_of_top {G : Type} [Group G] [Finite G] {X R M V : Subgroup G} {n : ℕ}
    {F : Type} [Field F] (hS : EvenSL2Setting X R M V n F) {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)}
    (hout : EvenSL2BlockOutput (⊤ : Subgroup ↥X) (R.subgroupOf X) (V.subgroupOf X)
      (top_le_normalizer_subgroupOf hS.reduced.1 hS.reduced.2.1) n r
      (fun i => (Lc i).map (autEmbed hS.reduced.1).toMonoidHom)) :
    EvenSL2BlockOutput X R V hS.reduced.2.1 n r Lc := by
  classical
  have hVX : V ≤ X := hS.reduced.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hS.reduced.2.1
  have hRX : R ≤ X := hS.sylow.1
  have hι : Function.Injective X.subtype := X.subtype_injective
  obtain ⟨B', hB'⟩ : ∃ B' : Fin r → Subgroup ↥X, ∀ i, B' i = blockOf (⊤ : Subgroup ↥X)
      (R.subgroupOf X) (V.subgroupOf X) (top_le_normalizer_subgroupOf hVX hX)
      ((Lc i).map (autEmbed hVX).toMonoidHom) := ⟨fun i => _, fun i => rfl⟩
  have hB : ∀ i, (B' i).map X.subtype = blockOf X R V hX (Lc i) := fun i => by
    rw [hB' i]
    exact blockOf_map hVX hX hRX (Lc i)
  have hR : (R.subgroupOf X).map X.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRX
  have hV : (V.subgroupOf X).map X.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVX
  have hTop : (⊤ : Subgroup ↥X).map X.subtype = X := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hL : (oddOrderSubgroup (⊤ : Subgroup ↥X)).map X.subtype = oddOrderSubgroup X :=
    map_oddOrderSubgroup_top X
  have hSb : (baum (R.subgroupOf X)).map X.subtype = baum R := by
    rw [← baum_map_of_injective hι, hR]
  have hJ : (thompsonJ (R.subgroupOf X)).map X.subtype = thompsonJ R := by
    rw [← thompsonJ_map_of_injective' hι, hR]
  have hLS : (oddOrderSubgroup (⊤ : Subgroup ↥X) ⊔ baum (R.subgroupOf X)).map X.subtype =
      oddOrderSubgroup X ⊔ baum R := by
    rw [Subgroup.map_sup, hL, hSb]
  have hpc : ∀ K' : Subgroup ↥X, (pCoreOf 2 K').map X.subtype = pCoreOf 2 (K'.map X.subtype) :=
    fun K' => CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 X K'
  have hsubOf : ∀ K' : Subgroup ↥X, (K'.map X.subtype).subgroupOf X = K' := fun K' =>
    Subgroup.comap_map_eq_self_of_injective hι K'
  have hBX : ∀ i, blockOf X R V hX (Lc i) ≤ X := fun i =>
    ((oddOrderSubgroup_le _).trans inf_le_left).trans
      (sup_le (oddOrderSubgroup_le X) ((inf_le_left : baum R ≤ R).trans hRX))
  have hBLS : ∀ i, blockOf X R V hX (Lc i) ≤ oddOrderSubgroup X ⊔ baum R := fun i =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hmod : ∀ i, (modComm (V.subgroupOf X) ((Lc i).map (autEmbed hVX).toMonoidHom)).map
      X.subtype = modComm V (Lc i) := fun i => modComm_map hVX (Lc i)
  have hJ' : (thompsonJ R).subgroupOf X = thompsonJ (R.subgroupOf X) := by rw [← hJ, hsubOf]
  have hL' : (oddOrderSubgroup X).subgroupOf X = oddOrderSubgroup (⊤ : Subgroup ↥X) := by
    rw [← hL, hsubOf]
  have hJX : thompsonJ R ≤ X := (B6.thompsonJ_le R).trans hRX
  have hLX : oddOrderSubgroup X ≤ X := oddOrderSubgroup_le X
  have hnat : autOn (thompsonJ (R.subgroupOf X)) (V.subgroupOf X) ≤
      autOn (oddOrderSubgroup (⊤ : Subgroup ↥X)) (V.subgroupOf X) ↔
      autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V := by
    rw [← hJ', ← hL', autOn_subgroupOf hVX hX hJX, autOn_subgroupOf hVX hX hLX]
    exact Subgroup.map_le_map_iff_of_injective (autEmbed hVX).injective
  have hout_inj : Function.Injective B' := fun i j hij => by
    apply hout.injective
    show blockOf (⊤ : Subgroup ↥X) (R.subgroupOf X) (V.subgroupOf X)
      (top_le_normalizer_subgroupOf hVX hX) ((Lc i).map (autEmbed hVX).toMonoidHom) =
        blockOf (⊤ : Subgroup ↥X) (R.subgroupOf X) (V.subgroupOf X)
          (top_le_normalizer_subgroupOf hVX hX) ((Lc j).map (autEmbed hVX).toMonoidHom)
    rw [← hB' i, ← hB' j]
    exact hij
  have hchi0 : ∀ i, IsChi0Block X (blockOf X R V hX (Lc i)) := fun i => by
    have h : IsChi0Block (⊤ : Subgroup ↥X) (B' i) := by
      rw [hB' i]
      exact hout.chi0 i
    have := IsChi0Block.map_of_injective X.subtype hι h
    rwa [hTop, hB i] at this
  have htl : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
      ∀ i, IsLin2Type (blockOf X R V hX (Lc i)) n := by
    intro h i
    have h' : IsLin2Type (B' i) n := by
      rw [hB' i]
      exact hout.type_lin (hnat.2 h) i
    have := IsLin2Type.map_of_injective X.subtype hι h'
    rwa [hB i] at this
  have hta : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
      n = 2 ∧ ∀ i, IsAltType (blockOf X R V hX (Lc i)) 5 := by
    intro h
    obtain ⟨hn2, hAlt⟩ := hout.type_alt (fun h' => h (hnat.1 h'))
    refine ⟨hn2, fun i => ?_⟩
    have h' : IsAltType (B' i) 5 := by
      rw [hB' i]
      exact hAlt i
    have := IsAltType.map_of_injective X.subtype hι h'
    rwa [hB i] at this
  have hcc : ∀ i, quasithinIsCComponent (blockOf X R V hX (Lc i)) X := fun i => by
    by_cases h : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V
    · exact mem_cComp_iff.1 (L238.mem_cComp_of_isChi0Block_nonsolvable (hchi0 i).1
        (Or.inl ⟨n, hS.two_le, htl h i⟩))
    · exact mem_cComp_iff.1 (L238.mem_cComp_of_isChi0Block_nonsolvable (hchi0 i).1
        (Or.inr ((hta h).2 i)))
  have hLSX : oddOrderSubgroup X ⊔ baum R ≤ X :=
    sup_le hLX ((inf_le_left : baum R ≤ R).trans hRX)
  have hnLS : ((oddOrderSubgroup X ⊔ baum R).subgroupOf X).Normal := by
    have h1 : ((oddOrderSubgroup (⊤ : Subgroup ↥X) ⊔ baum (R.subgroupOf X)).subgroupOf
        (⊤ : Subgroup ↥X)).Normal := hout.normal_LS
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top] at h1
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLSX]
    refine le_normalizer_of_subgroupOf hLSX le_rfl ?_
    rw [Subgroup.subgroupOf_self, ← hLS, hsubOf]
    exact h1
  have hnB : ∀ i, ((blockOf X R V hX (Lc i)).subgroupOf (oddOrderSubgroup X ⊔ baum R)).Normal :=
    fun i => by
    have h1 : ((B' i).subgroupOf (oddOrderSubgroup (⊤ : Subgroup ↥X) ⊔
        baum (R.subgroupOf X))).Normal := by
      rw [hB' i]
      exact hout.normal_B i
    have hB'LS : B' i ≤ oddOrderSubgroup (⊤ : Subgroup ↥X) ⊔ baum (R.subgroupOf X) := by
      rw [hB' i]
      exact (oddOrderSubgroup_le _).trans inf_le_left
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hB'LS] at h1
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS i)]
    refine le_normalizer_of_subgroupOf (hBX i) hLSX ?_
    rw [← hLS, ← hB i, hsubOf, hsubOf]
    exact h1
  have hperm : ∀ t ∈ R, ∀ i, ∃ j, (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom =
      blockOf X R V hX (Lc j) := by
    intro t ht i
    have ht' : (⟨t, hRX ht⟩ : ↥X) ∈ R.subgroupOf X := ht
    obtain ⟨j, hj⟩ := hout.permuted ⟨t, hRX ht⟩ ht' i
    refine ⟨j, ?_⟩
    have hj' : (B' i).map (MulAut.conj (⟨t, hRX ht⟩ : ↥X)).toMonoidHom = B' j := by
      rw [hB' i, hB' j]
      exact hj
    calc (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom =
        ((B' i).map X.subtype).map (MulAut.conj t).toMonoidHom := by rw [hB i]
      _ = ((B' i).map (MulAut.conj (⟨t, hRX ht⟩ : ↥X)).toMonoidHom).map X.subtype :=
        (map_subtype_map_conj (B' i) ⟨t, hRX ht⟩).symm
      _ = blockOf X R V hX (Lc j) := by rw [hj', hB j]
  have htrans : ∀ i j, ∃ t ∈ R, (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom =
      blockOf X R V hX (Lc j) := by
    intro i j
    obtain ⟨t, ht, hj⟩ := hout.transitive i j
    have ht' : (t : G) ∈ R := by
      have := Subgroup.mem_map_of_mem X.subtype ht
      rwa [hR] at this
    refine ⟨(t : G), ht', ?_⟩
    have hj' : (B' i).map (MulAut.conj t).toMonoidHom = B' j := by
      rw [hB' i, hB' j]
      exact hj
    calc (blockOf X R V hX (Lc i)).map (MulAut.conj (t : G)).toMonoidHom =
        ((B' i).map X.subtype).map (MulAut.conj (t : G)).toMonoidHom := by rw [hB i]
      _ = ((B' i).map (MulAut.conj t).toMonoidHom).map X.subtype :=
        (map_subtype_map_conj (B' i) t).symm
      _ = blockOf X R V hX (Lc j) := by rw [hj', hB j]
  have hgen : ∀ i, X = blockOf X R V hX (Lc i) ⊔ R := fun i => by
    have h1 : (⊤ : Subgroup ↥X) = B' i ⊔ R.subgroupOf X := by
      rw [hB' i]
      exact hout.gen i
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [Subgroup.map_sup, hTop, hB i, hR] at h2
  have hperf : ∀ i, ⁅blockOf X R V hX (Lc i), thompsonJ R⁆ = blockOf X R V hX (Lc i) := fun i => by
    have h1 : ⁅B' i, thompsonJ (R.subgroupOf X)⁆ = B' i := by
      rw [hB' i]
      exact hout.perfect i
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [Subgroup.map_commutator, hB i, hJ] at h2
  have himage : ∀ i, autOn (blockOf X R V hX (Lc i)) V = Lc i := fun i => by
    have h1 : autOn (B' i) (V.subgroupOf X) = (Lc i).map (autEmbed hVX).toMonoidHom := by
      rw [hB' i]
      exact hout.image i
    have h2 : B' i = (blockOf X R V hX (Lc i)).subgroupOf X := by rw [← hB i, hsubOf]
    rw [h2, autOn_subgroupOf hVX hX (hBX i)] at h1
    exact Subgroup.map_injective (autEmbed hVX).injective h1
  have hcore : ∀ i, ⁅pCoreOf 2 (blockOf X R V hX (Lc i)), blockOf X R V hX (Lc i)⁆ =
        modComm V (Lc i) ∧
      ⁅pCoreOf 2 (oddOrderSubgroup X ⊔ baum R), blockOf X R V hX (Lc i)⁆ = modComm V (Lc i) := by
    intro i
    obtain ⟨c1, c2⟩ := hout.coreComm i
    have c1' : ⁅pCoreOf 2 (B' i), B' i⁆ =
        modComm (V.subgroupOf X) ((Lc i).map (autEmbed hVX).toMonoidHom) := by
      rw [hB' i]
      exact c1
    have c2' : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup ↥X) ⊔ baum (R.subgroupOf X)), B' i⁆ =
        modComm (V.subgroupOf X) ((Lc i).map (autEmbed hVX).toMonoidHom) := by
      rw [hB' i]
      exact c2
    constructor
    · have h := congrArg (Subgroup.map X.subtype) c1'
      rwa [Subgroup.map_commutator, hpc, hB i, hmod i] at h
    · have h := congrArg (Subgroup.map X.subtype) c2'
      rwa [Subgroup.map_commutator, hpc, hLS, hB i, hmod i] at h
  have hcomm : ∀ i j, i ≠ j →
      ⁅blockOf X R V hX (Lc i), blockOf X R V hX (Lc j)⁆ = ⊥ := fun i j hij => by
    have h1 : ⁅B' i, B' j⁆ = ⊥ := by
      rw [hB' i, hB' j]
      exact hout.commute i j hij
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [Subgroup.map_commutator, hB i, hB j, Subgroup.map_bot] at h2
  have hprod : oddOrderSubgroup X = ⨆ i, blockOf X R V hX (Lc i) ∧
      ∀ i, blockOf X R V hX (Lc i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), blockOf X R V hX (Lc j)) ≤
        centerIn (blockOf X R V hX (Lc i)) := by
    have hp1 : oddOrderSubgroup (⊤ : Subgroup ↥X) = ⨆ i, B' i := by
      have := hout.product.1
      simp only [← hB'] at this
      exact this
    have hp2 : ∀ i, B' i ⊓ (⨆ j, ⨆ (_ : j ≠ i), B' j) ≤ centerIn (B' i) := fun i => by
      have := hout.product.2 i
      simp only [← hB'] at this
      exact this
    refine ⟨?_, fun i => ?_⟩
    · have h := congrArg (Subgroup.map X.subtype) hp1
      rw [hL, Subgroup.map_iSup] at h
      rw [h]
      exact iSup_congr hB
    · have hD : (⨆ j, ⨆ (_ : j ≠ i), B' j).map X.subtype =
          ⨆ j, ⨆ (_ : j ≠ i), blockOf X R V hX (Lc j) := by
        rw [Subgroup.map_iSup]
        refine iSup_congr fun j => ?_
        rw [Subgroup.map_iSup]
        exact iSup_congr fun _ => hB j
      have h1 := Subgroup.map_mono (f := X.subtype) (hp2 i)
      rw [Subgroup.map_inf _ _ _ hι, hD, hB i] at h1
      refine h1.trans ?_
      unfold centerIn
      rw [← map_inf_centralizer_map' X.subtype hι, hB i]
  have hkernel : X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X ∧
      (oddOrderSubgroup X ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) =
        pCoreOf 2 (oddOrderSubgroup X ⊔ baum R) := by
    obtain ⟨k1, k2⟩ := hout.kernel
    constructor
    · have h := congrArg (Subgroup.map X.subtype) k1
      rwa [← map_inf_centralizer_map' X.subtype hι, hpc, hTop, hV] at h
    · have h := congrArg (Subgroup.map X.subtype) k2
      rwa [← map_inf_centralizer_map' X.subtype hι, hpc, hLS, hV] at h
  have hcommutator : ⁅pCoreOf 2 (oddOrderSubgroup X ⊔ baum R), oddOrderSubgroup X⁆ =
        ⁅V, oddOrderSubgroup X⁆ ∧
      ⁅V, oddOrderSubgroup X⁆ = ⨆ i, modComm V (Lc i) ∧
      (⨆ i, modComm V (Lc i)) ≤ omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup X ⊔ baum R)) := by
    obtain ⟨c1, c2, c3⟩ := hout.commutator
    have hmodsup : (⨆ i, modComm (V.subgroupOf X) ((Lc i).map (autEmbed hVX).toMonoidHom)).map
        X.subtype = ⨆ i, modComm V (Lc i) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hmod
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg (Subgroup.map X.subtype) c1
      rwa [Subgroup.map_commutator, Subgroup.map_commutator, hpc, hLS, hV, hL] at h
    · have h := congrArg (Subgroup.map X.subtype) c2
      rwa [Subgroup.map_commutator, hV, hL, hmodsup] at h
    · have h := Subgroup.map_mono (f := X.subtype) c3
      rwa [hmodsup, ← omegaOneCenterOf_map_of_injective hι, hpc, hLS] at h
  have hrank : (∃ k : ℕ, r = 2 ^ k) ∧ r ≤ CFSG.pRank 3 X := by
    refine ⟨hout.rank.1, ?_⟩
    have h1 : r ≤ CFSG.pRank 3 (⊤ : Subgroup ↥X) := hout.rank.2
    have h2 : CFSG.pRank 3 (⊤ : Subgroup ↥X) = CFSG.pRank 3 X :=
      Campbell.pRank_eq_of_mulEquiv Subgroup.topEquiv 3
    rwa [h2] at h1
  exact ⟨fun i j hij => hout_inj (Subgroup.map_injective hι (by rw [hB i, hB j]; exact hij)), hnLS,
    hnB, hperm, htrans, hcc, hchi0, hgen, hperf, himage, hcore, hcomm, hprod, hkernel,
    hcommutator, htl, hta, hrank⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift
