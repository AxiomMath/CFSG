module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUKernel
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUFrattini
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUThompson
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped Pointwise

theorem le_scalarKer_of_le_sup_centralizer {G : Type} [Group G] {S K L U E : Subgroup G}
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hKS : K ≤ S) (hUL : U ≤ L) (hEL : E ≤ L)
    (hKL : K ≤ L ⊔ Subgroup.centralizer (L : Set G))
    (hcomm : ∀ a ∈ L ⊓ Subgroup.normalizer (U : Set G), ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ U) :
    K ≤ scalarKer S U E := by
  have hLC : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    (Subgroup.le_normalizer : L ≤ Subgroup.normalizer (L : Set G)).trans
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
  have hmul : ((L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) =
      (L : Set G) * (Subgroup.centralizer (L : Set G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right L _ hLC
  intro s hsK
  have hsS : s ∈ S := hKS hsK
  have hsN : s ∈ Subgroup.normalizer (U : Set G) := hSU hsS
  have hs : s ∈ (L : Set G) * (Subgroup.centralizer (L : Set G) : Set G) := by
    rw [← hmul]
    exact hKL hsK
  obtain ⟨a, haL, c, hcC, hx⟩ := hs
  have hcL : ∀ x ∈ L, x * c = c * x := Subgroup.mem_centralizer_iff.mp hcC
  have hcN : c ∈ Subgroup.normalizer (U : Set G) := by
    refine Subgroup.centralizer_le_normalizer (U : Set G) ?_
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => hcL u (hUL hu)
  have haN : a ∈ Subgroup.normalizer (U : Set G) := by
    have h : s * c⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ hsN (Subgroup.inv_mem _ hcN)
    have haeq : a = s * c⁻¹ := by
      rw [← hx]
      group
    rwa [haeq]
  refine (mem_scalarKer_iff hSU).mpr ⟨hsS, ?_⟩
  intro e he
  have hce : c * e * c⁻¹ = e := by
    rw [← hcL e (hEL he), mul_assoc, mul_inv_cancel, mul_one]
  have heq : a * c * e * (a * c)⁻¹ * e⁻¹ = a * e * a⁻¹ * e⁻¹ := by
    rw [show a * c * e * (a * c)⁻¹ * e⁻¹ = a * (c * e * c⁻¹) * a⁻¹ * e⁻¹ by group,
      hce]
  rw [← hx, heq]
  exact hcomm a ⟨haL, haN⟩ e he

private theorem le_gnA_of_gnImg_baum_le_scalarKer {X : Type} [Group X] [Finite X]
    {T T₂ : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {Ls E : Subgroup (X ⧸ gnC T)}
    (hEnorm : E ≤ Subgroup.normalizer
      (scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E : Set (X ⧸ gnC T)))
    (hbaum : gnImg T (CFSG.Quasithin.baum T) ≤
      scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E)
    (hT₂B : T₂ ≤ CFSG.Quasithin.baum T)
    (hchar : (T₂.subgroupOf (CFSG.Quasithin.baum T)).Characteristic)
    (hELs : E ≤ Ls) :
    E ≤ gnA T T₂ Ls := by
  have hST : scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E ≤ gnImg T T :=
    scalarKer_le _ _ _
  have hN : E ≤ gnImg T (Subgroup.normalizer (CFSG.Quasithin.baum T : Set X)) :=
    hEnorm.trans (normalizer_le_gnImg_normalizer_baum hT hST hbaum)
  have hNB : Subgroup.normalizer (CFSG.Quasithin.baum T : Set X) ≤
      Subgroup.normalizer (T₂ : Set X) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (T₂.subgroupOf (CFSG.Quasithin.baum T))
    rwa [Subgroup.map_subgroupOf_eq_of_le hT₂B] at h
  exact le_inf (hN.trans (Subgroup.map_mono hNB)) hELs

private theorem le_gnA_of_not_gnImg_baum_le_scalarKer {X : Type} [Group X] [Finite X]
    {T T₁ : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Ls : Subgroup (X ⧸ gnC T)}
    (hSU : gnImg T T ≤ Subgroup.normalizer
      ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)))
    {E : Subgroup (X ⧸ gnC T)} (hELs : E ≤ Ls)
    (hEq : ∀ x ∈ E, x ^ q = 1)
    (hscal : ∀ s ∈ gnImg T (CFSG.Quasithin.baum T), ∃ j : ℕ,
      ∀ x ∈ E, s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls)
    (hEnormJ : E ≤ gnImg T (Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X)))
    (hnot : ¬ gnImg T (CFSG.Quasithin.baum T) ≤
      scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E)
    (hT₁ : T₁ ≤ CFSG.Quasithin.omegaOneCenterOf T) :
    E ≤ gnA T T₁ Ls := by
  classical
  obtain ⟨s, hsbaum, hsnot⟩ := SetLike.not_le_iff_exists.mp hnot
  have hsT : s ∈ gnImg T T := Subgroup.map_mono (CFSG.Quasithin.C1GN.baum_le T) hsbaum
  have hnotmem : ¬ ∀ e ∈ E, s * e * s⁻¹ * e⁻¹ ∈ gnImg T T ⊓ Ls := by
    intro h
    exact hsnot ((mem_scalarKer_iff hSU).mpr ⟨hsT, h⟩)
  push Not at hnotmem
  obtain ⟨e₀, he₀, hne⟩ := hnotmem
  let K : Subgroup (X ⧸ gnC T) := gnImg T (jNormCent T)
  have hTnormJ : T ≤ Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ T)
  have hTmap : gnImg T T ≤
      gnImg T (Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X)) :=
    Subgroup.map_mono hTnormJ
  have hUK : (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) ≤
      Subgroup.normalizer (K : Set (X ⧸ gnC T)) :=
    (inf_le_left.trans hTmap).trans
      (gnImg_normalizer_thompsonJ_le_normalizer_jNormCent T)
  have hEK : E ≤ Subgroup.normalizer (K : Set (X ⧸ gnC T)) :=
    hEnormJ.trans (gnImg_normalizer_thompsonJ_le_normalizer_jNormCent T)
  have hsK : s ∈ K := Subgroup.map_mono (baum_le_jNormCent T) hsbaum
  obtain ⟨j, hsj⟩ := hscal s hsbaum
  have hUP : IsPGroup 2 (gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :=
    (IsPGroup.map hT.2.1 (QuotientGroup.mk' (gnC T))).to_le inf_le_left
  have hEKle : E ≤ K :=
    le_of_scalar_commutator hq hq2 hUP hUK hEK hEq hsK hsj he₀ hne
  have hKN : K ≤ gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
    Subgroup.map_mono
      ((jNormCent_le_centralizer hT₁).trans (Subgroup.centralizer_le_normalizer _))
  exact le_inf (hEKle.trans hKN) hELs

theorem le_gnA_of_thompsonJ_le_scalarKer {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hc : CFSG.Quasithin.IsC118Pair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (X ⧸ gnC T)} (hELs : E ≤ Ls)
    (hEU : E ≤ Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)))
    (hEq : ∀ x ∈ E, x ^ q = 1)
    (hscal : ∀ s ∈ gnImg T (CFSG.Quasithin.baum T), ∃ j : ℕ,
      ∀ x ∈ E, s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls)
    (hJ : gnImg T (CFSG.Quasithin.thompsonJ T) ≤ scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E) :
    E ≤ gnA T T₁ Ls ∨ E ≤ gnA T T₂ Ls := by
  classical
  have hSU : gnImg T T ≤ Subgroup.normalizer
      ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hinv hx⟩
  have hEnorm : E ≤ Subgroup.normalizer
      (scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E : Set (X ⧸ gnC T)) :=
    le_normalizer_scalarKer inf_le_left hEU
  have hEnormJ : E ≤ gnImg T (Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X)) :=
    hEnorm.trans (normalizer_le_gnImg_normalizer_thompsonJ hT (scalarKer_le _ _ _) hJ)
  by_cases hA : gnImg T (CFSG.Quasithin.baum T) ≤
      scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E
  · exact Or.inr (le_gnA_of_gnImg_baum_le_scalarKer hT hEnorm hA
      hc.2.2.2.2.1 hc.2.2.2.2.2.1 hELs)
  · exact Or.inl (le_gnA_of_not_gnImg_baum_le_scalarKer hT hq hq2 hSU hELs hEq hscal
      hEnormJ hA hc.2.1)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
