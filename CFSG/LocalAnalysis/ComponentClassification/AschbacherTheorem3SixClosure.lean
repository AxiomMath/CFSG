module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleSubgroups

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem mem_of_weaklyClosed {G S₀ A : Subgroup X} (hS₀ : IsSylowOf 2 S₀ G) (hAS : A ≤ S₀)
    (hAab : IsMulCommutative A)
    (hwc : ∀ x ∈ G, rightConjugate A x ≤ S₀ → rightConjugate A x = A)
    {a x : X} (ha : a ∈ A) (hx : x ∈ G)
    (hcomm : x⁻¹ * a * x ∈ Subgroup.centralizer (A : Set X)) :
    x⁻¹ * a * x ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := x⁻¹ * a * x with hsdef
  set C := G ⊓ Subgroup.centralizer ({s} : Set X) with hCdef
  have hS₀G : S₀ ≤ G := hS₀.le
  have hS₀2 : IsPGroup 2 S₀ := hS₀.isPGroup
  have hAG : A ≤ G := hAS.trans hS₀G
  have hsA : s ∈ rightConjugate A x := conj_mem_rightConjugate ha x
  have hAx : rightConjugate A x ≤ C := by
    intro y hy
    refine ⟨rightConjugate_le_of_mem hAG hx hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hcab := isMulCommutative_rightConjugate hAab x
    exact congrArg Subtype.val (hcab.is_comm.comm ⟨y, hy⟩ ⟨s, hsA⟩)
  have hAC : A ≤ C := by
    intro y hy
    refine ⟨hAG hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hcomm y hy)
  obtain ⟨P, hP, hAP⟩ := exists_isSylowOf_le (hS₀2.to_le hAS) hAC
  obtain ⟨c, hcC, hcle⟩ := exists_rightConjugate_le_of_isSylowOf hP
    (isPGroup_rightConjugate (hS₀2.to_le hAS) x) hAx
  obtain ⟨d, hdG, hdle⟩ := exists_rightConjugate_le_of_isSylowOf hS₀ hP.isPGroup
    (hP.le.trans inf_le_left)
  have hAd : rightConjugate A d = A :=
    hwc d hdG ((rightConjugate_le_rightConjugate hAP d).trans hdle)
  have hAxcd : rightConjugate A (x * c * d) = A := by
    apply hwc _ (G.mul_mem (G.mul_mem hx hcC.1) hdG)
    rw [← rightConjugate_mul, ← rightConjugate_mul]
    exact (rightConjugate_le_rightConjugate hcle d).trans hdle
  have hsc : c⁻¹ * s * c = s := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hcC.2
    calc c⁻¹ * s * c = c⁻¹ * (s * c) := by group
      _ = c⁻¹ * (c * s) := by rw [h]
      _ = s := by group
  have h1 : d⁻¹ * s * d ∈ A := by
    have h2 : (x * c * d)⁻¹ * a * (x * c * d) ∈ rightConjugate A (x * c * d) :=
      conj_mem_rightConjugate ha _
    rw [hAxcd] at h2
    have : (x * c * d)⁻¹ * a * (x * c * d) = d⁻¹ * (c⁻¹ * s * c) * d := by
      rw [hsdef]; group
    rw [this, hsc] at h2
    exact h2
  have hdN : d ∈ Subgroup.normalizer (A : Set X) := (rightConjugate_eq_self_iff A d).mp hAd
  have h3 := (Subgroup.mem_normalizer_iff.mp hdN (d⁻¹ * s * d)).mp h1
  simpa [mul_assoc] using h3

omit [Finite X] in
theorem map_subtype_map_conj {G A : Subgroup X} (hAG : A ≤ G) {x : X} (hx : x ∈ G) :
    ((A.subgroupOf G).map (MulAut.conj (⟨x, hx⟩ : G)⁻¹).toMonoidHom).map G.subtype =
      rightConjugate A x := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [mem_rightConjugate_iff]
    have ha' := Subgroup.mem_subgroupOf.mp ha
    simpa [MulAut.conj_apply, mul_assoc] using ha'
  · intro hy
    rw [mem_rightConjugate_iff] at hy
    have hyG : y ∈ G := by
      have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [this]
      exact G.mul_mem (G.mul_mem (G.inv_mem hx) (hAG hy)) hx
    refine ⟨⟨y, hyG⟩, ⟨⟨x * y * x⁻¹, hAG hy⟩, hy, ?_⟩, rfl⟩
    apply Subtype.ext
    simp [mul_assoc]

theorem rightConjugate_eq_of_alperin {G S₀ A : Subgroup X} (hS₀ : IsSylowOf 2 S₀ G)
    (hAS : A ≤ S₀)
    (hloc : ∀ D : Subgroup X, D ≤ S₀ → A ≤ D →
      IsSylowOf 2 (S₀ ⊓ Subgroup.normalizer (D : Set X)) (G ⊓ Subgroup.normalizer (D : Set X)) →
      S₀ ⊓ Subgroup.centralizer (D : Set X) ≤ D →
      ∀ n ∈ G ⊓ Subgroup.normalizer (D : Set X), rightConjugate A n = A)
    {x : X} (hx : x ∈ G) (hle : rightConjugate A x ≤ S₀) : rightConjugate A x = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀G : S₀ ≤ G := hS₀.le
  have hAG : A ≤ G := hAS.trans hS₀G
  obtain ⟨P, hP⟩ := hS₀
  set A' := A.subgroupOf G with hA'
  have hmapA : A'.map G.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAG]
  have hmemP : ∀ y : G, (y : X) ∈ S₀ → y ∈ (P : Subgroup G) := by
    intro y hy
    rw [← hP] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [← Subtype.ext hzy]
  have hA'P : A' ≤ (P : Subgroup G) := fun y hy => hmemP y (hAS hy)
  have hconj : ∀ n : G, rightConjugate A (n : X) = A →
      A'.map (MulAut.conj n⁻¹).toMonoidHom = A' := by
    intro n hn
    apply Subgroup.map_injective G.subtype_injective
    rw [map_subtype_map_conj hAG n.2, hn, hmapA]
  have hx' : A'.map (MulAut.conj (⟨x, hx⟩ : G)⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    intro y hy
    apply hmemP
    apply hle
    rw [← map_subtype_map_conj hAG hx]
    exact ⟨y, hy, rfl⟩
  obtain ⟨c, hdec, hpt⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion P hA'P hx'
  have hstep : ∀ {c : G}, CFSG.RankTwoShapes.AlperinDecomposition 2 (P : Subgroup G) A' c →
      A'.map (MulAut.conj c⁻¹).toMonoidHom = A' := by
    intro c h
    induction h with
    | one => ext y; simp
    | @step c n Q _ hQ hAQ hn ih =>
      rw [ih] at hAQ
      set D := Q.map G.subtype with hD
      have hDQ : D.subgroupOf G = Q := by
        exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective Q
      have hDG : D ≤ G := Subgroup.map_subtype_le Q
      have hNmap : (Subgroup.normalizer (Q : Set G)).map G.subtype =
          G ⊓ Subgroup.normalizer (D : Set X) := by
        rw [← hDQ, ← Subgroup.subgroupOf_normalizer_eq hDG, Subgroup.subgroupOf_map_subtype,
          inf_comm]
      have hDS : D ≤ S₀ := by
        rw [← hP]
        exact Subgroup.map_mono hQ.1
      have hAD : A ≤ D := by
        rw [← hmapA]
        exact Subgroup.map_mono hAQ
      have hsylQ : IsSylowOf 2 ((P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G))
          (Subgroup.normalizer (Q : Set G)) := by
        rw [isSylowOf_iff]
        refine ⟨inf_le_right, P.isPGroup'.to_le inf_le_left, fun h2 => ?_⟩
        have hcop := hQ.2.1
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hcop
        exact hcop h2
      have hsyl : IsSylowOf 2 (S₀ ⊓ Subgroup.normalizer (D : Set X))
          (G ⊓ Subgroup.normalizer (D : Set X)) := by
        rw [← isSylowOf_map_subtype_iff G, Subgroup.map_inf_eq _ _ _ G.subtype_injective, hNmap,
          hP, ← inf_assoc, inf_eq_left.mpr hS₀G] at hsylQ
        exact hsylQ
      have hcent : S₀ ⊓ Subgroup.centralizer (D : Set X) ≤ D := by
        rintro y ⟨hyS, hyC⟩
        have hyG : y ∈ G := hS₀G hyS
        have hyP : (⟨y, hyG⟩ : G) ∈ (P : Subgroup G) := hmemP _ hyS
        have hyCQ : (⟨y, hyG⟩ : G) ∈ Subgroup.centralizer (Q : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC q ⟨q, hq, rfl⟩)
        exact ⟨_, hQ.2.2.1 ⟨hyCQ, hyP⟩, rfl⟩
      have hnD : (n : X) ∈ G ⊓ Subgroup.normalizer (D : Set X) := by
        rw [← hNmap]
        exact ⟨n, hn, rfl⟩
      have hAn := hconj n (hloc D hDS hAD hsyl hcent n hnD)
      have hcomp : (MulAut.conj (c * n)⁻¹).toMonoidHom =
          (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom := by
        ext y
        simp [mul_assoc]
      rw [hcomp, ← Subgroup.map_map, ih, hAn]
  have hpt' : ∀ a ∈ A', (MulAut.conj (⟨x, hx⟩ : G)⁻¹).toMonoidHom a =
      (MulAut.conj c⁻¹).toMonoidHom a := fun a ha => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact (hpt a ha).symm
  have hx'' : A'.map (MulAut.conj (⟨x, hx⟩ : G)⁻¹).toMonoidHom = A' := by
    refine Eq.trans ?_ (hstep hdec)
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (hpt' a ha).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hpt' a ha⟩
  rw [← map_subtype_map_conj hAG hx, hx'', hmapA]

end CFSG.ComponentClassification.AschbacherTheorem3
