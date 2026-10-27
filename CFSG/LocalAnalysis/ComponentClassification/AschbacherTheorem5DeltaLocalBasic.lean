module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBarTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveStrong

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace DeltaDatum

theorem exists_of_mem {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (a : Fin r) :
    ∃ d : DeltaDatum D Abar a, d.g = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  obtain ⟨-, -, hne', U, hU'⟩ := hΔ
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (rightConjugate A g ⊓ Subgroup.normalizer (A : Set G))
  set Hg := rightConjugate H g with hHgdef
  have hTHg : T ≤ Hg :=
    hT.le.trans (inf_le_left.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate
      ((preimage_le D _).trans Subgroup.le_normalizer) g))
  have hTA : T ≤ Subgroup.normalizer (A : Set G) := hT.le.trans inf_le_right
  have hTAHg : T ≤ Subgroup.normalizer ((A ⊓ Hg : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTA ht, Subgroup.le_normalizer (hTHg ht)⟩
  obtain ⟨P₁, hP₁, hTP₁⟩ := AschbacherTheorem3.exists_isSylowOf_le hT.isPGroup
    (le_sup_right : T ≤ (A ⊓ Hg) ⊔ T)
  have hP₀ : IsSylowOf 2 (P₁ ⊓ (A ⊓ Hg)) (A ⊓ Hg) :=
    hP₁.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTAHg)
  obtain ⟨S₁, hS₁, hP₁S₁⟩ := AschbacherTheorem3.exists_isSylowOf_le hP₁.isPGroup
    (hP₁.le.trans (sup_le_sup_right inf_le_left T))
  have hS : IsSylowOf 2 (S₁ ⊓ A) A :=
    hS₁.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTA)
  have hTS : T ≤ Subgroup.normalizer ((S₁ ⊓ A : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hP₁S₁ (hTP₁ ht)), hTA ht⟩
  have hSHg : IsSylowOf 2 (S₁ ⊓ A ⊓ Hg) (A ⊓ Hg) := by
    have hle : P₁ ⊓ (A ⊓ Hg) ≤ S₁ ⊓ A ⊓ Hg := fun x hx =>
      ⟨⟨hP₁S₁ hx.1, hx.2.1⟩, hx.2.2⟩
    have heq := hP₀.eq_of_le hle (inf_le_inf_right Hg inf_le_right)
      (hS.isPGroup.to_le inf_le_left)
    rw [heq]
    exact hP₀
  exact ⟨⟨g, hne', U, hU', T, hT, S₁ ⊓ A, hS, hTS, hSHg⟩, rfl⟩

end DeltaDatum

theorem lemma_6_5_one (hC : Counterexample G D r Abar) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) (i : Fin r) :
    U ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUH, hUel, hU4, hUC⟩ := hU
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  intro u hu
  by_contra hun
  obtain ⟨j, hj⟩ := hC.hyp.hperm u (hUH hu) i
  have hji : j ≠ i := by
    rintro rfl
    exact hun (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj)
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hun (Subgroup.one_mem _)
  obtain ⟨p, hp, q, hq, hp1, hq1, hqp⟩ :=
    AschbacherTheorem3.exists_two_ne_one (show 4 ≤ Nat.card U by rw [hU4])
  obtain ⟨v, hv, hv1, hvu⟩ : ∃ v ∈ U, v ≠ 1 ∧ v ≠ u := by
    by_cases hpu : p = u
    · exact ⟨q, hq, hq1, fun h => hqp (h.trans hpu.symm)⟩
    · exact ⟨p, hp, hp1, hpu⟩
  have huu : u * u = 1 := by rw [← pow_two]; exact hUel.2 u hu
  have hvv : v * v = 1 := by rw [← pow_two]; exact hUel.2 v hv
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left huu
  set ub := toBar D ⟨u, hUH hu⟩ with hubdef
  set vb := toBar D ⟨v, hUH hv⟩ with hvbdef
  have hinj : ∀ {x y : G} (hx : x ∈ U) (hy : y ∈ U),
      toBar D ⟨x, hUH hx⟩ = toBar D ⟨y, hUH hy⟩ → x = y := fun hx hy h =>
    congrArg Subtype.val (toBar_injOn_of_isPGroup hU2 (u := ⟨_, hUH hx⟩) (v := ⟨_, hUH hy⟩)
      hx hy h)
  have hub1 : ub ≠ 1 := fun h => hu1 (hinj hu U.one_mem (h.trans (map_one _).symm))
  have hvb1 : vb ≠ 1 := fun h => hv1 (hinj hv U.one_mem (h.trans (map_one _).symm))
  have hubvb : ub ≠ vb := fun h => hvu (hinj hu hv h).symm
  have hubub : ub * ub = 1 := by
    rw [hubdef, ← map_mul, show (⟨u, hUH hu⟩ : H) * ⟨u, hUH hu⟩ = 1 from Subtype.ext huu,
      map_one]
  have hvbvb : vb * vb = 1 := by
    rw [hvbdef, ← map_mul, show (⟨v, hUH hv⟩ : H) * ⟨v, hUH hv⟩ = 1 from Subtype.ext hvv,
      map_one]
  have hcomm : Commute ub vb := by
    change ub * vb = vb * ub
    rw [hubdef, hvbdef, ← map_mul, ← map_mul]
    congr 1
    have h := congrArg Subtype.val (hUel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    exact Subtype.ext h
  have hubU : ub ∈ bar D U := toBar_mem_bar D (h := ⟨u, hUH hu⟩) hu
  have hvbU : vb ∈ bar D U := toBar_mem_bar D (h := ⟨v, hUH hv⟩) hv
  have hAj : rightConjugate A u = aschbacherThm5Preimage D (Abar j) := by
    change A.map (MulAut.conj u⁻¹).toMonoidHom = _
    rw [huinv]
    exact hj
  have hbarAj : rightConjugate (bar D A) ub = bar D (aschbacherThm5Preimage D (Abar j)) := by
    rw [← hAj]
    exact (bar_rightConjugate A ⟨u, hUH hu⟩).symm
  obtain ⟨m, K, -, hK, -, hKgen⟩ := bar_factor_components hC.hyp i
  have hmoved : ∀ l, AschbacherComponentAction.rightComponent (K l) ub ≠ K l := by
    intro l hl
    have hKA : K l ≤ bar D A := (hK l).2
    have hKAj : K l ≤ bar D (aschbacherThm5Preimage D (Abar j)) := by
      rw [← hbarAj]
      have h1 : AschbacherComponentAction.rightComponent (K l) ub ≤ rightConjugate (bar D A) ub :=
        Subgroup.map_mono hKA
      rw [hl] at h1
      exact h1
    have hcen := Strong.bar_factor_le_centralizer hC.hyp (Ne.symm hji)
    have : Group.IsPerfect (K l) := component_perfect (hK l).1
    have : Nontrivial (K l) := (K l).nontrivial_iff_ne_bot.mpr (component_ne_bot (hK l).1)
    apply Group.IsPerfect.not_isMulCommutative (K l)
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hcen (hKAj x.2))) y (hKA y.2)).symm
  have hKle : ∀ l, K l ≤ AschbacherToolkit.centralizerJoin (bar D U) := fun l =>
    AschbacherToolkit.moved_component_le_centralizerJoin (bar D U) (K l) ub vb (hK l).1 hubU hvbU
      hubub hvbvb hub1 hvb1 hubvb hcomm (hmoved l)
  have hAle : bar D A ≤ AschbacherToolkit.centralizerJoin (bar D U) := by
    rw [← hKgen]
    exact iSup_le hKle
  set X := (AschbacherToolkit.centralizerJoin (U.subgroupOf H)).map H.subtype with hXdef
  have hcj := AschbacherToolkit.centralizerJoin_quotient_of_isPGroup (coreIn D) (coreIn_odd D)
    (U := U.subgroupOf H) hU2.comap_subtype
  have hXbar : bar D X = AschbacherToolkit.centralizerJoin (bar D U) := by
    have hsub : X.subgroupOf H = AschbacherToolkit.centralizerJoin (U.subgroupOf H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    change (X.subgroupOf H).map (toBar D) = AschbacherToolkit.centralizerJoin
      ((U.subgroupOf H).map (toBar D))
    rw [hsub]
    exact hcj.symm
  have hXH : X ≤ H := Subgroup.map_subtype_le _
  have hXHg : X ≤ rightConjugate H g := by
    rw [hXdef, Subgroup.map_le_iff_le_comap]
    apply iSup₂_le
    intro w hw1 y hy
    have hwU : (((w : H) : G)) ∈ U := w.2
    have hw1' : ((w : H) : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
    refine hUC _ hwU hw1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have hAX := le_sup_core_of_bar_le ((preimage_le D _).trans Subgroup.le_normalizer)
    (hAle.trans hXbar.symm.le)
  exact hg (AschbacherTheorem3.rightConjugate_eq_of_mem
    (mem_normalizer_of_le_sup hC i g X hXHg hXH hAX))

end CFSG.ComponentClassification.AschbacherTheorem5
