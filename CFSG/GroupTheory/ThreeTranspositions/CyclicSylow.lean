module

public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open Subgroup

open scoped IsMulCommutative

private lemma mem_zpowers_of_orderOf_eq_three {G : Type*} [Group G] [Finite G] (hX : ¬ HasE9 G)
    {x y : G} (hxo : orderOf x = 3) (hyo : orderOf y = 3) (hcomm : Commute x y) :
    x ∈ Subgroup.zpowers y := by
  by_contra hxy
  have hy_not : y ∉ Subgroup.zpowers x := by
    intro hy
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hy
    have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
    have hcardy : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyo]
    have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardy, hcardx])
    rw [heq] at hxy
    exact hxy (Subgroup.mem_zpowers x)
  exact hX ⟨x, y, hxo, hyo, hcomm, hy_not⟩

theorem isCyclic_of_isPGroup_three {X : Type*} [Group X] [Finite X] (hX : ¬ HasE9 X)
    {P : Subgroup X} (hP : IsPGroup 3 P) : IsCyclic P := by
  by_contra hnc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 P) := ⟨hP⟩
  obtain ⟨S, _hSnorm, hScard, hSelem⟩ :=
    CFSG.lemma_4_5_a (R := P) (p := 3) (by norm_num) hnc
  have hSne : S ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card S = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hScard] at h1
    norm_num at h1
  obtain ⟨xS, hxSne⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := S)).mp hSne
  let x : P := xS.1
  have hxS : x ∈ S := xS.2
  have hxne : x ≠ 1 := fun h => hxSne (Subtype.ext h)
  have hx3 : x ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := S) x hxS
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hnotsub : ¬ S ≤ Subgroup.zpowers x := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hxo] at hcard
    rw [hScard] at hcard
    norm_num at hcard
  obtain ⟨y, hyS, hy_not⟩ : ∃ y ∈ S, y ∉ Subgroup.zpowers x := by
    by_contra h
    exact hnotsub fun z hz => by
      by_contra hz'
      exact h ⟨z, hz, hz'⟩
  have hyne : y ≠ 1 := by
    intro h1
    rw [h1] at hy_not
    exact hy_not (Subgroup.one_mem _)
  have hy3 : y ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := S) y hyS
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hyne
  have hcomm : Commute x y := by
    haveI : IsMulCommutative S := hSelem.toIsMulCommutative
    have h := mul_comm xS (⟨y, hyS⟩ : S)
    exact congrArg Subtype.val h
  exact hX (HasE9.map_injective P.subtype P.subtype_injective
    ⟨x, y, hxo, hyo, hcomm, hy_not⟩)

theorem mem_of_normal_of_orderOf_eq_three {X : Type*} [Group X] [Finite X] (hX : ¬ HasE9 X)
    {M : Subgroup X} [M.Normal] {y x : X} (hy : y ∈ M) (hyo : orderOf y = 3)
    (hxo : orderOf x = 3) : x ∈ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨P₁, hxP₁le⟩ := hxP.exists_le_sylow
  obtain ⟨P₂, hyP₂le⟩ := hyP.exists_le_sylow
  have hxP₁ : x ∈ (P₁ : Subgroup X) := hxP₁le (Subgroup.mem_zpowers x)
  have hyP₂ : y ∈ (P₂ : Subgroup X) := hyP₂le (Subgroup.mem_zpowers y)
  haveI : Finite (Sylow 3 X) := Sylow.finite_of_finiteIndex P₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := X) P₂ P₁
  have hy'P₁ : (MulAut.conj g) y ∈ (P₁ : Subgroup X) := by
    have hmem := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P₂ : Subgroup X) hyP₂
    rw [← Sylow.coe_subgroup_smul (g := g) (P := P₂), hg] at hmem
    simpa using hmem
  have hy'o : orderOf ((MulAut.conj g) y) = 3 := by
    rw [← hyo]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  have hy'M : (MulAut.conj g) y ∈ M := by
    rw [MulAut.conj_apply]
    exact (inferInstance : M.Normal).conj_mem y hy g
  haveI : IsCyclic (P₁ : Subgroup X) := isCyclic_of_isPGroup_three hX P₁.isPGroup'
  have hcomm : Commute x ((MulAut.conj g) y) := by
    have h := mul_comm (⟨x, hxP₁⟩ : (P₁ : Subgroup X))
      (⟨(MulAut.conj g) y, hy'P₁⟩ : (P₁ : Subgroup X))
    exact congrArg Subtype.val h
  have hxzp : x ∈ Subgroup.zpowers ((MulAut.conj g) y) :=
    mem_zpowers_of_orderOf_eq_three hX hxo hy'o hcomm
  exact (Subgroup.zpowers_le.mpr hy'M) hxzp

theorem mem_of_normal_of_three_dvd_card {X : Type*} [Group X] [Finite X] (hX : ¬ HasE9 X)
    {M : Subgroup X} [M.Normal] (hM : 3 ∣ Nat.card M) {x : X} (hxo : orderOf x = 3) : x ∈ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' (G := M) 3 hM
  have hyoX : orderOf (y : X) = 3 := by rw [Subgroup.orderOf_coe, hyo]
  exact mem_of_normal_of_orderOf_eq_three hX y.2 hyoX hxo

theorem isSimpleGroup_of_generated_by_order_three {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    (hY : ¬ HasE9 Y) (hO : CFSG.pPrimeCore 3 Y = ⊥) {S : Set Y}
    (hS : Subgroup.closure S = ⊤) (hS3 : ∀ s ∈ S, s = 1 ∨ orderOf s = 3) : IsSimpleGroup Y := by
  refine ⟨fun N hN => ?_⟩
  by_cases h3 : 3 ∣ Nat.card N
  · right
    rw [eq_top_iff, ← hS, Subgroup.closure_le]
    intro s hs
    rcases hS3 s hs with rfl | h
    · exact N.one_mem
    · exact mem_of_normal_of_three_dvd_card hY h3 h
  · left
    have hle : N ≤ CFSG.pPrimeCore 3 Y :=
      le_sSup ⟨hN, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
    rw [hO] at hle
    exact eq_bot_iff.mpr hle

end CFSG.GroupTheory.ThreeTranspositions
