module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.TwoGroupCase.TightEmbedding
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

variable {G : Type*} [Group G]

section Components

@[expose] def deltaComp (J A : Subgroup G) : Set (Subgroup G) :=
  {B | Relation.ReflTransGen (commutingAdj J) A B}

@[expose] def ControlC (J : Subgroup G) : Prop :=
  ∀ t : G, t ≠ 1 → IsPGroup 2 (Subgroup.zpowers t) →
    ∀ A ∈ conjugateSet J, ∀ B ∈ conjugateSet J,
      A ≤ Subgroup.centralizer ({t} : Set G) → B ≤ Subgroup.centralizer ({t} : Set G) →
      B ∈ deltaComp J A

theorem self_mem_conjugateSet (J : Subgroup G) : J ∈ conjugateSet J :=
  ⟨1, by
    change J = conjSubgroup 1⁻¹ J
    rw [inv_one, conjSubgroup_one]⟩

theorem conjSubgroup_mem_conjugateSet {J A : Subgroup G} (g : G) (hA : A ∈ conjugateSet J) :
    conjSubgroup g A ∈ conjugateSet J := by
  obtain ⟨h, rfl⟩ := hA
  refine ⟨h * g⁻¹, ?_⟩
  change _ = conjSubgroup _ J
  rw [show (h * g⁻¹)⁻¹ = g * h⁻¹ by group, ← conjSubgroup_conjSubgroup]

theorem commutingAdj_conjSubgroup {J A B : Subgroup G} (h : commutingAdj J A B) (g : G) :
    commutingAdj J (conjSubgroup g A) (conjSubgroup g B) := by
  obtain ⟨hA, hB, hne, hcomm⟩ := h
  refine ⟨conjSubgroup_mem_conjugateSet g hA, conjSubgroup_mem_conjugateSet g hB, ?_, ?_⟩
  · intro heq
    apply hne
    have := congrArg (conjSubgroup g⁻¹) heq
    rwa [conjSubgroup_inv_conjSubgroup, conjSubgroup_inv_conjSubgroup] at this
  · intro a ha b hb
    have ha' := mem_conjSubgroup_iff.mp ha
    have hb' := mem_conjSubgroup_iff.mp hb
    have := hcomm _ ha' _ hb'
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group

theorem conjSubgroup_mem_deltaComp {J A B : Subgroup G} (g : G) (h : B ∈ deltaComp J A) :
    conjSubgroup g B ∈ deltaComp J (conjSubgroup g A) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (commutingAdj_conjSubgroup hbc g)

theorem eq_of_mem_deltaComp_of_edgeless {J A B : Subgroup G} (hE : ∀ X Y, ¬ commutingAdj J X Y)
    (h : B ∈ deltaComp J A) : B = A := by
  induction h with
  | refl => rfl
  | tail _ hbc _ => exact absurd hbc (hE _ _)

theorem ControlC.conjSubgroup_mem_deltaComp {J : Subgroup G} (hC : ControlC J) {P A : Subgroup G}
    (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥) (hA : A ∈ conjugateSet J)
    (hAP : A ≤ Subgroup.centralizer (P : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) : conjSubgroup n A ∈ deltaComp J A := by
  obtain ⟨⟨t, htP⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hz2 : IsPGroup 2 (Subgroup.zpowers t) := by
    have hle : Subgroup.zpowers t ≤ P := (Subgroup.zpowers_le).mpr htP
    exact hP2.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hAt : A ≤ Subgroup.centralizer ({t} : Set G) :=
    hAP.trans (Subgroup.centralizer_le (by simpa using htP))
  refine hC t ht1' hz2 A hA _ (conjSubgroup_mem_conjugateSet n hA) hAt ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hxa : n⁻¹ * x * n ∈ A := mem_conjSubgroup_iff.mp hx
  have hn' : n⁻¹ * y * n ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) (y)).mp htP
    simpa using this
  have := Subgroup.mem_centralizer_iff.mp (hAP hxa) _ hn'
  calc y * x = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by rw [this]
    _ = x * y := by group


theorem commutingAdj_symm {J A B : Subgroup G} (h : commutingAdj J A B) : commutingAdj J B A :=
  ⟨h.2.1, h.1, fun e => h.2.2.1 e.symm, fun b hb a ha => (h.2.2.2 a ha b hb).symm⟩

theorem deltaComp_symm {J A B : Subgroup G} (h : B ∈ deltaComp J A) : A ∈ deltaComp J B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (commutingAdj_symm hbc) ih

theorem deltaComp_eq_of_mem {J A B : Subgroup G} (h : B ∈ deltaComp J A) :
    deltaComp J B = deltaComp J A := by
  ext C
  constructor
  · intro hC
    exact Relation.ReflTransGen.trans h hC
  · intro hC
    exact Relation.ReflTransGen.trans (deltaComp_symm h) hC

@[expose] def compSpan (J A : Subgroup G) : Subgroup G := ⨆ B ∈ deltaComp J A, B

theorem le_compSpan {J A B : Subgroup G} (h : B ∈ deltaComp J A) : B ≤ compSpan J A :=
  le_iSup₂ (f := fun B (_ : B ∈ deltaComp J A) => B) B h

theorem compSpan_conjSubgroup (J A : Subgroup G) (g : G) :
    compSpan J (conjSubgroup g A) = conjSubgroup g (compSpan J A) := by
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    have h1 : conjSubgroup g⁻¹ B ∈ deltaComp J A := by
      have := conjSubgroup_mem_deltaComp g⁻¹ hB
      rwa [conjSubgroup_inv_conjSubgroup] at this
    have h2 := conjSubgroup_mono (g := g) (le_compSpan h1)
    rwa [conjSubgroup_conjSubgroup_inv] at h2
  · show Subgroup.map _ _ ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun B hB => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_compSpan (conjSubgroup_mem_deltaComp g hB)

theorem compSpan_eq_of_mem {J A B : Subgroup G} (h : B ∈ deltaComp J A) :
    compSpan J B = compSpan J A := by
  unfold compSpan
  rw [deltaComp_eq_of_mem h]

theorem mem_normalizer_compSpan {J A : Subgroup G} {g : G} (h : conjSubgroup g A ∈ deltaComp J A) :
    g ∈ Subgroup.normalizer (compSpan J A : Set G) := by
  rw [← conjSubgroup_eq_self_iff, ← compSpan_conjSubgroup, compSpan_eq_of_mem h]

end Components

section Standard

private theorem normalizer_le_normalizer_centralizer (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ c ∈ Subgroup.centralizer (J : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g hg h
  · intro h'
    have := key g⁻¹ (inv_mem hg) _ h'
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

private theorem isPGroup_two_zpowers_of_orderOf_eq_two {b : G} (hb : orderOf b = 2) :
    IsPGroup 2 (Subgroup.zpowers b) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; norm_num)

theorem le_centralizer_of_mem_centralizer_compSpan {J A : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.centralizer (compSpan J A : Set G)) :
    A ≤ Subgroup.centralizer ({b} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (Subgroup.mem_centralizer_iff.mp hb x (le_compSpan Relation.ReflTransGen.refl hx)).symm

theorem conjSubgroup_le_centralizer_of_conj_mem {J A : Subgroup G} {b g : G}
    (hb : g⁻¹ * b * g ∈ Subgroup.centralizer (compSpan J A : Set G)) :
    conjSubgroup g A ≤ Subgroup.centralizer ({b} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h1 := Subgroup.mem_centralizer_iff.mp hb _
    (le_compSpan Relation.ReflTransGen.refl (mem_conjSubgroup_iff.mp hx))
  calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [← h1]
    _ = x * y := by group

theorem ControlC.odd_card_inf_conjSubgroup_compCentralizer [Finite G] {J A : Subgroup G}
    (hC : ControlC J) (hA : A ∈ conjugateSet J) {g : G}
    (hg : g ∉ Subgroup.normalizer
      (Subgroup.centralizer (compSpan J A : Set G) : Set G)) :
    Odd (Nat.card (↥(Subgroup.centralizer (compSpan J A : Set G) ⊓
      conjSubgroup g (Subgroup.centralizer (compSpan J A : Set G))))) := by
  by_contra hodd
  have h2 := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have := Fact.mk Nat.prime_two
  obtain ⟨⟨b, hb⟩, hb2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hb2' : orderOf b = 2 := by rw [← Subgroup.orderOf_mk b hb]; exact hb2
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb2'
  obtain ⟨hbR, hbRg⟩ := hb
  have hcomp := hC b hb1 (isPGroup_two_zpowers_of_orderOf_eq_two hb2') A hA (conjSubgroup g A)
    (conjSubgroup_mem_conjugateSet g hA) (le_centralizer_of_mem_centralizer_compSpan hbR)
    (conjSubgroup_le_centralizer_of_conj_mem (mem_conjSubgroup_iff.mp hbRg))
  exact hg (normalizer_le_normalizer_centralizer _ (mem_normalizer_compSpan hcomp))

theorem ControlC.normalizer_compCentralizer_le [Finite G] {J A : Subgroup G} (hC : ControlC J)
    (hA : A ∈ conjugateSet J) {b : G} (hb2 : orderOf b = 2)
    (hbR : b ∈ Subgroup.centralizer (compSpan J A : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.centralizer (compSpan J A : Set G) : Set G)) :
    n ∈ Subgroup.normalizer (compSpan J A : Set G) := by
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb2
  have hnb : n⁻¹ * b * n ∈ Subgroup.centralizer (compSpan J A : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) b).mp hbR
    simpa using this
  exact mem_normalizer_compSpan (hC b hb1 (isPGroup_two_zpowers_of_orderOf_eq_two hb2) A hA
    (conjSubgroup n A) (conjSubgroup_mem_conjugateSet n hA)
    (le_centralizer_of_mem_centralizer_compSpan hbR)
    (conjSubgroup_le_centralizer_of_conj_mem hnb))

theorem standardComponentIsStandard_of_control [Finite G] {J : Subgroup G} {z : G}
    (hJ : IsQuasisimple J) (hz : orderOf z = 2) (hzC : z ∈ Subgroup.centralizer (J : Set G))
    (hC : ControlC J) (hE : ∀ X Y, ¬ commutingAdj J X Y) :
    standardComponentIsStandard J := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hJz : J ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp hzC x hx).symm
  have hNC : Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) ≤
      Subgroup.normalizer (J : Set G) := by
    intro n hn
    rw [← conjSubgroup_eq_self_iff]
    have hnz : n⁻¹ * z * n ∈ Subgroup.centralizer (J : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) z).mp hzC
      simpa using this
    have hle : conjSubgroup n J ≤ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := Subgroup.mem_centralizer_iff.mp hnz _ (mem_conjSubgroup_iff.mp hx)
      calc y * x = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
        _ = x * y := by group
    exact eq_of_mem_deltaComp_of_edgeless hE
      (hC z hz1 (isPGroup_two_zpowers_of_orderOf_eq_two hz) J (self_mem_conjugateSet J)
        (conjSubgroup n J) (conjSubgroup_mem_conjugateSet n (self_mem_conjugateSet J)) hJz hle)
  refine ⟨hJ, ?_, ?_, le_antisymm hNC (normalizer_le_normalizer_centralizer J), ?_⟩
  ·
    have h1 : orderOf (⟨z, hzC⟩ : Subgroup.centralizer (J : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk, hz]
    exact even_iff_two_dvd.mpr (h1 ▸ orderOf_dvd_natCard _)
  ·
    intro g hg
    by_contra hodd
    have heven := Nat.not_odd_iff_even.mp hodd
    have h2 : 2 ∣ Nat.card (↥(Subgroup.centralizer (J : Set G) ⊓
        (Subgroup.centralizer (J : Set G)).map (MulAut.conj g).toMonoidHom)) :=
      even_iff_two_dvd.mp heven
    have := Fact.mk Nat.prime_two
    obtain ⟨⟨b, hb⟩, hb2⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hb2' : orderOf b = 2 := by rw [← Subgroup.orderOf_mk b hb]; exact hb2
    have hb1 : b ≠ 1 := by
      rintro rfl
      simp at hb2'
    obtain ⟨hbC, hbCg⟩ := hb
    have hJb : J ≤ Subgroup.centralizer ({b} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hbC x hx).symm
    have hJgb : conjSubgroup g J ≤ Subgroup.centralizer ({b} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hbg : g⁻¹ * y * g ∈ Subgroup.centralizer (J : Set G) := mem_conjSubgroup_iff.mp hbCg
      have h1 := Subgroup.mem_centralizer_iff.mp hbg _ (mem_conjSubgroup_iff.mp hx)
      calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = x * y := by group
    have hcomp := hC b hb1 (isPGroup_two_zpowers_of_orderOf_eq_two hb2') J
      (self_mem_conjugateSet J) (conjSubgroup g J)
      (conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet J)) hJb hJgb
    have hgJ : conjSubgroup g J = J := eq_of_mem_deltaComp_of_edgeless hE hcomp
    exact hg (normalizer_le_normalizer_centralizer J (conjSubgroup_eq_self_iff.mp hgJ))
  ·
    intro g hbot
    have hbot' : ⁅J, conjSubgroup g J⁆ = ⊥ := hbot
    by_cases hg : conjSubgroup g J = J
    · rw [hg] at hbot'
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot'
      have hcomm : ∀ a b : J, a * b = b * a := by
        intro a b
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hle a.2) b b.2).symm
      have hc : commutator J = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hcomm y x
      have htop : (⊥ : Subgroup J) = ⊤ := hc.symm.trans hJ.1
      have hsub : Subsingleton J := by
        refine ⟨fun a b => ?_⟩
        have ha : a ∈ (⊥ : Subgroup J) := htop ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup J) := htop ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      have : Nontrivial (J ⧸ Subgroup.center J) := hJ.2.toNontrivial
      have hsub' : Subsingleton (J ⧸ Subgroup.center J) := inferInstance
      exact not_subsingleton _ hsub'
    · refine hE J (conjSubgroup g J) ⟨self_mem_conjugateSet J,
        conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet J), fun h => hg h.symm, ?_⟩
      intro a ha b hb
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot'
      exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

end Standard

end CFSG.ClassicalInvolution
