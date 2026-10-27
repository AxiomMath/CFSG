module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Components
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open Subgroup CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped commutatorElement

section Solvable

variable {G : Type*} [Group G]

theorem isSolvable_of_le_sup_of_commute {X C K : Subgroup G}
    (hc : ∀ x ∈ X, ∀ c ∈ C, Commute x c) (hC : Group.IsSolvable ↥C)
    (hK : K ≤ X ⊔ C) (hKX : Group.IsSolvable ↥(K ⊓ X)) : Group.IsSolvable ↥K := by
  classical
  set Y : Subgroup G := X ⊔ C with hY
  set N : Subgroup ↥Y := X.subgroupOf Y with hN
  have hdec : ∀ y ∈ Y, ∃ x ∈ X, ∃ c ∈ C, y = x * c := fun y hy =>
    exists_mul_of_mem_sup_of_commute hc hy
  haveI : N.Normal := ⟨fun n hn y => by
    obtain ⟨x, hx, c, hc', hxc⟩ := hdec y.1 y.2
    have hn' : (n : G) ∈ X := hn
    show ((y * n * y⁻¹ : ↥Y) : G) ∈ X
    have e : ((y * n * y⁻¹ : ↥Y) : G) = x * (n : G) * x⁻¹ := by
      have h1 : (c : G) * (n : G) = (n : G) * c := ((hc n hn' c hc').eq).symm
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxc]
      calc x * c * (n : G) * (x * c)⁻¹ = x * (c * (n : G)) * c⁻¹ * x⁻¹ := by group
        _ = x * ((n : G) * c) * c⁻¹ * x⁻¹ := by rw [h1]
        _ = x * (n : G) * x⁻¹ := by group
    rw [e]
    exact X.mul_mem (X.mul_mem hx hn') (X.inv_mem hx)⟩
  let j : ↥C →* ↥Y ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion (le_sup_right : C ≤ Y))
  have hj : Function.Surjective j := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, hx, c, hc', hxc⟩ := hdec y.1 y.2
    refine ⟨⟨c, hc'⟩, ?_⟩
    show (QuotientGroup.mk' N) (Subgroup.inclusion le_sup_right ⟨c, hc'⟩) = QuotientGroup.mk y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_right ⟨c, hc'⟩)⁻¹ * y : ↥Y) ∈ N
    show (((Subgroup.inclusion le_sup_right ⟨c, hc'⟩)⁻¹ * y : ↥Y) : G) ∈ X
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hxc]
    show c⁻¹ * (x * c) ∈ X
    have h1 : c⁻¹ * x = x * c⁻¹ := ((hc x hx c⁻¹ (C.inv_mem hc')).eq).symm
    rw [← mul_assoc, h1, mul_assoc, inv_mul_cancel, mul_one]
    exact hx
  haveI : Group.IsSolvable (↥Y ⧸ N) := Group.isSolvable_of_surjective hj
  let f : ↥K →* ↥Y ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hK)
  have hker : Group.IsSolvable ↥f.ker := by
    let e : ↥f.ker →* ↥(K ⊓ X) :=
      { toFun := fun k => ⟨(k.1 : G), k.1.2, by
          have hk := k.2
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at hk
          exact hk⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have he : Function.Injective e := fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥(K ⊓ X) => (w : G)) hab
    exact Group.isSolvable_of_isSolvable_injective he
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

end Solvable

section Frame2

variable {G MA MB : Type*} [Group G] [Group MA] [Group MB] {ψA : MA →* G} {ψB : MB →* G}

theorem range_le_centralizer_range₂ (hcomm : ∀ x y, Commute (ψA x) (ψB y)) :
    ψB.range ≤ centralizer (ψA.range : Set G) := by
  rintro _ ⟨y, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  exact (hcomm x y).eq

theorem sup_le_normalizer_left₂ (hcomm : ∀ x y, Commute (ψA x) (ψB y)) :
    ψA.range ⊔ ψB.range ≤ normalizer (ψA.range : Set G) :=
  sup_le le_normalizer ((range_le_centralizer_range₂ hcomm).trans (centralizer_le_normalizer _))

theorem sup_le_normalizer_right₂ (hcomm : ∀ x y, Commute (ψA x) (ψB y)) :
    ψA.range ⊔ ψB.range ≤ normalizer (ψB.range : Set G) := by
  rw [sup_comm]
  exact sup_le_normalizer_left₂ fun x y => (hcomm y x).symm

theorem map_conj_le_or_le_of_frame [Finite MA] (hQ : CFSG.IsQuasisimple MA)
    (hA : Function.Injective ψA) (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {g : G}
    (hg : g ∈ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G)) :
    ψA.range.map (MulAut.conj g : G →* G) ≤ ψA.range ∨
      ψA.range.map (MulAut.conj g : G →* G) ≤ ψB.range := by
  classical
  set A := ψA.range with hAdef
  set B := ψB.range with hBdef
  set X := A ⊔ B with hXdef
  set φ : MA →* G := (MulAut.conj g : G →* G).comp ψA with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective.comp hA
  set N := A.map (MulAut.conj g : G →* G) with hNdef
  have hNφ : N = φ.range := by rw [hNdef, hφ, MonoidHom.range_comp]
  have hXg : X.map (MulAut.conj g : G →* G) = X := mem_normalizer_iff_map_conj_eq.1 hg
  have hNX : N ≤ X := by
    rw [← hXg]
    exact map_mono le_sup_left
  have hXA : X ≤ normalizer (A : Set G) := sup_le_normalizer_left₂ hcomm
  have hXB : X ≤ normalizer (B : Set G) := sup_le_normalizer_right₂ hcomm
  have hXN : X ≤ normalizer (N : Set G) := by
    calc X = X.map (MulAut.conj g : G →* G) := hXg.symm
      _ ≤ (normalizer (A : Set G)).map (MulAut.conj g : G →* G) := map_mono hXA
      _ ≤ normalizer (N : Set G) := le_normalizer_map _
  have hABc : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y
  have hperf : ⁅N, N⁆ = N := by
    rw [hNφ, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
      hQ.1.commutator_eq_top]
  have hNsup : N ≤ (N ⊓ A) ⊔ (N ⊓ B) := by
    calc N = ⁅N, N⁆ := hperf.symm
      _ ≤ (N ⊓ A) ⊔ (N ⊓ B) := ?_
    rw [commutator_le]
    intro n hn n' hn'
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hABc (hNX hn')
    have hnX := hNX hn
    have haX : a ∈ X := le_sup_left (a := A) ha
    have hbX : b ∈ X := le_sup_right (b := B) hb
    have h1 : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ A := by
      refine ⟨?_, A.mul_mem (conj_mem_of_mem_normalizer (hXA hnX) ha) (A.inv_mem ha)⟩
      have : a * n⁻¹ * a⁻¹ ∈ N := conj_mem_of_mem_normalizer (hXN haX) (N.inv_mem hn)
      have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
      rw [e]
      exact N.mul_mem hn this
    have h2 : n * b * n⁻¹ * b⁻¹ ∈ N ⊓ B := by
      refine ⟨?_, B.mul_mem (conj_mem_of_mem_normalizer (hXB hnX) hb) (B.inv_mem hb)⟩
      have : b * n⁻¹ * b⁻¹ ∈ N := conj_mem_of_mem_normalizer (hXN hbX) (N.inv_mem hn)
      have e : n * b * n⁻¹ * b⁻¹ = n * (b * n⁻¹ * b⁻¹) := by group
      rw [e]
      exact N.mul_mem hn this
    have h3 : a * (n * b * n⁻¹ * b⁻¹) * a⁻¹ ∈ N ⊓ B :=
      ⟨conj_mem_of_mem_normalizer (hXN haX) h2.1, conj_mem_of_mem_normalizer (hXB haX) h2.2⟩
    have e : ⁅n, a * b⁆ = (n * a * n⁻¹ * a⁻¹) * (a * (n * b * n⁻¹ * b⁻¹) * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mem_sup_left h1) (mem_sup_right h3)
  set U := (N ⊓ A).comap φ with hU
  set V := (N ⊓ B).comap φ with hV
  have hφN : ∀ m, φ m ∈ N := fun m => by rw [hNφ]; exact ⟨m, rfl⟩
  have hUn : U.Normal := ⟨fun u hu m => by
    show φ (m * u * m⁻¹) ∈ N ⊓ A
    rw [map_mul, map_mul, map_inv]
    exact ⟨conj_mem_of_mem_normalizer (hXN (hNX (hφN m))) hu.1,
      conj_mem_of_mem_normalizer (hXA (hNX (hφN m))) hu.2⟩⟩
  have hVn : V.Normal := ⟨fun v hv m => by
    show φ (m * v * m⁻¹) ∈ N ⊓ B
    rw [map_mul, map_mul, map_inv]
    exact ⟨conj_mem_of_mem_normalizer (hXN (hNX (hφN m))) hv.1,
      conj_mem_of_mem_normalizer (hXB (hNX (hφN m))) hv.2⟩⟩
  have hdec : ∀ m : MA, ∃ u ∈ U, ∃ v ∈ V, m = u * v := by
    intro m
    have hc : ∀ x ∈ N ⊓ A, ∀ y ∈ N ⊓ B, Commute x y := fun x hx y hy => hABc x hx.2 y hy.2
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup_of_commute hc (hNsup (hφN m))
    have hxN : x ∈ φ.range := hNφ ▸ hx.1
    have hyN : y ∈ φ.range := hNφ ▸ hy.1
    obtain ⟨u, rfl⟩ := hxN
    obtain ⟨v, rfl⟩ := hyN
    refine ⟨u, hx, v, hy, hφinj ?_⟩
    rw [hxy, map_mul]
  rcases le_center_or_eq_top_of_isQuasisimple hQ U with hUc | hUt
  · rcases le_center_or_eq_top_of_isQuasisimple hQ V with hVc | hVt
    · exfalso
      obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hQ
      apply hxy
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec x
      have hz : u * v ∈ center MA := mul_mem (hUc hu) (hVc hv)
      exact (mem_center_iff.1 hz y).symm
    · right
      intro n hn
      rw [hNφ] at hn
      obtain ⟨m, rfl⟩ := hn
      have : m ∈ V := hVt ▸ mem_top m
      exact this.2
  · left
    intro n hn
    rw [hNφ] at hn
    obtain ⟨m, rfl⟩ := hn
    have : m ∈ U := hUt ▸ mem_top m
    exact this.2

theorem range_ne_range₂ (hQ : CFSG.IsQuasisimple MA) (hA : Function.Injective ψA)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) : ψA.range ≠ ψB.range := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hQ
  apply hxy
  have hy : ψA y ∈ ψB.range := h ▸ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hy
  apply hA
  rw [map_mul, map_mul, ← hz]
  exact (hcomm x z).eq

theorem map_conj_swap_of_frame [Finite MA] [Finite MB] (hQA : CFSG.IsQuasisimple MA)
    (hQB : CFSG.IsQuasisimple MB) (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {g : G}
    (hg : g ∈ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G)) :
    (ψA.range.map (MulAut.conj g : G →* G) = ψA.range ∧
        ψB.range.map (MulAut.conj g : G →* G) = ψB.range) ∨
      (ψA.range.map (MulAut.conj g : G →* G) = ψB.range ∧
        ψB.range.map (MulAut.conj g : G →* G) = ψA.range) := by
  classical
  have hcomm' : ∀ y x, Commute (ψB y) (ψA x) := fun y x => (hcomm x y).symm
  have hg' : g ∈ normalizer ((ψB.range ⊔ ψA.range : Subgroup G) : Set G) := by
    rwa [sup_comm]
  have h1 := map_conj_le_or_le_of_frame hQA hA hcomm hg
  have h2 := map_conj_le_or_le_of_frame hQB hB hcomm' hg'
  have hfA : Finite ψA.range := Finite.of_surjective _ ψA.rangeRestrict_surjective
  have hfB : Finite ψB.range := Finite.of_surjective _ ψB.rangeRestrict_surjective
  set A := ψA.range with hAdef
  set B := ψB.range with hBdef
  have hXg : (A ⊔ B).map (MulAut.conj g : G →* G) = A ⊔ B := mem_normalizer_iff_map_conj_eq.1 hg
  have hcA : Nat.card (A.map (MulAut.conj g : G →* G)) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm
  have hcB : Nat.card (B.map (MulAut.conj g : G →* G)) = Nat.card B :=
    (Nat.card_congr (B.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    exact ⟨eq_of_le_of_card_ge h1 hcA.ge, eq_of_le_of_card_ge h2 hcB.ge⟩
  · exfalso
    have hX : A ⊔ B ≤ A := by
      rw [← hXg, Subgroup.map_sup]
      exact sup_le h1 h2
    have hBA : B ≤ A := le_sup_right.trans hX
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hQB
    apply hxy
    obtain ⟨a, ha⟩ := hBA ⟨x, rfl⟩
    apply hB
    rw [map_mul, map_mul, ← ha]
    exact (hcomm a y).eq
  · exfalso
    have hX : A ⊔ B ≤ B := by
      rw [← hXg, Subgroup.map_sup]
      exact sup_le h1 h2
    have hAB : A ≤ B := le_sup_left.trans hX
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hQA
    apply hxy
    obtain ⟨b, hb⟩ := hAB ⟨x, rfl⟩
    apply hA
    rw [map_mul, map_mul, ← hb]
    exact (hcomm y b).eq.symm
  · right
    have c1 : Nat.card A ≤ Nat.card B := hcA.symm.le.trans (Subgroup.card_le_of_le h1)
    have c2 : Nat.card B ≤ Nat.card A := hcB.symm.le.trans (Subgroup.card_le_of_le h2)
    exact ⟨eq_of_le_of_card_ge h1 (by rw [hcA]; exact c2),
      eq_of_le_of_card_ge h2 (by rw [hcB]; exact c1)⟩

theorem isSolvable_of_le_normalizer_frame₂ [Finite MA] [Finite MB] (hQA : CFSG.IsQuasisimple MA)
    (hQB : CFSG.IsQuasisimple MB)
    (hOA : Group.IsSolvable (MulAut MA ⧸ (MulAut.conj : MA →* MulAut MA).range))
    (hOB : Group.IsSolvable (MulAut MB ⧸ (MulAut.conj : MB →* MulAut MB).range))
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {Gh : Subgroup G}
    (hXG : ψA.range ⊔ ψB.range ≤ Gh)
    (hC : Group.IsSolvable ↥(centralizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) ⊓ Gh))
    {P : Subgroup G} (hPG : P ≤ Gh)
    (hPN : P ≤ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G))
    (hPX : Group.IsSolvable ↥(P ⊓ (ψA.range ⊔ ψB.range))) : Group.IsSolvable ↥P := by
  classical
  set A := ψA.range with hAdef
  set B := ψB.range with hBdef
  set X := A ⊔ B with hXdef
  have hABc : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y
  have hAB := range_ne_range₂ hQA hA hcomm
  have hswap := fun {g : G} (hg : g ∈ normalizer (X : Set G)) =>
    map_conj_swap_of_frame hQA hQB hA hB hcomm hg
  have hσmul : ∀ p q : P,
      (if A.map (MulAut.conj ((p * q : P) : G) : G →* G) = A then (1 : ℤˣ) else -1) =
        (if A.map (MulAut.conj (p : G) : G →* G) = A then 1 else -1) *
          (if A.map (MulAut.conj (q : G) : G →* G) = A then 1 else -1) := by
    intro p q
    have hp := hPN p.2
    have hq := hPN q.2
    have e : A.map (MulAut.conj ((p * q : P) : G) : G →* G) =
        (A.map (MulAut.conj (q : G) : G →* G)).map (MulAut.conj (p : G) : G →* G) := by
      rw [Subgroup.coe_mul, map_conj_mul]
    rcases hswap hq with ⟨hqA, hqB⟩ | ⟨hqA, hqB⟩
    · rw [e, hqA, if_pos rfl, mul_one]
    · rw [e, hqA, if_neg (Ne.symm hAB)]
      rcases hswap hp with ⟨hpA, hpB⟩ | ⟨hpA, hpB⟩
      · rw [hpB, if_neg (Ne.symm hAB), if_pos hpA, one_mul]
      · rw [hpB, if_pos rfl, if_neg (by rw [hpA]; exact Ne.symm hAB)]
        decide
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  let σ : ↥P →* ℤˣ :=
    { toFun := fun p => if A.map (MulAut.conj (p : G) : G →* G) = A then 1 else -1
      map_one' := by
        rw [if_pos]
        rw [OneMemClass.coe_one, map_one]
        ext x
        simp
      map_mul' := hσmul }
  set P₀ := σ.ker with hP₀
  have hfixA : ∀ p : P₀, A.map (MulAut.conj ((p : P) : G) : G →* G) = A := by
    intro p
    by_contra h
    have hp := p.2
    rw [MonoidHom.mem_ker] at hp
    simp only [σ, MonoidHom.coe_mk, OneHom.coe_mk, if_neg h] at hp
    exact hneg hp
  have hfixB : ∀ p : P₀, B.map (MulAut.conj ((p : P) : G) : G →* G) = B := by
    intro p
    rcases hswap (hPN (p : P).2) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd ((hfixA p).symm.trans h) hAB
  suffices h0 : Group.IsSolvable ↥P₀ from
    Group.isSolvable_of_ker_le_range P₀.subtype σ (by rw [Subgroup.range_subtype])
  let ρA : ↥P₀ →* MulAut MA :=
    { toFun := fun p => frameAut ψA hA ((p : P) : G) (hfixA p)
      map_one' := by
        ext m
        apply hA
        rw [frameAut_spec]
        simp
      map_mul' := fun p q => by
        have := frameAut_mul ψA hA (hfixA p) (hfixA q) (hfixA (p * q))
        exact this }
  let ρB : ↥P₀ →* MulAut MB :=
    { toFun := fun p => frameAut ψB hB ((p : P) : G) (hfixB p)
      map_one' := by
        ext m
        apply hB
        rw [frameAut_spec]
        simp
      map_mul' := fun p q => by
        have := frameAut_mul ψB hB (hfixB p) (hfixB q) (hfixB (p * q))
        exact this }
  have : Group.IsSolvable (MulAut MA ⧸ (MulAut.conj : MA →* MulAut MA).range) := hOA
  have : Group.IsSolvable (MulAut MB ⧸ (MulAut.conj : MB →* MulAut MB).range) := hOB
  let Θ : ↥P₀ →* (MulAut MA ⧸ (MulAut.conj : MA →* MulAut MA).range) ×
      (MulAut MB ⧸ (MulAut.conj : MB →* MulAut MB).range) :=
    ((QuotientGroup.mk' (MulAut.conj : MA →* MulAut MA).range).comp ρA).prod
      ((QuotientGroup.mk' (MulAut.conj : MB →* MulAut MB).range).comp ρB)
  suffices hK : Group.IsSolvable ↥Θ.ker from
    Group.isSolvable_of_ker_le_range Θ.ker.subtype Θ (by rw [Subgroup.range_subtype])
  have hdec : ∀ k : Θ.ker, ∃ x ∈ X, ∃ c ∈ centralizer (X : Set G) ⊓ Gh,
      (((k : P₀) : P) : G) = x * c := by
    intro k
    have hk := k.2
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hk
    obtain ⟨hkA, hkB⟩ := hk
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hkA hkB
    obtain ⟨a, ha⟩ := hkA
    obtain ⟨b, hb⟩ := hkB
    set g : G := (((k : P₀) : P) : G) with hg
    have hgA : ∀ m, g * ψA m * g⁻¹ = ψA a * ψA m * (ψA a)⁻¹ := by
      intro m
      have h1 := frameAut_spec ψA hA g (hfixA k) m
      have h2 : frameAut ψA hA g (hfixA k) m = a * m * a⁻¹ := by
        have := congrArg (fun φ : MulAut MA => φ m) ha
        simp only [MulAut.conj_apply] at this
        exact this.symm
      rw [← h1, h2, map_mul, map_mul, map_inv]
    have hgB : ∀ m, g * ψB m * g⁻¹ = ψB b * ψB m * (ψB b)⁻¹ := by
      intro m
      have h1 := frameAut_spec ψB hB g (hfixB k) m
      have h2 : frameAut ψB hB g (hfixB k) m = b * m * b⁻¹ := by
        have := congrArg (fun φ : MulAut MB => φ m) hb
        simp only [MulAut.conj_apply] at this
        exact this.symm
      rw [← h1, h2, map_mul, map_mul, map_inv]
    set x : G := ψA a * ψB b with hx
    set c : G := x⁻¹ * g with hcdef
    have e1 : ∀ m, g * ψA m = ψA a * ψA m * (ψA a)⁻¹ * g := fun m => by
      rw [← hgA m]
      group
    have e2 : ∀ m, g * ψB m = ψB b * ψB m * (ψB b)⁻¹ * g := fun m => by
      rw [← hgB m]
      group
    have hcA : ∀ m, ψA m * c = c * ψA m := by
      intro m
      have hAB' : ψA m * (ψB b)⁻¹ = (ψB b)⁻¹ * ψA m := ((hcomm m b).inv_right).eq
      calc ψA m * c = ψA m * (ψB b)⁻¹ * (ψA a)⁻¹ * g := by rw [hcdef, hx, mul_inv_rev]; group
        _ = (ψB b)⁻¹ * ψA m * (ψA a)⁻¹ * g := by rw [hAB']
        _ = x⁻¹ * (ψA a * ψA m * (ψA a)⁻¹ * g) := by rw [hx, mul_inv_rev]; group
        _ = x⁻¹ * (g * ψA m) := by rw [← e1]
        _ = c * ψA m := by rw [hcdef]; group
    have hcB : ∀ m, ψB m * c = c * ψB m := by
      intro m
      set z : MB := b * m * b⁻¹ with hz
      have hcz : ψB z * (ψA a)⁻¹ = (ψA a)⁻¹ * ψB z := ((hcomm a z).inv_left).eq.symm
      have e2' : g * ψB m = ψB z * g := by
        rw [e2, hz, map_mul, map_mul, map_inv]
      calc ψB m * c = (ψB b)⁻¹ * (ψB z * (ψA a)⁻¹) * g := by
            rw [hcdef, hx, hz, map_mul, map_mul, map_inv]; group
        _ = (ψB b)⁻¹ * ((ψA a)⁻¹ * ψB z) * g := by rw [hcz]
        _ = x⁻¹ * (ψB z * g) := by rw [hx, mul_inv_rev]; group
        _ = x⁻¹ * (g * ψB m) := by rw [e2']
        _ = c * ψB m := by rw [hcdef]; group
    refine ⟨x, mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩), c, mem_inf.2 ⟨?_, ?_⟩,
      by rw [hcdef]; group⟩
    · rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨_, ⟨m₁, rfl⟩, _, ⟨m₂, rfl⟩, rfl⟩ := exists_mul_of_mem_sup_of_commute hABc hy
      calc ψA m₁ * ψB m₂ * c = ψA m₁ * (ψB m₂ * c) := mul_assoc _ _ _
        _ = ψA m₁ * (c * ψB m₂) := by rw [hcB]
        _ = ψA m₁ * c * ψB m₂ := (mul_assoc _ _ _).symm
        _ = c * ψA m₁ * ψB m₂ := by rw [hcA]
        _ = c * (ψA m₁ * ψB m₂) := mul_assoc _ _ _
    · rw [hcdef]
      exact mul_mem (inv_mem (hXG (mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩))))
        (hPG (k : P₀).1.2)
  let ι : ↥Θ.ker →* G := P.subtype.comp (P₀.subtype.comp Θ.ker.subtype)
  have hι : Function.Injective ι :=
    P.subtype_injective.comp (P₀.subtype_injective.comp Θ.ker.subtype_injective)
  have hιK : ι.range ≤ X ⊔ (centralizer (X : Set G) ⊓ Gh) := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨x, hx, c, hc, e⟩ := hdec k
    have : ι k = x * c := e
    rw [this]
    exact mul_mem (mem_sup_left hx) (mem_sup_right hc)
  have hιX : Group.IsSolvable ↥(ι.range ⊓ X) := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_inf_right X (show ι.range ≤ P from ?_))) (Subgroup.inclusion_injective _)
    rintro _ ⟨k, rfl⟩
    exact (k : P₀).1.2
  have hrange : Group.IsSolvable ↥ι.range :=
    isSolvable_of_le_sup_of_commute (X := X) (C := centralizer (X : Set G) ⊓ Gh)
      (fun x hx c hc => mem_centralizer_iff.1 hc.1 x hx) hC hιK hιX
  exact Group.isSolvable_of_isSolvable_injective (f := ι.rangeRestrict)
    (fun a b h => hι (congrArg (fun w : ↥ι.range => (w : G)) h))

end Frame2

section Centralizer

variable {G : Type*} [Group G]

theorem isSolvable_of_le_sup_normalizing {T X₂ C : Subgroup G}
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTN : T ≤ normalizer (X₂ : Set G))
    (hC : C ≤ T ⊔ X₂) (hCX : ∀ c ∈ C, ∀ x ∈ X₂, c * x = x * c) : Group.IsSolvable ↥C := by
  classical
  set Y : Subgroup G := T ⊔ X₂ with hY
  have hdec : ∀ y ∈ Y, ∃ t ∈ T, ∃ x ∈ X₂, y = t * x := by
    let S : Subgroup G :=
      { carrier := {y | ∃ t ∈ T, ∃ x ∈ X₂, y = t * x}
        mul_mem' := by
          rintro _ _ ⟨t, ht, x, hx, rfl⟩ ⟨t', ht', x', hx', rfl⟩
          refine ⟨t * t', T.mul_mem ht ht', (t'⁻¹ * x * t'⁻¹⁻¹) * x', ?_, ?_⟩
          · exact X₂.mul_mem (conj_mem_of_mem_normalizer (hTN (T.inv_mem ht')) hx) hx'
          · group
        one_mem' := ⟨1, T.one_mem, 1, X₂.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨t, ht, x, hx, rfl⟩
          refine ⟨t⁻¹, T.inv_mem ht, t * x⁻¹ * t⁻¹, ?_, ?_⟩
          · exact conj_mem_of_mem_normalizer (hTN ht) (X₂.inv_mem hx)
          · group }
    have hle : T ⊔ X₂ ≤ S := sup_le (fun t ht => ⟨t, ht, 1, X₂.one_mem, by simp⟩)
      (fun x hx => ⟨1, T.one_mem, x, hx, by simp⟩)
    exact fun y hy => hle hy
  haveI : (X₂.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTN
  have hTcomm : Group.IsSolvable ↥T :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hT a.1 a.2 b.1 b.2)
  let j : ↥T →* ↥Y ⧸ X₂.subgroupOf Y :=
    (QuotientGroup.mk' (X₂.subgroupOf Y)).comp (Subgroup.inclusion (le_sup_left : T ≤ Y))
  have hj : Function.Surjective j := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨t, ht, x, hx, hxy⟩ := hdec y.1 y.2
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk' (X₂.subgroupOf Y)) (Subgroup.inclusion le_sup_left ⟨t, ht⟩) =
      QuotientGroup.mk y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (((Subgroup.inclusion le_sup_left ⟨t, ht⟩)⁻¹ * y : ↥Y) : G) ∈ X₂
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hxy]
    show t⁻¹ * (t * x) ∈ X₂
    rw [inv_mul_cancel_left]
    exact hx
  haveI : Group.IsSolvable (↥Y ⧸ X₂.subgroupOf Y) := Group.isSolvable_of_surjective hj
  let f : ↥C →* ↥Y ⧸ X₂.subgroupOf Y :=
    (QuotientGroup.mk' (X₂.subgroupOf Y)).comp (Subgroup.inclusion hC)
  have hker : Group.IsSolvable ↥f.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have ha := a.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have hax : (a.1 : G) ∈ X₂ := ha
    apply Subtype.ext
    apply Subtype.ext
    exact (hCX b.1 b.1.2 a hax).symm
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

end Centralizer

section Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K] [Finite K] {X₁ X₂ : Subgroup (ModGL τ K)}

theorem isSolvable_centralizer_of_central (hc : TwCentral X₁ X₂) :
    Group.IsSolvable ↥(centralizer ((X₁ ⊔ X₂ : Subgroup (ModGL τ K)) : Set (ModGL τ K)) ⊓
      adjointGroup τ K) := by
  obtain ⟨T, hT, hTN, hcent⟩ := hc.centralizer_le
  refine isSolvable_of_le_sup_normalizing hT hTN ?_ ?_
  · intro g hg
    refine hcent g hg.2 fun x hx => ?_
    exact (mem_centralizer_iff.1 hg.1 x (mem_sup_left hx)).symm
  · intro g hg x hx
    exact (mem_centralizer_iff.1 hg.1 x (mem_sup_right hx)).symm

theorem twFrameNormalizerSolvable_of_out (hq : TwQuasi X₁ X₂) (hb : TwBasic X₁ X₂)
    (hc : TwCentral X₁ X₂) (hO₁ : Group.IsSolvable (Outer ↥X₁))
    (hO₂ : Group.IsSolvable (Outer ↥X₂)) :
    TwFrameNormalizerSolvable τ K (X₁ ⊔ X₂) := by
  intro P hPG hPN hPX
  haveI : Finite (ModGL τ K) := finite_modGL
  have hr₁ : X₁.subtype.range = X₁ := Subgroup.range_subtype X₁
  have hr₂ : X₂.subtype.range = X₂ := Subgroup.range_subtype X₂
  refine isSolvable_of_le_normalizer_frame₂ (ψA := X₁.subtype) (ψB := X₂.subtype) hq.1 hq.2
    hO₁ hO₂ X₁.subtype_injective X₂.subtype_injective
    (fun x y => hb.comm x.1 x.2 y.1 y.2) (Gh := adjointGroup τ K)
    (by rw [hr₁, hr₂]; exact sup_le hb.le₁ hb.le₂) ?_ hPG
    (by rw [hr₁, hr₂]; exact hPN) (by rw [hr₁, hr₂]; exact hPX)
  rw [hr₁, hr₂]
  exact isSolvable_centralizer_of_central hc

end Assembly


end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
