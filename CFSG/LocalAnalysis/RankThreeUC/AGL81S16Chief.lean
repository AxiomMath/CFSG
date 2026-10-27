module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFacts
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDKTwo
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDThompson
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizes_of_stable_series {x : G} {D D₀ D₁ : Subgroup G} (hx : Odd (orderOf x))
    (hD : IsElemAbelian 2 D) (hD₀ : D₀ ≤ D₁) (hD₁ : D₁ ≤ D)
    (h0 : ∀ d ∈ D₀, x * d * x⁻¹ = d) (h1 : ∀ d ∈ D₁, ⁅x, d⁆ ∈ D₀)
    (h2 : ∀ d ∈ D, ⁅x, d⁆ ∈ D₁) : ∀ d ∈ D, x * d * x⁻¹ = d := by
  have hsq : ∀ y ∈ D, y * y = 1 := fun y hy => by rw [← pow_two]; exact hD.2 y hy
  have key : ∀ d ∈ D, x * (x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ = d := by
    intro d hd
    set c : G := ⁅x, d⁆ with hc
    have hcD₁ : c ∈ D₁ := h2 d hd
    set c' : G := ⁅x, c⁆ with hc'
    have hc'D₀ : c' ∈ D₀ := h1 c hcD₁
    have e1 : x * d * x⁻¹ = c * d := by simp [hc, commutatorElement_def]
    have e2 : x * c * x⁻¹ = c' * c := by simp [hc', commutatorElement_def]
    have e0 : x * c' * x⁻¹ = c' := h0 c' hc'D₀
    have hcc : c * c = 1 := hsq c (hD₁ hcD₁)
    have hc'c' : c' * c' = 1 := hsq c' (hD₁ (hD₀ hc'D₀))
    have e3 : x * (x * d * x⁻¹) * x⁻¹ = c' * d := by
      rw [e1]
      calc x * (c * d) * x⁻¹ = (x * c * x⁻¹) * (x * d * x⁻¹) := by group
        _ = (c' * c) * (c * d) := by rw [e2, e1]
        _ = c' * (c * c) * d := by group
        _ = c' * d := by rw [hcc]; group
    calc x * (x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹
        = x * (x * (c' * d) * x⁻¹) * x⁻¹ := by rw [e3]
      _ = x * ((x * c' * x⁻¹) * (x * d * x⁻¹)) * x⁻¹ := by group
      _ = x * (c' * (c * d)) * x⁻¹ := by rw [e0, e1]
      _ = (x * c' * x⁻¹) * (x * (c * d) * x⁻¹) := by group
      _ = c' * (c' * d) := by
        rw [e0]
        congr 1
        calc x * (c * d) * x⁻¹ = (x * c * x⁻¹) * (x * d * x⁻¹) := by group
          _ = (c' * c) * (c * d) := by rw [e2, e1]
          _ = c' * (c * c) * d := by group
          _ = c' * d := by rw [hcc]; group
      _ = (c' * c') * d := by group
      _ = d := by rw [hc'c']; group
  have hx4 : x ^ (2 ^ 2) ∈ centralizer (D : Set G) := by
    rw [mem_centralizer_iff]
    intro d hd
    have hp4 : x ^ (2 ^ 2) = x * x * x * x := by
      norm_num [pow_succ, mul_assoc]
    have e : x ^ (2 ^ 2) * d * (x ^ (2 ^ 2))⁻¹ =
        x * (x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ := by
      rw [hp4]; group
    have h1 : x ^ (2 ^ 2) * d * (x ^ (2 ^ 2))⁻¹ = d := by rw [e]; exact key d hd
    have h2 : x ^ (2 ^ 2) * d = d * x ^ (2 ^ 2) := by
      calc x ^ (2 ^ 2) * d = (x ^ (2 ^ 2) * d * (x ^ (2 ^ 2))⁻¹) * x ^ (2 ^ 2) := by group
        _ = d * x ^ (2 ^ 2) := by rw [h1]
    exact h2.symm
  intro d hd
  have hxc := mem_of_pow_two_pow_mem_of_odd_orderOf (H := centralizer (D : Set G)) hx hx4
  have := mem_centralizer_iff.mp hxc d hd
  rw [← this]
  group

omit [Finite G] in
theorem isElemAbelian_two_of_le {D V : Subgroup G} (hV : IsElemAbelian 2 V) (h : D ≤ V) :
    IsElemAbelian 2 D := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hV.2 x (h hx)⟩
  have hcomm := hV.1.is_comm.comm ⟨a, h a.2⟩ ⟨b, h b.2⟩
  exact Subtype.ext (by simpa using congrArg Subtype.val hcomm)

omit [Finite G] in
theorem pElement_centralizes_Z {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M T V L Q : Subgroup G}
    (hVab : IsElemAbelian 2 V) (hZV : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ V)
    (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) (hQT : Q ≤ T) {x : G} (hxL : x ∈ L)
    (hxQ : x ∈ normalizer (Q : Set G)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hP : ∀ u ∈ ⁅V, L⁆, (∀ s ∈ Q, ⁅s, u⁆ ∈ centralizer (L : Set G)) →
      ⁅x, u⁆ ∈ centralizer (L : Set G)) :
    ∀ z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T, x * z = z * x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hodd : Odd (orderOf x) := by rw [hord]; exact hp.odd_of_ne_two hp2
  have hxV : x ∈ normalizer (V : Set G) := hMV (hLM hxL)
  have hDV : V ⊓ centralizer (Q : Set G) ≤ V := inf_le_left
  have hD : IsElemAbelian 2 (V ⊓ centralizer (Q : Set G)) := isElemAbelian_two_of_le hVab hDV
  have hxD : ∀ d ∈ V ⊓ centralizer (Q : Set G), x * d * x⁻¹ ∈ V ⊓ centralizer (Q : Set G) := by
    intro d hd
    refine ⟨(mem_normalizer_iff.mp hxV d).mp hd.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    have hs' : x⁻¹ * s * x ∈ Q := by
      have := (mem_normalizer_iff.mp (inv_mem hxQ) s).mp hs
      simpa using this
    have hdc : (x⁻¹ * s * x) * d = d * (x⁻¹ * s * x) := Subgroup.mem_centralizer_iff.mp hd.2 _ hs'
    calc s * (x * d * x⁻¹) = x * ((x⁻¹ * s * x) * d) * x⁻¹ := by group
      _ = x * (d * (x⁻¹ * s * x)) * x⁻¹ := by rw [hdc]
      _ = x * d * x⁻¹ * s := by group
  have hcomm_mem : ∀ d ∈ V, ⁅x, d⁆ ∈ ⁅V, L⁆ := fun d hd => by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hxL hd
  have hcomm_D : ∀ d ∈ V ⊓ centralizer (Q : Set G), ⁅x, d⁆ ∈ V ⊓ centralizer (Q : Set G) :=
    fun d hd => by
      have h1 := hxD d hd
      have h2 := (V ⊓ centralizer (Q : Set G)).mul_mem h1
        ((V ⊓ centralizer (Q : Set G)).inv_mem hd)
      simpa [commutatorElement_def] using h2
  have hseries := centralizes_of_stable_series
    (D := V ⊓ centralizer (Q : Set G))
    (D₀ := (V ⊓ centralizer (Q : Set G)) ⊓ ⁅V, L⁆ ⊓ centralizer (L : Set G))
    (D₁ := (V ⊓ centralizer (Q : Set G)) ⊓ ⁅V, L⁆) hodd hD
    inf_le_left inf_le_left
    (fun d hd => by
      have := Subgroup.mem_centralizer_iff.mp hd.2 x hxL
      rw [this]; group)
    (fun d hd => ⟨⟨hcomm_D d hd.1, hcomm_mem d (hDV hd.1)⟩,
      hP d hd.2 (fun s hs => by
        have h1 : s * d = d * s := Subgroup.mem_centralizer_iff.mp hd.1.2 s hs
        have : ⁅s, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h1
        rw [this]; exact one_mem _)⟩)
    (fun d hd => ⟨hcomm_D d hd, hcomm_mem d (hDV hd)⟩)
  intro z hz
  have hzD : z ∈ V ⊓ centralizer (Q : Set G) := by
    refine ⟨hZV hz, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 s (hQT hs))
  have := hseries z hzD
  calc x * z = (x * z * x⁻¹) * x := by group
    _ = z * x := by rw [this]

theorem exists_ne_one_mem_center_of_normal' {T X : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hXT : X ≤ T) (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let X' : Subgroup ↥T := X.subgroupOf T
  have hX'n : X'.Normal := ⟨fun x hx t => by
    show ((t * x * t⁻¹ : ↥T) : G) ∈ X
    have : ((t * x * t⁻¹ : ↥T) : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl
    rw [this]
    exact hXn t t.2 x hx⟩
  have hX'ne : X' ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXT hx⟩ : ↥T) ∈ X' := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzX : ((z : ↥T) : G) ∈ X := (Subgroup.mem_inf.1 z.2).1
  have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2
  refine ⟨((z : ↥T) : G), hzX, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  exact congrArg Subtype.val (hzc ⟨t, ht⟩)

theorem inf_centralizer_eq_bot {p : ℕ} (hp : p.Prime) {M T V L : Subgroup G} {x : G}
    (hS : LocalSetting p M V) (hT2 : IsPGroup 2 ↥T)
    (hN : ¬ normalizer (T : Set G) ≤ M) (hLM : L ≤ M) (hL2 : 2 ≤ CFSG.Open.pRank p L)
    (hxM : x ∈ M) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxZ : ∀ z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T, x * z = z * x) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  by_contra hA
  have hAT : CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G) ≤ T :=
    inf_le_left.trans (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T)
  have hA2 : IsPGroup 2 ↥(CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G)) :=
    hT2.to_le hAT
  have hLC : L ≤ centralizer
      ((CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G) : Subgroup G) :
        Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hrk : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer
      ((CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G) : Subgroup G) :
        Set G)) :=
    hL2.trans (CFSG.SectionRank.pRank_mono hp.one_lt
      (le_inf hLM (hLC.trans (centralizer_le_normalizer_subgroup _))))
  have hNA := hS.u2 _ hA hA2 hrk
  obtain ⟨g, hgT, hgM⟩ := SetLike.not_le_iff_exists.mp hN
  have hgZ := normalizer_le_normalizer_omegaOneCenterIn T hgT
  have hBZ : cj g (CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G)) ≤
      CFSG.RankThree.PartOne.omegaOneCenterIn T := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : g * a * g⁻¹ ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T :=
      (mem_normalizer_iff.mp hgZ a).mp ha.1
    simpa using h1
  have hxc : x ∈ centralizer
      ((cj g (CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G)) :
        Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact (hxZ y (hBZ hy)).symm
  have hxB := centralizer_le_normalizer_subgroup _ hxc
  rw [cj_normalizer] at hxB
  have hxM' : x ∈ cj g M := Subgroup.map_mono hNA hxB
  have hcard : p ∣ Nat.card ↥(M ⊓ cj g M) := by
    have hle : zpowers x ≤ M ⊓ cj g M := (zpowers_le).mpr ⟨hxM, hxM'⟩
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hord] at h
  exact hS.spe g hgM hcard

theorem inf_centralizer_V_eq_bot {M T V L : Subgroup G} (hT2 : IsPGroup 2 ↥T) (hTM : T ≤ M)
    (hVT : V ≤ T) (hMV : M ≤ normalizer (V : Set G)) (hML : M ≤ normalizer (L : Set G))
    (hVab : IsElemAbelian 2 V)
    (hZ : CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G) = ⊥) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hD
  obtain ⟨d, hdD, hd1, hdT⟩ := exists_ne_one_mem_center_of_normal' hT2
    (inf_le_left.trans hVT)
    (fun t ht x hx => by
      refine ⟨(mem_normalizer_iff.mp (hMV (hTM ht)) x).mp hx.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have hl' : t⁻¹ * l * t ∈ L := by
        have := (mem_normalizer_iff.mp (hML (hTM (T.inv_mem ht))) l).mp hl
        simpa using this
      have hxc : (t⁻¹ * l * t) * x = x * (t⁻¹ * l * t) := Subgroup.mem_centralizer_iff.mp hx.2 _ hl'
      calc l * (t * x * t⁻¹) = t * ((t⁻¹ * l * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * l * t)) * t⁻¹ := by rw [hxc]
        _ = t * x * t⁻¹ * l := by group) hD
  have hd2 : d ^ 2 = 1 := hVab.2 d hdD.1
  have hdZ : d ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T :=
    CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr ⟨hVT hdD.1, hdT, hd2⟩
  have : d ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T ⊓ centralizer (L : Set G) :=
    ⟨hdZ, hdD.2⟩
  rw [hZ, Subgroup.mem_bot] at this
  exact hd1 this

end CFSG.LocalAnalysis.RankThreeUC
