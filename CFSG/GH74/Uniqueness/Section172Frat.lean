module

public import CFSG.GH74.Uniqueness.Section172Defs
public import CFSG.GH74.Uniqueness.Section172K

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem index_eq_of_eq_mul {G A C : Subgroup X} (hAG : A ≤ G)
    (h : ∀ g ∈ G, ∃ a ∈ A, ∃ c ∈ C, g = a * c) :
    (C.subgroupOf G).index = (C.subgroupOf A).index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE C hAG)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE C hAG).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha, c, hc, hgac⟩ := h g g.2
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show a⁻¹ * (g : X) ∈ C
    rw [hgac, inv_mul_cancel_left]
    exact hc

omit [Finite X] in
theorem mem_centralizer_pair_iff {x a b : X} :
    x ∈ centralizer ({a, b} : Set X) ↔ x ∈ centralizer ({a} : Set X) ∧
      x ∈ centralizer ({b} : Set X) := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]

theorem ZDSetup.centralizer_D_decomp (S : ZDSetup X Z M) (c : Conf16 Z M) {w : X}
    (hw : w * c.t = c.t * w) {d : X} (hd : d ∈ c.D ⊓ centralizer ({w} : Set X)) :
    ∃ n ∈ c.D ⊓ cenHull Z w, ∃ c' ∈ c.D ⊓ centralizer ({w, c.t} : Set X), d = n * c' := by
  classical
  have ht2 := S.conf_t_sq c
  have ht2' : orderOf c.t = 2 := S.invariant.1 c.t c.ht
  have htD : c.t ∈ normalizer (c.D : Set X) := mem_normalizer_inf_conjugate ht2
  have hZst := S.prodDisc.isZStarIn_inf_conjugate_sup S.invariant c.ht c.htM
  have hcomm : ∀ d ∈ c.D, d * c.t * d⁻¹ * c.t⁻¹ ∈ pPrimeCoreIn c.D := fun d hd =>
    commutator_mem_pPrimeCoreIn hZst htD hd
  have hEodd : Odd (Nat.card (pPrimeCoreIn c.D)) := odd_card_pPrimeCoreIn _
  have htE : c.t ∈ normalizer (pPrimeCoreIn c.D : Set X) := mem_normalizer_pPrimeCoreIn htD
  have htw : c.t ∈ centralizer ({w} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hw.symm
  have hE₁G₁ : pPrimeCoreIn c.D ⊓ centralizer ({w} : Set X) ≤ c.D ⊓ centralizer ({w} : Set X) :=
    inf_le_inf_right _ (pPrimeCoreIn_le c.D)
  have htE₁ : c.t ∈ normalizer ((pPrimeCoreIn c.D ⊓ centralizer ({w} : Set X) : Subgroup X) :
      Set X) := mem_normalizer_inf_of_mem_normalizer htE (Subgroup.le_normalizer htw)
  have hE₁odd : Odd (Nat.card ↥(pPrimeCoreIn c.D ⊓ centralizer ({w} : Set X))) :=
    Odd.of_dvd_nat hEodd (Subgroup.card_dvd_of_le inf_le_left)
  have hcomm₁ : ∀ a ∈ c.D ⊓ centralizer ({w} : Set X), a * c.t * a⁻¹ * c.t⁻¹ ∈
      pPrimeCoreIn c.D ⊓ centralizer ({w} : Set X) := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨hcomm a (Subgroup.mem_inf.mp ha).1, ?_⟩
    have hac := (Subgroup.mem_inf.mp ha).2
    exact (centralizer _).mul_mem ((centralizer _).mul_mem ((centralizer _).mul_mem hac htw)
      ((centralizer _).inv_mem hac)) ((centralizer _).inv_mem htw)
  obtain ⟨e₁, he₁, c₁, hc₁, hdec⟩ := exists_mul_centralizer ht2' hE₁G₁ htE₁ hE₁odd hcomm₁ hd
  set E₁ : Subgroup X := pPrimeCoreIn c.D ⊓ centralizer ({w} : Set X) with hE₁
  have hN₂E₁ : ⁅zpowers c.t, E₁⁆ ≤ E₁ :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (Subgroup.zpowers_le.mpr htE₁)
  have htN₂ : c.t ∈ normalizer ((⁅zpowers c.t, E₁⁆ : Subgroup X) : Set X) :=
    Subgroup.normalizer_commutator_ge_left _ _ (Subgroup.mem_zpowers c.t)
  have hN₂odd : Odd (Nat.card ↥⁅zpowers c.t, E₁⁆) :=
    Odd.of_dvd_nat hE₁odd (Subgroup.card_dvd_of_le hN₂E₁)
  have hcomm₂ : ∀ a ∈ E₁, a * c.t * a⁻¹ * c.t⁻¹ ∈ ⁅zpowers c.t, E₁⁆ := by
    intro a ha
    have h1 : c.t * a * c.t⁻¹ * a⁻¹ ∈ ⁅zpowers c.t, E₁⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers c.t) ha
    have e : a * c.t * a⁻¹ * c.t⁻¹ = (c.t * a * c.t⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1
  obtain ⟨n, hn, c₂, hc₂, hdec₂⟩ := exists_mul_centralizer ht2' hN₂E₁ htN₂ hN₂odd hcomm₂ he₁
  have htH : c.t ∈ cenHull Z w := Subgroup.subset_closure ⟨c.ht, htw⟩
  have hN₂H : ⁅zpowers c.t, E₁⁆ ≤ cenHull Z w := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    have haH : a ∈ cenHull Z w := (Subgroup.zpowers_le.mpr htH) ha
    have hyw : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2
    have h1 := Sec172.mem_cenHull_conj S.invariant y haH
    have hyw' : y * w * y⁻¹ = w := by rw [hyw]; group
    rw [hyw'] at h1
    have e : ⁅a, y⁆ = a * (y * a * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (cenHull Z w).mul_mem haH ((cenHull Z w).inv_mem h1)
  refine ⟨n, Subgroup.mem_inf.mpr ⟨(pPrimeCoreIn_le c.D) (Subgroup.mem_inf.mp (hN₂E₁ hn)).1,
    hN₂H hn⟩, c₂ * c₁, ?_, ?_⟩
  ·
    obtain ⟨hc₂E, hc₂t⟩ := Subgroup.mem_inf.mp hc₂
    obtain ⟨hc₂E', hc₂w⟩ := Subgroup.mem_inf.mp hc₂E
    obtain ⟨hc₁G, hc₁t⟩ := Subgroup.mem_inf.mp hc₁
    obtain ⟨hc₁D, hc₁w⟩ := Subgroup.mem_inf.mp hc₁G
    refine Subgroup.mem_inf.mpr ⟨c.D.mul_mem ((pPrimeCoreIn_le c.D) hc₂E') hc₁D, ?_⟩
    rw [mem_centralizer_pair_iff]
    exact ⟨(centralizer _).mul_mem hc₂w hc₁w, (centralizer _).mul_mem hc₂t hc₁t⟩
  · rw [hdec, hdec₂, mul_assoc]

omit [Finite X] in
theorem mem_centralizer_of_tu {x t u : X} (hx1 : x ∈ centralizer ({t * u} : Set X))
    (hx2 : x ∈ centralizer ({t} : Set X)) : x ∈ centralizer ({u} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx1 hx2 ⊢
  have h : t * (x * u) = t * (u * x) := by
    calc t * (x * u) = (t * x) * u := by rw [mul_assoc]
      _ = (x * t) * u := by rw [hx2]
      _ = x * (t * u) := by rw [mul_assoc]
      _ = (t * u) * x := hx1
      _ = t * (u * x) := by rw [mul_assoc]
  exact mul_left_cancel h

theorem ZDSetup.lemma172g (S : ZDSetup X Z M) : Lemma172gStmt Z M := by
  intro c n i e hB
  have hw : (c.t * c.u) * c.t = c.t * (c.t * c.u) := by
    calc (c.t * c.u) * c.t = c.t * (c.u * c.t) := by rw [mul_assoc]
      _ = c.t * (c.t * c.u) := by rw [c.t_mul_u_comm]
  have hdec : ∀ g ∈ c.D ⊓ centralizer ({c.t * c.u} : Set X),
      ∃ a ∈ c.D ⊓ cenHull Z (c.t * c.u), ∃ y ∈ c.D ⊓ centralizer ({c.t, c.u} : Set X),
        g = a * y := by
    intro g hg
    obtain ⟨a, ha, y, hy, h⟩ := S.centralizer_D_decomp c hw hg
    refine ⟨a, ha, y, ?_, h⟩
    obtain ⟨hyD, hyc⟩ := Subgroup.mem_inf.mp hy
    rw [mem_centralizer_pair_iff] at hyc
    refine Subgroup.mem_inf.mpr ⟨hyD, ?_⟩
    rw [mem_centralizer_pair_iff]
    exact ⟨hyc.2, mem_centralizer_of_tu hyc.1 hyc.2⟩
  have hAG : c.D ⊓ cenHull Z (c.t * c.u) ≤ c.D ⊓ centralizer ({c.t * c.u} : Set X) :=
    inf_le_inf_left _ (Cor713.zHull_le (Z := Z) (centralizer ({c.t * c.u} : Set X)))
  have key := index_eq_of_eq_mul hAG hdec
  unfold Subgroup.relIndex
  rw [key]
  have hset : (c.D ⊓ centralizer ({c.t, c.u} : Set X)) ⊓ (c.D ⊓ cenHull Z (c.t * c.u)) =
      ((c.D ⊓ cenHull Z (c.t * c.u)) ⊓ centralizer ({c.t} : Set X)) := by
    ext x
    simp only [Subgroup.mem_inf, mem_centralizer_pair_iff]
    constructor
    · rintro ⟨⟨hD, htc, huc⟩, -, hH⟩
      exact ⟨⟨hD, hH⟩, htc⟩
    · rintro ⟨⟨hD, hH⟩, htc⟩
      have hxc : x ∈ centralizer ({c.t * c.u} : Set X) :=
        Cor713.zHull_le (Z := Z) (centralizer ({c.t * c.u} : Set X)) hH
      exact ⟨⟨hD, htc, mem_centralizer_of_tu hxc htc⟩, hD, hH⟩
  have h2 := Subgroup.inf_relIndex_right (c.D ⊓ centralizer ({c.t, c.u} : Set X))
    (c.D ⊓ cenHull Z (c.t * c.u))
  rw [hset] at h2
  unfold Subgroup.relIndex at h2
  exact h2.symm

theorem ZDSetup.lemma172a (S : ZDSetup X Z M) (haB : Lemma172aBStmt Z M)
    (c : Conf16 Z M) (n i e : ℕ) (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex (c.D ⊓ centralizer ({c.u} : Set X)) =
      2 ^ n - 1 := by
  have hw : c.u * c.t = c.t * c.u := c.t_mul_u_comm.symm
  have hdec : ∀ g ∈ c.D ⊓ centralizer ({c.u} : Set X),
      ∃ a ∈ c.D ⊓ cenHull Z c.u, ∃ y ∈ c.D ⊓ centralizer ({c.t, c.u} : Set X), g = a * y := by
    intro g hg
    obtain ⟨a, ha, y, hy, h⟩ := S.centralizer_D_decomp c hw hg
    refine ⟨a, ha, y, ?_, h⟩
    rwa [Set.pair_comm]
  have hAG : c.D ⊓ cenHull Z c.u ≤ c.D ⊓ centralizer ({c.u} : Set X) :=
    inf_le_inf_left _ (Cor713.zHull_le (Z := Z) (centralizer ({c.u} : Set X)))
  have key := index_eq_of_eq_mul hAG hdec
  unfold Subgroup.relIndex
  rw [key]
  have hset : (c.D ⊓ centralizer ({c.t, c.u} : Set X)) ⊓ (c.D ⊓ cenHull Z c.u) =
      ((c.D ⊓ cenHull Z c.u) ⊓ centralizer ({c.t} : Set X)) := by
    ext x
    simp only [Subgroup.mem_inf, mem_centralizer_pair_iff]
    constructor
    · rintro ⟨⟨hD, htc, huc⟩, -, hH⟩
      exact ⟨⟨hD, hH⟩, htc⟩
    · rintro ⟨⟨hD, hH⟩, htc⟩
      have hxc : x ∈ centralizer ({c.u} : Set X) :=
        Cor713.zHull_le (Z := Z) (centralizer ({c.u} : Set X)) hH
      exact ⟨⟨hD, htc, hxc⟩, hD, hH⟩
  have h2 := Subgroup.inf_relIndex_right (c.D ⊓ centralizer ({c.t, c.u} : Set X))
    (c.D ⊓ cenHull Z c.u)
  rw [hset] at h2
  have h3 := haB c n i e hB
  unfold Subgroup.relIndex at h2 h3
  rw [← h2]
  exact h3

end CFSG.GH74.Uniqueness
