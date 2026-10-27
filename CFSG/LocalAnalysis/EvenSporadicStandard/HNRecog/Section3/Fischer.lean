module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.ZMod.Basic
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartOne.FIS.Item74
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fischer.LocalZ2S5
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Fischer.Uniq.Counting
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.LocalAnalysis.GorensteinLyons CFSG.RankThree.PartTwo.Sec7


private theorem orderOf_mul_le_three {K : Type} [Group K] {D : Set K}
    (h3 : ∀ d ∈ D, ∀ e ∈ D, (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1)
    {d e : K} (hd : d ∈ D) (he : e ∈ D) : orderOf (d * e) ≤ 3 := by
  rcases h3 d hd e he with h | h
  · exact orderOf_le_of_pow_eq_one (by norm_num) h
  · exact le_trans (orderOf_le_of_pow_eq_one (by norm_num) h) (by norm_num)

private theorem isThreeTranspositions_D {K : Type} [Group K] (D : Set K)
    (hinv : ∀ d ∈ D, d ^ 2 = 1 ∧ d ≠ 1)
    (hnorm : ∀ d ∈ D, ∀ k : K, k * d * k⁻¹ ∈ D)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1)
    (hgen : Subgroup.closure D = ⊤) :
    IsThreeTranspositions D := by
  refine ⟨⟨?_, ?_, hgen, ?_, ?_⟩, ?_⟩
  · intro g x hx
    exact hnorm x hx g
  · intro x hx
    exact orderOf_eq_prime (p := 2) (hinv x hx).1 (hinv x hx).2
  · intro x hx y hy
    exact le_trans (orderOf_mul_le_three h3 hx hy) (by norm_num)
  · intro x hx y hy h4
    exact absurd h4 (by
      have := orderOf_mul_le_three h3 hx hy
      omega)
  · intro x hx y hy
    exact orderOf_mul_le_three h3 hx hy

private lemma perm_fin5_eq_one_of_forall_commute_swap
    {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ i j : Fin 5, σ * Equiv.swap i j = Equiv.swap i j * σ) : σ = 1 := by
  apply Equiv.ext
  intro i
  change σ i = i
  by_contra hne
  have hik : i ≠ σ i := fun h => hne h.symm
  have hlt : ({i, σ i} : Finset (Fin 5)).card < Fintype.card (Fin 5) := by
    rw [Finset.card_insert_of_notMem (by simpa using hik), Finset.card_singleton]
    simp
  obtain ⟨j, -, hjnot⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := ({i, σ i} : Finset (Fin 5)))
      (t := Finset.univ) (by simpa using hlt)
  have hji : j ≠ i := fun h => hjnot (by simp [h])
  have hjk : j ≠ σ i := fun h => hjnot (by simp [h])
  have h := congrArg (fun p : Equiv.Perm (Fin 5) => p i) (hσ i j)
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h
  rw [Equiv.swap_apply_of_ne_of_ne hne hjk.symm] at h
  exact hji (σ.injective h)

private lemma snd_eq_one_of_mem_center
    {z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)}
    (hz : ∀ g : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), g * z = z * g) : z.2 = 1 := by
  apply perm_fin5_eq_one_of_forall_commute_swap
  intro i j
  exact (congrArg Prod.snd (hz (1, Equiv.swap i j))).symm

private lemma eq_one_or_zeta_of_mem_center
    {z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)}
    (hz : ∀ g : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), g * z = z * g)
    (hz2 : z ^ 2 = 1) : z = 1 ∨ z = zetaZ2S5 := by
  have h2 : z.2 = 1 := snd_eq_one_of_mem_center hz
  have hgen : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 →
      a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide
  have hp : z.1 ^ 2 = 1 := by
    have := congrArg Prod.fst hz2
    simpa using this
  rcases hgen z.1 hp with h1 | h1
  · left; exact Prod.ext h1 h2
  · right; exact Prod.ext h1 h2

structure FischerHyp {K : Type} [Group K] (D : Set K) : Prop where
  inv : ∀ d ∈ D, d ^ 2 = 1 ∧ d ≠ 1
  norm : ∀ d ∈ D, ∀ k : K, k * d * k⁻¹ ∈ D
  three : ∀ d ∈ D, ∀ e ∈ D, (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1
  gen : Subgroup.closure D = ⊤
  cent : ∀ d ∈ D, Subgroup.centralizer ({d} : Set K) =
    Subgroup.closure (D ∩ (Subgroup.centralizer ({d} : Set K) : Set K))
  shape : ∀ d ∈ D, Nonempty (↥(Subgroup.centralizer ({d} : Set K)) ≃*
    Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))

theorem FischerHyp.local_structure {K : Type} [Group K] [Finite K] {D : Set K} (h : FischerHyp D)
    {d : K} (hd : d ∈ D) :
    (∃ x ∈ localSet D d, ∀ y ∈ localSet D d,
        ∃ g ∈ Subgroup.centralizer ({d} : Set K), g * x * g⁻¹ = y) ∧
      (∃ x ∈ localSet D d, ∃ y ∈ localSet D d, x ≠ y ∧ x * y = y * x) ∧
      Nonempty (↥(Subgroup.closure (localSet D d)) ≃* Equiv.Perm (Fin 5)) := by
  classical
  let C : Subgroup K := Subgroup.centralizer ({d} : Set K)
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let dc : C := ⟨d, hdC⟩
  obtain ⟨φ⟩ : Nonempty (C ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) := h.shape d hd
  let Slocal : Set C := {y : C | (y : K) ∈ localSet D d}
  let SD : Set C := {y : C | (y : K) ∈ D}
  let X : Set (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) := φ '' Slocal
  have map_inv' (a : C) : φ a⁻¹ = (φ a)⁻¹ := by
    have h1 : φ a * φ a⁻¹ = 1 := by simp [← map_mul]
    exact eq_inv_of_mul_eq_one_right h1
  have map_conj (a b : C) : φ (a * b * a⁻¹) = φ a * φ b * (φ a)⁻¹ := by
    calc φ (a * b * a⁻¹) = φ (a * b) * φ a⁻¹ := map_mul φ (a * b) a⁻¹
      _ = (φ a * φ b) * φ a⁻¹ := by rw [map_mul]
      _ = (φ a * φ b) * (φ a)⁻¹ := by rw [map_inv' a]
  have hdc_central : ∀ g : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), g * φ dc = φ dc * g := by
    intro g
    obtain ⟨c, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2))
  have hdc_ne_one : dc ≠ 1 := by
    intro h1
    exact (h.inv d hd).2 (congrArg Subtype.val h1)
  have hdc_sq : dc ^ 2 = 1 := by
    apply Subtype.ext
    simpa using (h.inv d hd).1
  have hdc_image : φ dc = zetaZ2S5 := by
    rcases eq_one_or_zeta_of_mem_center hdc_central (by rw [← map_pow, hdc_sq, map_one]) with h1 | h1
    · exact absurd (φ.injective (by rw [h1, map_one])) hdc_ne_one
    · exact h1
  have hSD : SD = insert dc Slocal := by
    ext y
    constructor
    · intro hy
      by_cases hyd : y = dc
      · exact Or.inl hyd
      · refine Or.inr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mp y.2, ?_⟩
        intro hcon
        exact hyd (Subtype.ext hcon)
    · rintro (rfl | hy)
      · exact hd
      · exact hy.1
  have hXY : insert zetaZ2S5 X = φ '' SD := by
    rw [hSD, Set.image_insert_eq, hdc_image]
  have hsub : C.subtype '' SD = D ∩ (C : Set K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxD, hxC⟩
      exact ⟨⟨x, hxC⟩, hxD, rfl⟩
  have hclosure_SD : Subgroup.closure SD = ⊤ := by
    have hmap : (Subgroup.closure SD).map C.subtype = C := by
      rw [MonoidHom.map_closure, hsub]
      exact (h.cent d hd).symm
    have htop : Subgroup.map C.subtype ⊤ = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective C.subtype_injective (hmap.trans htop.symm)
  have hgen : Subgroup.closure (insert zetaZ2S5 X) = ⊤ := by
    rw [hXY]
    change Subgroup.closure (φ.toMonoidHom '' SD) = ⊤
    rw [← MonoidHom.map_closure φ.toMonoidHom SD, hclosure_SD]
    exact Subgroup.map_top_of_surjective φ.toMonoidHom (EquivLike.surjective φ)
  have hconj : ∀ g x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), x ∈ X → g * x * g⁻¹ ∈ X := by
    intro g x hx
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := φ.surjective g
    refine ⟨c * w * c⁻¹, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · have := h.norm (w : K) hw.1 (c : K)
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
      · exact Subgroup.mem_centralizer_singleton_iff.mp (C.mul_mem (C.mul_mem c.2 w.2) (C.inv_mem c.2))
      · intro hcon
        apply hw.2.2
        have hcon' : (c : K) * (w : K) * (c : K)⁻¹ = d := by
          simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcon
        have hc_inv : (c : K)⁻¹ * d = d * (c : K)⁻¹ :=
          Subgroup.mem_centralizer_singleton_iff.mp (C.inv_mem c.2)
        calc (w : K) = (c : K)⁻¹ * ((c : K) * (w : K) * (c : K)⁻¹) * (c : K) := by group
          _ = (c : K)⁻¹ * d * (c : K) := by rw [hcon']
          _ = d := by rw [hc_inv]; group
    · rw [map_conj c w]
  have hinv : ∀ x ∈ X, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ zetaZ2S5 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using (h.inv (w:K) hw.1).1),
        map_one]
    · intro h1
      have hw1 : w = 1 := φ.injective (h1.trans (map_one φ).symm)
      exact (h.inv (w:K) hw.1).2 (by rw [hw1]; rfl)
    · intro hz
      have : w = dc := φ.injective (hz.trans hdc_image.symm)
      exact hw.2.2 (by rw [this])
  have h3 : ∀ x ∈ insert zetaZ2S5 X, ∀ y ∈ insert zetaZ2S5 X,
      (x * y) ^ 3 = 1 ∨ (x * y) ^ 2 = 1 := by
    intro x hx y hy
    rw [hXY] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rcases h.three (u:K) hu (v:K) hv with hh | hh
    · left
      rw [← map_mul, ← map_pow, show (u * v) ^ 3 = 1 from Subtype.ext (by simpa using hh), map_one]
    · right
      rw [← map_mul, ← map_pow, show (u * v) ^ 2 = 1 from Subtype.ext (by simpa using hh), map_one]
  obtain ⟨ε, hXswap⟩ := eq_swapSet_of_threeTranspositions X hconj hinv h3 hgen
  have hmemX : ∀ z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5),
      z ∈ X ↔ ((φ.symm z : C) : K) ∈ localSet D d := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [Slocal] using hy
    · intro hz
      exact ⟨φ.symm z, hz, by simp⟩
  have hbase : (ε, Equiv.swap (0 : Fin 5) 1) ∈ swapSetZ2S5 ε :=
    ⟨rfl, ⟨0, 1, by decide, rfl⟩⟩
  have hbaseX : (ε, Equiv.swap (0 : Fin 5) 1) ∈ X := by rw [hXswap]; exact hbase
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨((φ.symm (ε, Equiv.swap 0 1) : C) : K), (hmemX _).mp hbaseX, ?_⟩
    intro y hy
    have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hy.2.1
    have hyX : φ ⟨y, hyC⟩ ∈ X := ⟨⟨y, hyC⟩, hy, rfl⟩
    have hySwap : φ ⟨y, hyC⟩ ∈ swapSetZ2S5 ε := by rw [← hXswap]; exact hyX
    obtain ⟨g, hg⟩ := swapSetZ2S5_oneClass ε (ε, Equiv.swap 0 1) hbase (φ ⟨y, hyC⟩) hySwap
    obtain ⟨c, rfl⟩ := φ.surjective g
    refine ⟨(c : K), c.2, ?_⟩
    have hg' : c * φ.symm (ε, Equiv.swap 0 1) * c⁻¹ = ⟨y, hyC⟩ := by
      apply φ.injective
      rw [map_conj c (φ.symm (ε, Equiv.swap 0 1)), MulEquiv.apply_symm_apply]
      exact hg
    have := congrArg Subtype.val hg'
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
  · obtain ⟨xG, hxG, yG, hyG, hxyne, hxycomm⟩ := swapSetZ2S5_commuting_pair ε
    have hxX : xG ∈ X := by rw [hXswap]; exact hxG
    have hyX : yG ∈ X := by rw [hXswap]; exact hyG
    refine ⟨((φ.symm xG : C) : K), (hmemX _).mp hxX, ((φ.symm yG : C) : K), (hmemX _).mp hyX,
      ?_, ?_⟩
    · intro hcon
      exact hxyne (φ.symm.injective (Subtype.ext hcon))
    · have hcommC : φ.symm xG * φ.symm yG = φ.symm yG * φ.symm xG := by
        apply φ.injective
        simpa using hxycomm
      exact congrArg Subtype.val hcommC
  · have hsubC : C.subtype '' Slocal = localSet D d := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hx.2.1⟩, hx, rfl⟩
    have hmapC' : (Subgroup.closure Slocal).map C.subtype = Subgroup.closure (localSet D d) := by
      rw [MonoidHom.map_closure, hsubC]
    have hmapφ : (Subgroup.closure Slocal).map φ.toMonoidHom =
        Subgroup.closure (swapSetZ2S5 ε) := by
      rw [MonoidHom.map_closure]
      exact congrArg Subgroup.closure (by rw [← hXswap]; rfl)
    obtain ⟨e⟩ := closure_swapSetZ2S5_equiv ε
    let e1 : Subgroup.closure Slocal ≃* Subgroup.closure (localSet D d) :=
      (Subgroup.equivMapOfInjective (Subgroup.closure Slocal) C.subtype C.subtype_injective).trans
        (MulEquiv.subgroupCongr hmapC')
    let e2 : Subgroup.closure Slocal ≃* Subgroup.closure (swapSetZ2S5 ε) :=
      (Subgroup.equivMapOfInjective (Subgroup.closure Slocal) φ.toMonoidHom φ.injective).trans
        (MulEquiv.subgroupCongr hmapφ)
    exact ⟨e1.symm.trans (e2.trans e)⟩

theorem FischerHyp.isConj {K : Type} [Group K] [Finite K] {D : Set K} (h : FischerHyp D) :
    ∀ d ∈ D, ∀ e ∈ D, IsConj d e := by
  intro d0 hd0 e0 he0
  by_contra hconj
  have hD3 : IsThreeTranspositions D := isThreeTranspositions_D D h.inv h.norm h.three h.gen
  let A : Set K := {x | IsConj d0 x}
  let B : Set K := D \ A
  have hd0A : d0 ∈ A := isConj_iff.2 ⟨1, by simp⟩
  have hAinv : ∀ g : K, ∀ x ∈ A, g * x * g⁻¹ ∈ A := by
    intro g x hx
    obtain ⟨k, hk⟩ := isConj_iff.1 hx
    exact isConj_iff.2 ⟨g * k, by rw [← hk]; group⟩
  have hBinv : ∀ g : K, ∀ x ∈ B, g * x * g⁻¹ ∈ B := by
    intro g x hx
    refine ⟨h.norm x hx.1 g, ?_⟩
    intro hgxA
    apply hx.2
    have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxeq]
    simpa using hAinv g⁻¹ (g * x * g⁻¹) hgxA
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hxB.2 hxA
  have hAB : D = A ∪ B := by
    ext x
    constructor
    · intro hx
      by_cases hcon : IsConj d0 x
      · exact Or.inl hcon
      · exact Or.inr ⟨hx, hcon⟩
    · rintro (hx | hx)
      · obtain ⟨k, hk⟩ := isConj_iff.1 hx
        rw [← hk]
        exact h.norm d0 hd0 k
      · exact hx.1
  have hcomm := rank3II_7_1 hD3 hAB hdisj hAinv
  have he0B : e0 ∈ B := ⟨he0, hconj⟩
  have hAeq : ∀ e ∈ B, A = localSet D e := by
    intro e heB
    have hAle : A ⊆ localSet D e := by
      intro a ha
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := isConj_iff.1 ha
        rw [← hk]
        exact h.norm d0 hd0 k
      · exact hcomm a ha e heB
      · intro hcon
        exact heB.2 (hcon ▸ ha)
    obtain ⟨x0, -, hxall⟩ := (h.local_structure heB.1).1
    obtain ⟨g0, -, hg0⟩ := hxall d0 (hAle hd0A)
    refine Set.Subset.antisymm hAle ?_
    intro y hy
    obtain ⟨g, -, hg⟩ := hxall y hy
    have hyeq : y = (g * g0⁻¹) * d0 * (g * g0⁻¹)⁻¹ := by
      rw [← hg, ← hg0]; group
    rw [hyeq]
    exact hAinv (g * g0⁻¹) d0 hd0A
  have hBeq : B = localSet D d0 := by
    have hBle : B ⊆ localSet D d0 := by
      intro b hb
      refine ⟨hb.1, ?_, ?_⟩
      · exact (hcomm d0 hd0A b hb).symm
      · intro hcon
        exact hb.2 (hcon ▸ hd0A)
    obtain ⟨x0, -, hxall⟩ := (h.local_structure hd0).1
    obtain ⟨g0, -, hg0⟩ := hxall e0 (hBle he0B)
    refine Set.Subset.antisymm hBle ?_
    intro y hy
    obtain ⟨g, -, hg⟩ := hxall y hy
    have hyeq : y = (g * g0⁻¹) * e0 * (g * g0⁻¹)⁻¹ := by
      rw [← hg, ← hg0]; group
    rw [hyeq]
    exact hBinv (g * g0⁻¹) e0 he0B
  obtain ⟨x, hxL, y, hyL, hxyne, hxycomm⟩ := (h.local_structure hd0).2.1
  have hxB : x ∈ B := by rw [hBeq]; exact hxL
  have hyB : y ∈ B := by rw [hBeq]; exact hyL
  have hylocal : y ∈ localSet D x := ⟨hyB.1, hxycomm.symm, Ne.symm hxyne⟩
  exact hyB.2 ((hAeq x hxB) ▸ hylocal)

theorem fischer_S7 {K : Type} [Group K] [Finite K] (D : Set K)
    (hinv : ∀ d ∈ D, d ^ 2 = 1 ∧ d ≠ 1)
    (hnorm : ∀ d ∈ D, ∀ k : K, k * d * k⁻¹ ∈ D)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1)
    (hgen : Subgroup.closure D = ⊤) (hne : D.Nonempty)
    (hC : ∀ d ∈ D, Subgroup.centralizer ({d} : Set K) =
      Subgroup.closure (D ∩ (Subgroup.centralizer ({d} : Set K) : Set K)))
    (hshape : ∀ d ∈ D, Nonempty (↥(Subgroup.centralizer ({d} : Set K)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))) :
    Nonempty (K ≃* Equiv.Perm (Fin 7)) ∧ ∀ d ∈ D, ∀ e ∈ D, IsConj d e := by
  have hh : FischerHyp D := ⟨hinv, hnorm, h3, hgen, hC, hshape⟩
  have hD3 : IsThreeTranspositions D := isThreeTranspositions_D D hinv hnorm h3 hgen
  have hconj := hh.isConj
  obtain ⟨d, hd⟩ := hne
  rcases CFSG.RankThree.PartOne.FIS.inFischer44 K D hD3
      (fun d hd e he => isConj_iff.1 (hconj d hd e he)) d hd 5 (by norm_num) (by norm_num)
      (hh.local_structure hd).2.2 with h | ⟨h5, -⟩
  · exact ⟨h, hconj⟩
  · omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
