module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore
import CFSG.LargeExtraspecial.A2ModSLd
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowCriteria
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Matrix
open CFSG.LargeExtraspecial.A2Mod (slEquiv galoisFieldTwoOneEquiv slEquiv_transvection)
open scoped MatrixGroups

section Tools

variable {G : Type} [Group G]

private theorem notMem_closure_of_smul {V : Type*} [MulAction G V] {s : Set G} {g : G} {v : V}
    (hs : ∀ x ∈ s, x • v = v) (hg : g • v ≠ v) : g ∉ Subgroup.closure s := fun h =>
  hg (MulAction.mem_stabilizer_iff.mp ((Subgroup.closure_le _).mpr
    (fun x hx => MulAction.mem_stabilizer_iff.mpr (hs x hx)) h))

private theorem card_closure_pair_of_smul [Finite G] {V : Type*} [MulAction G V] {x y : G}
    {v : V} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1)
    (hxv : x • v = v) (hyv : y • v ≠ v) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.HardMathSupport.Dickson.I271.card_closure_pair_sq hxy hx hy hx1 ?_
  rw [Subgroup.zpowers_eq_closure]
  exact notMem_closure_of_smul (by rintro _ rfl; exact hxv) hyv

private theorem isElemAbelian_e27 [Finite G] {V : Type*} [MulAction G V] {a₁ a₂ a₃ : G}
    {v₁ v₂ : V} (h₁ : a₁ ^ 3 = 1) (h₂ : a₂ ^ 3 = 1) (h₃ : a₃ ^ 3 = 1) (h₁₂ : a₁ * a₂ = a₂ * a₁)
    (h₁₃ : a₁ * a₃ = a₃ * a₁) (h₂₃ : a₂ * a₃ = a₃ * a₂) (ha₁ : a₁ ≠ 1) (hv₁ : a₁ • v₁ = v₁)
    (hv₁' : a₂ • v₁ ≠ v₁) (hv₂ : a₁ • v₂ = v₂) (hv₂' : a₂ • v₂ = v₂) (hv₂'' : a₃ • v₂ ≠ v₂) :
    IsElemAbelian 3 (Subgroup.closure ({a₁, a₂} : Set G) ⊔ Subgroup.zpowers a₃) ∧
      Nat.card (Subgroup.closure ({a₁, a₂} : Set G) ⊔ Subgroup.zpowers a₃ : Subgroup G) =
        3 ^ 3 := by
  have hX : IsElemAbelian 3 (Subgroup.closure ({a₁, a₂} : Set G)) :=
    IsElemAbelian.closure_of_commute
      (by rintro x (rfl | rfl) y (rfl | rfl) <;> first | rfl | exact h₁₂ | exact h₁₂.symm)
      (by rintro x (rfl | rfl) <;> assumption)
  have hle : Subgroup.closure ({a₁, a₂} : Set G) ≤ Subgroup.centralizer {a₃} := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h₁₃
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h₂₃
  obtain ⟨hE, hEc⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen Nat.prime_three hX h₃
    (notMem_closure_of_smul (s := {a₁, a₂}) (by rintro x (rfl | rfl) <;> assumption) hv₂'')
    fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  refine ⟨hE, ?_⟩
  rw [hEc, card_closure_pair_of_smul h₁₂ h₁ h₂ ha₁ hv₁ hv₁']
  norm_num

private theorem mem_normalizer_pair [Finite G] {a b g wa wb : G}
    (hwa : wa ∈ Subgroup.closure ({a, b} : Set G)) (hwb : wb ∈ Subgroup.closure ({a, b} : Set G))
    (ha : g * a = wa * g) (hb : g * b = wb * g) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set G) : Set G) := by
  refine RankOneCent.mem_normalizer_of_forall_conj_mem fun s hs => ?_
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rwa [ha, mul_inv_cancel_right]
    · rwa [hb, mul_inv_cancel_right]
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

private theorem mem_of_mul_eq_mul {H : Subgroup G} {p t t' : G} (hp : p ∈ H) (ht : t ∈ H)
    (h : t' * p = p * t) : t' ∈ H := by
  rw [eq_mul_inv_of_mul_eq h]
  exact H.mul_mem (H.mul_mem hp ht) (H.inv_mem hp)

end Tools

section ZModTwo

variable {n : ℕ}

private theorem eq_top_of_hub_zmod {H : Subgroup SL(n, ZMod 2)} (h : Fin n)
    (hin : ∀ (i : Fin n) (hi : i ≠ h), SpecialLinearGroup.transvection hi 1 ∈ H)
    (hout : ∀ (i : Fin n) (hi : h ≠ i), SpecialLinearGroup.transvection hi 1 ∈ H) : H = ⊤ := by
  have he : ∀ {i j : Fin n} (hij : i ≠ j),
      slEquiv galoisFieldTwoOneEquiv (SpecialLinearGroup.transvection hij 1) =
        SpecialLinearGroup.transvection hij 1 :=
    fun hij => by rw [slEquiv_transvection, map_one]
  have hK : H.comap (slEquiv (n := n) galoisFieldTwoOneEquiv).toMonoidHom = ⊤ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.eq_top_of_hub h
      (fun i hi => by rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, he]; exact hin i hi)
      (fun i hi => by rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, he]; exact hout i hi)
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (slEquiv galoisFieldTwoOneEquiv).symm x ∈
      H.comap (slEquiv (n := n) galoisFieldTwoOneEquiv).toMonoidHom := by
    rw [hK]
    exact Subgroup.mem_top _
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hx

private noncomputable def zmodEquivProjSL (hn : 1 ≤ n) :
    SL(n, ZMod 2) ≃* CFSG.Assembly.RankThreeEven.projSL n (GaloisField 2 1) :=
  (slEquiv galoisFieldTwoOneEquiv.symm).trans
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL hn)

private theorem det_eq_one_of_mul_eq_one {M M' : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : M * M' = 1) : M.det = 1 := by
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  exact key _ M'.det (by rw [← Matrix.det_mul, h, Matrix.det_one])

private def mkSL (M M' : Matrix (Fin n) (Fin n) (ZMod 2)) (h : M * M' = 1) : SL(n, ZMod 2) :=
  ⟨M, det_eq_one_of_mul_eq_one h⟩

private def blkN (a b : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  single a b 1 + single b a 1 + single a a 1

private def permM (σ : Fin n → Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if σ j = i then 1 else 0

end ZModTwo

section Seven

private abbrev T7 (i j : Fin 7) (h : i ≠ j := by decide) : SL(7, ZMod 2) :=
  SpecialLinearGroup.transvection h 1

private def t7₁ : SL(7, ZMod 2) := mkSL (1 + blkN 0 1) (1 + blkN 1 0) (by decide +kernel)

private def t7₂ : SL(7, ZMod 2) := mkSL (1 + blkN 2 3) (1 + blkN 3 2) (by decide +kernel)

private def t7₃ : SL(7, ZMod 2) := mkSL (1 + blkN 4 5) (1 + blkN 5 4) (by decide +kernel)

private def c7 : SL(7, ZMod 2) :=
  mkSL (1 + blkN 0 1 + blkN 3 2) (1 + blkN 1 0 + blkN 2 3) (by decide +kernel)

private def d7 : SL(7, ZMod 2) :=
  mkSL (1 + blkN 2 3 + blkN 5 4) (1 + blkN 3 2 + blkN 4 5) (by decide +kernel)

private def σ7 : SL(7, ZMod 2) :=
  mkSL (permM ![2, 3, 4, 5, 0, 1, 6]) (permM ![4, 5, 0, 1, 2, 3, 6]) (by decide +kernel)

private theorem threePlaneGen_SL7 : ThreePlaneGen SL(7, ZMod 2) := by
  obtain ⟨hE, hEc⟩ := isElemAbelian_e27 (a₁ := t7₁) (a₂ := t7₂) (a₃ := t7₃)
    (v₁ := (Pi.single 2 1 : Fin 7 → ZMod 2)) (v₂ := (Pi.single 4 1 : Fin 7 → ZMod 2))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h1E : t7₁ ∈ Subgroup.closure ({t7₁, t7₂} : Set SL(7, ZMod 2)) ⊔ Subgroup.zpowers t7₃ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert _ _))
  have h2E : t7₂ ∈ Subgroup.closure ({t7₁, t7₂} : Set SL(7, ZMod 2)) ⊔ Subgroup.zpowers t7₃ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have h3E : t7₃ ∈ Subgroup.closure ({t7₁, t7₂} : Set SL(7, ZMod 2)) ⊔ Subgroup.zpowers t7₃ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine ⟨_, Subgroup.closure {t7₁, t7₂}, Subgroup.closure {c7, d7}, 3, hE, le_rfl, hEc,
    le_sup_left, card_closure_pair_of_smul (v := (Pi.single 2 1 : Fin 7 → ZMod 2))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), ?_,
    card_closure_pair_of_smul (v := (Pi.single 4 1 : Fin 7 → ZMod 2))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [show c7 = t7₁ * t7₂ ^ 2 by decide +kernel]
      exact Subgroup.mul_mem _ h1E (Subgroup.pow_mem _ h2E 2)
    · rw [show d7 = t7₂ * t7₃ ^ 2 by decide +kernel]
      exact Subgroup.mul_mem _ h2E (Subgroup.pow_mem _ h3E 2)
  set H : Subgroup SL(7, ZMod 2) :=
    Subgroup.normalizer (Subgroup.closure ({t7₁, t7₂} : Set SL(7, ZMod 2)) : Set SL(7, ZMod 2)) ⊔
      Subgroup.normalizer (Subgroup.closure ({c7, d7} : Set SL(7, ZMod 2)) : Set SL(7, ZMod 2))
  have hc : ∀ {i j : Fin 7} (hij : i ≠ j), T7 i j hij * t7₁ = t7₁ * T7 i j hij →
      T7 i j hij * t7₂ = t7₂ * T7 i j hij → T7 i j hij ∈ H := fun _ h1 h2 =>
    Subgroup.mem_sup_left (mem_normalizer_pair (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) h1 h2)
  have h46 : T7 4 6 ∈ H := hc _ (by decide +kernel) (by decide +kernel)
  have h56 : T7 5 6 ∈ H := hc _ (by decide +kernel) (by decide +kernel)
  have h64 : T7 6 4 ∈ H := hc _ (by decide +kernel) (by decide +kernel)
  have h65 : T7 6 5 ∈ H := hc _ (by decide +kernel) (by decide +kernel)
  have hcX : c7 ∈ Subgroup.closure ({c7, d7} : Set SL(7, ZMod 2)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hdX : d7 ∈ Subgroup.closure ({c7, d7} : Set SL(7, ZMod 2)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hσ : σ7 ∈ H := Subgroup.mem_sup_right (mem_normalizer_pair hdX
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcX hcX) (Subgroup.mul_mem _ hdX hdX))
    (by decide +kernel) (by decide +kernel))
  have h06 : T7 0 6 ∈ H := mem_of_mul_eq_mul hσ h46 (by decide +kernel)
  have h16 : T7 1 6 ∈ H := mem_of_mul_eq_mul hσ h56 (by decide +kernel)
  have h26 : T7 2 6 ∈ H := mem_of_mul_eq_mul hσ h06 (by decide +kernel)
  have h36 : T7 3 6 ∈ H := mem_of_mul_eq_mul hσ h16 (by decide +kernel)
  have h60 : T7 6 0 ∈ H := mem_of_mul_eq_mul hσ h64 (by decide +kernel)
  have h61 : T7 6 1 ∈ H := mem_of_mul_eq_mul hσ h65 (by decide +kernel)
  have h62 : T7 6 2 ∈ H := mem_of_mul_eq_mul hσ h60 (by decide +kernel)
  have h63 : T7 6 3 ∈ H := mem_of_mul_eq_mul hσ h61 (by decide +kernel)
  refine eq_top_of_hub_zmod 6 (fun i hi => ?_) (fun i hi => ?_)
  · fin_cases i
    exacts [h06, h16, h26, h36, h46, h56, absurd rfl hi]
  · fin_cases i
    exacts [h60, h61, h62, h63, h64, h65, absurd rfl hi]

theorem threeCoreAt_L72 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSL 7 (GaloisField 2 1)) :=
  threeCoreAt_of_threePlaneGen (zmodEquivProjSL (by norm_num)) threePlaneGen_SL7

end Seven

section Six

private abbrev T6 (i j : Fin 6) (h : i ≠ j := by decide) : SL(6, ZMod 2) :=
  SpecialLinearGroup.transvection h 1

private def t6₁ : SL(6, ZMod 2) := mkSL (1 + blkN 0 1) (1 + blkN 1 0) (by decide +kernel)

private def t6₂ : SL(6, ZMod 2) := mkSL (1 + blkN 2 3) (1 + blkN 3 2) (by decide +kernel)

private def t6₃ : SL(6, ZMod 2) := mkSL (1 + blkN 4 5) (1 + blkN 5 4) (by decide +kernel)

private def b6 : SL(6, ZMod 2) :=
  mkSL (1 + blkN 2 3 + blkN 4 5) (1 + blkN 3 2 + blkN 5 4) (by decide +kernel)

private def d6 : SL(6, ZMod 2) :=
  mkSL (1 + blkN 0 1 + blkN 2 3) (1 + blkN 1 0 + blkN 3 2) (by decide +kernel)

private def p6₀₁ : SL(6, ZMod 2) :=
  mkSL (permM ![1, 0, 2, 3, 4, 5]) (permM ![1, 0, 2, 3, 4, 5]) (by decide +kernel)

private def p6₂₄ : SL(6, ZMod 2) :=
  mkSL (permM ![0, 1, 4, 5, 2, 3]) (permM ![0, 1, 4, 5, 2, 3]) (by decide +kernel)

private def p6₂₃ : SL(6, ZMod 2) :=
  mkSL (permM ![0, 1, 3, 2, 5, 4]) (permM ![0, 1, 3, 2, 5, 4]) (by decide +kernel)

private def p6₀₂ : SL(6, ZMod 2) :=
  mkSL (permM ![2, 3, 0, 1, 4, 5]) (permM ![2, 3, 0, 1, 4, 5]) (by decide +kernel)

private abbrev u6 : SL(6, ZMod 2) := T6 0 2 * T6 1 3

private theorem threePlaneGen_SL6 : ThreePlaneGen SL(6, ZMod 2) := by
  obtain ⟨hE, hEc⟩ := isElemAbelian_e27 (a₁ := t6₁) (a₂ := t6₂) (a₃ := t6₃)
    (v₁ := (Pi.single 2 1 : Fin 6 → ZMod 2)) (v₂ := (Pi.single 4 1 : Fin 6 → ZMod 2))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h1E : t6₁ ∈ Subgroup.closure ({t6₁, t6₂} : Set SL(6, ZMod 2)) ⊔ Subgroup.zpowers t6₃ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert _ _))
  have h2E : t6₂ ∈ Subgroup.closure ({t6₁, t6₂} : Set SL(6, ZMod 2)) ⊔ Subgroup.zpowers t6₃ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have h3E : t6₃ ∈ Subgroup.closure ({t6₁, t6₂} : Set SL(6, ZMod 2)) ⊔ Subgroup.zpowers t6₃ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine ⟨_, Subgroup.closure {t6₁, b6}, Subgroup.closure {t6₃, d6}, 3, hE, le_rfl, hEc, ?_,
    card_closure_pair_of_smul (v := (Pi.single 2 1 : Fin 6 → ZMod 2))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), ?_,
    card_closure_pair_of_smul (v := (Pi.single 0 1 : Fin 6 → ZMod 2))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h1E
    · rw [show b6 = t6₂ * t6₃ by decide +kernel]
      exact Subgroup.mul_mem _ h2E h3E
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h3E
    · rw [show d6 = t6₁ * t6₂ by decide +kernel]
      exact Subgroup.mul_mem _ h1E h2E
  set H : Subgroup SL(6, ZMod 2) :=
    Subgroup.normalizer (Subgroup.closure ({t6₁, b6} : Set SL(6, ZMod 2)) : Set SL(6, ZMod 2)) ⊔
      Subgroup.normalizer (Subgroup.closure ({t6₃, d6} : Set SL(6, ZMod 2)) : Set SL(6, ZMod 2))
  have ha : t6₁ ∈ Subgroup.closure ({t6₁, b6} : Set SL(6, ZMod 2)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b6 ∈ Subgroup.closure ({t6₁, b6} : Set SL(6, ZMod 2)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc : t6₃ ∈ Subgroup.closure ({t6₃, d6} : Set SL(6, ZMod 2)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hd : d6 ∈ Subgroup.closure ({t6₃, d6} : Set SL(6, ZMod 2)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h10 : T6 1 0 ∈ H := Subgroup.mem_sup_left (mem_normalizer_pair
    (Subgroup.mul_mem _ ha ha) hb (by decide +kernel) (by decide +kernel))
  have hp₀₁ : p6₀₁ ∈ H := Subgroup.mem_sup_left (mem_normalizer_pair
    (Subgroup.mul_mem _ ha ha) hb (by decide +kernel) (by decide +kernel))
  have hp₂₄ : p6₂₄ ∈ H := Subgroup.mem_sup_left (mem_normalizer_pair
    ha hb (by decide +kernel) (by decide +kernel))
  have hp₂₃ : p6₂₃ ∈ H := Subgroup.mem_sup_left (mem_normalizer_pair
    ha (Subgroup.mul_mem _ hb hb) (by decide +kernel) (by decide +kernel))
  have hu : u6 ∈ H := Subgroup.mem_sup_right (mem_normalizer_pair
    hc hd (by decide +kernel) (by decide +kernel))
  have hp₀₂ : p6₀₂ ∈ H := Subgroup.mem_sup_right (mem_normalizer_pair
    hc hd (by decide +kernel) (by decide +kernel))
  have h01 : T6 0 1 ∈ H := mem_of_mul_eq_mul hp₀₁ h10 (by decide +kernel)
  have h12 : T6 1 2 ∈ H := by
    rw [show T6 1 2 = T6 1 0 * u6 * T6 1 0 * u6 by decide +kernel]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h10 hu) h10) hu
  have h02 : T6 0 2 ∈ H := mem_of_mul_eq_mul hp₀₁ h12 (by decide +kernel)
  have h30 : T6 3 0 ∈ H := mem_of_mul_eq_mul hp₀₂ h12 (by decide +kernel)
  have h20 : T6 2 0 ∈ H := mem_of_mul_eq_mul hp₂₃ h30 (by decide +kernel)
  have h03 : T6 0 3 ∈ H := mem_of_mul_eq_mul hp₂₃ h02 (by decide +kernel)
  have h04 : T6 0 4 ∈ H := mem_of_mul_eq_mul hp₂₄ h02 (by decide +kernel)
  have h05 : T6 0 5 ∈ H := mem_of_mul_eq_mul hp₂₄ h03 (by decide +kernel)
  have h40 : T6 4 0 ∈ H := mem_of_mul_eq_mul hp₂₄ h20 (by decide +kernel)
  have h50 : T6 5 0 ∈ H := mem_of_mul_eq_mul hp₂₄ h30 (by decide +kernel)
  refine eq_top_of_hub_zmod 0 (fun i hi => ?_) (fun i hi => ?_)
  · fin_cases i
    exacts [absurd rfl hi, h10, h20, h30, h40, h50]
  · fin_cases i
    exacts [absurd rfl hi, h01, h02, h03, h04, h05]

theorem threeCoreAt_L62 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSL 6 (GaloisField 2 1)) :=
  threeCoreAt_of_threePlaneGen (zmodEquivProjSL (by norm_num)) threePlaneGen_SL6

end Six

end CFSG.LocalAnalysis.RankThreeTheoremC
