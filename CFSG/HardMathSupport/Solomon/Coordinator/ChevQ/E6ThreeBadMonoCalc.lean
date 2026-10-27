module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadCubeGen
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.FrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.RankThree.Chevalley (wordAct wordSign wordRep wordRep_conj_pinnedX wordSign_eq_one_or
  isRoot_wordAct wordAct_eq_smul)
open CFSG.StandardType.TableBExc.E6Three (monomial_conj_rootDiagUnit_weylTuple)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame (eq_of_pinnedX_eq_pinnedX)

set_option linter.unusedSectionVars false

theorem bm_closure_three_eq {G : Type*} [Group G] {E : Subgroup G} (hE : Nat.card E = 3 ^ 3)
    {x y z : G} (hx : x ∈ E) (hy : y ∈ E) (hz : z ∈ E) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) (hzxy : z ∉ Subgroup.closure ({x, y} : Set G)) :
    Subgroup.closure ({x, y, z} : Set G) = E := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have h12 : Subgroup.zpowers x ≤ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have h23 : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.closure ({x, y, z} : Set G) :=
    Subgroup.closure_mono (by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      tauto)
  have h3E : Subgroup.closure ({x, y, z} : Set G) ≤ E :=
    (Subgroup.closure_le _).2 (by rintro a (rfl | rfl | rfl) <;> assumption)
  have hfin3 : Finite (Subgroup.closure ({x, y, z} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective h3E)
  have hfin2 : Finite (Subgroup.closure ({x, y} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective h23)
  have hfin1 : Finite (Subgroup.zpowers x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective h12)
  have hlt12 : Nat.card (Subgroup.zpowers x) < Nat.card (Subgroup.closure ({x, y} : Set G)) := by
    by_contra h
    have e := Subgroup.eq_of_le_of_card_ge h12 (not_lt.1 h)
    exact hyx (by rw [e]; exact Subgroup.subset_closure (by simp))
  have hlt23 : Nat.card (Subgroup.closure ({x, y} : Set G)) <
      Nat.card (Subgroup.closure ({x, y, z} : Set G)) := by
    by_contra h
    have e := Subgroup.eq_of_le_of_card_ge h23 (not_lt.1 h)
    exact hzxy (by rw [e]; exact Subgroup.subset_closure (by simp))
  have h1lt : 1 < Nat.card (Subgroup.zpowers x) :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 (Subgroup.zpowers_eq_bot.not.2 hx1)
  obtain ⟨k3, hk3, hc3⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (hE ▸ Subgroup.card_dvd_of_le h3E)
  obtain ⟨k2, hk2, hc2⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (hc3 ▸ Subgroup.card_dvd_of_le h23)
  obtain ⟨k1, hk1, hc1⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (hc2 ▸ Subgroup.card_dvd_of_le h12)
  rw [hc1, hc2] at hlt12
  rw [hc2, hc3] at hlt23
  rw [hc1] at h1lt
  have e1 : 1 ≤ k1 := by
    by_contra h
    rw [show k1 = 0 by omega, pow_zero] at h1lt
    exact lt_irrefl _ h1lt
  have e2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hlt12
  have e3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hlt23
  refine Subgroup.eq_of_le_of_card_ge h3E ?_
  rw [hE, hc3, show k3 = 3 by omega]

section Calc

variable
  {K : Type} [Field K]

theorem bm_conj_eq_rootDiagAutHom {h : adjointGroup Tag.E6 K} {t : Fin Tag.E6.rank → Kˣ}
    (ht : (h : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 t) :
    MulAut.conj h = rootDiagAutHom Tag.E6 K t := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht]
  rfl

theorem bm_conj_mul_rootDiag {n : adjointGroup Tag.E6 K} {v : WeylGroup Tag.E6}
    (hn : (n : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K)
    (hv : MapsRootLines (n : ModGL Tag.E6 K) v) (t : Fin Tag.E6.rank → Kˣ) :
    MulAut.conj n * rootDiagAutHom Tag.E6 K t =
      rootDiagAutHom Tag.E6 K (weylTuple v t) * MulAut.conj n := by
  have h := monomial_conj_rootDiagUnit_weylTuple hn hv t
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change (n : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 t * g * (rootDiagUnit Tag.E6 t)⁻¹) *
      (n : ModGL Tag.E6 K)⁻¹ = rootDiagUnit Tag.E6 (weylTuple v t) *
      ((n : ModGL Tag.E6 K) * g * (n : ModGL Tag.E6 K)⁻¹) *
      (rootDiagUnit Tag.E6 (weylTuple v t))⁻¹
  rw [← h]
  group

theorem bm_rootDiag_mul_conj {n : adjointGroup Tag.E6 K} {v : WeylGroup Tag.E6}
    (hn : (n : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K)
    (hv : MapsRootLines (n : ModGL Tag.E6 K) v) (t : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom Tag.E6 K t * MulAut.conj n =
      MulAut.conj n * rootDiagAutHom Tag.E6 K (weylTuple v⁻¹ t) := by
  rw [bm_conj_mul_rootDiag hn hv, weylTuple_weylTuple, mul_inv_cancel, weylTuple_one]

theorem bm_weylWordElt_mem_monomial (μ : List (Fin Tag.E6.rank)) :
    (weylWordElt .E6 K μ : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K := by
  rw [coe_weylWordElt]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_monomialSubgroup i

theorem bm_mapsRootLines_weylWordElt (μ : List (Fin Tag.E6.rank)) :
    MapsRootLines (weylWordElt .E6 K μ : ModGL Tag.E6 K) ((coxeterSystem Tag.E6).wordProd μ) := by
  rw [coe_weylWordElt]
  exact mapsRootLines_list_prod μ

theorem bm_weylWordElt_append (μ μ' : List (Fin Tag.E6.rank)) :
    weylWordElt .E6 K (μ ++ μ') = weylWordElt .E6 K μ * weylWordElt .E6 K μ' := by
  simp only [weylWordElt, List.map_append, List.prod_append]

@[expose] def BmMono (X : MulAut (adjointGroup Tag.E6 K)) (v : WeylGroup Tag.E6) : Prop :=
  ∃ (n : adjointGroup Tag.E6 K) (b : Fin Tag.E6.rank → Kˣ),
    (n : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K ∧ MapsRootLines (n : ModGL Tag.E6 K) v ∧
      X = MulAut.conj n * rootDiagAutHom Tag.E6 K b

theorem BmMono.mul {X Y : MulAut (adjointGroup Tag.E6 K)} {v u : WeylGroup Tag.E6}
    (hX : BmMono X v) (hY : BmMono Y u) : BmMono (X * Y) (v * u) := by
  obtain ⟨n, a, hn, hnv, rfl⟩ := hX
  obtain ⟨m, b, hm, hmu, rfl⟩ := hY
  refine ⟨n * m, weylTuple u⁻¹ a * b, mul_mem hn hm, hnv.mul hmu, ?_⟩
  have h := bm_rootDiag_mul_conj hm hmu a
  calc MulAut.conj n * rootDiagAutHom Tag.E6 K a * (MulAut.conj m * rootDiagAutHom Tag.E6 K b)
      = MulAut.conj n * (rootDiagAutHom Tag.E6 K a * MulAut.conj m) *
          rootDiagAutHom Tag.E6 K b := by group
    _ = MulAut.conj (n * m) * rootDiagAutHom Tag.E6 K (weylTuple u⁻¹ a * b) := by
        rw [h, map_mul, map_mul]
        group

theorem bmMono_word (μ : List (Fin Tag.E6.rank)) (b : Fin Tag.E6.rank → Kˣ) :
    BmMono (MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K b)
      ((coxeterSystem Tag.E6).wordProd μ) :=
  ⟨_, b, bm_weylWordElt_mem_monomial μ, bm_mapsRootLines_weylWordElt μ, rfl⟩

theorem bmMono_conj (μ : List (Fin Tag.E6.rank)) :
    BmMono (MulAut.conj (weylWordElt .E6 K μ)) ((coxeterSystem Tag.E6).wordProd μ) :=
  ⟨_, 1, bm_weylWordElt_mem_monomial μ, bm_mapsRootLines_weylWordElt μ, by rw [map_one, mul_one]⟩

theorem bmMono_conj_inv (μ : List (Fin Tag.E6.rank)) :
    BmMono (MulAut.conj (weylWordElt .E6 K μ))⁻¹ ((coxeterSystem Tag.E6).wordProd μ)⁻¹ :=
  ⟨(weylWordElt .E6 K μ)⁻¹, 1, inv_mem (bm_weylWordElt_mem_monomial μ),
    (bm_mapsRootLines_weylWordElt μ).inv, by rw [map_one, mul_one, map_inv]⟩

theorem BmMono.exists_eq_word {X : MulAut (adjointGroup Tag.E6 K)} {μ : List (Fin Tag.E6.rank)}
    (hX : BmMono X ((coxeterSystem Tag.E6).wordProd μ)) :
    ∃ b, X = MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K b := by
  obtain ⟨n, a, hn, hnv, rfl⟩ := hX
  have hy : (((weylWordElt .E6 K μ)⁻¹ * n : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      torusGroup Tag.E6 K := by
    refine CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one
      (mul_mem (inv_mem (bm_weylWordElt_mem_monomial μ)) hn) ?_
    have := (bm_mapsRootLines_weylWordElt (K := K) μ).inv.mul hnv
    rwa [inv_mul_cancel] at this
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  refine ⟨s * a, ?_⟩
  have e : n = weylWordElt .E6 K μ * ((weylWordElt .E6 K μ)⁻¹ * n) := by group
  rw [e, map_mul MulAut.conj, bm_conj_eq_rootDiagAutHom hs, map_mul, mul_assoc]

theorem bm_weylWordElt_eq_mul_sign {μ μ' : List (Fin Tag.E6.rank)}
    (h : (coxeterSystem Tag.E6).wordProd μ = (coxeterSystem Tag.E6).wordProd μ') :
    ∃ s : Fin Tag.E6.rank → Kˣ, (∀ i, s i ^ 2 = 1) ∧
      (weylWordElt .E6 K μ : ModGL Tag.E6 K) =
        weylWordElt .E6 K μ' * rootDiagUnit Tag.E6 s := by
  have hy : (weylWordElt .E6 K μ' : ModGL Tag.E6 K)⁻¹ * weylWordElt .E6 K μ ∈
      torusGroup Tag.E6 K := by
    refine CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one
      (mul_mem (inv_mem (bm_weylWordElt_mem_monomial μ')) (bm_weylWordElt_mem_monomial μ)) ?_
    have := (bm_mapsRootLines_weylWordElt (K := K) μ').inv.mul (bm_mapsRootLines_weylWordElt μ)
    rwa [h, inv_mul_cancel] at this
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  have he : (weylWordElt .E6 K μ : ModGL Tag.E6 K) =
      weylWordElt .E6 K μ' * rootDiagUnit Tag.E6 s := by
    rw [← hs]
    group
  refine ⟨s, fun i => ?_, he⟩
  have hi := isRoot_single Tag.E6 i
  have key : (weylWordElt .E6 K μ : ModGL Tag.E6 K) * pinnedX Tag.E6 K (Pi.single i 1) 1 *
      (weylWordElt .E6 K μ : ModGL Tag.E6 K)⁻¹ = (weylWordElt .E6 K μ' : ModGL Tag.E6 K) *
        (rootDiagUnit Tag.E6 s * pinnedX Tag.E6 K (Pi.single i 1) 1 *
          (rootDiagUnit Tag.E6 s)⁻¹) * (weylWordElt .E6 K μ' : ModGL Tag.E6 K)⁻¹ := by
    rw [he]
    group
  rw [rootDiagUnit_conj_pinnedX s hi, coe_weylWordElt, coe_weylWordElt,
    wordRep_conj_pinnedX K μ hi, wordRep_conj_pinnedX K μ' hi, wordAct_eq_smul, wordAct_eq_smul,
    h] at key
  have hv := pinnedX_injective Tag.E6 K _ key
  have hsi : rootChar s (Pi.single i 1) = s i := by simpa using rootChar_nsmul_single s i 1
  rw [hsi] at hv
  have hσ' : ((wordSign Tag.E6 μ' (Pi.single i 1) : ℤ) : K) ^ 2 = 1 := by
    rcases wordSign_eq_one_or μ' hi with h1 | h1 <;> simp [h1]
  have hσ : ((wordSign Tag.E6 μ (Pi.single i 1) : ℤ) : K) ^ 2 = 1 := by
    rcases wordSign_eq_one_or μ hi with h1 | h1 <;> simp [h1]
  have hs' : (s i : K) = (wordSign Tag.E6 μ (Pi.single i 1) : K) *
      (wordSign Tag.E6 μ' (Pi.single i 1) : K) := by
    linear_combination (-(wordSign Tag.E6 μ' (Pi.single i 1) : K)) * hv +
      (-(s i : K)) * hσ'
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, hs', mul_pow, hσ, hσ', one_mul]

theorem bm_word_mul (μ μ' : List (Fin Tag.E6.rank)) (a b : Fin Tag.E6.rank → Kˣ) :
    MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K a *
        (MulAut.conj (weylWordElt .E6 K μ') * rootDiagAutHom Tag.E6 K b) =
      MulAut.conj (weylWordElt .E6 K (μ ++ μ')) *
        rootDiagAutHom Tag.E6 K (weylTuple ((coxeterSystem Tag.E6).wordProd μ')⁻¹ a * b) := by
  have h := bm_rootDiag_mul_conj (bm_weylWordElt_mem_monomial (K := K) μ')
    (bm_mapsRootLines_weylWordElt μ') a
  rw [bm_weylWordElt_append, map_mul, map_mul]
  calc MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K a *
        (MulAut.conj (weylWordElt .E6 K μ') * rootDiagAutHom Tag.E6 K b)
      = MulAut.conj (weylWordElt .E6 K μ) * (rootDiagAutHom Tag.E6 K a *
          MulAut.conj (weylWordElt .E6 K μ')) * rootDiagAutHom Tag.E6 K b := by group
    _ = _ := by
        rw [h]
        group

theorem bm_weylTuple_eq_of_commute {n : adjointGroup Tag.E6 K} {v : WeylGroup Tag.E6}
    (hn : (n : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K)
    (hv : MapsRootLines (n : ModGL Tag.E6 K) v) (a t : Fin Tag.E6.rank → Kˣ)
    (h : MulAut.conj n * rootDiagAutHom Tag.E6 K a * rootDiagAutHom Tag.E6 K t =
      rootDiagAutHom Tag.E6 K t * (MulAut.conj n * rootDiagAutHom Tag.E6 K a)) :
    weylTuple v t = t := by
  apply rootDiagAutHom_injective (τ := Tag.E6) (K := K)
  have h2 : rootDiagAutHom Tag.E6 K a * rootDiagAutHom Tag.E6 K t =
      rootDiagAutHom Tag.E6 K t * rootDiagAutHom Tag.E6 K a := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [mul_assoc, h2, ← mul_assoc, bm_conj_mul_rootDiag hn hv, mul_assoc] at h
  exact mul_right_cancel h

theorem bm_wordProd_eq_one {μ : List (Fin Tag.E6.rank)} {b : Fin Tag.E6.rank → Kˣ}
    (h : MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K b = 1) :
    (coxeterSystem Tag.E6).wordProd μ = 1 := by
  refine ext_single fun i => ?_
  have hi := isRoot_single Tag.E6 i
  have hx := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) =>
    ((φ ⟨xUnit Tag.E6 K i 1, xUnit_mem_adjointGroup i 1⟩ : adjointGroup Tag.E6 K) :
      ModGL Tag.E6 K)) h
  change (weylWordElt .E6 K μ : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b * xUnit Tag.E6 K i 1 *
      (rootDiagUnit Tag.E6 b)⁻¹) * (weylWordElt .E6 K μ : ModGL Tag.E6 K)⁻¹ =
    xUnit Tag.E6 K i 1 at hx
  rw [← pinnedX_single, rootDiagUnit_conj_pinnedX b hi, coe_weylWordElt,
    wordRep_conj_pinnedX K μ hi] at hx
  have hne : ((wordSign Tag.E6 μ (Pi.single i 1) : ℤ) : K) *
      (((rootChar b (Pi.single i 1) : Kˣ) : K) * 1) ≠ 0 := by
    refine mul_ne_zero ?_ (by simp)
    rcases wordSign_eq_one_or μ hi with h1 | h1 <;> simp [h1]
  have e := eq_of_pinnedX_eq_pinnedX (isRoot_wordAct μ hi) ⟨hi, by simp⟩ hne hx
  rw [wordAct_eq_smul] at e
  rw [e, one_smul]

theorem bm_conj_word_bmX {u : List (Fin Tag.E6.rank)} (μ : List (Fin Tag.E6.rank))
    (hu : (coxeterSystem Tag.E6).wordProd u * (coxeterSystem Tag.E6).wordProd μ =
      (coxeterSystem Tag.E6).wordProd μ * (coxeterSystem Tag.E6).wordProd u)
    (b : Fin Tag.E6.rank → Kˣ) :
    ∃ s : Fin Tag.E6.rank → Kˣ, (∀ i, s i ^ 2 = 1) ∧
      MulAut.conj (weylWordElt .E6 K u) *
          (MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K b) *
          (MulAut.conj (weylWordElt .E6 K u))⁻¹ =
        MulAut.conj (weylWordElt .E6 K μ) *
          rootDiagAutHom Tag.E6 K (s * weylTuple ((coxeterSystem Tag.E6).wordProd u) b) := by
  obtain ⟨s, hs, he⟩ := bm_weylWordElt_eq_mul_sign (K := K) (μ := u ++ μ) (μ' := μ ++ u)
    (by rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, hu])
  have hum := bm_weylWordElt_mem_monomial (K := K) u
  have hur := bm_mapsRootLines_weylWordElt (K := K) u
  rw [bm_weylWordElt_append, bm_weylWordElt_append, Subgroup.coe_mul, Subgroup.coe_mul] at he
  set v := (coxeterSystem Tag.E6).wordProd u
  set y : adjointGroup Tag.E6 K := (weylWordElt .E6 K μ)⁻¹ *
    (weylWordElt .E6 K u * weylWordElt .E6 K μ * (weylWordElt .E6 K u)⁻¹) with hy
  have hyd : (y : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 (weylTuple v s) := by
    rw [← monomial_conj_rootDiagUnit_weylTuple hum hur s, hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [he]
    group
  refine ⟨weylTuple v s, weylTuple_sq_eq_one hs v, ?_⟩
  have e1 : weylWordElt .E6 K u * weylWordElt .E6 K μ * (weylWordElt .E6 K u)⁻¹ =
      weylWordElt .E6 K μ * y := by
    rw [hy]
    group
  have e2 := bm_conj_mul_rootDiag hum hur b
  calc MulAut.conj (weylWordElt .E6 K u) *
        (MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K b) *
        (MulAut.conj (weylWordElt .E6 K u))⁻¹
      = MulAut.conj (weylWordElt .E6 K u * weylWordElt .E6 K μ *
          (weylWordElt .E6 K u)⁻¹) * (MulAut.conj (weylWordElt .E6 K u) *
            rootDiagAutHom Tag.E6 K b * (MulAut.conj (weylWordElt .E6 K u))⁻¹) := by
        simp only [map_mul, map_inv]
        group
    _ = _ := by
        rw [e1, e2, map_mul MulAut.conj, bm_conj_eq_rootDiagAutHom hyd, map_mul]
        group

end Calc

section Cube

variable
  {K : Type} [Field K]

theorem bm_conj_e6LineElt (ω : Kˣ) :
    MulAut.conj (e6LineElt ω) = rootDiagAutHom Tag.E6 K (e6LineChar ω) :=
  bm_conj_eq_rootDiagAutHom (coe_e6LineElt ω)

theorem bm_rootDiagUnit_cartan_mem (u : Kˣ) (z : Fin Tag.E6.rank → ℤ) :
    rootDiagUnit Tag.E6 (fun j => u ^ ∑ i, z i * Tag.E6.cartan i j) ∈ adjointGroup Tag.E6 K := by
  have h := list_prod_torusElt_eq_rootDiagUnit (K := K) (τ := Tag.E6) (fun i => u ^ z i)
  have e : cartanChar (fun i => u ^ z i) = fun j => u ^ ∑ i, z i * Tag.E6.cartan i j := by
    funext j
    simp only [cartanChar, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum]
  rw [← e, ← h]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_adjointGroup i _

@[expose] def bmD0Coeff : Fin Tag.E6.rank → ℤ := ![3, 5, 6, 9, 7, 4]

@[expose] def bmD0Exp : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 0, 1, 1]

theorem bm_e6D0Char_cartan : ∀ j : Fin Tag.E6.rank,
    ∑ i, bmD0Coeff i * Tag.E6.cartan i j = bmD0Exp j := by
  decide +kernel

theorem bm_rootDiagUnit_e6D0Char_mem (ω : Kˣ) :
    rootDiagUnit Tag.E6 (e6D0Char ω) ∈ adjointGroup Tag.E6 K := by
  have e : e6D0Char ω = fun j => ω ^ ∑ i, bmD0Coeff i * Tag.E6.cartan i j := by
    rw [e6D0Char_eq]
    funext j
    rw [bm_e6D0Char_cartan j]
    rfl
  rw [e]
  exact bm_rootDiagUnit_cartan_mem ω _

theorem bm_d0_mem_innerAut (ω : Kˣ) :
    rootDiagAutHom Tag.E6 K (e6D0Char ω) ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
  ⟨⟨_, bm_rootDiagUnit_e6D0Char_mem ω⟩, bm_conj_eq_rootDiagAutHom rfl⟩

theorem bm_ch_ne_one {ω : Kˣ} (h1 : ω ≠ 1) : MulAut.conj (e6LineElt ω) ≠ 1 := by
  rw [bm_conj_e6LineElt]
  intro h
  exact h1 (by
    simpa [e6LineChar] using
      congrFun (rootDiagAutHom_injective (h.trans (map_one (rootDiagAutHom Tag.E6 K)).symm)) 3)

theorem bm_d0_notMem_zpowers {ω : Kˣ} (h1 : ω ≠ 1) :
    rootDiagAutHom Tag.E6 K (e6D0Char ω) ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rw [bm_conj_e6LineElt, ← map_zpow] at hk
  have e := congrFun (rootDiagAutHom_injective hk) 1
  change e6LineChar ω 1 ^ k = e6D0Char ω 1 at e
  simp [e6LineChar, e6D0Char] at e
  exact h1 e.symm

variable [Finite K]

@[expose] def BmGood (ω : Kˣ) (E : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    (X : MulAut (adjointGroup Tag.E6 K)) : Prop :=
  IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ ¬ E6NormalizesR K E ∧
    MulAut.conj (e6LineElt ω) ∈ E ∧ rootDiagAutHom Tag.E6 K (e6D0Char ω) ∈ E ∧ X ∈ E ∧
      X ∉ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)

@[expose] def BmGoal (ω : Kˣ) (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Prop :=
  ∃ (c : Kˣ) (φ : MulAut (adjointGroup Tag.E6 K)),
    E.map (MulAut.congr φ).toMonoidHom = e6BadCube K ω c

theorem bm_mem_map_congr {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (φ : MulAut (adjointGroup Tag.E6 K)) {ε : MulAut (adjointGroup Tag.E6 K)} (hε : ε ∈ E) :
    φ * ε * φ⁻¹ ∈ E.map (MulAut.congr φ).toMonoidHom :=
  ⟨ε, hε, congr_toMonoidHom_apply φ ε⟩

theorem BmGood.map {ω : Kˣ} {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {X : MulAut (adjointGroup Tag.E6 K)} (h : BmGood ω E X) (φ : MulAut (adjointGroup Tag.E6 K))
    (hh : MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr φ).toMonoidHom)
    (hd : rootDiagAutHom Tag.E6 K (e6D0Char ω) ∈ E.map (MulAut.congr φ).toMonoidHom) :
    BmGood ω (E.map (MulAut.congr φ).toMonoidHom) (φ * X * φ⁻¹) := by
  obtain ⟨hE, hEc, hER, -, -, hX, hXi⟩ := h
  refine ⟨hE.map _, ?_, fun h' => hER (e6NormalizesR_of_map_congr φ h'), hh, hd,
    bm_mem_map_congr φ hX, fun hi => hXi ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hEc]
  · have h2 := CFSG.Fischer.innerAut_normal.conj_mem _ hi φ⁻¹
    rwa [inv_inv, show φ⁻¹ * (φ * X * φ⁻¹) * φ = X by group] at h2

theorem bmGoal_of_map {ω : Kˣ} {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (φ : MulAut (adjointGroup Tag.E6 K)) (h : BmGoal ω (E.map (MulAut.congr φ).toMonoidHom)) :
    BmGoal ω E := by
  obtain ⟨c, ψ, hψ⟩ := h
  exact ⟨c, ψ * φ, by rw [← hψ, Subgroup.map_map]; rfl⟩

theorem BmGood.closure_eq {ω : Kˣ} (h1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {X : MulAut (adjointGroup Tag.E6 K)} (h : BmGood ω E X) :
    Subgroup.closure {MulAut.conj (e6LineElt ω), rootDiagAutHom Tag.E6 K (e6D0Char ω), X} = E := by
  obtain ⟨-, hEc, -, hh, hd, hX, hXi⟩ := h
  refine bm_closure_three_eq hEc hh hd hX (bm_ch_ne_one h1) (bm_d0_notMem_zpowers h1)
    fun hc => hXi ((Subgroup.closure_le _).2 ?_ hc)
  rintro x (rfl | rfl)
  · exact ⟨e6LineElt ω, rfl⟩
  · exact bm_d0_mem_innerAut ω

theorem bmGoal_of_bmX {ω : Kˣ} (h1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {c : Kˣ} (h : BmGood ω E (e6BadX K c)) : BmGoal ω E := by
  refine ⟨c, 1, ?_⟩
  have hid : (MulAut.congr (1 : MulAut (adjointGroup Tag.E6 K))).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun ε => by
    rw [congr_toMonoidHom_apply]
    simp
  rw [hid, Subgroup.map_id, e6BadCube, h.closure_eq h1]

end Cube

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
