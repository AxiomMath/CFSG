module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Frame
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.Goldschmidt.Steps.Sec82Tools

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

namespace E8Layer

open CFSG.LieType.Steinberg CFSG.Open CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)

open scoped commutatorElement
open CFSG.Timmesfeld TauCeti CFSG.RankThree.PartOne.KE CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

@[expose] def e8E6Node (k : Fin 6) : Fin (Tag.rank .E8) := k.castLE (by decide)

@[expose] def wordL : List (Fin 8) :=
  [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4,
    5, 0, 2, 3, 4, 1, 3]

@[expose] def unitVec (i : Fin (Tag.rank .E8)) : Fin (Tag.rank .E8) → ℤ := Pi.single i 1

@[expose] def wRefl (L : List (Fin 8)) (v : Fin (Tag.rank .E8) → ℤ) : Fin (Tag.rank .E8) → ℤ :=
  L.foldr (fun i u => reflect .E8 i u) v

theorem isRoot_wRefl (L : List (Fin 8)) {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) :
    IsRoot .E8 (wRefl L γ) := by
  induction L with
  | nil => exact hγ
  | cons i L ih => exact IsRoot.reflect (τ := .E8) i ih

theorem map_conj_mul_subgroup {K : Type} [Field K] (a b : adjointGroup .E8 K)
    (H : Subgroup (adjointGroup .E8 K)) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  have hc : (MulAut.conj (a * b)).toMonoidHom =
      ((MulAut.conj a).toMonoidHom).comp (MulAut.conj b).toMonoidHom :=
    MonoidHom.ext fun x => by simp [mul_assoc]
  rw [hc]

section Certs


@[expose] noncomputable def wElt (K : Type) [Field K] (L : List (Fin 8)) :
    adjointGroup .E8 K :=
  (L.map fun i => CFSG.LieType.Chevalley.weylElement .E8 K i).foldr (· * ·) 1


theorem map_conj_wElt (K : Type) [Field K] (L : List (Fin 8)) {γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : IsRoot .E8 γ) :
    ((adjDatum (rootOperatorFamily .E8) K).rootGroup γ).map
        (MulAut.conj (wElt K L)).toMonoidHom =
      (adjDatum (rootOperatorFamily .E8) K).rootGroup (wRefl L γ) := by
  induction L generalizing γ with
  | nil =>
    have h0 : wElt K [] = 1 := rfl
    have h1 : (MulAut.conj (wElt K [])).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun x => by rw [h0]; simp
    rw [h1, Subgroup.map_id]
    rfl
  | cons i L ih =>
    have h1 : wElt K (i :: L) = CFSG.LieType.Chevalley.weylElement .E8 K i * wElt K L := rfl
    rw [h1, map_conj_mul_subgroup, ih hγ,
      map_conj_weylElement_rootGroup_adj (τ := .E8) (K := K) i (isRoot_wRefl L hγ)]
    rfl

end Certs

section Generic

variable {G : Type*} [Group G]

theorem isElemAbelian_zpowers' {p : ℕ} [Fact p.Prime] {x : G} (hx : orderOf x = p) :
    IsElemAbelian p (Subgroup.zpowers x) :=
  ⟨inferInstance, fun y hy => orderOf_dvd_iff_pow_eq_one.1 (hx ▸ orderOf_dvd_of_mem_zpowers hy)⟩

theorem disjoint_zpowers_of_not_mem {p : ℕ} [hp : Fact p.Prime] {x : G}
    (hx : orderOf x = p)
    {P : Subgroup G} (hxP : x ∉ P) : Disjoint (Subgroup.zpowers x) P := by
  rw [Subgroup.disjoint_def]
  intro g hg hgP
  by_contra hg1
  have hord : orderOf g = p := by
    have h1 : orderOf g ∣ p := hx ▸ orderOf_dvd_of_mem_zpowers hg
    rcases (Nat.dvd_prime hp.out).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  have heq : Subgroup.zpowers g = Subgroup.zpowers x := by
    haveI : Finite (Subgroup.zpowers x) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx]; exact hp.out.ne_zero)
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.2 hg
    · simp [Nat.card_zpowers, hord, hx]
  have hxg : x ∈ Subgroup.zpowers g := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact hxP (Subgroup.zpowers_le.2 hgP hxg)

theorem commute_zpowers_of {x : G} {P : Subgroup G} (hc : ∀ l ∈ P, x * l = l * x) :
    ∀ a ∈ Subgroup.zpowers x, ∀ l ∈ P, l * a = a * l := by
  intro a ha l hl
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact ((Commute.zpow_left (show Commute x l from hc l hl) n).symm).eq

theorem not_mem_of_card_center {p : ℕ} [hp : Fact p.Prime] {x : G} (hx : orderOf x = p)
    {P : Subgroup G} (hc : ∀ l ∈ P, x * l = l * x) (hcard : ¬ p ∣ Nat.card (Subgroup.center ↥P)) :
    x ∉ P := by
  intro hxP
  apply hcard
  have hz : (⟨x, hxP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hc g.1 g.2).symm
  have h1 : orderOf (⟨⟨x, hxP⟩, hz⟩ : ↥(Subgroup.center ↥P)) = orderOf (⟨x, hxP⟩ : ↥P) :=
    Subgroup.orderOf_mk _ _
  have h2 : orderOf (⟨x, hxP⟩ : ↥P) = orderOf x := Subgroup.orderOf_mk _ _
  have h3 := orderOf_dvd_natCard (⟨⟨x, hxP⟩, hz⟩ : ↥(Subgroup.center ↥P))
  rw [h1, h2, hx] at h3
  exact h3

theorem center_eq_map_of_perfect {M H : Type*} [Group M] [Group H] {Ψ : M →* H}
    (hΨ : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center M)
    (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = (⊤ : Subgroup M)) :
    Subgroup.center H = (Subgroup.center M).map Ψ := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, rfl⟩ := hΨ z
    refine ⟨g, ?_, rfl⟩
    have hc : ∀ h : M, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center M := by
      intro h
      apply hker
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      have key : Ψ h * Ψ g = Ψ g * Ψ h := Subgroup.mem_center_iff.1 hz (Ψ h)
      calc Ψ g * Ψ h * (Ψ g)⁻¹ * (Ψ h)⁻¹ = (Ψ h * Ψ g) * (Ψ g)⁻¹ * (Ψ h)⁻¹ := by rw [key]
        _ = 1 := by group
    let φ : M →* Subgroup.center M :=
      MonoidHom.mk' (fun h => (⟨g * h * g⁻¹ * h⁻¹, hc h⟩ : Subgroup.center M)) (fun a b => by
        apply Subtype.ext
        show g * (a * b) * g⁻¹ * (a * b)⁻¹ =
          (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹)
        have hca : ∀ m : M, m * (g * a * g⁻¹ * a⁻¹) = (g * a * g⁻¹ * a⁻¹) * m :=
          fun m => Subgroup.mem_center_iff.1 (hc a) m
        have hcb : ∀ m : M, m * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * m :=
          fun m => Subgroup.mem_center_iff.1 (hc b) m
        calc g * (a * b) * g⁻¹ * (a * b)⁻¹
            = ((g * a * g⁻¹ * a⁻¹) * a) * ((g * b * g⁻¹ * b⁻¹) * b) * (a * b)⁻¹ := by group
          _ = (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹)) * b * (a * b)⁻¹ := by group
          _ = (g * a * g⁻¹ * a⁻¹) * ((g * b * g⁻¹ * b⁻¹) * a) * b * (a * b)⁻¹ := by
              rw [hcb a]
          _ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by group)
    have hcomm : ∀ a b : M, ⁅a, b⁆ ∈ φ.ker := by
      intro a b
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply commutatorElement_eq_one_iff_commute.2
      apply Subtype.ext
      show (φ a : M) * (φ b : M) = (φ b : M) * (φ a : M)
      exact Subgroup.mem_center_iff.1 (φ b).2 (φ a : M)
    have htop : (⊤ : Subgroup M) ≤ φ.ker := by
      calc (⊤ : Subgroup M) = ⁅(⊤ : Subgroup M), ⊤⁆ := hM.symm
        _ ≤ φ.ker := Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    have hcen : ∀ h : M, g * h = h * g := by
      intro h
      have hh : φ h = 1 := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top h))
      have h1 : g * h * g⁻¹ * h⁻¹ = 1 := congrArg Subtype.val hh
      calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
        _ = h * g := by rw [h1, one_mul]
    exact Subgroup.mem_center_iff.2 fun h => (hcen h).symm
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := hΨ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.1 hg m

theorem card_center_dvd_of_perfect {M H : Type*} [Group M] [Group H] {Ψ : M →* H}
    (hΨ : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center M)
    (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = (⊤ : Subgroup M)) :
    Nat.card (Subgroup.center H) ∣ Nat.card (Subgroup.center M) := by
  rw [center_eq_map_of_perfect hΨ hker hM]
  exact Subgroup.card_map_dvd _ _

end Generic

section SL3

theorem card_SL3_eq (K : Type) [Field K] [Fintype K] (hK : 2 ≤ Fintype.card K) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      (Fintype.card K ^ 3 - 1) * Fintype.card K ^ 3 * (Fintype.card K ^ 2 - 1) := by
  rw [Matrix.card_SL_field]
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  obtain ⟨t, ht⟩ : ∃ t, Fintype.card K = t + 2 := ⟨Fintype.card K - 2, by omega⟩
  rw [ht]
  have h1 : t + 2 ≤ (t + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : (t + 2) ^ 2 ≤ (t + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : 1 ≤ (t + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (t + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ t + 2 := by omega
  apply Nat.div_eq_of_eq_mul_left (by omega)
  zify [h1, h2, h3, h4, h5]
  ring

theorem exists_orderOf_SL3 (K : Type) [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hdvd : p ∣ Nat.card K ^ 3 - 1) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) K, orderOf a = p := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hK : 2 ≤ Fintype.card K := by
    have h := Finite.one_lt_card (α := K)
    rw [Nat.card_eq_fintype_card] at h
    omega
  apply exists_prime_orderOf_dvd_card'
  rw [Nat.card_eq_fintype_card (α := K)] at hdvd
  rw [card_SL3_eq K hK]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _

end SL3

section Layer


theorem reflect_neg_vec (i : Fin (Tag.rank .E8)) (v : Fin (Tag.rank .E8) → ℤ) :
    reflect .E8 i (-v) = -reflect .E8 i v := by
  funext j
  simp [reflect, Finset.sum_neg_distrib]
  ring

theorem wRefl_neg (L : List (Fin 8)) (v : Fin (Tag.rank .E8) → ℤ) :
    wRefl L (-v) = -wRefl L v := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    show reflect .E8 i (wRefl L (-v)) = -reflect .E8 i (wRefl L v)
    rw [ih]
    exact reflect_neg_vec _ _

@[expose] noncomputable def pairG (K : Type) [Field K] (v : Fin (Tag.rank .E8) → ℤ) :
    Subgroup (adjointGroup .E8 K) :=
  (adjDatum (rootOperatorFamily .E8) K).rootGroup v ⊔
    (adjDatum (rootOperatorFamily .E8) K).rootGroup (-v)

@[expose] def e8Sup : Fin 2 → Fin 8 := ![0, 2]

theorem map_conj_pairG (K : Type) [Field K] (L : List (Fin 8)) {v : Fin (Tag.rank .E8) → ℤ}
    (hv : IsRoot .E8 v) :
    (pairG K v).map (MulAut.conj (wElt K L)).toMonoidHom = pairG K (wRefl L v) := by
  unfold pairG
  rw [Subgroup.map_sup, map_conj_wElt K L hv,
    map_conj_wElt K L (CFSG.LieType.Chevalley.IsRoot.neg hv), wRefl_neg]

theorem noG2_E8 : NoG2 .E8 := by
  unfold NoG2
  decide +kernel

theorem not_isRoot_of_iform_ne_two {v : Fin (Tag.rank .E8) → ℤ}
    (h : iform (τ := .E8) v v ≠ 2) : ¬ IsRoot .E8 v := by
  intro hv
  obtain ⟨j, hj⟩ := iform_self_of_isRoot (τ := .E8) hv
  apply h
  have hs : ∀ j : Fin (Tag.rank .E8), Tag.symmetrizer .E8 j j = 1 := by decide
  rw [hj, hs j, mul_one]

theorem allOrth : ∀ i : Fin 2, ∀ k : Fin 6,
    iform (τ := .E8) (wRefl wordL (unitVec (e8Sup i))) (unitVec (e8E6Node k)) = 0 ∧
    wRefl wordL (unitVec (e8Sup i)) ≠ unitVec (e8E6Node k) ∧
    wRefl wordL (unitVec (e8Sup i)) ≠ -unitVec (e8E6Node k) ∧
    iform (τ := .E8) (wRefl wordL (unitVec (e8Sup i)) + unitVec (e8E6Node k))
      (wRefl wordL (unitVec (e8Sup i)) + unitVec (e8E6Node k)) ≠ 2 ∧
    iform (τ := .E8) (wRefl wordL (unitVec (e8Sup i)) + -unitVec (e8E6Node k))
      (wRefl wordL (unitVec (e8Sup i)) + -unitVec (e8E6Node k)) ≠ 2 := by
  decide +kernel

theorem comm_pair (K : Type) [Field K] (i : Fin 2) (k : Fin 6) :
    Commutes (pairG K (wRefl wordL (unitVec (e8Sup i)))) (pairG K (unitVec (e8E6Node k))) := by
  obtain ⟨h0, hne, hne', hpp, hpm⟩ := allOrth i k
  exact commutes_rootPair_of_noG2 noG2_E8 (isRoot_wRefl _ (isRoot_single _ _))
    (isRoot_single _ _) hne hne' h0 (not_isRoot_of_iform_ne_two hpp)
    (not_isRoot_of_iform_ne_two hpm)

theorem commutes_iSup_iSup {G : Type*} [Group G] {ι κ : Type*} (H : ι → Subgroup G)
    (L : κ → Subgroup G) (h : ∀ i j, Commutes (H i) (L j)) :
    Commutes (⨆ i, H i) (⨆ j, L j) := by
  have key : ∀ x ∈ (⨆ i, H i), ∀ y ∈ (⨆ j, L j), x * y = y * x := by
    intro x hx
    refine Subgroup.iSup_induction H (C := fun x => ∀ y ∈ (⨆ j, L j), x * y = y * x) hx ?_ ?_ ?_
    · intro i x hx y hy
      refine Subgroup.iSup_induction L (C := fun y => x * y = y * x) hy ?_ ?_ ?_
      · intro j y hy
        exact h i j x hx y hy
      · simp
      · intro a b ha hb
        rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
    · intro y _
      simp
    · intro a b ha hb y hy
      calc (a * b) * y = a * (b * y) := mul_assoc _ _ _
        _ = a * (y * b) := by rw [hb y hy]
        _ = (a * y) * b := (mul_assoc _ _ _).symm
        _ = (y * a) * b := by rw [ha y hy]
        _ = y * (a * b) := mul_assoc _ _ _
  exact fun x hx y hy => key x hx y hy

theorem comm_S_P (K : Type) [Field K] :
    Commutes (⨆ i : Fin 2, pairG K (wRefl wordL (unitVec (e8Sup i))))
      (⨆ k : Fin 6, pairG K (unitVec (e8E6Node k))) :=
  commutes_iSup_iSup _ _ (fun i k => comm_pair K i k)

theorem map_conj_S (K : Type) [Field K] :
    ((⨆ i : Fin 2, (adjDatum (rootOperatorFamily .E8) K).rootGroup (unitVec (e8Sup i)) ⊔
        (adjDatum (rootOperatorFamily .E8) K).rootGroup (-unitVec (e8Sup i))).map
      (MulAut.conj (wElt K wordL)).toMonoidHom) =
      ⨆ i : Fin 2, pairG K (wRefl wordL (unitVec (e8Sup i))) := by
  rw [Subgroup.map_iSup]
  refine iSup_congr fun i => ?_
  exact map_conj_pairG K wordL (isRoot_single _ _)

end Layer

section Adj


theorem e8E6_adj : ∀ i j : Fin 6, edgeE 6 i j → e8E6Node i ≠ e8E6Node j ∧
    Tag.cartan .E8 (e8E6Node i) (e8E6Node j) = -1 ∧
    Tag.cartan .E8 (e8E6Node j) (e8E6Node i) = -1 ∧
    ∃ l : Fin 8, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8E6Node i) l + 2 * Tag.cartan .E8 (e8E6Node j) l := by
  decide

theorem e8E6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
    e8E6Node i ≠ e8E6Node j ∧ Tag.cartan .E8 (e8E6Node i) (e8E6Node j) = 0 ∧
    Tag.cartan .E8 (e8E6Node j) (e8E6Node i) = 0 := by
  decide

theorem e8E6_frame (p f : ℕ) [Fact p.Prime] (hadm : StatedLieAdmissible .E6 0 p f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) :
    ∃ Ψ : (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →*
      adjointGroup .E8 K,
      Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup (e8E6Node k) ∧
      CFSG.IsQuasisimple ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup
        (e8E6Node k)) ∧
      CFSG.Blueprint.LieModel
        (↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup (e8E6Node k)) ⧸
          Subgroup.center ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup
            (e8E6Node k))) .E6 0 p f := by
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e8E6Node e8E6_adj e8E6_nadj
  exact e6_frame_subgroup hadm hK hcomm hρ hψ

theorem openQuasi_of_cfs {G : Type} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

theorem e8sup_range : Set.range e8Sup = e8support13 := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hi
    simp only [e8support13, e8Index, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

end Adj

section Main



theorem map_U_eq (K : Type) [Field K] :
    (⨆ i : Fin 2, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup (e8Sup i)).map
        (adjointGroup .E8 K).subtype =
      subsystemGroup .E8 K e8support13 := by
  rw [← e8sup_range]
  exact map_subtype_iSup_rankOne (τ := .E8) (K := K) e8Sup

theorem e8E6_layer_adjoint (q : PrimePower) (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.p ^ q.exponent)
    (hord : p ∣ q.card ^ 3 - 1) :
    ∃ (P : Subgroup (adjointGroup .E8 K))
      (x : adjointGroup .E8 K),
      orderOf x = p ∧ (∀ l ∈ P, x * l = l * x) ∧ x ∉ P ∧ CFSG.Open.IsQuasisimple ↥P ∧
      ∃ π : ↥P →* Cat ⟨.E6 q, LieTypeIndex.valid_E6 q⟩, Function.Surjective π ∧
        Nat.card π.ker ∣ 3 ∧ (∀ z : ↥P, π z = 1 → z ∈ Subgroup.center ↥P) := by
  classical
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hadm : StatedLieAdmissible .E6 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
  obtain ⟨Ψ, hker, hrange, hqs, hLM⟩ := e8E6_frame q.p q.exponent hadm hK
  have hMq := Group.isPerfect_def.1
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 (GaloisField q.p q.exponent)).1
  have hcen_dvd : Nat.card (Subgroup.center ↥Ψ.range) ∣ 3 := by
    have h1 := card_center_dvd_of_perfect (Ψ := Ψ.rangeRestrict)
      (MonoidHom.rangeRestrict_surjective Ψ) (by rw [MonoidHom.ker_rangeRestrict]; exact hker) hMq
    have h2 := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (GaloisField q.p q.exponent)).1
    exact dvd_trans h1 (by rw [h2]; exact Nat.gcd_dvd_left 3 _)
  have hcardP : ¬ p ∣ Nat.card (Subgroup.center ↥Ψ.range) := fun h => by
    have h3 : p ∣ 3 := dvd_trans h hcen_dvd
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hLM' : CFSG.Blueprint.LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range)
      StatedLieTag.E6 0 q.p q.exponent := by
    rw [hrange]
    exact hLM
  obtain ⟨-, hm⟩ := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hLM' (by decide)
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e6a⟩⟩ := hm
  obtain ⟨e6b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q (LieTypeIndex.valid_E6 q) K'
    (hK'c.trans (PrimePower.card_def q).symm)
  let e6 : ↥Ψ.range ⧸ Subgroup.center ↥Ψ.range ≃* Cat ⟨.E6 q, LieTypeIndex.valid_E6 q⟩ :=
    e6a.trans e6b
  let π : ↥Ψ.range →* Cat ⟨.E6 q, LieTypeIndex.valid_E6 q⟩ :=
    e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Ψ.range))
  have hπker : π.ker = Subgroup.center ↥Ψ.range := by
    ext g
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [← map_one e6, e6.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hπsurj : Function.Surjective π :=
    e6.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπcard : Nat.card π.ker ∣ 3 := by
    rw [hπker]
    exact hcen_dvd
  have hπcen : ∀ z : ↥Ψ.range, π z = 1 → z ∈ Subgroup.center ↥Ψ.range := fun z hz => by
    have hz' : z ∈ π.ker := MonoidHom.mem_ker.2 hz
    rw [hπker] at hz'
    exact hz'
  have hdvdK : p ∣ Nat.card K ^ 3 - 1 := by
    rw [hK]
    rw [PrimePower.card_def] at hord
    exact hord
  obtain ⟨a, ha⟩ := exists_orderOf_SL3 K hdvdK
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup (adjointGroup .E8 K),
      U = ⨆ i : Fin 2,
        rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup
          (e8Sup i) := ⟨_, rfl⟩
  have hU : U.map (adjointGroup .E8 K).subtype = subsystemGroup .E8 K e8support13 := by
    rw [hUdef]
    exact map_U_eq K
  obtain ⟨eU⟩ : Nonempty (U ≃* ↥(subsystemGroup .E8 K e8support13)) :=
    ⟨(U.equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hU)⟩
  obtain ⟨eSup⟩ : Nonempty (Matrix.SpecialLinearGroup (Fin 3) K ≃* U) :=
    ⟨(e8a2Equiv K).trans eU.symm⟩
  have hsord : orderOf (eSup a) = p := by
    rw [← ha]
    exact orderOf_injective eSup.toMonoidHom eSup.injective a
  obtain ⟨g0, hg0⟩ : ∃ g0 : adjointGroup .E8 K,
      g0 = ((eSup a : U) : adjointGroup .E8 K) := ⟨_, rfl⟩
  have hg0ord : orderOf g0 = p := by
    rw [hg0, Subgroup.orderOf_coe, hsord]
  obtain ⟨n, hn⟩ : ∃ n : adjointGroup .E8 K,
      n = wElt K wordL := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : adjointGroup .E8 K, x = n * g0 * n⁻¹ :=
    ⟨_, rfl⟩
  have h1 : x = (MulAut.conj n).toMonoidHom g0 := by
    rw [hx]
    rfl
  have hxord : orderOf x = p := by
    rw [h1, orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective g0, hg0ord]
  have hmapS : U.map (MulAut.conj n).toMonoidHom =
      ⨆ i : Fin 2, pairG K (wRefl wordL (unitVec (e8Sup i))) := by
    rw [hUdef, hn]
    exact map_conj_S K
  have hxmem : x ∈ ⨆ i : Fin 2,
      pairG K (wRefl wordL (unitVec (e8Sup i))) := by
    rw [← hmapS, h1]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [hg0]
    exact (eSup a).2
  have hxcomm : ∀ l ∈ Ψ.range, x * l = l * x := by
    intro l hl
    rw [hrange] at hl
    exact comm_S_P K x hxmem l hl
  have hxP : x ∉ Ψ.range := not_mem_of_card_center hxord hxcomm hcardP
  have hqs' : CFSG.Open.IsQuasisimple ↥Ψ.range := openQuasi_of_cfs (by rw [hrange]; exact hqs)
  exact ⟨Ψ.range, x, hxord, hxcomm, hxP, hqs', π, hπsurj, hπcard, hπcen⟩

end Main

section Final



theorem card_ker_comp_equiv' {G H Q : Type*} [Group G] [Group H] [Group Q] (e : G ≃* H)
    (f : H →* Q) : Nat.card (f.comp e.toMonoidHom).ker = Nat.card f.ker := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv e.toEquiv (fun x => Iff.rfl)

theorem mem_center_of_equiv_symm' {A B : Type*} [Group A] [Group B] (e : A ≃* B) {z : B}
    (h : e.symm z ∈ Subgroup.center A) : z ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h' := Subgroup.mem_center_iff.1 h (e.symm g)
  apply e.symm.injective
  simpa [map_mul] using h'

theorem e8E6LayerInput_proved : CFSG.LieType.SeitzGeneration.ExcHigh.E8E6LayerInput := by
  intro q hv p hp h7 _hpq hord
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqpos : 0 < q.card := by
    rw [PrimePower.card_def]
    exact pow_pos q.prime_p.pos _
  have hdvd : p ∣ q.card ^ 3 - 1 := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have h3 : ((q.card ^ 3 - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hqpos), Nat.cast_pow, Nat.cast_one, sub_eq_zero]
      have h := pow_orderOf_eq_one ((q.card : ℕ) : ZMod p)
      rw [hord] at h
      exact h
    exact (ZMod.natCast_eq_zero_iff _ _).1 h3
  have hKp : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.card :=
    hKp.trans (PrimePower.card_def q).symm
  obtain ⟨P, x, hxord, hcomm, hxP, hqs, π, hπsurj, hπdvd, hπcen⟩ :=
    e8E6_layer_adjoint q p h7 (GaloisField q.p q.exponent) hKp hdvd
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    (GaloisField q.p q.exponent) hKq
  let ι8 : adjointGroup .E8 (GaloisField q.p q.exponent) ≃* Cat ⟨.E8 q, hv⟩ :=
    (CFSG.GH74.Filter.Lie.adjointQuotientEquiv .E8 (GaloisField q.p q.exponent)).symm.trans b
  have hx' : orderOf (ι8 x) = p :=
    (orderOf_injective ι8.toMonoidHom ι8.injective x).trans hxord
  have hc' : ∀ l ∈ P.map ι8.toMonoidHom, ι8 x * l = l * ι8 x := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := Subgroup.mem_map.1 hl
    show ι8 x * ι8 l0 = ι8 l0 * ι8 x
    rw [← map_mul, ← map_mul, hcomm l0 hl0]
  have hxP' : ι8 x ∉ P.map ι8.toMonoidHom := by
    intro h
    obtain ⟨l0, hl0, hl⟩ := Subgroup.mem_map.1 h
    exact hxP ((ι8.injective hl) ▸ hl0)
  let e := P.equivMapOfInjective ι8.toMonoidHom ι8.injective
  refine ⟨P.map ι8.toMonoidHom, Subgroup.zpowers (ι8 x), π.comp e.symm.toMonoidHom, ?_, ?_, ?_,
    ?_, isElemAbelian_zpowers' hx', ?_, ?_, disjoint_zpowers_of_not_mem hx' hxP'⟩
  · exact hπsurj.comp e.symm.surjective
  · rw [card_ker_comp_equiv']
    exact hπdvd
  · intro z hz
    exact mem_center_of_equiv_symm' e (hπcen (e.symm z) hz)
  · exact CFSG.Goldschmidt.Sec82.isQuasisimple_of_mulEquiv e hqs
  · rw [Nat.card_zpowers, hx']
  · intro l hl a ha
    exact commute_zpowers_of hc' a ha l hl

end Final

end E8Layer
end CFSG.LieType.SeitzGeneration.ExcHigh
end
