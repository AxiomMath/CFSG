module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K]

namespace LeviBlock

theorem linBlock_eq_two_of_sixty [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {n : ℕ}
    {I : Set ℕ} {a : Fin n} (hq : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a))
    (h60 : Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 60) :
    linBlockLen n I a = 2 ∧ Nat.card K = 4 := by
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) (linBlockLen n I a)).symm hq)
  rw [card_range_toGL_quotient_center (by omega)] at h60
  obtain ⟨h1, h4⟩ := (ordA_eq_sixty_iff hK).mp h60
  exact ⟨by omega, h4⟩

theorem card_linBlockSL_of_sixty [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {n : ℕ}
    {I : Set ℕ} {a : Fin n} (hq : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a))
    (h60 : Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 60) :
    Nat.card ↥(linBlockSL K n I a) = 60 := by
  obtain ⟨h2, h4⟩ := linBlock_eq_two_of_sixty hK hq h60
  rw [← Nat.card_congr (slEquivToGLRange (K := K) (linBlockLen n I a)).toEquiv,
    card_SL_eq (by omega), h2, h4]
  decide

theorem six_le_of_three_le_card_linBlock {n : ℕ} {I : Set ℕ}
    (h3 : 3 ≤ Nat.card {a : Fin n // linBlockLen n I a = 2}) : 6 ≤ n := by
  let φ : {a : Fin n // linBlockLen n I a = 2} × Fin 2 → Fin n := fun x =>
    ⟨x.1.1 + x.2, by
      have := linBlockLen_le (I := I) x.1.1
      have := x.1.2
      have := x.2.isLt
      omega⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, i⟩ ⟨⟨a', ha'⟩, i'⟩ h
    have h' : (a : ℕ) + i = a' + i' := congrArg Fin.val h
    have hi := i.isLt
    have hi' := i'.isLt
    have haa : a = a' := by
      by_contra hne
      exact linBlock_disjoint (I := I) hne (r := a + i) (by omega) (by omega) (by omega)
        (by omega)
    subst haa
    exact Prod.ext rfl (show i = i' from Fin.ext (by omega))
  have h := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Nat.card_fin] at h
  omega

@[expose] def torusFourVec {n : ℕ} (t : Fin 4 → Kˣ) (i : Fin n) : Kˣ :=
  if h : (i : ℕ) < 4 then t ⟨i, h⟩ else if (i : ℕ) = 4 then (∏ j, t j)⁻¹ else 1

theorem torusFourVec_one {n : ℕ} : torusFourVec (n := n) (1 : Fin 4 → Kˣ) = 1 := by
  funext i
  simp only [torusFourVec, Pi.one_apply, Finset.prod_const_one, inv_one]
  split_ifs <;> rfl

theorem torusFourVec_mul {n : ℕ} (t s : Fin 4 → Kˣ) :
    torusFourVec (n := n) (t * s) = torusFourVec t * torusFourVec s := by
  funext i
  simp only [torusFourVec, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
  split_ifs <;> simp

theorem prod_torusFourVec {n : ℕ} (hn : 5 ≤ n) (t : Fin 4 → Kˣ) :
    ∏ i, torusFourVec (n := n) t i = 1 := by
  let g : ℕ → Kˣ := fun k => if h : k < 4 then t ⟨k, h⟩ else if k = 4 then (∏ j, t j)⁻¹ else 1
  have e : ∏ i, torusFourVec (n := n) t i = ∏ i : Fin n, g i := rfl
  rw [e, Fin.prod_univ_eq_prod_range g n, ← Finset.prod_range_mul_prod_Ico g hn,
    Finset.prod_eq_one (s := Finset.Ico 5 n) fun k hk => ?_, mul_one]
  · simp [Finset.prod_range_succ, g, Fin.prod_univ_four]
  · rw [Finset.mem_Ico] at hk
    have h1 : ¬ k < 4 := by omega
    have h2 : k ≠ 4 := by omega
    simp only [g, h1, h2, ↓reduceDIte, ↓reduceIte]

variable (K) in
@[expose] noncomputable def torusFour {n : ℕ} (hn : 5 ≤ n) :
    (Fin 4 → Kˣ) →* SpecialLinearGroup (Fin n) K where
  toFun t := ⟨diagonal fun i => (torusFourVec t i : K), by
    rw [det_diagonal, ← Units.coe_prod, prod_torusFourVec hn, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [torusFourVec_one]
  map_mul' t s := by
    apply Subtype.ext
    change diagonal (fun i => (torusFourVec (t * s) i : K)) =
      diagonal (fun i => (torusFourVec t i : K)) * diagonal (fun i => (torusFourVec s i : K))
    rw [diagonal_mul_diagonal, torusFourVec_mul]
    rfl

theorem coe_torusFour {n : ℕ} (hn : 5 ≤ n) (t : Fin 4 → Kˣ) :
    ((torusFour K hn t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (torusFourVec t i : K) :=
  rfl

theorem torusFour_mem_flagStabilizer {n : ℕ} (hn : 5 ≤ n) (I : Set ℕ) (t : Fin 4 → Kˣ) :
    torusFour K hn t ∈ flagStabilizer n K I := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries
    fun k l c _ hl hk => ?_
  rw [coe_torusFour, diagonal_apply_ne]
  intro e
  subst e
  omega

theorem eq_one_of_torusFour_mem_center {n : ℕ} (hn : 6 ≤ n) {t : Fin 4 → Kˣ}
    (ht : torusFour K (by omega) t ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    t = 1 := by
  have hsc := SpecialLinearGroup.scalar_eq_self_of_mem_center ht ⟨5, by omega⟩
  have h5 : ((torusFour K (by omega) t : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) ⟨5, by omega⟩ ⟨5, by omega⟩ = 1 := by
    rw [coe_torusFour, diagonal_apply_eq]
    have h1 : ¬ (5 : ℕ) < 4 := by omega
    have h2 : (5 : ℕ) ≠ 4 := by omega
    simp only [torusFourVec, h1, h2, ↓reduceDIte, ↓reduceIte, Units.val_one]
  rw [h5, map_one] at hsc
  funext j
  have hj := congrArg (fun A : Matrix (Fin n) (Fin n) K => A ⟨j, by omega⟩ ⟨j, by omega⟩) hsc
  have hj4 : (j : ℕ) < 4 := j.isLt
  simp only [one_apply_eq, coe_torusFour, diagonal_apply_eq, torusFourVec, hj4, ↓reduceDIte,
    Fin.eta] at hj
  exact Units.ext hj.symm

end LeviBlock

open LeviBlock

theorem four_le_pRank_of_comap_eq_flagStabilizer {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} [Finite K] (hK : Nat.card K = 4) {n : ℕ} (hn : 6 ≤ n) {I : Set ℕ}
    (ρ : SpecialLinearGroup (Fin n) K →* ↥L)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n K I) : 4 ≤ CFSG.Open.pRank 3 P := by
  have hn5 : 5 ≤ n := by omega
  set φ : (Fin 4 → Kˣ) →* Y := L.subtype.comp (ρ.comp (torusFour K hn5)) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ρ (torusFour K hn5 t) = 1 := Subtype.ext ht
    exact eq_one_of_torusFour_mem_center hn (hker h1)
  have hrange : φ.range ≤ P := by
    rintro _ ⟨t, rfl⟩
    have h1 : torusFour K hn5 t ∈ (P.subgroupOf L).comap ρ :=
      hcomap ▸ torusFour_mem_flagStabilizer hn5 I t
    exact h1
  have hunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
    (fun a => ?_) ?_ φ hinj hrange
  · funext j
    rw [Pi.pow_apply, Pi.one_apply, ← hunits]
    exact pow_card_eq_one'
  · rw [Nat.card_fun, hunits, Nat.card_fin]

theorem four_le_pRank_of_three_sixty_blocks {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {n : ℕ} {I : Set ℕ}
    (ρ : SpecialLinearGroup (Fin n) K →* ↥L)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n K I)
    (h3 : 3 ≤ Nat.card {a : Fin n // CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a) ∧
      Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 60}) :
    4 ≤ CFSG.Open.pRank 3 P := by
  obtain ⟨⟨a, hq, h60⟩⟩ : Nonempty {a : Fin n // CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a) ∧
      Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 60} := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Nat.card_of_isEmpty] at h3
    omega
  have h3' : 3 ≤ Nat.card {a : Fin n // linBlockLen n I a = 2} :=
    h3.trans (Nat.card_le_card_of_injective
      (fun x => ⟨x.1, (linBlock_eq_two_of_sixty hK x.2.1 x.2.2).1⟩)
      fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
  exact four_le_pRank_of_comap_eq_flagStabilizer (linBlock_eq_two_of_sixty hK hq h60).2
    (six_le_of_three_le_card_linBlock h3') ρ hker hcomap

end CFSG.AGLEmbedding
