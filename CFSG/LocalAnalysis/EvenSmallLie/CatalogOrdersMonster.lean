module

public import CFSG.YGroups.Chain
public import CFSG.LocalAnalysis.SectionRank.Monster
public meta import CFSG.YGroups.Defs
public meta import Certificates.Data.CFSGNative.YGroups.Check
public import Certificates.Certificate3174
public import Certificates.Certificate10093
public import CFSG.Open.Defs
public import CFSG.YGroups.Bound
public meta import Mathlib

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.YGroups CFSG.Certificates.CosetEnumeration

theorem rels_y110_y210 : ∀ w ∈ yRels 1 1 0, w.map (shiftAt 1) ∈ yRels 2 1 0 := by decide

theorem y210 :
    Finite (YGroup 2 1 0) ∧ Nat.card (YGroup 2 1 0) ≤ 120 :=
  Certificates.certificate3174.1

theorem rels_y210_y220 : ∀ w ∈ yRels 2 1 0, w.map (shiftAt 3) ∈ yRels 2 2 0 := by decide

theorem y220 :
    Finite (YGroup 2 2 0) ∧ Nat.card (YGroup 2 2 0) ≤ 720 :=
  Certificates.certificate3174.2.1

theorem rels_y220_y320 : ∀ w ∈ yRels 2 2 0, w.map (shiftAt 2) ∈ yRels 3 2 0 := by decide

theorem y320 :
    Finite (YGroup 3 2 0) ∧ Nat.card (YGroup 3 2 0) ≤ 5040 :=
  Certificates.certificate3174.2.2.1

theorem rels_y320_y330 : ∀ w ∈ yRels 3 2 0, w.map (shiftAt 5) ∈ yRels 3 3 0 := by decide

theorem y330 :
    Finite (YGroup 3 3 0) ∧ Nat.card (YGroup 3 3 0) ≤ 40320 :=
  Certificates.certificate3174.2.2.2.1

theorem rels_y330_y430 : ∀ w ∈ yRels 3 3 0, w.map (shiftAt 3) ∈ yRels 4 3 0 := by decide

theorem y430 :
    Finite (YGroup 4 3 0) ∧ Nat.card (YGroup 4 3 0) ≤ 362880 :=
  Certificates.certificate3174.2.2.2.2.1

theorem rels_y430_y440 : ∀ w ∈ yRels 4 3 0, w.map (shiftAt 7) ∈ yRels 4 4 0 := by decide

theorem y440 :
    Finite (YGroup 4 4 0) ∧ Nat.card (YGroup 4 4 0) ≤ 3628800 :=
  Certificates.certificate3174.2.2.2.2.2

noncomputable def yLift {G : Type*} [Group G] (p q r : ℕ) (g : ℕ → G)
    (hg : ∀ w ∈ yRels p q r, evalWord g w = 1) : YGroup p q r →* G :=
  PresentedGroup.toGroup (f := fun c : Fin (ngen p q r) => g c) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := g)]
    · exact hg w hw
    · intro c hc
      simp [lt_ngen_of_mem_yRels hw c hc])

theorem yLift_yGen {G : Type*} [Group G] {p q r : ℕ} {g : ℕ → G}
    (hg : ∀ w ∈ yRels p q r, evalWord g w = 1) {c : ℕ} (hc : c < ngen p q r) :
    yLift p q r g hg (yGen p q r c) = g c := by
  rw [yGen_of_lt hc, yLift, PresentedGroup.toGroup.of]

def pathPos (c : ℕ) : ℕ := if c ≤ 4 then 4 - c else c

def s10Gen (c : ℕ) : Equiv.Perm (Fin 10) :=
  if h : pathPos c < 9 then Equiv.swap (Fin.castSucc ⟨pathPos c, h⟩) (Fin.succ ⟨pathPos c, h⟩)
  else 1

theorem s10Gen_rels : ∀ w ∈ yRels 4 4 0, evalWord s10Gen w = 1 := by decide

noncomputable def s10Hom : YGroup 4 4 0 →* Equiv.Perm (Fin 10) := yLift 4 4 0 s10Gen s10Gen_rels

theorem s10Gen_pathPos : ∀ i : Fin 9, s10Gen (pathPos i) = Equiv.swap i.castSucc i.succ := by
  decide

theorem s10Hom_surjective : Function.Surjective s10Hom := by
  intro σ
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 9 ↦ Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  have hle : Submonoid.closure (Set.range fun i : Fin 9 ↦ Equiv.swap i.castSucc i.succ) ≤
      s10Hom.range.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    have hi : pathPos i < ngen 4 4 0 := by
      have := i.2
      simp only [pathPos, ngen]
      split_ifs <;> omega
    exact ⟨yGen 4 4 0 (pathPos i), by rw [s10Hom, yLift_yGen _ hi, s10Gen_pathPos]⟩
  exact hle hσ

theorem s10Hom_bijective :
    Function.Bijective s10Hom := by
  have := y440.1
  refine (Nat.bijective_iff_surjective_and_card s10Hom).2 ⟨s10Hom_surjective, ?_⟩
  have h1 := Nat.card_le_card_of_surjective s10Hom s10Hom_surjective
  have h2 : Nat.card (Equiv.Perm (Fin 10)) = 3628800 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have := y440.2
  omega

noncomputable def s10Equiv :
    YGroup 4 4 0 ≃* Equiv.Perm (Fin 10) :=
  MulEquiv.ofBijective s10Hom s10Hom_bijective

open CFSG.Blueprint.NativeSporadic CFSG.SectionRank

theorem evalWord_pairWord {G : Type*} [Group G] (g : ℕ → G) (p q r s t : ℕ) :
    evalWord g (pairWord p q r s t) = (g s * g t) ^ pairExp p q r s t := by
  simp [evalWord, pairWord, List.map_flatten, List.prod_flatten, List.prod_replicate]

noncomputable def y443Letter (c : ℕ) : Y443 := if h : c < 12 then y443Gen ⟨c, h⟩ else 1

theorem yEdges_440_iff : ∀ s t : Fin 9, s < t →
    ((s.val, t.val) ∈ yEdges 4 4 0 ↔
      y443AdjB (Fin.castLE (by norm_num) s) (Fin.castLE (by norm_num) t) = true) := by
  decide

theorem y443Letter_rels : ∀ w ∈ yRels 4 4 0, evalWord y443Letter w = 1 := by
  intro w hw
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hsp
  · have hs' : s < 12 := by simp only [ngen] at hs; omega
    rw [evalWord_cons, evalWord_cons, evalWord_nil, mul_one, y443Letter, dite_eq_left hs', ← sq,
      y443Gen_sq]
  · have hs' : s < 9 := by simp only [ngen] at hs; omega
    have ht' : t < 9 := by simp only [ngen] at ht; omega
    have key := yEdges_440_iff ⟨s, hs'⟩ ⟨t, ht'⟩ hst
    rw [evalWord_pairWord, y443Letter, dite_eq_left (by omega), y443Letter,
      dite_eq_left (by omega), pairExp]
    split_ifs with he
    · exact y443Gen_edge _ _ (y443Graph_adj _ _ (key.1 he))
    · have hne : (⟨s, by omega⟩ : Fin 12) ≠ ⟨t, by omega⟩ := fun h => by
        rw [Fin.mk.injEq] at h
        omega
      have hc := y443Gen_commute _ _ hne fun h => he (key.2 ((y443Adjacent_iff _ _).1 h))
      rw [hc.mul_pow, y443Gen_sq, y443Gen_sq, one_mul]
  · simp at hsp

noncomputable def y443Hom : YGroup 4 4 0 →* Y443 := yLift 4 4 0 y443Letter y443Letter_rels

noncomputable def s10ToY443 :
    Equiv.Perm (Fin 10) →* Y443 :=
  y443Hom.comp s10Equiv.symm.toMonoidHom

theorem s10ToY443_threeCycle :
    s10ToY443 (s10Gen 0 * s10Gen 1) = y443Gen 0 * y443Gen 1 := by
  have h0 : (0 : ℕ) < ngen 4 4 0 := by simp [ngen]
  have h1 : (1 : ℕ) < ngen 4 4 0 := by simp [ngen]
  have h : s10Equiv.symm (s10Gen 0 * s10Gen 1) = yGen 4 4 0 0 * yGen 4 4 0 1 := by
    rw [MulEquiv.symm_apply_eq, map_mul, s10Equiv, MulEquiv.ofBijective_apply,
      MulEquiv.ofBijective_apply, s10Hom, yLift_yGen _ h0, yLift_yGen _ h1]
  rw [s10ToY443, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, map_mul, y443Hom,
    yLift_yGen _ h0, yLift_yGen _ h1]
  rfl

theorem s10ToY443_mem_commutator
    {σ : Equiv.Perm (Fin 10)}
    (hσ : σ ∈ alternatingGroup (Fin 10)) :
    s10ToY443 σ ∈ commutator Y443 := by
  rw [← alternatingGroup.commutator_perm_eq (by simp)] at hσ
  have hle : (commutator (Equiv.Perm (Fin 10))).map s10ToY443 ≤ commutator Y443 := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hle ⟨σ, hσ, rfl⟩

theorem twentyfive_dvd_card_of_mulEquiv_M
    {T : Type} [Group T]
    [Finite T] [Nontrivial T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.M) : 25 ∣ Nat.card T := by
  have : Nontrivial M := e.injective.nontrivial
  have hG : commutator Y443 ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hord : orderOf (y443Gen 0 * y443Gen 1) = 3 :=
    orderOf_mul_eq_three_of_adj y443Graph y443Graph_connected y443Graph_cliqueFree y443Gen
      y443_closure y443Gen_sq y443Gen_edge y443Gen_commute hG (y443Graph_adj 0 1 rfl)
  have hc : s10Gen 0 * s10Gen 1 ∈ alternatingGroup (Fin 10) :=
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨4, 5, by decide, by decide⟩
      ⟨3, 4, by decide, by decide⟩
  have := alternatingGroup.isSimpleGroup (α := Fin 10) (by simp)
  let f : alternatingGroup (Fin 10) →* commutator Y443 :=
    (s10ToY443.comp (alternatingGroup (Fin 10)).subtype).codRestrict _
      fun σ => s10ToY443_mem_commutator σ.2
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker).resolve_right fun htop => ?_
    have hmem : (⟨_, hc⟩ : alternatingGroup (Fin 10)) ∈ f.ker := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have h1 : y443Gen 0 * y443Gen 1 = 1 := by
      rw [← s10ToY443_threeCycle]
      exact congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [nat_card_alternatingGroup, Nat.card_fin] at hdvd
  rw [Nat.card_congr e.toEquiv]
  exact dvd_trans (by decide) hdvd

end CFSG.EvenSmallLie.CatalogOrders
