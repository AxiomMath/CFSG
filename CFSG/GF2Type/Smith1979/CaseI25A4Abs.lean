module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case25

namespace SixGen

section Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_two_ne_notMem (hι : Fintype.card ι = 6) (T : Finset ι) (hT : T.card ≤ 4) :
    ∃ a b : ι, a ∉ T ∧ b ∉ T ∧ a ≠ b := by
  have hc : 1 < Tᶜ.card := by rw [Finset.card_compl, hι]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
  exact ⟨a, b, Finset.mem_compl.1 ha, Finset.mem_compl.1 hb, hab⟩

theorem exists_alt_two (hι : Fintype.card ι = 6) {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ σ ∈ alternatingGroup ι, σ i = k ∧ σ j = l := by
  have hτi : Equiv.swap i k i = k := Equiv.swap_apply_left i k
  have hτj : Equiv.swap i k j ≠ k := fun h =>
    hij ((Equiv.swap i k).injective (h.trans hτi.symm)).symm
  have h0i : (Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k) i = k := by
    rw [Equiv.Perm.mul_apply, hτi]
    exact Equiv.swap_apply_of_ne_of_ne hτj.symm hkl
  have h0j : (Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k) j = l := by
    rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne_notMem hι {k, l}
    ((Finset.card_le_two).trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
  by_cases hs : Equiv.Perm.sign (Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k) = 1
  · exact ⟨_, Equiv.Perm.mem_alternatingGroup.2 hs, h0i, h0j⟩
  · refine ⟨Equiv.swap a b * (Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k), ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      rcases Int.units_eq_one_or
        (Equiv.Perm.sign (Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k)) with h | h
      · exact absurd h hs
      · rw [h]; rfl
    · rw [Equiv.Perm.mul_apply, h0i]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.1) (Ne.symm hb.1)
    · rw [Equiv.Perm.mul_apply, h0j]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.2) (Ne.symm hb.2)

theorem exists_alt_one (hι : Fintype.card ι = 6) (i k : ι) :
    ∃ σ ∈ alternatingGroup ι, σ i = k := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) k
  obtain ⟨σ, hσ, hσi, -⟩ := exists_alt_two hι hj.symm hl.symm
  exact ⟨σ, hσ, hσi⟩

theorem exists_alt_three (hι : Fintype.card ι = 6) {i j k l : ι} (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∃ σ ∈ alternatingGroup ι, σ i = i ∧ σ j = j ∧ σ k = l := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne_notMem hι {i, j, k, l}
    Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
  refine ⟨Equiv.swap k l * Equiv.swap a b, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hkl,
      Equiv.Perm.sign_swap hab]
    rfl
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.1) (Ne.symm hb.1)]
    exact Equiv.swap_apply_of_ne_of_ne hik hil
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.2.1) (Ne.symm hb.2.1)]
    exact Equiv.swap_apply_of_ne_of_ne hjk hjl
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha.2.2.1) (Ne.symm hb.2.2.1)]
    exact Equiv.swap_apply_left _ _

end Perm

section LinearAlgebra

variable {L : Type*} [CommGroup L] [Finite L] [Module (ZMod 2) (Additive L)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → L)

noncomputable def ev : (ι → ZMod 2) →ₗ[ZMod 2] Additive L :=
  Fintype.linearCombination (ZMod 2) fun i => Additive.ofMul (d i)

def ind (S : Finset ι) : ι → ZMod 2 := fun i => if i ∈ S then 1 else 0

theorem zmod2_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide

theorem exists_ind (s : ι → ZMod 2) : ∃ S : Finset ι, s = ind S := by
  refine ⟨Finset.univ.filter fun i => s i = 1, funext fun i => ?_⟩
  by_cases h : s i = 1
  · simp [ind, h]
  · simp [ind, h, zmod2_eq_zero_of_ne_one _ h]

theorem ind_eq_zero_iff (S : Finset ι) : ind S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    have := congrFun h i
    simp [ind, hi] at this
  · rintro rfl
    funext i
    simp [ind]

theorem ind_eq_one_iff (S : Finset ι) : ind S = (fun _ => 1) ↔ S = Finset.univ := by
  constructor
  · intro h
    refine Finset.eq_univ_of_forall fun i => ?_
    have := congrFun h i
    by_contra hi
    simp [ind, hi] at this
  · rintro rfl
    funext i
    simp [ind]

theorem ev_single (i : ι) : ev d (Pi.single i 1) = Additive.ofMul (d i) := by
  simp [ev]

theorem ev_ind (S : Finset ι) : ev d (ind S) = Additive.ofMul (∏ i ∈ S, d i) := by
  simp only [ev, ind, Fintype.linearCombination_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_mem, Finset.univ_inter, ofMul_prod]

theorem ev_surjective (hgen : Subgroup.closure (Set.range d) = ⊤) :
    Function.Surjective (ev d) := by
  rw [← LinearMap.range_eq_top, ev, Fintype.range_linearCombination]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : Additive.toMul x ∈ Subgroup.closure (Set.range d) := by
    rw [hgen]; exact Subgroup.mem_top _
  have key : ∀ l ∈ Subgroup.closure (Set.range d), Additive.ofMul l ∈
      Submodule.span (ZMod 2) (Set.range fun i => Additive.ofMul (d i)) := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | one => exact Submodule.zero_mem _
    | mul y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | inv y _ hy => exact Submodule.neg_mem _ hy
  exact key _ hx

theorem exists_finset_prod (hgen : Subgroup.closure (Set.range d) = ⊤) (l : L) :
    ∃ S : Finset ι, l = ∏ i ∈ S, d i := by
  obtain ⟨s, hs⟩ := ev_surjective d hgen (Additive.ofMul l)
  obtain ⟨S, rfl⟩ := exists_ind s
  rw [ev_ind] at hs
  exact ⟨S, (congrArg Additive.toMul hs).symm⟩

theorem finrank_additive (hcard : Nat.card L = 2 ^ 5) :
    Module.finrank (ZMod 2) (Additive L) = 5 := by
  have hF : Module.Finite (ZMod 2) (Additive L) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive L)
  rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive L ≃ L), hcard] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem finrank_ker_ev (hι : Fintype.card ι = 6) (hcard : Nat.card L = 2 ^ 5)
    (hgen : Subgroup.closure (Set.range d) = ⊤) :
    Module.finrank (ZMod 2) (LinearMap.ker (ev d)) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (ev d)
  rw [LinearMap.range_eq_top.2 (ev_surjective d hgen), finrank_top, finrank_additive hcard,
    Module.finrank_fintype_fun_eq_card, hι] at h
  omega

theorem ev_comp_perm (φ : L ≃* L) (σ : Equiv.Perm ι) (hφ : ∀ i, φ (d i) = d (σ i))
    (s : ι → ZMod 2) :
    ev d (s ∘ σ.symm) = Additive.ofMul (φ (Additive.toMul (ev d s))) := by
  have h1 : ev d (s ∘ σ.symm) = ∑ j, s j • Additive.ofMul (d (σ j)) := by
    simp only [ev, Fintype.linearCombination_apply, Function.comp_apply]
    rw [← Equiv.sum_comp σ]
    simp
  let φA : Additive L →+ Additive L := MonoidHom.toAdditive (φ : L →* L)
  have h2 : Additive.ofMul (φ (Additive.toMul (ev d s))) = φA (ev d s) := rfl
  rw [h1, h2]
  simp only [ev, Fintype.linearCombination_apply, map_sum, ZMod.map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hφ j]
  rfl

theorem ker_ev_eq (hι : Fintype.card ι = 6) (hcard : Nat.card L = 2 ^ 5)
    (hgen : Subgroup.closure (Set.range d) = ⊤)
    (hinv : ∀ σ ∈ alternatingGroup ι, ∀ s, ev d s = 0 → ev d (s ∘ σ.symm) = 0)
    (s : ι → ZMod 2) : ev d s = 0 ↔ s = 0 ∨ s = fun _ => 1 := by
  have hfin := finrank_ker_ev d hι hcard hgen
  obtain ⟨⟨r, hr⟩, hr0, hrall⟩ := finrank_eq_one_iff'.1 hfin
  have hker : ∀ w, ev d w = 0 → w = 0 ∨ w = r := by
    intro w hw
    obtain ⟨c, hc⟩ := hrall ⟨w, hw⟩
    have hc' : c • r = w := congrArg Subtype.val hc
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · left; rw [← hc', zero_smul]
    · right; rw [← hc', one_smul]
  have hr0' : r ≠ 0 := fun h => hr0 (Subtype.ext h)
  have hrinv : ∀ σ ∈ alternatingGroup ι, r ∘ σ.symm = r := by
    intro σ hσ
    rcases hker _ (hinv σ hσ r hr) with h | h
    · exfalso
      apply hr0'
      funext i
      have := congrFun h (σ i)
      simpa using this
    · exact h
  have hconst : ∀ i k, r k = r i := by
    intro i k
    obtain ⟨σ, hσ, hσi⟩ := exists_alt_one hι i k
    have := congrFun (hrinv σ hσ) k
    rw [Function.comp_apply, ← hσi, Equiv.symm_apply_apply, hσi] at this
    exact this.symm
  have hr1 : r = fun _ => 1 := by
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hi₀ : r i₀ = 1 := by
      by_contra hne
      apply hr0'
      funext k
      rw [hconst i₀ k, zmod2_eq_zero_of_ne_one _ hne]
      rfl
    funext k
    rw [hconst i₀ k, hi₀]
  constructor
  · intro h
    rcases hker s h with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hr1)
  · rintro (rfl | rfl)
    · exact map_zero _
    · rw [← hr1]; exact hr

theorem prod_eq_one_iff (hι : Fintype.card ι = 6) (hcard : Nat.card L = 2 ^ 5)
    (hgen : Subgroup.closure (Set.range d) = ⊤)
    (hinv : ∀ σ ∈ alternatingGroup ι, ∀ s, ev d s = 0 → ev d (s ∘ σ.symm) = 0)
    (S : Finset ι) : ∏ i ∈ S, d i = 1 ↔ S = ∅ ∨ S = Finset.univ := by
  have h := ker_ev_eq d hι hcard hgen hinv (ind S)
  rw [ev_ind, ofMul_eq_zero, ind_eq_zero_iff, ind_eq_one_iff] at h
  exact h

theorem exists_functional (hsurj : Function.Surjective (ev d))
    (hker : ∀ s, ev d s = 0 → ∑ i, s i = 0) :
    ∃ f : L →* Multiplicative (ZMod 2),
      ∀ s, f (Additive.toMul (ev d s)) = Multiplicative.ofAdd (∑ i, s i) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (ev d)
    (LinearMap.range_eq_top.2 hsurj)
  let ε : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun s => ∑ i, s i
      map_add' := fun s t => by simp [Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.mul_sum] }
  let f₀ : Additive L →ₗ[ZMod 2] ZMod 2 := ε ∘ₗ g
  have key : ∀ s, f₀ (ev d s) = ∑ i, s i := by
    intro s
    have h1 : ev d (g (ev d s) - s) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact LinearMap.congr_fun hg (ev d s)
    have h2 := hker _ h1
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sub_eq_zero] at h2
    exact h2
  refine ⟨{ toFun := fun l => Multiplicative.ofAdd (f₀ (Additive.ofMul l))
            map_one' := by simp
            map_mul' := fun x y => by simp [ofAdd_add] }, ?_⟩
  intro s
  simp [key]

end LinearAlgebra

section Combinatorics

variable {L : Type*} [CommGroup L] {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → L}
  {Γ : Set (L ≃* L)} {f : L →* Multiplicative (ZMod 2)}

theorem ofAdd_one_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide

theorem ofAdd_one_mul_ofAdd_one :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide

theorem ofAdd_one_mul_ofAdd_one_mul_ofAdd_one :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 =
      Multiplicative.ofAdd 1 := by decide

theorem eq_of_ne_one_of_ne_one :
    ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide

theorem exists_card_le_three (hι : Fintype.card ι = 6) (hsq : ∀ a : L, a * a = 1)
    (hsurj : ∀ l : L, ∃ S : Finset ι, l = ∏ i ∈ S, d i) (hprod : ∏ i, d i = 1) (l : L) :
    ∃ S : Finset ι, S.card ≤ 3 ∧ l = ∏ i ∈ S, d i := by
  obtain ⟨S, rfl⟩ := hsurj l
  by_cases hS : S.card ≤ 3
  · exact ⟨S, hS, rfl⟩
  · refine ⟨Sᶜ, ?_, ?_⟩
    · rw [Finset.card_compl, hι]; omega
    · have h := Finset.prod_mul_prod_compl S d
      rw [hprod] at h
      exact (mul_left_cancel (h.trans (hsq _).symm)).symm

theorem classify (hι : Fintype.card ι = 6) (hsq : ∀ a : L, a * a = 1)
    (hsurj : ∀ l : L, ∃ S : Finset ι, l = ∏ i ∈ S, d i) (hprod : ∏ i, d i = 1) (l : L) :
    l = 1 ∨ (∃ i, l = d i) ∨ (∃ i j, i ≠ j ∧ l = d i * d j) ∨
      ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ l = d i * d j * d k := by
  obtain ⟨S, hS, rfl⟩ := exists_card_le_three hι hsq hsurj hprod l
  have : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases this with h | h | h | h
  · left
    rw [Finset.card_eq_zero.1 h]
    simp
  · right; left
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h
    exact ⟨i, by simp⟩
  · right; right; left
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 h
    exact ⟨i, j, hij, Finset.prod_pair hij⟩
  · right; right; right
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.1 h
    refine ⟨i, j, k, hij, hik, hjk, ?_⟩
    rw [Finset.prod_insert (by simp [hij, hik]), Finset.prod_pair hjk, mul_assoc]

structure Setup (d : ι → L) (Γ : Set (L ≃* L)) (f : L →* Multiplicative (ZMod 2)) : Prop where
  card_eq : Fintype.card ι = 6
  sq : ∀ a : L, a * a = 1
  gen : Subgroup.closure (Set.range d) = ⊤
  surj : ∀ l : L, ∃ S : Finset ι, l = ∏ i ∈ S, d i
  prod_univ : ∏ i, d i = 1
  f_d : ∀ i, f (d i) = Multiplicative.ofAdd 1
  perm : ∀ φ ∈ Γ, ∃ σ : Equiv.Perm ι, ∀ i, φ (d i) = d (σ i)
  alt : ∀ σ ∈ alternatingGroup ι, ∃ φ ∈ Γ, ∀ i, φ (d i) = d (σ i)

namespace Setup

variable (h : Setup d Γ f)
include h

theorem f_pair (i j : ι) : f (d i * d j) = 1 := by
  rw [map_mul, h.f_d, h.f_d, ofAdd_one_mul_ofAdd_one]

theorem f_triple (i j k : ι) : f (d i * d j * d k) = Multiplicative.ofAdd 1 := by
  rw [map_mul, map_mul, h.f_d, h.f_d, h.f_d, ofAdd_one_mul_ofAdd_one_mul_ofAdd_one]

theorem f_comp (φ : L ≃* L) (hφ : φ ∈ Γ) (l : L) : f (φ l) = f l := by
  obtain ⟨σ, hσ⟩ := h.perm φ hφ
  have : f.comp (φ : L →* L) = f := by
    refine MonoidHom.eq_of_eqOn_dense h.gen ?_
    rintro _ ⟨i, rfl⟩
    simp [hσ, h.f_d]
  exact DFunLike.congr_fun this l

theorem ker_classify (z : L) (hz : z ∈ f.ker) (hz1 : z ≠ 1) : ∃ i j, i ≠ j ∧ z = d i * d j := by
  rw [MonoidHom.mem_ker] at hz
  rcases classify h.card_eq h.sq h.surj h.prod_univ z with
    rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, k, -, -, -, rfl⟩
  · exact absurd rfl hz1
  · rw [h.f_d] at hz
    exact absurd hz ofAdd_one_ne_one
  · exact ⟨i, j, hij, rfl⟩
  · rw [h.f_triple] at hz
    exact absurd hz ofAdd_one_ne_one

theorem ker_eq_closure : f.ker = Subgroup.closure {z | ∃ i j, z = d i * d j} := by
  apply le_antisymm
  · intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem _
    · obtain ⟨i, j, -, rfl⟩ := h.ker_classify z hz hz1
      exact Subgroup.subset_closure ⟨i, j, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, rfl⟩
    exact h.f_pair i j

theorem index_ker : f.ker.index = 2 := by
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by rw [h.card_eq]; omega)
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hy : y = 1
    · exact ⟨1, by rw [hy, map_one]⟩
    · exact ⟨d i₀, by rw [h.f_d]; exact eq_of_ne_one_of_ne_one _ _ ofAdd_one_ne_one hy⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exists_aut_ker (a : L) (ha : a ∈ f.ker) (ha1 : a ≠ 1) (b : L) (hb : b ∈ f.ker)
    (hb1 : b ≠ 1) : ∃ φ ∈ Γ, φ a = b := by
  obtain ⟨i, j, hij, rfl⟩ := h.ker_classify a ha ha1
  obtain ⟨k, l, hkl, rfl⟩ := h.ker_classify b hb hb1
  obtain ⟨σ, hσ, hσi, hσj⟩ := exists_alt_two h.card_eq hij hkl
  obtain ⟨φ, hφ, hφd⟩ := h.alt σ hσ
  exact ⟨φ, hφ, by rw [map_mul, hφd, hφd, hσi, hσj]⟩

theorem eq_ker_of_invariant (M : Subgroup L) (hM : ∀ φ ∈ Γ, ∀ m ∈ M, φ m ∈ M) (hbot : M ≠ ⊥)
    (htop : M ≠ ⊤) : M = f.ker := by
  have hd_mem : ∀ i k, d i ∈ M → d k ∈ M := by
    intro i k hi
    obtain ⟨σ, hσ, hσi⟩ := exists_alt_one h.card_eq i k
    obtain ⟨φ, hφ, hφd⟩ := h.alt σ hσ
    have := hM φ hφ _ hi
    rwa [hφd, hσi] at this
  have hpair : ∀ i j k l, i ≠ j → k ≠ l → d i * d j ∈ M → d k * d l ∈ M := by
    intro i j k l hij hkl hm
    obtain ⟨σ, hσ, hσi, hσj⟩ := exists_alt_two h.card_eq hij hkl
    obtain ⟨φ, hφ, hφd⟩ := h.alt σ hσ
    have := hM φ hφ _ hm
    rwa [map_mul, hφd, hφd, hσi, hσj] at this
  have hker : ∀ i j, i ≠ j → d i * d j ∈ M → f.ker ≤ M := by
    intro i j hij hm z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact M.one_mem
    · obtain ⟨k, l, hkl, rfl⟩ := h.ker_classify z hz hz1
      exact hpair i j k l hij hkl hm
  have hKM : f.ker ≤ M := by
    obtain ⟨m, hm, hm1⟩ : ∃ m ∈ M, m ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hbot ((Subgroup.eq_bot_iff_forall M).2 hcon)
    rcases classify h.card_eq h.sq h.surj h.prod_univ m with
      rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, k, hij, hik, hjk, rfl⟩
    · exact absurd rfl hm1
    · exfalso
      apply htop
      rw [eq_top_iff, ← h.gen, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact hd_mem i k hm
    · exact hker i j hij hm
    · obtain ⟨l, hl⟩ : ∃ l, l ∉ ({i, j, k} : Finset ι) := by
        by_contra hcon
        push Not at hcon
        have hc := Finset.card_le_three (a := i) (b := j) (c := k)
        rw [Finset.eq_univ_of_forall hcon, Finset.card_univ, h.card_eq] at hc
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨σ, hσ, hσi, hσj, hσk⟩ := exists_alt_three h.card_eq hik (Ne.symm hl.1) hjk
        (Ne.symm hl.2.1) (Ne.symm hl.2.2)
      obtain ⟨φ, hφ, hφd⟩ := h.alt σ hσ
      have h2 := M.mul_mem hm (hM φ hφ _ hm)
      have h3 : d i * d j * d k * φ (d i * d j * d k) = d k * d l := by
        rw [map_mul, map_mul, hφd, hφd, hφd, hσi, hσj, hσk]
        calc _ = (d i * d i) * (d j * d j) * (d k * d l) := by ac_rfl
          _ = d k * d l := by rw [h.sq, h.sq, one_mul, one_mul]
      rw [h3] at h2
      exact hker k l (Ne.symm hl.2.2) h2
  refine le_antisymm (fun m hm => ?_) hKM
  by_contra hmK
  apply htop
  rw [eq_top_iff]
  intro x _
  by_cases hx : f x = 1
  · exact hKM hx
  · have hxm : x * m⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, eq_of_ne_one_of_ne_one _ _ hx hmK, mul_inv_cancel]
    simpa using M.mul_mem (hKM hxm) hm

end Setup

theorem list_prod_eq_one_iff (hι : Fintype.card ι = 6)
    (hker : ∀ S : Finset ι, ∏ i ∈ S, d i = 1 ↔ S = ∅ ∨ S = Finset.univ)
    (l : List ι) (hl : l.Nodup) : (l.map d).prod = 1 ↔ l = [] ∨ l.length = 6 := by
  rw [← List.prod_toFinset d hl, hker]
  have hc : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl
  constructor
  · rintro (h | h)
    · left
      simpa using h
    · right
      rw [← hc, h, Finset.card_univ, hι]
  · rintro (h | h)
    · left
      simp [h]
    · right
      apply Finset.eq_univ_of_card
      rw [hc, h, hι]

end Combinatorics

theorem sixGenerators_comm {L : Type*} [CommGroup L] [Finite L] (hsq : ∀ a : L, a * a = 1)
    (hcard : Nat.card L = 2 ^ 5) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 6) (d : ι → L) (hgen : Subgroup.closure (Set.range d) = ⊤)
    (Γ : Set (L ≃* L)) (hΓ : ∀ φ ∈ Γ, ∃ σ : Equiv.Perm ι, ∀ i, φ (d i) = d (σ i))
    (hΓalt : ∀ σ ∈ alternatingGroup ι, ∃ φ ∈ Γ, ∀ i, φ (d i) = d (σ i)) :
    (∀ l : List ι, l.Nodup → ((l.map d).prod = 1 ↔ l = [] ∨ l.length = 6)) ∧
    ∃ f : L →* Multiplicative (ZMod 2),
      (∀ i, f (d i) = Multiplicative.ofAdd 1) ∧
      (∀ φ ∈ Γ, ∀ l, f (φ l) = f l) ∧
      f.ker = Subgroup.closure {z | ∃ i j, z = d i * d j} ∧
      f.ker.index = 2 ∧
      (∀ z ∈ f.ker, z ≠ 1 → ∃ i j, i ≠ j ∧ z = d i * d j) ∧
      (∀ a ∈ f.ker, a ≠ 1 → ∀ b ∈ f.ker, b ≠ 1 → ∃ φ ∈ Γ, φ a = b) ∧
      (∀ M : Subgroup L, (∀ φ ∈ Γ, ∀ m ∈ M, φ m ∈ M) → M ≠ ⊥ → M ≠ ⊤ → M = f.ker) := by
  letI : Module (ZMod 2) (Additive L) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x)
  have hinv : ∀ σ ∈ alternatingGroup ι, ∀ s, ev d s = 0 → ev d (s ∘ σ.symm) = 0 := by
    intro σ hσ s hs
    obtain ⟨φ, -, hφ⟩ := hΓalt σ hσ
    rw [ev_comp_perm d φ σ hφ s, hs]
    exact map_one φ
  have hkerS := prod_eq_one_iff d hι hcard hgen hinv
  have hprod : ∏ i, d i = 1 := (hkerS Finset.univ).2 (Or.inr rfl)
  have hker : ∀ s, ev d s = 0 → ∑ i, s i = 0 := by
    intro s hs
    rcases (ker_ev_eq d hι hcard hgen hinv s).1 hs with rfl | rfl
    · simp
    · simp only [Finset.sum_const, Finset.card_univ, hι]
      decide
  obtain ⟨f, hf⟩ := exists_functional d (ev_surjective d hgen) hker
  have hfd : ∀ i, f (d i) = Multiplicative.ofAdd 1 := by
    intro i
    have h := hf (Pi.single i 1)
    rw [ev_single, toMul_ofMul] at h
    rw [h]
    simp
  have hS : Setup d Γ f := ⟨hι, hsq, hgen, exists_finset_prod d hgen, hprod, hfd, hΓ, hΓalt⟩
  exact ⟨list_prod_eq_one_iff hι hkerS, f, hfd, fun φ hφ l => hS.f_comp φ hφ l,
    hS.ker_eq_closure, hS.index_ker, hS.ker_classify, hS.exists_aut_ker,
    fun M hM hbot htop => hS.eq_ker_of_invariant M hM hbot htop⟩

end SixGen

theorem sixGenerators {L : Type*} [Group L] [Finite L]
    (hcomm : ∀ a b : L, a * b = b * a) (hsq : ∀ a : L, a * a = 1)
    (hcard : Nat.card L = 2 ^ 5)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 6)
    (d : ι → L) (hgen : Subgroup.closure (Set.range d) = ⊤) (Γ : Set (L ≃* L))
    (hΓ : ∀ φ ∈ Γ, ∃ σ : Equiv.Perm ι, ∀ i, φ (d i) = d (σ i))
    (hΓalt : ∀ σ ∈ alternatingGroup ι, ∃ φ ∈ Γ, ∀ i, φ (d i) = d (σ i)) :
    (∀ l : List ι, l.Nodup → ((l.map d).prod = 1 ↔ l = [] ∨ l.length = 6)) ∧
    ∃ f : L →* Multiplicative (ZMod 2),
      (∀ i, f (d i) = Multiplicative.ofAdd 1) ∧
      (∀ φ ∈ Γ, ∀ l, f (φ l) = f l) ∧
      f.ker = Subgroup.closure {z | ∃ i j, z = d i * d j} ∧
      f.ker.index = 2 ∧
      (∀ z ∈ f.ker, z ≠ 1 → ∃ i j, i ≠ j ∧ z = d i * d j) ∧
      (∀ a ∈ f.ker, a ≠ 1 → ∀ b ∈ f.ker, b ≠ 1 → ∃ φ ∈ Γ, φ a = b) ∧
      (∀ M : Subgroup L, (∀ φ ∈ Γ, ∀ m ∈ M, φ m ∈ M) → M ≠ ⊥ → M ≠ ⊤ → M = f.ker) := by
  letI : CommGroup L := { (inferInstance : Group L) with mul_comm := hcomm }
  exact SixGen.sixGenerators_comm hsq hcard hι d hgen Γ hΓ hΓalt

end CFSG.GF2Type.Smith1979.Case25
