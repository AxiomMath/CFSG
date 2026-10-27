module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSpMultJ3
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverON
public import CFSG.Sporadic.ONOddCore.Involutions
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON
public import Certificates.Certificate22225
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator

public section

namespace CFSG.ComponentClassification.GSThmB.SpMult

open CFSG Subgroup CFSG.CosetTable TauCeti CFSG.ONSchreier
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover

theorem lift_update_mul_central {m : ℕ} {E : Type*} [Group E] (f : Fin m → E) (j : Fin m)
    {v : E} (hv : v ∈ center E) (hv2 : v * v = 1) (w : List (Fin m × Bool)) :
    FreeGroup.lift (Function.update f j (f j * v)) (FreeGroup.mk w) =
      FreeGroup.lift f (FreeGroup.mk w) * v ^ (w.countP fun x => x.1 = j) := by
  have hvc := mem_center_iff.mp hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  induction w with
  | nil => rw [← FreeGroup.one_eq_mk, map_one, map_one, List.countP_nil, pow_zero, one_mul]
  | cons x w ih =>
    obtain ⟨i, b⟩ := x
    rw [List.countP_cons, show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w
      from (FreeGroup.mul_mk (L₁ := [(i, b)]) (L₂ := w)).symm, map_mul, map_mul, ih]
    set L := FreeGroup.lift f (FreeGroup.mk w)
    set n := w.countP fun x => x.1 = j
    have hsingle : ∀ (g : Fin m → E), FreeGroup.lift g (FreeGroup.mk [(i, b)]) =
        if b then g i else (g i)⁻¹ := fun g => by
      cases b
      · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        rfl
      · rw [lift_mk_single]
        rfl
    rw [hsingle, hsingle]
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, decide_true, ite_true, pow_succ]
      cases b
      · simp only [Bool.false_eq_true, ite_false, mul_inv_rev, hvi]
        calc v * (f i)⁻¹ * (L * v ^ n) = (f i)⁻¹ * (v * (L * v ^ n)) := by
              rw [← hvc ((f i)⁻¹), mul_assoc]
          _ = (f i)⁻¹ * (L * v ^ n * v) := by rw [← hvc (L * v ^ n)]
          _ = (f i)⁻¹ * L * (v ^ n * v) := by simp only [mul_assoc]
      · simp only [ite_true]
        calc f i * v * (L * v ^ n) = f i * (v * (L * v ^ n)) := by rw [mul_assoc]
          _ = f i * (L * v ^ n * v) := by rw [← hvc (L * v ^ n)]
          _ = f i * L * (v ^ n * v) := by simp only [mul_assoc]
    · simp only [Function.update_of_ne hij, hij, decide_false, Bool.false_eq_true, ite_false,
        add_zero, mul_assoc]

theorem pow_eq_pow_mod_two {E : Type*} [Monoid E] {v : E} (hv2 : v * v = 1) (n : ℕ) :
    v ^ n = v ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, sq, hv2, one_pow, one_mul]

theorem lift_update_even {m : ℕ} {E : Type*} [Group E] (f : Fin m → E) (j : Fin m) {v : E}
    (hv : v ∈ center E) (hv2 : v * v = 1) {w : List (Fin m × Bool)}
    (hw : (w.countP fun x => x.1 = j) % 2 = 0) :
    FreeGroup.lift (Function.update f j (f j * v)) (FreeGroup.mk w) =
      FreeGroup.lift f (FreeGroup.mk w) := by
  rw [lift_update_mul_central f j hv hv2, pow_eq_pow_mod_two hv2, hw, pow_zero, mul_one]

theorem lift_update_odd {m : ℕ} {E : Type*} [Group E] (f : Fin m → E) (j : Fin m) {v : E}
    (hv : v ∈ center E) (hv2 : v * v = 1) {w : List (Fin m × Bool)}
    (hw : (w.countP fun x => x.1 = j) % 2 = 1)
    (hval : FreeGroup.lift f (FreeGroup.mk w) = v) :
    FreeGroup.lift (Function.update f j (f j * v)) (FreeGroup.mk w) = 1 := by
  rw [lift_update_mul_central f j hv hv2, pow_eq_pow_mod_two hv2, hw, pow_one, hval, hv2]

theorem on_mul_self_eq_one
    {E : Type*} [Group E] {ρ : E →* Blueprint.NativeSporadic.ON} (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) (hexp : ∀ v ∈ ρ.ker, v * v = 1) {w : E}
    (hw : ρ w * ρ w = 1) : w * w = 1 := by
  obtain ⟨a₁, a₂, a₃, n, hd⟩ := on_e8Datum
  obtain ⟨b₁, -, -, hb₁, -, -, hb₁2, -⟩ := hd.exists_lift hρ hker
  refine mul_self_eq_one_of_lift hρ hker hexp hb₁ (by rw [← sq]; exact hb₁2) ?_ hw
  intro t ht
  set φ := onEquivPv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf ((φ t : ↥Pv) : Equiv.Perm (Fin N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have h2 : orderOf ((φ a₁ : ↥Pv) : Equiv.Perm (Fin N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hd.sq hd.ne_one
  obtain ⟨g₁, hg₁, e₁⟩ := Sporadic.ONOddCore.cti_on_all_involutions_conjugate _ (φ t).2 h1
  obtain ⟨g₂, hg₂, e₂⟩ := Sporadic.ONOddCore.cti_on_all_involutions_conjugate _ (φ a₁).2 h2
  refine ⟨φ.symm ⟨g₁ * g₂⁻¹, mul_mem hg₁ (inv_mem hg₂)⟩, φ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e₁, e₂]
  group

theorem onGens_eq : onGens = 7 := by decide

private theorem onRels_length : onRels.length = 29 := by decide

theorem onRels_mem {i : ℕ} (hi : i < 29) : onRels.getD i [] ∈ onRels := by
  rw [List.getD_eq_getElem _ _ (by rw [onRels_length]; exact hi)]
  exact List.getElem_mem _

@[expose] def onSqIdx : List ℕ := [0, 1, 2, 3, 4, 5, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

theorem onRels_squares : ∀ i ∈ onSqIdx, onRels.getD i [] =
    (onRels.getD i []).take ((onRels.getD i []).length / 2) ++
      (onRels.getD i []).take ((onRels.getD i []).length / 2) := by
  decide

@[expose] def onGen (k : ℕ) (hk : k < 7) : Fin onGens := ⟨k, by rw [onGens_eq]; exact hk⟩

theorem onRels_counts :
    let cnt := fun (i k : ℕ) (hk : k < 7) =>
      ((onRels.getD i []).countP fun x => x.1 = onGen k hk) % 2
    (cnt 27 1 (by norm_num) = 1 ∧ cnt 27 0 (by norm_num) = 0 ∧ cnt 27 2 (by norm_num) = 0 ∧
      cnt 27 5 (by norm_num) = 0 ∧ cnt 27 4 (by norm_num) = 0 ∧ cnt 27 3 (by norm_num) = 0 ∧
      cnt 27 6 (by norm_num) = 0) ∧
    (cnt 6 0 (by norm_num) = 1 ∧ cnt 6 2 (by norm_num) = 0 ∧ cnt 6 5 (by norm_num) = 0 ∧
      cnt 6 4 (by norm_num) = 0 ∧ cnt 6 3 (by norm_num) = 0 ∧ cnt 6 6 (by norm_num) = 0) ∧
    (cnt 7 2 (by norm_num) = 1 ∧ cnt 7 5 (by norm_num) = 0 ∧ cnt 7 4 (by norm_num) = 0 ∧
      cnt 7 3 (by norm_num) = 0 ∧ cnt 7 6 (by norm_num) = 0) ∧
    (cnt 23 5 (by norm_num) = 1 ∧ cnt 23 4 (by norm_num) = 0 ∧ cnt 23 3 (by norm_num) = 0 ∧
      cnt 23 6 (by norm_num) = 0) ∧
    (cnt 10 4 (by norm_num) = 1 ∧ cnt 10 3 (by norm_num) = 0 ∧ cnt 10 6 (by norm_num) = 0) ∧
    (cnt 9 3 (by norm_num) = 1 ∧ cnt 9 6 (by norm_num) = 0) ∧
    cnt 26 6 (by norm_num) = 1 := by
  decide

theorem restrict_onCoverRels :
    restrictWords (subsetOf onGens [0, 1, 2, 3, 4, 5]) onCoverRels =
      Sporadic.Presentation.ONan.R1 := by
  decide

theorem on_card_le
    (E : Type) [Group E] [Finite E] (ρ : E →* Blueprint.NativeSporadic.ON)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E) (hexp : ∀ v ∈ ρ.ker, v * v = 1)
    (hperf : Group.IsPerfect E) : Nat.card E ≤ Nat.card Blueprint.NativeSporadic.ON := by
  obtain ⟨β⟩ := Sporadic.Bridge.ON.nonempty_mulEquiv
  set g : Fin onGens → Blueprint.NativeSporadic.ON := fun i => β.symm (PresentedGroup.of i)
    with hg
  have hlift : ∀ w : FreeGroup (Fin onGens),
      FreeGroup.lift g w = β.symm (PresentedGroup.mk _ w) := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => rw [map_one, map_one, map_one]
    | of i => rw [FreeGroup.lift_apply_of]; rfl
    | inv_of i ih => rw [map_inv, ih, map_inv, map_inv]
    | mul x y hx hy => rw [map_mul, hx, hy, map_mul, map_mul]
  have hgrel : ∀ r ∈ onRels, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
    intro r hr
    have hmem : FreeGroup.mk r ∈ SporadicName.ONan.presentation.relatorSet := by
      rw [Sporadic.Presentation.relatorSet_eq]
      exact List.mem_map_of_mem hr
    rw [hlift, PresentedGroup.one_of_mem hmem, map_one]
  have hgen : Subgroup.closure (Set.range g) = ⊤ := by
    rw [← FreeGroup.range_lift_eq_closure, MonoidHom.range_eq_top]
    intro t
    obtain ⟨p, rfl⟩ := β.symm.surjective t
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ p
    exact ⟨w, hlift w⟩
  have hsq : ∀ w : E, ρ w * ρ w = 1 → w * w = 1 := fun w hw =>
    on_mul_self_eq_one hρ hker hexp hw
  have hcomp : ∀ f : Fin onGens → E, (∀ i, ρ (f i) = g i) →
      ρ.comp (FreeGroup.lift f) = FreeGroup.lift g := fun f hf =>
    FreeGroup.ext_hom _ _ fun i => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hf]
  have hval : ∀ f : Fin onGens → E, (∀ i, ρ (f i) = g i) → ∀ r ∈ onRels,
      FreeGroup.lift f (FreeGroup.mk r) ∈ ρ.ker := fun f hf r hr => by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp f hf, hgrel r hr]
  have hupd : ∀ f : Fin onGens → E, (∀ i, ρ (f i) = g i) → ∀ (j : Fin onGens) (v : E),
      v ∈ ρ.ker → ∀ i, ρ (Function.update f j (f j * v) i) = g i := by
    intro f hf j v hv i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, map_mul, hv, mul_one, hf]
    · rw [Function.update_of_ne hij, hf]
  choose f₀ hf₀ using fun i => hρ (g i)
  have hrK : ∀ (f : Fin onGens → E), (∀ i, ρ (f i) = g i) → ∀ {i : ℕ}, i < 29 →
      FreeGroup.lift f (FreeGroup.mk (onRels.getD i [])) ∈ ρ.ker := fun f hf i hi =>
    hval f hf _ (onRels_mem hi)
  obtain ⟨⟨h27b, h27a, h27c, h27f, h27e, h27d, h27g⟩, ⟨h6a, h6c, h6f, h6e, h6d, h6g⟩,
    ⟨h7c, h7f, h7e, h7d, h7g⟩, ⟨h23f, h23e, h23d, h23g⟩, ⟨h10e, h10d, h10g⟩, ⟨h9d, h9g⟩, h26g⟩ :=
    onRels_counts
  set v₁ := FreeGroup.lift f₀ (FreeGroup.mk (onRels.getD 27 [])) with hv₁
  have hv₁K : v₁ ∈ ρ.ker := hrK f₀ hf₀ (by norm_num)
  set f₁ := Function.update f₀ (onGen 1 (by norm_num)) (f₀ (onGen 1 (by norm_num)) * v₁)
  have hf₁ : ∀ i, ρ (f₁ i) = g i := hupd f₀ hf₀ _ _ hv₁K
  set v₂ := FreeGroup.lift f₁ (FreeGroup.mk (onRels.getD 6 [])) with hv₂
  have hv₂K : v₂ ∈ ρ.ker := hrK f₁ hf₁ (by norm_num)
  set f₂ := Function.update f₁ (onGen 0 (by norm_num)) (f₁ (onGen 0 (by norm_num)) * v₂)
  have hf₂ : ∀ i, ρ (f₂ i) = g i := hupd f₁ hf₁ _ _ hv₂K
  set v₃ := FreeGroup.lift f₂ (FreeGroup.mk (onRels.getD 7 [])) with hv₃
  have hv₃K : v₃ ∈ ρ.ker := hrK f₂ hf₂ (by norm_num)
  set f₃ := Function.update f₂ (onGen 2 (by norm_num)) (f₂ (onGen 2 (by norm_num)) * v₃)
  have hf₃ : ∀ i, ρ (f₃ i) = g i := hupd f₂ hf₂ _ _ hv₃K
  set v₄ := FreeGroup.lift f₃ (FreeGroup.mk (onRels.getD 23 [])) with hv₄
  have hv₄K : v₄ ∈ ρ.ker := hrK f₃ hf₃ (by norm_num)
  set f₄ := Function.update f₃ (onGen 5 (by norm_num)) (f₃ (onGen 5 (by norm_num)) * v₄)
  have hf₄ : ∀ i, ρ (f₄ i) = g i := hupd f₃ hf₃ _ _ hv₄K
  set v₅ := FreeGroup.lift f₄ (FreeGroup.mk (onRels.getD 10 [])) with hv₅
  have hv₅K : v₅ ∈ ρ.ker := hrK f₄ hf₄ (by norm_num)
  set f₅ := Function.update f₄ (onGen 4 (by norm_num)) (f₄ (onGen 4 (by norm_num)) * v₅)
  have hf₅ : ∀ i, ρ (f₅ i) = g i := hupd f₄ hf₄ _ _ hv₅K
  set v₆ := FreeGroup.lift f₅ (FreeGroup.mk (onRels.getD 9 [])) with hv₆
  have hv₆K : v₆ ∈ ρ.ker := hrK f₅ hf₅ (by norm_num)
  set f₆ := Function.update f₅ (onGen 3 (by norm_num)) (f₅ (onGen 3 (by norm_num)) * v₆)
  have hf₆ : ∀ i, ρ (f₆ i) = g i := hupd f₅ hf₅ _ _ hv₆K
  set v₇ := FreeGroup.lift f₆ (FreeGroup.mk (onRels.getD 26 [])) with hv₇
  have hv₇K : v₇ ∈ ρ.ker := hrK f₆ hf₆ (by norm_num)
  set f₇ := Function.update f₆ (onGen 6 (by norm_num)) (f₆ (onGen 6 (by norm_num)) * v₇)
  have hf₇ : ∀ i, ρ (f₇ i) = g i := hupd f₆ hf₆ _ _ hv₇K
  have hc : ∀ v ∈ ρ.ker, v ∈ center E := fun v hv => hker hv
  have e27 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 27 [])) = 1 := by
    rw [lift_update_even _ _ (hc _ hv₇K) (hexp _ hv₇K) h27g,
      lift_update_even _ _ (hc _ hv₆K) (hexp _ hv₆K) h27d,
      lift_update_even _ _ (hc _ hv₅K) (hexp _ hv₅K) h27e,
      lift_update_even _ _ (hc _ hv₄K) (hexp _ hv₄K) h27f,
      lift_update_even _ _ (hc _ hv₃K) (hexp _ hv₃K) h27c,
      lift_update_even _ _ (hc _ hv₂K) (hexp _ hv₂K) h27a]
    exact lift_update_odd _ _ (hc _ hv₁K) (hexp _ hv₁K) h27b rfl
  have e6 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 6 [])) = 1 := by
    rw [lift_update_even _ _ (hc _ hv₇K) (hexp _ hv₇K) h6g,
      lift_update_even _ _ (hc _ hv₆K) (hexp _ hv₆K) h6d,
      lift_update_even _ _ (hc _ hv₅K) (hexp _ hv₅K) h6e,
      lift_update_even _ _ (hc _ hv₄K) (hexp _ hv₄K) h6f,
      lift_update_even _ _ (hc _ hv₃K) (hexp _ hv₃K) h6c]
    exact lift_update_odd _ _ (hc _ hv₂K) (hexp _ hv₂K) h6a rfl
  have e7 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 7 [])) = 1 := by
    rw [lift_update_even _ _ (hc _ hv₇K) (hexp _ hv₇K) h7g,
      lift_update_even _ _ (hc _ hv₆K) (hexp _ hv₆K) h7d,
      lift_update_even _ _ (hc _ hv₅K) (hexp _ hv₅K) h7e,
      lift_update_even _ _ (hc _ hv₄K) (hexp _ hv₄K) h7f]
    exact lift_update_odd _ _ (hc _ hv₃K) (hexp _ hv₃K) h7c rfl
  have e23 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 23 [])) = 1 := by
    rw [lift_update_even _ _ (hc _ hv₇K) (hexp _ hv₇K) h23g,
      lift_update_even _ _ (hc _ hv₆K) (hexp _ hv₆K) h23d,
      lift_update_even _ _ (hc _ hv₅K) (hexp _ hv₅K) h23e]
    exact lift_update_odd _ _ (hc _ hv₄K) (hexp _ hv₄K) h23f rfl
  have e10 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 10 [])) = 1 := by
    rw [lift_update_even _ _ (hc _ hv₇K) (hexp _ hv₇K) h10g,
      lift_update_even _ _ (hc _ hv₆K) (hexp _ hv₆K) h10d]
    exact lift_update_odd _ _ (hc _ hv₅K) (hexp _ hv₅K) h10e rfl
  have e9 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 9 [])) = 1 := by
    rw [lift_update_even _ _ (hc _ hv₇K) (hexp _ hv₇K) h9g]
    exact lift_update_odd _ _ (hc _ hv₆K) (hexp _ hv₆K) h9d rfl
  have e26 : FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD 26 [])) = 1 :=
    lift_update_odd _ _ (hc _ hv₇K) (hexp _ hv₇K) h26g rfl
  have hsqrel : ∀ i ∈ onSqIdx, FreeGroup.lift f₇ (FreeGroup.mk (onRels.getD i [])) = 1 := by
    intro i hi
    have hi29 : i < 29 := by
      simp only [onSqIdx, List.mem_cons, List.mem_nil_iff, or_false] at hi
      omega
    have hu := onRels_squares i hi
    have h := hval f₇ hf₇ _ (onRels_mem hi29)
    rw [MonoidHom.mem_ker, hu, lift_mk_append, map_mul] at h
    rw [hu, lift_mk_append]
    exact hsq _ h
  have hrest : ∀ i ∈ onExactIdx, i ∉ onSqIdx → i ∈ [6, 7, 9, 10, 23, 26, 27] := by decide
  have hrel : ∀ w ∈ onCoverRels, FreeGroup.lift f₇ (FreeGroup.mk w) = 1 := by
    intro w hw
    simp only [onCoverRels, List.mem_append, List.mem_map, List.mem_flatMap] at hw
    rcases hw with ⟨i, hi, rfl⟩ | ⟨i, hi, hw⟩
    · by_cases hsqi : i ∈ onSqIdx
      · exact hsqrel i hsqi
      · have := hrest i hi hsqi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact e6
        · exact e7
        · exact e9
        · exact e10
        · exact e23
        · exact e26
        · exact e27
    · have hi29 : i < 29 := by
        simp only [onCentralIdx, List.mem_cons, List.mem_nil_iff, or_false] at hi
        omega
      have hk := hval f₇ hf₇ _ (onRels_mem hi29)
      exact lift_centralWords f₇ _ (hc _ hk) (hexp _ hk) w hw
  have hgenE : (Subgroup.closure (Set.range f₇) ⊔ ρ.ker : Subgroup E) = ⊤ := by
    rw [← comap_map_eq, MonoidHom.map_closure, ← Set.range_comp]
    rw [show (⇑ρ ∘ f₇) = g from funext hf₇, hgen, comap_top]
  obtain ⟨hR1fin, hR1⟩ := Sporadic.Presentation.ONan.card_R1_le
  have hrestr := restrict_onCoverRels
  have : Finite (PG (subsetOf onGens [0, 1, 2, 3, 4, 5]).length
      (restrictWords (subsetOf onGens [0, 1, 2, 3, 4, 5]) onCoverRels)) := by
    rw [hrestr]
    exact hR1fin
  obtain ⟨hfinP, hcardP⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict onCoverRels
    (subsetOf onGens [0, 1, 2, 3, 4, 5]) Certificates.certificate22225
    ⟨this, le_refl _⟩
  have hle := card_le_card_of_relators ρ hker f₇ hrel hgenE
  rw [hrestr] at hcardP
  rw [Sporadic.ON.card_ON]
  exact hle.trans (hcardP.trans (by
    have := Nat.mul_le_mul_left 122760 hR1
    exact this.trans (by norm_num)))

theorem on_odd_card_center
    (Q : Type) [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (he : Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.ON)) :
    Odd (Nat.card (center Q)) :=
  odd_card_center_of_card_le (fun E _ _ ρ hρ hker hexp hperf => on_card_le E ρ hρ hker hexp hperf)
    Q hQ he

end CFSG.ComponentClassification.GSThmB.SpMult
