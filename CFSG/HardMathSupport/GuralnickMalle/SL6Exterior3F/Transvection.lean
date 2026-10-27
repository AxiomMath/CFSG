module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Compare

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module

variable {K : Type} [Field K]

@[expose] noncomputable def natEnd (g : GL (Fin 6) K) : (Fin 6 → K) →ₗ[K] (Fin 6 → K) :=
  Matrix.toLin' ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

@[expose] noncomputable def transvectionPart (g : GL (Fin 6) K) :
    (Fin 6 → K) →ₗ[K] (Fin 6 → K) :=
  natEnd g - 1

lemma mul_sub_one_eq {R : Type*} [Ring R] (A B : R) :
    A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by
  rw [sub_mul, one_mul, mul_sub, mul_one]
  abel

lemma sub_one_mul_comm {R : Type*} [Ring R] {A B : R} (h : A * B = B * A) :
    (A - 1) * (B - 1) = (B - 1) * (A - 1) := by
  rw [sub_mul, one_mul, mul_sub, mul_one, sub_mul, one_mul, mul_sub, mul_one, h]
  abel

lemma natEnd_one : natEnd (1 : GL (Fin 6) K) = 1 := by
  simp [natEnd, Module.End.one_eq_id]

lemma natEnd_mul (g h : GL (Fin 6) K) : natEnd (g * h) = natEnd g * natEnd h := by
  simp only [natEnd, Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

lemma transvectionPart_one : transvectionPart (1 : GL (Fin 6) K) = 0 := by
  change natEnd 1 - 1 = 0
  rw [natEnd_one, sub_self]

lemma transvectionPart_mul (g h : GL (Fin 6) K) :
    transvectionPart (g * h) =
      transvectionPart g + transvectionPart h +
        transvectionPart g * transvectionPart h := by
  change natEnd (g * h) - 1 =
    (natEnd g - 1) + (natEnd h - 1) + (natEnd g - 1) * (natEnd h - 1)
  rw [natEnd_mul]
  exact mul_sub_one_eq (natEnd g) (natEnd h)

lemma transvectionPart_mul_self [CharP K 2] (g : GL (Fin 6) K) (hg : g ^ 2 = 1) :
    transvectionPart g * transvectionPart g = 0 := by
  have hsq : g * g = 1 := by simpa [pow_two] using hg
  have h := transvectionPart_mul g g
  rw [hsq, transvectionPart_one] at h
  have h2 : transvectionPart g + transvectionPart g = 0 := by
    rw [← two_smul K (transvectionPart g)]
    have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [h2K, zero_smul]
  rw [h2, zero_add] at h
  exact h.symm

lemma transvectionPart_eq_zero_iff (g : GL (Fin 6) K) :
    transvectionPart g = 0 ↔ g = 1 := by
  constructor
  · intro h
    have h' : natEnd g = 1 := by
      exact sub_eq_zero.mp (by simpa [transvectionPart] using h)
    have h'' : ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      have hc := congrArg LinearMap.toMatrix' h'
      simpa [natEnd, Module.End.one_eq_id] using hc
    exact Units.ext h''
  · intro h
    rw [h]
    exact transvectionPart_one

lemma mul_eq_zero_of_commute_of_finrank_range_eq_one {V : Type*} [AddCommGroup V]
    [Module K V] (x y : V →ₗ[K] V) (hx2 : x * x = 0) (_hy2 : y * y = 0)
    (hcomm : x * y = y * x) (hx : finrank K (LinearMap.range x) = 1)
    (hy : finrank K (LinearMap.range y) = 1) : x * y = 0 := by
  classical
  have hxbot : LinearMap.range x ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hx
    exact zero_ne_one hx
  have hybot : LinearMap.range y ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hy
    exact zero_ne_one hy
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hxbot
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hybot
  have hx_span : LinearMap.range x = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hx hu_mem hu_ne
  have hy_span : LinearMap.range y = K ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hy hv_mem hv_ne
  have hxu : x u = 0 := by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hu_mem
    rw [← Module.End.mul_apply, hx2]
    rfl
  by_contra hxy
  have hne : ∃ w, (x * y) w ≠ 0 := by
    by_contra h
    exact hxy (LinearMap.ext (fun w => Classical.not_not.mp (not_exists.mp h w)))
  obtain ⟨w, hw⟩ := hne
  have hyw : y w ∈ K ∙ v := hy_span ▸ LinearMap.mem_range_self y w
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyw
  have hxw : (x * y) w = c • x v := by
    rw [Module.End.mul_apply, ← hc, map_smul]
  have hcne : c ≠ 0 := by
    intro hc0
    exact hw (by rw [hxw, hc0, zero_smul])
  have hxv : x v ≠ 0 := by
    intro hv0
    exact hw (by rw [hxw, hv0, smul_zero])
  have hne2 : ∃ w', (y * x) w' ≠ 0 := ⟨w, by simpa only [← hcomm] using hw⟩
  obtain ⟨w', hw'⟩ := hne2
  have hxw' : x w' ∈ K ∙ u := hx_span ▸ LinearMap.mem_range_self x w'
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hxw'
  have hdne : d ≠ 0 := by
    intro hd0
    exact hw' (by rw [Module.End.mul_apply, ← hd, hd0, zero_smul, map_zero])
  have hyu : y u ≠ 0 := by
    intro hyu0
    exact hw' (by rw [Module.End.mul_apply, ← hd, map_smul, hyu0, smul_zero])
  have hyu_span : y u ∈ K ∙ v := hy_span ▸ LinearMap.mem_range_self y u
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hyu_span
  have hbne : b ≠ 0 := by
    intro hb0
    exact hyu (by rw [← hb, hb0, zero_smul])
  have h2 : (x * y) u ≠ 0 := by
    rw [Module.End.mul_apply, ← hb, map_smul]
    exact smul_ne_zero hbne hxv
  have h1 : (x * y) u = 0 := by
    rw [hcomm, Module.End.mul_apply, hxu, map_zero]
  exact h2 h1

lemma finrank_ker_of_finrank_range_eq_one (x : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    (hx : finrank K (LinearMap.range x) = 1) : finrank K (LinearMap.ker x) = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker x
  rw [hx, Module.finrank_fin_fun] at h
  omega

lemma range_le_ker_of_mul_self_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    (x : V →ₗ[K] V) (hx2 : x * x = 0) : LinearMap.range x ≤ LinearMap.ker x := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, ← Module.End.mul_apply, hx2]
  rfl

lemma ker_eq_of_range_ne_of_finrank_range_add_eq_one [CharP K 2]
    (x y : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    (hx : finrank K (LinearMap.range x) = 1) (hy : finrank K (LinearMap.range y) = 1)
    (hxy : finrank K (LinearMap.range (x + y)) = 1)
    (hne : LinearMap.range x ≠ LinearMap.range y) :
    LinearMap.ker x = LinearMap.ker y := by
  classical
  have hxker : finrank K (LinearMap.ker x) = 5 := finrank_ker_of_finrank_range_eq_one x hx
  have hyker : finrank K (LinearMap.ker y) = 5 := finrank_ker_of_finrank_range_eq_one y hy
  have hxyker : finrank K (LinearMap.ker (x + y)) = 5 :=
    finrank_ker_of_finrank_range_eq_one (x + y) hxy
  have hdisj : LinearMap.range x ⊓ LinearMap.range y = ⊥ := by
    by_contra h
    obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hwr : w ∈ LinearMap.range x := hw_mem.1
    have hspan : LinearMap.range x = K ∙ w :=
      eq_span_singleton_of_mem_of_finrank_eq_one hx hwr hw_ne
    have hsub : ({w} : Set (Fin 6 → K)) ⊆ (LinearMap.range y : Set (Fin 6 → K)) := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hw_mem.2
    have hle : LinearMap.range x ≤ LinearMap.range y := by
      rw [hspan]
      exact Submodule.span_le.mpr hsub
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hx, hy]))
  have hker : LinearMap.ker (x + y) = LinearMap.ker x ⊓ LinearMap.ker y := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.add_apply, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.mem_ker]
    constructor
    · intro hv
      have hxyeq : x v = -y v := eq_neg_of_add_eq_zero_left hv
      have hmem : x v ∈ LinearMap.range x ⊓ LinearMap.range y := by
        refine ⟨LinearMap.mem_range_self x v, ?_⟩
        rw [hxyeq]
        exact neg_mem (LinearMap.mem_range_self y v)
      rw [hdisj] at hmem
      have hxv0 : x v = 0 := by simpa using hmem
      have hyv0 : y v = 0 := by
        have hneg : -y v = 0 := by rw [← hxyeq, hxv0]
        exact neg_eq_zero.mp hneg
      exact ⟨hxv0, hyv0⟩
    · rintro ⟨hx0, hy0⟩
      rw [hx0, hy0, add_zero]
  have hEq : (LinearMap.ker x ⊓ LinearMap.ker y : Submodule K (Fin 6 → K)) =
      LinearMap.ker (x + y) := hker.symm
  have hfr : finrank K ((LinearMap.ker x ⊓ LinearMap.ker y : Submodule K (Fin 6 → K))) = 5 := by
    rw [hEq, hxyker]
  have hEx : (LinearMap.ker x ⊓ LinearMap.ker y : Submodule K (Fin 6 → K)) = LinearMap.ker x :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hfr, hxker])
  have hEy : (LinearMap.ker x ⊓ LinearMap.ker y : Submodule K (Fin 6 → K)) = LinearMap.ker y :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hfr, hyker])
  exact hEx.symm.trans hEy

theorem card_le_pow_five_of_forall_rank_one (K : Type) [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (GL (Fin 6) K)) (hAel : CFSG.Open.IsElemAbelian 2 A) (hA : A ≠ ⊥)
    (hrank : ∀ a ∈ A, a ≠ 1 →
      Module.finrank K (LinearMap.range
        (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1)) = 1) :
    Nat.card A ≤ Nat.card K ^ 5 := by
  classical
  have hcommA : IsMulCommutative A := hAel.1
  let hKfin : Fintype K := Fintype.ofFinite K
  let hVfin : Fintype (Fin 6 → K) := inferInstance
  let x : A → (Fin 6 → K) →ₗ[K] (Fin 6 → K) := fun a => transvectionPart (a : GL (Fin 6) K)
  have hx_one : x 1 = 0 := by
    change transvectionPart ((1 : A) : GL (Fin 6) K) = 0
    rw [Subgroup.coe_one]
    exact transvectionPart_one
  have hx_sq : ∀ a : A, x a * x a = 0 := fun a =>
    transvectionPart_mul_self (a : GL (Fin 6) K) (hAel.2 (a : GL (Fin 6) K) a.2)
  have hx_rank : ∀ a : A, a ≠ 1 → finrank K (LinearMap.range (x a)) = 1 := by
    intro a ha
    have hagl : (a : GL (Fin 6) K) ≠ 1 := by
      intro h1
      exact ha (Subtype.ext h1)
    have h := hrank (a : GL (Fin 6) K) a.2 hagl
    change finrank K (LinearMap.range (transvectionPart (a : GL (Fin 6) K))) = 1
    exact h
  have hx_ker : ∀ a : A, a ≠ 1 → finrank K (LinearMap.ker (x a)) = 5 := fun a ha =>
    finrank_ker_of_finrank_range_eq_one (x a) (hx_rank a ha)
  have hx_range_le_ker : ∀ a : A, LinearMap.range (x a) ≤ LinearMap.ker (x a) := fun a =>
    range_le_ker_of_mul_self_eq_zero (x a) (hx_sq a)
  have hx_comm : ∀ a b : A, x a * x b = x b * x a := by
    intro a b
    by_cases ha1 : (a : GL (Fin 6) K) = 1
    · have haA : a = 1 := Subtype.ext ha1
      subst haA
      rw [hx_one]
      rw [zero_mul, mul_zero]
    · by_cases hb1 : (b : GL (Fin 6) K) = 1
      · have hbA : b = 1 := Subtype.ext hb1
        subst hbA
        rw [hx_one]
        rw [mul_zero, zero_mul]
      · have hcomm : (a : GL (Fin 6) K) * (b : GL (Fin 6) K) =
            (b : GL (Fin 6) K) * (a : GL (Fin 6) K) := congrArg Subtype.val (mul_comm' a b)
        have hAB : natEnd (a : GL (Fin 6) K) * natEnd (b : GL (Fin 6) K) =
            natEnd (b : GL (Fin 6) K) * natEnd (a : GL (Fin 6) K) := by
          rw [← natEnd_mul, ← natEnd_mul, hcomm]
        change transvectionPart (a : GL (Fin 6) K) * transvectionPart (b : GL (Fin 6) K) =
          transvectionPart (b : GL (Fin 6) K) * transvectionPart (a : GL (Fin 6) K)
        exact sub_one_mul_comm hAB
  have hx_mul_zero : ∀ a b : A, a ≠ 1 → b ≠ 1 → x a * x b = 0 := by
    intro a b ha hb
    exact mul_eq_zero_of_commute_of_finrank_range_eq_one (x a) (x b) (hx_sq a) (hx_sq b)
      (hx_comm a b) (hx_rank a ha) (hx_rank b hb)
  have hx_add : ∀ a b : A, x (a * b) = x a + x b := by
    intro a b
    by_cases ha1 : (a : GL (Fin 6) K) = 1
    · have haA : a = 1 := Subtype.ext ha1
      subst haA
      rw [one_mul, hx_one, zero_add]
    · by_cases hb1 : (b : GL (Fin 6) K) = 1
      · have hbA : b = 1 := Subtype.ext hb1
        subst hbA
        rw [mul_one, hx_one, add_zero]
      · have haA : a ≠ 1 := by intro h1; exact ha1 (congrArg Subtype.val h1)
        have hbA : b ≠ 1 := by intro h1; exact hb1 (congrArg Subtype.val h1)
        change transvectionPart ((a : GL (Fin 6) K) * (b : GL (Fin 6) K)) =
          transvectionPart (a : GL (Fin 6) K) + transvectionPart (b : GL (Fin 6) K)
        rw [transvectionPart_mul, hx_mul_zero a b haA hbA, add_zero]
  have hx_eq_one : ∀ a : A, x a = 0 → a = 1 := by
    intro a ha
    have hagl : (a : GL (Fin 6) K) = 1 := by
      apply (transvectionPart_eq_zero_iff (a : GL (Fin 6) K)).mp
      simpa only [x] using ha
    exact Subtype.ext hagl
  have hx_inj : Function.Injective x := by
    intro a b hab
    have h := hx_add a b
    rw [hab] at h
    have hzero : x (a * b) = 0 := by
      rw [h]
      exact add_self_eq_zero_of_charP_two (K := K) (W := (Fin 6 → K) →ₗ[K] (Fin 6 → K)) (x b)
    have hab1 : a * b = 1 := hx_eq_one (a * b) hzero
    have haa : a * a = 1 := by
      apply Subtype.ext
      show (a : GL (Fin 6) K) * (a : GL (Fin 6) K) = 1
      simpa [pow_two] using hAel.2 (a : GL (Fin 6) K) a.2
    have hmul : a * (a * b) = a * 1 := by rw [hab1]
    rw [← mul_assoc, haa, one_mul, mul_one] at hmul
    exact hmul.symm
  by_cases hcase : ∀ a b : A, a ≠ 1 → b ≠ 1 →
      LinearMap.range (x a) = LinearMap.range (x b)
  ·
    obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    have hxbot : LinearMap.range (x a₀) ≠ ⊥ := by
      intro hbot
      have h := hx_rank a₀ ha₀
      rw [hbot, finrank_bot] at h
      exact zero_ne_one h
    obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hxbot
    have hspan : LinearMap.range (x a₀) = K ∙ u :=
      eq_span_singleton_of_mem_of_finrank_eq_one (hx_rank a₀ ha₀) hu_mem hu_ne
    obtain ⟨j, hj⟩ : ∃ j : Fin 6, u j ≠ 0 := by
      by_contra h
      exact hu_ne (funext fun j => Classical.not_not.mp (not_exists.mp h j))
    let ell : (Fin 6 → K) →ₗ[K] K := (u j)⁻¹ • LinearMap.proj j
    have hell : ell u = 1 := by
      simp only [ell, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
      exact inv_mul_cancel₀ hj
    let phi : A → Module.Dual K (Fin 6 → K) := fun a => ell.comp (x a)
    have hphi_one : phi 1 = 0 := by
      simp only [phi, hx_one, LinearMap.comp_zero]
    have hphi_u : ∀ a : A, phi a u = 0 := by
      intro a
      by_cases ha : a = 1
      · subst ha
        simp only [hphi_one, LinearMap.zero_apply]
      · have hrange : LinearMap.range (x a) = K ∙ u := by
          rw [hcase a a₀ ha ha₀, hspan]
        obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (by
          rw [hrange]
          exact Submodule.mem_span_singleton_self u)
        have hxau : x a u = 0 := by
          rw [← hw, ← Module.End.mul_apply, hx_sq a]
          rfl
        simp only [phi, LinearMap.comp_apply, hxau, map_zero]
    have hx_decomp : ∀ a : A, x a = (phi a).smulRight u := by
      intro a
      by_cases ha : a = 1
      · subst ha
        rw [hx_one, hphi_one, LinearMap.zero_smulRight]
      · have hrange : LinearMap.range (x a) = K ∙ u := by
          rw [hcase a a₀ ha ha₀, hspan]
        apply LinearMap.ext
        intro v
        rw [LinearMap.smulRight_apply]
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hrange ▸ LinearMap.mem_range_self (x a) v)
        have hphi : phi a v = c := by
          simp only [phi, LinearMap.comp_apply]
          rw [← hc, map_smul, hell, smul_eq_mul, mul_one]
        rw [hphi, ← hc]
    have hphi_mem : ∀ a : A, phi a ∈ (K ∙ u).dualAnnihilator := by
      intro a
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hphi_u a, smul_zero]
    let Phi : A → (K ∙ u).dualAnnihilator := fun a => ⟨phi a, hphi_mem a⟩
    have hPhi_inj : Function.Injective Phi := by
      intro a b hab
      have hphieq : phi a = phi b := congrArg Subtype.val hab
      have hxeq : x a = x b := by rw [hx_decomp a, hx_decomp b, hphieq]
      exact hx_inj hxeq
    let hDfin : Fintype (Module.Dual K (Fin 6 → K)) :=
      FunLike.fintype (Module.Dual K (Fin 6 → K))
    let hAnnfin : Fintype ((K ∙ u).dualAnnihilator) := Subtype.fintype _
    have hcard : Nat.card A ≤ Nat.card ((K ∙ u).dualAnnihilator) :=
      Nat.card_le_card_of_injective Phi hPhi_inj
    have hfr : finrank K (K ∙ u).dualAnnihilator = 5 := by
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := K) (V := Fin 6 → K) (K ∙ u)
      rw [finrank_span_singleton hu_ne, Module.finrank_fin_fun] at h
      omega
    have hcardW : Fintype.card ((K ∙ u).dualAnnihilator) = Fintype.card K ^ 5 :=
      (Module.card_eq_pow_finrank (K := K) (V := (K ∙ u).dualAnnihilator)).trans (by rw [hfr])
    have hcard' : Nat.card A ≤ Fintype.card ((K ∙ u).dualAnnihilator) := by
      have hEq : Nat.card ((K ∙ u).dualAnnihilator) =
          Fintype.card ((K ∙ u).dualAnnihilator) := Nat.card_eq_fintype_card
      exact le_trans hcard (le_of_eq hEq)
    calc Nat.card A ≤ Fintype.card ((K ∙ u).dualAnnihilator) := hcard'
      _ = Fintype.card K ^ 5 := hcardW
      _ = Nat.card K ^ 5 := by rw [Nat.card_eq_fintype_card]
  ·
    push Not at hcase
    obtain ⟨a₀, b₀, ha₀, hb₀, hne⟩ := hcase
    let H : Submodule K (Fin 6 → K) := LinearMap.ker (x a₀)
    have hHfr : finrank K H = 5 := by
      simpa only [H] using hx_ker a₀ ha₀
    have hdich : ∀ a b : A, a ≠ 1 → b ≠ 1 → LinearMap.range (x a) ≠ LinearMap.range (x b) →
        LinearMap.ker (x a) = LinearMap.ker (x b) := by
      intro a b ha hb hneab
      have hrank_add : finrank K (LinearMap.range (x a + x b)) = 1 := by
        by_cases hab : a * b = 1
        · exfalso
          have hzero : x (a * b) = 0 := by rw [hab]; exact hx_one
          rw [hx_add a b] at hzero
          have hxab : x a = x b := by
            have h := eq_neg_of_add_eq_zero_left hzero
            rwa [neg_eq_self_of_charP_two (K := K)
              (W := (Fin 6 → K) →ₗ[K] (Fin 6 → K)) (x b)] at h
          exact hneab (by rw [hxab])
        · have h := hx_rank (a * b) hab
          rwa [hx_add a b] at h
      exact ker_eq_of_range_ne_of_finrank_range_add_eq_one (x a) (x b)
        (hx_rank a ha) (hx_rank b hb) hrank_add hneab
    have hker_all : ∀ c : A, c ≠ 1 → LinearMap.ker (x c) = H := by
      intro c hc
      by_cases hca : LinearMap.range (x c) = LinearMap.range (x a₀)
      · have hne_cb : LinearMap.range (x c) ≠ LinearMap.range (x b₀) := by
          rw [hca]
          exact hne
        have h1 := hdich c b₀ hc hb₀ hne_cb
        have h2 := hdich a₀ b₀ ha₀ hb₀ hne
        rw [h1, ← h2]
      · exact hdich c a₀ hc ha₀ hca
    have hHne_top : H ≠ ⊤ := by
      intro htop
      have h5 := hHfr
      rw [htop, finrank_top, Module.finrank_fin_fun] at h5
      omega
    obtain ⟨v₀, hv₀⟩ : ∃ v : Fin 6 → K, v ∉ H := by
      by_contra h
      apply hHne_top
      apply Submodule.ext
      intro v
      simp only [Submodule.mem_top, iff_true]
      by_contra hv
      exact h ⟨v, hv⟩
    have hF_mem : ∀ a : A, x a v₀ ∈ H := by
      intro a
      by_cases ha : a = 1
      · subst ha
        rw [hx_one]
        exact H.zero_mem
      · have hmem : x a v₀ ∈ LinearMap.ker (x a) := hx_range_le_ker a (LinearMap.mem_range_self _ _)
        rw [hker_all a ha] at hmem
        exact hmem
    let F : A → H := fun a => ⟨x a v₀, hF_mem a⟩
    have hF_mul : ∀ a b : A, F (a * b) = F a + F b := by
      intro a b
      apply Subtype.ext
      simp only [F, Submodule.coe_add, LinearMap.add_apply, hx_add a b]
    have hF_zero : ∀ a : A, F a = 0 → a = 1 := by
      intro a ha
      by_contra hane
      have hxav : x a v₀ = 0 := by
        have := congrArg Subtype.val ha
        simpa only [F, Subtype.coe_mk, ZeroMemClass.coe_zero] using this
      have hmem : v₀ ∈ H := by
        rw [← hker_all a hane]
        exact LinearMap.mem_ker.mpr hxav
      exact hv₀ hmem
    have hF_inj : Function.Injective F := by
      intro a b hab
      have h := hF_mul a b
      rw [hab] at h
      have hzero : F (a * b) = 0 := by
        rw [h]
        exact add_self_eq_zero_of_charP_two (K := K) (W := H) (F b)
      have hab1 : a * b = 1 := hF_zero (a * b) hzero
      have haa : a * a = 1 := by
        apply Subtype.ext
        show (a : GL (Fin 6) K) * (a : GL (Fin 6) K) = 1
        simpa [pow_two] using hAel.2 (a : GL (Fin 6) K) a.2
      have hmul : a * (a * b) = a * 1 := by rw [hab1]
      rw [← mul_assoc, haa, one_mul, mul_one] at hmul
      exact hmul.symm
    let hHfin : Fintype H := Subtype.fintype _
    have hcard : Nat.card A ≤ Nat.card H := Nat.card_le_card_of_injective F hF_inj
    have hcardH : Fintype.card H = Fintype.card K ^ 5 :=
      (Module.card_eq_pow_finrank (K := K) (V := H)).trans (by rw [hHfr])
    have hcard' : Nat.card A ≤ Fintype.card H := by
      have hEq : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
      exact le_trans hcard (le_of_eq hEq)
    calc Nat.card A ≤ Fintype.card H := hcard'
      _ = Fintype.card K ^ 5 := hcardH
      _ = Nat.card K ^ 5 := by rw [Nat.card_eq_fintype_card]

end CFSG.HardMathSupport.GuralnickMalle
