module

public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions
public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed
open CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

section Model

theorem Z_sq_eq_one (n : ℕ) (hn : 1 ≤ n) (w : Wreath (2 ^ n)) (hw : w ∈ Original.Z (2 ^ n))
    (hsq : w ^ 2 = 1) : w = 1 ∨ w = Original.x (2 ^ n) := by
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨⟨a, b, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
  change element _ a b f ∈ Original.Z _ at hw
  change element _ a b f ^ 2 = 1 at hsq
  change element _ a b f = 1 ∨ element _ a b f = _
  rw [mem_Z_iff _ hm] at hw
  obtain ⟨rfl, rfl⟩ := hw
  rw [element_base_sq_eq_one_iff n hn] at hsq
  rw [x_eq_element]
  rcases hsq.1 with rfl | rfl
  · exact Or.inl (element_zero _)
  · exact Or.inr rfl

theorem base_conj_x2_cases (n : ℕ) (w : Wreath (2 ^ n)) :
    w⁻¹ * Original.x2 (2 ^ n) * w = Original.x2 (2 ^ n) ∨
      w⁻¹ * Original.x2 (2 ^ n) * w = Original.t (2 ^ n) ^ (2 ^ n / 2) := by
  have h : IsConj (Original.x2 (2 ^ n)) (w⁻¹ * Original.x2 (2 ^ n) * w) :=
    isConj_iff.mpr ⟨w⁻¹, by rw [inv_inv]⟩
  rw [x2_eq_element, base_conjugacy_iff] at h
  rw [x2_eq_element, t_half_eq_element]
  exact h

end Model

theorem inv_conj_pow (s w : G) (k : ℕ) : (s⁻¹ * w * s) ^ k = s⁻¹ * w ^ k * s := by
  have h := conj_pow (a := s⁻¹) (b := w) (i := k)
  rwa [inv_inv] at h

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

@[expose] def offBaseClass (u : G) : Set G :=
  {v | v ∈ modelBase S e ∧ ∃ j : ℤ, wreathModelHom S e (Original.a (2 ^ n)) ^ (2 * j) = u ∧
    ∃ g ∈ Subgroup.normalizer (modelBase S e : Set G),
      g⁻¹ * (wreathModelHom S e (Original.x2 (2 ^ n)) *
        wreathModelHom S e (Original.a (2 ^ n)) ^ j) * g = v}

@[expose] def baseClass (w : G) : Set G :=
  {v | v ∈ modelBase S e ∧ ∃ g ∈ Subgroup.normalizer (modelBase S e : Set G), g⁻¹ * w * g = v}

@[expose] def classInvariant (w : G) : Set G :=
  {v | (w ∈ modelBase S e ∧ v ∈ baseClass S e w) ∨
    (w ∉ modelBase S e ∧ v ∈ offBaseClass S e (w ^ 2))}

theorem classInvariant_of_mem {w : G} (hw : w ∈ modelBase S e) :
    classInvariant S e w = baseClass S e w := by
  ext v
  simp only [classInvariant, Set.mem_ofPred_eq, hw, true_and, not_true_eq_false, false_and,
    or_false]

theorem classInvariant_of_not_mem {w : G} (hw : w ∉ modelBase S e) :
    classInvariant S e w = offBaseClass S e (w ^ 2) := by
  ext v
  simp only [classInvariant, Set.mem_ofPred_eq, hw, false_and, not_false_eq_true, true_and,
    false_or]

theorem baseClass_conj {w g : G} (hg : g ∈ Subgroup.normalizer (modelBase S e : Set G)) :
    baseClass S e (g⁻¹ * w * g) = baseClass S e w := by
  ext v
  simp only [baseClass, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, k, hk, rfl⟩
    exact ⟨hv, g * k, Subgroup.mul_mem _ hg hk, by group⟩
  · rintro ⟨hv, k, hk, rfl⟩
    exact ⟨hv, g⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hk, by group⟩

theorem mem_baseClass_self {w : G} (hw : w ∈ modelBase S e) : w ∈ baseClass S e w :=
  ⟨hw, 1, Subgroup.one_mem _, by group⟩

theorem baseClass_eq_offBaseClass (hn : 2 ≤ n) {v : G}
    (hv : (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ * v ∈ modelCenter S e) :
    baseClass S e v = offBaseClass S e (v ^ 2) := by
  set φ := wreathModelHom S e
  set j₁ := φ (Original.x2 (2 ^ n))
  set aG := φ (Original.a (2 ^ n))
  set T := φ (Original.z (2 ^ n))
  rw [modelCenter_eq_zpowers] at hv
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hj₁sq : j₁ ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (Original.x2 (2 ^ n))
    rw [hstr.involution_orders.2.1] at h
    rw [← map_pow, h, map_one]
  have haB : aG ∈ modelBase S e :=
    (mem_modelBase_iff S e _).mpr (by rw [Original.a_eq, element_mem_base])
  have hcomm : j₁ * aG ^ i = aG ^ i * j₁ :=
    modelBase_commute S e _ _ (modelHom_x2_mem_modelBase S e)
      ((modelBase S e).zpow_mem haB i)
  have hveq : v = j₁ * aG ^ i := by rw [hi, mul_inv_cancel_left]
  have hvsq : v ^ 2 = aG ^ (2 * i) := by
    rw [hveq, (show Commute j₁ (aG ^ i) from hcomm).mul_pow, hj₁sq, one_mul, ← zpow_natCast,
      ← zpow_mul]
    congr 1
    push_cast
    ring
  have hTN : T ∈ Subgroup.normalizer (modelBase S e : Set G) :=
    sylow_le_modelBase_normalizer S e (wreathModelHom_mem S e _)
  ext u
  simp only [baseClass, offBaseClass, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, g, hg, rfl⟩
    exact ⟨hu, i, hvsq.symm, g, hg, by rw [← hveq]⟩
  · rintro ⟨hu, j, hj, g, hg, rfl⟩
    refine ⟨hu, ?_⟩
    change aG ^ (2 * j) = v ^ 2 at hj
    have hd : (aG ^ (j - i)) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul,
        show (j - i) * ((2 : ℕ) : ℤ) = 2 * j - 2 * i by push_cast; ring, zpow_sub, hj, ← hvsq,
        mul_inv_cancel]
    have hdZ : aG ^ (j - i) ∈ modelCenter S e := by
      rw [modelCenter_eq_zpowers]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    obtain ⟨w, hw, hwd⟩ := hdZ
    have hwsq : w ^ 2 = 1 := by
      apply wreathModelHom_injective S e
      rw [map_pow, hwd, hd, map_one]
    have hsplit : j₁ * aG ^ j = v * aG ^ (j - i) := by
      rw [hveq, mul_assoc, ← zpow_add, add_sub_cancel]
    rcases Z_sq_eq_one n (by omega) w hw hwsq with rfl | rfl
    · rw [map_one] at hwd
      refine ⟨g, hg, ?_⟩
      rw [hsplit, ← hwd, mul_one]
    · refine ⟨T * g, Subgroup.mul_mem _ hTN hg, ?_⟩
      have hTv : T⁻¹ * v * T = v * aG ^ (j - i) := by
        rw [← hwd, hveq]
        have hTa : T⁻¹ * aG ^ i * T = aG ^ i := by
          have h := modelCenter_conj S e hn
            ((modelCenter S e).zpow_mem (⟨_, Subgroup.mem_zpowers _, rfl⟩ : aG ∈ modelCenter S e) i)
            (wreathModelHom_mem S e (Original.z (2 ^ n)))
          exact h
        calc
          T⁻¹ * (j₁ * aG ^ i) * T = (T⁻¹ * j₁ * T) * (T⁻¹ * aG ^ i * T) := by group
          _ = φ (Original.t (2 ^ n) ^ (2 ^ n / 2)) * aG ^ i := by
            rw [modelHom_swap_conj_x2 S e, hTa]
          _ = j₁ * aG ^ i * φ (Original.x (2 ^ n)) := by
            rw [← modelHom_x_mul_x2 S e (by omega)]
            have hxc : φ (Original.x (2 ^ n)) * aG ^ i = aG ^ i * φ (Original.x (2 ^ n)) :=
              modelBase_commute S e _ _ (modelHom_x_mem_modelBase S e)
                ((modelBase S e).zpow_mem haB i)
            have hxj : φ (Original.x (2 ^ n)) * j₁ = j₁ * φ (Original.x (2 ^ n)) :=
              modelBase_commute S e _ _ (modelHom_x_mem_modelBase S e)
                (modelHom_x2_mem_modelBase S e)
            rw [hxj, mul_assoc, hxc, ← mul_assoc]
      rw [hsplit, ← hTv]
      group

theorem sq_mem_modelCenter_of_not_mem (hn : 1 ≤ n) {w : G} (hw : w ∈ (S : Subgroup G))
    (hwB : w ∉ modelBase S e) : w ^ 2 ∈ modelCenter S e := by
  obtain ⟨w', rfl⟩ := exists_wreathModelHom_eq S e hw
  rw [mem_modelBase_iff] at hwB
  rw [← map_pow, mem_modelCenter_iff]
  obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w'
  change element _ c d f ∉ baseSubgroup _ at hwB
  change element _ c d f ^ 2 ∈ _
  rw [element_mem_base] at hwB
  rw [(swap_exponent_cases f).resolve_left hwB]
  exact element_swap_sq_mem_Z n hn c d

theorem classInvariant_sylow_conj (hn : 2 ≤ n) {w s : G} (hw : w ∈ (S : Subgroup G))
    (hs : s ∈ (S : Subgroup G)) : classInvariant S e (s⁻¹ * w * s) = classInvariant S e w := by
  by_cases hwB : w ∈ modelBase S e
  · rw [classInvariant_of_mem S e hwB, classInvariant_of_mem S e (modelBase_conj_mem S e hwB hs),
      baseClass_conj S e (sylow_le_modelBase_normalizer S e hs)]
  · have hwB' : s⁻¹ * w * s ∉ modelBase S e := fun h => hwB ((modelBase_conj_mem_iff S e hs).mp h)
    rw [classInvariant_of_not_mem S e hwB, classInvariant_of_not_mem S e hwB', inv_conj_pow,
      modelCenter_conj S e hn (sq_mem_modelCenter_of_not_mem S e (by omega) hw hwB) hs]

theorem classInvariant_base_conj {w g : G} (hw : w ∈ modelBase S e)
    (hg : g ∈ Subgroup.normalizer (modelBase S e : Set G)) :
    classInvariant S e (g⁻¹ * w * g) = classInvariant S e w := by
  have hw' : g⁻¹ * w * g ∈ modelBase S e := (Subgroup.mem_normalizer_iff''.mp hg w).mp hw
  rw [classInvariant_of_mem S e hw, classInvariant_of_mem S e hw', baseClass_conj S e hg]

theorem classInvariant_of_mem_rightConjugate_modelV (hn : 2 ≤ n) {v s : G}
    (hs : s ∈ (S : Subgroup G)) (hv : v ∈ rightConjugate (modelV S e) s)
    (hvZ : v ∉ modelCenter S e) : classInvariant S e v = offBaseClass S e (v ^ 2) := by
  by_cases hvB : v ∈ modelBase S e
  · rw [classInvariant_of_mem S e hvB]
    apply baseClass_eq_offBaseClass S e hn
    obtain ⟨y, hy, rfl⟩ := hv
    change s⁻¹ * y * s⁻¹⁻¹ ∈ modelBase S e at hvB
    change s⁻¹ * y * s⁻¹⁻¹ ∉ modelCenter S e at hvZ
    change (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ * (s⁻¹ * y * s⁻¹⁻¹) ∈ modelCenter S e
    rw [inv_inv] at hvB hvZ ⊢
    obtain ⟨w, hw, rfl⟩ := hy
    have hwB : wreathModelHom S e w ∈ modelBase S e := (modelBase_conj_mem_iff S e hs).mp hvB
    rw [mem_modelBase_iff] at hwB
    have hwZ : w ∉ Original.Z (2 ^ n) := by
      intro h
      apply hvZ
      rw [modelCenter_conj S e hn ⟨w, h, rfl⟩ hs]
      exact ⟨w, h, rfl⟩
    have hx2w := (V_inf_base n hn w hw hwB).resolve_left hwZ
    obtain ⟨t, rfl⟩ := exists_wreathModelHom_eq S e hs
    have hcase := base_conj_x2_cases n t
    have hsx2 : (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ *
        ((wreathModelHom S e t)⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) *
          wreathModelHom S e t) ∈ modelCenter S e := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, mem_modelCenter_iff]
      rcases hcase with h | h
      · rw [h, inv_mul_cancel]
        exact (Original.Z _).one_mem
      · rw [h]
        have hx2inv : (Original.x2 (2 ^ n))⁻¹ = Original.x2 (2 ^ n) := by
          rw [x2_eq_element, element_base_inv, neg_zero, neg_half n (by omega)]
        rw [hx2inv, x2_eq_element, t_half_eq_element, element_base_mul, zero_add, add_zero]
        rw [mem_Z_iff _ (Nat.one_lt_two_pow (by omega))]
        exact ⟨rfl, rfl⟩
    have hc : (wreathModelHom S e t)⁻¹ * wreathModelHom S e ((Original.x2 (2 ^ n))⁻¹ * w) *
        wreathModelHom S e t = wreathModelHom S e ((Original.x2 (2 ^ n))⁻¹ * w) :=
      modelCenter_conj S e hn ⟨_, hx2w, rfl⟩ (wreathModelHom_mem S e t)
    have hsplit : (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ *
        ((wreathModelHom S e t)⁻¹ * wreathModelHom S e w * wreathModelHom S e t) =
      ((wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ *
        ((wreathModelHom S e t)⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) *
          wreathModelHom S e t)) *
        ((wreathModelHom S e t)⁻¹ * wreathModelHom S e ((Original.x2 (2 ^ n))⁻¹ * w) *
          wreathModelHom S e t) := by
      rw [map_mul, map_inv]
      group
    rw [hsplit, hc]
    exact (modelCenter S e).mul_mem hsx2 ⟨_, hx2w, rfl⟩
  · rw [classInvariant_of_not_mem S e hvB]

theorem sq_mem_modelCenter_of_mem_rightConjugate_modelV (hn : 2 ≤ n) {v s : G}
    (hs : s ∈ (S : Subgroup G)) (hv : v ∈ rightConjugate (modelV S e) s) :
    v ^ 2 ∈ modelCenter S e := by
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨w, hw, rfl⟩ := hy
  change (s⁻¹ * wreathModelHom S e w * s⁻¹⁻¹) ^ 2 ∈ modelCenter S e
  rw [inv_inv, inv_conj_pow, ← map_pow]
  have hsq : wreathModelHom S e (w ^ 2) ∈ modelCenter S e := ⟨_, V_sq_mem_Z n hn w hw, rfl⟩
  rw [modelCenter_conj S e hn hsq hs]
  exact hsq

variable [Finite G]

theorem classInvariant_v_conj (hn : 2 ≤ n) (s : S) {v h : G}
    (hh : h ∈ Subgroup.normalizer (rightConjugate (modelV S e) (s : G) : Set G))
    (hv : v ∈ rightConjugate (modelV S e) (s : G)) :
    classInvariant S e (h⁻¹ * v * h) = classInvariant S e v := by
  have hfix : ∀ c ∈ modelCenter S e, h⁻¹ * c * h = c := by
    rintro _ ⟨w, hw, rfl⟩
    exact model_v_conjugate_normalizer_center_fixed n hn S e s h hh w hw
  by_cases hvZ : v ∈ modelCenter S e
  · rw [hfix v hvZ]
  · have hv' : h⁻¹ * v * h ∈ rightConjugate (modelV S e) (s : G) :=
      (Subgroup.mem_normalizer_iff''.mp hh v).mp hv
    have hvZ' : h⁻¹ * v * h ∉ modelCenter S e := by
      intro h'
      apply hvZ
      have := hfix _ h'
      have heq : h⁻¹ * v * h = v := by
        have h2 := congrArg (fun y => h * y * h⁻¹) this
        rw [show h * (h⁻¹ * (h⁻¹ * v * h) * h) * h⁻¹ = h⁻¹ * v * h by group,
          show h * (h⁻¹ * v * h) * h⁻¹ = v by group] at h2
        exact h2
      rw [← heq]
      exact h'
    rw [classInvariant_of_mem_rightConjugate_modelV S e hn s.property hv hvZ,
      classInvariant_of_mem_rightConjugate_modelV S e hn s.property hv' hvZ', inv_conj_pow,
      hfix _ (sq_mem_modelCenter_of_mem_rightConjugate_modelV S e hn s.property hv)]

theorem classInvariant_step (hn : 2 ≤ n) {T : Subgroup G} (hTS : T ≤ (S : Subgroup G))
    {h : G} (hstep : WreathedFusionStep (S : Subgroup G) e T h) {w : G} (hw : w ∈ T) :
    classInvariant S e (h⁻¹ * w * h) = classInvariant S e w := by
  rcases hstep with ⟨rfl, hh⟩ | ⟨hT, hh⟩ | ⟨⟨s, hT⟩, hh⟩
  · exact classInvariant_sylow_conj S e hn hw hh
  · rw [ambient_original_base_eq_modelBase] at hT
    subst hT
    exact classInvariant_base_conj S e hw hh
  · rw [ambient_original_v_eq_modelV] at hT
    subst hT
    exact classInvariant_v_conj S e hn s hh hw

theorem classInvariant_chain (hn : 2 ≤ n) {P : Subgroup G} {g : G}
    (hchain : WreathedFusionDecomposition (S : Subgroup G) e P g) :
    ∀ x ∈ P, classInvariant S e (g⁻¹ * x * g) = classInvariant S e x := by
  induction hchain with
  | one => intro x _; simp
  | @tail g h T _ hTS hcur hstep ih =>
      intro x hx
      have hxT : g⁻¹ * x * g ∈ T := hcur ⟨x, hx, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group,
        classInvariant_step S e hn hTS hstep hxT, ih x hx]

theorem base_isConj_iff (hn : 2 ≤ n) {x y : G} (hx : x ∈ modelBase S e)
    (hy : y ∈ modelBase S e) :
    IsConj x y ↔ ∃ g ∈ Subgroup.normalizer (modelBase S e : Set G), g⁻¹ * x * g = y := by
  constructor
  · intro hxy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    let P := Subgroup.zpowers x
    have hxP : x ∈ P := Subgroup.mem_zpowers _
    have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr (modelBase_le_sylow S e hx)
    have hgP : rightConjugate P c⁻¹ ≤ (S : Subgroup G) := by
      rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        modelBase_le_sylow S e hy
    obtain ⟨z, hchain, -, hzg⟩ := wreathed_fusion_decomposition S n hn e P hPS c⁻¹ hgP
    have hzx : z⁻¹ * x * z = c * x * c⁻¹ := by rw [hzg x hxP, inv_inv]
    have hinv := classInvariant_chain S e hn hchain x hxP
    rw [hzx, classInvariant_of_mem S e hy, classInvariant_of_mem S e hx] at hinv
    have hmem : c * x * c⁻¹ ∈ baseClass S e x := hinv ▸ mem_baseClass_self S e hy
    exact hmem.2
  · rintro ⟨g, -, rfl⟩
    exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩

theorem exists_isConj_mem_modelBase (hn : 2 ≤ n)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3)))
    (g : G) (hg : ∃ k : ℕ, orderOf g = 2 ^ k) (hord : orderOf g ≠ 2 * 2 ^ n) :
    ∃ x ∈ modelBase S e, IsConj g x := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hg
  have hgp : IsPGroup 2 (Subgroup.zpowers g) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨y, hgy⟩ := CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow S g hgp
  have hyord : orderOf (y : G) ≠ 2 * 2 ^ n := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hgy
    rw [← hc, show c * g * c⁻¹ = (MulAut.conj c) g by simp, MulEquiv.orderOf_eq]
    exact hord
  by_cases hyB : (y : G) ∈ modelBase S e
  · exact ⟨y, hyB, hgy⟩
  ·
    obtain ⟨w, hw⟩ := exists_wreathModelHom_eq S e y.property
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
    change wreathModelHom S e (element _ c d f) = _ at hw
    rw [← hw, mem_modelBase_iff, element_mem_base] at hyB
    have hf : f = 1 := (swap_exponent_cases f).resolve_left hyB
    subst hf
    rw [← hw, orderOf_injective _ (wreathModelHom_injective S e)] at hyord
    obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    have heven : ¬ Odd (c + d).val := fun hodd =>
      hyord ((element_maximal_order_iff k' c d 1).mpr ⟨rfl, hodd⟩)
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨j, hj⟩ := heven
    have hconj : IsConj (element (2 ^ (k' + 1)) c d 1)
        (element (2 ^ (k' + 1)) (j : ZMod _) (j : ZMod _) 1) := by
      rw [swap_isConj_iff, ← ZMod.natCast_zmod_val (c + d), hj]
      push_cast
      ring
    obtain ⟨h₀, hh₀N, hh₀⟩ := exists_centralizer_conj_swap_eq_x2 hn S e hsix
    have haj : wreathModelHom S e (element (2 ^ (k' + 1)) (j : ZMod _) (j : ZMod _) 1) =
        wreathModelHom S e (Original.a (2 ^ (k' + 1))) ^ j *
          wreathModelHom S e (Original.z (2 ^ (k' + 1))) := by
      rw [← map_pow, ← map_mul, Original.a_eq, element_base_pow, Original.z, element_base_mul]
      simp only [nsmul_eq_mul, mul_one, add_zero]
    have haZ : wreathModelHom S e (Original.a (2 ^ (k' + 1))) ^ j ∈ modelCenter S e :=
      (modelCenter S e).pow_mem ⟨_, Subgroup.mem_zpowers _, rfl⟩ j
    have hcen := Subgroup.mem_centralizer_iff.mp hh₀N _ haZ
    refine ⟨wreathModelHom S e (Original.a (2 ^ (k' + 1))) ^ j *
      wreathModelHom S e (Original.x2 (2 ^ (k' + 1))), ?_, ?_⟩
    · exact (modelBase S e).mul_mem
        ((modelBase S e).pow_mem ((mem_modelBase_iff S e _).mpr
          (by rw [Original.a_eq, element_mem_base])) j)
        (modelHom_x2_mem_modelBase S e)
    · have hgy' : IsConj g (wreathModelHom S e (element (2 ^ (k' + 1)) c d 1)) := by
        rw [hw]
        exact hgy
      refine hgy'.trans ((((wreathModelHom S e).map_isConj hconj).trans ?_))
      rw [haj]
      refine isConj_iff.mpr ⟨h₀⁻¹, ?_⟩
      rw [inv_inv, ← hh₀]
      calc
        h₀⁻¹ * (wreathModelHom S e (Original.a (2 ^ (k' + 1))) ^ j *
            wreathModelHom S e (Original.z (2 ^ (k' + 1)))) * h₀ =
          (h₀⁻¹ * wreathModelHom S e (Original.a (2 ^ (k' + 1))) ^ j * h₀) *
            (h₀⁻¹ * wreathModelHom S e (Original.z (2 ^ (k' + 1))) * h₀) := by group
        _ = _ := by
          rw [mul_assoc h₀⁻¹, hcen]
          group

theorem modelBase_sylow_centralizer_of_not_isConj (hn : 2 ≤ n) {μ : G}
    (hμ : μ ∈ modelBase S e) (hμZ : ¬ ∃ z ∈ modelCenter S e, IsConj μ z) :
    ∃ P : Sylow 2 (Subgroup.centralizer ({μ} : Set G)),
      (P : Subgroup _).map (Subgroup.centralizer ({μ} : Set G)).subtype = modelBase S e := by
  apply modelBase_sylow_of_forall S e _
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact modelBase_commute S e x μ hx hμ
  · intro k hk w hwS hwB hwC
    rw [Subgroup.mem_centralizer_singleton_iff] at hwC
    apply hμZ
    have hμ' : k⁻¹ * μ * k ∈ modelBase S e := (Subgroup.mem_normalizer_iff''.mp hk μ).mp hμ
    have hcomm : (k⁻¹ * μ * k) * w = w * (k⁻¹ * μ * k) := by
      calc
        (k⁻¹ * μ * k) * w = k⁻¹ * (μ * (k * w * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * w * k⁻¹) * μ) * k := by rw [hwC]
        _ = w * (k⁻¹ * μ * k) := by group
    refine ⟨k⁻¹ * μ * k,
      mem_modelCenter_of_commute_outside S e (by omega) hμ' hwS hwB hcomm, ?_⟩
    exact isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]⟩

end CFSG.Wreathed.BrauerWong
