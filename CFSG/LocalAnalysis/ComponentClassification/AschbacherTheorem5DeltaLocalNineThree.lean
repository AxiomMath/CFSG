module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineWeak
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineConj

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem rightConjugate_orbitProduct_le (hC : Counterexample G D r Abar) (g : G) {y : G}
    (hyH : y ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) {m k : Fin r}
    (hmk : rightConjugate (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
      y = aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k)) :
    rightConjugate (orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m}) y ≤
      orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ k} := by
  have hC' := hC.conj g
  change (orbitProduct _ _ _).map (MulAut.conj y⁻¹).toMonoidHom ≤ _
  rw [orbitProduct, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hj => ?_
  obtain ⟨j', hj'⟩ := hC'.hyp.hperm y⁻¹ (Subgroup.inv_mem _ hyH) j
  rw [hj']
  refine factor_le_orbitProduct (I := {j | j ≠ k}) fun hjk => hj ?_
  rw [hjk] at hj'
  apply SixTools.index_eq_of_preimage_eq hC'.hyp
  exact Subgroup.map_injective (f := (MulAut.conj y⁻¹).toMonoidHom) (MulAut.conj y⁻¹).injective
    (hj'.trans hmk.symm)

theorem part_three (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) {a m : Fin r}
    {X S T : Subgroup G} (hX2 : IsPGroup 2 X) (hXH : X ≤ Subgroup.normalizer (D : Set G))
    (hTX : T ≤ X) (hTXne : T ≠ X)
    (hXm : X ≤ orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m})
    (hXA : X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hY : ∀ j, j ≠ m → ∃ Y : Subgroup G, Y ≤ X ∧
      Y ≤ rightConjugate (aschbacherThm5Preimage D (Abar j)) g ∧
      ¬ Y ≤ rightConjugate (factorZStar D Abar j) g)
    (hS : IsSylowOf 2 S (aschbacherThm5Preimage D (Abar a))) (hST : Nat.card S ≤ Nat.card T)
    (hXS : ∀ x ∈ X, ∀ s ∈ S, x * s = s * x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set D' := rightConjugate D g with hD'def
  set Abar' := conjFactors D Abar g with hAbar'def
  have hC' : Counterexample G D' r Abar' := hC.conj g
  have hg : g ∉ Subgroup.normalizer (D : Set G) := by
    obtain ⟨-, -, hne, -⟩ := hΔ
    exact fun h => hne ((rightConjugate_eq_self_iff _ g).mpr (Subgroup.le_normalizer h))
  have hH' : Subgroup.normalizer (D' : Set G) =
      rightConjugate (Subgroup.normalizer (D : Set G)) g := normalizer_rightConjugate D g
  have hTlt : Nat.card T < Nat.card X := lt_of_le_of_ne (Subgroup.card_le_of_le hTX)
    fun h => hTXne (Subgroup.eq_of_le_of_card_ge hTX (le_of_eq h.symm))
  have hX1 : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hTlt
    have := Nat.card_pos (α := T)
    omega
  have hXAbot : X ⊓ A = ⊥ := inf_orbitProduct_eq_bot hC hg hX2 hXm
  have hSX : S ≤ Subgroup.normalizer (X : Set G) := by
    refine le_trans (fun s hs => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => hXS x hx s hs
  have hcm := orbitProduct_le_centralizing hC'.hyp.hcomm (j := m) (I := {j | j ≠ m}) (by simp)
  obtain ⟨y, hyA, hXy, hXyne⟩ := exists_weak hC hg hX2 hXH hX1 hXm hXA hS hXS
  have hphi : ∀ x ∈ X, x⁻¹ * (y⁻¹ * x * y) ∈ S := by
    intro x hx
    have hmem : y⁻¹ * x * y ∈ ((X ⊔ S : Subgroup G) : Set G) :=
      hXy (AschbacherTheorem3.conj_mem_rightConjugate hx y)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X S hSX] at hmem
    obtain ⟨x₁, hx₁, s, hs, hxs⟩ := Set.mem_mul.mp hmem
    have hcomA : x⁻¹ * (y⁻¹ * x * y) ∈ A := by
      have h1 : x⁻¹ * y⁻¹ * x⁻¹⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXA hx)) y⁻¹).mp (A.inv_mem hyA)
      rw [inv_inv] at h1
      have := A.mul_mem h1 hyA
      simpa [mul_assoc] using this
    have hxx₁ : x⁻¹ * x₁ ∈ X ⊓ A := by
      refine ⟨X.mul_mem (X.inv_mem hx) hx₁, ?_⟩
      have := A.mul_mem hcomA (A.inv_mem (hS.le hs))
      rw [← hxs] at this
      simpa [mul_assoc] using this
    rw [hXAbot, Subgroup.mem_bot, inv_mul_eq_one] at hxx₁
    rw [← hxs, ← hxx₁]
    simpa using hs
  by_cases hyHg : y ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g
  ·
    have hyH' : y ∈ Subgroup.normalizer (D' : Set G) := by rw [hH']; exact hyHg
    have hπ : ∀ j : Fin r, ∃ j', rightConjugate (aschbacherThm5Preimage D' (Abar' j)) y =
        aschbacherThm5Preimage D' (Abar' j') := fun j =>
      hC'.hyp.hperm y⁻¹ (Subgroup.inv_mem _ hyH') j
    obtain ⟨k, hk⟩ := hπ m
    have hXyk : rightConjugate X y ≤ orbitProduct D' Abar' {j | j ≠ k} :=
      (AschbacherTheorem3.rightConjugate_le_rightConjugate hXm y).trans
        (rightConjugate_orbitProduct_le hC g hyH' hk)
    have hSk : ∀ s ∈ S, s ∈ orbitProduct D' Abar' {j | j ≠ k} → s = 1 := by
      intro s hs hsk
      have h1 := inf_orbitProduct_eq_bot hC hg (a := a) (m := k)
        (hS.isPGroup.to_le inf_le_left : IsPGroup 2 (S ⊓ orbitProduct D' Abar' {j | j ≠ k} :
          Subgroup G)) inf_le_right
      have h2 : s ∈ (S ⊓ orbitProduct D' Abar' {j | j ≠ k}) ⊓ A := ⟨⟨hs, hsk⟩, hS.le hs⟩
      rw [h1] at h2
      exact Subgroup.mem_bot.mp h2
    have hkm : k ≠ m := by
      rintro rfl
      apply hXyne
      refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by rw [rightConjugate_card])
      have hz' : z ∈ ((X ⊔ S : Subgroup G) : Set G) := hXy hz
      rw [Subgroup.coe_mul_of_right_le_normalizer_left X S hSX] at hz'
      obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_mul.mp hz'
      have hsk : s ∈ orbitProduct D' Abar' {j | j ≠ k} := by
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXm hx)) (hXyk hz)
        simpa using this
      rw [hSk s hs hsk, mul_one]
      exact hx
    have hfix : ∀ j, j ≠ m → j ≠ k →
        rightConjugate (aschbacherThm5Preimage D' (Abar' j)) y =
          aschbacherThm5Preimage D' (Abar' j) := by
      intro j hjm hjk
      obtain ⟨Y, hYX, hYL, hYZ⟩ := hY j hjm
      have hYc : ∀ w ∈ Y, y⁻¹ * w * y = w := by
        intro w hw
        have hwk : w ∈ orbitProduct D' Abar' {j | j ≠ k} := by
          have : w ∈ aschbacherThm5Preimage D' (Abar' j) := by
            rw [preimage_conjFactors]
            exact hYL hw
          exact factor_le_orbitProduct (I := {j | j ≠ k}) hjk this
        have hw' : w⁻¹ * (y⁻¹ * w * y) ∈ orbitProduct D' Abar' {j | j ≠ k} :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hwk)
            (hXyk (AschbacherTheorem3.conj_mem_rightConjugate (hYX hw) y))
        have h1 := hSk _ (hphi w (hYX hw)) hw'
        rw [inv_mul_eq_one] at h1
        exact h1.symm
      obtain ⟨j', hj'⟩ := hπ j
      rw [hj']
      by_contra hne
      have hjj' : j' ≠ j := fun h => hne (by rw [h])
      apply hYZ
      intro w hw
      have hwj' : w ∈ aschbacherThm5Preimage D' (Abar' j') := by
        rw [← hj']
        have := AschbacherTheorem3.conj_mem_rightConjugate (hYL hw) y
        rw [← preimage_conjFactors] at this
        rwa [hYc w hw] at this
      rw [← factorZStar_conj]
      refine ⟨by rw [preimage_conjFactors]; exact hYL hw, ?_⟩
      exact factor_le_centralizing hC'.hyp.hcomm (Ne.symm hjj') hwj'
    obtain ⟨k', hk'⟩ := hπ k
    have hinj : ∀ {j₁ j₂ : Fin r}, rightConjugate (aschbacherThm5Preimage D' (Abar' j₁)) y =
        rightConjugate (aschbacherThm5Preimage D' (Abar' j₂)) y → j₁ = j₂ := fun h =>
      SixTools.index_eq_of_preimage_eq hC'.hyp (Subgroup.map_injective
        (f := (MulAut.conj y⁻¹).toMonoidHom) (MulAut.conj y⁻¹).injective h)
    have hk'm : k' = m := by
      by_contra hk'm
      by_cases hk'k : k' = k
      · rw [hk'k] at hk'
        exact hkm (hinj (hk.trans hk'.symm)).symm
      · have h1 := hfix k' hk'm hk'k
        exact hk'k (hinj (h1.trans hk'.symm))
    rw [hk'm] at hk'
    have hyy : rightConjugate (aschbacherThm5Preimage D' (Abar' m)) (y * y) =
        aschbacherThm5Preimage D' (Abar' m) := by
      rw [← rightConjugate_mul, hk, hk']
    obtain ⟨e, o, ho, hno⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    obtain ⟨t, rfl⟩ := ho
    have hpow : ∀ n : ℕ, rightConjugate (aschbacherThm5Preimage D' (Abar' m)) ((y * y) ^ n) =
        aschbacherThm5Preimage D' (Abar' m) := by
      intro n
      induction n with
      | zero => rw [pow_zero, rightConjugate_one]
      | succ n ih => rw [pow_succ, ← rightConjugate_mul, ih, hyy]
    have hyo : rightConjugate (aschbacherThm5Preimage D' (Abar' m)) (y ^ (2 * t + 1)) =
        aschbacherThm5Preimage D' (Abar' k) := by
      rw [pow_succ, pow_mul, ← rightConjugate_mul, sq, hpow, hk]
    have hy2 : (y ^ (2 * t + 1)) ^ (2 ^ e) = 1 := by
      rw [← pow_mul, mul_comm, ← hno, pow_orderOf_eq_one]
    have hyoA : y ^ (2 * t + 1) ∈ A := A.pow_mem hyA _
    have hyoHg : y ^ (2 * t + 1) ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g :=
      Subgroup.pow_mem _ hyHg _
    have hN := normalizes_conj_of_le h3 hin hC hΔ hr (i := a)
      (Five.isPGroup_zpowers_of_pow hy2) (Subgroup.zpowers_le.mpr hyoA)
      (Subgroup.zpowers_le.mpr hyoHg) m (Subgroup.mem_zpowers _)
    rw [← preimage_conjFactors D Abar g m] at hN
    rw [(rightConjugate_eq_self_iff _ _).mpr hN] at hyo
    exact hkm (SixTools.index_eq_of_preimage_eq hC'.hyp hyo.symm)
  ·
    have hinj : Function.Injective
        (fun x : X => (⟨(x : G)⁻¹ * (y⁻¹ * x * y), hphi x x.2⟩ : S)) := by
      intro x x' hxx'
      have h1 : (x : G)⁻¹ * (y⁻¹ * x * y) = (x' : G)⁻¹ * (y⁻¹ * x' * y) := congrArg Subtype.val hxx'
      set z : G := (x' : G) * (x : G)⁻¹ with hz
      have hzX : z ∈ X := X.mul_mem x'.2 (X.inv_mem x.2)
      have hzy : y⁻¹ * z * y = z := by
        rw [hz]
        calc y⁻¹ * ((x' : G) * (x : G)⁻¹) * y = (y⁻¹ * x' * y) * (y⁻¹ * x * y)⁻¹ := by group
          _ = (x' : G) * (x : G)⁻¹ := by
            have h2 : y⁻¹ * (x' : G) * y = x' * ((x : G)⁻¹ * (y⁻¹ * x * y)) := by
              rw [h1]
              group
            rw [h2]
            group
      by_contra hne
      have hz1 : z ≠ 1 := by
        intro h
        apply hne
        apply Subtype.ext
        have : (x' : G) = x := by
          calc (x' : G) = z * x := by rw [hz]; group
            _ = x := by rw [h, one_mul]
        exact this.symm
      obtain ⟨n, hn⟩ := hX2 ⟨z, hzX⟩
      apply hyHg
      have h := mem_normalizer_of_fusion hC' m m (t := z) (g := y)
        ⟨n, by simpa using congrArg Subtype.val hn⟩ hz1
        (centralizes_of_mem_centralizing (hcm (hXm hzX)))
        (by rw [hzy]; exact centralizes_of_mem_centralizing (hcm (hXm hzX)))
      rwa [hH'] at h
    have h1 := Nat.card_le_card_of_injective _ hinj
    omega

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
