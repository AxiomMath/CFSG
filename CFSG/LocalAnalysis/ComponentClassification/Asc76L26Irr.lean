module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender

section Def

variable {X : Type*} [Group X]

@[expose] def IrrAt (T : Subgroup X) : Prop :=
  ∀ A : Subgroup X, sylowCenter T ≤ A → A ≤ T →
    (∀ n ∈ normalizer (T : Set X), ∀ a ∈ A, n⁻¹ * a * n ∈ A) → ¬ A ≤ sylowCenter T → A = T

theorem mem_sylowCenter_map {X' : Type*} [Group X'] (e : X ≃* X') (T : Subgroup X) (x : X) :
    e x ∈ sylowCenter (T.map e.toMonoidHom) ↔ x ∈ sylowCenter T := by
  have hT : ∀ y : X, e y ∈ T.map e.toMonoidHom ↔ y ∈ T := fun y => by
    rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [mem_sylowCenter, mem_sylowCenter, hT]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun t ht => e.injective ?_⟩
    rw [map_mul, map_mul]
    exact hc (e t) ((hT t).mpr ht)
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun t' ht' => ?_⟩
    obtain ⟨t, rfl⟩ := e.surjective t'
    rw [← map_mul, ← map_mul, hc t ((hT t).mp ht')]

theorem IrrAt.map {X' : Type*} [Group X'] {T : Subgroup X} (h : IrrAt T) (e : X ≃* X') :
    IrrAt (T.map e.toMonoidHom) := by
  intro B hZB hBT hN hBZ
  set A := B.map e.symm.toMonoidHom with hA
  have hmemA : ∀ x : X, x ∈ A ↔ e x ∈ B := fun x => by
    rw [hA, mem_map_equiv, MulEquiv.symm_symm]
  have hmemT : ∀ x : X, e x ∈ T.map e.toMonoidHom ↔ x ∈ T := fun x => by
    rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  have hAT : A = T := by
    refine h A (fun z hz => ?_) (fun x hx => ?_) (fun n hn a ha => ?_) (fun hle => hBZ ?_)
    · rw [hmemA]
      exact hZB ((mem_sylowCenter_map e T z).mpr hz)
    · rw [hmemA] at hx
      exact (hmemT x).mp (hBT hx)
    · rw [hmemA] at ha ⊢
      have hn' : e n ∈ normalizer ((T.map e.toMonoidHom : Subgroup X') : Set X') := by
        rw [← map_equiv_normalizer_eq]
        exact ⟨n, hn, rfl⟩
      have := hN (e n) hn' (e a) ha
      simpa only [map_mul, map_inv] using this
    · intro y hy
      obtain ⟨x, rfl⟩ := e.surjective y
      exact (mem_sylowCenter_map e T x).mpr (hle ((hmemA x).mpr hy))
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← hmemA, hAT, hmemT]

theorem irrAt_of_one_sylow [Finite X] (R : Sylow 2 X) (h : IrrAt (R : Subgroup X))
    (T : Sylow 2 X) : IrrAt (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R T
  have hT : (T : Subgroup X) = (R : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map (MulAut.conj g)

theorem irrAt_of_mulEquiv [Finite X] {X' : Type*} [Group X'] (e : X ≃* X')
    (hX' : ∀ T : Sylow 2 X', IrrAt (T : Subgroup X')) (T : Sylow 2 X) :
    IrrAt (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X' := Finite.of_equiv X e.toEquiv
  have h := (hX' (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map e.symm
  have h' : IrrAt (((T : Subgroup X).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

end Def

section Suzuki

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

theorem irrAt_rootSub (m : ℕ) (hm : 0 < m) : IrrAt (SuzukiAut.rootSub m) := by
  intro A hZA hAR hN hAZ
  obtain ⟨x, hxA, hxZ⟩ := Set.not_subset.mp hAZ
  obtain ⟨a₀, b₀, rfl⟩ := (SuzukiAut.mem_rootSub m).mp (hAR hxA)
  have ha₀ : a₀ ≠ 0 := by
    rintro rfl
    exact hxZ ((SuzukiAut.mem_sylowCenter_rootSub m hm).mpr ⟨b₀, rfl⟩)
  refine le_antisymm hAR fun t ht => ?_
  obtain ⟨a, b, rfl⟩ := (SuzukiAut.mem_rootSub m).mp ht
  by_cases ha : a = 0
  · subst ha
    exact hZA ((SuzukiAut.mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩)
  set u : (BinaryGaloisField (2 * m + 1))ˣ := Units.mk0 (a / a₀) (div_ne_zero ha ha₀) with hu
  have hn : (SuzukiAut.torus m u)⁻¹ ∈
      normalizer ((SuzukiAut.rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _) :=
    inv_mem (SuzukiAut.torusSub_le_normalizer m (SuzukiAut.torus_mem m u))
  have h1 := hN _ hn _ hxA
  rw [inv_inv, SuzukiAut.torus_conj_root] at h1
  have hua : (u : BinaryGaloisField (2 * m + 1)) * a₀ = a := div_mul_cancel₀ a ha₀
  rw [hua] at h1
  set β := (u : BinaryGaloisField (2 * m + 1)) * SuzukiAut.tits m u * b₀ with hβ
  have h2 : SuzukiAut.root m 0 (b - β) ∈ A :=
    hZA ((SuzukiAut.mem_sylowCenter_rootSub m hm).mpr ⟨_, rfl⟩)
  have h3 := A.mul_mem h1 h2
  rw [SuzukiAut.root_mul m hm, map_zero, mul_zero, add_zero, add_zero] at h3
  convert h3 using 2
  ring

theorem irrAt_of_mulEquiv_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (T : Sylow 2 X) : IrrAt (T : Subgroup X) := by
  let e' : X ≃* SuzukiMatrixGroup a := e.trans (SuzukiAut.suzukiEquiv a).symm
  have : Finite (SuzukiMatrixGroup a) := Finite.of_equiv X e'.toEquiv
  obtain ⟨S, hS⟩ := SuzukiAut.exists_sylow_eq_rootSub a (by omega)
  refine irrAt_of_mulEquiv e' (irrAt_of_one_sylow S ?_) T
  rw [hS]
  exact irrAt_rootSub a (by omega)

end Suzuki

section Unitary

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem le_card_scalarImage (J : HermitianForm 3 K) (q : ℕ) (hq : 4 ≤ q)
    (hKcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    q ≤ Nat.card (unitaryCoverScalarImage J) := by
  rw [unitaryCoverScalarImage_card J q hKcard hfixed hJ]
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q + 1))
  have hg0 : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  calc q ≤ (q ^ 2 - 1) / 3 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        have : 4 * q ≤ q * q := Nat.mul_le_mul_right q hq
        have : q * 3 + 1 ≤ q ^ 2 := by nlinarith
        omega
    _ ≤ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := Nat.div_le_div_left hg hg0

theorem irrAt_root (J : HermitianForm 3 K) (q : ℕ) (hq : 4 ≤ q) (hKcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : IrrAt (unitaryCoverRoot J hJ) := by
  classical
  set U := hermitianUnipotentPSU J hJ with hU
  intro A hZA hAR hN hAZ
  obtain ⟨x, hxA, hxZ⟩ := Set.not_subset.mp hAZ
  obtain ⟨z, rfl⟩ := hAR hxA
  have hz : z.1.1 ≠ 0 := fun h =>
    hxZ ((UnitaryAut.mem_sylowCenter_root J q hKcard hfixed (by omega) hJ z).mpr h)
  set W : Set K := {v | ∃ w : hermitianUnipotentCoord J, U w ∈ A ∧ w.1.1 = v} with hW
  have hW0 : (0 : K) ∈ W := ⟨1, by rw [map_one]; exact one_mem _, rfl⟩
  have hWadd : ∀ v ∈ W, ∀ v' ∈ W, v + v' ∈ W := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    exact ⟨w * w', by rw [map_mul]; exact A.mul_mem hw hw', rfl⟩
  have hWneg : ∀ v ∈ W, -v ∈ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w⁻¹, by rw [map_inv]; exact A.inv_mem hw, rfl⟩
  have hWtorus : ∀ v ∈ W, ∀ k : Kˣ, v * (unitaryCoverScalar J k : K) ∈ W := by
    rintro _ ⟨w, hw, rfl⟩ k
    refine ⟨hermitianTorusAction J k w, ?_, UnitaryCoord.hermitianTorusAction_fst_eq J k w⟩
    have hn : (hermitianTorusPSU J hJ k)⁻¹ ∈
        normalizer ((unitaryCoverRoot J hJ : Subgroup _) : Set _) :=
      inv_mem (unitaryCoverTorus_le_normalizer J hJ ⟨k, rfl⟩)
    have := hN _ hn _ hw
    rwa [inv_inv, unitaryCoverTorus_conj_root] at this
  set M : Set K := {s | ∀ v ∈ W, v * s ∈ W} with hM
  have hMmul : ∀ s ∈ M, ∀ t ∈ M, s * t ∈ M := fun s hs t ht v hv => by
    rw [← mul_assoc]
    exact ht _ (hs v hv)
  have hMone : (1 : K) ∈ M := fun v hv => by rw [mul_one]; exact hv
  have hMpow : ∀ s ∈ M, ∀ n : ℕ, s ^ n ∈ M := by
    intro s hs n
    induction n with
    | zero => rw [pow_zero]; exact hMone
    | succ n ih => rw [pow_succ]; exact hMmul _ ih _ hs
  have : Fintype K := Fintype.ofFinite K
  have hcardK : 2 ≤ Fintype.card K := by
    rw [Fintype.card_eq_nat_card, hKcard]
    nlinarith
  let Q : Subfield K :=
    { carrier := M
      mul_mem' := fun {s t} hs ht => hMmul s hs t ht
      one_mem' := hMone
      add_mem' := fun {s t} hs ht v hv => by
        rw [mul_add]
        exact hWadd _ (hs v hv) _ (ht v hv)
      zero_mem' := fun v _ => by rw [mul_zero]; exact hW0
      neg_mem' := fun {s} hs v hv => by
        rw [mul_neg]
        exact hWneg _ (hs v hv)
      inv_mem' := fun s hs => by
        by_cases hs0 : s = 0
        · rw [hs0, inv_zero]
          exact fun v _ => by rw [mul_zero]; exact hW0
        · have h1 : s * s ^ (Fintype.card K - 2) = 1 := by
            rw [← pow_succ', show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega]
            exact FiniteField.pow_card_sub_one_eq_one s hs0
          change s⁻¹ ∈ M
          rw [inv_eq_of_mul_eq_one_right h1]
          exact hMpow s hs _ }
  have hQcard : q + 1 ≤ Nat.card Q := by
    let ι : Option (unitaryCoverScalarImage J) → Q := fun o => match o with
      | none => 0
      | some s => ⟨((s : Kˣ) : K), by
          obtain ⟨k, hk⟩ := s.2
          change ∀ v ∈ W, v * ((s : Kˣ) : K) ∈ W
          intro v hv
          rw [← hk]
          exact hWtorus v hv k⟩
    have hι : Function.Injective ι := by
      rintro (_ | s) (_ | s') h
      · rfl
      · exfalso
        have h' := congrArg Subtype.val h
        exact (Units.ne_zero (s' : Kˣ)) h'.symm
      · exfalso
        have h' := congrArg Subtype.val h
        exact (Units.ne_zero (s : Kˣ)) h'
      · have h' : ((s : Kˣ) : K) = ((s' : Kˣ) : K) := congrArg Subtype.val h
        rw [Subtype.ext (Units.ext h')]
    have h1 := Nat.card_le_card_of_injective ι hι
    rw [Finite.card_option] at h1
    have h2 := le_card_scalarImage J q hq hKcard hfixed hJ
    omega
  have hQtop : ∀ s : K, s ∈ Q := by
    have hfin := Module.natCard_eq_pow_finrank (K := Q) (V := K)
    rw [hKcard] at hfin
    set n := Module.finrank Q K with hn
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · rw [pow_zero] at hfin
          nlinarith
        · rfl
      · exfalso
        have : (q + 1) ^ 2 ≤ Nat.card Q ^ n :=
          (Nat.pow_le_pow_left hQcard 2).trans (Nat.pow_le_pow_right (by omega) h)
        nlinarith
    rw [hn1, pow_one] at hfin
    have hbij : Function.Bijective (Subtype.val : Q → K) := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨Subtype.val_injective, ?_⟩
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, ← hfin, hKcard]
    intro s
    obtain ⟨⟨t, ht⟩, rfl⟩ := hbij.2 s
    exact ht
  have hzW : z.1.1 ∈ W := ⟨z, hxA, rfl⟩
  refine le_antisymm hAR ?_
  rintro _ ⟨w, rfl⟩
  have hsW : z.1.1 * (w.1.1 / z.1.1) ∈ W := hQtop (w.1.1 / z.1.1) _ hzW
  rw [mul_div_cancel₀ _ hz] at hsW
  obtain ⟨w', hw'A, hw'⟩ := hsW
  have h0 : (w'⁻¹ * w).1.1 = 0 := by
    change -w'.1.1 + w.1.1 = 0
    rw [hw']
    ring
  have hc : U (w'⁻¹ * w) ∈ A := hZA (UnitaryAut.mem_sylowCenter_root_of_fst J hJ h0)
  have := A.mul_mem hw'A hc
  rwa [← map_mul, mul_inv_cancel_left] at this

theorem irrAt_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (T : Sylow 2 X) : IrrAt (T : Subgroup X) := by
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, ⟨e'⟩⟩ :=
    Asc76X.exists_mulEquiv_hermitian_of_mulEquiv_psu3 hf e
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv X e'.toEquiv
  obtain ⟨S, hS⟩ := UnitaryAut.exists_sylow_eq_root J f hf hKcard hfixed hJ
  refine irrAt_of_mulEquiv e' (irrAt_of_one_sylow S ?_) T
  rw [hS]
  have hq : 4 ≤ 2 ^ f :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf)
  exact irrAt_root J (2 ^ f) hq hKcard hfixed hJ

end Unitary

theorem irrAt_of_isSzOrU3 {X : Type*} [Group X] [Finite X] (hX : IsSzOrU3 X) (T : Sylow 2 X) :
    IrrAt (T : Subgroup X) := by
  rcases hX with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · exact irrAt_of_mulEquiv_sz ha e T
  · exact irrAt_of_mulEquiv_psu3 hf e T

end CFSG.ComponentClassification.Asc76.L26
