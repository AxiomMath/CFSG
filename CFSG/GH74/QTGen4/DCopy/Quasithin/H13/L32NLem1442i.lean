module

public import CFSG.Quasithin.H13.L32NLem1442i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442e

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Mat8Cert L1442M

namespace L1442

private theorem s7_span_facts :
    ∀ i : Fin 8, ∃ j : Fin 2, ∃ n : Fin 256,
      mv8 ((Mat8Cert.colsOf ((if j = 0 then s7g0 else s7g1 : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)))) n ^^^ n = 2 ^ (i : ℕ) := by
  decide +kernel

end L1442

namespace L1442

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L1442.Ctx_F4

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx_F4 G T L V V₂ g a D)
include C

theorem case4_of_concl8_F4
    (h12213 : Stmt12_2_13_F4)
    (h8 : G112Concl8 D.B (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    Case1442Four T V V₂ g D := by
  classical
  have hB := C.g111.toG101Hyp
  have h8' := h8
  obtain ⟨hd8, ⟨φ⟩, I, hI4, hIiso, hIinv, x, hxX, ⟨v₀, hv₀I, hxv₀⟩, hcompl⟩ := h8
  set Γ := D.img (l32nH T V) with hΓ
  set X := D.img (CFSG.conjugate (l32nW T V V₂) g) with hX
  have hxΓ : x ∈ Γ := C.X_le_F4 hxX
  have hxx : x * x = 1 := hB.X_sq x hxX
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hxx).symm
  have hxxv : ∀ w, x (x w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, hxx]
    rfl

  have hX8 : Nat.card X = 2 ^ 3 := by
    obtain ⟨k, hk⟩ := C.exists_card_X_F4
    have hlt : ¬ 16 ≤ Nat.card X := fun h16 =>
      L14324.false_of_concl8 C.X_le_F4 hB.X_sq hk h16 h8'
    have hlow := C.lower_F4
    rw [hd8] at hlow
    rw [hk] at hlt hlow ⊢
    have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hlow)
    have hk4 : k < 4 := by
      by_contra h4
      exact hlt (by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ k by omega)
        simpa using this)
    rw [show k = 3 by omega]

  obtain ⟨A₀, hA₀n, hA₀c, hA₀o⟩ := perm7_normal_data φ
  set A : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := A₀.map Γ.subtype with hA
  have hAΓ : A ≤ Γ := Subgroup.map_subtype_le A₀
  have hAI : ∀ a' ∈ A, ∀ i ∈ I, a' i ∈ I := by
    rintro _ ⟨a₀, ha₀, rfl⟩ i hi
    have hlay : a₀ ∈ genFittingLayer ↥Γ := (le_sSup hA₀c : A₀ ≤ genFittingLayer ↥Γ) ha₀
    exact hIinv _ ⟨a₀, hlay, rfl⟩ i hi
  have hxA : x ∉ A := fun hx => hxv₀ (hAI x hx v₀ hv₀I)
  have houter : ∀ γ ∈ Γ, γ ∉ A → ∃ a' ∈ A, γ = a' * x := by
    intro γ hγ hγA
    have hγ' : (⟨γ, hγ⟩ : ↥Γ) ∉ A₀ := fun h => hγA ⟨_, h, rfl⟩
    have hx' : (⟨x, hxΓ⟩ : ↥Γ) ∉ A₀ := fun h => hxA ⟨_, h, rfl⟩
    have h1 := hA₀o _ _ hγ' hx'
    refine ⟨γ * x⁻¹, ⟨_, h1, rfl⟩, by group⟩

  set I' : Submodule (ZMod 2) D.V := I.map (x : D.V →ₗ[ZMod 2] D.V) with hI'
  have hxI : ∀ i ∈ I, x i ∈ I' := fun i hi => ⟨i, hi, rfl⟩
  have hxI' : ∀ j ∈ I', x j ∈ I := by
    rintro _ ⟨i, hi, rfl⟩
    rw [LinearEquiv.coe_coe, hxxv]
    exact hi
  have hAI' : ∀ a' ∈ A, ∀ j ∈ I', a' j ∈ I' := by
    rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨i, hi, rfl⟩
    have hc : (⟨x, hxΓ⟩ : ↥Γ) * a₀ * (⟨x, hxΓ⟩ : ↥Γ)⁻¹ ∈ A₀ := hA₀n.conj_mem a₀ ha₀ _
    have hcA : x * (a₀ : D.V ≃ₗ[ZMod 2] D.V) * x ∈ A := by
      refine ⟨_, hc, ?_⟩
      simp [hxinv]
    refine ⟨(x * (a₀ : D.V ≃ₗ[ZMod 2] D.V) * x) i, hAI _ hcA i hi, ?_⟩
    simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, Subgroup.coe_subtype, hxxv]

  have F : S8Tr.Frame D.B I I' :=
    { alt := hB.alt
      nd := hB.nondegenerate
      compl := hcompl
      iso := hIiso
      iso' := by
        rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
        exact (hB.isometry x hxΓ i i').trans (hIiso i hi i' hi')
      rank := hI4
      rank' := by rw [hI', LinearEquiv.finrank_map_eq, hI4] }
  let bI : Module.Basis (Fin 4) (ZMod 2) I := Module.finBasisOfFinrankEq (ZMod 2) I hI4
  obtain ⟨d, hd, hbd⟩ := F.exists_dual bI
  set e₀ := F.coord bI hd hbd with he₀

  have hAs8 : ∀ a' ∈ A, L14411.matOf e₀ a' ∈ s8 := by
    intro a' ha'
    obtain ⟨hdet, hmat⟩ := F.matOf_eq_blk bI hd hbd (hB.isometry a' (hAΓ ha')) (hAI a' ha')
      (hAI' a' ha')
    obtain ⟨u, hu, hu'⟩ := S8Cert.blk_mem_s8 _ hdet
    have : L14411.matOf e₀ a' = u := Units.ext (hmat.trans hu'.symm)
    rw [this]
    exact hu
  have hxs8 : L14411.matOf e₀ x ∈ s8 := by
    obtain ⟨hdet, hmat⟩ := F.matOf_eq_blk_tau bI hd hbd (hB.isometry x hxΓ) hxI hxI'
    obtain ⟨u, hu, hu'⟩ := S8Cert.blk_mem_s8 _ hdet
    have : L14411.matOf e₀ x = u * s8g4 := Units.ext (by rw [hmat, Units.val_mul, hu'])
    rw [this]
    exact mul_mem hu S8Cert.s8g4_mem
  have hΓs8 : ∀ γ ∈ Γ, L14411.matOf e₀ γ ∈ s8 := by
    intro γ hγ
    by_cases hγA : γ ∈ A
    · exact hAs8 γ hγA
    · obtain ⟨a', ha', rfl⟩ := houter γ hγ hγA
      rw [map_mul]
      exact mul_mem (hAs8 a' ha') hxs8

  set Y := Γ.map (L14411.matOf e₀) with hY
  have hYs8 : Y ≤ s8 := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hΓs8 γ hγ
  let ψ : ↥Γ ≃* ↥Y := Γ.equivMapOfInjective _ (L14411.matOf_injective e₀)
  obtain ⟨m, hm, hmY⟩ := S7Conj.exists_conj_s7 hYs8 (φ.symm.trans ψ)
  set e₁ := e₀.trans (L14411.linOf m) with he₁
  have he₁v : ∀ v, e₁ v = (m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e₀ v) := fun v => rfl
  have hΓs7 : ∀ γ ∈ Γ, L14411.matOf e₁ γ ∈ s7 := by
    intro γ hγ
    rw [he₁, L14411.matOf_trans]
    exact hmY _ ⟨γ, hγ, rfl⟩
  have himg : Γ.map (L14411.matOf e₁) = s7 := by
    refine Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨γ, hγ, rfl⟩; exact hΓs7 γ hγ) ?_
    rw [S7Cert.card_s7, Subgroup.card_map_of_injective (L14411.matOf_injective e₁),
      Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    decide

  obtain ⟨q, hqU, hqB, hqΓ⟩ := C.exists_quad_F4 h12213
  have hBe₁ : ∀ v w, D.B v w = b4V (e₁ v) (e₁ w) := by
    intro v w
    rw [F.B_eq_b4V bI hd hbd v w, he₁v, he₁v, S8Cert.b4V_s8 hm]
  set lam : (Fin 8 → ZMod 2) → ZMod 2 := fun y => q (e₁.symm y) + q4V y with hlam
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hadd : ∀ y z, lam (y + z) = lam y + lam z := by
    intro y z
    simp only [hlam]
    rw [map_add, hqB, hBe₁, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [b4V]
    linear_combination (q4V (y + z)) * h2
  have hinv : ∀ γ ∈ s7, ∀ y, lam ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec y) = lam y := by
    intro γ hγ y
    rw [← himg] at hγ
    obtain ⟨ψ', hψ', rfl⟩ := hγ
    simp only [hlam]
    rw [S8Cert.q4V_s8 (S7Conj.s7_le_s8 (hΓs7 ψ' hψ')), L14411.matOf_mulVec',
      LinearEquiv.symm_apply_apply, hqΓ ψ' hψ']
  have hlam0 : lam 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    have key : ∀ c : ZMod 2, c = c + c → c = 0 := by decide
    exact key _ this
  have hsingle : ∀ i : Fin 8, lam (Pi.single i 1) = 0 := by
    intro i
    obtain ⟨j, n, hjn⟩ := s7_span_facts i
    set γ : GL (Fin 8) (ZMod 2) := if j = 0 then s7g0 else s7g1 with hγ
    have hγs7 : γ ∈ s7 := by
      rw [hγ]
      split_ifs
      · exact S7Conj.s7g0_mem_s7
      · exact Subgroup.subset_closure (by simp)
    have hvec : Pi.single i (1 : ZMod 2) =
        (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 n) + vec8 n := by
      rw [← dec8_colsOf (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)), dec8_mulVec, ← vec8_xor, hjn]
      ext k
      fin_cases i <;> fin_cases k <;> rfl
    rw [hvec, hadd, hinv γ hγs7]
    have key : ∀ c : ZMod 2, c + c = 0 := by decide
    exact key _
  have hlamall : ∀ y, lam y = 0 := by
    intro y
    have hsum : ∀ (s : Finset (Fin 8)), lam (∑ i ∈ s, y i • Pi.single i (1 : ZMod 2)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hlam0
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, hadd, ih, add_zero]
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (y i) with h | h
        · rw [h, zero_smul, hlam0]
        · rw [h, one_smul, hsingle]
    rw [pi_eq_sum_univ' y]
    exact hsum _
  have hq4 : ∀ v, q v = quadOf q4 (e₁ v) := by
    intro v
    have h1 := hlamall (e₁ v)
    simp only [hlam, LinearEquiv.symm_apply_apply] at h1
    rw [L14411.quadOf_q4]
    have key : ∀ c c' : ZMod 2, c + c' = 0 → c = c' := by decide
    exact key _ _ h1

  refine ⟨e₁, ⟨fun u hu => ?_, fun φ' => ?_⟩, hX8, ?_⟩
  · rw [← hq4, hqU u hu, sq]
  · constructor
    · intro hφ'
      exact ⟨L14411.matOf e₁ φ', hΓs7 φ' hφ', fun v => (L14411.matOf_mulVec e₁ φ' v).symm⟩
    · rintro ⟨γ, hγ, hγv⟩
      rw [← himg] at hγ
      obtain ⟨ψ', hψ', rfl⟩ := hγ
      have : φ' = ψ' := L14411.matOf_injective e₁ ((L14411.matOf_eq_iff e₁ φ' _).mpr hγv)
      rw [this]
      exact hψ'
  ·
    have he₀I : ∀ i ∈ I, S8Cert.InI (e₀ i) := by
      intro i hi
      have h0 : ∀ k : Fin 4, e₀ i (Fin.natAdd 4 k) = 0 := by
        intro k
        rw [he₀, F.coord_apply, Function.comp_apply, S8Tr.e8, finSumFinEquiv_symm_apply_natAdd]
        exact F.iso _ (bI k).2 _ hi
      exact ⟨h0 0, h0 1, h0 2, h0 3⟩
    have he₀I' : ∀ j ∈ I', S8Cert.InIs (e₀ j) := by
      intro j hj
      have h0 : ∀ k : Fin 4, e₀ j (Fin.castAdd 4 k) = 0 := by
        intro k
        rw [he₀, F.coord_apply, Function.comp_apply, S8Tr.e8, finSumFinEquiv_symm_apply_castAdd]
        exact F.iso' _ hj _ (hd k)
      exact ⟨h0 0, h0 1, h0 2, h0 3⟩
    have hv₀ne : v₀ ≠ 0 := fun h => hxv₀ (by rw [h, map_zero]; exact I.zero_mem)
    have hne : ∀ v, v ≠ 0 → e₁ v ≠ 0 := fun v hv h => hv (e₁.injective (h.trans e₁.map_zero.symm))
    have hInIadd : ∀ v w, S8Cert.InI v → S8Cert.InI w → S8Cert.InI (v + w) :=
      fun _ _ => S8Cert.inI_add
    have hInIsadd : ∀ v w, S8Cert.InIs v → S8Cert.InIs w → S8Cert.InIs (v + w) :=
      fun _ _ => S8Cert.inIs_add
    rcases S8Cert.subI_cases hm with hcase | hcase
    ·
      have hcase' : ∀ v, S8Cert.InIs v →
          S8Cert.InIs ((m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
        rcases S8Cert.subIs_cases hm with h | h
        · exact (S8Cert.not_both hInIadd ⟨_, S8Cert.not_inI_single⟩ hcase h).elim
        · exact h
      refine ⟨x, hxX, v₀, ?_, ?_⟩
      · rw [← S8Cert.inI_iff_mem_subI, he₁v]
        exact hcase _ (he₀I v₀ hv₀I)
      · intro hmem
        rw [← S8Cert.inI_iff_mem_subI, he₁v] at hmem
        have h1 := hcase' _ (he₀I' _ (hxI v₀ hv₀I))
        have h0 := S8Cert.eq_zero_of_inI_inIs hmem h1
        rw [← he₁v] at h0
        exact hne _ (fun h => hv₀ne (by rw [← hxxv v₀, h, map_zero])) h0
    ·
      have hcase' : ∀ v, S8Cert.InIs v →
          S8Cert.InI ((m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
        rcases S8Cert.subIs_cases hm with h | h
        · exact h
        · exact (S8Cert.not_both hInIsadd ⟨_, S8Cert.not_inIs_single⟩ hcase h).elim
      refine ⟨x, hxX, x v₀, ?_, ?_⟩
      · rw [← S8Cert.inI_iff_mem_subI, he₁v]
        exact hcase' _ (he₀I' _ (hxI v₀ hv₀I))
      · intro hmem
        rw [hxxv, ← S8Cert.inI_iff_mem_subI, he₁v] at hmem
        have h1 := hcase _ (he₀I v₀ hv₀I)
        have h0 := S8Cert.eq_zero_of_inI_inIs hmem h1
        rw [← he₁v] at h0
        exact hne _ hv₀ne h0

end Ctx_F4

end L1442

end CFSG.Quasithin.H13
