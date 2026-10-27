module

public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.SectionRank.CatalogStep

public section

namespace CFSG.SectionRank

open CFSG.Open

theorem isCyclic_of_isPGroup_GL_four {k : Type} [Field k] [Fintype k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {r : ℕ} [hr : Fact r.Prime] (h0 : ¬ r ∣ Fintype.card k)
    (h1 : ¬ r ∣ Fintype.card k - 1) (h2 : ¬ r ∣ Fintype.card k ^ 2 - 1)
    (h3 : ¬ r ∣ Fintype.card k ^ 3 - 1) (P : Subgroup (GL (Fin 4) k)) (hP : IsPGroup r P) :
    IsCyclic P := by
  classical
  set q := Fintype.card k with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  let L := FiniteField.Extension k p 4
  have : Fintype L := Fintype.ofFinite L
  let b : Module.Basis (Fin 4) k L :=
    Module.finBasisOfFinrankEq k L (FiniteField.finrank_extension k p 4)
  let ψ : Lˣ →* GL (Fin 4) k := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => Units.ext
    (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  set S := ψ.range with hSdef
  have hScyc : IsCyclic S := isCyclic_of_surjective (MonoidHom.ofInjective hψ).toMonoidHom
    (MonoidHom.ofInjective hψ).surjective
  have hcardL : Fintype.card L = q ^ 4 := by
    rw [Module.card_eq_pow_finrank (K := k), FiniteField.finrank_extension k p 4]
  have hcardS : Nat.card S = q ^ 4 - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_units, Nat.card_eq_fintype_card,
      hcardL]
  have hGL : Nat.card (GL (Fin 4) k) =
      (q ^ 4 - 1) * ((q ^ 4 - q) * (q ^ 4 - q ^ 2) * (q ^ 4 - q ^ 3)) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]
    ring
  have hfac : ∀ i, i ≤ 3 → q ^ 4 - q ^ i = q ^ i * (q ^ (4 - i) - 1) := by
    intro i hi
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hcopM : Nat.Coprime r ((q ^ 4 - q) * (q ^ 4 - q ^ 2) * (q ^ 4 - q ^ 3)) := by
    have hcq : ∀ i, Nat.Coprime r (q ^ i) := fun i =>
      Nat.Coprime.pow_right i ((Nat.Prime.coprime_iff_not_dvd hr.out).2 h0)
    have hc : ∀ i, (i = 1 ∨ i = 2 ∨ i = 3) → Nat.Coprime r (q ^ i - 1) := by
      rintro i (rfl | rfl | rfl)
      · rw [pow_one]; exact (Nat.Prime.coprime_iff_not_dvd hr.out).2 h1
      · exact (Nat.Prime.coprime_iff_not_dvd hr.out).2 h2
      · exact (Nat.Prime.coprime_iff_not_dvd hr.out).2 h3
    rw [show q ^ 4 - q = q ^ 4 - q ^ 1 by rw [pow_one], hfac 1 (by norm_num),
      hfac 2 (by norm_num), hfac 3 (by norm_num)]
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
    · exact Nat.Coprime.mul_right (hcq 1) (hc 3 (by norm_num))
    · exact Nat.Coprime.mul_right (hcq 2) (hc 2 (by norm_num))
    · exact Nat.Coprime.mul_right (hcq 3) (hc 1 (by norm_num))
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow r S))
  set T' : Subgroup (GL (Fin 4) k) := (T : Subgroup S).map S.subtype with hT'
  have hT'p : IsPGroup r T' := T.isPGroup'.map S.subtype
  obtain ⟨R₀, hR₀⟩ := hT'p.exists_le_sylow
  have hq4 : q ^ 4 - 1 ≠ 0 := by
    have : 2 ≤ q := Fintype.one_lt_card
    have : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left this 4
    omega
  have hR₀eq : (R₀ : Subgroup (GL (Fin 4) k)) = T' := by
    refine (Subgroup.eq_of_le_of_card_ge hR₀ ?_).symm
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 R₀.isPGroup'
    have hdvd : r ^ j ∣ q ^ 4 - 1 := by
      have h := hj ▸ Subgroup.card_subgroup_dvd_card (R₀ : Subgroup (GL (Fin 4) k))
      rw [hGL] at h
      exact (Nat.Coprime.pow_left j hcopM).dvd_of_dvd_mul_right h
    have hTcard : Nat.card (T : Subgroup S) = r ^ (Nat.card S).factorization r :=
      Sylow.card_eq_multiplicity T
    rw [hT', Subgroup.card_map_of_injective S.subtype_injective, hTcard, hcardS, hj]
    exact Nat.pow_le_pow_right hr.out.pos
      ((Nat.Prime.pow_dvd_iff_le_factorization hr.out hq4).1 hdvd)
  have hR₀cyc : IsCyclic (R₀ : Subgroup (GL (Fin 4) k)) := by
    rw [hR₀eq, hT']
    have : IsCyclic (T : Subgroup S) := Subgroup.isCyclic_of_le le_top
    exact isCyclic_of_surjective
      ((T : Subgroup S).equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
      ((T : Subgroup S).equivMapOfInjective S.subtype S.subtype_injective).surjective
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 4) k) R₀ R
  have hRcyc : IsCyclic (R : Subgroup (GL (Fin 4) k)) := by
    rw [← hg]
    exact isCyclic_of_surjective (R₀.equivSMul g).toMonoidHom (R₀.equivSMul g).surjective
  exact Subgroup.isCyclic_of_le hPR

theorem sylow_isCyclic_of_cyclic_subgroup {G : Type*} [Group G] [Finite G] {r : ℕ}
    [hr : Fact r.Prime] (C : Subgroup G) [IsCyclic C]
    (hC : (Nat.card G).factorization r ≤ (Nat.card C).factorization r) (R : Sylow r G) :
    IsCyclic (R : Subgroup G) := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow r C))
  set T' : Subgroup G := (T : Subgroup C).map C.subtype with hT'
  have hT'p : IsPGroup r T' := T.isPGroup'.map C.subtype
  obtain ⟨R₀, hR₀⟩ := hT'p.exists_le_sylow
  have hR₀eq : (R₀ : Subgroup G) = T' := by
    refine (Subgroup.eq_of_le_of_card_ge hR₀ ?_).symm
    have hTcard : Nat.card (T : Subgroup C) = r ^ (Nat.card C).factorization r :=
      Sylow.card_eq_multiplicity T
    rw [hT', Subgroup.card_map_of_injective C.subtype_injective, hTcard,
      Sylow.card_eq_multiplicity R₀]
    exact Nat.pow_le_pow_right hr.out.pos hC
  have hR₀cyc : IsCyclic (R₀ : Subgroup G) := by
    rw [hR₀eq, hT']
    have : IsCyclic (T : Subgroup C) := Subgroup.isCyclic_of_le le_top
    exact isCyclic_of_surjective
      ((T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
      ((T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R₀ R
  rw [← hg]
  exact isCyclic_of_surjective (R₀.equivSMul g).toMonoidHom (R₀.equivSMul g).surjective

theorem ker_eq_bot_of_sylow_isCyclic {E S : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    [Group S] [Finite S] (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r S),
      IsCyclic (Q : Subgroup S)) : π.ker = ⊥ := by
  by_contra hne
  have hnt : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.2 hnt).ne'
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  obtain ⟨Cr⟩ := (inferInstance : Nonempty (Sylow r π.ker))
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r S))
  exact Sylow.ne_bot_of_dvd_card Cr hrd
    (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cr Q
      (hcyc r hr hr2 Q))

theorem odd_central_extension_splitting_of_sylow_isCyclic {E S : Type*} [Group E] [Finite E]
    [Group S] [Finite S] [Group.IsPerfect S] (η : E →* S)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card η.ker))
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r S),
      IsCyclic (Q : Subgroup S)) :
    (∃! σ : S →* E, η.comp σ = MonoidHom.id S) ∧
      ∀ σ : S →* E, η.comp σ = MonoidHom.id S →
        σ.range = commutator E ∧
          ∃ e : η.ker × S ≃* E, ∀ x : η.ker × S, e x = (x.1 : E) * σ x.2 := by
  obtain ⟨-, hperf, hsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective η hη hC inferInstance
  set D := commutator E with hD
  set η' : D →* S := η.comp D.subtype with hη'
  have : Group.IsPerfect D := hperf
  have hC' : η'.ker ≤ Subgroup.center D := fun x hx => by
    have hx' : (x : E) ∈ Subgroup.center E := hC (by simpa [η'] using hx)
    exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 hx' y)
  have hodd' : Odd (Nat.card η'.ker) := by
    have hle : η'.ker.map D.subtype ≤ η.ker := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      simpa [η'] using hy
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective D.subtype_injective] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hinj : Function.Injective η' :=
    (MonoidHom.ker_eq_bot_iff η').1 (ker_eq_bot_of_sylow_isCyclic η' hsurj hC' hodd' hcyc)
  have hσD : ∀ σ : S →* E, σ.range ≤ D := by
    intro σ
    have : Group.IsPerfect σ.range := Group.IsPerfect.range σ
    rw [← Subgroup.commutator_eq_self (H := σ.range), hD, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hsec : ∀ σ : S →* E, η.comp σ = MonoidHom.id S → ∀ x : D, σ (η x) = x := by
    intro σ hσ x
    have hmem : σ (η x) ∈ D := hσD σ ⟨η x, rfl⟩
    have h := congrArg Subtype.val (hinj (a₁ := ⟨σ (η x), hmem⟩) (a₂ := x) (by
      change η (σ (η x)) = η x
      exact congrArg (fun φ : S →* S => φ (η x)) hσ))
    exact h
  let e' : D ≃* S := MulEquiv.ofBijective η' ⟨hinj, hsurj⟩
  let σ₀ : S →* E := D.subtype.comp e'.symm.toMonoidHom
  have hσ₀ : η.comp σ₀ = MonoidHom.id S := by
    ext s
    change η' (e'.symm s) = s
    exact e'.apply_symm_apply s
  refine ⟨⟨σ₀, hσ₀, fun σ hσ => ?_⟩, fun σ hσ => ⟨le_antisymm (hσD σ) fun x hx => ?_, ?_⟩⟩
  · ext s
    obtain ⟨x, rfl⟩ := hsurj s
    change σ (η x) = σ₀ (η x)
    rw [hsec σ hσ x, hsec σ₀ hσ₀ x]
  · exact ⟨η x, hsec σ hσ ⟨x, hx⟩⟩
  · have hσs : ∀ s, η (σ s) = s := fun s => congrArg (fun φ : S →* S => φ s) hσ
    let φ : η.ker × S →* E := MonoidHom.noncommCoprod η.ker.subtype σ fun c s =>
      Subgroup.mem_center_iff.1 (hC c.2) (σ s) |>.symm
    have hbij : Function.Bijective φ := by
      refine ⟨fun x y hxy => ?_, fun g => ?_⟩
      · have hxy' : (x.1 : E) * σ x.2 = y.1 * σ y.2 := hxy
        have h2 : x.2 = y.2 := by
          have := congrArg η hxy'
          rwa [map_mul, map_mul, MonoidHom.mem_ker.1 x.1.2, MonoidHom.mem_ker.1 y.1.2, one_mul,
            one_mul, hσs, hσs] at this
        rw [h2, mul_left_inj] at hxy'
        exact Prod.ext (Subtype.ext hxy') h2
      · refine ⟨(⟨g * (σ (η g))⁻¹, ?_⟩, η g), ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hσs, mul_inv_cancel]
        · change g * (σ (η g))⁻¹ * σ (η g) = g
          rw [inv_mul_cancel_right]
    exact ⟨MulEquiv.ofBijective φ hbij, fun x => rfl⟩

section Suzuki

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

@[expose] noncomputable def szTorus :
    (BinaryGaloisField (2 * m + 1))ˣ →* SuzukiMatrixGroup m where
  toFun x := ⟨SuzukiTorusGL m x, Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))⟩
  map_one' := Subtype.ext (suzukiTorusGL_one m)
  map_mul' x y := Subtype.ext (suzukiTorusGL_mul m x y).symm

theorem szTorus_injective : Function.Injective (szTorus m) := by
  intro x y hxy
  apply Units.ext
  let K := BinaryGaloisField (2 * m + 1)
  let frob : K ≃+* K := iterateFrobeniusEquiv K 2 m
  apply frob.injective
  have h11 := congrArg
    (fun A : SuzukiMatrixGroup m => ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1) hxy
  simpa [frob, iterateFrobeniusEquiv_def, iterateFrobenius_def, szTorus, SuzukiTorusGL,
    SuzukiTorusMatrix] using h11

theorem card_suzukiMatrixGroup (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  have hpi : ∀ x : K, iterateFrobeniusEquiv K 2 (m + 1) x = x ^ (2 ^ (m + 1)) := fun x => by
    rw [iterateFrobeniusEquiv_def]
  exact (huppert_blackburn_XI_3_3 m hm (iterateFrobeniusEquiv K 2 (m + 1)) hpi).2.2.2.2.2.2.1

theorem natCard_binaryGaloisField : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) :=
  GaloisField.card 2 (2 * m + 1) (by omega)

theorem not_dvd_of_dvd_sq_add_one {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : 1 ≤ q)
    (h : r ∣ q ^ 2 + 1) :
    ¬ r ∣ q ∧ ¬ r ∣ q - 1 ∧ ¬ r ∣ q ^ 2 - 1 ∧ ¬ r ∣ q ^ 3 - 1 := by
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h0
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 r).1 this))
  have hx2 : (q : ZMod r) ^ 2 = -1 := by
    have := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) r).2 h
    push_cast at this
    linear_combination this
  have hsub : ∀ j, (r ∣ q ^ j - 1 ↔ (q : ZMod r) ^ j = 1) := fun j => by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero]
    push_cast
    rfl
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have hx0 : (q : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff q r).2 h0
    rw [hx0] at hx2
    exact h2 (by linear_combination 2 * hx2)
  · have hx1 : (q : ZMod r) ^ 1 = 1 := (hsub 1).1 (by rwa [pow_one])
    rw [pow_one] at hx1
    rw [hx1] at hx2
    exact h2 (by linear_combination hx2)
  · have := (hsub 2).1 h1
    rw [hx2] at this
    exact h2 (by linear_combination -this)
  · have h3 := (hsub 3).1 h1
    have : (q : ZMod r) = -1 := by
      linear_combination (-1 : ZMod r) * h3 + (q : ZMod r) * hx2
    rw [this] at hx2
    exact h2 (by linear_combination hx2)

theorem suzuki_sylow_isCyclic (hm : 0 < m) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (R : Sylow r (SuzukiMatrixGroup m)) : IsCyclic (R : Subgroup (SuzukiMatrixGroup m)) := by
  set q := 2 ^ (2 * m + 1) with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hcard := card_suzukiMatrixGroup m hm
  have hr2q : ¬ r ∣ q := fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 (hr.out.dvd_of_dvd_pow h))
  by_cases hsq : r ∣ q ^ 2 + 1
  ·
    obtain ⟨h0, h1, h2, h3⟩ := not_dvd_of_dvd_sq_add_one hr.out hr2 hq1 hsq
    let K := BinaryGaloisField (2 * m + 1)
    have : Fintype K := Fintype.ofFinite K
    have hK : Fintype.card K = q := by
      rw [← Nat.card_eq_fintype_card, natCard_binaryGaloisField]
    have hcyc := isCyclic_of_isPGroup_GL_four (k := K) (p := 2) (r := r)
      (hK ▸ h0) (hK ▸ h1) (hK ▸ h2) (hK ▸ h3)
      ((R : Subgroup (SuzukiMatrixGroup m)).map (SuzukiMatrixGroup m).subtype)
      (R.isPGroup'.map _)
    exact isCyclic_of_surjective
      ((R : Subgroup (SuzukiMatrixGroup m)).equivMapOfInjective _
        (SuzukiMatrixGroup m).subtype_injective).symm.toMonoidHom
      ((R : Subgroup (SuzukiMatrixGroup m)).equivMapOfInjective _
        (SuzukiMatrixGroup m).subtype_injective).symm.surjective
  · by_cases hq1r : r ∣ q - 1
    ·
      have : IsCyclic (szTorus m).range := isCyclic_of_surjective
        (MonoidHom.ofInjective (szTorus_injective m)).toMonoidHom
        (MonoidHom.ofInjective (szTorus_injective m)).surjective
      refine sylow_isCyclic_of_cyclic_subgroup (szTorus m).range ?_ R
      have hT : Nat.card (szTorus m).range = q - 1 := by
        rw [← Nat.card_congr (MonoidHom.ofInjective (szTorus_injective m)).toEquiv,
          Nat.card_units, natCard_binaryGaloisField]
      rw [hT, hcard]
      have hq2 : 2 ≤ q := by
        rw [hq]
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hne1 : q ^ 2 + 1 ≠ 0 := by positivity
      have hne2 : q ^ 2 ≠ 0 := by positivity
      have hne3 : q - 1 ≠ 0 := by omega
      rw [Nat.factorization_mul (Nat.mul_ne_zero hne1 hne2) hne3,
        Nat.factorization_mul hne1 hne2, Finsupp.add_apply, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hsq,
        Nat.factorization_eq_zero_of_not_dvd (fun h => hr2q (hr.out.dvd_of_dvd_pow h))]
      simp
    ·
      have hnd : ¬ r ∣ Nat.card (SuzukiMatrixGroup m) := by
        rw [hcard]
        intro h
        rcases (Nat.Prime.dvd_mul hr.out).1 h with h' | h'
        · rcases (Nat.Prime.dvd_mul hr.out).1 h' with h'' | h''
          · exact hsq h''
          · exact hr2q (hr.out.dvd_of_dvd_pow h'')
        · exact hq1r h'
      have hR1 : Nat.card (R : Subgroup (SuzukiMatrixGroup m)) = 1 := by
        rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero]
      have : Subsingleton (R : Subgroup (SuzukiMatrixGroup m)) :=
        (Nat.card_eq_one_iff_unique.1 hR1).1
      exact isCyclic_of_subsingleton

theorem suzukiMatrixGroup_nonabelian (hm : 0 < m) :
    ∃ a b : SuzukiMatrixGroup m, a * b ≠ b * a := by
  have hsimp := (huppert_blackburn_XI_3_6 m hm).1
  by_contra h
  push Not at h
  have : IsMulCommutative (SuzukiMatrixGroup m) := ⟨⟨h⟩⟩
  have hp := (Group.is_simple_iff_prime_card).1 hsimp
  rw [card_suzukiMatrixGroup m hm] at hp
  set q := 2 ^ (2 * m + 1)
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : 1 ≤ q - 1 := by omega
  rcases hp.eq_one_or_self_of_dvd (q ^ 2) ⟨(q ^ 2 + 1) * (q - 1), by ring⟩ with h1 | h1
  · have : 4 ≤ q ^ 2 := by nlinarith
    omega
  · have hpos : 0 < q ^ 2 := by positivity
    have h5 : 2 ≤ (q ^ 2 + 1) * (q - 1) := by nlinarith
    have h1' : q ^ 2 * 1 = q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by rw [mul_one]; nth_rewrite 1 [h1]; ring
    have := Nat.eq_of_mul_eq_mul_left hpos h1'
    linarith

theorem suzukiMatrixGroup_isPerfect (hm : 0 < m) : Group.IsPerfect (SuzukiMatrixGroup m) :=
  have := (huppert_blackburn_XI_3_6 m hm).1
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (suzukiMatrixGroup_nonabelian m hm)).1.1

theorem suzuki_odd_central_extension_splitting (hm : 0 < m) {E : Type*} [Group E] [Finite E]
    (η : E →* SuzukiMatrixGroup m) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card η.ker)) :
    (∃! σ : SuzukiMatrixGroup m →* E, η.comp σ = MonoidHom.id _) ∧
      ∀ σ : SuzukiMatrixGroup m →* E, η.comp σ = MonoidHom.id _ →
        σ.range = commutator E ∧
          ∃ e : η.ker × SuzukiMatrixGroup m ≃* E,
            ∀ x : η.ker × SuzukiMatrixGroup m, e x = (x.1 : E) * σ x.2 :=
  have := suzukiMatrixGroup_isPerfect m hm
  odd_central_extension_splitting_of_sylow_isCyclic η hη hC hodd fun _ _ hr2 _ Q =>
    suzuki_sylow_isCyclic m hm hr2 Q

theorem suzuki_perfect_odd_cover_trivial (hm : 0 < m) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* SuzukiMatrixGroup m) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ :=
  ker_eq_bot_of_sylow_isCyclic π hπ hC hodd fun _ _ hr2 _ Q => suzuki_sylow_isCyclic m hm hr2 Q

end Suzuki

theorem catalogStepConclusion_of_center_eq_bot {L : Type} [Group L] [Finite L]
    (hSQT : IsStronglyQuasithin L) (hZ : Subgroup.center L = ⊥) : CatalogStepConclusion L := by
  refine ⟨Or.inl (by rw [hZ, Subgroup.card_bot]), fun A _ hA => ?_⟩
  obtain rfl : A = ⊥ := le_bot_iff.1 (hZ ▸ hA)
  exact isStronglyQuasithin_of_mulEquiv QuotientGroup.quotientBot hSQT

theorem center_eq_ker_of_mulEquiv {L S : Type} [Group L] [Group S]
    (e : L ⧸ Subgroup.center L ≃* S) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

open CFSG.BenderSuzuki.MatrixGroups in
theorem catalog_suzuki {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    (hSQT : IsStronglyQuasithin L) (hodd : Odd (Nat.card (Subgroup.center L))) {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel (L ⧸ Subgroup.center L) p f) : CatalogStepConclusion L := by
  have : Group.IsPerfect L := hL.1
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel h
  let π : L →* SuzukiMatrixGroup a := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := center_eq_ker_of_mulEquiv e
  have hZ := suzuki_perfect_odd_cover_trivial a (by omega) π hπ hker.le (hker ▸ hodd)
  exact catalogStepConclusion_of_center_eq_bot hSQT (hker ▸ hZ)

end CFSG.SectionRank
