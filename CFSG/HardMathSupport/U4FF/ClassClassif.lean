module

public import CFSG.HardMathSupport.U4FF.ClassDatumDefs
public import CFSG.HardMathSupport.U4FF.ClassDescent
public import CFSG.HardMathSupport.U4FF.ClassFiber
public import CFSG.HardMathSupport.U4FF.ClassChar
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType
public import CFSG.HardMathSupport.U4FF.ClassWeyl

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.QuasithinUnique.Setup.X7 (matRep fixedSub)

structure CurtisIface (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (hK : Nat.card K = (2 ^ n) ^ 2) where
  D : CurtisDatum (G4 K n) csB 2
  C : CentralCoverData D (MonoidHom.id (G4 K n)) 2
  R : CoverRankOne C (Fs K n)
  hU : C.lU = UpperU K n
  hH : D.H = Hd K n
  hh0 : ∀ u : Kˣ, R.hh 0 u = hTor0 hK u
  hh1 : ∀ v : (Fq K n)ˣ, R.hh 1 v = hTor1 hK v
  hodd : ∀ h ∈ D.H.comap (MonoidHom.id (G4 K n)), IsPElt 2 h → h = 1
  hsplit : ∀ (k : Type) [Field k] [Algebra K k], SplitOver k (D.H.comap (MonoidHom.id (G4 K n)))

section Generic

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p}
  {π : Ĝ →* G} {C : CentralCoverData D π p} {F : B → Type} [∀ s, Field (F s)]
  (R : CoverRankOne C F) {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  {ρ : Representation k Ĝ V} {y : V} {χ χ' : Ĝ → k} {J : Finset B}

theorem IsCoverType.congr_H (ht : IsCoverType R ρ y χ J)
    (h : ∀ g ∈ D.H.comap π, χ g = χ' g) : IsCoverType R ρ y χ' J := by
  obtain ⟨hy, hy0, hχ, hJ⟩ := ht
  refine ⟨hy, hy0, fun g hg => by rw [← h g hg]; exact hχ g hg, fun s => ?_⟩
  have e : ∀ u : (F s)ˣ, χ (R.hh s u) = χ' (R.hh s u) := fun u => h _ (R.hh_mem s u)
  rw [hJ s]
  simp only [e]

end Generic

section Weights

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k] [CharP k 2]
  [Algebra K k]

@[expose] noncomputable def chiE (k : Type) [Field k] [Algebra K k] (e₁ e₂ : ℕ) (g : G4 K n) : k :=
  algebraMap K k ((gm g 0 0) ^ e₁ * (gm g 0 0 * gm g 1 1) ^ e₂)

@[expose] noncomputable def chiL (k : Type) [Field k] [Algebra K k] (l : Lbl n) (g : G4 K n) : k :=
  chiE k l.e1 l.e2 g

theorem gm_hTor_mul_00 (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) (v : (Fq K n)ˣ) :
    gm (hTor0 hK u * hTor1 hK v) 0 0 = (u : K) := by
  rw [gm_mul, gm_hTor0, gm_hTor1]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, tor0Vec, tor1Vec]

theorem gm_hTor_mul_11 (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) (v : (Fq K n)ˣ) :
    gm (hTor0 hK u * hTor1 hK v) 1 1 = (u : K)⁻¹ * ((v : Fq K n) : K) := by
  rw [gm_mul, gm_hTor0, gm_hTor1]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, tor0Vec, tor1Vec]

theorem chiE_hTor (hK : Nat.card K = (2 ^ n) ^ 2) (e₁ e₂ : ℕ) (u : Kˣ) (v : (Fq K n)ˣ) :
    chiE k e₁ e₂ (hTor0 hK u * hTor1 hK v) =
      algebraMap K k ((u : K) ^ e₁ * ((v : Fq K n) : K) ^ e₂) := by
  unfold chiE
  rw [gm_hTor_mul_00, gm_hTor_mul_11]
  have hu : (u : K) ≠ 0 := u.ne_zero
  congr 2
  field_simp

theorem Tmod_Hd_weight (l : Lbl n) {h : G4 K n} (hh : h ∈ Hd K n) :
    Tmod K l k h *ᵥ hwv l k = chiL k l h • hwv l k := by
  have hd := (mem_Hd).mp hh
  have hdet := Hd_det hh
  have hr0 := Hd_rel hh 0
  have hrel : gm h 0 0 * gm h 1 1 * gm h 2 2 = (gm h 0 0) ^ 2 ^ n := by
    have h3 : gm h (Fin.rev 0) (Fin.rev 0) = gm h 3 3 := rfl
    rw [h3] at hr0
    calc gm h 0 0 * gm h 1 1 * gm h 2 2
        = gm h 0 0 * gm h 1 1 * gm h 2 2 * (gm h 0 0 ^ 2 ^ n * gm h 3 3) := by rw [hr0, mul_one]
      _ = gm h 0 0 ^ 2 ^ n * (gm h 0 0 * gm h 1 1 * gm h 2 2 * gm h 3 3) := by ring
      _ = gm h 0 0 ^ 2 ^ n := by rw [hdet, mul_one]
  exact Tmod_diag_weight l hd hrel

end Weights

section TypeOfTmod

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {hK : Nat.card K = (2 ^ n) ^ 2}
  (I : CurtisIface K n hK) {k : Type} [Field k] [CharP k 2] [Algebra K k]

theorem mem_H_iff {g : G4 K n} : g ∈ I.D.H.comap (MonoidHom.id (G4 K n)) ↔ g ∈ Hd K n := by
  rw [Subgroup.mem_comap, MonoidHom.id_apply, I.hH]

theorem type_of_Trep (l : Lbl n) :
    ∃ (y : TIdx l → k) (χ : G4 K n → k) (J : Finset (Fin 2)),
      IsCoverType I.R (Trep K l k) y χ J ∧ ∀ h ∈ Hd K n, χ h = chiL k l h := by
  have hρ := Tmod_isSimpleRep (k := k) hK l
  obtain ⟨y, χ, J, ht⟩ := exists_isCoverType (R := I.R) hρ (I.hsplit k)
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (I.hsplit k)
  have hfix : hwv l k ∈ I.C.datum.fixU (Trep K l k) := by
    rw [CurtisDatum.mem_fixU]
    intro u hu
    have hu' : u ∈ UpperU K n := by
      have : u ∈ I.C.lU := hu
      rwa [I.hU] at this
    rw [Trep_apply, Tmod_eq]
    exact TmodΦ_upper_fix hK l _ hu'
  obtain ⟨c, hc⟩ := I.C.datum.fixU_eq_smul hρ hμ hfix
  refine ⟨y, χ, J, ht, fun h hh => ?_⟩
  have hhH : h ∈ I.D.H.comap (MonoidHom.id (G4 K n)) := (mem_H_iff I).2 hh
  have h1 : (Trep K l k) h (hwv l k) = chiL k l h • hwv l k := by
    rw [Trep_apply]
    exact Tmod_Hd_weight l hh
  have h2 : (Trep K l k) h (hwv l k) = χ h • hwv l k := by
    rw [hc, map_smul, ht.2.2.1 h hhH, smul_comm]
  have h3 : (χ h - chiL k l h) • hwv l k = 0 := by
    rw [sub_smul, ← h2, ← h1, sub_self]
  have h4 := (smul_eq_zero.mp h3).resolve_right (hwv_ne_zero l)
  exact sub_eq_zero.mp h4

theorem card_Fq (hK : Nat.card K = (2 ^ n) ^ 2) : Nat.card (Fq K n) = 2 ^ n := by
  rw [← card_fixed_eq hK]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => mem_Fq)

theorem char_exponents {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k (G4 K n) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : G4 K n → k} {J : Finset (Fin 2)}
    (ht : IsCoverType I.R ρ y χ J) :
    ∃ e₁ e₂ : ℕ, e₁ < 2 ^ (2 * n) - 1 ∧ e₂ < 2 ^ n - 1 ∧
      ∀ h ∈ Hd K n, χ h = chiE k e₁ e₂ h := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (I.hsplit k)
  have hmem0 : ∀ u : Kˣ, hTor0 hK u ∈ I.D.H.comap (MonoidHom.id (G4 K n)) := fun u =>
    (mem_H_iff I).2 (hTor0_mem hK u)
  have hmem1 : ∀ v : (Fq K n)ˣ, hTor1 hK v ∈ I.D.H.comap (MonoidHom.id (G4 K n)) := fun v =>
    (mem_H_iff I).2 (hTor1_mem hK v)
  obtain ⟨e₁, he₁, hχ₀⟩ := exists_char_exponent (F := K) (k := k)
    (fun u => χ (hTor0 hK u))
    (fun u u' => by
      simp only [hTor0_mul]
      exact hμ.chi_mul (hmem0 u) (hmem0 u'))
    (by
      simp only [hTor0_one]
      exact hμ.chi_one)
  letI : Algebra (Fq K n) k := ((algebraMap K k).comp (Fq K n).subtype).toAlgebra
  obtain ⟨e₂, he₂, hχ₁⟩ := exists_char_exponent (F := Fq K n) (k := k)
    (fun v => χ (hTor1 hK v))
    (fun v v' => by
      simp only [hTor1_mul]
      exact hμ.chi_mul (hmem1 v) (hmem1 v'))
    (by
      simp only [hTor1_one]
      exact hμ.chi_one)
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · have : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by
      rw [Nat.card_units, hK, ← pow_mul, mul_comm]
    omega
  · have : Nat.card (Fq K n)ˣ = 2 ^ n - 1 := by
      rw [Nat.card_units, card_Fq hK]
    omega
  · intro h hh
    obtain ⟨u, v, rfl⟩ := Hd_eq_hTor hK hh
    rw [hμ.chi_mul (hmem0 u) (hmem1 v), hχ₀, hχ₁, chiE_hTor, map_mul, map_pow, map_pow]
    rfl

theorem chiE_congr (hK : Nat.card K = (2 ^ n) ^ 2) {e₁ e₂ e₁' e₂' : ℕ}
    (h1 : e₁ ≡ e₁' [MOD 2 ^ (2 * n) - 1])
    (h2 : e₂ ≡ e₂' [MOD 2 ^ n - 1]) {h : G4 K n} (hh : h ∈ Hd K n) :
    chiE k e₁ e₂ h = chiE k e₁' e₂' h := by
  obtain ⟨u, v, rfl⟩ := Hd_eq_hTor hK hh
  rw [chiE_hTor, chiE_hTor]
  have hu : (u : K) ^ e₁ = (u : K) ^ e₁' := by
    have hord : orderOf u ∣ 2 ^ (2 * n) - 1 := by
      have := orderOf_dvd_natCard u
      rwa [Nat.card_units, hK, ← pow_mul, mul_comm] at this
    have h1' : e₁ ≡ e₁' [MOD orderOf u] := Nat.ModEq.of_dvd hord h1
    have := (pow_eq_pow_iff_modEq (x := u)).mpr h1'
    exact congrArg Units.val this
  have hv : ((v : Fq K n) : K) ^ e₂ = ((v : Fq K n) : K) ^ e₂' := by
    have hord : orderOf v ∣ 2 ^ n - 1 := by
      have := orderOf_dvd_natCard v
      rwa [Nat.card_units, card_Fq hK] at this
    have h2' : e₂ ≡ e₂' [MOD orderOf v] := Nat.ModEq.of_dvd hord h2
    have := (pow_eq_pow_iff_modEq (x := v)).mpr h2'
    exact congrArg (fun w : (Fq K n)ˣ => ((w : Fq K n) : K)) this
  rw [hu, hv]

theorem chiE_hTor0 (e₁ e₂ : ℕ) (u : Kˣ) :
    chiE k e₁ e₂ (hTor0 hK u) = algebraMap K k (u : K) ^ e₁ := by
  have h : hTor0 hK u = hTor0 hK u * hTor1 hK 1 := by rw [hTor1_one, mul_one]
  rw [h, chiE_hTor]
  simp [map_pow]

theorem chiE_hTor1 (e₁ e₂ : ℕ) (v : (Fq K n)ˣ) :
    chiE k e₁ e₂ (hTor1 hK v) = algebraMap K k ((v : Fq K n) : K) ^ e₂ := by
  have h : hTor1 hK v = hTor0 hK 1 * hTor1 hK v := by rw [hTor0_one, one_mul]
  rw [h, chiE_hTor]
  simp [map_pow]

open Classical in
noncomputable def Sfin (χ : G4 K n → k) : Finset (Fin 2) :=
  Finset.univ.filter fun s => ∀ u : (Fs K n s)ˣ, χ (I.R.hh s u) = 1

theorem mem_Sfin_zero (e₁ e₂ : ℕ) :
    (0 : Fin 2) ∈ Sfin I (chiE k e₁ e₂) ↔ 2 ^ (2 * n) - 1 ∣ e₁ := by
  classical
  simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ u : Kˣ, chiE k e₁ e₂ (I.R.hh 0 u) = 1) ↔ _
  have h1 : ∀ u : Kˣ, chiE k e₁ e₂ (I.R.hh 0 u) = algebraMap K k (u : K) ^ e₁ := by
    intro u
    rw [I.hh0 u, chiE_hTor0]
  simp only [h1]
  have h2 := units_pow_eq_one_iff (F := K) (k := k) e₁
  have h3 : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by
    rw [Nat.card_units, hK, ← pow_mul, mul_comm]
  rw [← h3]
  exact h2

theorem mem_Sfin_one (e₁ e₂ : ℕ) :
    (1 : Fin 2) ∈ Sfin I (chiE k e₁ e₂) ↔ 2 ^ n - 1 ∣ e₂ := by
  classical
  letI : Algebra (Fq K n) k := ((algebraMap K k).comp (Fq K n).subtype).toAlgebra
  simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ v : (Fq K n)ˣ, chiE k e₁ e₂ (I.R.hh 1 v) = 1) ↔ _
  have h1 : ∀ v : (Fq K n)ˣ, chiE k e₁ e₂ (I.R.hh 1 v) =
      algebraMap (Fq K n) k (v : Fq K n) ^ e₂ := by
    intro v
    rw [I.hh1 v, chiE_hTor1]
    rfl
  simp only [h1]
  have h2 := units_pow_eq_one_iff (F := Fq K n) (k := k) e₂
  have h3 : Nat.card (Fq K n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, card_Fq hK]
  rw [← h3]
  exact h2

theorem card_Sfin (e₁ e₂ : ℕ) :
    (Sfin I (chiE k e₁ e₂)).card =
      (if 2 ^ (2 * n) - 1 ∣ e₁ then 1 else 0) + (if 2 ^ n - 1 ∣ e₂ then 1 else 0) := by
  classical
  have h0 := mem_Sfin_zero I (k := k) e₁ e₂
  have h1 := mem_Sfin_one I (k := k) e₁ e₂
  have : Sfin I (chiE k e₁ e₂) = Finset.univ.filter fun s : Fin 2 =>
      (s = 0 ∧ 2 ^ (2 * n) - 1 ∣ e₁) ∨ (s = 1 ∧ 2 ^ n - 1 ∣ e₂) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, true_and, Fin.reduceEq, false_and, or_false]
      exact h0
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceEq, false_and, true_and, false_or]
      exact h1
  rw [this, Finset.card_filter, Fin.sum_univ_two]
  simp

end TypeOfTmod

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {hK : Nat.card K = (2 ^ n) ^ 2}
  (I : CurtisIface K n hK)

include I in
theorem classif_of_iface : Classif K n := by
  unfold Classif
  intro E _ _ _ V _ _ σ hσ
  classical
  have hn : 1 ≤ n := by
    have := one_lt_two_pow_of_card hK
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at this
    · exact h
  have hρ : IsSimpleRep σ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ).mp hσ
  obtain ⟨y, χ, J, ht⟩ := exists_isCoverType (R := I.R) hρ (I.hsplit E)
  obtain ⟨e₁, e₂, he₁, he₂, hχ⟩ := char_exponents I hρ ht
  have hT := fun l : Lbl n => type_of_Trep I (k := E) l
  choose y' χ' J' ht' hχ' using hT
  set S₀ : Finset (Fin 2) := Sfin I (chiE E e₁ e₂) with hS₀
  set Fb : Finset (Lbl n) := Finset.univ.filter fun l : Lbl n =>
    l.e1 ≡ e₁ [MOD 2 ^ (2 * n) - 1] ∧ l.e2 ≡ e₂ [MOD 2 ^ n - 1] with hFb
  have hHmem : ∀ g : G4 K n, g ∈ I.D.H.comap (MonoidHom.id (G4 K n)) ↔ g ∈ Hd K n :=
    fun g => mem_H_iff I
  have hagree : ∀ l ∈ Fb, ∀ g ∈ Hd K n, χ' l g = chiE E e₁ e₂ g := by
    intro l hl g hg
    rw [Finset.mem_filter] at hl
    rw [hχ' l g hg]
    exact chiE_congr hK hl.2.1 hl.2.2 hg
  have hht' : ∀ l ∈ Fb, IsCoverType I.R (Trep K l E) (y' l) (chiE E e₁ e₂) (J' l) := fun l hl =>
    IsCoverType.congr_H I.R (ht' l) fun g hg => hagree l hl g ((hHmem g).1 hg)
  have hht : IsCoverType I.R σ y (chiE E e₁ e₂) J :=
    IsCoverType.congr_H I.R ht fun g hg => hχ g ((hHmem g).1 hg)
  have hhh : ∀ (s : Fin 2) (u : (Fs K n s)ˣ), I.R.hh s u ∈ Hd K n := fun s u =>
    (hHmem _).1 (I.R.hh_mem s u)
  have hJsub : ∀ l ∈ Fb, J' l ⊆ S₀ := by
    intro l hl s hs
    have h1 := ((hht' l hl).2.2.2 s).1 hs
    simp only [hS₀, Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h1.1
  have hJV : J ⊆ S₀ := by
    intro s hs
    have h1 := (hht.2.2.2 s).1 hs
    simp only [hS₀, Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h1.1
  have hinj : Set.InjOn J' (Fb : Set (Lbl n)) := by
    intro l hl l' hl' hJ
    by_contra hne
    have hl1 := Finset.mem_filter.mp hl
    have hl1' := Finset.mem_filter.mp hl'
    have hρl := Tmod_isSimpleRep (k := E) hK l
    have hρl' := Tmod_isSimpleRep (k := E) hK l'
    have ht1 := hht' l hl
    have ht2 := hht' l' hl'
    rw [← hJ] at ht2
    obtain ⟨β, -⟩ := iso_of_isCoverType I.hodd hρl hρl' (I.hsplit E) ht1 ht2
    have h1 := β.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_TIdx,
      card_TIdx] at h1
    exact Lbl.dim_ne_of_fiber hn hne (hl1.2.1.trans hl1'.2.1.symm) (hl1.2.2.trans hl1'.2.2.symm) h1
  have hcard : Fb.card = S₀.powerset.card := by
    rw [hFb, Lbl.card_fiber hn e₁ e₂, Finset.card_powerset, hS₀, card_Sfin I (k := E) e₁ e₂]
  have himage : Fb.image J' = S₀.powerset := by
    refine Finset.eq_of_subset_of_card_le (fun J₁ hJ₁ => ?_) ?_
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hJ₁
      exact Finset.mem_powerset.mpr (hJsub l hl)
    · rw [Finset.card_image_of_injOn hinj, hcard]
  obtain ⟨l, hl, hlJ⟩ : ∃ l ∈ Fb, J' l = J := by
    have : J ∈ Fb.image J' := by rw [himage]; exact Finset.mem_powerset.mpr hJV
    obtain ⟨l, hl, h⟩ := Finset.mem_image.mp this
    exact ⟨l, hl, h⟩
  have hρl := Tmod_isSimpleRep (k := E) hK l
  have ht2 := hht' l hl
  rw [hlJ] at ht2
  obtain ⟨β, hβ⟩ := iso_of_isCoverType I.hodd hρ hρl (I.hsplit E) hht ht2
  refine ⟨l, ⟨Representation.Equiv.mk β.symm fun g => LinearMap.ext fun w => ?_⟩⟩
  have h1 := hβ g (β.symm w)
  rw [LinearEquiv.apply_symm_apply] at h1
  show β.symm ((matRep (Tmod K l E)) g w) = σ g (β.symm w)
  apply β.injective
  rw [LinearEquiv.apply_symm_apply, hβ, LinearEquiv.apply_symm_apply]
  rfl

end Main

end CFSG.HardMathSupport.U4FF
