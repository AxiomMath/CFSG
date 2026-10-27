module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmallNorm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmallSyl

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

section Four

theorem permFour_pow_four_or_pow_three : ∀ σ : Perm (Fin 4), σ ^ 4 = 1 ∨ σ ^ 3 = 1 := by
  decide

variable {N : ℕ} {U : Finset (Fin N)}

theorem restr_pow (hU : U.card = 4) {w : Perm (Fin N)} (hw : FixOut U w) (k : ℕ) :
    restr hU (w ^ k) (hw.pow k) = restr hU w hw ^ k := by
  induction k with
  | zero =>
    calc restr hU (w ^ 0) (hw.pow 0) = restr hU 1 FixOut.one :=
          restr_congr hU (pow_zero w) _ _
      _ = 1 := restr_one hU
      _ = restr hU w hw ^ 0 := (pow_zero _).symm
  | succ k ih =>
    calc restr hU (w ^ (k + 1)) (hw.pow (k + 1)) = restr hU (w ^ k * w) ((hw.pow k).mul hw) :=
          restr_congr hU (pow_succ w k) _ _
      _ = restr hU (w ^ k) (hw.pow k) * restr hU w hw := restr_mul hU (hw.pow k) hw
      _ = restr hU w hw ^ k * restr hU w hw := by rw [ih]
      _ = restr hU w hw ^ (k + 1) := (pow_succ _ k).symm

theorem pow_four_of_fixOut (hU : U.card = 4) {w : Perm (Fin N)} (hw : FixOut U w) {e : ℕ}
    (he : w ^ 2 ^ e = 1) : w ^ 4 = 1 := by
  have h1 : restr hU w hw ^ 2 ^ e = 1 :=
    (restr_pow hU hw (2 ^ e)).symm.trans
      ((restr_congr hU he (hw.pow _) FixOut.one).trans (restr_one hU))
  have h4 : restr hU w hw ^ 4 = 1 := by
    rcases permFour_pow_four_or_pow_three (restr hU w hw) with h | h
    · exact h
    · have hd1 : orderOf (restr hU w hw) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one h1
      have hd3 : orderOf (restr hU w hw) ∣ 3 := orderOf_dvd_of_pow_eq_one h
      have hcop : Nat.Coprime (2 ^ e) 3 := Nat.Coprime.pow_left e (by norm_num)
      have ho : orderOf (restr hU w hw) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd3
      rw [orderOf_eq_one_iff.mp ho, one_pow]
  exact restr_injective hU (hw.pow 4) FixOut.one
    ((restr_pow hU hw 4).trans (h4.trans (restr_one hU).symm))

end Four

namespace AltGenCore

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenCore A R T g n Φ)
include s

theorem card_R_le_four : Nat.card R ≤ 4 := by
  classical
  have := Fintype.ofFinite G
  have hR := s.sec3.sylowR
  have hRY : ∀ r ∈ R, r ∈ Φ.range := fun r hr => s.le_range' (s.R_le hr)
  let θ : G → Perm (Fin (n + 4)) := fun k =>
    if h : k ∈ Φ.range then
      ((MonoidHom.ofInjective s.injective).symm ⟨k, h⟩ : alternatingGroup (Fin (n + 4)))
    else 1
  have hθ : ∀ π : alternatingGroup (Fin (n + 4)), θ (Φ π) = π := by
    intro π
    have h1 : (⟨Φ π, ⟨π, rfl⟩⟩ : Φ.range) = MonoidHom.ofInjective s.injective π :=
      Subtype.ext (MonoidHom.ofInjective_apply _).symm
    show (if h : Φ π ∈ Φ.range then _ else _) = _
    rw [dite_eq_left_of_eq_true (eq_true ⟨π, rfl⟩), h1, MulEquiv.symm_apply_apply]
  set S : Finset G := (R : Set G).toFinset with hS
  have hinj : Set.InjOn θ S := by
    intro k hk k' hk' h
    rw [hS, Set.coe_toFinset] at hk hk'
    obtain ⟨π, rfl⟩ := hRY k hk
    obtain ⟨π', rfl⟩ := hRY k' hk'
    rw [hθ, hθ] at h
    rw [Subtype.ext h]
  set U : Finset (Fin (n + 4)) := Finset.univ.map (Fin.natAddEmb n) with hUdef
  have hU : U.card = 4 := by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcard : Nat.card R = S.card := by
    rw [hS, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  rw [hcard, ← Finset.card_image_of_injOn hinj]
  apply card_le_four_of_fixOut hU
  intro w hw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  rw [hS, Set.mem_toFinset] at hk
  obtain ⟨π, rfl⟩ := hRY k hk
  rw [hθ]
  have hfix : FixOut U (π : Perm (Fin (n + 4))) := by
    intro y hy
    have hyn : (y : ℕ) < n := by
      by_contra hyn
      apply hy
      rw [hUdef, Finset.mem_map]
      refine ⟨⟨(y : ℕ) - n, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd]
      omega
    have h1 := s.fix_of_mem_centralizer (hR.le hk) ⟨y, hyn⟩
    have h2 : (Fin.castLEEmb (by omega : n ≤ n + 4) ⟨y, hyn⟩ : Fin (n + 4)) = y :=
      Fin.ext (by simp)
    rw [h2] at h1
    exact h1
  refine ⟨hfix, π.2, ?_⟩
  obtain ⟨e, he⟩ := hR.isPGroup ⟨Φ π, hk⟩
  have he' : π ^ 2 ^ e = 1 := by
    apply s.injective
    rw [map_pow, map_one]
    exact congrArg Subtype.val he
  exact pow_four_of_fixOut hU hfix (by rw [← Subgroup.coe_pow, he']; rfl)

theorem card_le_four_of_isPGroup_centralizer {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ centralizer (A : Set G)) : Nat.card Q ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ a ∣ Nat.card (centralizer (A : Set G)) := ha ▸ Subgroup.card_dvd_of_le hQK
  have hle : a ≤ (Nat.card (centralizer (A : Set G))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have hR := s.sec3.sylowR.card_eq
  calc Nat.card Q = 2 ^ a := ha
    _ ≤ 2 ^ (Nat.card (centralizer (A : Set G))).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) hle
    _ = Nat.card R := hR.symm
    _ ≤ 4 := s.card_R_le_four

end AltGenCore

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

@[expose] noncomputable def actAlt : normalizer (A : Set G) →* MulAut (alternatingGroup (Fin n)) :=
  (MulAut.congr s.psiA.symm).toMonoidHom.comp (Lemma39.normConj A)

theorem actAlt_spec (x : normalizer (A : Set G)) (z : alternatingGroup (Fin n)) :
    Φ (liftA s.six_le (s.actAlt x z)) = (x : G) * Φ (liftA s.six_le z) * (x : G)⁻¹ := by
  show Φ (liftA s.six_le ((MulAut.congr s.psiA.symm) (Lemma39.normConj A x) z)) = _
  rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← psiA_apply s, MulEquiv.apply_symm_apply, Lemma39.normConj_apply, psiA_apply]

theorem actAlt_eq_one_iff (x : normalizer (A : Set G)) :
    s.actAlt x = 1 ↔ (x : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨z, rfl⟩ := s.exists_liftA_eq ha
    have h1 := s.actAlt_spec x z
    rw [h, MulAut.one_apply] at h1
    calc Φ (liftA s.six_le z) * (x : G) = (x : G) * Φ (liftA s.six_le z) * (x : G)⁻¹ * x := by
          rw [← h1]
      _ = x * Φ (liftA s.six_le z) := by group
  · intro h
    ext z : 1
    apply liftA_injective s.six_le
    apply s.injective
    rw [s.actAlt_spec, MulAut.one_apply]
    have hc : Φ (liftA s.six_le z) * (x : G) = x * Φ (liftA s.six_le z) :=
      mem_centralizer_iff.mp h _ (s.liftA_mem z)
    calc (x : G) * Φ (liftA s.six_le z) * (x : G)⁻¹ =
        Φ (liftA s.six_le z) * x * (x : G)⁻¹ := by rw [hc]
      _ = Φ (liftA s.six_le z) := by group

theorem card_le_of_isPGroup_le_normalizer (hn : n = 6 ∨ n = 7)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (A : Set G)) :
    Nat.card P ≤ 2 ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn4 : 4 ≤ n := by omega
  have hrange : ∀ x : normalizer (A : Set G), s.actAlt x ∈ (conjPerm n).range := by
    intro x
    obtain ⟨σ, hσ⟩ := s.exists_conjPerm_small hn x.2
    refine ⟨σ, MulEquiv.ext fun z => ?_⟩
    apply liftA_injective s.six_le
    apply s.injective
    rw [hσ z, s.actAlt_spec]
  set f : ↥P →* MulAut (alternatingGroup (Fin n)) := s.actAlt.comp (inclusion hPN) with hf
  have hker : Nat.card f.ker ≤ 4 := by
    have h1 : Nat.card f.ker = Nat.card (f.ker.map P.subtype) :=
      (Subgroup.card_map_of_injective P.subtype_injective).symm
    rw [h1]
    refine s.card_le_four_of_isPGroup_centralizer (hP.to_le (Subgroup.map_subtype_le f.ker)) ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : f y = 1 := hy
    rw [hf, MonoidHom.comp_apply] at hy'
    exact (s.actAlt_eq_one_iff _).mp hy'
  have himg : Nat.card f.range ≤ 2 ^ 4 := by
    obtain ⟨a, ha⟩ := (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
    have hle : f.range ≤ (conjPerm n).range := by
      rintro _ ⟨y, rfl⟩
      exact hrange _
    have hdvd : Nat.card f.range ∣ Nat.card (Perm (Fin n)) := by
      have h1 := Subgroup.card_dvd_of_le hle
      have h2 : Nat.card (conjPerm n).range = Nat.card (Perm (Fin n)) :=
        Nat.card_congr (MonoidHom.ofInjective (conjPerm_injective hn4)).toEquiv.symm
      rwa [h2] at h1
    rw [ha] at hdvd ⊢
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
    have hle' : a ≤ 4 := by
      rcases hn with rfl | rfl
      · have h720 : Nat.factorial 6 = 2 ^ 4 * 45 := by decide
        rw [h720] at hdvd
        by_contra hgt
        have h5 : 2 ^ 5 ∣ 2 ^ 4 * 45 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
        exact absurd h5 (by decide)
      · have h5040 : Nat.factorial 7 = 2 ^ 4 * 315 := by decide
        rw [h5040] at hdvd
        by_contra hgt
        have h5 : 2 ^ 5 ∣ 2 ^ 4 * 315 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
        exact absurd h5 (by decide)
    exact Nat.pow_le_pow_right (by norm_num) hle'
  have h := card_ker_mul_card_range f
  calc Nat.card P = Nat.card f.ker * Nat.card f.range := h.symm
    _ ≤ 4 * 2 ^ 4 := Nat.mul_le_mul hker himg
    _ = 2 ^ 6 := by norm_num

theorem rootFusionAt_small (hn : n = 6 ∨ n = 7) :
    RootFusionAt A Φ := by
  intro π x hπ2 hπ1 hx
  have hπ2' : (π : Perm (Fin (n + 4))) * π = 1 := by
    rw [← Subgroup.coe_mul, hπ2]
    rfl
  have hπ1' : (π : Perm (Fin (n + 4))) ≠ 1 := fun h => hπ1 (Subtype.ext h)
  obtain ⟨j, hj1, hct, hj4⟩ := exists_cycleType_eq_replicate hπ1' hπ2' π.2
  rw [Fintype.card_fin] at hj4
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
  · rw [hct]
    rfl
  · exfalso
    obtain ⟨P, hPcard, hPC⟩ := exists_card_eq_le_centralizer_of_cycleType (N := n + 4) (by omega)
      (π := π) (by rw [hct]; rfl)
    set t := x * Φ π * x⁻¹ with ht
    have ht2 : t ^ 2 = 1 := by
      rw [sq, ht]
      calc x * Φ π * x⁻¹ * (x * Φ π * x⁻¹) = x * Φ (π * π) * x⁻¹ := by rw [map_mul]; group
        _ = 1 := by rw [hπ2, map_one, mul_one, mul_inv_cancel]
    have ht1 : t ≠ 1 := by
      intro h1
      apply hπ1
      apply s.injective
      rw [map_one]
      calc Φ π = x⁻¹ * (x * Φ π * x⁻¹) * x := by group
        _ = 1 := by rw [← ht, h1, mul_one, inv_mul_cancel]
    have hCN : centralizer ({t} : Set G) ≤ normalizer (A : Set G) := by
      have h := Lemma39.centralizer_le_normalizer_rightConjugate s.sec3.hyp 1 (t := t)
        (by rw [rightConjugate_one]; exact hx) ht1 ht2
      rwa [rightConjugate_one] at h
    set P' : Subgroup G := (P.map Φ).map (MulAut.conj x).toMonoidHom with hP'
    have hP'card : Nat.card P' = 2 ^ 7 := by
      rw [hP', Subgroup.card_map_of_injective (MulAut.conj x).injective,
        Subgroup.card_map_of_injective s.injective, hPcard]
    have hP'N : P' ≤ normalizer (A : Set G) := by
      refine le_trans ?_ hCN
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have hpπ : p * π = π * p := mem_centralizer_singleton_iff.mp (hPC hp)
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht]
      calc x * Φ p * x⁻¹ * (x * Φ π * x⁻¹) = x * Φ (p * π) * x⁻¹ := by rw [map_mul]; group
        _ = x * Φ (π * p) * x⁻¹ := by rw [hpπ]
        _ = x * Φ π * x⁻¹ * (x * Φ p * x⁻¹) := by rw [map_mul]; group
    have h := s.card_le_of_isPGroup_le_normalizer hn (IsPGroup.of_card hP'card) hP'N
    rw [hP'card] at h
    exact absurd h (by norm_num)

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
