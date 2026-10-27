module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSpin

public section

namespace CFSG.AGLEmbedding.P1Lie

open CFSG.AGLEmbedding.CharPGen CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open CFSG.Open (GLBWeakCore)

section TypeB

variable {K : Type*} [Group K] [Finite K] {m : ℕ}

@[expose] def toStdBHom (m : ℕ) : (Fin m → ℤ) →+ (Fin m → ℤ) :=
  AddMonoidHom.mk' (toStdB m) (toStdB_add m)

theorem toStdBHom_apply (v : Fin m → ℤ) : toStdBHom m v = toStdB m v := rfl

@[expose, reducible] def typeBDatum (m : ℕ) (X : (Fin m → ℤ) → Subgroup K) :
    UniversalRootDatum K where
  rank := m
  cartan := cartanB m
  isFiniteType := isFiniteType_cartanB m
  divisible := ∅
  rootGroup := X

theorem rootsB_support {ε : Fin m → ℤ} (hε : ε ∈ roots (isFiniteType_cartanB m) ∅) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (toStdBHom m ε i ≠ 0 ∧ toStdBHom m ε j ≠ 0 ∧ toStdBHom m ε k ≠ 0) := by
  rw [rootsB_eq] at hε
  rintro ⟨h1, h2, h3⟩
  rw [toStdBHom_apply] at h1 h2 h3
  rcases hε with ⟨a, b, s, t, hab, hs, ht, he⟩ | ⟨a, s, hs, he⟩ <;> rw [he] at h1 h2 h3 <;>
    simp only [Pi.add_apply, Pi.single_apply, ne_eq] at h1 h2 h3 <;>
    split_ifs at h1 h2 h3 <;> simp_all

theorem weakCore_typeB {X : (Fin m → ℤ) → Subgroup K} {n : Fin m → K} {H : Fin m → Subgroup K}
    (hm : 3 ≤ m)
    (hct : IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanB m)).toCoxeterSystem
      (weylAction (isFiniteType_cartanB m)) (roots (isFiniteType_cartanB m) ∅) X n H)
    (hext : SteinbergExtras (typeBDatum m X) n H) {p : ℕ} (hp : p.Prime)
    (hX : ∀ γ ∈ roots (isFiniteType_cartanB m) ∅, IsPGroup p (X γ)) :
    GLBWeakCore p (posUnipotent (typeBDatum m X)) = ⊤ := by
  have e : ∀ {i j : Fin m} (hij : i ≠ j), ofStdB m (Pi.single i 1 + Pi.single j 1) ∈
      roots (isFiniteType_cartanB m) ∅ ∧ toStdBHom m (ofStdB m (Pi.single i 1 + Pi.single j 1)) =
        Pi.single i 1 + Pi.single j 1 ∧ ht (ofStdB m (Pi.single i 1 + Pi.single j 1)) =
        ((m : ℤ) - i) + ((m : ℤ) - j) := by
    intro i j hij
    refine ⟨ofStdB_mem_rootsB m (Or.inl ⟨i, j, 1, 1, hij, Or.inl rfl, Or.inl rfl, rfl⟩),
      toStdB_ofStdB m _, ?_⟩
    have := ht_of_toStdB_eq_add m (γ := ofStdB m (Pi.single i 1 + Pi.single j 1)) (i := i)
      (j := j) (s := 1) (t := 1) (toStdB_ofStdB m _)
    rw [this]; ring
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨r1, t1, g1⟩ := e h01
  obtain ⟨r2, t2, g2⟩ := e h02
  obtain ⟨r3, t3, g3⟩ := e h12
  refine weakCore_posUnipotent_eq_top_of_image_triple (D := typeBDatum m X) hct hext hp
    (by change 2 ≤ m; omega) hX rfl (toStdBHom m) (fun ε hε i j k => rootsB_support hε) h01 h02
    h12 r1 r2 r3 t1 t2 t3 ?_ ?_ ?_
  · rw [g1]; omega
  · rw [g2]; omega
  · rw [g3]; omega

end TypeB

section TypeD

variable {K : Type*} [Group K] [Finite K] {m : ℕ}

@[expose] def toStdDHom (m : ℕ) : (Fin m → ℤ) →+ (Fin m → ℤ) :=
  AddMonoidHom.mk' (toStdD m) (toStdD_add m)

theorem toStdDHom_apply (v : Fin m → ℤ) : toStdDHom m v = toStdD m v := rfl

@[expose, reducible] def typeDDatum (m : ℕ) (X : (Fin m → ℤ) → Subgroup K) :
    UniversalRootDatum K where
  rank := m
  cartan := cartanD m
  isFiniteType := isFiniteType_cartanD m
  divisible := ∅
  rootGroup := X

theorem rootsD_support (hm : m ≠ 1) {ε : Fin m → ℤ} (hε : ε ∈ roots (isFiniteType_cartanD m) ∅)
    {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (toStdDHom m ε i ≠ 0 ∧ toStdDHom m ε j ≠ 0 ∧ toStdDHom m ε k ≠ 0) := by
  rw [rootsD_eq m hm] at hε
  rintro ⟨h1, h2, h3⟩
  rw [toStdDHom_apply] at h1 h2 h3
  obtain ⟨a, b, s, t, hab, hs, ht, he⟩ := hε
  rw [he] at h1 h2 h3
  simp only [Pi.add_apply, Pi.single_apply, ne_eq] at h1 h2 h3
  split_ifs at h1 h2 h3 <;> simp_all

theorem weakCore_typeD {X : (Fin m → ℤ) → Subgroup K} {n : Fin m → K} {H : Fin m → Subgroup K}
    (hm : 4 ≤ m)
    (hct : IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanD m)).toCoxeterSystem
      (weylAction (isFiniteType_cartanD m)) (roots (isFiniteType_cartanD m) ∅) X n H)
    (hext : SteinbergExtras (typeDDatum m X) n H) {p : ℕ} (hp : p.Prime)
    (hX : ∀ γ ∈ roots (isFiniteType_cartanD m) ∅, IsPGroup p (X γ)) :
    GLBWeakCore p (posUnipotent (typeDDatum m X)) = ⊤ := by
  have hm1 : m ≠ 1 := by omega
  have e : ∀ {i j : Fin m} (hij : i ≠ j), ∃ γ ∈ roots (isFiniteType_cartanD m) ∅,
      toStdDHom m γ = Pi.single i 1 + Pi.single j 1 ∧
        ht γ = ((m : ℤ) - 1 - i) + ((m : ℤ) - 1 - j) := by
    intro i j hij
    obtain ⟨γ, hγ, h⟩ := exists_mem_rootsD_toStdD_eq m hij (Or.inl rfl) (Or.inl rfl)
    refine ⟨γ, hγ, h, ?_⟩
    have := ht_of_toStdD_eq_add m hm1 (s := 1) (t := 1) h
    rw [this]; ring
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨γ1, r1, t1, g1⟩ := e h01
  obtain ⟨γ2, r2, t2, g2⟩ := e h02
  obtain ⟨γ3, r3, t3, g3⟩ := e h12
  refine weakCore_posUnipotent_eq_top_of_image_triple (D := typeDDatum m X) hct hext hp
    (by change 2 ≤ m; omega) hX rfl (toStdDHom m) (fun ε hε i j k => rootsD_support hm1 hε) h01
    h02 h12 r1 r2 r3 t1 t2 t3 ?_ ?_ ?_
  · rw [g1]; simp only []; omega
  · rw [g2]; simp only []; omega
  · rw [g3]; simp only []; omega

end TypeD

theorem exists_pGroup_weakCore_of_spin {G : Type} [Group G] [Finite G] {σ : Type} [Fintype σ]
    [DecidableEq σ] {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (i : σ) {Q : QuadraticForm F (σ → F)} {Q₀ : (σ → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hker : ∀ x ∈ (spinMatrix Q).ker, x ^ 2 = 1) [Finite (spinGroup Q)]
    {D : UniversalRootDatum (spinGroup Q)} (hU : IsPGroup p (posUnipotent D))
    (hcore : GLBWeakCore p (posUnipotent D) = ⊤) (e : G ≃* StatedProj (StatedOmega Q₀)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  let π : spinGroup Q →* G := e.symm.toMonoidHom.comp (spinToStatedProj Q hR)
  have hπ : Function.Surjective π := e.symm.surjective.comp (spinToStatedProj_surjective Q hR)
  have hinj : ∀ x ∈ posUnipotent D, π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : spinToStatedProj Q hR x = 1 := e.symm.injective (by rw [map_one]; exact hx1)
    have hsc : spinMatrix Q x ∈ StatedScalars σ F :=
      Subgroup.mem_comap.1 ((ker_spinToStatedProj Q hR).le (MonoidHom.mem_ker.2 hmk))
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have hm1 : spinMatrix Q x = 1 :=
      eq_one_of_mem_statedScalars_of_pow_gl i hsc (by rw [← map_pow, hk', map_one])
    exact eq_one_of_sq_eq_one_of_pow_prime_pow hp2 (hker x (MonoidHom.mem_ker.2 hm1)) hk'
  exact ⟨(posUnipotent D).map π, hU.map π, weakCore_map_eq_top Fact.out π hπ hinj hcore⟩

theorem exists_pGroup_weakCore_of_model_pomegaOdd {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  obtain ⟨⟨hp, -, hn, hp2⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP hp2
  have : Finite (spinGroup (quadOdd n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have hX : ∀ γ ∈ (oddDatum n F).roots, IsPGroup p ((oddDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization SpinOdd.isParametrization hγ
  have hext := oddDatum_steinbergExtras (n := n) (K := F) h2
  exact exists_pGroup_weakCore_of_spin hp2 (Sum.inr (Sum.inr ())) (range_spinMatrix_quadOdd h2 hn)
    (fun x hx => sq_eq_one_of_eq_one_or_eq_neg_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).1 hx))
    (D := oddDatum n F) (isPGroup_iSup_pos hext hX)
    (weakCore_typeB hn (oddDatum_isCTGroupDatum n F (oddDatum_iSup_eq_top n F h2 hn)) hext
      Fact.out hX) e

theorem exists_pGroup_weakCore_of_model_pomegaPlus {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G .POmegaPlus n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  obtain ⟨⟨hp, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hX : ∀ γ ∈ (plusDatum n F hn3).roots, IsPGroup p ((plusDatum n F hn3).rootGroup γ) :=
    fun γ hγ => isPGroup_of_isParametrization (SpinPlus.isParametrization (K := F) hn3) hγ
  have hext := plusDatum_steinbergExtras (n := n) (K := F) hn3
  exact exists_pGroup_weakCore_of_spin hp2 (Sum.inl ⟨0, by omega⟩) (range_spinMatrix_quadPlus hn3)
    (fun x hx => sq_eq_one_of_eq_one_or_eq_neg_one ((mem_ker_spinMatrix_quadPlus_iff x).1 hx))
    (D := plusDatum n F hn3) (isPGroup_iSup_pos hext hX)
    (weakCore_typeD (by omega) (plusDatum_isCTGroupDatum hn3 (plusDatum_iSup_eq_top n F hn3))
      hext Fact.out hX) e

theorem exists_pGroup_weakCore_of_model_pomegaMinus {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G .POmegaMinus n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  obtain ⟨⟨hp, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hX : ∀ γ ∈ (Twisted.minusDatum n hirr).roots,
      IsPGroup p ((Twisted.minusDatum n hirr).rootGroup γ) := fun γ hγ =>
    isPGroup_minusRootGroup hirr hγ
  have hext := Twisted.minusDatum_steinbergExtras n hirr
  exact exists_pGroup_weakCore_of_spin hp2 (Sum.inr (Sum.inr 0))
    (range_spinMatrix_quadMinus hn hirr) (fun x hx => sq_eq_one_of_eq_one_or_eq_neg_one
      ((mem_ker_spinMatrix_quadMinus_iff hirr x).1 hx))
    (D := Twisted.minusDatum n hirr) (isPGroup_iSup_pos hext hX)
    (weakCore_typeB (m := n - 1) (by omega) (Twisted.minusDatum_isCTGroupDatum n hirr hn) hext
      Fact.out hX) e

end CFSG.AGLEmbedding.P1Lie

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem weakCharPGenAt_bOdd : WeakCharPGenAt IsBOddIndex := by
  intro K _ _ _ _ d ⟨r, q, hr, hd⟩ ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_of_model_pomegaOdd
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr e)
  exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T

theorem weakCharPGenAt_d : WeakCharPGenAt IsDIndex := by
  intro K _ _ _ _ d ⟨r, q, hd⟩ ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_of_model_pomegaPlus hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
  exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T

theorem weakCharPGenAt_twistedD : WeakCharPGenAt IsTwistedDIndex := by
  intro K _ _ _ _ d ⟨r, q, hd⟩ ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_of_model_pomegaMinus hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
  exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T

end CFSG.AGLEmbedding
