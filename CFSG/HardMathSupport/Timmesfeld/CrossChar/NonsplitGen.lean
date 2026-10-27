module

public import CFSG.RankThree.PartOne.KC.LinearPlaneCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.Classical

section Nonsplit

variable {n p : ℕ} {F : Type} [Field F]

theorem commute_toLin'_of_mul_comm {R S : GL (Fin n) F} (hRS : R * S = S * R) :
    Commute (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F))
      (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)) := by
  have h := congrArg (fun T : GL (Fin n) F => Matrix.toLin' (T : Matrix (Fin n) (Fin n) F)) hRS
  simp only [Units.val_mul, Matrix.toLin'_mul] at h
  exact h

theorem toLin'_pow_eq_one {S : GL (Fin n) F} (hS : S ^ p = 1) :
    Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) ^ p = 1 := by
  rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hS, Units.val_one, Matrix.toLin'_one]
  rfl

theorem aeval_X_pow_sub_C_eq_zero {R : GL (Fin n) F} {c : Fˣ}
    (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    aeval (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F)) (X ^ p - C (c : F)) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hR]
  ext v i
  by_cases hi : i = v <;> simp [hi]

theorem mem_primaryFactors_X_pow_sub_C (hn : 0 < n) (hp : p ≠ 0) {R : GL (Fin n) F} {c : Fˣ}
    (hirr : Irreducible (X ^ p - C (c : F))) (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    (X ^ p - C (c : F)) ∈ primaryFactors (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F)) := by
  classical
  refine mem_primaryFactors_of_ne_zero hirr (monic_X_pow_sub_C _ hp)
    (v := Pi.single ⟨0, hn⟩ 1) ?_ ?_
  · intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp at this
  · rw [mem_primaryComponent, aeval_X_pow_sub_C_eq_zero hR]
    rfl

theorem mem_primaryComponent_X_pow_sub_C {R : GL (Fin n) F} {c : Fˣ}
    (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c) (v : Fin n → F) :
    v ∈ primaryComponent (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F)) (X ^ p - C (c : F)) := by
  rw [mem_primaryComponent, aeval_X_pow_sub_C_eq_zero hR]
  rfl

theorem squarefree_minpoly_of_irreducible {R : GL (Fin n) F} {c : Fˣ}
    (hirr : Irreducible (X ^ p - C (c : F))) (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly F (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F))) :=
  squarefree_minpoly_of_aeval_eq_zero hirr.squarefree (aeval_X_pow_sub_C_eq_zero hR)

theorem exists_eq_X_sub_C_of_mem_primaryFactors (hp0 : p ≠ 0) {ω : F}
    (hω : IsPrimitiveRoot ω p) {S : GL (Fin n) F} (hS : S ^ p = 1) {a : F[X]}
    (ha : a ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))) :
    ∃ ζ : F, a = X - C ζ := by
  have hirr := irreducible_of_mem_primaryFactors ha
  have hmon := monic_of_mem_primaryFactors ha
  have hdvd : a ∣ X ^ p - C (1 : F) := (mem_primaryFactors.mp ha).2.2.trans
    (minpoly.dvd F _ (by simp [toLin'_pow_eq_one hS]))
  have hne0 : (X ^ p - C (1 : F) : F[X]) ≠ 0 := (monic_X_pow_sub_C (1 : F) hp0).ne_zero
  have hsplit := (X_pow_sub_one_splits hω).of_dvd hne0 hdvd
  have hdeg : a.degree ≠ 0 := fun h0 =>
    hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr h0)
  obtain ⟨ζ, hζ⟩ := hsplit.exists_eval_eq_zero hdeg
  have h1 : X - C ζ ∣ a := dvd_iff_isRoot.mpr hζ
  have h2 : a ∣ X - C ζ := (irreducible_X_sub_C ζ).dvd_symm hirr h1
  exact ⟨ζ, eq_of_monic_of_associated hmon (monic_X_sub_C ζ) (associated_of_dvd_dvd h2 h1)⟩

theorem range_primaryProjection {x : Module.End F (Fin n → F)} (hsq : Squarefree (minpoly F x))
    {a : F[X]} (ha : a ∈ primaryFactors x) :
    LinearMap.range (primaryProjection x a) = primaryComponent x a := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact primaryProjection_mem hsq ha w
  · intro hv
    exact ⟨v, primaryProjection_of_mem hsq ha hv⟩

theorem primaryProjection_mul_self {x : Module.End F (Fin n → F)}
    (hsq : Squarefree (minpoly F x)) {a : F[X]} (ha : a ∈ primaryFactors x) :
    primaryProjection x a * primaryProjection x a = primaryProjection x a :=
  LinearMap.ext fun v => primaryProjection_of_mem hsq ha (primaryProjection_mem hsq ha v)

theorem primaryProjection_mul_of_ne {x : Module.End F (Fin n → F)}
    (hsq : Squarefree (minpoly F x)) {a b : F[X]} (ha : a ∈ primaryFactors x)
    (hb : b ∈ primaryFactors x) (hab : a ≠ b) :
    primaryProjection x a * primaryProjection x b = 0 :=
  LinearMap.ext fun v => primaryProjection_of_mem_ne hsq ha hb (Ne.symm hab)
    (primaryProjection_mem hsq hb v)

theorem le_finrank_primaryComponent (hn : 0 < n) (hp : p ≠ 0) {R S : GL (Fin n) F}
    (hRS : R * S = S * R) {c : Fˣ} (hirr : Irreducible (X ^ p - C (c : F)))
    (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hsqS : Squarefree (minpoly F (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)))) {a : F[X]}
    (ha : a ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))) :
    p ≤ finrank F (primaryComponent (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)) a) := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsqS ha)
  have h := natDegree_le_finrank_of_stable (mem_primaryFactors_X_pow_sub_C hn hp hirr hR)
    (U := primaryComponent (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)) a)
    (fun u hu => apply_mem_primaryComponent (commute_toLin'_of_mul_comm hRS) hu) hy
    (mem_primaryComponent_X_pow_sub_C hR y) hy0
  rwa [natDegree_X_pow_sub_C] at h

theorem suppGroup_le_blockImage {S : GL (Fin n) F}
    (hsq : Squarefree (minpoly F (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)))) {ζ : F}
    (ha : (X - C ζ : F[X]) ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)))
    {g : (Fin n → F) ≃ₗ[F] (Fin n → F)}
    (hg : g ∈ suppGroup (primaryProjection (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))
      (X - C ζ)))
    {A : SpecialLinearGroup (Fin n) F}
    (hA : ∀ v, Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) v = g v) :
    SpecialLinearGroup.toGL A ∈ blockImage hsq ⟨X - C ζ, ha⟩ := by
  set x := Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) with hx
  set P := primaryProjection x (X - C ζ) with hP
  obtain ⟨hdet, hc, hf⟩ := hg
  have hPP : ∀ v, P (P v) = P v := fun v =>
    primaryProjection_of_mem hsq ha (primaryProjection_mem hsq ha v)
  have hxP : ∀ v, x (P v) = ζ • P v := by
    intro v
    have h1 := mem_primaryComponent.1 (primaryProjection_mem hsq ha v)
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply] at h1
    exact sub_eq_zero.1 h1
  have hPx : ∀ v, P (x v) = x (P v) := fun v => by
    have := (commute_aeval (Commute.refl x) (primaryIdempotent x (X - C ζ))).eq
    exact (congrArg (fun T : Module.End F (Fin n → F) => T v) this).symm
  have hgx : ∀ v, g (x v) = x (g v) := by
    intro v
    have e1 : x v = ζ • P v + (x v - P (x v)) := by rw [hPx, hxP]; abel
    have e2 : g v - P (g v) = v - P v := by rw [← hc, ← map_sub, hf]
    have e3 : g v = P (g v) + (v - P v) := by rw [← e2]; abel
    calc g (x v) = g (ζ • P v + (x v - P (x v))) := by rw [← e1]
      _ = ζ • P (g v) + (x v - P (x v)) := by rw [map_add, map_smul, hc, hf]
      _ = x (g v) := by
        conv_rhs => rw [e3]
        rw [map_add, hxP, map_sub, hPx]
  have hcomm : SpecialLinearGroup.toGL A * S = S * SpecialLinearGroup.toGL A := by
    refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    change Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) (x v) =
      x (Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) v)
    rw [hA, hA]
    exact hgx v
  have hfix : ∀ k : primaryFactors x, k ≠ ⟨X - C ζ, ha⟩ →
      ∀ v ∈ primaryComponent x (k : F[X]),
        Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) v =
          v := by
    intro k hk v hv
    have h0 : P v = 0 := primaryProjection_of_mem_ne hsq ha k.2 (fun hh => hk (Subtype.ext hh)) hv
    change Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) v = v
    rw [hA]
    have := hf v
    rwa [h0, sub_zero] at this
  refine mem_blockImage_of_restrict hsq ⟨X - C ζ, ha⟩ rfl hcomm hfix ?_
  intro r hr
  have : Fact (Irreducible (X - C ζ : F[X])) := ⟨irreducible_X_sub_C ζ⟩
  have hrg : (r : Module.End F (Fin n → F)) = (g : Module.End F (Fin n → F)) :=
    LinearMap.ext fun v => by rw [hr]; exact hA v
  refine det_eq_one_of_restrictScalars (natDegree_X_sub_C ζ) _ ?_
  have hW : primaryComponent x (X - C ζ) = LinearMap.range P :=
    (range_primaryProjection hsq ha).symm
  have hmaps : primaryComponent x (X - C ζ) ≤
      (primaryComponent x (X - C ζ)).comap (r : Module.End F (Fin n → F)) :=
    fun v hv => apply_mem_primaryComponent ((mem_commutant _).mp r.2) hv
  have h1 : (commutantRestrict (X - C ζ) r).restrictScalars F =
      (r : Module.End F (Fin n → F)).restrict hmaps := rfl
  rw [h1, det_restrict_eq_det _ _ hW (primaryProjection_mul_self hsq ha) _
    (fun v => by rw [hrg]; exact hc v) (fun v => by rw [hrg]; exact hf v) hmaps, hrg]
  exact (det_eq_one_iff g).mp hdet

theorem exists_mixing_mem_blockImage (hn : 0 < n) (hp : p ≠ 0) {R S : GL (Fin n) F}
    (hRS : R * S = S * R) {c : Fˣ} (hirr : Irreducible (X ^ p - C (c : F)))
    (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hsqS : Squarefree (minpoly F (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)))) {a a' : F[X]}
    (ha : a ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)))
    (ha' : a' ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))) (haa' : a ≠ a') :
    ∃ β : Module.End F (Fin n → F),
      primaryProjection (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)) a * β = β ∧
      β * primaryProjection (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)) a' = β ∧ β ≠ 0 ∧
      (∃ g ∈ blockImage (squarefree_minpoly_of_irreducible hirr hR)
          ⟨X ^ p - C (c : F), mem_primaryFactors_X_pow_sub_C hn hp hirr hR⟩,
        ∀ v, Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) v = v + β v) ∧
      2 ≤ mult (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F))
        ⟨X ^ p - C (c : F), mem_primaryFactors_X_pow_sub_C hn hp hirr hR⟩ := by
  set xR := Matrix.toLin' (R : Matrix (Fin n) (Fin n) F) with hxR
  set xS := Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) with hxS
  have hsqR := squarefree_minpoly_of_irreducible hirr hR
  have hh := mem_primaryFactors_X_pow_sub_C hn hp hirr hR
  have hcomm : Commute xR xS := commute_toLin'_of_mul_comm hRS
  have hex : Commute (primaryProjection xS a') xR := (commute_aeval hcomm _).symm
  have hex' : Commute (primaryProjection xS a) xR := (commute_aeval hcomm _).symm
  have hPR : ∀ v, primaryProjection xR (X ^ p - C (c : F)) v = v := fun v =>
    primaryProjection_of_mem hsqR hh (mem_primaryComponent_X_pow_sub_C hR v)
  have hne : ∀ {b : F[X]}, b ∈ primaryFactors xS →
      primaryProjection xS b * primaryProjection xR (X ^ p - C (c : F)) ≠ 0 := by
    intro b hb h0
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsqS hb)
    have h1 := LinearMap.congr_fun h0 y
    rw [Module.End.mul_apply, hPR, primaryProjection_of_mem hsqS hb hy] at h1
    exact hy0 h1
  obtain ⟨β, hβ, hβ1, hβ2, hβ0, hββ, hkill, hdet, hmult⟩ := exists_mixing_unipotent hsqR hh hex
    hex' (primaryProjection_mul_self hsqS ha') (primaryProjection_mul_self hsqS ha)
    (primaryProjection_mul_of_ne hsqS ha' ha (Ne.symm haa')) (hne ha') (hne ha)
  obtain ⟨g, hg, hgv⟩ := exists_mem_blockImage_one_add hsqR (a0 := R) rfl
    ⟨X ^ p - C (c : F), hh⟩ β hβ hββ hkill hdet
  exact ⟨β, hβ1, hβ2, hβ0, ⟨g, hg, hgv⟩, hmult⟩

theorem eq_top_of_nonsplit_blocks_le (hn : 0 < n) (hp2 : 2 ≤ p) (hpF : (p : F) ≠ 0) {ω : F}
    (hω : IsPrimitiveRoot ω p) {R S : GL (Fin n) F} (hRS : R * S = S * R) {c : Fˣ}
    (hirr : Irreducible (X ^ p - C (c : F))) (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hS : S ^ p = 1) (𝒢 : Subgroup (SpecialLinearGroup (Fin n) F))
    (hRb : ∀ (hsq : Squarefree (minpoly F (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F))))
      (h : primaryFactors (Matrix.toLin' (R : Matrix (Fin n) (Fin n) F))),
      blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL)
    (hSb : ∀ (hsq : Squarefree (minpoly F (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))))
      (h : primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))),
      blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL) :
    𝒢 = ⊤ := by
  classical
  have hp : p ≠ 0 := by omega
  set xS := Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) with hxS
  have hsqS : Squarefree (minpoly F xS) := squarefree_minpoly_of_pow_eq_one hpF
    (toLin'_pow_eq_one hS)
  have hsqR := squarefree_minpoly_of_irreducible hirr hR
  let e : Option (primaryFactors xS) → Module.End F (Fin n → F) := fun o =>
    o.elim 0 fun a => primaryProjection xS (a : F[X])
  have he_none : e none = 0 := rfl
  have he_some : ∀ a : primaryFactors xS, e (some a) = primaryProjection xS (a : F[X]) :=
    fun _ => rfl
  have hidem : ∀ i, e i * e i = e i := by
    rintro (_ | a)
    · rw [he_none, mul_zero]
    · rw [he_some]
      exact primaryProjection_mul_self hsqS a.2
  have horth : ∀ i j, i ≠ j → e i * e j = 0 := by
    rintro (_ | a) (_ | b) hij
    · exact absurd rfl hij
    · rw [he_none, zero_mul]
    · rw [he_none, mul_zero]
    · rw [he_some, he_some]
      exact primaryProjection_mul_of_ne hsqS a.2 b.2
        (fun hab => hij (congrArg some (Subtype.ext hab)))
  have hsum : ∑ i, e i = 1 := by
    rw [Fintype.sum_option, he_none, zero_add]
    simp only [he_some]
    rw [Finset.sum_coe_sort (primaryFactors xS) (fun a => primaryProjection xS a)]
    exact sum_primaryProjection hsqS
  set A : Finset (Option (primaryFactors xS)) := Finset.univ.filter (fun o => o ≠ none) with hA
  have hzA : (none : Option (primaryFactors xS)) ∉ A := by simp [hA]
  have hmemA : ∀ a : primaryFactors xS, some a ∈ A := fun a => by simp [hA]
  have hAne : A.Nonempty := by
    by_contra hne
    have hempty : primaryFactors xS = ∅ := by
      by_contra hne'
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hne'
      exact hne ⟨some ⟨a, ha⟩, hmemA _⟩
    have h1 := sum_primaryProjection hsqS
    rw [hempty, Finset.sum_empty] at h1
    have h2 := LinearMap.congr_fun h1 (Pi.single ⟨0, hn⟩ 1)
    have h3 := congrFun h2 ⟨0, hn⟩
    simp at h3
  have hinact : ∀ i, i ≠ none → i ∉ A → e i = 0 := by
    intro i hi hiA
    exact absurd (by simp [hA, hi]) hiA
  have hdim : ∀ i ∈ A, 2 ≤ finrank F (LinearMap.range (e i)) := by
    rintro (_ | a) hi
    · exact absurd hi hzA
    · rw [he_some, range_primaryProjection hsqS a.2]
      exact hp2.trans (le_finrank_primaryComponent hn hp hRS hirr hR hsqS a.2)
  set b₀ := Pi.basisFun F (Fin n) with hb₀
  set G : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) := 𝒢.map (slAction b₀) with hG
  have hGdet : ∀ g ∈ G, LinearEquiv.det g = 1 := by
    rintro _ ⟨s, -, rfl⟩
    exact det_slAction b₀ s
  have hsupp : ∀ i ∈ A, suppGroup (e none + e i) ≤ G := by
    rintro (_ | ⟨a, ha⟩) hi
    · exact absurd hi hzA
    rw [he_none, zero_add, he_some]
    obtain ⟨ζ, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp hω hS ha
    intro g hg
    obtain ⟨A', hA'⟩ := exists_slAction_eq b₀ hg.1
    have hAv : ∀ v, Matrix.toLin' (A' : Matrix (Fin n) (Fin n) F) v = g v := fun v => by
      rw [toLin'_apply_eq_slAction, hA']
    obtain ⟨s, hs𝒢, hs⟩ := hSb hsqS ⟨X - C ζ, ha⟩ (suppGroup_le_blockImage hsqS ha hg hAv)
    exact ⟨s, hs𝒢, (SpecialLinearGroup.toGL_injective hs) ▸ hA'⟩
  have hmix : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ β : Module.End F (Fin n → F),
      e i * β = β ∧ β * e j = β ∧ β ≠ 0 ∧ ∃ u ∈ G, ∀ v, u v = v + β v := by
    rintro (_ | ⟨a, ha⟩) hi (_ | ⟨a', ha'⟩) hj hij
    · exact absurd hi hzA
    · exact absurd hi hzA
    · exact absurd hj hzA
    have haa' : a ≠ a' := fun h' => hij (by subst h'; rfl)
    obtain ⟨β, hβ1, hβ2, hβ0, ⟨g, hg, hgv⟩, -⟩ :=
      exists_mixing_mem_blockImage hn hp hRS hirr hR hsqS ha ha' haa'
    obtain ⟨s, hs𝒢, hs⟩ := hRb hsqR _ hg
    refine ⟨β, hβ1, hβ2, hβ0, slAction b₀ s, ⟨s, hs𝒢, rfl⟩, fun v => ?_⟩
    have hsmat : (s : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) :=
      congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) hs
    rw [← toLin'_apply_eq_slAction, hsmat]
    exact hgv v
  have hmain := generation_of_blocks e hidem horth hsum none A hzA hAne hinact hdim G hGdet
    hsupp hmix
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨s', hs'𝒢, hs'⟩ := hmain (slAction b₀ s) (det_slAction b₀ s)
  exact (slAction_injective b₀ hs') ▸ hs'𝒢

end Nonsplit

end CFSG.HardMathSupport.Timmesfeld.CrossChar
