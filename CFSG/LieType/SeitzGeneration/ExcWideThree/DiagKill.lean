module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed
public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagRootCheck

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree

section GLKill


variable {τ : Tag}

structure LangGLData (τ : Tag) (K : Type) [Field K] [Finite K] (A : Subgroup (ModGL τ K)) where
  w : WeylGroup τ
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ Nat.card K
  g0 : ModGL τ (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)
  hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w
  c : ModGL τ K
  hcN : c ∈ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K))
  hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K)) (c * x * c⁻¹ : ModGL τ K) ∈
    (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom

@[expose] def LangGLData.Kills {τ : Tag} {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL τ K)}
    (D : LangGLData τ K A) (α : Fin τ.rank → ℤ) : Prop :=
  ∀ x ∈ A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
    rootDiagUnit τ a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL τ K) * D.g0 ∧ rootChar a α = 1

theorem kill_core_gl (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] (A : Subgroup (ModGL τ K)) (D : LangGLData τ K A)
    (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) (hk : D.Kills α) :
    ∃ uL : ModGL τ (AlgebraicClosure K), uL ∈ adjointGroup τ (AlgebraicClosure K) ∧ uL ≠ 1 ∧
      uL ^ ringChar K = 1 ∧ Units.map (entrywiseHom D.Fr) uL = uL ∧
      ∀ y ∈ A, uL * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * y * D.c⁻¹ : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * y * D.c⁻¹ : ModGL τ K) * uL := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL τ (AlgebraicClosure K),
      Units.map (entrywiseHom D.Fr) g = entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e D.g0 =
      D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
    rw [← hFrob]
    exact D.hg0
  have hBF : ∀ z : ModGL τ K, entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) z := by
    intro z
    rw [← hFrob]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed D.Fr D.hFr z
  have hk' : ∀ y : A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * (y : ModGL τ K) * D.c⁻¹ : ModGL τ K) * D.g0 ∧
        rootChar a α = 1 := fun y => hk y.1 y.2
  choose a ha using hk'
  have hconj : ∀ y : A, rootDiagUnit τ (a y) =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (rootDiagUnit τ (a y)) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ := by
    intro y
    have hF : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (rootDiagUnit τ (a y)) =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ * rootDiagUnit τ (a y) *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
      rw [(ha y).1, map_mul, map_mul, map_inv, hg0F, hBF]
      group
    rw [hF]
    group
  have hrel : ∀ y : A, ∀ v, rootChar (a y) (D.w • v) = rootChar (a y) v ^ (ringChar K ^ e) :=
    fun y v => rootChar_frob_of_conj (a y) D.w (hconj y) v
  have hαS : α ∈ familyKernel a := ⟨hα, fun y => (ha y).2⟩
  have hSw : ∀ β ∈ familyKernel a, D.w • β ∈ familyKernel a ∧ D.w⁻¹ • β ∈ familyKernel a :=
    fun β hβ => family_w_stab a (fun i v => hrel i v) hβ
  have hwS : (fun β => D.w • β) '' familyKernel a = familyKernel a :=
    image_eq_of_mem_stab _ D.w (fun β hβ => (hSw β hβ).1) (fun β hβ => (hSw β hβ).2)
  obtain ⟨x, hx, n, β, hn, hper, hβS, horth, hgβ⟩ := kill_cycle_periodic hτ a D.w hwS hαS
  have hxstab : ∀ i, x ∈ rootCharStabilizerSubgroup (a i) :=
    fun i => closure_refl_stab a (familyKernel a) (fun γ hγ => hγ) hx i
  have hxM : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x ∈
      familyGroup (K := AlgebraicClosure K) a :=
    canonicalRep_closure_mem_familyGroup a hx
  have hxw_img : (fun γ => (x * D.w) • γ) '' familyKernel a = familyKernel a := by
    apply image_eq_of_mem_stab
    · intro γ hγ
      rw [mul_smul]
      exact stab_mem_familyKernel a hxstab (hSw γ hγ).1
    · intro γ hγ
      rw [mul_inv_rev, mul_smul]
      exact (hSw _ (stab_mem_familyKernel a (fun i => inv_mem (hxstab i)) hγ)).2
  have hQnorm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) ∈
      Subgroup.normalizer (familyGroup (K := AlgebraicClosure K) a :
        Set (ModGL τ (AlgebraicClosure K))) :=
    canonicalRep_mem_normalizer_of_image hxw_img
  obtain ⟨k, hk, hkxw⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) x D.w
  have hQk : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) =
      k⁻¹ * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w) := by
    rw [hkxw]
    group
  have hm_mem : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ ∈
        familyGroup (K := AlgebraicClosure K) a := by
    have hm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x)⁻¹ * k := by
      rw [hQk]
      group
    rw [hm]
    exact mul_mem (inv_mem hxM) (torus_le_familyGroup a hk)
  have hn_lang : D.g0⁻¹ * entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e D.g0 =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹) *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    rw [hg0F]
    group
  have hLang := lang_familyGroup (ringChar K) a e he _ hQnorm
  obtain ⟨ζ, hζ, hζQ⟩ := exists_mem_lang_conj (entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e)
    hm_mem hn_lang hLang
  have hg1F : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (D.g0 * ζ) =
      (D.g0 * ζ) * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    rw [← hζQ, mul_inv_cancel_left]
  obtain ⟨v, hvM, hvF, hv1, hvp⟩ := exists_cycle_element (L := AlgebraicClosure K) (ringChar K) e he
    (x * D.w) n hn β hper (fun k => (hβS k).1) horth hgβ (familyKernel a) hβS
  have hvM' : v ∈ familyGroup (K := AlgebraicClosure K) a := rootSpan_le_familyGroup a hvM
  have hFvQ : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) *
      entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ = v := by
    rw [frobTwistGL_apply] at hvF
    exact hvF
  have hFv : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ * v *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    calc entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v
        = (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) *
              entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹) *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by group
      _ = _ := by rw [hFvQ]
  have hζadj : ζ ∈ adjointGroup τ (AlgebraicClosure K) := familyGroup_le_adjoint a hζ
  have hvadj : v ∈ adjointGroup τ (AlgebraicClosure K) := familyGroup_le_adjoint a hvM'
  refine ⟨(D.g0 * ζ) * v * (D.g0 * ζ)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem D.hg0C hζadj) hvadj) (inv_mem (mul_mem D.hg0C hζadj))
  · intro h
    apply hv1
    calc v = (D.g0 * ζ)⁻¹ * ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) * (D.g0 * ζ) := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, hvp]
    group
  · rw [hFrob, map_mul, map_mul, map_inv, hg1F, hFv]
    group
  · intro y hy
    obtain ⟨d, hd⟩ : ∃ d, rootDiagUnit τ (a ⟨y, hy⟩) = d := ⟨_, rfl⟩
    have hdy : d = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * y * D.c⁻¹ : ModGL τ K) * D.g0 := by
      rw [← hd]
      exact (ha ⟨y, hy⟩).1
    have hζd : ζ * d = d * ζ := by
      rw [← hd]
      exact familyGroup_comm a ⟨y, hy⟩ hζ
    have hvd : v * d = d * v := by
      rw [← hd]
      exact familyGroup_comm a ⟨y, hy⟩ hvM'
    have hbz : baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * y * D.c⁻¹ : ModGL τ K) =
        (D.g0 * ζ) * d * (D.g0 * ζ)⁻¹ := by
      have hζd' : ζ * d * ζ⁻¹ = d := by
        rw [hζd]
        group
      calc baseChangeGL (algebraMap K (AlgebraicClosure K))
            (D.c * y * D.c⁻¹ : ModGL τ K)
          = D.g0 * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (D.c * y * D.c⁻¹ : ModGL τ K) * D.g0) * D.g0⁻¹ := by group
        _ = D.g0 * d * D.g0⁻¹ := by rw [← hdy]
        _ = (D.g0 * ζ) * d * (D.g0 * ζ)⁻¹ := by
          rw [show D.g0 * ζ * d * (D.g0 * ζ)⁻¹ = D.g0 * (ζ * d * ζ⁻¹) * D.g0⁻¹ by group, hζd']
    rw [hbz]
    calc ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) * ((D.g0 * ζ) * d * (D.g0 * ζ)⁻¹)
        = (D.g0 * ζ) * (v * d) * (D.g0 * ζ)⁻¹ := by group
      _ = (D.g0 * ζ) * (d * v) * (D.g0 * ζ)⁻¹ := by rw [hvd]
      _ = ((D.g0 * ζ) * d * (D.g0 * ζ)⁻¹) * ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) := by group

@[expose] def diagMapGL {τ : Tag} {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL τ K)}
    (D : LangGLData τ K A) : ModGL τ K →* ModGL τ (AlgebraicClosure K) :=
  (MulAut.conj D.g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (MulAut.conj D.c).toMonoidHom)

theorem diagMapGL_apply {τ : Tag} {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL τ K)}
    (D : LangGLData τ K A) (x : ModGL τ K) :
    diagMapGL D x = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL τ K) * D.g0 := by
  simp [diagMapGL, MulAut.conj_apply]

theorem finish_gl {τ : Tag} (K : Type) [Field K] [Finite K] (A : Subgroup (ModGL τ K))
    (c : ModGL τ K) (hcN : c ∈ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K)))
    (u' : ModGL τ K) (hu'mem : u' ∈ adjointGroup τ K)
    (uL : ModGL τ (AlgebraicClosure K))
    (hu' : baseChangeGL (algebraMap K (AlgebraicClosure K)) u' = uL)
    (hL1 : uL ≠ 1) (hLp : uL ^ ringChar K = 1)
    (hLc : ∀ y ∈ A, uL * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (c * y * c⁻¹ : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c * y * c⁻¹ : ModGL τ K) * uL) :
    ∃ u : ModGL τ K, u ∈ adjointGroup τ K ∧ u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      ∀ x ∈ A, Commute u x := by
  have hinj := baseChangeGL_injective (τ := τ) (algebraMap K (AlgebraicClosure K))
  have hcomm : ∀ y ∈ A, u' * (c * y * c⁻¹ : ModGL τ K) = (c * y * c⁻¹ : ModGL τ K) * u' := by
    intro y hy
    apply hinj
    rw [map_mul (baseChangeGL (algebraMap K (AlgebraicClosure K))) u' (c * y * c⁻¹ : ModGL τ K),
      map_mul (baseChangeGL (algebraMap K (AlgebraicClosure K))) (c * y * c⁻¹ : ModGL τ K) u', hu']
    exact hLc y hy
  have hU1 : u' ≠ 1 := by
    intro h
    apply hL1
    rw [← hu', h, map_one]
  have hUp : u' ^ ringChar K = 1 := by
    apply hinj
    rw [map_pow, hu', hLp, map_one]
  have hv : c⁻¹ * u' * c ∈ adjointGroup τ K := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcN) u').1 hu'mem
    rwa [inv_inv] at this
  refine ⟨c⁻¹ * u' * c, hv, ?_, ⟨1, ?_⟩, ?_⟩
  · intro h
    apply hU1
    calc u' = c * (c⁻¹ * u' * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rw [pow_one, show c⁻¹ * u' * c = c⁻¹ * u' * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hUp]
    group
  · intro x hx
    have hcomm' : u' * (c * x * c⁻¹) = (c * x * c⁻¹) * u' := hcomm x hx
    show c⁻¹ * u' * c * x = x * (c⁻¹ * u' * c)
    calc c⁻¹ * u' * c * x = c⁻¹ * (u' * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * u') * c := by rw [hcomm']
      _ = x * (c⁻¹ * u' * c) := by group

theorem kill_root_gl_E6 (K : Type) [Field K] [Finite K] (hp : ringChar K ≠ 3)
    (A : Subgroup (ModGL Tag.E6 K)) (D : LangGLData Tag.E6 K A)
    (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α) (hk : D.Kills α) :
    ∃ u : ModGL Tag.E6 K, u ∈ adjointGroup Tag.E6 K ∧ u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      ∀ x ∈ A, Commute u x := by
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
    kill_core_gl (τ := Tag.E6) (Or.inr (Or.inl rfl)) K A D α hα hk
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hcop : ringChar K ≠ 3 → Nat.Coprime 3 (orderOf uL) := by
    intro _
    rw [orderOf_eq_prime huLp huL1]
    exact (Nat.coprime_primes Nat.prime_three (Fact.out : (ringChar K).Prime)).2 (Ne.symm hp)
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E6 D.Fr D.hFr
      huLad huLF hcop)
  exact finish_gl K A D.c D.hcN u' hu'mem uL hu'eq huL1 huLp huLc

theorem closure_pair_eq_of_not_mem {M : Type*} [Group M] (D : Subgroup M) (hcard : Nat.card D = 3 ^ 2)
    {x y : M} (hx : x ∈ D) (hy : y ∈ D) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) : Subgroup.closure ({x, y} : Set M) = D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hzx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  set H := Subgroup.closure ({x, y} : Set M) with hH
  have hHD : H ≤ D := by
    refine (Subgroup.closure_le D).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  haveI : Finite H := Finite.of_injective (fun h : H => (⟨h.1, hHD h.2⟩ : D))
    (fun a b hab => Subtype.ext (congrArg (fun z : D => (z : M)) hab))
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  have hzH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.2 hxH
  have h3 : 3 ∣ Nat.card H := by
    rw [← hzx]
    exact Subgroup.card_dvd_of_le hzH
  have hdvd : Nat.card H ∣ 3 ^ 2 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hHD
  have hHcard : Nat.card H = 3 ^ 2 := by
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases i
    · simp [hHi] at h3
    · exfalso
      have heq : Subgroup.zpowers x = H :=
        Subgroup.eq_of_le_of_card_ge hzH (by rw [hzx, hHi]; norm_num)
      exact hyx (by rw [heq]; exact hyH)
    · rw [hHi]
  exact Subgroup.eq_of_le_of_card_ge hHD (le_of_eq (by rw [hcard, hHcard]))

theorem exists_mem_not_mem_zpowers {M : Type*} [Group M] (D : Subgroup M) (hcard : Nat.card D = 3 ^ 2)
    {x : M} (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hle : D ≤ Subgroup.zpowers x := fun y hy => hcon y hy
  have h1 := Subgroup.card_dvd_of_le hle
  rw [hcard, Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at h1
  norm_num at h1

theorem langGL_diag_exponent {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (D : LangGLData Tag.E6 K A) (ω : (AlgebraicClosure K)ˣ)
    (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {x : ModGL Tag.E6 K} (hx : x ∈ A) (hx3 : x ^ 3 = 1) :
    ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 ∧
      ∃ k : Fin Tag.E6.rank → ℕ, ∀ i, a i = ω ^ k i := by
  obtain ⟨t, ht, hte⟩ := D.hc x hx
  have hdiag : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 = t := by
    rw [← hte]
    simp [MulAut.conj_apply, mul_assoc]
  have htor : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := (Subgroup.mem_inf.1 ht).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup htor
  have hx' : (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) ^ 3 = 1 := by
    rw [conj_pow, hx3]
    group
  have hcube : (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0) ^ 3 = 1 := by
    rw [show D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * (D.g0⁻¹)⁻¹ by rw [inv_inv], conj_pow, ← map_pow, hx',
      map_one]
    group
  have e1 : rootDiagUnit Tag.E6 (a ^ 3) = (rootDiagUnit Tag.E6 a) ^ 3 :=
    map_pow (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) a 3
  have e2 : rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) = 1 :=
    map_one (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))
  have h3 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
    rw [e1, ha, e2, ← hdiag]
    exact hcube
  have h4 : a ^ 3 = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h3
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun h4 i
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 3 = 1 → ∃ k : ℕ, b = ω ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 3 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hb'
    exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hk])⟩
  choose k hk using fun i => hpow (a i) (ha3 i)
  exact ⟨a, ha.trans hdiag.symm, k, hk⟩

theorem langGL_kills_of_outer {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (hexp : ∀ x ∈ A, x ^ 3 = 1) (hcard : Nat.card A = 3 ^ 2) (D : LangGLData Tag.E6 K A)
    (ω : (AlgebraicClosure K)ˣ) (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {x₁ : ModGL Tag.E6 K} (hx₁ : x₁ ∈ A) (hx₁1 : x₁ ≠ 1)
    (a₁ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (ha₁ : rootDiagUnit Tag.E6 a₁ = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x₁ * D.c⁻¹ : ModGL Tag.E6 K) * D.g0)
    (k₁ : Fin Tag.E6.rank → ℕ) (hk₁ : ∀ i, a₁ i = ω ^ k₁ i)
    (hout : ¬ (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₁ i : ℤ)) :
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ D.Kills α := by
  obtain ⟨x₂, hx₂, hx₂n⟩ := exists_mem_not_mem_zpowers A hcard hx₁ (hexp x₁ hx₁) hx₁1
  have hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL Tag.E6 K)) = A :=
    closure_pair_eq_of_not_mem A hcard hx₁ hx₂ (hexp x₁ hx₁) hx₁1 hx₂n
  obtain ⟨a₂, ha₂, k₂, hk₂⟩ := langGL_diag_exponent D ω hω hx₂ (hexp x₂ hx₂)
  obtain ⟨α, hα, h1, h2⟩ := e6_diagPair_killed k₁ k₂ (Or.inl hout)
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hr₁ : rootChar a₁ α = 1 := rootChar_eq_one_of_dvd hω3 hk₁ h1
  have hr₂ : rootChar a₂ α = 1 := rootChar_eq_one_of_dvd hω3 hk₂ h2
  set Sg : Subgroup (ModGL Tag.E6 K) :=
    ((rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))).comap (diagMapGL D) with hSg
  have hker : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, rootChar a α = 1 →
      a ∈ (rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker :=
    fun a h => MonoidHom.mem_ker.2 (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from h)
  have hmem : ∀ (x : ModGL Tag.E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hr
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, hker a hr, ?_⟩)
    rw [diagMapGL_apply]
    exact hax
  have hx₁S : x₁ ∈ Sg := hmem x₁ a₁ ha₁ hr₁
  have hx₂S : x₂ ∈ Sg := hmem x₂ a₂ ha₂ hr₂
  have hAS : A ≤ Sg := by
    rw [← hgen]
    refine (Subgroup.closure_le Sg).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hx₁S
    · exact hx₂S
  refine ⟨α, hα, fun y hy => ?_⟩
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hy))
  refine ⟨a, ?_, ?_⟩
  · rw [diagMapGL_apply] at hay
    exact hay
  · exact (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from MonoidHom.mem_ker.1 ha)

end GLKill

end CFSG.LieType.SeitzGeneration.ExcWideThree
