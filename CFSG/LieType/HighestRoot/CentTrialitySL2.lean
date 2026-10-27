module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelDefs
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.G2D4Models
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Toral

theorem exists_pow_mul_eq {G : Type*} [Group G] {S : Subgroup G} {t s : G}
    (ht : t ∈ Subgroup.normalizer (S : Set G)) (hs : s ∈ S) (n : ℕ) :
    ∃ s' ∈ S, (t * s) ^ n = t ^ n * s' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
  | succ n ih =>
    obtain ⟨s', hs', h⟩ := ih
    have hts : t⁻¹ * s' * t ∈ S := by
      have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) s').1 hs'
      rwa [inv_inv] at h'
    refine ⟨t⁻¹ * s' * t * s, mul_mem hts hs, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem coprime_pow_sub_one {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) : Nat.Coprime p (p ^ m - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp.one_lt.ne' ?_
  have h1 : p ∣ p ^ m := dvd_pow_self p hm
  have hpos : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
  have h2 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self hpos] at h2
  exact Nat.dvd_one.1 h2

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem mem_rootSpan_of_mem_toralRootGroup_of_pow
    {p : ℕ} (hp : Nat.Coprime p (Nat.card K - 1))
    {a : Fin τ.rank → Kˣ} {x : ModGL τ K} (hx : x ∈ toralRootGroup τ K a) (hxp : x ^ p = 1) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  have hT := torusGroup_le_normalizer_rootSpan (K := K) (S := rootCharKernel a)
    fun _ hα => hα.1
  have hx' : x ∈ ((torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) : Subgroup (ModGL τ K)) :
      Set (ModGL τ K)) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT] at hx'
  obtain ⟨t, ht, s, hs, rfl⟩ := hx'
  obtain ⟨s', hs', h⟩ := exists_pow_mul_eq (hT ht) hs p
  rw [h] at hxp
  have htp : t ^ p ∈ rootSpan τ K (rootCharKernel a) := by
    rw [eq_inv_of_mul_eq_one_left hxp]
    exact inv_mem hs'
  have hcop : Nat.Coprime p (orderOf t) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one
      (pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ht))) hp
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have htS : t ∈ rootSpan τ K (rootCharKernel a) := by
    rw [← hm]
    exact pow_mem htp m
  exact mul_mem htS hs

theorem mem_rootSpan_of_pow_eq_one
    {p : ℕ} (hp2 : Odd p) (hp : Nat.Coprime p (Nat.card K - 1))
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K}
    (hx : x ∈ toralCentralizer τ K a) (hxp : x ^ p = 1) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  obtain ⟨m, rfl⟩ := hp2
  have hxe : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hxp, one_mul]
  have hM : x ∈ toralRootGroup τ K a := by
    rw [hxe]
    exact pow_mem (sq_mem_toralRootGroup hK ha hx) _
  exact mem_rootSpan_of_mem_toralRootGroup_of_pow hp hM hxp

end Toral

section SL2

variable {F : Type} [Field F]

theorem sl2Upper_pow (c : F) (n : ℕ) : sl2Upper F c ^ n = sl2Upper F (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, sl2Upper_zero]
  | succ n ih =>
    rw [pow_succ, ih, sl2Upper_mul]
    congr 1
    push_cast
    ring

theorem sl2Lower_pow (c : F) (n : ℕ) : sl2Lower F c ^ n = sl2Lower F (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, sl2Lower_zero]
  | succ n ih =>
    rw [pow_succ, ih, sl2Lower_mul]
    congr 1
    push_cast
    ring

theorem closure_pow_eq_one_eq_top (p : ℕ) [CharP F p] :
    Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin 2) F | x ^ p = 1} = ⊤ := by
  rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · refine Subgroup.subset_closure ?_
    change sl2Upper F c ^ p = 1
    rw [sl2Upper_pow, CharP.cast_eq_zero, zero_mul, sl2Upper_zero]
  · refine Subgroup.subset_closure ?_
    change sl2Lower F c ^ p = 1
    rw [sl2Lower_pow, CharP.cast_eq_zero, zero_mul, sl2Lower_zero]

theorem closure_pow_eq_one_eq_top_of_mulEquiv (p : ℕ) [CharP F p] {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup.closure {x : J | x ^ p = 1} = ⊤ := by
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) (closure_pow_eq_one_eq_top (F := F) p)
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
  rw [← hmap]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    rw [← map_pow, hx, map_one]
  · rintro ⟨y, hy, rfl⟩
    rw [← map_pow, hy, map_one]

theorem card_SL2 [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem ringChar_eq_of_card_eq_pow [Finite F] {p m : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ m) : ringChar F = p := by
  have : Fintype F := Fintype.ofFinite F
  have hc := CharP.prime_ringChar F
  have h0 : ((p ^ m : ℕ) : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rwa [← Nat.card_eq_fintype_card, hF] at h
  exact (Nat.prime_dvd_prime_iff_eq hc hp).1 (hc.dvd_of_dvd_pow (ringChar.dvd h0))

end SL2

theorem card_fixedField_le {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ} (hq : 1 < q)
    (hσ : ∀ c, σ c = c ^ q) : Nat.card (fixedField σ) ≤ q := by
  classical
  set P : Polynomial K := Polynomial.X ^ q - Polynomial.X with hPdef
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hmem : ∀ c : fixedField σ, (c : K) ∈ P.roots.toFinset := by
    intro c
    have hc : σ c = c := c.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, hPdef,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← hσ, hc, sub_self]
  calc Nat.card (fixedField σ) ≤ Nat.card P.roots.toFinset :=
        Nat.card_le_card_of_injective (fun c => ⟨c, hmem c⟩) fun c d h => by
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext h
    _ = P.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq

section Main

variable {K : Type} [Field K]

theorem pow_eq_one_of_mem_rootSubgroup
    {p : ℕ} (hp : (p : K) = 0) {β : Fin d4.rank → ℤ}
    {x : ModGL d4 K} (hx : x ∈ rootSubgroup d4 K β) : x ^ p = 1 := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have h : ∀ n : ℕ, pinnedX d4 K β c ^ n = pinnedX d4 K β (n * c) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, pinnedX_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← pinnedX_add]
      congr 1
      push_cast
      ring
  rw [h, hp, zero_mul, pinnedX_zero]

variable [Finite K]

theorem eq_rankOne_long_of_card
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : e ≠ 0)
    (hKc : Nat.card K = (p ^ e) ^ 3) {σ : K →+* K} (hσq : ∀ c, σ c = c ^ (p ^ e))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ e)
    {z : twistedGroup σ} (hz : z ∈ rankOne (twistedRootGroup σ) (ng 0)) (h2 : orderOf z = 2)
    {L : Subgroup (twistedGroup σ)}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set (twistedGroup σ)))
    (hCL : Subgroup.centralizer ({z} : Set (twistedGroup σ)) ≤
      Subgroup.normalizer (L : Set (twistedGroup σ)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    L = rankOne (twistedRootGroup σ) (ng 0) := by
  have hKp : ringChar K = p := ringChar_eq_of_card_eq_pow hp (by rw [hKc, ← pow_mul])
  have hFp : ringChar F = p := ringChar_eq_of_card_eq_pow hp hF
  have : CharP K p := hKp ▸ ringChar.charP K
  have : CharP F p := hFp ▸ ringChar.charP F
  have hK : ringChar K ≠ 2 := by rw [hKp]; exact hp2
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hKc hσq
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hq1 : 1 < p ^ e := Nat.one_lt_pow he hp.one_lt
  have hq3 : 3 ≤ p ^ e := le_trans (hp.two_le.lt_of_ne (Ne.symm hp2)) (Nat.le_self_pow he p)
  set a := signTuple d4 K (nd 2) with ha_def
  have ha : ∀ j, a j = 1 ∨ a j = -1 := signTuple_eq_one_or_eq_neg_one (nd 2)
  set ι := td4Incl σ with hι
  have hzC : ι z = rootDiagUnit d4 a := by
    rw [hι, td4Incl_eq_of_mem hK hz h2, aLongTD4_eq_signTuple]
  have hcommz : ∀ g : twistedGroup σ, g ∈ Subgroup.centralizer ({z} : Set (twistedGroup σ)) →
      ι g * rootDiagUnit d4 a = rootDiagUnit d4 a * ι g := by
    intro g hg
    rw [← hzC, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  set L' := L.map ι with hL'
  have eL' : L' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.equivMapOfInjective L ι (td4Incl_injective σ)).symm.trans eL
  have : Finite (ModGL d4 K) := finite_modGL
  have : Finite L' := Finite.of_equiv _ eL'.symm.toEquiv
  have hLX : L' ≤ toralCentralizer d4 K a := by
    rintro _ ⟨l, hl, rfl⟩
    refine mem_toralCentralizer.2 ⟨(l : adjointGroup d4 K).2, ?_⟩
    rw [← hcommz l (hLC hl)]
    group
  have hKcop : Nat.Coprime p (Nat.card K - 1) := by
    rw [hKc, ← pow_mul]
    exact coprime_pow_sub_one hp (Nat.mul_ne_zero he (by norm_num))
  set χ := signChar d4 K (nd 2) with hχ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signTuple_eq hK
  have hgenp := closure_pow_eq_one_eq_top_of_mulEquiv p eL'
  have hLS : L' ≤ rootSpan d4 K (kernelRoots χ) := by
    rw [← hker]
    intro x hx
    have hle' : Subgroup.closure {y : L' | y ^ p = 1} ≤
        (rootSpan d4 K (rootCharKernel a)).subgroupOf L' :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
        (mem_rootSpan_of_pow_eq_one hpodd hKcop hK ha (hLX y.2) (by
          have hy' : y ^ p = 1 := hy
          rw [← SubgroupClass.coe_pow, hy', OneMemClass.coe_one]))
    exact Subgroup.mem_subgroupOf.1 (hle' (hgenp ▸ Subgroup.mem_top (⟨x, hx⟩ : L')))
  have hSz : ∀ u : twistedGroup σ, ι u ∈ rootSpan d4 K (rootCharKernel a) →
      u ∈ Subgroup.centralizer ({z} : Set (twistedGroup σ)) := by
    intro u hu
    have h := (mem_toralCentralizer.1 (rootSpan_rootCharKernel_le_toralCentralizer a hu)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply td4Incl_injective σ
    rw [map_mul, map_mul, ← hι, hzC]
    calc ι u * rootDiagUnit d4 a = (rootDiagUnit d4 a * ι u * (rootDiagUnit d4 a)⁻¹) *
        rootDiagUnit d4 a := by rw [h]
      _ = rootDiagUnit d4 a * ι u := by group
  have hcent : ∀ β, IsT4Outer β →
      L' ≤ Subgroup.centralizer (pairGroup d4 K β : Set (ModGL d4 K)) := by
    intro β hβ
    have hβF : IsT4Frame β := Or.inr hβ
    have hβr := isRoot_of_isT4Frame hβF
    have hSk := componentRootSpan_t4 hK hβF
    obtain ⟨-, ⟨eβ⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components d4 K hK hβr
    have hq : CFSG.IsQuasisimple (pairGroup d4 K β) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eβ
        (isQuasisimple_SL2_of_four_le (by
          rw [hKc]
          calc 4 ≤ 3 ^ 3 := by norm_num
            _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left hq3 3))
    have hgen : ∀ {s : ℤ}, (s = 1 ∨ s = -1) → ∀ x ∈ rootSubgroup d4 K (s • β),
        x ∈ actLike (pairGroup d4 K β) (Subgroup.normalizer (L' : Set (ModGL d4 K))) := by
      intro s hs x hx
      have hsr : IsRoot d4 (s • β) := by
        rcases hs with rfl | rfl
        · rwa [one_smul]
        · rw [neg_one_smul]; exact IsRoot.neg hβr
      have hxA : x ∈ pairGroup d4 K β := by
        rcases hs with rfl | rfl
        · rw [one_smul] at hx; exact Subgroup.mem_sup_left hx
        · rw [neg_one_smul] at hx; exact Subgroup.mem_sup_right hx
      have hxH : x ∈ adjointGroup d4 K := rootSubgroup_le_adjointGroup _ hx
      have hx' : (⟨x, hxH⟩ : adjointGroup d4 K) ∈
          rootGroup (rootOperatorFamily d4) K (s • β) := by
        rw [rootGroup_eq_subgroupOf hsr]
        exact Subgroup.mem_subgroupOf.2 hx
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff hsr _).1 hx'
      have hne : rho (s • β) ≠ s • β := by
        intro h
        apply rho_ne_of_isT4Outer hβ
        have h' : s • rho β = s • β := h
        rcases hs with rfl | rfl
        · simpa using h'
        · simpa using h'
      have hu : xOrbit σ (s • β) c ∈ twistedGroup σ :=
        twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hsr) (xOrbit_mem hσ hsr hne c)
      set u : twistedGroup σ := ⟨_, hu⟩
      obtain ⟨w, hw, hxw⟩ := xOrbit_eq_mul σ hβ hs c
      have hιu : ι u = x * w := by
        rw [hι, td4Incl_apply]
        change ((xOrbit σ (s • β) c : adjointGroup d4 K) : ModGL d4 K) = x * w
        rw [hxw, hc]
      have hρs : rho (s • β) = s • rho β := rfl
      have hρρs : rho (rho (s • β)) = s • rho (rho β) := rfl
      have hkr : ∀ {γ : Fin d4.rank → ℤ}, IsT4Outer γ → s • γ ∈ rootCharKernel a := by
        intro γ hγ
        rw [t4_mem_kernel_iff hK]
        rcases hs with rfl | rfl
        · exact ⟨γ, Or.inr hγ, Or.inl (one_smul _ _)⟩
        · exact ⟨γ, Or.inr hγ, Or.inr (neg_one_smul _ _)⟩
      have hmemS : ∀ {γ : Fin d4.rank → ℤ}, s • γ ∈ rootCharKernel a → IsRoot d4 (s • γ) →
          ∀ d : K, ((xPar (rootOperatorFamily d4) (s • γ) d : adjointGroup d4 K) :
            ModGL d4 K) ∈ rootSpan d4 K (rootCharKernel a) := fun hγ hγr d =>
        (le_iSup₂_of_le _ hγ le_rfl : rootSubgroup d4 K _ ≤ rootSpan d4 K (rootCharKernel a))
          (coe_xPar_mem_rootSubgroup hγr d)
      have hρr : IsRoot d4 (s • rho β) := hρs ▸ isRoot_rho hsr
      have hρρr : IsRoot d4 (s • rho (rho β)) := hρρs ▸ isRoot_rho (isRoot_rho hsr)
      have huS : ι u ∈ rootSpan d4 K (rootCharKernel a) := by
        rw [hι, td4Incl_apply]
        change ((xOrbit σ (s • β) c : adjointGroup d4 K) : ModGL d4 K) ∈ _
        rw [xOrbit, Subgroup.coe_mul, Subgroup.coe_mul, hρρs, hρs]
        exact mul_mem (mul_mem (hmemS (hkr hβ) hsr c)
          (hmemS (hkr (isT4Outer_rho hβ)) hρr _))
          (hmemS (hkr (isT4Outer_rho (isT4Outer_rho hβ))) hρρr _)
      have hN : ι u ∈ Subgroup.normalizer (L' : Set (ModGL d4 K)) :=
        Subgroup.le_normalizer_map ι ⟨u, hCL (hSz u huS), rfl⟩
      refine ⟨hxA, ι u, hN, fun y hy => ?_⟩
      rw [hιu]
      have hwy := (Subgroup.mem_centralizer_iff.1 hw) y hy
      calc x * y * x⁻¹ = x * (y * w) * w⁻¹ * x⁻¹ := by group
        _ = x * (w * y) * w⁻¹ * x⁻¹ := by rw [hwy]
        _ = x * w * y * (x * w)⁻¹ := by group
    have hproj : pairGroup d4 K β ≤
        actLike (pairGroup d4 K β) (Subgroup.normalizer (L' : Set (ModGL d4 K))) :=
      sup_le (fun x hx => hgen (Or.inl rfl) x (by rwa [one_smul]))
        (fun x hx => hgen (Or.inr rfl) x (by rwa [neg_one_smul]))
    refine le_centralizer_of_isQuasisimple hq (fun l hl => ?_) (fun g hg => (hproj hg).2)
      (X := rootSubgroup d4 K β) le_sup_left (fun x hx hcen => ?_) ?_
    ·
      obtain ⟨j, hj, c, hc, rfl⟩ := exists_eq_mul_of_mem_rootSpan χ
        ⟦⟨β, mem_kernelRoots_t4 hK hβF⟩⟧ (hLS hl)
      rw [hSk] at hj hc
      refine ⟨j, hj, fun y hy => ?_⟩
      have hjy : j * y * j⁻¹ ∈ pairGroup d4 K β := mul_mem (mul_mem hj hy) (inv_mem hj)
      have hcj := (Subgroup.mem_centralizer_iff.1 hc) _ hjy
      calc c * j * y * (c * j)⁻¹ = c * (j * y * j⁻¹) * c⁻¹ := by group
        _ = (j * y * j⁻¹) * c * c⁻¹ := by rw [← hcj]
        _ = j * y * j⁻¹ := by group
    ·
      have hxc : (⟨x, Subgroup.mem_sup_left hx⟩ : pairGroup d4 K β) ∈
          Subgroup.center (pairGroup d4 K β) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcen g g.2).symm
      have hx2 : x * x = 1 := congrArg Subtype.val (mul_self_eq_one_of_mem_center eβ.symm hxc)
      have hxp := pow_eq_one_of_mem_rootSubgroup hpK hx
      have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
      have h3 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
      have h4 : orderOf x ∣ 1 := by
        have h5 := Nat.dvd_gcd h1 h3
        rwa [(Nat.coprime_two_left.2 hpodd).gcd_eq_one] at h5
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
    · rw [card_rootSubgroup, hKc, Nat.card_congr eL'.toEquiv, card_SL2, hF]
      have hq0 : 0 < p ^ e := by omega
      rw [Nat.mul_sub_one, ← pow_succ']
      exact Nat.sub_lt (Nat.pow_pos hq0) hq0
  set k₀ : KernelComponent χ := ⟦⟨t4c, mem_kernelRoots_t4 hK (Or.inl rfl)⟩⟧ with hk₀
  have hS₀ : componentRootSpan K χ k₀ = pairGroup d4 K t4c :=
    componentRootSpan_t4 hK (Or.inl rfl)
  have hLk : ∀ x ∈ L', ∀ k, k ≠ k₀ → ∀ y ∈ componentRootSpan K χ k, x * y = y * x := by
    intro x hx k hk y hy
    obtain ⟨β, hβ, rfl⟩ := exists_t4_of_class hK k
    rcases hβ with hβc | hβo
    · exact absurd (by subst hβc; rfl) hk
    · rw [componentRootSpan_t4 hK (Or.inr hβo)] at hy
      exact ((Subgroup.mem_centralizer_iff.1 (hcent β hβo hx)) y hy).symm
  have hpQ : ∀ x ∈ L', x ^ p = 1 → x ∈ pairGroup d4 K t4c := by
    intro x hx hxp
    obtain ⟨j, hj, t, ⟨htT, htJ⟩, rfl⟩ := exists_eq_mul_of_commute χ k₀ (hLS hx) (hLk x hx)
    rw [hS₀] at hj htJ
    have hcomm' : Commute t j := ((Subgroup.mem_centralizer_iff.1 htJ) j hj).symm
    rw [hcomm'.mul_pow] at hxp
    have htp : t ^ p ∈ pairGroup d4 K t4c := by
      rw [eq_inv_of_mul_eq_one_left hxp]
      exact inv_mem (pow_mem hj p)
    have hcop : Nat.Coprime p (orderOf t) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one
        (pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup htT))) hKcop
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have htJc : t ∈ pairGroup d4 K t4c := by
      rw [← hm]
      exact pow_mem htp m
    exact mul_mem htJc hj
  have hLJ : L' ≤ pairGroup d4 K t4c := by
    intro x hx
    have hle' : Subgroup.closure {y : L' | y ^ p = 1} ≤ (pairGroup d4 K t4c).subgroupOf L' :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2 (hpQ y.1 y.2 (by
        have hy' : y ^ p = 1 := hy
        rw [← SubgroupClass.coe_pow, hy', OneMemClass.coe_one]))
    exact Subgroup.mem_subgroupOf.1 (hle' (hgenp ▸ Subgroup.mem_top (⟨x, hx⟩ : L')))
  have hLL : L ≤ rankOne (twistedRootGroup σ) (ng 0) := by
    intro l hl
    have h1 : ι l ∈ pairGroup d4 K t4c := hLJ ⟨l, hl, rfl⟩
    refine mem_rankOne_long_of_mem_rankOneTwo hσ ?_
    change (l : adjointGroup d4 K) ∈ rootGroup (rootOperatorFamily d4) K (Pi.single (nd 2) 1) ⊔
      rootGroup (rootOperatorFamily d4) K (-Pi.single (nd 2) 1)
    rw [rootGroup_eq_subgroupOf (isRoot_single _ _),
      rootGroup_eq_subgroupOf (IsRoot.neg (isRoot_single _ _)),
      ← Subgroup.subgroupOf_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)]
    exact Subgroup.mem_subgroupOf.2 h1
  have hm := card_fixedField_le hq1 hσq
  have hcard : Nat.card (rankOne (twistedRootGroup σ) (ng 0)) ≤ Nat.card L := by
    calc Nat.card (rankOne (twistedRootGroup σ) (ng 0)) ≤
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) := card_rankOne_long_le hσ
      _ = Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := card_SL2
      _ ≤ p ^ e * ((p ^ e) ^ 2 - 1) :=
          Nat.mul_le_mul hm (Nat.sub_le_sub_right (Nat.pow_le_pow_left hm 2) 1)
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by rw [card_SL2, hF]
      _ = Nat.card L := (Nat.card_congr eL.toEquiv).symm
  have : Finite (twistedGroup σ) := by
    have : Finite (adjointGroup d4 K) := inferInstance
    infer_instance
  exact Subgroup.eq_of_le_of_card_ge hLL hcard

end Main

section Conj

variable {G : Type*} [Group G] (g : G) {z : G} {L : Subgroup G}

theorem map_conj_le_centralizer (hLC : L ≤ Subgroup.centralizer ({z} : Set G)) :
    L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hLC hy)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
    _ = g * (z * y) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group

theorem centralizer_le_normalizer_map_conj
    (hCL : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤
      Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro w hw
  have hw' : g⁻¹ * w * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    calc g⁻¹ * w * g * z = g⁻¹ * (w * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * w) * g := by rw [hw]
      _ = z * (g⁻¹ * w * g) := by group
  have hN := Subgroup.mem_normalizer_iff.1 (hCL hw')
  have key : ∀ v : G, v ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * v * g ∈ L := by
    intro v
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [Subgroup.mem_normalizer_iff]
  intro u
  rw [key, key, hN (g⁻¹ * u * g)]
  have e : g⁻¹ * w * g * (g⁻¹ * u * g) * (g⁻¹ * w * g)⁻¹ = g⁻¹ * (w * u * w⁻¹) * g := by group
  rw [e]

end Conj

section Unique

variable {K : Type} [Field K] [Finite K]

theorem eq_of_map_conj_eq
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : e ≠ 0)
    (hKc : Nat.card K = (p ^ e) ^ 3) {σ : K →+* K} (hσq : ∀ c, σ c = c ^ (p ^ e))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ e) {γ : Fin (Tag.rank .G2) → ℤ}
    {g : twistedGroup σ}
    (hg : (twistedRootGroup σ γ ⊔ twistedRootGroup σ (-γ)).map (MulAut.conj g).toMonoidHom =
      rankOne (twistedRootGroup σ) (ng 0))
    {z : twistedGroup σ} (hz : z ∈ twistedRootGroup σ γ ⊔ twistedRootGroup σ (-γ))
    (h2 : orderOf z = 2) {L : Subgroup (twistedGroup σ)}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set (twistedGroup σ)))
    (hCL : Subgroup.centralizer ({z} : Set (twistedGroup σ)) ≤
      Subgroup.normalizer (L : Set (twistedGroup σ)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    L = twistedRootGroup σ γ ⊔ twistedRootGroup σ (-γ) := by
  have hz' : g * z * g⁻¹ ∈ rankOne (twistedRootGroup σ) (ng 0) := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem _ hz
  have h2' : orderOf (g * z * g⁻¹) = 2 := by
    rw [← h2]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
  have eL' : L.map (MulAut.conj g).toMonoidHom ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (L.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans eL
  have h := eq_rankOne_long_of_card hp hp2 he hKc hσq hF hz' h2'
    (map_conj_le_centralizer g hLC) (centralizer_le_normalizer_map_conj g hCL) eL'
  rw [← hg] at h
  exact Subgroup.map_injective (MulAut.conj g).injective h

end Unique

theorem trialityD4SL2Unique
    : CFSG.ComponentClassification.RankTwoOddLie.TrialityD4SL2Unique := by
  intro n p e _ hp2 hadm _ γ hγ z hz h2 L hLC hCL ⟨eL⟩ _
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  have hcardK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
    rw [hcardK]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have : Finite (GaloisField p e) := Nat.finite_of_card_ne_zero (by
    rw [hF]
    exact (pow_pos (Fact.out : p.Prime).pos e).ne')
  have hγ₀ : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .trialityD4 n p e Fact.out).D
        (Pi.single (ng 0) 1) :=
    CFSG.ClassicalInvolution.ModelFacts.isLongest_single_G2 rfl _ (k := ng 0) rfl
  have hγ' : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .trialityD4 n p e Fact.out).D γ := hγ
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_conj_of_isLongestRoot .trialityD4
    n p e Fact.out trivial hadm hγ' hγ₀
  exact eq_of_map_conj_eq Fact.out hp2 he hcardK (fun c => iterateFrobenius_def p e c) hF hg hz
    h2 hLC hCL eL

end CFSG.LieType.HighestRoot
