module

public import CFSG.RankThree.PartOne.KF1514B.Tns
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLeviPPrime
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2MinusATail
public import CFSG.RankThree.PartOne.KF1514B.Rank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.RankThree.PartOne.KF1514B

section Theta

variable {K : Type} [Field K] (b c : K) (r : ℕ)

@[expose] noncomputable def tailMatHom (hani : (minusTailForm K b c).Anisotropic) :
    tailFlagStab r (minusTailForm K b c) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := LinearMap.toMatrix' (stabDiagHom r (minusTailForm K b c) hani g).2
  map_one' := by
    rw [map_one]
    exact LinearMap.toMatrix'_one
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.toMatrix'_mul _ _

theorem tailMatHom_apply (hani : (minusTailForm K b c).Anisotropic)
    (g : tailFlagStab r (minusTailForm K b c)) :
    tailMatHom b c r hani g = LinearMap.toMatrix' (stabDiag g.1).2 := rfl

end Theta

section Props

variable {K : Type} [Field K] {b c : K} {r : ℕ}

theorem tailMat_isometry (hani : (minusTailForm K b c).Anisotropic)
    (g : tailFlagStab r (minusTailForm K b c)) (a : Fin 2 → K) :
    minusTailForm K b c ((tailMatHom b c r hani g).mulVec a) = minusTailForm K b c a := by
  obtain ⟨D, h, L, C, hD, hh, -, -, he⟩ := exists_dMap_uMap_eq hani g.2
  have h2 : (stabDiag g.1).2 = (h : Module.End K (Fin 2 → K)) := by
    rw [he, stabDiag_dMap_uMap]
  rw [tailMatHom_apply, h2, LinearMap.toMatrix'_mulVec]
  exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hh) a

theorem stabDiag_fst_ne_zero (hani : (minusTailForm K b c).Anisotropic)
    (g : tailFlagStab r (minusTailForm K b c)) (i : Fin r) : (stabDiag g.1).1 i ≠ 0 := by
  obtain ⟨D, h, L, C, hD, hh, -, -, he⟩ := exists_dMap_uMap_eq hani g.2
  have h2 : (stabDiag g.1).1 i = (D : Matrix (Fin r) (Fin r) K) i i := by
    rw [he, stabDiag_dMap_uMap]
  rw [h2]
  exact diag_ne_zero_of_upperTriangular hD i

end Props

section TnsIndex

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem Tns_le_matrixIsometries : Tns b c ≤ matrixIsometries (minusTailForm K b c) := fun g hg => by
  rw [mem_matrixIsometries_iff]
  intro v
  exact isometry_of_mem_Tns hg v

theorem card_matrixIsometries_tail :
    Nat.card (matrixIsometries (minusTailForm K b c)) = 2 * (Nat.card K + 1) := by
  have h1 : Nat.card (matrixIsometries (minusTailForm K b c)) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c)) := by
    have e := matrixLinearIso.subgroupMap (matrixIsometries (minusTailForm K b c))
    have h2 : (matrixIsometries (minusTailForm K b c)).map
        (matrixLinearIso (d := 2) (K := K)).toMonoidHom =
        TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c) :=
      Subgroup.map_comap_eq_self_of_surjective (matrixLinearIso (d := 2) (K := K)).surjective _
    exact Nat.card_congr (e.trans (MulEquiv.subgroupCongr h2)).toEquiv
  rw [h1]
  exact CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
    finrank_fin_two_fun (fun x hx h => hx (anisotropic_minusTailForm AnisoPair.hirr x h))

theorem index_Tns_tail :
    ((Tns b c).subgroupOf (matrixIsometries (minusTailForm K b c))).index = 2 := by
  have h1 := Subgroup.card_mul_index ((Tns b c).subgroupOf (matrixIsometries (minusTailForm K b c)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tns_le_matrixIsometries).toEquiv,
    card_Tns, card_matrixIsometries_tail] at h1
  have hpos : 0 < Nat.card K + 1 := Nat.succ_pos _
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)

theorem mem_Tns_of_odd_order {H : GL (Fin 2) K}
    (hH : H ∈ matrixIsometries (minusTailForm K b c)) {N : ℕ} (hN : Odd N) (hHN : H ^ N = 1) :
    H ∈ Tns b c := by
  set G := matrixIsometries (minusTailForm K b c) with hG
  set T := (Tns b c).subgroupOf G with hT
  have : T.Normal := Subgroup.normal_of_index_eq_two index_Tns_tail
  set x : G := ⟨H, hH⟩ with hx
  have hsq : x ^ 2 ∈ T := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have := pow_card_eq_one' (G := G ⧸ T) (x := (QuotientGroup.mk x : G ⧸ T))
    rwa [← Subgroup.index_eq_card, index_Tns_tail] at this
  obtain ⟨m, rfl⟩ := hN
  have hxN : x ^ (2 * m + 1) = 1 := Subtype.ext hHN
  have hxx : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hxN, one_mul]
  have : x ∈ T := by
    rw [hxx]
    exact Subgroup.pow_mem T hsq _
  exact this

end TnsIndex

section Borel

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {b c : K} {r : ℕ}

@[expose] noncomputable def tailGL (hani : (minusTailForm K b c).Anisotropic) :
    tailBorel r (minusTailForm K b c) →* GL (Fin 2) K :=
  ((tailMatHom b c r hani).comp (Subgroup.inclusion tailBorel_le_tailFlagStab)).toHomUnits

theorem tailGL_val (hani : (minusTailForm K b c).Anisotropic)
    (g : tailBorel r (minusTailForm K b c)) :
    ((tailGL hani g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      LinearMap.toMatrix' (stabDiag g.1).2 := rfl

theorem tailGL_mem_matrixIsometries (hani : (minusTailForm K b c).Anisotropic)
    (g : tailBorel r (minusTailForm K b c)) :
    tailGL hani g ∈ matrixIsometries (minusTailForm K b c) := by
  rw [mem_matrixIsometries_iff]
  intro v
  exact tailMat_isometry hani ⟨g.1, tailBorel_le_tailFlagStab g.2⟩ v

theorem tailGL_unipotent (hani : (minusTailForm K b c).Anisotropic)
    (g : tailBorel r (minusTailForm K b c)) (hg : g.1 ∈ tailUnipotent r (minusTailForm K b c)) :
    tailGL hani g = 1 := by
  obtain ⟨hf, h1⟩ := (mem_tailUnipotent_iff_ker hani).1 hg
  refine Units.ext ?_
  rw [tailGL_val]
  have : (stabDiag g.1).2 = 1 := by
    have := congrArg Prod.snd h1
    exact this
  rw [this]
  exact LinearMap.toMatrix'_one

variable [Finite K] [CharP K 2]

theorem tailGL_pow_odd (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) :
    ∃ N : ℕ, Odd N ∧ ∀ g : tailBorel r (minusTailForm K b c),
      tailGL (anisotropic_minusTailForm hirr) g ^ N = 1 := by
  have hani := anisotropic_minusTailForm hirr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd := (nondegenerate_minusTailForm hirr)
  have hm : Module.finrank K (Fin 2 → K) = 1 ∨ Module.finrank K (Fin 2 → K) = 2 :=
    Or.inr finrank_fin_two_fun
  have hN := orthogonal_geometry_tail_small_anisotropic_Levi_p_prime (p := 2) hr hani hnd hm
  have hfin : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) => (g : _ → _)) DFunLike.coe_injective
  refine ⟨Nat.card (tailTorus r (minusTailForm K b c)), ?_, fun g => ?_⟩
  · rw [Nat.odd_iff]
    omega
  obtain ⟨t, ht, u, hu, hg⟩ := exists_tailTorus_mul_tailUnipotent hani g.2
  have htB : t ∈ tailBorel r (minusTailForm K b c) := tailTorus_le_tailBorel ht
  have huB : u ∈ tailBorel r (minusTailForm K b c) := tailUnipotent_le_tailBorel hani hu
  set tB : tailBorel r (minusTailForm K b c) := ⟨t, htB⟩ with htBdef
  set uB : tailBorel r (minusTailForm K b c) := ⟨u, huB⟩ with huBdef
  have hgtu : g = tB * uB := Subtype.ext hg
  have hu1 : tailGL hani uB = 1 := tailGL_unipotent hani uB hu
  have htN : tB ^ Nat.card (tailTorus r (minusTailForm K b c)) = 1 := by
    have := pow_card_eq_one' (G := tailTorus r (minusTailForm K b c)) (x := ⟨t, ht⟩)
    have h1 : t ^ Nat.card (tailTorus r (minusTailForm K b c)) = 1 := by
      have h2 := congrArg Subtype.val this
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact h1
  rw [hgtu, map_mul, hu1, mul_one, ← map_pow, htN, map_one]

theorem tailGL_mem_Tns (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r)
    (g : tailBorel r (minusTailForm K b c)) :
    have : AnisoPair b c := ⟨hirr⟩
    tailGL (anisotropic_minusTailForm hirr) g ∈ Tns b c := by
  intro _
  obtain ⟨N, hNodd, hN⟩ := tailGL_pow_odd hirr hr
  exact mem_Tns_of_odd_order (tailGL_mem_matrixIsometries _ g) hNodd (hN g)

theorem isCyclic_range_tailGL (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) :
    IsCyclic (tailGL (anisotropic_minusTailForm hirr) :
      tailBorel r (minusTailForm K b c) →* GL (Fin 2) K).range := by
  have : AnisoPair b c := ⟨hirr⟩
  have hle : (tailGL (anisotropic_minusTailForm hirr) :
      tailBorel r (minusTailForm K b c) →* GL (Fin 2) K).range ≤ Tns b c := by
    rintro _ ⟨g, rfl⟩
    exact tailGL_mem_Tns hirr hr g
  have : IsCyclic (Tns b c) := isCyclic_Tns
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Borel

section Cmap

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] (b c : K) (hb : b ≠ 0)

@[expose] noncomputable def kappaGL : GL (Fin 2) K :=
  ⟨!![1, c; 0, b], !![1, -(c / b); 0, b⁻¹],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb, div_eq_mul_inv],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb, div_eq_mul_inv]⟩

theorem kappaGL_mulVec (u : Fin 2 → K) :
    (kappaGL b c hb : Matrix (Fin 2) (Fin 2) K) *ᵥ u = ![u 0 + c * u 1, b * u 1] := by
  funext i
  fin_cases i <;> simp [kappaGL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem tailA_eq_mulVec (a : Fin 2 → K) :
    tailA b c a = (kappaGL b c hb : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => a i ^ 2) := by
  rw [kappaGL_mulVec]
  funext i
  fin_cases i <;> simp [tailA]

variable [Finite K] [CharP K 2]

@[expose] noncomputable def cMap : GL (Fin 2) K →* GL (Fin 2) K :=
  (MulAut.conj (kappaGL b c hb)).toMonoidHom.comp
    (glFieldAut (Fin 2) K (frobeniusEquiv K 2)).toMonoidHom

end Cmap

section Rel

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (hn : 1 ≤ n) (b c : K) (hb : b ≠ 0)

theorem exists_sq_vec (u : Fin 2 → K) : ∃ a : Fin 2 → K, (fun i => a i ^ 2) = u := by
  have : Fintype K := Fintype.ofFinite K
  have h : ∀ i, ∃ x : K, x ^ 2 = u i := fun i => by
    obtain ⟨x, hx⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (u i)
    exact ⟨x, by rw [hx]; ring⟩
  choose a ha using h
  exact ⟨a, funext ha⟩

theorem tailGL_rel (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g g' : tailBorel (n - 1) (minusTailForm K b c)}
    (h : ∀ y, g'.1 (mnFrob n hn b c hb y) = mnFrob n hn b c hb (g.1 y)) :
    tailGL (anisotropic_minusTailForm hirr) g' =
      cMap b c hb (tailGL (anisotropic_minusTailForm hirr) g) := by
  have hsnd := mnStabDiag_snd_of_rel n hn b c hb h
  set X := tailGL (anisotropic_minusTailForm hirr) g' with hX
  set Y := tailGL (anisotropic_minusTailForm hirr) g with hY
  have key : ∀ u : Fin 2 → K, (X : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((kappaGL b c hb : Matrix (Fin 2) (Fin 2) K) *ᵥ u) =
      (kappaGL b c hb : Matrix (Fin 2) (Fin 2) K) *ᵥ
        ((Y : Matrix (Fin 2) (Fin 2) K).map (frobeniusEquiv K 2) *ᵥ u) := by
    intro u
    obtain ⟨a, rfl⟩ := exists_sq_vec u
    rw [← tailA_eq_mulVec b c hb a, hX, tailGL_val, LinearMap.toMatrix'_mulVec, hsnd a, hY,
      tailGL_val, ← LinearMap.toMatrix'_mulVec, tailA_eq_mulVec b c hb]
    congr 1
    funext i
    exact (frobeniusEquiv K 2).toRingHom.map_mulVec _ _ i
  have hmat : (X : Matrix (Fin 2) (Fin 2) K) * (kappaGL b c hb : Matrix (Fin 2) (Fin 2) K) =
      (kappaGL b c hb : Matrix (Fin 2) (Fin 2) K) *
        (Y : Matrix (Fin 2) (Fin 2) K).map (frobeniusEquiv K 2) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _
  have hunit : X * kappaGL b c hb = kappaGL b c hb *
      glFieldAut (Fin 2) K (frobeniusEquiv K 2) Y := Units.ext hmat
  change X = kappaGL b c hb * glFieldAut (Fin 2) K (frobeniusEquiv K 2) Y * (kappaGL b c hb)⁻¹
  exact eq_mul_inv_of_mul_eq hunit

end Rel

section Final

open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem zpow_eq_pow_of_modEq {G : Type*} [Group G] {x : G} {N : ℕ} (hx : x ^ N = 1) {m : ℤ}
    {k : ℕ} (h : (k : ℤ) ≡ m [ZMOD N]) : x ^ m = x ^ k := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq]
  exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hx)) h.symm

omit [CharP K 2] in
theorem sq_eq_pow_of_modEq {d : K} (hd : d ≠ 0) {k : ℕ} (hk : k ≡ 2 [MOD Nat.card K - 1]) :
    d ^ 2 = d ^ k := by
  have : Fintype K := Fintype.ofFinite K
  have h1 : d ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one d hd
  have hu : (Units.mk0 d hd) ^ (Nat.card K - 1) = 1 := Units.ext (by simpa using h1)
  have := (pow_eq_pow_iff_modEq (x := Units.mk0 d hd) (n := 2) (m := k)).2
    (hk.symm.of_dvd (orderOf_dvd_of_pow_eq_one hu))
  simpa using congrArg Units.val this

theorem coprime_card_sub_one_add_one : Nat.Coprime (Nat.card K - 1) (Nat.card K + 1) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hp, hq⟩ := FiniteField.card K 2
  have h2 : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hq]
    exact dvd_pow_self 2 e.ne_zero
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card K - 1 := by omega
  have h3 : Nat.card K + 1 = 2 + (Nat.card K - 1) := by omega
  rw [h3, Nat.coprime_add_self_right]
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm

theorem tail_commutator {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : 3 ≤ r)
    {x y : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}
    (hx : x ∈ tailBorel r (minusTailForm K b c)) (hy : y ∈ tailBorel r (minusTailForm K b c)) :
    ⁅x, y⁆ ∈ tailUnipotent r (minusTailForm K b c) := by
  have hani := anisotropic_minusTailForm hirr
  have : AnisoPair b c := ⟨hirr⟩
  set X : tailBorel r (minusTailForm K b c) := ⟨x, hx⟩ with hXdef
  set Y : tailBorel r (minusTailForm K b c) := ⟨y, hy⟩ with hYdef
  set Z : tailBorel r (minusTailForm K b c) := ⁅X, Y⁆ with hZdef
  have hZ : Z.1 = ⁅x, y⁆ := rfl
  rw [← hZ]
  refine (mem_tailUnipotent_iff_ker hani).2 ⟨tailBorel_le_tailFlagStab Z.2, ?_⟩
  set F : tailBorel r (minusTailForm K b c) →*
      (Fin r → K) × Module.End K (Fin 2 → K) :=
    (stabDiagHom r (minusTailForm K b c) hani).comp (Subgroup.inclusion tailBorel_le_tailFlagStab)
    with hF
  have hFZ : stabDiagHom r (minusTailForm K b c) hani ⟨Z.1, tailBorel_le_tailFlagStab Z.2⟩ =
      F Z := rfl
  rw [hFZ]
  have hinv : ∀ W : tailBorel r (minusTailForm K b c), F W * F W⁻¹ = 1 := fun W => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcomm1 : F Z = F X * F Y * F X⁻¹ * F Y⁻¹ := by
    rw [hZdef, commutatorElement_def]
    simp only [map_mul]
  refine Prod.ext (funext fun i => ?_) ?_
  · have h1 := congrArg (fun p => p.1 i) (hinv X)
    have h2 := congrArg (fun p => p.1 i) (hinv Y)
    simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at h1 h2
    rw [hcomm1]
    simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply]
    calc (F X).1 i * (F Y).1 i * (F X⁻¹).1 i * (F Y⁻¹).1 i
        = ((F X).1 i * (F X⁻¹).1 i) * ((F Y).1 i * (F Y⁻¹).1 i) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  ·
    have hZ1 : tailGL hani Z = 1 := by
      rw [hZdef, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (comm_of_mem_Tns (tailGL_mem_Tns hirr hr X) (tailGL_mem_Tns hirr hr Y))
    have hmat : LinearMap.toMatrix' (stabDiag Z.1).2 = 1 := by
      have := congrArg (fun U : GL (Fin 2) K => (U : Matrix (Fin 2) (Fin 2) K)) hZ1
      simpa [tailGL_val] using this
    have : (stabDiag Z.1).2 = 1 := by
      apply LinearMap.toMatrix'.injective
      rw [hmat]
      exact LinearMap.toMatrix'_one.symm
    exact this

theorem tail_power_map (n : ℕ) (hn : 1 ≤ n) (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ n - 1)
    (hτ : ∀ g ∈ tailBorel (n - 1) (minusTailForm K b c),
      ∃ g' ∈ tailBorel (n - 1) (minusTailForm K b c),
        ∀ y, g' (mnFrob n hn b c hb y) = mnFrob n hn b c hb (g y)) :
    ∃ k : ℕ, ∀ g ∈ tailBorel (n - 1) (minusTailForm K b c),
      ∀ g' ∈ tailBorel (n - 1) (minusTailForm K b c),
        (∀ y, g' (mnFrob n hn b c hb y) = mnFrob n hn b c hb (g y)) →
          stabDiag g' = stabDiag g ^ k := by
  have hani := anisotropic_minusTailForm hirr
  have : AnisoPair b c := ⟨hirr⟩
  set R : Subgroup (GL (Fin 2) K) :=
    (tailGL hani : tailBorel (n - 1) (minusTailForm K b c) →* GL (Fin 2) K).range with hR
  have hcyc : IsCyclic R := isCyclic_range_tailGL hirr hr
  have hc : ∀ H ∈ R, cMap b c hb H ∈ R := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨g', hg'B, hg'⟩ := hτ g.1 g.2
    exact ⟨⟨g', hg'B⟩, tailGL_rel n hn b c hb hirr (g := g) (g' := ⟨g', hg'B⟩) hg'⟩
  let cR : R →* R := ((cMap b c hb).comp R.subtype).codRestrict R (fun H => hc H.1 H.2)
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic cR
  have hmR : ∀ H ∈ R, cMap b c hb H = H ^ m := by
    intro H hH
    have h0 := congrArg Subtype.val (hm ⟨H, hH⟩)
    have h1 : ((cR ⟨H, hH⟩ : R) : GL (Fin 2) K) = cMap b c hb H := rfl
    have h2 : (((⟨H, hH⟩ : R) ^ m : R) : GL (Fin 2) K) = H ^ m := by simp
    rw [← h1, h0, h2]
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (coprime_card_sub_one_add_one (K := K)) 2
    (m % ((Nat.card K + 1 : ℕ) : ℤ)).toNat
  have hmod : (k : ℤ) ≡ m [ZMOD ((Nat.card K + 1 : ℕ) : ℤ)] := by
    have h1 := Int.natCast_modEq_iff.2 hk2
    have h2 : (((m % ((Nat.card K + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
        m % ((Nat.card K + 1 : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
    rw [h2] at h1
    exact h1.trans (Int.mod_modEq _ _)
  refine ⟨k, fun g hg g' hg' hrel => ?_⟩
  set G : tailBorel (n - 1) (minusTailForm K b c) := ⟨g, hg⟩ with hG
  set G' : tailBorel (n - 1) (minusTailForm K b c) := ⟨g', hg'⟩ with hG'
  have hflag : g ∈ tailFlagStab (n - 1) (minusTailForm K b c) := tailBorel_le_tailFlagStab hg
  refine Prod.ext (funext fun i => ?_) ?_
  · calc (stabDiag g').1 i = ((stabDiag g).1 i) ^ 2 :=
          mnStabDiag_fst_of_rel n hn b c hb hrel i
      _ = ((stabDiag g).1 i) ^ k :=
        sq_eq_pow_of_modEq (stabDiag_fst_ne_zero hani ⟨g, hflag⟩ i) hk1
      _ = (stabDiag g ^ k).1 i := by simp [Prod.pow_fst, Pi.pow_apply]
  · apply LinearMap.toMatrix'.injective
    have hrelG : tailGL hani G' = cMap b c hb (tailGL hani G) := tailGL_rel n hn b c hb hirr hrel
    have hTns : tailGL hani G ∈ Tns b c := tailGL_mem_Tns hirr hr G
    have hpow : tailGL hani G ^ (Nat.card K + 1) = 1 := by
      have := pow_card_eq_one' (G := Tns b c) (x := ⟨tailGL hani G, hTns⟩)
      rw [card_Tns] at this
      exact congrArg Subtype.val this
    have h3 : tailGL hani G' = tailGL hani G ^ k := by
      rw [hrelG, hmR _ ⟨G, rfl⟩]
      exact zpow_eq_pow_of_modEq hpow hmod
    have h4 := congrArg (fun U : GL (Fin 2) K => (U : Matrix (Fin 2) (Fin 2) K)) h3
    simp only [tailGL_val, Units.val_pow_eq_pow_val] at h4
    rw [h4]
    have h5 : LinearMap.toMatrix' ((stabDiag g).2 ^ k) =
        (LinearMap.toMatrix' (stabDiag g).2) ^ k :=
      map_pow (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin 2)) (stabDiag g).2 k
    rw [Prod.pow_snd]
    exact h5.symm

end Final

end CFSG.AGLEmbedding.ParabAutIrr
