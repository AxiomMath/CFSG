module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.SL2OppositeRootScalar
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section SL2

variable {k : Type} [Field k]

theorem SL2_eq_neg_one_of_mul_self (hk : ringChar k ≠ 2) {A : SL2 k} (h : A * A = 1)
    (hA : A ≠ 1) : A = -1 := by
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : k, (A : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := A.2
    rwa [hm, Matrix.det_fin_two_of] at this
  have hsq := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hm] at hsq
  have h00 := congrFun (congrFun hsq 0) 0
  have h01 := congrFun (congrFun hsq 0) 1
  have h10 := congrFun (congrFun hsq 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have hs : a + d ≠ 0 := by
    intro hs
    apply Ring.two_ne_zero hk
    linear_combination -(h00 + hdet) + a * hs
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    exact (mul_eq_zero.1 this).resolve_right hs
  subst hb hc
  have ha : a * a = 1 := by linear_combination h00
  have had : a * d = 1 := by linear_combination hdet
  have hda : d = a := by linear_combination a * had - d * ha
  subst hda
  rcases mul_self_eq_one_iff.1 ha with rfl | rfl
  · exfalso
    apply hA
    ext i j
    rw [hm, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    rw [hm, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp

theorem map_neg_one_of_injective (hk : ringChar k ≠ 2) {T : SL2 k →* SL2 k}
    (hT : Function.Injective T) : T (-1) = -1 := by
  have hne : (-1 : SL2 k) ≠ 1 := by
    intro h
    have h00 := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h00
    exact Ring.neg_one_ne_one_of_char_ne_two hk (by simpa using h00)
  refine SL2_eq_neg_one_of_mul_self hk ?_ fun h => hne (hT (h.trans (map_one T).symm))
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

end SL2

section Frobenius

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [CharP k p]

theorem entrywiseFrobGL_pinnedX
    (e : ℕ) (α : Fin τ.rank → ℤ) (c : k) :
    entrywiseFrobGL τ k p e (pinnedX τ k α c) = pinnedX τ k α (iterateFrobenius k p e c) :=
  Units.ext (by rw [Units.coe_map]; exact entrywise_pinnedX _ α c)

theorem entrywiseFrobGL_rootDiagUnit_eq_map (e : ℕ) (a : Fin τ.rank → kˣ) :
    entrywiseFrobGL τ k p e (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map (iterateFrobenius k p e).toMonoidHom (a i) :=
  Units.ext (by rw [Units.coe_map]; exact entrywise_rootDiag _ a)

theorem entrywiseFrobGL_injective (e : ℕ) : Function.Injective (entrywiseFrobGL τ k p e) := by
  intro x y h
  have h' : entrywise (iterateFrobenius k p e) (x : Module.End k (RootModule τ k)) =
      entrywise (iterateFrobenius k p e) (y : Module.End k (RootModule τ k)) :=
    congrArg Units.val h
  refine Units.ext (end_ext_single fun b => ?_)
  have hb := congrArg (fun A : Module.End k (RootModule τ k) => A (Finsupp.single b 1)) h'
  simp only [entrywise_single] at hb
  exact Finsupp.mapRange_injective _ (map_zero _) (iterateFrobenius k p e).injective hb

theorem frobTwistGL_injective (e : ℕ) (Q : ModGL τ k) :
    Function.Injective (frobTwistGL τ k p e Q) :=
  (MulAut.conj Q).injective.comp (entrywiseFrobGL_injective p e)

theorem exists_frobTwistGL_pinnedX
    (e : ℕ) {Q : ModGL τ k} (hQ : Q ∈ monomialSubgroup τ k)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ μ : kˣ, ∀ c : k, frobTwistGL τ k p e Q (pinnedX τ k α c) =
      pinnedX τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • α) (μ * iterateFrobenius k p e c) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hQ hα
  exact ⟨μ, fun c => by rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, hμ]⟩

theorem map_rootSubgroup_eq_of_forall
    {f : ModGL τ k →* ModGL τ k} {α α' : Fin τ.rank → ℤ}
    {g : k → k} (hg : Function.Surjective g)
    (hf : ∀ c, f (pinnedX τ k α c) = pinnedX τ k α' (g c)) :
    (rootSubgroup τ k α).map f = rootSubgroup τ k α' := by
  rw [rootSubgroup, MonoidHom.map_closure, rootSubgroup]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨g c, (hf c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨d, rfl⟩ := hg c
    exact ⟨_, ⟨d, rfl⟩, hf d⟩

theorem entrywiseFrobGL_rootSL2
    (e : ℕ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : SL2 k) :
    entrywiseFrobGL τ k p e (rootSL2 τ k β A) =
      rootSL2 τ k β (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A) := by
  have h := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := k))
    (f := (entrywiseFrobGL τ k p e).comp (rootSL2 τ k β))
    (g := (rootSL2 τ k β).comp (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e))) ?_
  · exact DFunLike.congr_fun h A
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change entrywiseFrobGL τ k p e (rootSL2 τ k β (uSL c)) =
      rootSL2 τ k β (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) (uSL c))
    rw [map_uSL, rootSL2_uSL_eq, rootSL2_uSL_eq, entrywiseFrobGL_pinnedX, map_zsmul]
  · obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := k) hβ
    change entrywiseFrobGL τ k p e (rootSL2 τ k β (vSL c)) =
      rootSL2 τ k β (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) (vSL c))
    rw [map_vSL, hv, hv, entrywiseFrobGL_pinnedX, map_mul]
    rcases mul_self_eq_one_iff.1 hη with rfl | rfl
    · rw [map_one]
    · rw [map_neg, map_one]

variable [PerfectRing k p]

theorem map_frobTwistGL_rootSubgroup
    (e : ℕ) {Q : ModGL τ k} (hQ : Q ∈ monomialSubgroup τ k)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ k α).map (frobTwistGL τ k p e Q) =
      rootSubgroup τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • α) := by
  obtain ⟨μ, hμ⟩ := exists_frobTwistGL_pinnedX p e hQ hα
  refine map_rootSubgroup_eq_of_forall (g := fun c => (μ : k) * iterateFrobenius k p e c)
    (fun c => ?_) hμ
  obtain ⟨d, hd⟩ := (iterateFrobeniusEquiv k p e).surjective (((μ⁻¹ : kˣ) : k) * c)
  refine ⟨d, ?_⟩
  change (μ : k) * (iterateFrobeniusEquiv k p e) d = c
  rw [hd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem map_frobTwistGL_rootSpan
    (e : ℕ) {Q : ModGL τ k} (hQ : Q ∈ monomialSubgroup τ k)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    (rootSpan τ k S).map (frobTwistGL τ k p e Q) =
      rootSpan τ k ((fun α => weylQuotientHom τ k ⟨Q, hQ⟩ • α) '' S) := by
  simp only [rootSpan, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    rw [map_frobTwistGL_rootSubgroup p e hQ (hS α hα)]
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ (fun α => weylQuotientHom τ k ⟨Q, hQ⟩ • α) '' S) =>
      rootSubgroup τ k β) _ ⟨α, hα, rfl⟩ le_rfl
  · refine iSup₂_le ?_
    rintro _ ⟨α, hα, rfl⟩
    rw [← map_frobTwistGL_rootSubgroup p e hQ (hS α hα)]
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ S) =>
      (rootSubgroup τ k β).map (frobTwistGL τ k p e Q)) α hα le_rfl

theorem map_entrywiseFrobGL_torusGroup
    [IsAlgClosed k] (e : ℕ) :
    (torusGroup τ k).map (entrywiseFrobGL τ k p e) = torusGroup τ k := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    rw [entrywiseFrobGL_rootDiagUnit_eq_map]
    exact rootDiagUnit_mem_torusGroup _
  · intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    refine ⟨rootDiagUnit τ fun i =>
      Units.map (iterateFrobeniusEquiv k p e).symm.toRingHom.toMonoidHom (b i),
      rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [entrywiseFrobGL_rootDiagUnit_eq_map]
    congr 1
    funext i
    ext
    change (iterateFrobeniusEquiv k p e) ((iterateFrobeniusEquiv k p e).symm (b i : k)) = b i
    rw [RingEquiv.apply_symm_apply]

theorem map_frobTwistGL_torusGroup
    [IsAlgClosed k] (e : ℕ) {Q : ModGL τ k}
    (hQ : Q ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k))) :
    (torusGroup τ k).map (frobTwistGL τ k p e Q) = torusGroup τ k := by
  rw [← Subgroup.map_map, map_entrywiseFrobGL_torusGroup p e, map_conj_eq_of_mem_normalizer hQ]

end Frobenius

section Signs

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem intCast_ne_zero_of_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : (ε : k) ≠ 0 := by
  rcases hε with rfl | rfl <;> simp

omit [IsAlgClosed k] in
theorem intCast_mul_self_of_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : (ε : k) * ε = 1 := by
  rcases hε with rfl | rfl <;> simp

theorem exists_frobTwistGL_rootSL2
    (hp : p ≠ 2) (e : ℕ) {Q : ModGL τ k}
    (hQ : Q ∈ monomialSubgroup τ k) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ a : kˣ, ∀ c : k,
      frobTwistGL τ k p e Q (rootSL2 τ k β (uSL c)) =
          rootSL2 τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β)
            (uSL ((a : k) * iterateFrobenius k p e c)) ∧
        frobTwistGL τ k p e Q (rootSL2 τ k β (vSL c)) =
          rootSL2 τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β)
            (vSL (((a⁻¹ : kˣ) : k) * iterateFrobenius k p e c)) := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have hwβ : IsRoot τ (weylQuotientHom τ k ⟨Q, hQ⟩ • β) := IsRoot.smul hβ _
  obtain ⟨μ, hμ⟩ := exists_frobTwistGL_pinnedX p e hQ hβ
  have hε := pinnedSign_eq τ β
  have hε' := pinnedSign_eq τ (weylQuotientHom τ k ⟨Q, hQ⟩ • β)
  set ε := (pinnedData τ β).2.2
  set ε' := (pinnedData τ (weylQuotientHom τ k ⟨Q, hQ⟩ • β)).2.2
  set a : kˣ := Units.mk0 ((ε' : k) * ε * μ)
    (mul_ne_zero (mul_ne_zero (intCast_ne_zero_of_sign hε') (intCast_ne_zero_of_sign hε))
      μ.ne_zero) with ha
  have hu : ∀ c, frobTwistGL τ k p e Q (rootSL2 τ k β (uSL c)) =
      rootSL2 τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β) (uSL ((a : k) * iterateFrobenius k p e c)) := by
    intro c
    rw [rootSL2_uSL_eq, hμ, rootSL2_uSL_eq, map_zsmul, zsmul_eq_mul, zsmul_eq_mul, ha,
      Units.val_mk0]
    congr 1
    linear_combination -((μ : k) * (ε : k) * iterateFrobenius k p e c) *
      intCast_mul_self_of_sign (k := k) hε'
  obtain ⟨μ', hμ'⟩ := exists_frobTwistGL_pinnedX p e hQ (IsRoot.neg hβ)
  obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := k) hβ
  obtain ⟨η', hη', hv'⟩ := exists_rootSL2_vSL_eq (K := k) hwβ
  have hη0 : η ≠ 0 := fun h => by rw [h, zero_mul] at hη; exact zero_ne_one hη
  have hη'0 : η' ≠ 0 := fun h => by rw [h, zero_mul] at hη'; exact zero_ne_one hη'
  have hση : iterateFrobenius k p e η = η := by
    rcases mul_self_eq_one_iff.1 hη with h | h <;> rw [h]
    · exact map_one _
    · rw [map_neg, map_one]
  set b : kˣ := Units.mk0 (η' * μ' * η) (mul_ne_zero (mul_ne_zero hη'0 μ'.ne_zero) hη0) with hb
  have hl : ∀ c, frobTwistGL τ k p e Q (rootSL2 τ k β (vSL c)) =
      rootSL2 τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β) (vSL ((b : k) * iterateFrobenius k p e c)) := by
    intro c
    rw [hv, hμ', smul_neg, hv', map_mul, hση, hb, Units.val_mk0]
    congr 1
    linear_combination -((μ' : k) * η * iterateFrobenius k p e c) * hη'
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ :=
    exceptional_Lang_root_rank_one_data τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β)
  obtain ⟨hρinj, e', he'⟩ := hinj hk
  obtain ⟨-, -, -, -, -, -, -, hinjβ, -⟩ := exceptional_Lang_root_rank_one_data τ k β
  have hmem : ∀ A, frobTwistGL τ k p e Q (rootSL2 τ k β A) ∈
      rootRankOneGroup τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β) := by
    intro A
    have htop : (rootRankOneGroup τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β)).comap
        ((frobTwistGL τ k p e Q).comp (rootSL2 τ k β)) = ⊤ := by
      rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨uSL _, (hu c).symm⟩
      · exact ⟨vSL _, (hl c).symm⟩
    have hA : A ∈ (rootRankOneGroup τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β)).comap
        ((frobTwistGL τ k p e Q).comp (rootSL2 τ k β)) := by
      rw [htop]
      exact Subgroup.mem_top A
    exact hA
  let T : SL2 k →* SL2 k := e'.symm.toMonoidHom.comp
    (((frobTwistGL τ k p e Q).comp (rootSL2 τ k β)).codRestrict _ hmem)
  have hT : ∀ A, rootSL2 τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β) (T A) =
      frobTwistGL τ k p e Q (rootSL2 τ k β A) := by
    intro A
    rw [← he']
    simp [T]
  have hTinj : Function.Injective T := fun A B h => by
    have h' := congrArg (rootSL2 τ k (weylQuotientHom τ k ⟨Q, hQ⟩ • β)) h
    rw [hT, hT] at h'
    exact (hinjβ hk).1 (frobTwistGL_injective p e Q h')
  have hTu : ∀ c, T (uSL c) = uSL ((a : k) * (iterateFrobeniusEquiv k p e) c) := fun c =>
    hρinj (by rw [hT, hu]; rfl)
  have hTl : ∀ c, T (vSL c) = vSL ((b : k) * (iterateFrobeniusEquiv k p e) c) := fun c =>
    hρinj (by rw [hT, hl]; rfl)
  obtain ⟨hab, -⟩ := SL2_opposite_root_scalar_compatibility hk (iterateFrobeniusEquiv k p e) a b T
    hTu hTl (map_neg_one_of_injective hk hTinj)
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  refine ⟨a, fun c => ⟨hu c, ?_⟩⟩
  rw [hl, hb']

end Signs

end CFSG.LieType.AlgebraicGroups
