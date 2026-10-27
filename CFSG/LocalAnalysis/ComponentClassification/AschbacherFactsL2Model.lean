module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CaseThree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsA7Core

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem ringEquiv_involution_unique {K : Type} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] (hKcard : Nat.card K = p ^ f) {σ τ : K ≃+* K} (hσ : σ ^ 2 = 1)
    (hτ : τ ^ 2 = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hKcard
  have : CharP K p := charP_of_card_eq_prime_pow hKF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (by
        intro x
        have h : (σ.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
            algebraMap (ZMod p) K := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun σ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  have : IsCyclic (K ≃+* K) := (MulEquiv.isCyclic e).mpr inferInstance
  have : Finite (K ≃+* K) := Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
    intro e e' h
    ext x
    exact congrFun h x)
  exact eq_of_sq_eq_one_of_isCyclic hσ hτ hσ1 hτ1

theorem eq_inl_of_right_eq_one {K : Type} [Field K] {x : PGammaL2 K} (hx : x.right = 1) :
    x = SemidirectProduct.inl x.left :=
  SemidirectProduct.ext (by simp) (by simpa using hx)

theorem psl2_generation_model {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {a b : PGammaL2 K} (hab : a * b = b * a) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (H : Subgroup (PSL2 K))
    (hinv : ∀ γ ∈ ({a, b, a * b} : Set (PGammaL2 K)), ∀ x ∈ H, conjPSL K hK hcard γ x ∈ H)
    (hP1 : ∀ γ ∈ ({a, b, a * b} : Set (PGammaL2 K)), ∀ x : PSL2 K,
      γ * psl2Incl K x = psl2Incl K x * γ → Odd (orderOf x) → x ∈ H)
    (hP2 : ∀ γ ∈ ({a, b, a * b} : Set (PGammaL2 K)), ∀ t : PSL2 K, t ^ 2 = 1 → t ≠ 1 →
      γ = psl2Incl K t → ∀ y : PSL2 K, t ∈ Subgroup.zpowers y → y ∈ H) :
    H = ⊤ ∨ (Nat.card K ∈ ({5, 7, 9} : Finset ℕ) ∧ a ∈ (psl2Incl K).range ∧
      b ∈ (psl2Incl K).range) := by
  classical
  set S : Set (PGammaL2 K) := {a, b, a * b} with hS
  have haS : a ∈ S := Set.mem_insert _ _
  have hbS : b ∈ S := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have habS : a * b ∈ S := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have hqodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hK
  have htop : H.map (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) =
      pslRange K → H = ⊤ := by
    intro h
    rw [eq_top_iff]
    intro y _
    have hy : Matrix.ProjectiveSpecialLinearGroup.toPGL y ∈ H.map
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) := h ▸ ⟨y, rfl⟩
    obtain ⟨y', hy'H, hy'⟩ := hy
    rwa [Matrix.ProjectiveSpecialLinearGroup.toPGL_injective hy'] at hy'H
  have hcase2 : ∀ t g : PGL2 K, SemidirectProduct.inl t ∈ S → SemidirectProduct.inl g ∈ S →
      SemidirectProduct.inl (t * g) ∈ S → t ∈ pslRange K → t * t = 1 → t ≠ 1 → g ^ 2 = 1 →
      g ∉ pslRange K → t * g = g * t → H = ⊤ := by
    intro t g htS hgS htgS htJ htt ht1 hg2 hgJ htg
    apply htop
    obtain ⟨t', rfl⟩ := htJ
    have ht'2 : t' ^ 2 = 1 := by
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [map_pow, pow_two, htt, map_one]
    have ht'1 : t' ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hP1' : ∀ s : PGL2 K, SemidirectProduct.inl s ∈ S → ∀ x ∈ pslRange K,
        x * s = s * x → Odd (orderOf x) → x ∈ H.map
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) := by
      rintro s hsS _ ⟨x', rfl⟩ hxs hodd
      refine ⟨x', hP1 _ hsS x' ?_ ?_, rfl⟩
      · rw [psl2Incl_apply, ← map_mul, ← map_mul, hxs]
      · rwa [orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective] at hodd
    refine case_two_pgl2 hKcard hK hcard ⟨t', rfl⟩ htt ht1 hg2 hgJ htg _ ?_ ?_ ?_
      (hP1' g hgS) (hP1' (_ * g) htgS)
    · exact Subgroup.map_le_range _ _
    · exact ⟨t', hP2 _ htS t' ht'2 ht'1 (psl2Incl_apply K t').symm t'
        (Subgroup.mem_zpowers t'), rfl⟩
    · rintro _ ⟨x', hx'H, rfl⟩
      refine ⟨_, hinv _ hgS x' hx'H, ?_⟩
      have h := psl2Incl_conjPSL K hK hcard (SemidirectProduct.inl g) x'
      rw [psl2Incl_apply, psl2Incl_apply, ← map_inv, ← map_mul, ← map_mul] at h
      exact SemidirectProduct.inl_injective h
  rcases em (a.right = 1 ∧ b.right = 1) with ⟨har, hbr⟩ | hlin
  ·
    have ha' := eq_inl_of_right_eq_one har
    have hb' := eq_inl_of_right_eq_one hbr
    set a₀ := a.left with ha₀
    set b₀ := b.left with hb₀
    have hinj := SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
    have ha₀2 : a₀ ^ 2 = 1 := hinj (by rw [map_pow, ← ha', ha2, map_one])
    have hb₀2 : b₀ ^ 2 = 1 := hinj (by rw [map_pow, ← hb', hb2, map_one])
    have hab₀ : a₀ * b₀ = b₀ * a₀ := hinj (by rw [map_mul, map_mul, ← ha', ← hb', hab])
    have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [ha', h, map_one])
    have hb₀1 : b₀ ≠ 1 := fun h => hb1 (by rw [hb', h, map_one])
    have hne₀ : a₀ ≠ b₀ := fun h => hne (by rw [ha', hb', h])
    have haS' : SemidirectProduct.inl a₀ ∈ S := ha' ▸ haS
    have hbS' : SemidirectProduct.inl b₀ ∈ S := hb' ▸ hbS
    have habS' : SemidirectProduct.inl (a₀ * b₀) ∈ S := by
      rw [map_mul, ← ha', ← hb']
      exact habS
    have hbaS' : SemidirectProduct.inl (b₀ * a₀) ∈ S := hab₀ ▸ habS'
    have hJ2 := pslRange_index_eq_two hK
    by_cases hA : a₀ ∈ pslRange K <;> by_cases hB : b₀ ∈ pslRange K
    ·
      obtain ⟨t₁, ht₁⟩ := hA
      obtain ⟨t₂, ht₂⟩ := hB
      have ha'' : a = psl2Incl K t₁ := by rw [psl2Incl_apply, ht₁]; exact ha'
      have hb'' : b = psl2Incl K t₂ := by rw [psl2Incl_apply, ht₂]; exact hb'
      by_cases hq : Nat.card K ∈ ({5, 7, 9} : Finset ℕ)
      · exact Or.inr ⟨hq, ⟨t₁, ha''.symm⟩, ⟨t₂, hb''.symm⟩⟩
      · left
        have hq11 : 11 ≤ Nat.card K := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
          obtain ⟨k, hk⟩ := hqodd
          omega
        have hinjι := psl2Incl_injective K
        have ht₁2 : t₁ ^ 2 = 1 := hinjι (by rw [map_pow, ← ha'', ha2, map_one])
        have ht₂2 : t₂ ^ 2 = 1 := hinjι (by rw [map_pow, ← hb'', hb2, map_one])
        exact case_one_psl2 hKcard hK hq11 ht₁2 ht₂2
          (fun h => ha1 (by rw [ha'', h, map_one])) (fun h => hb1 (by rw [hb'', h, map_one]))
          (fun h => hne (by rw [ha'', hb'', h]))
          (hinjι (by rw [map_mul, map_mul, ← ha'', ← hb'', hab])) H
          (hP2 a haS t₁ ht₁2 (fun h => ha1 (by rw [ha'', h, map_one])) ha'')
          (hP2 b hbS t₂ ht₂2 (fun h => hb1 (by rw [hb'', h, map_one])) hb'')
    · exact Or.inl (hcase2 a₀ b₀ haS' hbS' habS' hA
        (by rw [← pow_two]; exact ha₀2) ha₀1 hb₀2 hB hab₀)
    · exact Or.inl (hcase2 b₀ a₀ hbS' haS' hbaS' hB
        (by rw [← pow_two]; exact hb₀2) hb₀1 ha₀2 hA hab₀.symm)
    ·
      have htJ : a₀ * b₀ ∈ pslRange K :=
        (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false hA hB)
      have htg : a₀ * b₀ * a₀ = b₀ := by
        rw [mul_assoc, ← hab₀, ← mul_assoc, ← pow_two, ha₀2, one_mul]
      refine Or.inl (hcase2 (a₀ * b₀) a₀ habS' haS' (by rw [htg]; exact hbS') htJ ?_ ?_ ha₀2
        hA ?_)
      · rw [← pow_two]
        exact sq_mul_eq_one_of_commute ha₀2 hb₀2 hab₀
      · intro h
        apply hne₀
        have hb₀' : b₀⁻¹ = b₀ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb₀2)
        rw [← hb₀']
        exact eq_inv_of_mul_eq_one_left h
      · rw [htg, ← mul_assoc, ← pow_two, ha₀2, one_mul]
  ·
    left
    have hra : a.right ^ 2 = 1 := by
      have h := congrArg SemidirectProduct.right ha2
      simpa [pow_two] using h
    have hrb : b.right ^ 2 = 1 := by
      have h := congrArg SemidirectProduct.right hb2
      simpa [pow_two] using h
    obtain ⟨z, u, hzS, huS, huzS, hz2, hu2, huz, hz1, hzr, hur⟩ :
        ∃ z u : PGammaL2 K, z ∈ S ∧ u ∈ S ∧ u * z ∈ S ∧ z ^ 2 = 1 ∧ u ^ 2 = 1 ∧
          u * z = z * u ∧ z ≠ 1 ∧ z.right = 1 ∧ u.right ≠ 1 := by
      by_cases har : a.right = 1
      · have hbr : b.right ≠ 1 := fun h => hlin ⟨har, h⟩
        exact ⟨a, b, haS, hbS, hab ▸ habS, ha2, hb2, hab.symm, ha1, har, hbr⟩
      by_cases hbr : b.right = 1
      · exact ⟨b, a, hbS, haS, habS, hb2, ha2, hab, hb1, hbr, har⟩
      have heq : a.right = b.right := ringEquiv_involution_unique hKcard hra hrb har hbr
      refine ⟨a * b, a, habS, haS, ?_, sq_mul_eq_one_of_commute ha2 hb2 hab, ha2, ?_, ?_, ?_,
        har⟩
      · rw [← mul_assoc, ← pow_two, ha2, one_mul]
        exact hbS
      · rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc]
      · intro h
        apply hne
        have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
        rw [← hb']
        exact eq_inv_of_mul_eq_one_left h
      · rw [SemidirectProduct.mul_right, heq, ← pow_two, hrb]
    have hz' := eq_inl_of_right_eq_one hzr
    set z₀ := z.left with hz₀
    have hz₀2 : z₀ ^ 2 = 1 :=
      SemidirectProduct.inl_injective (by rw [map_pow, ← hz', hz2, map_one])
    by_cases hzJ : z₀ ∈ pslRange K
    · obtain ⟨z', hz'z⟩ := hzJ
      have hzι : z = psl2Incl K z' := by rw [psl2Incl_apply, hz'z]; exact hz'
      have hz'2 : z' ^ 2 = 1 := psl2Incl_injective K (by rw [map_pow, ← hzι, hz2, map_one])
      have hz'1 : z' ≠ 1 := fun h => hz1 (by rw [hzι, h, map_one])
      rw [hzι] at huz huzS hzS
      exact case_three_psl2 hKcard hK hcard hz'2 hz'1 hu2 hur huz H (hinv u huS)
        (hinv _ huzS) (hP1 u huS) (hP1 _ huzS) (hP2 _ hzS z' hz'2 hz'1 rfl)
    · rw [hz'] at hzS
      exact case_field_outer_psl2 hKcard hK hcard hz₀2 hzJ hu2 hur H (hinv _ hzS) (hP1 _ hzS)
        (hP1 u huS)

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
