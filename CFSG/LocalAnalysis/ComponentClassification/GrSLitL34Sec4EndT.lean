module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4AutB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoIn_inf_centralizer {S B : Subgroup G}
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hSN : S ≤ normalizer (B : Set G)) :
    IsSylowTwoIn (S ⊓ centralizer (B : Set G)) (centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := hS
  have hSN' : IsSylowTwoIn (P : Subgroup G) (normalizer (B : Set G)) :=
    isSylowTwoIn_of_not_dvd hSN P.isPGroup' fun h =>
      P.not_dvd_index (h.trans (relIndex_dvd_index_of_le hSN))
  exact isSylowTwoIn_inf_of_normal hSN'
    (fun c hc => mem_normalizer_of_forall_commute fun y hy =>
      (mem_centralizer_iff.mp hc y hy).symm)
    fun n hn => mem_normalizer_centralizer hn

theorem exists_mul_mem_normalizer {B T : Subgroup G}
    (hT : IsSylowTwoIn T (centralizer (B : Set G))) {m : G} (hm : m ∈ normalizer (B : Set G)) :
    ∃ c ∈ centralizer (B : Set G), m * c ∈ normalizer (T : Set G) := by
  have hT2 : IsPGroup 2 T := isPGroup_of_isSylowTwoIn hT
  have hmC : m⁻¹ ∈ normalizer (centralizer (B : Set G) : Set G) :=
    mem_normalizer_centralizer (inv_mem hm)
  have hVC : T.map (MulAut.conj m⁻¹).toMonoidHom ≤ centralizer (B : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact (mem_normalizer_iff.mp hmC t).mp (hT.1 ht)
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_of_isSylowTwoIn hT hVC (hT2.map _)
  refine ⟨c, hcC, ?_⟩
  have h1 : (m * c)⁻¹ ∈ normalizer (T : Set G) := mem_normalizer_of_map_le_self (by
    rintro _ ⟨t, ht, rfl⟩
    have h2 := hc _ (mem_map_of_mem (MulAut.conj m⁻¹).toMonoidHom ht)
    convert h2 using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_inv_rev]
    group)
  simpa using inv_mem h1

theorem exists_mem_normalizer_conj_eq {B T : Subgroup G} (hB : IsElemTwo B)
    (hT : IsSylowTwoIn T (centralizer (B : Set G)))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G))
    {a b : G} (haB : a ∈ B) (hbB : b ∈ B) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ g ∈ normalizer (T : Set G), g⁻¹ * a * g = b := by
  obtain ⟨σ, hσ⟩ := exists_mulAut_apply_eq (E := ↥B) (fun u v => Subtype.ext (hB.1 _ u.2 _ v.2))
    (fun u => Subtype.ext (hB.2 _ u.2)) (a := ⟨a, haB⟩) (b := ⟨b, hbB⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨n, hnN, hn⟩ := hAut σ
  have hnab : n⁻¹ * a * n = b := by
    have h := hn ⟨a, haB⟩
    rw [hσ] at h
    exact h
  obtain ⟨c, hcC, hnc⟩ := exists_mul_mem_normalizer hT hnN
  refine ⟨n * c, hnc, ?_⟩
  have hcb : c⁻¹ * b * c = b := by
    rw [mul_assoc, (mem_centralizer_iff.mp hcC b hbB), ← mul_assoc, inv_mul_cancel, one_mul]
  calc (n * c)⁻¹ * a * (n * c) = c⁻¹ * (n⁻¹ * a * n) * c := by group
    _ = b := by rw [hnab, hcb]

omit [Finite G] in
private theorem card_eq_card_map_mul_card_inf_ker' {H : Type*} [Group H] (φ : G →* H)
    (K : Subgroup G) : Nat.card K = Nat.card (K.map φ) * Nat.card (K ⊓ φ.ker : Subgroup G) := by
  let ψ : K →* H := φ.comp K.subtype
  have hrange : ψ.range = K.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (K ⊓ φ.ker : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : K) : G), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

theorem card_sylow_eq {J P : Subgroup G}
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J)
    (hZ4 : Nat.card ↥(P ⊓ zStarIn J) = 4) : Nat.card P = 256 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPJ, T, hT⟩ := hP
  obtain ⟨e⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL34
  have hcardQ : Nat.card (J ⧸ Open.fusionZStar J) = 20160 := by
    rw [Nat.card_congr e.toEquiv, PSL3Four.card_S]
  have hsurj := QuotientGroup.mk'_surjective (Open.fusionZStar ↥J)
  have h1 : Nat.card ((T : Subgroup J).map (QuotientGroup.mk' (Open.fusionZStar ↥J))) = 64 := by
    have h := Sylow.card_eq_multiplicity (T.mapSurjective hsurj)
    rw [Sylow.coe_mapSurjective] at h
    rw [h, hcardQ, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  have h2 : Nat.card ↥((T : Subgroup J) ⊓ (QuotientGroup.mk' (Open.fusionZStar ↥J)).ker) = 4 := by
    rw [← hZ4, QuotientGroup.ker_mk']
    have hmap : ((T : Subgroup J) ⊓ Open.fusionZStar J).map J.subtype = P ⊓ zStarIn J := by
      rw [map_inf_eq _ _ _ J.subtype_injective, hT, subgroupOf_map_subtype,
        inf_eq_left.mpr hPJ]
      rfl
    rw [← hmap, card_map_of_injective J.subtype_injective]
  have h3 := card_eq_card_map_mul_card_inf_ker' (QuotientGroup.mk' (Open.fusionZStar ↥J))
    (T : Subgroup J)
  rw [h1, h2] at h3
  have h4 : Nat.card (T : Subgroup J) = Nat.card P := by
    rw [hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv
  omega

omit [Finite G] in
theorem exists_mem_not_mem_four {B : Subgroup G} (hB8 : Nat.card B = 8) (x y z w : G) :
    ∃ b ∈ B, b ≠ x ∧ b ≠ y ∧ b ≠ z ∧ b ≠ w := by
  by_contra! h
  have hsub : (B : Set G) ⊆ {x, y, z, w} := by
    intro b hb
    by_cases hx : b = x
    · exact Or.inl hx
    by_cases hy : b = y
    · exact Or.inr (Or.inl hy)
    by_cases hz : b = z
    · exact Or.inr (Or.inr (Or.inl hz))
    exact Or.inr (Or.inr (Or.inr (h b hb hx hy hz)))
  have h1 : Nat.card B ≤ 4 := by
    have h0 : Nat.card B = (B : Set G).ncard := Nat.card_coe_set_eq (B : Set G)
    rw [h0]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    have := Set.ncard_insert_le y ({z, w} : Set G)
    have := Set.ncard_insert_le z ({w} : Set G)
    rw [Set.ncard_singleton] at this
    omega
  omega

theorem card_inf_centralizer_le (hTr : L34EightTransvectionFact)
    {J P B : Subgroup G} {a : G} (hJper : ⁅J, J⁆ = J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J)
    (hZc : IsCyclic ↥(P ⊓ zStarIn J)) (hZ4 : Nat.card ↥(P ⊓ zStarIn J) = 4) (hBP : B ≤ P)
    (hB8 : IsEightGroup B) (hBZ : B ⊓ zStarIn J = zpowers a) (ha1 : a ≠ 1) :
    Nat.card ↥(P ⊓ centralizer (B : Set G)) ≤ 64 := by
  have hP256 := card_sylow_eq hL34 hP hZ4
  have haB : a ∈ B := (le_of_eq hBZ.symm).trans inf_le_left (mem_zpowers a)
  have hcomm : ∀ u v : ↥B, u * v = v * u := fun u v => Subtype.ext (hB8.1.1 _ u.2 _ v.2)
  have hinv : ∀ u : ↥B, u * u = 1 := fun u => Subtype.ext (hB8.1.2 _ u.2)
  obtain ⟨b₂, hb₂B, hb₂1, hb₂a, -, -⟩ := exists_mem_not_mem_four hB8.2 1 a 1 1
  obtain ⟨b₃, hb₃B, hb₃1, hb₃a, hb₃b, hb₃ab⟩ := exists_mem_not_mem_four hB8.2 1 a b₂ (a * b₂)
  have haa : a * a = 1 := hB8.1.2 a haB
  have hb₂ab₃ : b₂ ≠ a * b₃ := by
    intro h
    apply hb₃ab
    rw [h, ← mul_assoc, haa, one_mul]
  have hne : ∀ {u v : G} (hu : u ∈ B) (hv : v ∈ B), u ≠ v → (⟨u, hu⟩ : ↥B) ≠ ⟨v, hv⟩ :=
    fun _ _ h h' => h (congrArg Subtype.val h')
  obtain ⟨τ₂, hτ₂, hτ₂u, hτ₂v⟩ := exists_mulAut_transvection hcomm hinv
    (a := ⟨a, haB⟩) (u := ⟨b₂, hb₂B⟩) (v := ⟨b₃, hb₃B⟩) (hne hb₂B (one_mem B) hb₂1)
    (hne hb₂B haB hb₂a) (hne hb₂B hb₃B (Ne.symm hb₃b))
    (hne hb₂B (mul_mem haB hb₃B) hb₂ab₃)
  obtain ⟨τ₃, hτ₃, hτ₃u, hτ₃v⟩ := exists_mulAut_transvection hcomm hinv
    (a := ⟨a, haB⟩) (u := ⟨b₃, hb₃B⟩) (v := ⟨b₂, hb₂B⟩) (hne hb₃B (one_mem B) hb₃1)
    (hne hb₃B haB hb₃a) (hne hb₃B hb₂B hb₃b) (hne hb₃B (mul_mem haB hb₂B) hb₃ab)
  have hcoe : ∀ τ : MulAut ↥B, (∀ x : ↥B, x⁻¹ * τ x ∈ zpowers (⟨a, haB⟩ : ↥B)) →
      ∀ y : ↥B, (y : G)⁻¹ * (τ y : G) ∈ zpowers a := by
    intro τ h y
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (h y)
    refine mem_zpowers_iff.mpr ⟨m, ?_⟩
    have h1 := congrArg Subtype.val hm
    simpa using h1
  obtain ⟨p₂, hp₂, hp₂τ⟩ := hTr G J P B a hJper hL34 hP hZc hZ4 hBP hB8 hBZ τ₂ (hcoe τ₂ hτ₂)
  obtain ⟨p₃, hp₃, hp₃τ⟩ := hTr G J P B a hJper hL34 hP hZc hZ4 hBP hB8 hBZ τ₃ (hcoe τ₃ hτ₃)
  have hp₂b₂ : p₂⁻¹ * b₂ * p₂ = b₂ * a := by
    have h := hp₂τ ⟨b₂, hb₂B⟩
    rw [hτ₂u] at h
    exact h
  have hp₃b₂ : p₃⁻¹ * b₂ * p₃ = b₂ := by
    have h := hp₃τ ⟨b₂, hb₂B⟩
    rw [hτ₃v] at h
    exact h
  have hp₃b₃ : p₃⁻¹ * b₃ * p₃ = b₃ * a := by
    have h := hp₃τ ⟨b₃, hb₃B⟩
    rw [hτ₃u] at h
    exact h
  set D₂ : Subgroup G := P ⊓ centralizer ({b₂} : Set G) with hD₂
  set D₂₃ : Subgroup G := D₂ ⊓ centralizer ({b₃} : Set G) with hD₂₃
  have hmemC : ∀ {p b : G}, p ∈ centralizer ({b} : Set G) → p⁻¹ * b * p = b := by
    intro p b hp
    rw [mem_centralizer_singleton_iff] at hp
    rw [mul_assoc, ← hp, ← mul_assoc, inv_mul_cancel, one_mul]
  have hb₂ne : b₂ * a ≠ b₂ := fun h => ha1 (mul_left_cancel (h.trans (mul_one b₂).symm))
  have hb₃ne : b₃ * a ≠ b₃ := fun h => ha1 (mul_left_cancel (h.trans (mul_one b₃).symm))
  have hr₁ : 2 ≤ D₂.relIndex P := by
    have h0 := relIndex_mul_card D₂ P
    have hne1 : D₂.relIndex P ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      intro hle
      exact hb₂ne (hp₂b₂.symm.trans (hmemC (mem_inf.mp (hle (mem_inf.mp hp₂).1)).2))
    have hne0 : D₂.relIndex P ≠ 0 := by
      intro h
      rw [h, zero_mul] at h0
      exact Nat.card_pos.ne' h0.symm
    omega
  have hr₂ : 2 ≤ D₂₃.relIndex D₂ := by
    have h0 := relIndex_mul_card D₂₃ D₂
    have hp₃D : p₃ ∈ D₂ := mem_inf.mpr ⟨(mem_inf.mp hp₃).1,
      mem_centralizer_singleton_iff.mpr (by
        calc p₃ * b₂ = p₃ * (p₃⁻¹ * b₂ * p₃) := by rw [hp₃b₂]
          _ = b₂ * p₃ := by group)⟩
    have hne1 : D₂₃.relIndex D₂ ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      intro hle
      exact hb₃ne (hp₃b₃.symm.trans (hmemC (mem_inf.mp (hle hp₃D)).2))
    have hne0 : D₂₃.relIndex D₂ ≠ 0 := by
      intro h
      rw [h, zero_mul] at h0
      exact Nat.card_pos.ne' h0.symm
    omega
  have hc₁ : Nat.card P = D₂.relIndex P * Nat.card D₂ := by
    rw [← relIndex_mul_card D₂ P, inf_eq_left.mpr inf_le_left]
  have hc₂ : Nat.card D₂ = D₂₃.relIndex D₂ * Nat.card D₂₃ := by
    rw [← relIndex_mul_card D₂₃ D₂, inf_eq_left.mpr inf_le_left]
  have hle : P ⊓ centralizer (B : Set G) ≤ D₂₃ := by
    intro p hp
    obtain ⟨hpP, hpC⟩ := mem_inf.mp hp
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hpP, ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hpC b₂ hb₂B).symm
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hpC b₃ hb₃B).symm
  have h1 := card_le_of_le hle
  have h2 : 4 * Nat.card D₂₃ ≤ 256 := by
    rw [← hP256, hc₁, hc₂]
    nlinarith
  omega

end CFSG.ComponentClassification.GrSLit.GrS4
