module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {Λ Ã : Type} [Group Λ] [Finite Λ] [Group Ã] [Finite Ã]

@[expose] def lift2 (φ : Λ →* Ã) (K : Subgroup Ã) : Subgroup Λ := pCoreOf 2 (K.comap φ)

omit [Finite Λ] [Finite Ã] in
theorem lift2_isPGroup (φ : Λ →* Ã) (K : Subgroup Ã) : IsPGroup 2 (lift2 φ K) :=
  pCoreOf_isPGroup 2 _

omit [Finite Λ] [Finite Ã] in
theorem lift2_le_comap (φ : Λ →* Ã) (K : Subgroup Ã) : lift2 φ K ≤ K.comap φ :=
  pCoreOf_le 2 _

omit [Finite Λ] in
theorem isNilpotent_comap (φ : Λ →* Ã) (hker : φ.ker ≤ Subgroup.center Λ) {K : Subgroup Ã}
    (hK : IsPGroup 2 ↥K) : Group.IsNilpotent ↥(K.comap φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥K := hK.isNilpotent
  let f : ↥(K.comap φ) →* ↥K := (φ.comp (K.comap φ).subtype).codRestrict K (fun x => x.2)
  refine Subgroup.isNilpotent_of_ker_le_center f ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx1 : φ x = 1 := congrArg Subtype.val hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker (by rwa [MonoidHom.mem_ker])) g

theorem le_lift2 (φ : Λ →* Ã) (hker : φ.ker ≤ Subgroup.center Λ) {K : Subgroup Ã}
    (hK : IsPGroup 2 ↥K) {T : Subgroup Λ} (hT : T ≤ K.comap φ) (hT2 : IsPGroup 2 ↥T) :
    T ≤ lift2 φ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil := isNilpotent_comap φ hker hK
  set E : Subgroup Λ := K.comap φ with hE
  have hT' : IsPGroup 2 (T.subgroupOf E) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hT).symm
  obtain ⟨P, hTP⟩ := hT'.exists_le_sylow
  have hPn : (P : Subgroup ↥E).Normal := inferInstance
  have hPcore : (P : Subgroup ↥E) ≤ pCore 2 ↥E := by
    rw [pCore_eq_sSup]; exact le_sSup ⟨hPn, P.isPGroup'⟩
  intro t ht
  have h1 : (⟨t, hT ht⟩ : ↥E) ∈ (P : Subgroup ↥E) :=
    hTP (show (⟨t, hT ht⟩ : ↥E) ∈ T.subgroupOf E from ht)
  exact ⟨⟨t, hT ht⟩, hPcore h1, rfl⟩

omit [Finite Λ] [Finite Ã] in
theorem injective_comp_subtype (φ : Λ →* Ã) (hodd : Odd (Nat.card φ.ker)) {T : Subgroup Λ}
    (hT : IsPGroup 2 ↥T) : Function.Injective (φ.comp T.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxker : ((x : ↥T) : Λ) ∈ φ.ker := hx
  obtain ⟨e, he⟩ := hT x
  have h1 : ((x : Λ)) ^ 2 ^ e = 1 := congrArg Subtype.val he
  have h2 : orderOf (⟨(x : Λ), hxker⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
  have h3 : orderOf (⟨(x : Λ), hxker⟩ : φ.ker) ∣ 2 ^ e := by
    apply orderOf_dvd_of_pow_eq_one; exact Subtype.ext h1
  have h4 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr (hodd.of_dvd_nat h2))) h3
  rw [orderOf_eq_one_iff] at h4
  rw [Subgroup.mem_bot]
  exact Subtype.ext (congrArg (fun z : φ.ker => (z : Λ)) h4)

omit [Finite Λ] [Finite Ã] in
theorem card_map_of_isPGroup (φ : Λ →* Ã) (hodd : Odd (Nat.card φ.ker)) {T : Subgroup Λ}
    (hT : IsPGroup 2 ↥T) : Nat.card ↥(T.map φ) = Nat.card ↥T := by
  have hrange : T.map φ = (φ.comp T.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective (injective_comp_subtype φ hodd hT)).toEquiv).symm

theorem map_lift2 (φ : Λ →* Ã) (hker : φ.ker ≤ Subgroup.center Λ)
    (hodd : Odd (Nat.card φ.ker)) (hsurj : Function.Surjective φ) {K : Subgroup Ã}
    (hK : IsPGroup 2 ↥K) : (lift2 φ K).map φ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil := isNilpotent_comap φ hker hK
  set E : Subgroup Λ := K.comap φ with hE
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.map_le_iff_le_comap.mpr (lift2_le_comap φ K)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hK
  let f : ↥E →* ↥K := (φ.comp E.subtype).codRestrict K (fun x => x.2)
  have hfs : Function.Surjective f := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := hsurj k
    exact ⟨⟨x, show φ x ∈ K by rw [hx]; exact hk⟩, Subtype.ext hx⟩
  have hcardE : Nat.card f.ker * Nat.card ↥K = Nat.card ↥E := by
    have := Subgroup.card_ker_mul_card_range f
    rwa [f.range_eq_top_of_surjective hfs, Subgroup.card_top] at this
  have hkerE : Nat.card f.ker = Nat.card φ.ker := by
    have hmapE : f.ker.map E.subtype = φ.ker := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : f y = 1 := hy
        exact congrArg Subtype.val hy'
      · intro hx
        have hx1 : φ x = 1 := hx
        have hxE : x ∈ E := show φ x ∈ K by rw [hx1]; exact K.one_mem
        refine ⟨⟨x, hxE⟩, ?_, rfl⟩
        exact Subtype.ext hx1
    rw [← hmapE, Subgroup.card_map_of_injective E.subtype_injective]
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥E))
  have hPcard : Nat.card (P : Subgroup ↥E) = 2 ^ m := by
    rw [Sylow.card_eq_multiplicity, ← hcardE, hkerE, hm]
    have hodd' : ¬ 2 ∣ Nat.card φ.ker := by
      rintro h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    have hfac : (Nat.card φ.ker).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hodd'
    rw [Nat.factorization_mul (Nat.card_pos (α := φ.ker)).ne' (by positivity), Finsupp.add_apply,
      hfac, Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
    simp
  have hPn : (P : Subgroup ↥E).Normal := inferInstance
  have hPcore : (P : Subgroup ↥E) ≤ pCore 2 ↥E := by
    rw [pCore_eq_sSup]; exact le_sSup ⟨hPn, P.isPGroup'⟩
  have hlift : 2 ^ m ≤ Nat.card ↥(lift2 φ K) := by
    have h1 : Nat.card (pCoreOf 2 E) = Nat.card (pCore 2 ↥E) :=
      Subgroup.card_map_of_injective E.subtype_injective
    rw [← hPcard]
    calc Nat.card (P : Subgroup ↥E) ≤ Nat.card (pCore 2 ↥E) := Subgroup.card_le_of_le hPcore
      _ = Nat.card ↥(lift2 φ K) := h1.symm
  have hmapcard : Nat.card ↥((lift2 φ K).map φ) = Nat.card ↥(lift2 φ K) :=
    card_map_of_isPGroup φ hodd (lift2_isPGroup φ K)
  rw [hmapcard, hm]
  exact hlift

theorem mem_normalizer_lift2 (φ : Λ →* Ã) (hker : φ.ker ≤ Subgroup.center Λ) {K : Subgroup Ã}
    (hK : IsPGroup 2 ↥K) {n : Λ} (hn : φ n ∈ Subgroup.normalizer (K : Set Ã)) :
    n ∈ Subgroup.normalizer (lift2 φ K : Set Λ) := by
  have key : ∀ m : Λ, φ m ∈ Subgroup.normalizer (K : Set Ã) → ∀ x ∈ lift2 φ K,
      m * x * m⁻¹ ∈ lift2 φ K := by
    intro m hm x hx
    have hT2 : IsPGroup 2 ↥((lift2 φ K).map (MulAut.conj m).toMonoidHom) :=
      (lift2_isPGroup φ K).map (MulAut.conj m).toMonoidHom
    have hle : (lift2 φ K).map (MulAut.conj m).toMonoidHom ≤ K.comap φ := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : φ y ∈ K := lift2_le_comap φ K hy
      show φ (m * y * m⁻¹) ∈ K
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hm (φ y)).mp h1
    exact le_lift2 φ hker hK hle hT2 ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
  have hn' : φ n⁻¹ ∈ Subgroup.normalizer (K : Set Ã) := by
    rw [map_inv]; exact Subgroup.inv_mem _ hn
  have := key n⁻¹ hn' _ hx
  simpa [mul_assoc] using this

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
