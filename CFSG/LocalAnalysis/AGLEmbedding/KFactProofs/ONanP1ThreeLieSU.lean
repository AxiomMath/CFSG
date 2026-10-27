module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSU
public import CFSG.LieType.Universal.Unitary.Extras.Commutator

public section

namespace CFSG.AGLEmbedding.P1Lie

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.RootSystem

section SU

variable {n : ℕ} {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] def toStdUHom (n : ℕ) : (Fin (n / 2) → ℤ) →+ (Fin (n / 2) → ℤ) :=
  AddMonoidHom.mk' (Unitary.toStd n) toStd_add'

theorem toStdUHom_apply (v : Fin (n / 2) → ℤ) : toStdUHom n v = Unitary.toStd n v := rfl

@[expose] def uSum (n : ℕ) : Fin (n / 2) → ℤ := fun k =>
  if Even n then cSum (n / 2) 0 1 k else if k.val = 0 then 1 else 2

@[expose] def uHead (n : ℕ) : Fin (n / 2) → ℤ := fun k =>
  if Even n then cLong (n / 2) 0 k else 1

theorem uSum_even (he : Even n) : uSum n = cSum (n / 2) 0 1 := by
  funext k
  simp only [uSum, he, ite_true]

theorem uHead_even (he : Even n) : uHead n = cLong (n / 2) 0 := by
  funext k
  simp only [uHead, he, ite_true]

theorem toStd_uSum (hn : 4 ≤ n) :
    Unitary.toStd n (uSum n) =
      Pi.single (⟨0, by omega⟩ : Fin (n / 2)) 1 + Pi.single (⟨1, by omega⟩ : Fin (n / 2)) 1 := by
  by_cases he : Even n
  · have h := toStd_cSum (n := n / 2) (a := 0) (b := 1) (by omega) (by omega)
    rw [uSum_even he]
    simpa only [Unitary.toStd, he, ite_true] using h
  · funext a
    simp only [Unitary.toStd, uSum, he, ite_false, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem toStd_uHead (hn : 4 ≤ n) :
    Unitary.toStd n (uHead n) =
      (if Even n then (2 : ℤ) else 1) • Pi.single (⟨0, by omega⟩ : Fin (n / 2)) 1 := by
  by_cases he : Even n
  · have h := toStd_cLong (n := n / 2) (a := 0) (by omega)
    rw [uHead_even he]
    simpa only [Unitary.toStd, he, ite_true, two_smul, two_nsmul] using h
  · funext a
    simp only [Unitary.toStd, uHead, he, ite_false, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      one_smul]
    split_ifs <;> omega

theorem weight_zero (hn : 4 ≤ n) :
    weight n ⟨0, by omega⟩ = Pi.single (⟨0, by omega⟩ : Fin (n / 2)) 1 := by
  funext c
  simp only [weight_apply', Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem weight_rev_one (hn : 4 ≤ n) :
    weight n (Fin.rev ⟨1, by omega⟩) = -Pi.single (⟨1, by omega⟩ : Fin (n / 2)) 1 := by
  funext c
  simp only [weight_apply', Pi.single_apply, Pi.neg_apply, Fin.ext_iff, Fin.val_rev]
  have := c.isLt
  split_ifs <;> omega

theorem weight_mid (hn : 4 ≤ n) (ho : ¬ Even n) : weight n ⟨n / 2, by omega⟩ = 0 := by
  have h2 : n % 2 = 1 := by have := Nat.even_iff.not.1 ho; omega
  funext c
  simp only [weight_apply', Pi.zero_apply]
  have := c.isLt
  split_ifs <;> omega

theorem uSum_mem_roots (hn : 4 ≤ n) :
    uSum n ∈ roots (isFiniteType_cartan n) (divisible n) := by
  refine mem_roots_of_weight_sub (a := ⟨0, by omega⟩) (b := Fin.rev ⟨1, by omega⟩) ?_ ?_
  · simp [Fin.ext_iff]; omega
  · rw [weight_zero hn, weight_rev_one hn, toStd_uSum hn, sub_neg_eq_add]

theorem uHead_mem_roots (hn : 4 ≤ n) :
    uHead n ∈ roots (isFiniteType_cartan n) (divisible n) := by
  by_cases he : Even n
  · refine mem_roots_of_weight_sub (a := ⟨0, by omega⟩) (b := Fin.rev ⟨0, by omega⟩) ?_ ?_
    · simp [Fin.ext_iff]; omega
    · rw [weight_rev', weight_zero hn, toStd_uHead hn, sub_neg_eq_add]
      simp [he, two_smul]
  · refine mem_roots_of_weight_sub (a := ⟨0, by omega⟩) (b := ⟨n / 2, by omega⟩) ?_ ?_
    · simp [Fin.ext_iff]; omega
    · rw [weight_zero hn, weight_mid hn he, toStd_uHead hn]
      simp [he]

theorem uSum_pos (hn : 4 ≤ n) :
    ∃ j₁ j₂ : Fin (n / 2), j₁ ≠ j₂ ∧ 0 < uSum n j₁ ∧ 0 < uSum n j₂ := by
  refine ⟨⟨0, by omega⟩, ⟨n / 2 - 1, by omega⟩, by simp [Fin.ext_iff]; omega, ?_, ?_⟩
  · by_cases he : Even n <;> simp [uSum, he, cSum]
  · by_cases he : Even n
    · simp only [uSum, he, ite_true, cSum]
      split_ifs <;> omega
    · simp only [uSum, he, ite_false]
      split_ifs <;> omega

theorem uHead_pos (hn : 4 ≤ n) :
    ∃ j₁ j₂ : Fin (n / 2), j₁ ≠ j₂ ∧ 0 < uHead n j₁ ∧ 0 < uHead n j₂ := by
  refine ⟨⟨0, by omega⟩, ⟨n / 2 - 1, by omega⟩, by simp [Fin.ext_iff]; omega, ?_, ?_⟩
  · by_cases he : Even n
    · simp only [uHead, he, ite_true, cLong]
      split_ifs <;> omega
    · simp [uHead, he]
  · by_cases he : Even n
    · simp only [uHead, he, ite_true, cLong]
      split_ifs <;> omega
    · simp [uHead, he]

theorem uSum_ne_two_smul (hn : 4 ≤ n) :
    ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), uSum n ≠ 2 • δ := by
  intro δ _ h
  have h1 := congrArg (fun v => Unitary.toStd n v ⟨0, by omega⟩) h
  rw [toStd_nsmul_two, toStd_uSum hn] at h1
  simp only [Pi.add_apply, Pi.single_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat,
    Fin.mk.injEq] at h1
  simp at h1
  omega

theorem uHead_ne_two_smul (hn : 4 ≤ n) :
    ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), uHead n ≠ 2 • δ := by
  intro δ hδ h
  by_cases he : Even n
  · have hd : divisible n = ∅ := by simp [divisible, he]
    exact two_smul_notMem_roots (isFiniteType_cartan n) hd hδ (h ▸ uHead_mem_roots hn)
  · have h1 := congrArg (fun v => Unitary.toStd n v ⟨0, by omega⟩) h
    rw [toStd_nsmul_two, toStd_uHead hn] at h1
    simp only [he, ite_false, one_smul, Pi.single_apply, Pi.smul_apply, nsmul_eq_mul,
      Nat.cast_ofNat] at h1
    simp at h1
    omega

theorem root_coord_one_eq_zero (hn : 4 ≤ n) {ε : Fin (n / 2) → ℤ}
    (hε : ε ∈ roots (isFiniteType_cartan n) (divisible n))
    (h0 : 2 ≤ Unitary.toStd n ε ⟨0, by omega⟩) : Unitary.toStd n ε ⟨1, by omega⟩ = 0 := by
  rw [roots_eq] at hε
  rcases hε with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exfalso
    have e0 := congrFun h ⟨0, by omega⟩
    rw [Pi.sub_apply, weight_apply', weight_apply'] at e0
    have hji' : j.val ≠ n - 1 - i.val := fun e => hji (Fin.ext (by simp only [Fin.val_rev]; omega))
    have := i.isLt
    have := j.isLt
    split_ifs at e0 <;> omega
  · have e0 := congrFun h ⟨0, by omega⟩
    have e1 := congrFun h ⟨1, by omega⟩
    rw [Pi.smul_apply, weight_apply'] at e0 e1
    have := i.isLt
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at e0 e1
    split_ifs at e0 e1 <;> omega
  · exfalso
    have e0 := congrFun h ⟨0, by omega⟩
    rw [weight_apply'] at e0
    split_ifs at e0 <;> omega

theorem toStd_combo (hn : 4 ≤ n) (a b : ℕ) :
    Unitary.toStd n (a • uSum n + b • uHead n) ⟨0, by omega⟩ =
        a + b * (if Even n then 2 else 1) ∧
      Unitary.toStd n (a • uSum n + b • uHead n) ⟨1, by omega⟩ = a := by
  have h : Unitary.toStd n (a • uSum n + b • uHead n) =
      a • Unitary.toStd n (uSum n) + b • Unitary.toStd n (uHead n) := by
    rw [← toStdUHom_apply, map_add, map_nsmul, map_nsmul]
    rfl
  rw [h, toStd_uSum hn, toStd_uHead hn]
  by_cases he : Even n <;>
    simp [he, Fin.ext_iff, nsmul_eq_mul, mul_comm]

theorem commRoots_uSum_uHead (hF : Nat.card F = (p ^ f) ^ 2) (hn : 4 ≤ n) :
    CommRoots (rootDatum hF n) (uSum n) (uHead n) := by
  refine ⟨fun a b h => ?_, ?_⟩
  · have e : Unitary.toStd n (a • uSum n + b • uHead n) =
        a • Unitary.toStd n (uSum n) + b • Unitary.toStd n (uHead n) := by
      rw [← toStdUHom_apply, map_add, map_zsmul, map_zsmul]
      rfl
    have h2 : a • uSum n + b • uHead n = (0 : Fin (n / 2) → ℤ) := h
    have h' : a • Unitary.toStd n (uSum n) + b • Unitary.toStd n (uHead n) = 0 := by
      rw [← e, h2]
      exact toStd_zero'
    have h0 := congrFun h' ⟨0, by omega⟩
    have h1 := congrFun h' ⟨1, by omega⟩
    rw [toStd_uSum hn, toStd_uHead hn] at h0 h1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.mk.injEq, Pi.zero_apply] at h0 h1
    by_cases he : Even n <;> simp [he] at h0 h1 <;> omega
  · ext ε
    simp only [openCone, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hε, a, b, ha, hb, rfl⟩
    obtain ⟨h0, h1⟩ := toStd_combo hn a b
    have hε' : (a • uSum n + b • uHead n : Fin (n / 2) → ℤ) ∈
        roots (isFiniteType_cartan n) (divisible n) := hε
    have h3 : (2 : ℤ) ≤ a + b * (if Even n then 2 else 1) := by split_ifs <;> omega
    have h2 := root_coord_one_eq_zero hn (ε := (a • uSum n + b • uHead n : Fin (n / 2) → ℤ)) hε'
      (by omega)
    omega

theorem isElemAbelian_range {A G : Type*} [CommGroup A] [Group G] {p : ℕ}
    (hA : ∀ a : A, a ^ p = 1) (φ : A →* G) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, hA x, map_one]

omit [Finite F] in
theorem rootHom_injective {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) :
    Function.Injective (rootHom σ hσ hij hi hj) := by
  intro c d h
  have hc := congrArg (fun g => mat σ n g i j) h
  simp only [mat_apply, coe_rootHom, rootMatrix_apply_pq hij hji] at hc
  exact hc

theorem exists_elemAbelian_uSum (hF : Nat.card F = (p ^ f) ^ 2) (hn : 4 ≤ n) :
    ∃ E ≤ (rootDatum hF n).rootGroup (uSum n), IsElemAbelian p E ∧ p ^ (2 * f) ≤ Nat.card E := by
  have hσ := unitaryInvolution_involutive hF
  have hij : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨1, by omega⟩ := by simp [Fin.ext_iff]; omega
  have hi : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by simp [Fin.ext_iff]; omega
  have hj : Fin.rev (⟨1, by omega⟩ : Fin n) ≠ Fin.rev (Fin.rev ⟨1, by omega⟩) := by
    simp [Fin.ext_iff]; omega
  have hji : Fin.rev (⟨1, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    simp [Fin.ext_iff]; omega
  have hw : weight n ⟨0, by omega⟩ - weight n (Fin.rev ⟨1, by omega⟩) = Unitary.toStd n (uSum n) :=
    by rw [weight_zero hn, weight_rev_one hn, toStd_uSum hn, sub_neg_eq_add]
  refine ⟨(rootHom (unitaryInvolution F p f) hσ hij hi hj).range, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact rootHom_mem hσ hij hi hj hji hw c
  · refine isElemAbelian_range (fun a => ?_) _
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · have key : Nat.card (rootHom (unitaryInvolution F p f) hσ hij hi hj).range =
        Nat.card (Multiplicative F) :=
      Nat.card_range_of_injective (rootHom_injective hσ hij hi hj hji)
    rw [key, Nat.card_congr Multiplicative.toAdd, hF, two_mul, pow_add, sq]

theorem weakCore_su (hF : Nat.card F = (p ^ f) ^ 2) (hn : 4 ≤ n) :
    GLBWeakCore p (posUnipotent (rootDatum hF n)) = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF n (by omega) ζ hζ
  have hct := isCTGroupDatum hF n (by omega) ζ hζ
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hX : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup p ((rootDatum hF n).rootGroup γ) := fun γ hγ =>
    isPGroup_rootGroup (unitaryInvolution_involutive hF) (SUExtras.toStd_ne_zero_of_mem_roots hγ)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 : Nat.card F = 1 := by simpa using hF
      have h2 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h
  have hne : uSum n ≠ uHead n := fun h => by
    have h1 := congrArg (fun v => Unitary.toStd n v ⟨1, by omega⟩) h
    rw [toStd_uSum hn, toStd_uHead hn] at h1
    by_cases he : Even n <;> simp [he, Fin.ext_iff] at h1
  refine weakCore_posUnipotent_eq_top_of_weighted_pair (D := rootDatum hF n) hct hext Fact.out
    (by show 2 ≤ n / 2; omega) (γ₁ := uSum n) (γ₂ := uHead n) (2 * f) 1
    (exists_elemAbelian_uSum hF hn)
    (exists_elemAbelian_of_pGroup_ne_bot Fact.out (hX _ (uHead_mem_roots hn))
      (hext.ne_bot _ (uHead_mem_roots hn))) ?_ hne (commRoots_uSum_uHead hF hn) (by omega)
  exact (Finset.forall_mem_insert _ _ _).2 ⟨⟨uSum_mem_roots hn, uSum_pos hn, uSum_ne_two_smul hn⟩,
    fun γ hγ => by
      rw [Finset.mem_singleton.1 hγ]
      exact ⟨uHead_mem_roots hn, uHead_pos hn, uHead_ne_two_smul hn⟩⟩

open CFSG.AGLEmbedding.CharPGen in
theorem exists_pGroup_weakCore_su {G : Type} [Group G] [Finite G]
    (hF : Nat.card F = (p ^ f) ^ 2) (hn : 4 ≤ n) (e : G ≃* StatedProj (StatedSU n (p ^ f) F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF n (by omega) ζ hζ
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hX : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup p ((rootDatum hF n).rootGroup γ) := fun γ hγ =>
    isPGroup_rootGroup (unitaryInvolution_involutive hF) (SUExtras.toStd_ne_zero_of_mem_roots hγ)
  have hU : IsPGroup p (posUnipotent (rootDatum hF n)) := isPGroup_iSup_pos hext hX
  let ψ := equivStatedSU hF n
  let π : SU (unitaryInvolution F p f) n →* G :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ψ.toMonoidHom)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp ψ.surjective)
  have hinj : ∀ x ∈ posUnipotent (rootDatum hF n), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ (ψ x) : StatedProj (StatedSU n (p ^ f) F)) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    have hk' : ψ x ^ p ^ k = 1 := by
      rw [← map_pow]
      exact (map_eq_one_iff _ ψ.injective).2 (congrArg Subtype.val hk)
    exact ψ.injective (by
      rw [map_one]
      exact eq_one_of_mem_statedScalars_of_pow (⟨0, by omega⟩ : Fin n)
        (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmk)) hk')
  exact ⟨(posUnipotent (rootDatum hF n)).map π, hU.map π,
    weakCore_map_eq_top Fact.out π hπ hinj (weakCore_su hF hn)⟩

theorem exists_pGroup_weakCore_of_model_psu {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (hn : 4 ≤ n) (h : StatedClassicalModel G .PSU n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact exists_pGroup_weakCore_su hcard hn e

end SU

end CFSG.AGLEmbedding.P1Lie

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem weakCharPGenAt_su : WeakCharPGenAt IsSUIndex := by
  intro K _ _ _ _ d ⟨r, q, hr, hd⟩ ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_of_model_psu (by omega)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T

end CFSG.AGLEmbedding
