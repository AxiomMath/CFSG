module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog71Cover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bSmallInv
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem pRank_two_le_one_of_forall_sq_eq_one_mem {Y : Type*} [Group Y] (Z : Subgroup Y)
    (hZ : Nat.card Z = 2) (h : ∀ y : Y, y ^ 2 = 1 → y ∈ Z) : CFSG.pRank 2 Y ≤ 1 := by
  refine LieType.SteinbergBR.pRank_le_of_card_le (by norm_num) fun A hA => ?_
  have hle : A ≤ Z := fun a ha => h a (elemPow_eq_one_of_isElementaryAbelian a ha)
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  calc Nat.card A ≤ Nat.card Z := card_le_of_le hle
    _ = 2 ^ 1 := by rw [hZ, pow_one]

theorem exists_sl2_equiv_of_perfect {P Q : Type} [Group P] [Group Q] [Finite P]
    (hP : Group.IsPerfect P) {η : P →* Q} (hη : Function.Surjective η)
    (hC : η.ker ≤ center P) (hcard : Nat.card η.ker = 2) {p f : ℕ} (hp2 : p ≠ 2)
    (hQ : Blueprint.LieModel Q .PSL 2 p f) :
    p.Prime ∧ 1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (P ≃* SL(2, K)) := by
  have := hP
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hQ
  have hk : ringChar K ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK
  let φ := specialLinearGroupEquivStatedSL 2 K
  let β : SL(2, K) →* Q := (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom
  have hβ : Function.Surjective β :=
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)).comp φ.surjective
  have hker : β.ker = center (SL(2, K)) := by
    ext x
    have h1 : x ∈ β.ker ↔ φ x ∈ (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) := by
      rw [← LieType.Steinberg.ker_comp_mk' _ e.symm]
      rfl
    rw [h1, ← map_center_eq_statedScalars]
    exact ⟨fun ⟨y, hy, hxy⟩ => (φ.injective hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(2, K)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : SL(2, K) →* E, ∀ x, π (σ x) = x :=
    fun E _ _ π hπ hcen h2 =>
      (LieType.Steinberg.sl_central_two_extension_splitting 1 hk hπ hcen h2).imp fun _ h => h.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  obtain ⟨α, hαβ, hαs, hαker⟩ :=
    LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ hη hC h2
  have hcardβ : Nat.card β.ker ≤ 2 := by
    rw [hker]
    exact Nat.le_of_dvd (by norm_num) ((LieType.Steinberg.card_center_specialLinearGroup_dvd
      (by norm_num) K).trans (Nat.gcd_dvd_left 2 _))
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxβ : x ∈ β.ker := by rw [MonoidHom.mem_ker, ← hαβ x, hx, map_one]
    let g : β.ker →* η.ker := (α.comp β.ker.subtype).codRestrict η.ker fun y => by
      rw [hαker]
      exact mem_map_of_mem _ y.2
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      rw [hαker] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨⟨w, hw⟩, rfl⟩
    have : Finite β.ker := inferInstance
    have hcard' : Nat.card η.ker ≤ Nat.card β.ker := Nat.card_le_card_of_surjective g hg
    have hgi : Function.Injective g :=
      (Function.Surjective.bijective_of_nat_card_le hg (by omega)).1
    have h1 : g ⟨x, hxβ⟩ = g 1 := Subtype.ext (by simpa [g] using hx)
    have := congrArg Subtype.val (hgi h1)
    simpa using this
  exact ⟨hp, hf, K, inferInstance, inferInstance, hK,
    ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm⟩⟩

theorem forall_sq_eq_one_mem_center_of_sl2 {P : Type*} [Group P] {K : Type*} [Field K]
    (hK : (2 : K) ≠ 0) (e : P ≃* SL(2, K)) (y : P) (hy : y ^ 2 = 1) : y ∈ center P := by
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  have h1 : e y ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  have h2 : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hneg : e y = -1 := Subtype.ext (LinearGroups.SL2_coe_eq_neg_one_of_sq hK _ h1 h2)
  rw [mem_center_iff]
  intro g
  apply e.injective
  rw [map_mul, map_mul, hneg]
  exact Subtype.ext (by simp)

theorem two_ne_zero_of_card {K : Type*} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) : (2 : K) ≠ 0 :=
  Ring.two_ne_zero (LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK)

noncomputable def alt67 : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  ((Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb).comp (alternatingGroup (Fin 6)).subtype).codRestrict
    (alternatingGroup (Fin 7)) fun σ => by
      classical
      rw [MonoidHom.comp_apply, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding,
        Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_extendDomain]
      exact σ.2

theorem alt67_injective : Function.Injective alt67 := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective Fin.castSuccEmb h')

@[expose] def dbl6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3,
    Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

@[expose] def cyc6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap (1 : Fin 6) 2 * Equiv.swap (2 : Fin 6) 3,
    Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

theorem dbl6_sq : dbl6 ^ 2 = 1 :=
  Subtype.ext (by
    show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3) ^ 2 = 1
    decide)

theorem dbl6_ne : dbl6 ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  revert h'
  show Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3 ≠ 1
  decide

theorem dbl6_cyc6 : dbl6 * cyc6 ≠ cyc6 * dbl6 := fun h => by
  have h' := congrArg Subtype.val h
  revert h'
  show Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3 *
      (Equiv.swap (1 : Fin 6) 2 * Equiv.swap (2 : Fin 6) 3) ≠
    Equiv.swap (1 : Fin 6) 2 * Equiv.swap (2 : Fin 6) 3 *
      (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3)
  decide

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem forall_sq_eq_one_mem_center_of_alt7 {Y : Type} [Group Y] [Finite Y]
    (hY : Group.IsPerfect Y) (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* alternatingGroup (Fin 7)) (y : Y) (hy : y ^ 2 = 1) :
    y ∈ center Y := by
  classical
  let π : Y →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' (center Y))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center Y := LieType.Steinberg.ker_comp_mk' _ e
  have hmemZ : ∀ x : Y, x ∈ center Y ↔ π x = 1 := fun x => by rw [← hker, MonoidHom.mem_ker]
  let H : Subgroup (alternatingGroup (Fin 7)) := alt67.range
  let Hh : Subgroup Y := H.comap π
  have hZH : center Y ≤ Hh := fun z hz => by
    show π z ∈ H
    rw [(hmemZ z).1 hz]
    exact one_mem _
  have hA6 : commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hHperf : (⁅H, H⁆ : Subgroup _) = H := by
    show ⁅alt67.range, alt67.range⁆ = alt67.range
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hA6]
  have hmapC : (⁅Hh, Hh⁆ : Subgroup Y).map π = H := by
    rw [map_commutator, map_comap_eq_self_of_surjective hπ, hHperf]
  have hsup : center Y ⊔ ⁅Hh, Hh⁆ = Hh := by
    refine le_antisymm (sup_le hZH (commutator_le_self Hh)) fun x hx => ?_
    have hπx : π x ∈ (⁅Hh, Hh⁆ : Subgroup Y).map π := by
      rw [hmapC]
      exact hx
    obtain ⟨c, hc, hcx⟩ := hπx
    have hz : c⁻¹ * x ∈ center Y := by
      rw [hmemZ, map_mul, map_inv, hcx, inv_mul_cancel]
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_sup_right hc) (mem_sup_left hz)
  have hcardH : Nat.card H = 360 := by
    rw [← card_alt6]
    exact Nat.card_congr (MonoidHom.ofInjective alt67_injective).symm.toEquiv
  have hindex : Hh.index = 7 := by
    rw [index_comap_of_surjective H hπ]
    have h := index_mul_card H
    rw [hcardH, card_alt7] at h
    omega
  have hinf : center Y ⊓ ⁅Hh, Hh⁆ ≠ ⊥ := by
    intro hbot
    have hcop : Nat.Coprime Hh.index (Nat.card (center Y)) := by
      rw [hindex, hZ]
      norm_num
    obtain ⟨D, hD, -, -⟩ := GroupTheory.abelian_normal_coprime_index_complement_lifting
      (center Y) Hh ⁅Hh, Hh⁆ hcop hbot hsup
    have hDi : D.index = 2 := by rw [hD.index_eq_card, hZ]
    have : D.Normal := normal_of_index_eq_two hDi
    have hQ : Nat.card (Y ⧸ D) = 2 := by rw [← index_eq_card, hDi]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (Y ⧸ D) := isCyclic_of_prime_card hQ
    have hle : commutator Y ≤ D := Normal.quotient_commutative_iff_commutator_le.1 inferInstance
    rw [hY.commutator_eq_top, top_le_iff] at hle
    rw [hle, index_top] at hDi
    omega
  have hZC : center Y ≤ ⁅Hh, Hh⁆ := by
    have hle : center Y ⊓ ⁅Hh, Hh⁆ ≤ center Y := inf_le_left
    have : Finite (center Y) := inferInstance
    have hdvd : Nat.card ↥(center Y ⊓ ⁅Hh, Hh⁆) ∣ 2 := hZ ▸ card_dvd_of_le hle
    have h1 : Nat.card ↥(center Y ⊓ ⁅Hh, Hh⁆) ≠ 1 := fun h1 =>
      hinf ((card_eq_one).1 h1)
    have h2 : Nat.card ↥(center Y ⊓ ⁅Hh, Hh⁆) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd h h1
      · exact h
    have heq : center Y ⊓ ⁅Hh, Hh⁆ = center Y :=
      eq_of_le_of_card_ge hle (by rw [hZ, h2])
    rw [← heq]
    exact inf_le_right
  have hHh : ⁅Hh, Hh⁆ = Hh := (sup_eq_right.2 hZC).symm.trans hsup
  have hperfH : Group.IsPerfect Hh := isPerfect_iff.2 hHh
  let η : Hh →* H := (π.comp Hh.subtype).codRestrict H fun x => x.2
  have hη : Function.Surjective η := by
    rintro ⟨h, hh⟩
    obtain ⟨x, rfl⟩ := hπ h
    exact ⟨⟨x, hh⟩, rfl⟩
  have hkerη : η.ker = (center Y).subgroupOf Hh := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hmemZ]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hηC : η.ker ≤ center Hh := by
    rw [hkerη]
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hx g)
  have hηcard : Nat.card η.ker = 2 := by
    rw [hkerη, ← hZ]
    exact Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv
  have hL : Blueprint.LieModel H .PSL 2 3 2 :=
    Or.inl ⟨by decide,
      LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six H
        ⟨(MonoidHom.ofInjective alt67_injective).symm⟩⟩
  obtain ⟨-, -, K, _, _, hK, ⟨eH⟩⟩ :=
    exists_sl2_equiv_of_perfect hperfH hη hηC hηcard (by norm_num) hL
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_card Nat.prime_three (by norm_num) hK
  by_contra hyZ
  have hπy : π y ≠ 1 := fun h => hyZ ((hmemZ y).2 h)
  have hπy2 : orderOf (π y) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hy, map_one]
    · exact hπy
  have hd2 : orderOf (alt67 dbl6) = 2 := by
    rw [orderOf_injective alt67 alt67_injective]
    exact orderOf_eq_prime dbl6_sq dbl6_ne
  obtain ⟨g, hg⟩ := alternating_involutions_conj (by norm_num) (π y) (alt67 dbl6) hπy2 hd2
  obtain ⟨g', rfl⟩ := hπ g
  have hy'H : g'⁻¹ * y * g' ∈ Hh := by
    show π (g'⁻¹ * y * g') ∈ H
    rw [map_mul, map_mul, map_inv, hg]
    exact ⟨dbl6, rfl⟩
  have hy'2 : (⟨g'⁻¹ * y * g', hy'H⟩ : Hh) ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    calc (g'⁻¹ * y * g') ^ 2 = g'⁻¹ * y ^ 2 * g' := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hy]; group
  have hcen := forall_sq_eq_one_mem_center_of_sl2 h2K eH _ hy'2
  have hcH : alt67 cyc6 ∈ H := ⟨cyc6, rfl⟩
  obtain ⟨c, hc⟩ := hπ (alt67 cyc6)
  have hcHh : c ∈ Hh := by
    show π c ∈ H
    rw [hc]
    exact hcH
  have hcomm := congrArg (fun w : Hh => π (w : Y)) ((mem_center_iff.1 hcen) ⟨c, hcHh⟩)
  simp only [coe_mul, map_mul, map_inv, hc, hg] at hcomm
  apply dbl6_cyc6
  apply alt67_injective
  rw [map_mul, map_mul]
  exact hcomm.symm

theorem cfDoubleCover : CFDoubleCover := by
  intro Y _ _ hq hZ htype
  have hperf : Group.IsPerfect Y := hq.1
  have hL2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel (Y ⧸ center Y) .PSL 2 p f →
      CFSG.pRank 2 Y ≤ 1 ∧ ((∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (Y ≃* SL(2, GaloisField p n))) ∨
        Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin 7))) := by
    intro p f hp hp2 hf hL
    have hker : (QuotientGroup.mk' (center Y)).ker = center Y := QuotientGroup.ker_mk' _
    obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := exists_sl2_equiv_of_perfect hperf
      (QuotientGroup.mk'_surjective _) hker.le (by rw [hker, hZ]) hp2 hL
    have h2K := two_ne_zero_of_card hp hp2 hK
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨pRank_two_le_one_of_forall_sq_eq_one_mem (center Y) hZ
      (forall_sq_eq_one_mem_center_of_sl2 h2K e), Or.inl ⟨p, f, ⟨hp⟩, hp2, hf, ⟨e.trans
        (Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
          (ClassicalModels.finiteFieldEquivGaloisField K p f hf hK))⟩⟩⟩
  rcases htype with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · rcases hn with rfl | rfl | rfl
    · exact hL2 5 1 Nat.prime_five (by norm_num) le_rfl (Or.inl ⟨by decide,
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
          ⟨e⟩⟩)
    · exact hL2 3 2 Nat.prime_three (by norm_num) (by norm_num) (Or.inl ⟨by decide,
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
          ⟨e⟩⟩)
    · exact ⟨pRank_two_le_one_of_forall_sq_eq_one_mem (center Y) hZ
        (forall_sq_eq_one_mem_center_of_alt7 hperf hZ e), Or.inr ⟨e⟩⟩
  · exact hL2 p f hp hp2 hf hL

end CFSG.ComponentClassification.CatFactsSmall
