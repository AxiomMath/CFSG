module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicBasic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

section Six

variable {G : Type} [Group G] [Finite G]

theorem commutator_ne_self_of_card_six {L : Subgroup G} (h6 : Nat.card L = 6) :
    ⁅L, L⁆ ≠ L := by
  intro hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 (by rw [h6]; norm_num)
  have hP : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have h1 := (Subgroup.zpowers x).index_mul_card
    rw [h6, hP] at h1
    omega
  have : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hidx
  have hcyc : IsCyclic (↥L ⧸ Subgroup.zpowers x) := isCyclic_of_prime_card (p := 2) hidx
  have hcomm : ∀ a b : ↥L ⧸ Subgroup.zpowers x, a * b = b * a :=
    isMulCommutative_iff.1 hcyc.isMulCommutative
  have hle : ⁅L, L⁆ ≤ (Subgroup.zpowers x).map L.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : (QuotientGroup.mk' (Subgroup.zpowers x)) ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  have := Subgroup.card_le_of_le (hp.symm.le.trans hle)
  rw [h6, Subgroup.card_map_of_injective L.subtype_injective, hP] at this
  omega

theorem exists_elemAbelian_card_27 {L₁ L₂ L₃ : Subgroup G}
    (h₁ : Nat.card L₁ = 6) (h₃ : Nat.card L₃ = 6)
    (hnc₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hnc₃ : ∃ a ∈ L₃, ∃ b ∈ L₃, a * b ≠ b * a)
    (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (h23 : ∀ b ∈ L₂, ∀ c ∈ L₃, b * c = c * b) {c₁ c₂ c₃ : G} (hc₁ : c₁ ∈ L₁) (hc₂ : c₂ ∈ L₂)
    (hc₃ : c₃ ∈ L₃) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1) (h3 : c₃ ≠ 1) (h1' : c₁ ^ 3 = 1)
    (h2' : c₂ ^ 3 = 1) (h3' : c₃ ^ 3 = 1) :
    ∃ E : Subgroup G, E ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : ∀ c : G, c ≠ 1 → c ^ 3 = 1 → Nat.card (Subgroup.zpowers c) = 3 := fun c hc hc3 => by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc]
  have hZ₁ : Subgroup.zpowers c₁ ≤ L₁ := (Subgroup.zpowers_le).mpr hc₁
  have hZ₂ : Subgroup.zpowers c₂ ≤ L₂ := (Subgroup.zpowers_le).mpr hc₂
  have hZ₃ : Subgroup.zpowers c₃ ≤ L₃ := (Subgroup.zpowers_le).mpr hc₃
  have c12 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_commute (A := Subgroup.zpowers c₁) (B := Subgroup.zpowers c₂)
      fun a ha b hb => h12 a (hZ₁ ha) b (hZ₂ hb))
  have hi12 : Subgroup.zpowers c₁ ⊓ Subgroup.zpowers c₂ = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hZ₁ hZ₂).trans (inf_eq_bot_of_commutes_of_card_six h₁ hnc₁ h12).le)
  rw [hi12, Subgroup.card_bot, mul_one, hz _ h1 h1', hz _ h2 h2'] at c12
  have h123 := commute_sup_of h13 h23
  have c3 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_commute (A := Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂)
      (B := Subgroup.zpowers c₃) fun a ha b hb => h123 a (sup_le_sup hZ₁ hZ₂ ha) b (hZ₃ hb))
  have hi3 : (Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂) ⊓ Subgroup.zpowers c₃ = ⊥ := by
    refine eq_bot_iff.mpr ((inf_le_inf (sup_le_sup hZ₁ hZ₂) hZ₃).trans ?_)
    rw [inf_comm]
    exact (inf_eq_bot_of_commutes_of_card_six h₃ hnc₃ fun c hc x hx => (h123 x hx c hc).symm).le
  rw [hi3, Subgroup.card_bot, mul_one, c12, hz _ h3 h3'] at c3
  refine ⟨Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ ⊔ Subgroup.zpowers c₃,
    sup_le_sup (sup_le_sup hZ₁ hZ₂) hZ₃, ?_, by rw [c3]⟩
  have hcl : Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ ⊔ Subgroup.zpowers c₃ =
      Subgroup.closure {c₁, c₂, c₃} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      sup_assoc, ← Subgroup.closure_union, ← Subgroup.closure_union, Set.singleton_union,
      Set.singleton_union]
  rw [hcl]
  refine isElemAbelian_three_closure_of_pairwise ?_ ?_
  · have k12 : Commute c₁ c₂ := h12 _ hc₁ _ hc₂
    have k13 : Commute c₁ c₃ := h13 _ hc₁ _ hc₃
    have k23 : Commute c₂ c₃ := h23 _ hc₂ _ hc₃
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl <;> assumption

end Six

section Index

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem card_borel_sup_rankOne_of
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hH : ∀ k, H k = ⊥) (hU2 : IsPGroup 2 (posUnipotent D)) (i : Fin D.rank)
    (h6 : Nat.card (rankOne D.rootGroup i) = 6)
    (hnc : ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a) :
    Nat.card (borel D H ⊔ rankOne D.rootGroup i : Subgroup K) = 3 * Nat.card (borel D H) := by
  set L := rankOne D.rootGroup i with hL
  set U := ⨆ j ∈ ({i} : Set (Fin D.rank))ᶜ, radical D j with hU
  have hBU : borel D H ≤ posUnipotent D := sup_le (iSup_le fun k => (hH k).le.trans bot_le) le_rfl
  have hB2 : IsPGroup 2 (borel D H) := hU2.to_le hBU
  have hUB : U ≤ borel D H :=
    (iSup₂_le fun j _ => radical_le_posUnipotent j).trans posUnipotent_le_borel
  have hB : borel D H ≤ (borel D H ⊓ L) ⊔ U :=
    borel_le_sup_radicals hH ({i} : Set (Fin D.rank)) (borel D H ⊓ L) fun γ hγ hpos h =>
      le_inf (rootGroup_le_borel hγ hpos) (hct.le_rankOne i γ hγ fun k hk => h k hk)
  have hLN : L ≤ Subgroup.normalizer (U : Set K) :=
    le_normalizer_sup_radicals ({i} : Set (Fin D.rank)) fun j hj =>
      rankOne_le_normalizer_radical hext fun h => hj h.symm
  have hU2' : IsPGroup 2 U := sup_radicals_isPGroup hU2 ({i} : Set (Fin D.rank))
  have hUL : U ⊓ L = ⊥ :=
    eq_bot_of_isPGroup_two_of_card_six h6 hnc inf_le_right
      ((le_inf hLN Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (hU2'.to_le inf_le_left)
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hXBL : D.rootGroup (Pi.single i 1) ≤ borel D H ⊓ L :=
    le_inf (rootGroup_le_borel hα (ht_single_pos i)) le_sup_left
  have hBL2 : Nat.card (borel D H ⊓ L : Subgroup K) = 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hB2.to_le (inf_le_left : borel D H ⊓ L ≤ _))
    have hd : 2 ^ k ∣ 6 := by
      rw [← hk, ← h6]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have := (pow_dvd_pow 2 (show 2 ≤ k by omega)).trans hd
      norm_num at this
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      exact hext.ne_bot (Pi.single i 1) hα
        (eq_bot_iff.mpr (hXBL.trans (Subgroup.eq_bot_of_card_eq _ hk).le))
    rw [hk, show k = 1 by omega, pow_one]
  have hBeq : borel D H = U ⊔ (borel D H ⊓ L) :=
    le_antisymm (hB.trans (le_of_eq (sup_comm _ _))) (sup_le hUB inf_le_left)
  have hcB := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    ((inf_le_right : borel D H ⊓ L ≤ L).trans hLN)
  have hUBL : U ⊓ (borel D H ⊓ L) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left U inf_le_right).trans hUL.le)
  rw [hUBL, Subgroup.card_bot, mul_one, hBL2, ← hBeq] at hcB
  have hBLeq : borel D H ⊔ L = U ⊔ L :=
    le_antisymm (sup_le (hBeq.le.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right)))
      le_sup_right) (sup_le (hUB.trans le_sup_left) le_sup_right)
  have hcL := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hLN
  rw [hUL, Subgroup.card_bot, mul_one, h6] at hcL
  rw [hBLeq, hcL, hcB]
  ring

end Index

section Spin

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem spin_cover_core (hF : Nat.card F = 2) {A₁ A₂ : Subgroup (spinGroup (quadPlus 4 F))}
    (hcov : ∀ i : Fin 4, rankOne (plusDatum 4 F three_le_four).rootGroup i ≤ A₁ ∨
      rankOne (plusDatum 4 F three_le_four).rootGroup i ≤ A₂)
    (h27₁ : ∀ E : Subgroup (spinGroup (quadPlus 4 F)), E ≤ A₁ → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E ≠ 27)
    (h27₂ : ∀ E : Subgroup (spinGroup (quadPlus 4 F)), E ≤ A₂ → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E ≠ 27) :
    (∃ J : Subgroup (spinGroup (quadPlus 4 F)), J ≤ A₁ ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J) ∨
      (∃ J : Subgroup (spinGroup (quadPlus 4 F)), J ≤ A₂ ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J) := by
  have := finite_spinFour (F := F)
  have hct := spinFour_ct (F := F)
  have hext := spinFour_extras (F := F)
  have hfacts := rankOne_spin_facts hF
  have hL := twoLevi_spinPlus hF three_le_four hct hext
  set D := plusDatum 4 F three_le_four with hD
  have hlevi : ∀ x : Fin 4, x ≠ 1 →
      ⁅rankOne D.rootGroup (1 : Fin 4) ⊔ rankOne D.rootGroup x,
        rankOne D.rootGroup (1 : Fin 4) ⊔ rankOne D.rootGroup x⁆ =
          rankOne D.rootGroup (1 : Fin 4) ⊔ rankOne D.rootGroup x ∧
      3 ∣ Nat.card (rankOne D.rootGroup (1 : Fin 4) ⊔ rankOne D.rootGroup x : Subgroup _) := by
    intro x hx
    have hA : cartanD 4 1 x ≠ 0 := by
      fin_cases x <;> simp_all [cartanD]
    refine ⟨(hL.pair (1 : Fin 4) x (Ne.symm hx) hA
      (commutator_ne_self_of_card_six (hfacts 1).1)
      (commutator_ne_self_of_card_six (hfacts x).1)).resolve_right id, ?_⟩
    exact (show 3 ∣ Nat.card (rankOne D.rootGroup (1 : Fin 4)) by
      rw [(hfacts 1).1]; norm_num).trans (Subgroup.card_dvd_of_le le_sup_left)
  have hcomm : ∀ x y : Fin 4, x ≠ y → x ≠ 1 → y ≠ 1 →
      ∀ a ∈ rankOne D.rootGroup x, ∀ b ∈ rankOne D.rootGroup y, a * b = b * a :=
    fun x y hxy hx hy => commutes_rankOne_of_cartan_eq_zero hext hxy
      (cartanD_four_leaves hxy hx hy)
  obtain ⟨c₀, hc₀, hc₀1, hc₀3⟩ := (hfacts 0).2.2
  obtain ⟨c₂, hc₂, hc₂1, hc₂3⟩ := (hfacts 2).2.2
  obtain ⟨c₃, hc₃, hc₃1, hc₃3⟩ := (hfacts 3).2.2
  obtain ⟨E, hE, hEel, hE27⟩ := exists_elemAbelian_card_27 (hfacts 0).1 (hfacts 3).1
    (hfacts 0).2.1 (hfacts 3).2.1 (hcomm 0 2 (by decide) (by decide) (by decide))
    (hcomm 0 3 (by decide) (by decide) (by decide)) (hcomm 2 3 (by decide) (by decide) (by decide))
    hc₀ hc₂ hc₃ hc₀1 hc₂1 hc₃1 hc₀3 hc₂3 hc₃3
  have hleaves : ∀ A : Subgroup (spinGroup (quadPlus 4 F)),
      (∀ E : Subgroup (spinGroup (quadPlus 4 F)), E ≤ A → CFSG.Open.IsElemAbelian 3 E →
        Nat.card E ≠ 27) →
      rankOne D.rootGroup (0 : Fin 4) ≤ A → rankOne D.rootGroup (2 : Fin 4) ≤ A →
      rankOne D.rootGroup (3 : Fin 4) ≤ A → False :=
    fun A h27 h0 h2 h3 => h27 E (hE.trans (sup_le (sup_le h0 h2) h3)) hEel hE27
  rcases hcov 1 with h1 | h1
  · by_cases hx : ∃ x : Fin 4, x ≠ 1 ∧ rankOne D.rootGroup x ≤ A₁
    · obtain ⟨x, hx1, hxA⟩ := hx
      exact Or.inl ⟨_, sup_le h1 hxA, (hlevi x hx1).1, (hlevi x hx1).2⟩
    · push Not at hx
      exact (hleaves A₂ h27₂ ((hcov 0).resolve_left (hx 0 (by decide)))
        ((hcov 2).resolve_left (hx 2 (by decide))) ((hcov 3).resolve_left (hx 3 (by decide)))).elim
  · by_cases hx : ∃ x : Fin 4, x ≠ 1 ∧ rankOne D.rootGroup x ≤ A₂
    · obtain ⟨x, hx1, hxA⟩ := hx
      exact Or.inr ⟨_, sup_le h1 hxA, (hlevi x hx1).1, (hlevi x hx1).2⟩
    · push Not at hx
      exact (hleaves A₁ h27₁ ((hcov 0).resolve_right (hx 0 (by decide)))
        ((hcov 2).resolve_right (hx 2 (by decide))) ((hcov 3).resolve_right (hx 3 (by decide)))).elim

end Spin

end CFSG.AGLEmbeddingD2.McLaughlin.Lie

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem kFactParabolicCoverOmega8_proved : KFactParabolicCoverOmega8 := by
  intro W _ _ L S₀ A₁ A₂ hΩ hS hcov hr₁ hr₂
  obtain ⟨T, hT⟩ := Lie.exists_sylow_of_isSylowTwoOf hS
  have hS₀L : S₀ ≤ L := hS.1
  obtain ⟨⟨-, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := Lie.statedClassicalModel_of_isOmegaEightPlus hΩ
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have := Lie.finite_spinFour (F := F)
  have h := borelQuotient_spinPlus Lie.three_le_four e
  obtain ⟨π', hπ', hker, hTπ⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient (plusDatum 4 F Lie.three_le_four) (weylD F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range) π' (Nat.card F - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hTπ] at hNπ
  have hinj : Function.Injective π' := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, eq_bot_iff]
    intro z hz
    have := h.ker_pow z hz
    rw [hF2] at this
    simpa using this
  set D := plusDatum 4 F Lie.three_le_four with hD
  set B := borel D (fun k => (torusD F Lie.three_le_four k).range) with hB
  set φ : ↥(spinGroup (quadPlus 4 F)) →* W := L.subtype.comp π' with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp hinj
  have hφL : ∀ k, φ k ∈ L := fun k => (π' k).2
  have hNS : L ⊓ Subgroup.normalizer (S₀ : Set W) = B.map φ := by
    rw [hφ, ← Subgroup.map_map, ← hNπ, map_normalizer_eq_inf, hT,
      Subgroup.map_subgroupOf_eq_of_le hS₀L, inf_comm]
  have hcardB : ∀ i : Fin 4,
      Nat.card (B ⊔ rankOne D.rootGroup i : Subgroup _) = 3 * Nat.card B := fun i =>
    Lie.card_borel_sup_rankOne_of Lie.spinFour_ct Lie.spinFour_extras
      (Lie.torusD_range_eq_bot hF2) Lie.posUnipotent_spinFour_isPGroup i
      (Lie.rankOne_spin_facts hF2 i).1 (Lie.rankOne_spin_facts hF2 i).2.1
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hmin : ∀ i : Fin 4, IsMinOverBorel L S₀ ((B ⊔ rankOne D.rootGroup i).map φ) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨k, -, rfl⟩
      exact hφL k
    · rw [hNS]
      refine lt_of_le_of_ne (Subgroup.map_mono le_sup_left) fun heq => ?_
      have := congrArg (fun A : Subgroup W => Nat.card A) heq
      simp only [Subgroup.card_map_of_injective hφinj, hcardB i] at this
      omega
    · intro Q hQ1 hQ2
      rw [hNS] at hQ1 ⊢
      have hQr : Q ≤ φ.range := hQ2.trans (Subgroup.map_le_range _ _)
      have hQeq : (Q.comap φ).map φ = Q := Subgroup.map_comap_eq_self hQr
      have hBQ : B ≤ Q.comap φ := Subgroup.map_le_iff_le_comap.mp hQ1
      have hQP : Q.comap φ ≤ B ⊔ rankOne D.rootGroup i := by
        have := Subgroup.comap_mono (f := φ) hQ2
        rwa [Subgroup.comap_map_eq_self_of_injective hφinj] at this
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBQ
      have hd2 : Nat.card (Q.comap φ) ∣ 3 * Nat.card B := by
        rw [← hcardB i]
        exact Subgroup.card_dvd_of_le hQP
      rw [hm, mul_comm 3] at hd2
      have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos hd2
      rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
      · left
        rw [mul_one] at hm
        have heqB := Subgroup.eq_of_le_of_card_ge hBQ hm.le
        rw [← hQeq, ← heqB]
      · right
        have heqP := Subgroup.eq_of_le_of_card_ge hQP
          (le_of_eq (by rw [hcardB i, hm, mul_comm]))
        rw [← hQeq, heqP]
  have hpel : ∀ i : Fin 4, (rankOne D.rootGroup i).map φ ≤
      pElementSubgroup 2 ((B ⊔ rankOne D.rootGroup i).map φ) := by
    intro i
    have hγ : ∀ γ : Fin 4 → ℤ, γ ∈ D.roots → D.rootGroup γ ≤ rankOne D.rootGroup i →
        (D.rootGroup γ).map φ ≤ pElementSubgroup 2 ((B ⊔ rankOne D.rootGroup i).map φ) := by
      rintro γ hγr hγL _ ⟨x, hx, rfl⟩
      refine Subgroup.subset_closure ⟨⟨x, Subgroup.mem_sup_right (hγL hx), rfl⟩, ?_⟩
      obtain ⟨k, hk⟩ := Lie.rootGroup_spinFour_isPGroup hγr ⟨x, hx⟩
      have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [orderOf_injective φ hφinj x]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2)
      exact ⟨j, hj⟩
    have hα : (Pi.single i 1 : Fin 4 → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
    have hα' : (-Pi.single i 1 : Fin 4 → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
    show (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map φ ≤ _
    rw [Subgroup.map_sup]
    exact sup_le (hγ _ hα le_sup_left) (hγ _ hα' le_sup_right)
  have hcovK : ∀ i : Fin 4,
      rankOne D.rootGroup i ≤ A₁.comap φ ∨ rankOne D.rootGroup i ≤ A₂.comap φ := fun i =>
    (hcov _ (hmin i)).imp (fun h1 => Subgroup.map_le_iff_le_comap.mp ((hpel i).trans h1))
      (fun h2 => Subgroup.map_le_iff_le_comap.mp ((hpel i).trans h2))
  have h27 : ∀ A : Subgroup W, Open.pRank 3 A ≤ 2 →
      ∀ E : Subgroup ↥(spinGroup (quadPlus 4 F)), E ≤ A.comap φ → IsElemAbelian 3 E →
        Nat.card E ≠ 27 := by
    intro A hr E hEA hEel hE27
    have hEA' : E.map φ ≤ A := Subgroup.map_le_iff_le_comap.mpr hEA
    have hel := elementary_map_injective 3 E φ hφinj hEel
    have hc : Nat.card (E.map φ) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective hφinj, hE27]
      norm_num
    have := CFSG.SectionRank.le_pRank (by norm_num) hEA' hel hc
    omega
  rcases Lie.spin_cover_core hF2 hcovK (h27 A₁ hr₁) (h27 A₂ hr₂) with
    ⟨J, hJ, hJp, hJ3⟩ | ⟨J, hJ, hJp, hJ3⟩
  · exact Or.inl ⟨J.map φ, Subgroup.map_le_iff_le_comap.mpr hJ,
      by rw [← Subgroup.map_commutator, hJp], by rwa [Subgroup.card_map_of_injective hφinj]⟩
  · exact Or.inr ⟨J.map φ, Subgroup.map_le_iff_le_comap.mpr hJ,
      by rw [← Subgroup.map_commutator, hJp], by rwa [Subgroup.card_map_of_injective hφinj]⟩

end CFSG.AGLEmbeddingD2.McLaughlin
