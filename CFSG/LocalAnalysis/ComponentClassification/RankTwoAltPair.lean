module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltC5

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

structure AltPair {G : Type} [Group G] [Finite G] (n : ℕ) (A B : Subgroup G) : Prop where
  exists_coords : ∃ (ψA : A ≃* alternatingGroup (Fin n)) (ψB : B ≃* alternatingGroup (Fin n)),
    IsSylowOf 2 (((rootV n).map ψA.symm.toMonoidHom).map A.subtype)
        (Subgroup.centralizer (B : Set G)) ∧
      IsSylowOf 2 (((rootV n).map ψB.symm.toMonoidHom).map B.subtype)
        (Subgroup.centralizer (A : Set G)) ∧
      ((rootAlt n).map ψA.symm.toMonoidHom).map A.subtype ≤ Subgroup.centralizer (B : Set G) ∧
      ((rootAlt n).map ψB.symm.toMonoidHom).map B.subtype ≤ Subgroup.centralizer (A : Set G) ∧
      (∀ x : A, (∀ i : Fin n, (i : ℕ) < 4 → ((ψA x : Perm (Fin n)) i : ℕ) < 4) →
        ∀ b : B, ∃ hb : (x : G) * b * (x : G)⁻¹ ∈ B,
          (ψB ⟨_, hb⟩ : Perm (Fin n)) =
            restrictO (ψA x : Perm (Fin n)) * ψB b * (restrictO (ψA x : Perm (Fin n)))⁻¹) ∧
      (∀ y : B, (∀ i : Fin n, (i : ℕ) < 4 → ((ψB y : Perm (Fin n)) i : ℕ) < 4) →
        ∃ τ : Perm (Fin n), (∀ i : Fin n, (i : ℕ) < 4 → τ i = i) ∧
          ∀ a : A, ∃ ha : (y : G) * a * (y : G)⁻¹ ∈ A,
            (ψA ⟨_, ha⟩ : Perm (Fin n)) = τ * ψA a * τ⁻¹) ∧
      (∃ β' : Perm (Fin n), (∀ i : Fin n, (i : ℕ) < 4 → β' i = i) ∧
        ∀ y : B, (∀ i : Fin n, (i : ℕ) < 4 → ((ψB y : Perm (Fin n)) i : ℕ) < 4) →
          ∀ a : A, ∃ ha : (y : G) * a * (y : G)⁻¹ ∈ A,
            (ψA ⟨_, ha⟩ : Perm (Fin n)) =
              (β' * restrictO (ψB y : Perm (Fin n)) * β'⁻¹) * ψA a *
                (β' * restrictO (ψB y : Perm (Fin n)) * β'⁻¹)⁻¹) ∧
      (∀ k ∈ Subgroup.centralizer (A : Set G), k ∈ normalizer (B : Set G) ∧
        ∃ π : Perm (Fin n), (∀ i : Fin n, 4 ≤ (i : ℕ) → π i = i) ∧
          ∀ b : B, ∃ hb : k * b * k⁻¹ ∈ B, (ψB ⟨_, hb⟩ : Perm (Fin n)) = π * ψB b * π⁻¹) ∧
      (∀ k ∈ Subgroup.centralizer (B : Set G), k ∈ normalizer (A : Set G) ∧
        ∃ π : Perm (Fin n), (∀ i : Fin n, 4 ≤ (i : ℕ) → π i = i) ∧
          ∀ a : A, ∃ ha : k * a * k⁻¹ ∈ A, (ψA ⟨_, ha⟩ : Perm (Fin n)) = π * ψA a * π⁻¹)
  odd_inf : Odd (Nat.card (Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) :
    Subgroup G))
  normalizer_le : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
    normalizer ((Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) :
      Subgroup G) : Set G)
  centralizer_le_A : ∀ t ∈ Subgroup.centralizer (A : Set G), t * t = 1 → t ≠ 1 →
    Subgroup.centralizer ({t} : Set G) ≤ normalizer (A : Set G)
  centralizer_le_B : ∀ t ∈ Subgroup.centralizer (B : Set G), t * t = 1 → t ≠ 1 →
    Subgroup.centralizer ({t} : Set G) ≤ normalizer (B : Set G)

theorem odd_card_commutator_outer_of_mulEquiv {L : Type*} [Group L] {n : ℕ} (hn : 7 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) :
    Odd (Nat.card (commutator (outerAutomorphismGroup L))) := by
  have hcomm : IsMulCommutative (OuterAutomorphisms.Outer (alternatingGroup (Fin n))) := by
    have hdvd := CatalogueSchreierAlternating.outer_card_dvd_two_outside_six (Or.inr hn)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have : Subsingleton (OuterAutomorphisms.Outer (alternatingGroup (Fin n))) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := isCyclic_of_prime_card h2
      infer_instance
  have hL : IsMulCommutative (OuterAutomorphisms.Outer L) :=
    ⟨⟨fun a b => (OuterAutomorphisms.equivalence e).injective (by
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _)⟩⟩
  have h : commutator (OuterAutomorphisms.Outer L) = ⊥ := (commutator_eq_bot_iff _).mpr hL
  show Odd (Nat.card (commutator (OuterAutomorphisms.Outer L)))
  rw [h, Subgroup.card_bot]
  exact odd_one

variable {G : Type} [Group G] [Finite G]

namespace NormPair

variable {A R T : Subgroup G} {g : G} {n : ℕ} (np : NormPair A R T g n)

@[expose] noncomputable def equivA : ↥A ≃* alternatingGroup (Fin n) :=
  MulEquiv.ofBijective (restrictA np.hψA) ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
    rw [ker_restrictA, np.center_eq_bot]), restrictA_surjective np.hψA⟩

@[expose] noncomputable def equivB : ↥(rightConjugate A g) ≃* alternatingGroup (Fin n) :=
  MulEquiv.ofBijective (restrictA np.hψB) ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
    rw [ker_restrictA, np.center_B_eq_bot]), restrictA_surjective np.hψB⟩

omit [Finite G] in
theorem equivA_coe (a : ↥A) : ((np.equivA a : alternatingGroup (Fin n)) : Perm (Fin n)) =
    np.ψA ⟨a, le_normalizer a.2⟩ :=
  rfl

omit [Finite G] in
theorem equivB_coe (b : ↥(rightConjugate A g)) :
    ((np.equivB b : alternatingGroup (Fin n)) : Perm (Fin n)) = np.ψB ⟨b, le_normalizer b.2⟩ :=
  rfl

omit [Finite G] in
theorem mem_map_equivA {P : Subgroup (alternatingGroup (Fin n))} {x : G} :
    x ∈ (P.map np.equivA.symm.toMonoidHom).map A.subtype ↔
      ∃ hx : x ∈ A, np.ψA ⟨x, le_normalizer hx⟩ ∈ P.map (alternatingGroup (Fin n)).subtype := by
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨(np.equivA.symm v).2, v, hv, ?_⟩
    exact (congrArg Subtype.val (np.equivA.apply_symm_apply v)).symm.trans
      (np.equivA_coe (np.equivA.symm v))
  · rintro ⟨hx, v, hv, hve⟩
    refine ⟨⟨x, hx⟩, ⟨v, hv, ?_⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [equivA_coe]
    exact hve

omit [Finite G] in
theorem mem_map_equivB {P : Subgroup (alternatingGroup (Fin n))} {x : G} :
    x ∈ (P.map np.equivB.symm.toMonoidHom).map (rightConjugate A g).subtype ↔
      ∃ hx : x ∈ rightConjugate A g,
        np.ψB ⟨x, le_normalizer hx⟩ ∈ P.map (alternatingGroup (Fin n)).subtype := by
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨(np.equivB.symm v).2, v, hv, ?_⟩
    exact (congrArg Subtype.val (np.equivB.apply_symm_apply v)).symm.trans
      (np.equivB_coe (np.equivB.symm v))
  · rintro ⟨hx, v, hv, hve⟩
    refine ⟨⟨x, hx⟩, ⟨v, hv, ?_⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [equivB_coe]
    exact hve

omit [Finite G] in
theorem map_rootV_A : ((rootV n).map np.equivA.symm.toMonoidHom).map A.subtype = T := by
  ext x
  rw [np.mem_map_equivA]
  constructor
  · rintro ⟨hx, hV⟩
    obtain ⟨t, ht, hte⟩ := np.exists_T_of_mem hV
    have := np.injA (np.le_A ht) hx hte
    rw [← show (t : G) = x from congrArg Subtype.val this]
    exact ht
  · intro hx
    exact ⟨np.le_A hx, np.ψA_mem_of_T (t := ⟨x, le_normalizer (np.le_A hx)⟩) hx⟩

omit [Finite G] in
theorem map_rootV_B :
    ((rootV n).map np.equivB.symm.toMonoidHom).map (rightConjugate A g).subtype = R := by
  ext x
  rw [np.mem_map_equivB]
  constructor
  · rintro ⟨hx, hV⟩
    obtain ⟨r, hr, hre⟩ := np.exists_R_of_mem hV
    have := np.injB (np.le_B hr) hx hre
    rw [← show (r : G) = x from congrArg Subtype.val this]
    exact hr
  · intro hx
    exact ⟨np.le_B hx, np.ψB_mem_of_R (r := ⟨x, le_normalizer (np.le_B hx)⟩) hx⟩

theorem hasRestrictO_conjB (hc : Sec3 A R T g) (hn : 7 ≤ n) (h4 : 4 ≤ n) {β : Perm (Fin n)}
    (hβF : ∀ j, β (fourEmb h4 j) = fourEmb h4 j)
    (hβ : ∀ (x : normalizer (A : Set G)) (hx : (x : G) ∈ A) (hs : StabO (np.ψA x)),
      np.ψB ⟨x, np.mem_normalizer_B_of_stabO hc hn hx hs⟩ = β * restrictO (np.ψA x) * β⁻¹) :
    (np.conjB h4 β hβF).HasRestrictO hc hn := by
  intro x hx hs
  have hs' : StabO (np.ψA x) := hs
  rw [conjB_ψB, hβ x hx hs']
  show β⁻¹ * (β * restrictO (np.ψA x) * β⁻¹) * β = restrictO (np.ψA x)
  group

end NormPair

omit [Finite G] in
theorem stabO_of_lt {n : ℕ} (h4 : 4 ≤ n) {π : Perm (Fin n)}
    (hπ : ∀ i : Fin n, (i : ℕ) < 4 → ((π i : Fin n) : ℕ) < 4) : StabO π := by
  have hstab : ∀ j, π (fourEmb h4 j) ∈ Set.range (fourEmb h4) := fun j => by
    rw [mem_range_fourEmb_iff]
    exact hπ _ (by rw [fourEmb_apply]; exact j.2)
  obtain ⟨κ, hκ⟩ := exists_restrict (fourEmb h4) hstab
  intro i
  constructor
  · intro hi
    by_contra hc
    push Not at hc
    exact absurd (hπ i hc) (by omega)
  · intro hi
    by_contra hc
    push Not at hc
    obtain ⟨j, hj⟩ := (mem_range_fourEmb_iff h4).mpr hc
    have : π i = π (fourEmb h4 (κ⁻¹ j)) := by rw [hκ, perm_apply_inv, hj]
    rw [π.injective this, fourEmb_apply] at hi
    have := (κ⁻¹ j).2
    omega

section Producer

variable {A R T : Subgroup G} {g : G}

theorem altPair_of_sec3 (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (h2 : Asc76Theorem2) {n : ℕ} (hn : 7 ≤ n) (hn10 : n ≠ 10)
    (e : ↥A ≃* alternatingGroup (Fin n)) : AltPair n A (rightConjugate A g) := by
  have h4n : 4 ≤ n := by omega
  have hOut := odd_card_commutator_outer_of_mulEquiv hn e
  have hZ : center ↥A = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, alternatingGroup.center_eq_bot (by simp; omega),
      Subgroup.map_bot]
  let e' : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)
  obtain ⟨np₀⟩ := exists_normPair hc h32 h4 h34 h2 hOut hn e' hZ
  obtain ⟨np, -, h1⟩ := np₀.exists_restrictO hc hn hn10
  obtain ⟨β', hβ'F, hβ'⟩ := np.swap.exists_beta hc.swap hn h4n hn10
  set np₂ := np.swap.conjB h4n β' hβ'F with hnp₂
  have h1₂ : np₂.HasRestrictO hc.swap hn := np.swap.hasRestrictO_conjB hc.swap hn h4n hβ'F hβ'
  have hβ'inv : ∀ j, β'⁻¹ (fourEmb h4n j) = fourEmb h4n j := fun j => by
    rw [Perm.inv_eq_iff_eq, hβ'F]
  have hKt := tightlyEmbedded_centralizer_of_standard hc.hyp.standard
  have hgK : g ∉ normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hc.not_mem
  refine ⟨⟨np.equivA, np.equivB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    rw [np.map_rootV_A, centralizer_rightConjugate]
    exact hc.sylowT
  ·
    rw [np.map_rootV_B]
    exact hc.sylowR
  ·
    intro x hx
    obtain ⟨hxA, hY⟩ := (np.mem_map_equivA (P := rootAlt n)).mp hx
    exact np.YT_le hc hn (y := ⟨x, le_normalizer hxA⟩) hxA hY
  ·
    intro x hx
    obtain ⟨hxB, hY⟩ := (np.mem_map_equivB (P := rootAlt n)).mp hx
    exact np.YR_le hc hn (y := ⟨x, le_normalizer hxB⟩) hxB hY
  ·
    intro x hx b
    have hs : StabO (np.ψA ⟨x, le_normalizer x.2⟩) := stabO_of_lt h4n hx
    have hxB := np.mem_normalizer_B_of_stabO hc hn x.2 hs
    have hb : (x : G) * b * (x : G)⁻¹ ∈ rightConjugate A g := (mem_normalizer_iff.mp hxB b).mp b.2
    refine ⟨hb, ?_⟩
    rw [NormPair.equivB_coe, NormPair.equivB_coe, NormPair.equivA_coe]
    have e1 : (⟨(x : G) * b * (x : G)⁻¹, le_normalizer hb⟩ :
        normalizer (rightConjugate A g : Set G)) =
        ⟨x, hxB⟩ * ⟨b, le_normalizer b.2⟩ * ⟨x, hxB⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, h1 ⟨x, le_normalizer x.2⟩ x.2 hs]
  ·
    intro y hy
    have hs : StabO (np.ψB ⟨y, le_normalizer y.2⟩) := stabO_of_lt h4n hy
    have hyR := np.mem_normalizer_R h4n (x := ⟨y, le_normalizer y.2⟩) y.2
      (normalizesV_of_stabO h4n hs)
    have hyA : (y : G) ∈ normalizer (A : Set G) := normalizer_R_le hc hyR
    refine ⟨np.ψA ⟨y, hyA⟩, fun i hi => ?_, fun a => ?_⟩
    · have := np.ψA_apply_of_mem_B hc hn (y := ⟨y, hyA⟩) y.2 ⟨i, hi⟩
      rwa [show fourEmb (by omega : 4 ≤ n) ⟨i, hi⟩ = i from Fin.ext rfl] at this
    · have ha : (y : G) * a * (y : G)⁻¹ ∈ A := (mem_normalizer_iff.mp hyA a).mp a.2
      refine ⟨ha, ?_⟩
      rw [NormPair.equivA_coe, NormPair.equivA_coe]
      have e1 : (⟨(y : G) * a * (y : G)⁻¹, le_normalizer ha⟩ : normalizer (A : Set G)) =
          ⟨y, hyA⟩ * ⟨a, le_normalizer a.2⟩ * ⟨y, hyA⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
  ·
    refine ⟨β', fun i hi => ?_, fun y hy a => ?_⟩
    · have := hβ'F ⟨i, hi⟩
      rwa [show fourEmb h4n ⟨i, hi⟩ = i from Fin.ext rfl] at this
    ·
      have hxA' : g * (y : G) * g⁻¹ ∈ A := (mem_rightConjugate_iff A g y).mp y.2
      obtain ⟨x, hxdef⟩ : ∃ x : normalizer (A : Set G), (x : G) = g * (y : G) * g⁻¹ :=
        ⟨⟨_, le_normalizer hxA'⟩, rfl⟩
      have hxA : (x : G) ∈ A := by rw [hxdef]; exact hxA'
      have hψx : np.swap.ψA x = np.ψB ⟨y, le_normalizer y.2⟩ := by
        rw [NormPair.swap_ψA]
        congr 1
        apply Subtype.ext
        rw [conjNInv_coe, hxdef]
        group
      have hs : StabO (np.swap.ψA x) := by rw [hψx]; exact stabO_of_lt h4n hy
      have hxB := np.swap.mem_normalizer_B_of_stabO hc.swap hn hxA hs
      have hyA : (y : G) ∈ normalizer (A : Set G) := by
        have h := (mem_normalizer_rightConjugate_iff A g⁻¹ _).mp hxB
        rw [hxdef] at h
        simpa [mul_assoc] using h
      have ha : (y : G) * a * (y : G)⁻¹ ∈ A := (mem_normalizer_iff.mp hyA a).mp a.2
      refine ⟨ha, ?_⟩
      have haB : g * (a : G) * g⁻¹ ∈ rightConjugate A g⁻¹ := by
        rw [mem_rightConjugate_iff]
        simp [mul_assoc]
      have key := hβ' x hxA hs
      have e2 : ∀ z : G, ∀ hz : g * z * g⁻¹ ∈ normalizer (rightConjugate A g⁻¹ : Set G),
          ∀ hz' : z ∈ normalizer (A : Set G),
          np.swap.ψB ⟨g * z * g⁻¹, hz⟩ = np.ψA ⟨z, hz'⟩ := by
        intro z hz hz'
        rw [NormPair.swap_ψB]
        congr 1
        apply Subtype.ext
        rw [conjN_coe]
        group
      have hyaB : g * ((y : G) * a * (y : G)⁻¹) * g⁻¹ ∈ rightConjugate A g⁻¹ := by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using ha
      have hconj : (⟨g * ((y : G) * a * (y : G)⁻¹) * g⁻¹, le_normalizer hyaB⟩ :
          normalizer (rightConjugate A g⁻¹ : Set G)) =
          ⟨x, hxB⟩ * ⟨g * (a : G) * g⁻¹, le_normalizer haB⟩ * ⟨x, hxB⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxdef]
        group
      rw [NormPair.equivA_coe, NormPair.equivA_coe, ← e2 _ (le_normalizer hyaB) (le_normalizer ha),
        hconj, map_mul,
        map_mul, map_inv, key, e2 _ _ (le_normalizer a.2), hψx, NormPair.equivB_coe]
  ·
    intro k hk
    have hkB := NormPair.centralizer_le_normalizer_B hc np.le_A hk
    refine ⟨hkB, np.ψB ⟨k, hkB⟩, fun i hi => np.ψB_fix_of_mem_K hc hn h1 hk hi, fun b => ?_⟩
    have hb : k * b * k⁻¹ ∈ rightConjugate A g := (mem_normalizer_iff.mp hkB b).mp b.2
    refine ⟨hb, ?_⟩
    rw [NormPair.equivB_coe, NormPair.equivB_coe]
    have e1 : (⟨k * b * k⁻¹, le_normalizer hb⟩ : normalizer (rightConjugate A g : Set G)) =
        ⟨k, hkB⟩ * ⟨b, le_normalizer b.2⟩ * ⟨k, hkB⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
  ·
    intro k hk
    have hk' : g * k * g⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      rw [centralizer_rightConjugate, mem_rightConjugate_iff] at hk
      exact hk
    have hk'B := NormPair.centralizer_le_normalizer_B hc.swap np₂.le_A hk'
    have hkA : k ∈ normalizer (A : Set G) := by
      have h := (mem_normalizer_rightConjugate_iff A g⁻¹ _).mp hk'B
      simpa [mul_assoc] using h
    have hfix : ∀ i : Fin n, 4 ≤ (i : ℕ) → np₂.ψB ⟨g * k * g⁻¹, hk'B⟩ i = i := fun i hi =>
      np₂.ψB_fix_of_mem_K hc.swap hn h1₂ hk' hi
    have hψk : np.ψA ⟨k, hkA⟩ = β' * np₂.ψB ⟨g * k * g⁻¹, hk'B⟩ * β'⁻¹ := by
      rw [hnp₂, NormPair.conjB_ψB, NormPair.swap_ψB]
      have : conjN A g⁻¹ ⟨g * k * g⁻¹, hk'B⟩ = ⟨k, hkA⟩ := by
        apply Subtype.ext
        rw [conjN_coe]
        group
      rw [this]
      group
    refine ⟨hkA, np.ψA ⟨k, hkA⟩, fun i hi => ?_, fun a => ?_⟩
    · have hβi : 4 ≤ ((β'⁻¹ i : Fin n) : ℕ) := (stabO_inv (stabO_of_fix h4n hβ'F) i).mpr hi
      rw [hψk, Perm.mul_apply, Perm.mul_apply, hfix _ hβi, perm_apply_inv]
    · have ha : k * a * k⁻¹ ∈ A := (mem_normalizer_iff.mp hkA a).mp a.2
      refine ⟨ha, ?_⟩
      rw [NormPair.equivA_coe, NormPair.equivA_coe]
      have e1 : (⟨k * a * k⁻¹, le_normalizer ha⟩ : normalizer (A : Set G)) =
          ⟨k, hkA⟩ * ⟨a, le_normalizer a.2⟩ * ⟨k, hkA⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
  ·
    have h := hKt.2 g hgK
    rwa [← centralizer_rightConjugate] at h
  ·
    refine sup_le (np.normalizer_le_inf hc hn h1) ?_
    intro y hy
    have hyA : g * y * g⁻¹ ∈ normalizer (A : Set G) :=
      (mem_normalizer_rightConjugate_iff A g y).mp hy
    have h := np₂.normalizer_le_inf hc.swap hn h1₂ hyA
    have hQ : rightConjugate (Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (rightConjugate A g⁻¹ : Set G)) g =
        Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (rightConjugate A g : Set G) := by
      ext z
      rw [mem_rightConjugate_iff, Subgroup.mem_inf, Subgroup.mem_inf,
        centralizer_rightConjugate A g⁻¹, mem_rightConjugate_iff, centralizer_rightConjugate A g,
        mem_rightConjugate_iff (Subgroup.centralizer (A : Set G)) g z]
      have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
      rw [e]
      exact and_comm
    rw [← hQ, mem_normalizer_rightConjugate_iff]
    exact h
  ·
    intro t ht ht2 ht1
    have h := Lemma39.centralizer_le_normalizer_rightConjugate hc.hyp 1 (t := t)
      (by rw [rightConjugate_one]; exact ht) ht1 (by rw [sq]; exact ht2)
    rwa [rightConjugate_one] at h
  ·
    intro t ht ht2 ht1
    rw [centralizer_rightConjugate] at ht
    exact Lemma39.centralizer_le_normalizer_rightConjugate hc.hyp g ht ht1 (by rw [sq]; exact ht2)

end Producer

end CFSG.ComponentClassification.RankTwoAlt
