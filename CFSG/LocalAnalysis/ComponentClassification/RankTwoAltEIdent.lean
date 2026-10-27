module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEInd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEPerm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCarmichael

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical CFSG.Quasithin.SteinbergCB

section Letters

variable {n : ℕ}

@[expose] def betaE (n : ℕ) : Fin n ↪ Fin (n + 1) :=
  Fin.castSuccEmb.trans (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)).toEmbedding

theorem betaE_apply (i : Fin n) :
    betaE n i = Equiv.swap (0 : Fin (n + 1)) (Fin.last n) (Fin.castSucc i) := rfl

theorem betaE_apply_of_ne {i : Fin n} (hi : (i : ℕ) ≠ 0) : betaE n i = Fin.castSucc i := by
  rw [betaE_apply, swap_apply_of_ne_of_ne]
  · intro h
    apply hi
    simpa using congrArg Fin.val h
  · intro h
    have h1 := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at h1
    exact absurd h1 i.2.ne

theorem betaE_apply_zero (hn : 0 < n) : betaE n ⟨0, hn⟩ = Fin.last n := by
  rw [betaE_apply, show Fin.castSucc (⟨0, hn⟩ : Fin n) = 0 from Fin.ext (by simp),
    swap_apply_left]

theorem zero_notMem_range_betaE : (0 : Fin (n + 1)) ∉ Set.range (betaE n) := by
  rintro ⟨i, hi⟩
  rw [betaE_apply, swap_apply_eq_iff, swap_apply_left] at hi
  have h1 := congrArg Fin.val hi
  simp only [Fin.val_castSucc, Fin.val_last] at h1
  exact absurd h1 i.2.ne

theorem apply_inv_eqE {α : Type*} (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x := by simp

abbrev InQ {n : ℕ} (z : Fin (n + 1)) : Prop :=
  (z : ℕ) ≠ 1 ∧ (z : ℕ) ≠ 2 ∧ (z : ℕ) ≠ 3 ∧ (z : ℕ) ≠ n

@[expose] def castSuccS (n : ℕ) : {i : Fin n // InS i} ≃ {z : Fin (n + 1) // InQ z} where
  toFun s := ⟨Fin.castSucc s.1, by
    simp only [InQ, Fin.val_castSucc]
    exact ⟨s.2.1, s.2.2.1, s.2.2.2, s.1.2.ne⟩⟩
  invFun z := ⟨⟨z.1, by have := z.1.2; have := z.2.2.2.2; omega⟩, z.2.1, z.2.2.1, z.2.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem castSuccS_apply (s : {i : Fin n // InS i}) :
    ((castSuccS n s : {z : Fin (n + 1) // InQ z}) : Fin (n + 1)) = Fin.castSucc s.1 := rfl

@[expose] def sZero (hn : 0 < n) : {i : Fin n // InS i} := ⟨⟨0, hn⟩, by simp [InS]⟩

theorem mem_rootV_of_fix (h4 : 4 ≤ n) {σ : alternatingGroup (Fin n)}
    (hσ2 : (σ : Perm (Fin n)) * σ = 1)
    (hfix : ∀ i : Fin n, 4 ≤ (i : ℕ) → (σ : Perm (Fin n)) i = i) : σ ∈ rootV n := by
  have h1 := mem_rootAltP_of_fix h4 σ.2 hfix
  rw [rootAltP_eq h4] at h1
  obtain ⟨k, hk, hkσ⟩ := h1
  have hk2 : k * k = 1 :=
    viaEmbeddingHom_injective (fourEmb h4) (by rw [map_mul, hkσ, hσ2, map_one])
  have key : ∀ k : Perm (Fin 4), sign k = 1 → k * k = 1 → ∃ i, kOf i = k := by decide
  obtain ⟨i, rfl⟩ := key k hk hk2
  exact (mem_rootV_iff h4 σ).mpr ⟨kOf i, kOf_mem i, hkσ⟩

theorem c45_mem_altS (hn : 6 ≤ n) {o : Fin n} (ho : InS o) (ho5 : (o : ℕ) ≠ 5) :
    c45 hn o ∈ altS n := by
  rw [mem_altS_iff]
  refine ⟨fun i hi => ?_, mem_alternatingGroup.mp (c45_mem hn ho5)⟩
  have hi' : (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by
    simp only [InS, not_and_or, not_not] at hi
    exact hi
  have h4 : i ≠ l4 hn := fun h => by rw [h] at hi'; simp [l4] at hi'
  have h5 : i ≠ l5 hn := fun h => by rw [h] at hi'; simp [l5] at hi'
  have hoi : i ≠ o := fun h => by
    rw [h] at hi'
    rcases hi' with h' | h' | h'
    · exact ho.1 h'
    · exact ho.2.1 h'
    · exact ho.2.2 h'
  rw [c45, Perm.mul_apply, swap_apply_of_ne_of_ne h5 hoi, swap_apply_of_ne_of_ne h4 h5]

theorem viaEmbeddingHom_betaE_c45 (hn : 6 ≤ n) {o : Fin n} (ho : (o : ℕ) ≠ 0) :
    viaEmbeddingHom (betaE n) (c45 hn o) = viaEmbeddingHom Fin.castSuccEmb (c45 hn o) := by
  rw [c45, map_mul, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap, viaEmbeddingHom_swap,
    viaEmbeddingHom_swap, betaE_apply_of_ne (i := l4 hn) (by simp [l4]),
    betaE_apply_of_ne (i := l5 hn) (by simp [l5]), betaE_apply_of_ne ho]
  rfl

theorem sq_viaEmbeddingHom_c45_mul (hn : 6 ≤ n) :
    (viaEmbeddingHom Fin.castSuccEmb (c45 hn ⟨0, by omega⟩) *
      viaEmbeddingHom (betaE n) (c45 hn ⟨0, by omega⟩)) ^ 2 = 1 := by
  rw [c45, map_mul, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap, viaEmbeddingHom_swap,
    viaEmbeddingHom_swap, betaE_apply_of_ne (i := l4 hn) (by simp [l4]),
    betaE_apply_of_ne (i := l5 hn) (by simp [l5]), betaE_apply_zero]
  set x4 : Fin (n + 1) := Fin.castSuccEmb (l4 hn) with hx4
  set x5 : Fin (n + 1) := Fin.castSuccEmb (l5 hn) with hx5
  set x0 : Fin (n + 1) := Fin.castSuccEmb ⟨0, by omega⟩ with hx0
  have v4 : (x4 : ℕ) = 4 := rfl
  have v5 : (x5 : ℕ) = 5 := rfl
  have v0 : (x0 : ℕ) = 0 := rfl
  have vN : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
  have h40 : x4 ≠ x0 := fun h => by have := congrArg Fin.val h; omega
  have h50 : x5 ≠ x0 := fun h => by have := congrArg Fin.val h; omega
  have h45 : x4 ≠ x5 := fun h => by have := congrArg Fin.val h; omega
  have h4N : x4 ≠ Fin.last n := fun h => by have := congrArg Fin.val h; omega
  have h0N : x0 ≠ Fin.last n := fun h => by have := congrArg Fin.val h; omega
  rw [show Fin.castSucc (l4 hn) = x4 from rfl, show Fin.castSucc (l5 hn) = x5 from rfl,
    swap_mul_swap_mul_swap_mul_swap_eq h40 h50]
  exact PresentationLocal.swap_mul_swap_sq_eq_one h45 h4N h50.symm h0N

end Letters

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}

@[expose] noncomputable def altSIncl (n : ℕ) :
    alternatingGroup {i : Fin n // InS i} →* alternatingGroup (Fin n) :=
  ((Perm.ofSubtype).comp (alternatingGroup {i : Fin n // InS i}).subtype).codRestrict _ fun x => by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, mem_alternatingGroup, sign_ofSubtype]
    exact x.2

theorem altSIncl_apply (x : alternatingGroup {i : Fin n // InS i}) :
    ((altSIncl n x : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ofSubtype (x : Perm {i : Fin n // InS i}) := rfl

theorem altSIncl_injective : Function.Injective (altSIncl n) := fun _ _ h =>
  Subtype.ext (ofSubtype_injective (congrArg Subtype.val h))

namespace NormPair

variable (np : NormPair A R T g n) (hn : 8 ≤ n)

omit [Finite G] in
theorem equivA_symm_altSIncl_mem_LE (x : alternatingGroup {i : Fin n // InS i}) :
    ((np.equivA.symm (altSIncl n x) : A) : G) ∈ np.LE := by
  refine np.mem_LE_iff.mpr ⟨(np.equivA.symm _).2, ?_⟩
  rw [← np.equivA_coe, MulEquiv.apply_symm_apply, altSIncl_apply]
  exact ⟨x, x.2, rfl⟩

@[expose] noncomputable def kappaE : alternatingGroup {i : Fin n // InS i} →* np.DW hn :=
  ((A.subtype.comp np.equivA.symm.toMonoidHom).comp (altSIncl n)).codRestrict (np.DW hn)
    fun x => np.LE_le_DW hn (np.equivA_symm_altSIncl_mem_LE x)

omit [Finite G] in
theorem kappaE_coe (x : alternatingGroup {i : Fin n // InS i}) :
    ((np.kappaE hn x : np.DW hn) : G) = ((np.equivA.symm (altSIncl n x) : A) : G) := rfl

omit [Finite G] in
theorem kappaE_mem_LE (x : alternatingGroup {i : Fin n // InS i}) :
    ((np.kappaE hn x : np.DW hn) : G) ∈ np.LE :=
  np.equivA_symm_altSIncl_mem_LE x

omit [Finite G] in
theorem kappaE_mem_A (x : alternatingGroup {i : Fin n // InS i}) :
    ((np.kappaE hn x : np.DW hn) : G) ∈ A :=
  (np.equivA.symm (altSIncl n x)).2

omit [Finite G] in
theorem equivA_kappaE (x : alternatingGroup {i : Fin n // InS i}) :
    np.equivA ⟨_, np.kappaE_mem_A hn x⟩ = altSIncl n x := by
  rw [show (⟨_, np.kappaE_mem_A hn x⟩ : A) = np.equivA.symm (altSIncl n x) from Subtype.ext rfl,
    MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem kappaE_injective : Function.Injective (np.kappaE hn) := by
  intro x y h
  have h0 : ((np.kappaE hn x : np.DW hn) : G) = (np.kappaE hn y : G) := congrArg Subtype.val h
  have h1 : np.equivA.symm (altSIncl n x) = np.equivA.symm (altSIncl n y) := Subtype.ext h0
  exact altSIncl_injective (np.equivA.symm.injective h1)

omit [Finite G] in
theorem exists_kappaE_eq {a : A} (ha : (np.equivA a : Perm (Fin n)) ∈ altS n) :
    ∃ x, ((np.kappaE hn x : np.DW hn) : G) = a ∧
      ofSubtype (x : Perm {i : Fin n // InS i}) = (np.equivA a : Perm (Fin n)) := by
  obtain ⟨x, hx, hxa⟩ := ha
  refine ⟨⟨x, hx⟩, ?_, hxa⟩
  have h1 : altSIncl n ⟨x, hx⟩ = np.equivA a := Subtype.ext hxa
  rw [kappaE_coe, h1, MulEquiv.symm_apply_apply]

variable (ψD : np.DW hn ≃* alternatingGroup (Fin (n + 1)))

@[expose] noncomputable def fE : alternatingGroup {i : Fin n // InS i} →* Perm (Fin (n + 1)) :=
  (alternatingGroup (Fin (n + 1))).subtype.comp (ψD.toMonoidHom.comp (np.kappaE hn))

omit [Finite G] in
theorem fE_apply (x : alternatingGroup {i : Fin n // InS i}) :
    np.fE hn ψD x =
      ((ψD (np.kappaE hn x) : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) :=
  rfl

omit [Finite G] in
theorem fE_injective : Function.Injective (np.fE hn ψD) := fun _ _ h =>
  np.kappaE_injective hn (ψD.injective (Subtype.ext h))

variable (hc : Sec3 A R T g)
include hc

theorem exists_fixed_B : ∃ p : Fin (n + 1), ∀ y : np.DW hn, (y : G) ∈ rightConjugate A g →
    ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p := by
  have hBD := np.B_le_DW hn hc ψD
  set ρ : np.DW hn →* Perm (Fin (n + 1)) :=
    (alternatingGroup (Fin (n + 1))).subtype.comp ψD.toMonoidHom with hρdef
  have hρ : Function.Injective ρ := Subtype.val_injective.comp ψD.injective
  let e : ((rightConjugate A g).subgroupOf (np.DW hn)).map ρ ≃* alternatingGroup (Fin n) :=
    (((rightConjugate A g).subgroupOf (np.DW hn)).equivMapOfInjective ρ hρ).symm.trans
      ((subgroupOfEquivOfLe hBD).trans np.equivB)
  obtain ⟨p, hp⟩ := exists_fixed_of_mulEquiv_alternating (m := n) (by omega) e
  exact ⟨p, fun y hy => hp _ ⟨y, hy, rfl⟩⟩

theorem mem_B_of_fix {p : Fin (n + 1)} (hp : ∀ y : np.DW hn, (y : G) ∈ rightConjugate A g →
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p)
    {x : np.DW hn} (hx : ((ψD x : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p) :
    (x : G) ∈ rightConjugate A g := by
  have hBD := np.B_le_DW hn hc ψD
  set ρ : np.DW hn →* Perm (Fin (n + 1)) :=
    (alternatingGroup (Fin (n + 1))).subtype.comp ψD.toMonoidHom with hρdef
  have hρ : Function.Injective ρ := Subtype.val_injective.comp ψD.injective
  set Sp : Subgroup (np.DW hn) := (MulAction.stabilizer (Perm (Fin (n + 1))) p).comap ρ
    with hSpdef
  have hmemSp : ∀ y : np.DW hn, y ∈ Sp ↔
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p := fun y => by
    rw [hSpdef, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Perm.smul_def]
    rfl
  have hBS : (rightConjugate A g).subgroupOf (np.DW hn) ≤ Sp := fun y hy =>
    (hmemSp y).mpr (hp y hy)
  have hle : Sp.map ρ ≤ (alternatingGroup {y : Fin (n + 1) // y ≠ p}).map ofSubtype := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff]
    refine ⟨fun z hz => ?_, mem_alternatingGroup.mp (ψD y).2⟩
    push Not at hz
    rw [hz]
    exact (hmemSp y).mp hy
  have hne : Fintype.card {y : Fin (n + 1) // y ≠ p} = n := by
    rw [Fintype.card_subtype, Finset.filter_ne' Finset.univ p,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  have : Nontrivial {y : Fin (n + 1) // y ≠ p} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card Sp ≤ Nat.card ((rightConjugate A g).subgroupOf (np.DW hn)) := by
    calc Nat.card Sp = Nat.card (Sp.map ρ) := (card_map_of_injective hρ).symm
      _ ≤ Nat.card ((alternatingGroup {y : Fin (n + 1) // y ≠ p}).map ofSubtype) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card (alternatingGroup {y : Fin (n + 1) // y ≠ p}) :=
          SymmetricLocal.card_map_ofSubtype_alternatingGroup
      _ = n.factorial / 2 := by rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hne]
      _ = Nat.card ((rightConjugate A g).subgroupOf (np.DW hn)) := by
          rw [Nat.card_congr (subgroupOfEquivOfLe hBD).toEquiv, Nat.card_congr np.equivB.toEquiv,
            nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have heq := Subgroup.eq_of_le_of_card_ge hBS hcard
  have hxS : x ∈ Sp := (hmemSp x).mpr hx
  rw [← heq] at hxS
  exact hxS

theorem commute_fE_of_mem_R {y : np.DW hn} (hy : (y : G) ∈ R)
    (x : alternatingGroup {i : Fin n // InS i}) :
    np.fE hn ψD x * ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) * np.fE hn ψD x := by
  have hrL : (y : G) ∈ centralizer (np.LE : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (np.R_le_X hn hc hy)).1).2
  have hcomm : ((np.kappaE hn x : np.DW hn) : G) * y = y * (np.kappaE hn x : G) :=
    mem_centralizer_iff.mp hrL _ (np.kappaE_mem_LE hn x)
  have h1 : np.kappaE hn x * y = y * np.kappaE hn x := Subtype.ext hcomm
  have h2 := congrArg (fun z => ((ψD z : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1)))) h1
  simpa only [map_mul, Subgroup.coe_mul, np.fE_apply hn ψD] using h2

theorem fix_of_mem_R {y : np.DW hn} (hy : (y : G) ∈ R) {z : Fin (n + 1)}
    (hz : z ∈ movedSet (np.fE hn ψD)) :
    ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) z = z := by
  have hS : Fintype.card {i : Fin n // InS i} = n - 3 := card_S n (by omega)
  exact fix_of_commute_movedSet (np.fE_injective hn ψD) (by omega) (by omega)
    (np.commute_fE_of_mem_R hn ψD hc hy) hz

theorem exists_R_props (h32 : Lemma32) : ∃ y : np.DW hn, (y : G) ∈ R ∧
    ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) ≠ 1 ∧
    ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) *
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) = 1 ∧
    sign ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) = 1 := by
  have hRE := h32 G A hc.hyp R hc.sylowR
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.R_ne_bot
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  set y : np.DW hn := ⟨r, np.B_le_DW hn hc ψD (np.le_B hr)⟩ with hydef
  refine ⟨y, hr, fun h => hr1' ?_, ?_, mem_alternatingGroup.mp (ψD y).2⟩
  · have h1 : ψD y = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  · have h1 : y * y = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← sq]
      exact hRE.2 r hr)
    rw [← Subgroup.coe_mul, ← map_mul, h1, map_one]
    rfl

theorem card_movedSet_fE (h32 : Lemma32) :
    (movedSet (np.fE hn ψD)).card = Fintype.card {i : Fin n // InS i} := by
  obtain ⟨y, hy, h1, h2, hs⟩ := np.exists_R_props hn ψD hc h32
  have hS : Fintype.card {i : Fin n // InS i} = n - 3 := card_S n (by omega)
  exact (card_movedSet (np.fE_injective hn ψD) (by omega) (by omega) (by omega) h1 h2 hs
    (np.commute_fE_of_mem_R hn ψD hc hy)).1

theorem mem_movedSet_of_fix (h32 : Lemma32) {p : Fin (n + 1)}
    (hp : ∀ y : np.DW hn, (y : G) ∈ rightConjugate A g →
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p) :
    p ∈ movedSet (np.fE hn ψD) := by
  obtain ⟨y, hy, h1, h2, hs⟩ := np.exists_R_props hn ψD hc h32
  have hS : Fintype.card {i : Fin n // InS i} = n - 3 := card_S n (by omega)
  have hcard := np.card_movedSet_fE hn ψD hc h32
  set rD : Perm (Fin (n + 1)) := ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1)))
    with hrD
  by_contra hpM
  have hsub : rD.support ⊆ Finset.univ \ movedSet (np.fE hn ψD) := fun z hz =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hzM =>
      (mem_support.mp hz) (np.fix_of_mem_R hn ψD hc hy hzM)⟩
  have hc4 : (Finset.univ \ movedSet (np.fE hn ψD)).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hcard, hS]
    omega
  have h4 := four_le_card_support_of_mul_self_eq_one h1 h2 hs
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hpS : p ∈ rD.support := by
    rw [heq]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpM⟩
  exact (mem_support.mp hpS) (hp y (np.le_B hy))

theorem fix_zero_of_fix {p : Fin (n + 1)}
    (hp : ∀ y : np.DW hn, (y : G) ∈ rightConjugate A g →
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p)
    {x : alternatingGroup {i : Fin n // InS i}} (hx : np.fE hn ψD x p = p) :
    (x : Perm {i : Fin n // InS i}) (sZero (by omega)) = sZero (by omega) := by
  have hB : ((np.kappaE hn x : np.DW hn) : G) ∈ rightConjugate A g :=
    np.mem_B_of_fix hn ψD hc hp hx
  have h4 : 4 ≤ n := by omega
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h03 : (⟨0, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  set x₁ : Perm (Fin n) :=
    Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩
    with hx₁
  have hx₁A : x₁ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, hx₁, Perm.sign_mul, sign_swap h01, sign_swap h23]
    rfl
  have hx₁fix : ∀ i : Fin n, 4 ≤ (i : ℕ) → x₁ i = i := fun i hi => by
    have hi0 : i ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have hi1 : i ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have hi2 : i ≠ ⟨2, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have hi3 : i ≠ ⟨3, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    rw [hx₁, Perm.mul_apply, swap_apply_of_ne_of_ne hi2 hi3, swap_apply_of_ne_of_ne hi0 hi1]
  have hx₁0 : x₁ ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
    rw [hx₁, Perm.mul_apply, swap_apply_of_ne_of_ne h02 h03, swap_apply_left]
  set t : A := np.equivA.symm ⟨x₁, hx₁A⟩ with htdef
  have hψt : np.ψA ⟨(t : G), le_normalizer t.2⟩ = x₁ := by
    rw [← np.equivA_coe, htdef, MulEquiv.apply_symm_apply]
  have htB : (t : G) ∈ centralizer (rightConjugate A g : Set G) :=
    np.YT_le hc (by omega) (y := ⟨t, le_normalizer t.2⟩) t.2
      (by rw [hψt]; exact mem_rootAltP_of_fix h4 hx₁A hx₁fix)
  have hcomm : ((np.kappaE hn x : np.DW hn) : G) * t = t * (np.kappaE hn x : G) :=
    mem_centralizer_iff.mp htB _ hB
  have hcomm' : np.equivA ⟨_, np.kappaE_mem_A hn x⟩ * np.equivA t =
      np.equivA t * np.equivA ⟨_, np.kappaE_mem_A hn x⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  rw [np.equivA_kappaE hn x, htdef, MulEquiv.apply_symm_apply] at hcomm'
  have h := congrArg (fun y : alternatingGroup (Fin n) => (y : Perm (Fin n)) ⟨0, by omega⟩)
    hcomm'
  simp only [Subgroup.coe_mul, Perm.mul_apply, altSIncl_apply] at h
  have hfix1 : ofSubtype (x : Perm {i : Fin n // InS i}) ⟨1, by omega⟩ = ⟨1, by omega⟩ :=
    ofSubtype_apply_of_not_mem _ (by simp [InS])
  rw [hx₁0, hfix1] at h
  have h2 : ofSubtype (x : Perm {i : Fin n // InS i}) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    apply x₁.injective
    rw [← h, hx₁0]
  apply Subtype.ext
  rw [← ofSubtype_apply_coe]
  exact h2

theorem exists_tau (h32 : Lemma32) {p : Fin (n + 1)}
    (hp : ∀ y : np.DW hn, (y : G) ∈ rightConjugate A g →
      ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p) :
    ∃ τ : {i : Fin n // InS i} ≃ {y // y ∈ movedSet (np.fE hn ψD)},
      (∀ x, np.fE hn ψD x = ofSubtype (τ.permCongr (x : Perm {i : Fin n // InS i}))) ∧
        ((τ (sZero (by omega)) : {y // y ∈ movedSet (np.fE hn ψD)}) : Fin (n + 1)) = p := by
  have hS : Fintype.card {i : Fin n // InS i} = n - 3 := card_S n (by omega)
  have hcard := np.card_movedSet_fE hn ψD hc h32
  have hpM := np.mem_movedSet_of_fix hn ψD hc h32 hp
  have hfix0 : ∀ {x : alternatingGroup {i : Fin n // InS i}}, np.fE hn ψD x p = p →
      (x : Perm {i : Fin n // InS i}) (sZero (by omega)) = sZero (by omega) := fun hx =>
    np.fix_zero_of_fix hn ψD hc hp hx
  obtain ⟨τ, hτ⟩ : ∃ τ : {i : Fin n // InS i} ≃ {y // y ∈ movedSet (np.fE hn ψD)},
      ∀ x, np.fE hn ψD x = ofSubtype (τ.permCongr (x : Perm {i : Fin n // InS i})) := by
    refine exists_equiv_movedSet (np.fE_injective hn ψD) (by omega) hcard ?_
    by_cases h9 : n = 9
    ·
      right
      obtain ⟨g', hg'⟩ := exists_mulEquiv_movedSet (np.fE_injective hn ψD) (by omega) hcard
      have hcard' : 2 < ((movedSet (np.fE hn ψD)).erase p).card := by
        rw [Finset.card_erase_of_mem hpM, hcard, hS]
        omega
      obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hcard'
      have hc'3 : (Equiv.swap a b * Equiv.swap a d).IsThreeCycle :=
        isThreeCycle_swap_mul_swap_same hab had hbd
      have hc'mem : Equiv.swap a b * Equiv.swap a d ∈
          (alternatingGroup {y // y ∈ movedSet (np.fE hn ψD)}).map ofSubtype := by
        rw [SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff]
        refine ⟨fun y hy => ?_, mem_alternatingGroup.mp hc'3.mem_alternatingGroup⟩
        have hya : y ≠ a := fun h => hy (h ▸ Finset.mem_of_mem_erase ha)
        have hyb : y ≠ b := fun h => hy (h ▸ Finset.mem_of_mem_erase hb)
        have hyd : y ≠ d := fun h => hy (h ▸ Finset.mem_of_mem_erase hd)
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hya hyd, swap_apply_of_ne_of_ne hya hyb]
      obtain ⟨c'', hc''A, hc''⟩ := hc'mem
      have hfx : np.fE hn ψD (g'.symm ⟨c'', hc''A⟩) = Equiv.swap a b * Equiv.swap a d := by
        rw [← hg', MulEquiv.apply_symm_apply]
        exact hc''
      refine ⟨g'.symm ⟨c'', hc''A⟩, ?_, by rw [hfx]; exact hc'3⟩
      set x := g'.symm ⟨c'', hc''A⟩ with hxdef
      have hpa : p ≠ a := (Finset.ne_of_mem_erase ha).symm
      have hpb : p ≠ b := (Finset.ne_of_mem_erase hb).symm
      have hpd : p ≠ d := (Finset.ne_of_mem_erase hd).symm
      have hxp : np.fE hn ψD x p = p := by
        rw [hfx, Perm.mul_apply, swap_apply_of_ne_of_ne hpa hpd, swap_apply_of_ne_of_ne hpa hpb]
      have hxs := hfix0 hxp
      have hx3 : (x : Perm {i : Fin n // InS i}) ^ 3 = 1 := by
        have h1 : np.fE hn ψD (x ^ 3) = 1 := by
          rw [map_pow, hfx, ← hc'3.orderOf, pow_orderOf_eq_one]
        have h2 : x ^ 3 = 1 := np.fE_injective hn ψD (by rw [h1, map_one])
        rw [← Subgroup.coe_pow, h2]
        rfl
      have hx1 : (x : Perm {i : Fin n // InS i}) ≠ 1 := by
        intro h
        have h1 : x = 1 := Subtype.ext h
        have h2 := congrArg (np.fE hn ψD) h1
        rw [hfx, map_one] at h2
        exact hc'3.ne_one h2
      have hsupp : (x : Perm {i : Fin n // InS i}).support.card ≤ 5 := by
        have hsub : (x : Perm {i : Fin n // InS i}).support ⊆
            Finset.univ.erase (sZero (by omega)) := fun s hs =>
          Finset.mem_erase.mpr ⟨fun h => (mem_support.mp hs) (h ▸ hxs), Finset.mem_univ _⟩
        calc (x : Perm {i : Fin n // InS i}).support.card ≤
              (Finset.univ.erase (sZero (n := n) (by omega))).card := Finset.card_le_card hsub
          _ = 5 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hS]
              omega
      exact isThreeCycle_of_card_support_le_five hx3 hx1 hsupp
    · left
      omega
  refine ⟨τ, hτ, ?_⟩
  by_contra hne
  set s₀ := sZero (n := n) (by omega) with hs₀
  set s₁ := τ.symm ⟨p, hpM⟩ with hs₁
  have hτs₁ : ((τ s₁ : {y // y ∈ movedSet (np.fE hn ψD)}) : Fin (n + 1)) = p := by
    rw [hs₁, apply_symm_apply]
  have hs₀₁ : s₀ ≠ s₁ := fun h => hne (by rw [h, hτs₁])
  have hcard2 : 1 < ((Finset.univ.erase s₀).erase s₁).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hs₀₁.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hS]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard2
  have ha1 : a ≠ s₁ := Finset.ne_of_mem_erase ha
  have ha0 : a ≠ s₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha)
  have hb1 : b ≠ s₁ := Finset.ne_of_mem_erase hb
  have hb0 : b ≠ s₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb)
  have h3 : (Equiv.swap s₀ a * Equiv.swap s₀ b).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same ha0.symm hb0.symm hab
  set x : alternatingGroup {i : Fin n // InS i} :=
    ⟨Equiv.swap s₀ a * Equiv.swap s₀ b, h3.mem_alternatingGroup⟩ with hxdef
  have hxs₁ : (x : Perm {i : Fin n // InS i}) s₁ = s₁ := by
    show (Equiv.swap s₀ a * Equiv.swap s₀ b) s₁ = s₁
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hs₀₁.symm hb1.symm,
      swap_apply_of_ne_of_ne hs₀₁.symm ha1.symm]
  have hxp : np.fE hn ψD x p = p := by
    rw [hτ x, ← hτs₁, ofSubtype_apply_coe, permCongr_apply, symm_apply_apply, hxs₁]
  have hxs₀ : (x : Perm {i : Fin n // InS i}) s₀ = b := by
    show (Equiv.swap s₀ a * Equiv.swap s₀ b) s₀ = b
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hb0 hab.symm]
  have hfx : (x : Perm {i : Fin n // InS i}) s₀ = s₀ := hfix0 hxp
  rw [hxs₀] at hfx
  exact hb0 hfx

include ψD in
theorem exists_relabel (h32 : Lemma32) :
    ∃ ψD' : np.DW hn ≃* alternatingGroup (Fin (n + 1)),
      (∀ x, ((ψD' (np.kappaE hn x) : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
        viaEmbeddingHom Fin.castSuccEmb (ofSubtype (x : Perm {i : Fin n // InS i}))) ∧
      (∀ y : np.DW hn, (y : G) ∈ R → ∀ z : Fin (n + 1), InQ z →
        ((ψD' y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) z = z) ∧
      (∀ y : np.DW hn, ((ψD' y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) 0 = 0 ↔
        (y : G) ∈ rightConjugate A g) := by
  obtain ⟨p, hp⟩ := np.exists_fixed_B hn ψD hc
  obtain ⟨τ, hτ, hτ0⟩ := np.exists_tau hn ψD hc h32 hp
  set e : {y // y ∈ movedSet (np.fE hn ψD)} ≃ {z : Fin (n + 1) // InQ z} :=
    τ.symm.trans (castSuccS n) with hedef
  set σ : Perm (Fin (n + 1)) := e.extendSubtype with hσdef
  have hστ : ∀ s, σ (τ s : Fin (n + 1)) = Fin.castSucc s.1 := fun s => by
    rw [hσdef, extendSubtype_apply_of_mem e _ (τ s).2]
    rw [show (⟨(τ s : Fin (n + 1)), (τ s).2⟩ : {y // y ∈ movedSet (np.fE hn ψD)}) = τ s from rfl,
      hedef, trans_apply,
      symm_apply_apply, castSuccS_apply]
  have hσp : σ p = 0 := by
    rw [← hτ0, hστ]
    exact Fin.ext (by simp [sZero])
  have hσinvp : σ⁻¹ 0 = p := by rw [Perm.inv_eq_iff_eq, hσp]
  have hσQ : ∀ y, y ∉ movedSet (np.fE hn ψD) → ¬ InQ (σ y) := fun y hy =>
    extendSubtype_not_mem e y hy
  set ψD' := ψD.trans (conjPerm (n + 1) σ) with hψD'def
  have hψD' : ∀ y, ((ψD' y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
      σ * ψD y * σ⁻¹ := fun y => by rw [hψD'def, MulEquiv.trans_apply, conjPerm_apply]
  refine ⟨ψD', fun x => ?_, fun y hy z hz => ?_, fun y => ?_⟩
  ·
    rw [hψD', ← np.fE_apply hn ψD, hτ x]
    refine Equiv.ext fun z => ?_
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hw : σ⁻¹ z ∈ movedSet (np.fE hn ψD)
    · set s := τ.symm ⟨σ⁻¹ z, hw⟩ with hs
      have hτs : ((τ s : {y // y ∈ movedSet (np.fE hn ψD)}) : Fin (n + 1)) = σ⁻¹ z := by
        rw [hs, apply_symm_apply]
      have hz : z = Fin.castSucc s.1 := by rw [← hστ s, hτs, apply_inv_eqE]
      rw [← hτs, ofSubtype_apply_coe, permCongr_apply, symm_apply_apply, hστ, hz,
        show Fin.castSucc s.1 = Fin.castSuccEmb s.1 from rfl, viaEmbeddingHom_apply_image,
        ofSubtype_apply_coe]
      rfl
    · have hzQ : ¬ InQ z := by
        have := hσQ _ hw
        rwa [apply_inv_eqE] at this
      rw [ofSubtype_apply_of_not_mem _ hw, apply_inv_eqE]
      by_cases hzn : (z : ℕ) = n
      · rw [viaEmbeddingHom_apply_of_notMem]
        rintro ⟨i, hi⟩
        have h1 := congrArg Fin.val hi
        simp only [Fin.coe_castSuccEmb, Fin.val_castSucc] at h1
        have := i.2
        omega
      · have hzlt : (z : ℕ) < n := by have := z.2; omega
        have hiz : Fin.castSuccEmb (⟨z, hzlt⟩ : Fin n) = z := Fin.ext rfl
        have hiS : ¬ InS (⟨z, hzlt⟩ : Fin n) := fun hS => hzQ ⟨hS.1, hS.2.1, hS.2.2, hzn⟩
        rw [← hiz, viaEmbeddingHom_apply_image, ofSubtype_apply_of_not_mem _ hiS]
  ·
    rw [hψD', Perm.mul_apply, Perm.mul_apply]
    have hw : σ⁻¹ z ∈ movedSet (np.fE hn ψD) := by
      by_contra hw
      have := hσQ _ hw
      rw [apply_inv_eqE] at this
      exact this hz
    rw [np.fix_of_mem_R hn ψD hc hy hw, apply_inv_eqE]
  ·
    rw [hψD', Perm.mul_apply, Perm.mul_apply, hσinvp]
    constructor
    · intro h
      have h1 : ((ψD y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) p = p := by
        apply σ.injective
        rw [h, hσp]
      exact np.mem_B_of_fix hn ψD hc hp h1
    · intro hy
      rw [hp y hy, hσp]

omit hc in
theorem exists_psiB {ψD' : np.DW hn ≃* alternatingGroup (Fin (n + 1))}
    (h0 : ∀ y : np.DW hn, ((ψD' y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) 0 = 0 ↔
      (y : G) ∈ rightConjugate A g) :
    ∃ ψB : rightConjugate A g ≃* alternatingGroup (Fin n), ∀ (y : np.DW hn)
      (hy : (y : G) ∈ rightConjugate A g),
      ((ψD' y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
        viaEmbeddingHom (betaE n) (ψB ⟨y, hy⟩ : Perm (Fin n)) := by
  let via : alternatingGroup (Fin n) →* alternatingGroup (Fin (n + 1)) :=
    ((viaEmbeddingHom (betaE n)).comp (alternatingGroup (Fin n)).subtype).codRestrict _
      fun y => by
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, mem_alternatingGroup,
          sign_viaEmbeddingHom]
        exact y.2
  have hvia : ∀ y, ((via y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
      viaEmbeddingHom (betaE n) (y : Perm (Fin n)) := fun _ => rfl
  let Φ : alternatingGroup (Fin n) →* np.DW hn := ψD'.symm.toMonoidHom.comp via
  have hΦ : ∀ y, ψD' (Φ y) = via y := fun y => MulEquiv.apply_symm_apply ψD' (via y)
  have hΦB : ∀ y, ((Φ y : np.DW hn) : G) ∈ rightConjugate A g := fun y => by
    rw [← h0, hΦ, hvia]
    exact viaEmbeddingHom_apply_of_notMem _ _ zero_notMem_range_betaE
  let Φ' : alternatingGroup (Fin n) →* rightConjugate A g :=
    ((np.DW hn).subtype.comp Φ).codRestrict (rightConjugate A g) hΦB
  have hinj : Function.Injective Φ' := by
    intro y₁ y₂ h
    have h0 : ((Φ' y₁ : rightConjugate A g) : G) = (Φ' y₂ : rightConjugate A g) :=
      congrArg Subtype.val h
    have h1 : Φ y₁ = Φ y₂ := Subtype.ext h0
    have h2 := congrArg ψD' h1
    rw [hΦ, hΦ] at h2
    exact Subtype.ext (viaEmbeddingHom_injective (betaE n) (congrArg Subtype.val h2))
  have hbij : Function.Bijective Φ' :=
    hinj.bijective_of_nat_card_le (Nat.card_congr np.equivB.toEquiv).le
  refine ⟨(MulEquiv.ofBijective Φ' hbij).symm, fun y hy => ?_⟩
  set y' := (MulEquiv.ofBijective Φ' hbij).symm ⟨y, hy⟩ with hy'def
  have hyb : Φ' y' = ⟨y, hy⟩ := (MulEquiv.ofBijective Φ' hbij).apply_symm_apply ⟨y, hy⟩
  have hy' : y = Φ y' := Subtype.ext (congrArg Subtype.val hyb).symm
  rw [hy', hΦ, hvia]

include np ψD in
theorem exists_star_coords_of (h32 : Lemma32) :
    ∃ (ψA : A ≃* alternatingGroup (Fin n)) (ψB : rightConjugate A g ≃* alternatingGroup (Fin n)),
      (∀ a : A, ψA a ∈ rootV n → (a : G) ∈ centralizer (rightConjugate A g : Set G)) ∧
      (∀ b : rightConjugate A g, ψB b ∈ rootV n → (b : G) ∈ centralizer (A : Set G)) ∧
      (∀ (a : A) (b : rightConjugate A g),
        (ψA a : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) ⟨0, by omega⟩ →
        (ψB b : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) ⟨0, by omega⟩ →
          ((a : G) * b) ^ 2 = 1) ∧
      ∀ (a : A) (b : rightConjugate A g) (o : Fin n), 6 ≤ (o : ℕ) →
        (ψA a : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) o →
        (ψB b : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) o → (a : G) = b := by
  have hn6 : 6 ≤ n := le_trans (by norm_num) hn
  obtain ⟨ψD', hF1, hF3, hF0⟩ := np.exists_relabel hn ψD hc h32
  obtain ⟨ψB, hψB⟩ := np.exists_psiB hn hF0
  have hBD := np.B_le_DW hn hc ψD'
  have hRE := h32 G A hc.hyp R hc.sylowR
  have hA : ∀ (a : A) (ha : (np.equivA a : Perm (Fin n)) ∈ altS n), ∃ y : np.DW hn,
      (y : G) = a ∧ ((ψD' y : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
        viaEmbeddingHom Fin.castSuccEmb (np.equivA a : Perm (Fin n)) := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := np.exists_kappaE_eq hn ha
    exact ⟨np.kappaE hn x, hx, by rw [hF1 x, hxa]⟩
  refine ⟨np.equivA, ψB, fun a ha => ?_, fun b hb => ?_, fun a b ha hb => ?_,
    fun a b o ho ha hb => ?_⟩
  ·
    exact np.YT_le hc (by omega) (y := ⟨a, le_normalizer a.2⟩) a.2
      ⟨np.equivA a, rootV_le_rootAlt n ha, rfl⟩
  ·
    have hRV : ∀ (r : G) (hr : r ∈ R), ψB ⟨r, np.le_B hr⟩ ∈ rootV n := by
      intro r hr
      refine mem_rootV_of_fix (by omega) ?_ fun i hi => ?_
      · have h1 : (⟨r, np.le_B hr⟩ * ⟨r, np.le_B hr⟩ : rightConjugate A g) = 1 :=
          Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hRE.2 r hr)
        rw [← Subgroup.coe_mul, ← map_mul, h1, map_one]
        rfl
      · have hi0 : (i : ℕ) ≠ 0 := by omega
        have h1 := hψB ⟨r, hBD (np.le_B hr)⟩ (np.le_B hr)
        have h2 := congrArg (fun π : Perm (Fin (n + 1)) => π (betaE n i)) h1
        simp only at h2
        rw [viaEmbeddingHom_apply_image] at h2
        have hQ : InQ (betaE n i) := by
          rw [betaE_apply_of_ne hi0]
          simp only [InQ, Fin.val_castSucc]
          have := i.2
          exact ⟨by omega, by omega, by omega, by omega⟩
        rw [hF3 ⟨r, hBD (np.le_B hr)⟩ hr (betaE n i) hQ] at h2
        exact (betaE n).injective h2.symm
    have hle : (R.subgroupOf (rightConjugate A g)).map ψB.toMonoidHom ≤ rootV n := by
      rintro _ ⟨⟨r, hrB⟩, hr, rfl⟩
      exact hRV r hr
    have hcard : Nat.card ((R.subgroupOf (rightConjugate A g)).map ψB.toMonoidHom) =
        Nat.card (rootV n) := by
      rw [card_map_of_injective ψB.injective, Nat.card_congr (subgroupOfEquivOfLe np.le_B).toEquiv,
        np.card_R (by omega), nat_card_rootV (by omega)]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    rw [← heq] at hb
    obtain ⟨r, hr, hrb⟩ := hb
    have hrb' : r = b := ψB.injective hrb
    rw [← hrb']
    exact hc.sylowR.le hr
  ·
    have haS : (np.equivA a : Perm (Fin n)) ∈ altS n := by
      rw [ha]
      exact c45_mem_altS hn6 (by simp [InS]) (by simp)
    obtain ⟨ya, hya, hψa⟩ := hA a haS
    set yb : np.DW hn := ⟨b, hBD b.2⟩ with hybdef
    have hψb := hψB yb b.2
    rw [show (⟨(yb : G), b.2⟩ : rightConjugate A g) = b from rfl, hb] at hψb
    rw [ha] at hψa
    have hsq : (ya * yb) ^ 2 = 1 := by
      have h1 : ψD' ((ya * yb) ^ 2) = 1 := Subtype.ext (by
        rw [map_pow, map_mul, Subgroup.coe_pow, Subgroup.coe_mul, hψa, hψb]
        exact sq_viaEmbeddingHom_c45_mul hn6)
      exact (MulEquiv.map_eq_one_iff ψD').mp h1
    have h2 := congrArg Subtype.val hsq
    rw [Subgroup.coe_pow, Subgroup.coe_mul, hya] at h2
    exact h2
  ·
    have haS : (np.equivA a : Perm (Fin n)) ∈ altS n := by
      rw [ha]
      exact c45_mem_altS hn6 ⟨by omega, by omega, by omega⟩ (by omega)
    obtain ⟨ya, hya, hψa⟩ := hA a haS
    set yb : np.DW hn := ⟨b, hBD b.2⟩ with hybdef
    have hψb := hψB yb b.2
    rw [show (⟨(yb : G), b.2⟩ : rightConjugate A g) = b from rfl, hb,
      viaEmbeddingHom_betaE_c45 hn6 (o := o) (by omega)] at hψb
    rw [ha] at hψa
    have h1 : ya = yb := ψD'.injective (Subtype.ext (by rw [hψa, hψb]))
    rw [← hya, h1]

include np ψD in
theorem exists_hom_of_DW (h32 : Lemma32) :
    ∃ (ψA : A ≃* alternatingGroup (Fin n)) (ψB : rightConjugate A g ≃* alternatingGroup (Fin n))
      (Φ : alternatingGroup (Fin (n + 4)) →* G), Function.Injective Φ ∧
        Φ.range = A ⊔ rightConjugate A g ∧
        (∀ z, Φ (liftA (le_trans (by norm_num) hn) z) = ((ψA.symm z : A) : G)) ∧
        ∀ z, Φ (liftB (le_trans (by norm_num) hn) z) =
          ((ψB.symm z : rightConjugate A g) : G) := by
  obtain ⟨ψA, ψB, hT, hR, hstar, hU⟩ := np.exists_star_coords_of hn ψD hc h32
  exact ⟨ψA, ψB, exists_hom_of_star (le_trans (by norm_num) hn) ψA ψB hT hR hstar hU⟩

end NormPair

namespace NormPair

variable (np : NormPair A R T g n) (hn : 9 ≤ n) (hc : Sec3 A R T g)
include hc

include np in
theorem exists_star_coords
    (hK : Assembly.KProper Blueprint.Catalog G) (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h34 : Asc08Lemma34) (IH : AltStandardAt (n - 3)) :
    ∃ (ψA : A ≃* alternatingGroup (Fin n)) (ψB : rightConjugate A g ≃* alternatingGroup (Fin n)),
      (∀ a : A, ψA a ∈ rootV n → (a : G) ∈ centralizer (rightConjugate A g : Set G)) ∧
      (∀ b : rightConjugate A g, ψB b ∈ rootV n → (b : G) ∈ centralizer (A : Set G)) ∧
      (∀ (a : A) (b : rightConjugate A g),
        (ψA a : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) ⟨0, by omega⟩ →
        (ψB b : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) ⟨0, by omega⟩ →
          ((a : G) * b) ^ 2 = 1) ∧
      ∀ (a : A) (b : rightConjugate A g) (o : Fin n), 6 ≤ (o : ℕ) →
        (ψA a : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) o →
        (ψB b : Perm (Fin n)) = c45 (le_trans (by norm_num) hn) o → (a : G) = b := by
  obtain ⟨ψD⟩ := np.nonempty_DW_equiv (by omega) hc hn hK h4 h32 h34 IH
  exact np.exists_star_coords_of (by omega) ψD hc h32

include np in
theorem exists_hom_ge_nine
    (hK : Assembly.KProper Blueprint.Catalog G) (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h34 : Asc08Lemma34) (IH : AltStandardAt (n - 3)) :
    ∃ (ψA : A ≃* alternatingGroup (Fin n)) (ψB : rightConjugate A g ≃* alternatingGroup (Fin n))
      (Φ : alternatingGroup (Fin (n + 4)) →* G), Function.Injective Φ ∧
        Φ.range = A ⊔ rightConjugate A g ∧
        (∀ z, Φ (liftA (le_trans (by norm_num) hn) z) = ((ψA.symm z : A) : G)) ∧
        ∀ z, Φ (liftB (le_trans (by norm_num) hn) z) =
          ((ψB.symm z : rightConjugate A g) : G) := by
  obtain ⟨ψD⟩ := np.nonempty_DW_equiv (by omega) hc hn hK h4 h32 h34 IH
  exact np.exists_hom_of_DW (by omega) ψD hc h32

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
