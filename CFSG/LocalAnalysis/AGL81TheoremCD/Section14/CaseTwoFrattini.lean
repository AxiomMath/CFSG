module

public import CFSG.Open.LocalVocabulary

import CFSG.RankThree.Asc83Table.E9
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.Quasithin.Background.B682Ambient
import CFSG.GH74.GLS.C3.Layer3.A8Cover

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

@[expose] def KFactA9NotInvolvedGL4 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
  ∀ (V : Type) [Group V] [Finite V], IsMulCommutative V → (∀ v : V, v ^ p = 1) →
    Nat.card V ≤ p ^ 4 →
  ∀ (n : ℕ), 9 ≤ n →
  ∀ (Y : Type) [Group Y] [Finite Y] (ρ : Y →* MulAut V) (φ : Y →* alternatingGroup (Fin n)),
    Function.Surjective φ → ¬ ρ.ker ≤ φ.ker

private theorem centralizer_singleton_le_of_mem_zpowers {X : Type*} [Group X] {u v : X}
    (hv : v ∈ Subgroup.zpowers u) :
    Subgroup.centralizer ({u} : Set X) ≤ Subgroup.centralizer ({v} : Set X) := by
  rw [← Subgroup.centralizer_closure ({u} : Set X),
    ← Subgroup.centralizer_closure ({v} : Set X),
    ← Subgroup.zpowers_eq_closure u, ← Subgroup.zpowers_eq_closure v]
  exact Subgroup.centralizer_le (fun x hx => Subgroup.zpowers_le.mpr hv hx)

private theorem exists_rep_of_mem_closure_pair {X : Type*} [Group X]
    {u₁ u₂ u : X} (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hu : Commute u₁ u₂)
    (hu₁1 : u₁ ≠ 1) (hu₂z : u₂ ∉ Subgroup.zpowers u₁)
    (humem : u ∈ Subgroup.closure ({u₁, u₂} : Set X)) (hu1 : u ≠ 1) :
    ∃ v : X, (v = u₁ ∨ v = u₂ ∨ v = u₁ * u₂ ∨ v = u₁ * u₂ ^ 2) ∧
      v ∈ Subgroup.zpowers u := by
  classical
  let E : CFSG.RankThree.Asc83Table.E9Basis X :=
    { a := u₁, b := u₂, ha := hu₁, hb := hu₂, hab := hu, card :=
        CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hu₁ hu₂ hu hu₁1 hu₂z }
  obtain ⟨i, j, hi, hj, hform⟩ := E.exists_pow_mul_pow humem
  simp only [E] at hform
  have hc3 : (u₁ * u₂) ^ 3 = 1 := by
    rw [hu.mul_pow, hu₁, hu₂, mul_one]
  have hd3 : (u₁ * u₂ ^ 2) ^ 3 = 1 := by
    have hc : Commute u₁ (u₂ ^ 2) := by simpa using hu.pow_pow 1 2
    rw [hc.mul_pow, hu₁]
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hu₂, one_pow, mul_one]
  have h4 : (u₂ ^ 2) ^ 2 = u₂ := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hu₂, one_mul, pow_one]
  have hsq (v : X) (hv3 : v ^ 3 = 1) (huv : u = v ^ 2) :
      v ∈ Subgroup.zpowers u := by
    have hv_eq : v = u ^ 2 := by
      rw [huv]
      calc v = v ^ 3 * v := by rw [hv3, one_mul]
        _ = (v ^ 2) ^ 2 := by group
    rw [hv_eq]
    exact Subgroup.pow_mem (Subgroup.zpowers u) (Subgroup.mem_zpowers u) 2
  interval_cases i <;> interval_cases j
  · exact absurd (by simpa using hform) hu1
  · refine ⟨u₂, Or.inr (Or.inl rfl), ?_⟩
    rw [hform]
    simpa using Subgroup.mem_zpowers u₂
  · exact ⟨u₂, Or.inr (Or.inl rfl), hsq u₂ hu₂ (by simpa using hform)⟩
  · refine ⟨u₁, Or.inl rfl, ?_⟩
    rw [hform]
    simpa using Subgroup.mem_zpowers u₁
  · refine ⟨u₁ * u₂, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    rw [hform]
    simpa using Subgroup.mem_zpowers (u₁ * u₂)
  · refine ⟨u₁ * u₂ ^ 2, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    rw [hform]
    simpa using Subgroup.mem_zpowers (u₁ * u₂ ^ 2)
  · exact ⟨u₁, Or.inl rfl, hsq u₁ hu₁ (by simpa using hform)⟩
  · have huv : u = (u₁ * u₂ ^ 2) ^ 2 := by
      rw [hform]
      have hc : Commute u₁ (u₂ ^ 2) := by simpa using hu.pow_pow 1 2
      rw [hc.mul_pow, h4]
      simp
    exact ⟨u₁ * u₂ ^ 2, Or.inr (Or.inr (Or.inr rfl)),
      hsq (u₁ * u₂ ^ 2) hd3 huv⟩
  · have huv : u = (u₁ * u₂) ^ 2 := by
      rw [hform, hu.mul_pow]
    exact ⟨u₁ * u₂, Or.inr (Or.inr (Or.inl rfl)),
      hsq (u₁ * u₂) hc3 huv⟩

private theorem mul_ne_one_and_mul_sq_ne_one {X : Type*} [Group X] {u₁ u₂ : X}
    (hu₂ : u₂ ^ 3 = 1) (hu₂z : u₂ ∉ Subgroup.zpowers u₁) :
    u₁ * u₂ ≠ 1 ∧ u₁ * u₂ ^ 2 ≠ 1 := by
  constructor
  · intro h
    apply hu₂z
    have hu₂eq : u₂ = u₁⁻¹ * (u₁ * u₂) := by group
    rw [hu₂eq, h, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩
  · intro h
    apply hu₂z
    have hb2 : u₂ ^ 2 ∈ Subgroup.zpowers u₁ := by
      have hb : u₂ ^ 2 = u₁⁻¹ := by
        have h' : u₁⁻¹ * (u₁ * u₂ ^ 2) = u₁⁻¹ := by rw [h, mul_one]
        simpa using h'
      rw [hb]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩
    have hb : u₂ = (u₂ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hu₂, one_mul, pow_one]
    rw [hb]
    exact Subgroup.pow_mem _ hb2 2

private theorem le_sup_centralizers {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {P : Subgroup X} (hP : IsPGroup p ↥P)
    {u₁ u₂ : X} (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hu : Commute u₁ u₂)
    (hu₁1 : u₁ ≠ 1) (hu₂z : u₂ ∉ Subgroup.zpowers u₁)
    (hN : Subgroup.closure ({u₁, u₂} : Set X) ≤ Subgroup.normalizer (P : Set X))
    (hrank : ∀ u ∈ Subgroup.closure ({u₁, u₂} : Set X), u ≠ 1 →
      CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({u} : Set X)) ≤ 1) :
    P ≤ (P ⊓ Subgroup.centralizer ({u₁} : Set X)) ⊔
        (P ⊓ Subgroup.centralizer ({u₂} : Set X)) ⊔
        (P ⊓ Subgroup.centralizer ({u₁ * u₂} : Set X)) ⊔
        (P ⊓ Subgroup.centralizer ({u₁ * u₂ ^ 2} : Set X)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let U : Subgroup X := Subgroup.closure ({u₁, u₂} : Set X)
  let C : X → Subgroup X := fun v => P ⊓ Subgroup.centralizer ({v} : Set X)
  have hcardU : Nat.card U = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hu₁ hu₂ hu hu₁1 hu₂z
  have hU3 : IsPGroup 3 ↥U := IsPGroup.of_card (n := 2) (by rw [hcardU]; norm_num)
  have hUexp : ∀ u : ↥U, u ^ 3 = 1 := fun u => Subtype.ext
    (CFSG.GH74.GLS.Layer3.pow_three_eq_one_of_mem_closure_pair hu hu₁ hu₂ u.2)
  have hcomp : ¬ 3 ∣ Nat.card ↥P := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    have hcop : Nat.Coprime 3 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hgen : P = ⨆ (u : ↥U) (_ : u ≠ 1), C (u : X) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      3 Nat.prime_three U P hUexp (by rw [hcardU]; norm_num) hcomp hN
  have hgoal : (⨆ (u : ↥U) (_ : u ≠ 1), C (u : X)) ≤
      C u₁ ⊔ C u₂ ⊔ C (u₁ * u₂) ⊔ C (u₁ * u₂ ^ 2) := by
    refine iSup_le fun u => iSup_le fun hune => ?_
    have hune' : (u : X) ≠ 1 := fun h => hune (Subtype.ext h)
    obtain ⟨v, hv4, hvu⟩ := exists_rep_of_mem_closure_pair hu₁ hu₂ hu hu₁1 hu₂z u.2 hune'
    refine (inf_le_inf_left P (centralizer_singleton_le_of_mem_zpowers hvu)).trans ?_
    rcases hv4 with rfl | rfl | rfl | rfl
    · exact le_trans (le_trans le_sup_left le_sup_left) le_sup_left
    · exact le_trans (le_trans le_sup_right le_sup_left) le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  conv_lhs => rw [hgen]
  exact hgoal

private theorem isCyclic_frattini_image {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p ↥P) {v : X}
    (hrankv : CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({v} : Set X)) ≤ 1) :
    IsCyclic ↥(Subgroup.map (QuotientGroup.mk' (frattini ↥P))
      ((P ⊓ Subgroup.centralizer ({v} : Set X)).subgroupOf P)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Cv : Subgroup X := P ⊓ Subgroup.centralizer ({v} : Set X)
  have hCpg : IsPGroup p ↥Cv :=
    IsPGroup.of_equiv (hP.to_subgroup (Cv.subgroupOf P))
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Cv ≤ P))
  have hCcyc : IsCyclic ↥Cv :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one (p := p) hp2 (H := Cv) (P := Cv)
      le_rfl hCpg hrankv
  haveI : IsCyclic ↥(Cv.subgroupOf P) :=
    ((Subgroup.subgroupOfEquivOfLe (inf_le_left : Cv ≤ P)).isCyclic).mpr hCcyc
  let π : ↥P →* (↥P ⧸ frattini ↥P) := QuotientGroup.mk' (frattini ↥P)
  have hrange : (π.comp (Cv.subgroupOf P).subtype).range =
      Subgroup.map π (Cv.subgroupOf P) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcyc : IsCyclic ↥((π.comp (Cv.subgroupOf P).subtype).range) :=
    isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  rwa [hrange] at hcyc

private theorem exists_generators_of_cyclic_four {V : Type*} [Group V]
    (K : Fin 4 → Subgroup V) (hK : ∀ i, IsCyclic ↥(K i))
    (htop : K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 = ⊤) :
    ∃ g : Fin 4 → V, Subgroup.closure (Set.range g) = ⊤ := by
  choose g hg using fun i =>
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (K i)).mp (hK i)
  refine ⟨g, ?_⟩
  have hKi : ∀ i, K i = Subgroup.zpowers (g i) := fun i => (hg i).symm
  rw [← htop]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · exact SetLike.le_def.mp (le_trans (le_trans le_sup_left le_sup_left) le_sup_left)
        ((hKi 0).symm ▸ Subgroup.mem_zpowers (g 0))
    · exact SetLike.le_def.mp (le_trans (le_trans le_sup_right le_sup_left) le_sup_left)
        ((hKi 1).symm ▸ Subgroup.mem_zpowers (g 1))
    · exact SetLike.le_def.mp (le_trans le_sup_right le_sup_left)
        ((hKi 2).symm ▸ Subgroup.mem_zpowers (g 2))
    · exact SetLike.le_def.mp le_sup_right
        ((hKi 3).symm ▸ Subgroup.mem_zpowers (g 3))
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (hKi 0).le.trans
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨0, rfl⟩))
    · exact (hKi 1).le.trans
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨1, rfl⟩))
    · exact (hKi 2).le.trans
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨2, rfl⟩))
    · exact (hKi 3).le.trans
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨3, rfl⟩))

private theorem card_le_pow_of_cyclic_four {V : Type*} [Group V] [Finite V] {p : ℕ}
    (hp : p.Prime) (hcomm : IsMulCommutative V) (hexp : ∀ v : V, v ^ p = 1)
    (K : Fin 4 → Subgroup V) (hK : ∀ i, IsCyclic ↥(K i))
    (htop : K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 = ⊤) : Nat.card V ≤ p ^ 4 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => hcomm.is_comm.comm a b }
  haveI : CFSG.IsElementaryAbelian p V :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  obtain ⟨g, hclosure⟩ := exists_generators_of_cyclic_four K hK htop
  let v : Fin 4 → Additive V := fun i => Additive.ofMul (g i)
  have hpre : Additive.toMul ⁻¹' Set.range g = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa using congrArg Additive.ofMul hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hAdd : AddSubgroup.closure (Set.range v) = ⊤ := by
    have h := congrArg Subgroup.toAddSubgroup hclosure
    rw [Subgroup.toAddSubgroup_closure, hpre] at h
    simpa using h
  have hspan : Submodule.span (ZMod p) (Set.range v) = ⊤ := by
    have hle : AddSubgroup.closure (Set.range v) ≤
        (Submodule.span (ZMod p) (Set.range v)).toAddSubgroup :=
      (AddSubgroup.closure_le _).mpr (Submodule.subset_span (R := ZMod p) (s := Set.range v))
    rw [hAdd] at hle
    exact Submodule.toAddSubgroup_eq_top.mp (le_antisymm le_top hle)
  have hfin : Module.finrank (ZMod p) (Additive V) ≤ 4 := by
    have := finrank_le_of_span_eq_top (R := ZMod p) (v := v) hspan
    simpa using this
  haveI : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
  calc Nat.card V = Nat.card (Additive V) := rfl
    _ = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (Additive V) :=
        Module.natCard_eq_pow_finrank
    _ = p ^ Module.finrank (ZMod p) (Additive V) := by rw [Nat.card_zmod]
    _ ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos hfin

theorem card_frattini_quotient_le_pow_four {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {P : Subgroup X} (hP : IsPGroup p ↥P)
    {u₁ u₂ : X} (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hu : Commute u₁ u₂) (hu₁1 : u₁ ≠ 1)
    (hu₂z : u₂ ∉ Subgroup.zpowers u₁)
    (hN : Subgroup.closure ({u₁, u₂} : Set X) ≤ Subgroup.normalizer (P : Set X))
    (hrank : ∀ u ∈ Subgroup.closure ({u₁, u₂} : Set X), u ≠ 1 →
      CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({u} : Set X)) ≤ 1) :
    Nat.card (↥P ⧸ frattini ↥P) ≤ p ^ 4 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let U : Subgroup X := Subgroup.closure ({u₁, u₂} : Set X)
  let C : X → Subgroup X := fun v => P ⊓ Subgroup.centralizer ({v} : Set X)
  have hPM : P ≤ C u₁ ⊔ C u₂ ⊔ C (u₁ * u₂) ⊔ C (u₁ * u₂ ^ 2) :=
    le_sup_centralizers hp hp3 hP hu₁ hu₂ hu hu₁1 hu₂z hN hrank
  have hu1U : u₁ ∈ U := Subgroup.subset_closure (by simp)
  have hu2U : u₂ ∈ U := Subgroup.subset_closure (by simp)
  have hu2ne : u₂ ≠ 1 := fun h => hu₂z (h ▸ Subgroup.one_mem _)
  have hne := mul_ne_one_and_mul_sq_ne_one hu₂ hu₂z
  have hC_le : ∀ v : X, C v ≤ P := fun v => inf_le_left
  let π : ↥P →* (↥P ⧸ frattini ↥P) := QuotientGroup.mk' (frattini ↥P)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let K0 : Subgroup (↥P ⧸ frattini ↥P) := Subgroup.map π ((C u₁).subgroupOf P)
  let K1 : Subgroup (↥P ⧸ frattini ↥P) := Subgroup.map π ((C u₂).subgroupOf P)
  let K2 : Subgroup (↥P ⧸ frattini ↥P) := Subgroup.map π ((C (u₁ * u₂)).subgroupOf P)
  let K3 : Subgroup (↥P ⧸ frattini ↥P) :=
    Subgroup.map π ((C (u₁ * u₂ ^ 2)).subgroupOf P)
  let K : Fin 4 → Subgroup (↥P ⧸ frattini ↥P) :=
    Fin.cases K0 (Fin.cases K1 (Fin.cases K2 (fun _ => K3)))
  have hMsub : (C u₁ ⊔ C u₂ ⊔ C (u₁ * u₂) ⊔ C (u₁ * u₂ ^ 2)).subgroupOf P = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr hPM
  have htop : K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 = ⊤ := by
    have h := congrArg (Subgroup.map π) hMsub
    rw [Subgroup.map_top_of_surjective π hπsurj] at h
    rw [Subgroup.subgroupOf_sup
        (sup_le (sup_le (hC_le u₁) (hC_le u₂)) (hC_le (u₁ * u₂)))
        (hC_le (u₁ * u₂ ^ 2)),
      Subgroup.subgroupOf_sup (sup_le (hC_le u₁) (hC_le u₂)) (hC_le (u₁ * u₂)),
      Subgroup.subgroupOf_sup (hC_le u₁) (hC_le u₂),
      Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup] at h
    exact h
  have hVcomm : IsMulCommutative (↥P ⧸ frattini ↥P) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hP).2.1
  have hVexp : ∀ x : ↥P ⧸ frattini ↥P, x ^ p = 1 :=
    (CFSG.GroupTheory.frattini_elementary_quotient hP).2.2.1
  have hKcyc : ∀ i, IsCyclic ↥(K i) := by
    intro i
    fin_cases i
    · change IsCyclic ↥K0
      exact isCyclic_frattini_image hp hp2 hP (hrank u₁ hu1U hu₁1)
    · change IsCyclic ↥K1
      exact isCyclic_frattini_image hp hp2 hP (hrank u₂ hu2U hu2ne)
    · change IsCyclic ↥K2
      exact isCyclic_frattini_image hp hp2 hP
        (hrank (u₁ * u₂) (U.mul_mem hu1U hu2U) hne.1)
    · change IsCyclic ↥K3
      exact isCyclic_frattini_image hp hp2 hP
        (hrank (u₁ * u₂ ^ 2) (U.mul_mem hu1U (U.pow_mem hu2U 2)) hne.2)
  exact card_le_pow_of_cyclic_four hp hVcomm hVexp K hKcyc htop

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
