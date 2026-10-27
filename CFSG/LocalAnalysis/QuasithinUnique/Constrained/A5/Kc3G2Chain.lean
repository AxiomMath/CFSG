module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock

public section

namespace CFSG.QuasithinUnique.A5.Kc3G2

open CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def nKW (K W : Subgroup G) : Subgroup G := K ⊓ Subgroup.normalizer (W : Set G)

@[expose] def chainStep (K W : Subgroup G) : Subgroup G := pCoreOf 2 (nKW K W)

@[expose] noncomputable def chainIter (K W : Subgroup G) : ℕ → Subgroup G
  | 0 => W
  | n + 1 => chainStep K (chainIter K W n)

theorem le_nKW {K W : Subgroup G} (hWK : W ≤ K) : W ≤ nKW K W :=
  le_inf hWK Subgroup.le_normalizer

theorem nKW_le_left (K W : Subgroup G) : nKW K W ≤ K := inf_le_left

theorem chainStep_le (K W : Subgroup G) : chainStep K W ≤ K :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 (nKW K W)).trans (nKW_le_left K W)

theorem chainStep_isPGroup [Finite G] (K W : Subgroup G) : IsPGroup 2 (chainStep K W) :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (nKW K W)

theorem le_chainStep {K W : Subgroup G} (hWK : W ≤ K) (hW : IsPGroup 2 W) :
    W ≤ chainStep K W :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_nKW hWK) inf_le_right hW

theorem nKW_le_nKW_chainStep (K W : Subgroup G) : nKW K W ≤ nKW K (chainStep K W) :=
  le_inf inf_le_left (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (nKW K W))

theorem mem_normalizer_chainStep {K W : Subgroup G} {s : G}
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hsW : s ∈ Subgroup.normalizer (W : Set G)) :
    s ∈ Subgroup.normalizer (chainStep K W : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (nKW K W)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hsK, Subgroup.le_normalizer hsW⟩)

theorem chainIter_le [Finite G] {K W : Subgroup G} (hWK : W ≤ K) (n : ℕ) :
    chainIter K W n ≤ K := by
  induction n with
  | zero => exact hWK
  | succ n _ => exact chainStep_le K _

theorem chainIter_isPGroup [Finite G] {K W : Subgroup G} (hW : IsPGroup 2 W) (n : ℕ) :
    IsPGroup 2 (chainIter K W n) := by
  induction n with
  | zero => exact hW
  | succ n _ => exact chainStep_isPGroup K _

theorem chainIter_mono [Finite G] {K W : Subgroup G} (hWK : W ≤ K) (hW : IsPGroup 2 W) :
    Monotone (chainIter K W) :=
  monotone_nat_of_le_succ fun n =>
    le_chainStep (chainIter_le hWK n) (chainIter_isPGroup hW n)

theorem nKW_le_chainIter [Finite G] {K W : Subgroup G} (n : ℕ) :
    nKW K W ≤ nKW K (chainIter K W n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (nKW_le_nKW_chainStep K _)

theorem mem_normalizer_chainIter [Finite G] {K W : Subgroup G} {s : G}
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (n : ℕ) : s ∈ Subgroup.normalizer (chainIter K W n : Set G) := by
  induction n with
  | zero => exact hsW
  | succ n ih => exact mem_normalizer_chainStep hsK ih

theorem exists_stable [Finite G] {K W : Subgroup G} (hWK : W ≤ K) (hW : IsPGroup 2 W) :
    ∃ n : ℕ, chainStep K (chainIter K W n) = chainIter K W n := by
  obtain ⟨n, hn⟩ := (wellFoundedGT_iff_monotone_chain_condition.1 inferInstance)
    ⟨chainIter K W, chainIter_mono hWK hW⟩
  exact ⟨n, (hn (n + 1) (Nat.le_succ n)).symm⟩

@[expose] def BT2 (K : Subgroup G) : Prop :=
  ∀ W : Subgroup G, W ≤ K → W ≠ ⊥ → IsPGroup 2 W →
    ∃ S P : Subgroup G, IsSylowTwoOf S K ∧ P ≤ K ∧ P ≠ K ∧ nKW K W ≤ P ∧
      W ≤ pCoreOf 2 P ∧ S ≤ P

@[expose] def Lat2 (K : Subgroup G) : Prop :=
  ∀ U P : Subgroup G, IsSylowTwoOf U K → U ≤ P → P ≤ K → P ≠ K →
    ∃ P'' Q'' : Subgroup G, ParabolicFacts P'' Q'' ∧ P ≤ P'' ∧ P'' ≤ K ∧
      ∀ M : Subgroup G, U ≤ M → M ≤ P → ¬ Group.IsSolvable ↥M →
        CFSG.Quasithin.perfectCore M = CFSG.Quasithin.perfectCore P''

theorem normalizer_subgroupOf_eq' {K V : Subgroup G} (hVK : V ≤ K) :
    Subgroup.normalizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) =
      (K ⊓ Subgroup.normalizer (V : Set G)).subgroupOf K := by
  ext n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    refine ⟨n.2, fun x => ?_⟩
    constructor
    · intro hx
      have := (h ⟨x, hVK hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 (by simpa using this)
    · intro hx
      have hxK : x ∈ K := by
        have h1 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem n.2) (hVK hx)) n.2
        have e : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) = x := by group
        rwa [e] at h1
      have := (h ⟨x, hxK⟩).2 (Subgroup.mem_subgroupOf.2 (by simpa using hx))
      exact Subgroup.mem_subgroupOf.1 this
  · rintro ⟨-, h⟩ x
    have hxK : (x : G) ∈ K := x.2
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.2 (by simpa using (h x).1 (Subgroup.mem_subgroupOf.1 hx))
    · intro hx
      exact Subgroup.mem_subgroupOf.2 ((h x).2 (by simpa using Subgroup.mem_subgroupOf.1 hx))

theorem stable_parabolic [Finite G] {K W : Subgroup G} (hBT : BT2 K) (hWK : W ≤ K) (hW0 : W ≠ ⊥)
    (hW2 : IsPGroup 2 W) (hst : chainStep K W = W) :
    ∃ S : Subgroup G, IsSylowTwoOf S K ∧ S ≤ nKW K W ∧ nKW K W ≠ K ∧
      pCoreOf 2 (nKW K W) = W := by
  obtain ⟨S, P', hS, hP'K, hP'top, hNP', hWP', hSP'⟩ := hBT W hWK hW0 hW2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := pCoreOf 2 P' with hR
  have hRP' : R ≤ P' := CFSG.LieType.BorelTits.pCoreOf_le 2 P'
  have hRK : R ≤ K := hRP'.trans hP'K
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P'
  have hP'R : P' ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P'
  set E : Subgroup G := R ⊓ Subgroup.normalizer (W : Set G) with hE
  have hEW : E ≤ W := by
    have hEle : E ≤ nKW K W := le_inf (inf_le_left.trans hRK) inf_le_right
    have hnorm : nKW K W ≤ Subgroup.normalizer (E : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hP'R (hNP' hx), Subgroup.le_normalizer hx.2⟩
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEle hnorm
      (hR2.to_le inf_le_left)
    exact h1.trans (le_of_eq hst)
  have hWR : W ≤ R := hWP'
  have hRW : R ≤ W := by
    by_contra hRW
    have hnil : Group.IsNilpotent ↥R := hR2.isNilpotent
    have hlt : W.subgroupOf R < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hRW ?_
      exact Subgroup.subgroupOf_eq_top.1 h
    have hgrow := Group.normalizerCondition_of_isNilpotent (W.subgroupOf R) hlt
    obtain ⟨x, hxN, hxH⟩ := IsConcreteLE.exists_of_lt hgrow
    rw [normalizer_subgroupOf_eq' hWR] at hxN
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.1 hxN
    exact hxH (Subgroup.mem_subgroupOf.2 (hEW hxE))
  have hReq : R = W := le_antisymm hRW hWR
  have hPeq : P' = nKW K W := by
    apply le_antisymm
    · exact le_inf hP'K (by rw [← hReq]; exact hP'R)
    · exact hNP'
  refine ⟨S, hS, hPeq ▸ hSP', ?_, ?_⟩
  · rw [← hPeq]
    exact hP'top
  · rw [← hPeq]
    exact hReq

theorem centralizer_le_of_lat2 [Finite G] {K W S : Subgroup G} (hL : Lat2 K)
    (hS : IsSylowTwoOf S K) (hSP : S ≤ nKW K W) (hPK : nKW K W ≠ K)
    (hcore : pCoreOf 2 (nKW K W) = W) : K ⊓ Subgroup.centralizer (W : Set G) ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P'', Q'', hF, hPP'', hP''K, -⟩ := hL S (nKW K W) hS hSP (nKW_le_left K W) hPK
  have hSP'' : S ≤ P'' := hSP.trans hPP''
  have hSyl : IsSylowOf 2 S P'' :=
    (isSylowTwoOf_iff_isSylowOf.1 hS).of_le hSP'' hP''K
  have hS2 : IsPGroup 2 S := hS.2.1
  have hSn : S ≤ Subgroup.normalizer (Q'' : Set G) := hSP''.trans hF.normalizes
  have hsup : IsPGroup 2 (Q'' ⊔ S : Subgroup G) := hF.pGroup.to_sup_of_normal_left' hS2 hSn
  have hQS : Q'' ⊔ S = S :=
    hSyl.eq_of_le le_sup_right (sup_le hF.le hSP'') hsup
  have hQ''S : Q'' ≤ S := le_sup_left.trans hQS.le
  have hQ''P : Q'' ≤ nKW K W := hQ''S.trans hSP
  have hQ''W : Q'' ≤ W := by
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ''P
      (hPP''.trans hF.normalizes) hF.pGroup
    rwa [hcore] at h1
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (W : Set G) := Subgroup.centralizer_le_normalizer _ hx.2
  have hxP : x ∈ P'' := hPP'' ⟨hx.1, hxN⟩
  have hxC : x ∈ Subgroup.centralizer (Q'' : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQ''W) hx.2
  exact hQ''W (hF.selfCentralizing ⟨hxP, hxC⟩)

end CFSG.QuasithinUnique.A5.Kc3G2
