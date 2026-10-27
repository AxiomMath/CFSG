module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.AschTight.Sec7Basic
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen610

public section

namespace CFSG.ClassicalInvolution.Q3.TC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def IsNormalTwoIn (P : Subgroup G) (z : G) : Prop :=
  P ≤ Subgroup.centralizer ({z} : Set G) ∧ IsPGroup 2 P ∧
    ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ P

@[expose] def UCond (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  ∀ z : G, IsUniqueInvolution K z → ∀ J ∈ KPerp Ω K, ∃ U ∈ USet Ω, U ≤ J ∧
    ∃ P : Subgroup G, IsNormalTwoIn P z ∧ U ≤ P

@[expose] def etaSpan (η : Set (Subgroup G)) : Subgroup G := ⨆ U ∈ η, U

omit [Finite G] in
theorem le_etaSpan {η : Set (Subgroup G)} {U : Subgroup G} (hU : U ∈ η) : U ≤ etaSpan η :=
  le_biSup (fun V => V) hU

omit [Finite G] in
theorem etaSpan_le {η : Set (Subgroup G)} {H : Subgroup G} (h : ∀ U ∈ η, U ≤ H) :
    etaSpan η ≤ H :=
  iSup₂_le h

omit [Finite G] in
theorem etaSpan_isPGroup {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) : IsPGroup 2 (etaSpan η) := by
  obtain ⟨S, hS, -⟩ := hη
  exact S.isPGroup'.to_le (etaSpan_le fun U hU => (hS.1 hU).2)

theorem etaSpan_comm (hΩ : HypOmegaGen Ω) {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) :
    ∀ x ∈ etaSpan η, ∀ y ∈ etaSpan η, x * y = y * x := by
  obtain ⟨S, hS, hinv⟩ := hη
  exact (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hS hinv).1

omit [Finite G] in
theorem mem_RSet_of_isPGroup {J : Subgroup G} (hJ : J ∈ Ω) (h2 : IsPGroup 2 J) :
    J ∈ RSet Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥J :=
    { toSubgroup := ⊤
      isPGroup' := h2.of_equiv Subgroup.topEquiv.symm
      is_maximal' := fun {Q} _ hle => top_unique hle }
  refine ⟨J, hJ, P, ?_⟩
  show J = Subgroup.map J.subtype ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem normalizes_w_of_le_twoNormal (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {z : G} {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hWz : etaSpan η ≤ Subgroup.centralizer ({z} : Set G))
    {J : Subgroup G} (hJ : J ∈ Ω) {U₀ : Subgroup G} (hU₀ : U₀ ∈ USet Ω) (hU₀J : U₀ ≤ J)
    {P : Subgroup G} (hP : IsNormalTwoIn P z) (hU₀P : U₀ ≤ P) :
    (∀ j ∈ J, ∀ V ∈ η, conjSub j V ∈ η) ∧
      ∃ u : G, IsUniqueInvolution J u ∧ etaSpan η ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := etaSpan η with hWdef
  have hW2 : IsPGroup 2 W := etaSpan_isPGroup hη
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := etaSpan_comm hΩ hη
  obtain ⟨hPC, hP2, hPn⟩ := hP
  have hWnP : W ≤ Subgroup.normalizer (P : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      exact hPn w (hWz hw) p hp
    · intro hp
      have h1 := hPn w⁻¹ ((Subgroup.centralizer ({z} : Set G)).inv_mem (hWz hw)) _ hp
      simpa [mul_assoc] using h1
  have hWP2 : IsPGroup 2 (W ⊔ P : Subgroup G) := hW2.to_sup_of_normal_right' hP2 hWnP
  obtain ⟨S', hS'⟩ := hWP2.exists_le_sylow
  have hηS' : ∀ V ∈ η, V ≤ (S' : Subgroup G) := fun V hV =>
    (le_etaSpan hV).trans (le_sup_left.trans hS')
  have hU₀S' : U₀ ≤ (S' : Subgroup G) := hU₀P.trans (le_sup_right.trans hS')
  have hcard : 2 < Nat.card ↥(J ⊓ (S' : Subgroup G)) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU₀
    have hle : U₀ ≤ J ⊓ (S' : Subgroup G) := le_inf hU₀J hU₀S'
    have := Subgroup.card_le_of_le hle
    omega
  have hJW : J ⊓ W ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S' η hη hηS' J hJ hcard
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hJWU : J ⊓ W ∈ USet Ω := by
    obtain ⟨S₀, hS₀, -⟩ := hη
    exact (hS₀.1 hJW).1
  obtain ⟨-, -, -, -, -, -, -, -, hJW4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hJWU
  have huJW : u ∈ J ⊓ W := hu.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)
  have hWu : W ≤ Subgroup.centralizer ({u} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hWcomm w hw u huJW.2
  have hWNJ : W ≤ Subgroup.normalizer (J : Set G) := by
    refine etaSpan_le fun V hV => ?_
    by_cases hVJ : V = J ⊓ W
    · rw [hVJ]
      exact inf_le_left.trans Subgroup.le_normalizer
    obtain ⟨S₀, hS₀, -⟩ := hη
    have hVU : V ∈ USet Ω := (hS₀.1 hV).1
    obtain ⟨KV, hKV, hVKV⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hVU
    have hne : J ≠ KV := by
      rintro rfl
      exact hS₀.2.1 V hV (J ⊓ W) hJW hVJ J hJ ⟨hVKV, inf_le_left⟩
    obtain ⟨-, -, -, -, -, -, -, -, hV4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
    refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hKV hne hu hVKV
      (Sec6Gen.isPGroup_of_mem_USet hΩ hVU) (by omega) ?_
    exact (le_etaSpan hV).trans hWu
  have hJW2 : IsPGroup 2 (W ⊔ J : Subgroup G) := hW2.to_sup_of_normal_right' (h2 J hJ) hWNJ
  obtain ⟨S'', hS''⟩ := hJW2.exists_le_sylow
  have hηS'' : ∀ V ∈ η, V ≤ (S'' : Subgroup G) := fun V hV =>
    (le_etaSpan hV).trans (le_sup_left.trans hS'')
  have hJR : J ∈ RSet Ω := mem_RSet_of_isPGroup hJ (h2 J hJ)
  refine ⟨fun j hj V hV => ?_, u, hu, hWu⟩
  exact (Sec6Gen.l6_10Gen G Ω hΩ S'' η hη hηS'').1 J hJR (le_sup_right.trans hS'') j hj V hV

@[expose] def UCondOn (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Relation.ReflTransGen (fun M N : Subgroup G =>
    N ∈ Ω ∧ Disconnected.dAdj Ω M N) K L → UCond Ω L

theorem normalizes_w_of_reach (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hWz : etaSpan η ≤ Subgroup.centralizer ({z} : Set G)) (hU : UCondOn Ω K)
    {L : Subgroup G} (hL : Relation.ReflTransGen (fun M N : Subgroup G =>
      N ∈ Ω ∧ Disconnected.dAdj Ω M N) K L) :
    L ∈ Ω ∧ (∀ l ∈ L, ∀ V ∈ η, conjSub l V ∈ η) ∧
      ∃ u : G, IsUniqueInvolution L u ∧ etaSpan η ≤ Subgroup.centralizer ({u} : Set G) := by
  have key : ∀ M : Subgroup G, Relation.ReflTransGen (fun M N : Subgroup G =>
      N ∈ Ω ∧ Disconnected.dAdj Ω M N) K M →
      M ∈ Ω ∧ ∃ u : G, IsUniqueInvolution M u ∧
        etaSpan η ≤ Subgroup.centralizer ({u} : Set G) := by
    intro M hM
    induction hM with
    | refl => exact ⟨hK, z, hz, hWz⟩
    | tail hKM hMN ih =>
      rename_i M N
      obtain ⟨hMΩ, uM, huM, hWuM⟩ := ih
      obtain ⟨hNΩ, hadj⟩ := hMN
      have hNM : N ∈ KPerp Ω M := by
        refine Set.mem_insert_of_mem _ ?_
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hNΩ hMΩ h
      obtain ⟨U₀, hU₀, hU₀N, P, hP, hU₀P⟩ := hU M hKM uM huM N hNM
      obtain ⟨-, uN, huN, hWuN⟩ :=
        normalizes_w_of_le_twoNormal hΩ h2 hη hWuM hNΩ hU₀ hU₀N hP hU₀P
      exact ⟨hNΩ, uN, huN, hWuN⟩
  have hLΩ : L ∈ Ω := (key L hL).1
  refine ⟨hLΩ, ?_, (key L hL).2⟩
  obtain ⟨-, uL, huL, hWuL⟩ := key L hL
  have hLL : L ∈ KPerp Ω L := Set.mem_insert L _
  obtain ⟨U₀, hU₀, hU₀L, P, hP, hU₀P⟩ := hU L hL uL huL L hLL
  exact (normalizes_w_of_le_twoNormal hΩ h2 hη hWuL hLΩ hU₀ hU₀L hP hU₀P).1

end CFSG.ClassicalInvolution.Q3.TC
