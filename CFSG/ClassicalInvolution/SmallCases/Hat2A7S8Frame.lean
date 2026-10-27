module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Hyp51
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerFam
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Graph
public import CFSG.ClassicalInvolution.Asc77.AscT8T1
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_centralized_of_acts_trivially {K E : Subgroup G} (hE : IsPGroup 2 E)
    (hEN : E ≤ Subgroup.normalizer (K : Set G))
    (htriv : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ oddCoreOf K) :
    ∃ R : Subgroup G, IsSylow2In R K ∧ ∀ e ∈ E, ∀ r ∈ R, e * r = r * e := by
  obtain ⟨R, hR, hRinv⟩ := T3.exists_sylow_normalized hE hEN
  refine ⟨R, hR, fun e he r hr => ?_⟩
  have hrK : r ∈ K := hR.1 hr
  have hrR : e * r * e⁻¹ ∈ R := by
    have h1 : conjSub e R = R := hRinv e he
    rw [← h1]
    exact conj_mem_conjSub hr
  have h1 : e * r * e⁻¹ * r⁻¹ ∈ oddCoreOf K := htriv e he r hrK
  have hx : r⁻¹ * (e * r * e⁻¹) ∈ oddCoreOf K := by
    have e1 : r⁻¹ * (e * r * e⁻¹) = r⁻¹ * (e * r * e⁻¹ * r⁻¹) * r⁻¹⁻¹ := by group
    rw [e1]
    exact Balance.conj_mem_oddCoreIn (K.inv_mem hrK) h1
  have hxR : r⁻¹ * (e * r * e⁻¹) ∈ R := R.mul_mem (R.inv_mem hr) hrR
  have hx1 : r⁻¹ * (e * r * e⁻¹) = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hx
      (hR.2.1.to_le (Subgroup.zpowers_le.mpr hxR))
  have h3 : r = e * r * e⁻¹ := inv_mul_eq_one.mp hx1
  calc e * r = (e * r * e⁻¹) * e := by group
    _ = r * e := by rw [← h3]

theorem comm_mem_oddCore_of_mem_omegaNbr (hΩ : HypOmegaGen Ω) {K M : Subgroup G} {u : G}
    (hw : A7Witness K) (hM : M ∈ omegaNbr Ω K) (hu : IsUniqueInvolution M u) :
    u ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ oddCoreOf K := by
  obtain ⟨-, -, RM, hRM, hRMM, hRMN⟩ := hM
  have hRM2 : IsPGroup 2 RM := Sec7.isPGroup_of_mem_RSet hRM
  have h8M := Sec6Gen.eight_le_of_mem_RSet hΩ hRM
  have huRM : u ∈ RM := T3.mem_of_isPGroup hu hRMM hRM2 (by omega)
  have hgt : u ∈ Subgroup.normalizer (K : Set G) := hRMN huRM
  have huniq : ∀ x ∈ RM, orderOf x = 2 → x = u := by
    intro x hx hx2
    have hxx : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2, pow_two] at this
    rcases hu.unique x (hRMM hx) hxx with h | h
    · exfalso
      rw [h, orderOf_one] at hx2
      omega
    · exact h
  have htriv := Hat2A7.oddQuotAut_conjOn_eq_one_of_card hw hRMN hRM2 huRM huniq (by omega)
  refine ⟨hgt, fun k hk => ?_⟩
  have hmem := commutator_mem_oddCore_of_action_eq_one hgt htriv ⟨k, hk⟩
  have hmemG : k⁻¹ * (u * k * u⁻¹) ∈ oddCoreOf K := ⟨_, hmem, rfl⟩
  have e : u * k * u⁻¹ * k⁻¹ = k * (k⁻¹ * (u * k * u⁻¹)) * k⁻¹ := by group
  rw [e]
  exact Balance.conj_mem_oddCoreIn hk hmemG

theorem mem_centralizerModOdd {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ oddCoreOf K) : g ∈ centralizerModOdd ⊤ K :=
  ⟨Subgroup.mem_top g, hg, mem_normalizer_oddCore_of_mem_normalizer hg, fun k hk => h k hk⟩

theorem comm_of_mem_isUniqueInvolution {M : Subgroup G} {u : G} (hu : IsUniqueInvolution M u)
    {k : G} (hk : k ∈ M) : k * u = u * k := by
  have h := hu.conj_eq (n := k) (conjSub_eq_self_of_mem hk)
  calc k * u = (k * u * k⁻¹) * k := by group
    _ = u * k := by rw [h]

end Sylow

section Triangle

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {M : Fin 3 → Subgroup G}
  {x : Fin 3 → G}

structure Tri (Ω : Set (Subgroup G)) (M : Fin 3 → Subgroup G) (x : Fin 3 → G) : Prop where
  mem : ∀ i, M i ∈ Ω
  inv : ∀ i, IsUniqueInvolution (M i) (x i)
  adj : ∀ i j, i ≠ j → M j ∈ omegaNbr Ω (M i)

theorem Tri.sq (hT : Tri Ω M x) (i : Fin 3) : x i * x i = 1 := (hT.inv i).sq

theorem Tri.ne_one (hT : Tri Ω M x) (i : Fin 3) : x i ≠ 1 := (hT.inv i).ne_one

theorem Tri.comm (hΩ : HypOmegaGen Ω) (hT : Tri Ω M x) (i j : Fin 3) :
    x i * x j = x j * x i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · exact Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ (hT.inv i) (hT.adj i j hij) (hT.inv j)

theorem Tri.x_ne (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hT : Tri Ω M x) {i j : Fin 3}
    (hij : i ≠ j) : x i ≠ x j := by
  intro h
  have h1 : IsUniqueInvolution (M j) (x i) := h ▸ hT.inv j
  have h2 : M j = M i := hnt (M i) (hT.mem i) (M j) ⟨hT.mem j, x i, hT.inv i, h1⟩
  exact (hT.adj i j hij).2.1 h2

theorem Tri.mem_B (_ : Tri Ω M x) (i : Fin 3) :
    x i ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G) := by
  apply Subgroup.subset_closure
  fin_cases i <;> simp

theorem Tri.B_isElemAbelian (hΩ : HypOmegaGen Ω) (hT : Tri Ω M x) :
    IsElemAbelian 2 (Subgroup.closure ({x 0, x 1, x 2} : Set G)) :=
  T8T.isElemAbelian_closure_three (hT.sq 0) (hT.sq 1) (hT.sq 2) (hT.comm hΩ 0 1)
    (hT.comm hΩ 0 2) (hT.comm hΩ 1 2)

theorem Tri.card_B (hΩ : HypOmegaGen Ω) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hT : Tri Ω M x) (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) :
    Nat.card ↥(Subgroup.closure ({x 0, x 1, x 2} : Set G)) = 8 :=
  T8T.natCard_closure_three (hT.sq 0) (hT.sq 1) (hT.sq 2) (hT.comm hΩ 0 1) (hT.comm hΩ 0 2)
    (hT.comm hΩ 1 2) (hT.ne_one 0) (hT.ne_one 1) (hT.x_ne hnt (i := 0) (j := 1) (by decide))
    (hT.ne_one 2) hind

theorem Tri.x_mem_normalizer (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hT : Tri Ω M x) (i j : Fin 3) :
    x j ∈ Subgroup.normalizer (M i : Set G) :=
  T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hT.mem i) (hnt (M i) (hT.mem i))
    (hT.inv i) (Subgroup.mem_centralizer_singleton_iff.mpr (hT.comm hΩ j i))

theorem Tri.acts_trivially (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hT : Tri Ω M x) (i j : Fin 3) :
    x j ∈ centralizerModOdd ⊤ (M i) := by
  refine mem_centralizerModOdd (hT.x_mem_normalizer hΩ hnt i j) fun k hk => ?_
  by_cases hij : i = j
  · subst hij
    have h1 : x i * k = k * x i := (comm_of_mem_isUniqueInvolution (hT.inv i) hk).symm
    have h2 : x i * k * (x i)⁻¹ * k⁻¹ = 1 := by
      rw [h1]
      group
    rw [h2]
    exact (oddCoreOf (M i)).one_mem
  · exact (comm_mem_oddCore_of_mem_omegaNbr hΩ (hw (M i) (hT.mem i)) (hT.adj i j hij)
      (hT.inv j)).2 k hk

theorem Tri.B_le_centralizerModOdd (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hT : Tri Ω M x) (i : Fin 3) :
    Subgroup.closure ({x 0, x 1, x 2} : Set G) ≤ centralizerModOdd ⊤ (M i) := by
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl | rfl
  · exact hT.acts_trivially hΩ hw hnt i 0
  · exact hT.acts_trivially hΩ hw hnt i 1
  · exact hT.acts_trivially hΩ hw hnt i 2

theorem Tri.exists_sylow (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hT : Tri Ω M x)
    (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) (i : Fin 3) :
    ∃ R : Subgroup G, IsSylow2In R (M i) ∧
      ∀ c ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G), ∀ r ∈ R, c * r = r * c := by
  have hB8 := hT.card_B hΩ hnt hind
  have hB2 : IsPGroup 2 ↥(Subgroup.closure ({x 0, x 1, x 2} : Set G)) :=
    IsPGroup.of_card (n := 3) (by rw [hB8]; norm_num)
  have hle := hT.B_le_centralizerModOdd hΩ hw hnt i
  exact exists_sylow_centralized_of_acts_trivially hB2 (fun c hc => (hle hc).2.1)
    (fun e he k hk => (hle he).2.2.2 k hk)

theorem Tri.xMem (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hT : Tri Ω M x)
    (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) (i : Fin 3) {c : G}
    (hc : c ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G)) : T8.XMem Ω c (M i) := by
  obtain ⟨R, hR, hRc⟩ := hT.exists_sylow hΩ hw hnt hind i
  exact ⟨hT.mem i, (hT.B_le_centralizerModOdd hΩ hw hnt i hc).2.1, R, hR,
    fun r hr => (hRc c hc r hr).symm⟩

end Triangle

section Hyp51


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {K₀ : Subgroup G}

theorem layerHyp_of_pre (hs : Hat2A7S.Pre2A7 Ω K₀) {c : G} (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    Asc77.T8.LayerHyp Ω c :=
  ⟨hs.hyp, hs.classical, hs.below, hc2, Asc77.T8.not_central_of_ne_one hs.nonabelian hc1⟩

theorem witness_of_pre (hs : Hat2A7S.Pre2A7 Ω K₀) : ∀ L ∈ Ω, A7Witness L := fun L hL =>
  (hs.classical L hL).choose_spec.witness

theorem Tri.zStar (hs : Hat2A7S.Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hT : Tri Ω M x) (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) {c : G}
    (hcB : c ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G)) (hc1 : c ≠ 1) (i : Fin 3) :
    x i ∈ T8.layerJoin Ω c ∧
      ∀ y ∈ T8.layerJoin Ω c, x i * y * (x i)⁻¹ * y⁻¹ ∈ oddCoreOf (T8.layerJoin Ω c) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hc2 : c * c = 1 := by
    have := (hT.B_isElemAbelian hΩ).2 c hcB
    rwa [pow_two] at this
  have hL : Asc77.T8.LayerHyp Ω c := layerHyp_of_pre hs hc2 hc1
  have hK : T8.XMem Ω c (M i) := hT.xMem hΩ (witness_of_pre hs) hnt hind i hcB
  have hF := Asc77.T8.LayerFam.layerSet hΩ hK
  have hLΛ : T8.layerRes c (M i) ∈ T8.layerSet Ω c := ⟨M i, hK, rfl⟩
  have huL : x i ∈ T8.layerRes c (M i) :=
    (Asc77.T8.XMem.isUniqueInvolution_layerRes hΩ hs.classical hc2 hK (hT.inv i)).mem
  have hu : ∀ a ∈ T8.layerRes c (M i), a * x i = x i * a := fun a ha =>
    comm_of_mem_isUniqueInvolution (hT.inv i) (T8.layerRes_le c (M i) ha)
  exact ⟨T8.le_layerJoin hLΛ huL, fun y hy => hF.commutator_mem_oddCoreOf hL hLΛ huL hu hy⟩

theorem Tri.hyp51 (hs : Hat2A7S.Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hT : Tri Ω M x) (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) :
    Hyp51 (Subgroup.closure ({x 0, x 1, x 2} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  refine hyp51_of_zStar (hT.B_isElemAbelian hΩ) (hT.card_B hΩ hnt hind) fun c hcB hc1 => ?_
  have hc2 : c * c = 1 := by
    have := (hT.B_isElemAbelian hΩ).2 c hcB
    rwa [pow_two] at this
  have hcord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, x i ≠ c := by
    by_cases h0 : x 0 = c
    · exact ⟨1, fun h => hT.x_ne hnt (i := 0) (j := 1) (by decide) (h0.trans h.symm)⟩
    · exact ⟨0, h0⟩
  have hK : T8.XMem Ω c (M i) := hT.xMem hΩ (witness_of_pre hs) hnt hind i hcB
  have hF := Asc77.T8.LayerFam.layerSet hΩ hK
  obtain ⟨hbY, hZ⟩ := hT.zStar hs hnt hind hcB hc1 i
  refine ⟨x i, hT.mem_B i, ?_, T8.layerJoin Ω c, hbY, ?_, ?_, hZ⟩
  · intro h
    rcases T7A.eq_one_or_eq_of_mem_zpowers hcord h with h1 | h1
    · exact hT.ne_one i h1
    · exact hi h1
  · rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ c
  · intro n hn
    have hn' : n ∈ T8.cenZ c := by
      rw [T8.cenZ_eq_centralizer]
      exact hn
    exact hF.conjSub_famJoin hn'

end Hyp51

end CFSG.ClassicalInvolution.Hat2A7S8
