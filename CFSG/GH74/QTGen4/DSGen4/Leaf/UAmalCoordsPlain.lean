module

public import CFSG.GH74.QTGen4.U42.CoordsB
public import CFSG.GH74.QTGen4.U42.CoordsC
public import CFSG.GH74.QTGen4.U42.U0CoreE
public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement
open scoped Pointwise
open CFSG.Quasithin.A5Model
open CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open CFSG.Quasithin.A5Model
open scoped Pointwise

theorem dsucp_pact_of_coords (σ : Equiv.Perm (Fin 5)) (x y : W5)
    (h : ∀ i : Fin 5, ((Multiplicative.toAdd y : ↥Ev) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) (σ⁻¹ i)) : y = pact σ x := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  show ((Multiplicative.toAdd y : ↥Ev) : Fin 5 → ZMod 2) = ((pw σ (Multiplicative.toAdd x) : ↥Ev) : Fin 5 → ZMod 2)
  funext i
  rw [pw_coe]
  exact h i

theorem dsucp_pact_conj (σ g : Equiv.Perm (Fin 5)) (x : W5) :
    pact (σ * g * σ⁻¹) (pact σ x) = pact σ (pact g x) := by
  have h : pact (σ * g * σ⁻¹) * pact σ = pact σ * pact g := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  exact congrArg (fun φ : MulAut W5 => φ x) h

theorem dsucp_norm_K4_fix4 : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
    (∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
      CFSG.Quasithin.H13.A5.InK4 (σ * k * σ⁻¹)) → σ 4 = 4 := by
  decide +kernel

theorem dsucp_frame_psi {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hα : IsAltType L 5) (hblk : blockU L ≤ pCoreOf 2 L) (hE : Nat.card (pCoreOf 2 L) = 16) :
    ∃ (α : ↥L →* alternatingGroup (Fin 5)) (ψ : ↥(pCoreOf 2 L) ≃* W5),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ∀ (ℓ : ↥L) (u w : ↥(pCoreOf 2 L)), (w : G) = ℓ * u * ℓ⁻¹ →
        ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u) := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := hα
  have key : ∀ (U : Subgroup G) (hU : U = pCoreOf 2 L) (β : ↥U →* W5),
      Function.Surjective β →
      (∀ (ℓ : ↥L) (u v : ↥U), (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin 5,
        ((Multiplicative.toAdd (β v) : ↥Ev) : Fin 5 → ZMod 2) i =
          ((Multiplicative.toAdd (β u) : ↥Ev) : Fin 5 → ZMod 2) ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i)) →
      ∃ (ψ : ↥(pCoreOf 2 L) ≃* W5), ∀ (ℓ : ↥L) (u w : ↥(pCoreOf 2 L)),
        (w : G) = ℓ * u * ℓ⁻¹ → ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u) := by
    intro U hU β hs hβeq
    subst hU
    have hcard : Nat.card ↥(pCoreOf 2 L) = Nat.card W5 := by
      rw [hE, CFSG.Quasithin.H13.A5.card_W5]
    have hbij : Function.Bijective β := (Nat.bijective_iff_surjective_and_card β).mpr ⟨hs, hcard⟩
    refine ⟨MulEquiv.ofBijective β hbij, fun ℓ u w hw => ?_⟩
    exact dsucp_pact_of_coords _ _ _ (fun i => hβeq ℓ u w hw i)
  have hUE : blockU L = pCoreOf 2 L := by
    apply Subgroup.eq_of_le_of_card_ge hblk
    rw [hE]
    have := Nat.card_le_card_of_surjective β hβs
    rw [CFSG.Quasithin.H13.A5.card_W5] at this
    exact this
  obtain ⟨ψ, hψ⟩ := key (blockU L) hUE β hβs (fun ℓ u v hv i => hβe ℓ u v hv i)
  exact ⟨α, ψ, hαs, hαk, hψ⟩


theorem dsucp_sylow_K4 (T0 : Subgroup A5) (hT0 : IsPGroup 2 T0) (hT0i : ¬ 2 ∣ T0.index) :
    ∃ g : A5, ∀ x : A5, x ∈ T0 ↔ g * x * g⁻¹ ∈ K4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4p : IsPGroup 2 K4 := IsPGroup.of_card (n := 2) (by rw [card_K4]; norm_num)
  let P : Sylow 2 A5 := hT0.toSylow hT0i
  let Q : Sylow 2 A5 := hK4p.toSylow (by simpa using K4_index_odd)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 P Q
  have hc : (K4 : Subgroup A5) = MulAut.conj g • T0 := by
    have := congrArg (fun R : Sylow 2 A5 => (R : Subgroup A5)) hg
    simpa [Sylow.coe_subgroup_smul, P, Q, IsPGroup.toSylow_coe] using this.symm
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [hc]
    exact ⟨x, hx, rfl⟩
  · rw [hc] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    have : s = x := by
      apply (MulAut.conj g).injective
      exact hsx
    rw [← this]
    exact hs


theorem dsucp_pCoreOf_le {G : Type} [Group G] (L : Subgroup G) : pCoreOf 2 L ≤ L :=
  Subgroup.map_subtype_le _


theorem dsucp_conj_eq_one_iff (σ : Equiv.Perm (Fin 5)) (a : alternatingGroup (Fin 5)) :
    σ * (a : Equiv.Perm (Fin 5)) * σ⁻¹ = 1 ↔ a = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    have h2 : (a : Equiv.Perm (Fin 5)) = 1 := by
      have := congrArg (fun x => σ⁻¹ * x * σ) h
      simpa [mul_assoc] using this
    simpa using h2
  · intro h
    subst h
    simp

theorem dsucp_V_normal {G : Type} [Group G] (L : Subgroup G) :
    ((pCoreOf 2 L).subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (dsucp_pCoreOf_le L)).mpr
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)

@[expose] noncomputable def dsucp_coords {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 5)) (ψ : ↥(pCoreOf 2 L) ≃* W5)
    (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hψ : ∀ (ℓ : ↥L) (u w : ↥(pCoreOf 2 L)), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u))
    (σ : alternatingGroup (Fin 5)) : CFSG.GH74.QTGen4.U42.CoordData ↥L where
  V := (pCoreOf 2 L).subgroupOf L
  hV := dsucp_V_normal L
  ψ := (Subgroup.subgroupOfEquivOfLe (dsucp_pCoreOf_le L)).trans (ψ.trans (pact (σ : Equiv.Perm (Fin 5))))
  ρ := (MulAut.conj (σ : Equiv.Perm (Fin 5))).toMonoidHom.comp ((alternatingGroup (Fin 5)).subtype.comp α)
  ker_ρ := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (σ : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * (σ : Equiv.Perm (Fin 5))⁻¹ = 1 ↔ (m : G) ∈ pCoreOf 2 L
    rw [dsucp_conj_eq_one_iff, ← MonoidHom.mem_ker, hαk]
    exact CFSG.Quasithin.F1.mem_pCore_iff_coe m
  conj_ψ := fun m v => by
    have h2 : (v : G) ∈ pCoreOf 2 L := Subgroup.mem_subgroupOf.mp v.2
    have h1 : ((m * (v : ↥L) * m⁻¹ : ↥L) : G) ∈ pCoreOf 2 L :=
      Subgroup.mem_subgroupOf.mp ((dsucp_V_normal L).conj_mem _ v.2 m)
    have key := hψ m ⟨(v : G), h2⟩ ⟨((m * (v : ↥L) * m⁻¹ : ↥L) : G), h1⟩ (by simp)
    show pact (σ : Equiv.Perm (Fin 5)) (ψ ⟨((m * (v : ↥L) * m⁻¹ : ↥L) : G), h1⟩) =
      pact ((σ : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * (σ : Equiv.Perm (Fin 5))⁻¹) (pact (σ : Equiv.Perm (Fin 5)) (ψ ⟨(v : G), h2⟩))
    rw [key, dsucp_pact_conj]


theorem dsucp_range {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 5)) (hαs : Function.Surjective α)
    (ψ : ↥(pCoreOf 2 L) ≃* W5) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hψ : ∀ (ℓ : ↥L) (u w : ↥(pCoreOf 2 L)), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u))
    (σ : alternatingGroup (Fin 5)) :
    (dsucp_coords α ψ hαk hψ σ).ρ.range = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    show (σ : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
      (σ : Equiv.Perm (Fin 5))⁻¹ ∈ alternatingGroup (Fin 5)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    have hσ : (σ : Equiv.Perm (Fin 5)).sign = 1 := Equiv.Perm.mem_alternatingGroup.mp σ.2
    have hm : ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)).sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (α m).2
    rw [hσ, hm]
    simp
  · intro τ hτ
    obtain ⟨m, hm⟩ := hαs ⟨(σ : Equiv.Perm (Fin 5))⁻¹ * τ * (σ : Equiv.Perm (Fin 5)), by
      rw [Equiv.Perm.mem_alternatingGroup]
      have hσ : (σ : Equiv.Perm (Fin 5)).sign = 1 := Equiv.Perm.mem_alternatingGroup.mp σ.2
      have hτ' : τ.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp hτ
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hσ, hτ']
      simp⟩
    refine ⟨m, ?_⟩
    show (σ : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
      (σ : Equiv.Perm (Fin 5))⁻¹ = τ
    rw [hm]
    simp [mul_assoc]

theorem dsucp_e {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 5)) (hαs : Function.Surjective α)
    (ψ : ↥(pCoreOf 2 L) ≃* W5) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hψ : ∀ (ℓ : ↥L) (u w : ↥(pCoreOf 2 L)), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u))
    (σ : alternatingGroup (Fin 5)) (T : Subgroup ↥L)
    (hVT : (pCoreOf 2 L).subgroupOf L ≤ T) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (hρT : ∀ t ∈ T, CFSG.Quasithin.H13.A5.InK4 ((dsucp_coords α ψ hαk hψ σ).ρ t))
    (hK4 : ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
      ∃ t ∈ T, (dsucp_coords α ψ hαk hψ σ).ρ t = k) :
    ∃ e : ↥L ≃* CFSG.GH74.QTGen4.U42.Mof (alternatingGroup (Fin 5)),
      (∀ m : ↥L, ((e m : CFSG.GH74.QTGen4.U42.Mof _) : CFSG.GH74.QTGen4.U42.Mc).right =
        (dsucp_coords α ψ hαk hψ σ).ρ m) ∧
      (∀ v : ↥((pCoreOf 2 L).subgroupOf L), ((e v : CFSG.GH74.QTGen4.U42.Mof _) : CFSG.GH74.QTGen4.U42.Mc) =
        SemidirectProduct.inl ((dsucp_coords α ψ hαk hψ σ).ψ v)) := by
  classical
  obtain ⟨A, hA1, hA2⟩ := (dsucp_coords α ψ hαk hψ σ).exists_complement_plain T hVT hT hTi hρT hK4
  obtain ⟨e, he1, he2⟩ := (dsucp_coords α ψ hαk hψ σ).equiv_of_complement A hA1 hA2
  have hrange := dsucp_range α hαs ψ hαk hψ σ
  refine ⟨e.trans (MulEquiv.subgroupCongr (congrArg CFSG.GH74.QTGen4.U42.Mof hrange)), fun m => he2 m, fun v => he1 v⟩

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open CFSG.Quasithin.A5Model

theorem dsucp_s3_centralizer : ∀ a g : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 →
    g * a = a * g → g = 1 ∨ g = a := by
  decide

theorem dsucp_perm3_card : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem dsucp_normalizer_sylow {G : Type} [Group G] [Finite G] {L2 S : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2)
    (e : oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))
    (hN : pCoreOf 2 L2 ≤ S ⊓ L2)
    (hNc : Nat.card ↥(pCoreOf 2 L2) = 32) :
    ∀ x ∈ L2, x ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) → x ∈ S ⊓ L2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro x hxL hxN
  let φ : ↥L2 →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L2))
  have hφsurj : Function.Surjective φ := by
    intro σ
    obtain ⟨q, hq⟩ := e.surjective σ
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, by simpa [φ] using hq⟩
  have hker : φ.ker = CFSG.pCore 2 ↥L2 := by
    ext y
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hpc_mem : ∀ y : ↥L2, y ∈ CFSG.pCore 2 ↥L2 ↔ (y : G) ∈ pCoreOf 2 L2 :=
    fun y => CFSG.Quasithin.F1.mem_pCore_iff_coe y
  have hcardpc : Nat.card ↥(CFSG.pCore 2 ↥L2) = 32 := by
    rw [← hNc]
    exact (Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥L2) (f := L2.subtype) (Subgroup.subtype_injective L2)).symm
  have hcardL2 : Nat.card ↥L2 = 192 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L2), hcardpc,
      Nat.card_congr e.toEquiv, dsucp_perm3_card]
  set T : Subgroup ↥L2 := (S ⊓ L2 : Subgroup G).subgroupOf L2 with hTdef
  have hTpc : CFSG.pCore 2 ↥L2 ≤ T := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact hN ((hpc_mem y).mp hy)
  have hTodd : ¬ 2 ∣ T.index := hsyl.2.2
  have hT2 : ∀ y : ↥L2, y ∈ T → ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hsyl.2.1 ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(S ⊓ L2 : Subgroup G) => (z : G)) hk
    simpa using this
  have hdvd : T.index ∣ 192 := by
    have h1 := Subgroup.card_mul_index T
    rw [hcardL2] at h1
    exact ⟨Nat.card T, by rw [← h1]; ring⟩
  have hTindex : T.index = 3 := by
    have hne1 : T.index ≠ 1 := by
      intro h1
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L2) 3 (by rw [hcardL2]; norm_num)
      have hyT : y ∈ T := by
        rw [Subgroup.index_eq_one] at h1
        rw [h1]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := hT2 y hyT
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hy]
        exact orderOf_dvd_of_pow_eq_one hk
      have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
      omega
    have h2k : Nat.Coprime 2 T.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hTodd
    have hc64 : Nat.Coprime (2 ^ 6) T.index := Nat.Coprime.pow_left 6 h2k
    have h192 : T.index ∣ 3 * 2 ^ 6 := by norm_num; exact hdvd
    have h3 : T.index ∣ 3 := Nat.Coprime.dvd_of_dvd_mul_right hc64.symm h192
    rcases (Nat.dvd_prime (by norm_num)).mp h3 with h | h
    · exact absurd h hne1
    · exact h
  have hcardT : Nat.card T = 64 := by
    have h1 := Subgroup.card_mul_index T
    rw [hcardL2, hTindex] at h1
    omega
  have hker_le : φ.ker ≤ T := by
    rw [hker]
    exact hTpc
  have hHindex : (T.map φ).index = 3 := by
    rw [Subgroup.index_map_eq T hφsurj hker_le, hTindex]
  have hHcard : Nat.card ↥(T.map φ) = 2 := by
    have h1 := Subgroup.card_mul_index (T.map φ)
    rw [hHindex, dsucp_perm3_card] at h1
    omega
  obtain ⟨a', ha'1, ha'u⟩ := (Nat.card_eq_two_iff' (1 : ↥(T.map φ))).mp hHcard
  set a : Equiv.Perm (Fin 3) := (a' : Equiv.Perm (Fin 3)) with ha_def
  have ha_ne : a ≠ 1 := fun h => ha'1 (Subtype.ext h)
  have ha_mem : a ∈ T.map φ := a'.2
  have ha_sq : a * a = 1 := by
    have hord : orderOf a' ∣ 2 := by
      have := orderOf_dvd_natCard a'
      rwa [hHcard] at this
    have hne : orderOf a' ≠ 1 := fun h => ha'1 (orderOf_eq_one_iff.mp h)
    have h2 : orderOf a' = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact absurd h hne
      · exact h
    have hpow : a' ^ 2 = 1 := by
      rw [← h2]
      exact pow_orderOf_eq_one a'
    have := congrArg (fun z : ↥(T.map φ) => (z : Equiv.Perm (Fin 3))) hpow
    simpa [ha_def, pow_two] using this
  have hmem_of : ∀ h ∈ T.map φ, h = 1 ∨ h = a := by
    intro h hh
    by_cases h1 : h = 1
    · exact Or.inl h1
    · right
      have := ha'u ⟨h, hh⟩ (fun e => h1 (congrArg Subtype.val e))
      exact congrArg Subtype.val this
  set X : ↥L2 := ⟨x, hxL⟩ with hX
  have hconjT : ∀ t ∈ T, X * t * X⁻¹ ∈ T := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    have hx' : ((X * t * X⁻¹ : ↥L2) : G) = x * (t : G) * x⁻¹ := by
      simp [hX]
    rw [hx']
    exact (Subgroup.mem_normalizer_iff.mp hxN (t : G)).mp ht
  have hgH : ∀ h ∈ T.map φ, φ X * h * (φ X)⁻¹ ∈ T.map φ := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨X * t * X⁻¹, hconjT t ht, ?_⟩
    simp [map_mul, map_inv]
  have hcomm : φ X * a = a * φ X := by
    have h1 : φ X * a * (φ X)⁻¹ = a := by
      rcases hmem_of _ (hgH a ha_mem) with h | h
      · exfalso
        apply ha_ne
        calc a = (φ X)⁻¹ * (φ X * a * (φ X)⁻¹) * φ X := by group
          _ = 1 := by rw [h]; group
      · exact h
    calc φ X * a = (φ X * a * (φ X)⁻¹) * φ X := by group
      _ = a * φ X := by rw [h1]
  have hgT : φ X ∈ T.map φ := by
    rcases dsucp_s3_centralizer a (φ X) ha_sq ha_ne hcomm with h | h
    · rw [h]
      exact (T.map φ).one_mem
    · rw [h]
      exact ha_mem
  obtain ⟨t, ht, hφt⟩ := hgT
  have hXT : X ∈ T := by
    have h1 : t⁻¹ * X ∈ CFSG.pCore 2 ↥L2 := by
      rw [← hker]
      refine MonoidHom.mem_ker.mpr ?_
      simp [map_mul, map_inv, hφt]
    have h2 := hTpc h1
    have h3 : X = t * (t⁻¹ * X) := by group
    rw [h3]
    exact T.mul_mem ht h2
  exact Subgroup.mem_subgroupOf.mp hXT

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement
open CFSG.Quasithin.A5Model

theorem dsucp_borelOf_plain {G : Type} [Group G] {L1 S : Subgroup G} (hS : S ≤ L1) :
    borelOf L1 S = L1 ⊓ Subgroup.normalizer (S : Set G) := by
  unfold borelOf
  rw [inf_eq_left.mpr hS]

theorem dsucp_P1_eq {G : Type} [Group G] {L1 L2 S : Subgroup G}
    (hS : S ≤ L1) (hb2 : borelOf L2 S ≤ S) : L1 ⊔ bigB L1 L2 S = L1 := by
  apply le_antisymm
  · refine sup_le le_rfl ?_
    show borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ L1
    exact sup_le (sup_le (CFSG.Quasithin.F1.borelOf_le L1 S) (hb2.trans hS)) hS
  · exact le_sup_left

theorem dsucp_bigB_eq {G : Type} [Group G] {L1 L2 S : Subgroup G}
    (hS : S ≤ L1) (hb2 : borelOf L2 S ≤ S) :
    bigB L1 L2 S = L1 ⊓ Subgroup.normalizer (S : Set G) := by
  apply le_antisymm
  · have hSN : S ≤ L1 ⊓ Subgroup.normalizer (S : Set G) := le_inf hS Subgroup.le_normalizer
    show borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ L1 ⊓ Subgroup.normalizer (S : Set G)
    refine sup_le (sup_le ?_ ?_) hSN
    · rw [dsucp_borelOf_plain hS]
    · exact (hb2.trans hSN)
  · rw [← dsucp_borelOf_plain hS]
    exact le_sup_of_le_left le_sup_left


theorem dsucp_card_sup {G : Type} [Group G] [Finite G] {L2 B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L2 : Set G)) :
    Nat.card ↥(B ⊔ L2) * Nat.card ↥(B ⊓ L2) = Nat.card ↥L2 * Nat.card ↥B := by
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hBN
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBN
  have hcard := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B L2 hBN).toEquiv
  have hq1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L2.subgroupOf B)
  have hq2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L2.subgroupOf (B ⊔ L2))
  have hc1 : Nat.card ↥(L2.subgroupOf (B ⊔ L2)) = Nat.card ↥L2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : L2 ≤ B ⊔ L2)).toEquiv
  have hc2 : Nat.card ↥(L2.subgroupOf B) = Nat.card ↥(B ⊓ L2) := by
    rw [← Subgroup.card_map_of_injective (f := B.subtype) (Subgroup.subtype_injective B),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hq2, hc1, hq1, hc2, hcard]
  ring

instance dsucpDecA4s : DecidablePred (· ∈ CFSG.Quasithin.A5Model.A4s) := fun σ =>
  decidable_of_iff ((σ : Equiv.Perm (Fin 5)) 4 = 4) CFSG.Quasithin.A5Model.mem_A4s.symm

theorem dsucp_card_A4s : Nat.card ↥CFSG.Quasithin.A5Model.A4s = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel


theorem dsucp_K4_stable : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ 4 = 4 →
    ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
      CFSG.Quasithin.H13.A5.InK4 (σ * k * σ⁻¹) := by
  decide +kernel

theorem dsucp_K4_InD : ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
    CFSG.Quasithin.H13.A5.InD k := by
  decide +kernel

theorem dsucp_K1 {G : Type} [Group G] {L1 S : Subgroup G}
    {ρ : ↥L1 →* Equiv.Perm (Fin 5)}
    (hker : ∀ m : ↥L1, ρ m = 1 → (m : G) ∈ S)
    (hρS : ∀ m : ↥L1, (m : G) ∈ S → CFSG.Quasithin.H13.A5.InK4 (ρ m))
    (hsurj : ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
      ∃ m : ↥L1, (m : G) ∈ S ∧ ρ m = k) :
    ∀ m : ↥L1, (m : G) ∈ S ↔ CFSG.Quasithin.H13.A5.InK4 (ρ m) := by
  intro m
  refine ⟨hρS m, fun hk => ?_⟩
  obtain ⟨t, ht, hρt⟩ := hsurj (ρ m) hk
  have h1 : ρ (t⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, hρt, inv_mul_cancel]
  have h2 : ((t⁻¹ * m : ↥L1) : G) ∈ S := hker _ h1
  have h3 : (m : G) = (t : G) * ((t⁻¹ * m : ↥L1) : G) := by
    simp
  rw [h3]
  exact S.mul_mem ht h2

theorem dsucp_K2 {G : Type} [Group G] {L1 S : Subgroup G} (hSL : S ≤ L1)
    {ρ : ↥L1 →* Equiv.Perm (Fin 5)}
    (hsgn : ∀ m : ↥L1, (ρ m).sign = 1)
    (hK1 : ∀ m : ↥L1, (m : G) ∈ S ↔ CFSG.Quasithin.H13.A5.InK4 (ρ m))
    (hsurj : ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
      ∃ m : ↥L1, (m : G) ∈ S ∧ ρ m = k) :
    ∀ m : ↥L1, (m : G) ∈ Subgroup.normalizer (S : Set G) ↔ (ρ m) 4 = 4 := by
  have hconj : ∀ m : ↥L1, (ρ m) 4 = 4 → ∀ s : ↥L1, (s : G) ∈ S →
      ((m * s * m⁻¹ : ↥L1) : G) ∈ S := by
    intro m hm s hs
    rw [hK1] at hs ⊢
    have := dsucp_K4_stable (ρ m) (hsgn m) hm (ρ s) hs
    simpa [map_mul, map_inv] using this
  intro m
  constructor
  · intro hm
    apply dsucp_norm_K4_fix4 (ρ m) (hsgn m)
    intro k hk
    obtain ⟨s, hs, rfl⟩ := hsurj k hk
    have h1 : (m : G) * (s : G) * (m : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hm (s : G)).mp hs
    have h2 : ((m * s * m⁻¹ : ↥L1) : G) ∈ S := by simpa using h1
    have h3 := (hK1 _).mp h2
    simpa [map_mul, map_inv] using h3
  · intro hm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hconj m hm ⟨h, hSL hh⟩ hh
      simpa using this
    · intro hh
      have hm' : (ρ m⁻¹) 4 = 4 := by
        rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
        exact hm.symm
      have := hconj m⁻¹ hm' ⟨(m : G) * h * (m : G)⁻¹, hSL hh⟩ hh
      simpa [mul_assoc] using this

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement
open CFSG.Quasithin.A5Model
open CFSG.GH74.QTGen4.U42

theorem dsucp_U0 {G : Type} [Group G] [Finite G] {L1 L2 S B : Subgroup G}
    (hS : S ≤ L1) (hQS : pCoreOf 2 L2 ≤ S)
    (hQc : Nat.card ↥(pCoreOf 2 L2) = 32)
    (hBQ : ∀ b : G, b ∈ B → ∀ q : G, q ∈ pCoreOf 2 L2 → b * q * b⁻¹ ∈ pCoreOf 2 L2)
    (hnotE : ¬ pCoreOf 2 L1 ≤ pCoreOf 2 L2) (hE : pCoreOf 2 L1 ≤ L1)
    (e : ↥L1 ≃* U42.Mof (alternatingGroup (Fin 5)))
    (hBe : ∀ m : ↥L1, (m : G) ∈ B ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Bc)
    (hSe : ∀ m : ↥L1, (m : G) ∈ S ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Tc)
    (hEw : ∀ v : ↥((pCoreOf 2 L1).subgroupOf L1), ((e v : U42.Mof _) : U42.Mc) ∈ U42.Wc) :
    ∀ m : ↥L1, (m : G) ∈ pCoreOf 2 L2 ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.U0 := by
  classical
  have hQL1 : pCoreOf 2 L2 ≤ L1 := hQS.trans hS
  set Xm : Subgroup (U42.Mof (alternatingGroup (Fin 5))) :=
    ((pCoreOf 2 L2).subgroupOf L1).map e.toMonoidHom with hXm
  set X : Subgroup U42.Mc := Xm.map (U42.Mof (alternatingGroup (Fin 5))).subtype with hX
  have hXmem : ∀ x : U42.Mc, x ∈ X ↔ ∃ m : ↥L1, (m : G) ∈ pCoreOf 2 L2 ∧
      ((e m : U42.Mof _) : U42.Mc) = x := by
    intro x
    constructor
    · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨e m, ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩, rfl⟩
  have hXle : X ≤ U42.Thc := by
    rintro x hx
    obtain ⟨m, hm, rfl⟩ := (hXmem _).mp hx
    have hT : ((e m : U42.Mof _) : U42.Mc) ∈ U42.Tc := (hSe m).mp (hQS hm)
    exact dsucp_K4_InD _ hT
  have hXcard : Nat.card X = 32 := by
    have h1 : Nat.card ↥X = Nat.card ↥Xm :=
      Subgroup.card_map_of_injective (f := (U42.Mof (alternatingGroup (Fin 5))).subtype)
        (Subgroup.subtype_injective _)
    have h2 : Nat.card ↥Xm = Nat.card ↥((pCoreOf 2 L2).subgroupOf L1) :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    have h3 : Nat.card ↥((pCoreOf 2 L2).subgroupOf L1) = 32 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL1).toEquiv, hQc]
    rw [h1, h2, h3]
  have hXB : ∀ b ∈ U42.Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    obtain ⟨q, hq, rfl⟩ := (hXmem _).mp hx
    have hbM : b ∈ U42.Mof (alternatingGroup (Fin 5)) := by
      rw [U42.mem_Mof]
      exact Equiv.Perm.mem_alternatingGroup.mpr hb.1
    set bM : ↥(U42.Mof (alternatingGroup (Fin 5))) := ⟨b, hbM⟩ with hbM_def
    set mb : ↥L1 := e.symm bM with hmb_def
    have hmb : ((e mb : U42.Mof _) : U42.Mc) = b := by
      rw [hmb_def, MulEquiv.apply_symm_apply]
    have hmbB : (mb : G) ∈ B := (hBe mb).mpr (by rw [hmb]; exact hb)
    refine (hXmem _).mpr ⟨mb * q * mb⁻¹, ?_, ?_⟩
    · have := hBQ (mb : G) hmbB (q : G) hq
      simpa using this
    · simp [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hmb]
  have hnotW : ¬ U42.Wc ≤ X := by
    intro hW
    apply hnotE
    intro y hy
    let v : ↥((pCoreOf 2 L1).subgroupOf L1) := ⟨⟨y, hE hy⟩, Subgroup.mem_subgroupOf.mpr hy⟩
    obtain ⟨m, hm, hme⟩ := (hXmem _).mp (hW (hEw v))
    have hmv : m = (v : ↥L1) := e.injective (Subtype.ext hme)
    have hmy : (m : G) = y := by rw [hmv]
    rw [← hmy]
    exact hm
  have hX_eq : X = U42.U0 := U42.U0_unique hXle hXcard hXB hnotW
  intro m
  constructor
  · intro hm
    rw [← hX_eq]
    exact (hXmem _).mpr ⟨m, hm, rfl⟩
  · intro hm
    rw [← hX_eq] at hm
    obtain ⟨m', hm', hme⟩ := (hXmem _).mp hm
    have : m' = m := e.injective (Subtype.ext hme)
    rw [← this]
    exact hm'

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement
open CFSG.Quasithin.A5Model
open CFSG.GH74.QTGen4.U42

theorem dsucp_L2_cards {G : Type} [Group G] [Finite G] {L2 S : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2)
    (e : oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))
    (hN : pCoreOf 2 L2 ≤ S ⊓ L2)
    (hNc : Nat.card ↥(pCoreOf 2 L2) = 32) :
    Nat.card ↥L2 = 192 ∧ Nat.card ↥(S ⊓ L2) = 64 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let φ : ↥L2 →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L2))
  have hcardpc : Nat.card ↥(CFSG.pCore 2 ↥L2) = 32 := by
    rw [← hNc]
    exact (Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥L2) (f := L2.subtype)
      (Subgroup.subtype_injective L2)).symm
  have hcardL2 : Nat.card ↥L2 = 192 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L2), hcardpc,
      Nat.card_congr e.toEquiv, dsucp_perm3_card]
  refine ⟨hcardL2, ?_⟩
  set T : Subgroup ↥L2 := (S ⊓ L2 : Subgroup G).subgroupOf L2 with hTdef
  have hTodd : ¬ 2 ∣ T.index := hsyl.2.2
  have hT2 : ∀ y : ↥L2, y ∈ T → ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hsyl.2.1 ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(S ⊓ L2 : Subgroup G) => (z : G)) hk
    simpa using this
  have hdvd : T.index ∣ 192 := by
    have h1 := Subgroup.card_mul_index T
    rw [hcardL2] at h1
    exact ⟨Nat.card T, by rw [← h1]; ring⟩
  have hTindex : T.index = 3 := by
    have hne1 : T.index ≠ 1 := by
      intro h1
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L2) 3 (by rw [hcardL2]; norm_num)
      have hyT : y ∈ T := by
        rw [Subgroup.index_eq_one] at h1
        rw [h1]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := hT2 y hyT
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hy]
        exact orderOf_dvd_of_pow_eq_one hk
      have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
      omega
    have h2k : Nat.Coprime 2 T.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hTodd
    have hc64 : Nat.Coprime (2 ^ 6) T.index := Nat.Coprime.pow_left 6 h2k
    have h192 : T.index ∣ 3 * 2 ^ 6 := by norm_num; exact hdvd
    have h3 : T.index ∣ 3 := Nat.Coprime.dvd_of_dvd_mul_right hc64.symm h192
    rcases (Nat.dvd_prime (by norm_num)).mp h3 with h | h
    · exact absurd h hne1
    · exact h
  have h1 := Subgroup.card_mul_index T
  rw [hcardL2, hTindex] at h1
  have hcardT : Nat.card T = 64 := by omega
  rw [← hcardT]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ L2 ≤ L2)).toEquiv.symm

theorem dsucp_card_comap {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (f : ↥L →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (H : Subgroup (alternatingGroup (Fin 5))) :
    Nat.card ↥(H.comap f) * H.index = Nat.card ↥L := by
  rw [← Subgroup.index_comap_of_surjective (H := H) hf]
  exact Subgroup.card_mul_index _

theorem dsucp_index_K4 : CFSG.Quasithin.A5Model.K4.index = 15 := by
  have h := CFSG.Quasithin.A5Model.K4.card_mul_index
  rw [CFSG.Quasithin.A5Model.card_K4, CFSG.Quasithin.A5Model.card_A5] at h
  omega

theorem dsucp_index_A4s : CFSG.Quasithin.A5Model.A4s.index = 5 := by
  have h := CFSG.Quasithin.A5Model.A4s.card_mul_index
  rw [dsucp_card_A4s, CFSG.Quasithin.A5Model.card_A5] at h
  omega


theorem dsucp_cards_frame {G : Type} [Group G] [Finite G] {L1 S : Subgroup G}
    (α : ↥L1 →* alternatingGroup (Fin 5)) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L1) (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16)
    (g : alternatingGroup (Fin 5))
    (hKS : ∀ m : ↥L1, (m : G) ∈ S ↔ g * α m * g⁻¹ ∈ CFSG.Quasithin.A5Model.K4)
    (hNS : ∀ m : ↥L1, (m : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((g : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        (g : Equiv.Perm (Fin 5))⁻¹) 4 = 4) :
    Nat.card ↥(S.subgroupOf L1) = 64 ∧
      Nat.card ↥((L1 ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L1) = 192 := by
  classical
  have hker : Nat.card α.ker = 16 := by
    rw [hαk, ← hE16]
    exact (Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥L1) (f := L1.subtype)
      (Subgroup.subtype_injective L1)).symm
  have hrange : α.range = ⊤ := MonoidHom.range_eq_top.mpr hαs
  have hL1 : Nat.card ↥L1 = 960 := by
    have h1 := Subgroup.card_ker_mul_card_range α
    rw [hker, hrange, Subgroup.card_top, CFSG.Quasithin.A5Model.card_A5] at h1
    omega
  set ρ' : ↥L1 →* alternatingGroup (Fin 5) := (MulAut.conj g).toMonoidHom.comp α with hρ'
  have hρ'surj : Function.Surjective ρ' := by
    intro y
    obtain ⟨m, hm⟩ := hαs (g⁻¹ * y * g)
    refine ⟨m, ?_⟩
    simp only [hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hm]
    group
  have hρ'app : ∀ m : ↥L1, ((ρ' m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      (g : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        (g : Equiv.Perm (Fin 5))⁻¹ := by
    intro m
    simp [hρ', MulAut.conj_apply]
  have hTl : S.subgroupOf L1 = CFSG.Quasithin.A5Model.K4.comap ρ' := by
    ext m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hKS m]
    simp [hρ', MulAut.conj_apply]
  have hBl : (L1 ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L1 =
      CFSG.Quasithin.A5Model.A4s.comap ρ' := by
    ext m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, CFSG.Quasithin.A5Model.mem_A4s, hρ'app m,
      ← hNS m]
    constructor
    · intro h
      exact (Subgroup.mem_inf.mp h).2
    · intro h
      exact Subgroup.mem_inf.mpr ⟨m.2, h⟩
  have hT := dsucp_card_comap ρ' hρ'surj CFSG.Quasithin.A5Model.K4
  have hB := dsucp_card_comap ρ' hρ'surj CFSG.Quasithin.A5Model.A4s
  rw [dsucp_index_K4, hL1] at hT
  rw [dsucp_index_A4s, hL1] at hB
  rw [hTl, hBl]
  omega

theorem dsucp_comm {G : Type} [Group G] {L1 B : Subgroup G} (hB : B ≤ L1)
    (e : ↥L1 ≃* U42.Mof (alternatingGroup (Fin 5)))
    (hBe : ∀ m : ↥L1, (m : G) ∈ B ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Bc)
    (m : ↥L1) (hm : ((e m : U42.Mof _) : U42.Mc) ∈ U42.U0) : (m : G) ∈ ⁅B, B⁆ := by
  classical
  set B' : Subgroup ↥L1 := B.subgroupOf L1 with hB'
  set BM : Subgroup (U42.Mof (alternatingGroup (Fin 5))) := B'.map e.toMonoidHom with hBM
  have hBM_map : BM.map (U42.Mof (alternatingGroup (Fin 5))).subtype = U42.Bc := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨m, hmB, rfl⟩ := Subgroup.mem_map.mp hy
      exact (hBe m).mp (Subgroup.mem_subgroupOf.mp hmB)
    · intro hx
      have hxM : x ∈ U42.Mof (alternatingGroup (Fin 5)) := by
        rw [U42.mem_Mof]
        exact Equiv.Perm.mem_alternatingGroup.mpr hx.1
      set xM : ↥(U42.Mof (alternatingGroup (Fin 5))) := ⟨x, hxM⟩ with hxM_def
      refine ⟨xM, ?_, rfl⟩
      obtain ⟨m, hm'⟩ : ∃ m : ↥L1, e m = xM := ⟨e.symm xM, e.apply_symm_apply xM⟩
      refine Subgroup.mem_map.mpr ⟨m, Subgroup.mem_subgroupOf.mpr ((hBe m).mpr ?_), hm'⟩
      rw [show ((e m : U42.Mof _) : U42.Mc) = x by rw [hm']]
      exact hx
  set φ : ↥L1 →* U42.Mc := (U42.Mof (alternatingGroup (Fin 5))).subtype.comp e.toMonoidHom with hφ
  have hφB' : B'.map φ = U42.Bc := by
    rw [← hBM_map, hBM, Subgroup.map_map]
  have hcomm : (⁅B', B'⁆ : Subgroup ↥L1).map φ = ⁅U42.Bc, U42.Bc⁆ := by
    rw [Subgroup.map_commutator, hφB']
  have hmem : ((e m : U42.Mof _) : U42.Mc) ∈ (⁅B', B'⁆ : Subgroup ↥L1).map φ := by
    rw [hcomm]
    exact U42.U0_le_comm_Bc hm
  obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hmem
  have hxe : x = m := by
    have h1 : e x = e m := Subtype.ext hxm
    exact e.injective h1
  have hmB' : m ∈ ⁅B', B'⁆ := hxe ▸ hx
  have hmapB : B'.map L1.subtype = B := by
    rw [hB', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB]
  have hcomm2 : (⁅B', B'⁆ : Subgroup ↥L1).map L1.subtype = ⁅B, B⁆ := by
    rw [Subgroup.map_commutator, hmapB]
  have hmem2 : (m : G) ∈ (⁅B', B'⁆ : Subgroup ↥L1).map L1.subtype :=
    Subgroup.mem_map.mpr ⟨m, hmB', rfl⟩
  rw [hcomm2] at hmem2
  exact hmem2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement
open CFSG.Quasithin.A5Model
open CFSG.GH74.QTGen4.U42

theorem dsucp_inf_B_L2 {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) (hS : S ≤ L1) (hs3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hpc : pCoreOf 2 L2 ≤ S ⊓ L2) (hQ2c : Nat.card ↥(pCoreOf 2 L2) = 32)
    (hb2 : borelOf L2 S ≤ S) (hBeq : bigB L1 L2 S = L1 ⊓ Subgroup.normalizer (S : Set G)) :
    bigB L1 L2 S ⊓ L2 = S ⊓ L2 := by
  apply le_antisymm
  · rintro x ⟨hxB, hxL2⟩
    rw [hBeq] at hxB
    have hxN : x ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hxB.2 y).mp hy1,
          L2.mul_mem (L2.mul_mem hxL2 hy2) (L2.inv_mem hxL2)⟩
      · rintro ⟨hy1, hy2⟩
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxB.2) (x * y * x⁻¹)).mp
            (by simpa [mul_assoc] using hy1)
          simpa [mul_assoc] using this
        · have := L2.mul_mem (L2.mul_mem (L2.inv_mem hxL2) hy2) hxL2
          simpa [mul_assoc] using this
    exact dsucp_normalizer_sylow h.hyp.h2.sylow hs3.some hpc hQ2c x hxL2 hxN
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [hBeq]
    exact ⟨hS hx.1, (Subgroup.le_normalizer : S ≤ Subgroup.normalizer (S : Set G)) hx.1⟩


theorem dsucp_main {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) (hS : S ≤ L1)
    (hs3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hb6 : F112B6Loc L2 L1)
    (hE1 : pCoreOf 2 L1 = dsQ L1 L2 S) (hEZ : dsQ L1 L2 S = dsZi L1 S)
    (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16)
    (hQ2 : pCoreOf 2 L2 = dsQ L2 L1 S) (hQ2c : Nat.card ↥(pCoreOf 2 L2) = 32)
    (hQQ : dsQ L1 L2 S ⊔ dsQ L2 L1 S = S) (hnotZ : ¬ dsZi L1 S ≤ dsQ L2 L1 S)
    (hsylS : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S))
    (hsylS2 : IsSylowTwoOf S (L2 ⊔ bigB L2 L1 S)) :
    ∃ e : ↥(L1 ⊔ bigB L1 L2 S) ≃* U42.Mof (alternatingGroup (Fin 5)),
      (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ L2 ⊔ bigB L1 L2 S ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Bc) ∧
      (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ S ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Tc) ∧
      (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ pCoreOf 2 L2 ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.U0) ∧
      U42.PairCore (L2 ⊔ bigB L1 L2 S) ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)) S (pCoreOf 2 L2) ∧
      pCoreOf 2 L2 ≤ ⁅(L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S), (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)⁆ := by
  classical
  obtain ⟨-, -, hbl, -, -, halt⟩ := hb6
  have hblk : CFSG.QuasithinUnique.blockU L1 ≤ pCoreOf 2 L1 := hbl.1.2.2.1.1.trans inf_le_left
  obtain ⟨α, ψ, hαs, hαk, hψ⟩ := dsucp_frame_psi halt hblk hE16
  have hdsQ1 : dsQ L1 L2 S ≤ S := by
    calc dsQ L1 L2 S ≤ dsQ L1 L2 S ⊔ dsQ L2 L1 S := le_sup_left
      _ = S := hQQ
  have hdsQ2 : dsQ L2 L1 S ≤ S := by
    calc dsQ L2 L1 S ≤ dsQ L1 L2 S ⊔ dsQ L2 L1 S := le_sup_right
      _ = S := hQQ
  have hpcL1S : pCoreOf 2 L1 ≤ S := by rw [hE1]; exact hdsQ1
  have hQ2S : pCoreOf 2 L2 ≤ S := by rw [hQ2]; exact hdsQ2
  have hpcS2 : pCoreOf 2 L2 ≤ S ⊓ L2 := le_inf hQ2S (dsucp_pCoreOf_le L2)
  have hb2 : borelOf L2 S ≤ S := by
    intro x hx
    obtain ⟨hxL2, hxN⟩ := hx
    exact (dsucp_normalizer_sylow h.hyp.h2.sylow hs3.some hpcS2 hQ2c x hxL2 hxN).1
  have hP1 : L1 ⊔ bigB L1 L2 S = L1 := dsucp_P1_eq hS hb2
  have hBeq : bigB L1 L2 S = L1 ⊓ Subgroup.normalizer (S : Set G) := dsucp_bigB_eq hS hb2
  have hPB : (L2 ⊔ bigB L1 L2 S) ⊓ L1 = bigB L1 L2 S := by
    have := CFSG.Quasithin.F1.parabolic_inf_parabolic h
    rw [hP1] at this
    rw [inf_comm]
    exact this
  have hBL2 : bigB L1 L2 S ⊓ L2 = S ⊓ L2 :=
    dsucp_inf_B_L2 h hS hs3 hpcS2 hQ2c hb2 hBeq
  have hsylS1 : IsSylowTwoOf S L1 := by
    have := hsylS
    rw [hP1] at this
    exact this
  rw [bigB_comm] at hsylS2
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (CFSG.Quasithin.F1.bigB_le_normalizer_left h).2
  have hQ2eq : pCoreOf 2 L2 = pCoreOf 2 (L2 ⊔ bigB L2 L1 S) := hQ2
  have hP2N : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((pCoreOf 2 L2 : Subgroup G) : Set G) := by
    have h1 : L2 ⊔ bigB L1 L2 S ≤
        Subgroup.normalizer ((pCoreOf 2 (L2 ⊔ bigB L2 L1 S) : Subgroup G) : Set G) := by
      rw [bigB_comm]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    rw [hQ2eq]
    exact h1
  have hNQ : ∀ b ∈ L2 ⊔ bigB L1 L2 S, ∀ q ∈ pCoreOf 2 L2, b * q * b⁻¹ ∈ pCoreOf 2 L2 := by
    intro b hb q hq
    exact (Subgroup.mem_normalizer_iff.mp (hP2N hb) q).mp hq
  have hBQ : ∀ b : G, b ∈ bigB L1 L2 S → ∀ q : G, q ∈ pCoreOf 2 L2 → b * q * b⁻¹ ∈ pCoreOf 2 L2 :=
    fun b hb q hq => hNQ b ((le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hb) q hq
  set T : Subgroup ↥L1 := S.subgroupOf L1 with hT
  have hVT : (pCoreOf 2 L1).subgroupOf L1 ≤ T := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hpcL1S (Subgroup.mem_subgroupOf.mp hy))
  have hkerT : α.ker ≤ T := by
    rw [hαk]
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hpcL1S ((CFSG.Quasithin.F1.mem_pCore_iff_coe y).mp hy))
  have hTp : IsPGroup 2 ↥T := hsylS1.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hTi : ¬ 2 ∣ T.index := hsylS1.2.2
  have hT0p : IsPGroup 2 (T.map α) := hTp.map α
  have hT0i : ¬ 2 ∣ (T.map α).index := by
    rw [Subgroup.index_map_eq T hαs hkerT]
    exact hTi
  obtain ⟨g, hg⟩ := dsucp_sylow_K4 (T.map α) hT0p hT0i
  set C := dsucp_coords α ψ hαk hψ g with hC
  have hρval : ∀ m : ↥L1, C.ρ m = (g : Equiv.Perm (Fin 5)) *
      ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * (g : Equiv.Perm (Fin 5))⁻¹ :=
    fun m => rfl
  have hρT : ∀ t ∈ T, CFSG.Quasithin.H13.A5.InK4 (C.ρ t) := by
    intro t ht
    have h1 : α t ∈ T.map α := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have h2 := (hg (α t)).mp h1
    rw [hρval]
    have h3 := (CFSG.Quasithin.A5Model.mem_K4).mp h2
    have h4 : ((g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        ((α t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        ((g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ =
        ((g * α t * g⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
      simp
    rw [h4]
    exact h3
  have hK4 : ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k → ∃ t ∈ T, C.ρ t = k := by
    intro k hk
    have hkA : k ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr (sign_klein k hk)
    have hk'K : (⟨k, hkA⟩ : alternatingGroup (Fin 5)) ∈ CFSG.Quasithin.A5Model.K4 :=
      CFSG.Quasithin.A5Model.mem_K4.mpr hk
    have hx := (hg (g⁻¹ * ⟨k, hkA⟩ * g)).mpr (by
      rw [show g * (g⁻¹ * ⟨k, hkA⟩ * g) * g⁻¹ = ⟨k, hkA⟩ by group]
      exact hk'K)
    obtain ⟨t, ht, hαt⟩ := Subgroup.mem_map.mp hx
    refine ⟨t, ht, ?_⟩
    rw [hρval, hαt]
    show (g : Equiv.Perm (Fin 5)) * ((g⁻¹ * ⟨k, hkA⟩ * g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
      (g : Equiv.Perm (Fin 5))⁻¹ = k
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨e, he_ρ, he_V⟩ := dsucp_e α hαs ψ hαk hψ g T hVT hTp hTi hρT hK4
  have hker : ∀ m : ↥L1, C.ρ m = 1 → (m : G) ∈ S := by
    intro m hm
    have hmV : m ∈ C.V := by
      rw [← C.ker_ρ]
      exact MonoidHom.mem_ker.mpr hm
    exact hpcL1S (Subgroup.mem_subgroupOf.mp hmV)
  have hρS : ∀ m : ↥L1, (m : G) ∈ S → CFSG.Quasithin.H13.A5.InK4 (C.ρ m) :=
    fun m hm => hρT m (Subgroup.mem_subgroupOf.mpr hm)
  have hsurj : ∀ k : Equiv.Perm (Fin 5), CFSG.Quasithin.H13.A5.InK4 k →
      ∃ m : ↥L1, (m : G) ∈ S ∧ C.ρ m = k := by
    intro k hk
    obtain ⟨t, ht, hte⟩ := hK4 k hk
    exact ⟨t, Subgroup.mem_subgroupOf.mp ht, hte⟩
  have hsgn : ∀ m : ↥L1, (C.ρ m).sign = 1 := by
    intro m
    rw [hρval]
    have h1 : ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)).sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (α m).2
    have h2 : ((g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)).sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp g.2
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, h1, h2]
    simp
  have K1 := dsucp_K1 hker hρS hsurj
  have K2 := dsucp_K2 hS hsgn K1 hsurj
  have hmB : ∀ m : ↥L1, (m : G) ∈ L2 ⊔ bigB L1 L2 S ↔ (m : G) ∈ bigB L1 L2 S := by
    intro m
    constructor
    · intro hm
      have hmm : (m : G) ∈ (L2 ⊔ bigB L1 L2 S) ⊓ L1 := ⟨hm, m.2⟩
      rwa [hPB] at hmm
    · intro hm
      exact (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hm
  have hc1 : ∀ m : ↥L1, (m : G) ∈ L2 ⊔ bigB L1 L2 S ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Bc := by
    intro m
    rw [hmB m, hBeq]
    have hBc : ((e m : U42.Mof _) : U42.Mc) ∈ U42.Bc ↔ (C.ρ m) 4 = 4 := by
      show ((e m : U42.Mof _) : U42.Mc).right.sign = 1 ∧ ((e m : U42.Mof _) : U42.Mc).right 4 = 4 ↔ _
      rw [he_ρ m]
      exact ⟨fun h' => h'.2, fun h' => ⟨hsgn m, h'⟩⟩
    rw [hBc]
    exact ⟨fun h' => (K2 m).mp h'.2, fun h' => ⟨m.2, (K2 m).mpr h'⟩⟩
  have hc2 : ∀ m : ↥L1, (m : G) ∈ S ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Tc := by
    intro m
    have hTc : ((e m : U42.Mof _) : U42.Mc) ∈ U42.Tc ↔
        CFSG.Quasithin.H13.A5.InK4 (C.ρ m) := by
      show CFSG.Quasithin.H13.A5.InK4 (((e m : U42.Mof _) : U42.Mc).right) ↔ _
      rw [he_ρ m]
    rw [hTc]
    exact K1 m
  have hBe : ∀ m : ↥L1, (m : G) ∈ bigB L1 L2 S ↔ ((e m : U42.Mof _) : U42.Mc) ∈ U42.Bc :=
    fun m => (hmB m).symm.trans (hc1 m)
  have hEw : ∀ v : ↥((pCoreOf 2 L1).subgroupOf L1),
      ((e v : U42.Mof _) : U42.Mc) ∈ U42.Wc := fun v =>
    MonoidHom.mem_range.mpr ⟨C.ψ v, (he_V v).symm⟩
  have hnotE : ¬ pCoreOf 2 L1 ≤ pCoreOf 2 L2 := by
    intro hle
    apply hnotZ
    rw [← hEZ, ← hE1, ← hQ2]
    exact hle
  have hU0 := dsucp_U0 hS hQ2S hQ2c hBQ hnotE (dsucp_pCoreOf_le L1) e hBe hc2 hEw
  have hBle : bigB L1 L2 S ≤ L1 := by
    rw [hBeq]
    exact inf_le_left
  have hsup := dsucp_card_sup hBN
  have hcards := dsucp_L2_cards h.hyp.h2.sylow hs3.some hpcS2 hQ2c
  have hKS : ∀ m : ↥L1, (m : G) ∈ S ↔ g * α m * g⁻¹ ∈ CFSG.Quasithin.A5Model.K4 := by
    intro m
    rw [K1 m]
    have h4 : C.ρ m = ((g * α m * g⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
      rw [hρval]
      simp
    rw [h4]
    exact CFSG.Quasithin.A5Model.mem_K4.symm
  have hNS : ∀ m : ↥L1, (m : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((g : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        (g : Equiv.Perm (Fin 5))⁻¹) 4 = 4 := by
    intro m
    rw [← hρval m]
    exact K2 m
  have hcardsF := dsucp_cards_frame α hαs hαk hE16 g hKS hNS
  have hcardB : Nat.card ↥(bigB L1 L2 S) = 192 := by
    rw [hBeq]
    rw [← hcardsF.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv.symm
  have hcardS : Nat.card ↥S = 64 := by
    rw [← hcardsF.1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv.symm
  have hcardP2 : Nat.card ↥(L2 ⊔ bigB L1 L2 S) = 576 := by
    have hsup' := hsup
    rw [sup_comm, hBL2, hcards.2, hcards.1, hcardB] at hsup'
    omega
  have hBle' : bigB L1 L2 S ≤ L1 := hBle
  rw [hP1, hPB]
  refine ⟨e, hc1, hc2, hU0, ?_, ?_⟩
  · refine ⟨hQ2S, ?_, le_sup_right, hNQ, hsylS1.2.1, hsylS2.2.2, ?_, ?_⟩
    · rw [hBeq]
      exact le_inf hS Subgroup.le_normalizer
    · intro h' hh hcomm
      have hH : h' ∈ L2 ⊔ bigB L2 L1 S := by
        rw [bigB_comm]
        exact hh
      have hcen : h' ∈ Subgroup.centralizer
          ((pCoreOf 2 (L2 ⊔ bigB L2 L1 S) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hu' : u ∈ pCoreOf 2 L2 := by
          rw [hQ2eq]
          exact hu
        exact (hcomm u hu').symm
      have hmem := (CFSG.Quasithin.F1.parabolic_charTwo h.symm) (Subgroup.mem_inf.mpr ⟨hH, hcen⟩)
      rw [hQ2eq]
      exact hmem
    · rw [hcardP2, hcardS]
  · intro q hq
    have hqL1 : q ∈ L1 := hS (hQ2S hq)
    exact dsucp_comm hBle' e hBe ⟨q, hqL1⟩ ((hU0 ⟨q, hqL1⟩).mp hq)

theorem leafUAmalCoordsPlain [DSLeaf LeafDSBReduce] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafDSBUQQ] [DSLeaf LeafDSBUQ1] [DSLeaf LeafDSBUQ2] [DSLeaf LeafZiChief] [DSLeaf LeafM2] [DSLeaf LeafM3] [DSLeaf LeafM5] [DSLeaf LeafFaithfulA5] [DSLeaf LeafFrattiniChief] [DSLeaf LeafAlt5OfOrth] [DSLeaf LeafSylowS] [DSLeaf LeafDSBJQ2] : LeafUAmalCoordsPlain := by
  intro G _ _ L1 L2 S h hns hs3 hb6 hS
  have hDSB0 : DSBHyp0 L1 L2 S := ⟨h, hns, hs3⟩
  have hDSBr := dsb_reduce hDSB0
  have hSred : (S ⊓ L1) ⊔ (S ⊓ L2) = S := by
    rw [inf_eq_left.mpr hS]
    exact sup_eq_left.mpr inf_le_left
  have hDSB : DSBHyp L1 L2 S := by
    rw [hSred] at hDSBr
    exact hDSBr
  have hU : ⁅dsZi L1 S, L1⁆ ≠ ⊥ := by
    intro hJ
    obtain ⟨-, hc⟩ := dsbjq2 hDSB hJ
    obtain ⟨-, hsp, -⟩ := hb6
    have hcard : Nat.card ↥(pCoreOf 2 L2) = 2 ^ (1 + 2 * 2) := hsp.2.1
    rw [hc] at hcard
    norm_num at hcard
  obtain ⟨hE1, hEZ, -, -, hE16, -, -, -⟩ := dsbuq1 hDSB hU
  obtain ⟨hQ2, -, hsp2⟩ := dsbuq2 hDSB hU
  obtain ⟨hQQ, -, hnotZ⟩ := dsbuqq hDSB hU
  obtain ⟨-, hsylP1, -⟩ := sylow_s h
  obtain ⟨-, hsylP2, -⟩ := sylow_s h.symm
  have hQ2c : Nat.card ↥(pCoreOf 2 L2) = 32 := by
    have h32 : Nat.card ↥(pCoreOf 2 L2) = 2 ^ (1 + 2 * 2) := hsp2.2.1
    rw [h32]
    norm_num
  exact dsucp_main h hS hs3 hb6 hE1 hEZ hE16 hQ2 hQ2c hQQ hnotZ hsylP1 hsylP2


end CFSG.GH74.QTGen4.DSGen4
