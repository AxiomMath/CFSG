module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDC

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Final.Thm6.L20 (PairShape)
open scoped commutatorElement

section Perfect

variable {X : Type*} [Group X] [Finite X]

theorem exists_perfect_of_not_isSolvable (h : ¬ Group.IsSolvable X) :
    ∃ D : Subgroup X, ⁅D, D⁆ = D ∧ D ≠ ⊥ := by
  classical
  have hex : ∃ m : ℕ, ∃ n : ℕ, Nat.card ↥(derivedSeries X n) = m := ⟨_, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  refine ⟨derivedSeries X n, ?_, fun hbot => h ⟨n, hbot⟩⟩
  have hle : ⁅derivedSeries X n, derivedSeries X n⁆ ≤ derivedSeries X n :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hmin := Nat.find_min' hex ⟨n + 1, rfl⟩
  rw [← hn, derivedSeries_succ] at hmin
  exact Subgroup.eq_of_le_of_card_ge hle hmin

theorem exists_perfect_le_of_not_isSolvable {W : Subgroup X} (h : ¬ Group.IsSolvable ↥W) :
    ∃ D : Subgroup X, D ≤ W ∧ ⁅D, D⁆ = D ∧ D ≠ ⊥ := by
  obtain ⟨D, hD, hne⟩ := exists_perfect_of_not_isSolvable h
  refine ⟨D.map W.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hD]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective]

omit [Finite X] in
theorem perfect_subgroupOf {A K : Subgroup X} (hAK : A ≤ K) (hA : ⁅A, A⁆ = A) :
    ⁅A.subgroupOf K, A.subgroupOf K⁆ = A.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAK, hA]

end Perfect

theorem perfect_lift {M N : Type*} [Group M] [Finite M] [Group N] (f : M →* N)
    (hf : Function.Surjective f) {Q : Subgroup N} (hQ : ⁅Q, Q⁆ = Q) :
    ∃ P : Subgroup M, ⁅P, P⁆ = P ∧ P.map f = Q := by
  classical
  have hex : ∃ n : ℕ, ∃ P : Subgroup M, P.map f = Q ∧ Nat.card ↥P = n :=
    ⟨_, Q.comap f, Subgroup.map_comap_eq_self_of_surjective hf Q, rfl⟩
  obtain ⟨P, hPQ, hPn⟩ := Nat.find_spec hex
  refine ⟨P, ?_, hPQ⟩
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  have himg : (⁅P, P⁆).map f = Q := by rw [Subgroup.map_commutator, hPQ, hQ]
  have hmin := Nat.find_min' hex (m := Nat.card ↥⁅P, P⁆) ⟨⁅P, P⁆, himg, rfl⟩
  rw [← hPn] at hmin
  exact Subgroup.eq_of_le_of_card_ge hle hmin

theorem exists_perfect_lift_centralizer {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    [N.Normal] (hN : Odd (Nat.card ↥N)) {a : K} (ha : orderOf a = 2) {D : Subgroup (K ⧸ N)}
    (hD : ⁅D, D⁆ = D) (hDa : D ≤ centralizer ({QuotientGroup.mk' N a} : Set (K ⧸ N))) :
    ∃ P : Subgroup K, P ≤ centralizer ({a} : Set K) ∧ ⁅P, P⁆ = P ∧
      P.map (QuotientGroup.mk' N) = D := by
  set A : Subgroup K := centralizer ({a} : Set K) ⊓ D.comap (QuotientGroup.mk' N) with hA
  have hcen := CFSG.ProperTwoGeneratedCore.Assembly.map_centralizer_eq hN ha
  let g : ↥A →* ↥D :=
    ((QuotientGroup.mk' N).comp A.subtype).codRestrict D (fun x => x.2.2)
  have hg : Function.Surjective g := by
    rintro ⟨d, hd⟩
    have hd' : d ∈ (centralizer ({a} : Set K)).map (QuotientGroup.mk' N) := hcen ▸ hDa hd
    obtain ⟨c, hc, rfl⟩ := hd'
    exact ⟨⟨c, hc, hd⟩, rfl⟩
  have htop : ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ = (⊤ : Subgroup ↥D) := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hD]
  obtain ⟨P₀, hP₀, hmap⟩ := perfect_lift g hg htop
  refine ⟨P₀.map A.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  · rw [← Subgroup.map_commutator, hP₀]
  · have e : (P₀.map A.subtype).map (QuotientGroup.mk' N) = (P₀.map g).map D.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [e, hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_conj_mem_of_sylow {G : Type*} [Group G] [Finite G] {K T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T K) {y : G} (hy : y ∈ K) (hy2 : y * y = 1) :
    ∃ h ∈ K, h * y * h⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hT
  have hZ : IsPGroup 2 (Subgroup.zpowers (⟨y, hy⟩ : K)) := by
    have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy2)
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf y ∣ 2 ^ 1 from hd)
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk']
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨y, hy⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩

section Conj

variable {X : Type*} [Group X]

theorem conjugate_one (H : Subgroup X) : conjugate H 1 = H := by
  unfold conjugate
  ext x
  simp

theorem conjugate_inv_of_eq {H K : Subgroup X} {g : X} (h : conjugate H g = K) :
    conjugate K g⁻¹ = H := by
  rw [← h, conjugate_conjugate_eq, mul_inv_cancel, conjugate_one]

theorem conj_mem_of_conjugate_eq {H K : Subgroup X} {g : X} (h : conjugate K g = H) :
    ∀ a ∈ H, g * a * g⁻¹ ∈ K := by
  intro a ha
  rw [← h] at ha
  obtain ⟨b, hb, hba⟩ := ha
  have e : g * a * g⁻¹ = b := by
    rw [← hba]
    simp [mul_assoc]
  rw [e]
  exact hb

theorem mem_normalizer_of_conjugate_eq {K : Subgroup X} {g : X} (h : conjugate K g = K) :
    g ∈ normalizer (K : Set X) := by
  have h' : g⁻¹ ∈ normalizer (K : Set X) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  simpa using inv_mem h'

theorem sup_le_normalizer_left {K K' : Subgroup X} (hc : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) :
    K ⊔ K' ≤ normalizer (K : Set X) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← hc a ha b hb, mul_inv_cancel_right]
    exact ha
  · intro ha
    have e : a = b * a * b⁻¹ := by
      have := hc _ ha b hb
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [← this]; group
        _ = b * a * b⁻¹ := by group
    rw [e]
    exact ha

end Conj

section Pair

variable {Q : Type} [Group Q] [Finite Q] {L₁ L₂ : Subgroup Q}

theorem conjugate_dichotomy (h : PairShape L₁ L₂) (g : Q) :
    (conjugate L₁ g = L₁ ∧ conjugate L₂ g = L₂) ∨
      (conjugate L₁ g = L₂ ∧ conjugate L₂ g = L₁) := by
  have hc : ∀ {K : Subgroup Q}, IsComponent K → IsComponent (conjugate K g) := fun hK =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hK
  have hne : conjugate L₁ g ≠ conjugate L₂ g := fun he =>
    h.ne (Subgroup.map_injective (MulAut.conj g⁻¹).injective he)
  rcases h.comps _ (hc h.c₁) with h1 | h1 <;> rcases h.comps _ (hc h.c₂) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem mem_normalizer_sup (h : PairShape L₁ L₂) (g : Q) :
    g ∈ normalizer ((L₁ ⊔ L₂ : Subgroup Q) : Set Q) := by
  apply mem_normalizer_of_conjugate_eq
  have e : conjugate (L₁ ⊔ L₂) g = conjugate L₁ g ⊔ conjugate L₂ g := Subgroup.map_sup _ _ _
  rcases conjugate_dichotomy h g with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [e, h1, h2]
  · rw [e, h1, h2, sup_comm]

end Pair

variable {G : Type} [Group G] [Finite G] {z : G}

theorem swaps_conj_of_mem {L₁ L₂ : Subgroup (CentralizerBar z)} (h : PairShape L₁ L₂)
    {y d : G} (hsw : Swaps z y L₁ L₂) (hdC : d ∈ Cen z) : Swaps z (d * y * d⁻¹) L₁ L₂ := by
  obtain ⟨hyC, h1, h2⟩ := hsw
  have hC : d * y * d⁻¹ ∈ Cen z :=
    (Cen z).mul_mem ((Cen z).mul_mem hdC hyC) ((Cen z).inv_mem hdC)
  have e : toBar z ⟨d * y * d⁻¹, hC⟩ =
      toBar z ⟨d, hdC⟩ * toBar z ⟨y, hyC⟩ * (toBar z ⟨d, hdC⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨hC, ?_, ?_⟩ <;> rw [e, ← conjugate_conjugate_eq, ← conjugate_conjugate_eq] <;>
    rcases conjugate_dichotomy h (toBar z ⟨d, hdC⟩) with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
  · rw [hd1, h1, conjugate_inv_of_eq hd2]
  · rw [hd1, h2, conjugate_inv_of_eq hd2]
  · rw [hd2, h2, conjugate_inv_of_eq hd1]
  · rw [hd2, h1, conjugate_inv_of_eq hd1]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
