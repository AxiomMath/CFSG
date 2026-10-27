module

public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public section

namespace CFSG.GH74.Generic

open Subgroup
open scoped commutatorElement

theorem not_sectionalTwoRankLE_of_elementary {A : Type*} [Group A] [Finite A] (r : ℕ)
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (hcard : 2 ^ r < Nat.card A) : ¬ SectionalTwoRankLE A r := by
  intro h
  have hE : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup A) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun x _ => hsq x⟩
  have := SectionalTwoRankLE.card_le_of_elementary h ⊤ hE
  rw [Subgroup.card_top] at this
  omega

theorem not_sectionalTwoRankLE_of_surjection {G K A : Type*} [Group G] [Group K] [Finite K]
    [Group A] (r : ℕ) (α : K →* G) (β : K →* A) (hβ : Function.Surjective β)
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (hcard : 2 ^ r < Nat.card A) (hker : α.ker ≤ β.ker) : ¬ SectionalTwoRankLE G r := by
  intro hG
  have : Finite A := Finite.of_surjective β hβ
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  let P : Subgroup G := (S : Subgroup K).map α
  have hGP : SectionalTwoRankLE P r := SectionalTwoRankLE.subgroup P hG
  let f : (S : Subgroup K) →* P :=
    (α.comp (S : Subgroup K).subtype).codRestrict P fun s => ⟨s, s.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have : Finite P := Finite.of_surjective f hf
  have hA2 : IsPGroup 2 A := fun a => ⟨1, by simpa using hsq a⟩
  have hSβ : (⊤ : Subgroup A) = (S : Subgroup K).map β := by
    have h2 := (S.mapSurjective hβ).is_maximal' (hA2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h2
    exact h2
  let ψ : (S : Subgroup K) →* A := β.comp (S : Subgroup K).subtype
  have hψ : Function.Surjective ψ := by
    intro a
    have : a ∈ (S : Subgroup K).map β := hSβ ▸ Subgroup.mem_top a
    obtain ⟨s, hs, rfl⟩ := this
    exact ⟨⟨s, hs⟩, rfl⟩
  have hkerψ : f.ker ≤ ψ.ker := by
    intro s hs
    have h1 : α s = 1 := by
      have h0 : f s = 1 := MonoidHom.mem_ker.1 hs
      exact congrArg Subtype.val h0
    exact hker (MonoidHom.mem_ker.2 h1)
  let φ : P →* A := (MonoidHom.liftOfSurjective f hf) ⟨ψ, hkerψ⟩
  have hφf : ∀ s, φ (f s) = ψ s := fun s => by
    simp [φ]
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    exact ⟨f s, hφf s⟩
  exact not_sectionalTwoRankLE_of_elementary r hcomm hsq hcard
    (SectionalTwoRankLE.of_surjective φ hφ hGP)

@[expose] def RankCertified (G : Type*) [Group G] (r : ℕ) : Prop :=
  ∃ (K A : Type) (_ : Group K) (_ : Finite K) (_ : Group A) (α : K →* G) (β : K →* A),
    Function.Surjective β ∧ (∀ a b : A, a * b = b * a) ∧ (∀ a : A, a ^ 2 = 1) ∧
      2 ^ r < Nat.card A ∧ α.ker ≤ β.ker

variable {G H : Type*} [Group G] [Group H] {r : ℕ}

theorem RankCertified.not_sectionalTwoRankLE (h : RankCertified G r) :
    ¬ SectionalTwoRankLE G r := by
  obtain ⟨K, A, _, _, _, α, β, hβ, hc, hs, hcard, hker⟩ := h
  exact not_sectionalTwoRankLE_of_surjection r α β hβ hc hs hcard hker

theorem RankCertified.not_gen4 (h : RankCertified G r) (hr : 4 ≤ r) : ¬ Gen4 G :=
  fun hG => h.not_sectionalTwoRankLE (hG.mono hr)

theorem RankCertified.mono (h : RankCertified G r) {s : ℕ} (hs : s ≤ r) : RankCertified G s := by
  obtain ⟨K, A, _, _, _, α, β, hβ, hc, hsq, hcard, hker⟩ := h
  exact ⟨K, A, inferInstance, inferInstance, inferInstance, α, β, hβ, hc, hsq,
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hs) hcard, hker⟩

theorem RankCertified.of_injective (h : RankCertified G r) (f : G →* H)
    (hf : Function.Injective f) : RankCertified H r := by
  obtain ⟨K, A, _, _, _, α, β, hβ, hc, hs, hcard, hker⟩ := h
  refine ⟨K, A, inferInstance, inferInstance, inferInstance, f.comp α, β, hβ, hc, hs, hcard, ?_⟩
  intro k hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hk
  exact hker (MonoidHom.mem_ker.2 (hf (by rw [hk, map_one])))

theorem RankCertified.of_mulEquiv (h : RankCertified G r) (e : G ≃* H) : RankCertified H r :=
  h.of_injective e.toMonoidHom e.injective

theorem RankCertified.of_subgroup {K : Subgroup G} (h : RankCertified K r) : RankCertified G r :=
  h.of_injective K.subtype K.subtype_injective

theorem RankCertified.of_surjective {H : Type} [Group H] [Finite H] (h : RankCertified G r)
    (π : H →* G) (hπ : Function.Surjective π) : RankCertified H r := by
  obtain ⟨K, A, _, _, _, α, β, hβ, hc, hs, hcard, hker⟩ := h
  let P : Subgroup (K × H) := (α.comp (MonoidHom.fst K H)).eqLocus (π.comp (MonoidHom.snd K H))
  have hPfin : Finite P := inferInstance
  let α' : P →* H := (MonoidHom.snd K H).comp P.subtype
  let β' : P →* A := (β.comp (MonoidHom.fst K H)).comp P.subtype
  refine ⟨P, A, inferInstance, inferInstance, inferInstance, α', β', ?_, hc, hs, hcard, ?_⟩
  · intro a
    obtain ⟨k, rfl⟩ := hβ a
    obtain ⟨g, hg⟩ := hπ (α k)
    exact ⟨⟨(k, g), (hg.symm : α k = π g)⟩, rfl⟩
  · rintro ⟨⟨k, g⟩, hkg⟩ hp
    have hg : g = 1 := by simpa [α'] using hp
    have hk : α k = π g := hkg
    rw [hg, map_one] at hk
    have := hker (MonoidHom.mem_ker.2 hk)
    simpa [β'] using this

theorem RankCertified.of_quotient {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (h : RankCertified (H ⧸ N) r) : RankCertified H r :=
  h.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem rankCertified_of_commuting_involutions {r : ℕ} (u : Fin r → G)
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1)
    {s : ℕ} (hs : s < r) : RankCertified G s := by
  obtain ⟨f, hf⟩ := Filter.exists_injective_of_commuting_involutions u hsq hcomm hker
  refine ⟨Fin r → Multiplicative (ZMod 2), Fin r → Multiplicative (ZMod 2), inferInstance,
    inferInstance, inferInstance, f, MonoidHom.id _, Function.surjective_id,
    fun a b => mul_comm a b, ?_, ?_, ?_⟩
  · intro a
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    generalize Multiplicative.toAdd (a i) = z
    revert z
    decide
  · rw [Filter.card_pi_zmod_two]
    exact Nat.pow_lt_pow_right (by norm_num) hs
  · rw [(MonoidHom.ker_eq_bot_iff f).2 hf]
    exact bot_le

theorem rankCertified_of_section_involutions {G : Type} [Group G] [Finite G] {r : ℕ}
    (N : Subgroup G)
    (x : Fin r → G) (hnorm : ∀ i, x i ∈ Subgroup.normalizer (N : Set G)) (hsq : ∀ i, x i ^ 2 ∈ N)
    (hcomm : ∀ i j, ⁅x i, x j⁆ ∈ N)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ∉ N)
    {s : ℕ} (hs : s < r) : RankCertified G s := by
  classical
  set Q : Subgroup G := Subgroup.closure ((N : Set G) ∪ Set.range x) with hQ
  have hNQ : N ≤ Q := fun n hn => Subgroup.subset_closure (Or.inl hn)
  have hxQ : ∀ i, x i ∈ Q := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hQnorm : Q ≤ Subgroup.normalizer (N : Set G) := by
    rw [hQ, Subgroup.closure_le]
    rintro y (hy | ⟨i, rfl⟩)
    · exact Subgroup.le_normalizer hy
    · exact hnorm i
  have hN : (N.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNQ).2 hQnorm
  let y : Fin r → Q := fun i => ⟨x i, hxQ i⟩
  let π : Q →* Q ⧸ N.subgroupOf Q := QuotientGroup.mk' _
  let z : Fin r → Q ⧸ N.subgroupOf Q := fun i => π (y i)
  have hmem : ∀ q : Q, π q = 1 ↔ (q : G) ∈ N := fun q => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hz2 : ∀ i, z i ^ 2 = 1 := fun i => by
    show π (y i) ^ 2 = 1
    rw [← map_pow, hmem]
    exact hsq i
  have hzc : ∀ i j, Commute (z i) (z j) := fun i j => by
    show π (y i) * π (y j) = π (y j) * π (y i)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    change (x i * x j)⁻¹ * (x j * x i) ∈ N
    have hg : (x i * x j)⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (hnorm i) (hnorm j))
    have hc : (⁅x i, x j⁆)⁻¹ ∈ N := Subgroup.inv_mem _ (hcomm i j)
    have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hc
    have heq : (x i * x j)⁻¹ * (x j * x i) =
        (x i * x j)⁻¹ * ⁅x i, x j⁆⁻¹ * ((x i * x j)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact h1
  have key : ∀ (g : G) (hg : g ∈ Subgroup.closure ((N : Set G) ∪ Set.range x)),
      π ⟨g, hg⟩ ∈ Subgroup.closure (Set.range z) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | ⟨i, rfl⟩
      · have h1 : π ⟨g, Subgroup.subset_closure (Or.inl hg)⟩ = 1 := (hmem _).2 hg
        rw [h1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨i, rfl⟩
    | one =>
      have h1 : π ⟨1, Subgroup.one_mem _⟩ = 1 := map_one π
      rw [h1]
      exact Subgroup.one_mem _
    | mul g h hg hh ihg ihh =>
      have h1 : π ⟨g * h, Subgroup.mul_mem _ hg hh⟩ = π ⟨g, hg⟩ * π ⟨h, hh⟩ :=
        map_mul π ⟨g, hg⟩ ⟨h, hh⟩
      rw [h1]
      exact Subgroup.mul_mem _ ihg ihh
    | inv g hg ihg =>
      have h1 : π ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ = (π ⟨g, hg⟩)⁻¹ := map_inv π ⟨g, hg⟩
      rw [h1]
      exact Subgroup.inv_mem _ ihg
  have hgen : Subgroup.closure (Set.range z) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Q) a
    exact key q.1 q.2
  have hcommA : IsMulCommutative (Subgroup.closure (Set.range z)) :=
    Subgroup.isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hzc i j)
  have hAcomm : ∀ a b : Q ⧸ N.subgroupOf Q, a * b = b * a := fun a b => by
    have ha : a ∈ Subgroup.closure (Set.range z) := hgen ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.closure (Set.range z) := hgen ▸ Subgroup.mem_top b
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure (Set.range z)) ⟨b, hb⟩)
  have hAsq : ∀ a : Q ⧸ N.subgroupOf Q, a ^ 2 = 1 := fun a => by
    have ha : a ∈ Subgroup.closure (Set.range z) := hgen ▸ Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact hz2 i
    | one => exact one_pow 2
    | mul g h hg hh ihg ihh =>
      rw [(show Commute g h from hAcomm g h).mul_pow, ihg, ihh, one_mul]
    | inv g hg ihg => rw [inv_pow, ihg, inv_one]
  have hkerA : ∀ a : Fin r → Fin 2, a ≠ 0 →
      (List.ofFn fun i => z i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha h1
    apply hker a ha
    have h2 : π (List.ofFn fun i => y i ^ (a i : ℕ)).prod = 1 := by
      rw [map_list_prod, List.map_ofFn]
      simpa [Function.comp_def, z, map_pow] using h1
    have h3 := (hmem _).1 h2
    have h4 : ((List.ofFn fun i => y i ^ (a i : ℕ)).prod : Q).1 =
        (List.ofFn fun i => x i ^ (a i : ℕ)).prod := by
      simp [Function.comp_def, y]
    rwa [h4] at h3
  obtain ⟨f, hf⟩ := Filter.exists_injective_of_commuting_involutions z hz2 hzc hkerA
  have hcard : 2 ^ s < Nat.card (Q ⧸ N.subgroupOf Q) := by
    have := Nat.card_le_card_of_injective f hf
    rw [Filter.card_pi_zmod_two] at this
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hs) this
  refine ⟨↥Q, Q ⧸ N.subgroupOf Q, inferInstance, inferInstance, inferInstance, Q.subtype, π,
    QuotientGroup.mk'_surjective _, hAcomm, hAsq, hcard, ?_⟩
  rw [Subgroup.ker_subtype]
  exact bot_le

theorem rankCertified_of_central_section {G : Type} [Group G] [Finite G] {r : ℕ} (t : G)
    (ht : t ^ 2 = 1)
    (x : Fin r → G) (hc : ∀ i, x i * t = t * x i) (hsq : ∀ i, x i * x i = 1 ∨ x i * x i = t)
    (hcomm : ∀ i j, x i * x j = x j * x i ∨ x i * x j = t * (x j * x i))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 →
      (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 ∧ (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ t)
    {s : ℕ} (hs : s < r) : RankCertified G s := by
  have hN : ∀ y : G, y ∈ Subgroup.zpowers t ↔ y = 1 ∨ y = t := fun y => by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
        show t ^ (2 * m) = 1
        rw [zpow_mul, zpow_two, ← sq, ht, one_zpow]
      · right
        obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
        show t ^ (2 * m + 1) = t
        rw [zpow_add_one, zpow_mul, zpow_two, ← sq, ht, one_zpow, one_mul]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hconj : ∀ g : G, Commute t g → ∀ n ∈ Subgroup.zpowers t, g * n * g⁻¹ = n := by
    rintro g hg _ ⟨k, rfl⟩
    show g * t ^ k * g⁻¹ = t ^ k
    have hk : Commute (t ^ k) g := hg.zpow_left k
    rw [← hk.eq, mul_assoc, mul_inv_cancel, mul_one]
  refine rankCertified_of_section_involutions (Subgroup.zpowers t) x (fun i => ?_) (fun i => ?_)
    (fun i j => ?_) (fun a ha hmem => ?_) hs
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj _ (hc i).symm h hh]
      exact hh
    · intro hh
      have e : (x i)⁻¹ * (x i * h * (x i)⁻¹) * ((x i)⁻¹)⁻¹ = h := by group
      have h2 := hconj ((x i)⁻¹) (Commute.inv_right (show Commute t (x i) from (hc i).symm)) _ hh
      rw [e] at h2
      rw [h2]
      exact hh
  · rw [hN, sq]
    exact hsq i
  · rw [hN, commutatorElement_def]
    rcases hcomm i j with h | h
    · left
      rw [h]
      group
    · right
      rw [h]
      group
  · rw [hN] at hmem
    rcases hmem with h | h
    · exact (hker a ha).1 h
    · exact (hker a ha).2 h

theorem card_eq_two_pow_of_exponent_two {A : Type*} [Group A] [Finite A] (hsq : ∀ a : A, a ^ 2 = 1) :
    ∃ k : ℕ, Nat.card A = 2 ^ k :=
  (show IsPGroup 2 A from fun a => ⟨1, by simpa using hsq a⟩).exists_card_eq

theorem RankCertified.prod {X Y : Type*} [Group X] [Group Y] {a b : ℕ} (hX : RankCertified X a)
    (hY : RankCertified Y b) : RankCertified (X × Y) (a + b + 1) := by
  obtain ⟨K₁, A₁, _, _, _, α₁, β₁, hβ₁, hc₁, hs₁, hcard₁, hker₁⟩ := hX
  obtain ⟨K₂, A₂, _, _, _, α₂, β₂, hβ₂, hc₂, hs₂, hcard₂, hker₂⟩ := hY
  have : Finite A₁ := Finite.of_surjective β₁ hβ₁
  have : Finite A₂ := Finite.of_surjective β₂ hβ₂
  obtain ⟨k₁, hk₁⟩ := card_eq_two_pow_of_exponent_two hs₁
  obtain ⟨k₂, hk₂⟩ := card_eq_two_pow_of_exponent_two hs₂
  rw [hk₁] at hcard₁
  rw [hk₂] at hcard₂
  have h1 : a + 1 ≤ k₁ := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).1 hcard₁
  have h2 : b + 1 ≤ k₂ := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).1 hcard₂
  refine ⟨K₁ × K₂, A₁ × A₂, inferInstance, inferInstance, inferInstance, α₁.prodMap α₂,
    β₁.prodMap β₂, hβ₁.prodMap hβ₂, fun x y => Prod.ext (hc₁ _ _) (hc₂ _ _),
    fun x => Prod.ext (hs₁ _) (hs₂ _), ?_, ?_⟩
  · rw [Nat.card_prod, hk₁, hk₂, ← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rintro ⟨k₁', k₂'⟩ hk
    rw [MonoidHom.mem_ker] at hk
    have e1 : α₁ k₁' = 1 := congrArg Prod.fst hk
    have e2 : α₂ k₂' = 1 := congrArg Prod.snd hk
    exact MonoidHom.mem_ker.2 (Prod.ext (MonoidHom.mem_ker.1 (hker₁ (MonoidHom.mem_ker.2 e1)))
      (MonoidHom.mem_ker.1 (hker₂ (MonoidHom.mem_ker.2 e2))))

theorem RankCertified.of_central_involution {X : Type*} [Group X] {K : Subgroup X} {c : X}
    (hcc : ∀ x : X, x * c = c * x) (hc2 : c * c = 1) (hcK : c ∉ K)
    (h : RankCertified K r) : RankCertified X (r + 1) := by
  obtain ⟨Q, A, _, _, _, α, β, hβ, hc, hs, hcard, hker⟩ := h
  let E := Multiplicative (ZMod 2)
  let α' : Q × E →* X :=
    { toFun := fun p => ((α p.1 : K) : X) * c ^ (Multiplicative.toAdd p.2).val
      map_one' := by simp
      map_mul' := fun p p' => by
        have hpow : ∀ n : ℕ, Commute c ((α p.1 : K) : X) := fun _ => (hcc _).symm
        have hcomm : ((α p'.1 : K) : X) * c ^ (Multiplicative.toAdd p.2).val =
            c ^ (Multiplicative.toAdd p.2).val * ((α p'.1 : K) : X) :=
          ((Commute.pow_left (hcc _).symm _)).eq.symm
        have h2 : c ^ ((Multiplicative.toAdd (p * p').2).val) =
            c ^ (Multiplicative.toAdd p.2).val * c ^ (Multiplicative.toAdd p'.2).val := by
          have hc2' : c ^ 2 = 1 := by rw [sq]; exact hc2
          rw [Prod.snd_mul, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hc2', pow_add]
        calc ((α (p * p').1 : K) : X) * c ^ ((Multiplicative.toAdd (p * p').2).val)
            = ((α p.1 : K) : X) * ((α p'.1 : K) : X) *
                (c ^ (Multiplicative.toAdd p.2).val * c ^ (Multiplicative.toAdd p'.2).val) := by
              rw [Prod.fst_mul, map_mul, Subgroup.coe_mul, h2]
          _ = ((α p.1 : K) : X) * c ^ (Multiplicative.toAdd p.2).val *
                (((α p'.1 : K) : X) * c ^ (Multiplicative.toAdd p'.2).val) := by
              rw [mul_assoc, ← mul_assoc ((α p'.1 : K) : X), hcomm]
              simp only [mul_assoc] }
  let β' : Q × E →* A × E := β.prodMap (MonoidHom.id E)
  have hE2 : ∀ e : E, e ^ 2 = 1 := by decide
  have hEc : ∀ a b : E, a * b = b * a := fun a b => mul_comm a b
  have hEcard : Nat.card E = 2 := by simp [E, Nat.card_eq_fintype_card, ZMod.card]
  refine ⟨Q × E, A × E, inferInstance, inferInstance, inferInstance, α', β', ?_, ?_, ?_, ?_, ?_⟩
  · exact hβ.prodMap Function.surjective_id
  · intro a b
    exact Prod.ext (hc _ _) (hEc _ _)
  · intro a
    exact Prod.ext (hs _) (hE2 _)
  · rw [Nat.card_prod, hEcard, pow_succ]
    omega
  · rintro ⟨q, e⟩ hqe
    rw [MonoidHom.mem_ker] at hqe
    have he : (Multiplicative.toAdd e) = 0 := by
      by_contra hne
      have hv : (Multiplicative.toAdd e).val = 1 := by
        have h1 : (Multiplicative.toAdd e).val < 2 := ZMod.val_lt _
        have h2 : (Multiplicative.toAdd e).val ≠ 0 := by
          rwa [Ne, ZMod.val_eq_zero]
        omega
      have : ((α q : K) : X) * c = 1 := by simpa [α', hv] using hqe
      have hq : ((α q : K) : X) = c⁻¹ := eq_inv_of_mul_eq_one_left this
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
      rw [hcinv] at hq
      exact hcK (hq ▸ (α q).2)
    have he' : e = 1 := Multiplicative.toAdd.injective (by simpa using he)
    subst he'
    have hq1 : α q = 1 := by
      apply Subtype.ext
      simpa [α'] using hqe
    refine MonoidHom.mem_ker.2 (Prod.ext ?_ rfl)
    exact MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 hq1))

theorem rankCertified_of_not_sectionalTwoRankLE {G : Type} [Group G] [Finite G] {r : ℕ}
    (h : ¬ SectionalTwoRankLE G r) : RankCertified G r := by
  classical
  have h' : ∃ P : Subgroup G, IsPGroup 2 P ∧
      ∀ s : Finset G, s.card ≤ r → Subgroup.closure (s : Set G) ≠ P := by
    by_contra hcon
    apply h
    intro P hP
    by_contra hno
    exact hcon ⟨P, hP, fun s hs hcl => hno ⟨s, hs, hcl⟩⟩
  obtain ⟨P, hP, hnone⟩ := h'
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  obtain ⟨-, hcomm, hpow, helem, d, hd, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hP
  have := helem
  refine ⟨↥P, ↥P ⧸ frattini ↥P, inferInstance, inferInstance, inferInstance, P.subtype,
    QuotientGroup.mk' (frattini ↥P), QuotientGroup.mk'_surjective _,
    fun a b => mul_comm' a b, hpow, ?_, ?_⟩
  · by_contra hle
    rw [not_lt] at hle
    have hgen : Nat.card (↥P ⧸ frattini ↥P) = 2 ^ CFSG.generatorRank (↥P ⧸ frattini ↥P) :=
      CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := 2) _
    have h1 : CFSG.generatorRank (↥P ⧸ frattini ↥P) ≤ r := by
      rw [hgen] at hle
      exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hle
    have h2 : CFSG.generatorRank ↥P ≤ r :=
      (CFSG.generatorRank_le_generatorRank_quotient_frattini (p := 2) ↥P).trans h1
    obtain ⟨S, hScard, hStop⟩ := Group.rank_spec ↥P
    rw [← CFSG.generatorRank_eq_group_rank] at hScard
    refine hnone (S.image P.subtype) (Finset.card_image_le.trans (by omega)) ?_
    rw [Finset.coe_image, ← MonoidHom.map_closure, hStop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · intro k hk
    rw [MonoidHom.mem_ker, Subgroup.coe_subtype] at hk
    have : k = 1 := Subtype.ext hk
    rw [this]
    exact one_mem _

theorem rankCertified_iff {G : Type} [Group G] [Finite G] {r : ℕ} :
    RankCertified G r ↔ ¬ SectionalTwoRankLE G r :=
  ⟨RankCertified.not_sectionalTwoRankLE, rankCertified_of_not_sectionalTwoRankLE⟩

theorem not_rankCertified_three_of_gen4 {X : Type*} [Group X] (hX : Gen4 X) {K : Subgroup X}
    {c : X} (hcc : ∀ x : X, x * c = c * x) (hc2 : c * c = 1) (hcK : c ∉ K) :
    ¬ RankCertified K 3 :=
  fun h => (h.of_central_involution hcc hc2 hcK).not_gen4 (by norm_num) hX

end CFSG.GH74.Generic
