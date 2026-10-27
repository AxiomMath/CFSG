module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup
open scoped commutatorElement

section Pullback

variable {G S : Type*} [Group G] [Group S] {K : Subgroup G}

@[expose] def pullK (θ : ↥K →* S) (T : Subgroup S) : Subgroup G := (T.comap θ).map K.subtype

theorem mem_pullK {θ : ↥K →* S} {T : Subgroup S} {x : G} :
    x ∈ pullK θ T ↔ ∃ hx : x ∈ K, θ ⟨x, hx⟩ ∈ T := by
  simp only [pullK, mem_map, mem_comap, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hθ⟩
    exact ⟨⟨x, hx⟩, hθ, rfl⟩

theorem subgroupOf_pullK (θ : ↥K →* S) (T : Subgroup S) :
    (pullK θ T).subgroupOf K = T.comap θ :=
  comap_map_eq_self_of_injective K.subtype_injective _

theorem pullK_mono (θ : ↥K →* S) {T T' : Subgroup S} (h : T ≤ T') : pullK θ T ≤ pullK θ T' :=
  map_mono (comap_mono h)

theorem card_comap_of_le_range {A B : Type*} [Group A] [Group B] (f : A →* B) {T : Subgroup B}
    (hT : T ≤ f.range) : Nat.card (T.comap f) = Nat.card f.ker * Nat.card T := by
  let g : ↥(T.comap f) →* ↥T := (f.comp (T.comap f).subtype).codRestrict T fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨s, hs⟩
    obtain ⟨a, ha⟩ := hT hs
    exact ⟨⟨a, by simpa [ha] using hs⟩, Subtype.ext ha⟩
  have hker : g.ker = f.ker.subgroupOf (T.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [← Subgroup.card_ker_mul_card_of_surjective hg, hker]
  congr 1
  exact Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap f T)).toEquiv

theorem card_pullK (θ : ↥K →* S) {T : Subgroup S} (hT : T ≤ θ.range) :
    Nat.card (pullK θ T) = Nat.card θ.ker * Nat.card T := by
  rw [pullK, card_subtype, card_comap_of_le_range θ hT]

theorem card_le_mul_card_map {A B : Type*} [Group A] [Group B] (f : A →* B) [Finite f.ker]
    (U : Subgroup A) : Nat.card U ≤ Nat.card f.ker * Nat.card (U.map f) := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict U)
  rw [MonoidHom.domRestrict_range] at h
  rw [← h]
  refine Nat.mul_le_mul_right _ ?_
  rw [MonoidHom.ker_domRestrict]
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, x.2⟩) ?_
  intro x y hxy
  have h := congrArg (fun w : ↥f.ker => (w : A)) hxy
  exact Subtype.ext (Subtype.ext h)

theorem pullK_zpowers (θ : ↥K →* S) {t z : G} (ht : t ∈ K) (hz : z ∈ K) {s : S}
    (hker : θ.ker = (zpowers t).subgroupOf K) (hθz : θ ⟨z, hz⟩ = s) :
    pullK θ (zpowers s) = closure {t, z} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, n, hn⟩ := mem_pullK.mp hx
    have hn' : s ^ n = θ ⟨x, hxK⟩ := hn
    have hzn : z ^ n ∈ K := zpow_mem hz n
    have hθzn : θ ⟨z ^ n, hzn⟩ = s ^ n := by
      have : (⟨z ^ n, hzn⟩ : ↥K) = ⟨z, hz⟩ ^ n := rfl
      rw [this, map_zpow, hθz]
    have h1 : (⟨x * (z ^ n)⁻¹, K.mul_mem hxK (K.inv_mem hzn)⟩ : ↥K) ∈ θ.ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨x * (z ^ n)⁻¹, K.mul_mem hxK (K.inv_mem hzn)⟩ : ↥K) =
          ⟨x, hxK⟩ * (⟨z ^ n, hzn⟩ : ↥K)⁻¹ := Subtype.ext rfl
      rw [this, map_mul, map_inv, hθzn, hn', mul_inv_cancel]
    rw [hker, mem_subgroupOf] at h1
    have htc : t ∈ closure ({t, z} : Set G) := subset_closure (Set.mem_insert _ _)
    have hzc : z ∈ closure ({t, z} : Set G) :=
      subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h2 : x * (z ^ n)⁻¹ ∈ closure ({t, z} : Set G) := zpowers_le.mpr htc h1
    have h3 : z ^ n ∈ closure ({t, z} : Set G) := zpow_mem hzc n
    have : x = (x * (z ^ n)⁻¹) * z ^ n := by group
    rw [this]
    exact mul_mem h2 h3
  · rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · refine mem_pullK.mpr ⟨ht, ?_⟩
      have : θ ⟨x, ht⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
        exact mem_zpowers x
      rw [this]
      exact one_mem _
    · refine mem_pullK.mpr ⟨hz, ?_⟩
      rw [hθz]
      exact mem_zpowers s

theorem relIndex_pullK (θ : ↥K →* S) (T : Subgroup S) :
    (pullK θ T).relIndex K = T.relIndex θ.range := by
  rw [Subgroup.relIndex, subgroupOf_pullK, index_comap]

theorem map_subtype_sup_pullK (θ : ↥K →* S) {Y₀ : Subgroup ↥K} {Y Q : Subgroup S}
    (hY : Y ≤ θ.range) (hQ : Q ≤ θ.range) (h : Y₀ ⊔ θ.ker = Y.comap θ) :
    Y₀.map K.subtype ⊔ pullK θ Q = pullK θ (Y ⊔ Q) := by
  have e : Y₀ ⊔ Q.comap θ = (Y ⊔ Q).comap θ := by
    rw [← comap_sup_eq_of_le_range θ hY hQ, ← h, sup_assoc,
      sup_eq_right.mpr (ker_le_comap θ Q)]
  unfold pullK
  rw [← Subgroup.map_sup, e]

theorem pullK_map_subgroupOf (θ : ↥K →* S) {U : Subgroup G} (hU : U ≤ K)
    (hker : θ.ker ≤ U.subgroupOf K) : pullK θ ((U.subgroupOf K).map θ) = U := by
  rw [pullK, comap_map_eq, sup_eq_left.mpr hker]
  exact map_subgroupOf_eq_of_le hU

end Pullback

section Perfect

variable {A B : Type*} [Group A] [Group B]

theorem commutator_sup_eq_of_le_center {M N : Subgroup A} (hN : N ≤ center A) :
    ⁅M ⊔ N, M ⊔ N⁆ = ⁅M, M⁆ := by
  haveI : N.Normal := normal_of_le_center hN
  refine le_antisymm ?_ (commutator_mono le_sup_left le_sup_left)
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_normal_right.mp ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_sup_of_normal_right.mp hb
  have c1 : ∀ c : A, ⁅a₂, c⁆ = 1 := fun c =>
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hN ha₂) c).symm
  have c2 : ∀ c : A, ⁅c, b₂⁆ = 1 := fun c =>
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hN hb₂) c)
  have e : ⁅a₁ * a₂, b₁ * b₂⁆ = ⁅a₁, b₁⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, c1, commutatorElement_mul_right_eq_mul_conj, c2]
    simp
  rw [e]
  exact commutator_mem_commutator ha₁ hb₁

theorem exists_perfect_comap (θ : A →* B) (hker : θ.ker ≤ center A) {Y : Subgroup B}
    (hY : Y ≤ θ.range) (hperf : ⁅Y, Y⁆ = Y) :
    ∃ Y₀ : Subgroup A, ⁅Y₀, Y₀⁆ = Y₀ ∧ Y₀.map θ = Y ∧ Y₀ ⊔ θ.ker = Y.comap θ := by
  have h1 : (⁅Y.comap θ, Y.comap θ⁆).map θ = Y := by
    rw [map_commutator, map_comap_eq_self hY, hperf]
  have h2 : ⁅Y.comap θ, Y.comap θ⁆ ⊔ θ.ker = Y.comap θ := by
    rw [← comap_map_eq, h1]
  refine ⟨⁅Y.comap θ, Y.comap θ⁆, ?_, h1, h2⟩
  calc ⁅⁅Y.comap θ, Y.comap θ⁆, ⁅Y.comap θ, Y.comap θ⁆⁆
      = ⁅⁅Y.comap θ, Y.comap θ⁆ ⊔ θ.ker, ⁅Y.comap θ, Y.comap θ⁆ ⊔ θ.ker⁆ :=
        (commutator_sup_eq_of_le_center hker).symm
    _ = ⁅Y.comap θ, Y.comap θ⁆ := by rw [h2]

end Perfect

section TwoCore

variable {G S : Type} [Group G] [Group S] {K : Subgroup G}

theorem O2In_eq_pullK {θ : ↥K →* S} {C : Subgroup S} (hrange : θ.range = C)
    (hker : IsPGroup 2 θ.ker) : TwoFi22.O2In K = pullK θ (TwoFi22.O2In C) := by
  have hmem : ∀ x, θ x ∈ C := fun x => hrange ▸ (⟨x, rfl⟩ : θ x ∈ θ.range)
  let θ' : ↥K →* ↥C := θ.codRestrict C hmem
  have hq : CFSG.CGT.PushingUpLit.CGT6.TwoQuot θ' := by
    refine ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx⟩ := hrange.ge hc
      exact ⟨x, Subtype.ext hx⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hker
  have h2 : (CFSG.pCore 2 ↥C).comap θ' = (TwoFi22.O2In C).comap θ := by
    ext x
    simp only [TwoFi22.O2In, mem_comap, mem_map, coe_subtype]
    constructor
    · intro h
      exact ⟨θ' x, h, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      have : c = θ' x := Subtype.ext hcx
      rwa [← this]
  show (CFSG.pCore 2 ↥K).map K.subtype = ((TwoFi22.O2In C).comap θ).map K.subtype
  rw [hq.pCore_eq, h2]

theorem invUnder_map_pullK (θ : ↥K →* S) {Y₀ : Subgroup ↥K} {U : Subgroup G}
    (h : InvUnder (Y₀.map K.subtype) U) : InvUnder (Y₀.map θ) ((U.subgroupOf K).map θ) := by
  rintro n ⟨y, hy, rfl⟩ u ⟨v, hv, rfl⟩
  refine ⟨y * v * y⁻¹, ?_, by simp⟩
  show y * v * y⁻¹ ∈ U.subgroupOf K
  rw [mem_subgroupOf]
  have := h (y : G) ⟨y, hy, rfl⟩ (v : G) hv
  simpa using this

theorem exists_quot_pullK {θ : ↥K →* S} {C Q : Subgroup S} (hrange : θ.range = C)
    {X : Type*} [Group X] (ρ : ↥C →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q.subgroupOf C) :
    ∃ π : ↥K →* X, Function.Surjective π ∧ π.ker = (pullK θ Q).subgroupOf K := by
  have hmem : ∀ x, θ x ∈ C := fun x => hrange ▸ (⟨x, rfl⟩ : θ x ∈ θ.range)
  let θ' : ↥K →* ↥C := θ.codRestrict C hmem
  have hθ' : Function.Surjective θ' := by
    rintro ⟨c, hc⟩
    obtain ⟨x, hx⟩ := hrange.ge hc
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨ρ.comp θ', hρ.comp hθ', ?_⟩
  ext x
  rw [MonoidHom.mem_ker, subgroupOf_pullK, mem_comap]
  change ρ (θ' x) = 1 ↔ θ x ∈ Q
  rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  rfl

end TwoCore

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
