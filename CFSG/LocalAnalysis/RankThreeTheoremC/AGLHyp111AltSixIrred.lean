module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace AltSixIrred

def NormIrred {M : Type*} [Group M] (S : Subgroup M) : Prop :=
  ∀ V : Subgroup M, V ≤ S → V ≠ ⊥ →
    Subgroup.normalizer (S : Set M) ≤ Subgroup.normalizer (V : Set M) → V = S

theorem NormIrred.of_map {M N : Type*} [Group M] [Group N] (φ : M ≃* N) {S : Subgroup M}
    (h : NormIrred (S.map φ.toMonoidHom)) : NormIrred S := by
  intro V hVS hV1 hVn
  have hV : V.map φ.toMonoidHom = S.map φ.toMonoidHom := by
    refine h _ (Subgroup.map_mono hVS) ?_ ?_
    · exact fun h0 =>
        hV1 ((Subgroup.map_eq_bot_iff_of_injective V (f := φ.toMonoidHom) φ.injective).mp h0)
    · rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hVn
  exact Subgroup.map_injective φ.injective hV

def cycleA : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

def cycleB : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

def quartic : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 2 5

def sylowList : List (Equiv.Perm (Fin 6)) :=
  [1, cycleA, cycleA * cycleA, cycleB, cycleB * cycleB, cycleA * cycleB, cycleA * cycleA * cycleB,
    cycleA * cycleB * cycleB, cycleA * cycleA * cycleB * cycleB]

theorem one_mem_sylowList : (1 : Equiv.Perm (Fin 6)) ∈ sylowList := by decide +kernel

theorem mul_mem_sylowList : ∀ x ∈ sylowList, ∀ y ∈ sylowList, x * y ∈ sylowList := by
  decide +kernel

theorem inv_mem_sylowList : ∀ x ∈ sylowList, x⁻¹ ∈ sylowList := by decide +kernel

theorem sign_eq_one_of_mem_sylowList : ∀ σ ∈ sylowList, Equiv.Perm.sign σ = 1 := by
  decide +kernel

theorem sign_quartic : Equiv.Perm.sign quartic = 1 := by decide +kernel

theorem mem_sylowList_iff_quartic :
    ∀ σ : Equiv.Perm (Fin 6), σ ∈ sylowList ↔ quartic * σ * quartic⁻¹ ∈ sylowList := by
  decide +kernel

theorem card_toFinset_sylowList : sylowList.toFinset.card = 9 := by decide +kernel

theorem exists_pow_mul_pow_eq : ∀ v ∈ sylowList, v ≠ 1 → ∀ x ∈ sylowList,
    ∃ a b : Fin 3, v ^ (a : ℕ) * (quartic * v * quartic⁻¹) ^ (b : ℕ) = x := by
  decide +kernel

def sylowPerm : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | σ ∈ sylowList}
  one_mem' := one_mem_sylowList
  mul_mem' := fun {x y} hx hy => mul_mem_sylowList x hx y hy
  inv_mem' := fun {x} hx => inv_mem_sylowList x hx

theorem sylowPerm_le : sylowPerm ≤ alternatingGroup (Fin 6) := fun σ hσ =>
  Equiv.Perm.mem_alternatingGroup.mpr (sign_eq_one_of_mem_sylowList σ hσ)

def sylowZero : Subgroup (alternatingGroup (Fin 6)) :=
  sylowPerm.subgroupOf (alternatingGroup (Fin 6))

theorem card_sylowPerm : Nat.card sylowPerm = 9 := by
  have h : (sylowPerm : Set (Equiv.Perm (Fin 6))) = ↑sylowList.toFinset := by
    ext σ
    simp [sylowPerm]
  calc Nat.card sylowPerm = (sylowPerm : Set (Equiv.Perm (Fin 6))).ncard :=
        Nat.card_coe_set_eq _
    _ = sylowList.toFinset.card := by rw [h, Set.ncard_coe_finset]
    _ = 9 := card_toFinset_sylowList

theorem card_sylowZero : Nat.card sylowZero = 9 := by
  rw [sylowZero, Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowPerm_le).toEquiv,
    card_sylowPerm]

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isPGroup_sylowZero : IsPGroup 3 sylowZero :=
  IsPGroup.of_card (n := 2) (by rw [card_sylowZero]; norm_num)

theorem not_dvd_index_sylowZero : ¬ 3 ∣ sylowZero.index := by
  have h := Subgroup.card_mul_index sylowZero
  rw [card_sylowZero, card_alternatingGroup_six] at h
  omega

def sylowZeroSylow : Sylow 3 (alternatingGroup (Fin 6)) :=
  isPGroup_sylowZero.toSylow not_dvd_index_sylowZero

theorem normIrred_sylowZero : NormIrred sylowZero := by
  intro V hVS hV1 hVn
  let t : alternatingGroup (Fin 6) := ⟨quartic, Equiv.Perm.mem_alternatingGroup.mpr sign_quartic⟩
  have htN : t ∈ Subgroup.normalizer (sylowZero : Set (alternatingGroup (Fin 6))) :=
    Subgroup.mem_normalizer_iff.mpr fun x => mem_sylowList_iff_quartic x
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
  have hw : t * (v : alternatingGroup (Fin 6)) * t⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hVn htN) v).mp v.2
  refine le_antisymm hVS fun x hx => ?_
  have hvS : (v : alternatingGroup (Fin 6)) ∈ sylowZero := hVS v.2
  have hv1' : ((v : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ≠ 1 := fun h1 =>
    hv1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨a, b, hab⟩ := exists_pow_mul_pow_eq _ hvS hv1' _ hx
  have hx' : x = (v : alternatingGroup (Fin 6)) ^ (a : ℕ) * (t * v * t⁻¹) ^ (b : ℕ) :=
    Subtype.ext (by simpa using hab.symm)
  rw [hx']
  exact V.mul_mem (V.pow_mem v.2 _) (V.pow_mem hw _)

theorem normIrred_sylow (S : Sylow 3 (alternatingGroup (Fin 6))) :
    NormIrred (S : Subgroup (alternatingGroup (Fin 6))) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) S sylowZeroSylow
  refine NormIrred.of_map (MulAut.conj g) ?_
  have h : (S : Subgroup (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom =
      sylowZero := by
    have h1 := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    exact h1
  rw [h]
  exact normIrred_sylowZero

theorem normIrred_sylow_of_isAltTwoP {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K)
    (S : Sylow 3 K) : NormIrred (S : Subgroup K) := by
  obtain ⟨e⟩ := hK
  let e' : K ≃* alternatingGroup (Fin 6) := e
  exact NormIrred.of_map e'
    (normIrred_sylow (S.mapSurjective (f := e'.toMonoidHom) e'.surjective))

open scoped Pointwise

theorem inf_eq_bot_of_isPGroup_of_coprime {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {A N : Subgroup X} (hA : IsPGroup p A) (hN : p.Coprime (Nat.card N)) : A ⊓ N = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  exact Subgroup.inf_eq_bot_of_coprime (by rw [hn]; exact hN.pow_left n)

theorem card_sup_of_inf_eq_bot {X : Type*} [Group X] {A N : Subgroup X} [N.Normal]
    (h : A ⊓ N = ⊥) : Nat.card ↥(A ⊔ N) = Nat.card A * Nat.card N := by
  have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup X) N (A ⊔ N) bot_le le_sup_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1
  rw [← h1, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right, inf_comm, h,
    Subgroup.relIndex_bot_left, mul_comm]

theorem normalizer_map_le_map_normalizer {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    [Fact p.Prime] (f : X →* Y) (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    {A : Subgroup X} (hA : IsPGroup p A) :
    Subgroup.normalizer ((A.map f : Subgroup Y) : Set Y) ≤
      (Subgroup.normalizer (A : Set X)).map f := by
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  set B : Subgroup X := A ⊔ f.ker with hB
  have hBf : ∀ z : X, z ∈ B ↔ f z ∈ A.map f := fun z => by
    rw [hB, ← Subgroup.mem_comap, Subgroup.comap_map_eq]
  have hAB : A ≤ B := le_sup_left
  have hA2B : MulAut.conj x • A ≤ B := by
    rintro - ⟨a, ha, rfl⟩
    refine (hBf _).mpr ?_
    have := (Subgroup.mem_normalizer_iff.mp hy (f a)).mp (Subgroup.mem_map_of_mem f ha)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hcardB : Nat.card B = Nat.card A * Nat.card f.ker :=
    card_sup_of_inf_eq_bot (inf_eq_bot_of_isPGroup_of_coprime hA hker)
  have hSyl : ∀ T : Subgroup X, T ≤ B → IsPGroup p T → Nat.card T = Nat.card A →
      ∃ S : Sylow p B, (S : Subgroup B) = T.subgroupOf B := by
    intro T hTB hT hTcard
    have hidx : ¬ p ∣ (T.subgroupOf B).index := by
      have h := Subgroup.card_mul_index (T.subgroupOf B)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, hTcard, hcardB] at h
      rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hker
    exact ⟨hT.comap_subtype.toSylow hidx, rfl⟩
  obtain ⟨S₁, hS₁⟩ := hSyl A hAB hA rfl
  have hA2p : IsPGroup p (MulAut.conj x • A : Subgroup X) := hA.map _
  have hA2card : Nat.card (MulAut.conj x • A : Subgroup X) = Nat.card A :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj x) A).toEquiv).symm
  obtain ⟨S₂, hS₂⟩ := hSyl (MulAut.conj x • A) hA2B hA2p hA2card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B S₂ S₁
  have h1 : MulAut.conj g • (S₂ : Subgroup B) = (S₁ : Subgroup B) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [hS₁, hS₂, Subgroup.conj_smul_subgroupOf hA2B g] at h1
  have h2 : MulAut.conj (g : X) • (MulAut.conj x • A) = A := by
    have := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_of_le_left (Subgroup.conj_smul_le_of_le hA2B g), inf_of_le_left hAB] at this
  have hn : (g : X) * x ∈ Subgroup.normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h3 := SetLike.ext_iff.mp h2 ((g : X) * x * z * ((g : X) * x)⁻¹)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h3
    simpa [MulAut.smul_def, mul_assoc] using h3
  obtain ⟨a, ha, hfa⟩ := (hBf _).mp g.2
  refine ⟨a⁻¹ * ((g : X) * x),
    (Subgroup.normalizer (A : Set X)).mul_mem (Subgroup.le_normalizer (A.inv_mem ha)) hn, ?_⟩
  rw [map_mul, map_mul, map_inv, hfa, inv_mul_cancel_left]

theorem eq_of_le_of_normIrred {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ} [Fact p.Prime]
    (f : X →* Y) (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    {K : Subgroup Y} {S : Subgroup K} (hS : NormIrred S) {A V : Subgroup X} (hA : IsPGroup p A)
    (hSA : S.map K.subtype = A.map f) (hVA : V ≤ A) (hV1 : V ≠ ⊥)
    (hVn : Subgroup.normalizer (A : Set X) ≤ Subgroup.normalizer (V : Set X)) : V = A := by
  have hAker : A ⊓ f.ker = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hA hker
  have hinj : ∀ a ∈ A, f a = 1 → a = 1 := fun a ha h1 => by
    have hmem : a ∈ A ⊓ f.ker := ⟨ha, h1⟩
    rwa [hAker, Subgroup.mem_bot] at hmem
  have hfK : V.map f ≤ K := by
    refine (Subgroup.map_mono hVA).trans ?_
    rw [← hSA]
    exact Subgroup.map_subtype_le _
  set W : Subgroup K := (V.map f).subgroupOf K with hW
  have hWS : W ≤ S := by
    intro x hx
    have hx1 : (x : Y) ∈ S.map K.subtype := by
      rw [hSA]
      exact Subgroup.map_mono hVA hx
    obtain ⟨s, hs, hsx⟩ := hx1
    rwa [← Subtype.ext hsx]
  have hW1 : W ≠ ⊥ := by
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    have hfv : f (v : X) ≠ 1 := fun h => hv1 (Subtype.ext (hinj v (hVA v.2) h))
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨⟨f v, hfK ⟨v, v.2, rfl⟩⟩, ⟨v, v.2, rfl⟩⟩, fun h => hfv ?_⟩
    exact congrArg (fun z : W => ((z : K) : Y)) h
  have hSsub : (S.map K.subtype).subgroupOf K = S :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hWn : Subgroup.normalizer (S : Set K) ≤ Subgroup.normalizer (W : Set K) := by
    intro k hk
    have hk0 : k ∈ (Subgroup.normalizer ((S.map K.subtype : Subgroup Y) : Set Y)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le _), hSsub]
      exact hk
    rw [hSA] at hk0
    obtain ⟨n, hn, hnk⟩ := normalizer_map_le_map_normalizer f hf hker hA hk0
    have hn2 : f n ∈ Subgroup.normalizer ((V.map f : Subgroup Y) : Set Y) :=
      Subgroup.le_normalizer_map f ⟨n, hVn hn, rfl⟩
    rw [hnk] at hn2
    have hk2 : k ∈ (Subgroup.normalizer ((V.map f : Subgroup Y) : Set Y)).subgroupOf K := hn2
    rwa [Subgroup.subgroupOf_normalizer_eq hfK] at hk2
  have hWeq : W = S := hS W hWS hW1 hWn
  have hVf : V.map f = A.map f := by
    rw [← hSA, ← hWeq, hW, Subgroup.map_subgroupOf_eq_of_le hfK]
  refine le_antisymm hVA fun a ha => ?_
  obtain ⟨v, hv, hva⟩ : f a ∈ V.map f := by
    rw [hVf]
    exact ⟨a, ha, rfl⟩
  have hva' : v = a := inv_mul_eq_one.mp (hinj _ (A.mul_mem (A.inv_mem (hVA hv)) ha)
    (by rw [map_mul, map_inv, hva, inv_mul_cancel]))
  rwa [← hva']

end AltSixIrred

theorem eq_of_le_sylow_alt6 (S : Sylow 3 (alternatingGroup (Fin 6)))
    {V : Subgroup (alternatingGroup (Fin 6))} (hVS : V ≤ S) (hV1 : V ≠ ⊥)
    (hVn : Subgroup.normalizer ((S : Subgroup (alternatingGroup (Fin 6))) :
      Set (alternatingGroup (Fin 6))) ≤
      Subgroup.normalizer (V : Set (alternatingGroup (Fin 6)))) : V = S :=
  AltSixIrred.normIrred_sylow S V hVS hV1 hVn

theorem eq_of_le_sylow_of_isAltTwoP {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K)
    (S : Sylow 3 K) {V : Subgroup K} (hVS : V ≤ S) (hV1 : V ≠ ⊥)
    (hVn : Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K)) :
    V = S :=
  AltSixIrred.normIrred_sylow_of_isAltTwoP hK S V hVS hV1 hVn

theorem eq_of_le_of_normalizer_le {H A V : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsAltTwoP 3 K)
    (hAH : A ≤ H) (hA3 : IsPGroup 3 A)
    (hAsyl : ∃ S : Sylow 3 K, (S : Subgroup K).map K.subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hVA : V ≤ A) (hV1 : V ≠ ⊥)
    (hVn : H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    V = A := by
  obtain ⟨S, hS⟩ := hAsyl
  have hVH : V ≤ H := hVA.trans hAH
  have hVn' : Subgroup.normalizer ((A.subgroupOf H : Subgroup H) : Set H) ≤
      Subgroup.normalizer ((V.subgroupOf H : Subgroup H) : Set H) := by
    intro n hn
    have h1 : n ∈ (Subgroup.normalizer (A : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hAH]
      exact hn
    have h2 : n ∈ (Subgroup.normalizer (V : Set G)).subgroupOf H := hVn ⟨n.2, h1⟩
    rwa [Subgroup.subgroupOf_normalizer_eq hVH] at h2
  have hV1' : V.subgroupOf H ≠ ⊥ := by
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨v, hVH v.2⟩, v.2⟩, fun h => hv1 ?_⟩
    exact Subtype.ext (congrArg (fun z : V.subgroupOf H => ((z : H) : G)) h)
  have hker : Nat.Coprime 3
      (Nat.card (QuotientGroup.mk' (primeComplementCore (G := H) 3)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime 3
  have hVA' := AltSixIrred.eq_of_le_of_normIrred
    (QuotientGroup.mk' (primeComplementCore (G := H) 3)) (QuotientGroup.mk'_surjective _) hker
    (AltSixIrred.normIrred_sylow_of_isAltTwoP hK S) hA3.comap_subtype hS
    (fun x hx => hVA hx : V.subgroupOf H ≤ A.subgroupOf H) hV1' hVn'
  have := Subgroup.subgroupOf_inj.mp hVA'
  rwa [inf_of_le_left hVH, inf_of_le_left hAH] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
