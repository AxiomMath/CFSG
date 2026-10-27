module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

@[expose] def IsPClosedMod (p : ℕ) {X : Type*} [Group X] (U : Subgroup X) : Prop :=
  ∃ S : Subgroup X, S.Normal ∧ U ≤ S ∧ (∃ k : ℕ, U.relIndex S = p ^ k) ∧ ¬ p ∣ S.index

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem IsPClosedMod.sup_normalizer_eq_top [Fact p.Prime] {U : Subgroup X} [U.Normal]
    (hU : IsPClosedMod p U) (P : Sylow p X) : U ⊔ normalizer (P : Set X) = ⊤ := by
  obtain ⟨S, hSn, hUS, ⟨k, hk⟩, hSp⟩ := hU
  haveI := hSn
  have hp : p.Prime := Fact.out
  have hPS : (P : Subgroup X) ≤ S := by
    have h1 : IsPGroup p ↥(Subgroup.map (QuotientGroup.mk' S) (P : Subgroup X)) :=
      (show IsPGroup p (P : Subgroup X) from P.isPGroup').map (QuotientGroup.mk' S)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h1
    have hdvd : Nat.card ↥(Subgroup.map (QuotientGroup.mk' S) (P : Subgroup X)) ∣ S.index := by
      rw [Subgroup.index_eq_card]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra h
      exact hSp ((dvd_pow_self p h).trans hdvd)
    have hbot : Subgroup.map (QuotientGroup.mk' S) (P : Subgroup X) = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hn, hn0, pow_zero])
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have hPrel : ¬ p ∣ (P : Subgroup X).relIndex S := fun hdiv =>
    P.not_dvd_index (hdiv.trans (Subgroup.relIndex_dvd_index_of_le hPS))
  have hcop : Nat.Coprime (p ^ k) ((P : Subgroup X).relIndex S) :=
    (hp.coprime_iff_not_dvd.mpr hPrel).pow_left k
  have hTrel : (U ⊔ (P : Subgroup X)).relIndex S = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
    · rw [← hk]
      exact Subgroup.relIndex_dvd_of_le_left S le_sup_left
    · exact Subgroup.relIndex_dvd_of_le_left S le_sup_right
  have hST : S ≤ U ⊔ (P : Subgroup X) := Subgroup.relIndex_eq_one.mp hTrel
  have htop : normalizer (P : Set X) ⊔ S = ⊤ := Sylow.normalizer_sup_eq_top' P hPS
  apply top_le_iff.mp
  calc (⊤ : Subgroup X) = normalizer (P : Set X) ⊔ S := htop.symm
    _ ≤ normalizer (P : Set X) ⊔ (U ⊔ (P : Subgroup X)) :=
        sup_le le_sup_left (hST.trans le_sup_right)
    _ ≤ U ⊔ normalizer (P : Set X) :=
        sup_le le_sup_right (sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right))

theorem IsPClosedMod.le_sup_normalizer {G : Type*} [Group G] [Finite G] [Fact p.Prime]
    {B U P : Subgroup G} (hUB : U ≤ B) (hUn : (U.subgroupOf B).Normal)
    (hU : IsPClosedMod p (U.subgroupOf B)) (hP : CFSG.ABGLocalTools.IsSylowOf p P B) :
    B ≤ U ⊔ (B ⊓ normalizer (P : Set G)) := by
  obtain ⟨Q, hQ⟩ := hP
  haveI := hUn
  have htop : (U.subgroupOf B) ⊔ normalizer (Q : Set ↥B) = ⊤ :=
    IsPClosedMod.sup_normalizer_eq_top hU Q
  have h₁ : ((U.subgroupOf B) ⊔ normalizer (Q : Set ↥B)).map B.subtype ≤
      U ⊔ (B ⊓ normalizer (P : Set G)) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · calc ((U.subgroupOf B).map B.subtype) = U ⊓ B := Subgroup.subgroupOf_map_subtype U B
        _ ≤ U := inf_le_left
        _ ≤ U ⊔ (B ⊓ normalizer (P : Set G)) := le_sup_left
    · have h1 : Subgroup.map B.subtype (normalizer (Q : Set ↥B)) ≤ B :=
        Subgroup.map_subtype_le _
      have h2 : Subgroup.map B.subtype (normalizer (Q : Set ↥B)) ≤ normalizer (P : Set G) := by
        calc Subgroup.map B.subtype (normalizer (Q : Set ↥B))
            ≤ normalizer (Subgroup.map B.subtype (Q : Subgroup ↥B)) :=
              Subgroup.le_normalizer_map B.subtype
          _ = normalizer (P : Set G) := by rw [hQ]
      exact (le_inf h1 h2).trans le_sup_right
  have hBeq : ((U.subgroupOf B) ⊔ normalizer (Q : Set ↥B)).map B.subtype = B := by
    rw [htop, Subgroup.map_top, B.range_subtype]
  conv_lhs => rw [← hBeq]
  exact h₁

theorem isPClosedMod_of_index_eq_pow [Fact p.Prime] {U : Subgroup X} (k : ℕ)
    (hk : U.index = p ^ k) : IsPClosedMod p U := by
  refine ⟨⊤, inferInstance, le_top, ⟨k, ?_⟩, ?_⟩
  · rw [Subgroup.relIndex_top_right]
    exact hk
  · rw [Subgroup.index_top]
    exact (Fact.out : p.Prime).not_dvd_one

private lemma relIndex_dvd_relIndex_of_le_of_normal {G : Type*} [Group G] {H K K' : Subgroup G}
    [H.Normal] (h : K' ≤ K) : H.relIndex K' ∣ H.relIndex K := by
  have h1 : H.relIndex (K' ⊔ H) = H.relIndex K' := Subgroup.relIndex_sup_right K' H
  have h2 : H.relIndex (K ⊔ H) = H.relIndex K := Subgroup.relIndex_sup_right K H
  have h3 := Subgroup.relIndex_mul_relIndex H (K' ⊔ H) (K ⊔ H) le_sup_right
    (sup_le_sup h le_rfl)
  rw [h1, h2] at h3
  exact dvd_of_mul_right_eq _ h3

theorem IsPClosedMod.comap [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] {U : Subgroup X}
    [U.Normal] (hU : IsPClosedMod p U) (f : Y →* X) : IsPClosedMod p (U.comap f) := by
  obtain ⟨S, hSn, hUS, ⟨k, hk⟩, hSp⟩ := hU
  haveI := hSn
  have hp : p.Prime := Fact.out
  have hdvd : (U.comap f).relIndex (S.comap f) ∣ p ^ k := by
    rw [Subgroup.relIndex_comap U f (S.comap f), Subgroup.map_comap_eq f S, ← hk]
    exact relIndex_dvd_relIndex_of_le_of_normal (H := U) (K := S) (K' := f.range ⊓ S) inf_le_right
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨S.comap f, hSn.comap f, Subgroup.comap_mono hUS, ⟨j, hj⟩, ?_⟩
  rw [Subgroup.index_comap]
  exact fun hdiv => hSp (hdiv.trans (Subgroup.relIndex_dvd_index_of_normal S f.range))

theorem IsPClosedMod.inf [Fact p.Prime] {U₁ U₂ : Subgroup X} [U₁.Normal] [U₂.Normal]
    (h₁ : IsPClosedMod p U₁) (h₂ : IsPClosedMod p U₂) : IsPClosedMod p (U₁ ⊓ U₂) := by
  obtain ⟨S₁, hS₁n, hU₁S₁, ⟨k₁, hk₁⟩, hS₁p⟩ := h₁
  obtain ⟨S₂, hS₂n, hU₂S₂, ⟨k₂, hk₂⟩, hS₂p⟩ := h₂
  haveI := hS₁n
  haveI := hS₂n
  have hp : p.Prime := Fact.out
  have hdvd₁ : U₁.relIndex (U₂ ⊓ (S₁ ⊓ S₂)) ∣ p ^ k₁ := by
    rw [← hk₁]
    exact relIndex_dvd_relIndex_of_le_of_normal (H := U₁) (K := S₁)
      (K' := U₂ ⊓ (S₁ ⊓ S₂)) (le_trans inf_le_right inf_le_left)
  have hdvd₂ : U₂.relIndex (S₁ ⊓ S₂) ∣ p ^ k₂ := by
    rw [← hk₂]
    exact relIndex_dvd_relIndex_of_le_of_normal (H := U₂) (K := S₂) (K' := S₁ ⊓ S₂) inf_le_right
  have hprod : (U₁ ⊓ U₂).relIndex (S₁ ⊓ S₂) ∣ p ^ (k₁ + k₂) := by
    rw [← Subgroup.relIndex_inf_mul_relIndex U₁ U₂ (S₁ ⊓ S₂), pow_add]
    exact mul_dvd_mul hdvd₁ hdvd₂
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hprod
  refine ⟨S₁ ⊓ S₂, inferInstance, inf_le_inf hU₁S₁ hU₂S₂, ⟨j, hj⟩, ?_⟩
  have hrel : (S₁ ⊓ S₂).index = S₂.relIndex S₁ * S₁.index := by
    have h2 := Subgroup.relIndex_inf_mul_relIndex S₂ S₁ (⊤ : Subgroup X)
    rw [inf_top_eq, Subgroup.relIndex_top_right S₁, Subgroup.relIndex_top_right (S₂ ⊓ S₁),
      inf_comm] at h2
    exact h2.symm
  intro hdiv
  rw [hrel] at hdiv
  rcases (hp.dvd_mul.mp hdiv) with hdiv | hdiv
  · exact hS₂p (hdiv.trans (Subgroup.relIndex_dvd_index_of_normal S₂ S₁))
  · exact hS₁p hdiv

theorem IsPClosedMod.finset_inf [Fact p.Prime] {ι : Type*} (s : Finset ι) (U : ι → Subgroup X)
    (hn : ∀ i ∈ s, (U i).Normal) (h : ∀ i ∈ s, IsPClosedMod p (U i)) :
    IsPClosedMod p (s.inf U) := by
  classical
  have key : ∀ s : Finset ι,
      (∀ i ∈ s, (U i).Normal) → (∀ i ∈ s, IsPClosedMod p (U i)) →
        (s.inf U).Normal ∧ IsPClosedMod p (s.inf U) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ _
        rw [Finset.inf_empty]
        exact ⟨inferInstance, isPClosedMod_of_index_eq_pow 0 (by simp)⟩
    | insert a s ha ih =>
        intro hn hs
        rw [Finset.inf_insert]
        have hna : (U a).Normal := hn a (Finset.mem_insert_self a s)
        have hns : ∀ i ∈ s, (U i).Normal := fun i hi => hn i (Finset.mem_insert_of_mem hi)
        have hsa : IsPClosedMod p (U a) := hs a (Finset.mem_insert_self a s)
        have hss : ∀ i ∈ s, IsPClosedMod p (U i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
        obtain ⟨hsn, hsi⟩ := ih hns hss
        haveI := hna
        haveI := hsn
        exact ⟨inferInstance, IsPClosedMod.inf hsa hsi⟩
  exact (key s hn h).2

private lemma mem_map_subtype_iff {N U : Subgroup X} [N.Normal] [U.Normal] [Fact p.Prime]
    {S : Subgroup ↥N} [S.Normal] (hUS : U.subgroupOf N ≤ S) (hSp : ¬ p ∣ S.index) (k : ℕ)
    (hk : (U.subgroupOf N).relIndex S = p ^ k) {x : X} :
    x ∈ S.map N.subtype ↔ x ∈ N ∧ ∃ j, x ^ (p ^ j) ∈ U := by
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y.2, k, ?_⟩
    have hcard : Nat.card (↥S ⧸ (U.subgroupOf N).subgroupOf S) = p ^ k := by
      rw [← Subgroup.index_eq_card]
      exact hk
    have hord : orderOf (QuotientGroup.mk' ((U.subgroupOf N).subgroupOf S) ⟨y, hy⟩) ∣ p ^ k := by
      rw [← hcard]
      exact orderOf_dvd_natCard _
    have hpow : QuotientGroup.mk' ((U.subgroupOf N).subgroupOf S) (⟨y, hy⟩ ^ (p ^ k)) = 1 := by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp hord
    have hmem : (⟨y, hy⟩ : ↥S) ^ (p ^ k) ∈ (U.subgroupOf N).subgroupOf S := by
      rw [← QuotientGroup.eq_one_iff]
      exact hpow
    have hmemN : (y ^ (p ^ k) : ↥N) ∈ U.subgroupOf N := by
      have h := Subgroup.mem_subgroupOf.mp hmem
      simpa [map_pow] using h
    have hmemU : ((y ^ (p ^ k) : ↥N) : X) ∈ U := Subgroup.mem_subgroupOf.mp hmemN
    simpa [map_pow] using hmemU
  · rintro ⟨hxN, j, hxj⟩
    have hmemS : (⟨x, hxN⟩ : ↥N) ^ (p ^ j) ∈ S := by
      have hU : (⟨x, hxN⟩ : ↥N) ^ (p ^ j) ∈ U.subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        simpa [map_pow] using hxj
      exact hUS hU
    have hord : orderOf (QuotientGroup.mk' S (⟨x, hxN⟩ : ↥N)) ∣ p ^ j := by
      rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hmemS
    have hcard : Nat.card (↥N ⧸ S) = S.index := (Subgroup.index_eq_card S).symm
    have hord2 : orderOf (QuotientGroup.mk' S (⟨x, hxN⟩ : ↥N)) ∣ S.index := by
      rw [← hcard]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ j) S.index :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hSp).pow_left j
    have hone : QuotientGroup.mk' S (⟨x, hxN⟩ : ↥N) = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord hord2)
    have hxS : (⟨x, hxN⟩ : ↥N) ∈ S := by
      rw [← QuotientGroup.eq_one_iff]
      exact hone
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hxS, rfl⟩

theorem IsPClosedMod.of_subgroupOf [Fact p.Prime] {N U : Subgroup X} [N.Normal] [U.Normal]
    (hUN : U ≤ N) (hN : ¬ p ∣ N.index) (hU : IsPClosedMod p (U.subgroupOf N)) :
    IsPClosedMod p U := by
  obtain ⟨S₀, hS₀n, hUS₀, ⟨k, hk⟩, hS₀p⟩ := hU
  haveI := hS₀n
  have hNn : N.Normal := inferInstance
  have hUn : U.Normal := inferInstance
  have hp : p.Prime := Fact.out
  have hrel : (S₀.map N.subtype).relIndex N = S₀.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  refine ⟨S₀.map N.subtype, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x hx g => ?_⟩
    rw [mem_map_subtype_iff hUS₀ hS₀p k hk] at hx ⊢
    obtain ⟨hxN, j, hxj⟩ := hx
    exact ⟨hNn.conj_mem x hxN g, j, by rw [conj_pow]; exact hUn.conj_mem (x ^ (p ^ j)) hxj g⟩
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hUN hx⟩, hUS₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · exact ⟨k, by rw [← Subgroup.relIndex_comap U N.subtype S₀]; exact hk⟩
  · rw [← Subgroup.relIndex_mul_index (Subgroup.map_subtype_le S₀)]
    intro hdiv
    rcases (hp.dvd_mul.mp hdiv) with hdiv | hdiv
    · exact hS₀p (hrel ▸ hdiv)
    · exact hN hdiv

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
