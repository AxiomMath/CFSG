module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerDich

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace T8

section Sylow

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem isSylow2In_of_le_of_le {P M H : Subgroup G} (h : IsSylow2In P H) (hPM : P ≤ M)
    (hMH : M ≤ H) : IsSylow2In P M :=
  ⟨hPM, h.2.1, fun T hTM hT2 hPT => h.2.2 T (hTM.trans hMH) hT2 hPT⟩

omit [Finite G] in
theorem mem_normalizer_map_hom {H : Type} [Group H] (ψ : G →* H) {R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G)) :
    ψ y ∈ Subgroup.normalizer ((R.map ψ : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro h
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨y * r * y⁻¹, (hy r).mp hr, by simp⟩
  · rintro ⟨r, hr, hrh⟩
    refine ⟨y⁻¹ * r * y, ?_, ?_⟩
    · exact (hy (y⁻¹ * r * y)).mpr (by simpa [mul_assoc] using hr)
    · simp only [map_mul, map_inv]
      rw [hrh]
      group

theorem XMem.isSylow2In_layerRes_of_le (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) {P : Subgroup G}
    (hP : IsSylow2In P K) (hPx : P ≤ cenZ x) : IsSylow2In P (layerRes x K) := by
  have hCK : K ⊓ cenZ x ≤ K := inf_le_left
  have hP' : IsSylow2In P (K ⊓ cenZ x) := isSylow2In_of_le_of_le hP (le_inf hP.1 hPx) hCK
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ layerRes x K)
  have hQK : IsSylow2In Q K := h.isSylow2In_of_layerRes hp hq hΩ hx hQ
  have hQC : IsSylow2In Q (K ⊓ cenZ x) :=
    isSylow2In_of_le_of_le hQK (hQ.1.trans (layerRes_le_inf x K)) hCK
  obtain ⟨c, hcC, hcQ⟩ := exists_conj_of_isSylow2In hQC hP'
  have hcN : c ∈ Subgroup.normalizer (layerRes x K : Set G) :=
    mem_normalizer_layerRes (Subgroup.le_normalizer hcC.1) hcC.2
  have hPle : P ≤ layerRes x K := by
    rw [← hcQ]
    calc conjSub c Q ≤ conjSub c (layerRes x K) := conjSub_mono hQ.1
      _ = layerRes x K := mem_normalizer_iff_conjSub_eq.mp hcN
  exact isSylow2In_of_le_of_le hP hPle (layerRes_le x K)

end Sylow

section Quotient

theorem le_of_map_le_of_commutes {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) {P Q : Subgroup H} (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hc : Commutes P Q) (h : P.map (QuotientGroup.mk' N) ≤ Q.map (QuotientGroup.mk' N)) :
    P ≤ Q := by
  have hn : P ≤ Subgroup.normalizer (Q : Set H) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer (Q : Set H) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hc y hy u hu).symm
  have hU : IsPGroup 2 ↥(P ⊔ Q) := hP.to_sup_of_normal_right' hQ hn
  have hUN : (P ⊔ Q) ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hU le_rfl
      (hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  intro y hy
  obtain ⟨q, hq, hqy⟩ := h (Subgroup.mem_map_of_mem _ hy)
  have hmem : y⁻¹ * q ∈ (P ⊔ Q) ⊓ N :=
    ⟨(P ⊔ Q).mul_mem ((P ⊔ Q).inv_mem (Subgroup.mem_sup_left hy)) (Subgroup.mem_sup_right hq),
      QuotientGroup.eq.mp hqy.symm⟩
  rw [hUN, Subgroup.mem_bot] at hmem
  have : y = q := inv_mul_eq_one.mp hmem
  rw [this]
  exact hq

end Quotient

section Img

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def layerImg (Ω : Set (Subgroup G)) (x : G) (K : Subgroup G) :
    Subgroup (LayerQuot Ω x) :=
  ((layerRes x K).subgroupOf (layerJoin Ω x)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)))

omit [Finite G] in
theorem layerImg_mem {x : G} {K : Subgroup G} (h : XMem Ω x K) :
    layerImg Ω x K ∈ layerFamQ Ω x :=
  ⟨_, ⟨_, ⟨K, h, rfl⟩, le_layerJoin ⟨K, h, rfl⟩, rfl⟩, rfl⟩

theorem layerImg_isSylow2In (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K P : Subgroup G} (h : XMem Ω x K) (hP : IsSylow2In P K)
    (hPx : P ≤ cenZ x) :
    IsSylow2In ((P.subgroupOf (layerJoin Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)))) (layerImg Ω x K) :=
  isSylow2In_map_mk (CFSG.ComponentClassification.OddCore.odd_card ↥(layerJoin Ω x))
    ((h.isSylow2In_layerRes_of_le hp hq hΩ hx hP hPx).subgroupOf (le_layerJoin ⟨K, h, rfl⟩))

theorem layerImg_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J P : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (hP : IsSylow2In P J) (hPx : P ≤ cenZ x) (hPN : P ≤ Subgroup.normalizer (K : Set G))
    (hne : layerImg Ω x K ≠ layerImg Ω x J) :
    layerImg Ω x J ∈ omegaNbr (layerFamQ Ω x) (layerImg Ω x K) := by
  have hT := layerImg_isSylow2In hp hq hΩ hx hJ hP hPx
  refine ⟨layerImg_mem hJ, fun h => hne h.symm, _,
    mem_RSet_of_isSylow2In (layerImg_mem hJ) hT, hT.1, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have htK : (t : G) ∈ Subgroup.normalizer (K : Set G) := hPN (Subgroup.mem_subgroupOf.mp ht)
  have htx : (t : G) ∈ cenZ x := hPx (Subgroup.mem_subgroupOf.mp ht)
  have htN : (t : G) ∈ Subgroup.normalizer (layerRes x K : Set G) :=
    mem_normalizer_layerRes htK htx
  have htN' := (mem_normalizer_subgroupOf_iff (le_layerJoin ⟨K, hK, rfl⟩)).mp htN
  exact mem_normalizer_map_hom _ htN'

theorem layerImg_ne (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J P Q : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (hP : IsSylow2In P K) (hQ : IsSylow2In Q J) (hPx : P ≤ cenZ x) (hQx : Q ≤ cenZ x)
    (hc : Commutes P Q) (hPQ : P ≠ Q) : layerImg Ω x K ≠ layerImg Ω x J := by
  intro h
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hPL := hK.isSylow2In_layerRes_of_le hp hq hΩ hx hP hPx
  have hQL := hJ.isSylow2In_layerRes_of_le hp hq hΩ hx hQ hQx
  have hP1 := hPL.subgroupOf (le_layerJoin ⟨K, hK, rfl⟩)
  have hQ1 := hQL.subgroupOf (le_layerJoin ⟨J, hJ, rfl⟩)
  have hPs := isSylow2In_map_mk hodd hP1
  have hQs := isSylow2In_map_mk hodd hQ1
  change IsSylow2In _ (layerImg Ω x K) at hPs
  change IsSylow2In _ (layerImg Ω x J) at hQs
  rw [← h] at hQs
  have hc' : Commutes (P.subgroupOf (layerJoin Ω x)) (Q.subgroupOf (layerJoin Ω x)) :=
    fun a ha b hb => Subtype.ext
      (hc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
  have hc'' : Commutes (Q.subgroupOf (layerJoin Ω x)) (P.subgroupOf (layerJoin Ω x)) :=
    fun b hb a ha => (hc' a ha b hb).symm
  have hcmap : Commutes ((P.subgroupOf (layerJoin Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x))))
      ((Q.subgroupOf (layerJoin Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc' a ha b hb]
  have heq := eq_of_commutes_isSylow2In hPs hQs hcmap
  have h1 := le_of_map_le_of_commutes _ hodd hP1.2.1 hQ1.2.1 hc' heq.ge
  have h2 := le_of_map_le_of_commutes _ hodd hQ1.2.1 hP1.2.1 hc'' heq.le
  have hPY : P ≤ layerJoin Ω x := hPL.1.trans (le_layerJoin ⟨K, hK, rfl⟩)
  have hQY : Q ≤ layerJoin Ω x := hQL.1.trans (le_layerJoin ⟨J, hJ, rfl⟩)
  refine hPQ (le_antisymm (fun y hy => ?_) (fun y hy => ?_))
  · exact Subgroup.mem_subgroupOf.mp
      (h1 (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hPY hy⟩ : ↥(layerJoin Ω x)) ∈ _))
  · exact Subgroup.mem_subgroupOf.mp
      (h2 (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hQY hy⟩ : ↥(layerJoin Ω x)) ∈ _))

theorem layerImg_conj_of_mem_oddCore {x : G} {K : Subgroup G} {ν : G}
    (hν : ν ∈ oddCoreOf (layerJoin Ω x)) : layerImg Ω x (conjSub ν K) = layerImg Ω x K := by
  obtain ⟨ν', hν', rfl⟩ := Subgroup.mem_map.mp hν
  change layerImg Ω x (conjSub ((ν' : ↥(layerJoin Ω x)) : G) K) = _
  have hνc : ((ν' : ↥(layerJoin Ω x)) : G) ∈ cenZ x := layerJoin_le_cenZ x ν'.2
  have hn1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)) ν' = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hν'
  unfold layerImg
  rw [← layerRes_conj K hνc, ← conjSub_subgroupOf, AscQuot.map_conjSub, hn1, conjSub_one]

theorem exists_oddCore_conj_of_layerImg_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {x : G} (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K)
    (hJ : XMem Ω x J) (h : layerImg Ω x K = layerImg Ω x J) :
    ∃ n ∈ oddCoreOf (layerJoin Ω x), conjSub n K = J := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hΛ := hypOmegaMod_layer hp hq hΩ hx
  have hKL : layerRes x K ∈ layerSet Ω x := ⟨K, hK, rfl⟩
  have hJL : layerRes x J ∈ layerSet Ω x := ⟨J, hJ, rfl⟩
  have hK'Λ : (layerRes x K).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hKL, le_layerJoin hKL, rfl⟩
  have hJ'Λ : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hJL, le_layerJoin hJL, rfl⟩
  obtain ⟨m, hm, hJ'⟩ := exists_conj_of_map_eq hp hq hΛ hodd hK'Λ hJ'Λ h
  have hmy : ((m : ↥(layerJoin Ω x)) : G) ∈ layerJoin Ω x := m.2
  have hmc : ((m : ↥(layerJoin Ω x)) : G) ∈ cenZ x := layerJoin_le_cenZ x hmy
  refine ⟨(m : G), ⟨m, hm, rfl⟩, ?_⟩
  rw [conjSub_subgroupOf] at hJ'
  have h2 := Subgroup.subgroupOf_inj.mp hJ'
  rw [inf_eq_left.mpr (le_layerJoin hJL)] at h2
  have h3 : conjSub (m : G) (layerRes x K) ≤ layerJoin Ω x := by
    rw [layerRes_conj K hmc]
    exact le_layerJoin ⟨_, hK.conj hΩ hmc, rfl⟩
  rw [inf_eq_left.mpr h3] at h2
  exact XMem.eq_of_layerRes_eq hp hq hΩ hx (hK.conj hΩ hmc) hJ
    ((layerRes_conj K hmc).symm.trans h2.symm)

theorem exists_oddCore_conj_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (h : layerImg Ω x J ∈ omegaNbr (layerFamQ Ω x) (layerImg Ω x K)) :
    ∃ n ∈ oddCoreOf (layerJoin Ω x), J ∈ omegaNbr Ω (conjSub n K) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hΛ := hypOmegaMod_layer hp hq hΩ hx
  have hΨ := hypOmegaMod_layerQuot hp hq hΩ hx
  have hKL : layerRes x K ∈ layerSet Ω x := ⟨K, hK, rfl⟩
  have hJL : layerRes x J ∈ layerSet Ω x := ⟨J, hJ, rfl⟩
  have hK'Λ : (layerRes x K).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hKL, le_layerJoin hKL, rfl⟩
  have hJ'Λ : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hJL, le_layerJoin hJL, rfl⟩
  obtain ⟨m, hmN, hm⟩ := exists_conj_omegaNbr hp hq hΛ hΨ hodd hK'Λ hJ'Λ h
  exact ⟨(m : G), ⟨m, hmN, rfl⟩, layer_omegaNbr hp hq hΩ hx hK hJ m hm⟩

theorem exists_oddCore_conj_mem_dComp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K : Subgroup G} (hK : XMem Ω x K)
    (hconn : DConnected (layerFamQ Ω x)) {M : Subgroup G} (hM : XMem Ω x M) :
    ∃ ν ∈ oddCoreOf (layerJoin Ω x), conjSub ν M ∈ dComp Ω K := by
  have key : ∀ U : Subgroup (LayerQuot Ω x),
      Relation.ReflTransGen
        (fun A B : Subgroup (LayerQuot Ω x) => B ∈ layerFamQ Ω x ∧ dAdj (layerFamQ Ω x) A B)
        (layerImg Ω x K) U →
      U ∈ layerFamQ Ω x ∧ ∀ M' : Subgroup G, XMem Ω x M' → layerImg Ω x M' = U →
        ∃ ν ∈ oddCoreOf (layerJoin Ω x), conjSub ν M' ∈ dComp Ω K := by
    intro U hU
    induction hU with
    | refl =>
      refine ⟨layerImg_mem hK, fun M' hM' h => ?_⟩
      obtain ⟨n, hn, hnM⟩ := exists_oddCore_conj_of_layerImg_eq hp hq hΩ hx hK hM' h.symm
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      rw [← hnM, conjSub_inv_conjSub]
      exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      obtain ⟨hbΦ, hPb⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      refine ⟨hcΦ, fun M' hM' hMc => ?_⟩
      obtain ⟨_, ⟨L, ⟨M₁, hM₁, rfl⟩, hLY, rfl⟩, hb⟩ := hbΦ
      have hb' : layerImg Ω x M₁ = b := hb
      obtain ⟨ν₁, hν₁, hM₂⟩ := hPb M₁ hM₁ hb'
      have hν₁c : ν₁ ∈ cenZ x := layerJoin_le_cenZ x (oddCoreOf_le_self _ hν₁)
      have hM₂X : XMem Ω x (conjSub ν₁ M₁) := hM₁.conj hΩ hν₁c
      have hM₂b : layerImg Ω x (conjSub ν₁ M₁) = b :=
        (layerImg_conj_of_mem_oddCore hν₁).trans hb'
      have hdc : dComp Ω (conjSub ν₁ M₁) = dComp Ω K := dComp_eq_of_mem hK.1 hM₂
      rcases hadj with hc1 | hc2
      · rw [← hM₂b, ← hMc] at hc1
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaNbr hp hq hΩ hx hM₂X hM' hc1
        refine ⟨m⁻¹, (oddCoreOf _).inv_mem hm, ?_⟩
        have h1 := omegaNbr_conj hΩ.conjInvariant hmn m⁻¹
        rw [conjSub_inv_conjSub] at h1
        have h2 := mem_dComp_of_mem_omegaNbr h1
        rwa [hdc] at h2
      · rw [← hM₂b, ← hMc] at hc2
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaNbr hp hq hΩ hx hM' hM₂X hc2
        refine ⟨m, hm, ?_⟩
        exact Relation.ReflTransGen.tail hM₂
          ⟨hΩ.conjInvariant m M' hM'.1, Or.inr hmn⟩
  exact (key _ (hconn _ (layerImg_mem hK) _ (layerImg_mem hM))).2 M hM rfl

end Img

end T8

end CFSG.ClassicalInvolution.Asc77
