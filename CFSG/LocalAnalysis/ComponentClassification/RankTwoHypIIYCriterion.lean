module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup

section TwoNilpotent

variable {G G' : Type*} [Group G] [Group G']

theorem relIndex_map_dvd_relIndex {N X : Subgroup G} (hNX : N ≤ X) (f : G →* G') :
    (N.map f).relIndex (X.map f) ∣ N.relIndex X := by
  have h : (N.subgroupOf X).map (f.subgroupMap X) = (N.map f).subgroupOf (X.map f) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : G), hx, rfl⟩
    · intro hy
      obtain ⟨n, hn, hny⟩ := mem_map.mp (mem_subgroupOf.mp hy)
      exact ⟨⟨n, hNX hn⟩, hn, Subtype.ext hny⟩
  change ((N.map f).subgroupOf (X.map f)).index ∣ (N.subgroupOf X).index
  rw [← h]
  exact index_map_dvd _ (f.subgroupMap_surjective X)

theorem IsTwoNilpotent.map {X : Subgroup G} (hX : IsTwoNilpotent X) (f : G →* G') :
    IsTwoNilpotent (X.map f) := by
  obtain ⟨N, hNX, hNn, hNo, k, hk⟩ := hX
  have hXN : X ≤ normalizer (N : Set G) := (normal_subgroupOf_iff_le_normalizer hNX).mp hNn
  refine ⟨N.map f, map_mono hNX, ?_, hNo.of_dvd_nat (card_map_dvd N f), ?_⟩
  · exact (normal_subgroupOf_iff_le_normalizer (map_mono hNX)).mpr
      ((map_mono hXN).trans (le_normalizer_map f))
  · have hdvd := relIndex_map_dvd_relIndex hNX f
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩

theorem IsTwoNilpotent.subgroupOf {X M : Subgroup G} (hX : IsTwoNilpotent X) (hXM : X ≤ M) :
    IsTwoNilpotent (X.subgroupOf M) := by
  obtain ⟨N, hNX, hNn, hNo, k, hk⟩ := hX
  have hXN : X ≤ normalizer (N : Set G) := (normal_subgroupOf_iff_le_normalizer hNX).mp hNn
  have hNM : N ≤ M := hNX.trans hXM
  have hsub : N.subgroupOf M ≤ X.subgroupOf M := fun x hx => hNX hx
  refine ⟨N.subgroupOf M, hsub, ?_, ?_, k, ?_⟩
  · refine (normal_subgroupOf_iff_le_normalizer hsub).mpr fun x hx => ?_
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hXN hx) y
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv]
  · rw [relIndex_subgroupOf hXM, hk]

theorem IsTwoNilpotent.odd_card_of_le_of_perfect [Finite G] {Y P : Subgroup G}
    (hY : IsTwoNilpotent Y) (hPY : P ≤ Y) (hP : ⁅P, P⁆ = P) : Odd (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNP, hNn, hNo, k, hk⟩ := hY.mono hPY
  have := hNn
  have hcard : Nat.card (↥P ⧸ N.subgroupOf P) = 2 ^ k := hk
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have : Group.IsPerfect (↥P ⧸ N.subgroupOf P) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (N.subgroupOf P))
      (QuotientGroup.mk'_surjective _)
  have hnil : Group.IsNilpotent (↥P ⧸ N.subgroupOf P) := (IsPGroup.of_card hcard).isNilpotent
  have hsub : Subsingleton (↥P ⧸ N.subgroupOf P) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isNilpotent _ hnil
  have h1 : N.relIndex P = 1 :=
    show Nat.card (↥P ⧸ N.subgroupOf P) = 1 from Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  rwa [le_antisymm hNP (relIndex_eq_one.mp h1)] at hNo

end TwoNilpotent

end CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoHypIIY

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

section Criterion

variable {G W : Type*} [Group G] [Group W]

theorem nE_map_le {A Q T : Subgroup G} {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}
    (hψ : IsActionHom A X ψ) (hTQ : T ≤ Q) (hTN : T ≤ normalizer (A : Set G))
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (Q : Set G)) :
    nE X ((T.subgroupOf (normalizer (A : Set G))).map ψ) ≤
      ((A ⊓ Q).subgroupOf (normalizer (A : Set G))).map ψ := by
  have hΓ : gammaE X ((T.subgroupOf (normalizer (A : Set G))).map ψ) ≤
      ((A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))).map ψ := by
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    obtain ⟨t, ht, rfl⟩ := he
    have ht1 : (t : G) ≠ 1 := fun h => he1 (by rw [show t = 1 from Subtype.ext h, map_one])
    refine (centDer_le_map hψ t).trans (Subgroup.map_mono fun c hc => ?_)
    refine ⟨hc.1, hQ (t : G) ht ht1 (c : G) hc.1 ?_⟩
    exact (mem_centralizer_iff.mp hc.2 (t : G) rfl).symm
  have hcomm : ⁅T.subgroupOf (normalizer (A : Set G)),
      (A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))⁆ ≤
      (A ⊓ Q).subgroupOf (normalizer (A : Set G)) := by
    rw [commutator_le]
    intro v hv c hc
    have h := commutator_le_inf hTQ hTN
    rw [commutator_le] at h
    have hvc := h (v : G) hv (c : G) hc
    change ((⁅v, c⁆ : normalizer (A : Set G)) : G) ∈ A ⊓ Q
    simpa [commutatorElement_def] using hvc
  calc nE X ((T.subgroupOf (normalizer (A : Set G))).map ψ)
      ≤ ⁅(T.subgroupOf (normalizer (A : Set G))).map ψ,
          ((A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))).map ψ⁆ :=
        commutator_mono le_rfl hΓ
    _ = (⁅T.subgroupOf (normalizer (A : Set G)),
          (A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))⁆).map ψ :=
        (Subgroup.map_commutator _ _ ψ).symm
    _ ≤ _ := Subgroup.map_mono hcomm

theorem isTwoNilpotent_nE_map [Finite G] [Finite W] {A Q T : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ) (hTQ : T ≤ Q)
    (hTN : T ≤ normalizer (A : Set G))
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (Q : Set G))
    (hQn : IsTwoNilpotent Q) :
    IsTwoNilpotent (nE X ((T.subgroupOf (normalizer (A : Set G))).map ψ)) :=
  (((hQn.mono inf_le_right).subgroupOf (inf_le_left.trans le_normalizer)).map ψ).mono
    (nE_map_le hψ hTQ hTN hQ)

end Criterion

section Witness

variable {W : Type*} [Group W]

@[expose] def QWitness (X E : Subgroup W) : Prop :=
  ∃ P : Subgroup W, P ≤ nE X E ∧ ⁅P, P⁆ = P ∧ Even (Nat.card P)

theorem not_isTwoNilpotent_of_qWitness [Finite W] {X E : Subgroup W} (h : QWitness X E) :
    ¬ IsTwoNilpotent (nE X E) := by
  obtain ⟨P, hPN, hPP, hPe⟩ := h
  intro hnil
  exact Nat.not_even_iff_odd.mpr (hnil.odd_card_of_le_of_perfect hPN hPP) hPe

end Witness

section HypII

variable {W : Type*} [Group W]

theorem hypII_of_forall {X₀ : Type*} [Group X₀] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X)
    (hc : ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ E ≤ X → ¬ YWitness X E →
      IsTwoNilpotent (nE X E) → False)
    {A : Type*} [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* X₀) : HypII A := by
  intro H _ _ B T ⟨f⟩ hT hXh
  obtain ⟨hTab, hT4, hTN, hTC⟩ := hT
  obtain ⟨Xh, hXle, hTsyl, hnil, htight⟩ := hXh
  by_contra hnot
  have hB : commutator ↥B = ⊤ := by
    have hAp : Group.IsPerfect A := (Group.isPerfect_def).2 hA
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective)
  let eB : ↥B ⧸ center ↥B ≃* X₀ :=
    (QuotientGroup.congr (center ↥B) (center A) f (map_center_eq f)).trans e
  obtain ⟨ψ, hψ⟩ := exists_isActionHom hW hB eB
  have hTX : T ≤ Xh := hTsyl.le
  have hXN : Xh ≤ normalizer (B : Set H) := hXle.trans (sup_le hTN le_normalizer)
  have hTsyl' : IsSylowOf 2 T (Xh ⊓ normalizer (B : Set H)) := by
    rwa [inf_eq_left.mpr hXN]
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ B, c * t = t * c → c ∈ normalizer (Xh : Set H) := by
    intro t ht ht1 c hc hct
    have hn := mem_normalizer_of_commute_of_tightlyEmbedded htight
      (t := ⟨t, le_sup_left (a := T) (b := B) ht⟩) (c := ⟨c, le_sup_right (a := T) hc⟩)
      (hTX ht) (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext (hTab.2 t ht))
      (Subtype.ext hct)
    rw [mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ T ⊔ B
    · have := (mem_normalizer_iff.mp hn) ⟨x, hx⟩
      simpa [mem_subgroupOf] using this
    · have hcx : c * x * c⁻¹ ∉ T ⊔ B := by
        intro h
        apply hx
        have := (T ⊔ B).mul_mem ((T ⊔ B).mul_mem ((T ⊔ B).inv_mem
          (le_sup_right (a := T) hc)) h) (le_sup_right (a := T) hc)
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd (hXle h) hx, fun h => absurd (hXle h) hcx⟩
  refine hc _ ?_ ?_ ?_ (not_yWitness_map hψ hTsyl' hTab.2 hQ)
    (isTwoNilpotent_nE_map hψ hTX hTN hQ hnil)
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [coe_mul]
      exact congrArg Subtype.val (hTab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab.2 _ hx)
      rw [this, map_one]
  ·
    rw [card_map_eq_of_inf_centralizer hψ hTC,
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
    exact hT4
  ·
    intro hle
    apply hnot
    intro t ht
    obtain ⟨b, hb, hbt⟩ := hψ.exists_eq _ (hle ⟨⟨t, hTN ht⟩, ht, rfl⟩)
    have h1 : ψ ((⟨b, le_normalizer hb⟩ : normalizer (B : Set H))⁻¹ * ⟨t, hTN ht⟩) = 1 := by
      rw [map_mul, map_inv, hbt, inv_mul_cancel]
    have hC := (hψ.eq_one_iff _).mp h1
    simp only [coe_mul, coe_inv] at hC
    rw [show t = b * (b⁻¹ * t) by group]
    exact mul_mem_sup hb hC

theorem exists_elemAbelian_of_not_hypII {X₀ : Type*} [Group X₀] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X) {A : Type*} [Group A] (hA : commutator A = ⊤)
    (e : A ⧸ center A ≃* X₀) (h : ¬ HypII A) :
    ∃ E : Subgroup W, IsElemAbelian 2 E ∧ 4 ≤ Nat.card E ∧ ¬ E ≤ X ∧ ¬ YWitness X E ∧
      IsTwoNilpotent (nE X E) := by
  by_contra hne
  exact h (hypII_of_forall hW (fun E h1 h2 h3 h4 h5 => hne ⟨E, h1, h2, h3, h4, h5⟩) hA e)

theorem hypII_of_witness {X₀ : Type*} [Group X₀] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X)
    (hc : ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ E ≤ X →
      YWitness X E ∨ ¬ IsTwoNilpotent (nE X E))
    {A : Type*} [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* X₀) : HypII A :=
  hypII_of_forall hW (fun E h1 h2 h3 h4 h5 => (hc E h1 h2 h3).elim h4 (· h5)) hA e

end HypII

section MulAut

variable {X₀ : Type*} [Group X₀]

theorem conj_apply_eq_mul_conj_mul_inv (φ : MulAut X₀) (x : X₀) :
    MulAut.conj (φ x) = φ * MulAut.conj x * φ⁻¹ := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem conj_injective_of_center_eq_bot (hZ : center X₀ = ⊥) :
    Function.Injective (MulAut.conj : X₀ →* MulAut X₀) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ center X₀ := by
    rw [mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut X₀ => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hZ] at hxZ
  exact mem_bot.mp hxZ

theorem autModel_mulAut (hZ : center X₀ = ⊥) :
    AutModel X₀ (MulAut X₀) (MulAut.conj : X₀ →* MulAut X₀).range := by
  have hinj := conj_injective_of_center_eq_bot hZ
  let ι : X₀ ≃* (MulAut.conj : X₀ →* MulAut X₀).range := MonoidHom.ofInjective hinj
  have hι : ∀ z, ((ι z : (MulAut.conj : X₀ →* MulAut X₀).range) : MulAut X₀) =
      MulAut.conj z := fun z => rfl
  refine ⟨⟨fun _ ⟨x, hx⟩ φ => ⟨φ x, by rw [← hx, conj_apply_eq_mul_conj_mul_inv]⟩⟩, ?_,
    ⟨ι.symm⟩, ?_⟩
  ·
    rw [eq_bot_iff]
    intro φ hφ
    rw [mem_bot]
    ext x
    have h1 := mem_centralizer_iff.mp hφ (MulAut.conj x) ⟨x, rfl⟩
    have h2 : MulAut.conj (φ x) = MulAut.conj x := by
      rw [conj_apply_eq_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact hinj h2
  ·
    intro α
    refine ⟨(ι.trans α).trans ι.symm, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := ι.surjective x
    rw [hι y, ← conj_apply_eq_mul_conj_mul_inv, ← hι]
    simp

end MulAut

end CFSG.ComponentClassification.RankTwoHypIIY
