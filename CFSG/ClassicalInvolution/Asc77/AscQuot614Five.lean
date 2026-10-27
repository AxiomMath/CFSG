module

public import CFSG.ClassicalInvolution.Asc77.AscQuot614Comm

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace AscQuot

@[expose] noncomputable def sylowOfIsSylow2In' {V K : Subgroup G} (h : IsSylow2In V K) :
    Sylow 2 ↥K where
  toSubgroup := V.subgroupOf K
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
    rfl

private theorem isSylow2In_map_subtype' [Finite G] (K : Subgroup G) (P : Sylow 2 ↥K) :
    IsSylow2In ((P : Subgroup ↥K).map K.subtype) K := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, fun V' hV'K hV'2 hle => ?_⟩
  have hQV : (P : Subgroup ↥K) ≤ V'.subgroupOf K := fun x hx => hle ⟨x, hx, rfl⟩
  have hcomap : V'.subgroupOf K = (P : Subgroup ↥K) := P.is_maximal' hV'2.comap_subtype hQV
  rw [← Subgroup.map_subgroupOf_eq_of_le hV'K, hcomap]

private theorem natCard_isSylow2In' [Finite G] (K : Subgroup G) :
    Nat.card {R : Subgroup G // IsSylow2In R K} = Nat.card (Sylow 2 ↥K) := by
  refine Nat.card_congr
    { toFun := fun R => sylowOfIsSylow2In' R.2
      invFun := fun P => ⟨(P : Subgroup ↥K).map K.subtype, isSylow2In_map_subtype' K P⟩
      left_inv := fun R => ?_
      right_inv := fun P => ?_ }
  · exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le R.2.1)
  · apply Sylow.ext
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem exists_sylow_normalized' [Finite G] {M W : Subgroup G} (hW : IsPGroup 2 W)
    (hWM : W ≤ Subgroup.normalizer (M : Set G)) :
    ∃ P : Subgroup G, IsSylow2In P M ∧ ∀ w ∈ W, conjSub w P = P := by
  have hinv : ∀ w ∈ W, ∀ P ∈ {P : Subgroup G | IsSylow2In P M}, conjSub w P ∈
      {P : Subgroup G | IsSylow2In P M} := by
    intro w hw P hP
    have := IsSylow2In.conj hP w
    rwa [mem_normalizer_iff_conjSub_eq.mp (hWM hw)] at this
  have hodd : ¬ 2 ∣ Nat.card ↥{P : Subgroup G | IsSylow2In P M} := by
    have h1 : Nat.card ↥{P : Subgroup G | IsSylow2In P M} = Nat.card (Sylow 2 ↥M) :=
      natCard_isSylow2In' M
    rw [h1]
    exact not_dvd_card_sylow 2 ↥M
  obtain ⟨P, hP, hfix⟩ := exists_fixed_conjSub hW hinv hodd
  exact ⟨P, hP, hfix⟩

private theorem isSylowOf_of_isSylow2In' [Finite G] {V P : Subgroup G} (h : IsSylow2In V P) :
    CFSG.ABGLocalTools.IsSylowOf 2 V P :=
  ⟨sylowOfIsSylow2In' h, by
    show (V.subgroupOf P).map P.subtype = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.1]⟩

private theorem isSylow2In_of_isSylowOf' [Finite G] {V P : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 V P) : IsSylow2In V P :=
  ⟨h.le, h.isPGroup, fun _ hV'P hV'2 hle => h.eq_of_le hle hV'P hV'2⟩

theorem commutes_of_quot [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h67 : L6_7On Ω) (h62 : L6_2On Ω) (h69 : L6_9On Ω) (h611 : L6_11On Ω)
    (X : Subgroup G) [X.Normal] (hRX : ∀ R ∈ RSet Ω, Commutes R X) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z) {v : G}
    (hvJ : v ∈ J) (hvnc : ¬ ∀ w ∈ J, v * w = w * v) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (hvz : QuotientGroup.mk' X v * QuotientGroup.mk' X z =
      QuotientGroup.mk' X z * QuotientGroup.mk' X v) :
    v * z = z * v := by
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hcentral : ∀ w ∈ J, t * w = w * t := fun w hw => ht.commute_of_mem hw
  have hv3 : 3 ≤ orderOf v := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < orderOf v := orderOf_pos v
    have hv1 : v = 1 := by
      rcases (by omega : orderOf v = 1 ∨ orderOf v = 2) with h | h
      · exact orderOf_eq_one_iff.mp h
      · have hvv : v * v = 1 := by
          have := pow_orderOf_eq_one v
          rwa [h, pow_two] at this
        rcases ht.unique v hvJ hvv with h1 | h1
        · exact h1
        · exfalso
          apply hvnc
          intro w hw
          rw [h1]
          exact hcentral w hw
    apply hvnc
    intro w _
    rw [hv1, one_mul, mul_one]
  obtain ⟨Kk, hKk⟩ : ∃ Kk : ℤ → Subgroup G, ∀ k, Kk k = conjSub (v ^ k) K :=
    ⟨fun k => conjSub (v ^ k) K, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = ⨆ k : ℤ, Kk k := ⟨_, rfl⟩
  have hKkΩ : ∀ k : ℤ, Kk k ∈ Ω := fun k => by
    rw [hKk]
    exact hΩ.conjInvariant _ K hK
  have hzk : ∀ k : ℤ, IsUniqueInvolution (Kk k) (v ^ k * z * (v ^ k)⁻¹) := fun k => by
    rw [hKk]
    exact hz.conj _
  have hcong : ∀ k : ℤ, QuotientGroup.mk' X (v ^ k * z * (v ^ k)⁻¹) = QuotientGroup.mk' X z := by
    intro k
    have hc : Commute (QuotientGroup.mk' X v) (QuotientGroup.mk' X z) := hvz
    have hck := (hc.zpow_left k).eq
    rw [map_mul, map_mul, map_inv, map_zpow, hck, mul_inv_cancel_right]
  have hKkN : ∀ k : ℤ, Kk k ≤ Subgroup.normalizer (K : Set G) := by
    intro k
    by_cases hk : Kk k = K
    · rw [hk]
      exact Subgroup.le_normalizer
    · have hzt : (v ^ k * z * (v ^ k)⁻¹)⁻¹ * z ∈ X := by
        have := hcong k
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
        exact this
      have hcomm : ⁅K, Kk k⁆ ≤ oddCoreOf K ⊓ oddCoreOf (Kk k) :=
        commutes_of_congr hp hq hΩ h62 X hRX hK (hKkΩ k) (Ne.symm hk) hz (hzk k) hzt
      exact le_normalizer_of_commutator_le_oddCoreOf
        (by rw [Subgroup.commutator_comm]; exact hcomm.trans inf_le_left)
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := by
    rw [hM]
    exact iSup_le hKkN
  have hKM : K ≤ M := by
    have h0 : Kk 0 = K := by rw [hKk]; simp
    rw [hM]
    calc K = Kk 0 := h0.symm
      _ ≤ ⨆ k : ℤ, Kk k := le_iSup Kk 0
  have hvM : conjSub v M = M := by
    have h1 : conjSub v (⨆ k : ℤ, Kk k) = ⨆ k : ℤ, conjSub v (Kk k) := Subgroup.map_iSup _ _
    have h2 : ∀ k : ℤ, conjSub v (Kk k) = Kk (1 + k) := by
      intro k
      rw [hKk, hKk, ← conjSub_mul, zpow_one_add]
    rw [hM, h1]
    calc ⨆ k : ℤ, conjSub v (Kk k) = ⨆ k : ℤ, Kk (1 + k) := by simp only [h2]
      _ = ⨆ k : ℤ, Kk k := Equiv.iSup_comp (g := Kk) (Equiv.addLeft (1 : ℤ))
  have hvN : v ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_iff_conjSub_eq.mpr hvM
  have hW : Subgroup.zpowers v ≤ Subgroup.normalizer (M : Set G) := Subgroup.zpowers_le.mpr hvN
  obtain ⟨P, hP, hPfix⟩ := exists_sylow_normalized' hv2 hW
  have hvP : Subgroup.zpowers v ≤ Subgroup.normalizer (P : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hPfix w hw)
  have hQ2 : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' hv2 hP.2.1 hvP
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hQ2
  have hvS : v ∈ (S : Subgroup G) := hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
  have hPS : P ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRsyl' : IsSylow2In (P ⊓ K) K :=
    isSylow2In_of_isSylowOf' (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
      (isSylowOf_of_isSylow2In' hP) hKM hMN)
  obtain ⟨R, hRsyl, hRP⟩ : ∃ R : Subgroup G, IsSylow2In R K ∧ R ≤ P :=
    ⟨P ⊓ K, hRsyl', inf_le_left⟩
  have hRΩ : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hRS : R ≤ (S : Subgroup G) := hRP.trans hPS
  have hR8 := hΩ.eight_le_of_mem_RSet hp hRΩ
  have hzR : z ∈ R := mem_of_uniqueInvolution hz hRsyl.1 hRsyl.2.1 (by omega)
  obtain ⟨⟨η, hη, hηinv⟩, hab⟩ := h69 S
  obtain ⟨habel, -⟩ := hab η hη hηinv
  have hηG : η ∈ etaG Ω := ⟨S, hη, hηinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = ⨆ V ∈ η, V := ⟨_, rfl⟩
  have hWS : W ≤ (S : Subgroup G) := by
    rw [hWdef]
    exact iSup₂_le fun V hV => hηS V hV
  have hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRsyl.1 hRS)
    omega
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
    have h1 : Subgroup.zpowers v ≤ J ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hvJ) (Subgroup.zpowers_le.mpr hvS)
    have h2 := Subgroup.card_le_of_le h1
    rw [Nat.card_zpowers] at h2
    omega
  have hUKη : K ⊓ W ∈ η := by
    rw [hWdef]
    exact h611 S η hηG hηS K hK hKS
  have hUJη : J ⊓ W ∈ η := by
    rw [hWdef]
    exact h611 S η hηG hηS J hJ hJS
  obtain ⟨-, -, -, -, -, -, -, -, hUK4⟩ := hΩ.exists_data_of_mem_USet hp (hη.1 hUKη).1
  have hUK2 : IsPGroup 2 ↥(K ⊓ W) := (S.isPGroup'.to_le hWS).to_inf_right
  have hzW : z ∈ W := (mem_of_uniqueInvolution hz inf_le_left hUK2 (by omega)).2
  obtain ⟨R', -, J', hJ', hR'J', hUJR', -, hR'card, hUJ4⟩ :=
    hΩ.exists_data_of_mem_USet hp (hη.1 hUJη).1
  have hJJ' : J' = J :=
    hΩ.eq_of_mem_USet hp (hη.1 hUJη).1 hJ' hJ (hUJR'.trans hR'J'.1) inf_le_left
  rw [hJJ'] at hR'J'
  have hTS : (J ⊓ W) ⊔ Subgroup.zpowers v ≤ (S : Subgroup G) :=
    sup_le (inf_le_right.trans hWS) (Subgroup.zpowers_le.mpr hvS)
  have hT2 : IsPGroup 2 ↥((J ⊓ W) ⊔ Subgroup.zpowers v) := S.isPGroup'.to_le hTS
  have hTJ : (J ⊓ W) ⊔ Subgroup.zpowers v ≤ J :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hvJ)
  obtain ⟨V₁, hV₁, hTV₁⟩ := IsSylow2In.exists_ge hT2 hTJ
  have hV₁card : Nat.card V₁ = 2 * Nat.card ↥(J ⊓ W) := by
    rw [← hR'card, hV₁.natCard_eq hR'J']
  have hvT : v ∈ (J ⊓ W) ⊔ Subgroup.zpowers v := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  rcases eq_or_eq_of_natCard_eq_two_mul le_sup_left hTV₁ hV₁card with hT | hT
  · have hvW : v ∈ W := by
      rw [hT] at hvT
      exact hvT.2
    exact habel v (hWdef ▸ hvW) z (hWdef ▸ hzW)
  · have hV₁S : V₁ ≤ (S : Subgroup G) := hT ▸ hTS
    have hV₁Ω : V₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hV₁
    have hne : R ≠ V₁ := by
      intro h
      have h2 := hΩ.card_le_two_of_le_inf hK hJ hKJ hRsyl.2.1 hRsyl.1
        ((le_of_eq h).trans hV₁.1)
      omega
    have hcomm := h67 S R hRΩ V₁ hV₁Ω hRS hV₁S hne
    rw [hT] at hvT
    exact (hcomm z hzR v hvT).symm

end AscQuot

end CFSG.ClassicalInvolution.Asc77
