module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerTQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG3

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D Q T : Subgroup G} {z b : G}

private theorem ThCyc.M0_inf_centralizer_A_eq_K (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    M0 L A D hD.comm ⊓ centralizer (A : Set G) =
      normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
  refine le_antisymm ?_ ?_
  · rintro m ⟨hmM0, hmA⟩
    have hmA' : ∀ a ∈ A, m * a * m⁻¹ = a := fun a ha => by
      calc m * a * m⁻¹ = (a * m) * m⁻¹ := by rw [mem_centralizer_iff.1 hmA a ha]
        _ = a := by group
    refine ⟨hmM0.1, mem_centralizer_iff.2 fun v hv => ?_⟩
    have h := H.centralizes_omega1_of_mem_M0 W W2 hD hb hmM0 hmA' v hv
    calc v * m = (m * v * m⁻¹) * m := by rw [h]
      _ = m * v := by group
  · rintro m ⟨hmND, hmV⟩
    refine ⟨?_, (Subgroup.centralizer_le (H.A_le_omega1 W W2 hD)) hmV⟩
    rw [H.M0_eq_sup_centralizer_omega1 W W2 hD]
    exact Subgroup.mem_sup_left ⟨hmND, hmV⟩

theorem ThCyc.card_le_mul_card_inf_K (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTM : T ≤ normalizer (D : Set G)) :
    Nat.card T ≤ 128 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G))) := by
  classical
  haveI : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.two_of_forall_mul_self W.A_comm fun a ha => by
      simpa [pow_two] using W.A_sq a ha
  have hNA : T ⊓ M0 L A D hD.comm ≤ normalizer (A : Set G) := by
    intro x hx
    exact H.normalizer_D_le_normalizer_A W W2 hD h4 (hTM hx.1)
  have hcardM0 : Nat.card ↥(T ⊓ M0 L A D hD.comm) ≤
      64 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G))) := by
    have h := CFSG.GroupTheory.card_le_two_pow_mul_of_normalizes (A := A)
      (P := T ⊓ M0 L A D hD.comm) (n := 4) ?_ (hT.to_le inf_le_left) hNA
    · norm_num at h
      have hAK : (T ⊓ M0 L A D hD.comm) ⊓ centralizer (A : Set G) =
          T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) := by
        rw [inf_assoc, H.M0_inf_centralizer_A_eq_K W W2 hD hb]
      calc Nat.card ↥(T ⊓ M0 L A D hD.comm)
          ≤ 64 * Nat.card ↥((T ⊓ M0 L A D hD.comm) ⊓ centralizer (A : Set G)) := h
        _ = 64 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
            centralizer (omega1 D hD.comm : Set G))) := by rw [hAK]
    · rw [W.A_card]
      norm_num
  have hidx : (T ⊓ M0 L A D hD.comm).relIndex T ≤ 2 := by
    have hM2 : (M0 L A D hD.comm).relIndex (normalizer (D : Set G)) = 2 :=
      H.relIndex_M0_eq_two W W2 hD h4 hb
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right (H := M0 L A D hD.comm) hTM (by
      rw [hM2]
      norm_num)).trans (le_of_eq hM2)
  have hTcard : Nat.card T = (T ⊓ M0 L A D hD.comm).relIndex T *
      Nat.card ↥(T ⊓ M0 L A D hD.comm) := by
    have h := Subgroup.relIndex_mul_card (H := T ⊓ M0 L A D hD.comm) (K := T)
    rw [inf_of_le_left inf_le_left] at h
    exact h.symm
  calc Nat.card T = (T ⊓ M0 L A D hD.comm).relIndex T *
        Nat.card ↥(T ⊓ M0 L A D hD.comm) := hTcard
    _ ≤ 2 * (64 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G)))) := Nat.mul_le_mul hidx hcardM0
    _ = 128 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G))) := by ring

private theorem THyp.conj_mem_Q_of_mem_T (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) {x q : G} (hx : x ∈ T) (hq : q ∈ Q) : x * q * x⁻¹ ∈ Q := by
  rw [← THyp.inf_centralizer_eq hQ hT]
  exact ⟨T.mul_mem (T.mul_mem hx (hT.Q_le hq)) (T.inv_mem hx),
    normalizer_conj_mem_centralizer (m := x) (c := q) (hT.le_normalizer hx)
      (hQ.le_centralizer hq)⟩

private theorem THyp.le_normalizer_Q (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) : T ≤ normalizer (Q : Set G) := by
  intro x hx
  refine mem_normalizer_iff.2 fun q => ⟨fun hq => THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hx hq,
    fun hq => ?_⟩
  have h1 : x⁻¹ * (x * q * x⁻¹) * x ∈ Q := by
    simpa using THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT (T.inv_mem hx) hq
  have e : x⁻¹ * (x * q * x⁻¹) * x = q := by group
  rwa [e] at h1

private theorem THyp.commutator_mul_mem_Q (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) {a bb c : G} (hb : bb ∈ T)
    (hab : a * bb * a⁻¹ * bb⁻¹ ∈ Q) (hac : a * c * a⁻¹ * c⁻¹ ∈ Q) :
    a * (bb * c) * a⁻¹ * (bb * c)⁻¹ ∈ Q := by
  have hbc : bb * (a * c * a⁻¹ * c⁻¹) * bb⁻¹ ∈ Q :=
    THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hb hac
  have e : a * (bb * c) * a⁻¹ * (bb * c)⁻¹ =
      (a * bb * a⁻¹ * bb⁻¹) * (bb * (a * c * a⁻¹ * c⁻¹) * bb⁻¹) := by group
  rw [e]
  exact Q.mul_mem hab hbc

private theorem ThCyc.Q_inf_L_eq_Aa (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) :
    Q ⊓ L = Aa := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxQ, hxL⟩
    have hmem : x ∈ L ⊓ centralizer (Aa : Set G) := by
      refine ⟨hxL, mem_centralizer_iff.2 fun a ha => ?_⟩
      exact mem_centralizer_iff.1 (hQ.le_centralizer hxQ) a (hD.Aa_le ha)
    rwa [W2.inf_centralizer_Aa_eq W] at hmem
  · intro a ha
    exact ⟨hQ.D_le (hD.Aa_le ha), W.B_le (W2.Aa_le ha)⟩

private theorem ThCyc.card_inf_K_le_two_mul_card_Q (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) :
    Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G))) ≤ 2 * Nat.card Q := by
  classical
  have hbT : b ∈ T := hT.S_le (W.B_le_S W2.b_mem)
  have hbN : b ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hbT hq,
      fun hq => ?_⟩
    have h1 : b * (b * q * b⁻¹) * b⁻¹ ∈ Q :=
      THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hbT hq
    have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
    have e : b * (b * q * b⁻¹) * b⁻¹ = q := by
      calc b * (b * q * b⁻¹) * b⁻¹ = (b * b) * q * (b⁻¹ * b⁻¹) := by group
        _ = q := by rw [hbb, ← mul_inv_rev, hbb, inv_one, one_mul, mul_one]
    rwa [e] at h1
  have hbNle : zpowers b ≤ normalizer (Q : Set G) := zpowers_le.2 hbN
  have hbQ : b ∉ Q := fun h =>
    ThCyc.b_not_mem_centralizer_D W W2 hD hb (hQ.le_centralizer h)
  have hb1 : b ≠ 1 := fun h => hbQ (h ▸ Q.one_mem)
  have hord : orderOf b = 2 := orderOf_eq_prime W2.b_sq hb1
  have hprod := SylowEnd.card_sup_mul_card_inf (H := zpowers b) (K := Q) hbNle
  have hinf : zpowers b ⊓ Q = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxQ : x ∈ Q := hx.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx.1
    rcases zpow_eq_one_or_self W2.b_sq k with hk1 | hk1
    · rw [hk1] at hk
      exact Subgroup.mem_bot.2 hk.symm
    · rw [hk1] at hk
      exact absurd (hk ▸ hxQ) hbQ
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord] at hprod
  have hle : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      Q ⊔ zpowers b := by
    intro x hx
    have hxK1 : x ∈ ThCyc.K1 H W W2 hD h4 := hK1 hx
    rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hxK1 with hxC | hxCb
    · have hxQ : x ∈ Q := by
        have hmem : x ∈ T ⊓ centralizer (D : Set G) := ⟨hx.1, hxC⟩
        rwa [THyp.inf_centralizer_eq hQ hT] at hmem
      exact Subgroup.mem_sup_left hxQ
    · have hxbT : x * b ∈ T := T.mul_mem hx.1 hbT
      have hxbQ : x * b ∈ Q := by
        have hmem : x * b ∈ T ⊓ centralizer (D : Set G) := ⟨hxbT, hxCb⟩
        rwa [THyp.inf_centralizer_eq hQ hT] at hmem
      have hxeq : x = (x * b) * b⁻¹ := by group
      rw [hxeq]
      exact mul_mem_sup hxbQ ((zpowers b).inv_mem (Subgroup.mem_zpowers b))
  calc Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G)))
      ≤ Nat.card ↥(Q ⊔ zpowers b) := Subgroup.card_le_of_le hle
    _ = 2 * Nat.card Q := by rw [sup_comm]; exact hprod

private theorem ThCyc.T_eq_sup_Q_S_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : T = Q ⊔ (S ⊔ zpowers t) := by
  classical
  have hRleT : Q ⊔ (S ⊔ zpowers t) ≤ T :=
    sup_le hT.Q_le (sup_le hT.S_le (zpowers_le.2 hT.t_mem))
  have hRleNQ : S ⊔ zpowers t ≤ normalizer (Q : Set G) :=
    (sup_le hT.S_le (zpowers_le.2 hT.t_mem)).trans
      (THyp.le_normalizer_Q H W W2 hD hQ hT)
  have hcardR : Nat.card ↥(S ⊔ zpowers t) = 2 ^ 16 := by
    rw [H.card_sup_zpowers W, ThLocalIn.card_S W]
    norm_num
  have hinfR : (S ⊔ zpowers t) ⊓ Q = Aa := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxR, hxQ⟩
      have hsub : (S ⊔ zpowers t : Subgroup G) ≤ centralizer ({t} : Set G) := by
        refine sup_le ?_ ?_
        · intro s hs
          exact mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (W.S_le hs)).symm
        · intro y hy
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          exact mem_centralizer_singleton_iff.2
            ((Commute.refl t).zpow_right k).eq.symm
      have hxt : x ∈ centralizer ({t} : Set G) := hsub hxR
      have hmem : x ∈ centralizer (D : Set G) ⊓ centralizer ({t} : Set G) :=
        ⟨hQ.le_centralizer hxQ, hxt⟩
      rwa [H.centralizer_D_inf_centralizer_t W W2 hD] at hmem
    · intro a ha
      exact ⟨Subgroup.mem_sup_left (W.B_le_S (W2.Aa_le ha)),
        hQ.D_le (hD.Aa_le ha)⟩
  have hprod := SylowEnd.card_sup_mul_card_inf (H := S ⊔ zpowers t) (K := Q) hRleNQ
  rw [hinfR, hcardR, W2.Aa_card] at hprod
  have hQcard : Nat.card ↥(Q ⊔ (S ⊔ zpowers t)) = 2 ^ 8 * Nat.card Q := by
    rw [sup_comm]
    have hright : (2 : ℕ) ^ 16 * Nat.card Q = (2 ^ 8 * Nat.card Q) * 2 ^ 8 := by ring
    rw [hright] at hprod
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 8) hprod
  have hcardT : Nat.card T ≤ Nat.card ↥(Q ⊔ (S ⊔ zpowers t)) := by
    rw [hQcard]
    have hK := H.card_le_mul_card_inf_K W W2 hD h4 hb hT.pgroup hT.le_normalizer
    have hQbound := H.card_inf_K_le_two_mul_card_Q W W2 hD h4 hb hQ hT hK1
    calc Nat.card T ≤ 128 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G))) := hK
      _ ≤ 128 * (2 * Nat.card Q) := Nat.mul_le_mul_left 128 hQbound
      _ = 2 ^ 8 * Nat.card Q := by ring
  exact (Subgroup.eq_of_le_of_card_ge hRleT hcardT).symm

private theorem THyp.exists_mul_Q_S_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) {x : G} (hx : x ∈ T) :
    ∃ q ∈ Q, ∃ s ∈ S, ∃ i : ℤ, x = q * s * t ^ i := by
  classical
  have hT_eq : T = Q ⊔ (S ⊔ zpowers t) := H.T_eq_sup_Q_S_t W W2 hD h4 hb hQ hT hK1
  have hxR : x ∈ Q ⊔ (S ⊔ zpowers t) := hT_eq ▸ hx
  have hRleNQ : S ⊔ zpowers t ≤ normalizer (Q : Set G) :=
    (sup_le hT.S_le (zpowers_le.2 hT.t_mem)).trans
      (THyp.le_normalizer_Q H W W2 hD hQ hT)
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left Q (S ⊔ zpowers t) hRleNQ] at hxR
  obtain ⟨q, hq, r, hr, hqr⟩ := hxR
  have hts : ∀ s ∈ S, t * s * t⁻¹ = s := fun s hs => by
    calc t * s * t⁻¹ = (s * t) * t⁻¹ := by rw [← H.comm_of_mem_L (W.S_le hs)]
      _ = s := by group
  have htNS : t ∈ normalizer (S : Set G) := by
    refine mem_normalizer_iff.2 fun s => ⟨?_, ?_⟩
    · intro hs
      rwa [hts s hs]
    · intro hs
      have e : t * (t * s * t⁻¹) * t⁻¹ = s := by
        have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
        calc t * (t * s * t⁻¹) * t⁻¹ = (t * t) * s * (t⁻¹ * t⁻¹) := by group
          _ = s := by rw [ht2, ← mul_inv_rev, ht2, inv_one, one_mul, mul_one]
      have hu : t * (t * s * t⁻¹) * t⁻¹ = t * s * t⁻¹ := hts (t * s * t⁻¹) hs
      have hs1 : t * (t * s * t⁻¹) * t⁻¹ ∈ S := by
        rw [hu]
        exact hs
      rwa [e] at hs1
  have hztS : zpowers t ≤ normalizer (S : Set G) := zpowers_le.2 htNS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left S (zpowers t) hztS] at hr
  obtain ⟨s, hs, u, hu, hsu⟩ := hr
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  exact ⟨q, hq, s, hs, i, by rw [← hqr, ← hsu]; group⟩

private noncomputable def ThCyc.Pcomm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) : Subgroup G where
  carrier := {x | x ∈ T ∧ ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Q}
  one_mem' := ⟨T.one_mem, fun y _ => by simp⟩
  mul_mem' := by
    rintro x z ⟨hxT, hx⟩ ⟨hzT, hz⟩
    refine ⟨T.mul_mem hxT hzT, fun y hy => ?_⟩
    have h1 : x * (z * y * z⁻¹ * y⁻¹) * x⁻¹ ∈ Q :=
      THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hxT (hz y hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ Q := hx y hy
    have e : (x * z) * y * (x * z)⁻¹ * y⁻¹ =
        x * (z * y * z⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem h1 h2
  inv_mem' := by
    rintro x ⟨hxT, hx⟩
    refine ⟨T.inv_mem hxT, fun y hy => ?_⟩
    have h1 : x⁻¹ * (x * y * x⁻¹ * y⁻¹) * x ∈ Q := by
      simpa using THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT (T.inv_mem hxT) (hx y hy)
    have e : x⁻¹ * y * (x⁻¹)⁻¹ * y⁻¹ =
        (x⁻¹ * (x * y * x⁻¹ * y⁻¹) * x)⁻¹ := by group
    rw [e]
    exact Q.inv_mem h1

private theorem ThCyc.mem_Pcomm_iff (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) {x : G} :
    x ∈ Pcomm H W W2 hD hQ hT ↔ x ∈ T ∧
      ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Q := Iff.rfl

private theorem ThCyc.Pcomm_conj_mem (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) {g : G} (hgT : g ∈ normalizer (T : Set G))
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    ∀ x ∈ Pcomm H W W2 hD hQ hT, g * x * g⁻¹ ∈ Pcomm H W W2 hD hQ hT := by
  intro x hx
  rw [ThCyc.mem_Pcomm_iff] at hx ⊢
  refine ⟨(mem_normalizer_iff.1 hgT x).1 hx.1, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ T := by
    simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) y).1 hy
  have hc : x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹ ∈ Q := hx.2 _ hy'
  have hconj := hgQ _ hc
  have e : (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
      g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact hconj

private theorem ThCyc.Q_le_Pcomm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) : Q ≤ Pcomm H W W2 hD hQ hT := by
  intro q hq
  rw [ThCyc.mem_Pcomm_iff]
  refine ⟨hT.Q_le hq, fun y hy => ?_⟩
  have hyq : y * q⁻¹ * y⁻¹ ∈ Q :=
    THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hy (Q.inv_mem hq)
  have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
  rw [e]
  exact Q.mul_mem hq hyq

private theorem ThCyc.B_le_Pcomm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : B ≤ Pcomm H W W2 hD hQ hT := by
  intro β hβB
  rw [ThCyc.mem_Pcomm_iff]
  refine ⟨hT.S_le (W.B_le_S hβB), fun y hy => ?_⟩
  obtain ⟨q, hq, s, hs, i, rfl⟩ :=
    THyp.exists_mul_Q_S_t H W W2 hD h4 hb hQ hT hK1 hy
  have hβT : β ∈ T := hT.S_le (W.B_le_S hβB)
  have hqT : q ∈ T := hT.Q_le hq
  have hsT : s ∈ T := hT.S_le hs
  have hβq : β * q * β⁻¹ * q⁻¹ ∈ Q := by
    have h1 : β * q * β⁻¹ ∈ Q := THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hβT hq
    have e : β * q * β⁻¹ * q⁻¹ = (β * q * β⁻¹) * q⁻¹ := by group
    rw [e]
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hβs : β * s * β⁻¹ * s⁻¹ ∈ Aa := W2.comm_mem_Aa W hβB hs
  have hβsQ : β * s * β⁻¹ * s⁻¹ ∈ Q := hQ.D_le (hD.Aa_le hβs)
  have hβti : β * t ^ i * β⁻¹ * (t ^ i)⁻¹ = 1 := by
    have htβ : Commute β t := (H.comm_of_mem_L (W.S_le (W.B_le_S hβB))).symm
    rw [(htβ.zpow_right i).eq]
    group
  have hβtiQ : β * t ^ i * β⁻¹ * (t ^ i)⁻¹ ∈ Q := by rw [hβti]; exact Q.one_mem
  have hβsti : β * (s * t ^ i) * β⁻¹ * (s * t ^ i)⁻¹ ∈ Q :=
    THyp.commutator_mul_mem_Q H W W2 hD hQ hT hsT hβsQ hβtiQ
  have hβqsti : β * (q * (s * t ^ i)) * β⁻¹ * (q * (s * t ^ i))⁻¹ ∈ Q :=
    THyp.commutator_mul_mem_Q H W W2 hD hQ hT hqT hβq hβsti
  simpa [mul_assoc] using hβqsti

private theorem ThCyc.zpowers_t_le_Pcomm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : zpowers t ≤ Pcomm H W W2 hD hQ hT := by
  rw [zpowers_le, ThCyc.mem_Pcomm_iff]
  refine ⟨hT.t_mem, fun y hy => ?_⟩
  obtain ⟨q, hq, s, hs, j, rfl⟩ :=
    THyp.exists_mul_Q_S_t H W W2 hD h4 hb hQ hT hK1 hy
  have hqT : q ∈ T := hT.Q_le hq
  have hsT : s ∈ T := hT.S_le hs
  have htq : t * q * t⁻¹ * q⁻¹ ∈ Q := by
    have h1 : t * q * t⁻¹ ∈ Q :=
      THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hT.t_mem hq
    have e : t * q * t⁻¹ * q⁻¹ = (t * q * t⁻¹) * q⁻¹ := by group
    rw [e]
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hts : t * s * t⁻¹ * s⁻¹ = 1 := by
    have hcomm : Commute t s := H.comm_of_mem_L (W.S_le hs)
    rw [hcomm.eq]
    group
  have htsQ : t * s * t⁻¹ * s⁻¹ ∈ Q := by rw [hts]; exact Q.one_mem
  have httj : t * t ^ j * t⁻¹ * (t ^ j)⁻¹ = 1 := by
    have hcomm : Commute t (t ^ j) := (Commute.refl t).zpow_right j
    rw [hcomm.eq]
    group
  have httjQ : t * t ^ j * t⁻¹ * (t ^ j)⁻¹ ∈ Q := by
    rw [httj]; exact Q.one_mem
  have hstj : t * (s * t ^ j) * t⁻¹ * (s * t ^ j)⁻¹ ∈ Q :=
    THyp.commutator_mul_mem_Q H W W2 hD hQ hT hsT htsQ httjQ
  have hqtj : t * (q * (s * t ^ j)) * t⁻¹ * (q * (s * t ^ j))⁻¹ ∈ Q :=
    THyp.commutator_mul_mem_Q H W W2 hD hQ hT hqT htq hstj
  simpa [mul_assoc] using hqtj

private theorem ThCyc.Pcomm_le_sup (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : Pcomm H W W2 hD hQ hT ≤ Q ⊔ B ⊔ zpowers t := by
  intro x hx
  rw [ThCyc.mem_Pcomm_iff] at hx
  obtain ⟨q, hq, s, hs, i, hxeq⟩ :=
    THyp.exists_mul_Q_S_t H W W2 hD h4 hb hQ hT hK1 hx.1
  have hsB : s ∈ B := by
    refine F.center_quotient s hs ?_
    intro s' hs'
    have hs'T : s' ∈ T := hT.S_le hs'
    have htcomm : t ^ i * s' = s' * t ^ i :=
      ((show Commute t s' from (H.comm_of_mem_L (W.S_le hs'))).zpow_left i).eq
    have hd : s' * q⁻¹ * s'⁻¹ ∈ Q :=
      THyp.conj_mem_Q_of_mem_T H W W2 hD hQ hT hs'T (Q.inv_mem hq)
    have hbig : q * (s * s' * s⁻¹ * s'⁻¹) * (s' * q⁻¹ * s'⁻¹) ∈ Q := by
      have hxcomm : x * s' * x⁻¹ * s'⁻¹ ∈ Q := hx.2 s' hs'T
      rw [hxeq] at hxcomm
      have htconj : t ^ i * s' * (t ^ i)⁻¹ = s' := by
        calc t ^ i * s' * (t ^ i)⁻¹ = (s' * t ^ i) * (t ^ i)⁻¹ := by rw [htcomm]
          _ = s' := by group
      have heq : (q * s * t ^ i) * s' * (q * s * t ^ i)⁻¹ * s'⁻¹ =
          q * s * (t ^ i * s' * (t ^ i)⁻¹) * s⁻¹ * q⁻¹ * s'⁻¹ := by group
      rw [heq, htconj] at hxcomm
      have heq2 : q * (s * s' * s⁻¹ * s'⁻¹) * (s' * q⁻¹ * s'⁻¹) =
          q * s * s' * s⁻¹ * q⁻¹ * s'⁻¹ := by group
      rw [heq2]
      exact hxcomm
    have hc : s * s' * s⁻¹ * s'⁻¹ ∈ Q := by
      have h1 : q⁻¹ * (q * (s * s' * s⁻¹ * s'⁻¹) * (s' * q⁻¹ * s'⁻¹)) *
          (s' * q⁻¹ * s'⁻¹)⁻¹ ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hbig) (Q.inv_mem hd)
      have e : q⁻¹ * (q * (s * s' * s⁻¹ * s'⁻¹) * (s' * q⁻¹ * s'⁻¹)) *
          (s' * q⁻¹ * s'⁻¹)⁻¹ = s * s' * s⁻¹ * s'⁻¹ := by group
      rwa [e] at h1
    have hss'L : s * s' * s⁻¹ * s'⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (W.S_le hs) (W.S_le hs'))
        (L.inv_mem (W.S_le hs))) (L.inv_mem (W.S_le hs'))
    rw [← H.Q_inf_L_eq_Aa W W2 hD hQ]
    exact ⟨hc, hss'L⟩
  rw [hxeq]
  exact ((Q ⊔ B) ⊔ zpowers t).mul_mem
    (((Q ⊔ B) ⊔ zpowers t).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hq))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hsB)))
    (Subgroup.mem_sup_right
      (Subgroup.zpow_mem (zpowers t) (Subgroup.mem_zpowers t) i))

private theorem ThCyc.Pcomm_le_centralizer_A (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : Pcomm H W W2 hD hQ hT ≤ centralizer (A : Set G) := by
  refine (H.Pcomm_le_sup W W2 hD F h4 hb hQ hT hK1).trans ?_
  refine sup_le (sup_le ?_ ?_) ?_
  · intro q hq
    exact mem_centralizer_iff.2 fun a ha =>
      mem_centralizer_iff.1 (hQ.le_centralizer hq) a (hD.Aa_le (W2.A_le ha))
  · intro β hβB
    exact mem_centralizer_iff.2 fun a ha =>
      ((W.mem_B_iff β (W.B_le hβB)).1 hβB a ha).symm
  · intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    refine mem_centralizer_iff.2 fun a ha => ?_
    have hcomm : Commute a t :=
      (H.comm_of_mem_L (W.S_le ((W.mem_A_iff a).1 ha).1)).symm
    exact (hcomm.zpow_right k).eq

private theorem ThCyc.A_le_Pcomm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) : A ≤ Pcomm H W W2 hD hQ hT := fun a ha =>
  H.Q_le_Pcomm W W2 hD hQ hT (hQ.D_le (hD.Aa_le (W2.A_le ha)))

private theorem ThCyc.A_le_centralizer_Pcomm (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : A ≤ centralizer (Pcomm H W W2 hD hQ hT : Set G) := by
  intro a ha
  refine mem_centralizer_iff.2 fun p hp => ?_
  exact (mem_centralizer_iff.1
    (H.Pcomm_le_centralizer_A W W2 hD F h4 hb hQ hT hK1 hp) a ha).symm

private theorem ThCyc.inf_centralizer_Pcomm_eq_A (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) :
    Pcomm H W W2 hD hQ hT ⊓ centralizer (Pcomm H W W2 hD hQ hT : Set G) = A := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨hzP, hzC⟩
    have hzT : z ∈ T := ((H.mem_Pcomm_iff W W2 hD hQ hT).1 hzP).1
    have hzD : z ∈ centralizer (D : Set G) := by
      refine mem_centralizer_iff.2 fun d hd => ?_
      exact mem_centralizer_iff.1 hzC d
        (H.Q_le_Pcomm W W2 hD hQ hT (hQ.D_le hd))
    have hzQ : z ∈ Q := by
      have hmem : z ∈ T ⊓ centralizer (D : Set G) := ⟨hzT, hzD⟩
      rwa [THyp.inf_centralizer_eq hQ hT] at hmem
    have hzAa : z ∈ Aa := by
      have htP : t ∈ Pcomm H W W2 hD hQ hT :=
        H.zpowers_t_le_Pcomm W W2 hD h4 hb hQ hT hK1 (Subgroup.mem_zpowers t)
      have hzt : z ∈ centralizer ({t} : Set G) :=
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzC t htP).symm
      have hmem : z ∈ Q ⊓ centralizer ({t} : Set G) := ⟨hzQ, hzt⟩
      rwa [QHyp.inf_centralizer_t_eq H W W2 hD hQ] at hmem
    have hbP : b ∈ Pcomm H W W2 hD hQ hT :=
      H.B_le_Pcomm W W2 hD h4 hb hQ hT hK1 W2.b_mem
    have hbz : b * z * b⁻¹ = z⁻¹ := W2.b_inv z hzAa
    have hzb : b * z = z * b := mem_centralizer_iff.1 hzC b hbP
    have hz_eq : z = z⁻¹ := by
      rw [← hbz]
      calc z = (z * b) * b⁻¹ := by group
        _ = (b * z) * b⁻¹ := by rw [← hzb]
        _ = b * z * b⁻¹ := rfl
    have hz2 : z * z = 1 := by
      simpa [hz_eq.symm] using mul_inv_cancel z
    have hzV : z ∈ omega1 D hD.comm :=
      ⟨hD.Aa_le hzAa, by rw [pow_two]; exact hz2⟩
    rw [← H.omega1_inf_Aa W W2 hD]
    exact ⟨hzV, hzAa⟩
  · intro a ha
    exact ⟨H.A_le_Pcomm W W2 hD hQ hT ha,
      H.A_le_centralizer_Pcomm W W2 hD F h4 hb hQ hT hK1 ha⟩

theorem ThCyc.false_of_inf_K_le_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {Q T : Subgroup G} (hQ : QHyp L A D t Q) (hT : THyp S D Q t T) {g : G}
    (hgT : g ∈ normalizer (T : Set G)) (hgM : g ∉ normalizer (D : Set G))
    (hK1 : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
      ThCyc.K1 H W W2 hD h4) : False := by
  have hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT hgT
  have hgT' : g⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hgT
  have hgQ' : ∀ q ∈ Q, g⁻¹ * q * (g⁻¹)⁻¹ ∈ Q :=
    THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT hgT'
  have hPconj : ∀ x ∈ Pcomm H W W2 hD hQ hT, g * x * g⁻¹ ∈ Pcomm H W W2 hD hQ hT :=
    H.Pcomm_conj_mem W W2 hD hQ hT hgT hgQ
  have hPconj' : ∀ x ∈ Pcomm H W W2 hD hQ hT,
      g⁻¹ * x * g ∈ Pcomm H W W2 hD hQ hT := by
    intro x hx
    simpa only [inv_inv] using H.Pcomm_conj_mem W W2 hD hQ hT hgT' hgQ' x hx
  have hZA : Pcomm H W W2 hD hQ hT ⊓
      centralizer (Pcomm H W W2 hD hQ hT : Set G) = A :=
    H.inf_centralizer_Pcomm_eq_A W W2 hD F h4 hb hQ hT hK1
  have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro a ha
    have haP : a ∈ Pcomm H W W2 hD hQ hT := H.A_le_Pcomm W W2 hD hQ hT ha
    have haC : a ∈ centralizer (Pcomm H W W2 hD hQ hT : Set G) :=
      H.A_le_centralizer_Pcomm W W2 hD F h4 hb hQ hT hK1 ha
    have hconjP : g * a * g⁻¹ ∈ Pcomm H W W2 hD hQ hT := hPconj a haP
    have hconjC : g * a * g⁻¹ ∈ centralizer (Pcomm H W W2 hD hQ hT : Set G) := by
      refine mem_centralizer_iff.2 fun p hp => ?_
      have hp' : g⁻¹ * p * g ∈ Pcomm H W W2 hD hQ hT := hPconj' p hp
      have hcomm : (g⁻¹ * p * g) * a = a * (g⁻¹ * p * g) :=
        mem_centralizer_iff.1 haC (g⁻¹ * p * g) hp'
      calc p * (g * a * g⁻¹) = g * ((g⁻¹ * p * g) * a) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * p * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * a * g⁻¹) * p := by group
    have hmem : g * a * g⁻¹ ∈ Pcomm H W W2 hD hQ hT ⊓
        centralizer (Pcomm H W W2 hD hQ hT : Set G) := ⟨hconjP, hconjC⟩
    rwa [hZA] at hmem
  exact hgM (QHyp.mem_normalizer_D_of_conj_mem_A H W W2 hD h4 hQ hgQ hgA)

end CFSG.EvenSporadicStandard.ThStd
