module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.EndgameHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerDIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.OmegaOneInvariant

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D Q T : Subgroup G} {z b : G}

theorem QHyp.inf_centralizer_t_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) :
    Q ⊓ centralizer ({t} : Set G) = Aa := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxQ, hxt⟩
    have hxC : x ∈ centralizer (D : Set G) := hQ.le_centralizer hxQ
    rw [← H.centralizer_D_inf_centralizer_t W W2 hD]
    exact ⟨hxC, hxt⟩
  · intro a ha
    exact ⟨hQ.D_le (hD.Aa_le ha),
      mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (W.B_le (W2.Aa_le ha))).symm⟩

theorem QHyp.mem_omega1_iff (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {q : G} (hq : q ∈ Q) :
    q ∈ omega1 D hD.comm ↔ q ^ 2 = 1 :=
  ⟨fun h => h.2, fun h => ⟨hQ.mem_of_sq_eq_one q hq h, h⟩⟩

theorem QHyp.sq_mem_A_iff (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hQ : QHyp L A D t Q) {q : G} (hq : q ∈ Q) : q ^ 2 ∈ A ↔ q ∈ D := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hVD : omega1 D hD.comm ≤ D := fun _ h => h.1
  constructor
  · intro hq2
    let Y : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ x ^ 2 ∈ A}
        one_mem' := ⟨Q.one_mem, by simpa using A.one_mem⟩
        mul_mem' := by
          rintro x y ⟨hxQ, hxA⟩ ⟨hyQ, hyA⟩
          refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
          rw [(show Commute x y from hQ.comm x hxQ y hyQ).mul_pow]
          exact A.mul_mem hxA hyA
        inv_mem' := by
          rintro x ⟨hxQ, hxA⟩
          refine ⟨Q.inv_mem hxQ, ?_⟩
          rw [inv_pow]
          exact A.inv_mem hxA }
    have hYQ : Y ≤ Q := fun x hx => hx.1
    have hVY : omega1 D hD.comm ≤ Y := by
      intro v hv
      exact ⟨hQ.D_le (hVD hv), by rw [hv.2]; exact A.one_mem⟩
    let σ : ↥Y →* ↥A :=
      { toFun := fun x => ⟨(x : G) ^ 2, x.2.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          show ((x : G) * (y : G)) ^ 2 = (x : G) ^ 2 * (y : G) ^ 2
          exact (show Commute x.1 y.1 from hQ.comm x.1 x.2.1 y.1 y.2.1).mul_pow 2) }
    have hker : σ.ker = (omega1 D hD.comm).subgroupOf Y := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact ⟨fun h => (QHyp.mem_omega1_iff hD hQ (hYQ x.2)).2 (congrArg Subtype.val h),
        fun h => Subtype.ext ((QHyp.mem_omega1_iff hD hQ (hYQ x.2)).1 h)⟩
    have hrange : σ.range = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨d, hd, hd2⟩ := (W2.A_eq_sq (a : G)).1 a.2
      have hdD : d ∈ D := hD.Aa_le hd
      refine ⟨⟨d, hQ.D_le hdD, ?_⟩, Subtype.ext hd2⟩
      rw [hd2]
      exact a.2
    have hYcard : Nat.card ↥Y = 2 ^ 12 := by
      have h1 := Subgroup.card_ker_mul_card_range σ
      have hk : Nat.card ↥σ.ker = 2 ^ 8 := by
        rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv]
        exact H.card_omega1 W W2 hD hsq
      have hr : Nat.card ↥σ.range = 16 := by
        rw [hrange, Subgroup.card_top]
        exact W.A_card
      rw [hk, hr] at h1
      rw [← h1]
      norm_num
    have hDY : D ≤ Y := fun d hd => ⟨hQ.D_le hd, hsq d hd⟩
    have hYD : D = Y := Subgroup.eq_of_le_of_card_ge hDY (by rw [hYcard, hD.card])
    exact hYD.symm ▸ ⟨hq, hq2⟩
  · intro hqD
    exact hsq q hqD

private theorem QHyp.mul_conj_t_mem_Aa (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {q : G}
    (hq : q ∈ Q) : q * (t * q * t⁻¹) ∈ Aa := by
  have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
  have hti2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
  have hconj : t * (q * (t * q * t⁻¹)) * t⁻¹ = q * (t * q * t⁻¹) := by
    calc t * (q * (t * q * t⁻¹)) * t⁻¹
        = (t * q * t⁻¹) * (t * (t * q * t⁻¹) * t⁻¹) := by group
      _ = (t * q * t⁻¹) * q := by
          rw [show t * (t * q * t⁻¹) * t⁻¹ = q by
            calc t * (t * q * t⁻¹) * t⁻¹ = (t * t) * q * (t⁻¹ * t⁻¹) := by group
              _ = q := by rw [ht2, hti2]; group]
      _ = q * (t * q * t⁻¹) := hQ.comm _ (hQ.conj_t_mem q hq) _ hq
  have hcomm : (q * (t * q * t⁻¹)) * t = t * (q * (t * q * t⁻¹)) := by
    calc (q * (t * q * t⁻¹)) * t = (t * (q * (t * q * t⁻¹)) * t⁻¹) * t := by rw [hconj]
      _ = t * (q * (t * q * t⁻¹)) := by group
  rw [← QHyp.inf_centralizer_t_eq H W W2 hD hQ]
  exact ⟨Q.mul_mem hq (hQ.conj_t_mem q hq), mem_centralizer_singleton_iff.2 hcomm⟩

private theorem QHyp.conj_fourth (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {q : G}
    (hq : q ∈ Q) : t * q ^ 4 * t⁻¹ = (q ^ 4)⁻¹ := by
  have hu : q * (t * q * t⁻¹) ∈ Aa := QHyp.mul_conj_t_mem_Aa H W W2 hD hQ hq
  have hu4 : (q * (t * q * t⁻¹)) ^ 4 = 1 := W2.Aa_exp _ hu
  have hmul : (q * (t * q * t⁻¹)) ^ 4 = q ^ 4 * (t * q ^ 4 * t⁻¹) := by
    rw [(show Commute q (t * q * t⁻¹) from hQ.comm q hq _ (hQ.conj_t_mem q hq)).mul_pow, conj_pow]
  rw [hmul] at hu4
  exact eq_inv_of_mul_eq_one_right hu4

private def QHyp.powImage (hQ : QHyp L A D t Q) (k : ℕ) : Subgroup G where
  carrier := {z | ∃ q ∈ Q, q ^ 2 ^ k = z}
  one_mem' := ⟨1, Q.one_mem, by simp⟩
  mul_mem' := by
    rintro z w ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
    exact ⟨q * q', Q.mul_mem hq hq', (show Commute q q' from hQ.comm q hq q' hq').mul_pow (2 ^ k)⟩
  inv_mem' := by
    rintro z ⟨q, hq, rfl⟩
    exact ⟨q⁻¹, Q.inv_mem hq, by rw [inv_pow]⟩

private theorem QHyp.mem_powImage (hQ : QHyp L A D t Q) (k : ℕ) {z : G} :
    z ∈ hQ.powImage k ↔ ∃ q ∈ Q, q ^ 2 ^ k = z := Iff.rfl

private def QHyp.powHom (hQ : QHyp L A D t Q) (k : ℕ) : ↥Q →* ↥Q where
  toFun q := ⟨q.1 ^ 2 ^ k, Q.pow_mem q.2 _⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' x y := Subtype.ext ((show Commute x.1 y.1 from hQ.comm x.1 x.2 y.1 y.2).mul_pow (2 ^ k))

private theorem QHyp.powImage_le_omega1 (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {k : ℕ}
    (hk : ∀ q ∈ Q, q ^ 2 ^ (k + 1) = 1) : hQ.powImage k ≤ omega1 D hD.comm := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := (QHyp.mem_powImage hQ k).1 hz
  have hqQ : q ^ 2 ^ k ∈ Q := Q.pow_mem hq _
  refine (QHyp.mem_omega1_iff hD hQ hqQ).2 ?_
  rw [← pow_mul, show 2 ^ k * 2 = 2 ^ (k + 1) from (pow_succ 2 k).symm]
  exact hk q hq

private theorem QHyp.powImage_normalized (hQ : QHyp L A D t Q) (k : ℕ) :
    (∀ n ∈ L ⊓ normalizer (A : Set G), ∀ z ∈ hQ.powImage k, n * z * n⁻¹ ∈ hQ.powImage k) ∧
      (∀ z ∈ hQ.powImage k, t * z * t⁻¹ ∈ hQ.powImage k) := by
  constructor
  · rintro n hn z hz
    obtain ⟨q, hq, rfl⟩ := (QHyp.mem_powImage hQ k).1 hz
    rw [← conj_pow]
    exact (QHyp.mem_powImage hQ k).2 ⟨n * q * n⁻¹, hQ.conj_mem n hn q hq, rfl⟩
  · rintro z hz
    obtain ⟨q, hq, rfl⟩ := (QHyp.mem_powImage hQ k).1 hz
    rw [← conj_pow]
    exact (QHyp.mem_powImage hQ k).2 ⟨t * q * t⁻¹, hQ.conj_t_mem q hq, rfl⟩

private theorem QHyp.powImage_ne_bot (hQ : QHyp L A D t Q) {k : ℕ}
    (hk : ¬ ∀ q ∈ Q, q ^ 2 ^ k = 1) : hQ.powImage k ≠ ⊥ := by
  intro hbot
  apply hk
  intro q hq
  have hmem : q ^ 2 ^ k ∈ hQ.powImage k := (QHyp.mem_powImage hQ k).2 ⟨q, hq, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

private theorem QHyp.powImage_eq_range (hQ : QHyp L A D t Q) (k : ℕ) :
    hQ.powImage k = (hQ.powHom k).range.map Q.subtype := by
  ext z
  rw [QHyp.mem_powImage, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q ^ 2 ^ k, Q.pow_mem hq _⟩, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨x, hx⟩, hz⟩
    exact ⟨x.1, x.2, by rw [← hz, ← hx]; rfl⟩

theorem QHyp.pow_eq_A_or_exponent_four (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hQ : QHyp L A D t Q) :
    (∃ k : ℕ, ∀ a : G, a ∈ A ↔ ∃ q ∈ Q, q ^ 2 ^ k = a) ∨
      ((∀ q ∈ Q, q ^ 4 = 1) ∧ (∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) ∧
        Nat.card Q = 2 ^ 16) := by
  classical
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hVcard : Nat.card (omega1 D hD.comm) = 2 ^ 8 := H.card_omega1 W W2 hD hsq
  have hVQ : omega1 D hD.comm ≤ Q := by
    intro v hv
    exact hQ.D_le hv.1
  have hex : ∃ k : ℕ, ∀ q ∈ Q, q ^ 2 ^ k = 1 := by
    obtain ⟨n, hn⟩ := hQ.pgroup.exists_card_eq
    refine ⟨n, fun q hq => ?_⟩
    haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
    have hdvd : orderOf q ∣ Nat.card ↥Q := by
      have h : orderOf (⟨q, hq⟩ : ↥Q) ∣ Nat.card ↥Q := by
        rw [Nat.card_eq_fintype_card]
        exact orderOf_dvd_card
      rwa [Subgroup.orderOf_mk] at h
    rw [hn] at hdvd
    exact (orderOf_dvd_iff_pow_eq_one).1 hdvd
  obtain ⟨e, he, he_min⟩ : ∃ e : ℕ, (∀ q ∈ Q, q ^ 2 ^ e = 1) ∧
      ∀ k < e, ¬ ∀ q ∈ Q, q ^ 2 ^ k = 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have he2 : 2 ≤ e := by
    rcases lt_or_ge e 2 with h | h
    · interval_cases e
      · have hbot : Q = ⊥ := by
          refine eq_bot_iff.2 fun q hq => ?_
          have h1 := he q hq
          simpa using h1
        have hle : Nat.card ↥D ≤ Nat.card ↥Q := Subgroup.card_le_of_le hQ.D_le
        rw [hbot, Subgroup.card_bot, hD.card] at hle
        norm_num at hle
      · have hleQ : Q ≤ omega1 D hD.comm := fun q hq =>
          (QHyp.mem_omega1_iff hD hQ hq).2 (by simpa using he q hq)
        have hcard : Nat.card ↥Q ≤ 2 ^ 8 := (Subgroup.card_le_of_le hleQ).trans_eq hVcard
        have hle : Nat.card ↥D ≤ Nat.card ↥Q := Subgroup.card_le_of_le hQ.D_le
        have hle2 : Nat.card ↥D ≤ 2 ^ 8 := hle.trans hcard
        rw [hD.card] at hle2
        norm_num at hle2
    · exact h
  have hXle : hQ.powImage (e - 1) ≤ omega1 D hD.comm := by
    refine QHyp.powImage_le_omega1 hD hQ ?_
    intro q hq
    rw [show e - 1 + 1 = e by omega]
    exact he q hq
  obtain ⟨hXH, hXt⟩ := QHyp.powImage_normalized hQ (e - 1)
  have hXne : hQ.powImage (e - 1) ≠ ⊥ :=
    QHyp.powImage_ne_bot hQ (fun hall => he_min (e - 1) (by omega) hall)
  have hAX : A ≤ hQ.powImage (e - 1) := H.A_le_of_conj_mem W W2 hD hXle hXH hXt hXne
  rcases lt_or_ge e 3 with he3 | he3
  · have heq : e = 2 := by omega
    have he1 : e - 1 = 1 := by omega
    rcases H.eq_A_or_eq_omega1 W W2 hD h4 hAX hXle hXH with hXA | hXV
    · left
      have hk : 2 ^ (e - 1) = 2 := by rw [he1]; norm_num
      refine ⟨1, fun a => ⟨fun ha => ?_, ?_⟩⟩
      · have hmem : a ∈ hQ.powImage (e - 1) := by rw [hXA]; exact ha
        obtain ⟨q, hq, hqa⟩ := (QHyp.mem_powImage hQ (e - 1)).1 hmem
        exact ⟨q, hq, by rw [show (2 : ℕ) ^ 1 = 2 ^ (e - 1) from hk.symm]; exact hqa⟩
      · rintro ⟨q, hq, hqa⟩
        have hmem : q ^ 2 ^ (e - 1) ∈ hQ.powImage (e - 1) :=
          (QHyp.mem_powImage hQ (e - 1)).2 ⟨q, hq, rfl⟩
        rw [hXA] at hmem
        have h2 : q ^ 2 ^ (e - 1) = q ^ 2 ^ 1 := by rw [hk]; norm_num
        rw [h2] at hmem
        rwa [hqa] at hmem
    · right
      have hX1 : hQ.powImage 1 = omega1 D hD.comm := by rw [← he1]; exact hXV
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        have h1 := he q hq
        rw [heq] at h1
        norm_num at h1
        exact h1
      · intro v hv
        have hmem : v ∈ hQ.powImage (e - 1) := by rw [hXV]; exact hv
        obtain ⟨q, hq, hqa⟩ := (QHyp.mem_powImage hQ (e - 1)).1 hmem
        refine ⟨q, hq, ?_⟩
        have hk : 2 ^ (e - 1) = 2 := by rw [he1]; norm_num
        rw [hk] at hqa
        exact hqa
      · have h1 := Subgroup.card_ker_mul_card_range (hQ.powHom 1)
        have hker : Nat.card ↥(hQ.powHom 1).ker = 2 ^ 8 := by
          have heqker : (hQ.powHom 1).ker = (omega1 D hD.comm).subgroupOf Q := by
            ext x
            rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
            exact ⟨fun h => (QHyp.mem_omega1_iff hD hQ x.2).2 (congrArg Subtype.val h),
              fun h => Subtype.ext ((QHyp.mem_omega1_iff hD hQ x.2).1 h)⟩
          rw [heqker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVQ).toEquiv]
          exact hVcard
        have hrange : Nat.card ↥(hQ.powHom 1).range = 2 ^ 8 := by
          have hmap : (hQ.powHom 1).range.map Q.subtype = omega1 D hD.comm := by
            rw [← QHyp.powImage_eq_range hQ 1, hX1]
          calc Nat.card ↥(hQ.powHom 1).range
              = Nat.card ↥((hQ.powHom 1).range.map Q.subtype) :=
                (Subgroup.card_map_of_injective (K := (hQ.powHom 1).range)
                  Q.subtype_injective).symm
            _ = Nat.card ↥(omega1 D hD.comm) := by rw [hmap]
            _ = 2 ^ 8 := hVcard
        rw [hker, hrange] at h1
        rw [← h1]
        norm_num
  · have he3' : 3 ≤ e := he3
    have htriv : ∀ z ∈ hQ.powImage (e - 1), t * z * t⁻¹ = z := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := (QHyp.mem_powImage hQ (e - 1)).1 hz
      have hq4 : t * q ^ 4 * t⁻¹ = (q ^ 4)⁻¹ := QHyp.conj_fourth H W W2 hD hQ hq
      have harith : q ^ 2 ^ (e - 1) = (q ^ 4) ^ 2 ^ (e - 3) := by
        rw [← pow_mul]
        congr 1
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      have hz2 : (q ^ 2 ^ (e - 1)) ^ 2 = 1 := (hXle ⟨q, hq, rfl⟩).2
      calc t * q ^ 2 ^ (e - 1) * t⁻¹
          = t * (q ^ 4) ^ 2 ^ (e - 3) * t⁻¹ := by rw [harith]
        _ = (t * q ^ 4 * t⁻¹) ^ 2 ^ (e - 3) :=
            (conj_pow (a := t) (b := q ^ 4) (i := 2 ^ (e - 3))).symm
        _ = ((q ^ 4)⁻¹) ^ 2 ^ (e - 3) := by rw [hq4]
        _ = ((q ^ 4) ^ 2 ^ (e - 3))⁻¹ := inv_pow _ _
        _ = (q ^ 2 ^ (e - 1))⁻¹ := by rw [← harith]
        _ = q ^ 2 ^ (e - 1) := by
            refine inv_eq_of_mul_eq_one_right ?_
            rw [← sq]
            exact hz2
    have hXA : hQ.powImage (e - 1) = A := by
      refine le_antisymm ?_ hAX
      intro z hz
      have hzV : z ∈ omega1 D hD.comm := hXle hz
      have hzt : z ∈ centralizer ({t} : Set G) := by
        refine mem_centralizer_singleton_iff.2 ?_
        calc z * t = (t * z * t⁻¹) * t := by rw [htriv z hz]
          _ = t * z := by group
      have hmem : z ∈ omega1 D hD.comm ⊓ centralizer ({t} : Set G) := ⟨hzV, hzt⟩
      rwa [H.omega1_inf_centralizer_t W W2 hD] at hmem
    left
    refine ⟨e - 1, fun a => ⟨fun ha => ?_, ?_⟩⟩
    · have hmem : a ∈ hQ.powImage (e - 1) := by rw [hXA]; exact ha
      exact (QHyp.mem_powImage hQ (e - 1)).1 hmem
    · rintro ⟨q, hq, hqa⟩
      have hmem : q ^ 2 ^ (e - 1) ∈ hQ.powImage (e - 1) :=
        (QHyp.mem_powImage hQ (e - 1)).2 ⟨q, hq, rfl⟩
      rw [hXA] at hmem
      rwa [hqa] at hmem

theorem QHyp.eq_of_le_of_comm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    {Y : Subgroup G} (hYT : Y ≤ T) (hYA : Y ≤ centralizer (A : Set G))
    (hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hcard : Nat.card Q ≤ Nat.card Y) :
    Y = Q := by
  classical
  have hVcard : Nat.card (omega1 D hD.comm) = 2 ^ 8 :=
    H.card_omega1 W W2 hD (fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd)
  have hQT : Q ≤ T := hT.Q_le
  have hTN : T ≤ normalizer (D : Set G) := hT.le_normalizer
  have hQA : Q ≤ centralizer (A : Set G) :=
    hQ.le_centralizer.trans
      (Subgroup.centralizer_le (s := (A : Set G)) (t := (D : Set G)) fun a ha =>
        hD.Aa_le (W2.A_le ha))
  have hVQ : omega1 D hD.comm ≤ Q := by
    intro v hv
    exact hQ.D_le hv.1
  have hQHat : Q ≤ T ⊓ centralizer (A : Set G) := le_inf hQT hQA
  have hHatcard : Nat.card ↥(T ⊓ centralizer (A : Set G)) ≤ 8 * Nat.card ↥Q := by
    have hTKcard : Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G))) ≤ 4 * Nat.card ↥Q := by
      have hCK : centralizer (D : Set G) ≤
          normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
        centralizer_le_inf_normalizer_centralizer_omega1 hD.comm
      have hN : T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
          normalizer (centralizer (D : Set G) : Set G) := by
        intro y hy
        have hinv : y⁻¹ ∈ T ⊓ (normalizer (D : Set G) ⊓
            centralizer (omega1 D hD.comm : Set G)) :=
          (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))).inv_mem hy
        exact mem_normalizer_iff.2 fun c => ⟨fun hc =>
          normalizer_conj_mem_centralizer (m := y) (c := c) (hTN hy.1) hc,
          fun hc => by
            have h := normalizer_conj_mem_centralizer (m := y⁻¹) (c := y * c * y⁻¹)
              (hTN hinv.1) hc
            have e : y⁻¹ * (y * c * y⁻¹) * y⁻¹⁻¹ = c := by group
            rwa [e] at h⟩
      have hprod := SylowEnd.card_sup_mul_card_inf (H := T ⊓ (normalizer (D : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G))) (K := centralizer (D : Set G)) hN
      have hinf : (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) ⊓
          centralizer (D : Set G) = Q := by
        rw [inf_assoc, inf_comm (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
          (centralizer (D : Set G)), inf_eq_left.mpr hCK]
        exact THyp.inf_centralizer_eq hQ hT
      have hsup : (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) ⊔
          centralizer (D : Set G) ≤
          normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
        sup_le inf_le_right hCK
      have hKcard : Nat.card ↥(normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G)) ≤ 4 * Nat.card ↥(centralizer (D : Set G)) :=
        H.card_K_le_four_mul_card_centralizer W W2 hD h4 hb
      rw [hinf] at hprod
      have h1 : Nat.card ↥((T ⊓ (normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G))) ⊔ centralizer (D : Set G)) *
            Nat.card ↥Q ≤ (4 * Nat.card ↥(centralizer (D : Set G))) * Nat.card ↥Q :=
        Nat.mul_le_mul_right _ ((Subgroup.card_le_of_le hsup).trans hKcard)
      have h2 : Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G))) * Nat.card ↥(centralizer (D : Set G)) ≤
          (4 * Nat.card ↥Q) * Nat.card ↥(centralizer (D : Set G)) := by
        rw [← hprod]
        calc Nat.card ↥((T ⊓ (normalizer (D : Set G) ⊓
              centralizer (omega1 D hD.comm : Set G))) ⊔ centralizer (D : Set G)) *
              Nat.card ↥Q
            ≤ (4 * Nat.card ↥(centralizer (D : Set G))) * Nat.card ↥Q := h1
          _ = (4 * Nat.card ↥Q) * Nat.card ↥(centralizer (D : Set G)) := by ring
      exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
    have hsub : (T ⊓ centralizer (A : Set G) : Set G) ⊆
        (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G) ∪
          (fun z => t * z) ''
            (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G) := by
      intro x hx
      have hxN : x ∈ normalizer (D : Set G) := hTN hx.1
      have hxA : ∀ a ∈ A, x * a * x⁻¹ = a := by
        intro a ha
        have h := mem_centralizer_iff.1 hx.2 a ha
        calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [← h]
          _ = a := by group
      by_cases hxK : x ∈ normalizer (D : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G)
      · exact Or.inl ⟨hx.1, hxK⟩
      · rcases H.conj_omega1_eq_or_of_mem_normalizer_D W W2 hD h4 hb hxN hxA with htriv | ht
        · exact absurd ⟨hxN, mem_centralizer_iff.2 fun v hv => by
            have h := htriv v hv
            calc v * x = (x * v * x⁻¹) * x := by rw [h]
              _ = x * v := by group⟩ hxK
        · refine Or.inr ⟨t⁻¹ * x, ⟨T.mul_mem (T.inv_mem hT.t_mem) hx.1, ?_, ?_⟩, by group⟩
          · exact (normalizer (D : Set G)).mul_mem
              ((normalizer (D : Set G)).inv_mem (hTN hT.t_mem)) hxN
          · refine mem_centralizer_iff.2 fun v hv => ?_
            have h1 : (t⁻¹ * x) * v * (t⁻¹ * x)⁻¹ = v := by
              calc (t⁻¹ * x) * v * (t⁻¹ * x)⁻¹ = t⁻¹ * (x * v * x⁻¹) * t := by group
                _ = t⁻¹ * (t * v * t⁻¹) * t := by rw [ht v hv]
                _ = v := by group
            calc v * (t⁻¹ * x) = ((t⁻¹ * x) * v * (t⁻¹ * x)⁻¹) * (t⁻¹ * x) := by rw [h1]
              _ = (t⁻¹ * x) * v := by group
    have hfin : ((T ⊓ (normalizer (D : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G)) : Set G) ∪
          (fun z => t * z) ''
            (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
              Set G)).Finite :=
      Set.Finite.union (Set.toFinite _) (Set.toFinite _)
    have h1 : (T ⊓ centralizer (A : Set G) : Set G).ncard ≤
        ((T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
            Set G) ∪
          (fun z => t * z) ''
            (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
              Set G)).ncard :=
      Set.ncard_le_ncard hsub hfin
    have h2 : ((T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G) ∪
        (fun z => t * z) ''
          (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G)).ncard ≤
        (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G).ncard +
          ((fun z => t * z) ''
            (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
              Set G)).ncard :=
      Set.ncard_union_le _ _
    have h3 : ((fun z => t * z) ''
        (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
          Set G)).ncard =
        (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
          Set G).ncard :=
      Set.ncard_image_of_injective _ (mul_right_injective t)
    have hHat : Nat.card ↥(T ⊓ centralizer (A : Set G)) =
        (T ⊓ centralizer (A : Set G) : Set G).ncard := Nat.card_coe_set_eq _
    have hTK : Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G))) =
        (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
          Set G).ncard := Nat.card_coe_set_eq _
    rw [hHat]
    calc (T ⊓ centralizer (A : Set G) : Set G).ncard
        ≤ ((T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G) ∪
            (fun z => t * z) ''
              (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
                Set G)).ncard := h1
      _ ≤ (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
            Set G).ncard +
          ((fun z => t * z) ''
            (T ⊓ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
              Set G)).ncard := h2
      _ = 2 * Nat.card ↥(T ⊓ (normalizer (D : Set G) ⊓
            centralizer (omega1 D hD.comm : Set G))) := by rw [h3, hTK]; ring
      _ ≤ 2 * (4 * Nat.card ↥Q) := Nat.mul_le_mul_left 2 hTKcard
      _ = 8 * Nat.card ↥Q := by ring
  have hbound : ∀ x ∈ T ⊓ centralizer (A : Set G), x ∉ Q →
      Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 16 ≤ Nat.card ↥Q := by
    intro x hxH hxQ
    have hxN : x ∈ normalizer (D : Set G) := hTN hxH.1
    have hxA : ∀ a ∈ A, x * a * x⁻¹ = a := by
      intro a ha
      have h := mem_centralizer_iff.1 hxH.2 a ha
      calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [← h]
        _ = a := by group
    have hbK : b ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
      H.K1_le_K W W2 hD h4 (H.b_mem_K1 W W2 hD h4 hb)
    by_cases hxK : x ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)
    ·
      have hWD : Q ⊓ centralizer ({x} : Set G) ⊓ D = omega1 D hD.comm := by
        refine le_antisymm ?_ ?_
        · rintro d ⟨⟨hdQ, hdx⟩, hdD⟩
          have hxd : x * d * x⁻¹ = d := by
            have h1 : d * x = x * d := mem_centralizer_singleton_iff.1 hdx
            calc x * d * x⁻¹ = (d * x) * x⁻¹ := by rw [← h1]
              _ = d := by group
          have hphix : d⁻¹ * (x * d * x⁻¹) = 1 := by rw [hxd, inv_mul_cancel]
          have hmemV : d ∈ omega1 D hD.comm := by
            rcases H.mem_centralizer_or_mul_b_or_commutator_mul_b_mem_centralizer W W2 hD h4 hb
              x hxK with hC | hCb | hCtb
            · have hxTQ : x ∈ T ⊓ centralizer (D : Set G) := ⟨hxH.1, hC⟩
              rw [THyp.inf_centralizer_eq hQ hT] at hxTQ
              exact absurd hxTQ hxQ
            · have h1 : d⁻¹ * ((x * b) * d * (x * b)⁻¹) = 1 :=
                ThCyc.phi_centralizer_eq_one hCb hdD
              have h2 := H.conj_D_mul_mul_conj W W2 hD h4 hxK hbK hdD
              rw [h1, hphix, ThCyc.phi_b_eq_sq h4 hb hdD, one_mul] at h2
              exact ⟨hdD, h2.symm⟩
            · have hcommK : x * t * x⁻¹ * t⁻¹ ∈
                  normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
                H.commutator_t_mem_K W W2 hD hxK
              have h1 : d⁻¹ * (((x * t * x⁻¹ * t⁻¹) * b) * d *
                  (((x * t * x⁻¹ * t⁻¹) * b))⁻¹) = 1 :=
                ThCyc.phi_centralizer_eq_one hCtb hdD
              have h2 := H.conj_D_mul_mul_conj W W2 hD h4 hcommK hbK hdD
              rw [h1] at h2
              rw [H.phi_commutator W W2 hD h4 hxK hdD] at h2
              rw [hphix, ThCyc.phi_b_eq_sq h4 hb hdD, show thV t (1 : G) = 1 by simp [thV],
                one_mul] at h2
              exact ⟨hdD, h2.symm⟩
          exact hmemV
        · intro v hv
          exact ⟨⟨hQ.D_le hv.1, mem_centralizer_singleton_iff.2
            (mem_centralizer_iff.1 hxK.2 v hv)⟩, hv.1⟩
      have hprod := SylowEnd.card_sup_mul_card_inf (H := Q ⊓ centralizer ({x} : Set G)) (K := D)
        (fun y hy => Subgroup.centralizer_le_normalizer (D : Set G) (hQ.le_centralizer hy.1))
      rw [hWD] at hprod
      have hsup : Nat.card ↥((Q ⊓ centralizer ({x} : Set G)) ⊔ D) ≤ Nat.card ↥Q :=
        Subgroup.card_le_of_le (sup_le inf_le_left hQ.D_le)
      have h1 : Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * Nat.card ↥D ≤
          Nat.card ↥Q * Nat.card ↥(omega1 D hD.comm) := by
        rw [← hprod]
        exact Nat.mul_le_mul_right _ hsup
      rw [hD.card, hVcard] at h1
      have h2 : Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 16 * 2 ^ 8 ≤
          Nat.card ↥Q * 2 ^ 8 := by
        calc Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 16 * 2 ^ 8
            = Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 2 ^ 12 := by
              rw [mul_assoc, show (16 : ℕ) * 2 ^ 8 = 2 ^ 12 by norm_num]
          _ ≤ Nat.card ↥Q * 2 ^ 8 := h1
      exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
    ·
      have hxt : ∀ v ∈ omega1 D hD.comm, x * v * x⁻¹ = t * v * t⁻¹ := by
        rcases H.conj_omega1_eq_or_of_mem_normalizer_D W W2 hD h4 hb hxN hxA with h | h
        · exact absurd ⟨hxN, mem_centralizer_iff.2 fun v hv => by
            have h' := h v hv
            calc v * x = (x * v * x⁻¹) * x := by rw [h']
              _ = x * v := by group⟩ hxK
        · exact h
      have hWV : Q ⊓ centralizer ({x} : Set G) ⊓ omega1 D hD.comm = A := by
        refine le_antisymm ?_ ?_
        · rintro v ⟨⟨hvQ, hvx⟩, hvV⟩
          have h1 : x * v * x⁻¹ = v := by
            calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [← mem_centralizer_singleton_iff.1 hvx]
              _ = v := by group
          have h2 : t * v * t⁻¹ = v := by rw [← hxt v hvV, h1]
          have hvt : v ∈ centralizer ({t} : Set G) := by
            refine mem_centralizer_singleton_iff.2 ?_
            calc v * t = (t * v * t⁻¹) * t := by rw [h2]
              _ = t * v := by group
          have hmem : v ∈ omega1 D hD.comm ⊓ centralizer ({t} : Set G) := ⟨hvV, hvt⟩
          rwa [H.omega1_inf_centralizer_t W W2 hD] at hmem
        · intro a ha
          have haV : a ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD ha
          refine ⟨⟨hQ.D_le (hD.Aa_le (W2.A_le ha)), mem_centralizer_singleton_iff.2 ?_⟩, haV⟩
          calc a * x = (x * a * x⁻¹) * x := by rw [hxA a ha]
            _ = x * a := by group
      have hprod := SylowEnd.card_sup_mul_card_inf (H := Q ⊓ centralizer ({x} : Set G))
        (K := omega1 D hD.comm)
        (fun y hy => ThCyc.normalizer_D_le_normalizer_omega1 hD
          (Subgroup.centralizer_le_normalizer (D : Set G) (hQ.le_centralizer hy.1)))
      rw [hWV] at hprod
      have hsup : Nat.card ↥((Q ⊓ centralizer ({x} : Set G)) ⊔ omega1 D hD.comm) ≤
          Nat.card ↥Q :=
        Subgroup.card_le_of_le (sup_le inf_le_left hVQ)
      have h1 : Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * Nat.card ↥(omega1 D hD.comm) ≤
          Nat.card ↥Q * Nat.card ↥A := by
        rw [← hprod]
        exact Nat.mul_le_mul_right _ hsup
      rw [hVcard, W.A_card] at h1
      have h2 : Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 16 * 16 ≤
          Nat.card ↥Q * 16 := by
        calc Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 16 * 16
            = Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 2 ^ 8 := by
              rw [mul_assoc, show (16 : ℕ) * 16 = 2 ^ 8 by norm_num]
          _ ≤ Nat.card ↥Q * 16 := h1
      exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  by_contra hne
  have hnotle : ¬ Y ≤ Q := by
    intro hYQ
    exact hne (Subgroup.eq_of_le_of_card_ge hYQ hcard)
  obtain ⟨x, hxY, hxQ⟩ := Set.not_subset.1 hnotle
  have hxH : x ∈ T ⊓ centralizer (A : Set G) := ⟨hYT hxY, hYA hxY⟩
  have hxQ' : x ∉ Q := hxQ
  have hxbound := hbound x hxH hxQ'
  have hYQle : Y ⊓ Q ≤ Q ⊓ centralizer ({x} : Set G) := by
    rintro y ⟨hyY, hyQ⟩
    exact ⟨hyQ, mem_centralizer_singleton_iff.2 (hYc y hyY x hxY)⟩
  have hYH : Y ≤ T ⊓ centralizer (A : Set G) := le_inf hYT hYA
  have hpos : Q.relIndex (T ⊓ centralizer (A : Set G)) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card Q (T ⊓ centralizer (A : Set G))
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have hrel2 : Q.relIndex Y ≤ Q.relIndex (T ⊓ centralizer (A : Set G)) :=
    Subgroup.relIndex_le_of_le_right hYH hpos
  have hHatrel : Q.relIndex (T ⊓ centralizer (A : Set G)) ≤ 8 := by
    have h1 : Q.relIndex (T ⊓ centralizer (A : Set G)) * Nat.card ↥Q =
        Nat.card ↥(T ⊓ centralizer (A : Set G)) := by
      have := Subgroup.relIndex_mul_card Q (T ⊓ centralizer (A : Set G))
      rwa [inf_of_le_left hQHat] at this
    exact Nat.le_of_mul_le_mul_right (by rw [h1]; exact hHatcard) Nat.card_pos
  have hrel : (Y ⊓ Q).relIndex Y = Q.relIndex Y := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right Q Y
  have hYcard : Nat.card ↥Y ≤ 8 * Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) := by
    have h1 : (Y ⊓ Q).relIndex Y * Nat.card ↥(Y ⊓ Q) = Nat.card ↥Y := by
      have := Subgroup.relIndex_mul_card (Y ⊓ Q) Y
      rwa [inf_of_le_left inf_le_left] at this
    calc Nat.card ↥Y = (Y ⊓ Q).relIndex Y * Nat.card ↥(Y ⊓ Q) := h1.symm
      _ = Q.relIndex Y * Nat.card ↥(Y ⊓ Q) := by rw [hrel]
      _ ≤ Q.relIndex (T ⊓ centralizer (A : Set G)) *
            Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) :=
          Nat.mul_le_mul hrel2 (Subgroup.card_le_of_le hYQle)
      _ ≤ 8 * Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) := Nat.mul_le_mul_right _ hHatrel
  have h2Y : 2 * Nat.card ↥Y ≤ Nat.card ↥Q := by
    calc 2 * Nat.card ↥Y ≤ 2 * (8 * Nat.card ↥(Q ⊓ centralizer ({x} : Set G))) :=
          Nat.mul_le_mul_left 2 hYcard
      _ = Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) * 16 := by ring
      _ ≤ Nat.card ↥Q := hxbound
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hYpos : 0 < Nat.card ↥Y := Nat.card_pos
  omega

end CFSG.EvenSporadicStandard.ThStd
