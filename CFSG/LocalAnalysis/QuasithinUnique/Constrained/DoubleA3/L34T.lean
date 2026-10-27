module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Size

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section T

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))
include hD h27_1 hI hK hc

omit hD h27_1 hI hc in
theorem A3A3K.Ls_le_Ks : conjR L s ≤ conjR K s := by
  intro y hy
  rw [mem_conjR] at hy ⊢
  exact hK.L_le_K hy

theorem A3A3K.blockTC_eq_bot'
    : blockTC T S L = ⊥ := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨⟨-, hQ, -, -⟩, -⟩ := lemma2_4_27A3_part34 hD h27_1 hcs hK.a3 hK.conjJoin_ne
  have hTCR : blockTC T S L ≤ baum S := (le_sup_left.trans hQ.symm.le).trans hB.Q_le_R
  obtain ⟨e⟩ := hK.nonempty_psl27 hD h27_1 hI hc
  obtain ⟨ι, -⟩ := exists_conjR_equiv K s
  have hLle : L ≤ conjJoin S L := by rw [hK.join]; exact le_sup_left
  have hL₂le : conjR L s ≤ conjJoin S L := by rw [hK.join]; exact le_sup_right
  rw [eq_bot_iff]
  intro t ht
  have htR : t ∈ baum S := hTCR ht
  have htL : ∀ y ∈ conjJoin S L, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp ht.2 y hy).symm
  have htK : t ∈ normalizer (K : Set G) := hK.baum_le_normalizer_K hD h27_1 hI hc htR
  have htK' : t ∈ normalizer ((conjR K s : Subgroup G) : Set G) :=
    hK.baum_le_normalizer_Ks hD h27_1 hI hc htR
  obtain ⟨β, hβ⟩ := exists_conjAut htK
  have hβ1 := psl27_aut_eq_one e hK.isA4 hK.L_le_K β (fun l hl => by
    apply Subtype.ext
    rw [hβ]
    have := htL l (hLle hl)
    calc t⁻¹ * l * t = t⁻¹ * (l * t) := by group
      _ = t⁻¹ * (t * l) := by rw [this.symm]
      _ = l := by group)
  have htcK : ∀ y ∈ K, y * t = t * y := by
    intro y hy
    have h1 := congrArg Subtype.val (hβ1 ⟨y, hy⟩)
    rw [hβ] at h1
    have h2 : t⁻¹ * y * t = y := h1
    calc y * t = t * (t⁻¹ * y * t) := by group
      _ = t * y := by rw [h2]
  obtain ⟨β', hβ'⟩ := exists_conjAut htK'
  have e' : ↥(conjR K s) ≃* PSL(2, ZMod 7) := ι.symm.trans e
  have hβ1' := psl27_aut_eq_one e' hK.isA4s (hK.Ls_le_Ks) β' (fun l hl => by
    apply Subtype.ext
    rw [hβ']
    have := htL l (hL₂le hl)
    calc t⁻¹ * l * t = t⁻¹ * (l * t) := by group
      _ = t⁻¹ * (t * l) := by rw [this.symm]
      _ = l := by group)
  have htcK' : ∀ y ∈ conjR K s, y * t = t * y := by
    intro y hy
    have h1 := congrArg Subtype.val (hβ1' ⟨y, hy⟩)
    rw [hβ'] at h1
    have h2 : t⁻¹ * y * t = y := h1
    calc y * t = t * (t⁻¹ * y * t) := by group
      _ = t * y := by rw [h2]
  have htN : t ∈ Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) := by
    have hle : (K ⊔ conjR K s : Subgroup G) ≤ centralizerElem t :=
      sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (htcK y hy))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (htcK' y hy))
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hn)
  rw [hK.centralizer_sup_eq_bot hD h27_1 hI hc] at htN
  exact htN

theorem A3A3K.baum_le_sup
    : baum S ≤ K ⊔ conjR K s := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨⟨-, -, -, -⟩, hx⟩ := lemma2_4_27A3_part34 hD h27_1 hcs hK.a3 hK.conjJoin_ne
  have hbaum := (hx x hK.x_mem hK.x_not_mem).1
  have hU0 : blockU0 S L = blockU L ⊔ blockU2 L s := hK.toA3A3.blockU0_eq hB.hU0
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hU₂K' : blockU2 L s ≤ conjR K s := hK.isA4s.le.trans (hK.Ls_le_Ks)
  have hxN : x ∈ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G) :=
    hK.T_le_normalizer_sup hD h27_1 hI hc hK.x_mem
  have h1 : blockU0 S L ≤ K ⊔ conjR K s := by
    rw [hU0]
    exact sup_le (le_sup_of_le_left hUK) (le_sup_of_le_right hU₂K')
  rw [hbaum, hK.blockTC_eq_bot' hD h27_1 hI hc, bot_sup_eq]
  refine sup_le h1 ?_
  calc conjR (blockU0 S L) x ≤ conjR (K ⊔ conjR K s) x := Lin2.conjR_mono h1 x
    _ = K ⊔ conjR K s := mem_normalizer_iff_conjR_eq.mp hxN

theorem A3A3K.eq_of_mul_eq_mul
    {a a' b b' : G} (ha : a ∈ K) (ha' : a' ∈ K) (hb : b ∈ conjR K s)
    (hb' : b' ∈ conjR K s) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ K ⊓ conjR K s :=
    ⟨K.mul_mem (K.inv_mem ha') ha, by rw [h1]; exact (conjR K s).mul_mem hb' ((conjR K s).inv_mem hb)⟩
  rw [hK.inf_K_Ks hD h27_1 hI hc, Subgroup.mem_bot] at hmem
  have haa : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [hmem]; group
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact mul_left_cancel h

theorem A3A3K.T_inf_N_eq
    : T ⊓ (K ⊔ conjR K s) = (baum S ⊓ K) ⊔ (baum S ⊓ conjR K s) := by
  have hcs := hK.cs
  have hbT : baum S ≤ T := (inf_le_left : baum S ≤ S).trans hcs.le_T
  have hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ baum S ⊓ conjR K s, a * b = b * a := fun a ha b hb =>
    hK.comm_K_Ks hD h27_1 hI hc a ha.2 b hb.2
  have hN : baum S ⊓ K ≤ normalizer ((baum S ⊓ conjR K s : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute hcomm
  have hinf : (baum S ⊓ K) ⊓ (baum S ⊓ conjR K s) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ K ⊓ conjR K s := ⟨hy.1.2, hy.2.2⟩
    rwa [hK.inf_K_Ks hD h27_1 hI hc] at this
  have hcard := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, mul_one, hK.card_rK hD h27_1 hI hc, hK.card_rKs hD h27_1 hI hc] at hcard
  have hle : (baum S ⊓ K) ⊔ (baum S ⊓ conjR K s) ≤ T ⊓ (K ⊔ conjR K s) :=
    sup_le (le_inf (inf_le_left.trans hbT) (inf_le_right.trans le_sup_left))
      (le_inf (inf_le_left.trans hbT) (inf_le_right.trans le_sup_right))
  have hpow : IsPGroup 2 ↥(T ⊓ (K ⊔ conjR K s)) := hcs.setting.isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hpow.exists_card_eq
  have hdvd : Nat.card ↥(T ⊓ (K ⊔ conjR K s)) ∣ 64 * (21 * 21) := by
    have := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ (K ⊔ conjR K s) ≤ K ⊔ conjR K s)
    rw [hK.card_sup_K_Ks hD h27_1 hI hc] at this
    simpa using this
  rw [hn] at hdvd
  have h64 : 2 ^ n ∣ 64 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 (21 * 21)))
      hdvd
  have hn6 : n ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp
    (by simpa using h64 : 2 ^ n ∣ 2 ^ 6)
  have hle64 : Nat.card ↥(T ⊓ (K ⊔ conjR K s)) ≤ 64 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
      _ = 64 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem A3A3K.exists_sigma
    : ∃ σ ∈ S, σ * σ = 1 ∧ conjR K σ = conjR K s := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hss : s * s ∈ baum S := (s_mul_self_mem_baum hB hK.toA3A3).2
  have hbT : baum S ≤ T := (inf_le_left : baum S ≤ S).trans hcs.le_T
  have hsT : s ∈ T := hcs.le_T hK.s_mem
  have hssN : s * s ∈ T ⊓ (K ⊔ conjR K s) := ⟨hbT hss, hK.baum_le_sup hD h27_1 hI hc hss⟩
  rw [hK.T_inf_N_eq hD h27_1 hI hc] at hssN
  have hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ baum S ⊓ conjR K s, a * b = b * a := fun a ha b hb =>
    hK.comm_K_Ks hD h27_1 hI hc a ha.2 b hb.2
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm hssN
  have haK : a ∈ K := ha.2
  have hbK' : b ∈ conjR K s := hb.2
  have haR : a ∈ baum S := ha.1
  have hsK : ∀ y ∈ K, s * y * s⁻¹ ∈ conjR K s := by
    intro y hy
    rw [mem_conjR]
    have e : s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s * s)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hK.baum_le_normalizer_K hD h27_1 hI hc hss) y).mp hy
  have hsK' : ∀ y ∈ conjR K s, s * y * s⁻¹ ∈ K := fun y hy => mem_conjR.mp hy
  have hscomm : s * (s * s) * s⁻¹ = s * s := by group
  have hab' : a * b = b * a := hK.comm_K_Ks hD h27_1 hI hc a haK b hbK'
  have hprod : (s * b * s⁻¹) * (s * a * s⁻¹) = a * b := by
    have h1 : s * (a * b) * s⁻¹ = a * b := by
      rw [← hab]
      exact hscomm
    calc (s * b * s⁻¹) * (s * a * s⁻¹) = s * (b * a) * s⁻¹ := by group
      _ = s * (a * b) * s⁻¹ := by rw [hab']
      _ = a * b := h1
  have hdec := hK.eq_of_mul_eq_mul hD h27_1 hI hc (hsK' b hbK') haK (hsK a haK) hbK' hprod
  obtain ⟨hsb, hsa⟩ := hdec
  refine ⟨a⁻¹ * s, S.mul_mem (S.inv_mem ((inf_le_left : baum S ≤ S) haR)) hK.s_mem, ?_, ?_⟩
  · have e1 : s * a⁻¹ * s⁻¹ = b⁻¹ := by
      have : s * a * s⁻¹ = b := hsa
      calc s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        _ = b⁻¹ := by rw [this]
    calc a⁻¹ * s * (a⁻¹ * s) = a⁻¹ * (s * a⁻¹ * s⁻¹) * (s * s) := by group
      _ = a⁻¹ * b⁻¹ * (a * b) := by rw [e1, hab]
      _ = 1 := by
        calc a⁻¹ * b⁻¹ * (a * b) = a⁻¹ * b⁻¹ * (b * a) := by rw [hab']
          _ = 1 := by group
  · rw [← conjR_conjR_eq]
    have : conjR K a⁻¹ = K :=
      mem_normalizer_iff_conjR_eq.mp (Subgroup.le_normalizer (K.inv_mem haK))
    rw [this]

end T

end CFSG.QuasithinUnique.DoubleA3
