module

import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Aux

private theorem le_normalizer_of_forall_mem {B Y : Subgroup G}
    (h : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) : B ≤ Subgroup.normalizer (Y : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h b hb y hy, fun hy => ?_⟩
  have := h b⁻¹ (B.inv_mem hb) _ hy
  simpa [mul_assoc] using this

private theorem conj_mem_centModSubgroup {p : ℕ} {J : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) (hc : c ∈ centModSubgroup p J) :
    g * c * g⁻¹ ∈ centModSubgroup p J := by
  obtain ⟨hcN, hcJ⟩ := hc
  refine ⟨?_, fun l hl => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcN) (Subgroup.inv_mem _ hg)
  · have hl' : g⁻¹ * l * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) l).1 hl
      simpa using this
    have h1 := hcJ _ hl'
    have h2 : g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ ∈ GLAPPrimeCoreOf p J :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p J hg) _).1 h1
    have h3 : ⁅l, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]; exact h2

private theorem normalizer_le_normalizer_centModSubgroup (p : ℕ) (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (centModSubgroup p J : Set G) :=
  le_normalizer_of_forall_mem fun _ hb _ hc => conj_mem_centModSubgroup hb hc

private theorem glaPPrimeCoreOf_le_centModSubgroup (p : ℕ) (J : Subgroup G) :
    GLAPPrimeCoreOf p J ≤ centModSubgroup p J := by
  intro o ho
  have hoJ : o ∈ J := Subgroup.map_subtype_le _ ho
  refine ⟨Subgroup.le_normalizer hoJ, fun l hl => ?_⟩
  have h1 : l * o * l⁻¹ ∈ GLAPPrimeCoreOf p J :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p J hl) o).1 ho
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)

private theorem exists_centMod_mul_of_inducesInnerMod {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) (h : InducesInnerMod p J g) :
    ∃ c ∈ centModSubgroup p J, ∃ l ∈ J, g = c * l := by
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨g * l⁻¹, ⟨?_, fun x hx => ?_⟩, l, hl, by group⟩
  · exact Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (Subgroup.le_normalizer hl))
  · have h1 := hy x⁻¹ (J.inv_mem hx)
    have h2 : g * ((l⁻¹ * x⁻¹ * l)⁻¹ * (g⁻¹ * x⁻¹ * g)) * g⁻¹ ∈ GLAPPrimeCoreOf p J :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p J hg) _).1 h1
    have h3 : ⁅x, g * l⁻¹⁆ = (g * ((l⁻¹ * x⁻¹ * l)⁻¹ * (g⁻¹ * x⁻¹ * g)) * g⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]; exact Subgroup.inv_mem _ h2

private theorem exists_pow_mul_eq {C : Subgroup G} {s c : G}
    (hs : s ∈ Subgroup.normalizer (C : Set G)) (hc : c ∈ C) (n : ℕ) :
    ∃ c' ∈ C, (s * c) ^ n = s ^ n * c' := by
  induction n with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', h⟩ := ih
    have h1 : s⁻¹ * c' * s ∈ C := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hs) c').1 hc'
      simpa using this
    refine ⟨(s⁻¹ * c' * s) * c, C.mul_mem h1 hc, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

private theorem exists_relIndex_eq_two_pow {J S C : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hJC : J ≤ Subgroup.normalizer (C : Set G)) :
    ∃ k : ℕ, (J ⊓ C).relIndex (J ⊓ (S ⊔ C)) = 2 ^ k := by
  classical
  set Y := J ⊓ (S ⊔ C) with hY
  set Z := J ⊓ C with hZ
  have hZY : Z ≤ Y := inf_le_inf_left J le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (Z : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy.1, hJC hy.1⟩
  haveI : (Z.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZY).2 hYN
  have hP : IsPGroup 2 (↥Y ⧸ Z.subgroupOf Y) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hyS : (y : G) ∈ (S : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right S C hSC]; exact y.2.2
      obtain ⟨s, hs, c, hc, hsc⟩ := hyS
      obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
      have hsk : s ^ (2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      obtain ⟨c', hc', hpow⟩ := exists_pow_mul_eq (hSC hs) hc (2 ^ k)
      have hyk : (y : G) ^ (2 ^ k) = c' := by rw [← hsc, hpow, hsk, one_mul]
      have hyJ : (y : G) ^ (2 ^ k) ∈ J := J.pow_mem y.2.1 (2 ^ k)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact ⟨hyJ, hyk ▸ hc'⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  refine ⟨k, ?_⟩
  show (Z.subgroupOf Y).index = 2 ^ k
  rw [Subgroup.index_eq_card]
  exact hk

private theorem le_sup_of_odd_relIndex_of_two_pow {A B Y : Subgroup G}
    (hA : ¬ 2 ∣ A.relIndex Y) {k : ℕ} (hB : B.relIndex Y = 2 ^ k) : Y ≤ A ⊔ B := by
  have h1 : (A ⊔ B).relIndex Y ∣ A.relIndex Y := Subgroup.relIndex_dvd_of_le_left Y le_sup_left
  have h2 : (A ⊔ B).relIndex Y ∣ 2 ^ k := hB ▸ Subgroup.relIndex_dvd_of_le_left Y le_sup_right
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hi0 : i = 0 := by
    by_contra hne
    exact hA ((dvd_pow_self 2 hne).trans (hi ▸ h1))
  rw [hi0, pow_zero] at hi
  exact Subgroup.relIndex_eq_one.1 hi

private theorem le_normalizer_sup_of_le_sup {O Z R Y : Subgroup G} (hRY : R ≤ Y) (hZY : Z ≤ Y)
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hcomm : ∀ z ∈ Z, ∀ r ∈ R, ⁅z, r⁆ ∈ O)
    (hY : Y ≤ R ⊔ Z) : Y ≤ Subgroup.normalizer ((O ⊔ R : Subgroup G) : Set G) := by
  refine hY.trans (sup_le (le_sup_right.trans Subgroup.le_normalizer) ?_)
  refine le_normalizer_of_forall_mem fun z hz x hx => ?_
  have hRO : R ≤ Subgroup.normalizer (O : Set G) := hRY.trans hYO
  have hx' : x ∈ (O : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O R hRO]; exact hx
  obtain ⟨o, ho, r, hr, rfl⟩ := hx'
  have h1 : z * o * z⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hYO (hZY hz)) o).1 ho
  have h2 : z * (o * r) * z⁻¹ = (z * o * z⁻¹) * (⁅z, r⁆ * r) := by
    simp only [commutatorElement_def]; group
  rw [h2]
  exact (O ⊔ R).mul_mem (Subgroup.mem_sup_left h1)
    ((O ⊔ R).mul_mem (Subgroup.mem_sup_left (hcomm z hz r hr)) (Subgroup.mem_sup_right hr))

private theorem le_glaPPrimeCoreOf_of_normalized {p : ℕ} {A N : Subgroup G} (hNA : N ≤ A)
    (hn : A ≤ Subgroup.normalizer (N : Set G)) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p A := by
  have hnorm : (N.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 hn
  have hcard : Nat.card (N.subgroupOf A) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
  have h1 : N.subgroupOf A ≤ GLAPPrimeCore p ↥A := le_sSup ⟨hnorm, hcard ▸ hc⟩
  have h2 := Subgroup.map_mono (f := A.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hNA] at h2

private theorem exists_sylow_two_relIndex (Y : Subgroup G) :
    ∃ R : Subgroup G, R ≤ Y ∧ IsPGroup 2 R ∧ ¬ 2 ∣ R.relIndex Y := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  refine ⟨(P : Subgroup ↥Y).map Y.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  have : ((P : Subgroup ↥Y).map Y.subtype).relIndex Y = (P : Subgroup ↥Y).index := by
    unfold Subgroup.relIndex Subgroup.subgroupOf
    rw [Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  rw [this]
  exact P.not_dvd_index

open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710 in
private theorem exists_invariant_twoSubgroup_sup_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B Y Z O : Subgroup G} (hB : IsPGroup p B) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hOZ : O ≤ Z) (hZY : Z ≤ Y) (hYO : Y ≤ Subgroup.normalizer (O : Set G))
    (hOp : ¬ p ∣ Nat.card O) (hcomm : ∀ z ∈ Z, ∀ y ∈ Y, ⁅z, y⁆ ∈ O) {k : ℕ}
    (hk : Z.relIndex Y = 2 ^ k) :
    ∃ Q : Subgroup G, Q ≤ Y ∧ IsPGroup 2 Q ∧ B ≤ Subgroup.normalizer (Q : Set G) ∧
      Y ≤ Q ⊔ Z := by
  classical
  obtain ⟨R, hRY, hR2, hRodd⟩ := exists_sylow_two_relIndex Y
  have hYRZ : Y ≤ R ⊔ Z := le_sup_of_odd_relIndex_of_two_pow hRodd hk
  have hYN : Y ≤ Subgroup.normalizer ((O ⊔ R : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_sup hRY hZY hYO (fun z hz r hr => hcomm z hz r (hRY hr)) hYRZ
  have hRp : ¬ p ∣ Nat.card R := by
    obtain ⟨a, ha⟩ := hR2.exists_card_eq
    rw [ha]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hORcop : Nat.Coprime p (Nat.card (O ⊔ R : Subgroup G)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_sup_of_le_normalizer hp (hRY.trans hYO) hOp hRp)
  have hW : O ⊔ R ≤ GLAPPrimeCoreOf p Y :=
    le_glaPPrimeCoreOf_of_normalized (sup_le (hOZ.trans hZY) hRY) hYN hORcop
  have hWY : GLAPPrimeCoreOf p Y ≤ Y := Subgroup.map_subtype_le _
  have hBW : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set G) := by
    intro b hb
    have hb' := mem_normalizer_iff_gLBConj_eq.1 (hBY hb)
    exact mem_normalizer_iff_gLBConj_eq.2 (by rw [← glaPPrimeCoreOf_gLBConj, hb'])
  obtain ⟨Q, -, hQW, hQ2, hQodd, hBQ⟩ :=
    exists_invariant_sylow_containing_of_pGroup hp Nat.prime_two hB hBW
      (not_dvd_card_glaPPrimeCoreOf hp Y) bot_le IsPGroup.of_bot Subgroup.le_normalizer_of_normal
  have hRW : R ≤ GLAPPrimeCoreOf p Y := le_sup_right.trans hW
  have hWodd : ¬ 2 ∣ (GLAPPrimeCoreOf p Y).relIndex Y :=
    fun h => hRodd (h.trans (Subgroup.relIndex_dvd_of_le_left _ hRW))
  have hQodd' : ¬ 2 ∣ Q.relIndex Y := by
    rw [← Subgroup.relIndex_mul_relIndex Q _ _ hQW hWY]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact hQodd h
    · exact hWodd h
  exact ⟨Q, hQW.trans hWY, hQ2, hBQ, le_sup_of_odd_relIndex_of_two_pow hQodd' hk⟩

private theorem commutator_le_of_centralizes {J S B C Q : Subgroup G}
    (hBC : B ≤ Subgroup.normalizer (C : Set G)) (hJC : J ≤ Subgroup.normalizer (C : Set G))
    (hQJ : Q ≤ J) (hdec : ∀ s ∈ S, ∃ c ∈ C, ∃ l ∈ J, s = c * l)
    (hYQZ : J ⊓ (S ⊔ C) ≤ Q ⊔ (J ⊓ C)) (hcen : ∀ q ∈ Q, ∀ b ∈ B, b * q = q * b) :
    (⁅S, B⁆ : Subgroup G) ≤ C := by
  rw [Subgroup.commutator_le]
  intro s hs b hb
  obtain ⟨c, hc, l, hl, hsl⟩ := hdec s hs
  have hlY : l ∈ J ⊓ (S ⊔ C) := by
    refine ⟨hl, ?_⟩
    have : l = c⁻¹ * s := by rw [hsl]; group
    rw [this]
    exact (S ⊔ C).mul_mem (Subgroup.mem_sup_right (C.inv_mem hc)) (Subgroup.mem_sup_left hs)
  have hQZ : Q ≤ Subgroup.normalizer ((J ⊓ C : Subgroup G) : Set G) := fun q hq =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hQJ hq), hJC (hQJ hq)⟩
  have hlQZ : l ∈ (Q : Set G) * ((J ⊓ C : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q _ hQZ]
    exact hYQZ hlY
  obtain ⟨q, hq, z, hz, hqz⟩ := hlQZ
  have hbq : Commute b q := hcen q hq b hb
  have h4 : b⁻¹ * q⁻¹ * b = q⁻¹ := by rw [hbq.inv_inv.eq, inv_mul_cancel_right]
  have key : ⁅s, b⁆ = c * (q * (z * (b * z⁻¹ * b⁻¹)) * q⁻¹) * (b * c⁻¹ * b⁻¹) := by
    rw [hsl, ← hqz]
    calc ⁅c * (q * z), b⁆ = c * q * z * b * z⁻¹ * q⁻¹ * c⁻¹ * b⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = c * q * z * b * z⁻¹ * (b⁻¹ * q⁻¹ * b) * c⁻¹ * b⁻¹ := by rw [h4]
      _ = c * (q * (z * (b * z⁻¹ * b⁻¹)) * q⁻¹) * (b * c⁻¹ * b⁻¹) := by group
  rw [key]
  have hzC : z ∈ C := hz.2
  have h5 : b * z⁻¹ * b⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hBC hb) _).1 (C.inv_mem hzC)
  have h6 : q * (z * (b * z⁻¹ * b⁻¹)) * q⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.1 (hJC (hQJ hq)) _).1 (C.mul_mem hzC h5)
  have h7 : b * c⁻¹ * b⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hBC hb) _).1 (C.inv_mem hc)
  exact C.mul_mem (C.mul_mem hc h6) h7

end Aux

theorem exists_twoSubgroup_of_inducesInnerMod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X J B S : Subgroup G} (hJ : GLAPComponent p X J)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p J))) (hB : IsPGroup p B)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hS2 : IsPGroup 2 S) (hSJ : S ≤ Subgroup.normalizer (J : Set G))
    (hSB : (⁅S, B⁆ : Subgroup G) = S) (hinner : ∀ s ∈ S, InducesInnerMod p J s)
    (hnc : ¬ S ≤ centModSubgroup p J) :
    ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  classical
  have hNC := normalizer_le_normalizer_centModSubgroup p J
  have hSC : S ≤ Subgroup.normalizer (centModSubgroup p J : Set G) := hSJ.trans hNC
  have hJC : J ≤ Subgroup.normalizer (centModSubgroup p J : Set G) :=
    Subgroup.le_normalizer.trans hNC
  have hBC : B ≤ Subgroup.normalizer (centModSubgroup p J : Set G) := hBJ.trans hNC
  have hOJ : GLAPPrimeCoreOf p J ≤ J := Subgroup.map_subtype_le _
  have hZY : J ⊓ centModSubgroup p J ≤ J ⊓ (S ⊔ centModSubgroup p J) :=
    inf_le_inf_left J le_sup_right
  have hYJ : J ⊓ (S ⊔ centModSubgroup p J) ≤ J := inf_le_left
  have hBY : B ≤ Subgroup.normalizer ((J ⊓ (S ⊔ centModSubgroup p J) : Subgroup G) : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBJ hb,
      Subgroup.inf_normalizer_le_normalizer_sup S _ ⟨hBS hb, hBC hb⟩⟩
  obtain ⟨k, hk⟩ := exists_relIndex_eq_two_pow hS2 hSC hJC
  obtain ⟨Q, hQY, hQ2, hBQ, hYQZ⟩ := exists_invariant_twoSubgroup_sup_eq hp hp2 hB hBY
    (le_inf hOJ (glaPPrimeCoreOf_le_centModSubgroup p J)) hZY
    (hYJ.trans (le_normalizer_glaPPrimeCoreOf p J)) (not_dvd_card_glaPPrimeCoreOf hp J)
    (fun z hz y hy => by
      rw [← commutatorElement_inv]
      exact (GLAPPrimeCoreOf p J).inv_mem (hz.2.2 y (hYJ hy))) hk
  refine ⟨Q, hQY.trans hYJ, hQ2, hBQ, fun hQB => hnc ?_⟩
  have hcen : ∀ q ∈ Q, ∀ b ∈ B, b * q = q * b := fun q hq b hb =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hQB hq) b hb
  calc S = ⁅S, B⁆ := hSB.symm
    _ ≤ centModSubgroup p J := commutator_le_of_centralizes hBC hJC (hQY.trans hYJ)
        (fun s hs => exists_centMod_mul_of_inducesInnerMod (hSJ hs) (hinner s hs)) hYQZ hcen

end CFSG.LocalAnalysis.GLTheoremA.P55
