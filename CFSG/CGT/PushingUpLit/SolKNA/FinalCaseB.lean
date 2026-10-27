module

public import CFSG.CGT.PushingUpLit.SolKNA.FinalCaseA
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate mem_rightConjugate_iff
  rightConjugate_card rightConjugate_eq_self_iff)
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting (rightConjugate_mono)
open CFSG.ComponentClassification.AS76b (gammaOneOn)

variable {G : Type} [Group G]

theorem frattini_ne_bot_of_sq [Finite G] {D : Subgroup G} (hD : IsPGroup 2 D) {y : G} (hy : y ∈ D)
    (hy2 : y * y ≠ 1) : frattini D ≠ ⊥ := by
  intro hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 D) := ⟨hD⟩
  have hel : IsElementaryAbelian 2 D := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hbot
  exact hy2 (by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := D) y hy)

theorem exists_fourGroup_of_card [Finite G] {E : Subgroup G} (hE2 : IsPGroup 2 E)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (h4 : 4 ≤ Nat.card E) :
    ∃ V : Subgroup G, V ≤ E ∧ CFSG.Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hE2
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card ↥E := hn ▸ pow_dvd_pow 2 hn2
  obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 hdvd
  refine ⟨V'.map E.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · exact Subtype.ext (hcomm _ (Subgroup.map_subtype_le V' a.2) _
      (Subgroup.map_subtype_le V' b.2))
  · rw [sq]
    exact hsq x (Subgroup.map_subtype_le V' hx)
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hV']
    norm_num

theorem rightConjugate_conj_inf {R : Subgroup G} {x s : G}
    (hs : s ∈ Subgroup.normalizer (R : Set G)) :
    rightConjugate (conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G)) s =
      conjSubgroup (s⁻¹ * x) R ⊓ Subgroup.normalizer (R : Set G) := by
  have h1 : rightConjugate (conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G)) s =
      conjSubgroup s⁻¹ (conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G)) := rfl
  rw [h1, conjSubgroup_inf, ← conjSubgroup_mul,
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (Subgroup.inv_mem _ hs))]

namespace FinalCase

variable [Finite G] {R : Subgroup G} {z : G} (F : FinalCase G R z)
include F

theorem conj_eq_of_inf_ne_bot {a b : G} (h : conjSubgroup a R ⊓ conjSubgroup b R ≠ ⊥) :
    conjSubgroup a R = conjSubgroup b R := by
  have h1 : R ⊓ conjSubgroup (a⁻¹ * b) R ≠ ⊥ := by
    intro hbot
    apply h
    have : conjSubgroup a (R ⊓ conjSubgroup (a⁻¹ * b) R) =
        conjSubgroup a R ⊓ conjSubgroup b R := by
      rw [conjSubgroup_inf, ← conjSubgroup_mul, mul_inv_cancel_left]
    rw [← this, hbot]
    exact Subgroup.map_bot _
  have h2 := conjSubgroup_eq_of_isTI F.ti h1
  calc conjSubgroup a R = conjSubgroup a (conjSubgroup (a⁻¹ * b) R) := by rw [h2]
    _ = conjSubgroup b R := by rw [← conjSubgroup_mul, mul_inv_cancel_left]


theorem conj_z_ne_one (x : G) : x * z * x⁻¹ ≠ 1 := fun e => F.z_ne (by
  calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
    _ = 1 := by rw [e]; group)

theorem frattini_ne_bot_conj {x : G}
    (hne : conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥) :
    frattini ↥(conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G)) ≠ ⊥ := by
  obtain ⟨y, hyD, hyy⟩ := F.sq_mem x hne
  have hD2 : IsPGroup 2 ↥(conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G)) :=
    (F.two.map (MulAut.conj x).toMonoidHom).to_le inf_le_left
  exact frattini_ne_bot_of_sq hD2 hyD (by rw [hyy]; exact F.conj_z_ne_one x)

theorem commutable_family {A : Subgroup G} (hA2 : IsPGroup 2 A)
    (hAM : A ≤ Subgroup.normalizer (R : Set G)) {c : ℕ} (hc : c ≠ 1)
    {x₁ x₂ : G} (h1A : conjSubgroup x₁ R ⊓ Subgroup.normalizer (R : Set G) ≤ A)
    (h2A : conjSubgroup x₂ R ⊓ Subgroup.normalizer (R : Set G) ≤ A)
    (h1c : Nat.card ↥(conjSubgroup x₁ R ⊓ Subgroup.normalizer (R : Set G)) = c)
    (h2c : Nat.card ↥(conjSubgroup x₂ R ⊓ Subgroup.normalizer (R : Set G)) = c)
    (hne : conjSubgroup x₁ R ⊓ Subgroup.normalizer (R : Set G) ≠
      conjSubgroup x₂ R ⊓ Subgroup.normalizer (R : Set G)) :
    ⁅conjSubgroup x₁ R ⊓ Subgroup.normalizer (R : Set G),
      conjSubgroup x₂ R ⊓ Subgroup.normalizer (R : Set G)⁆ = ⊥ := by
  classical
  let Δ : Set (Subgroup G) :=
    {D | (∃ x : G, D = conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G)) ∧ D ≤ A ∧
      Nat.card D = c}
  have hinv : ∀ D ∈ Δ, ∀ s ∈ A, rightConjugate D s ∈ Δ := by
    rintro D ⟨⟨x, rfl⟩, hDA, hDc⟩ s hs
    have hsM : s ∈ Subgroup.normalizer (R : Set G) := hAM hs
    refine ⟨⟨s⁻¹ * x, rightConjugate_conj_inf hsM⟩, ?_, ?_⟩
    · calc rightConjugate _ s ≤ rightConjugate A s := rightConjugate_mono s hDA
        _ = A := (rightConjugate_eq_self_iff A s).mpr (Subgroup.le_normalizer hs)
    · rw [rightConjugate_card]
      exact hDc
  have hΦ : ∀ D ∈ Δ, frattini D ≠ ⊥ := by
    rintro D ⟨⟨x, rfl⟩, hDA, hDc⟩
    refine F.frattini_ne_bot_conj fun hb => hc ?_
    rw [hb, Subgroup.card_bot] at hDc
    exact hDc.symm
  have hTI : ∀ D ∈ Δ, ∀ D' ∈ Δ, D ≠ D' → D ⊓ D' = ⊥ := by
    rintro D ⟨⟨x, rfl⟩, -, -⟩ D' ⟨⟨x', rfl⟩, -, -⟩ hne'
    by_contra hbot
    apply hne'
    have : conjSubgroup x R = conjSubgroup x' R := F.conj_eq_of_inf_ne_bot fun hb => hbot (by
      rw [eq_bot_iff, ← hb]
      exact inf_le_inf inf_le_left inf_le_left)
    rw [this]
  exact CFSG.ComponentClassification.Asc76X.lemma25 (S := A) (Δ := Δ) hA2 (fun D hD => hD.2.1)
    hinv (fun D hD D' hD' => hD.2.2.trans hD'.2.2.symm) hΦ hTI _ ⟨⟨x₁, rfl⟩, h1A, h1c⟩ _
    ⟨⟨x₂, rfl⟩, h2A, h2c⟩ hne

theorem Z_comm_of_le {h k : G}
    (hh : conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G))
    (hk : conjSubgroup k (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    ∀ x ∈ conjSubgroup h (zCenter R), ∀ y ∈ conjSubgroup k (zCenter R), x * y = y * x := by
  classical
  by_cases hRR : conjSubgroup h R = conjSubgroup k R
  · have hZ : conjSubgroup h (zCenter R) = conjSubgroup k (zCenter R) := by
      rw [conjSubgroup_zCenter, conjSubgroup_zCenter, hRR]
    intro x hx y hy
    rw [hZ] at hx
    exact comm_conj_zCenter R k x hx y hy
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two (Subgroup.normalizer (R : Set G))
  have hZkQ := F.conj_Z_le_Q hk
  have hR2h : IsPGroup 2 (conjSubgroup h R) := F.two.map (MulAut.conj h).toMonoidHom
  have hT2 : IsPGroup 2 ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) :=
    hR2h.to_le inf_le_left
  have hzh : h * z * h⁻¹ ∈ conjSubgroup h (zCenter R) := by
    rw [mem_conjSubgroup, show h⁻¹ * (h * z * h⁻¹) * h = z by group]
    exact F.z_mem
  have hTne : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ := fun hb =>
    F.conj_z_ne_one h (by
      have hzhT : h * z * h⁻¹ ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.map_mono inf_le_left hzh, hh hzh⟩
      rw [hb, Subgroup.mem_bot] at hzhT
      exact hzhT)
  have hTcard : Nat.card ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) ≠ 1 := fun h1 =>
    hTne (Subgroup.card_eq_one.mp h1)
  have hTQ : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((qGroup R : Subgroup G) : Set G) := inf_le_right.trans hMQ
  have hA2 : IsPGroup 2 ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ⊔ qGroup R) :=
    IsPGroup.to_sup_of_normal_right' hT2 hQ2 hTQ
  have hAM : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ⊔ qGroup R ≤
      Subgroup.normalizer (R : Set G) := sup_le inf_le_right hQM
  obtain ⟨U, hUZ, hUel, hU4⟩ := exists_fourGroup_of_card
    (F.isPGroup_Z.map (MulAut.conj k).toMonoidHom) (comm_conj_zCenter R k) (F.sq_conj_Z k)
    (by
      show 4 ≤ Nat.card ↥(conjSubgroup k (zCenter R))
      rw [CFSG.RankThree.GF2n.card_conjSubgroup]
      exact F.Z_card)
  have hUA : U ≤ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ⊔ qGroup R :=
    hUZ.trans (hZkQ.trans le_sup_right)
  have hcomm : ∀ g ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ⊔ qGroup R,
      rightConjugate (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) g ≠
        conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) →
      ⁅conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G),
        rightConjugate (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) g⁆ = ⊥ := by
    intro g hg hne
    have hgM : g ∈ Subgroup.normalizer (R : Set G) := hAM hg
    rw [rightConjugate_conj_inf hgM] at hne ⊢
    refine F.commutable_family hA2 hAM hTcard le_sup_left ?_ rfl ?_ (Ne.symm hne)
    · rw [← rightConjugate_conj_inf hgM]
      calc _ ≤ rightConjugate _ g := rightConjugate_mono g le_sup_left
        _ = _ := (rightConjugate_eq_self_iff _ g).mpr (Subgroup.le_normalizer hg)
    · rw [← rightConjugate_conj_inf hgM, rightConjugate_card]
  have h24 := CFSG.ComponentClassification.Asc76X.lemma24In
    (A := conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ⊔ qGroup R)
    (R := conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) (U := U) le_sup_left hUA hT2
    hUel hU4 hcomm (F.frattini_ne_bot_conj hTne)
  have hΓ : gammaOneOn U (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ⊔ qGroup R) ≤
      Subgroup.normalizer (conjSubgroup k (zCenter R) : Set G) := by
    unfold gammaOneOn
    refine iSup_le fun U₀ => iSup_le fun hU₀ => iSup_le fun hU₀ne x hx => ?_
    have hxN := (Subgroup.mem_inf.mp hx).2
    rw [← conjSubgroup_eq_self_iff]
    refine conjSubgroup_eq_of_isTI (isTI_conjSubgroup F.isTI_Z k) fun hbot => hU₀ne ?_
    rw [eq_bot_iff]
    intro w hw
    have h1 : w ∈ conjSubgroup k (zCenter R) := hUZ (hU₀ hw)
    have h2 : w ∈ conjSubgroup x (conjSubgroup k (zCenter R)) := by
      rw [← conjSubgroup_eq_self_iff.mpr hxN] at hw
      exact Subgroup.map_mono (hU₀.trans hUZ) hw
    have : w ∈ conjSubgroup k (zCenter R) ⊓ conjSubgroup x (conjSubgroup k (zCenter R)) :=
      Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hbot] at this
    exact this
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h24.2
  have htΓ := hΓ (Subgroup.mem_inf.mp ht).1
  have htT : t ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).2).1
  rw [F.normalizer_conj_Z k] at htΓ
  have hT' : conjSubgroup h R ⊓ Subgroup.normalizer (conjSubgroup k R : Set G) ≠ ⊥ := fun hb => by
    have : t ∈ conjSubgroup h R ⊓ Subgroup.normalizer (conjSubgroup k R : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp htT).1, htΓ⟩
    rw [hb, Subgroup.mem_bot] at this
    exact ht1 (Subtype.ext this)
  obtain ⟨-, hcomm'⟩ := F.P_pair (a := k) (b := h) hRR hT'
  intro x hx y hy
  exact (hcomm' y hy x hx).symm

end FinalCase

end CFSG.CGT.PushingUpLit.SolKNA
