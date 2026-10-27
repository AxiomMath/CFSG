module

import CFSG.GH74.GLS.C3.Layer1.Thm1P310Two
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_of_relIndex_le_two {T H : Subgroup G} (hidx : H.relIndex T ≤ 2)
    {s : G} (hs : s ∈ T) : s * s ∈ H := by
  have hpos : 0 < H.relIndex T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h12 : H.relIndex T = 1 ∨ H.relIndex T = 2 := by omega
  rcases h12 with h | h
  · exact (Subgroup.relIndex_eq_one.1 h) (T.mul_mem hs hs)
  · exact IVK.Proofs2.mul_self_mem_of_index_two h hs

theorem relIndex_centralizer_le_two {T : Subgroup G} {a a' : G}
    (h : ∀ s ∈ T, s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a') :
    (T ⊓ centralizer ({a} : Set G)).relIndex T ≤ 2 := by
  classical
  unfold Subgroup.relIndex
  set H' : Subgroup ↥T := (T ⊓ centralizer ({a} : Set G)).subgroupOf T with hH'
  have hmem : ∀ s : ↥T, s ∈ H' ↔ (s : G) * a = a * (s : G) := by
    intro s
    rw [hH', Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun hs => hs.2, fun hs => ⟨s.2, hs⟩⟩
  let f : (↥T ⧸ H') → ({a, a'} : Set G) :=
    Quotient.lift (fun s : ↥T => (⟨(s : G) * a * (s : G)⁻¹, by
      rcases h s s.2 with h1 | h1
      · left; exact h1
      · right; exact h1⟩ : ({a, a'} : Set G))) (by
      intro s s' hss'
      have hr : s⁻¹ * s' ∈ H' := QuotientGroup.leftRel_apply.1 hss'
      have hc : (s⁻¹ * s' : ↥T).1 * a = a * (s⁻¹ * s' : ↥T).1 := (hmem _).1 hr
      apply Subtype.ext
      show (s : G) * a * (s : G)⁻¹ = (s' : G) * a * (s' : G)⁻¹
      have h2 : (s : G)⁻¹ * (s' : G) * a = a * ((s : G)⁻¹ * (s' : G)) := hc
      calc (s : G) * a * (s : G)⁻¹ = (s : G) * (a * ((s : G)⁻¹ * (s' : G))) * (s' : G)⁻¹ := by group
        _ = (s : G) * ((s : G)⁻¹ * (s' : G) * a) * (s' : G)⁻¹ := by rw [h2]
        _ = (s' : G) * a * (s' : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro q q' hqq'
    induction q using Quotient.inductionOn with | _ s => ?_
    induction q' using Quotient.inductionOn with | _ s' => ?_
    have h1 : (s : G) * a * (s : G)⁻¹ = (s' : G) * a * (s' : G)⁻¹ :=
      congrArg Subtype.val hqq'
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    rw [hmem]
    show (s : G)⁻¹ * (s' : G) * a = a * ((s : G)⁻¹ * (s' : G))
    calc (s : G)⁻¹ * (s' : G) * a = (s : G)⁻¹ * ((s' : G) * a * (s' : G)⁻¹) * (s' : G) := by group
      _ = (s : G)⁻¹ * ((s : G) * a * (s : G)⁻¹) * (s' : G) := by rw [h1]
      _ = a * ((s : G)⁻¹ * (s' : G)) := by group
  have h2 : Nat.card (↥T ⧸ H') ≤ Nat.card ({a, a'} : Set G) := Nat.card_le_card_of_injective f hf
  have h3 : Nat.card ({a, a'} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc ({a, a'} : Set G).ncard ≤ ({a'} : Set G).ncard + 1 := Set.ncard_insert_le a {a'}
      _ = 2 := by rw [Set.ncard_singleton]
  exact h2.trans h3

theorem transfer_finish (hIG : Stage1.Thm3.Sec5.IG_15_16_ext) (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    {T T₀ : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hT₀ : T₀ ≤ T) (hidx : T₀.relIndex T ≤ 2) {t : G}
    (htT : t ∈ T) (ht2 : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ T₀ ∧ ∀ c ∈ T ⊓ centralizer ({t} : Set G), g⁻¹ * c * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, -, hxT₀, hxS⟩ := hIG G ⊤ T T₀ ⊥ t hT hT₀ hidx bot_le
    (fun x _ n hn => by
      rw [Subgroup.mem_bot] at hn ⊢
      rw [hn]; group) (by simp) htT ht2 (by rw [hperf]; exact Subgroup.mem_sup_left (Subgroup.mem_top t))
  set t' : G := x⁻¹ * t * x with ht'
  set W : Subgroup G := (T ⊓ centralizer ({t} : Set G)).map (MulAut.conj x⁻¹).toMonoidHom with hW
  have hWc : W ≤ ⊤ ⊓ centralizer ({t'} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨mem_top _, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_centralizer_singleton_iff.1 hc.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ht']
    calc x⁻¹ * c * x * (x⁻¹ * t * x) = x⁻¹ * (c * t) * x := by group
      _ = x⁻¹ * (t * c) * x := by rw [this]
      _ = x⁻¹ * t * x * (x⁻¹ * c * x) := by group
  have hW2 : IsPGroup 2 ↥W := (hT.isPGroup.to_le inf_le_left).map (MulAut.conj x⁻¹).toMonoidHom
  obtain ⟨h, hh, hhW⟩ := Th2.exists_cj_le_of_isSylowOf hxS hWc hW2
  refine ⟨x * h⁻¹, ?_, ?_⟩
  · have hhc : h * t' = t' * h := by
      have := mem_centralizer_singleton_iff.1 hh.2
      exact this
    have : (x * h⁻¹)⁻¹ * t * (x * h⁻¹) = h * t' * h⁻¹ := by
      simp only [ht']; group
    rw [this, hhc]
    simpa using hxT₀
  · intro c hc
    have hcW : x⁻¹ * c * x ∈ W := ⟨c, hc, by simp⟩
    have hmem : h * (x⁻¹ * c * x) * h⁻¹ ∈ cj h W := by
      refine (mem_cj_iff h W _).2 ?_
      have e : h⁻¹ * (h * (x⁻¹ * c * x) * h⁻¹) * h = x⁻¹ * c * x := by group
      rw [e]; exact hcW
    have h1 := (hhW hmem).1
    have : (x * h⁻¹)⁻¹ * c * (x * h⁻¹) = h * (x⁻¹ * c * x) * h⁻¹ := by group
    rw [this]
    exact h1

theorem mem_of_centralizes_of_card_eight {H : Type} [Group H] [Finite H] (hcard : Nat.card H = 8)
    (hna : ∃ a b : H, a * b ≠ b * a) {V : Subgroup H} (hV4 : 4 ≤ Nat.card V)
    (hVc : ∀ e ∈ V, ∀ e' ∈ V, e * e' = e' * e) {w : H} (hw : ∀ e ∈ V, w * e = e * w) :
    w ∈ V := by
  set A : Subgroup H := V ⊔ zpowers w with hA
  have hcomm : ∀ u ∈ V, ∀ d ∈ zpowers w, u * d = d * u := by
    intro u hu d hd
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
    exact (Commute.zpow_right (show Commute u w from (hw u hu).symm) k).eq
  have hAtop : A ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have ha : a ∈ A := htop ▸ Subgroup.mem_top a
    have hb : b ∈ A := htop ▸ Subgroup.mem_top b
    obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm ha
    obtain ⟨u₂, hu₂, d₂, hd₂, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hb
    have hdd : d₁ * d₂ = d₂ * d₁ := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hd₁
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hd₂
      exact (Commute.zpow_zpow_self w i j).eq
    calc u₁ * d₁ * (u₂ * d₂) = u₁ * (d₁ * u₂) * d₂ := by group
      _ = u₁ * (u₂ * d₁) * d₂ := by rw [← hcomm u₂ hu₂ d₁ hd₁]
      _ = (u₁ * u₂) * (d₁ * d₂) := by group
      _ = (u₂ * u₁) * (d₂ * d₁) := by rw [hVc u₁ hu₁ u₂ hu₂, hdd]
      _ = u₂ * (u₁ * d₂) * d₁ := by group
      _ = u₂ * (d₂ * u₁) * d₁ := by rw [hcomm u₁ hu₁ d₂ hd₂]
      _ = u₂ * d₂ * (u₁ * d₁) := by group
  have hdvd : Nat.card A ∣ 8 := hcard ▸ Subgroup.card_subgroup_dvd_card A
  have hle : Nat.card V ≤ Nat.card A := Subgroup.card_le_of_le le_sup_left
  have hA8 : Nat.card A ≠ 8 := fun h =>
    hAtop ((Subgroup.card_eq_iff_eq_top A).1 (h.trans hcard.symm))
  have hA8' : Nat.card A ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hA4 : Nat.card A = 4 := by
    have h4 : 4 ≤ Nat.card A := hV4.trans hle
    interval_cases hAc : Nat.card A
    · rfl
    · omega
    · omega
    · omega
    · omega
  have hVA : V = A := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  rw [hVA]
  exact Subgroup.mem_sup_right (mem_zpowers w)


theorem sq_mem_of_centralizes {T Q E : Subgroup G} (hQT : Q ≤ T)
    (hQn : ∀ s ∈ T, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) (hcard : Nat.card T = 8 * Nat.card Q)
    (hna : ∃ a ∈ T, ∃ b ∈ T, a * b * a⁻¹ * b⁻¹ ∉ Q)
    (hET : E ≤ T) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hEs : ∀ e ∈ E, e * e = 1)
    (hE : 4 * Nat.card ↥(E ⊓ Q) ≤ Nat.card E)
    {v : G} (hv : v ∈ T) (hvE : ∀ e ∈ E, v * e = e * v) : v * v ∈ Q := by
  classical
  have hNQ : (Q.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g g.2 n hn⟩
  let π : ↥T →* ↥T ⧸ Q.subgroupOf T := QuotientGroup.mk' _
  have hker : π.ker = Q.subgroupOf T := QuotientGroup.ker_mk' _
  have hQc : Nat.card (Q.subgroupOf T) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv
  have hTc : Nat.card ↥T = Nat.card (↥T ⧸ Q.subgroupOf T) * Nat.card Q := by
    rw [← hQc]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf T)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h8 : Nat.card (↥T ⧸ Q.subgroupOf T) = 8 := by
    have : Nat.card (↥T ⧸ Q.subgroupOf T) * Nat.card Q = 8 * Nat.card Q := by rw [← hTc, hcard]
    exact Nat.eq_of_mul_eq_mul_right hQpos this
  set Et : Subgroup ↥T := E.subgroupOf T with hEt
  have hEtc : Nat.card Et = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv
  have hcardE := Thm1.card_eq_card_map_mul_card_inf_ker π Et
  have hinf : Nat.card ↥(Et ⊓ π.ker) = Nat.card ↥(E ⊓ Q) := by
    have e1 : Et ⊓ Q.subgroupOf T = (E ⊓ Q).subgroupOf T := by
      ext g; simp [hEt, Subgroup.mem_subgroupOf]
    rw [hker, e1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hET)).toEquiv
  rw [hEtc, hinf] at hcardE
  have hEpos : 0 < Nat.card ↥(E ⊓ Q) := Nat.card_pos
  have hV4 : 4 ≤ Nat.card ↥(Et.map π) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card E ≤ 3 * Nat.card ↥(E ⊓ Q) := by
      rw [hcardE]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hna' : ∃ a b : ↥T ⧸ Q.subgroupOf T, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    refine ⟨π ⟨a, ha⟩, π ⟨b, hb⟩, fun hcomm => hab ?_⟩
    have h1 : π (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]; group
    have h2 := (MonoidHom.mem_ker).2 h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hVc : ∀ e ∈ Et.map π, ∀ e' ∈ Et.map π, e * e' = e' * e := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc _ ha _ hb)
  have hw : ∀ e ∈ Et.map π, π ⟨v, hv⟩ * e = e * π ⟨v, hv⟩ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvE _ ha)
  have hmem := mem_of_centralizes_of_card_eight h8 hna' hV4 hVc hw
  obtain ⟨a, ha, haw⟩ := hmem
  have hsq : π (⟨v, hv⟩ * ⟨v, hv⟩) = 1 := by
    rw [map_mul, ← haw, ← map_mul]
    have : a * a = 1 := Subtype.ext (hEs _ ha)
    rw [this, map_one]
  have h3 : (⟨v, hv⟩ * ⟨v, hv⟩ : ↥T) ∈ π.ker := hsq
  rw [hker, Subgroup.mem_subgroupOf] at h3
  exact h3


theorem isSylowOf_of_le_top {T H : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hTH : T ≤ H) :
    IsSylowOf 2 T H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hT ⊢
  obtain ⟨-, hp, hdvd⟩ := hT
  refine ⟨hTH, hp, fun h2 => hdvd ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top]
  exact dvd_mul_of_dvd_left h2 _

theorem burnside_central {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {a g : G}
    (ha : ∀ s ∈ S, s * a = a * s) (hb : ∀ s ∈ S, s * (g⁻¹ * a * g) = (g⁻¹ * a * g) * s) :
    ∃ n ∈ normalizer (S : Set G), n⁻¹ * a * n = g⁻¹ * a * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b : G := g⁻¹ * a * g with hbdef
  have hSb : S ≤ centralizer ({b} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hb s hs)
  have hSC : IsSylowOf 2 S (centralizer ({b} : Set G)) := isSylowOf_of_le_top hS hSb
  set S' : Subgroup G := cj g⁻¹ S with hS'
  have hmemS' : ∀ z, z ∈ S' ↔ g * z * g⁻¹ ∈ S := by
    intro z
    rw [hS', mem_cj_iff, inv_inv]
  have hS'C : S' ≤ centralizer ({b} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    have hs : g * z * g⁻¹ ∈ S := (hmemS' z).1 hz
    have h1 := ha _ hs
    have e1 : b * z = g⁻¹ * (a * (g * z * g⁻¹)) * g := by simp only [hbdef]; group
    have e2 : z * b = g⁻¹ * ((g * z * g⁻¹) * a) * g := by simp only [hbdef]; group
    rw [e2, e1, h1]
  have hS'2 : IsPGroup 2 ↥S' := hS.isPGroup.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨c, hcC, hcS⟩ := Th2.exists_cj_le_of_isSylowOf hSC hS'C hS'2
  have hcb : c * b = b * c := mem_centralizer_singleton_iff.1 hcC
  have hcard : Nat.card S = Nat.card ↥(cj c S') := by
    have e1 : Nat.card ↥(cj c S') = Nat.card ↥S' :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have e2 : Nat.card ↥S' = Nat.card ↥S :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [e1, e2]
  have hcS' : cj c S' = S := Subgroup.eq_of_le_of_card_ge hcS hcard.le
  have hrev : ∀ s ∈ S, c⁻¹ * s * c ∈ S' := by
    intro s hs
    rw [← hcS'] at hs
    exact (mem_cj_iff c S' s).1 hs
  have hfwd : ∀ z ∈ S', c * z * c⁻¹ ∈ S := by
    intro z hz
    rw [← hcS']
    refine (mem_cj_iff c S' _).2 ?_
    have e : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    rw [e]; exact hz
  refine ⟨g * c⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have h1 := (hmemS' _).1 (hrev s hs)
      have e : g * (c⁻¹ * s * c) * g⁻¹ = g * c⁻¹ * s * (g * c⁻¹)⁻¹ := by group
      rwa [e] at h1
    · intro hs
      have e : g * c⁻¹ * s * (g * c⁻¹)⁻¹ = g * (c⁻¹ * s * c) * g⁻¹ := by group
      rw [e] at hs
      have h2 : c⁻¹ * s * c ∈ S' := (hmemS' _).2 hs
      have h3 := hfwd _ h2
      have e3 : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
      rwa [e3] at h3
  · have e : (g * c⁻¹)⁻¹ * a * (g * c⁻¹) = c * (g⁻¹ * a * g) * c⁻¹ := by group
    rw [e]
    change c * b * c⁻¹ = b
    rw [hcb]; group

theorem eq_of_normalizer_le_centralizer {T S : Subgroup G} {x : G} (hS : IsSylowOf 2 S ⊤)
    (hTS : T ≤ S) (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hn : ∀ n ∈ S, n ∈ normalizer (T : Set G) → n * x = x * n) : T = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hnil : Group.IsNilpotent ↥S := hS2.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    apply le_antisymm hTS
    intro s hs
    have : (⟨s, hs⟩ : ↥S) ∈ T.subgroupOf S := by rw [h]; trivial
    exact this
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥S) (T.subgroupOf S) hlt
  obtain ⟨m, hmN, hmT⟩ := Set.exists_of_ssubset hgrow
  have hmN' : m ∈ normalizer ((T.subgroupOf S : Subgroup ↥S) : Set ↥S) := hmN
  have hmNG : (m : G) ∈ normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hmN' ⊢
    intro h
    by_cases hh : h ∈ S
    · have := hmN' ⟨h, hh⟩
      simp only [Subgroup.mem_subgroupOf] at this
      simpa using this
    · constructor
      · intro hT'
        exact absurd (hTS hT') hh
      · intro hT'
        exfalso
        apply hh
        have h1 : (m : G) * h * (m : G)⁻¹ ∈ S := hTS hT'
        have h2 := S.mul_mem (S.mul_mem (S.inv_mem m.2) h1) m.2
        simpa [mul_assoc] using h2
  have hmx : (m : G) * x = x * (m : G) := hn m m.2 hmNG
  have hmC : (m : G) ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hmx
  set Y : Subgroup G := T ⊔ zpowers (m : G) with hY
  have hTY : T ≤ Y := le_sup_left
  have hYC : Y ≤ centralizer ({x} : Set G) := sup_le hT.le (zpowers_le.2 hmC)
  have hYS : Y ≤ S := sup_le hTS (zpowers_le.2 m.2)
  have hY2 : IsPGroup 2 ↥Y := hS2.to_le hYS
  have hYT : Y = T := hT.eq_of_le hTY hYC hY2
  apply hmT
  have : (m : G) ∈ T := by
    rw [← hYT]; exact mem_sup_right (mem_zpowers _)
  exact this

end CFSG.GH74.GLS.Th2.R714
