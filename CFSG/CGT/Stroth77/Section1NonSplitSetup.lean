module

public import CFSG.CGT.Stroth77.Section1SplitFacts

public section

namespace CFSG.CGT.Stroth77

open Subgroup

variable {G : Type*} [Group G] (ι : ↥Tsp →* G)

@[expose] def trS (K : Subgroup Msp) : Subgroup G := (K.subgroupOf Tsp).map ι

@[expose] noncomputable def ιe (m : Msp) : G := open Classical in
  if h : m ∈ Tsp then ι ⟨m, h⟩ else 1

variable {ι}

theorem ιe_apply {m : Msp} (h : m ∈ Tsp) : ιe ι m = ι ⟨m, h⟩ := by
  unfold ιe; rw [dif_pos h]

theorem ιe_mul {a b : Msp} (ha : a ∈ Tsp) (hb : b ∈ Tsp) : ιe ι (a * b) = ιe ι a * ιe ι b := by
  rw [ιe_apply (mul_mem ha hb), ιe_apply ha, ιe_apply hb, ← map_mul]; rfl

theorem ιe_inv {a : Msp} (ha : a ∈ Tsp) : ιe ι a⁻¹ = (ιe ι a)⁻¹ := by
  rw [ιe_apply (inv_mem ha), ιe_apply ha, ← map_inv]; rfl

theorem ιe_one : ιe ι 1 = 1 := by
  rw [ιe_apply (one_mem _)]; exact map_one ι

theorem ιe_injective (hι : Function.Injective ι) {a b : Msp} (ha : a ∈ Tsp) (hb : b ∈ Tsp)
    (h : ιe ι a = ιe ι b) : a = b := by
  rw [ιe_apply ha, ιe_apply hb] at h
  exact congrArg Subtype.val (hι h)

theorem mem_trS {K : Subgroup Msp} {g : G} :
    g ∈ trS ι K ↔ ∃ m, m ∈ K ∧ m ∈ Tsp ∧ ιe ι m = g := by
  constructor
  · rintro ⟨⟨m, hmT⟩, hmK, rfl⟩
    exact ⟨m, mem_subgroupOf.1 hmK, hmT, ιe_apply hmT⟩
  · rintro ⟨m, hmK, hmT, rfl⟩
    exact ⟨⟨m, hmT⟩, mem_subgroupOf.2 hmK, (ιe_apply hmT).symm⟩

theorem ιe_mem_trS {K : Subgroup Msp} {m : Msp} (hK : m ∈ K) (hT : m ∈ Tsp) :
    ιe ι m ∈ trS ι K := mem_trS.2 ⟨m, hK, hT, rfl⟩

theorem ιe_mem_range {m : Msp} (hT : m ∈ Tsp) : ιe ι m ∈ ι.range :=
  ⟨⟨m, hT⟩, (ιe_apply hT).symm⟩

theorem trS_le_range (K : Subgroup Msp) : trS ι K ≤ ι.range := map_le_range ι _

theorem trS_mono {K L : Subgroup Msp} (h : K ≤ L) : trS ι K ≤ trS ι L :=
  map_mono (subgroupOf_mono _ h)

theorem card_trS (hι : Function.Injective ι) {K : Subgroup Msp} (hK : K ≤ Tsp) :
    Nat.card (trS ι K) = Nat.card K := by
  rw [trS, card_map_of_injective hι]
  exact Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv

theorem exists_ιe_eq {g : G} (hg : g ∈ ι.range) : ∃ m, m ∈ Tsp ∧ ιe ι m = g := by
  obtain ⟨⟨m, hm⟩, rfl⟩ := hg
  exact ⟨m, hm, ιe_apply hm⟩

theorem eq_trS_comap {B : Subgroup G} (hB : B ≤ ι.range) :
    B = trS ι ((B.comap ι).map Tsp.subtype) := by
  rw [trS, ← comap_subtype, comap_map_eq_self_of_injective Subtype.val_injective,
    map_comap_eq_self hB]


theorem card_range (hι : Function.Injective ι) : Nat.card ι.range = 256 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, card_Tsp]

theorem trS_Asp_comm {x y : G} (hx : x ∈ trS ι Asp) (hy : y ∈ trS ι Asp) : x * y = y * x := by
  obtain ⟨m, hmA, hmT, rfl⟩ := mem_trS.1 hx
  obtain ⟨n, hnA, hnT, rfl⟩ := mem_trS.1 hy
  rw [← ιe_mul hmT hnT, ← ιe_mul hnT hmT, Asp_comm hmA hnA]

theorem trS_Asp_sq {x : G} (hx : x ∈ trS ι Asp) : x * x = 1 := by
  obtain ⟨m, hmA, hmT, rfl⟩ := mem_trS.1 hx
  rw [← ιe_mul hmT hmT, Asp_sq hmA, ιe_one]

theorem card_trS_Asp (hι : Function.Injective ι) : Nat.card (trS ι Asp) = 32 :=
  (card_trS hι Asp_le_Tsp).trans card_Asp

theorem mem_of_ιe_mem_trS (hι : Function.Injective ι) {K : Subgroup Msp} {m : Msp}
    (hm : m ∈ Tsp) (h : ιe ι m ∈ trS ι K) : m ∈ K := by
  obtain ⟨n, hnK, hnT, hn⟩ := mem_trS.1 h
  rw [← ιe_injective hι hnT hm hn]
  exact hnK

theorem eq_trS_Asp (hι : Function.Injective ι) (B : Subgroup G) (hB : B ≤ ι.range)
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : Nat.card B = 32) : B = trS ι Asp := by
  set B' := (B.comap ι).map Tsp.subtype with hB'
  have hB'T : B' ≤ Tsp := by rw [hB']; exact map_subtype_le _
  have hB'c : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have h := hc _ hu _ hv
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hι h)
  have hcard' : Nat.card B' = 32 := by
    rw [hB', card_map_of_injective Subtype.val_injective, ← hcard]
    conv_rhs => rw [← map_comap_eq_self hB]
    exact (card_map_of_injective hι).symm
  have := Asp_unique B' hB'T hB'c hcard'
  rw [eq_trS_comap hB, ← hB', this]

theorem mem_trS_Asp_of_commute (hι : Function.Injective ι) {g : G} (hg : g ∈ ι.range)
    (h : ∀ a ∈ trS ι Asp, g * a = a * g) : g ∈ trS ι Asp := by
  obtain ⟨m, hmT, rfl⟩ := exists_ιe_eq hg
  refine ιe_mem_trS (mem_Asp_of_commute hmT fun a ha => ?_) hmT
  have haT : a ∈ Tsp := Asp_le_Tsp ha
  have := h _ (ιe_mem_trS ha haT)
  rw [← ιe_mul hmT haT, ← ιe_mul haT hmT] at this
  exact ιe_injective hι (mul_mem hmT haT) (mul_mem haT hmT) this

theorem conj_mem_trS_Esp (hι : Function.Injective ι) {g : G}
    (hgA : g ∈ normalizer (trS ι Asp : Set G)) (hgAE : g ∈ normalizer (trS ι AEsp : Set G))
    {x : G} (hx : x ∈ trS ι Esp) : g * x * g⁻¹ ∈ trS ι Esp := by
  have hgA' := mem_normalizer_iff.1 hgA
  have hgAE' := mem_normalizer_iff.1 hgAE
  have hgAE'' : ∀ y, y ∈ trS ι AEsp ↔ g⁻¹ * y * g⁻¹⁻¹ ∈ trS ι AEsp :=
    mem_normalizer_iff.1 (inv_mem hgAE)
  obtain ⟨m, hmE, hmT, rfl⟩ := mem_trS.1 hx
  have hmAE : m ∈ AEsp := Esp_le_AEsp hmE
  obtain ⟨m', hm'AE, hm'T, hm'⟩ :=
    mem_trS.1 ((hgAE' _).1 (ιe_mem_trS hmAE hmT))
  have hP := (mem_Esp_iff hmAE).1 hmE
  refine ιe_mem_trS ?_ hm'T |> fun h => hm' ▸ h
  refine (mem_Esp_iff hm'AE).2 ⟨?_, ?_, ?_⟩
  ·
    refine ιe_injective hι (mul_mem hm'T hm'T) (one_mem _) ?_
    rw [ιe_mul hm'T hm'T, hm', ιe_one]
    calc g * ιe ι m * g⁻¹ * (g * ιe ι m * g⁻¹) = g * ιe ι (m * m) * g⁻¹ := by
          rw [ιe_mul hmT hmT]; group
      _ = 1 := by rw [hP.1, ιe_one]; group
  ·
    intro hm'A
    have hxA : ιe ι m ∈ trS ι Asp := (hgA' _).2 (hm' ▸ ιe_mem_trS hm'A hm'T)
    have hmA : m ∈ Asp := mem_of_ιe_mem_trS hι hmT hxA
    intro z hz
    have hzT : z ∈ Tsp := AEsp_le_Tsp hz
    obtain ⟨z', hz'AE, hz'T, hz'⟩ := mem_trS.1 ((hgAE'' _).1 (ιe_mem_trS hz hzT))
    have hc := hP.2.1 hmA z' hz'AE
    refine ιe_injective hι (mul_mem hm'T hzT) (mul_mem hzT hm'T) ?_
    rw [ιe_mul hm'T hzT, ιe_mul hzT hm'T, hm']
    have hz'' : ιe ι z = g * ιe ι z' * g⁻¹ := by rw [hz']; group
    rw [hz'']
    have hc' : ιe ι m * ιe ι z' = ιe ι z' * ιe ι m := by
      rw [← ιe_mul hmT hz'T, ← ιe_mul hz'T hmT, hc]
    calc g * ιe ι m * g⁻¹ * (g * ιe ι z' * g⁻¹) = g * (ιe ι m * ιe ι z') * g⁻¹ := by group
      _ = g * (ιe ι z' * ιe ι m) * g⁻¹ := by rw [hc']
      _ = g * ιe ι z' * g⁻¹ * (g * ιe ι m * g⁻¹) := by group
  ·
    intro hm'A
    have hmA : m ∉ Asp := fun hmA => hm'A (mem_of_ιe_mem_trS hι hm'T
      (hm' ▸ (hgA' _).1 (ιe_mem_trS hmA hmT)))
    obtain ⟨z, hzAE, hzA, hmzA, hz2, hmz⟩ := hP.2.2 hmA
    have hzT : z ∈ Tsp := AEsp_le_Tsp hzAE
    obtain ⟨z', hz'AE, hz'T, hz'⟩ := mem_trS.1 ((hgAE' _).1 (ιe_mem_trS hzAE hzT))
    refine ⟨z', hz'AE, ?_, ?_, ?_, ?_⟩
    · intro hz'A
      apply hzA
      refine mem_of_ιe_mem_trS hι hzT ((hgA' _).2 ?_)
      rw [← hz']; exact ιe_mem_trS hz'A hz'T
    · intro h
      apply hmzA
      have hT1 : m'⁻¹ * z' ∈ Tsp := mul_mem (inv_mem hm'T) hz'T
      have hT2 : m⁻¹ * z ∈ Tsp := mul_mem (inv_mem hmT) hzT
      refine mem_of_ιe_mem_trS hι hT2 ((hgA' _).2 ?_)
      have e : g * ιe ι (m⁻¹ * z) * g⁻¹ = ιe ι (m'⁻¹ * z') := by
        rw [ιe_mul (inv_mem hm'T) hz'T, ιe_inv hm'T, hm', hz', ιe_mul (inv_mem hmT) hzT,
          ιe_inv hmT]
        group
      rw [e]; exact ιe_mem_trS h hT1
    · refine ιe_injective hι (mul_mem hz'T hz'T) (one_mem _) ?_
      rw [ιe_mul hz'T hz'T, hz', ιe_one]
      calc g * ιe ι z * g⁻¹ * (g * ιe ι z * g⁻¹) = g * ιe ι (z * z) * g⁻¹ := by
            rw [ιe_mul hzT hzT]; group
        _ = 1 := by rw [hz2, ιe_one]; group
    · refine ιe_injective hι (mul_mem hm'T hz'T) (mul_mem hz'T hm'T) ?_
      rw [ιe_mul hm'T hz'T, ιe_mul hz'T hm'T, hm', hz']
      have hc' : ιe ι m * ιe ι z = ιe ι z * ιe ι m := by
        rw [← ιe_mul hmT hzT, ← ιe_mul hzT hmT, hmz]
      calc g * ιe ι m * g⁻¹ * (g * ιe ι z * g⁻¹) = g * (ιe ι m * ιe ι z) * g⁻¹ := by group
        _ = g * (ιe ι z * ιe ι m) * g⁻¹ := by rw [hc']
        _ = g * ιe ι z * g⁻¹ * (g * ιe ι m * g⁻¹) := by group

theorem mem_normalizer_trS_Esp (hι : Function.Injective ι) {g : G}
    (hgA : g ∈ normalizer (trS ι Asp : Set G)) (hgAE : g ∈ normalizer (trS ι AEsp : Set G)) :
    g ∈ normalizer (trS ι Esp : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_trS_Esp hι hgA hgAE, fun h => ?_⟩
  have := conj_mem_trS_Esp hι (inv_mem hgA) (inv_mem hgAE) h
  simpa [mul_assoc] using this

theorem exists_Dsp_mul_mem (hι : Function.Injective ι) {g : G} (hg : g ∈ ι.range) :
    ∃ d, d ∈ Dsp ∧ d ∈ Tsp ∧ g * (ιe ι d)⁻¹ ∈ trS ι Asp := by
  obtain ⟨m, hmT, rfl⟩ := exists_ιe_eq hg
  obtain ⟨d, hdD, hmd⟩ := exists_mem_Dsp hmT
  have hdT : d ∈ Tsp := Dsp_le_Tsp hdD
  refine ⟨d, hdD, hdT, ?_⟩
  rw [← ιe_inv hdT, ← ιe_mul hmT (inv_mem hdT)]
  exact ιe_mem_trS hmd (mul_mem hmT (inv_mem hdT))

theorem ιe_conj {a b : Msp} (ha : a ∈ Tsp) (hb : b ∈ Tsp) :
    ιe ι a * ιe ι b * (ιe ι a)⁻¹ = ιe ι (a * b * a⁻¹) := by
  rw [ιe_mul (mul_mem ha hb) (inv_mem ha), ιe_mul ha hb, ιe_inv ha]

theorem spX1_mem_Tsp : spX1 ∈ Tsp := Asp_le_Tsp spX1_mem_Asp
theorem spY1_mem_Tsp : spY1 ∈ Tsp := Asp_le_Tsp spY1_mem_Asp
theorem spX_mem_Tsp : spX ∈ Tsp := Asp_le_Tsp spX_mem_Asp
theorem spY_mem_Tsp : spY ∈ Tsp := Asp_le_Tsp spY_mem_Asp
theorem spW_mem_Tsp : spW ∈ Tsp := Asp_le_Tsp spW_mem_Asp
theorem spUV_mem_Tsp : spUV ∈ Tsp := Esp_le_Tsp spUV_mem_Esp
theorem spT_mem_Tsp : spT ∈ Tsp := Esp_le_Tsp spT_mem_Esp
theorem spU_mem_Tsp : spU ∈ Tsp := Dsp_le_Tsp spU_mem_Dsp

theorem ιe_ite (p : Prop) [Decidable p] {m : Msp} (hm : m ∈ Tsp) :
    ιe ι (if p then m else 1) = if p then ιe ι m else 1 := by
  split_ifs
  · rfl
  · exact ιe_one

theorem ιe_spPhi (r : Nat) : ιe ι (spPhi r) =
    (if r.testBit 0 then ιe ι spX1 else 1) * (if r.testBit 1 then ιe ι spY1 else 1) *
      (if r.testBit 2 then ιe ι spX else 1) * (if r.testBit 3 then ιe ι spY else 1) *
      (if r.testBit 4 then ιe ι spW else 1) := by
  have hT : ∀ (p : Prop) [Decidable p] {m : Msp}, m ∈ Tsp → (if p then m else 1) ∈ Tsp := by
    intro p _ m hm; split_ifs
    · exact hm
    · exact one_mem _
  unfold spPhi
  rw [ιe_mul (mul_mem (mul_mem (mul_mem (hT _ spX1_mem_Tsp) (hT _ spY1_mem_Tsp))
    (hT _ spX_mem_Tsp)) (hT _ spY_mem_Tsp)) (hT _ spW_mem_Tsp),
    ιe_mul (mul_mem (mul_mem (hT _ spX1_mem_Tsp) (hT _ spY1_mem_Tsp)) (hT _ spX_mem_Tsp))
      (hT _ spY_mem_Tsp),
    ιe_mul (mul_mem (hT _ spX1_mem_Tsp) (hT _ spY1_mem_Tsp)) (hT _ spX_mem_Tsp),
    ιe_mul (hT _ spX1_mem_Tsp) (hT _ spY1_mem_Tsp), ιe_ite _ spX1_mem_Tsp,
    ιe_ite _ spY1_mem_Tsp, ιe_ite _ spX_mem_Tsp, ιe_ite _ spY_mem_Tsp, ιe_ite _ spW_mem_Tsp]

theorem spPhi_mem_Tsp (r : Nat) : spPhi r ∈ Tsp := Asp_le_Tsp (spPhi_mem_Asp r)

end CFSG.CGT.Stroth77
