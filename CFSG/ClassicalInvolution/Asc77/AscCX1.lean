module

public import CFSG.ClassicalInvolution.Asc77.AscCX3
public import CFSG.ClassicalInvolution.Asc77.AscS22H
public import CFSG.ClassicalInvolution.Asc77.AscC25W16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Facts

@[expose] def LayerTwinFacts {Y : Type} [Group Y] (A A' : Subgroup Y) (z' : Y) : Prop :=
  Subgroup.center Y = ⊥ ∧ oddCoreOf A = ⊥ ∧ oddCoreOf A' = ⊥ ∧
  (∀ P : Subgroup (MulAut Y), IsPGroup 2 P →
    (∀ β ∈ P, (∀ y ∈ A, β y = y) ∧ (∀ y ∈ A', β y = y)) →
      (∀ β ∈ P, β * β = 1) ∧ Nat.card P ≤ 4) ∧
  (∀ β : MulAut Y, (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) → β * β = 1 → β ≠ 1 →
    β ≠ MulAut.conj z' →
      ∃ x : Y, β x = x ∧ x * z' * x⁻¹ ≠ z' ∧ (x * z' * x⁻¹) * z' = z' * (x * z' * x⁻¹))

variable {p f : ℕ} [Fact p.Prime]


theorem layerTwinFacts_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Y : Type} [Group Y] [Finite Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemData p f Y Φ) {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (hD1 : D.card = 1) (hi : ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) : LayerTwinFacts A A' z' := by
  classical
  obtain ⟨hcen, hO, hO'⟩ := layer5_facts hp2 hq D hD1 hi htw
  have hcent := C25W.cent5_proved (p := p) (f := f) hp2 hq Y Φ D A A' z' a₀ b₀ hD1 hi htw
  have hz2 : z' * z' = 1 := htw.hzA.sq
  have hcc : MulAut.conj z' * MulAut.conj z' = 1 := by
    rw [← map_mul, hz2, map_one]
  have hmem : ∀ β : MulAut Y, (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) →
      β = 1 ∨ β = MulAut.conj z' := by
    intro β hβ hβ'
    rcases hcent β hβ hβ' with h | h
    · exact Or.inl h
    · right
      ext y
      exact h y
  refine ⟨hcen, hO, hO', fun P _ hP => ?_, fun β hβ hβ' _ h1 hc => ?_⟩
  · refine ⟨fun β hβP => ?_, ?_⟩
    · rcases hmem β (hP β hβP).1 (hP β hβP).2 with rfl | rfl
      · exact mul_one 1
      · exact hcc
    · have hinj : Function.Injective
          (fun β : P => if (β : MulAut Y) = 1 then (0 : Fin 2) else 1) := by
        intro β₁ β₂ h
        apply Subtype.ext
        by_cases h₁ : (β₁ : MulAut Y) = 1 <;> by_cases h₂ : (β₂ : MulAut Y) = 1 <;>
          simp only [h₁, h₂, ↓reduceIte] at h
        · rw [h₁, h₂]
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rw [(hmem β₁ (hP β₁ β₁.2).1 (hP β₁ β₁.2).2).resolve_left h₁,
            (hmem β₂ (hP β₂ β₂.2).1 (hP β₂ β₂.2).2).resolve_left h₂]
      have h2 : Nat.card P ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_fin] at h2
      omega
  · rcases hmem β hβ hβ' with h | h
    · exact absurd h h1
    · exact absurd h hc

variable (p f) in
@[expose] def Layer6Twin : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 6 (!piSign p f) (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ → LayerTwinFacts A A' z'

end Facts

section Hom

variable {G : Type} [Group G]

@[expose] noncomputable def layerHom (Y H : Subgroup G) (hH : ∀ h ∈ H, conjSub h Y = Y) :
    ↥H →* MulAut (↥Y ⧸ classicalInvolutionOddCore ↥Y) where
  toFun h := C25Y.layerAut Y (hH h h.2)
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x fun x => ?_
    rw [C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp [C25Y.coe_conjOnSub]
  map_mul' g h := by
    ext x
    refine QuotientGroup.induction_on x fun x => ?_
    rw [MulAut.mul_apply, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp only [C25Y.coe_conjOnSub, Subgroup.coe_mul, mul_inv_rev]
    group

theorem layerHom_apply (Y H : Subgroup G) (hH : ∀ h ∈ H, conjSub h Y = Y) (h : ↥H) :
    layerHom Y H hH h = C25Y.layerAut Y (hH h h.2) := rfl

theorem mem_oddCore_of_mem_oddCoreOf [Finite G] {Y H : Subgroup G}
    (hH : ∀ h ∈ H, conjSub h Y = Y) {c : ↥H} (hc : (c : G) ∈ oddCoreOf Y) :
    c ∈ classicalInvolutionOddCore ↥H := by
  let N₀ : Subgroup ↥H := (oddCoreOf Y).subgroupOf H
  have hnorm : N₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * n * (g : G)⁻¹ ∈ conjSub (g : G) (oddCoreOf Y) :=
      Generic.conj_mem_conjSub hn
    rw [← Thompson.oddCoreOf_conjSub_eq, hH g g.2] at h1
    simpa using h1
  have hodd : Odd (Nat.card N₀) := by
    have hO : Odd (Nat.card (oddCoreOf Y)) := by
      unfold oddCoreOf
      rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥Y
    have hle : N₀.map H.subtype ≤ oddCoreOf Y := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hn
    have hdvd : Nat.card N₀ ∣ Nat.card (oddCoreOf Y) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hO hdvd
  exact le_sSup (show N₀ ∈ {N : Subgroup ↥H | N.Normal ∧ Odd (Nat.card N)} from ⟨hnorm, hodd⟩)
    (Subgroup.mem_subgroupOf.mpr hc)

end Hom

section Action

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}


theorem layerAut_fix_exactImg (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G} (hJ : J ∈ tqMembers Ω c)
    (hO : oddCoreOf (T7H.exactImg Ω c J) = ⊥) {v : G}
    (hvc : v ∈ Subgroup.centralizer ({c} : Set G)) (hvJ : v ∈ trivialOnQuot J) :
    ∀ y ∈ T7H.exactImg Ω c J,
      C25Y.layerAut (exactLayer Ω c) (conjSub_exactLayer hΩ.conjInvariant hvc) y = y := by
  intro y hy
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hy
  have hk : (k₀ : G) ∈ exactCore c J := Subgroup.mem_subgroupOf.mp hk₀
  have hvk : v * (k₀ : G) * v⁻¹ ∈ exactLayer Ω c := by
    have h1 : v * (k₀ : G) * v⁻¹ ∈ conjSub v (exactLayer Ω c) := Generic.conj_mem_conjSub k₀.2
    rwa [conjSub_exactLayer hΩ.conjInvariant hvc] at h1
  obtain ⟨n, hn, heq⟩ := S22.exists_odd_mul hΩ hc2 hJ hvc hvJ hk k₀.2 hvk
  rw [hO, Subgroup.mem_bot] at hn
  rw [hn, one_mul] at heq
  rw [QuotientGroup.mk'_apply, C25Y.layerAut_mk]
  exact heq

theorem mem_zStarOf_of_layerAut_eq_conj (hΩ : HypOmegaMod p f Ω) {b d z : G}
    (hdb : d ∈ Subgroup.centralizer ({b} : Set G)) (hzb : z ∈ Subgroup.centralizer ({b} : Set G))
    (hzd : z ∈ Subgroup.centralizer ({d} : Set G)) (hzY : z ∈ exactLayer Ω b)
    (hcen : Subgroup.center (↥(exactLayer Ω b) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω b)) =
      ⊥)
    (hd : ∀ y, C25Y.layerAut (exactLayer Ω b) (conjSub_exactLayer hΩ.conjInvariant hdb) y =
      T7H.toBar Ω b z hzY * y * (T7H.toBar Ω b z hzY)⁻¹) :
    z ∈ zStarOf (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set Y := exactLayer Ω b with hY
  set H := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) with hHdef
  have hHY : ∀ h ∈ H, conjSub h Y = Y := fun h hh =>
    conjSub_exactLayer hΩ.conjInvariant hh.1
  rw [C25W.mem_zStarOf_iff]
  refine ⟨⟨hzb, hzd⟩, fun y hy => ?_⟩
  have hyi : y⁻¹ ∈ H := H.inv_mem hy
  set w := y⁻¹ * z * y⁻¹⁻¹ with hw
  have hwY : w ∈ Y := by
    have h1 : w ∈ conjSub y⁻¹ Y := Generic.conj_mem_conjSub hzY
    rwa [hHY _ hyi] at h1
  set α := C25Y.layerAut Y (hHY _ hyi) with hα
  set δ := C25Y.layerAut Y (conjSub_exactLayer hΩ.conjInvariant hdb) with hδ
  have hαz : α (T7H.toBar Ω b z hzY) = T7H.toBar Ω b w hwY := by
    rw [hα]
    unfold T7H.toBar
    rw [QuotientGroup.mk'_apply, C25Y.layerAut_mk]
    rfl
  have hcomm : ∀ u, α (δ u) = δ (α u) := by
    intro u
    refine QuotientGroup.induction_on u fun u => ?_
    rw [hα, hδ, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp only [C25Y.coe_conjOnSub]
    have hyd : y⁻¹ * d = d * y⁻¹ := Subgroup.mem_centralizer_singleton_iff.mp hyi.2
    calc y⁻¹ * (d * (u : G) * d⁻¹) * y⁻¹⁻¹ = (y⁻¹ * d) * (u : G) * (y⁻¹ * d)⁻¹ := by group
      _ = (d * y⁻¹) * (u : G) * (d * y⁻¹)⁻¹ := by rw [hyd]
      _ = d * (y⁻¹ * (u : G) * y⁻¹⁻¹) * d⁻¹ := by group
  have hwz : T7H.toBar Ω b w hwY = T7H.toBar Ω b z hzY := by
    set zb := T7H.toBar Ω b z hzY with hzbdef
    set wb := T7H.toBar Ω b w hwY with hwbdef
    have hc : zb⁻¹ * wb ∈ Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y) := by
      rw [Subgroup.mem_center_iff]
      intro v
      obtain ⟨u, rfl⟩ := α.surjective v
      have h1 : α (δ u) = wb * α u * wb⁻¹ := by
        rw [hd u, map_mul, map_mul, map_inv, hαz]
      rw [hcomm u, hd (α u)] at h1
      have h2 : wb⁻¹ * zb * α u = α u * (wb⁻¹ * zb) := by
        calc wb⁻¹ * zb * α u = wb⁻¹ * (zb * α u * zb⁻¹) * zb := by group
          _ = wb⁻¹ * (wb * α u * wb⁻¹) * zb := by rw [h1]
          _ = α u * (wb⁻¹ * zb) := by group
      calc α u * (zb⁻¹ * wb) = (wb⁻¹ * zb)⁻¹ * ((wb⁻¹ * zb) * α u) * (zb⁻¹ * wb) := by group
        _ = (wb⁻¹ * zb)⁻¹ * (α u * (wb⁻¹ * zb)) * (zb⁻¹ * wb) := by rw [← h2]
        _ = zb⁻¹ * wb * α u := by group
    rw [hcen, Subgroup.mem_bot] at hc
    calc wb = zb * (zb⁻¹ * wb) := by group
      _ = zb := by rw [hc, mul_one]
  have hO : z⁻¹ * w ∈ oddCoreOf Y := by
    unfold T7H.toBar at hwz
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwz
    refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥Y).inv_mem hwz, ?_⟩
    simp
  have hmem : z⁻¹ * w ∈ H := by
    refine H.mul_mem (H.inv_mem ⟨hzb, hzd⟩) ?_
    rw [hw]
    exact H.mul_mem (H.mul_mem hyi ⟨hzb, hzd⟩) (H.inv_mem hyi)
  have h3 := mem_oddCore_of_mem_oddCoreOf hHY (c := ⟨z⁻¹ * w, hmem⟩) hO
  have e : z⁻¹ * y⁻¹ * z * y = z⁻¹ * w := by rw [hw]; group
  rw [e]
  exact Subgroup.mem_map.mpr ⟨_, h3, rfl⟩

theorem le_trivialOnQuot_of_layerAut_trivial (hΩ : HypOmegaMod p f Ω) {b : G} {F : Subgroup G}
    (hFb : F ≤ Subgroup.centralizer ({b} : Set G))
    (htriv : ∀ e (he : e ∈ F), ∀ y, C25Y.layerAut (exactLayer Ω b)
      (conjSub_exactLayer hΩ.conjInvariant (hFb he)) y = y) :
    F ≤ trivialOnQuot (exactLayer Ω b) := by
  intro e he
  have hY := conjSub_exactLayer hΩ.conjInvariant (hFb he)
  refine ⟨mem_normalizer_iff_conjSub_eq.mpr hY, fun x hx => ?_⟩
  have h1 := htriv e he (QuotientGroup.mk ⟨x, hx⟩)
  rw [C25Y.layerAut_mk, QuotientGroup.eq] at h1
  have h2 := (inferInstance : (classicalInvolutionOddCore ↥(exactLayer Ω b)).Normal).conj_mem _
    ((classicalInvolutionOddCore _).inv_mem h1) ⟨x, hx⟩
  refine Subgroup.mem_map.mpr ⟨_, h2, ?_⟩
  simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, C25Y.coe_conjOnSub,
    commutatorElement_def]
  group

theorem not_mem_zStarOf_of_layerAut_trivial (hΩ : HypOmegaMod p f Ω) {b z : G}
    {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFb : F ≤ Subgroup.centralizer ({b} : Set G))
    (hzF : z ∈ Subgroup.centralizer (F : Set G)) (hzY : z ∈ exactLayer Ω b)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcen : Subgroup.center (↥(exactLayer Ω b) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω b)) =
      ⊥)
    (htriv : ∀ e (he : e ∈ F), ∀ y, C25Y.layerAut (exactLayer Ω b)
      (conjSub_exactLayer hΩ.conjInvariant (hFb he)) y = y) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
  classical
  intro hz
  set Y := exactLayer Ω b with hY
  set N := classicalInvolutionOddCore ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set C := Subgroup.centralizer (F : Set G) with hC
  have hFY := le_trivialOnQuot_of_layerAut_trivial hΩ hFb htriv
  obtain ⟨-, hzc⟩ := (C25W.mem_zStarOf_iff C).mp hz
  set M : Subgroup (↥Y ⧸ N) :=
    ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y).map π with hM
  have hcover : ∀ x : ↥Y, ∃ h : ↥Y, (h : G) ∈ C ∧ π h = π x := by
    intro x
    obtain ⟨h, hh, n, hn, hxhn⟩ := exists_mem_inf_centralizer_mul hF2 hFY x.2
    refine ⟨⟨h, hh.1⟩, hh.2, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨h, hh.1⟩ : ↥Y)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥Y) : G) = n from hn'n, hxhn]
      group
    rw [e]
    exact hn'
  have hMnorm : M.Normal := by
    refine ⟨fun m hm y => ?_⟩
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨h, hhC, hhy⟩ := hcover y₀
    rw [← hhy]
    refine Subgroup.mem_map.mpr ⟨h * m₀ * h⁻¹, ?_, by simp [hπ]⟩
    rw [Subgroup.mem_subgroupOf] at hm₀ ⊢
    obtain ⟨hmO, hmY, hmC⟩ := hm₀
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (h : G) * m₀ * (h : G)⁻¹ ∈ conjSub (h : G) (oddCoreOf C) :=
        Generic.conj_mem_conjSub hmO
      rwa [← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_self_of_mem hhC] at h1
    · exact (h * m₀ * h⁻¹).2
    · exact C.mul_mem (C.mul_mem hhC hmC) (C.inv_mem hhC)
  have hModd : Odd (Nat.card M) := by
    have hO : Odd (Nat.card (oddCoreOf C)) := by
      unfold oddCoreOf
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥C
    have h1 : Nat.card M ∣ Nat.card ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y) ∣ Nat.card (oddCoreOf C) := by
      rw [← Subgroup.card_map_of_injective Y.subtype_injective]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx).1
    exact Odd.of_dvd_nat hO (h1.trans h2)
  have hMbot : M = ⊥ := by
    have h1 : M ≤ classicalInvolutionOddCore (↥Y ⧸ N) :=
      le_sSup (show M ∈ {K : Subgroup (↥Y ⧸ N) | K.Normal ∧ Odd (Nat.card K)} from
        ⟨hMnorm, hModd⟩)
    have h2 : classicalInvolutionOddCore (↥Y ⧸ N) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
    rw [h2] at h1
    exact le_bot_iff.mp h1
  have hzcen : π ⟨z, hzY⟩ ∈ Subgroup.center (↥Y ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨h, hhC, hhy⟩ := hcover y₀
    rw [← hhy]
    have hcom : (⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h ∈
        (oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      refine ⟨by simpa using hzc (h : G) hhC, SetLike.coe_mem _, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hzF) (C.inv_mem hhC)) hzF) hhC
    have h1 : π ((⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h) = 1 := by
      have : π ((⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h) ∈ M := Subgroup.mem_map_of_mem _ hcom
      rwa [hMbot, Subgroup.mem_bot] at this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π h * π ⟨z, hzY⟩ =
          π h * π ⟨z, hzY⟩ * ((π ⟨z, hzY⟩)⁻¹ * (π h)⁻¹ * π ⟨z, hzY⟩ * π h) := by
            rw [h1, mul_one]
      _ = π ⟨z, hzY⟩ * π h := by group
  rw [hcen, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzcen
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : orderOf (⟨⟨z, hzY⟩, hzcen⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzo] at hdvd
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem not_mem_zStarOf_of_fix_of_normalizes {Y F : Subgroup G} (hF2 : IsPGroup 2 F)
    (hFY : ∀ e ∈ F, conjSub e Y = Y) {z : G} (hzY : z ∈ Y) (hz2 : z * z = 1)
    {x : ↥Y ⧸ classicalInvolutionOddCore ↥Y}
    (hfix : ∀ e (he : e ∈ F), C25Y.layerAut Y (hFY e he) x = x)
    (hxz : x * QuotientGroup.mk ⟨z, hzY⟩ * x⁻¹ ≠ QuotientGroup.mk ⟨z, hzY⟩)
    (hxzc : (x * QuotientGroup.mk ⟨z, hzY⟩ * x⁻¹) * QuotientGroup.mk ⟨z, hzY⟩ =
      QuotientGroup.mk ⟨z, hzY⟩ * (x * QuotientGroup.mk ⟨z, hzY⟩ * x⁻¹)) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
  classical
  intro hz
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  set C := Subgroup.centralizer (F : Set G) with hC
  have hOodd : Odd (Nat.card (oddCoreOf Y)) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hAN : ∀ a ∈ F, ∀ n ∈ oddCoreOf Y, a * n * a⁻¹ ∈ oddCoreOf Y := by
    intro a ha n hn
    have h1 : a * n * a⁻¹ ∈ conjSub a (oddCoreOf Y) := Generic.conj_mem_conjSub hn
    rwa [← Thompson.oddCoreOf_conjSub_eq, hFY a ha] at h1
  have hx : ∀ a ∈ F, (x₀ : G)⁻¹ * (a * x₀ * a⁻¹) ∈ oddCoreOf Y := by
    intro a ha
    have h1 := hfix a ha
    rw [C25Y.layerAut_mk, QuotientGroup.eq] at h1
    refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥Y).inv_mem h1, ?_⟩
    simp [C25Y.coe_conjOnSub, mul_assoc]
  obtain ⟨n, hn, hfixn⟩ := exists_fixed_mem_coset_of_isPGroup hF2 hOodd hAN hx
  have hnY : n ∈ Y := Subgroup.map_subtype_le _ hn
  have hx₁Y : (x₀ : G) * n ∈ Y := Y.mul_mem x₀.2 hnY
  have hx₁C : (x₀ : G) * n ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro e he
    have := hfixn e he
    calc e * ((x₀ : G) * n) = e * ((x₀ : G) * n) * e⁻¹ * e := by group
      _ = (x₀ : G) * n * e := by rw [this]
  have hx₁bar : (QuotientGroup.mk (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y) :
      ↥Y ⧸ classicalInvolutionOddCore ↥Y) = QuotientGroup.mk x₀ := by
    rw [QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y)⁻¹ * x₀ = n'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥Y) : G) = n from hn'n]
      group
    rw [e]
    exact (classicalInvolutionOddCore ↥Y).inv_mem hn'
  have hc := ((C25W.mem_zStarOf_iff C).mp hz).2 ((x₀ : G) * n)⁻¹ (C.inv_mem hx₁C)
  set c : G := z⁻¹ * ((x₀ : G) * n)⁻¹⁻¹ * z * ((x₀ : G) * n)⁻¹ with hcdef
  have hcY : c ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem hzY) (Y.inv_mem (Y.inv_mem hx₁Y))) hzY)
      (Y.inv_mem hx₁Y)
  have hcodd : Odd (orderOf c) := by
    obtain ⟨c', hc', hc'c⟩ := Subgroup.mem_map.mp hc
    have h1 : orderOf c' ∣ Nat.card (classicalInvolutionOddCore ↥C) := by
      have := orderOf_dvd_natCard (⟨c', hc'⟩ : ↥(classicalInvolutionOddCore ↥C))
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf c = orderOf c' := by
      rw [← hc'c, Subgroup.subtype_apply, Subgroup.orderOf_coe]
    rw [h2]
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥C) h1
  set zb : ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk ⟨z, hzY⟩ with hzb
  set xb : ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk x₀ with hxb
  have hπc : (QuotientGroup.mk ⟨c, hcY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) =
      zb⁻¹ * (xb * zb * xb⁻¹) := by
    have e1 : (⟨c, hcY⟩ : ↥Y) = (⟨z, hzY⟩ : ↥Y)⁻¹ * ⟨(x₀ : G) * n, hx₁Y⟩ * ⟨z, hzY⟩ *
        (⟨(x₀ : G) * n, hx₁Y⟩ : ↥Y)⁻¹ := by
      apply Subtype.ext
      simp [hcdef]
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hx₁bar, ← hzb]
    group
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← QuotientGroup.mk_mul]
    have : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 := Subtype.ext hz2
    rw [this, QuotientGroup.mk_one]
  have hzi : zb⁻¹ = zb := by
    calc zb⁻¹ = zb⁻¹ * (zb * zb) := by rw [hzb2, mul_one]
      _ = zb := by group
  have hw2 : (xb * zb * xb⁻¹) * (xb * zb * xb⁻¹) = 1 := by
    calc (xb * zb * xb⁻¹) * (xb * zb * xb⁻¹) = xb * (zb * zb) * xb⁻¹ := by group
      _ = 1 := by rw [hzb2]; group
  have hord : orderOf (zb⁻¹ * (xb * zb * xb⁻¹)) = 2 := by
    rw [hzi]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc zb * (xb * zb * xb⁻¹) * (zb * (xb * zb * xb⁻¹)) =
            zb * ((xb * zb * xb⁻¹) * zb) * (xb * zb * xb⁻¹) := by group
        _ = zb * (zb * (xb * zb * xb⁻¹)) * (xb * zb * xb⁻¹) := by rw [hxzc]
        _ = (zb * zb) * ((xb * zb * xb⁻¹) * (xb * zb * xb⁻¹)) := by group
        _ = 1 := by rw [hzb2, hw2, one_mul]
    · intro h1
      apply hxz
      calc xb * zb * xb⁻¹ = zb⁻¹ * (zb * (xb * zb * xb⁻¹)) := by group
        _ = zb := by rw [h1, mul_one, hzi]
  have hdvd : orderOf (QuotientGroup.mk ⟨c, hcY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ∣
      orderOf (⟨c, hcY⟩ : ↥Y) :=
    orderOf_map_dvd (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) _
  rw [hπc, hord, Subgroup.orderOf_mk] at hdvd
  exact (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr hdvd)

theorem not_mem_zStarOf_of_layerAut_fix (hΩ : HypOmegaMod p f Ω) {b z : G}
    {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFb : F ≤ Subgroup.centralizer ({b} : Set G))
    (hzY : z ∈ exactLayer Ω b) (hz2 : z * z = 1)
    {x : ↥(exactLayer Ω b) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω b)}
    (hfix : ∀ e (he : e ∈ F), C25Y.layerAut (exactLayer Ω b)
      (conjSub_exactLayer hΩ.conjInvariant (hFb he)) x = x)
    (hxz : x * T7H.toBar Ω b z hzY * x⁻¹ ≠ T7H.toBar Ω b z hzY)
    (hxzc : (x * T7H.toBar Ω b z hzY * x⁻¹) * T7H.toBar Ω b z hzY =
      T7H.toBar Ω b z hzY * (x * T7H.toBar Ω b z hzY * x⁻¹)) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) :=
  not_mem_zStarOf_of_fix_of_normalizes hF2
    (fun _ he => conjSub_exactLayer hΩ.conjInvariant (hFb he)) hzY hz2 hfix hxz hxzc

end Action

end CFSG.ClassicalInvolution.Asc77.CX
