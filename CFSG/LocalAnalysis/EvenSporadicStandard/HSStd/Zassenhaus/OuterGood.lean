module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

omit [Finite G] in
theorem mem_vSub_iff (hv2 : v * v = 1) (y : ↥(centralizer ({v} : Set G))) :
    y ∈ vSub v ↔ (y : G) = 1 ∨ (y : G) = v := by
  have hz2 : vElem v * vElem v = 1 := Subtype.ext hv2
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
    rcases zpow_eq_one_or_self_aux hz2 k with h1 | h1
    · left
      rw [← hk, h1]
      rfl
    · right
      rw [← hk, h1]
      rfl
  · rintro (h1 | h1)
    · have : y = 1 := Subtype.ext h1
      rw [this]
      exact one_mem _
    · have : y = vElem v := Subtype.ext h1
      rw [this]
      exact mem_zpowers _

theorem conj_t_of_commute_tBar (h : HSOuterSetup G L t S z n v s)
    (x : ↥(centralizer ({v} : Set G))) (hx : QuotientGroup.mk x * h.tBar = h.tBar * QuotientGroup.mk x) :
    (x : G) * t * (x : G)⁻¹ = t ∨ (x : G) * t * (x : G)⁻¹ = t * v := by
  have hv2 : v * v = 1 := h.ctx.v_sq
  have hxv : (x : G) * v = v * (x : G) := mem_centralizer_singleton_iff.1 x.2
  have h1 : (QuotientGroup.mk (h.tElem * x) : OuterSection v) = QuotientGroup.mk (x * h.tElem) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hx.symm
  have h2 := (mem_vSub_iff hv2 _).1 (QuotientGroup.eq.1 h1)
  have ht2 : t * t = 1 := t_sq h
  have h3 : (((h.tElem * x)⁻¹ * (x * h.tElem) : ↥(centralizer ({v} : Set G))) : G) =
      (x : G)⁻¹ * t⁻¹ * (x : G) * t := by
    simp [HSOuterSetup.tElem, mul_assoc]
  rw [h3] at h2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv] at h2
  rcases h2 with h2 | h2
  · left
    have e : (x : G) * t = t * (x : G) := by
      calc (x : G) * t = t * (x : G) * ((x : G)⁻¹ * t * (x : G) * t) := by
            calc (x : G) * t = (t * t) * (x : G) * t := by rw [ht2, one_mul]
              _ = t * (x : G) * ((x : G)⁻¹ * t * (x : G) * t) := by group
        _ = t * (x : G) := by rw [h2, mul_one]
    calc (x : G) * t * (x : G)⁻¹ = t * (x : G) * (x : G)⁻¹ := by rw [e]
      _ = t := by group
  · right
    have e : (x : G) * t = t * (x : G) * v := by
      calc (x : G) * t = (t * t) * (x : G) * t := by rw [ht2, one_mul]
        _ = t * (x : G) * ((x : G)⁻¹ * t * (x : G) * t) := by group
        _ = t * (x : G) * v := by rw [h2]
    calc (x : G) * t * (x : G)⁻¹ = t * (x : G) * v * (x : G)⁻¹ := by rw [e]
      _ = t * ((x : G) * v * (x : G)⁻¹) := by group
      _ = t * v := by rw [hxv]; group

theorem exists_lift (h : HSOuterSetup G L t S z n v s) (hF : F v t) (y : OuterSection v)
    (hy : y * h.tBar = h.tBar * y) :
    ∃ x : ↥(centralizer ({v} : Set G)), QuotientGroup.mk x = y ∧ (x : G) * t = t * (x : G) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x, rfl, ?_⟩
  rcases conj_t_of_commute_tBar h x hy with h1 | h1
  · calc (x : G) * t = (x : G) * t * (x : G)⁻¹ * (x : G) := by group
      _ = t * (x : G) := by rw [h1]
  · exact absurd ⟨x, x.2, h1⟩ hF

omit [Finite G] in
theorem bp_comm (a b : Bool) {d : G}
    (hdt : d * t = t * d) (hdv : d * v = v * d) : d * (bp t a * bp v b) = (bp t a * bp v b) * d := by
  have h1 : d * bp t a = bp t a * d := by cases a <;> simp [bp, hdt]
  have h2 : d * bp v b = bp v b * d := by cases b <;> simp [bp, hdv]
  calc d * (bp t a * bp v b) = (d * bp t a) * bp v b := by rw [mul_assoc]
    _ = (bp t a * d) * bp v b := by rw [h1]
    _ = bp t a * (d * bp v b) := by rw [mul_assoc]
    _ = bp t a * (bp v b * d) := by rw [h2]
    _ = (bp t a * bp v b) * d := by rw [mul_assoc]

theorem bp_mem (h : HSOuterSetup G L t S z n v s) (a b : Bool) :
    (bp t a * bp v b) * t = t * (bp t a * bp v b) ∧ (bp t a * bp v b) * v = v * (bp t a * bp v b) := by
  have htv : t * v = v * t := h.t_comm_v
  constructor
  · symm
    exact bp_comm a b (d := t) rfl htv
  · symm
    exact bp_comm a b (d := v) htv.symm rfl

theorem decomp_Y (h : HSOuterSetup G L t S z n v s) {x : G} (hxt : x * t = t * x)
    (hxv : x * v = v * x) :
    ∃ β ∈ centralizer ({v} : Set G) ⊓ L, ∃ a b : Bool, x = β * (bp t a * bp v b) := by
  obtain ⟨β, hβL, a, b, rfl⟩ := exists_decomp h (d := x) (mem_centralizer_singleton_iff.2 hxt)
  obtain ⟨hc1, hc2⟩ := bp_mem h a b
  have hxv' : β * (bp t a * bp v b) * v = v * (β * (bp t a * bp v b)) := by
    simpa [mul_assoc] using hxv
  have h3 : β * v * (bp t a * bp v b) = v * β * (bp t a * bp v b) := by
    calc β * v * (bp t a * bp v b) = β * (v * (bp t a * bp v b)) := by rw [mul_assoc]
      _ = β * ((bp t a * bp v b) * v) := by rw [hc2]
      _ = β * (bp t a * bp v b) * v := (mul_assoc _ _ _).symm
      _ = v * (β * (bp t a * bp v b)) := hxv'
      _ = v * β * (bp t a * bp v b) := by rw [mul_assoc]
  have h4 : β * v = v * β := mul_right_cancel h3
  refine ⟨β, ⟨?_, hβL⟩, a, b, by rw [mul_assoc]⟩
  show β ∈ centralizer ({v} : Set G)
  exact mem_centralizer_singleton_iff.2 h4

omit [Finite G] in
theorem derivedCentralizerIn_le_Y (L : Subgroup G) (v : G) :
    derivedCentralizerIn L v ≤ centralizer ({v} : Set G) ⊓ L :=
  le_inf (derivedCentralizerIn_le_centralizer L v) (derivedCentralizerIn_le L v)

omit [Finite G] in
theorem conj_mem_derived {β l : G} (hβ : β ∈ centralizer ({v} : Set G) ⊓ L)
    (hl : l ∈ derivedCentralizerIn L v) : β * l * β⁻¹ ∈ derivedCentralizerIn L v := by
  rw [derivedCentralizerIn_eq_commutator] at hl ⊢
  have h1 : ⁅β, l⁆ ∈ ⁅centralizer ({v} : Set G) ⊓ L, centralizer ({v} : Set G) ⊓ L⁆ := by
    refine Subgroup.commutator_mem_commutator hβ ?_
    exact (derivedCentralizerIn_eq_commutator L v ▸ derivedCentralizerIn_le_Y L v) hl
  have : β * l * β⁻¹ = ⁅β, l⁆ * l := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact Subgroup.mul_mem _ h1 hl

theorem conj_mem_derived' (h : HSOuterSetup G L t S z n v s) {x l : G} (hxt : x * t = t * x)
    (hxv : x * v = v * x) (hl : l ∈ derivedCentralizerIn L v) :
    x * l * x⁻¹ ∈ derivedCentralizerIn L v := by
  obtain ⟨β, hβ, a, b, rfl⟩ := decomp_Y h hxt hxv
  have hlY := derivedCentralizerIn_le_Y L v hl
  have hct : (bp t a * bp v b) * l = l * (bp t a * bp v b) := by
    have := bp_comm (G := G) (t := t) (v := v) a b (d := l)
      (mem_centralizer_iff.1 h.t_mem l hlY.2)
      (mem_centralizer_singleton_iff.1 hlY.1)
    exact this.symm
  have : β * (bp t a * bp v b) * l * (β * (bp t a * bp v b))⁻¹ = β * l * β⁻¹ := by
    calc β * (bp t a * bp v b) * l * (β * (bp t a * bp v b))⁻¹
        = β * ((bp t a * bp v b) * l * (bp t a * bp v b)⁻¹) * β⁻¹ := by group
      _ = β * l * β⁻¹ := by rw [hct, mul_inv_cancel_right]
  rw [this]
  exact conj_mem_derived hβ hl

theorem commutator_mem_derived (h : HSOuterSetup G L t S z n v s) {x x' : G} (hxt : x * t = t * x)
    (hxv : x * v = v * x) (hxt' : x' * t = t * x') (hxv' : x' * v = v * x') :
    ⁅x, x'⁆ ∈ derivedCentralizerIn L v := by
  obtain ⟨β, hβ, a, b, rfl⟩ := decomp_Y h hxt hxv
  obtain ⟨β', hβ', a', b', rfl⟩ := decomp_Y h hxt' hxv'
  let D : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({v} : Set G)
  have hmemD : ∀ y ∈ centralizer ({v} : Set G) ⊓ L, y ∈ D := fun y hy =>
    ⟨mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h.t_mem y hy.2), hy.1⟩
  have hcD : ∀ a b : Bool, bp t a * bp v b ∈ D := fun a b =>
    ⟨mem_centralizer_singleton_iff.2 (bp_mem h a b).1,
      mem_centralizer_singleton_iff.2 (bp_mem h a b).2⟩
  have hcen : ∀ a b : Bool, (⟨bp t a * bp v b, hcD a b⟩ : ↥D) ∈ center ↥D := by
    intro a b
    rw [mem_center_iff]
    rintro ⟨d, hd1, hd2⟩
    apply Subtype.ext
    exact bp_comm a b (mem_centralizer_singleton_iff.1 hd1) (mem_centralizer_singleton_iff.1 hd2)
  have key := commutator_mul_central_mul
    (a := (⟨β, hmemD β hβ⟩ : ↥D)) (b := (⟨β', hmemD β' hβ'⟩ : ↥D)) (hcen a b) (hcen a' b')
  have key' := congrArg Subtype.val key
  have : ⁅β * (bp t a * bp v b), β' * (bp t a' * bp v b')⁆ = ⁅β, β'⁆ := by
    simpa [commutatorElement_def] using key'
  rw [this, derivedCentralizerIn_eq_commutator]
  exact Subgroup.commutator_mem_commutator hβ hβ'

omit [Finite G] in
theorem mk_vElem : (QuotientGroup.mk (vElem v) : OuterSection v) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (mem_zpowers _)

theorem v_not_mem_L (h : HSOuterSetup G L t S z n v s) : v ∉ L := fun hv =>
  h.ctx.v_outer ((le_sup_left : L ≤ L ⊔ zpowers t) hv)

theorem good_H3 (h : HSOuterSetup G L t S z n v s) (hF : F v t) (y : OuterSection v)
    (hy : y ∈ centralizer ((sectionImage v (derivedCentralizerIn L v) :
      Subgroup (OuterSection v)) : Set (OuterSection v)))
    (hyt : y * h.tBar = h.tBar * y) : y ∈ zpowers h.tBar := by
  have hv2 : v * v = 1 := h.ctx.v_sq
  obtain ⟨x, rfl, hxt⟩ := exists_lift h hF y hyt
  have hxv : (x : G) * v = v * (x : G) := mem_centralizer_singleton_iff.1 x.2
  obtain ⟨β, hβ, a, b, hx⟩ := decomp_Y h hxt hxv
  obtain ⟨hct, hcv⟩ := bp_mem h a b
  have hβc : ∀ l ∈ derivedCentralizerIn L v, β * l = l * β := by
    intro l hl
    have hlY := derivedCentralizerIn_le_Y L v hl
    have hlH : l ∈ centralizer ({v} : Set G) := hlY.1
    have hmem : (QuotientGroup.mk (⟨l, hlH⟩ : ↥(centralizer ({v} : Set G))) : OuterSection v) ∈
        sectionImage v (derivedCentralizerIn L v) := ⟨⟨l, hlH⟩, hl, rfl⟩
    have hc := mem_centralizer_iff.1 hy _ hmem
    have h1 : (QuotientGroup.mk (⟨l, hlH⟩ * x) : OuterSection v) =
        QuotientGroup.mk (x * ⟨l, hlH⟩) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hc
    have h2 := (mem_vSub_iff hv2 _).1 (QuotientGroup.eq.1 h1)
    have h3 : ((((⟨l, hlH⟩ * x)⁻¹ * (x * ⟨l, hlH⟩) :
        ↥(centralizer ({v} : Set G)))) : G) = (x : G)⁻¹ * l⁻¹ * (x : G) * l := by
      simp [mul_assoc]
    rw [h3, hx] at h2
    set c := bp t a * bp v b with hcdef
    have hcl : c * l = l * c :=
      (bp_comm a b (d := l) (mem_centralizer_iff.1 h.t_mem l hlY.2)
        (mem_centralizer_singleton_iff.1 hlH)).symm
    have hcβ : c * β = β * c :=
      (bp_comm a b (d := β) (mem_centralizer_iff.1 h.t_mem β hβ.2)
        (mem_centralizer_singleton_iff.1 hβ.1)).symm
    have hcκ : Commute c (β⁻¹ * l⁻¹ * β * l) :=
      (((((show Commute c β from hcβ).inv_right).mul_right (show Commute c l from hcl).inv_right).mul_right
        (show Commute c β from hcβ)).mul_right (show Commute c l from hcl))
    have h4 : (β * c)⁻¹ * l⁻¹ * (β * c) * l = β⁻¹ * l⁻¹ * β * l := by
      calc (β * c)⁻¹ * l⁻¹ * (β * c) * l = c⁻¹ * (β⁻¹ * l⁻¹ * β) * (c * l) := by group
        _ = c⁻¹ * (β⁻¹ * l⁻¹ * β) * (l * c) := by rw [hcl]
        _ = c⁻¹ * (β⁻¹ * l⁻¹ * β * l) * c := by group
        _ = β⁻¹ * l⁻¹ * β * l := by
          rw [hcκ.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [h4] at h2
    have hκL : β⁻¹ * l⁻¹ * β * l ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hβ.2) (L.inv_mem hlY.2)) hβ.2) hlY.2
    have hκ : β⁻¹ * l⁻¹ * β * l = 1 := by
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd (h2 ▸ hκL) (v_not_mem_L h)
    calc β * l = l * β * (β⁻¹ * l⁻¹ * β * l) := by group
      _ = l * β := by rw [hκ, mul_one]
  have hβ1 : β = 1 := eq_one_of_comm_derived h hβ hβc
  have hxe : (x : G) = bp t a * bp v b := by rw [hx, hβ1, one_mul]
  cases a <;> cases b
  · have : x = 1 := Subtype.ext (by simpa [bp] using hxe)
    rw [this]
    simp
  · have : x = vElem v := Subtype.ext (by simpa [bp, vElem] using hxe)
    rw [this, mk_vElem]
    exact one_mem _
  · have : x = h.tElem := Subtype.ext (by simpa [bp, HSOuterSetup.tElem] using hxe)
    rw [this]
    exact mem_zpowers _
  · have : x = h.tElem * vElem v := Subtype.ext (by simpa [bp, HSOuterSetup.tElem, vElem] using hxe)
    rw [this, QuotientGroup.mk_mul, mk_vElem, mul_one]
    exact mem_zpowers _

theorem good_conj_mem (h : HSOuterSetup G L t S z n v s) (hF : F v t) (y : OuterSection v)
    (hy : y * h.tBar = h.tBar * y) (w : OuterSection v)
    (hw : w ∈ sectionImage v (derivedCentralizerIn L v)) :
    y * w * y⁻¹ ∈ sectionImage v (derivedCentralizerIn L v) := by
  obtain ⟨x, rfl, hxt⟩ := exists_lift h hF y hy
  obtain ⟨l, hl, rfl⟩ := hw
  have hxv : (x : G) * v = v * (x : G) := mem_centralizer_singleton_iff.1 x.2
  refine ⟨x * l * x⁻¹, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_subgroupOf]
  have hl' : (l : G) ∈ derivedCentralizerIn L v := mem_subgroupOf.1 hl
  simpa using conj_mem_derived' h hxt hxv hl'

theorem good_H1 (h : HSOuterSetup G L t S z n v s) (hF : F v t) (y : OuterSection v)
    (hy : y * h.tBar = h.tBar * y) :
    y ∈ normalizer ((sectionImage v (derivedCentralizerIn L v) : Subgroup (OuterSection v)) :
      Set (OuterSection v)) := by
  rw [mem_set_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact good_conj_mem h hF y hy w hw
  · intro hw
    have hy' : y⁻¹ * h.tBar = h.tBar * y⁻¹ := (Commute.inv_left (show Commute y h.tBar from hy)).eq
    have := good_conj_mem h hF y⁻¹ hy' _ hw
    simpa [mul_assoc] using this

theorem good_H2 (h : HSOuterSetup G L t S z n v s) (hF : F v t) (w w' : OuterSection v)
    (hw : w * h.tBar = h.tBar * w) (hw' : w' * h.tBar = h.tBar * w') :
    ⁅w, w'⁆ ∈ sectionImage v (derivedCentralizerIn L v) := by
  obtain ⟨x, rfl, hxt⟩ := exists_lift h hF w hw
  obtain ⟨x', rfl, hxt'⟩ := exists_lift h hF w' hw'
  have hxv : (x : G) * v = v * (x : G) := mem_centralizer_singleton_iff.1 x.2
  have hxv' : (x' : G) * v = v * (x' : G) := mem_centralizer_singleton_iff.1 x'.2
  refine ⟨⁅x, x'⁆, ?_, by simp [commutatorElement_def]⟩
  rw [SetLike.mem_coe, mem_subgroupOf]
  simpa [commutatorElement_def] using commutator_mem_derived h hxt hxv hxt' hxv'

theorem good_data (h : HSOuterSetup G L t S z n v s) (hF : F v t) :
    GoodData (sectionImage v (derivedCentralizerIn L v)) h.tBar where
  sq := by
    rw [← pow_two]
    exact h.orderOf_tBar ▸ pow_orderOf_eq_one _
  ne := by
    intro h1
    have := h.orderOf_tBar
    rw [h1, orderOf_one] at this
    omega
  cent := h.tBar_mem_centralizer
  H1 := good_H1 h hF
  H2 := good_H2 h hF
  H3 := fun y hy hyt => good_H3 h hF y hy hyt

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
