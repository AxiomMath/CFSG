module

public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace WeakSigGen4

variable {Y : Type} [Group Y] {J : Type} [Group J]

theorem actOn_mk_eq_conj (L : Subgroup Y) (e : L ≃* J) (n : ↥(normalizer (L : Set Y)))
    (hn : (n : Y) ∈ L) : actOn L e n = MulAut.conj (e ⟨(n : Y), hn⟩) := by
  ext x
  apply e.symm.injective
  apply Subtype.ext
  rw [coe_symm_actOn]
  simp [MulAut.conj_apply]

theorem map_subgroupOf_actOn (L : Subgroup Y) (e : L ≃* J) :
    (L.subgroupOf (normalizer (L : Set Y))).map (actOn L e) =
      (MulAut.conj : J →* MulAut J).range := by
  ext φ
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨e ⟨(n : Y), hn⟩, (actOn_mk_eq_conj L e n hn).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨⟨(e.symm j : Y), Subgroup.le_normalizer (e.symm j).2⟩, (e.symm j).2, ?_⟩
    rw [actOn_mk_eq_conj L e _ (e.symm j).2]
    simp

theorem range_actOn_comp_inclusion (L : Subgroup Y) (e : L ≃* J) {D : Subgroup Y}
    (hDL : D ≤ normalizer (L : Set Y)) :
    ((actOn L e).comp (Subgroup.inclusion hDL)).range =
      (D.subgroupOf (normalizer (L : Set Y))).map (actOn L e) := by
  rw [← MonoidHom.map_range, Subgroup.inclusion_range]

theorem sectional_innJoin [Finite Y] (hY : SectionalTwoRankLE Y 4) (L : Subgroup Y) (e : L ≃* J)
    {D : Subgroup Y} (hDL : D ≤ normalizer (L : Set Y)) :
    SectionalTwoRankLE ↥(innJoin ((actOn L e).comp (Subgroup.inclusion hDL))) 4 := by
  set g := actOn L e with hg
  set K : Subgroup ↥(normalizer (L : Set Y)) :=
    L.subgroupOf (normalizer (L : Set Y)) ⊔ D.subgroupOf (normalizer (L : Set Y)) with hK
  have hN : SectionalTwoRankLE ↥(normalizer (L : Set Y)) 4 := SectionalTwoRankLE.subgroup _ hY
  have hKr : SectionalTwoRankLE ↥K 4 := SectionalTwoRankLE.subgroup K hN
  have heq : innJoin ((g).comp (Subgroup.inclusion hDL)) = (g.domRestrict K).range := by
    rw [MonoidHom.domRestrict_range, hK, Subgroup.map_sup, hg, map_subgroupOf_actOn,
      ← range_actOn_comp_inclusion L e hDL]
    rfl
  rw [heq]
  exact SectionalTwoRankLE.of_surjective (g.domRestrict K).rangeRestrict
    (g.domRestrict K).rangeRestrict_surjective hKr

open WeakSigGen

section Main

variable {J : Type} [Group J] {Y : Type} [Group Y] [Finite Y]

theorem weakSig2D4_aux (hq : IsQuasisimple J) (hev : 2 ∣ Nat.card J) (hnc2 : NC2 J) (h : GenLoc4 J)
    (hY : SectionalTwoRankLE Y 4)
    {L : Subgroup Y} (hLc : IsComponent L) (e : L ≃* J) {D W : Subgroup Y}
    (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hk : pRank 2 ↥D = 2 ∨ pRank 2 ↥D = 3) (hW : Odd (Nat.card ↥W))
    (hDL : D ≤ normalizer (L : Set Y)) (hDW : D ≤ normalizer (W : Set Y))
    (hC : ∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E → ∀ x ∈ L,
      x ∈ centralizer (E : Set Y) → x ∈ normalizer (W : Set Y)) :
    W ≤ centralizer (L : Set Y) := by
  classical
  have hqL : IsQuasisimple ↥L := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hL2 : 2 ∣ Nat.card ↥L := by rw [Nat.card_congr e.toEquiv]; exact hev
  set α : ↥D →* MulAut J := (actOn L e).comp (Subgroup.inclusion hDL) with hα
  have hαapply : ∀ (d : ↥D) (x : J), ((e.symm (α d x) : L) : Y) =
      (d : Y) * (e.symm x : Y) * (d : Y)⁻¹ := by
    intro d x
    exact coe_symm_actOn L e (Subgroup.inclusion hDL d) x
  have hfix : ∀ (E' : Subgroup Y), E' ≤ D → ∀ x : J,
      x ∈ fixedIn J ((E'.comap D.subtype).map α) ↔ (e.symm x : Y) ∈ centralizer (E' : Set Y) := by
    intro E' hE' x
    constructor
    · intro hx
      rw [mem_centralizer_iff]
      intro d' hd'
      have hmem : α ⟨d', hE' hd'⟩ ∈ (E'.comap D.subtype).map α :=
        Subgroup.mem_map.mpr ⟨⟨d', hE' hd'⟩, hd', rfl⟩
      have h1 := hx _ hmem
      have h2 := hαapply ⟨d', hE' hd'⟩ x
      rw [h1] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2.symm
    · intro hx φ hφ
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hφ
      apply e.symm.injective
      apply Subtype.ext
      rw [hαapply]
      have hc := mem_centralizer_iff.mp hx (d : Y) hd
      exact mul_inv_eq_iff_eq_mul.mpr hc
  have hrankA : IsRank23 ↥D := ⟨hD, hk⟩
  have hr2 : 2 ≤ pRank 2 ↥D := by
    rcases hk with h' | h'
    · omega
    · omega
  have hnormL : ∀ x : J, (∃ n : ℕ, x ^ (2 ^ n) = 1) → (∃ y : J, y * x ≠ x * y) →
      (e.symm x : Y) ∈ normalizer (W : Set Y) → W ≤ normalizer (L : Set Y) := by
    intro x hx2 hxc hxN
    refine normalizes_of_noncentral_two_elt hLc hW (e.symm x).2 hxN ?_ ?_
    · obtain ⟨n, hn⟩ := hx2
      refine ⟨n, ?_⟩
      have := congrArg (fun z : J => ((e.symm z : L) : Y)) hn
      simpa [map_pow] using this
    · obtain ⟨y, hy⟩ := hxc
      refine ⟨(e.symm y : Y), (e.symm y).2, fun hcomm => hy ?_⟩
      apply e.symm.injective
      apply Subtype.ext
      simpa using hcomm
  obtain hgen | ⟨hE1, hE2, hE3⟩ := h (↥D) α hrankA (sectional_innJoin hY L e hDL)
  ·
    have hLN : L ≤ normalizer (W : Set Y) := by
      intro l hl
      have hx : e ⟨l, hl⟩ ∈ gammaAct α := by rw [hgen]; trivial
      let T : Subgroup J := (normalizer (W : Set Y)).comap (L.subtype.comp e.symm.toMonoidHom)
      have hle : gammaAct α ≤ T := by
        refine iSup_le fun E => iSup_le fun hE => ?_
        intro x hx
        have hE'D : E.map D.subtype ≤ D := Subgroup.map_subtype_le E
        have hcomap : (E.map D.subtype).comap D.subtype = E :=
          Subgroup.comap_map_eq_self_of_injective D.subtype_injective E
        rw [← hcomap] at hx
        have hcent := (hfix _ hE'D x).mp hx
        have hrank : pRank 2 ↥D - 1 ≤ pRank 2 ↥(E.map D.subtype) := by
          rw [← pRank_comap_subtype hD hE'D, hcomap]; exact hE
        exact hC _ hE'D hrank (e.symm x : Y) (e.symm x).2 hcent
      have := hle hx
      simpa [T] using this
    have hWL : W ≤ normalizer (L : Set Y) := by
      obtain ⟨x, hx2, hxc⟩ := hnc2
      exact hnormL x hx2 hxc (hLN (e.symm x).2)
    exact centralizes_of_normalize hqL hL2 hW hLN hWL
  ·
    have hWL : W ≤ normalizer (L : Set Y) := by
      obtain ⟨E, hE, x, hx, hx2, hxc⟩ := hE3
      have hE'D : E.map D.subtype ≤ D := Subgroup.map_subtype_le E
      have hcomap : (E.map D.subtype).comap D.subtype = E :=
        Subgroup.comap_map_eq_self_of_injective D.subtype_injective E
      rw [← hcomap] at hx
      have hcent := (hfix _ hE'D x).mp hx
      have hrank : pRank 2 ↥D - 1 ≤ pRank 2 ↥(E.map D.subtype) := by
        rw [← pRank_comap_subtype hD hE'D, hcomap]; exact hE
      exact hnormL x hx2 hxc (hC _ hE'D hrank (e.symm x : Y) (e.symm x).2 hcent)
    have hW0 : W ⊓ L = ⊥ := by
      have hDW0 : D ≤ normalizer ((W ⊓ L : Subgroup Y) : Set Y) :=
        Subgroup.inf_normalizer_le_normalizer_inf (H := W) (K := L) |>.trans' (le_inf hDW hDL)
      have hodd0 : Odd (Nat.card ↥(W ⊓ L)) :=
        Odd.of_dvd_nat hW (Subgroup.card_dvd_of_le inf_le_left)
      have hgen := le_iSup_centralizer_hyperplanes hD hr2 hDW0 hodd0
      refine le_bot_iff.mp (hgen.trans (iSup_le fun E' => iSup_le fun hE'D =>
        iSup_le fun hrank => ?_))
      set X : Subgroup Y := (W ⊓ L) ⊓ centralizer (E' : Set Y) with hX
      have hXL : X ≤ L := fun y hy => hy.1.2
      have hXW : X ≤ W := fun y hy => hy.1.1
      have hrankE : pRank 2 ↥D - 1 ≤ pRank 2 ↥(E'.comap D.subtype) := by
        rw [pRank_comap_subtype hD hE'D]; exact hrank
      have hmemNJ : ∀ z : J, z ∈ ((X.subgroupOf L).map e.toMonoidHom) ↔
          ((e.symm z : L) : Y) ∈ X := by
        intro z
        constructor
        · rintro ⟨w', hw', rfl⟩
          simpa using Subgroup.mem_subgroupOf.mp hw'
        · intro hz
          exact ⟨e.symm z, hz, by simp⟩
      have hNJ : (X.subgroupOf L).map e.toMonoidHom = ⊥ := by
        apply hE1 (E'.comap D.subtype) hrankE
        · intro x hx
          rw [hfix E' hE'D]
          exact ((hmemNJ x).mp hx).2
        · have hc1 : Nat.card ↥((X.subgroupOf L).map e.toMonoidHom) = Nat.card ↥X := by
            rw [Subgroup.card_map_of_injective e.injective]
            exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv
          rw [hc1]
          exact Odd.of_dvd_nat hW (Subgroup.card_dvd_of_le hXW)
        · intro x hx
          have hcent := (hfix E' hE'D x).mp hx
          have hlN : (e.symm x : Y) ∈ normalizer (W : Set Y) :=
            hC E' hE'D hrank (e.symm x : Y) (e.symm x).2 hcent
          have hlL : (e.symm x : Y) ∈ normalizer (L : Set Y) := Subgroup.le_normalizer (e.symm x).2
          have hlC : (e.symm x : Y) ∈ normalizer ((centralizer (E' : Set Y) : Subgroup Y) : Set Y) :=
            Subgroup.le_normalizer hcent
          have hlX : (e.symm x : Y) ∈ normalizer (X : Set Y) :=
            Subgroup.inf_normalizer_le_normalizer_inf
              ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hlN, hlL⟩, hlC⟩
          rw [mem_normalizer_iff]
          intro z
          rw [hmemNJ z, hmemNJ (x * z * x⁻¹)]
          have hconj : ((e.symm (x * z * x⁻¹) : L) : Y) =
              (e.symm x : Y) * (e.symm z : Y) * (e.symm x : Y)⁻¹ := by simp
          rw [hconj]
          exact mem_normalizer_iff.mp hlX _
      intro y hy
      have hyL := hXL hy
      have hmem : e ⟨y, hyL⟩ ∈ (X.subgroupOf L).map e.toMonoidHom := ⟨⟨y, hyL⟩, hy, rfl⟩
      rw [hNJ, Subgroup.mem_bot] at hmem
      have h1 : (⟨y, hyL⟩ : ↥L) = 1 := e.injective (by rw [hmem, map_one])
      have h2 : y = 1 := congrArg Subtype.val h1
      rw [h2]
      exact Subgroup.one_mem _
    intro w hw
    have hwN : w ∈ normalizer (L : Set Y) := hWL hw
    set φ : MulAut J := actOn L e ⟨w, hwN⟩ with hφ
    have hodd : Odd (orderOf φ) := by
      have h1 : orderOf φ ∣ orderOf (⟨w, hwN⟩ : ↥(normalizer (L : Set Y))) :=
        orderOf_map_dvd (actOn L e) _
      have h2 : orderOf (⟨w, hwN⟩ : ↥(normalizer (L : Set Y))) = orderOf w :=
        Subgroup.orderOf_mk w hwN
      have h3 : orderOf w ∣ Nat.card ↥W := Subgroup.orderOf_dvd_natCard W hw
      rw [h2] at h1
      exact Odd.of_dvd_nat hW (h1.trans h3)
    let Fφ : Subgroup J :=
      { carrier := {x | φ x = x}
        mul_mem' := fun {a b} ha hb => by
          change φ (a * b) = a * b
          rw [map_mul, show φ a = a from ha, show φ b = b from hb]
        one_mem' := by
          change φ 1 = 1
          exact map_one φ
        inv_mem' := fun {a} ha => by
          change φ a⁻¹ = a⁻¹
          rw [map_inv, show φ a = a from ha] }
    have hle : gammaAct α ≤ Fφ := by
      refine iSup_le fun E => iSup_le fun hE => ?_
      intro x hx
      have hE'D : E.map D.subtype ≤ D := Subgroup.map_subtype_le E
      have hcomap : (E.map D.subtype).comap D.subtype = E :=
        Subgroup.comap_map_eq_self_of_injective D.subtype_injective E
      rw [← hcomap] at hx
      have hcent := (hfix _ hE'D x).mp hx
      have hrank : pRank 2 ↥D - 1 ≤ pRank 2 ↥(E.map D.subtype) := by
        rw [← pRank_comap_subtype hD hE'D, hcomap]; exact hE
      have hlN := hC _ hE'D hrank (e.symm x : Y) (e.symm x).2 hcent
      have hcW : (e.symm x : Y) * w * (e.symm x : Y)⁻¹ * w⁻¹ ∈ W :=
        W.mul_mem ((mem_normalizer_iff.mp hlN w).mp hw) (W.inv_mem hw)
      have hcL : (e.symm x : Y) * w * (e.symm x : Y)⁻¹ * w⁻¹ ∈ L := by
        have := L.mul_mem (e.symm x).2
          ((mem_normalizer_iff.mp hwN (e.symm x : Y)⁻¹).mp (L.inv_mem (e.symm x).2))
        simpa [mul_assoc] using this
      have hc1 : (e.symm x : Y) * w * (e.symm x : Y)⁻¹ * w⁻¹ = 1 := by
        have hmem : (e.symm x : Y) * w * (e.symm x : Y)⁻¹ * w⁻¹ ∈ W ⊓ L := ⟨hcW, hcL⟩
        rw [hW0] at hmem
        exact Subgroup.mem_bot.mp hmem
      show φ x = x
      apply e.symm.injective
      apply Subtype.ext
      rw [hφ, coe_symm_actOn]
      have hcomm : (e.symm x : Y) * w = w * (e.symm x : Y) :=
        commutatorElement_eq_one_iff_mul_comm.mp hc1
      show w * (e.symm x : Y) * w⁻¹ = (e.symm x : Y)
      exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
    have hφ1 : φ = 1 := hE2 φ hodd (fun x hx => hle hx)
    rw [mem_centralizer_iff]
    intro l hl
    have key := coe_symm_actOn L e ⟨w, hwN⟩ (e ⟨l, hl⟩)
    have h1 : actOn L e ⟨w, hwN⟩ (e ⟨l, hl⟩) = e ⟨l, hl⟩ := by
      have := congrArg (fun ψ : MulAut J => ψ (e ⟨l, hl⟩)) hφ1
      simpa [hφ] using this
    rw [h1, MulEquiv.symm_apply_apply] at key
    have key' : l = w * l * w⁻¹ := key
    exact (mul_inv_eq_iff_eq_mul.mp key'.symm).symm

end Main

end WeakSigGen4

@[expose] def WeakSig2D4 (J : Type) [Group J] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SectionalTwoRankLE Y 4 → ∀ (L : Subgroup Y), IsComponent L →
    Nonempty (↥L ≃* J) → ∀ D W : Subgroup Y,
    CFSG.IsElementaryAbelian 2 ↥D → (pRank 2 ↥D = 2 ∨ pRank 2 ↥D = 3) → Odd (Nat.card ↥W) →
      D ≤ normalizer (L : Set Y) → D ≤ normalizer (W : Set Y) →
      (∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E → ∀ x ∈ L, x ∈ centralizer (E : Set Y) →
        x ∈ normalizer (W : Set Y)) →
      W ≤ centralizer (L : Set Y)

theorem weakSig2D4_of_genLoc4 {J : Type} [Group J] (hq : IsQuasisimple J) (hev : 2 ∣ Nat.card J)
    (hnc2 : NC2 J) (h : GenLoc4 J) : WeakSig2D4 J := by
  intro Y _ _ hY L hLc hL D W hD hk hW hDL hDW hC
  obtain ⟨e⟩ := hL
  exact WeakSigGen4.weakSig2D4_aux hq hev hnc2 h hY hLc e hD hk hW hDL hDW hC

theorem weakSig2NormG4_of_genLoc4 {J : Type} [Group J] (hq : IsQuasisimple J) (hev : 2 ∣ Nat.card J)
    (hnc2 : NC2 J) (h : GenLoc4 J) : WeakSig2NormG4 J := by
  intro Y _ _ _ hY L hLc hL D W hD hk hW hDW hC hDL
  obtain ⟨e⟩ := hL
  exact WeakSigGen4.weakSig2D4_aux hq hev hnc2 h hY hLc e hD hk hW hDL hDW
    (fun E hE hr x _ hx => hC E hE hr hx)

end CFSG.GH74.Generic.BProg.B2
