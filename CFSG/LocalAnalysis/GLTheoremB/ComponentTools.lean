module

public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Subnormal

variable {X Y : Type*} [Group X] [Group Y]

theorem isSubnormal_map' (f : X →* Y) {A B : Subgroup X} (h : IsSubnormal A B) :
    IsSubnormal (A.map f) (B.map f) :=
  h.map f

theorem isSubnormal_comap' (f : X →* Y) {A B : Subgroup Y} (h : IsSubnormal A B) :
    IsSubnormal (A.comap f) (B.comap f) :=
  h.comap f

end Subnormal

section PPrimeCore

variable {G : Type*} [Group G] [Finite G]

theorem glaPPrimeCoreOf_le_of_normal {p : ℕ} (hp : p.Prime) {H M : Subgroup G} (hHM : H ≤ M)
    (hn : (H.subgroupOf M).Normal) : GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p M := by
  have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
  set O := GLAPPrimeCoreOf p H with hO
  have hOM : M ≤ Subgroup.normalizer (O : Set G) := by
    intro m hm
    have h1 := hMH hm
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [hO, ← glaPPrimeCoreOf_gLBConj, h1]
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOn : (O.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hOH.trans hHM)).2 hOM
  have hcop : Nat.Coprime p (Nat.card (O.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOH.trans hHM)).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp H)
  have hle : O.subgroupOf M ≤ GLAPPrimeCore p ↥M := le_sSup ⟨hOn, hcop⟩
  calc O = (O.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (hOH.trans hHM)).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

theorem glaPPrimeCoreOf_le_of_isSubnormal {p : ℕ} (hp : p.Prime) {L C : Subgroup G}
    (h : IsSubnormal L C) : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (glaPPrimeCoreOf_le_of_normal hp hHM hn).trans ih

end PPrimeCore

section Component

variable {G : Type*} [Group G]

theorem glaPComponent_top {p : ℕ} {C L : Subgroup G} (h : GLAPComponent p C L) :
    GLAPComponent p (⊤ : Subgroup ↥C) (L.subgroupOf C) := by
  obtain ⟨hLC, hsn, hcomp, hmin⟩ := h
  let t : ↥(⊤ : Subgroup ↥C) ≃* ↥C := Subgroup.topEquiv
  let Φ : (↥(⊤ : Subgroup ↥C) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup ↥C)) ≃*
      (↥C ⧸ GLAPPrimeCore p ↥C) := QuotientGroup.congr _ _ t (glaPPrimeCore_map_iso p t)
  have hbar : ∀ J : Subgroup ↥C,
      ((J.subgroupOf (⊤ : Subgroup ↥C)).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup ↥C)))).map Φ.toMonoidHom =
      J.map (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) := by
    intro J
    ext z
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w.1, hw, (QuotientGroup.congr_mk _ _ t (glaPPrimeCore_map_iso p t) w).symm⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨_, ⟨(⟨j, Subgroup.mem_top j⟩ : ↥(⊤ : Subgroup ↥C)), hj, rfl⟩, ?_⟩
      exact QuotientGroup.congr_mk _ _ t (glaPPrimeCore_map_iso p t) ⟨j, Subgroup.mem_top j⟩
  refine ⟨le_top, ?_, ?_, ?_⟩
  · have := isSubnormal_comap' C.subtype hsn
    rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at this
  · have hL' := (CFSG.ComponentClassification.LocalComponents.equiv_iff Φ.symm _).2 hcomp
    have h2 : ((L.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))).map
        Φ.symm.toMonoidHom = ((L.subgroupOf C).subgroupOf (⊤ : Subgroup ↥C)).map
          (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup ↥C))) := by
      have h4 := congrArg (Subgroup.map Φ.symm.toMonoidHom) (hbar (L.subgroupOf C))
      rw [Subgroup.map_map] at h4
      have h3 : (Φ.symm.toMonoidHom.comp Φ.toMonoidHom) = MonoidHom.id _ := by
        ext x; simp
      rw [h3, Subgroup.map_id] at h4
      exact h4.symm
    rw [← h2]
    exact hL'
  · intro J hJ hJsn heq
    have heq' : J.map (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) =
        (L.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) := by
      rw [← hbar J, ← hbar (L.subgroupOf C), heq]
    have hJg : (J.map C.subtype).subgroupOf C = J :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
    have hJgL : J.map C.subtype < L := by
      refine lt_of_le_of_ne ?_ (fun hEq => hJ.ne ?_)
      · rintro _ ⟨j, hj, rfl⟩
        exact (Subgroup.mem_subgroupOf).1 (hJ.le hj)
      · rw [← hJg, hEq]
    have hJgsn : IsSubnormal (J.map C.subtype) C := by
      have := isSubnormal_map' C.subtype hJsn
      rwa [Subgroup.map_top, Subgroup.range_subtype] at this
    refine hmin _ hJgL hJgsn ?_
    show ((J.map C.subtype).subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) =
      (L.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
    rw [hJg]
    exact heq'

theorem exists_glaPComponent_barX_eq [Finite G] {p : ℕ} (C : Subgroup G)
    {K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hK : IsComponentOf K ⊤) :
    ∃ L : Subgroup G, GLAPComponent p C L ∧ barX p C L = K := by
  classical
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  have hJ₀ : (K.comap π).map C.subtype ∈
      {J : Subgroup G | J ≤ C ∧ IsSubnormal J C ∧ barX p C J = K} := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · have h1 := isSubnormal_comap' π hK.2.1
      rw [Subgroup.comap_top] at h1
      have h2 := isSubnormal_map' C.subtype h1
      rwa [Subgroup.map_top, Subgroup.range_subtype] at h2
    · have hJg : ((K.comap π).map C.subtype).subgroupOf C = K.comap π :=
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
      show (((K.comap π).map C.subtype).subgroupOf C).map π = K
      rw [hJg]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K
  obtain ⟨L, ⟨hLC, hsn, hbar⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min _ ⟨_, hJ₀⟩
  refine ⟨L, ⟨hLC, hsn, ?_, ?_⟩, hbar⟩
  · change IsComponentOf (barX p C L) ⊤
    rw [hbar]
    exact hK
  · intro J hJ hJsn heq
    exact hmin J ⟨hJ.le.trans hLC, hJsn, heq.trans hbar⟩ hJ

theorem barX_le_centralizer {p : ℕ} {C S T : Subgroup G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s ∈ C → t ∈ C → s * t * s⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p C) :
    barX p C S ≤ Subgroup.centralizer (barX p C T : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  have hs' : (s : G) ∈ S := (Subgroup.mem_subgroupOf).1 hs
  have ht' : (t : G) ∈ T := (Subgroup.mem_subgroupOf).1 ht
  obtain ⟨z, hz, hzc⟩ := h _ hs' _ ht' s.2 t.2
  have hzeq : z = s * t * s⁻¹ * t⁻¹ := Subtype.ext (by simpa using hzc)
  rw [hzeq] at hz
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) (s * t * s⁻¹ * t⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (s * t * s⁻¹ * t⁻¹)).2 hz
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  set a := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) s
  set b := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) t
  calc b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
    _ = a * b := by
      have : b * a * b⁻¹ * a⁻¹ = 1 := by
        have h2 : (a * b * a⁻¹ * b⁻¹)⁻¹ = 1 := by rw [h1, inv_one]
        simpa [mul_assoc] using h2
      rw [this, one_mul]

theorem barX_le_normalizer {p : ℕ} {C S T : Subgroup G} (h : T ≤ Subgroup.normalizer (S : Set G)) :
    barX p C T ≤ Subgroup.normalizer (barX p C S : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  have key : ∀ u ∈ T.subgroupOf C, ∀ s ∈ S.subgroupOf C, u * s * u⁻¹ ∈ S.subgroupOf C := by
    intro u hu s hs
    have hu' : (u : G) ∈ T := (Subgroup.mem_subgroupOf).1 hu
    have := (Subgroup.mem_normalizer_iff.1 (h hu') (s : G)).1 ((Subgroup.mem_subgroupOf).1 hs)
    exact (Subgroup.mem_subgroupOf).2 (by simpa using this)
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
  constructor
  · rintro ⟨s, hs, hsw⟩
    refine ⟨u * s * u⁻¹, key u hu s hs, ?_⟩
    simp only [QuotientGroup.mk'_apply] at hsw ⊢
    rw [← hsw]
    simp
  · rintro ⟨s, hs, hsw⟩
    refine ⟨u⁻¹ * s * u, ?_, ?_⟩
    · have := key u⁻¹ ((T.subgroupOf C).inv_mem hu) s hs
      simpa using this
    · have hsw' : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) s =
          (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) u * (w : ↥C ⧸ GLAPPrimeCore p ↥C) *
            ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)) u)⁻¹ := hsw
      rw [map_mul, map_mul, map_inv, hsw']
      group

end Component

section KGroup

theorem isKGroup_of_isKProper {G : Type*} [Group G] (hG : CFSG.Open.IsKProper G) {C : Subgroup G}
    (hC : C ≠ ⊤) : CFSG.Open.IsKGroup ↥C :=
  hG.isKGroup C hC

theorem glaTwoLocalRank_subgroup_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    (C : Subgroup G) : GLATwoLocalRank p ↥C ≤ GLATwoLocalRank p G := by
  have hbdd : BddAbove {k | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧
      CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hp H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
    have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
    change CFSG.Open.pRank p H ≤ Nat.card G
    omega
  refine csSup_le' fun k hk => ?_
  obtain ⟨H, ⟨P₀, hP₀, hP₀2, rfl⟩, rfl⟩ := hk
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (P₀.map C.subtype : Set G)) :=
    ⟨P₀.map C.subtype, fun h => hP₀ ((Subgroup.map_eq_bot_iff_of_injective P₀
      C.subtype_injective).1 h), hP₀2.map _, rfl⟩
  have hle : (Subgroup.normalizer (P₀ : Set ↥C)).map C.subtype ≤
      Subgroup.normalizer (P₀.map C.subtype : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := Subgroup.mem_normalizer_iff.1 (SetLike.mem_coe.1 hc)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c * x * c⁻¹, (hc' x).1 hx, by simp⟩
    · rintro ⟨x, hx, hxe⟩
      have hxx : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
      refine ⟨c⁻¹ * x * c, (hc' _).2 (by rw [hxx]; exact hx), ?_⟩
      have := congrArg (fun z : G => (c : G)⁻¹ * z * (c : G)) hxe
      simpa [mul_assoc] using this
  calc CFSG.Open.pRank p (Subgroup.normalizer (P₀ : Set ↥C))
      ≤ CFSG.Open.pRank p ((Subgroup.normalizer (P₀ : Set ↥C)).map C.subtype) :=
        CFSG.SectionRank.pRank_le_map hp C.subtype C.subtype_injective _
    _ ≤ CFSG.Open.pRank p (Subgroup.normalizer (P₀.map C.subtype : Set G)) :=
        CFSG.SectionRank.pRank_mono hp hle
    _ ≤ GLATwoLocalRank p G := le_csSup hbdd ⟨_, hloc, rfl⟩

end KGroup

end CFSG.LocalAnalysis.GLTheoremB
