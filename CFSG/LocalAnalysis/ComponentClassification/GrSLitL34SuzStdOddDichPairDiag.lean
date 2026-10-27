module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSetup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem suzOdd_D_le_X {X : Subgroup G} {t : G} (ht : t ∈ X)
    {P : Subgroup G} (hPu : P ≤ X)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPXtG : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map X.subtype =
      P.map (MulAut.conj t).toMonoidHom) :
    (HarrisLit.swapDiag P t hc).range ≤ X := by
  rintro _ ⟨k, rfl⟩
  have hkX : (k : G) ∈ X := hPu k.2
  have hk'X : MulAut.conj t (k : G) ∈ X := by
    have hk' : MulAut.conj t (k : G) ∈ P.map (MulAut.conj t).toMonoidHom := ⟨k, k.2, rfl⟩
    rw [← hPXtG] at hk'
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hk'
    rw [← hxval]
    exact x.2
  exact X.mul_mem hkX hk'X

omit [Finite G] in
private theorem suzOdd_piPXt {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {L : Subgroup (↥X ⧸ N)} {t : G} (ht : t ∈ X) {P : Subgroup G}
    (hPL : (P.subgroupOf X).map (QuotientGroup.mk' N) = L)
    (hπ_comp : (QuotientGroup.mk' N).comp (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom.comp (QuotientGroup.mk' N)) :
    ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map (QuotientGroup.mk' N) =
      L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom := by
  rw [Subgroup.map_map, hπ_comp, ← Subgroup.map_map]
  exact congrArg (fun s : Subgroup (↥X ⧸ N) =>
    s.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom) hPL

omit [Finite G] in
private theorem suzOdd_conjP_ne {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {L : Subgroup (↥X ⧸ N)} {t : G} (ht : t ∈ X)
    (hLt : L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom ≠ L)
    {P : Subgroup G}
    (hPL : (P.subgroupOf X).map (QuotientGroup.mk' N) = L)
    (hπPXt : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map
        (QuotientGroup.mk' N) =
      L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom) :
    (P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom ≠ P.subgroupOf X := by
  intro h
  apply hLt
  rw [← hπPXt, h, hPL]

private theorem suzOdd_hcX {X : Subgroup G} {t : G} (ht : t ∈ X)
    {P : Subgroup G}
    (hPXcomp : IsComponent (P.subgroupOf X))
    (hnePt : (P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom ≠ P.subgroupOf X) :
    P.subgroupOf X ≤ centralizer ((((P.subgroupOf X).map
      (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom) : Subgroup ↥X) : Set ↥X) := by
  have hPXtcomp : IsComponent ((P.subgroupOf X).map
      (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (⟨t, ht⟩ : ↥X)) hPXcomp
  rcases CFSG.LocalCores.distinct_components_commute hPXcomp hPXtcomp with h | h
  · exact absurd h.symm hnePt
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

omit [Finite G] in
private theorem suzOdd_hc {X : Subgroup G} {t : G} (ht : t ∈ X)
    {P : Subgroup G} (hPu : P ≤ X)
    (hPXtG : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map X.subtype =
      P.map (MulAut.conj t).toMonoidHom)
    (hcX : P.subgroupOf X ≤ centralizer ((((P.subgroupOf X).map
      (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom) : Subgroup ↥X) : Set ↥X)) :
    P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [← hPXtG]
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨qX, hqX, rfl⟩ := Subgroup.mem_map.mp hq
  have hpX : (⟨p, hPu hp⟩ : ↥X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hp
  have hcomm := Subgroup.mem_centralizer_iff.mp (hcX hpX) qX hqX
  exact congrArg Subtype.val hcomm

omit [Finite G] in
private theorem suzOdd_hc_ne {X : Subgroup G} {t : G} (ht : t ∈ X)
    {P : Subgroup G} (hPu : P ≤ X)
    (hnePt : (P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom ≠ P.subgroupOf X)
    (hPXtG : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map X.subtype =
      P.map (MulAut.conj t).toMonoidHom) :
    P.map (MulAut.conj t).toMonoidHom ≠ P := by
  intro h
  apply hnePt
  have hm : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map X.subtype =
      (P.subgroupOf X).map X.subtype := by
    rw [hPXtG, h, Subgroup.map_subgroupOf_eq_of_le hPu]
  exact Subgroup.map_injective X.subtype_injective hm

private theorem suzOdd_N_cent_PX {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {L : Subgroup (↥X ⧸ N)} {t : G} (ht : t ∈ X)
    (hLt : L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom ≠ L)
    {P : Subgroup G} (hPXcomp : IsComponent (P.subgroupOf X))
    (hPL : (P.subgroupOf X).map (QuotientGroup.mk' N) = L)
    (hNnormal : N.Normal) :
    ∀ a ∈ P.subgroupOf X, ∀ n ∈ N, a * n = n * a := by
  have hNPX : P.subgroupOf X ≤ N ∨ ⁅P.subgroupOf X, N⁆ = ⊥ :=
    CFSG.LocalCores.component_normal_subgroup hPXcomp hNnormal
  have hcomm : ⁅P.subgroupOf X, N⁆ = ⊥ := by
    rcases hNPX with h | h
    · exfalso
      have hmap : (P.subgroupOf X).map (QuotientGroup.mk' N) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        rwa [QuotientGroup.ker_mk']
      have hLbot : L = ⊥ := by rw [← hPL, hmap]
      apply hLt
      rw [hLbot]
      simp
    · exact h
  intro a ha n hn
  have hcent : a ∈ Subgroup.centralizer (N : Set ↥X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha
  exact (Subgroup.mem_centralizer_iff.mp hcent n hn).symm

private theorem suzOdd_N_cent_PXt {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {L : Subgroup (↥X ⧸ N)} {t : G} (ht : t ∈ X)
    (hLt : L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom ≠ L)
    {P : Subgroup G} (hPXcomp : IsComponent (P.subgroupOf X))
    (hπPXt : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map
        (QuotientGroup.mk' N) =
      L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom)
    (hNnormal : N.Normal) :
    ∀ b ∈ ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom),
      ∀ n ∈ N, b * n = n * b := by
  have hPXtcomp : IsComponent ((P.subgroupOf X).map
      (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (⟨t, ht⟩ : ↥X)) hPXcomp
  have hNPXt : ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom) ≤ N ∨
      ⁅((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom), N⁆ = ⊥ :=
    CFSG.LocalCores.component_normal_subgroup hPXtcomp hNnormal
  have hcomm : ⁅((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom), N⁆ = ⊥ := by
    rcases hNPXt with h | h
    · exfalso
      have hmap : (((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map
          (QuotientGroup.mk' N)) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        rwa [QuotientGroup.ker_mk']
      rw [hπPXt] at hmap
      have hLbot : L = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective L
          (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).injective).mp hmap
      apply hLt
      rw [hLbot]
      simp
    · exact h
  intro b hb n hn
  have hcent : b ∈ Subgroup.centralizer (N : Set ↥X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hb
  exact (Subgroup.mem_centralizer_iff.mp hcent n hn).symm

omit [Finite G] in
private theorem suzOdd_N_cent_D {X : Subgroup G} {N : Subgroup ↥X}
    {t : G} (ht : t ∈ X) {P : Subgroup G} (hPu : P ≤ X)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hNcentPX : ∀ a ∈ P.subgroupOf X, ∀ n ∈ N, a * n = n * a)
    (hNcentPXt : ∀ b ∈ ((P.subgroupOf X).map
        (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom), ∀ n ∈ N, b * n = n * b) :
    ∀ n ∈ N, ∀ d ∈ ((HarrisLit.swapDiag P t hc).range).subgroupOf X, n * d = d * n := by
  intro n hn d hd
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hd)
  let aX : ↥X := ⟨(p : G), hPu p.2⟩
  have haX : aX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr p.2
  have hbX : MulAut.conj (⟨t, ht⟩ : ↥X) aX ∈ ((P.subgroupOf X).map
      (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom) := Subgroup.mem_map_of_mem _ haX
  have hd_eq : d = aX * MulAut.conj (⟨t, ht⟩ : ↥X) aX := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← hp, HarrisLit.swapDiag_apply, MulAut.conj_apply]
    rfl
  have hna : n * aX = aX * n := (hNcentPX aX haX n hn).symm
  have hnb : n * MulAut.conj (⟨t, ht⟩ : ↥X) aX =
      MulAut.conj (⟨t, ht⟩ : ↥X) aX * n := (hNcentPXt _ hbX n hn).symm
  calc n * d = n * (aX * MulAut.conj (⟨t, ht⟩ : ↥X) aX) := by rw [hd_eq]
    _ = (n * aX) * MulAut.conj (⟨t, ht⟩ : ↥X) aX := by group
    _ = (aX * n) * MulAut.conj (⟨t, ht⟩ : ↥X) aX := by rw [hna]
    _ = aX * (n * MulAut.conj (⟨t, ht⟩ : ↥X) aX) := by group
    _ = aX * (MulAut.conj (⟨t, ht⟩ : ↥X) aX * n) := by rw [hnb]
    _ = (aX * MulAut.conj (⟨t, ht⟩ : ↥X) aX) * n := by group
    _ = d * n := by rw [hd_eq]

omit [Finite G] in
private theorem suzOdd_N_norm_D {X : Subgroup G} {N : Subgroup ↥X}
    {t : G} {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hNcentD : ∀ n ∈ N, ∀ d ∈ ((HarrisLit.swapDiag P t hc).range).subgroupOf X, n * d = d * n) :
    N ≤ Subgroup.normalizer ((((HarrisLit.swapDiag P t hc).range).subgroupOf X) : Set ↥X) := by
  have hNcentDX : N ≤ Subgroup.centralizer ((((HarrisLit.swapDiag P t hc).range).subgroupOf X) :
      Set ↥X) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hNcentD n hn d hd).symm
  exact hNcentDX.trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
private theorem suzOdd_pi_conj {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {t : G} (ht : t ∈ X)
    (hπ_comp : (QuotientGroup.mk' N).comp (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom.comp (QuotientGroup.mk' N))
    (a : ↥X) :
    QuotientGroup.mk' N (MulAut.conj (⟨t, ht⟩ : ↥X) a) =
      QuotientGroup.mk' N ⟨t, ht⟩ * QuotientGroup.mk' N a * (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹ := by
  have h := DFunLike.congr_fun hπ_comp a
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [h, MulAut.conj_apply]

omit [Finite G] in
private theorem suzOdd_pi_le {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {K : Subgroup G} {t : G} (ht : t ∈ X)
    {L : Subgroup (↥X ⧸ N)} {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPL : (P.subgroupOf X).map (QuotientGroup.mk' N) = L)
    (hdiag : ((K.subgroupOf X).map (QuotientGroup.mk' N) : Set (↥X ⧸ N)) =
      {g | ∃ k ∈ L, k * (QuotientGroup.mk' N ⟨t, ht⟩ * k *
        (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) = g})
    (hπconj : ∀ a : ↥X, QuotientGroup.mk' N (MulAut.conj (⟨t, ht⟩ : ↥X) a) =
      QuotientGroup.mk' N ⟨t, ht⟩ * QuotientGroup.mk' N a * (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) :
    (K.subgroupOf X).map (QuotientGroup.mk' N) ≤
      (((HarrisLit.swapDiag P t hc).range).subgroupOf X).map (QuotientGroup.mk' N) := by
  intro g hg
  have hg' : g ∈ ((K.subgroupOf X).map (QuotientGroup.mk' N) : Set (↥X ⧸ N)) := hg
  rw [hdiag] at hg'
  obtain ⟨k, hkL, hkg⟩ := hg'
  have hk' : k ∈ (P.subgroupOf X).map (QuotientGroup.mk' N) := hPL.symm ▸ hkL
  obtain ⟨a, haPX, ha⟩ := Subgroup.mem_map.mp hk'
  refine Subgroup.mem_map.mpr ⟨a * MulAut.conj (⟨t, ht⟩ : ↥X) a, ?_, ?_⟩
  · apply Subgroup.mem_subgroupOf.mpr
    refine ⟨⟨(a : G), Subgroup.mem_subgroupOf.mp haPX⟩, ?_⟩
    rw [HarrisLit.swapDiag_apply, MulAut.conj_apply]
    rfl
  · calc QuotientGroup.mk' N (a * MulAut.conj (⟨t, ht⟩ : ↥X) a) =
        QuotientGroup.mk' N a * QuotientGroup.mk' N (MulAut.conj (⟨t, ht⟩ : ↥X) a) :=
          map_mul (QuotientGroup.mk' N) a _
      _ = QuotientGroup.mk' N a * (QuotientGroup.mk' N ⟨t, ht⟩ * QuotientGroup.mk' N a *
          (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) := by rw [hπconj]
      _ = k * (QuotientGroup.mk' N ⟨t, ht⟩ * k * (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) := by rw [ha]
      _ = g := hkg

omit [Finite G] in
private theorem suzOdd_pi_ge {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {K : Subgroup G} {t : G} (ht : t ∈ X)
    {L : Subgroup (↥X ⧸ N)} {P : Subgroup G} (hPu : P ≤ X)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPL : (P.subgroupOf X).map (QuotientGroup.mk' N) = L)
    (hdiag : ((K.subgroupOf X).map (QuotientGroup.mk' N) : Set (↥X ⧸ N)) =
      {g | ∃ k ∈ L, k * (QuotientGroup.mk' N ⟨t, ht⟩ * k *
        (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) = g})
    (hπconj : ∀ a : ↥X, QuotientGroup.mk' N (MulAut.conj (⟨t, ht⟩ : ↥X) a) =
      QuotientGroup.mk' N ⟨t, ht⟩ * QuotientGroup.mk' N a * (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) :
    ((((HarrisLit.swapDiag P t hc).range).subgroupOf X).map (QuotientGroup.mk' N)) ≤
      (K.subgroupOf X).map (QuotientGroup.mk' N) := by
  intro g hg
  obtain ⟨d, hdDX, hdπ⟩ := Subgroup.mem_map.mp hg
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hdDX)
  let aX : ↥X := ⟨(p : G), hPu p.2⟩
  have haX : aX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr p.2
  have hd_eq : d = aX * MulAut.conj (⟨t, ht⟩ : ↥X) aX := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← hp, HarrisLit.swapDiag_apply, MulAut.conj_apply]
    rfl
  have hg' : QuotientGroup.mk' N aX * (QuotientGroup.mk' N ⟨t, ht⟩ * QuotientGroup.mk' N aX *
      (QuotientGroup.mk' N ⟨t, ht⟩)⁻¹) = g := by
    rw [← hdπ, hd_eq, map_mul, hπconj]
  have hkL : QuotientGroup.mk' N aX ∈ L := by
    rw [← hPL]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) haX
  have hmem : g ∈ ((K.subgroupOf X).map (QuotientGroup.mk' N) : Set (↥X ⧸ N)) := by
    rw [hdiag]
    exact ⟨QuotientGroup.mk' N aX, hkL, hg'⟩
  exact hmem

omit [Finite G] in
private theorem suzOdd_KD_sup {X : Subgroup G} {N : Subgroup ↥X} [N.Normal] {K D : Subgroup G}
    (hπ : (K.subgroupOf X).map (QuotientGroup.mk' N) =
      (D.subgroupOf X).map (QuotientGroup.mk' N)) :
    K.subgroupOf X ≤ D.subgroupOf X ⊔ N := by
  intro x hx
  have hπx : QuotientGroup.mk' N x ∈ (K.subgroupOf X).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hπ] at hπx
  obtain ⟨y, hyD, hyπ⟩ := Subgroup.mem_map.mp hπx
  have hmemN : y⁻¹ * x ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' N (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hyπ, inv_mul_cancel]
  have hprod : y * (y⁻¹ * x) = x := by group
  rw [← hprod]
  exact Subgroup.mul_mem_sup hyD hmemN

omit [Finite G] in
private theorem suzOdd_DK_sup {X : Subgroup G} {N : Subgroup ↥X} [N.Normal] {K D : Subgroup G}
    (hπ : (K.subgroupOf X).map (QuotientGroup.mk' N) =
      (D.subgroupOf X).map (QuotientGroup.mk' N)) :
    D.subgroupOf X ≤ K.subgroupOf X ⊔ N := by
  intro x hx
  have hπx : QuotientGroup.mk' N x ∈ (D.subgroupOf X).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hx
  rw [← hπ] at hπx
  obtain ⟨y, hyK, hyπ⟩ := Subgroup.mem_map.mp hπx
  have hmemN : y⁻¹ * x ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' N (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hyπ, inv_mul_cancel]
  have hprod : y * (y⁻¹ * x) = x := by group
  rw [← hprod]
  exact Subgroup.mul_mem_sup hyK hmemN

omit [Finite G] in
private theorem suzOdd_D_perf {X : Subgroup G} {t : G} {P : Subgroup G} (hPu : P ≤ X)
    (hPXq : IsQuasisimple ↥(P.subgroupOf X))
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hDX : (HarrisLit.swapDiag P t hc).range ≤ X) :
    Group.IsPerfect ↥(((HarrisLit.swapDiag P t hc).range).subgroupOf X) := by
  have hPq : IsQuasisimple ↥P :=
    (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hPu)).mp hPXq
  have hDq : IsQuasisimple ↥((HarrisLit.swapDiag P t hc).range) :=
    CFSG.OddStandard.HigherRank.F3.isQuasisimple_range_swapDiag hc hPq
  have hDXq : IsQuasisimple ↥(((HarrisLit.swapDiag P t hc).range).subgroupOf X) :=
    (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hDX)).mpr hDq
  exact hDXq.1

private theorem suzOdd_final {X : Subgroup G} {N : Subgroup ↥X} [N.Normal] {K D : Subgroup G}
    (hKXleX : K ≤ X) (hDleX : D ≤ X)
    (hKXperf : Group.IsPerfect ↥(K.subgroupOf X))
    (hDXperf : Group.IsPerfect ↥(D.subgroupOf X))
    (hNodd : Odd (Nat.card N))
    (hNnormD : N ≤ Subgroup.normalizer ((D.subgroupOf X) : Set ↥X))
    (hKDsup : K.subgroupOf X ≤ D.subgroupOf X ⊔ N)
    (hDKsup : D.subgroupOf X ≤ K.subgroupOf X ⊔ N)
    (hNcentD : ∀ n ∈ N, ∀ d ∈ D.subgroupOf X, n * d = d * n) :
    K = D := by
  have hKD : K.subgroupOf X ≤ D.subgroupOf X :=
    CFSG.ComponentClassification.UnbalancedLayer.le_of_perfect_le_sup_of_odd
      hNodd hNnormD hKXperf hKDsup
  have hNnormK : N ≤ Subgroup.normalizer ((K.subgroupOf X) : Set ↥X) := by
    have hNcentK : N ≤ Subgroup.centralizer ((K.subgroupOf X) : Set ↥X) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hNcentD n hn k (hKD hk)).symm
    exact hNcentK.trans (Subgroup.centralizer_le_normalizer _)
  have hDK : D.subgroupOf X ≤ K.subgroupOf X :=
    CFSG.ComponentClassification.UnbalancedLayer.le_of_perfect_le_sup_of_odd
      hNodd hNnormK hDXperf hDKsup
  have hKXDX : K.subgroupOf X = D.subgroupOf X := le_antisymm hKD hDK
  calc K = (K.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hKXleX).symm
    _ = (D.subgroupOf X).map X.subtype := by rw [hKXDX]
    _ = D := Subgroup.map_subgroupOf_eq_of_le hDleX

omit [Finite G] in
private theorem suzOdd_PXtG {X : Subgroup G} {t : G} (ht : t ∈ X) {P : Subgroup G} (hPu : P ≤ X) :
    ((P.subgroupOf X).map (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom).map X.subtype =
      P.map (MulAut.conj t).toMonoidHom := by
  have hconj_comp : X.subtype.comp (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, hconj_comp, ← Subgroup.map_map]
  rw [Subgroup.map_subgroupOf_eq_of_le hPu]

omit [Finite G] in
private theorem suzOdd_pi_comp {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {t : G} (ht : t ∈ X) :
    (QuotientGroup.mk' N).comp (MulAut.conj (⟨t, ht⟩ : ↥X)).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' N ⟨t, ht⟩)).toMonoidHom.comp (QuotientGroup.mk' N) := by
  ext x
  simp [MulAut.conj_apply]

theorem l34SuzSwappedAt_of_l34SuzOdd (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (ht : t ∈ centralizer ({u} : Set G))
    {L : Subgroup (↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))}
    (hLt : L.map (MulAut.conj
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))) ⟨t, ht⟩)).toMonoidHom ≠ L)
    (hdiag : (((K.subgroupOf (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) :
        Subgroup (↥(centralizer ({u} : Set G)) ⧸
          pPrimeCore 2 ↥(centralizer ({u} : Set G)))) :
        Set (↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))) =
      {g | ∃ k ∈ L, k * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))) ⟨t, ht⟩ *
        k * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))) ⟨t, ht⟩)⁻¹) = g})
    {P : Subgroup G} (hPu : P ≤ centralizer ({u} : Set G))
    (hP : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hPL : (P.subgroupOf (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) = L) :
    L34SuzSwappedAt t K u := by
  classical
  let X : Subgroup G := centralizer ({u} : Set G)
  let N : Subgroup ↥X := pPrimeCore 2 ↥X
  have hNnormal : N.Normal := pPrimeCore_normal
  let π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N
  let tX : ↥X := ⟨t, ht⟩
  have htS : t ∈ centralizer ({u} : Set G) := mem_centralizer_of_l34SuzOdd hS hD hu
  have hKXleX : K ≤ X := le_centralizer_of_l34SuzOddData hD hu
  let PX : Subgroup ↥X := P.subgroupOf X
  let KX : Subgroup ↥X := K.subgroupOf X
  let PXt : Subgroup ↥X := PX.map (MulAut.conj tX).toMonoidHom
  have hPXcomp : IsComponent PX := hP
  have hKXperf : Group.IsPerfect ↥KX := (isQuasisimple_subgroupOf_of_l34SuzOdd hD hu).1
  have hPXtG : (PX.map (MulAut.conj tX).toMonoidHom).map X.subtype =
      P.map (MulAut.conj t).toMonoidHom :=
    suzOdd_PXtG (X := X) (t := t) ht hPu
  have hπ_comp : π.comp (MulAut.conj tX).toMonoidHom =
      (MulAut.conj (π tX)).toMonoidHom.comp π :=
    suzOdd_pi_comp (X := X) (N := N) (t := t) ht
  have hπPXt : PXt.map π = L.map (MulAut.conj (π tX)).toMonoidHom :=
    suzOdd_piPXt htS hPL hπ_comp
  have hnePt : PXt ≠ PX := suzOdd_conjP_ne ht hLt hPL hπPXt
  have hcX : PX ≤ centralizer ((PXt : Subgroup ↥X) : Set ↥X) :=
    suzOdd_hcX ht hPXcomp hnePt
  have hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    suzOdd_hc ht hPu hPXtG hcX
  have hne : P.map (MulAut.conj t).toMonoidHom ≠ P :=
    suzOdd_hc_ne ht hPu hnePt hPXtG
  let D : Subgroup G := (HarrisLit.swapDiag P t hc).range
  have hDleX : D ≤ X := suzOdd_D_le_X ht hPu hc hPXtG
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hNcentPX : ∀ a ∈ PX, ∀ n ∈ N, a * n = n * a :=
    suzOdd_N_cent_PX ht hLt hPXcomp hPL hNnormal
  have hNcentPXt : ∀ b ∈ PXt, ∀ n ∈ N, b * n = n * b :=
    suzOdd_N_cent_PXt ht hLt hPXcomp hπPXt hNnormal
  let DX : Subgroup ↥X := D.subgroupOf X
  have hNcentD : ∀ n ∈ N, ∀ d ∈ DX, n * d = d * n :=
    suzOdd_N_cent_D ht hPu hc hNcentPX hNcentPXt
  have hNnormD : N ≤ Subgroup.normalizer (DX : Set ↥X) := suzOdd_N_norm_D hc hNcentD
  have hπconj : ∀ a : ↥X, π (MulAut.conj tX a) = π tX * π a * (π tX)⁻¹ := by
    intro a
    exact suzOdd_pi_conj ht hπ_comp a
  have hπ : KX.map π = DX.map π :=
    le_antisymm (suzOdd_pi_le ht hc hPL hdiag hπconj)
      (suzOdd_pi_ge ht hPu hc hPL hdiag hπconj)
  have hKDsup : KX ≤ DX ⊔ N := suzOdd_KD_sup hπ
  have hDKsup : DX ≤ KX ⊔ N := suzOdd_DK_sup hπ
  have hDXperf : Group.IsPerfect ↥DX := suzOdd_D_perf hPu hPXcomp.1 hc hDleX
  have hK_eq_D : K = D :=
    suzOdd_final hKXleX hDleX hKXperf hDXperf hNodd hNnormD hKDsup hDKsup hNcentD
  refine ⟨P, hc, hPu, hP, hne, ?_⟩
  exact hK_eq_D

end CFSG.ComponentClassification.GrSLit.L34Sec5S
