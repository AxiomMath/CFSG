module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Pre

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem map_conj_A_eq_or (S : Sylow 2 G) (td : TData (S : Subgroup G)) {h : G}
    (hh : h ∈ normalizer ((S : Subgroup G) : Set G)) :
    td.A.map (MulAut.conj h).toMonoidHom = td.A ∨
      td.A.map (MulAut.conj h).toMonoidHom = td.B := by
  have hS : ∀ x ∈ (S : Subgroup G), h * x * h⁻¹ ∈ (S : Subgroup G) :=
    fun x hx => (Subgroup.mem_normalizer_iff.1 hh x).1 hx
  have hle : td.A.map (MulAut.conj h).toMonoidHom ≤ (S : Subgroup G) := by
    rintro y ⟨x, hx, rfl⟩
    exact hS x (td.A_le_S hx)
  have hsq : ∀ x ∈ td.A.map (MulAut.conj h).toMonoidHom, x * x = 1 := by
    rintro y ⟨x, hx, rfl⟩
    have := td.A_sq x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hcomm : ∀ x ∈ td.A.map (MulAut.conj h).toMonoidHom,
      ∀ y ∈ td.A.map (MulAut.conj h).toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * x * h⁻¹ * (h * y * h⁻¹) = h * (x * y) * h⁻¹ := by group
      _ = h * (y * x) * h⁻¹ := by rw [td.A_abel x hx y hy]
      _ = h * y * h⁻¹ * (h * x * h⁻¹) := by group
  have hcard : Nat.card (td.A.map (MulAut.conj h).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, td.card_A]
  rcases td.elemAb_le _ hle hsq hcomm with h1 | h1
  · left
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard, td.card_A])
  · right
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard, td.card_B])

theorem normalizer_le_A (S : Sylow 2 G) (td : TData (S : Subgroup G)) :
    normalizer ((S : Subgroup G) : Set G) ≤ normalizer (td.A : Set G) := by
  refine normalizer_of_odd_two _ (S : Subgroup G) td.A td.B Subgroup.le_normalizer ?_ ?_ ?_
  · intro hdvd
    exact S.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => td.A_norm s hs a ha
    · intro ha
      have := td.A_norm s⁻¹ ((S : Subgroup G).inv_mem hs) _ ha
      simpa [mul_assoc] using this
  · exact fun h hh => map_conj_A_eq_or S td hh

theorem normalizer_le_B (S : Sylow 2 G) (td : TData (S : Subgroup G)) :
    normalizer ((S : Subgroup G) : Set G) ≤ normalizer (td.B : Set G) :=
  normalizer_le_A S td.swap

end Normalizer

section Quotient

variable {Cg : Type} [Group Cg] [Finite Cg]

omit [Finite Cg] in
theorem comm_mem_iff_mk_comm (Z' : Subgroup Cg) [Z'.Normal] (a b : Cg) :
    a * b * a⁻¹ * b⁻¹ ∈ Z' ↔
      (QuotientGroup.mk a : Cg ⧸ Z') * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := by
  rw [← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk a : Cg ⧸ Z') * QuotientGroup.mk b * (QuotientGroup.mk a)⁻¹ *
    (QuotientGroup.mk b)⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

omit [Finite Cg] in
theorem conj_mem_of_mem_normalizer_map (S' Z' : Subgroup Cg) [Z'.Normal] (hZS : Z' ≤ S')
    (R : Subgroup (Cg ⧸ Z')) (hR : R = S'.map (QuotientGroup.mk' Z')) {g : Cg}
    (hg : (QuotientGroup.mk g : Cg ⧸ Z') ∈ normalizer (R : Set (Cg ⧸ Z'))) :
    ∀ s ∈ S', g * s * g⁻¹ ∈ S' := by
  subst hR
  intro s hs
  have h1 : (QuotientGroup.mk s : Cg ⧸ Z') ∈ S'.map (QuotientGroup.mk' Z') := ⟨s, hs, rfl⟩
  obtain ⟨t, ht, hts⟩ := (Subgroup.mem_normalizer_iff.1 hg _).1 h1
  have h3 : t⁻¹ * (g * s * g⁻¹) ∈ Z' := by
    rw [← QuotientGroup.eq]
    exact hts
  have : g * s * g⁻¹ = t * (t⁻¹ * (g * s * g⁻¹)) := by group
  rw [this]
  exact S'.mul_mem ht (hZS h3)

theorem card_map_mk' (S' Z' : Subgroup Cg) [Z'.Normal] (hZS : Z' ≤ S') :
    Nat.card (S'.map (QuotientGroup.mk' Z')) * Nat.card Z' = Nat.card S' := by
  have hsurj := QuotientGroup.mk'_surjective Z'
  have h1 : (S'.map (QuotientGroup.mk' Z')).index = S'.index :=
    Subgroup.index_map_eq S' hsurj (by rw [QuotientGroup.ker_mk']; exact hZS)
  have h2 := Subgroup.card_mul_index (S'.map (QuotientGroup.mk' Z'))
  have h3 := Subgroup.card_mul_index S'
  have h4 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [QuotientGroup.ker_mk'] at h4
  have h5 : S'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h1] at h2
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h5)
  calc Nat.card (S'.map (QuotientGroup.mk' Z')) * Nat.card Z' * S'.index
      = Nat.card Z' * (Nat.card (S'.map (QuotientGroup.mk' Z')) * S'.index) := by ring
    _ = Nat.card Z' * Nat.card (Cg ⧸ Z') := by rw [h2]
    _ = Nat.card Cg := h4
    _ = Nat.card S' * S'.index := h3.symm

theorem conj_closed_of_gor (hGor : Gor42) (S' : Sylow 2 Cg) (Z' : Subgroup Cg) [Z'.Normal]
    (hZS : Z' ≤ (S' : Subgroup Cg)) (hS : Nat.card (S' : Subgroup Cg) = 64)
    (hZ : Nat.card Z' = 4) (hQ : pPrimeCore 2 (Cg ⧸ Z') = ⊥)
    (hsq : ∀ s ∈ (S' : Subgroup Cg), s * s ∈ Z')
    (hcomm : ∀ s ∈ (S' : Subgroup Cg), ∀ t ∈ (S' : Subgroup Cg), s * t * s⁻¹ * t⁻¹ ∈ Z')
    (hdiag : ∀ g : Cg, (∀ s ∈ (S' : Subgroup Cg), g * s * g⁻¹ ∈ (S' : Subgroup Cg)) →
      (∀ s ∈ (S' : Subgroup Cg), g⁻¹ * s * g ∈ (S' : Subgroup Cg)) →
      (∀ s ∈ (S' : Subgroup Cg), g * s * g⁻¹ * s⁻¹ ∈ Z') ∨
        ((∀ s ∈ (S' : Subgroup Cg), g * s * g⁻¹ * s⁻¹ ∈ Z' → s ∈ Z') ∧
          ∀ s ∈ (S' : Subgroup Cg), g ^ 3 * s * (g ^ 3)⁻¹ * s⁻¹ ∈ Z')) :
    ∀ c : Cg, ∀ s ∈ (S' : Subgroup Cg), c * s * c⁻¹ ∈ (S' : Subgroup Cg) := by
  obtain ⟨R, hR⟩ : ∃ R : Sylow 2 (Cg ⧸ Z'),
      (R : Subgroup (Cg ⧸ Z')) = (S' : Subgroup Cg).map (QuotientGroup.mk' Z') :=
    ⟨S'.mapSurjective (QuotientGroup.mk'_surjective Z'), rfl⟩
  have hRcard : Nat.card (R : Subgroup (Cg ⧸ Z')) = 16 := by
    have := card_map_mk' (S' : Subgroup Cg) Z' hZS
    rw [hS, hZ, ← hR] at this
    omega
  have hRsq : ∀ r ∈ (R : Subgroup (Cg ⧸ Z')), r * r = 1 := by
    rw [hR]
    rintro _ ⟨s, hs, rfl⟩
    exact (QuotientGroup.eq_one_iff (s * s)).2 (hsq s hs)
  have hRcomm : ∀ r ∈ (R : Subgroup (Cg ⧸ Z')), ∀ r' ∈ (R : Subgroup (Cg ⧸ Z')),
      r * r' = r' * r := by
    rw [hR]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact (comm_mem_iff_mk_comm Z' s t).1 (hcomm s hs t ht)
  have hnorm : ∀ x ∈ normalizer ((R : Subgroup (Cg ⧸ Z')) : Set (Cg ⧸ Z')),
      (∀ r ∈ (R : Subgroup (Cg ⧸ Z')), x * r * x⁻¹ = r) ∨
        ((∀ r ∈ (R : Subgroup (Cg ⧸ Z')), x * r * x⁻¹ = r → r = 1) ∧
          ∀ r ∈ (R : Subgroup (Cg ⧸ Z')), x ^ 3 * r * (x ^ 3)⁻¹ = r) := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg1 := conj_mem_of_mem_normalizer_map (S' : Subgroup Cg) Z' hZS _ hR hx
    have hx' : (QuotientGroup.mk g⁻¹ : Cg ⧸ Z') ∈
        normalizer ((R : Subgroup (Cg ⧸ Z')) : Set (Cg ⧸ Z')) :=
      (normalizer ((R : Subgroup (Cg ⧸ Z')) : Set (Cg ⧸ Z'))).inv_mem hx
    have hg2 := conj_mem_of_mem_normalizer_map (S' : Subgroup Cg) Z' hZS _ hR hx'
    have hg2' : ∀ s ∈ (S' : Subgroup Cg), g⁻¹ * s * g ∈ (S' : Subgroup Cg) := by
      intro s hs
      simpa using hg2 s hs
    rw [hR]
    rcases hdiag g hg1 hg2' with h1 | ⟨h2, h3⟩
    · left
      rintro _ ⟨s, hs, rfl⟩
      exact mul_inv_eq_iff_eq_mul.2 ((comm_mem_iff_mk_comm Z' g s).1 (h1 s hs))
    · right
      constructor
      · rintro _ ⟨s, hs, rfl⟩ h
        have h4 : (QuotientGroup.mk g : Cg ⧸ Z') * QuotientGroup.mk s =
            QuotientGroup.mk s * QuotientGroup.mk g := mul_inv_eq_iff_eq_mul.1 h
        exact (QuotientGroup.eq_one_iff s).2 (h2 s hs ((comm_mem_iff_mk_comm Z' g s).2 h4))
      · rintro _ ⟨s, hs, rfl⟩
        exact mul_inv_eq_iff_eq_mul.2 ((comm_mem_iff_mk_comm Z' (g ^ 3) s).1 (h3 s hs))
  have hN : (R : Subgroup (Cg ⧸ Z')).Normal := hGor (Cg ⧸ Z') hQ R hRcard hRsq hRcomm hnorm
  intro c
  exact conj_mem_of_mem_normalizer_map (S' : Subgroup Cg) Z' hZS _ hR
    (by rw [Subgroup.normalizer_eq_top]; trivial)

end Quotient

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem sylow_normal_of_normalised (S : Sylow 2 G) (C : Subgroup G) [C.Normal]
    (hSC : (S : Subgroup G) ≤ C)
    (h : ∀ c ∈ C, ∀ s ∈ (S : Subgroup G), c * s * c⁻¹ ∈ (S : Subgroup G)) :
    (S : Subgroup G).Normal := by
  have hF : normalizer ((S : Subgroup G) : Set G) ⊔ C = ⊤ :=
    Sylow.normalizer_sup_eq_top' (p := 2) (N := C) S hSC
  have hCN : C ≤ normalizer ((S : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h c hc x hx, fun hx => ?_⟩
    have := h c⁻¹ (C.inv_mem hc) _ hx
    simpa [mul_assoc] using this
  rw [sup_eq_left.2 hCN] at hF
  exact normalizer_eq_top_iff.1 hF

omit [Finite G] in
theorem le_centralizer_Z (S : Sylow 2 G) (td : TData (S : Subgroup G)) :
    (S : Subgroup G) ≤ Subgroup.centralizer (td.Z : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((td.mem_Z z).1 hz).2 s hs

theorem kl_of_centralizing (hGor : Gor42) (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) (C : Subgroup G) [C.Normal] (hSC : (S : Subgroup G) ≤ C)
    (hCz : ∀ c ∈ C, ∀ z ∈ td.Z, z * c = c * z) : (S : Subgroup G).Normal := by
  have hZS : td.Z ≤ (S : Subgroup G) := fun z hz => ((td.mem_Z z).1 hz).1
  have hZC : td.Z ≤ C := hZS.trans hSC
  have hZ'c : td.Z.subgroupOf C ≤ center ↥C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hCz c c.2 z hz).symm
  have : (td.Z.subgroupOf C).Normal := normal_of_le_center hZ'c
  have hZ2 : IsPGroup 2 td.Z := IsPGroup.of_card (n := 2) (by rw [td.card_Z]; norm_num)
  have hZ2' : IsPGroup 2 (td.Z.subgroupOf C) :=
    hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZC).symm
  have hQ : pPrimeCore 2 (↥C ⧸ td.Z.subgroupOf C) = ⊥ := pPrimeCore_quot_central hO C _ hZ'c hZ2'
  have hS64 : Nat.card ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C) = 64 := by
    rw [← td.card_S]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
  have hZ4 : Nat.card (td.Z.subgroupOf C) = 4 := by
    rw [← td.card_Z]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  have hdiag : ∀ g : ↥C,
      (∀ s ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C),
        g * s * g⁻¹ ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C)) →
      (∀ s ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C),
        g⁻¹ * s * g ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C)) →
      (∀ s ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C),
        g * s * g⁻¹ * s⁻¹ ∈ td.Z.subgroupOf C) ∨
      ((∀ s ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C),
        g * s * g⁻¹ * s⁻¹ ∈ td.Z.subgroupOf C → s ∈ td.Z.subgroupOf C) ∧
        ∀ s ∈ ((S.subtype hSC : Sylow 2 ↥C) : Subgroup ↥C),
          g ^ 3 * s * (g ^ 3)⁻¹ * s⁻¹ ∈ td.Z.subgroupOf C) := by
    intro g h1 h2
    have hgN : (g : G) ∈ normalizer ((S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact h1 ⟨x, hSC hx⟩ hx
      · intro hx
        have hxC : (g : G) * x * (g : G)⁻¹ ∈ C := hSC hx
        have h3 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) ∈ (S : Subgroup G) :=
          h2 ⟨(g : G) * x * (g : G)⁻¹, hxC⟩ hx
        have h4 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) = x := by group
        rwa [h4] at h3
    have hgZ : ∀ z ∈ td.Z, (g : G) * z * (g : G)⁻¹ = z := by
      intro z hz
      rw [← hCz g g.2 z hz]
      simp
    have hgA : ∀ a ∈ td.A, (g : G) * a * (g : G)⁻¹ ∈ td.A := fun a ha =>
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_A S td hgN) a).1 ha
    have hgB : ∀ b ∈ td.B, (g : G) * b * (g : G)⁻¹ ∈ td.B := fun b hb =>
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_B S td hgN) b).1 hb
    rcases td.diag (g : G) hgN hgZ hgA hgB with h | ⟨h', h''⟩
    · exact Or.inl fun s hs => h s hs
    · exact Or.inr ⟨fun s hs hz => h' s hs hz, fun s hs => h'' s hs⟩
  have hmain := conj_closed_of_gor hGor (S.subtype hSC) (td.Z.subgroupOf C)
    (fun z hz => hZS hz) hS64 hZ4 hQ (fun s hs => td.sq_mem_Z s hs)
    (fun s hs t ht => td.comm_mem_Z s hs t ht) hdiag
  exact sylow_normal_of_normalised S C hSC fun c hc s hs => hmain ⟨c, hc⟩ ⟨s, hSC hs⟩ hs

theorem kl (hGor : Gor42) (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) (hZ : td.Z.Normal) : (S : Subgroup G).Normal := by
  have : td.Z.Normal := hZ
  exact kl_of_centralizing hGor hO S td (Subgroup.centralizer (td.Z : Set G))
    (le_centralizer_Z S td) fun c hc z hz => Subgroup.mem_centralizer_iff.1 hc z hz

end Assembly

end CFSG.OddStandard.ThmC.O2
