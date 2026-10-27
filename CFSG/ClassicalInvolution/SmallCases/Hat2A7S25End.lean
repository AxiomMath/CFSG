module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Rank
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M6
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M5
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Exit

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Standing

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem Hyp25A7.of_mirror (h : Hat2A7M.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ :=
  { hW := h.hW
    hzW := h.hzW
    hE4 := h.hE4
    hR := h.hR
    hR' := h.hR'
    hRS := h.hRS
    hzS := h.hzS
    ht := h.ht
    hu₁ := h.hu₁
    hu₂ := h.hu₂
    std := ⟨⟨h.std.1.stand.toStd2A7, h.std.1.disconnected, h.std.1.hz, h.std.1.hK', h.std.1.hne⟩,
      h.std.2⟩ }

theorem three_le_twoRank_of_hyp25 [IsSimpleGroup G]
    (h : Hat2A7M.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂) : 3 ≤ twoRank G := by
  obtain ⟨t', ht'S, ⟨g, hg⟩, ht'R⟩ :=
    Hat2A7M.Asc77.c25_2_t_proved G Ω K K' W S R R' z t u₁ u₂ h
  have hz : IsUniqueInvolution K z := h.std.1.hz
  have hz2 : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hT : Hat2A7M.Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := ⟨h, ht'S, ht'2, ht'R⟩
  have hcomm := hT.hcomm
  have hRne : R ≠ R' := hT.hne
  have hRS : R ≤ (S : Subgroup G) := h.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := h.hR'.2.2
  obtain ⟨hu1R, hu4, -⟩ := h.hu₁
  have hRK : IsSylow2In R K := hT.hRsyl
  have hu1sq : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz (hRK.1 hu1R) hu4
  set u' : G := t' * u₁ * t'⁻¹ with hu'
  have hu'R' : u' ∈ R' := by
    have := conj_mem_conjSub (n := t') hu1R
    rwa [ht'R] at this
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hzt' : z * t' = t' * z := (h.hzS t' ht'S).symm
  have hu'sq : u' * u' = z := by
    calc u' * u' = t' * (u₁ * u₁) * t'⁻¹ := by rw [hu']; group
      _ = t' * z * t'⁻¹ := by rw [hu1sq]
      _ = z := by rw [← hzt']; group
  have hu'u : u₁ * u' = u' * u₁ := hcomm u₁ hu1R u' hu'R'
  set v : G := u₁ * u' with hv
  have hv2 : v * v = 1 := by
    calc v * v = (u₁ * u₁) * (u' * u') := by
          rw [hv]
          calc u₁ * u' * (u₁ * u') = u₁ * (u' * u₁) * u' := by group
            _ = u₁ * (u₁ * u') * u' := by rw [← hu'u]
            _ = (u₁ * u₁) * (u' * u') := by group
      _ = 1 := by rw [hu1sq, hu'sq, hz2]
  have hinf : Nat.card ↥(R ⊓ R') = 2 := hT.inf_R_R'
  have hord2 : ∀ x ∈ R, x ∈ R' → orderOf x ∣ 2 := by
    intro x hxR hxR'
    have hdvd : orderOf (⟨x, hxR, hxR'⟩ : ↥(R ⊓ R')) ∣ Nat.card ↥(R ⊓ R') :=
      orderOf_dvd_natCard _
    rw [hinf] at hdvd
    simpa [← Subgroup.orderOf_coe] using hdvd
  have hu1R' : u₁ ∈ R' → False := by
    intro hx
    have := hord2 u₁ hu1R hx
    rw [hu4] at this
    omega
  have hv1 : v ≠ 1 := by
    intro hv1
    apply hu1R'
    have : u₁ = u'⁻¹ := eq_inv_of_mul_eq_one_left hv1
    rw [this]
    exact R'.inv_mem hu'R'
  have hzR' : z ∈ R' := hT.hzR'.mem
  have hvz : z ≠ v := by
    intro hzv
    apply hu1R'
    have : u₁ = z * u'⁻¹ := by
      calc u₁ = (u₁ * u') * u'⁻¹ := by group
        _ = z * u'⁻¹ := by rw [← hv, ← hzv]
    rw [this]
    exact R'.mul_mem hzR' (R'.inv_mem hu'R')
  have ht'1 : t' ≠ 1 := by
    intro h1
    apply hRne
    rw [← ht'R, h1, conjSub_one]
  have e1 : t' * u₁ * t'⁻¹ = u' := rfl
  have ht'2' : t'⁻¹ * t'⁻¹ = 1 := by rw [ht'inv, ht'2]
  have e2 : t' * u' * t'⁻¹ = u₁ := by
    rw [hu']
    calc t' * (t' * u₁ * t'⁻¹) * t'⁻¹ = (t' * t') * u₁ * (t'⁻¹ * t'⁻¹) := by group
      _ = u₁ := by rw [ht'2, ht'2']; group
  have hvt'conj : t' * v * t'⁻¹ = v := by
    calc t' * v * t'⁻¹ = (t' * u₁ * t'⁻¹) * (t' * u' * t'⁻¹) := by rw [hv]; group
      _ = u' * u₁ := by rw [e1, e2]
      _ = u₁ * u' := hu'u.symm
  have hvt' : v * t' = t' * v := by
    calc v * t' = (t' * v * t'⁻¹) * t' := by rw [hvt'conj]
      _ = t' * v := by group
  have hvS : v ∈ (S : Subgroup G) := S.mul_mem (hRS hu1R) (hR'S hu'R')
  have hzv : z * v = v * z := (h.hzS v hvS).symm
  have hzN : z ∈ Subgroup.normalizer (R : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    exact T7F2.conjSub_eq_of_centralizes fun r hr => h.hzS r (hRS hr)
  have hvN : v ∈ Subgroup.normalizer (R : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, hv, conjSub_mul]
    have h1 : conjSub u' R = R :=
      T7F2.conjSub_eq_of_centralizes fun r hr => hcomm r hr u' hu'R'
    rw [h1, conjSub_eq_self_of_mem hu1R]
  have hcA : t' ∉ Subgroup.closure ({z, v} : Set G) := by
    intro hmem
    have hle : Subgroup.closure ({z, v} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hzN
      · exact hvN
    have := mem_normalizer_iff_conjSub_eq.mp (hle hmem)
    exact hRne (this.symm.trans ht'R)
  exact three_le_twoRank_of_commuting_involutions hz2 hv2 ht'2 hzt' hvt' hzv hz1 hv1 hvz ht'1 hcA

end Standing

section Assembly

theorem a7C25_E4_of_parts (h11 : A7C25_11) (h16 : A7C25_16) (hexit : A7ExitTF4) : A7C25_E4 := by
  intro G _ _ _ Ω K K' z hyp W hW hzW hE4
  have hstd := hyp.1
  have hyp23 : Hat2A7M.Asc77.Hyp23 Ω K K' z :=
    ⟨⟨Hat2A7M.Asc77.AscStand.of_std2A7 hstd.stand, hstd.disconnected, hstd.hz, hstd.hK',
      hstd.hne⟩, hyp.2⟩
  have h11' : Hat2A7M.Asc77.C25_11 := fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ h =>
    h11 G Ω K K' W S R R' z t u₁ u₂ (Hyp25A7.of_mirror h)
  have h16' : Hat2A7M.Asc77.C25_16 := fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ h =>
    h16 G Ω K K' W S R R' z t u₁ u₂ (Hyp25A7.of_mirror h)
  have hTF : TwoSubgroupsFourGenerated G :=
    Hat2A7M.Asc77.T7Q.c25_E4_of_11_16 h11' h16' G Ω K K' z hyp23 W hW hzW hE4
  obtain ⟨S, R, R', t, u₁, u₂, hyp25⟩ :=
    Hat2A7M.Asc77.c25_setup_of Hat2A7M.Asc77.c25_RS_proved G Ω K K' z hyp23 W hW hzW hE4
  have hrank : 3 ≤ twoRank G := three_le_twoRank_of_hyp25 hyp25
  obtain ⟨w, hw⟩ := hstd.stand.classical K hstd.stand.mem
  have hwz : w = z := by
    rcases hstd.hz.unique w hw.mem hw.mul_self with h | h
    · exfalso
      have h2 := hw.orderOf_eq_two
      rw [h, orderOf_one] at h2
      omega
    · exact h
  exact hexit G hstd.stand.nonabelian hrank hTF K z (hwz ▸ hw)

theorem Hyp25A7.toMirror {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}
    (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) :
    Hat2A7M.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂ :=
  { hW := h.hW
    hzW := h.hzW
    hE4 := h.hE4
    hR := h.hR
    hR' := h.hR'
    hRS := h.hRS
    hzS := h.hzS
    ht := h.ht
    hu₁ := h.hu₁
    hu₂ := h.hu₂
    std := ⟨⟨Hat2A7M.Asc77.AscStand.of_std2A7 h.std.1.stand, h.std.1.disconnected, h.std.1.hz,
      h.std.1.hK', h.std.1.hne⟩, h.std.2⟩ }

theorem a7C25_5_proved : A7C25_5 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS hAnorm hZ
  exact Hat2A7M.Asc77.T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp.toMirror A hzA hAS hAnorm hZ

end Assembly

end CFSG.ClassicalInvolution.Hat2A7S
