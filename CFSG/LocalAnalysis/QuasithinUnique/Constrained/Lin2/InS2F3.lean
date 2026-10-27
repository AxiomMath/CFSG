module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

@[expose] def s2K₁ (S L : Subgroup G) : Subgroup G :=
  (thompsonJ S ⊓ L) ⊔ (AppE.R1 S L ⊓ Subgroup.centralizer (blockU L : Set G))

@[expose] def s2K₂ (S L : Subgroup G) (t : G) : Subgroup G :=
  (thompsonJ S ⊓ conjR L t) ⊔
    (AppE.R1 S L ⊓ Subgroup.centralizer (blockU (conjR L t) : Set G))

omit [Finite G] in
theorem comm_of_sq {E : Subgroup G} (hsq : ∀ e ∈ E, e * e = 1) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
  fun a ha b hb => by
    have h1 : (a * b) * (a * b) = 1 := hsq _ (E.mul_mem ha hb)
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [← e3, mul_inv_rev, e1, e2]

omit [Finite G] in
theorem R₁_le_R1 {S L : Subgroup G} : thompsonJ S ⊓ L ≤ AppE.R1 S L := fun _ hr =>
  ⟨GammaExtra.thompsonJ_le_self S hr.1, Subgroup.le_normalizer hr.2⟩

omit [Finite G] in
theorem R1_conj_R₁ {S L : Subgroup G} :
    ∀ s ∈ AppE.R1 S L, ∀ r ∈ thompsonJ S ⊓ L, s * r * s⁻¹ ∈ thompsonJ S ⊓ L := by
  intro s hs r hr
  obtain ⟨hsS, hsN⟩ := hs
  refine ⟨?_, (Subgroup.mem_normalizer_iff.1 hsN r).1 hr.2⟩
  have : r ∈ conjR (thompsonJ S) s := by
    rw [thompsonJ_normalized (Subgroup.le_normalizer hsS)]
    exact hr.1
  exact mem_conjR.1 this

theorem R₁_le_normalizer_N₁ {S L : Subgroup G} : thompsonJ S ⊓ L ≤
    Subgroup.normalizer ((AppE.R1 S L ⊓ Subgroup.centralizer (blockU L : Set G) : Subgroup G) :
      Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
    (fun _ hr => Subgroup.le_normalizer (R₁_le_R1 hr))
    (fun _ hr => CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _
      (C1.le_normalizer_blockU L hr.2))

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem R1_isPGroup : IsPGroup 2 (AppE.R1 S L) := B.sylow.isPGroup.to_le AppE.R1_le_S

theorem R₂_le_R1 : thompsonJ S ⊓ conjR L t ≤ AppE.R1 S L := fun _ hr =>
  ⟨GammaExtra.thompsonJ_le_self S hr.1,
    le_normalizer_of_commute (A := L) (B := conjR L t) (fun a ha b hb => B.comm_elem a ha b hb)
      hr.2⟩

theorem R1_conj_R₂ : ∀ s ∈ AppE.R1 S L, ∀ r ∈ thompsonJ S ⊓ conjR L t,
    s * r * s⁻¹ ∈ thompsonJ S ⊓ conjR L t := by
  intro s hs r hr
  refine ⟨?_, (Subgroup.mem_normalizer_iff.1 (B.dbl.R1_le_normalizer_L₂ hs) r).1 hr.2⟩
  have : r ∈ conjR (thompsonJ S) s := by
    rw [thompsonJ_normalized (Subgroup.le_normalizer hs.1)]
    exact hr.1
  exact mem_conjR.1 this

theorem R₂_le_normalizer_N₂ : thompsonJ S ⊓ conjR L t ≤
    Subgroup.normalizer ((AppE.R1 S L ⊓ Subgroup.centralizer (blockU (conjR L t) : Set G) :
      Subgroup G) : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
    (fun _ hr => Subgroup.le_normalizer (B.R₂_le_R1 hr))
    (fun _ hr => CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _
      (C1.le_normalizer_blockU (conjR L t) hr.2))

theorem S0_facts₁ : ∀ E : Subgroup G, E ≤ AppE.R1 S L → (∀ e ∈ E, e * e = 1) →
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ s2K₁ S L) :=
  (C56.lin2_S_facts (L := L) B.hL (by have := B.hn; omega) B.hlin B.isSylowTwoOf_R₁
    B.R1_isPGroup inf_le_right R₁_le_R1 R1_conj_R₁).1

theorem S0_facts₂ : ∀ E : Subgroup G, E ≤ AppE.R1 S L → (∀ e ∈ E, e * e = 1) →
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ s2K₂ S L t) :=
  (C56.lin2_S_facts (L := conjR L t) B.hL₂ (by have := B.hn; omega) B.hlin₂ B.isSylowTwoOf_R₂
    B.R1_isPGroup (B.dbl.R1_le_normalizer_L₂) B.R₂_le_R1 B.R1_conj_R₂).1

theorem conjR_K₁ {w : G} (hwS : w ∈ S) (hw : w ∉ AppE.R1 S L) :
    conjR (s2K₁ S L) w = s2K₂ S L t := by
  have hwL : conjR L w = conjR L t := B.dbl.conjR_eq_t_of_not_mem hwS hw
  have hwR : conjR (thompsonJ S) w = thompsonJ S :=
    thompsonJ_normalized (Subgroup.le_normalizer hwS)
  have hwS₀ : conjR (AppE.R1 S L) w = AppE.R1 S L := by
    rw [conjR_eq_self_iff, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => B.dbl.R1_normal hwS hh, fun hh => ?_⟩
    have := B.dbl.R1_normal (S.inv_mem hwS) hh
    simpa [mul_assoc] using this
  unfold s2K₁ s2K₂
  rw [conjR_sup, conjR_inf, conjR_inf, hwR, hwL, hwS₀, ← conjR_centralizer, ← DoubleA3.blockU_conjR,
    hwL]

end S2Base

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem K₁_inf_K₂_le_R : s2K₁ S L ⊓ s2K₂ S L t ≤ thompsonJ S := by
  have hB := O.base
  rintro k ⟨hk₁, hk₂⟩
  have hk₁' : k ∈ (AppE.R1 S L ⊓ Subgroup.centralizer (blockU L : Set G)) ⊔
      (thompsonJ S ⊓ L) := by
    unfold s2K₁ at hk₁
    rwa [sup_comm] at hk₁
  have hk₂' : k ∈ (AppE.R1 S L ⊓ Subgroup.centralizer (blockU (conjR L t) : Set G)) ⊔
      (thompsonJ S ⊓ conjR L t) := by
    unfold s2K₂ at hk₂
    rwa [sup_comm] at hk₂
  obtain ⟨c₁, hc₁, r₁, hr₁, hk₁e⟩ := (mem_sup_iff_of_le_normalizer R₁_le_normalizer_N₁).1 hk₁'
  obtain ⟨c₂, hc₂, r₂, hr₂, hk₂e⟩ := (mem_sup_iff_of_le_normalizer hB.R₂_le_normalizer_N₂).1 hk₂'
  have hkk : c₁ * r₁ = c₂ * r₂ := hk₁e.symm.trans hk₂e
  set z : G := r₂⁻¹ * c₁ with hz
  have hz₁ : ∀ u ∈ blockU L, u * z = z * u := by
    intro u hu
    have h1 : u * r₂⁻¹ = r₂⁻¹ * u := hB.comm_elem u (blockU_le L hu) r₂⁻¹ ((conjR L t).inv_mem hr₂.2)
    have h2 : u * c₁ = c₁ * u := Subgroup.mem_centralizer_iff.1 hc₁.2 u hu
    calc u * z = (u * r₂⁻¹) * c₁ := by rw [hz]; group
      _ = r₂⁻¹ * (u * c₁) := by rw [h1]; group
      _ = r₂⁻¹ * (c₁ * u) := by rw [h2]
      _ = z * u := by rw [hz]; group
  have hy : r₂⁻¹ * c₂ * r₂ ∈ Subgroup.centralizer (blockU (conjR L t) : Set G) := by
    have hn : r₂⁻¹ ∈ Subgroup.normalizer (blockU (conjR L t) : Set G) :=
      C1.le_normalizer_blockU (conjR L t) ((conjR L t).inv_mem hr₂.2)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : r₂ * u * r₂⁻¹ ∈ blockU (conjR L t) :=
      (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU (conjR L t) hr₂.2) u).1 hu
    have h1 := Subgroup.mem_centralizer_iff.1 hc₂.2 _ hu'
    calc u * (r₂⁻¹ * c₂ * r₂) = r₂⁻¹ * ((r₂ * u * r₂⁻¹) * c₂) * r₂ := by group
      _ = r₂⁻¹ * (c₂ * (r₂ * u * r₂⁻¹)) * r₂ := by rw [h1]
      _ = r₂⁻¹ * c₂ * r₂ * u := by group
  have hzy : z = (r₂⁻¹ * c₂ * r₂) * r₁⁻¹ := by
    have : c₁ = c₂ * r₂ * r₁⁻¹ := by
      calc c₁ = c₁ * r₁ * r₁⁻¹ := by group
        _ = c₂ * r₂ * r₁⁻¹ := by rw [hkk]
    rw [hz, this]
    group
  have hz₂ : ∀ u ∈ blockU (conjR L t), u * z = z * u := by
    intro u hu
    have h1 : u * r₁⁻¹ = r₁⁻¹ * u :=
      (hB.comm_elem r₁⁻¹ (L.inv_mem hr₁.2) u (blockU_le _ hu)).symm
    have h2 : u * (r₂⁻¹ * c₂ * r₂) = (r₂⁻¹ * c₂ * r₂) * u := Subgroup.mem_centralizer_iff.1 hy u hu
    rw [hzy]
    calc u * (r₂⁻¹ * c₂ * r₂ * r₁⁻¹) = (u * (r₂⁻¹ * c₂ * r₂)) * r₁⁻¹ := by group
      _ = ((r₂⁻¹ * c₂ * r₂) * u) * r₁⁻¹ := by rw [h2]
      _ = (r₂⁻¹ * c₂ * r₂) * (u * r₁⁻¹) := by group
      _ = (r₂⁻¹ * c₂ * r₂) * (r₁⁻¹ * u) := by rw [h1]
      _ = (r₂⁻¹ * c₂ * r₂ * r₁⁻¹) * u := by group
  have hzQ : z ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [hB.pCore_eq_UU O.hC]
    exact C56.mem_centralizer_sup hz₁
      (fun u hu => hz₂ u (by rw [DoubleA3.blockU_conjR]; exact hu))
  have hzH : z ∈ H := H.mul_mem (H.inv_mem (hB.S_le_H (GammaExtra.thompsonJ_le_self S
    (hr₂.1)))) (hB.S_le_H (AppE.R1_le_S hc₁.1))
  have hzR : z ∈ thompsonJ S := hB.Q_le_R (hB.cs.charTwo ⟨hzH, hzQ⟩)
  have hc₁R : c₁ ∈ thompsonJ S := by
    have : r₂ * z ∈ thompsonJ S := (thompsonJ S).mul_mem hr₂.1 hzR
    rw [hz] at this
    simpa using this
  rw [hk₁e]
  exact (thompsonJ S).mul_mem hc₁R hr₁.1

theorem card_le_four_mul {E : Subgroup G} (hE : E ≤ S) (hsq : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 * Nat.card ↥(E ⊓ thompsonJ S) := by
  have hB := O.base
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := comm_of_sq hsq
  have hKK := O.K₁_inf_K₂_le_R
  by_cases hE₀ : E ≤ AppE.R1 S L
  · have h1 := hB.S0_facts₁ E hE₀ hsq
    have hE₁ : E ⊓ s2K₁ S L ≤ AppE.R1 S L := inf_le_left.trans hE₀
    have hsq₁ : ∀ e ∈ E ⊓ s2K₁ S L, e * e = 1 := fun e he => hsq e he.1
    have h2 := hB.S0_facts₂ _ hE₁ hsq₁
    have h3 : Nat.card ↥(E ⊓ s2K₁ S L ⊓ s2K₂ S L t) ≤ Nat.card ↥(E ⊓ thompsonJ S) :=
      Subgroup.card_le_of_le (fun e he => ⟨he.1.1, hKK ⟨he.1.2, he.2⟩⟩)
    calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ s2K₁ S L) := h1
      _ ≤ 2 * (2 * Nat.card ↥(E ⊓ s2K₁ S L ⊓ s2K₂ S L t)) := Nat.mul_le_mul_left 2 h2
      _ ≤ 2 * (2 * Nat.card ↥(E ⊓ thompsonJ S)) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 h3)
      _ = 4 * Nat.card ↥(E ⊓ thompsonJ S) := by ring
  · obtain ⟨w, hwE, hwS₀⟩ : ∃ w ∈ E, w ∉ AppE.R1 S L := by
      by_contra h
      push Not at h
      exact hE₀ h
    have hwS : w ∈ S := hE hwE
    have hconj := hB.conjR_K₁ hwS hwS₀
    have hidx : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ AppE.R1 S L) := by
      have h1 : Nat.card E = Nat.card ↥(E ⊓ AppE.R1 S L) * (E ⊓ AppE.R1 S L).relIndex E :=
        C5.card_eq_card_mul_relIndex inf_le_left
      have h2 : (E ⊓ AppE.R1 S L).relIndex E = (AppE.R1 S L).relIndex E := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
      have h3 : (AppE.R1 S L).relIndex E ≤ (AppE.R1 S L).relIndex S :=
        Subgroup.relIndex_le_of_le_right hE (by rw [hB.dbl.relIndex_R1]; omega)
      rw [hB.dbl.relIndex_R1] at h3
      calc Nat.card E = Nat.card ↥(E ⊓ AppE.R1 S L) * (E ⊓ AppE.R1 S L).relIndex E := h1
        _ ≤ Nat.card ↥(E ⊓ AppE.R1 S L) * 2 := by
            rw [h2]
            exact Nat.mul_le_mul_left _ h3
        _ = 2 * Nat.card ↥(E ⊓ AppE.R1 S L) := mul_comm _ _
    have hsq₀ : ∀ e ∈ E ⊓ AppE.R1 S L, e * e = 1 := fun e he => hsq e he.1
    have h1 := hB.S0_facts₁ _ inf_le_right hsq₀
    have h3 : Nat.card ↥(E ⊓ AppE.R1 S L ⊓ s2K₁ S L) ≤ Nat.card ↥(E ⊓ thompsonJ S) := by
      refine Subgroup.card_le_of_le fun e he => ⟨he.1.1, ?_⟩
      have hwe : w * e = e * w := hcomm w hwE e he.1.1
      have hek : e ∈ conjR (s2K₁ S L) w := by
        refine mem_conjR_iff'.2 ⟨e, he.2, ?_⟩
        calc e = w⁻¹ * (w * e) := by group
          _ = w⁻¹ * (e * w) := by rw [hwe]
          _ = w⁻¹ * e * w := by group
      rw [hconj] at hek
      exact hKK ⟨he.2, hek⟩
    calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ AppE.R1 S L) := hidx
      _ ≤ 2 * (2 * Nat.card ↥(E ⊓ AppE.R1 S L ⊓ s2K₁ S L)) := Nat.mul_le_mul_left 2 h1
      _ ≤ 2 * (2 * Nat.card ↥(E ⊓ thompsonJ S)) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 h3)
      _ = 4 * Nat.card ↥(E ⊓ thompsonJ S) := by ring

end S2Ok

end CFSG.QuasithinUnique.Lin2
