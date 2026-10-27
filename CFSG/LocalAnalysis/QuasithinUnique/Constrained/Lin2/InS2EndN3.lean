module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndN2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

namespace EndN

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x : G} {q : ℕ} {W D₁ D₂ : Subgroup G}

namespace Data

variable (E : Data T M H S L D n t M₀ x q W D₁ D₂)
include E

theorem D₁_le_L : D₁ ≤ L := E.hT₁.le_borel.trans inf_le_left

theorem D₂_le_L₂ : D₂ ≤ conjR L t := E.hT₂.le_borel.trans inf_le_left

theorem D₁_ne_D₂ : D₁ ≠ D₂ := by
  intro h
  have h4 := two_pow_ge_four E.B.hn
  obtain ⟨d, hd, hd1⟩ := exists_ne_one_of_one_lt_card (X := D₁) (by rw [E.hT₁.card]; omega)
  have : d ∈ L ⊓ conjR L t := ⟨E.D₁_le_L hd, E.D₂_le_L₂ (h ▸ hd)⟩
  rw [E.B.L_inf_L₂, Subgroup.mem_bot] at this
  exact hd1 this

theorem L₀_inf_normalizer_le_M :
    conjJoin S L ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ M := by
  rintro g ⟨hgL, hgN⟩
  have hSH : S ≤ H := E.B.S_le_H
  have hXlt : H ⊓ Subgroup.normalizer (thompsonJ S : Set G) < H := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hHN : H ≤ Subgroup.normalizer (thompsonJ S : Set G) := inf_eq_left.1 heq
    have hRH : thompsonJ S ≤ H := (thompsonJ_le_self S).trans hSH
    have hRQ : thompsonJ S ≤ pCoreOf 2 H := le_pCoreOf_of_normalizes hRH hHN E.B.R_isPGroup
    have h1 : conjR (pCoreOf 2 H) x ≤ pCoreOf 2 H := E.B.conj_pCore_le_R.trans hRQ
    exact E.Qx_ne_Q (Subgroup.eq_of_le_of_card_ge h1 (card_conjR _ _).ge)
  have hSX : S ≤ H ⊓ Subgroup.normalizer (thompsonJ S : Set G) :=
    le_inf hSH fun s hs => conjR_eq_self_iff.1 (thompsonJ_normalized (Subgroup.le_normalizer hs))
  exact E.cs.maxInf _ hSX hXlt ⟨E.B.L₀_le_H hgL, hgN⟩

theorem conjD_le_RD
    {y : G} (hy : y ∈ Subgroup.normalizer (thompsonJ S : Set G)) :
    conjR D y ≤ thompsonJ S ⊔ D := by
  intro z hz
  obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hz
  have h1 : y⁻¹ * d * y ∈ conjJoin S L := by
    simpa using E.conj_mem_L₀ (Subgroup.inv_mem _ hy) hd
  have h2 : y⁻¹ * d * y ∈ Subgroup.normalizer (thompsonJ S : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) (E.B.D_le_normalizer_R hd)) hy
  rw [E.B.R_sup_D_eq]
  exact Subgroup.mem_sup_left ⟨h1, E.L₀_inf_normalizer_le_M ⟨h1, h2⟩⟩

theorem exists_mem_normalizer_D
    {y : G} (hy : y ∈ Subgroup.normalizer (thompsonJ S : Set G)) :
    ∃ r ∈ thompsonJ S, y * r⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
  set R := thompsonJ S with hR
  have hR2 : IsPGroup 2 R := E.B.R_isPGroup
  have hRF : R ≤ R ⊔ D := le_sup_left
  have hFN : R ⊔ D ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer E.B.D_le_normalizer_R
  have hodd : ¬ 2 ∣ R.relIndex (R ⊔ D) := E.B.relIndex_R_RD_odd
  have hDcomp : IsComplementIn R (R ⊔ D) D :=
    ⟨le_sup_right, by
      rw [inf_comm]; exact inf_eq_bot_of_odd_card_of_isPGroup E.B.cfg.hall.2.1 hR2,
      fun f hf => E.B.RD_decomp f hf⟩
  have hDy : conjR D y ≤ R ⊔ D := E.conjD_le_RD hy
  have hDyN : conjR D y ≤ Subgroup.normalizer (R : Set G) := hDy.trans hFN
  have hodd' : Odd (Nat.card (conjR D y)) := by rw [card_conjR]; exact E.B.cfg.hall.2.1
  have hRDy : R ⊓ conjR D y = ⊥ := by
    rw [inf_comm]; exact inf_eq_bot_of_odd_card_of_isPGroup hodd' hR2
  have hsup : R ⊔ conjR D y = R ⊔ D := by
    have hc := card_sup_mul_card_inf (A := conjR D y) (B := R) hDyN
    rw [inf_comm, hRDy, Subgroup.card_bot, mul_one, sup_comm] at hc
    refine Subgroup.eq_of_le_of_card_ge (sup_le hRF hDy) ?_
    rw [hc, card_conjR, E.B.card_RD, mul_comm]
  have hFDy : ∀ f ∈ R ⊔ D, ∃ r ∈ R, ∃ b ∈ conjR D y, f = r * b := by
    intro f hf
    rw [← hsup] at hf
    obtain ⟨r, hr, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hDyN).1 hf
    exact ⟨r, hr, b, hb, rfl⟩
  obtain ⟨r, hr, hconj⟩ := exists_conj_of_complements (F := R ⊔ D) hRF hFN hR2 hodd hDcomp.1 hDy
    hDcomp.2.1 hRDy hDcomp.2.2 hFDy
  refine ⟨r, hr, ?_⟩
  rw [← conjR_eq_self_iff, conjR_mul, hconj, conjR_conjR_inv]

theorem conjR_D₁_cases' {w : G} (hwR : conjR (thompsonJ S) w = thompsonJ S)
    (hwD : conjR D w = D) : conjR D₁ w = D₁ ∨ conjR D₁ w = D₂ := by
  have hD₁D : D₁ ≤ D := E.hD ▸ le_sup_left
  have hle : conjR D₁ w ≤ D := by
    have := conjR_mono hD₁D w
    rwa [hwD] at this
  have hE : ∀ g ∈ conjR D₁ w, g ≠ 1 →
      thompsonJ S ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥ := by
    intro g hg hg1
    obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hg
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_one_lt_card (X := blockU (conjR L t))
      (one_lt_card_blockU E.B.hlin₂ E.B.hn)
    have hz : w⁻¹ * u * w ∈ conjR (thompsonJ S) w :=
      mem_conjR_iff'.2 ⟨u, E.B.U₂_le_R hu, rfl⟩
    rw [hwR] at hz
    have hcomm : d * u = u * d := E.B.comm_elem d (E.D₁_le_L hd) u (blockU_le _ hu)
    have hzc : w⁻¹ * u * w ∈ Subgroup.centralizer ({w⁻¹ * d * w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w⁻¹ * u * w * (w⁻¹ * d * w) = w⁻¹ * (u * d) * w := by group
        _ = w⁻¹ * (d * u) * w := by rw [hcomm]
        _ = w⁻¹ * d * w * (w⁻¹ * u * w) := by group
    intro h
    have hmem : w⁻¹ * u * w ∈ (⊥ : Subgroup G) := h ▸ (⟨hz, hzc⟩ : _ ∈ thompsonJ S ⊓ _)
    rw [Subgroup.mem_bot] at hmem
    apply hu1
    have := congrArg (fun z => w * z * w⁻¹) hmem
    simpa [mul_assoc] using this
  rcases E.B.sub_D_le_or E.hT₁ E.hT₂ E.hD E.hC hle hE with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (card_conjR D₁ w).ge)
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge h ?_)
    rw [E.hT₂.card, card_conjR, E.hT₁.card]

theorem conjR_D₂_cases' {w : G} (hwR : conjR (thompsonJ S) w = thompsonJ S)
    (hwD : conjR D w = D) : conjR D₂ w = D₁ ∨ conjR D₂ w = D₂ := by
  have hD₂D : D₂ ≤ D := E.hD ▸ le_sup_right
  have hle : conjR D₂ w ≤ D := by
    have := conjR_mono hD₂D w
    rwa [hwD] at this
  have hE : ∀ g ∈ conjR D₂ w, g ≠ 1 →
      thompsonJ S ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥ := by
    intro g hg hg1
    obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hg
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_one_lt_card (X := blockU L)
      (one_lt_card_blockU E.B.hlin E.B.hn)
    have hz : w⁻¹ * u * w ∈ conjR (thompsonJ S) w :=
      mem_conjR_iff'.2 ⟨u, E.B.U₁_le_R hu, rfl⟩
    rw [hwR] at hz
    have hcomm : u * d = d * u := E.B.comm_elem u (blockU_le _ hu) d (E.D₂_le_L₂ hd)
    have hzc : w⁻¹ * u * w ∈ Subgroup.centralizer ({w⁻¹ * d * w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w⁻¹ * u * w * (w⁻¹ * d * w) = w⁻¹ * (u * d) * w := by group
        _ = w⁻¹ * (d * u) * w := by rw [hcomm]
        _ = w⁻¹ * d * w * (w⁻¹ * u * w) := by group
    intro h
    have hmem : w⁻¹ * u * w ∈ (⊥ : Subgroup G) := h ▸ (⟨hz, hzc⟩ : _ ∈ thompsonJ S ⊓ _)
    rw [Subgroup.mem_bot] at hmem
    apply hu1
    have := congrArg (fun z => w * z * w⁻¹) hmem
    simpa [mul_assoc] using this
  rcases E.B.sub_D_le_or E.hT₁ E.hT₂ E.hD E.hC hle hE with h | h
  · refine Or.inl (Subgroup.eq_of_le_of_card_ge h ?_)
    rw [E.hT₁.card, card_conjR, E.hT₂.card]
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (card_conjR D₂ w).ge)

theorem perm_cases {w : G} (hwR : conjR (thompsonJ S) w = thompsonJ S) (hwD : conjR D w = D) :
    (conjR (thompsonJ S ⊓ L) w = thompsonJ S ⊓ L ∧
      conjR (thompsonJ S ⊓ conjR L t) w = thompsonJ S ⊓ conjR L t) ∨
    (conjR (thompsonJ S ⊓ L) w = thompsonJ S ⊓ conjR L t ∧
      conjR (thompsonJ S ⊓ conjR L t) w = thompsonJ S ⊓ L) := by
  have h₁ := E.B.R₁_eq_centralizer E.hT₁ E.hT₂ E.hD E.hC
  have h₂ := E.B.R₂_eq_centralizer E.hT₁ E.hT₂ E.hD E.hC
  have hne := E.D₁_ne_D₂
  have hc₁ : conjR (thompsonJ S ⊓ L) w =
      thompsonJ S ⊓ Subgroup.centralizer ((conjR D₂ w : Subgroup G) : Set G) := by
    rw [h₁, conjR_inf, hwR, conjR_centralizer]
  have hc₂ : conjR (thompsonJ S ⊓ conjR L t) w =
      thompsonJ S ⊓ Subgroup.centralizer ((conjR D₁ w : Subgroup G) : Set G) := by
    rw [h₂, conjR_inf, hwR, conjR_centralizer]
  rcases E.conjR_D₁_cases' hwR hwD with h1 | h1 <;> rcases E.conjR_D₂_cases' hwR hwD with h2 | h2
  · exact absurd (conjR_inj_right (h2.trans h1.symm)).symm hne
  · refine Or.inl ⟨?_, ?_⟩
    · rw [hc₁, h2, ← h₁]
    · rw [hc₂, h1, ← h₂]
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hc₁, h2, ← h₂]
    · rw [hc₂, h1, ← h₁]
  · exact absurd (conjR_inj_right (h1.trans h2.symm)) hne

theorem perm_cases_all
    {y : G} (hy : y ∈ Subgroup.normalizer (thompsonJ S : Set G)) :
    (conjR (thompsonJ S ⊓ L) y = thompsonJ S ⊓ L ∧
      conjR (thompsonJ S ⊓ conjR L t) y = thompsonJ S ⊓ conjR L t) ∨
    (conjR (thompsonJ S ⊓ L) y = thompsonJ S ⊓ conjR L t ∧
      conjR (thompsonJ S ⊓ conjR L t) y = thompsonJ S ⊓ L) := by
  obtain ⟨r, hr, hrD⟩ := E.exists_mem_normalizer_D hy
  have hwR : conjR (thompsonJ S) (y * r⁻¹) = thompsonJ S :=
    conjR_eq_self_iff.2 (Subgroup.mul_mem _ hy
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hr)))
  have hwD : conjR D (y * r⁻¹) = D := conjR_eq_self_iff.2 hrD
  have hrR₁ : conjR (thompsonJ S ⊓ L) r = thompsonJ S ⊓ L := by
    rw [conjR_inf, conjR_eq_of_mem hr, conjR_eq_of_mem_normalizer (E.B.R_le_normalizer_L hr)]
  have hrR₂ : conjR (thompsonJ S ⊓ conjR L t) r = thompsonJ S ⊓ conjR L t := by
    rw [conjR_inf, conjR_eq_of_mem hr,
      conjR_eq_of_mem_normalizer (E.B.R_le_normalizer_L₂ hr)]
  have key : ∀ X : Subgroup G, conjR X y = conjR (conjR X (y * r⁻¹)) r := fun X => by
    rw [← conjR_mul]; congr 1; group
  rcases E.perm_cases hwR hwD with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [key, key, h1, h2, hrR₁, hrR₂]
    exact ⟨rfl, rfl⟩
  · right
    rw [key, key, h1, h2, hrR₁, hrR₂]
    exact ⟨rfl, rfl⟩

theorem R₁_ne_R₂ : thompsonJ S ⊓ L ≠ thompsonJ S ⊓ conjR L t := by
  intro h
  apply E.B.R₁_ne_bot
  have := E.B.R₁_inf_R₂
  rwa [← h, inf_idem] at this

theorem conjR_R₂_of_normalizer
    {y : G} (hy : y ∈ Subgroup.normalizer (thompsonJ S : Set G))
    (hy₁ : y ∈ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) :
    conjR (thompsonJ S ⊓ conjR L t) y = thompsonJ S ⊓ conjR L t := by
  rcases E.perm_cases_all hy with ⟨-, h⟩ | ⟨h1, -⟩
  · exact h
  · exact absurd (h1.symm.trans (conjR_eq_of_mem_normalizer hy₁)) E.R₁_ne_R₂.symm

theorem relIndex_T₁_le
    :
    ((T ⊓ Subgroup.normalizer (thompsonJ S : Set G)) ⊓
        Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)).relIndex
      (T ⊓ Subgroup.normalizer (thompsonJ S : Set G)) ≤ 2 := by
  set P := T ⊓ Subgroup.normalizer (thompsonJ S : Set G) with hP
  rw [← card_conj_orbit_eq_relIndex P (thompsonJ S ⊓ L)]
  have hsub : {L' : Subgroup G | ∃ h ∈ P, L' = CFSG.conjugate (thompsonJ S ⊓ L) h} ⊆
      {thompsonJ S ⊓ L, thompsonJ S ⊓ conjR L t} := by
    rintro _ ⟨h, hh, rfl⟩
    rcases E.perm_cases_all hh.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have h1 : Nat.card {L' : Subgroup G // ∃ h ∈ P, L' = CFSG.conjugate (thompsonJ S ⊓ L) h} =
      Set.ncard {L' : Subgroup G | ∃ h ∈ P, L' = CFSG.conjugate (thompsonJ S ⊓ L) h} :=
    Nat.card_coe_set_eq _
  rw [h1]
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [Set.ncard_singleton]

theorem relIndex_S₂_le
    :
    (((T ⊓ Subgroup.normalizer (thompsonJ S : Set G)) ⊓
        Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) ⊓
        Subgroup.normalizer ((blockU (conjR L t) : Subgroup G) : Set G)).relIndex
      ((T ⊓ Subgroup.normalizer (thompsonJ S : Set G)) ⊓
        Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) ≤ 2 := by
  set P := T ⊓ Subgroup.normalizer (thompsonJ S : Set G) with hP
  set T₁ := P ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) with hT₁
  have O : S2Ok T M H S L D n t M₀ x q W D₁ D₂ := ⟨E.B, E.hT₁, E.hT₂, E.hD, E.hC, E.hDx⟩
  rw [← card_conj_orbit_eq_relIndex T₁ (blockU (conjR L t))]
  have hsub : {L' : Subgroup G | ∃ h ∈ T₁, L' = CFSG.conjugate (blockU (conjR L t)) h} ⊆
      {blockU (conjR L t), conjR (blockU (conjR L t)) x} := by
    rintro _ ⟨h, hh, rfl⟩
    have hR₂ : conjR (thompsonJ S ⊓ conjR L t) h = thompsonJ S ⊓ conjR L t :=
      E.conjR_R₂_of_normalizer hh.1.2 hh.2
    have hU := O.UT3_R₂.conj h
    have hle : conjR (blockU (conjR L t)) h ≤ thompsonJ S ⊓ conjR L t := by
      have := hU.U_le_R
      rwa [hR₂] at this
    exact O.UT3_R₂.eq_of_card hle hU.sq₁ hU.card_U
  have h1 : Nat.card {L' : Subgroup G // ∃ h ∈ T₁, L' = CFSG.conjugate (blockU (conjR L t)) h} =
      Set.ncard {L' : Subgroup G | ∃ h ∈ T₁, L' = CFSG.conjugate (blockU (conjR L t)) h} :=
    Nat.card_coe_set_eq _
  rw [h1]
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [Set.ncard_singleton]

theorem four_mul_card_le : 4 * Nat.card S ≤
    Nat.card (T ⊓ Subgroup.normalizer (thompsonJ S : Set G) : Subgroup G) := by
  set P := T ⊓ Subgroup.normalizer (thompsonJ S : Set G) with hP
  have hM₀P : M₀ ≤ P := le_inf E.B.hMT E.B.M₀_le_normalizer_R
  have hM₀ne : M₀ ≠ P := fun h => E.hlt (h ▸ le_rfl)
  have hcard : Nat.card M₀ = 2 * Nat.card S :=
    GammaExtra.card_eq_two_mul_of_relIndex_eq_two E.B.hSM E.B.h2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hM₀P
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hM₀ne (Subgroup.eq_of_le_of_card_ge hM₀P hk.le)
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card P := Nat.card_pos
    omega
  have hk2 : 2 ≤ k := by omega
  calc 4 * Nat.card S = 2 * Nat.card M₀ := by rw [hcard]; ring
    _ ≤ k * Nat.card M₀ := Nat.mul_le_mul_right _ hk2
    _ = Nat.card P := by rw [hk, mul_comm]

end Data

end EndN

end CFSG.QuasithinUnique.Lin2
