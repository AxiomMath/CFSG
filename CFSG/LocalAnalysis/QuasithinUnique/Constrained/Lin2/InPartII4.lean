module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartII3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

@[expose] def Lin2BPropsNA (T S R D B : Subgroup G) : Prop :=
  D ≤ B ∧ IsHallTwoPrimeOf B (T ⊔ D) ∧
    ((T ⊔ D : Subgroup G) : Set G) = (T : Set G) * (B : Set G) ∧
    S ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) ∧
    B ≤ Subgroup.normalizer (R : Set G) ∧
    T ⊔ D ≤ Subgroup.normalizer ((R ⊔ B : Subgroup G) : Set G) ∧
    R ⊓ Subgroup.centralizer (B : Set G) = ⊥ ∧
    R ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T ∧
    R ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
    (∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S → B = D ⊔ conjR D x) ∧
    (∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S → conjR D x ≤ Subgroup.normalizer (D : Set G))

section Stage4

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.D_isComplement_Bo : IsComplementIn (thompsonJ S) (L ⊓ M) D := by
  refine ⟨dat.D_le_Bo h, ?_, ?_⟩
  · rw [inf_comm, dat.R_eq_P h]
    exact h.decomp.1
  · intro f hf
    obtain ⟨p, hp, d, hd, hpd⟩ := h.decomp.2.2 f hf
    exact ⟨p, dat.P_le_R h hp, d, hd, hpd⟩

theorem Lin2Data.relIndex_R_Bo_odd : ¬ 2 ∣ (thompsonJ S).relIndex (L ⊓ M) := by
  have hrel := Subgroup.relIndex_mul_card (H := thompsonJ S) (K := L ⊓ M)
  rw [inf_eq_left.mpr (dat.R_le_Bo h), dat.card_Bo h] at hrel
  have hRpos : 0 < Nat.card (thompsonJ S) := Nat.card_pos
  have : (thompsonJ S).relIndex (L ⊓ M) = Nat.card D := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    rw [hrel]
    ring
  rw [this]
  exact h.hall.2.1.not_two_dvd_nat

theorem Lin2Data.exists_BNA : ∃ B : Subgroup G, Lin2BPropsNA T S (thompsonJ S) D B := by
  obtain ⟨x₀, hx₀, hx₀S⟩ := h.exists_mem_T_not_mem_S
  set R := thompsonJ S with hRdef
  set Bo := L ⊓ M with hBodef
  set K := Bo ⊔ conjR D x₀ with hKdef
  have hRBo : R ≤ Bo := dat.R_le_Bo h
  have hRK : R ≤ K := hRBo.trans le_sup_left
  have hKN : K ≤ Subgroup.normalizer (R : Set G) := dat.K_le_normalizer_R h hx₀
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := dat.T_le_normalizer_K h hx₀ hx₀S
  have hR2 : IsPGroup 2 R := h.R_isPGroup
  have hRodd : ¬ 2 ∣ R.relIndex K := dat.relIndex_R_K_odd h hx₀ hx₀S
  have hBoN : Bo ≤ Subgroup.normalizer (R : Set G) := dat.Bo_le_normalizer_R h
  obtain ⟨B₁, hB₁K, hRB₁, hdec₁⟩ := exists_complement_of_odd hRK hKN hR2 hRodd
  have hB₁'comp : IsComplementIn R Bo (B₁ ⊓ Bo) := by
    refine ⟨inf_le_right, ?_, ?_⟩
    · exact le_bot_iff.1 ((inf_le_inf_left R inf_le_left).trans hRB₁.le)
    · intro f hf
      obtain ⟨r, hr, b, hb, hfb⟩ := hdec₁ f ((le_sup_left : Bo ≤ K) hf)
      refine ⟨r, hr, b, ⟨hb, ?_⟩, hfb⟩
      have : b = r⁻¹ * f := by rw [hfb]; group
      rw [this]
      exact Bo.mul_mem (Bo.inv_mem (hRBo hr)) hf
  obtain ⟨r, hr, hDr⟩ := exists_conj_of_complements (F := Bo) hRBo hBoN hR2
    (dat.relIndex_R_Bo_odd h) hB₁'comp.1 (dat.D_isComplement_Bo h).1
    hB₁'comp.2.1 (dat.D_isComplement_Bo h).2.1 hB₁'comp.2.2 (dat.D_isComplement_Bo h).2.2
  set B := conjR B₁ r with hBdef
  have hrK : r ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hRK hr)
  have hrR : r ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer hr
  have hB₁comp : IsComplementIn R K B₁ := ⟨hB₁K, hRB₁, hdec₁⟩
  have hBcomp : IsComplementIn R K B := hB₁comp.conj hrK hrR
  have hDB : D ≤ B := by
    rw [hDr]
    exact conjR_mono inf_le_left r
  have hBK : B ≤ K := hBcomp.1
  have hRB : R ⊓ B = ⊥ := hBcomp.2.1
  have hsupB : R ⊔ B = K := hBcomp.sup_eq hRK
  have hcardK : Nat.card K = Nat.card R * Nat.card B := hBcomp.card_mul hRK hKN
  have hRS : R ≤ S := thompsonJ_le_self S
  have hRT : R ≤ T := hRS.trans h.S_le_T
  have hBN : B ≤ Subgroup.normalizer (R : Set G) := hBK.trans hKN
  have hFr : ∀ t ∈ T, ∃ r' ∈ R, conjR B t = conjR B r' := by
    intro t ht
    have hc : IsComplementIn R K (conjR B t) := hBcomp.conj (hTK ht) (dat.x_normalizer_R h ht)
    obtain ⟨r', hr', hconj⟩ := exists_conj_of_complements (F := K) hRK hKN hR2 hRodd hBK hc.1
      hRB hc.2.1 hBcomp.2.2 hc.2.2
    exact ⟨r', hr', hconj⟩
  have hNT : ∀ t r' : G, conjR B t = conjR B r' → t * r'⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
    intro t r' he
    rw [← conjR_eq_self_iff, conjR_mul, he, conjR_conjR_inv]
  obtain ⟨r₀, hr₀, he₀⟩ := hFr x₀ hx₀
  have hyB : x₀ * r₀⁻¹ ∈ Subgroup.normalizer (B : Set G) := hNT x₀ r₀ he₀
  have hyT : x₀ * r₀⁻¹ ∈ T := T.mul_mem hx₀ (T.inv_mem (hRT hr₀))
  have hyS : x₀ * r₀⁻¹ ∉ S := by
    intro hyS
    apply hx₀S
    have := S.mul_mem hyS (hRS hr₀)
    simpa using this
  have hDne : D ≠ ⊥ := by
    intro hD
    have h1 := h.card_D
    rw [hD, Subgroup.card_bot] at h1
    have h4 : 4 ≤ 2 ^ n := h.four_le_two_pow
    omega
  obtain ⟨δ, hδ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hδD : (δ : G) ∈ D := δ.2
  have hδ1 : (δ : G) ≠ 1 := fun e => hδ (Subtype.ext e)
  have hCR : ∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S →
      R ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
    intro x hx hxS
    rw [eq_bot_iff]
    rintro r ⟨hrR, hrC⟩
    have hrD : r ∈ blockD S L := by
      refine dat.centralizer_R h hδD hδ1 hrR ?_
      exact Subgroup.mem_centralizer_iff.1 hrC δ (hDB hδD)
    have hδ' : x⁻¹ * δ * x ∈ B := by
      have : x⁻¹ * δ * x ∈ conjR B x := mem_conjR_iff'.2 ⟨δ, hDB hδD, rfl⟩
      rwa [conjR_eq_of_mem_normalizer hx.2] at this
    have hxR := dat.x_normalizer_R h hx.1
    have hcomm : (x * r * x⁻¹) * δ = δ * (x * r * x⁻¹) := by
      have h1 := Subgroup.mem_centralizer_iff.1 hrC _ hδ'
      calc (x * r * x⁻¹) * δ = x * (r * (x⁻¹ * δ * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * δ * x) * r) * x⁻¹ := by rw [← h1]
        _ = δ * (x * r * x⁻¹) := by group
    have hxrR : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hxR r).1 hrR
    have hmem : x * r * x⁻¹ ∈ blockD S L :=
      dat.centralizer_R h hδD hδ1 hxrR hcomm.symm
    have : r ∈ blockD S L ⊓ conjR (blockD S L) x := ⟨hrD, mem_conjR.2 hmem⟩
    rw [dat.D₀_inf x hx.1 hxS, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  have hCR' : R ⊓ Subgroup.centralizer (B : Set G) = ⊥ := hCR _ ⟨hyT, hyB⟩ hyS
  have hRD : R ⊔ D = Bo := dat.R_sup_D h
  have hDK : D ≤ K := hDB.trans hBK
  have hKTD : K ≤ T ⊔ D := by
    refine sup_le ?_ ?_
    · rw [← hRD]
      exact sup_le_sup hRT le_rfl
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
        (Subgroup.mem_sup_left hx₀)) (Subgroup.mem_sup_right hd)) (Subgroup.mem_sup_left hx₀)
  have hTDK : T ⊔ D = T ⊔ K := le_antisymm (sup_le_sup le_rfl hDK) (sup_le le_sup_left hKTD)
  have hBTD : B ≤ T ⊔ D := hBK.trans hKTD
  have hTcard : ∃ k : ℕ, Nat.card T = 2 ^ k := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact h.sylowT.isPGroup.exists_card_eq
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hTKR : T ⊓ K = R := dat.T_inf_K h hx₀ hx₀S
  have hTDcard : Nat.card (T ⊔ D : Subgroup G) = Nat.card T * Nat.card B := by
    rw [hTDK]
    have hc := card_sup_mul_card_inf hTK
    rw [hTKR, hcardK] at hc
    apply Nat.eq_of_mul_eq_mul_right hRpos
    rw [hc]
    ring
  have hHall : IsHallTwoPrimeOf B (T ⊔ D) := by
    refine ⟨hBTD, ?_, ?_⟩
    · have h1 : R.relIndex K * Nat.card R = Nat.card K := by
        have := Subgroup.relIndex_mul_card (H := R) (K := K)
        rwa [inf_eq_left.mpr hRK] at this
      have h2 : R.relIndex K = Nat.card B := by
        apply Nat.eq_of_mul_eq_mul_right hRpos
        rw [h1, hcardK, mul_comm]
      rw [← h2]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hRodd)
    · obtain ⟨k, hk⟩ := hTcard
      refine ⟨k, ?_⟩
      have h1 := Subgroup.relIndex_mul_card (H := B) (K := T ⊔ D)
      rw [inf_eq_left.mpr hBTD, hTDcard] at h1
      have hBpos : 0 < Nat.card B := Nat.card_pos
      have h2 : B.relIndex (T ⊔ D) = Nat.card T := Nat.eq_of_mul_eq_mul_right hBpos h1
      rw [h2, hk]
  have hset : ((T ⊔ D : Subgroup G) : Set G) = (T : Set G) * (B : Set G) := by
    ext x
    constructor
    · intro hx
      have hx' : x⁻¹ ∈ T ⊔ D := Subgroup.inv_mem _ hx
      rw [hTDK, sup_comm] at hx'
      obtain ⟨k, hk, t, ht, hkt⟩ := (mem_sup_iff_of_le_normalizer hTK).1 hx'
      obtain ⟨r₁, hr₁, b, hb, rfl⟩ := hBcomp.2.2 k hk
      have hr₂ : b⁻¹ * r₁ * b ∈ R := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hBN hb)) r₁).1 hr₁
        simpa using this
      refine ⟨(b⁻¹ * r₁ * b * t)⁻¹, ?_, b⁻¹, B.inv_mem hb, ?_⟩
      · exact T.inv_mem (T.mul_mem (hRT hr₂) ht)
      · calc (b⁻¹ * r₁ * b * t)⁻¹ * b⁻¹ = (r₁ * b * t)⁻¹ := by group
          _ = x := by rw [← hkt, inv_inv]
    · rintro ⟨t, ht, b, hb, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (hBTD hb)
  have h4 : S ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) := by
    rw [hRD]
    exact h.S_le_normalizer_Bo
  have h6 : T ⊔ D ≤ Subgroup.normalizer ((R ⊔ B : Subgroup G) : Set G) := by
    rw [hsupB]
    exact sup_le hTK (hDK.trans Subgroup.le_normalizer)
  have h8 : R ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T := by
    apply le_antisymm (sup_le hRT inf_le_left)
    intro t ht
    obtain ⟨r', hr', he⟩ := hFr t ht
    have hn := hNT t r' he
    have e : t = (t * r'⁻¹) * r' := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right
      ⟨T.mul_mem ht (T.inv_mem (hRT hr')), hn⟩) (Subgroup.mem_sup_left hr')
  have h9 : R ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro r ⟨hrR, -, hrN⟩
    have hrC : r ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : r * b * r⁻¹ * b⁻¹ ∈ B :=
        B.mul_mem ((Subgroup.mem_normalizer_iff.1 hrN b).1 hb) (B.inv_mem hb)
      have h2 : r * (b * r⁻¹ * b⁻¹) ∈ R :=
        R.mul_mem hrR ((Subgroup.mem_normalizer_iff.1 (hBN hb) r⁻¹).1 (R.inv_mem hrR))
      have h3 : r * b * r⁻¹ * b⁻¹ ∈ R ⊓ B := ⟨by simpa [mul_assoc] using h2, h1⟩
      rw [hRB, Subgroup.mem_bot] at h3
      have h5 : r * b = b * r := by
        calc r * b = (r * b * r⁻¹ * b⁻¹) * b * r := by group
          _ = b * r := by rw [h3]; group
      exact h5.symm
    have : r ∈ R ⊓ Subgroup.centralizer (B : Set G) := ⟨hrR, hrC⟩
    rw [hCR'] at this
    exact this
  have hD_Bo_B : Bo ⊓ B = D := by
    apply le_antisymm
    · rintro f ⟨hfBo, hfB⟩
      obtain ⟨r₁, hr₁, d, hd, hfd⟩ := (dat.D_isComplement_Bo h).2.2 f hfBo
      have hr₁B : r₁ ∈ B := by
        have : r₁ = f * d⁻¹ := by rw [hfd]; group
        rw [this]
        exact B.mul_mem hfB (B.inv_mem (hDB hd))
      have hmem : r₁ ∈ R ⊓ B := ⟨hr₁, hr₁B⟩
      rw [hRB, Subgroup.mem_bot] at hmem
      rw [hfd, hmem, one_mul]
      exact hd
    · exact le_inf (dat.D_le_Bo h) hDB
  have hA10 : ∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S →
      B = D ⊔ conjR D x ∧ conjR D x ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx hxS
    have hEB : conjR D x ≤ B := by
      calc conjR D x ≤ conjR B x := conjR_mono hDB x
        _ = B := conjR_eq_of_mem_normalizer hx.2
    have hEBo := dat.conjR_D_le_normalizer_Bo h hx.1 hxS
    have hEN : conjR D x ≤ Subgroup.normalizer (D : Set G) := by
      refine le_normalizer_of_conj_mem fun e he d hd => ?_
      have h1 : e * d * e⁻¹ ∈ Bo :=
        (Subgroup.mem_normalizer_iff.1 (hEBo he) d).1 (dat.D_le_Bo h hd)
      have h2 : e * d * e⁻¹ ∈ B :=
        B.mul_mem (B.mul_mem (hEB he) (hDB hd)) (B.inv_mem (hEB he))
      have hm : e * d * e⁻¹ ∈ Bo ⊓ B := ⟨h1, h2⟩
      rwa [hD_Bo_B] at hm
    refine ⟨?_, hEN⟩
    have hB'le : D ⊔ conjR D x ≤ B := sup_le hDB hEB
    have hKx : K = Bo ⊔ conjR D x := dat.K_eq h hx₀ hx₀S hx.1 hxS
    have hRB'K : R ⊔ (D ⊔ conjR D x) = K := by
      apply le_antisymm
      · exact sup_le hRK (hB'le.trans hBK)
      · rw [hKx]
        refine sup_le ?_ ?_
        · rw [← hRD]
          exact sup_le_sup le_rfl le_sup_left
        · exact le_sup_right.trans le_sup_right
    have hB'N : D ⊔ conjR D x ≤ Subgroup.normalizer (R : Set G) := hB'le.trans hBN
    have hc := card_sup_mul_card_inf hB'N
    have hbot : (D ⊔ conjR D x) ⊓ R = ⊥ := by
      rw [eq_bot_iff, ← hRB]
      exact fun z hz => ⟨hz.2, hB'le hz.1⟩
    rw [hbot, Subgroup.card_bot, mul_one, sup_comm, hRB'K, hcardK] at hc
    have hcc : Nat.card R * Nat.card B = Nat.card R * Nat.card (D ⊔ conjR D x : Subgroup G) := by
      rw [hc]
      ring
    have hcard : Nat.card B = Nat.card (D ⊔ conjR D x : Subgroup G) :=
      Nat.eq_of_mul_eq_mul_left hRpos hcc
    exact (Subgroup.eq_of_le_of_card_ge hB'le hcard.le).symm
  exact ⟨B, hDB, hHall, hset, h4, hBN, h6, hCR', h8, h9,
    fun x hx hxS => (hA10 x hx hxS).1, fun x hx hxS => (hA10 x hx hxS).2⟩

end Stage4

end CFSG.QuasithinUnique.Lin2
