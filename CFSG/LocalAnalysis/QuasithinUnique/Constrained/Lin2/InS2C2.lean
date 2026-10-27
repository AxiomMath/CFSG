module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2C1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Borel2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

theorem inf_eq_bot_of_odd_card_of_isPGroup {X Y : Subgroup G} (hX : Odd (Nat.card X))
    (hY : IsPGroup 2 Y) : X ⊓ Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI : IsPGroup 2 ↥(X ⊓ Y) := hY.to_le inf_le_right
  obtain ⟨k, hk⟩ := hI.exists_card_eq
  have hdvd : Nat.card ↥(X ⊓ Y) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hne
    rw [hk] at hdvd
    exact hX.not_two_dvd_nat (h2.trans hdvd)
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0]; rfl)

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem conjR_R_x₀ : conjR (thompsonJ S) x₀ = thompsonJ S := thompsonJ_normalized B.su.hxN

theorem x₀_mem_M : x₀ ∈ M := B.cs.setting.le (B.hMT B.hx₀)

theorem P_le_R : S ⊓ conjJoin S L ≤ thompsonJ S := by
  rw [B.S_inf_L₀_eq]
  exact sup_le inf_le_left inf_le_left

theorem D_le_inf_M : D ≤ conjJoin S L ⊓ M := B.cfg.hall.1

theorem C_eq_baumD : thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G) = baumD S L := by
  unfold baumD
  rw [B.baum_eq]

theorem R_sup_D_eq : thompsonJ S ⊔ D = (conjJoin S L ⊓ M) ⊔ pCoreOf 2 H := by
  apply le_antisymm
  · refine (sup_le_sup_right B.R_eq_P_sup_C.le D).trans ?_
    refine sup_le (sup_le (B.P_le_inf_M.trans le_sup_left) ?_) (B.D_le_inf_M.trans le_sup_left)
    rw [B.C_eq_baumD, B.su.O_eq_DU]
    exact le_sup_of_le_right le_sup_left
  · refine sup_le ?_ (B.Q_le_R.trans le_sup_left)
    rw [← B.inf_M_decomp.2.1]
    exact sup_le_sup B.P_le_R le_rfl

theorem conjD_le_normalizer_pCore : conjR D x₀ ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  have h := conjR_mono B.D_le_normalizer_conj_pCore x₀
  rw [← conjR_normalizer, conjR_conjR,
    conjR_eq_of_mem_normalizer (B.S_le_normalizer_pCore B.su.hxsq)] at h
  exact h

theorem conjD_le_normalizer_L₀ (h246 : Lemma246Double) :
    conjR D x₀ ≤ Subgroup.normalizer (conjJoin S L : Set G) :=
  B.conjD_le_normalizer_pCore.trans (h246 G T M H S L B.cs B.cfg.double ⟨n, B.cfg.one_lt, B.hlin⟩)

theorem conjD_le_M : conjR D x₀ ≤ M := by
  intro y hy
  obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hy
  have hdM : d ∈ M := (B.D_le_inf_M hd).2
  exact M.mul_mem (M.mul_mem (M.inv_mem B.x₀_mem_M) hdM) B.x₀_mem_M

theorem conjD_le_normalizer_R : conjR D x₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  have h := conjR_mono B.D_le_normalizer_R x₀
  rwa [← conjR_normalizer, B.conjR_R_x₀] at h

theorem conjD_le_normalizer_RD (h246 : Lemma246Double) :
    conjR D x₀ ≤ Subgroup.normalizer ((thompsonJ S ⊔ D : Subgroup G) : Set G) := by
  intro g hg
  rw [B.R_sup_D_eq, ← conjR_eq_self_iff, conjR_sup, conjR_inf,
    conjR_eq_of_mem_normalizer (B.conjD_le_normalizer_L₀ h246 hg),
    conjR_eq_of_mem_normalizer (Subgroup.le_normalizer (B.conjD_le_M hg)),
    conjR_eq_of_mem_normalizer (B.conjD_le_normalizer_pCore hg)]

theorem S_le_normalizer_RD : S ≤ Subgroup.normalizer ((thompsonJ S ⊔ D : Subgroup G) : Set G) := by
  intro s hs
  rw [B.R_sup_D_eq, ← conjR_eq_self_iff, conjR_sup, conjR_inf,
    conjR_eq_of_mem_normalizer (S_le_normalizer_conjJoin' S L hs),
    conjR_eq_of_mem_normalizer (Subgroup.le_normalizer (B.S_le_M hs)),
    conjR_eq_of_mem_normalizer (B.S_le_normalizer_pCore hs)]

theorem S_le_normalizer_conj_RD :
    S ≤ Subgroup.normalizer ((conjR (thompsonJ S ⊔ D) x₀ : Subgroup G) : Set G) := by
  have h := conjR_mono B.S_le_normalizer_RD x₀
  rw [← conjR_normalizer, conjR_eq_of_mem_normalizer B.su.hxN] at h
  exact h

theorem K_eq : thompsonJ S ⊔ D ⊔ conjR D x₀ =
    (thompsonJ S ⊔ D) ⊔ conjR (thompsonJ S ⊔ D) x₀ := by
  rw [conjR_sup, B.conjR_R_x₀]
  apply le_antisymm
  · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  · exact sup_le le_sup_left (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)

omit [Finite G] B in
theorem R_le_K : thompsonJ S ≤ thompsonJ S ⊔ D ⊔ conjR D x₀ := le_sup_of_le_left le_sup_left

theorem K_le_normalizer_R :
    thompsonJ S ⊔ D ⊔ conjR D x₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
  sup_le (sup_le Subgroup.le_normalizer B.D_le_normalizer_R) B.conjD_le_normalizer_R

theorem S_le_normalizer_K :
    S ≤ Subgroup.normalizer ((thompsonJ S ⊔ D ⊔ conjR D x₀ : Subgroup G) : Set G) := by
  intro s hs
  rw [B.K_eq, ← conjR_eq_self_iff, conjR_sup, conjR_eq_of_mem_normalizer (B.S_le_normalizer_RD hs),
    conjR_eq_of_mem_normalizer (B.S_le_normalizer_conj_RD hs)]

theorem x₀_mem_normalizer_K :
    x₀ ∈ Subgroup.normalizer ((thompsonJ S ⊔ D ⊔ conjR D x₀ : Subgroup G) : Set G) := by
  rw [B.K_eq, ← conjR_eq_self_iff, conjR_sup, conjR_conjR,
    conjR_eq_of_mem_normalizer (B.S_le_normalizer_RD B.su.hxsq), sup_comm]

theorem M₀_le_normalizer_K :
    M₀ ≤ Subgroup.normalizer ((thompsonJ S ⊔ D ⊔ conjR D x₀ : Subgroup G) : Set G) := by
  intro m hm
  by_cases hmS : m ∈ S
  · exact B.S_le_normalizer_K hmS
  · have hs : x₀⁻¹ * m ∈ S :=
      CFSG.QuasithinUnique.inv_mul_mem_of_relIndex_two B.h2 B.hx₀ B.hx₀S hm hmS
    have e : m = x₀ * (x₀⁻¹ * m) := by group
    rw [e]
    exact Subgroup.mul_mem _ B.x₀_mem_normalizer_K (B.S_le_normalizer_K hs)

theorem card_RD : Nat.card ↥(thompsonJ S ⊔ D) = Nat.card ↥(thompsonJ S) * Nat.card ↥D := by
  have h := card_sup_mul_card_inf (A := D) (B := thompsonJ S) B.D_le_normalizer_R
  rw [inf_eq_bot_of_odd_card_of_isPGroup B.cfg.hall.2.1 B.R_isPGroup, Subgroup.card_bot, mul_one,
    sup_comm] at h
  rw [h, mul_comm]

theorem relIndex_R_RD : (thompsonJ S).relIndex (thompsonJ S ⊔ D) = Nat.card ↥D := by
  have h := Subgroup.relIndex_mul_card (H := thompsonJ S) (K := thompsonJ S ⊔ D)
  rw [inf_eq_left.mpr (le_sup_left : thompsonJ S ≤ thompsonJ S ⊔ D), B.card_RD] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h, mul_comm])

theorem relIndex_R_RD_odd : ¬ 2 ∣ (thompsonJ S).relIndex (thompsonJ S ⊔ D) := by
  rw [B.relIndex_R_RD]
  exact B.cfg.hall.2.1.not_two_dvd_nat

theorem relIndex_R_K_odd (h246 : Lemma246Double) :
    ¬ 2 ∣ (thompsonJ S).relIndex (thompsonJ S ⊔ D ⊔ conjR D x₀) := by
  have hN := B.conjD_le_normalizer_RD h246
  have hc := card_sup_mul_card_inf hN
  rw [sup_comm (conjR D x₀) (thompsonJ S ⊔ D), card_conjR, B.card_RD] at hc
  have h1 : (thompsonJ S).relIndex (thompsonJ S ⊔ D ⊔ conjR D x₀) * Nat.card ↥(thompsonJ S) =
      Nat.card ↥(thompsonJ S ⊔ D ⊔ conjR D x₀) := by
    have := Subgroup.relIndex_mul_card (H := thompsonJ S) (K := thompsonJ S ⊔ D ⊔ conjR D x₀)
    rwa [inf_eq_left.mpr R_le_K] at this
  have hRpos : 0 < Nat.card ↥(thompsonJ S) := Nat.card_pos
  rw [← h1] at hc
  have key : (thompsonJ S).relIndex (thompsonJ S ⊔ D ⊔ conjR D x₀) *
      Nat.card ↥(conjR D x₀ ⊓ (thompsonJ S ⊔ D) : Subgroup G) = Nat.card ↥D * Nat.card ↥D := by
    apply Nat.eq_of_mul_eq_mul_left hRpos
    calc Nat.card ↥(thompsonJ S) * ((thompsonJ S).relIndex (thompsonJ S ⊔ D ⊔ conjR D x₀) *
          Nat.card ↥(conjR D x₀ ⊓ (thompsonJ S ⊔ D) : Subgroup G))
        = ((thompsonJ S).relIndex (thompsonJ S ⊔ D ⊔ conjR D x₀) * Nat.card ↥(thompsonJ S)) *
          Nat.card ↥(conjR D x₀ ⊓ (thompsonJ S ⊔ D) : Subgroup G) := by ring
      _ = Nat.card ↥D * (Nat.card ↥(thompsonJ S) * Nat.card ↥D) := hc
      _ = Nat.card ↥(thompsonJ S) * (Nat.card ↥D * Nat.card ↥D) := by ring
  have hodd : Odd (Nat.card ↥D * Nat.card ↥D) := B.cfg.hall.2.1.mul B.cfg.hall.2.1
  rw [← key] at hodd
  exact (Nat.odd_mul.1 hodd).1.not_two_dvd_nat

theorem RD_decomp : ∀ f ∈ thompsonJ S ⊔ D, ∃ r ∈ thompsonJ S, ∃ d ∈ D, f = r * d :=
  fun _ hf => (mem_sup_iff_of_le_normalizer B.D_le_normalizer_R).1 hf

theorem exists_hall (h246 : Lemma246Double) :
    ∃ (r : G) (B' : Subgroup G), r ∈ thompsonJ S ∧ D ≤ B' ∧
      B' ≤ thompsonJ S ⊔ D ⊔ conjR D x₀ ∧ thompsonJ S ⊓ B' = ⊥ ∧
      (∀ f ∈ thompsonJ S ⊔ D ⊔ conjR D x₀, ∃ ρ ∈ thompsonJ S, ∃ b ∈ B', f = ρ * b) ∧
      Odd (Nat.card B') ∧ x₀ * r⁻¹ ∈ Subgroup.normalizer (B' : Set G) := by
  set R := thompsonJ S with hRdef
  set K := R ⊔ D ⊔ conjR D x₀ with hKdef
  set Bo := R ⊔ D with hBodef
  have hRBo : R ≤ Bo := le_sup_left
  have hRK : R ≤ K := R_le_K
  have hBoK : Bo ≤ K := le_sup_left
  have hKN : K ≤ Subgroup.normalizer (R : Set G) := B.K_le_normalizer_R
  have hR2 : IsPGroup 2 R := B.R_isPGroup
  have hRodd : ¬ 2 ∣ R.relIndex K := B.relIndex_R_K_odd h246
  have hBoN : Bo ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer B.D_le_normalizer_R
  have hBoodd : ¬ 2 ∣ R.relIndex Bo := B.relIndex_R_RD_odd
  have hDcomp : IsComplementIn R Bo D :=
    ⟨le_sup_right, by rw [inf_comm]; exact inf_eq_bot_of_odd_card_of_isPGroup B.cfg.hall.2.1 hR2,
      fun f hf => B.RD_decomp f hf⟩
  obtain ⟨B₁, hB₁K, hRB₁, hdec₁⟩ := exists_complement_of_odd hRK hKN hR2 hRodd
  have hB₁'comp : IsComplementIn R Bo (B₁ ⊓ Bo) := by
    refine ⟨inf_le_right, ?_, ?_⟩
    · exact le_bot_iff.1 ((inf_le_inf_left R inf_le_left).trans hRB₁.le)
    · intro f hf
      obtain ⟨r, hr, b, hb, hfb⟩ := hdec₁ f (hBoK hf)
      refine ⟨r, hr, b, ⟨hb, ?_⟩, hfb⟩
      have : b = r⁻¹ * f := by rw [hfb]; group
      rw [this]
      exact Bo.mul_mem (Bo.inv_mem (hRBo hr)) hf
  obtain ⟨r, hr, hDr⟩ := exists_conj_of_complements (F := Bo) hRBo hBoN hR2 hBoodd hB₁'comp.1
    hDcomp.1 hB₁'comp.2.1 hDcomp.2.1 hB₁'comp.2.2 hDcomp.2.2
  set B' := conjR B₁ r with hB'def
  have hrK : r ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hRK hr)
  have hrR : r ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer hr
  have hB₁comp : IsComplementIn R K B₁ := ⟨hB₁K, hRB₁, hdec₁⟩
  have hB'comp : IsComplementIn R K B' := hB₁comp.conj hrK hrR
  have hDB : D ≤ B' := by
    rw [hDr]
    exact conjR_mono inf_le_left r
  have hFr : ∀ m ∈ M₀, ∃ r' ∈ R, conjR B' m = conjR B' r' := by
    intro m hm
    have hmR : m ∈ Subgroup.normalizer (R : Set G) :=
      conjR_eq_self_iff.1 (thompsonJ_normalized (normalizer_of_relIndex_two B.hSM B.h2 hm))
    have hc : IsComplementIn R K (conjR B' m) := hB'comp.conj (B.M₀_le_normalizer_K hm) hmR
    obtain ⟨r', hr', hconj⟩ := exists_conj_of_complements (F := K) hRK hKN hR2 hRodd hB'comp.1
      hc.1 hB'comp.2.1 hc.2.1 hB'comp.2.2 hc.2.2
    exact ⟨r', hr', hconj⟩
  have hNT : ∀ m r' : G, conjR B' m = conjR B' r' →
      m * r'⁻¹ ∈ Subgroup.normalizer (B' : Set G) := by
    intro m r' he
    rw [← conjR_eq_self_iff, conjR_mul, he, conjR_conjR_inv]
  have hBodd : Odd (Nat.card B') := by
    have hcard := hB'comp.card_mul hRK hKN
    have h1 : R.relIndex K * Nat.card R = Nat.card K := by
      have := Subgroup.relIndex_mul_card (H := R) (K := K)
      rwa [inf_eq_left.mpr hRK] at this
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have h2 : R.relIndex K = Nat.card B' :=
      Nat.eq_of_mul_eq_mul_right hRpos (by rw [h1, hcard, mul_comm])
    rw [← h2]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hRodd)
  obtain ⟨r₀, hr₀, he₀⟩ := hFr x₀ B.hx₀
  exact ⟨r₀, B', hr₀, hDB, hB'comp.1, hB'comp.2.1, hB'comp.2.2, hBodd, hNT x₀ r₀ he₀⟩

end S2Base

end CFSG.QuasithinUnique.Lin2
