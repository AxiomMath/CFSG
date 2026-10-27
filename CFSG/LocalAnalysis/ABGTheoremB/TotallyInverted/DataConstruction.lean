module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionConj
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionLemma71

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

namespace DataConstruction

variable {G : Type} [Group G] {σ : Setting G}

theorem conjSub_eq_bot_of_eq_bot {X : Subgroup G} (h : X = ⊥) (g : G) : conjSub g X = ⊥ := by
  rw [h, conjSub_bot]

variable [Finite G] {r : ℕ} {J Q Qs : Subgroup G} {a : G}

open scoped Classical in
theorem lemma71_all (hσ : σ.IsValid) (hT : σ.TIFacts) (hr : r.Prime) (hr2 : r ≠ 2)
    (hti : σ.TotallyInverted r) (hJ : σ.IsLayerComplement J)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) (hQ : QPair σ r J Q Qs)
    (haN : a ∈ Subgroup.normalizer (σ.T : Set G))
    (hcyc : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)) (i : Fin 3) :
    maximals (signalizers (σ.Ns i) σ.C r) =
      if σ.DeltaEpsMinus ∧ r ∣ σ.q then
        {σ.Ps r i ⊔ conjSub (a ^ (i : ℕ)) Q, σ.Ps r i ⊔ conjSub (a ^ (i : ℕ)) Qs}
      else {σ.Ps r i} := by
  have h := maximals_image_conjSub (a ^ (i : ℕ)) (signalizers σ.N σ.C r)
  rw [← signalizers_conjSub, conjSub_pow_N hcyc, conjSub_pow_C haN,
    lemma71_zero hσ hT hr hr2 hti hJ hP₀ hQ, Set.image_pair, conjSub_sup, conjSub_sup,
    conjSub_pow_Ps hcyc] at h
  rw [h]
  split_ifs with hc
  · rfl
  · obtain ⟨h1, h2⟩ := hQ.trivial hc
    rw [h1, h2, conjSub_bot, sup_bot_eq, Set.pair_eq_singleton]

open scoped Classical in
theorem lemma72_all (hσ : σ.IsValid) (hT : σ.TIFacts) (hr : r.Prime) (hr2 : r ≠ 2)
    (hti : σ.TotallyInverted r) (hJ : σ.IsLayerComplement J)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) (hQ : QPair σ r J Q Qs)
    (haN : a ∈ Subgroup.normalizer (σ.T : Set G))
    (hcyc : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)) (i : Fin 3) (R : Subgroup G)
    (hR : IsSylowOf r R σ.C) :
    {U | U ∈ maximals (signalizersPerm (σ.Ns i) σ.T σ.C r) ∧ R ≤ U} =
      if σ.DeltaEpsMinus ∧ r ∣ σ.q then
        {R ⊔ conjSub (a ^ (i : ℕ)) Q ⊔ σ.Ps r i, R ⊔ conjSub (a ^ (i : ℕ)) Qs ⊔ σ.Ps r i}
      else {R ⊔ σ.Ps r i} := by
  have : Fact r.Prime := ⟨hr⟩
  have hR' : IsSylowOf r (conjSub (a ^ (i : ℕ))⁻¹ R) σ.C := by
    have := isSylowOf_conjSub hR (a ^ (i : ℕ))⁻¹
    rwa [conjSub_pow_inv_C haN] at this
  have h := setOf_image_conjSub_ge (a ^ (i : ℕ)) (maximals (signalizersPerm σ.N σ.T σ.C r))
    (conjSub (a ^ (i : ℕ))⁻¹ R)
  rw [conjSub_conjSub_inv, ← maximals_image_conjSub, ← signalizersPerm_conjSub,
    conjSub_pow_N hcyc, conjSub_pow_T haN, conjSub_pow_C haN,
    lemma72_zero hσ hT hr hr2 hti hJ hP₀ hQ hR', Set.image_pair] at h
  rw [h]
  simp only [conjSub_sup, conjSub_conjSub_inv, conjSub_pow_Ps hcyc]
  split_ifs with hc
  · rfl
  · obtain ⟨h1, h2⟩ := hQ.trivial hc
    rw [h1, h2, conjSub_bot, sup_bot_eq, Set.pair_eq_singleton]

end DataConstruction

open DataConstruction

theorem nonempty_data_core {G : Type} [Group G] [Finite G] {σ : Setting G} (hσ : σ.IsValid)
    (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (hJ : ∀ J : Subgroup G, J ≤ σ.L₀ → σ.L₀ = J ⊔ σ.ON →
      J ≤ Subgroup.centralizer (σ.ON : Set G) → σ.N ≤ Subgroup.normalizer (J : Set G) →
        ¬ (σ.q = 9 ∧ σ.height = 1 ∧ Nat.card (J ⊓ σ.ON : Subgroup G) = 3))
    (hA : automizerIndex σ.T = 6) (hV : σ.CorollaryV61) (hT : σ.TIFacts) {r : ℕ}
    (hr : r.Prime) (hdvd : r ∣ Nat.card σ.ON) (hexc : σ.Exceptional r)
    (hti : σ.TotallyInverted r) : Nonempty (Data σ r) := by
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdvd
  obtain ⟨a, haN, ha3, ha1, ha2⟩ := exists_a hσ hA
  have hcyc := xs_cycle hσ ha1 ha2
  obtain ⟨d, hdD, hd2⟩ := hd
  have hd1 := conj_x_of_mem_D hσ hdD
  obtain ⟨J, hJ', hsl⟩ := exists_layerComplement hJ hV
  obtain ⟨hP₀, hP₀inv, hP₀ab⟩ := Ps_zero_facts hσ hV hr hdvd hti
  obtain ⟨Q₀, Qs₀, hQ⟩ := exists_QPair hσ hT hr hr2 hti hJ'
  obtain ⟨P, hPsyl, hPD, hPL⟩ := exists_P hT hr hr2 hti
  exact ⟨{
    prime := hr
    ne_two := hr2
    dvd := hdvd
    exceptional := hexc
    totallyInverted := hti
    a := a
    a_mem := normalizer_T_le_M haN
    a_three := ha3
    a_cycle := hcyc
    d := d
    d_mem := hdD
    d_x := hd1
    d_x₂ := hd2
    M_eq := M_eq hσ hF₀ hT haN ha1 ha2 hdD hd1 hd2
    F₀_sylow := hF₀
    F₀_abelian := hT.F₀_abelian
    F₀_omega := hT.F₀_omega
    L_normal := N_le_normalizer_L hσ hT
    T_le_L := T_le_L hσ
    J := J
    J_le := hJ'.le
    L₀_eq := hJ'.sup_eq
    J_centralizes := hJ'.centralizes
    J_normal := hJ'.normal
    J_inf := Or.inl hJ'.inf_eq
    J_sl2 := fun _ => hsl
    W := oddCoreIn (σ.C ⊓ J)
    W_eq := rfl
    W_cyclic := isCyclic_W hT hJ'
    W_coprime := not_dvd_card_W hti hJ'
    Op_C := pCoreIn_C_eq_bot hT hr hti hJ'
    P_conj := conjSub_Ps hcyc r
    P_abelian := Ps_abelian hcyc hP₀ab
    P_centralized := fun i => pCoreIn_le r (σ.Ns i)
    P_inverted := fun i j hji _ hu => Ps_inverted hcyc hP₀inv i j hji hu
    P_sylow := hP₀
    Q := fun i => conjSub (a ^ (i : ℕ)) Q₀
    Qs := fun i => conjSub (a ^ (i : ℕ)) Qs₀
    Q_trivial := fun hc _ => ⟨conjSub_eq_bot_of_eq_bot (hQ.trivial hc).1 _,
      conjSub_eq_bot_of_eq_bot (hQ.trivial hc).2 _⟩
    Q_le := fun _ => ⟨conjSub_mono hQ.le, conjSub_mono hQ.le_s⟩
    Q_pgroup := fun _ => ⟨isPGroup_conjSub hQ.isPGroup _, isPGroup_conjSub hQ.isPGroup_s _⟩
    Q_C := fun _ => ⟨le_normalizer_conjSub_of_eq (conjSub_pow_C haN _) hQ.normal,
      le_normalizer_conjSub_of_eq (conjSub_pow_C haN _) hQ.normal_s⟩
    Q_conj := fun i => ⟨conjSub_conjSub_pow hcyc hQ.normal i,
      conjSub_conjSub_pow hcyc hQ.normal_s i⟩
    Q_cases := fun hc i => by
      have h := hQ.conj_cases hJ' hP₀.le hc (conjSub_pow_C haN (i : ℕ))
      rw [conjSub_pow_Ps hcyc] at h
      exact h
    P := P
    P_sylowC := hPsyl
    P_D := hPD
    P_L := hPL
    lemma71 := lemma71_all hσ hT hr hr2 hti hJ' hP₀ hQ haN hcyc
    lemma72 := lemma72_all hσ hT hr hr2 hti hJ' hP₀ hQ haN hcyc }⟩

theorem nonempty_data {G : Type} [Group G] [Finite G] {σ : Setting G} (hσ : σ.IsValid)
    (hh : σ.height ≠ 1) (hA : automizerIndex σ.T = 6) (hV : σ.CorollaryV61)
    (hT : σ.TIFacts) {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card σ.ON)
    (hexc : σ.Exceptional r) (hti : σ.TotallyInverted r) : Nonempty (Data σ r) :=
  nonempty_data_core hσ (exists_d_of_height_ne_one hσ hh) (isSylowOf_F₀_of_height_ne_one hσ hh)
    (noExceptionalLayer_of_height_ne_one hh) hA hV hT hr hdvd hexc hti

end CFSG.ABGTheoremB.TotallyInverted
