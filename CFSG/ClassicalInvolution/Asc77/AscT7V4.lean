module

public import CFSG.ClassicalInvolution.Asc77.AscT7V1
public import CFSG.ClassicalInvolution.Asc77.AscT7V3
public import CFSG.ClassicalInvolution.Asc77.AscT7JFrame
import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma
import CFSG.ClassicalInvolution.Asc77.AscT8S26E4
public import CFSG.ClassicalInvolution.Asc77.AscT7FI

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T7V

section Frame

variable {G : Type} [Group G]

@[expose] def FuseFrame (K₃ K₄ : Subgroup G) (z u : G) : Prop :=
  ∃ (R R' : Subgroup G) (b b' y : G),
    IsSylow2In R (ExactLayer.exactCore u K₃) ∧ IsSylow2In R' (ExactLayer.exactCore u K₄) ∧
    Commutes R R' ∧ b ∈ ExactLayer.exactCore u K₃ ∧ b' ∈ ExactLayer.exactCore u K₄ ∧
    b * b = z ∧ b' * b' = z ∧ y ∈ Subgroup.centralizer ({u} : Set G) ∧
    y * z * y⁻¹ = b * b' * u ∧ b * b' * u ≠ z ∧ z * (b * b' * u) = (b * b' * u) * z

variable [Finite G]

theorem FuseFrame.conj {K₃ K₄ : Subgroup G} {z u : G} (hF : FuseFrame K₃ K₄ z u) {c : G}
    (hc₃ : conjSub c K₃ = K₃) (hc₄ : conjSub c K₄ = K₄) (hcz : c * z * c⁻¹ = z) :
    FuseFrame K₃ K₄ z (c * u * c⁻¹) := by
  obtain ⟨R, R', b, b', y, hR, hR', hRR', hb, hb', hbz, hb'z, hy, hyz, hne, hcomm⟩ := hF
  have hcz' : c⁻¹ * z * c = z := by
    have := congrArg (fun x => c⁻¹ * x * c) hcz
    simpa [mul_assoc] using this.symm
  have e₃ : exactCore (c * u * c⁻¹) K₃ = conjSub c (exactCore u K₃) := by
    rw [← exactCore_conjSub, hc₃]
  have e₄ : exactCore (c * u * c⁻¹) K₄ = conjSub c (exactCore u K₄) := by
    rw [← exactCore_conjSub, hc₄]
  refine ⟨conjSub c R, conjSub c R', c * b * c⁻¹, c * b' * c⁻¹, c * y * c⁻¹, ?_, ?_,
    hRR'.conjSub c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₃]; exact hR.conj c
  · rw [e₄]; exact hR'.conj c
  · rw [e₃]; exact conj_mem_conjSub hb
  · rw [e₄]; exact conj_mem_conjSub hb'
  · calc c * b * c⁻¹ * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
      _ = z := by rw [hbz, hcz]
  · calc c * b' * c⁻¹ * (c * b' * c⁻¹) = c * (b' * b') * c⁻¹ := by group
      _ = z := by rw [hb'z, hcz]
  · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hy]
      _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
  · calc c * y * c⁻¹ * z * (c * y * c⁻¹)⁻¹ = c * y * (c⁻¹ * z * c) * y⁻¹ * c⁻¹ := by group
      _ = c * (y * z * y⁻¹) * c⁻¹ := by rw [hcz']; group
      _ = c * (b * b' * u) * c⁻¹ := by rw [hyz]
      _ = c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹) := by group
  · intro h
    apply hne
    have h2 : b * b' * u = c⁻¹ * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) * c := by group
    rw [h2, h, hcz']
  · calc z * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) =
        c * (z * (b * b' * u)) * c⁻¹ := by
          calc z * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹))
              = (c * z * c⁻¹) * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) := by rw [hcz]
            _ = c * (z * (b * b' * u)) * c⁻¹ := by group
      _ = c * ((b * b' * u) * z) * c⁻¹ := by rw [hcomm]
      _ = (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) * z := by
          calc c * ((b * b' * u) * z) * c⁻¹
              = (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) * (c * z * c⁻¹) := by group
            _ = _ := by rw [hcz]

end Frame

section Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem adj_of_twins (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {J J' : Subgroup G}
    (hJ : J ∈ twinSet Ω K) (hJ' : J' ∈ twinSet Ω K) (hne : J' ≠ J) : J' ∈ omegaNbr Ω J := by
  have h1 : KPerp Ω J = twinSet Ω J := T7S22.perp_of_twin h hJ
  have h2 : twinSet Ω J = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz hJ
  have h3 : J' ∈ KPerp Ω J := by rw [h1, h2]; exact hJ'
  rcases h3 with rfl | h3
  · exact absurd rfl hne
  · exact h3

theorem exists_sylow_quad (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) :
    ∃ R₁ R₂ R₃ R₄ : Subgroup G, IsSylow2In R₁ K ∧ IsSylow2In R₂ K' ∧ IsSylow2In R₃ K₃ ∧
      IsSylow2In R₄ K₄ ∧ u₁ ∈ R₁ ∧ u₂ ∈ R₂ ∧ Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ ∧
      Commutes R₁ R₄ ∧ Commutes R₂ R₄ ∧ Commutes R₃ R₄ := by
  obtain ⟨R₁, R₂, R₃, h1, h2, h3, hu₁, hu₂, -, c12, c13, c23⟩ := T7B.exists_sylow_triple h
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK' : K' ∈ Ω := h.std.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz := h.std.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have nK : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have nK₃ : K₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK₄Ω h43.symm hz₃ hz₄
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hPN : (R₁ ⊔ R₂) ⊔ R₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    sup_le (sup_le (h1.1.trans nK) (h2.1.trans nK')) (h3.1.trans nK₃)
  obtain ⟨R₄, h4, hQ⟩ := exists_isPGroup_sup_sylow hP hPN
  have hR₁Q : R₁ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hR₂Q : R₂ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR₃Q : R₃ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans le_sup_left
  have hR₄Q : R₄ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right
  refine ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₄Ω h41.symm hz hz₄ h1.1 h4.1
      (hQ.to_le (sup_le hR₁Q hR₄Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₄Ω h42.symm hz' hz₄ h2.1 h4.1
      (hQ.to_le (sup_le hR₂Q hR₄Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK₃ hK₄Ω h43.symm hz₃ hz₄ h3.1 h4.1
      (hQ.to_le (sup_le hR₃Q hR₄Q))

theorem not_dbarConnected_of_wyl (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (ρ₀ : Rep Ω W) (hρ₀ : ρ₀.K = K) (hμ : MuIsoWylD4 Ω W) :
    ¬ DbarConnected Ω W := by
  intro hconn
  have c : Ctx p f Ω W := T7D.ctx_of_stand h.stand hW
  have hover : ∀ ρ : Rep Ω W, ρ.K ∈ twinSet Ω K := by
    intro ρ
    have := c.mem_dComp_of_connected hconn h.stand.mem ρ.hK ρ₀.hR ρ.hR (hρ₀ ▸ ρ₀.hRK) ρ.hRK
    exact T7S22.dComp_subset_twinSet h this
  have hcomm : ∀ x ∈ muDelta Ω W, ∀ y ∈ muDelta Ω W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hx
    obtain ⟨σ, hσ⟩ := exists_rep_of_mem_muDelta hy
    apply Subtype.ext
    show (x : NQuot (W ⊔ OCW W)) * y = y * x
    rw [← hρ, ← hσ]
    by_cases hK : σ.K = ρ.K
    · rw [c.img_eq_of_K_eq σ ρ hK]
    · exact c.comm_of_omega ρ σ (adj_of_twins h (hover ρ) (hover σ) hK)
  have hcenter : ∀ y ∈ muDelta Ω W, ∀ x : ↥(muGroup Ω W), x * y = y * x := by
    intro y hy x
    have hx : x ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx y hy
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha]
        _ = y * a⁻¹ := by group
  have habel : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    have hy : y ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hcenter y hy x
    | one => simp
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
    | inv a _ ha =>
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * x := by group
  obtain ⟨e⟩ := hμ
  apply s26_coxeterD4_not_comm
  intro u v
  have h1 := habel (e.symm u) (e.symm v)
  calc u * v = e (e.symm u * e.symm v) := by simp
    _ = e (e.symm v * e.symm u) := by rw [h1]
    _ = v * u := by simp

theorem fuseFrame_w (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ a a' : G, a ∈ K ∧ a' ∈ K' ∧ orderOf a = 4 ∧ orderOf a' = 4 ∧ a * a' = a' * a ∧
      FuseFrame K₃ K₄ z (a * a') := by
  classical
  have hs := h.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, c14, c24, c34⟩ :=
    exists_sylow_quad h hK₄ h41 h42 h43
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := exists_W_of_isPGroup hp hq hΩ hP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := T7D.exists_rep hp hq hΩ hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := T7D.exists_rep hp hq hΩ hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := T7D.exists_rep hp hq hΩ hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := T7D.exists_rep hp hq hΩ hW hK₄Ω h4 hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hρR : ∀ i, (ρ i).R = ![R₁, R₂, R₃, R₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀R, hρ₁R, hρ₂R, hρ₃R]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hs.hK'
    · exact hs.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact adj_of_twins hs (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    not_dbarConnected_of_wyl hs hW ρ₀ hρ₀K (hμ W hW)
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hs.stand hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hR⟩ := c.fuse_frame hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hρ0R : (ρ 0).R = R₁ := hρ₀R
  have hρ1R : (ρ 1).R = R₂ := hρ₁R
  have hρ2R : (ρ 2).R = R₃ := hρ₂R
  have hρ3R : (ρ 3).R = R₄ := hρ₃R
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (inf_W_of_mem_D hp hq hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hzρ i) (hg i).1.1 (hg i).2
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hzρ 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hu0W : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hu2 : (g 0 * g 1) * (g 0 * g 1) = 1 := by
    calc (g 0 * g 1) * (g 0 * g 1) = (g 0 * g 0) * (g 1 * g 1) := by
          rw [mul_assoc, ← mul_assoc (g 1), ← hcomm _ (hgW 0) _ (hgW 1)]; group
      _ = 1 := by rw [hgsq 0, hgsq 1]; exact (hzρ 0).sq
  have hc2 : IsPGroup 2 (Subgroup.zpowers (g 0 * g 1)) := isPGroup_zpowers_of_sq_eq_one hu2
  have hg0R₁ : g 0 ∈ R₁ := by simpa [hρ0R] using hgR 0
  have hg1R₂ : g 1 ∈ R₂ := by simpa [hρ1R] using hgR 1
  have hR₃C : R₃ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c13 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c23 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hR₄C : R₄ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c14 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c24 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hcK₃ : g 0 * g 1 ∈ trivialOnQuot K₃ :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hK₃).mpr ⟨R₃, h3, hR₃C⟩
  have hcK₄ : g 0 * g 1 ∈ trivialOnQuot K₄ :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hK₄Ω).mpr ⟨R₄, h4, hR₄C⟩
  have hex₃ : IsSylow2In R₃ (exactCore (g 0 * g 1) K₃) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK₃ hcK₃).mpr ⟨h3, hR₃C⟩
  have hex₄ : IsSylow2In R₄ (exactCore (g 0 * g 1) K₄) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK₄Ω hcK₄).mpr ⟨h4, hR₄C⟩
  have hg2R₃ : g 2 ∈ R₃ := by simpa [hρ2R] using hgR 2
  have hg3R₄ : g 3 ∈ R₄ := by simpa [hρ3R] using hgR 3
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hr₂R : (ρ 2).r ∈ R₃ := by simpa [hρ2R] using (ρ 2).hr
  have hyC : y ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR₃C hr₂R) (hR σ.hr))
      (Subgroup.inv_mem _ (hR₃C hr₂R))
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have htz : t ≠ z := by
    intro h'
    have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
    have hperp : σ.K ∈ KPerp Ω K := by rw [hs.perp]; exact hσK
    rcases hperp with h'' | h''
    · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
    · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm
  have hperm : g 0 * g 1 * g 2 * g 3 = g 2 * g 3 * (g 0 * g 1) := by
    calc g 0 * g 1 * g 2 * g 3 = (g 0 * g 1) * (g 2 * g 3) := by group
      _ = (g 2 * g 3) * (g 0 * g 1) := hcomm _ hu0W _ (W.mul_mem (hgW 2) (hgW 3))
  refine ⟨g 0, g 1, by simpa [hρ0K] using (hg 0).1.1, by simpa [hρ1K] using (hg 1).1.1,
    (hg 0).2, (hg 1).2, hcomm _ (hgW 0) _ (hgW 1), ?_⟩
  refine ⟨R₃, R₄, g 2, g 3, y, hex₃, hex₄, c34, hex₃.1 hg2R₃, hex₄.1 hg3R₄, hgsq 2, hgsq 3,
    hyC, ?_, ?_, ?_⟩
  · rw [hyz, hrel, hperm]
  · rw [← hperm, ← hrel]
    exact htz
  · exact hcomm _ hzW _ (W.mul_mem (W.mul_mem (hgW 2) (hgW 3)) hu0W)

theorem hyp22Fuse_of_c22_4 (hμ : C22_4 p f) : Hyp22Fuse p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ h41 h42 h43
  have hs := h.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨a, a', ha, ha', ha4, ha'4, haa', hF⟩ :=
    fuseFrame_w h hK₄ h41 h42 h43 (hμ G Ω K K' K₃ z u₁ u₂ u₃ h)
  have hKK' : K ≤ trivialOnQuot K' := T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz hz'
  have hK'K : K' ≤ trivialOnQuot K := T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c, hc, hconj⟩ := exists_conj_pair hp hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K ha ha'
    hs.hu₁.1 hs.hu₂.1 ha4 ha'4 hs.hu₁.2 hs.hu₂.2 haa' hs.comm₁₂
  have nK₃ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hs.hK₃K.symm hz hz₃
  have nK₃' : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hs.hK₃K'.symm hz' hz₃
  have nK₄ : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK₄' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have hc₃ : conjSub c K₃ = K₃ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₃ nK₃' hc)
  have hc₄ : conjSub c K₄ = K₄ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₄ nK₄' hc)
  have hcz : c * z * c⁻¹ = z := by
    have hle : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz'.commute_of_mem hx).symm
    have h1 : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    rw [h1]
    group
  have := hF.conj hc₃ hc₄ hcz
  rw [hconj] at this
  exact this

end Setting

end T7V

end CFSG.ClassicalInvolution.Asc77
