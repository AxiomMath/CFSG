module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1Setup

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

theorem hNQ_univ :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G) :=
  hS.normalizer_E_le fun w => ⟨0, hZ 0, w, hZ w, zero_add w⟩

theorem lin_eq_of_mem_D {d : G} (hd : d ∈ Dsub t Q) (v : V6) : lin ψ d v = v := by
  rw [hS.rad.lin_eq_iff (hS.hNQ_univ hZ hd.1)]
  have h := mem_centralizer_iff.1 hd.2 (ψ v) (hS.rad.ψ_mem v)
  rw [← h, mul_inv_cancel_right]

theorem affF_D {d : G} (hd : d ∈ Dsub t Q) (v : V6) : affF t ψ d v = tauD t ψ d + v := by
  rw [hS.affF_eq_add (hS.hNQ_univ hZ) hd.1, hS.lin_eq_of_mem_D hZ hd, tauD]

theorem conj_t_D {d : G} (hd : d ∈ Dsub t Q) : d * t * d⁻¹ = t * ψ (tauD t ψ d) := by
  have h := hS.t_affF (hS.hNQ_univ hZ) hd.1 0
  rw [hS.rad.ψ_zero, mul_one] at h
  rw [tauD, ← h]

theorem tauD_mul {d e : G} (hd : d ∈ Dsub t Q) (he : e ∈ Dsub t Q) :
    tauD t ψ (d * e) = tauD t ψ d + tauD t ψ e := by
  rw [tauD, hS.affF_mul (hS.hNQ_univ hZ) hd.1 he.1, hS.affF_D hZ hd, ← tauD]

omit hZ in
theorem E_le_D : (Q ⊔ zpowers t : Subgroup G) ≤ Dsub t Q := fun _ hx =>
  ⟨le_normalizer hx, mem_centralizer_iff.2 fun _ hy => hS.E_comm (mem_sup_left hy) hx⟩

theorem tauD_eq_zero_iff {d : G} (hd : d ∈ Dsub t Q) :
    tauD t ψ d = 0 ↔ d ∈ (Q ⊔ zpowers t : Subgroup G) := by
  rw [← hS.affF_eq_self_iff (hS.hNQ_univ hZ) hd.1]
  constructor
  · intro h v
    rw [hS.affF_D hZ hd, h, zero_add]
  · intro h
    have := h 0
    rwa [hS.affF_D hZ hd, add_zero] at this

omit hZ in
theorem conj_mem_D {x : G} (hx : x ∈ P) {d : G} (hd : d ∈ Dsub t Q) : x * d * x⁻¹ ∈ Dsub t Q := by
  have hxN := hS.P_le_normalizer_E hx
  have hxQ := hS.rad.P_le_normalizer hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hd.1)
    (Subgroup.inv_mem _ hxN), mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : x⁻¹ * y * x ∈ Q := by
    have := (mem_normalizer_iff.1 (inv_mem hxQ) y).1 hy
    simpa using this
  have h := mem_centralizer_iff.1 hd.2 _ hy'
  calc y * (x * d * x⁻¹) = x * ((x⁻¹ * y * x) * d) * x⁻¹ := by group
    _ = x * (d * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
    _ = x * d * x⁻¹ * y := by group

theorem tauD_conj {x : G} (hx : x ∈ P) {d : G} (hd : d ∈ Dsub t Q) :
    tauD t ψ (x * d * x⁻¹) = lin ψ x (tauD t ψ d) := by
  have h1 := hS.conj_t_D hZ (hS.conj_mem_D hx hd)
  have hxt : x⁻¹ * t * x = t := by
    rw [mul_assoc, ← hS.commute_of_mem_P hx, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : x * d * x⁻¹ * t * (x * d * x⁻¹)⁻¹ = t * (x * ψ (tauD t ψ d) * x⁻¹) := by
    calc x * d * x⁻¹ * t * (x * d * x⁻¹)⁻¹ = x * (d * (x⁻¹ * t * x) * d⁻¹) * x⁻¹ := by group
      _ = x * (d * t * d⁻¹) * x⁻¹ := by rw [hxt]
      _ = x * t * x⁻¹ * (x * ψ (tauD t ψ d) * x⁻¹) := by rw [hS.conj_t_D hZ hd]; group
      _ = t * (x * ψ (tauD t ψ d) * x⁻¹) := by
          rw [hS.commute_of_mem_P hx, mul_inv_cancel_right]
  rw [h2, ← hS.rad.ψ_lin (hS.rad.P_le_normalizer hx)] at h1
  exact (hS.rad.ψ_inj (mul_left_cancel h1)).symm

@[expose] noncomputable def linN :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →* Equiv.Perm V6 :=
  hS.rad.linHom.comp (inclusion (hS.hNQ_univ hZ))

theorem linN_apply (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    hS.linN hZ g v = lin ψ g v := rfl

theorem mem_D_iff_linN {g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)} :
    hS.linN hZ g = 1 ↔ (g : G) ∈ Dsub t Q := by
  constructor
  · intro h
    refine ⟨g.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨v, rfl⟩ := hS.rad.mem_ψ y hy
    have h1 : lin ψ g v = v := by
      have := congrArg (fun σ : Equiv.Perm V6 => σ v) h
      simpa [hS.linN_apply hZ] using this
    rw [hS.rad.lin_eq_iff (hS.hNQ_univ hZ g.2)] at h1
    calc ψ v * g = g * ψ v * (g : G)⁻¹ * g := by rw [h1]
      _ = g * ψ v := by group
  · intro hd
    exact Equiv.ext fun v => hS.lin_eq_of_mem_D hZ hd v

theorem card_D_mul_card_linN [Finite G] :
    Nat.card (Dsub t Q) * Nat.card (hS.linN hZ).range =
      Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) := by
  have hker : Nat.card (hS.linN hZ).ker = Nat.card (Dsub t Q) := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g.1.1, (hS.mem_D_iff_linN hZ).1
      (MonoidHom.mem_ker.1 g.2)⟩) ⟨fun g h e => ?_, fun x => ?_⟩)
    · simp only [Subtype.mk.injEq] at e
      exact Subtype.ext (Subtype.ext e)
    · exact ⟨⟨⟨x, x.2.1⟩, MonoidHom.mem_ker.2 ((hS.mem_D_iff_linN hZ).2 x.2)⟩, rfl⟩
  rw [← hker, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_normalizer_E_univ [Finite G] :
    Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) = 64 * (2 * (2 * Nat.card P)) := by
  rw [hS.card_normalizer_E, hS.card_K]
  have : Nat.card (Zset t Q ψ) = 64 := by
    have hset : Zset t Q ψ = Set.univ := Set.eq_univ_of_forall hZ
    rw [hset, Nat.card_univ, Nat.card_eq_fintype_card]
    simp
  rw [this]

omit hS hZ in
theorem plus_gen0_facts : (∀ x < 64, bmulVec 6 6 (genRows .plus 0)
    (bmulVec 6 6 (genRows .plus 0) (bmulVec 6 6 (genRows .plus 0) x)) = x) ∧
    bmulVec 6 6 (genRows .plus 0) 1 = 1 ∧ bmulVec 6 6 (genRows .plus 0) 2 ≠ 2 := by
  refine ⟨?_, by decide, by decide⟩
  have h : (List.range 64).all (fun x => bmulVec 6 6 (genRows .plus 0)
      (bmulVec 6 6 (genRows .plus 0) (bmulVec 6 6 (genRows .plus 0) x)) == x) = true := by
    decide
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem tauD_surjective [Finite G] (v : V6) : ∃ d ∈ Dsub t Q, tauD t ψ d = v := by
  classical
  have hadd : ∀ w w', (∃ d ∈ Dsub t Q, tauD t ψ d = w) → (∃ d ∈ Dsub t Q, tauD t ψ d = w') →
      ∃ d ∈ Dsub t Q, tauD t ψ d = w + w' := by
    rintro w w' ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
    exact ⟨d * e, mul_mem hd he, hS.tauD_mul hZ hd he⟩
  have hzero : ∃ d ∈ Dsub t Q, tauD t ψ d = 0 :=
    ⟨1, one_mem _, (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)⟩
  by_cases hS0 : ∃ d ∈ Dsub t Q, tauD t ψ d ≠ 0
  · obtain ⟨d₀, hd₀, hne⟩ := hS0
    have hall : ∀ w, qfV ε w = qfV ε (tauD t ψ d₀) → ∃ d ∈ Dsub t Q, tauD t ψ d = w := by
      intro w hw
      by_cases hw0 : w = 0
      · exact hw0 ▸ hzero
      obtain ⟨x, hx, hxw⟩ := hS.rad.exists_lin_eq hne hw0 hw.symm
      exact ⟨x * d₀ * x⁻¹, hS.conj_mem_D hx hd₀, by rw [hS.tauD_conj hZ hx hd₀, hxw]⟩
    rcases qfV_cases ε (tauD t ψ d₀) with h0 | h1
    · obtain ⟨u, hu, hu'⟩ := sum_zeroSet ε v
      have := hadd u (u + v) (hall u (hu.trans h0.symm)) (hall _ (hu'.trans h0.symm))
      rwa [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
    · obtain ⟨u, hu, hu'⟩ := sum_oneSet ε v
      have := hadd u (u + v) (hall u (hu.trans h1.symm)) (hall _ (hu'.trans h1.symm))
      rwa [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
  · exfalso
    push Not at hS0
    set E : Subgroup G := Q ⊔ zpowers t
    have hcardD : Nat.card (Dsub t Q) = 128 := by
      rw [← hS.card_E]
      exact le_antisymm (Subgroup.card_le_of_le fun d hd =>
        (hS.tauD_eq_zero_iff hZ hd).1 (hS0 d hd)) (Subgroup.card_le_of_le (hS.E_le_D))
    set X := (hS.linN hZ).range
    have hcardX : Nat.card X = 64 * oBound ε := by
      have h1 : Nat.card (Dsub t Q) * Nat.card X = _ := hS.card_D_mul_card_linN hZ
      rw [hcardD, hS.card_normalizer_E_univ hZ, hS.rad.card_P] at h1
      have h2 := oBound_even ε
      omega
    have hob : 0 < oBound ε := by cases ε <;> decide
    by_cases horth : X ≤ orthGroup ε
    · have := (Subgroup.card_le_of_le horth).trans (card_orthGroup_le ε)
      omega
    ·
      obtain ⟨σ, hσX, hσo⟩ := Set.not_subset.1 horth
      obtain ⟨g, rfl⟩ := hσX
      have hglin : hS.linN hZ g ∈ linGroup := hS.rad.linHom_mem_linGroup _
      obtain ⟨v₁, hv₁⟩ : ∃ v, qfV ε (lin ψ g v) ≠ qfV ε v := by
        by_contra hcon
        push Not at hcon
        exact hσo ⟨hglin, hcon⟩
      have hPN : ∀ x ∈ P, ∃ σ ∈ X, ∀ v, σ v = lin ψ x v := fun x hx =>
        ⟨hS.linN hZ ⟨x, hS.P_le_normalizer_E hx⟩, ⟨_, rfl⟩, fun v => rfl⟩
      have he₀ : (Pi.single 0 1 : V6) ≠ 0 := fun h => by
        have := congrFun h 0
        simp at this
      have hte₀ : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
      have hqe₀ : qfV ε (Pi.single 0 1 : V6) = 0 := by
        rw [hte₀, qfV_toVec ε (by norm_num), qfB_one]
        rfl
      have hl0 : lin ψ g (0 : V6) = 0 := map_zero_of_mem_linGroup hglin
      have hv0 : v₁ ≠ 0 := fun h => hv₁ (by rw [h, hl0])
      have hu0 : lin ψ g v₁ ≠ 0 := fun h =>
        hv0 ((hS.linN hZ g).injective (h.trans hl0.symm))
      have hN : ∀ x ∈ P, x ∈ normalizer (E : Set G) := fun x hx => hS.P_le_normalizer_E hx
      have hlinN : ∀ (x : normalizer (E : Set G)) (w : V6), hS.linN hZ x w = lin ψ x w :=
        fun _ _ => rfl
      have htrans : ∀ w : V6, w ≠ 0 → ∃ σ ∈ X, σ (Pi.single 0 1) = w := by
        intro w hw0
        rcases qfV_cases ε w with hw | hw
        · obtain ⟨x, hx, hxw⟩ := hS.rad.exists_lin_eq he₀ hw0 (hqe₀.trans hw.symm)
          exact ⟨hS.linN hZ ⟨x, hN x hx⟩, ⟨_, rfl⟩, hxw⟩
        · rcases qfV_cases ε v₁ with h0 | h1
          · have hq1 : qfV ε (lin ψ g v₁) = 1 :=
              (qfV_cases ε _).resolve_left fun h => hv₁ (h.trans h0.symm)
            obtain ⟨x₁, hx₁, hx₁v⟩ := hS.rad.exists_lin_eq he₀ hv0 (hqe₀.trans h0.symm)
            obtain ⟨x₂, hx₂, hx₂w⟩ := hS.rad.exists_lin_eq hu0 hw0 (hq1.trans hw.symm)
            refine ⟨hS.linN hZ (⟨x₂, hN x₂ hx₂⟩ * g * ⟨x₁, hN x₁ hx₁⟩), ⟨_, rfl⟩, ?_⟩
            simp only [map_mul, Equiv.Perm.mul_apply, hlinN]
            rw [hx₁v, hx₂w]
          · have hq0 : qfV ε (lin ψ g v₁) = 0 :=
              (qfV_cases ε _).resolve_right fun h => hv₁ (h.trans h1.symm)
            obtain ⟨x₁, hx₁, hx₁v⟩ := hS.rad.exists_lin_eq he₀ hu0 (hqe₀.trans hq0.symm)
            obtain ⟨x₂, hx₂, hx₂w⟩ := hS.rad.exists_lin_eq hv0 hw0 (h1.trans hw.symm)
            refine ⟨hS.linN hZ (⟨x₂, hN x₂ hx₂⟩ * g⁻¹ * ⟨x₁, hN x₁ hx₁⟩), ⟨_, rfl⟩, ?_⟩
            simp only [map_mul, map_inv, Equiv.Perm.mul_apply, hlinN]
            rw [hx₁v]
            have : (hS.linN hZ g)⁻¹ (lin ψ g v₁) = v₁ := by
              rw [← hlinN g v₁, perm_inv_apply]
            rw [this, hx₂w]
      have horb : Nat.card (MulAction.orbit X (Pi.single 0 1 : V6)) = 63 := by
        have e : MulAction.orbit X (Pi.single 0 1 : V6) ≃ {w : V6 // w ≠ 0} :=
          { toFun := fun w => ⟨w.1, by
              obtain ⟨σ, hσ⟩ := w.2
              intro h
              have hσlin : (σ : Equiv.Perm V6) ∈ linGroup := by
                obtain ⟨g', hg'⟩ := σ.2
                rw [← hg']
                exact hS.rad.linHom_mem_linGroup _
              have h1 : (σ : Equiv.Perm V6) (Pi.single 0 1) = (σ : Equiv.Perm V6) 0 := by
                rw [map_zero_of_mem_linGroup hσlin, ← h]
                exact hσ
              exact he₀ ((σ : Equiv.Perm V6).injective h1)⟩
            invFun := fun w => ⟨w.1, by
              obtain ⟨σ, hσX, hσ⟩ := htrans w.1 w.2
              exact ⟨⟨σ, hσX⟩, hσ⟩⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        simp
      have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X (Pi.single 0 1 : V6))
      rw [Nat.card_prod, horb, hcardX] at hos
      cases ε
      ·
        have hstab : Nat.card (MulAction.stabilizer X (Pi.single 0 1 : V6)) = 40960 := by
          simp only [oBound] at hos
          omega
        obtain ⟨hcube, hfix, hmove⟩ := plus_gen0_facts
        set σ₃ := hS.linN hZ ⟨p 0, hN _ (hS.rad.p_mem 0)⟩
        have hσ₃ : ∀ w, σ₃ w = genMat .plus 0 *ᵥ w := fun w => hS.rad.lin_p 0 w
        have hσ₃e : σ₃ (Pi.single 0 1) = Pi.single 0 1 := by
          rw [hσ₃, hte₀, genMat, mulVec_toVec, hfix]
        have hσ₃3 : σ₃ ^ 3 = 1 := Equiv.ext fun w => by
          rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ₃,
            hσ₃, hσ₃, ← toVec_vecBits w, genMat, mulVec_toVec, mulVec_toVec, mulVec_toVec,
            hcube _ (vecBits_lt w)]
          rfl
        have hσ₃1 : σ₃ ≠ 1 := fun h => by
          have h2 := congrArg (fun τ : Equiv.Perm V6 => τ (toVec 6 2)) h
          simp only [hσ₃, genMat, mulVec_toVec, Equiv.Perm.coe_one, id] at h2
          exact hmove (toVec_injective (bmulVec_lt _ _) (by norm_num) h2)
        let s : MulAction.stabilizer X (Pi.single 0 1 : V6) := ⟨⟨σ₃, ⟨_, rfl⟩⟩, hσ₃e⟩
        have hs3 : orderOf s = 3 := by
          refine orderOf_eq_prime ?_ ?_
          · exact Subtype.ext (Subtype.ext hσ₃3)
          · intro h
            exact hσ₃1 (congrArg (fun z : MulAction.stabilizer X (Pi.single 0 1 : V6) =>
              ((z : X) : Equiv.Perm V6)) h)
        have := orderOf_dvd_natCard s
        rw [hs3, hstab] at this
        norm_num at this
      ·
        simp only [oBound] at hos
        omega

@[expose] noncomputable def tauHom : Dsub t Q →* Multiplicative V6 where
  toFun d := Multiplicative.ofAdd (tauD t ψ d)
  map_one' := by
    change Multiplicative.ofAdd (tauD t ψ 1) = 1
    rw [(hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)]
    rfl
  map_mul' d e := by
    rw [Subgroup.coe_mul, hS.tauD_mul hZ d.2 e.2]
    rfl

theorem card_D [Finite G] : Nat.card (Dsub t Q) = 8192 := by
  have hker : Nat.card (hS.tauHom hZ).ker = 128 := by
    rw [← hS.card_E]
    refine Nat.card_congr (Equiv.ofBijective (fun d => ⟨d.1.1, (hS.tauD_eq_zero_iff hZ d.1.2).1
      (by
        have h1 : Multiplicative.ofAdd (tauD t ψ d.1.1) = 1 := MonoidHom.mem_ker.1 d.2
        exact congrArg Multiplicative.toAdd h1)⟩)
      ⟨fun d e h => ?_, fun x => ?_⟩)
    · simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    · refine ⟨⟨⟨x, hS.E_le_D x.2⟩, MonoidHom.mem_ker.2 ?_⟩, rfl⟩
      change Multiplicative.ofAdd (tauD t ψ x) = 1
      rw [(hS.tauD_eq_zero_iff hZ (hS.E_le_D x.2)).2 x.2]
      rfl
  have hrange : (hS.tauHom hZ).range = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨d, hd, hdv⟩ := hS.tauD_surjective hZ (Multiplicative.toAdd v)
    exact ⟨⟨d, hd⟩, by change Multiplicative.ofAdd (tauD t ψ d) = v; rw [hdv]; rfl⟩
  have h := Subgroup.card_mul_index (hS.tauHom hZ).ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, hker] at h
  rw [← h, Nat.card_eq_fintype_card]
  rfl

omit hZ in
theorem mem_Q_of_mem_P {x : G} (hx : x ∈ P) (hc : x ∈ centralizer (Q : Set G)) : x ∈ Q := by
  have h : x ∈ Q ⊔ zpowers t := by
    rw [← hS.shape.centralizer_eq]
    exact ⟨hS.shape.le_centralizer (hS.rad.P_le_L hx), hc⟩
  obtain ⟨q, hq, h1 | h1⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 h
  · exact h1 ▸ hq
  · exfalso
    apply hS.shape.not_mem
    have h2 : q⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hS.rad.Q_le_L hq)) (hS.rad.P_le_L hx)
    rwa [h1, ← mul_assoc, inv_mul_cancel, one_mul] at h2

omit hZ in
theorem mem_Q_of_mem_K {x : G} (hx : x ∈ P ⊔ zpowers x₀) (hc : x ∈ centralizer (Q : Set G)) :
    x ∈ Q := by
  have hSp := hS.inputs.setting.shape
  have h : x ∈ Q ⊔ zpowers t := by
    rw [← hS.shape.centralizer_eq]
    exact ⟨hS.K_le_centralizer hx, hc⟩
  obtain ⟨q, hq, h1 | h1⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 h
  · exact h1 ▸ hq
  · exfalso
    apply hSp.not_mem
    have h2 : q⁻¹ * x ∈ H₀ := H₀.mul_mem (H₀.inv_mem (hSp.L_le (hS.rad.Q_le_L hq)))
      (hS.K_le_H₀ hx)
    rwa [h1, ← mul_assoc, inv_mul_cancel, one_mul] at h2

omit hZ in
@[expose] noncomputable def linK : (P ⊔ zpowers x₀ : Subgroup G) →* Equiv.Perm V6 :=
  hS.rad.linHom.comp (inclusion hS.K_le_normalizer_Q)

omit hZ in
theorem card_linK [Finite G] :
    64 * Nat.card hS.linK.range = Nat.card (P ⊔ zpowers x₀ : Subgroup G) := by
  have hker : Nat.card hS.linK.ker = 64 := by
    rw [← hS.rad.card_Q]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.1, hS.mem_Q_of_mem_K x.1.2
      (mem_centralizer_iff.2 fun y hy => ?_)⟩) ⟨fun x y h => ?_, fun q => ?_⟩)
    · obtain ⟨v, rfl⟩ := hS.rad.mem_ψ y hy
      have h1 : lin ψ x.1.1 v = v := by
        have := congrArg (fun σ : Equiv.Perm V6 => σ v) (MonoidHom.mem_ker.1 x.2)
        exact this
      rw [hS.rad.lin_eq_iff (hS.K_le_normalizer_Q x.1.2)] at h1
      calc ψ v * x.1.1 = x.1.1 * ψ v * (x.1.1)⁻¹ * x.1.1 := by rw [h1]
        _ = x.1.1 * ψ v := by group
    · simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    · have hqK : (q : G) ∈ P ⊔ zpowers x₀ := mem_sup_left (hS.rad.U_le_P (hS.rad.Q_le_U q.2))
      exact ⟨⟨⟨q, hqK⟩, MonoidHom.mem_ker.2 (Equiv.ext fun v => hS.rad.lin_of_mem_Q q.2 v)⟩, rfl⟩
  have h := Subgroup.card_mul_index hS.linK.ker
  rw [Subgroup.index_ker, hker] at h
  exact h

end SetupX

end CFSG.EvenSmallLie.OmegaEight.SplitIn
