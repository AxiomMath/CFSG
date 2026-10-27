module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverNorm

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

theorem center_eq_bot_of_borelFacts (hperf : commutator K = ⊤)
    (hZ : IsPGroup 2 (Subgroup.center K)) {u : K}
    (hu : ∀ s ∈ Subgroup.center K, s * s = 1 → s = 1 ∨ s = u) (Q : Sylow 2 K)
    (hBF : BenderBorelFacts (K ⧸ Subgroup.center K) (centralImage (Q : Subgroup K)))
    {w₀ : K} (hw₀Q : w₀ ∈ (Q : Subgroup K)) (hw₀c : ∀ q ∈ (Q : Subgroup K), Commute q w₀)
    (hw₀Z : w₀ ∉ Subgroup.center K) : Subgroup.center K = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZQ : Subgroup.center K ≤ (Q : Subgroup K) := hZ.le_sylow_of_normal Q
  obtain ⟨D, hDodd, hDN, -, htrans, hforms⟩ := hBF.torus
  have hWQ : ∀ x ∈ centerPreimage (Q : Subgroup K), x ∈ (Q : Subgroup K) ∧
      ∀ q ∈ (Q : Subgroup K), Commute q x :=
    fun x hx => centerPreimage_le hZQ hDN htrans hw₀Q hw₀c hw₀Z hx
  set W := centerPreimage (Q : Subgroup K) with hW
  have hWcomm : ∀ a b : W, a * b = b * a := fun a b =>
    Subtype.ext ((hWQ b b.2).2 a (hWQ a a.2).1).eq
  have hDW : ∀ d ∈ D, ∀ w ∈ W, liftConj d w ∈ W := fun d hd w hw =>
    mem_centerPreimage_iff.mpr (by
      rw [mk_liftConj]
      exact inCenterOf_conj (hDN hd) (mem_centerPreimage_iff.mp hw))
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hWcomm }
  let _ : MulDistribMulAction D W := liftConjAction D W hDW
  let _ : Fintype D := Fintype.ofFinite D
  have hsmul : ∀ (d : D) (w : W),
      ((d • w : W) : K) = liftConj (d : K ⧸ Subgroup.center K) w := fun _ _ => rfl
  have hNZ : ∀ w : W, (actNorm D W w : K) ∈ Subgroup.center K := fun w =>
    mem_center_of_forall_conj_eq htrans hBF.center_card (actNorm D W w).2 fun d hd => by
      rw [← mk_liftConj, ← hsmul ⟨d, hd⟩, smul_actNorm]
  have hNpow : ∀ w : W, (w : K) ∈ Subgroup.center K → actNorm D W w = w ^ Fintype.card D :=
    fun w hw => actNorm_of_forall_smul_eq fun d => Subtype.ext (by
      rw [hsmul, liftConj_of_mem_center _ hw])
  let nm : K → K := fun x => if h : x ∈ W then (actNorm D W ⟨x, h⟩ : K) else 1
  have hnm : ∀ x (h : x ∈ W), nm x = actNorm D W ⟨x, h⟩ := fun x h => by simp [nm, h]
  have hnm_mul : ∀ x ∈ W, ∀ y ∈ W, nm (x * y) = nm x * nm y := by
    intro x hx y hy
    rw [hnm _ (W.mul_mem hx hy), hnm x hx, hnm y hy]
    exact congrArg Subtype.val (map_mul (actNorm D W) ⟨x, hx⟩ ⟨y, hy⟩)
  have hnm_one : nm 1 = 1 := by
    rw [hnm 1 W.one_mem]
    exact congrArg Subtype.val (map_one (actNorm D W))
  have hnm_conj : ∀ d ∈ D, ∀ x ∈ W, nm (liftConj d x) = nm x := by
    intro d hd x hx
    rw [hnm _ (hDW d hd x hx), hnm x hx]
    exact congrArg Subtype.val (actNorm_smul (⟨d, hd⟩ : D) (⟨x, hx⟩ : W))
  have hout : ∀ a ∈ centralImage (Q : Subgroup K), Quotient.out a ∈ (Q : Subgroup K) :=
    fun a ha => (mk_mem_centralImage_iff hZQ).mp (by rwa [QuotientGroup.out_eq'])
  have hcomW : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), ⁅a, b⁆ ∈ W := fun a ha b hb =>
    mem_centerPreimage_iff.mpr (by
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      exact hBF.commutator_central _ (Subgroup.mem_map_of_mem _ ha) _
        (Subgroup.mem_map_of_mem _ hb))
  have hconj : ∀ a ∈ (Q : Subgroup K), ∀ w ∈ W, a * w * a⁻¹ = w := fun a ha w hw => by
    rw [((hWQ w hw).2 a ha).eq, mul_inv_cancel_right]
  have hmul_left : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), ∀ c ∈ (Q : Subgroup K),
      ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
    intro a ha b hb c hc
    have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hconj a ha _ (hcomW b hb c hc)]
  have hmul_right : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), ∀ c ∈ (Q : Subgroup K),
      ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
    intro a ha b hb c hc
    have h1 : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1, hconj b hb _ (hcomW a ha c hc)]
  have hsq : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), nm ⁅a, b⁆ * nm ⁅a, b⁆ = 1 := by
    intro a ha b hb
    have haa : a * a ∈ W := mem_centerPreimage_iff.mpr (by
      rw [QuotientGroup.mk_mul]
      exact hBF.sq_central _ (Subgroup.mem_map_of_mem _ ha))
    rw [← hnm_mul _ (hcomW a ha b hb) _ (hcomW a ha b hb), ← hmul_left a ha a ha b hb,
      commutatorElement_eq_one_iff_mul_comm.mpr ((hWQ _ haa).2 b hb).symm.eq, hnm_one]
  have hval : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), nm ⁅a, b⁆ = 1 ∨ nm ⁅a, b⁆ = u :=
    fun a ha b hb => hu _ (by rw [hnm _ (hcomW a ha b hb)]; exact hNZ _) (hsq a ha b hb)
  have hor : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), ∀ c ∈ (Q : Subgroup K),
      ∀ e ∈ (Q : Subgroup K), nm ⁅a, b⁆ = 1 ∨ nm ⁅c, e⁆ = 1 ∨ nm ⁅a, b⁆ = nm ⁅c, e⁆ := by
    intro a ha b hb c hc e he
    rcases hval a ha b hb with h | h
    · exact Or.inl h
    rcases hval c hc e he with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))
  let β : K ⧸ Subgroup.center K → K ⧸ Subgroup.center K → ZMod 2 :=
    fun a b => neOneIndicator (nm ⁅Quotient.out a, Quotient.out b⁆)
  have hβ : ∀ (a b : K ⧸ Subgroup.center K) (x y : K), (x : K ⧸ Subgroup.center K) = a →
      (y : K ⧸ Subgroup.center K) = b → β a b = neOneIndicator (nm ⁅x, y⁆) := by
    intro a b x y hx hy
    change neOneIndicator (nm ⁅Quotient.out a, Quotient.out b⁆) = _
    rw [commutatorElement_eq_of_mk_eq (a := x) (b := y) (by rw [hx, QuotientGroup.out_eq'])
      (by rw [hy, QuotientGroup.out_eq'])]
  have hβ0 := hforms β
    (by
      intro a ha b hb c hc
      have hA := hout a ha
      have hB := hout b hb
      have hC := hout c hc
      rw [hβ (a * b) c (Quotient.out a * Quotient.out b) (Quotient.out c)
          (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq'])
          (QuotientGroup.out_eq' c),
        hmul_left _ hA _ hB _ hC, hnm_mul _ (hcomW _ hB _ hC) _ (hcomW _ hA _ hC),
        neOneIndicator_mul (hor _ hB _ hC _ hA _ hC) (hsq _ hB _ hC)]
      exact add_comm _ _)
    (by
      intro a ha b hb c hc
      have hA := hout a ha
      have hB := hout b hb
      have hC := hout c hc
      rw [hβ a (b * c) (Quotient.out a) (Quotient.out b * Quotient.out c)
          (QuotientGroup.out_eq' a)
          (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']),
        hmul_right _ hA _ hB _ hC, hnm_mul _ (hcomW _ hA _ hB) _ (hcomW _ hA _ hC),
        neOneIndicator_mul (hor _ hA _ hB _ hA _ hC) (hsq _ hA _ hB)])
    (by
      intro a _
      change neOneIndicator (nm ⁅Quotient.out a, Quotient.out a⁆) = 0
      rw [commutatorElement_self, hnm_one, neOneIndicator_one])
    (by
      intro a ha b hb
      have hbW : Quotient.out b ∈ W := mem_centerPreimage_iff.mpr (by
        rwa [QuotientGroup.out_eq'])
      change neOneIndicator (nm ⁅Quotient.out a, Quotient.out b⁆) = 0
      rw [commutatorElement_eq_one_iff_mul_comm.mpr ((hWQ _ hbW).2 _ (hout a ha)).eq, hnm_one,
        neOneIndicator_one])
    (by
      intro d hd a ha b hb
      rw [hβ _ _ (liftConj d⁻¹ (Quotient.out a)) (liftConj d⁻¹ (Quotient.out b))
          (by rw [mk_liftConj, QuotientGroup.out_eq', inv_inv])
          (by rw [mk_liftConj, QuotientGroup.out_eq', inv_inv]),
        ← liftConj_commutatorElement,
        hnm_conj _ (D.inv_mem hd) _ (hcomW _ (hout a ha) _ (hout b hb))])
  have hcom1 : ∀ x ∈ (Q : Subgroup K), ∀ y ∈ (Q : Subgroup K), nm ⁅x, y⁆ = 1 := by
    intro x hx y hy
    have h := hβ0 _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)
    rw [hβ (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) x y rfl rfl] at h
    exact eq_one_of_neOneIndicator_eq_zero h
  have hle : ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ ≤ (actNorm D W).ker.map W.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⟨⁅x, y⁆, hcomW x hx y hy⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply Subtype.ext
    rw [← hnm _ (hcomW x hx y hy)]
    exact hcom1 x hx y hy
  have hinf : Subgroup.center K ⊓ ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxZ, hxC⟩
    obtain ⟨w, hw, rfl⟩ := hle hxC
    have hw1 : actNorm D W w = 1 := MonoidHom.mem_ker.mp hw
    rw [hNpow w hxZ] at hw1
    have hw' : (⟨(w : K), hxZ⟩ : Subgroup.center K) ^ Fintype.card D = 1 := by
      apply Subtype.ext
      change (w : K) ^ Fintype.card D = 1
      exact congrArg Subtype.val hw1
    have hcop : Nat.Coprime 2 (Fintype.card D) := by
      rw [Fintype.card_eq_nat_card]
      exact Nat.coprime_two_left.mpr hDodd
    have h1 := Nat.Coprime.eq_one_of_dvd (hZ.orderOf_coprime hcop _)
      (orderOf_dvd_of_pow_eq_one hw')
    rw [orderOf_eq_one_iff] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  exact CentralTwoCover.eq_bot_of_inf_commutator_eq_bot_of_perfect hperf Q le_rfl hZQ hinf

end CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover
