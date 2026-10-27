module

public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

variable {V : Type*} [CommGroup V]

theorem FFModel.realizesVia_sup_of_inf (D : FFModel) {H : Subgroup (MulAut V)} {W C : Subgroup V}
    {π : D.Gam →* ↥H} (hC : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C)
    (h : D.RealizesVia H W (W ⊓ C) π) : D.RealizesVia H (C ⊔ W) C π := by
  obtain ⟨hπs, -, hkerle, hUinv, -, hsec, hkerinv, β₀, hβs, hβz, hβeq⟩ := h
  refine ⟨hπs, le_sup_left, hkerle, ?_, hC, hsec, hkerinv, ?_⟩
  · intro hh u hu
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hC hh y hy) (hUinv hh z hz)
  have hdec : ∀ x : ↥(C ⊔ W), ∃ c ∈ C, ∃ w ∈ W, c * w = (x : V) := by
    intro x
    obtain ⟨c, hc, w, hw, hcw⟩ := Subgroup.mem_sup.mp x.2
    exact ⟨c, hc, w, hw, hcw⟩
  choose c hc w hw hcw using hdec
  have hwell : ∀ (c w c' w' : V) (hc : c ∈ C) (hw : w ∈ W) (hc' : c' ∈ C) (hw' : w' ∈ W),
      c * w = c' * w' → β₀ ⟨w, hw⟩ = β₀ ⟨w', hw'⟩ := by
    intro c w c' w' hc hw hc' hw' h
    have hwe : w = c⁻¹ * c' * w' := by
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    have hmem : w * w'⁻¹ ∈ W ⊓ C := by
      refine Subgroup.mem_inf.mpr ⟨W.mul_mem hw (W.inv_mem hw'), ?_⟩
      have heq : w * w'⁻¹ = c⁻¹ * c' := by
        rw [hwe, mul_inv_cancel_right]
      rw [heq]
      exact C.mul_mem (C.inv_mem hc) hc'
    have hz : β₀ ((⟨w, hw⟩ : ↥W) * (⟨w', hw'⟩ : ↥W)⁻¹) = 1 := (hβz _).mpr hmem
    rw [map_mul, map_inv] at hz
    exact mul_inv_eq_one.mp hz
  have hchar : ∀ (x : ↥(C ⊔ W)) (c₀ w₀ : V) (hc₀ : c₀ ∈ C) (hw₀ : w₀ ∈ W),
      c₀ * w₀ = (x : V) → β₀ ⟨w x, hw x⟩ = β₀ ⟨w₀, hw₀⟩ := by
    intro x c₀ w₀ hc₀ hw₀ hx
    exact hwell (c x) (w x) c₀ w₀ (hc x) (hw x) hc₀ hw₀ ((hcw x).trans hx.symm)
  refine ⟨{ toFun := fun x => β₀ ⟨w x, hw x⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_, ?_, ?_⟩
  · show β₀ ⟨w 1, hw 1⟩ = 1
    exact (hchar 1 1 1 C.one_mem W.one_mem (by simp)).trans (map_one β₀)
  · intro x y
    show β₀ ⟨w (x * y), hw (x * y)⟩ = β₀ ⟨w x, hw x⟩ * β₀ ⟨w y, hw y⟩
    have hxy : c x * c y * (w x * w y) = ((x * y : ↥(C ⊔ W)) : V) := by
      rw [mul_mul_mul_comm, hcw x, hcw y, Subgroup.coe_mul]
    rw [hchar (x * y) (c x * c y) (w x * w y) (C.mul_mem (hc x) (hc y))
      (W.mul_mem (hw x) (hw y)) hxy]
    exact map_mul β₀ ⟨w x, hw x⟩ ⟨w y, hw y⟩
  · intro q
    obtain ⟨u, hu⟩ := hβs q
    have hx : (u : V) ∈ C ⊔ W := Subgroup.mem_sup_right u.2
    refine ⟨⟨(u : V), hx⟩, ?_⟩
    exact (hchar ⟨(u : V), hx⟩ 1 (u : V) C.one_mem u.2 (one_mul (u : V))).trans hu
  · intro x
    constructor
    · intro hx
      obtain ⟨-, hwC⟩ := Subgroup.mem_inf.mp ((hβz ⟨w x, hw x⟩).mp hx)
      rw [← hcw x]
      exact C.mul_mem (hc x) hwC
    · intro hx
      have hwC : w x ∈ C := by
        have heq : w x = (c x)⁻¹ * (x : V) := by
          rw [← hcw x, inv_mul_cancel_left]
        rw [heq]
        exact C.mul_mem (C.inv_mem (hc x)) hx
      exact (hβz ⟨w x, hw x⟩).mpr (Subgroup.mem_inf.mpr ⟨hw x, hwC⟩)
  · intro γ u m hu hm hmk
    have hc' : ((π γ : ↥H) : MulAut V) (c u) ∈ C := hC (π γ) (c u) (hc u)
    have hw' : ((π γ : ↥H) : MulAut V) (w u) ∈ W := hUinv (π γ) (w u) (hw u)
    have hdecomp : ((π γ : ↥H) : MulAut V) (c u) * ((π γ : ↥H) : MulAut V) (w u) =
        ((π γ : ↥H) : MulAut V) (u : V) := by
      rw [← map_mul, hcw u]
    exact (hchar ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ _ _ hc' hw' hdecomp).trans
      (hβeq γ ⟨w u, hw u⟩ m hw' hm hmk)

theorem binaryNaturalSL_sup_of_inf {H : Subgroup (MulAut V)} {W C : Subgroup V} {d a : ℕ}
    (hC : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C) (h : BinaryNaturalSL H W (W ⊓ C) d a) :
    BinaryNaturalSL H (C ⊔ W) C d a := by
  obtain ⟨K, instK, instF, hK, π, hπ⟩ := h
  exact ⟨K, instK, instF, hK, π, FFModel.realizesVia_sup_of_inf _ hC hπ⟩

noncomputable def sl2MulEquivOfRingEquiv {K K' : Type} [Field K] [Field K'] (f : K ≃+* K') :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K' where
  toFun := Matrix.SpecialLinearGroup.map f.toRingHom
  invFun := Matrix.SpecialLinearGroup.map f.symm.toRingHom
  left_inv A := Subtype.ext (Matrix.ext fun i j => by simp)
  right_inv B := Subtype.ext (Matrix.ext fun i j => by simp)
  map_mul' A B := map_mul (Matrix.SpecialLinearGroup.map f.toRingHom) A B

theorem nonempty_mulEquiv_sl2_of_binaryNatural {H : Subgroup (MulAut V)} {U Z : Subgroup V} {e : ℕ}
    (he : 1 ≤ e) (h : BinaryNaturalSL H U Z 2 e) :
    Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) := by
  obtain ⟨K, instK, instF, hK, π, hπs, -, -, -, -, -, -, β, hβs, -, hβeq⟩ := h
  have key : ∀ γ : ↥(StatedSL 2 K), π γ = 1 → ∀ w : Fin 2 → K,
      ((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w = w := by
    intro γ hγ w
    obtain ⟨m, hm⟩ : ∃ m : ↥(FFModel.nat (StatedSL 2 K)).sec,
        (m : (FFModel.nat (StatedSL 2 K)).Amb) =
          (Multiplicative.ofAdd w : Multiplicative (Fin 2 → K)) :=
      ⟨⟨(Multiplicative.ofAdd w : Multiplicative (Fin 2 → K)), trivial⟩, rfl⟩
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    have hfixV : ((π γ : ↥H) : MulAut V) (u : V) = (u : V) := by
      rw [hγ] <;> rfl
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := by
      rw [hfixV]
      exact u.2
    have hfix : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext hfixV
    have h1 := hβeq γ u m hu' trivial hu
    have h2 := (congrArg β hfix.symm).trans h1
    rw [hu] at h2
    have h3 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h2)
    have h4 : ((m : (FFModel.nat (StatedSL 2 K)).Amb))⁻¹ *
        (FFModel.nat (StatedSL 2 K)).act γ (m : (FFModel.nat (StatedSL 2 K)).Amb) = 1 :=
      Subgroup.mem_bot.mp h3
    have h5 : ((m : (FFModel.nat (StatedSL 2 K)).Amb)) =
        (FFModel.nat (StatedSL 2 K)).act γ (m : (FFModel.nat (StatedSL 2 K)).Amb) :=
      inv_mul_eq_one.mp h4
    have h6 : Multiplicative.ofAdd w = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w) :=
      hm.symm.trans (h5.trans (congrArg ((FFModel.nat (StatedSL 2 K)).act γ) hm))
    exact (Multiplicative.ofAdd.injective h6).symm
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective γ
    have hA : A = 1 := by
      refine CFSG.Quasithin.Ch3z.sl2_eq_one_of_mulVec A (fun w => ?_)
      have hw := key _ hγ w
      rw [specialLinearGroupEquivStatedSL_coe] at hw
      exact hw
    rw [hA] <;> exact map_one _
  have hψ : Function.Bijective (π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom) :=
    ⟨hπinj.comp (specialLinearGroupEquivStatedSL 2 K).injective,
      hπs.comp (specialLinearGroupEquivStatedSL 2 K).surjective⟩
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 e) := Fintype.ofFinite (GaloisField 2 e)
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 e) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK, GaloisField.card 2 e (by omega)]
  have hiso : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H :=
    MulEquiv.ofBijective (π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom) hψ
  exact ⟨hiso.symm.trans (sl2MulEquivOfRingEquiv (FiniteField.ringEquivOfCardEq hcard))⟩

end CFSG.Quasithin
