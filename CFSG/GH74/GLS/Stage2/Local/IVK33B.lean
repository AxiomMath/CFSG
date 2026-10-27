module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassF
public import CFSG.GH74.GLS.Stage2.Local.IVK33A
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Main CFSG.GH74.GLS.Stage1.Thm6.Prod

section Cycle

variable {G : Type} [Group G] [Finite G] {z : G}

theorem prop21h_of_cycle {v₁ v₂ w : CentralizerBar z} (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1)
    (hc : v₁ * v₂ = v₂ * v₁) (h₁ : v₁ ≠ 1) (h₂ : v₂ ≠ 1) (h₁₂ : v₁ ≠ v₂)
    (hw₁ : w * v₁ * w⁻¹ = v₂) (hw₂ : w * v₂ * w⁻¹ = v₁ * v₂) (hL₁ : v₁ ∈ LBar z)
    (hL₂ : v₂ ∈ LBar z) : Prop21h z := by
  classical
  have hN : Odd (Nat.card (pPrimeCore 2 ↥(Cen z))) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  obtain ⟨V', ω, hea, hcard, -, himg, hnorm, hne, h3⟩ :=
    exists_lift_four (N := pPrimeCore 2 ↥(Cen z)) hN (τ := 1) (one_mul 1) hv₁ hv₂ hc h₁ h₂ h₁₂
      (by simp) (by simp) hw₁ hw₂
  have hfour : IVK.IsFourSubgroup (V'.map (Cen z).subtype) := by
    refine ⟨IsElementaryAbelian.map_subtype, ?_⟩
    rw [Subgroup.card_map_of_injective (Cen z).subtype_injective]
    exact hcard
  have hle : V'.map (Cen z).subtype ≤ LC z := by
    rintro _ ⟨v, hv, rfl⟩
    have hv2 : (v : ↥(Cen z)) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
    have hk : (v : ↥(Cen z)) ^ (2 ^ 1) = 1 := by simpa using hv2
    refine (mem_LC_iff_of_pElt (z := z) v hk).2 ?_
    show (QuotientGroup.mk v : CentralizerBar z) ∈ LBar z
    rcases himg v hv with h | h | h | h
    · rw [h]
      exact (LBar z).one_mem
    · rw [h]
      exact hL₁
    · rw [h]
      exact hL₂
    · rw [h]
      exact (LBar z).mul_mem hL₁ hL₂
  have hωN : ∀ g ∈ V'.map (Cen z).subtype, (ω : G) * g * (ω : G)⁻¹ ∈ V'.map (Cen z).subtype := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ω * v * ω⁻¹, hnorm v hv, by simp⟩
  have hne' : ∃ g ∈ V'.map (Cen z).subtype, (ω : G) * g * (ω : G)⁻¹ ≠ g := by
    obtain ⟨v, hv, hvne⟩ := hne
    refine ⟨(v : G), ⟨v, hv, rfl⟩, fun h => hvne (Subtype.ext ?_)⟩
    simpa using h
  have h3' : ∀ g ∈ V'.map (Cen z).subtype, (ω : G) ^ 3 * g * ((ω : G) ^ 3)⁻¹ = g := by
    rintro _ ⟨v, hv, rfl⟩
    have := congrArg Subtype.val (h3 v hv)
    simpa using this
  exact ⟨V'.map (Cen z).subtype, hle, hfour, autOrd_of_cycle hfour ω.2 hωN hne' h3'⟩

end Cycle

section Product

variable {Y : Type} [Group Y]

theorem exists_inf_central {L₁ L₂ : Subgroup Y} (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2) :
    ∃ c : Y, ∃ (hc₁ : c ∈ L₁) (hc₂ : c ∈ L₂), c ≠ 1 ∧ c * c = 1 ∧ (∀ x ∈ L₁ ⊓ L₂, x * x = 1) ∧
      (⟨c, hc₁⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ ∧ (⟨c, hc₂⟩ : ↥L₂) ∈ Subgroup.center ↥L₂ := by
  classical
  have hfin : Finite ↥(L₁ ⊓ L₂) := Nat.finite_of_card_ne_zero (by omega)
  have hsq : ∀ x ∈ L₁ ⊓ L₂, x * x = 1 := by
    intro x hx
    have h := pow_card_eq_one' (G := ↥(L₁ ⊓ L₂)) (x := ⟨x, hx⟩)
    rw [hcard, sq] at h
    exact congrArg Subtype.val h
  have : Nontrivial ↥(L₁ ⊓ L₂) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : ↥(L₁ ⊓ L₂))
  have hc₁ : c ∈ L₁ := (Subgroup.mem_inf.1 hc).1
  have hc₂ : c ∈ L₂ := (Subgroup.mem_inf.1 hc).2
  refine ⟨c, hc₁, hc₂, fun h => hc1 (Subtype.ext h), hsq c hc, hsq, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 c hc₂)
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm c hc₁ g g.2).symm

theorem exists_cycle_of_quat_pair {L₁ L₂ : Subgroup Y} (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hsq : ∀ x ∈ L₁ ⊓ L₂, x * x = 1) {c : Y} (hc₁ : c ∈ L₁) (hc₂ : c ∈ L₂) (hcc : c * c = 1)
    (hc1 : c ≠ 1) {a₁ b₁ : ↥L₁} {a₂ b₂ : ↥L₂} {w : Y} (ha₁ : a₁ * a₁ = ⟨c, hc₁⟩)
    (hb₁ : b₁ * b₁ = ⟨c, hc₁⟩) (hba₁ : b₁ * a₁ = ⟨c, hc₁⟩ * (a₁ * b₁)) (ha₂ : a₂ * a₂ = ⟨c, hc₂⟩)
    (hb₂ : b₂ * b₂ = ⟨c, hc₂⟩) (hba₂ : b₂ * a₂ = ⟨c, hc₂⟩ * (a₂ * b₂))
    (hwa₁ : w * (a₁ : Y) * w⁻¹ = b₁) (hwa₂ : w * (a₂ : Y) * w⁻¹ = b₂)
    (hwb₁ : w * (b₁ : Y) * w⁻¹ = (a₁ : Y) * b₁) (hwb₂ : w * (b₂ : Y) * w⁻¹ = (a₂ : Y) * b₂) :
    ∃ v₁ v₂ : Y, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧
      w * v₁ * w⁻¹ = v₂ ∧ w * v₂ * w⁻¹ = v₁ * v₂ ∧ v₁ ∈ L₁ ⊔ L₂ ∧ v₂ ∈ L₁ ⊔ L₂ := by
  classical
  let φ : ↥L₁ × ↥L₂ →* Y := MonoidHom.noncommCoprod L₁.subtype L₂.subtype
    (fun m n => (hcomm m m.2 n n.2))
  have hφ : ∀ p : ↥L₁ × ↥L₂, φ p = (p.1 : Y) * p.2 := fun p => rfl
  have hφc : φ (⟨c, hc₁⟩, ⟨c, hc₂⟩) = 1 := by rw [hφ]; exact hcc
  have hφmul : ∀ p q : ↥L₁ × ↥L₂, p = (⟨c, hc₁⟩, ⟨c, hc₂⟩) * q → φ p = φ q := by
    intro p q h
    rw [h, map_mul, hφc, one_mul]
  have hv₁sq : φ (a₁, a₂) * φ (a₁, a₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, ha₁, ha₂]
    exact hφc
  have hv₂sq : φ (b₁, b₂) * φ (b₁, b₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hb₁, hb₂]
    exact hφc
  have hcommv : φ (a₁, a₂) * φ (b₁, b₂) = φ (b₁, b₂) * φ (a₁, a₂) := by
    rw [← map_mul, ← map_mul]
    symm
    apply hφmul
    simp only [Prod.mk_mul_mk, Prod.mk.injEq]
    exact ⟨hba₁, hba₂⟩
  have hne1 : φ (a₁, a₂) ≠ 1 := by
    intro h
    rw [hφ] at h
    have hmem : ((a₁ : ↥L₁) : Y) ∈ L₁ ⊓ L₂ := by
      refine ⟨a₁.2, ?_⟩
      have : ((a₁ : ↥L₁) : Y) = ((a₂ : ↥L₂) : Y)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact L₂.inv_mem a₂.2
    exact hc1 ((congrArg Subtype.val ha₁).symm.trans (hsq _ hmem))
  have hconj₁ : w * φ (a₁, a₂) * w⁻¹ = φ (b₁, b₂) := by
    show w * ((a₁ : Y) * a₂) * w⁻¹ = (b₁ : Y) * b₂
    calc w * ((a₁ : Y) * a₂) * w⁻¹ = (w * a₁ * w⁻¹) * (w * a₂ * w⁻¹) := by group
      _ = (b₁ : Y) * b₂ := by rw [hwa₁, hwa₂]
  have hconj₂ : w * φ (b₁, b₂) * w⁻¹ = φ (a₁, a₂) * φ (b₁, b₂) := by
    show w * ((b₁ : Y) * b₂) * w⁻¹ = ((a₁ : Y) * a₂) * ((b₁ : Y) * b₂)
    calc w * ((b₁ : Y) * b₂) * w⁻¹ = (w * b₁ * w⁻¹) * (w * b₂ * w⁻¹) := by group
      _ = ((a₁ : Y) * b₁) * ((a₂ : Y) * b₂) := by rw [hwb₁, hwb₂]
      _ = (a₁ : Y) * ((b₁ : Y) * a₂) * b₂ := by group
      _ = (a₁ : Y) * ((a₂ : Y) * b₁) * b₂ := by rw [hcomm b₁ b₁.2 a₂ a₂.2]
      _ = ((a₁ : Y) * a₂) * ((b₁ : Y) * b₂) := by group
  have hne2 : φ (b₁, b₂) ≠ 1 := by
    intro h
    apply hne1
    rw [h] at hconj₁
    simpa using hconj₁
  have hne12 : φ (a₁, a₂) ≠ φ (b₁, b₂) := by
    intro h
    apply hne1
    have h2 : φ (b₁, b₂) = φ (a₁, a₂) * φ (b₁, b₂) :=
      calc φ (b₁, b₂) = w * φ (a₁, a₂) * w⁻¹ := hconj₁.symm
        _ = w * φ (b₁, b₂) * w⁻¹ := by rw [h]
        _ = φ (a₁, a₂) * φ (b₁, b₂) := hconj₂
    simpa using h2.symm
  exact ⟨φ (a₁, a₂), φ (b₁, b₂), hv₁sq, hv₂sq, hcommv, hne1, hne2, hne12, hconj₁, hconj₂,
    Subgroup.mul_mem_sup a₁.2 a₂.2, Subgroup.mul_mem_sup b₁.2 b₂.2⟩

theorem exists_cycle_of_sl2_prod {L₁ L₂ : Subgroup Y} (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2) (h₁ : HasSL2Model ↥L₁ Odd) (h₂ : HasSL2Model ↥L₂ Odd) :
    ∃ v₁ v₂ w : Y, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧
      w * v₁ * w⁻¹ = v₂ ∧ w * v₂ * w⁻¹ = v₁ * v₂ ∧ v₁ ∈ L₁ ⊔ L₂ ∧ v₂ ∈ L₁ ⊔ L₂ := by
  classical
  obtain ⟨c, hc₁, hc₂, hc1', hcc, hsq, hz₁, hz₂⟩ := exists_inf_central hcomm hcard
  obtain ⟨a₁, b₁, w₁, ha₁, hb₁, hba₁, hwa₁, hwb₁⟩ :=
    exists_quat_of_hasSL2Model h₁ hz₁ (fun h => hc1' (congrArg Subtype.val h))
  obtain ⟨a₂, b₂, w₂, ha₂, hb₂, hba₂, hwa₂, hwb₂⟩ :=
    exists_quat_of_hasSL2Model h₂ hz₂ (fun h => hc1' (congrArg Subtype.val h))
  have hx₁ : ∀ x ∈ L₁, ∀ y ∈ L₂, y * x * y⁻¹ = x := by
    intro x hx y hy
    rw [← hcomm x hx y hy, mul_inv_cancel_right]
  have hx₂ : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y * x⁻¹ = y := by
    intro x hx y hy
    rw [hcomm x hx y hy, mul_inv_cancel_right]
  have hconj₁ : ∀ (u : ↥L₁) (v : ↥L₂) (x : ↥L₁), ((u : Y) * v) * x * ((u : Y) * v)⁻¹ =
      (u : Y) * x * (u : Y)⁻¹ := by
    intro u v x
    calc ((u : Y) * v) * x * ((u : Y) * v)⁻¹ = u * (v * x * (v : Y)⁻¹) * (u : Y)⁻¹ := by group
      _ = (u : Y) * x * (u : Y)⁻¹ := by rw [hx₁ x x.2 v v.2]
  have hconj₂ : ∀ (u : ↥L₁) (v : ↥L₂) (y : ↥L₂), ((u : Y) * v) * y * ((u : Y) * v)⁻¹ =
      (v : Y) * y * (v : Y)⁻¹ := by
    intro u v y
    calc ((u : Y) * v) * y * ((u : Y) * v)⁻¹ = u * (v * y * (v : Y)⁻¹) * (u : Y)⁻¹ := by group
      _ = (v : Y) * y * (v : Y)⁻¹ :=
        hx₂ u u.2 _ (L₂.mul_mem (L₂.mul_mem v.2 y.2) (L₂.inv_mem v.2))
  obtain ⟨v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_cycle_of_quat_pair hcomm hsq hc₁ hc₂ hcc hc1' ha₁ hb₁ hba₁ ha₂ hb₂ hba₂
      (w := (w₁ : Y) * w₂)
      (by rw [hconj₁]; exact congrArg Subtype.val hwa₁)
      (by rw [hconj₂]; exact congrArg Subtype.val hwa₂)
      (by rw [hconj₁]; exact congrArg Subtype.val hwb₁)
      (by rw [hconj₂]; exact congrArg Subtype.val hwb₂)
  exact ⟨v₁, v₂, (w₁ : Y) * w₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Product

section Wrappers

variable {G : Type} [Group G] [Finite G] {z : G}

theorem prop21h_of_sl2_prod {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hprod : IsCentralProd L₁ L₂ (LBar z)) (h₁ : HasSL2Model ↥L₁ Odd) (h₂ : HasSL2Model ↥L₂ Odd) :
    Prop21h z := by
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  obtain ⟨v₁, v₂, w, hv₁, hv₂, hc, h₁1, h₂1, h₁₂, hw₁, hw₂, hm₁, hm₂⟩ :=
    exists_cycle_of_sl2_prod hcomm hcard h₁ h₂
  rw [hsup] at hm₁ hm₂
  exact prop21h_of_cycle hv₁ hv₂ hc h₁1 h₂1 h₁₂ hw₁ hw₂ hm₁ hm₂

theorem prop21h_of_pair {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hpair : Stage1Pair G z S q L₁ L₂) : Prop21h z :=
  prop21h_of_sl2_prod hpair.prod
    (hasSL2Model_mono hpair.sl₁ fun n (hn : n = q) => by rw [hn]; exact hpair.odd)
    (hasSL2Model_mono hpair.sl₂ fun n (hn : n = q) => by rw [hn]; exact hpair.odd)

theorem prop21h_of_g2 {S : Subgroup G} {r₁ r₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (h : G2Shape z S r₁ r₂ L₁ L₂) : Prop21h z := by
  obtain ⟨hr₁, hr₂, -, hprod, hs₁, hs₂, -⟩ := h
  exact prop21h_of_sl2_prod hprod (hasSL2Model_mono hs₁ fun n (hn : n = r₁) => by rw [hn]; exact hr₁)
    (hasSL2Model_mono hs₂ fun n (hn : n = r₂) => by rw [hn]; exact hr₂)

end Wrappers

end CFSG.GH74.GLS.Stage2.Local
