module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneTorus
public import CFSG.LocalAnalysis.EvenBN.U4.NormalizerB1OrderTwo
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModuleTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo card_sup_mul_card_inf_eq)
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

theorem R2G_conj_mem_F_of_mem_W (hS : Setting h L η t Q T) {w : G} (hw : w ∈ 𝓦) :
    (miyamotoR2G h L η)⁻¹ * w * miyamotoR2G h L η ∈ miyamotoFG h L η t Q := by
  have : CharP K 2 := h.charP
  set r := miyamotoR2G h L η with hr
  have hrN := hS.I2N2_le_normalizer_F2 (mem_sup_right hS.R2G_mem_N2)
  have hwF2 : r⁻¹ * w * r ∈ miyamotoF2G h L η t Q := by
    have := (mem_normalizer_iff.1 (inv_mem hrN) w).1 (hS.W_le_F2 hw)
    rwa [inv_inv] at this
  have key := miyamotoPull_map_conj h L η (miyamotoI1 h) ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩
  have e : miyamotoPull h L η (miyamotoI1r2 h) = (miyamotoI1G h L η).map
      (MulAut.conj (miyamotoR2G h L η)⁻¹).toMonoidHom := key
  have hC : r⁻¹ * w * r ∈ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := by
    rw [mem_centralizer_iff]
    intro i' hi'
    rw [SetLike.mem_coe, e] at hi'
    obtain ⟨i, hi, rfl⟩ := hi'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hwi : i * w = w * i := (mem_centralizer_iff.1 (mem_inf.1 hw).2 i hi)
    calc r⁻¹ * i * r * (r⁻¹ * w * r) = r⁻¹ * (i * w) * r := by group
      _ = r⁻¹ * (w * i) * r := by rw [hwi]
      _ = r⁻¹ * w * r * (r⁻¹ * i * r) := by group
  have hmem : r⁻¹ * w * r ∈ miyamotoRG h L η t Q ⊓
      centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := mem_inf.2 ⟨hwF2.2, hC⟩
  rw [hS.RG_inf_centralizer_I1r2] at hmem
  exact mem_sup_right hmem

theorem exists_conj_mem_F1_of_mem_F2 (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJW : J ≤ normalizer (𝓦 : Set G)) (hJE : J ≤ normalizer (miyamotoEG h L η Q : Set G))
    (htrans : ∀ a ∈ 𝓥, ∀ b ∈ 𝓥, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j * a * j⁻¹ = b)
    (hcard : ∀ w ∈ 𝓦, w ≠ 1 →
      Nat.card (miyamotoFG h L η t Q ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 4)
    {x : G} (hx : x ∈ miyamotoF2G h L η t Q) (hxx : x * x = 1) :
    ∃ g : G, g * x * g⁻¹ ∈ miyamotoF1G h L η t := by
  rw [hS.F2_eq] at hx
  obtain ⟨φ, hφ, w, hw, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' (inf_le_left.trans hS.RG_le_normalizer_F) hx
  by_cases hw1 : w = 1
  · refine ⟨1, ?_⟩
    rw [hw1, mul_one, one_mul, inv_one, mul_one]
    exact hS.F_le_F1 hφ
  have hφF1 := hS.F_le_F1 hφ
  have hwR : w ∈ miyamotoRG h L η t Q := (mem_inf.1 hw).1
  have hφφ : φ * φ = 1 := hS.F1_mul_self φ hφF1
  have hww : w * w = 1 := hS.W_mul_self hw
  have hφi : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφφ
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hφw : w * φ = φ * w := by
    have e1 : φ * w * (φ * w) = 1 := hxx
    calc w * φ = φ⁻¹ * (φ * w * (φ * w)) * w⁻¹ := by group
      _ = φ * w := by rw [e1, hφi, hwi]; group
  have hV1 : ∀ v ∈ 𝓥, v ∈ miyamotoF1G h L η t := fun v hv => by
    rw [hS.RG_inf_centralizer_I2] at hv
    exact (mem_inf.1 hv).1
  have hcF : ∀ v ∈ 𝓥, v * w * v⁻¹ * w⁻¹ ∈ miyamotoFG h L η t Q := fun v hv =>
    hS.commutator_F1_W_mem_F (hV1 v hv) hw
  let c : (𝓥 : Subgroup G) →* G :=
    { toFun := fun v => (v : G) * w * (v : G)⁻¹ * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        obtain ⟨a, ha'⟩ := a
        obtain ⟨b, hb'⟩ := b
        have ha := hV1 a ha'
        have hca := hS.F_le_F1 (hcF a ha')
        have hcb := hS.F_le_F1 (hcF b hb')
        show a * b * w * (a * b)⁻¹ * w⁻¹ = (a * w * a⁻¹ * w⁻¹) * (b * w * b⁻¹ * w⁻¹)
        calc a * b * w * (a * b)⁻¹ * w⁻¹ = a * (b * w * b⁻¹ * w⁻¹) * (w * a⁻¹ * w⁻¹) := by
              group
          _ = (b * w * b⁻¹ * w⁻¹) * a * (w * a⁻¹ * w⁻¹) := by rw [hS.F1_comm ha hcb]
          _ = (b * w * b⁻¹ * w⁻¹) * (a * w * a⁻¹ * w⁻¹) := by group
          _ = (a * w * a⁻¹ * w⁻¹) * (b * w * b⁻¹ * w⁻¹) := hS.F1_comm hcb hca }
  have hc : ∀ v : (𝓥 : Subgroup G), c v = (v : G) * w * (v : G)⁻¹ * w⁻¹ := fun v => rfl
  have hcE : ∀ v : (𝓥 : Subgroup G), c v ∈ miyamotoEG h L η Q → v = 1 := by
    intro v hv
    by_contra hv1
    have hv1' : (v : G) ≠ 1 := fun e => hv1 (Subtype.ext e)
    apply hS.commutator_W_V2_not_mem_E hJW hJE htrans hw hw1 v.2 hv1'
    have e : (w * (v : G) * w⁻¹ * (v : G)⁻¹) = (c v)⁻¹ := by rw [hc]; group
    rw [e]
    exact inv_mem hv
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro v hv
    exact hcE v (by rw [hv]; exact one_mem _)
  set Img := c.range with hImg
  have hImgF : Img ≤ miyamotoFG h L η t Q := by
    rintro _ ⟨v, rfl⟩
    exact hcF v v.2
  have hImgC : Img ≤ centralizer ({w} : Set G) := by
    rintro _ ⟨v, rfl⟩
    rw [mem_centralizer_singleton_iff, hc]
    have hcv := hS.F1_mul_self _ (hS.F_le_F1 (hcF v v.2))
    have hcvi : ((v : G) * w * (v : G)⁻¹ * w⁻¹)⁻¹ = (v : G) * w * (v : G)⁻¹ * w⁻¹ :=
      inv_eq_of_mul_eq_one_right hcv
    have key : w * ((v : G) * w * (v : G)⁻¹ * w⁻¹) =
        ((v : G) * w * (v : G)⁻¹ * w⁻¹)⁻¹ * w := by
      simp only [mul_inv_rev, inv_inv]
      rw [hwi]
      group
    rw [key, hcvi]
  have hImgE : miyamotoEG h L η Q ⊓ Img = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨he, ⟨v, rfl⟩⟩
    rw [hcE v he, map_one]
    exact one_mem _
  have hImgcard : Nat.card Img = (2 ^ f) ^ 2 := by
    rw [hImg, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hS.card_V2]
  have hImgN : Img ≤ normalizer (miyamotoEG h L η Q : Set G) := fun y hy =>
    mem_normalizer_of_mem_centralizer'
      (hS.RG_le_centralizer_E (hS.F_le_RG (hImgF hy)))
  have h1 := card_sup_mul_card_inf_eq hImgN
  rw [hImgE, card_bot, mul_one, hS.card_E, hImgcard] at h1
  have hle : miyamotoEG h L η Q ⊔ Img ≤ miyamotoFG h L η t Q ⊓ centralizer ({w} : Set G) :=
    sup_le (le_inf (hS.E_le_F) fun e he => mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (hS.RG_le_centralizer_E hwR) e he)) (le_inf hImgF hImgC)
  have heq : miyamotoEG h L η Q ⊔ Img = miyamotoFG h L η t Q ⊓ centralizer ({w} : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h1]
    calc Nat.card (miyamotoFG h L η t Q ⊓ centralizer ({w} : Set G) : Subgroup G) ≤
        (2 ^ f) ^ 4 := hcard w hw hw1
      _ = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
  have hφC : φ ∈ miyamotoEG h L η Q ⊔ Img := by
    rw [heq]
    exact mem_inf.2 ⟨hφ, mem_centralizer_singleton_iff.2 hφw.symm⟩
  obtain ⟨e, he, y, ⟨v, rfl⟩, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hImgN hφC
  set r := miyamotoR2G h L η with hr
  have hrE : r ∈ centralizer (miyamotoEG h L η Q : Set G) := hS.N2G_le_centralizer_E hS.R2G_mem_N2
  have hcv := hS.F1_mul_self _ (hS.F_le_F1 (hcF v v.2))
  have heF1 : e ∈ miyamotoF1G h L η t := hS.F_le_F1 (hS.E_le_F he)
  have hcvF1 := hS.F_le_F1 (hcF v v.2)
  have hvF1 := hV1 v v.2
  refine ⟨r⁻¹ * v, ?_⟩
  have e1 : (v : G) * (e * c v * w) * (v : G)⁻¹ = e * w := by
    rw [hc]
    set y := (v : G) * w * (v : G)⁻¹ * w⁻¹ with hy
    have hve : (v : G) * e = e * v := hS.F1_comm hvF1 heF1
    have hvc : (v : G) * y = y * v := hS.F1_comm hvF1 hcvF1
    calc (v : G) * (e * y * w) * (v : G)⁻¹ = ((v : G) * e) * y * w * (v : G)⁻¹ := by group
      _ = (e * v) * y * w * (v : G)⁻¹ := by rw [hve]
      _ = e * ((v : G) * y) * w * (v : G)⁻¹ := by group
      _ = e * (y * v) * w * (v : G)⁻¹ := by rw [hvc]
      _ = e * (y * y) * w := by rw [hy]; group
      _ = e * w := by rw [hcv, mul_one]
  have e2 : r⁻¹ * (v : G) * (e * c v * w) * (r⁻¹ * (v : G))⁻¹ = e * (r⁻¹ * w * r) := by
    have hre : r⁻¹ * e * r = e := by
      rw [mul_assoc, mem_centralizer_iff.1 hrE e he, ← mul_assoc, inv_mul_cancel, one_mul]
    calc r⁻¹ * (v : G) * (e * c v * w) * (r⁻¹ * (v : G))⁻¹ =
        r⁻¹ * ((v : G) * (e * c v * w) * (v : G)⁻¹) * r := by group
      _ = r⁻¹ * (e * w) * r := by rw [e1]
      _ = (r⁻¹ * e * r) * (r⁻¹ * w * r) := by group
      _ = e * (r⁻¹ * w * r) := by rw [hre]
  rw [e2]
  exact hS.F_le_F1 (mul_mem (hS.E_le_F he) (hS.R2G_conj_mem_F_of_mem_W hw))

theorem conj_t_not_mem_RG_of_card_le (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJW : J ≤ normalizer (𝓦 : Set G)) (hJE : J ≤ normalizer (miyamotoEG h L η Q : Set G))
    (htrans : ∀ a ∈ 𝓥, ∀ b ∈ 𝓥, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j * a * j⁻¹ = b)
    (hcard : ∀ w ∈ 𝓦, w ≠ 1 →
      Nat.card (miyamotoFG h L η t Q ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 4)
    (g : G) : g⁻¹ * t * g ∉ miyamotoRG h L η t Q := by
  intro hx
  have hxx : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, hS.t_mul_t]
    group
  obtain ⟨c, hc⟩ : ∃ c : G, c * (g⁻¹ * t * g) * c⁻¹ ∈ miyamotoF1G h L η t := by
    rcases hS.mem_F1_or_mem_F2_of_mul_self hJW hJE htrans hx hxx with h1 | h2
    · exact ⟨1, by simpa using h1⟩
    · exact hS.exists_conj_mem_F1_of_mem_F2 hJW hJE htrans hcard h2 hxx
  have e : c * (g⁻¹ * t * g) * c⁻¹ = (c * g⁻¹) * t * (c * g⁻¹)⁻¹ := by group
  have hle : miyamotoF1G h L η t ≤ centralizer ({(c * g⁻¹) * t * (c * g⁻¹)⁻¹} : Set G) :=
    fun y hy => by
      rw [mem_centralizer_singleton_iff, ← e]
      exact hS.F1_comm hy hc
  have hcard' := hS.card_le_of_le_centralizer_conj (c * g⁻¹) hle
    (GMS.isElementaryAbelian_of_mul_self hS.F1_mul_self)
  rw [hS.card_F1] at hcard'
  have hq := hS.four_le
  have h4 : 4 * (2 ^ f) ^ 4 ≤ (2 ^ f) ^ 4 * (2 ^ f) ^ 4 :=
    Nat.mul_le_mul_right _ (le_trans hq (Nat.le_self_pow (by norm_num) _))
  have hpos : 0 < (2 ^ f) ^ 4 := by positivity
  nlinarith

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

theorem card_F_inf_centralizer_le_aux (hS : Setting h L η t Q T)
    (hZF : CFSG.centerIn 𝓤 ≤ miyamotoFG h L η t Q)
    (hZcard : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4)
    (hfix : ∀ w ∈ 𝓦 ⊓ prodFactorTwo ψ, w ≠ 1 →
      CFSG.centerIn 𝓤 ⊓ centralizer ({w} : Set G) ≤ miyamotoEG h L η Q)
    {w₁ w₂ : G} (hw₁ : w₁ ∈ 𝓦 ⊓ prodFactorOne ψ) (hw₂ : w₂ ∈ 𝓦 ⊓ prodFactorTwo ψ)
    (hw₂1 : w₂ ≠ 1) :
    Nat.card (miyamotoFG h L η t Q ⊓ centralizer ({w₁ * w₂} : Set G) : Subgroup G) ≤
      (2 ^ f) ^ 4 := by
  set Z := CFSG.centerIn 𝓤 with hZdef
  set C := miyamotoFG h L η t Q ⊓ centralizer ({w₁ * w₂} : Set G) with hCdef
  have hFab : ∀ a ∈ miyamotoFG h L η t Q, ∀ b ∈ miyamotoFG h L η t Q, a * b = b * a :=
    fun a ha b hb => hS.F1_comm (hS.F_le_F1 ha) (hS.F_le_F1 hb)
  have hCN : C ≤ normalizer (Z : Set G) := fun x hx =>
    mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun z hz =>
      hFab z (hZF hz) x (mem_inf.1 hx).1)
  have h1 := card_sup_mul_card_inf_eq hCN
  have hinf : Z ⊓ C ≤ miyamotoEG h L η Q := by
    intro z hz
    obtain ⟨hzZ, hzFC⟩ := mem_inf.1 hz
    obtain ⟨-, hzC⟩ := mem_inf.1 hzFC
    have hz1 : w₁ * z = z * w₁ := mem_centralizer_iff.1 (mem_inf.1 hzZ).2 w₁ (mem_sup_right hw₁)
    have hzw : z * (w₁ * w₂) = (w₁ * w₂) * z := mem_centralizer_singleton_iff.1 hzC
    refine hfix w₂ hw₂ hw₂1 (mem_inf.2 ⟨hzZ, mem_centralizer_singleton_iff.2 ?_⟩)
    calc z * w₂ = w₁⁻¹ * (w₁ * z) * w₂ := by group
      _ = w₁⁻¹ * (z * w₁) * w₂ := by rw [hz1]
      _ = w₁⁻¹ * (z * (w₁ * w₂)) := by group
      _ = w₁⁻¹ * ((w₁ * w₂) * z) := by rw [hzw]
      _ = w₂ * z := by group
  have hsup : Z ⊔ C ≤ miyamotoFG h L η t Q := sup_le hZF inf_le_left
  have hs := Subgroup.card_le_of_le hsup
  have hi := Subgroup.card_le_of_le hinf
  rw [hS.card_F] at hs
  rw [hS.card_E] at hi
  have hZpos : 0 < (2 ^ f) ^ 4 := by positivity
  rw [hZcard] at h1
  have : Nat.card C * (2 ^ f) ^ 4 ≤ (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by
    calc Nat.card C * (2 ^ f) ^ 4 = (2 ^ f) ^ 4 * Nat.card C := mul_comm _ _
      _ = Nat.card (Z ⊔ C : Subgroup G) * Nat.card (Z ⊓ C : Subgroup G) := h1.symm
      _ ≤ (2 ^ f) ^ 6 * (2 ^ f) ^ 2 := Nat.mul_le_mul hs hi
      _ = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
  exact Nat.le_of_mul_le_mul_right this hZpos


theorem card_F_inf_centralizer_le [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZF : CFSG.centerIn 𝓤 ≤ miyamotoFG h L η t Q)
    (hZcard : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4)
    (hfix : ∀ w ∈ 𝓦 ⊓ prodFactorTwo ψ, w ≠ 1 →
      CFSG.centerIn 𝓤 ⊓ centralizer ({w} : Set G) ≤ miyamotoEG h L η Q)
    {w : G} (hw : w ∈ 𝓦) (hw1 : w ≠ 1) :
    Nat.card (miyamotoFG h L η t Q ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 4 := by
  have hc : ∀ x ∈ 𝓦 ⊓ prodFactorOne ψ, ∀ y ∈ 𝓦 ⊓ prodFactorTwo ψ, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ
      (mem_inf.1 hy).2) x (mem_inf.1 hx).2)
  rw [← (hS.W_eq_sup (ψ := ψ) hk).1] at hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hw
  by_cases hw₂1 : w₂ = 1
  · subst hw₂1
    rw [mul_one] at hw1 ⊢
    have htW : t ∈ normalizer (𝓦 : Set G) := hS.t_mem_normalizer_W
    have hti : t⁻¹ = t := hS.t_inv
    have hw' : t⁻¹ * w₁ * t ∈ 𝓦 ⊓ prodFactorTwo ψ := by
      refine mem_inf.2 ⟨?_, hS.t_conj_mem_X2 hψt (mem_inf.1 hw₁).2⟩
      have := (mem_normalizer_iff.1 (inv_mem htW) w₁).1 (mem_inf.1 hw₁).1
      rwa [inv_inv] at this
    have hw'1 : t⁻¹ * w₁ * t ≠ 1 := fun e => hw1 (by
      calc w₁ = t * (t⁻¹ * w₁ * t) * t⁻¹ := by group
        _ = 1 := by rw [e]; group)
    have key := hS.card_F_inf_centralizer_le_aux hZF hZcard hfix (one_mem _) hw' hw'1
    rw [one_mul] at key
    have htF : t ∈ normalizer (miyamotoFG h L η t Q : Set G) :=
      hS.normalizer_P1_le_normalizer_F hS.t_mem_normalizer_P1
    have hmap : (miyamotoFG h L η t Q ⊓ centralizer ({w₁} : Set G)).map
        (MulAut.conj t⁻¹).toMonoidHom ≤
          miyamotoFG h L η t Q ⊓ centralizer ({t⁻¹ * w₁ * t} : Set G) := by
      rintro _ ⟨y, ⟨hyF, hyC⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem htF) y).1 hyF
        rwa [inv_inv] at this
      · have hyw : y * w₁ = w₁ * y := mem_centralizer_singleton_iff.1 hyC
        calc t⁻¹ * y * t * (t⁻¹ * w₁ * t) = t⁻¹ * (y * w₁) * t := by group
          _ = t⁻¹ * (w₁ * y) * t := by rw [hyw]
          _ = t⁻¹ * w₁ * t * (t⁻¹ * y * t) := by group
    have := Subgroup.card_le_of_le hmap
    rw [card_map_of_injective (MulAut.conj t⁻¹).injective] at this
    exact this.trans key
  · exact hS.card_F_inf_centralizer_le_aux hZF hZcard hfix hw₁ hw₂ hw₂1

theorem centerIn_U_inf_centralizer_le_E [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4) {w : G} (hw : w ∈ 𝓦 ⊓ prodFactorTwo ψ)
    (hw1 : w ≠ 1) :
    CFSG.centerIn 𝓤 ⊓ centralizer ({w} : Set G) ≤ miyamotoEG h L η Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hZF1 : CFSG.centerIn 𝓤 ≤ miyamotoF1G h L η t := hS.centerIn_U_le_F1
  have hcomm : ∀ a ∈ CFSG.centerIn 𝓤, ∀ b ∈ CFSG.centerIn 𝓤, a * b = b * a :=
    fun a ha b hb => hS.F1_comm (hZF1 ha) (hZF1 hb)
  have hXA : prodFactorTwo ψ ≤ normalizer ((CFSG.centerIn 𝓤 : Subgroup G) : Set G) :=
    fun x hx => normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U hx)
  have hcard : Nat.card (CFSG.centerIn 𝓤) = (2 ^ (2 * f)) ^ 2 := by
    rw [hZ, ← pow_mul, ← pow_mul]
    ring_nf
  have hfix : CFSG.centerIn 𝓤 ⊓ centralizer (prodFactorTwo ψ : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [← hS.F1_inf_centralizer_X2 hk hψt hZ]
    exact mem_inf.2 ⟨hZF1 (mem_inf.1 hz).1, (mem_inf.1 hz).2⟩
  have hSX : 𝓦 ⊓ prodFactorTwo ψ ≤ prodFactorTwo ψ := inf_le_right
  have hScard : Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) = Nat.card k := by
    rw [(hS.W_eq_sup (ψ := ψ) hk).2.2, Nat.card_eq_fintype_card, hk]
  have hfixS : Nat.card (CFSG.centerIn 𝓤 ⊓ centralizer ((𝓦 ⊓ prodFactorTwo ψ : Subgroup G) :
      Set G) : Subgroup G) = 2 ^ (2 * f) := by
    rw [hS.centerIn_U_inf_centralizer_W2 hk, hS.card_E, ← pow_mul, mul_comm]
  rw [Common.natural_module_inf_centralizer_of_ne_one hk' (Common.prodFactorTwoEquiv ψ) hcomm
    hXA hcard hfix hSX hScard hfixS hw hw1, hS.centerIn_U_inf_centralizer_W2 hk]

theorem conj_t_not_mem_RG_of_case_one (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂)) (g : G) :
    g⁻¹ * t * g ∉ miyamotoRG h L η t Q := by
  obtain ⟨k', _, _, hk', ψ', -, -, hψt'⟩ := hS.sec3_15_iso
  have hZF := hS.centerIn_U_le_F_of_case_one hk₂ ψ₂ hk' ψ'
  have hZ := (hS.F1_eq_centerIn_U_sup_r1 hk' hψt' hZF).1
  obtain ⟨J, hJW, hJE, htrans⟩ := hS.exists_transitive_torus_V2 hk₂ ψ₂
  exact hS.conj_t_not_mem_RG_of_card_le hJW hJE htrans (fun w hw hw1 =>
    hS.card_F_inf_centralizer_le hk' hψt' hZF hZ
      (fun w' hw' hw'1 => hS.centerIn_U_inf_centralizer_le_E hk' hψt' hZ hw' hw'1) hw hw1) g

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
