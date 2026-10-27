module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Base
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Q
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dii

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

@[expose] def EndB.qTilde (β : X) (W : Subgroup X) : Subgroup X :=
  W ⊓ preimageOf (centralizer ({β} : Set X)) (pCore 2 (MBar β))

theorem EndB.le_of_barOf_le {M W A B : Subgroup X} (hWM : W ≤ M) (hW : IsPGroup 2 W)
    (hAW : A ≤ W) (hBW : B ≤ W) (h : barOf M A ≤ barOf M B) : A ≤ B := by
  intro a ha
  obtain ⟨b, hbB, hb⟩ := mem_barOf.mp (h (mk_mem_barOf (hWM (hAW ha)) ha))
  have : (b : X) = a := mk_injOn hWM hW (hBW hbB) (hAW ha) hb
  exact this ▸ hbB

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem qTilde_le (_hc : L2Ctx hs W) :
    qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ≤ W :=
  inf_le_left

theorem pCore_le_barOf_W (hc : L2Ctx hs W) :
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWb := isSylowOf_barOf hc.sylow
  have hsup : IsPGroup 2 ↥(barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W
      ⊔ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    IsPGroup.to_sup_of_normal_right hWb.isPGroup pCore_isPGroup
  have heq := hWb.eq_of_le le_sup_left le_top hsup
  rw [← heq]
  exact le_sup_right

theorem barOf_qTilde (hc : L2Ctx hs W) :
    barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
        (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) =
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [qTilde, barOf_inf_preimageOf, inf_eq_right]
  exact hc.pCore_le_barOf_W

theorem card_qTilde (hc : L2Ctx hs W) :
    Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) =
      Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  rw [← hc.barOf_qTilde, card_barOf (hc.qTilde_le.trans hc.sylow.le)
    (hc.sylow.isPGroup.to_le hc.qTilde_le)]

@[expose] def qTildeEquiv (hc : L2Ctx hs W) :
    ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) ≃*
      ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  (barEquiv (hc.qTilde_le.trans hc.sylow.le) (hc.sylow.isPGroup.to_le hc.qTilde_le)).trans
    (MulEquiv.subgroupCongr hc.barOf_qTilde)

theorem qTilde_normal (hc : L2Ctx hs W) {g y : X} (hg : g ∈ W)
    (hy : y ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) :
    g * y * g⁻¹ ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W := by
  have hWM := hc.sylow.le
  have hmem : g * y * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    mul_mem (mul_mem (hWM hg) (hWM hy.1)) (inv_mem (hWM hg))
  refine ⟨W.mul_mem (W.mul_mem hg hy.1) (W.inv_mem hg), (mem_preimageOf hmem).mpr ?_⟩
  have hy' := (mem_preimageOf (hWM hy.1)).mp hy.2
  have : (QuotientGroup.mk ⟨g * y * g⁻¹, hmem⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk ⟨g, hWM hg⟩ * QuotientGroup.mk ⟨y, hWM hy.1⟩ *
        (QuotientGroup.mk ⟨g, hWM hg⟩)⁻¹ := rfl
  rw [this]
  exact pCore_normal.conj_mem _ hy' _

omit [Finite X] in
theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.barOf_zpowers {M : Subgroup X}
    {x : X} (hx : x ∈ M) :
    barOf M (zpowers x) = zpowers (QuotientGroup.mk ⟨x, hx⟩ : ↥M ⧸ pPrimeCore 2 ↥M) := by
  rw [barOf, zpowers_subgroupOf hx, MonoidHom.map_zpowers]
  rfl

theorem qTilde_inf_centralizer (hc : L2Ctx hs W) :
    qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊓ centralizer ({t} : Set X) =
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  have hWM := hc.sylow.le
  have hW2 := hc.sylow.isPGroup
  have htW : t ∈ W := hc.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hβW : β ∈ W := hc.T_le (hs.setup.X_le_T (beta_mem_X i j))
  have hβM : β ∈ M := mem_centralizer_singleton_iff.mpr rfl
  have h1 : qTilde β W ⊓ centralizer ({t} : Set X) =
      (W ⊓ centralizer ({t} : Set X)) ⊓ preimageOf M (pCore 2 (MBar β)) := by
    rw [qTilde]
    ac_rfl
  have hbar : barOf M (qTilde β W ⊓ centralizer ({t} : Set X)) = barOf M (zpowers β) := by
    rw [h1, barOf_inf_preimageOf, barOf_inf_centralizer hWM hW2 htW, EndB.barOf_zpowers hβM,
      inf_right_comm, inf_eq_right.mpr hc.pCore_le_barOf_W]
    exact hs.pCore_inf_centralizer_tBar
  have hle1 : qTilde β W ⊓ centralizer ({t} : Set X) ≤ W := inf_le_left.trans inf_le_left
  have hle2 : zpowers β ≤ W := zpowers_le.mpr hβW
  exact le_antisymm (EndB.le_of_barOf_le hWM hW2 hle1 hle2 hbar.le)
    (EndB.le_of_barOf_le hWM hW2 hle2 hle1 hbar.ge)

theorem beta_mem_qTilde (hc : L2Ctx hs W) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W := by
  have h := hc.qTilde_inf_centralizer
  have : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    mem_zpowers _
  rw [← h] at this
  exact this.1

theorem z_not_mem_qTilde (hc : L2Ctx hs W) :
    z ∉ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have := hc.simple
  intro hzQ
  have hzK : z ∈ centralizerResidual L β := hs.lemma45.z_mem.2
  have hzM : z ∈ centralizer ({β} : Set X) := K_le_centralizer_beta i j hzK
  have hzE : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈ layer (MBar β) :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hzP := (mem_preimageOf hzM).mp hzQ.2
  rw [← hs.centralizer_layer_eq hc.h412] at hzP
  have hKnab := nonabelian_of_lieModel_psl2 (hs.lieModel_KBar hc.h412)
  have hCE := centralizer_inf_layer_eq_bot hs.KBar_le_layer hKnab
  have hz1 : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) = 1 := by
    have : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈
        centralizer (layer (MBar β) : Set (MBar β)) ⊓ layer (MBar β) := ⟨hzP, hzE⟩
    rwa [hCE, mem_bot] at this
  have hzW : z ∈ W := hzQ.1
  have := mk_injOn hc.sylow.le hc.sylow.isPGroup hzW (one_mem W)
    (by rw [hz1]; rfl)
  have hzo := hs.setup.z_order
  rw [this, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

theorem qTilde_inf_X_le (hc : L2Ctx hs W) :
    qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊓ closure {t, w ^ (orderOf w / 2), z} ≤
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  rw [← hc.qTilde_inf_centralizer]
  exact inf_le_inf_left _ ((hs.setup.X_le_T.trans hs.setup.T_le).trans hs.sylow.le)

theorem qTilde_shape (hc : L2Ctx hs W) :
    IsCyclic ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) ∨
      ∃ k : ℕ, 1 ≤ k ∧
        Nonempty (↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) ≃* DihedralGroup (2 ^ k)) := by
  rcases hc.h412.pCore_shape with h | ⟨k, hk, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_surjective hc.qTildeEquiv.symm.toMonoidHom
      hc.qTildeEquiv.symm.surjective)
  · exact Or.inr ⟨k, hk, ⟨hc.qTildeEquiv.trans e⟩⟩

theorem card_zpowers_beta (_hc : L2Ctx hs W) :
    Nat.card ↥(zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
  rw [Nat.card_zpowers, hs.setup.orderOf_beta i j]

theorem card_qTilde_le_four (hc : L2Ctx hs W)
    (hN : ∀ y ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W,
      y * t * y⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) :
    Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) ≤ 4 := by
  classical
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have htW : t ∈ W := hc.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have key : ∀ a ∈ qTilde β W, a * t * a⁻¹ ∈ ({t, β * t} : Finset X) := by
    intro a ha
    have hc1 : a * t * a⁻¹ * t⁻¹ ∈ qTilde β W := by
      have : a * t * a⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by group
      rw [this]
      exact mul_mem ha (hc.qTilde_normal htW (inv_mem ha))
    have hc2 : a * t * a⁻¹ * t⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
      mul_mem (hN a ha) (inv_mem htX)
    have hc3 := hc.qTilde_inf_X_le ⟨hc1, hc2⟩
    rcases eq_one_or_eq_of_mem_zpowers_two (hs.setup.orderOf_beta i j) hc3 with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      calc a * t * a⁻¹ = a * t * a⁻¹ * t⁻¹ * t := by group
        _ = t := by rw [h, one_mul]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      calc a * t * a⁻¹ = a * t * a⁻¹ * t⁻¹ * t := by group
        _ = β * t := by rw [h]
  have h := L415.card_le_of_fiber (A := qTilde β W) (K := centralizer ({t} : Set X))
    (fun y => y * t * y⁻¹) (fun a _ a' _ haa => by
      rw [mem_centralizer_singleton_iff]
      have h1 : a⁻¹ * a' * t = a⁻¹ * (a' * t * a'⁻¹) * a' := by group
      have h2 : t * (a⁻¹ * a') = a⁻¹ * (a * t * a⁻¹) * a' := by group
      rw [h2, h1, haa]) ({t, β * t} : Finset X) key
  rw [hc.qTilde_inf_centralizer, hc.card_zpowers_beta] at h
  have h2 : ({t, β * t} : Finset X).card ≤ 2 := Finset.card_le_two
  omega

theorem exists_conj_t_eq (hc : L2Ctx hs W)
    (h4 : 4 ≤ Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W)) :
    ∃ y ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W,
      y * t * y⁻¹ = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htW : t ∈ W := hc.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have ht2 : t * t = 1 := by
    rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hβQ := hc.beta_mem_qTilde
  have hβ2 : β * β = 1 := by rw [← sq]; exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hβ1 : β ≠ 1 := fun h => by
    have := hs.setup.orderOf_beta i j
    rw [← hβ, h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβc : ∀ x ∈ qTilde β W, x * β = β * x := fun x hx =>
    (mem_centralizer_singleton_iff.mp (hc.sylow.le hx.1))
  have hCt : ∀ y ∈ qTilde β W, y * t = t * y → y ∈ zpowers β := fun y hy hyt => by
    rw [← hc.qTilde_inf_centralizer]
    exact ⟨hy, mem_centralizer_singleton_iff.mpr hyt⟩
  by_cases hq : ∃ q ∈ qTilde β W, q * q ≠ 1
  ·
    obtain ⟨q, hqQ, hqq⟩ := hq
    obtain ⟨v, hvQ, hv4, hv2, hvall⟩ := L415.exists_four
      (hc.sylow.isPGroup.to_le hc.qTilde_le) hc.qTilde_shape hβQ hβ2 hβ1 hβc hqQ hqq
    have hxQ : t * v * t⁻¹ ∈ qTilde β W := hc.qTilde_normal htW hvQ
    have hx4 : orderOf (t * v * t⁻¹) = 4 := by
      rw [← hv4, ← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective v
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hvall _ hxQ hx4)
    have hk' : v ^ (k % 4) = t * v * t⁻¹ := by
      have h1 := zpow_mod_orderOf v k
      rw [hv4] at h1
      rw [← hk, ← h1]
      rfl
    have hv44 : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
    have hkr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    have hinv : t * v * t⁻¹ = v⁻¹ := by
      rcases hkr with h | h | h | h <;> rw [h] at hk'
      · exfalso
        rw [zpow_zero] at hk'
        have : orderOf (t * v * t⁻¹) = 1 := by rw [← hk', orderOf_one]
        omega
      · exfalso
        rw [zpow_one] at hk'
        have hvt : v * t = t * v := by
          calc v * t = t * v * t⁻¹ * t := by rw [← hk']
            _ = t * v := by group
        have := hCt v hvQ hvt
        have h2 := orderOf_dvd_of_mem_zpowers this
        rw [hv4, hs.setup.orderOf_beta i j] at h2
        norm_num at h2
      · exfalso
        have : orderOf (t * v * t⁻¹) = 2 := by
          rw [← hk', show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, hv2,
            hs.setup.orderOf_beta i j]
        omega
      · rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast] at hk'
        rw [← hk']
        have : v ^ 3 * v = 1 := by rw [← pow_succ, hv44]
        exact eq_inv_of_mul_eq_one_left this
    refine ⟨v, hvQ, ?_⟩
    calc v * t * v⁻¹ = v * (t * v⁻¹ * t⁻¹) * t := by group
      _ = v * (t * v * t⁻¹)⁻¹ * t := by group
      _ = v ^ 2 * t := by rw [hinv, inv_inv, sq]
      _ = β * t := by rw [hv2]
  ·
    push Not at hq
    have hex : ∃ y ∈ qTilde β W, y ∉ zpowers β := by
      by_contra hno
      push Not at hno
      have hle : qTilde β W ≤ zpowers β := fun y hy => hno y hy
      have := Subgroup.card_le_of_le hle
      rw [hc.card_zpowers_beta] at this
      omega
    obtain ⟨y, hyQ, hyb⟩ := hex
    set d := y * t * y⁻¹ * t⁻¹ with hd
    have hdQ : d ∈ qTilde β W := by
      have : d = y * (t * y⁻¹ * t⁻¹) := by rw [hd]; group
      rw [this]
      exact mul_mem hyQ (hc.qTilde_normal htW (inv_mem hyQ))
    have hdd : d * d = 1 := hq d hdQ
    have hdt : d * t = t * d := by
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
      have h1 : t * d * t⁻¹ = d⁻¹ := by
        calc t * d * t⁻¹ = t * y * t * y⁻¹ * (t⁻¹ * t⁻¹) := by rw [hd]; group
          _ = t * y * t * y⁻¹ := by rw [← mul_inv_rev, ht2, inv_one, mul_one]
          _ = t * y * t⁻¹ * y⁻¹ := by rw [hti]
          _ = d⁻¹ := by rw [hd]; group
      have h2 : t * d * t⁻¹ = d := h1.trans hdi
      calc d * t = t * d * t⁻¹ * t := by rw [h2]
        _ = t * d := by group
    have hdb := hCt d hdQ hdt
    rcases eq_one_or_eq_of_mem_zpowers_two (hs.setup.orderOf_beta i j) hdb with h | h
    · exfalso
      apply hyb
      apply hCt y hyQ
      calc y * t = y * t * y⁻¹ * t⁻¹ * t * y := by group
        _ = t * y := by rw [← hd, h, one_mul]
    · refine ⟨y, hyQ, ?_⟩
      calc y * t * y⁻¹ = d * t := by rw [hd]; group
        _ = β * t := by rw [h]

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
