module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Syl

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

theorem EndB.mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

local notation "Q₀" => qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W
local notation "A₀" => (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z : Subgroup X)

theorem beta_comm (hc : L2Ctx hs W) {g : X} (hg : g ∈ W) : g * β₀ = β₀ * g :=
  mem_centralizer_singleton_iff.mp (hc.sylow.le hg)

theorem beta_sq (_hc : L2Ctx hs W) : β₀ * β₀ = 1 := by
  rw [← sq]
  exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)

theorem conj_zpowers_eq (hc : L2Ctx hs W) {g b : X} (hg : g ∈ W) (hb : b ∈ zpowers β₀) :
    g * b * g⁻¹ = b := by
  rcases L415.mem_zpowers_two hc.beta_sq hb with rfl | rfl
  · group
  · rw [hc.beta_comm hg]
    group

theorem card_qTilde_eq_four (hc : L2Ctx hs W) (hnc : ¬ IsCyclic ↥(pCore 2 (MBar β₀)))
    (hle : Nat.card ↥(Q₀) ≤ 4) : Nat.card ↥(Q₀) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(Q₀) := hc.sylow.isPGroup.to_le hc.qTilde_le
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hge : 2 ≤ Nat.card ↥(Q₀) := by
    have := Subgroup.card_le_of_le (zpowers_le.mpr hc.beta_mem_qTilde)
    rwa [hc.card_zpowers_beta] at this
  rw [hk] at hle hge ⊢
  rcases k with _ | _ | _ | k
  · norm_num at hge
  · exfalso
    apply hnc
    refine isCyclic_of_prime_card (p := 2) ?_
    rw [← hc.card_qTilde, hk]
    rfl
  · rfl
  · exfalso
    have : 2 ^ 3 ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem qTilde_sq (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4)
    (hnc : ¬ IsCyclic ↥(pCore 2 (MBar β₀))) {q : X} (hq : q ∈ Q₀) : q * q = 1 := by
  have hnc' : ¬ IsCyclic ↥(Q₀) := fun h =>
    hnc (isCyclic_of_surjective hc.qTildeEquiv.toMonoidHom hc.qTildeEquiv.surjective)
  have hdvd : orderOf (⟨q, hq⟩ : ↥(Q₀)) ∣ 2 ^ 2 := by
    have := _root_.orderOf_dvd_natCard (⟨q, hq⟩ : ↥(Q₀))
    rwa [h4] at this
  have h4' : orderOf (⟨q, hq⟩ : ↥(Q₀)) ≠ 2 ^ 2 := fun h =>
    hnc' (isCyclic_of_orderOf_eq_card _ (h.trans h4.symm))
  have h2 : orderOf q ∣ 2 := by
    rw [← Subgroup.orderOf_mk q hq]
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · rw [hk']
      norm_num
    · rw [hk']
      norm_num
    · exact absurd hk' h4'
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem relIndex_beta (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4) :
    (zpowers β₀).relIndex (Q₀) = 2 := by
  have h := Subgroup.relIndex_mul_card (zpowers β₀) (Q₀)
  rw [inf_of_le_left (zpowers_le.mpr hc.beta_mem_qTilde), hc.card_zpowers_beta, h4] at h
  omega

theorem comm_mem (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4) {x q : X} (hx : x ∈ W)
    (hq : q ∈ Q₀) : x * q * x⁻¹ * q⁻¹ ∈ zpowers β₀ := by
  by_cases hqb : q ∈ zpowers β₀
  · rw [hc.conj_zpowers_eq hx hqb, mul_inv_cancel]
    exact one_mem _
  · have hxq := hc.qTilde_normal hx hq
    have hxqb : x * q * x⁻¹ ∉ zpowers β₀ := by
      intro h
      apply hqb
      have h1 := hc.conj_zpowers_eq (W.inv_mem hx) h
      rw [show x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q by group] at h1
      rw [h1]
      exact h
    have hmem := inv_mul_mem_of_relIndex_two (hc.relIndex_beta h4) hq hxq hqb hxqb
    have e : x * q * x⁻¹ * q⁻¹ = q * (q⁻¹ * (x * q * x⁻¹)) * q⁻¹ := by group
    rw [e, hc.conj_zpowers_eq (hc.qTilde_le hq) hmem]
    exact hmem

theorem A_comm_mem (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W)
    (h4 : Nat.card ↥(Q₀) = 4) {x a : X} (hx : x ∈ W) (ha : a ∈ A₀) :
    x * a * x⁻¹ * a⁻¹ ∈ zpowers β₀ := by
  obtain ⟨q, hq, rfl | rfl⟩ := hc.mem_A_cases hKC ha
  · exact hc.comm_mem h4 hx hq
  · have hxz := hc.z_comm hKC (W.inv_mem hx)
    have e : x * (q * z) * x⁻¹ * (q * z)⁻¹ = x * q * x⁻¹ * q⁻¹ := by
      calc x * (q * z) * x⁻¹ * (q * z)⁻¹ = x * q * (z * x⁻¹) * z⁻¹ * q⁻¹ := by group
        _ = x * q * (x⁻¹ * z) * z⁻¹ * q⁻¹ := by rw [hxz]
        _ = x * q * x⁻¹ * q⁻¹ := by group
    rw [e]
    exact hc.comm_mem h4 hx hq

theorem exists_y0 (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4) :
    ∃ y₀ ∈ Q₀, y₀ ∉ zpowers β₀ ∧ t * y₀ * t⁻¹ = y₀ * β₀ := by
  have hlt : zpowers β₀ < Q₀ := by
    refine lt_of_le_of_ne (zpowers_le.mpr hc.beta_mem_qTilde) fun h => ?_
    have := hc.card_zpowers_beta
    rw [h, h4] at this
    norm_num at this
  obtain ⟨y₀, hy₀, hy₀b⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨y₀, hy₀, hy₀b, ?_⟩
  have hm := hc.comm_mem h4 hc.t_mem_W hy₀
  have e : t * y₀ * t⁻¹ = (t * y₀ * t⁻¹ * y₀⁻¹) * y₀ := by group
  rcases L415.mem_zpowers_two hc.beta_sq hm with h1 | h1
  · exfalso
    apply hy₀b
    have h2 : t * y₀ * t⁻¹ = y₀ := by rw [e, h1, one_mul]
    have : y₀ ∈ Q₀ ⊓ centralizer ({t} : Set X) := by
      refine ⟨hy₀, mem_centralizer_singleton_iff.mpr ?_⟩
      calc y₀ * t = t * y₀ * t⁻¹ * t := by rw [h2]
        _ = t * y₀ := by group
    rwa [hc.qTilde_inf_centralizer] at this
  · rw [e, h1]
    exact (hc.beta_comm (hc.qTilde_le hy₀)).symm

theorem mem_qTilde_cases (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4) {y₀ q : X}
    (hy₀ : y₀ ∈ Q₀) (hy₀b : y₀ ∉ zpowers β₀) (hq : q ∈ Q₀) :
    q = 1 ∨ q = β₀ ∨ q = y₀ ∨ q = y₀ * β₀ := by
  by_cases hqb : q ∈ zpowers β₀
  · rcases L415.mem_zpowers_two hc.beta_sq hqb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hm := inv_mul_mem_of_relIndex_two (hc.relIndex_beta h4) hy₀ hq hy₀b hqb
    have e : q = y₀ * (y₀⁻¹ * q) := by group
    rcases L415.mem_zpowers_two hc.beta_sq hm with h | h
    · exact Or.inr (Or.inr (Or.inl (by rw [e, h, mul_one])))
    · exact Or.inr (Or.inr (Or.inr (by rw [e, h])))

theorem A_le_centralizer (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W)
    (h4 : Nat.card ↥(Q₀) = 4) {y₀ n : X} (hy₀ : y₀ ∈ Q₀) (hy₀b : y₀ ∉ zpowers β₀)
    (hnW : n ∈ W) (hn : n * y₀ = y₀ * n) : A₀ ≤ centralizer ({n} : Set X) := by
  refine sup_le (fun q hq => ?_)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hc.z_comm hKC hnW).symm))
  rw [mem_centralizer_singleton_iff]
  have hβn := hc.beta_comm hnW
  rcases hc.mem_qTilde_cases h4 hy₀ hy₀b hq with rfl | rfl | rfl | rfl
  · group
  · exact hβn.symm
  · exact hn.symm
  · calc y₀ * β₀ * n = y₀ * (β₀ * n) := by group
      _ = y₀ * (n * β₀) := by rw [hβn]
      _ = (y₀ * n) * β₀ := by group
      _ = n * y₀ * β₀ := by rw [hn]
      _ = n * (y₀ * β₀) := by group

theorem A_elem (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4)
    (hQ2 : ∀ q ∈ Q₀, q * q = 1) :
    (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) ∧ (∀ a ∈ A₀, a * a = 1) ∧ Nat.card ↥(A₀) = 8 := by
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  obtain ⟨h1, h2, h3⟩ := L415.elem_sup (fun a ha b hb => EndB.comm_of_sq hQ2 ha hb) hQ2 hz2
    hc.z_not_mem_qTilde (fun a ha => hc.z_comm hKC (hc.qTilde_le ha))
  exact ⟨h1, h2, by rw [h3, h4]⟩

theorem t_not_mem_A (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) : t ∉ A₀ := fun htA =>
  hs.setup.not_mem_closure_beta_z (beta_mem_X i j) hs.beta.not_mem
    (hc.mem_closure_of_comm hKC htA rfl)

theorem relIndex_centralizer_eq (hc : L2Ctx hs W) (h4 : Nat.card ↥(Q₀) = 4) {y₀ : X}
    (hy₀ : y₀ ∈ Q₀) (hty₀ : t * y₀ * t⁻¹ = y₀ * β₀) :
    (W ⊓ centralizer ({y₀} : Set X)).relIndex W = 2 := by
  classical
  have hfib := L415.card_le_of_fiber (A := W) (K := centralizer ({y₀} : Set X))
    (fun g => g * y₀ * g⁻¹) (fun a _ b _ h => by
      rw [mem_centralizer_singleton_iff]
      calc a⁻¹ * b * y₀ = a⁻¹ * (b * y₀ * b⁻¹) * b := by group
        _ = a⁻¹ * (a * y₀ * a⁻¹) * b := by rw [h]
        _ = y₀ * (a⁻¹ * b) := by group)
    ({y₀, y₀ * β₀} : Finset X) (fun g hg => by
      have hm := hc.comm_mem h4 hg hy₀
      have e : g * y₀ * g⁻¹ = (g * y₀ * g⁻¹ * y₀⁻¹) * y₀ := by group
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases L415.mem_zpowers_two hc.beta_sq hm with h1 | h1
      · left
        rw [e, h1, one_mul]
      · right
        rw [e, h1]
        exact (hc.beta_comm (hc.qTilde_le hy₀)).symm)
  have hcard : ({y₀, y₀ * β₀} : Finset X).card ≤ 2 := Finset.card_le_two
  have h2 := Subgroup.relIndex_mul_card (W ⊓ centralizer ({y₀} : Set X)) W
  rw [inf_of_le_left inf_le_left] at h2
  have hpos : 0 < Nat.card ↥(W ⊓ centralizer ({y₀} : Set X)) := Nat.card_pos
  have hle : (W ⊓ centralizer ({y₀} : Set X)).relIndex W ≤ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [h2]
    calc Nat.card W ≤ Nat.card ↥(W ⊓ centralizer ({y₀} : Set X)) *
          ({y₀, y₀ * β₀} : Finset X).card := hfib
      _ ≤ Nat.card ↥(W ⊓ centralizer ({y₀} : Set X)) * 2 := Nat.mul_le_mul_left _ hcard
      _ = 2 * Nat.card ↥(W ⊓ centralizer ({y₀} : Set X)) := mul_comm _ _
  have hne1 : (W ⊓ centralizer ({y₀} : Set X)).relIndex W ≠ 1 := fun h => by
    have htC := (Subgroup.relIndex_eq_one.mp h) hc.t_mem_W
    have h1 : t * y₀ = y₀ * t := mem_centralizer_singleton_iff.mp htC.2
    have : y₀ * β₀ = y₀ * 1 := by
      rw [← hty₀, h1, mul_one]
      group
    exact hs.beta.ne_one (mul_left_cancel this)
  have hne0 : (W ⊓ centralizer ({y₀} : Set X)).relIndex W ≠ 0 := fun h => by
    rw [h, zero_mul] at h2
    exact (Nat.card_pos (α := W)).ne' h2.symm
  omega

theorem eq_U_of_normal_X (hc : L2Ctx hs W)
    (hWX : ∀ g ∈ W, ∀ x ∈ X₈, g * x * g⁻¹ ∈ X₈) :
    W = V ⊓ centralizer ({β₀} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T₀ ≤ centralizer ((X₈ : Subgroup X) : Set X) := fun g hg =>
    mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hs.setup.X_le_center_T hx).2 g hg).symm
  have hCW : W ⊓ centralizer ((X₈ : Subgroup X) : Set X) = T₀ :=
    hs.lemma44a_X.2.eq_of_le (le_inf hc.T_le hTC) inf_le_right
      (hc.sylow.isPGroup.to_le inf_le_left)
  have key : ∀ g ∈ W, ∀ x ∈ T₀, g * x * g⁻¹ ∈ T₀ := by
    intro g hg x hx
    rw [← hCW] at hx ⊢
    refine ⟨W.mul_mem (W.mul_mem hg hx.1) (W.inv_mem hg), mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' := hWX g⁻¹ (W.inv_mem hg) y hy
    rw [inv_inv] at hy'
    have h1 := (mem_centralizer_iff.mp hx.2) _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  refine hc.eq_U_of_le_normalizer fun g hg => EndB.mem_normalizer_of_conj (key g hg) ?_
  intro x hx
  have := key g⁻¹ (W.inv_mem hg) x hx
  rwa [inv_inv] at this

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
