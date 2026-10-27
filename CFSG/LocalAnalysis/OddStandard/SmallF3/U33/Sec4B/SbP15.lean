module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

section Abstract

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {τ : G}

private theorem tau_mul_eq (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹) {a : G} (ha : a ∈ Q) :
    τ * a = a⁻¹ * τ := by
  calc τ * a = τ * a * τ⁻¹ * τ := by group
    _ = a⁻¹ * τ := by rw [hinv a ha]

theorem mem_sup_zpowers_iff (hτ2 : τ ^ 2 = 1) (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹) {x : G} :
    x ∈ Q ⊔ zpowers τ ↔ x ∈ Q ∨ ∃ q ∈ Q, x = q * τ := by
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ2
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  let T : Subgroup G :=
    { carrier := {x | x ∈ Q ∨ ∃ q ∈ Q, x = q * τ}
      mul_mem' := by
        rintro a b (ha | ⟨q, hq, rfl⟩) (hb | ⟨r, hr, rfl⟩)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr ⟨a * r, mul_mem ha hr, by group⟩
        · refine Or.inr ⟨q * b⁻¹, mul_mem hq (inv_mem hb), ?_⟩
          calc (q * τ) * b = q * (τ * b) := by group
            _ = q * (b⁻¹ * τ) := by rw [tau_mul_eq hinv hb]
            _ = (q * b⁻¹) * τ := by group
        · refine Or.inl ?_
          have hkey : (q * τ) * (r * τ) = q * r⁻¹ := by
            calc (q * τ) * (r * τ) = q * (τ * r) * τ := by group
              _ = q * (r⁻¹ * τ) * τ := by rw [tau_mul_eq hinv hr]
              _ = q * r⁻¹ * (τ * τ) := by group
              _ = q * r⁻¹ := by rw [hττ, mul_one]
          rw [hkey]
          exact mul_mem hq (inv_mem hr)
      one_mem' := Or.inl Q.one_mem
      inv_mem' := by
        rintro a (ha | ⟨q, hq, rfl⟩)
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ⟨q, hq, ?_⟩
          calc (q * τ)⁻¹ = τ⁻¹ * q⁻¹ := by rw [mul_inv_rev]
            _ = τ * q⁻¹ := by rw [hτinv]
            _ = q * τ := by rw [tau_mul_eq hinv (inv_mem hq)]; simp }
  have hle : Q ⊔ zpowers τ ≤ T :=
    sup_le (fun a ha => Or.inl ha)
      (Subgroup.zpowers_le.mpr (Or.inr ⟨1, Q.one_mem, by simp⟩))
  constructor
  · intro hx
    exact hle hx
  · rintro (hx | ⟨q, hq, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hq) (mem_sup_right (mem_zpowers τ))

theorem card_sup_zpowers_inv (hτ2 : τ ^ 2 = 1) (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹)
    (hτQ : τ ∉ Q) :
    Nat.card ↥(Q ⊔ zpowers τ) = 2 * Nat.card Q ∧ Q.relIndex (Q ⊔ zpowers τ) = 2 := by
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ2
  have hQfalse : ∀ q ∈ Q, q * τ ∉ Q := by
    intro q hq hmem
    refine hτQ ?_
    have h2 : q⁻¹ * (q * τ) ∈ Q := mul_mem (inv_mem hq) hmem
    rwa [show q⁻¹ * (q * τ) = τ by group] at h2
  have hxor : ∀ b ∈ Q ⊔ zpowers τ, Xor (b * τ ∈ Q) (b ∈ Q) := by
    intro b hb
    rcases (mem_sup_zpowers_iff hτ2 hinv).mp hb with hbQ | ⟨q, hq, hbq⟩
    · rw [xor_iff_or_and_not_and]
      exact ⟨Or.inr hbQ, fun h => hQfalse b hbQ h.1⟩
    · rw [hbq, xor_iff_or_and_not_and]
      refine ⟨Or.inl ?_, fun h => hQfalse q hq h.2⟩
      show (q * τ) * τ ∈ Q
      rw [mul_assoc, hττ, mul_one]
      exact hq
  have hrel : Q.relIndex (Q ⊔ zpowers τ) = 2 :=
    Subgroup.relIndex_eq_two_iff.mpr ⟨τ, mem_sup_right (mem_zpowers τ), hxor⟩
  have hcard := Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ zpowers τ)
  have hinf : Q ⊓ (Q ⊔ zpowers τ) = Q := inf_eq_left.mpr le_sup_left
  rw [hinf] at hcard
  exact ⟨by rw [← hcard, hrel], hrel⟩

theorem inf_centralizer_coset_eq (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hτ2 : τ ^ 2 = 1)
    (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹) (hY : ∀ a, a ∈ Y ↔ a ∈ Q ∧ a ^ 2 = 1) {q : G}
    (hq : q ∈ Q) : Q ⊓ centralizer ({q * τ} : Set G) = Y := by
  ext a
  rw [Subgroup.mem_inf, hY a, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨haQ, hcomm'⟩
    refine ⟨haQ, ?_⟩
    have hqa : q * a⁻¹ = a * q := by
      have key : (q * a⁻¹) * τ = (a * q) * τ := by
        calc (q * a⁻¹) * τ = q * (τ * a) := by rw [tau_mul_eq hinv haQ]; group
          _ = q * τ * a := by group
          _ = a * (q * τ) := hcomm'.symm
          _ = (a * q) * τ := by group
      exact mul_right_cancel key
    have haeq : a = a⁻¹ := by
      have hqa' : q * a⁻¹ = q * a := by rw [hqa, hcomm a haQ q hq]
      exact (mul_left_cancel hqa').symm
    rw [pow_two, mul_eq_one_iff_eq_inv]
    exact haeq
  · rintro ⟨haQ, hsq⟩
    refine ⟨haQ, ?_⟩
    have hainv : a⁻¹ = a := by
      rw [pow_two] at hsq
      exact inv_eq_of_mul_eq_one_right hsq
    calc a * (q * τ) = (a * q) * τ := by group
      _ = (q * a) * τ := by rw [hcomm a haQ q hq]
      _ = (q * a⁻¹) * τ := by rw [hainv]
      _ = (q * τ) * a := by
          rw [show (q * τ) * a = q * (τ * a) by group, tau_mul_eq hinv haQ]
          group

theorem thirty_two_le_card_inf (hτ2 : τ ^ 2 = 1) (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹)
    (hτQ : τ ∉ Q) (hQ64 : Nat.card Q = 64) {B : Subgroup G} (hB : B ⋖ Q ⊔ zpowers τ) :
    32 ≤ Nat.card ↥(B ⊓ Q) ∧ Nat.card B = 64 := by
  have hcard := (card_sup_zpowers_inv hτ2 hinv hτQ).1
  have hrelQ := (card_sup_zpowers_inv hτ2 hinv hτQ).2
  have h128 : Nat.card ↥(Q ⊔ zpowers τ) = 2 ^ 7 := by
    rw [hcard, hQ64]; norm_num
  have hP : IsPGroup 2 ↥(Q ⊔ zpowers τ) := IsPGroup.of_card h128
  have hBrel : B.relIndex (Q ⊔ zpowers τ) = 2 := relIndex_eq_two_of_covBy hP hB
  have hinf : B ⊓ (Q ⊔ zpowers τ) = B := inf_eq_left.mpr hB.le
  have hc := Subgroup.relIndex_mul_card (H := B) (K := Q ⊔ zpowers τ)
  rw [hinf, hBrel, h128] at hc
  have hB64 : Nat.card B = 64 := by
    norm_num at hc
    omega
  refine ⟨?_, hB64⟩
  have hle := card_le_two_mul_card_inf hB.le hrelQ
  omega

theorem lemma4_15_core (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQ64 : Nat.card Q = 64)
    (hτ2 : τ ^ 2 = 1) (hτQ : τ ∉ Q) (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹)
    (hY : ∀ a, a ∈ Y ↔ a ∈ Q ∧ a ^ 2 = 1) (hY16 : Nat.card Y = 16) {B : Subgroup G}
    (hB : B ⋖ Q ⊔ zpowers τ) (hZ : Nat.card ↥(B ⊓ centralizer (B : Set G)) = 16) :
    B ⊓ centralizer (B : Set G) = Y := by
  obtain ⟨h32, hB64⟩ := thirty_two_le_card_inf hτ2 hinv hτQ hQ64 hB
  set Z : Subgroup G := B ⊓ centralizer (B : Set G) with hZdef
  have hZleQ : Z ≤ Q := by
    intro z hz
    rw [hZdef] at hz
    by_contra hzQ
    have hzB : z ∈ B := hz.1
    have hzA : z ∈ Q ⊔ zpowers τ := hB.le hzB
    rcases (mem_sup_zpowers_iff hτ2 hinv).mp hzA with hzQ' | ⟨q, hq, hzq⟩
    · exact hzQ hzQ'
    · have hzcent : z ∈ centralizer (B : Set G) := hz.2
      have hBQleY : B ⊓ Q ≤ Y := by
        intro x hx
        have hxB : x ∈ B := hx.1
        have hxQ : x ∈ Q := hx.2
        have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.mp hzcent x hxB
        have hxcent : x ∈ centralizer ({z} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hxz
        have hxinf : x ∈ Q ⊓ centralizer ({z} : Set G) := ⟨hxQ, hxcent⟩
        have hYeq : Q ⊓ centralizer ({q * τ} : Set G) = Y :=
          inf_centralizer_coset_eq hcomm hτ2 hinv hY hq
        rw [hzq, hYeq] at hxinf
        exact hxinf
      have hcardle : Nat.card ↥(B ⊓ Q) ≤ Nat.card Y := Subgroup.card_le_of_le hBQleY
      rw [hY16] at hcardle
      omega
  have hex : ∃ α ∈ B, α ∉ Q := by
    by_contra h
    have hBQ : B ≤ Q := by
      intro α hαB
      by_contra hαQ
      exact h ⟨α, hαB, hαQ⟩
    have hBQeq : B = Q :=
      Subgroup.eq_of_le_of_card_ge hBQ (by omega)
    have hQcent : Q ≤ centralizer (Q : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcomm b hb a ha
    have hZeqQ : Z = Q := by
      rw [hZdef, hBQeq]
      exact inf_eq_left.mpr hQcent
    have hZ64 : Nat.card ↥Z = 64 := by rw [hZeqQ, hQ64]
    omega
  obtain ⟨α, hαB, hαQ⟩ := hex
  have hαA : α ∈ Q ⊔ zpowers τ := hB.le hαB
  rcases (mem_sup_zpowers_iff hτ2 hinv).mp hαA with hαQ' | ⟨q, hq, hαq⟩
  · exact absurd hαQ' hαQ
  · have hZleY : Z ≤ Y := by
      intro z hz
      have hzQ : z ∈ Q := hZleQ hz
      have hz' : z ∈ B ⊓ centralizer (B : Set G) := by rwa [hZdef] at hz
      have hzB : z ∈ B := hz'.1
      have hzcent : z ∈ centralizer (B : Set G) := hz'.2
      have hzα : z * α = α * z :=
        (Subgroup.mem_centralizer_iff.mp hzcent α hαB).symm
      have hzcentα : z ∈ centralizer ({α} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzα
      have hzinf : z ∈ Q ⊓ centralizer ({α} : Set G) := ⟨hzQ, hzcentα⟩
      have hYeq : Q ⊓ centralizer ({q * τ} : Set G) = Y :=
        inf_centralizer_coset_eq hcomm hτ2 hinv hY hq
      rw [hαq, hYeq] at hzinf
      exact hzinf
    have hcard : Nat.card ↥Y ≤ Nat.card ↥Z := by omega
    exact Subgroup.eq_of_le_of_card_ge hZleY hcard

end Abstract

section Ctx

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem Ctx13.tau_not_mem_Q (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    tau ∉ ctxQ t tau x₁ x₂ rho := by
  intro htau
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hcomm' : tau * x₁ = x₁ * tau :=
    IsZ4Z4E4.comm hc.q_iso htau hx₁Q
  have h1 : tau * x₁ * tau⁻¹ = x₁ := by
    rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
  have h2 : x₁ = x₁⁻¹ := h1.symm.trans hc.tau_x₁
  have hx1sq : x₁ ^ 2 = 1 := by
    rw [pow_two, mul_eq_one_iff_eq_inv]
    exact h2
  have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_of_pow_eq_one hx1sq
  rw [hc.wreath.ord_x₁] at hdvd
  norm_num at hdvd

theorem lemma4_15_proof (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Lemma4_15Concl t tau x₁ x₂ rho := by
  unfold Lemma4_15Concl
  intro B hB _ hZ
  exact lemma4_15_core (Q := ctxQ t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    (fun a ha b hb => IsZ4Z4E4.comm hc.q_iso ha hb) (IsZ4Z4E4.card hc.q_iso) hc.l44.1
    (Ctx13.tau_not_mem_Q hc) hc.tau_inv_Q (mem_ctxYq_iff hc.q_iso) (card_ctxYq hc.q_iso)
    hB hZ

end Ctx

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
