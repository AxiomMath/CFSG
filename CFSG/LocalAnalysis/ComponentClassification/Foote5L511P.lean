module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511O
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem eight_le_card_R (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) :
    8 ≤ Nat.card ↥(S ⊓ L) := by
  classical
  obtain ⟨m, hm1, ⟨e⟩⟩ := h.exists_dihedral_R
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm : m = 1 := by omega
    subst hm
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    apply hab
    have hcomm : ∀ u v : DihedralGroup (2 ^ 1), u * v = v * u := by decide
    have h1 := hcomm (e ⟨a, ha⟩) (e ⟨b, hb⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  omega

theorem false_of_pgl_mem_E (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {E : Subgroup G} (hES : E ≤ S)
    (hTE : T ≤ normalizer (E : Set G)) (hEsq : ∀ e ∈ E, e * e = 1) (hE8 : Nat.card E = 8)
    (htE : t ∈ E) (hzE : z ∈ E) {e : G} (heE : e ∈ E) (helin : actG L ε e ∈ Lin)
    (heinn : actG L ε e ∉ innAut5 𝕊) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : E ≤ normalizer (L : Set G) := hES.trans h.S_le
  have heS := hES heE
  have heN := h.S_le heS
  have htN := h.S_le h.tS
  set α := actG L ε e with hα
  set τ := psi L ε ⟨t, h.tL⟩ with hτ
  set Eb := actImage L ε E with hEb
  have hEbcard : Nat.card Eb ≤ 4 := by
    have h1 := card_eq_card_inf_mul_card_actImage ε hEN
    have hz1 : z ≠ 1 := fun h2 => by
      have := h.z2
      rw [h2, orderOf_one] at this
      omega
    have h2 : 2 ≤ Nat.card ↥(E ⊓ coreActionKernel L) :=
      (Nat.succ_le_of_lt (Subgroup.one_lt_card_iff_ne_bot _ |>.mpr fun hb => hz1 (by
        have h3 : z ∈ E ⊓ coreActionKernel L := mem_inf.mpr ⟨hzE, h.Q_le h.zQ⟩
        rw [hb, mem_bot] at h3
        exact h3)))
    rw [hE8, ← hEb] at h1
    by_contra hlt
    push Not at hlt
    have : 2 * 5 ≤ Nat.card ↥(E ⊓ coreActionKernel L) * Nat.card Eb := Nat.mul_le_mul h2 hlt
    omega
  have htb : actG L ε t = MulAut.conj τ := actG_of_mem_self ε h.tL
  have hτ1 : τ ≠ 1 := fun h1 => h.t_not_mem_Q ((h.actG_eq_one_iff_mem_Q ε h.tS).mp
    (by rw [htb, h1, map_one]))
  have hEbinn : ∀ x ∈ Eb ⊓ innAut5 𝕊, x = 1 ∨ x = MulAut.conj τ := by
    have hK : Nat.card ↥(Eb ⊓ innAut5 𝕊) ≤ 2 := by
      have hlt : Eb ⊓ innAut5 𝕊 < Eb := lt_of_le_of_ne inf_le_left fun h1 => heinn (by
        have h2 : α ∈ Eb := actG_mem_actImage ε hEN heE
        rw [← h1] at h2
        exact (mem_inf.mp h2).2)
      have hdvd := Subgroup.card_dvd_of_le (inf_le_left : Eb ⊓ innAut5 𝕊 ≤ Eb)
      have hne := Subgroup.card_lt_of_lt hlt
      obtain ⟨k, hk⟩ := hdvd
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · simp at hk
          omega
        · omega
        · omega
      have : 2 * Nat.card ↥(Eb ⊓ innAut5 𝕊) ≤ Nat.card Eb := by
        rw [hk, mul_comm]
        exact Nat.mul_le_mul_left _ hk2
      omega
    have htmem : MulAut.conj τ ∈ Eb ⊓ innAut5 𝕊 :=
      mem_inf.mpr ⟨htb ▸ actG_mem_actImage ε hEN htE, ⟨τ, rfl⟩⟩
    have hconj1 : MulAut.conj τ ≠ 1 := fun h1 => hτ1 (h.conj_injective ε (h1.trans
      (map_one _).symm))
    exact fun x hx => eq_one_or_eq_of_card_le_two hK htmem hconj1 hx
  have hmove : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ ∨ α ρ = τ⁻¹ * ρ := by
    intro ρ hρ
    obtain ⟨ρ₀, hρ₀R, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
    have hρ₀S := (mem_inf.mp hρ₀R).1
    have hρ₀N := h.S_le hρ₀S
    have hcE : (ρ₀ : G) * e * (ρ₀ : G)⁻¹ * e⁻¹ ∈ E :=
      mul_mem ((mem_normalizer_iff.mp (hTE (h.ST hρ₀S)) e).mp heE) (inv_mem heE)
    have hcact : actG L ε ((ρ₀ : G) * e * (ρ₀ : G)⁻¹ * e⁻¹) =
        MulAut.conj (psi L ε ρ₀ * (α (psi L ε ρ₀))⁻¹) := by
      rw [actG_mul ε (mul_mem (mul_mem hρ₀N heN) (inv_mem hρ₀N)) (inv_mem heN),
        actG_mul ε (mul_mem hρ₀N heN) (inv_mem hρ₀N), actG_mul ε hρ₀N heN,
        actG_inv ε hρ₀N, actG_inv ε heN, actG_of_mem_self ε ρ₀.2]
      rw [show MulAut.conj (psi L ε ⟨(ρ₀ : G), ρ₀.2⟩) * α * (MulAut.conj (psi L ε ⟨(ρ₀ : G),
          ρ₀.2⟩))⁻¹ * α⁻¹ = MulAut.conj (psi L ε ρ₀) * (α * MulAut.conj (psi L ε ρ₀)⁻¹ * α⁻¹)
          by rw [map_inv]; group]
      rw [mulAut_mul_conj_mul_inv, map_inv, ← map_mul]
    have hcmem : actG L ε ((ρ₀ : G) * e * (ρ₀ : G)⁻¹ * e⁻¹) ∈ Eb ⊓ innAut5 𝕊 :=
      mem_inf.mpr ⟨actG_mem_actImage ε hEN hcE, by rw [hcact]; exact ⟨_, rfl⟩⟩
    rcases hEbinn _ hcmem with h1 | h1
    · left
      rw [hcact, ← map_one MulAut.conj] at h1
      have h2 := h.conj_injective ε h1
      rw [mul_inv_eq_one] at h2
      exact h2.symm
    · right
      rw [hcact] at h1
      have h2 := h.conj_injective ε h1
      calc α (psi L ε ρ₀) = (psi L ε ρ₀ * (α (psi L ε ρ₀))⁻¹)⁻¹ * psi L ε ρ₀ := by group
        _ = τ⁻¹ * psi L ε ρ₀ := by rw [h2]
  have hfix := hD.pgl_fixed (h.Rbar ε) α helin heinn
    (by rw [hα, ← actG_mul ε heN heN, hEsq e heE, actG_one]) (h.actG_map_Rbar ε heS)
  set F := (h.Rbar ε : Subgroup 𝕊) ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id 𝕊) with hF
  have hRb4 : Nat.card (h.Rbar ε : Subgroup 𝕊) ≤ 4 := by
    by_cases hex : ∃ ρ₁ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ₁ ≠ ρ₁
    · obtain ⟨ρ₁, hρ₁, hρ₁α⟩ := hex
      have hρ₁t := (hmove ρ₁ hρ₁).resolve_left hρ₁α
      have h1 := card_le_two_mul_of_cover (P := (h.Rbar ε : Subgroup 𝕊)) (S := F) (h := ρ₁)
        fun x hx => by
          rcases hmove x hx with h2 | h2
          · exact Or.inl (mem_inf.mpr ⟨hx, h2⟩)
          · right
            refine mem_inf.mpr ⟨mul_mem (inv_mem hρ₁) hx, ?_⟩
            change α (ρ₁⁻¹ * x) = ρ₁⁻¹ * x
            rw [map_mul, map_inv, hρ₁t, h2]
            group
      omega
    · push Not at hex
      have h1 : (h.Rbar ε : Subgroup 𝕊) ≤ F := fun x hx => mem_inf.mpr ⟨hx, hex x hx⟩
      have := card_le_of_le h1
      omega
  have h8 := h.eight_le_card_R hna
  rw [← h.card_Rbar ε] at h8
  omega

end Sec5

end CFSG.ComponentClassification.Foote5
