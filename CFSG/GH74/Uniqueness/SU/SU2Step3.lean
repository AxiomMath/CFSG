module

public import CFSG.GH74.Uniqueness.SU.SU2Bridge
public import CFSG.GH74.Uniqueness.SU.SU2Final

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

theorem GOPair.card_eq_mul_of_split [Finite X] [Finite V] {Y : Subgroup X} (hGO : GOPair V Y)
    {F : Subgroup V} (hF : ∀ p ∈ commSub V Y, ∀ c ∈ fixSub V Y, p * c ∈ F → p ∈ F ∧ c ∈ F) :
    Nat.card ↥F = Nat.card ↥(commSub V Y ⊓ F) * Nat.card ↥(fixSub V Y ⊓ F) := by
  rw [← Nat.card_prod]
  let f : ↥(commSub V Y ⊓ F) × ↥(fixSub V Y ⊓ F) → ↥F := fun pc =>
    ⟨(pc.1 : V) * (pc.2 : V), F.mul_mem pc.1.2.2 pc.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨p, hp⟩, ⟨c, hc⟩⟩ ⟨⟨p', hp'⟩, ⟨c', hc'⟩⟩ h
      have h1 : p * c = p' * c' := congrArg Subtype.val h
      obtain ⟨h2, h3⟩ := hGO.decomp_unique hp.1 hp'.1 hc.1 hc'.1 h1
      subst h2; subst h3
      rfl
    · rintro ⟨v, hv⟩
      obtain ⟨c, hc, hp⟩ := hGO.exists_decomp v
      obtain ⟨p, hpdef⟩ : ∃ p : V, p = v * c⁻¹ := ⟨_, rfl⟩
      have hp' : p ∈ commSub V Y := hpdef ▸ hp
      have hvpc : v = p * c := by rw [hpdef]; simp
      have hpcF : p * c ∈ F := hvpc ▸ hv
      obtain ⟨hpF, hcF⟩ := hF p hp' c hc hpcF
      exact ⟨(⟨p, hp', hpF⟩, ⟨c, hc, hcF⟩), Subtype.ext hvpc.symm⟩
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

theorem pow_smul_eq_self {t : X} {v : V} (h : t • v = v) (n : ℕ) : t ^ n • v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, h, ih]

theorem GOPair.no_trivial_involution [Finite X] [Finite V] {Y : Subgroup X} (hGO : GOPair V Y)
    {W₁ W₂ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) {s : X}
    (hs0 : s • fixSub V Y = fixSub V Y) (hs2 : orderOf s = 2)
    (hs1 : ∀ u ∈ commSub V Y, s • u = u) : False := by
  obtain ⟨h, hh⟩ := mem_omega_iff.1 hW₁.1
  obtain ⟨g, hgW₁, hgV₀⟩ : ∃ g : X, g • W₁ = fixSub V Y ∧ g⁻¹ • fixSub V Y = W₁ :=
    ⟨h⁻¹, by rw [inv_smul_eq_iff]; exact hh.symm, by rw [inv_inv]; exact hh⟩
  obtain ⟨t, ht⟩ : ∃ t : X, t = g * s * g⁻¹ := ⟨_, rfl⟩
  have htV₀ : ∀ c ∈ fixSub V Y, t • c = c := by
    intro c hc
    have hc' : g⁻¹ • c ∈ W₁ := by
      have := Subgroup.smul_mem_pointwise_smul c g⁻¹ _ hc
      rwa [hgV₀] at this
    have h1 := hs1 _ (hW₁.2.2 hc')
    calc t • c = g • s • g⁻¹ • c := by rw [ht, mul_smul, mul_smul]
      _ = g • g⁻¹ • c := by rw [h1]
      _ = c := smul_inv_smul g c
  have ht0 : t • fixSub V Y = fixSub V Y := by
    apply smul_eq_of_smul_le
    intro m hm
    obtain ⟨c, hc, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [htV₀ c hc]
    exact hc
  have ht2 : orderOf t = 2 := by
    rw [← hs2, ht]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
  have hnt : ∃ u ∈ commSub V Y, t • u ≠ u := by
    by_contra hcon
    have hall : ∀ u ∈ commSub V Y, t • u = u := fun u hu => by
      by_contra h'
      exact hcon ⟨u, hu, h'⟩
    have ht1 : t = 1 := by
      apply hGO.faithful
      intro v
      obtain ⟨c, hc, hp⟩ := hGO.exists_decomp v
      obtain ⟨p, hpdef⟩ : ∃ p : V, p = v * c⁻¹ := ⟨_, rfl⟩
      have hp' : p ∈ commSub V Y := hpdef ▸ hp
      have hv : v = p * c := by rw [hpdef]; simp
      rw [hv, smul_mul', hall p hp', htV₀ c hc]
    have hs1' : s = 1 := by
      have : g⁻¹ * t * g = s := by rw [ht]; group
      rw [← this, ht1]; group
    rw [hs1', orderOf_one] at hs2
    omega
  have hsem := (sem_consequences hGO).1 t ht0 ht2 hnt
  have hsq := hGO.sq_le hW₁ hW₂
  have hss : s * s = 1 := by rw [← pow_two]; rw [← hs2]; exact pow_orderOf_eq_one s
  have hsF : ∀ p ∈ commSub V Y, ∀ c ∈ fixSub V Y, p * c ∈ fixElt s → p ∈ fixElt s ∧ c ∈ fixElt s := by
    intro p hp c hc hpc
    have h1 : s • p = p := hs1 p hp
    have h2 : s • (p * c) = p * c := hpc
    rw [smul_mul', h1] at h2
    have h3 : s • c = c := mul_left_cancel h2
    exact ⟨h1, h3⟩
  have htF : ∀ p ∈ commSub V Y, ∀ c ∈ fixSub V Y, p * c ∈ fixElt t → p ∈ fixElt t ∧ c ∈ fixElt t := by
    intro p hp c hc hpc
    have h2 : t • (p * c) = p * c := hpc
    rw [smul_mul', htV₀ c hc] at h2
    have h3 : t • p = p := mul_right_cancel h2
    exact ⟨h3, htV₀ c hc⟩
  have hcs := hGO.card_eq_mul_of_split hsF
  have hct := hGO.card_eq_mul_of_split htF
  have h1s : commSub V Y ⊓ fixElt s = commSub V Y := inf_eq_left.2 fun u hu => hs1 u hu
  have h0t : fixSub V Y ⊓ fixElt t = fixSub V Y := inf_eq_left.2 fun c hc => htV₀ c hc
  rw [h1s] at hcs
  rw [h0t] at hct
  have hFeq : fixElt t = g • fixElt (V := V) s := by
    ext v
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · intro hv
      refine ⟨g⁻¹ • v, ?_, smul_inv_smul g v⟩
      have hv' : t • v = v := hv
      change s • g⁻¹ • v = g⁻¹ • v
      have : g • s • g⁻¹ • v = v := by
        calc g • s • g⁻¹ • v = (g * s * g⁻¹) • v := by rw [mul_smul, mul_smul]
          _ = v := by rw [← ht]; exact hv'
      calc s • g⁻¹ • v = g⁻¹ • g • s • g⁻¹ • v := by rw [inv_smul_smul]
        _ = g⁻¹ • v := by rw [this]
    · rintro ⟨s', hs', rfl⟩
      have hs'' : s • s' = s' := hs'
      change t • g • s' = g • s'
      rw [ht, mul_smul, mul_smul, inv_smul_smul, hs'']
  have hcardeq : Nat.card ↥(fixElt (V := V) t) = Nat.card ↥(fixElt (V := V) s) := by
    rw [hFeq]
    exact (Nat.card_congr (Subgroup.equivSMul g (fixElt (V := V) s)).toEquiv).symm
  have hc2 : 2 ≤ Nat.card ↥(fixSub V Y ⊓ fixElt s) := by
    obtain ⟨c₀, hc₀, hc₀1⟩ := exists_ne_one_of_ne_bot hGO.fixSub_ne_bot
    have hd : ∃ d ∈ fixSub V Y, d ≠ 1 ∧ s • d = d := by
      by_cases hfix : s • c₀ = c₀
      · exact ⟨c₀, hc₀, hc₀1, hfix⟩
      · refine ⟨c₀ * s • c₀, (fixSub V Y).mul_mem hc₀ ?_, ?_, ?_⟩
        · have : s • c₀ ∈ s • fixSub V Y := Subgroup.smul_mem_pointwise_smul c₀ s _ hc₀
          rwa [hs0] at this
        · intro h1
          apply hfix
          exact (eq_inv_of_mul_eq_one_right h1).trans
            (inv_eq_of_mul_eq_one_right (hGO.exp_two c₀))
        · rw [smul_mul', smul_smul, hss, one_smul, hGO.mul_comm' (s • c₀) c₀]
    obtain ⟨d, hd0, hd1, hds⟩ := hd
    have hne : fixSub V Y ⊓ fixElt s ≠ ⊥ := by
      intro hbot
      have : d ∈ fixSub V Y ⊓ fixElt s := ⟨hd0, hds⟩
      rw [hbot] at this
      exact hd1 this
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  rw [hcardeq, hcs] at hct
  set a := Nat.card ↥(commSub V Y ⊓ fixElt t) with ha
  set c := Nat.card ↥(fixSub V Y ⊓ fixElt s) with hc
  set A := Nat.card ↥(commSub V Y) with hA
  set B := Nat.card ↥(fixSub V Y) with hB
  have hApos : 0 < A := Nat.card_pos
  have hapos : 0 < a := Nat.card_pos
  have h1 : a * (a * c) = a * B := by
    calc a * (a * c) = a ^ 2 * c := by ring
      _ = A * c := by rw [hsem]
      _ = a * B := hct
  have h2 : a * c = B := Nat.eq_of_mul_eq_mul_left hapos h1
  have h3 : B ^ 2 = a ^ 2 * c ^ 2 := by rw [← h2]; ring
  rw [hsem] at h3
  nlinarith

end CFSG.GH74.Uniqueness.SU.SU2
