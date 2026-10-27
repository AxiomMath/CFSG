module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterSylowComplement
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterSylowCore

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem not_dvd_card_of_invariant
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 3)
    (hinv : (∃ Q₁ : Subgroup G, IsSylowOf p Q₁ (C t) ∧
      Subgroup.zpowers s₀ ⊔ torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G) ∧
      C t ⊓ Subgroup.normalizer (Q₁ : Set G) = Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
        (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)) ∧
      ∀ X : Subgroup G, X ≤ C t → IsPGroup p X → X ≠ ⊥ →
        torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → Nat.card X = p ^ f) :
    ¬ p ^ (f + 1) ∣ Nat.card G := by
  classical
  intro hdvd
  have : Fact p.Prime := ⟨h.prime⟩
  have hL := h.localData
  obtain ⟨⟨Q₁, hQ₁, hsW, hCN⟩, hX⟩ := hinv
  obtain ⟨hcard, -⟩ := h.sylow_C_facts hQ₁
  obtain ⟨R, hR, hWR, hBR, hQR, hRN, hVR, hRH, hodd⟩ := h.exists_odd_sup he hQ₁ hsW hCN
  obtain ⟨U, hUR, hRU, hdisj, hrel, hcopW⟩ := h.exists_complement hR hWR hBR hRH
  have hcopB := h.coprime_card_U_B hQ₁ hsW hCN hBR hRN hUR hRU hdisj
  obtain ⟨hUodd, hVU, hQU, hpU, hcent, hCV⟩ :=
    h.complement_facts he hQ₁ hR hUR hRU hrel hcopW hcopB hVR hQR
  obtain ⟨g, hgN, hgQ, hg⟩ := exists_mem_normalizer_not_mem hcard hdvd
  have hgodd : Odd (orderOf g) := Odd.of_dvd_nat h.odd.pow (orderOf_dvd_of_pow_eq_one hg)
  have hgU : g ∈ U := hpU g (hodd g hgN hgodd) hg
  have hUne : U ≠ Q₁ := fun hUQ => hgQ (hUQ ▸ hgU)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL.t_sq) hL.t_ne_one
  have hs2 : orderOf s₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL.s_sq) hL.s_ne_one
  have hts1 : t * s₀ * (t * s₀) = 1 := by
    calc t * s₀ * (t * s₀) = t * (s₀ * t) * s₀ := by group
      _ = t * (t * s₀) * s₀ := by rw [← hL.ts]
      _ = (t * t) * (s₀ * s₀) := by group
      _ = 1 := by rw [hL.t_sq, hL.s_sq, one_mul]
  have hts2 : orderOf (t * s₀) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hts1) fun h1 => hL.s_ne ?_
    calc s₀ = t⁻¹ * (t * s₀) := by group
      _ = t := by rw [h1, mul_one, inv_eq_of_mul_eq_one_left hL.t_sq]
  have hUt : Nat.card (U ⊓ Subgroup.centralizer {t} : Subgroup G) = p ^ f := by
    apply Nat.dvd_antisymm (hcent t ht2)
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (le_inf hQU hQ₁.le)
  have hUC : ¬ U ≤ C t := by
    intro hle
    apply hUne
    symm
    apply Subgroup.eq_of_le_of_card_ge hQU
    have h1 : Nat.card U = p ^ f := by rw [← hUt, inf_eq_left.mpr hle]
    exact (h1.trans hcard.symm).le
  obtain ⟨b₀, hb₀, hb₀1⟩ := (Subgroup.bot_or_exists_ne_one ((N t).map (C t).subtype)).resolve_left
    h.B_ne_bot
  have hBU : (N t).map (C t).subtype ≤ Subgroup.normalizer (U : Set G) := hBR.trans hRU
  have hfree : ∀ u : G, u * u = 1 → u ∈ Subgroup.normalizer (U : Set G) →
      (∀ b ∈ (N t).map (C t).subtype, u * b * u⁻¹ = b⁻¹) →
        U ⊓ Subgroup.centralizer {u} ≠ ⊥ := by
    intro u hu2 huU huB hbot
    exact hUC ((le_centralizer_of_inf_centralizer_eq_bot hUodd hu2 huU hbot huB hL.B_odd hBU
      hb₀).trans (h.confine b₀ hb₀ hb₀1))
  have htU : t ∈ Subgroup.normalizer (U : Set G) :=
    hVU (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hsU : s₀ ∈ Subgroup.normalizer (U : Set G) :=
    hVU (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))
  have hts : ∀ b ∈ (N t).map (C t).subtype, t * s₀ * b * (t * s₀)⁻¹ = b⁻¹ := by
    intro b hb
    have hbt : b⁻¹ * t = t * b⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hL.B_le (inv_mem hb))
    calc t * s₀ * b * (t * s₀)⁻¹ = t * (s₀ * b * s₀⁻¹) * t⁻¹ := by group
      _ = t * b⁻¹ * t⁻¹ := by rw [hL.s_inv b hb]
      _ = b⁻¹ := by rw [← hbt, mul_inv_cancel_right]
  have hU2 := hfree s₀ hL.s_sq hsU hL.s_inv
  have hU3 := hfree (t * s₀) hts1 (Subgroup.mul_mem _ htU hsU) hts
  have hV4 := h.isKleinFour_V
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq hUodd hVU
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)) hL.t_ne_one hL.s_ne_one hL.s_ne.symm
  rw [hCV, one_pow, mul_one] at hBW
  have hUp : IsPGroup p U := by
    have hUdvd : Nat.card U ∣ p ^ (f * 3) := by
      rw [hBW, pow_mul, pow_three']
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (hcent t ht2) (hcent s₀ hs2)) (hcent _ hts2)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow h.prime).mp hUdvd
    exact IsPGroup.of_card hi
  obtain ⟨τ, hτt, hτs, hτW⟩ := h.exists_three_cycle
  have hτN : τ ∈ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem hτW
  have hWU : torusW G t s₀ ≤ Subgroup.normalizer (U : Set G) := hWR.trans hRU
  have hWV : torusW G t s₀ ≤ Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
    rw [torusW]
    exact Subgroup.map_subtype_le _
  have hcardX : ∀ x g : G, g * x * g⁻¹ = t →
      g ∈ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G) →
      x ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ → U ⊓ Subgroup.centralizer {x} ≠ ⊥ →
        Nat.card (U ⊓ Subgroup.centralizer {x} : Subgroup G) = p ^ f := by
    intro x g hgx hgW hxV hne
    have hWX : torusW G t s₀ ≤
        Subgroup.normalizer ((U ⊓ Subgroup.centralizer {x} : Subgroup G) : Set G) := by
      intro w hw
      apply mem_normalizer_of_conj_mem
      rintro y ⟨hyU, hyx⟩
      have hwx : w ∈ Subgroup.centralizer {x} :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hWV hw) x hxV).symm
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hWU hw) y).mp hyU,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hwx hyx) (Subgroup.inv_mem _ hwx)⟩
    have hle : (U ⊓ Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom ≤ C t := by
      rw [← hgx]
      exact map_conj_le_centralizer inf_le_right
    have hne' : (U ⊓ Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom ≠ ⊥ :=
      fun hb => hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hb)
    have h1 := hX _ hle (hUp.to_inf_left.map _) hne' (le_normalizer_map_conj hgW hWX)
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1
  have hc2 := hcardX s₀ τ⁻¹ (by rw [inv_inv, ← hτt]; group) (inv_mem hτN)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)) hU2
  have hc3 := hcardX (t * s₀) (τ⁻¹ * τ⁻¹) (by rw [← hτs, ← hτt]; group)
    (Subgroup.mul_mem _ (inv_mem hτN) (inv_mem hτN))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))) hU3
  apply h.not_cube
  have hU3 : Nat.card U = (p ^ f) ^ 3 := by
    rw [hBW, hUt, hc2, hc3, pow_three']
  rw [← hU3]
  exact Subgroup.card_subgroup_dvd_card U

theorem card_sylow_of_mod_four_eq_three_of_invariant
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 3)
    (hinv : (∃ Q₁ : Subgroup G, IsSylowOf p Q₁ (C t) ∧
      Subgroup.zpowers s₀ ⊔ torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G) ∧
      C t ⊓ Subgroup.normalizer (Q₁ : Set G) = Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
        (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)) ∧
      ∀ X : Subgroup G, X ≤ C t → IsPGroup p X → X ≠ ⊥ →
        torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → Nat.card X = p ^ f)
    (T : Sylow p G) : Nat.card T = p ^ f := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hndvd := h.not_dvd_card_of_invariant he hinv
  obtain ⟨⟨Q₁, hQ₁, -, -⟩, -⟩ := hinv
  have hcard : Nat.card Q₁ = p ^ f := (h.sylow_C_facts hQ₁).1
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h1 : f ≤ (Nat.card G).factorization p :=
    (h.prime.pow_dvd_iff_le_factorization hG0).mp (hcard ▸ Subgroup.card_subgroup_dvd_card Q₁)
  have h2 : ¬ f + 1 ≤ (Nat.card G).factorization p := fun h2 =>
    hndvd ((h.prime.pow_dvd_iff_le_factorization hG0).mpr h2)
  rw [Sylow.card_eq_multiplicity]
  congr 1
  omega

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
