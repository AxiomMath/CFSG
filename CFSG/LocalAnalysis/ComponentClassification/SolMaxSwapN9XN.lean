module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace ExactRho

@[expose] noncomputable def altFixPerm {n : ℕ} (σ : Perm (Fin n)) : Subgroup (Perm (Fin n)) :=
  (fixAlt σ).map (alternatingGroup (Fin n)).subtype

theorem mem_altFixPerm {n : ℕ} {σ g : Perm (Fin n)} :
    g ∈ altFixPerm σ ↔ g ∈ alternatingGroup (Fin n) ∧ g.support ⊆ σ.supportᶜ := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, mem_fixAlt.mp hk⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, h1⟩, mem_fixAlt.mpr h2, rfl⟩

noncomputable def altFixPermEquiv {n : ℕ} (σ : Perm (Fin n)) :
    alternatingGroup ↥(σ.supportᶜ : Finset (Fin n)) ≃* altFixPerm σ :=
  (fixAltEquiv σ).trans (Subgroup.equivMapOfInjective (fixAlt σ) (alternatingGroup (Fin n)).subtype
    (alternatingGroup (Fin n)).subtype_injective)

theorem card_altFixPerm {n : ℕ} {σ : Perm (Fin n)} (h2 : 2 ≤ n - σ.support.card) :
    Nat.card (altFixPerm σ) = (n - σ.support.card).factorial / 2 := by
  rw [altFixPerm, Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective]
  exact card_fixAlt h2

private theorem five_le_card_fixed {n : ℕ} {σ : Perm (Fin n)} (h5 : 5 ≤ n - σ.support.card) :
    5 ≤ Nat.card ↥(σ.supportᶜ : Finset (Fin n)) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  exact h5

theorem isSimpleGroup_altFixPerm {n : ℕ} {σ : Perm (Fin n)} (h5 : 5 ≤ n - σ.support.card) :
    IsSimpleGroup (altFixPerm σ) := by
  have : IsSimpleGroup (alternatingGroup ↥(σ.supportᶜ : Finset (Fin n))) :=
    alternatingGroup.isSimpleGroup (five_le_card_fixed h5)
  exact (altFixPermEquiv σ).symm.isSimpleGroup

theorem exists_not_comm_altFixPerm {n : ℕ} {σ : Perm (Fin n)} (h5 : 5 ≤ n - σ.support.card) :
    ∃ a b : altFixPerm σ, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := alt_nonabelian_of_card (Ω := ↥(σ.supportᶜ : Finset (Fin n)))
    ((by norm_num : 4 ≤ 5).trans (five_le_card_fixed h5))
  refine ⟨altFixPermEquiv σ a, altFixPermEquiv σ b, fun h => hab ?_⟩
  apply (altFixPermEquiv σ).injective
  rw [map_mul, map_mul]
  exact h

section Exact

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M F : Subgroup X} {DF : Finset (Fin n)} {f : X} {L N : Subgroup X}

theorem J_le_normalizer (hs : Setting t J n e E D M) : J ≤ normalizer (M : Set X) :=
  le_normalizer_of_swap (hs.cent (mem_centralizer_singleton_iff.mpr rfl)) hs.le hs.pc hs.swap
    hs.diag

theorem f_mem_normalizer (hs : Setting t J n e E D M) (hx : ExactData t J n e F DF f L N) :
    f ∈ normalizer (M : Set X) :=
  J_le_normalizer hs (hx.FJ hx.fF)

theorem L_le_normalizer (hs : Setting t J n e E D M) (hx : ExactData t J n e F DF f L N) :
    L ≤ normalizer (M : Set X) :=
  hx.LJ.trans (J_le_normalizer hs)

theorem f_mul_self (hx : ExactData t J n e F DF f L N) : f * f = 1 := by
  rw [← sq]
  exact (card_sq_of_klein hx.Fk).2 f hx.fF

variable {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem card_support_rho (hs : Setting t J n e E D M) (hx : ExactData t J n e F DF f L N)
    (hρ : IsPermAction θ ρ) : (ρ ⟨f, f_mem_normalizer hs hx⟩).support.card = 4 := by
  rw [hs.sig.card_support_rho_of_swap hs.cent hs.le hs.pc hs.swap hs.diag θ hρ (hx.FJ hx.fF)
    (f_mem_normalizer hs hx)]
  exact (hs.sig.ofFour hx.FJ hx.Fk hx.DFc hx.Fs).card_support_coreImage_E hx.fF hx.f1

theorem rho_eq_one_of_mem_core (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) (hρ : IsPermAction θ ρ) {z : X}
    (hz : z ∈ core (centralizer ({f} : Set X))) (hzN : z ∈ normalizer (M : Set X)) :
    ρ ⟨z, hzN⟩ = 1 := by
  have h4 := card_support_rho hs hx hρ
  have hK : core (centralizer ({f} : Set X)) ⊓ normalizer (M : Set X) ≤
      UnbalancedLayer.coreActionKernel M :=
    hρ.le_coreActionKernel (f_mem_normalizer hs hx) (f_mul_self hx) h4.le (by omega) inf_le_right
      inf_le_left
  exact hρ.eq_one_of_mem_coreActionKernel (by omega) (hK ⟨hz, hzN⟩)

theorem rho_mem_altFixPerm (hs : Setting t J n e E D M) (hx : ExactData t J n e F DF f L N)
    (hρ : IsPermAction θ ρ) {z : X} (hz : z ∈ L) :
    ρ ⟨z, L_le_normalizer hs hx hz⟩ ∈ altFixPerm (ρ ⟨f, f_mem_normalizer hs hx⟩) := by
  have hperfL : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hx.LC hx.Lpc
  have hLf : L ≤ centralizer ({f} : Set X) := hx.LC.trans inf_le_right
  refine mem_altFixPerm.mpr ⟨IsPermAction.mem_alternatingGroup_of_perfect
    (L_le_normalizer hs hx) hperfL hz, fun ω hω => ?_⟩
  rw [Finset.mem_compl]
  intro hωf
  have h1 := fix_support_rho_of_perfect (f_mem_normalizer hs hx) (f_mul_self hx)
    (card_support_rho hs hx hρ).le (L_le_normalizer hs hx) hLf hperfL hz ω hωf
  exact (Perm.mem_support.mp hω) h1

theorem exists_rho_eq (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) (hρ : IsPermAction θ ρ) {g : Perm (Fin n)}
    (hg : g ∈ altFixPerm (ρ ⟨f, f_mem_normalizer hs hx⟩)) :
    ∃ (z : X) (hz : z ∈ L), ρ ⟨z, L_le_normalizer hs hx hz⟩ = g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN := L_le_normalizer hs hx
  have hJN := J_le_normalizer hs
  have hperfL : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hx.LC hx.Lpc
  obtain ⟨eL⟩ := hx.Ltype
  have hLK : ¬ L ≤ UnbalancedLayer.coreActionKernel M := by
    intro hLK
    have hperfJ : ⁅J, J⁆ = J :=
      UnbalancedCorr.commutator_eq_of_isPComponent hs.sig.pair.1.2.1 hs.sig.pair.1.2.2.1
    have hJK : ¬ J ≤ UnbalancedLayer.coreActionKernel M :=
      hs.sig.not_le_coreActionKernel_of_swap hs.cent hs.le hs.pc hs.swap hs.diag θ
    have hkJ := mem_coreNOf_of_rho_eq_one_of_not_le hρ hJN (by omega : 5 ≤ n) e hperfJ hJK
    have hLO : L ≤ (pPrimeCore 2 ↥J).map J.subtype := fun z hz =>
      hkJ z (hx.LJ hz) (hρ.eq_one_of_mem_coreActionKernel (by omega) (hLK hz))
    have h1 := card_dvd_of_le hLO
    rw [card_map_of_injective J.subtype_injective] at h1
    have h2 := two_dvd_card_of_isPComponent_in hx.LC hx.Lpc
    have h3 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    exact absurd h3 (by
      rw [Nat.coprime_two_left]
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))
  have h4 := card_support_rho hs hx hρ
  have hQc : Nat.card (altFixPerm (ρ ⟨f, f_mem_normalizer hs hx⟩)) ≤ (5 : ℕ).factorial / 2 := by
    have h5 : 2 ≤ n - (ρ ⟨f, f_mem_normalizer hs hx⟩).support.card := by omega
    have h6 := card_altFixPerm h5
    rw [h4, show n - 4 = 5 by omega] at h6
    exact h6.le
  exact (hρ.image_eq_of_le hLN (by norm_num : 5 ≤ 5) eL hperfL hLK hQc
    (fun z hz => rho_mem_altFixPerm hs hx hρ hz)).1 g hg

theorem rho_mem_altFixPerm_of_mem_fixedLayer (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) (hρ : IsPermAction θ ρ) {y : X}
    (hy : y ∈ GSLit.fixedLayer M (zpowers f)) (hyN : y ∈ normalizer (M : Set X)) :
    ρ ⟨y, hyN⟩ ∈ altFixPerm (ρ ⟨f, f_mem_normalizer hs hx⟩) := by
  have h4 := card_support_rho hs hx hρ
  obtain ⟨-, -, -, hsupp, -⟩ := SwapN9.fixedLayer_data hs.le hs.pc hρ (f_mem_normalizer hs hx)
    (f_mul_self hx) h4.le (by omega) (N := GSLit.fixedLayer M (zpowers f)) rfl
  obtain ⟨hyM, hyS⟩ := hsupp y hy
  have hc : ρ ⟨y, hyN⟩ = coreImage θ hyM := hρ.apply_of_mem (by omega) ⟨y, hyM⟩
  rw [hc]
  exact mem_altFixPerm.mpr ⟨coreImage_mem θ hyM, hyS⟩

end Exact

end ExactRho

section Exact

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M F : Subgroup X} {DF : Finset (Fin n)} {f : X} {L N : Subgroup X}

theorem ExactData.conj_eq (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) {y : X}
    (hy : y ∈ GSLit.fixedLayer M (zpowers f)) (hy' : y ∉ core M) : conjBy N y = N := by
  classical
  by_contra hne
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hLN := ExactRho.L_le_normalizer hs hx
  have hy1 := GSLit.fixedLayer_le_inf M (zpowers f) hy
  have hyM : y ∈ M := (mem_inf.mp hy1).1
  have hyC : y ∈ centralizer ({f} : Set X) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers f))
      (mem_inf.mp hy1).2
  have hyN : y ∈ normalizer (M : Set X) := le_normalizer hyM
  obtain ⟨hNyC, hNypc⟩ := isPComponent_conj hx.NC hx.Npc hyC
  have hcomm := GSThmB.B5a.commutator_le_oddCoreIn_of_ne hx.NC hNyC hx.Npc hNypc (Ne.symm hne)
  have hgmem := ExactRho.rho_mem_altFixPerm_of_mem_fixedLayer hs hn hx hρ hy hyN
  have h4 := ExactRho.card_support_rho hs hx hρ
  obtain ⟨g, hg⟩ : ∃ g : Perm (Fin n), ρ ⟨y, hyN⟩ = g := ⟨_, rfl⟩
  rw [hg] at hgmem
  have hcommute : ∀ a ∈ ExactRho.altFixPerm (ρ ⟨f, ExactRho.f_mem_normalizer hs hx⟩),
      ∀ b ∈ ExactRho.altFixPerm (ρ ⟨f, ExactRho.f_mem_normalizer hs hx⟩), a * b = b * a := by
    intro a ha b hb
    obtain ⟨l, hl, rfl⟩ := ExactRho.exists_rho_eq hs hn hx hρ ha
    have hb' : g⁻¹ * b * g ∈ ExactRho.altFixPerm (ρ ⟨f, ExactRho.f_mem_normalizer hs hx⟩) :=
      mul_mem (mul_mem (inv_mem hgmem) hb) hgmem
    obtain ⟨l', hl', hl'b⟩ := ExactRho.exists_rho_eq hs hn hx hρ hb'
    have hz : y * l' * y⁻¹ ∈ conjBy N y := ⟨l', hx.LN hl', rfl⟩
    have hcm := hcomm (Subgroup.commutator_mem_commutator (hx.LN hl) hz)
    rw [commutatorElement_def] at hcm
    have hlN' : l ∈ normalizer (M : Set X) := hLN hl
    have hzN' : y * l' * y⁻¹ ∈ normalizer (M : Set X) :=
      mul_mem (mul_mem hyN (hLN hl')) (inv_mem hyN)
    have hcN : l * (y * l' * y⁻¹) * l⁻¹ * (y * l' * y⁻¹)⁻¹ ∈ normalizer (M : Set X) :=
      mul_mem (mul_mem (mul_mem hlN' hzN') (inv_mem hlN')) (inv_mem hzN')
    have h1 := ExactRho.rho_eq_one_of_mem_core hs hn hx hρ hcm hcN
    have h2 : ρ ⟨l * (y * l' * y⁻¹) * l⁻¹ * (y * l' * y⁻¹)⁻¹, hcN⟩ =
        ρ ⟨l, hlN'⟩ * (g * ρ ⟨l', hLN hl'⟩ * g⁻¹) * (ρ ⟨l, hlN'⟩)⁻¹ *
          (g * ρ ⟨l', hLN hl'⟩ * g⁻¹)⁻¹ := by
      have : (⟨l * (y * l' * y⁻¹) * l⁻¹ * (y * l' * y⁻¹)⁻¹, hcN⟩ : ↥(normalizer (M : Set X))) =
          ⟨l, hlN'⟩ * (⟨y, hyN⟩ * ⟨l', hLN hl'⟩ * ⟨y, hyN⟩⁻¹) * ⟨l, hlN'⟩⁻¹ *
            (⟨y, hyN⟩ * ⟨l', hLN hl'⟩ * ⟨y, hyN⟩⁻¹)⁻¹ := rfl
      rw [this]
      simp only [map_mul, map_inv, hg]
    rw [h2, hl'b, show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at h1
    have h3 : ρ ⟨l, hlN'⟩ * b * (ρ ⟨l, hlN'⟩)⁻¹ = b := mul_inv_eq_one.mp h1
    calc ρ ⟨l, hlN'⟩ * b = (ρ ⟨l, hlN'⟩ * b * (ρ ⟨l, hlN'⟩)⁻¹) * ρ ⟨l, hlN'⟩ := by group
      _ = b * ρ ⟨l, hlN'⟩ := by rw [h3]
  obtain ⟨a, b, hab⟩ := ExactRho.exists_not_comm_altFixPerm
    (σ := ρ ⟨f, ExactRho.f_mem_normalizer hs hx⟩) (by omega)
  exact hab (Subtype.ext (hcommute a a.2 b b.2))

end Exact

end CFSG.ComponentClassification.SolMax.SwapP2
