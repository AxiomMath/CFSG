module

public import CFSG.GH74.GLS.C3.Layer1.BkL27K
public import CFSG.GH74.GLS.C3.Layer1.BkXuLift
public import CFSG.GH74.GLS.C3.Layer1.Back113E

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G]

theorem involution_mem_R_seven
    {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (hK7 : HasL2Model (kBar K) (fun r => r = 7))
    (hnoV2 : ¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K')
    {u : G} (huT : u ∈ T) (hu2 : u * u = 1) : u ∈ (T ⊓ K) ⊔ Q := by
  by_contra hnot
  have hu1 : u ≠ 1 := fun h => hnot (h ▸ one_mem _)
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
  have hsimple : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hK7
  have hnonab : ∃ a b : kBar K, a * b ≠ b * a :=
    Back.nonab_of_quasisimple (TwoThin.isQuasisimple_hat hh.twoTerminal.1.2.2)
  have hR := (hh.R_eq hsimple hnonab).1
  have huC : u ∈ centralizer ({x} : Set G) := hh.sylowT.le huT
  have huM : u ∈ M := hh.centralizer_le huC
  have hLn := hh.L_normal.2
  have hρ2 : (Back.actHom hLn ⟨u, huM⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨u, huM⟩ : ↥M) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hu2']
      exact pow_orderOf_eq_one u
    rw [this, map_one]
  have hρout : Back.actHom hLn ⟨u, huM⟩ ∉ (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
    intro h
    apply hnot
    rw [← hR]
    exact ⟨huT, mem_sup_of_actHom_mem_range hh.L_normal.1 hLn huM h⟩
  obtain ⟨h3, hodd⟩ := xu_seven_outer hK7 hρout hρ2
  have hne : IVK.xu (Back.actHom hLn ⟨u, huM⟩) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3
    omega
  have hL34 : ¬ IsL34Quotient (kBar K) :=
    not_isL34Quotient_of_card_lt (by rw [card_eq_of_hasL2Model_seven hK7]; norm_num)
  exact hnoV2 ⟨x, u, K, isV2Triple_of_xu hh hsimple hL34 huC hu2' ⟨hne, hodd⟩⟩

theorem b_lemma113_L27_of
    (h112 : S_lemma112) : B_lemma113_L27 := by
  intro G _ _ hG x K L M T Q hh p91 hK7
  have h168 := card_eq_of_hasL2Model_seven hK7
  have hnoV2 : ¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' := by
    intro hex
    rcases p91.2.2.2 hex with h5 | h7
    · have := card_eq_of_hasL2Model_five h5
      omega
    · obtain ⟨e⟩ := h7
      have h2520 : Nat.card (kBar K) = 2520 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
  have hKL : K = L := by
    rcases hh.b with hB1 | hB2
    · exfalso
      obtain ⟨y, hy⟩ := hB1.v2star
      exact hnoV2 ⟨x, y, K, hy.1.1.1.1⟩
    · exact hh.a.terminal_eq hB2.terminal
  subst hKL
  have hsK : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hK7
  have hnK : ∃ a b : kBar K, a * b ≠ b * a :=
    Back.nonab_of_quasisimple (TwoThin.isQuasisimple_hat hh.a.twoTerminal.1.2.2)
  obtain ⟨-, hcommPQ, -⟩ := hh.a.R_eq hsK hnK
  have hQabel := (forall_of_isElementaryAbelian p91.1.1).1
  have hQR : ∀ q ∈ Q, ∀ r ∈ (T ⊓ K) ⊔ Q, q * r = r * q := fun q hq r hr =>
    Aux113E.comm_of_mem_sup hcommPQ hQabel hq hr
  have hQcentral : ∀ q ∈ Q, ∀ t ∈ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q := by
    intro q hq t ht
    have hcl : Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} ≤ (T ⊓ K) ⊔ Q := by
      rw [Subgroup.closure_le]
      intro u hu
      exact involution_mem_R_seven hh.a hK7 hnoV2 hu.1 hu.2
    exact hQR q hq t (hcl ht)
  rcases h112 G hG x K K M T Q hh p91 rfl hQcentral with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
  · have h360 : Nat.card (kBar K) = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega
  · have h60 : Nat.card (kBar K) = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega

end CFSG.GH74.GLS.C3.Layer1.Bk
