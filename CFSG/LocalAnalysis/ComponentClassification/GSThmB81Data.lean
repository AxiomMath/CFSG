module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Setup
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512c

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

structure Data (H₁ : h.L81Hyp) where
  b : H
  p : H
  r : H
  z : H
  g : H
  B_eq : h.B = zpowers b
  b_ord : orderOf b = 2
  T_card : Nat.card h.T = 4
  T_eq : h.T = zpowers h.a ⊔ zpowers b
  T_eq' : h.T = h.P ⊓ centralizer ({b} : Set H)
  p_mem : p ∈ h.P
  r_mem : r ∈ h.P
  P_cl : closure {p, r} = h.P
  card_P : 2 * orderOf p = Nat.card h.P
  r_sq : r ^ 2 = 1
  rel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1)
  S_p : ∀ s ∈ h.S, s * p * s⁻¹ ∈ zpowers p
  C_p : h.P ⊓ centralizer ({p} : Set H) = zpowers p
  p_a : p ^ (orderOf p / 2) = h.a
  z_ord : orderOf z = 2
  z_D : z ∈ h.D
  z_S : z ∈ centralizer (h.S : Set H)
  SS_inv : ∀ u ∈ ⁅h.S, h.S⁆, orderOf u = 2 → u ∈ closure {z, h.a}
  SS_comm : ∀ u ∈ ⁅h.S, h.S⁆, ∀ v ∈ ⁅h.S, h.S⁆, u * v = v * u
  g_M : g ∈ h.M3
  g_K : g ∈ h.K
  g_N : g ∈ normalizer ((h.Q ⊓ h.M3 : Subgroup H) : Set H)
  g_Q : g ∉ h.Q
  g_sq : g * g ∈ h.Q
  tau_K : h.a * (g⁻¹ * h.a * g) ∈ h.K

theorem exists_data (H₁ : h.L81Hyp) (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hAC : CFAutSmallCommutator)
    (hAQ : CFAutSmallQuotient) (hST : SuzukiTausskyInput) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (hJo : CFSec8JOrder) (hF2 : CFSp4F2) :
    Nonempty (Data H₁) := by
  obtain ⟨b, hBb, hb, hT4, hTab, hTC⟩ := H₁.exists_b
  obtain ⟨p, r, hp, hr, hcl, hc, hr2, hrel, hSp, hCp, hpa⟩ :=
    h.presentation_of_index_two embedsTQuotStatement hST H₁.card_quot_T H₁.eight_le
  obtain ⟨-, hSS, -, z, hz2, hzD, hzS, hzinv⟩ :=
    h.commutator_structure hB1 hB6 embedsTQuotStatement hCF23 hCF24 hAC hAQ hST
      H₁.card_quot_T
  obtain ⟨g, hgK, hgN, hgQ, hgsq, htau⟩ := H₁.kloc.exists_g_gen hCF1 hCF2 hJo hF2
  exact ⟨{
    b := b
    p := p
    r := r
    z := z
    g := (g : H)
    B_eq := hBb
    b_ord := hb
    T_card := hT4
    T_eq := hTab
    T_eq' := hTC
    p_mem := hp
    r_mem := hr
    P_cl := hcl
    card_P := hc
    r_sq := hr2
    rel := hrel
    S_p := hSp
    C_p := hCp
    p_a := hpa
    z_ord := hz2
    z_D := hzD
    z_S := hzS
    SS_inv := hzinv
    SS_comm := hSS
    g_M := g.2
    g_K := hgK
    g_N := mem_normalizer_inf_of_subgroupOf hgN
    g_Q := fun h1 => hgQ h1
    g_sq := hgsq
    tau_K := by simpa using htau }⟩

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
