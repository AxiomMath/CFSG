module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cj_eq_conjugate (H : Subgroup G) (g : G) : M.cj H g = conjugate H g := by
  ext x
  rw [M.mem_cj]
  show _ ↔ x ∈ cmap g⁻¹ H
  rw [mem_cmap, inv_inv]

theorem secCent_eq (K N : Subgroup G) : M.secCent K N = centralizerSection K N := rfl

theorem syl2In_of_isSylowOf [Finite G] {P H : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 P H) : M.Syl2In P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.isSylowOf_iff.1 h

theorem le_pPrimeCoreOf' {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (h : G) h.2 (a : G) ha⟩
  have hcop' : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

theorem isOddCore_pPrimeCoreOf [Finite G] (X : Subgroup G) :
    M.IsOddCore X (pPrimeCoreOf 2 X) where
  le := TwoThin.pPrimeCoreOf_le X
  normal := fun _ hx _ hn => TwoThin.pPrimeCoreOf_normalized X hx hn
  odd := TwoThin.card_pPrimeCoreOf_odd X
  max := fun _ hNX hnorm hodd => le_pPrimeCoreOf' hNX hnorm hodd

theorem rk1_of_pRank_one [Finite G] {K : Subgroup G} (hr : pRank 2 ↥K = 1) : M.Rk1 K := by
  intro a ha b hb ha2 hb2 hab
  by_contra hne
  push Not at hne
  exact hne.2.2 (eq_of_pRank_one hr ha hb (orderOf_eq_two_of_mul_self_eq_one ha2 hne.1)
    (orderOf_eq_two_of_mul_self_eq_one hb2 hne.2.1) hab)

theorem nonab_of_isPCompIn [Finite G] {X K : Subgroup G} (hK : IsPCompIn 2 X K) :
    ∃ a ∈ K, ∃ b ∈ K, ⁅a, b⁆ ∉ pPrimeCoreOf 2 K := by
  obtain ⟨-, -, a', b', hab'⟩ := TwoThin.isQuasisimple_hat hK
  obtain ⟨a₁, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b₁, rfl⟩ := QuotientGroup.mk_surjective b'
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a₁
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b₁
  refine ⟨a, a.2, b, b.2, fun hmem => ?_⟩
  apply hab'
  have h1 : ⁅a, b⁆ ∈ pPrimeCore 2 ↥K := by
    obtain ⟨c, hc, hcc⟩ := hmem
    have : c = ⁅a, b⁆ := Subtype.ext (by simpa [commutatorElement_def] using hcc)
    rwa [← this]
  have h2 : ⁅(a : ↥K ⧸ pPrimeCore 2 ↥K), (b : ↥K ⧸ pPrimeCore 2 ↥K)⁆ = 1 := by
    have h3 := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥K) ⁅a, b⁆).2 h1
    rwa [show ((⁅a, b⁆ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) =
      ⁅(a : ↥K ⧸ pPrimeCore 2 ↥K), (b : ↥K ⧸ pPrimeCore 2 ↥K)⁆ from
        map_commutatorElement (QuotientGroup.mk' (pPrimeCore 2 ↥K)) a b] at h3
  have h4 := commutatorElement_eq_one_iff_mul_comm.1 h2
  rw [← QuotientGroup.mk_mul, h4, QuotientGroup.mk_mul]

theorem sTop_of_clause_d [Finite G] {z : G} {S : Subgroup G}
    (hSyl : M.Syl2In S (centralizer ({z} : Set G)))
    (hd : ∃ S' : Sylow 2 G, ∀ g : G, (g ∈ (S' : Subgroup G) ∧
      (∀ s ∈ (S' : Subgroup G), s * g = g * s) ∧ g ^ 2 = 1) ↔ g ∈ zpowers z) :
    M.Syl2In S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hd
  have hzS' := (hS' z).2 (mem_zpowers z)
  have hle : (S' : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzS'.2.1 s hs)
  have hS'top : M.Syl2In (S' : Subgroup G) ⊤ :=
    ⟨le_top, S'.isPGroup', by simpa [Subgroup.relIndex_top_right] using Sylow.not_dvd_index S'⟩
  have hS'C : M.Syl2In (S' : Subgroup G) (centralizer ({z} : Set G)) := by
    refine ⟨hle, S'.isPGroup', fun hdvd => ?_⟩
    have h1 : (S' : Subgroup G).relIndex (centralizer ({z} : Set G)) ∣ (S' : Subgroup G).index := by
      rw [← Subgroup.relIndex_mul_index hle]
      exact dvd_mul_right _ _
    exact Sylow.not_dvd_index S' (hdvd.trans h1)
  obtain ⟨c, -, hc⟩ := hS'C.exists_conj hSyl
  have h2 := M.syl2In_cj hS'top c
  rw [← hc] at h2
  have hcj : M.cj (⊤ : Subgroup G) c = ⊤ := by
    ext x
    simp [M.mem_cj]
  rwa [hcj] at h2

theorem rigidProduct_eq {z : G} {K₁ K₂ : Subgroup G}
    (hc : {K : Subgroup G | IsRigidRankOneComp z K} = {K₁, K₂}) : rigidProduct z = K₁ ⊔ K₂ := by
  unfold rigidProduct
  rw [hc, sSup_pair]

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
