module

public import CFSG.GH74.GLS.C3.Layer1.St1Prop51
public import CFSG.GH74.GLS.C3.Layer1.Back113A
public import CFSG.GH74.GLS.C3.Layer1.St1P89Tools
public import CFSG.GH74.GLS.C3.Layer1.P34RealAut
public import CFSG.GH74.GLS.C3.Layer1.P34RealCtx
public import CFSG.GH74.GLS.C3.Layer1.Thm1Normal

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
  CFSG.GH74.GLS.C3.Layer1.P34Real
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_alt6 : 2 ≤ pRank 2 (alternatingGroup (Fin 6)) := by
  have hXm : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  have hYm : (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  set a : alternatingGroup (Fin 6) := ⟨_, hXm⟩ with ha
  set b : alternatingGroup (Fin 6) := ⟨_, hYm⟩ with hb
  have ha2 : a ^ 2 = 1 := Subtype.ext (by
    change (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ^ 2 = 1
    decide)
  have hb2 : b ^ 2 = 1 := Subtype.ext (by
    change (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3) ^ 2 = 1
    decide)
  have hab : a * b = b * a := Subtype.ext (by
    change Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 * (Equiv.swap 0 2 * Equiv.swap 1 3) =
      Equiv.swap 0 2 * Equiv.swap 1 3 * (Equiv.swap 0 1 * Equiv.swap 2 3)
    decide)
  have ha1 : a ≠ 1 := fun h => by
    have h1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) = 1 :=
      congrArg Subtype.val h
    revert h1
    decide
  have hb1 : b ≠ 1 := fun h => by
    have h1 : (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 6)) = 1 :=
      congrArg Subtype.val h
    revert h1
    decide
  have hne : a ≠ b := fun h => by
    have h1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) =
        Equiv.swap 0 2 * Equiv.swap 1 3 := congrArg Subtype.val h
    revert h1
    decide
  have hEl := isElemAbelian_pair ha2 hb2 hab
  have hcard := card_klein ha2 hb2 hab ha1 hb1 hne
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank (k := 2) (by norm_num) le_top hEl (by rw [hcard]; norm_num)

theorem pRank_CxK_eq_one {u : G} {K W : Subgroup G} (hW : IsSylowOf 2 W (NxK u K))
    (hQ : pRank 2 ↥(W ⊓ CxK u K) = 1) : pRank 2 ↥(CxK u K) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCxN : ∀ g ∈ NxK u K, ∀ n ∈ CxK u K, g * n * g⁻¹ ∈ CxK u K := by
    intro g hg n hn
    have hKN : ∀ c ∈ NxK u K, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
      (mem_normalizer_iff.1 hc.2 k).1 hk
    have := CMK_conj (C := NxK u K) hKN hg (n := n) ⟨⟨hn.1, hn.2.1⟩, hn.2⟩
    exact ⟨this.1.1, this.2⟩
  have hCxle : CxK u K ≤ NxK u K := fun g hg => ⟨hg.1, hg.2.1⟩
  have hNN : NxK u K ≤ normalizer (CxK u K : Set G) := by
    intro g hg
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hCxN g hg h hh, fun hh => ?_⟩
    have := hCxN g⁻¹ ((NxK u K).inv_mem hg) _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  rw [← pRank_eq_of_isSylowOf (hW.inf_of_le_normalizer hCxle hNN)]
  exact hQ

theorem K_normal_of_rank_one {u : G} {K W : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({u} : Set G)) K)
    (hL2 : HasL2Model (kBar K) (fun q => q = 9))
    (hW : IsSylowOf 2 W (NxK u K)) (hQ : pRank 2 ↥(W ⊓ CxK u K) = 1) :
    ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hKC : K ≤ C := hK.1
  have hK2 : 2 ≤ pRank 2 ↥K := by
    obtain ⟨e⟩ := Back.nonempty_alt6_of_hasL2Model9 hL2
    have h6 : 2 ≤ pRank 2 (alternatingGroup (Fin 6)) := two_le_pRank_alt6
    have hbar : pRank 2 (kBar K) = pRank 2 ↥K :=
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
        (pPrimeCore 2 ↥K) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card)
    rw [← hbar, Bg.pRank_mulEquiv one_lt_two e]
    exact h6
  have hCx : pRank 2 ↥(CxK u K) = 1 := pRank_CxK_eq_one hW hQ
  intro c hc k hk
  by_contra hkc
  set K' : Subgroup G := K.map (MulAut.conj c).toMonoidHom with hK'
  have hK'comp : IsPCompIn 2 C K' := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [map_conj_eq_self_of_mem hc] at this
  have hne : K ≠ K' := by
    intro h
    apply hkc
    rw [h]
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩
  have hK'C : K' ≤ C := hK'comp.1
  have hcomm : ∀ a ∈ K, ∀ b ∈ K', ⁅a, b⁆ ∈ pPrimeCoreOf 2 K := by
    intro a ha b hb
    have hne' : K.subgroupOf C ≠ K'.subgroupOf C := by
      intro h
      apply hne
      have := congrArg (fun X : Subgroup ↥C => X.map C.subtype) h
      simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKC, inf_eq_left.2 hK'C] using this
    obtain ⟨-, h2⟩ := CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      2 Nat.prime_two (K.subgroupOf C) (K'.subgroupOf C) hK.2 hK'comp.2
    obtain ⟨-, -, hcore, -⟩ := h2 hne'
    have haC : (⟨a, hKC ha⟩ : ↥C) ∈ K.subgroupOf C := ha
    have hbC : (⟨b, hK'C hb⟩ : ↥C) ∈ K'.subgroupOf C := hb
    have h3 := hcore (Subgroup.commutator_mem_commutator haC hbC)
    have h4 : ((⁅(⟨a, hKC ha⟩ : ↥C), (⟨b, hK'C hb⟩ : ↥C)⁆ : ↥C) : G) ∈
        ((pPrimeCore 2 (K.subgroupOf C)).map (K.subgroupOf C).subtype).map C.subtype :=
      ⟨_, h3.1, rfl⟩
    rw [CFSG.pPrimeCore_map_subgroupOf 2 K C hKC] at h4
    exact h4
  have hK'N : ∀ b ∈ K', b ∈ normalizer (K : Set G) := by
    have hfwd : ∀ b ∈ K', ∀ a ∈ K, b * a * b⁻¹ ∈ K := by
      intro b hb a ha
      have h1 : ⁅b, a⁆ ∈ pPrimeCoreOf 2 K := by
        have := (pPrimeCoreOf 2 K).inv_mem (hcomm a ha b hb)
        rwa [commutatorElement_inv] at this
      have h2 : b * a * b⁻¹ = ⁅b, a⁆ * a := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact K.mul_mem (TwoThin.pPrimeCoreOf_le K h1) ha
    intro b hb
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hfwd b hb h hh, fun hh => ?_⟩
    have := hfwd b⁻¹ (K'.inv_mem hb) _ hh
    rwa [show b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h by group] at this
  have hK'Cx : K' ≤ CxK u K := by
    intro b hb
    refine ⟨hK'C hb, hK'N b hb, TwoThin.mem_normalizer_pPrimeCoreOf (hK'N b hb), fun a ha => ?_⟩
    exact hcomm a ha b hb
  have hrk : pRank 2 ↥K' = pRank 2 ↥K :=
    (Bg.pRank_mulEquiv one_lt_two
      (Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)).symm
  have h1 : pRank 2 ↥K' ≤ pRank 2 ↥(CxK u K) := Bg.pRank_subgroup_mono one_lt_two hK'Cx
  omega

end CFSG.GH74.GLS.C3.Layer1.P89
