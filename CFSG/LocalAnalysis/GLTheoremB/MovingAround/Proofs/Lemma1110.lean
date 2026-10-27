module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43One
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf innerAut IsFiTwentyTwo Fi22Facts)

section Glue1

variable {G : Type} [Group G]

theorem l1110_isElemAbelian_closure_singleton {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.closure ({x} : Set G)) :=
  IsElemAbelian.closure_of_commute
    (fun a ha b hb => by rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb])
    (fun a ha => by rw [Set.mem_singleton_iff.1 ha]; exact hx)

theorem l1110_isElemAbelian_of_le {p : ℕ} {E H : Subgroup G} (hE : IsElemAbelian p E)
    (hHE : H ≤ E) : IsElemAbelian p H :=
  ⟨⟨⟨fun a b => Subtype.ext (hE.comm (hHE a.2) (hHE b.2))⟩⟩, fun x hx => hE.2 x (hHE hx)⟩

theorem l1110_mem_of_isSCp {p : ℕ} {E R : Subgroup G} (hE : IsSCp p ⊤ E) (hER : E ≤ R) {x : G}
    (hxc : ∀ g ∈ R, g * x = x * g) (hxp : x ^ p = 1) : x ∈ E := by
  have hc : ∀ a ∈ E, ∀ b ∈ Subgroup.closure ({x} : Set G), a * b = b * a := by
    intro a ha b hb
    have hsub : Subgroup.closure ({x} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hxc a (hER ha))
    exact Subgroup.mem_centralizer_iff.1 (hsub hb) a (Set.mem_singleton a)
  have hEx : IsElemAbelian p (E ⊔ Subgroup.closure ({x} : Set G)) :=
    IsElemAbelian.sup_of_commute hE.2.1 (l1110_isElemAbelian_closure_singleton hxp) hc
  have heq : E ⊔ Subgroup.closure ({x} : Set G) = E :=
    hE.2.2 _ le_top hEx le_sup_left
  have hx' : x ∈ E ⊔ Subgroup.closure ({x} : Set G) :=
    (le_sup_right : Subgroup.closure ({x} : Set G) ≤ E ⊔ Subgroup.closure ({x} : Set G))
      (Subgroup.subset_closure (Set.mem_singleton x))
  rwa [heq] at hx'

theorem l1110_omegaOne_centerOf_le {p : ℕ} {E R : Subgroup G} (hE : IsSCp p ⊤ E) (hER : E ≤ R) :
    omegaOne p (centerOf R) ≤ E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxZ, hxp⟩
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hxZ
  refine l1110_mem_of_isSCp hE hER (fun g hg => ?_) hxp
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)

end Glue1

section Glue2

variable {G : Type} [Group G] [Finite G]

theorem l1110_card_eq_pow_pRank {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E = p ^ CFSG.Open.pRank p E := by
  have hpg : IsPGroup p E := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨g, hg⟩
    have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 g hg)
    rw [Subgroup.orderOf_mk]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  unfold CFSG.Open.pRank
  have hgr : IsGreatest {k | ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k} n := by
    refine ⟨⟨E, le_rfl, hE, hn⟩, ?_⟩
    rintro k ⟨F, hFE, -, hFk⟩
    have hle : p ^ k ≤ p ^ n := by
      rw [← hFk, ← hn]
      exact Subgroup.card_le_of_le hFE
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle
  rw [hgr.csSup_eq, hn]

theorem l1110_card_innerAut {K : Type} [Group K] [Finite K] (hc : Subgroup.center K = ⊥) :
    Nat.card (innerAut K) = Nat.card K := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcen : g ∈ Subgroup.center K := by
      refine Subgroup.mem_center_iff.2 (fun x => ?_)
      have h1 : g * x * g⁻¹ = x := by
        have := congrArg (fun φ : MulAut K => φ x) hg
        simpa [MulAut.conj_apply] using this
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    rw [hc] at hcen
    exact (Subgroup.mem_bot.1 hcen)
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem l1110_a0_innerImage [Fact (Nat.Prime 5)] {K A0 : Subgroup G} (hF : Fi22Facts)
    (hK : IsFiTwentyTwo (barOf 5 K)) (hA0 : IsElemAbelian 5 A0) (hrk : CFSG.Open.pRank 5 A0 = 2)
    (hN : A0 ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ A0, x ∈ centBar 5 ⊤ K → x = 1)
    (hinn : ∀ x ∈ A0, InducesInner 5 K x) :
    ∃ S : Subgroup (MulAut (barOf 5 K)), S ≤ innerAut (barOf 5 K) ∧ IsPGroup 5 S ∧
      Nat.card S = 5 ^ (Nat.card (innerAut (barOf 5 K))).factorization 5 := by
  obtain ⟨hcen, hfac, -, -⟩ := hF (barOf 5 K) hK
  have hcardA : Nat.card A0 = 5 ^ 2 := by
    rw [l1110_card_eq_pow_pRank hA0, hrk]
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set D : Subgroup N := A0.subgroupOf N with hDdef
  let ψ : D →* MulAut (barOf 5 K) := (barAut 5 K).comp D.subtype
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨x, hxN⟩, hxA⟩ h1
    have hxA' : x ∈ A0 := hxA
    have hker : (⟨x, hxN⟩ : N) ∈ MonoidHom.ker (barAut 5 K) := by
      rw [MonoidHom.mem_ker]
      exact h1
    have hcent : x ∈ centBar 5 ⊤ K :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨x, hxN⟩, hker, rfl⟩, trivial⟩
    have hx1 : x = 1 := hfaith x hxA' hcent
    subst hx1
    rfl
  have hrange : ∀ y : D, ψ y ∈ innerAut (barOf 5 K) := by
    rintro ⟨⟨x, hxN⟩, hxA⟩
    obtain ⟨k, hkK, hkc⟩ := hinn x hxA
    have hkN : k ∈ N := Subgroup.le_normalizer hkK
    obtain ⟨⟨z, hzN⟩, hzker, hzeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hkc).1
    have hz1 : barAut 5 K ⟨z, hzN⟩ = 1 := (MonoidHom.mem_ker).1 hzker
    have hxeq : (⟨x, hxN⟩ : N) = ⟨k, hkN⟩ * ⟨z, hzN⟩ := by
      apply Subtype.ext
      change x = k * z
      have hz' : z = k⁻¹ * x := hzeq
      rw [hz']
      group
    have hconj : barAut 5 K ⟨k, hkN⟩ = MulAut.conj (QuotientGroup.mk (⟨k, hkK⟩ : K) : barOf 5 K) := by
      ext q
      induction q using QuotientGroup.induction_on with
      | H y =>
        rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply]
        rfl
    show barAut 5 K ⟨x, hxN⟩ ∈ innerAut (barOf 5 K)
    rw [hxeq, map_mul, hz1, mul_one, hconj]
    exact ⟨_, rfl⟩
  have hcardD : Nat.card D = 5 ^ 2 := by
    rw [← hcardA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hS : Nat.card (MonoidHom.range ψ) = 5 ^ 2 := by
    rw [← hcardD]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine ⟨MonoidHom.range ψ, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hrange y
  · exact IsPGroup.of_card (by rw [hS])
  · rw [hS, l1110_card_innerAut hcen, hfac]

end Glue2

section Glue3

variable {G : Type} [Group G] [Finite G]

theorem l1110_normalizer_le_glbCore {p : ℕ} {P Q : Subgroup G} (hQ : Q ≤ P)
    (hk : 2 ≤ CFSG.Open.pRank p Q) : Subgroup.normalizer (Q : Set G) ≤ GLBCore p 2 P :=
  le_sSup ⟨Q, hQ, hk, rfl⟩

theorem l1110_normalizer_A0_le {p : ℕ} {M E A : Subgroup G} (hE : inD p M E)
    (hA0 : CFSG.Open.pRank p (E ⊓ A) = 2) :
    Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
  (l1110_normalizer_le_glbCore inf_le_left (by rw [hA0])).trans hE.2.clause_d

end Glue3

@[expose] def Input14_21 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsFiTwentyTwo K → ∀ x : K, orderOf x = 5 →
    IsAltType 5 ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set K)))

@[expose] def Lemma1110CaseB : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m p B M E A a K), Type117b p K →
    (∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → omegaOne 5 (centerOf R) ≤ E ⊓ A) →
    (∃ S : Subgroup (MulAut (barOf 5 K)), S ≤ innerAut (barOf 5 K) ∧ IsPGroup 5 S ∧
      Nat.card S = 5 ^ (Nat.card (innerAut (barOf 5 K))).factorization 5) →
    Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M →
    Input14_21 → False

theorem lemma1110_of_inputs (h118 : Lemma118Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (hF : Fi22Facts) (hI : Input14_21)
    (hcore : Lemma1110CaseB) : Lemma1110Statement := by
  intro G _ _ m p B M E A a K h
  rcases h118 h with hb | hc
  · obtain ⟨rfl, hfi⟩ := hb
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hsc := h104ii h.toCex117Base.toSec11.toSec10Fails h.pair
    have hEsc : IsSCp 5 ⊤ E := hsc.1
    have hAsc : IsSCp 5 ⊤ A := hsc.2
    obtain ⟨hrk, hN, hfaith, hinn⟩ := h119 h
    have hfr : ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R →
        omegaOne 5 (centerOf R) ≤ E ⊓ A := fun R _ hR =>
      le_inf (l1110_omegaOne_centerOf_le hEsc (le_trans le_sup_left hR))
        (l1110_omegaOne_centerOf_le hAsc (le_trans le_sup_right hR))
    have hEA : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hEsc.2.1 inf_le_left
    obtain ⟨S, hS, hSp, hScard⟩ := l1110_a0_innerImage hF hfi hEA hrk hN hfaith hinn
    have hN0 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
      l1110_normalizer_A0_le h.pair.1.1 hrk
    exact (hcore h ⟨rfl, hfi⟩ hfr ⟨S, hS, hSp, hScard⟩ hN0 hI).elim
  · exact hc

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
