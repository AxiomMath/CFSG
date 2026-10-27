module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.TransferComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction.TMem

@[expose] def Fi22AutFixInner : Prop :=
  ∀ (Y : Type) [Group Y], IsSporadic Y .Fi22 → ∀ uY : Y, orderOf uY = 2 →
    18393661440 ≤ Nat.card ↥(centralizer ({uY} : Set Y)) →
      ∀ β ∈ autFixing (centralizer ({uY} : Set Y)), ∃ y : Y, β = MulAut.conj y

theorem isCyclic_of_card_le_two {X : Type*} [Group X] [Finite X] (h : Nat.card X ≤ 2) :
    IsCyclic X := by
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases (by omega : Nat.card X = 1 ∨ Nat.card X = 2) with h1 | h2
  · have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

theorem two_le_twoAdic_of_perfect {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (hperf : Group.IsPerfect ↥M) (hne : M ≠ ⊥) : 2 ≤ twoAdic M := by
  by_contra h
  push Not at h
  have hcyc : ∀ P : Sylow 2 ↥M, IsCyclic ↥P := by
    intro P
    have hcard : Nat.card ↥(P : Subgroup ↥M) = 2 ^ twoAdic M := P.card_eq_multiplicity
    have hle : Nat.card ↥(P : Subgroup ↥M) ≤ 2 := by
      rw [hcard]
      have : twoAdic M ≤ 1 := by omega
      calc 2 ^ twoAdic M ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 := by norm_num
    exact isCyclic_of_card_le_two hle
  have hsolv : Group.IsSolvable ↥M := isSolvable_of_cyclic_sylow_two hcyc
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).2 hne
  exact Group.IsPerfect.not_isSolvable ↥M hsolv


theorem tMemOfNotMax_fi22_proved (hAut : Fi22AutFixInner) :
    TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440) := by
  intro s hs H _ _ N L K t u hcov hhyp hQ hnm
  rcases List.mem_singleton.1 hs with rfl
  by_contra htN
  have : N.Normal := hhyp.fstar.normal
  have hQ' := hQ
  obtain ⟨huL, hbar, hmodel⟩ := fiLoc22_data hcov hQ
  obtain ⟨-, hu2, hKL, hKu, hKq, hsz⟩ := hQ
  have hodd : Odd (Nat.card (center ↥L)) := hcov.odd_center
  have hLperf : Group.IsPerfect ↥L := hcov.1.1
  have hKperf : Group.IsPerfect ↥K := hKq.1
  have hKperf' : Group.IsPerfect ↥(K.subgroupOf L) := isPerfect_subgroupOf hKL
  set ū : ↥L ⧸ center ↥L := ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) with hū
  have hnc : (⟨u, huL⟩ : ↥L) ∉ center ↥L := fun hz =>
    hcov.not_mem_centralizer_of_orderOf_two huL hu2 (mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩))
  have hu1 := sq_of_orderOf_two huL hu2
  have hū2 : orderOf ū = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hū, pow_two, ← QuotientGroup.mk_mul, hu1]
      rfl
    · intro h1
      exact hnc ((QuotientGroup.eq_one_iff _).1 h1)
  have hcardU : 18393661440 ≤ Nat.card ↥(centralizer ({ū} : Set (↥L ⧸ center ↥L))) := by
    have h1 : 18393661440 ≤ Nat.card (bar (K.subgroupOf L)) :=
      hsz.trans (card_quotient_oddCore_le_bar hodd hKL)
    rw [hbar] at h1
    exact h1
  have hinnFix : ∀ β ∈ autFixing ((K.subgroupOf L).map (q ↥L)), ∃ y : ↥L ⧸ center ↥L,
      β = MulAut.conj y := by
    intro β hβ
    have hβ' : β ∈ autFixing (centralizer ({ū} : Set (↥L ⧸ center ↥L))) := by
      have h1 : (K.subgroupOf L).map (q ↥L) = centralizer ({ū} : Set (↥L ⧸ center ↥L)) := hbar
      rwa [h1] at hβ
    exact hAut _ hcov.2.2 ū hū2 hcardU β hβ'
  have hMK : ∀ b ∈ normalizer (L : Set H), (∀ k ∈ K, b * k = k * b) →
      b ∈ L ⊔ centralizer (L : Set H) := by
    intro b hb hbK
    have hαK : L.normalizerMonoidHom ⟨b, hb⟩ ∈ autCentralizer L K := by
      intro k hk
      apply Subtype.ext
      show b * (k : H) * b⁻¹ = k
      calc b * (k : H) * b⁻¹ = ((k : H) * b) * b⁻¹ := by rw [hbK k hk]
        _ = k := by group
    obtain ⟨g, hg⟩ := autCentralizer_inner_of_quotient hLperf hinnFix _ hαK
    exact mem_sup_centralizer_iff.2 ⟨g, g.2, (normalizerMonoidHom_eq_conj_iff hb g).1 hg⟩
  have hS2 := card_sylow_eq_two_of_not_mem hhyp.index_le_two hhyp.cyclicSylow hhyp.t_mem
    hhyp.t_order htN
  obtain ⟨K₀, hK₀C, -, -, hmul, hinv⟩ := Closing.exists_K₀ hS2 hhyp.t_mem hhyp.t_order
  have hMperf : ∀ P : Subgroup H, P ≤ normalizer (L : Set H) → Group.IsPerfect ↥P →
      P ≤ L ⊔ centralizer (L : Set H) := by
    intro P hPM hPperf
    have hc : ⁅P, P⁆ ≤ L ⊔ K₀ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact Closing.comm_mem_sup (Group.isPerfect_def.1 hLperf) hmodel.outTwo hK₀C hmul hinv
        (hPM ha) (hPM hb)
    have heq : ⁅P, P⁆ = P := Subgroup.commutator_eq_self
    rw [heq] at hc
    exact hc.trans (sup_le_sup_left hK₀C L)
  have hC2 : Nat.card ↥(centralizer ((centralizer ({ū} : Set (↥L ⧸ center ↥L)) :
      Subgroup (↥L ⧸ center ↥L)) : Set (↥L ⧸ center ↥L))) ≤ 2 := hmodel.card_centralizer
  have hcycU : IsCyclic ↥(centralizer ((centralizer ({ū} : Set (↥L ⧸ center ↥L)) :
      Subgroup (↥L ⧸ center ↥L)) : Set (↥L ⧸ center ↥L))) := isCyclic_of_card_le_two hC2
  have hūU : ū ∈ centralizer ((centralizer ({ū} : Set (↥L ⧸ center ↥L)) :
      Subgroup (↥L ⧸ center ↥L)) : Set (↥L ⧸ center ↥L)) :=
    mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 hy
  have hconj : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) →
      ∃ x ∈ L, x * u * x⁻¹ = w := by
    intro w hwL hw2 hwK
    refine ⟨1, L.one_mem, ?_⟩
    have hww : (⟨w, hwL⟩ : ↥L) * ⟨w, hwL⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hw2)
    have hwU : ((⟨w, hwL⟩ : ↥L) : ↥L ⧸ center ↥L) ∈ centralizer ((centralizer
        ({ū} : Set (↥L ⧸ center ↥L)) : Subgroup (↥L ⧸ center ↥L)) : Set (↥L ⧸ center ↥L)) := by
      rw [← hbar]
      refine mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hwK k (mem_subgroupOf.1 hk))
    by_cases h1 : ((⟨w, hwL⟩ : ↥L) : ↥L ⧸ center ↥L) = 1
    · exact absurd (mem_centralizer_iff.2 fun l hl =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff _).1 h1)
          ⟨l, hl⟩)) (hcov.not_mem_centralizer_of_orderOf_two hwL hw2)
    · have hwbar2 : orderOf ((⟨w, hwL⟩ : ↥L) : ↥L ⧸ center ↥L) = 2 := by
        refine orderOf_eq_prime ?_ h1
        rw [pow_two, ← QuotientGroup.mk_mul, hww]
        rfl
      have heq := Closing.eq_of_orderOf_eq_two_of_cyclic hcycU hwU hūU hwbar2 hū2
      have h3 := Closing.eq_of_mk_eq_of_sq hodd hww hu1 heq
      have h4 : w = u := congrArg Subtype.val h3
      rw [h4]
      group
  have huniq : ∀ K'' : Subgroup H, K'' ≤ L → (∀ k ∈ K'', k * u = u * k) →
      Group.IsPerfect ↥K'' → Nat.card ↥K'' = Nat.card ↥K → K'' = K := by
    intro K'' hK''L hK''u hperf hcard
    have hmax : ∀ P : Subgroup (↥L ⧸ center ↥L),
        P ≤ centralizer ({q ↥L ⟨u, huL⟩} : Set (↥L ⧸ center ↥L)) → Group.IsPerfect ↥P →
          P ≤ (K.subgroupOf L).map (q ↥L) := by
      intro P hP _
      have h1 : (K.subgroupOf L).map (q ↥L) = centralizer ({ū} : Set (↥L ⧸ center ↥L)) := hbar
      rw [h1]
      exact hP
    have hle := perfect_le_of_quotient huL hmax K'' (fun x hx =>
      ⟨hK''L hx, mem_centralizer_singleton_iff.2 (hK''u x hx)⟩) hperf
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hsmall : ∀ S : Subgroup H, S ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥S →
      Nat.card ↥S < 2 ^ twoAdic K := by
    intro S hS hS2
    have hSL : S ≤ L := hS.trans inf_le_left
    have hSp : IsPGroup 2 ↥(S.subgroupOf L) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
    have hmemU : ∀ s : ↥(S.subgroupOf L), (s : ↥L ⧸ center ↥L) ∈ centralizer ((centralizer
        ({ū} : Set (↥L ⧸ center ↥L)) : Subgroup (↥L ⧸ center ↥L)) :
          Set (↥L ⧸ center ↥L)) := by
      intro s
      rw [← hbar]
      refine mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.1 (hS (mem_subgroupOf.1 s.2)).2 (k : H)
        (mem_subgroupOf.1 hk))
    let φ : ↥(S.subgroupOf L) → ↥(centralizer ((centralizer ({ū} : Set (↥L ⧸ center ↥L)) :
        Subgroup (↥L ⧸ center ↥L)) : Set (↥L ⧸ center ↥L))) := fun s =>
      ⟨((s : ↥L) : ↥L ⧸ center ↥L), hmemU s⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      have h1 : ((a : ↥L) : ↥L ⧸ center ↥L) = ((b : ↥L) : ↥L ⧸ center ↥L) :=
        congrArg Subtype.val hab
      exact Subtype.ext (eq_of_mk_eq_of_mem_isPGroup hodd hSp a.2 b.2 h1)
    have hSle : Nat.card ↥S ≤ 2 := by
      have h1 : Nat.card ↥S = Nat.card ↥(S.subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv).symm
      rw [h1]
      exact (Nat.card_le_card_of_injective φ hφ).trans hC2
    have h2 : 2 ≤ twoAdic K := by
      have e1 : twoAdic K = twoAdic (bar (K.subgroupOf L)) := by
        rw [twoAdic_bar hodd]
        unfold twoAdic
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
      rw [e1]
      have : Group.IsPerfect ↥(K.subgroupOf L) := hKperf'
      have hperfb : Group.IsPerfect ↥(bar (K.subgroupOf L)) := Group.IsPerfect.map _
      refine two_le_twoAdic_of_perfect hperfb ?_
      intro hbot
      have h1 : 18393661440 ≤ Nat.card (bar (K.subgroupOf L)) :=
        hsz.trans (card_quotient_oddCore_le_bar hodd hKL)
      rw [hbot, Subgroup.card_bot] at h1
      omega
    calc Nat.card ↥S ≤ 2 := hSle
      _ < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ twoAdic K := Nat.pow_le_pow_right (by norm_num) h2
  have hKq' : CFSG.Open.IsQuasisimple ↥K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).1 hKq
  have D : TMemData H N L K u :=
    { LN := le_of_perfect_of_index_le_two hhyp.index_le_two
      odd := oddCN_of_not_mem hhyp.index_le_two hhyp.cyclicSylow hhyp.t_mem hhyp.t_order htN
      u_mem := huL
      u_order := hu2
      h38 := hhyp.hyp38_2
      MK := hMK
      Mperf := hMperf
      KL := hKL
      Kperf := hKperf
      Ku := hKu
      conj := hconj
      uniq := huniq }
  exact hnm (D.maximal hKq' hsmall)

end CFSG.EvenSporadicStandard.Induction
