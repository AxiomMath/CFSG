module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Struct
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseF4

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem IsIntrinsicIn.cover_oTwoPrimeOf {H L : Subgroup X} {u : X} (h : IsIntrinsicIn X H L u) :
    oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) ≤ L ∧
      (oTwoPrimeOf (L ⊓ centralizer ({u} : Set X))).subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ ∧
        IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ centralizer ({u} : Set X))) := by
  have hEL : oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) ≤ L :=
    (oTwoPrimeOf_le _).trans inf_le_left
  have hLeq := h.2.2.2.1
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq
  have hcov : (oTwoPrimeOf (L ⊓ centralizer ({u} : Set X))).subgroupOf L ⊔
      pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff hEL, sup_comm]
    exact hLeq.symm
  exact ⟨hEL, hcov, isTwoGenQuasi_of_covers hEL hcov (primeResidual_oTwoPrimeOf _)
    h.isTwoGenQuasi⟩

omit [Finite X] in
theorem exists_sec5Comp_of_K0_ne_bot {H : Subgroup X} (h : K0 X n H ≠ ⊥) :
    ∃ M : Subgroup X, Sec5Comp X n H M := by
  by_contra hcon
  push Not at hcon
  apply h
  have : {L : Subgroup X | (∃ u, IsIntrinsicIn X H L u) ∧
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n} = ∅ :=
    Set.eq_empty_of_forall_notMem fun L hL => hcon L hL
  exact (congrArg sSup this).trans sSup_empty

theorem exists_K0_normalizer_inf_ne_bot {s r : X} {Zs : Subgroup X}
    {S₁ : Sylow 2 ↥(normalizer (Zs : Set X))} (hS₁ : Sec5Data X n s Zs S₁)
    (hr2 : orderOf r = 2) (hrs : r * s = s * r) (hrN : r ∈ normalizer (Zs : Set X))
    (hne : K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥) :
    K0 X n (K0 X n (normalizer (Zs : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : orderOf s = 2 := hS₁.pair.orderOf_z
  have hn : 8 ≤ n := hS₁.maxdeg.1
  set Cs : Subgroup X := centralizer ({s} : Set X) with hCs
  set Cr : Subgroup X := centralizer ({r} : Set X) with hCr
  have hrCs : r ∈ Cs := Subgroup.mem_centralizer_singleton_iff.2 hrs
  obtain ⟨B', hB'⟩ := exists_sec5Comp_of_K0_ne_bot hne
  obtain ⟨⟨u, hu⟩, hBn⟩ := hB'
  have hB'H : B' ≤ K0 X n Cs ⊓ Cr := hu.2.2.1.1
  obtain ⟨M₂, hM₂, hM₂n, hEM₂⟩ := exists_isIntrinsicIn_centralizer hS₁.hypA hS₁.maxdeg hs2
    (inf_le_left.trans (K0_le n Cs)) hu hBn
  set EB : Subgroup X := oTwoPrimeOf (B' ⊓ centralizer ({u} : Set X)) with hEB
  obtain ⟨hEBB, hcovB, hEBq⟩ := hu.cover_oTwoPrimeOf
  have hEBCr : EB ≤ Cr := (hEBB.trans hB'H).trans inf_le_right
  have hrEB : ∀ e ∈ EB, r * e * r⁻¹ = e := fun e he => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hEBCr he)
    rw [← this]; group
  have hM₂c : Sec5Comp X n Cs M₂ := ⟨⟨u, hM₂⟩, hM₂n⟩
  have hrM₂ : r ∈ normalizer (M₂ : Set X) := by
    have hM₂' : Sec5Comp X n Cs (M₂.map (MulAut.conj r).toMonoidHom) :=
      hM₂c.map_conj (Subgroup.le_normalizer hrCs)
    have hEBM₂' : EB ≤ M₂.map (MulAut.conj r).toMonoidHom := fun e he =>
      ⟨e, hEM₂ he, by simp [MulAut.conj_apply, hrEB e he]⟩
    exact mem_normalizer_of_map_conj_eq
      (eq_of_isPCompIn_of_le hM₂'.isPCompIn hM₂c.isPCompIn hEBM₂' hEM₂ hEBq)
  have hcovM : EB.subgroupOf M₂ ⊔ pPrimeCore 2 ↥M₂ = ⊤ := by
    have hEBc : IsDoubleCoverOfAlt (↥EB ⧸ pPrimeCore 2 ↥EB) n :=
      (isDoubleCoverOfAlt_quot_iff_of_covers hEBB hcovB n).2 hBn
    refine covers_of_card_le hEM₂ ?_
    rw [natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hM₂n,
      natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hEBc]
  have hr2' : r ^ 2 = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr2] at this
  have hrOM : r ∈ normalizer (pPrimeCoreOf 2 M₂ : Set X) :=
    normalizer_le_normalizer_pPrimeCoreOf M₂ hrM₂
  have hEBle : EB ≤ M₂ := hEM₂
  have hrcent : ∀ m ∈ M₂, ⁅m, r⁆ ∈ oddCoreOf M₂ := by
    intro m hm
    have hcov' : EB ⊔ pPrimeCoreOf 2 M₂ = M₂ := (covers_subgroupOf_iff hEBle).1 hcovM
    have hm' : m ∈ pPrimeCoreOf 2 M₂ ⊔ EB := by rw [sup_comm, hcov']; exact hm
    obtain ⟨o, ho, e, he, rfl⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
      (pPrimeCoreOf 2 M₂) EB (fun x hx => le_normalizer_oddCoreOf M₂ (hEBle hx)) m).1 hm'
    have hre : r * e = e * r := by
      have := hrEB e he
      calc r * e = (r * e * r⁻¹) * r := by group
        _ = e * r := by rw [this]
    have h1 : ⁅o * e, r⁆ = o * (r * o⁻¹ * r⁻¹) := by
      simp only [commutatorElement_def]
      calc o * e * r * (o * e)⁻¹ * r⁻¹ = o * (e * r * e⁻¹) * o⁻¹ * r⁻¹ := by group
        _ = o * (r * e * e⁻¹) * o⁻¹ * r⁻¹ := by rw [← hre]
        _ = o * (r * o⁻¹ * r⁻¹) := by group
    rw [h1]
    exact (pPrimeCoreOf 2 M₂).mul_mem ho
      ((Subgroup.mem_normalizer_iff.1 hrOM o⁻¹).1 ((pPrimeCoreOf 2 M₂).inv_mem ho))
  obtain ⟨u₂, hu₂Z, hu₂⟩ := hS₁.pair.exists_witness_mem hM₂ hM₂n
  obtain ⟨hE₂I, hE₂n, -⟩ := hS₁.pair.isIntrinsicIn_normalizer hu₂Z hu₂ hM₂n
  set E₂ : Subgroup X := oTwoPrimeOf (M₂ ⊓ centralizer (Zs : Set X)) with hE₂
  have hE₂M₂ : E₂ ≤ M₂ := (oTwoPrimeOf_le _).trans inf_le_left
  have hrCZ : r ∈ normalizer ((centralizer (Zs : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y : X, y ∈ normalizer (Zs : Set X) → ∀ x : X, x ∈ centralizer (Zs : Set X) →
        y * x * y⁻¹ ∈ centralizer (Zs : Set X) := by
      intro y hy x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : y⁻¹ * z * y ∈ Zs := by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer (Zs : Set X)).inv_mem hy) z).1 hz
        simpa using this
      have hxc := Subgroup.mem_centralizer_iff.1 hx (y⁻¹ * z * y) hz'
      calc z * (y * x * y⁻¹) = y * ((y⁻¹ * z * y) * x) * y⁻¹ := by group
        _ = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by rw [hxc]
        _ = y * x * y⁻¹ * z := by group
    refine ⟨fun hx => key r hrN x hx, fun hx => ?_⟩
    have := key r⁻¹ ((normalizer (Zs : Set X)).inv_mem hrN) _ hx
    simpa [mul_assoc] using this
  have hrE₂ : r ∈ normalizer (E₂ : Set X) :=
    oTwoPrimeOf_normalizes (A := Subgroup.zpowers r) (H := M₂ ⊓ centralizer (Zs : Set X))
      ((Subgroup.zpowers_le).2 (mem_normalizer_inf hrM₂ hrCZ)) (Subgroup.mem_zpowers r)
  have hcentE₂ : ∀ b ∈ E₂, ⁅b, r⁆ ∈ oddCoreOf E₂ := by
    intro b hb
    refine inf_oddCoreOf_le hE₂M₂ ⟨?_, hrcent b (hE₂M₂ hb)⟩
    have e : ⁅b, r⁆ = b * (r * b⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact E₂.mul_mem hb ((Subgroup.mem_normalizer_iff.1 hrE₂ b⁻¹).1 (E₂.inv_mem hb))
  have hsc : r ∈ centralizerSection E₂ (pPrimeCoreOf 2 E₂) :=
    ⟨hrE₂, mem_normalizer_oddCoreOf_of_mem_normalizer hrE₂, hcentE₂⟩
  obtain ⟨u₃, hu₃, hu₃C⟩ := hE₂I.exists_witness_centralizer_singleton hr2' hsc
  obtain ⟨hd1, hd2, -⟩ := hu₃.descend_singleton hE₂n hr2' hsc hu₃C
  set E₃ : Subgroup X := oTwoPrimeOf (E₂ ⊓ Cr) with hE₃
  have hE₂K : E₂ ≤ K0 X n (normalizer (Zs : Set X)) := le_sSup ⟨⟨u₂, hE₂I⟩, hE₂n⟩
  have hE₃E₂ : E₃ ≤ E₂ := (oTwoPrimeOf_le _).trans inf_le_left
  have hle : E₃ ≤ K0 X n (normalizer (Zs : Set X)) ⊓ Cr :=
    le_inf (hE₃E₂.trans hE₂K) ((oTwoPrimeOf_le _).trans inf_le_right)
  have hI : IsIntrinsicIn X (K0 X n (normalizer (Zs : Set X)) ⊓ Cr) E₃ u₃ :=
    ⟨hd1.1, hd1.2.1, ⟨hle, isPComponent_subgroupOf_mono hle
      (inf_le_inf_right _ (K0_le n (normalizer (Zs : Set X)))) hd1.2.2.1.2⟩, hd1.2.2.2⟩
  intro hbot
  have hE₃K0 : E₃ ≤ K0 X n (K0 X n (normalizer (Zs : Set X)) ⊓ Cr) := le_sSup ⟨⟨u₃, hI⟩, hd2⟩
  rw [hbot] at hE₃K0
  exact ne_bot_of_isDoubleCoverOfAlt hd2 (le_bot_iff.1 hE₃K0)

end CFSG.OddStandard.Solomon75
