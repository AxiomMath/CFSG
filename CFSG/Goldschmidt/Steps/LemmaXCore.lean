module

import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification

namespace LemmaX

theorem two_dvd_card_of_isQuasisimple {K : Type*} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) : 2 ∣ Nat.card K := by
  by_contra h
  have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hodd
  have : Nontrivial K := Quasisimple.nontrivial hK
  have : Group.IsPerfect K := ⟨hK.1⟩
  exact Group.IsPerfect.not_isSolvable K ‹_›

theorem layer_structure {Q : Type} [Group Q] [Finite Q] (hO : goldschmidtOddCore Q = ⊥)
    (P : Sylow 2 Q) {B : Subgroup Q} (ha : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hb : B = CFSG.Open.pCore 2 Q ⊔
      Subgroup.closure {t | t ∈ (P : Subgroup Q) ⊓ goldschmidtLayer Q ∧ t ^ 2 = 1})
    (hC2 : CFSG.Open.pCore 2 Q ≤ Subgroup.center Q) (K : Subgroup Q) (hK : IsComponentOf K ⊤)
    (hfaith : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set Q) → b = 1) :
    K = ⊤ ∧ Subgroup.center Q = ⊥ ∧ ∀ t ∈ (P : Subgroup Q), t ^ 2 = 1 → t ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2B : CFSG.Open.pCore 2 Q ≤ B := hb ▸ le_sup_left
  have hO2 : CFSG.Open.pCore 2 Q = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    exact Subgroup.mem_bot.2
      (hfaith p (hO2B hp) (Subgroup.center_le_centralizer _ (hC2 hp)))
  have hL : goldschmidtLayer Q = ⊤ := by rw [← ha, hO2, bot_sup_eq]
  have hinv : ∀ t ∈ (P : Subgroup Q), t ^ 2 = 1 → t ∈ B := by
    intro t ht ht2
    rw [hb]
    refine Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨ht, ?_⟩, ht2⟩)
    rw [hL]
    exact Subgroup.mem_top t
  have hone : ∀ K₂ : Subgroup Q, IsComponentOf K₂ ⊤ → K₂ = K := by
    intro K₂ hK₂
    by_contra hne
    have hsub := Components.mathlib_subnormal_of_chain hK₂.2.1 Subgroup.IsSubnormal.top
    obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hsub
    obtain ⟨s, hsR, hs2⟩ := PropHSetup.exists_orderOf_eq_two R.isPGroup'
      (R.ne_bot_of_dvd_card (two_dvd_card_of_isQuasisimple hK₂.2.2))
    have hs2' : orderOf (s : Q) = 2 := (Subgroup.orderOf_coe s).trans hs2
    have hsP : (s : Q) ∈ (P : Subgroup Q) := by
      have h1 : (s : Q) ∈ (R : Subgroup K₂).map K₂.subtype := ⟨s, hsR, rfl⟩
      rw [hR] at h1
      exact h1.1
    have hsB : (s : Q) ∈ B := hinv _ hsP (hs2' ▸ pow_orderOf_eq_one (s : Q))
    have hsC : (s : Q) ∈ Subgroup.centralizer (K : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b Q K₂ K hK₂ hK hne) s.2
    have h1 := hfaith _ hsB hsC
    rw [h1, orderOf_one] at hs2'
    exact absurd hs2' (by norm_num)
  have hKtop : K = ⊤ := by
    rw [← hL]
    refine le_antisymm (le_sSup hK) (sSup_le fun K₂ hK₂ => (hone K₂ hK₂).le)
  have hZ : Subgroup.center Q = ⊥ := by
    obtain ⟨-, hZE, -⟩ := N8d Q hO
    rw [eq_bot_iff, ← hO2]
    intro x hx
    have hxL : x ∈ goldschmidtLayer Q := by
      rw [hL]
      exact Subgroup.mem_top x
    apply hZE
    exact ⟨⟨x, hxL⟩,
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 hx y), rfl⟩
  exact ⟨hKtop, hZ, hinv⟩

theorem stronglyEmbedded_of {Q : Type} [Group Q] [Finite Q] (P : Sylow 2 Q) {B J : Subgroup Q}
    (hBP : B ≤ P) (hBab : IsMulCommutative B)
    (hBcl : fusionStronglyClosed (B : Set Q) (P : Subgroup Q))
    (hNB : Subgroup.normalizer (B : Set Q) ≤ J)
    (hCB : ∀ b ∈ B, b ≠ 1 → Subgroup.centralizer ({b} : Set Q) ≤ J)
    (hinv : ∀ t ∈ (P : Subgroup Q), t ^ 2 = 1 → t ∈ B) (hJ : J ≠ ⊤) (hB1 : B ≠ ⊥) :
    fusionStronglyEmbedded J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBJ : B ≤ J := fun b hb => hNB (Subgroup.le_normalizer hb)
  have hctl := N5a Q P B J hBP hBab hBcl hNB
  have hC : ∀ x ∈ J, orderOf x = 2 → Subgroup.centralizer ({x} : Set Q) ≤ J := by
    intro x hxJ hx2
    have hxsq : x ^ 2 = 1 := hx2 ▸ pow_orderOf_eq_one x
    have hx2' : x ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hxsq
    obtain ⟨m, hm⟩ := exists_conj_mem_sylow P hx2'
    have hmB : m * x * m⁻¹ ∈ B := hinv _ hm (by rw [conj_pow, hxsq, mul_one, mul_inv_cancel])
    obtain ⟨h, hhJ, hh⟩ := hctl x m⁻¹ hxJ (by simpa using hBJ hmB) ⟨1, hx2'⟩
    have hb1 : m * x * m⁻¹ ≠ 1 := by
      intro h1
      have : x = 1 := by
        calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    have e : m * x * m⁻¹ = h⁻¹ * x * h := by rw [hh]; group
    intro c hc
    have h1 : h⁻¹ * c * h ∈ Subgroup.centralizer ({m * x * m⁻¹} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      rw [e]
      calc h⁻¹ * c * h * (h⁻¹ * x * h) = h⁻¹ * (c * x) * h := by group
        _ = h⁻¹ * (x * c) * h := by rw [hc]
        _ = h⁻¹ * x * h * (h⁻¹ * c * h) := by group
    have h2 := hCB _ hmB hb1 h1
    have e2 : c = h * (h⁻¹ * c * h) * h⁻¹ := by group
    rw [e2]
    exact J.mul_mem (J.mul_mem hhJ h2) (J.inv_mem hhJ)
  refine ⟨hJ, ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb, hb2⟩ := PropHSetup.exists_orderOf_eq_two (P.isPGroup'.to_le hBP) hB1
    exact even_iff_two_dvd.2 (hb2 ▸ Subgroup.orderOf_dvd_natCard J (hBJ hb))
  · by_contra hodd
    obtain ⟨x, hx, hx2⟩ := exists_mem_orderOf_eq_two hodd
    obtain ⟨hxJ, hxg⟩ := Subgroup.mem_inf.1 hx
    have hgx : g * x * g⁻¹ ∈ J := mem_map_conj_inv_iff.1 hxg
    obtain ⟨h, hhJ, hh⟩ := hctl x g⁻¹ hxJ (by simpa using hgx)
      ⟨1, by rw [pow_one, ← hx2, pow_orderOf_eq_one]⟩
    have hhg : h * g ∈ Subgroup.centralizer ({x} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : g * x * g⁻¹ = h⁻¹ * x * h := by rw [hh]; group
      calc h * g * x = h * (g * x * g⁻¹) * g := by group
        _ = h * (h⁻¹ * x * h) * g := by rw [e]
        _ = x * (h * g) := by group
    apply hg
    have := J.mul_mem (J.inv_mem hhJ) (hC x hxJ hx2 hhg)
    simpa using this

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCoreOf_le {E J M : Subgroup Y} (hEab : IsMulCommutative E)
    (hEexp : ∀ e ∈ E, e ^ 2 = 1) (hE4 : 4 ≤ Nat.card E)
    (hCJ : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set Y) ≤ J) (hEM : E ≤ M) :
    oddCoreOf M ≤ J := by
  refine le_of_forall_inf_centralizer_le hEab hEexp hE4 ?_ ?_
    fun e he he1 => inf_le_right.trans (hCJ e he he1)
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨e, hEM he⟩ * o * ⟨e, hEM he⟩⁻¹,
        (goldschmidtOddCore_normal M).conj_mem o ho _, rfl⟩
    · rintro ⟨o, ho, hoe⟩
      refine ⟨⟨e, hEM he⟩⁻¹ * o * ⟨e, hEM he⟩, ?_, ?_⟩
      · have := (goldschmidtOddCore_normal M).conj_mem o ho ⟨e, hEM he⟩⁻¹
        simpa using this
      · have hoe' : (o : Y) = e * x * e⁻¹ := hoe
        show (e : Y)⁻¹ * o * e = x
        rw [hoe']
        group
  · rw [oddCoreOf, Subgroup.card_map_of_injective M.subtype_injective]
    exact OddCore.odd_card M

theorem core_fusion (T : Sylow 2 Y) {E J M : Subgroup Y} (hET : E ≤ T)
    (hEab : IsMulCommutative E) (hEexp : ∀ e ∈ E, e ^ 2 = 1)
    (hEcl : fusionStronglyClosed (E : Set Y) (T : Subgroup Y))
    (hNJ : Subgroup.normalizer (E : Set Y) ≤ J)
    (hCJ : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set Y) ≤ J) (hEM : E ≤ M)
    (hOJ : oddCoreOf M ≤ J) {e₁ e₂ : Y} (he₁ : e₁ ∈ E) (he₁1 : e₁ ≠ 1) (he₂ : e₂ ∈ E) (m : M)
    (h : ((m⁻¹ * ⟨e₁, hEM he₁⟩ * m : M) : M ⧸ goldschmidtOddCore M) =
      ((⟨e₂, hEM he₂⟩ : M) : M ⧸ goldschmidtOddCore M)) :
    (m : Y) ∈ J := by
  have hEJ : E ≤ J := fun e he => hNJ (Subgroup.le_normalizer he)
  have hO : (⟨e₂, hEM he₂⟩ : M)⁻¹ * (m⁻¹ * ⟨e₁, hEM he₁⟩ * m) ∈ goldschmidtOddCore M :=
    QuotientGroup.eq.1 h.symm
  set o : M := (⟨e₂, hEM he₂⟩ : M)⁻¹ * (m⁻¹ * ⟨e₁, hEM he₁⟩ * m) with ho
  have hoY : (o : Y) = e₂⁻¹ * ((m : Y)⁻¹ * e₁ * m) := by simp [ho]
  have he₂2 : e₂ * e₂ = 1 := by rw [← sq]; exact hEexp e₂ he₂
  have he₁2 : e₁ * e₁ = 1 := by rw [← sq]; exact hEexp e₁ he₁
  have hmul : e₂ * (o : Y) = (m : Y)⁻¹ * e₁ * m := by rw [hoY]; group
  have hto : e₂ * (o : Y) * (e₂ * o) = 1 := by
    rw [hmul]
    calc (m : Y)⁻¹ * e₁ * m * ((m : Y)⁻¹ * e₁ * m) = (m : Y)⁻¹ * (e₁ * e₁) * m := by group
      _ = 1 := by rw [he₁2]; group
  have hoodd : Odd (orderOf (o : Y)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (OddCore.odd_card M) (Subgroup.orderOf_dvd_natCard _ hO)
  obtain ⟨a, ha⟩ := exists_pow_conj_eq_mul he₂2 hto hoodd
  have hc : (o : Y) ^ a ∈ J := hOJ ⟨o ^ a, Subgroup.pow_mem _ hO a, by simp⟩
  set c : Y := (o : Y) ^ a with hcdef
  have h3 : (m : Y)⁻¹ * e₁ * m = c⁻¹ * e₂ * c := by rw [← hmul, ha]
  have h4 : ((m : Y) * c⁻¹)⁻¹ * e₁ * ((m : Y) * c⁻¹) = e₂ := by
    calc ((m : Y) * c⁻¹)⁻¹ * e₁ * ((m : Y) * c⁻¹) = c * ((m : Y)⁻¹ * e₁ * m) * c⁻¹ := by
          group
      _ = e₂ := by rw [h3]; group
  obtain ⟨g, hgJ, hg⟩ := N5a Y T E J hET hEab hEcl hNJ e₁ ((m : Y) * c⁻¹) (hEJ he₁)
    (by rw [h4]; exact hEJ he₂) ⟨1, by rw [pow_one]; exact hEexp e₁ he₁⟩
  set k : Y := (m : Y) * c⁻¹ with hk
  have h5 : k * g⁻¹ ∈ Subgroup.centralizer ({e₁} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : k * g⁻¹ * e₁ * (k * g⁻¹)⁻¹ = e₁ := by
      calc k * g⁻¹ * e₁ * (k * g⁻¹)⁻¹ = k * (g⁻¹ * e₁ * g) * k⁻¹ := by group
        _ = e₁ := by rw [hg]; group
    calc k * g⁻¹ * e₁ = k * g⁻¹ * e₁ * (k * g⁻¹)⁻¹ * (k * g⁻¹) := by group
      _ = e₁ * (k * g⁻¹) := by rw [e]
  have h6 := hCJ e₁ he₁ he₁1 h5
  have e : (m : Y) = k * g⁻¹ * g * c := by rw [hk]; group
  rw [e]
  exact J.mul_mem (J.mul_mem h6 hgJ) hc

theorem core_embedding {n : ℕ} (hIH : IH n) (hYn : Nat.card Y < n) (T : Sylow 2 Y)
    {E J : Subgroup Y} (hET : E ≤ T) (hEab : IsMulCommutative E)
    (hEexp : ∀ e ∈ E, e ^ 2 = 1) (hE4 : 4 ≤ Nat.card E)
    (hEcl : fusionStronglyClosed (E : Set Y) (T : Subgroup Y))
    (hNJ : Subgroup.normalizer (E : Set Y) ≤ J)
    (hCJ : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set Y) ≤ J) (hJ : J ≠ ⊤)
    {X : Type*} [Group X] [Finite X] (ι : X →* Y) (hι : Function.Injective ι)
    (hιn : ι.range.Normal) (hιE : ι.range ≤ Subgroup.normalClosure (E : Set Y))
    (hιe : ∃ x : X, ι x ∈ E ∧ ι x ≠ 1) :
    fusionStronglyEmbedded (J.comap ι) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEJ : E ≤ J := fun e he => hNJ (Subgroup.le_normalizer he)
  have hTsyl : fusionIsSylowIn 2 (T : Subgroup Y) ⊤ :=
    ⟨le_top, T.isPGroup', fun P _ hP hTP => T.is_maximal' hP hTP⟩
  obtain ⟨hC, hC1, hC2, -, -⟩ := N16_of N1 n hIH Y T E ⊤ T hET hEab hEcl hET hTsyl
    (by rw [Subgroup.card_top]; exact hYn)
  set M : Subgroup Y := normalClosureIn ⊤ E with hMdef
  have hMeq : M = Subgroup.normalClosure (E : Set Y) := by
    rw [hMdef, normalClosureIn,
      Subgroup.map_normalClosure _ _ (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, Subgroup.mem_top y⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hMn : M.Normal := by rw [hMeq]; exact Subgroup.normalClosure_normal
  have hEM : E ≤ M := by rw [hMeq]; exact Subgroup.le_normalClosure
  have hιM : ∀ x, ι x ∈ M := fun x => by rw [hMeq]; exact hιE ⟨x, rfl⟩
  have hOJ : oddCoreOf M ≤ J := oddCoreOf_le hEab hEexp hE4 hCJ hEM
  set π := QuotientGroup.mk' (goldschmidtOddCore M) with hπ
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hMn.isSubnormal
  have hPMeq : (PM : Subgroup M) = (T : Subgroup Y).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hPM, Subgroup.subgroupOf_map_subtype]
  have hEPM : E.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPMeq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hET (Subgroup.mem_subgroupOf.1 hx))
  have hclM := stronglyClosed_subgroupOf T hEcl hEM PM hEPM
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (E.subgroupOf M) (goldschmidtOddCore M) hEPM hclM
  set Ebar := (E.subgroupOf M).map π with hEbar
  set Jbar := (J.subgroupOf M).map π with hJbar
  have hEJbar : Ebar ≤ Jbar :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (hEJ (Subgroup.mem_subgroupOf.1 hx))
  have hEbarS : Ebar ≤ (Sbar : Subgroup _) := by
    rw [hSbar]
    exact Subgroup.map_mono hEPM
  have hEbarab : IsMulCommutative Ebar :=
    isMulCommutative_map (isMulCommutative_subgroupOf hEab M) π
  have hπE : ∀ w : M, (w : Y) ∈ E → π w = 1 → (w : Y) = 1 := by
    intro w hwE hw
    have hwO : w ∈ goldschmidtOddCore M := (QuotientGroup.eq_one_iff w).1 hw
    by_contra hw1
    have hw2 : orderOf w = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hEexp _ hwE) hw1
    exact not_mem_of_odd_card (OddCore.odd_card M) hw2 hwO
  have hpre : ∀ m : M, π m ∈ Jbar → (m : Y) ∈ J := by
    intro m hm
    obtain ⟨j, hj, hjm⟩ := hm
    have h1 : j⁻¹ * m ∈ goldschmidtOddCore M := QuotientGroup.eq.1 hjm
    have h2 : ((j⁻¹ * m : M) : Y) ∈ J := hOJ ⟨_, h1, rfl⟩
    have e : (m : Y) = (j : Y) * ((j⁻¹ * m : M) : Y) := by simp
    rw [e]
    exact J.mul_mem (Subgroup.mem_subgroupOf.1 hj) h2
  have hF4 : ∀ w : M, (w : Y) ∈ E → (w : Y) ≠ 1 →
      Subgroup.centralizer ({π w} : Set (M ⧸ goldschmidtOddCore M)) ≤ Jbar := by
    intro w hwE hw1 x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore M) x
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hx' : ((m : M) : M ⧸ goldschmidtOddCore M) * (w : M ⧸ goldschmidtOddCore M) =
        (w : M ⧸ goldschmidtOddCore M) * (m : M ⧸ goldschmidtOddCore M) := hx
    have h1 : ((m⁻¹ * w * m : M) : M ⧸ goldschmidtOddCore M) = (w : M ⧸ goldschmidtOddCore M) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc, ← hx']
      group
    exact ⟨m, Subgroup.mem_subgroupOf.2
      (core_fusion T hET hEab hEexp hEcl hNJ hCJ hEM hOJ hwE hw1 hwE m h1), rfl⟩
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    have h1 : 1 < Nat.card E := by omega
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨⟨e, he⟩, he1⟩ := exists_ne (1 : E)
    exact ⟨e, he, fun h => he1 (Subtype.ext h)⟩
  have hEbar1 : Ebar ≠ ⊥ := by
    intro hbot
    have : π ⟨e₀, hEM he₀⟩ ∈ Ebar := ⟨⟨e₀, hEM he₀⟩, Subgroup.mem_subgroupOf.2 he₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact he₀1 (hπE _ he₀ this)
  have hF5 : Subgroup.normalizer (Ebar : Set (M ⧸ goldschmidtOddCore M)) ≤ Jbar := by
    intro x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore M) x
    have h1 : π m * π ⟨e₀, hEM he₀⟩ * (π m)⁻¹ ∈ Ebar :=
      (Subgroup.mem_normalizer_iff.1 hx _).1 ⟨⟨e₀, hEM he₀⟩, Subgroup.mem_subgroupOf.2 he₀, rfl⟩
    obtain ⟨w, hw, hwe⟩ := h1
    have h2 : ((m⁻¹⁻¹ * ⟨e₀, hEM he₀⟩ * m⁻¹ : M) : M ⧸ goldschmidtOddCore M) =
        ((⟨(w : Y), hEM (Subgroup.mem_subgroupOf.1 hw)⟩ : M) : M ⧸ goldschmidtOddCore M) := by
      rw [inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hwe.symm
    have h3 := core_fusion T hET hEab hEexp hEcl hNJ hCJ hEM hOJ he₀ he₀1
      (Subgroup.mem_subgroupOf.1 hw) m⁻¹ h2
    refine ⟨m, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    have := J.inv_mem h3
    simpa using this
  have hJbar : Jbar ≠ ⊤ := by
    intro htop
    apply hJ
    have hMJ : M ≤ J := fun y hy => hpre ⟨y, hy⟩ (htop ▸ Subgroup.mem_top _)
    rw [eq_top_iff, ← hC1]
    exact sup_le hMJ (inf_le_right.trans hNJ)
  obtain ⟨ha, hb, -⟩ := hC
  have hb' : Ebar = CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure
      {t | t ∈ (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) ⊓
        goldschmidtLayer (M ⧸ goldschmidtOddCore M) ∧ t ^ 2 = 1} := by
    rw [hSbar, hPMeq]
    exact hb
  by_cases hA : ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      ∃ b ∈ Ebar, b ∈ Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M)) ∧ b ≠ 1
  · exfalso
    apply hJbar
    rw [eq_top_iff, ← ha]
    refine sup_le ((hb'.ge.trans' le_sup_left).trans hEJbar) ?_
    refine sSup_le fun K hK => ?_
    obtain ⟨b, hbE, hbK, hb1⟩ := hA K hK
    obtain ⟨w, hw, rfl⟩ := hbE
    have hw1 : (w : Y) ≠ 1 := fun h => hb1 (by rw [show w = 1 from Subtype.ext h, map_one])
    intro k hk
    apply hF4 w (Subgroup.mem_subgroupOf.1 hw) hw1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hbK) k hk
  push Not at hA
  obtain ⟨K, hK, hKf⟩ := hA
  obtain ⟨hKtop, hZ, hinv⟩ := layer_structure (goldschmidtOddCore_quotient_eq_bot M) Sbar ha hb'
    hC2 K hK hKf
  have hCB : ∀ b ∈ Ebar, b ≠ 1 →
      Subgroup.centralizer ({b} : Set (M ⧸ goldschmidtOddCore M)) ≤ Jbar := by
    rintro _ ⟨w, hw, rfl⟩ hb1
    exact hF4 w (Subgroup.mem_subgroupOf.1 hw)
      (fun h => hb1 (by rw [show w = 1 from Subtype.ext h, map_one]))
  have hSE := stronglyEmbedded_of Sbar hEbarS hEbarab hclbar hF5 hCB hinv hJbar hEbar1
  let f : X →* M ⧸ goldschmidtOddCore M := π.comp (ι.codRestrict M hιM)
  have hf : ∀ x, f x = π ⟨ι x, hιM x⟩ := fun x => rfl
  have hrn : f.range.Normal := by
    constructor
    rintro _ ⟨x, rfl⟩ g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore M) g
    obtain ⟨x', hx'⟩ := hιn.conj_mem (ι x) ⟨x, rfl⟩ (m : Y)
    refine ⟨x', ?_⟩
    have e : (⟨ι x', hιM x'⟩ : M) = m * ⟨ι x, hιM x⟩ * m⁻¹ := Subtype.ext (by simpa using hx')
    rw [hf, e, map_mul, map_mul, map_inv, ← hf]
  have hr1 : f.range ≠ ⊥ := by
    obtain ⟨x₀, hx₀E, hx₀1⟩ := hιe
    intro hbot
    have : f x₀ ∈ f.range := ⟨x₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx₀1 (hπE ⟨ι x₀, hιM x₀⟩ hx₀E this)
  have hfsurj : Function.Surjective f := by
    have := hrn
    rw [← MonoidHom.range_eq_top]
    rcases LocalComponents.normal_contains_or_commutes K f.range hK with h | h
    · exact eq_top_iff.2 (hKtop ▸ h)
    · exfalso
      apply hr1
      have hle : f.range ≤ Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M)) := by
        rw [Subgroup.commutator_comm] at h
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      rw [hKtop, Subgroup.coe_top, Subgroup.centralizer_univ, hZ] at hle
      exact le_bot_iff.1 hle
  have hker : Odd (Nat.card f.ker) := by
    let g := ι.codRestrict M hιM
    have hginj : Function.Injective g := fun a b hab => hι (congrArg Subtype.val hab)
    have hle : f.ker.map g ≤ goldschmidtOddCore M := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hx
    rw [← Subgroup.card_map_of_injective hginj]
    exact (OddCore.odd_card M).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hcomap : J.comap ι = Jbar.comap f := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨ι x, hιM x⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    · intro hx
      exact hpre ⟨ι x, hιM x⟩ hx
  rw [hcomap]
  exact fusionStronglyEmbedded_comap f hfsurj hker hSE

end LemmaX

end CFSG.Goldschmidt
