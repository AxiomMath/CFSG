module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Desc
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseZ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Defs

variable {X : Type} [Group X]

@[expose] def invsOf (s : X) (A : Subgroup X) : Set X :=
  {r | r ∈ A ∧ r ≠ 1 ∧ r * r = 1 ∧ r * s = s * r}

@[expose] def hGrp (s : X) (A : Subgroup X) : Subgroup X := Subgroup.closure (invsOf s A)

theorem subset_hGrp {s : X} {A : Subgroup X} : invsOf s A ⊆ hGrp s A :=
  Subgroup.subset_closure

theorem hGrp_le (s : X) (A : Subgroup X) : hGrp s A ≤ A ⊓ centralizer ({s} : Set X) := by
  rw [hGrp, Subgroup.closure_le]
  intro r hr
  exact ⟨hr.1, Subgroup.mem_centralizer_singleton_iff.2 hr.2.2.2⟩

@[expose] def normComps (X : Type) [Group X] (n : ℕ) (s : X) : Subgroup X :=
  centralizer ({s} : Set X) ⊓
    ⨅ (B : Subgroup X) (_ : Sec5Comp X n (centralizer ({s} : Set X)) B), normalizer (B : Set X)

theorem mem_normComps_iff {n : ℕ} {s c : X} :
    c ∈ normComps X n s ↔ c ∈ centralizer ({s} : Set X) ∧
      ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → c ∈ normalizer (B : Set X) := by
  simp [normComps, Subgroup.mem_inf, Subgroup.mem_iInf]

theorem normComps_le_normalizer {n : ℕ} {s : X} {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) :
    normComps X n s ≤ normalizer (B : Set X) :=
  fun _ hc => (mem_normComps_iff.1 hc).2 B hB

end Defs

structure Sec5S (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))) (s : X) : Prop where
  data : Sec5Data X n z Z S
  inv : IsSec5Inv X Z s
  norm : ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → s ∈ normalizer (A : Set X)
  frac : ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → ∀ hs : s ∈ normalizer (A : Set X),
    ∀ M : AhatModel X n A, fixCount (M.perm s hs) ≤ 3 ∧ transCount (M.perm s hs) ≠ 3
  l54 : ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → ∀ r ∈ A, r ≠ 1 → r * r = 1 → r * s = s * r →
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) = ⊥ ∧
      ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → r ∈ normalizer (B : Set X)

section Setup

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem Sec5S.hGrp_le_normComps (hS : Sec5S X n z Z S s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) : hGrp s A ≤ normComps X n s := by
  rw [hGrp, Subgroup.closure_le]
  intro r hr
  rw [SetLike.mem_coe, mem_normComps_iff]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hr.2.2.2,
    (hS.l54 A hA r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).2⟩

@[expose] noncomputable def pAct (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B) :
    ↥(normComps X n s) →* Perm (Fin n) :=
  (M.permHom hn).comp (Subgroup.inclusion (normComps_le_normalizer hB))

omit [Finite X] in
theorem pAct_eq_one_iff (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B)
    (c : ↥(normComps X n s)) : pAct hn hB M c = 1 ↔ CentModOdd B (c : X) :=
  M.perm_eq_one_iff hn (normComps_le_normalizer hB c.2)

theorem Sec5S.pAct_ne_one (hS : Sec5S X n z Z S s) (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {r : X} (hr : r ∈ invsOf s A) :
    pAct hn hB M ⟨r, hS.hGrp_le_normComps hA (subset_hGrp hr)⟩ ≠ 1 := by
  intro h1
  rw [pAct_eq_one_iff] at h1
  have hl := hS.l54 A hA r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hr2 : r ^ 2 = 1 := by rw [sq]; exact hr.2.2.1
  have hrB : r ∈ normalizer (B : Set X) := hl.2 B hB
  have hsc : r ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
    ⟨hrB, mem_normalizer_oddCoreOf_of_mem_normalizer hrB, h1⟩
  obtain ⟨⟨u, hu⟩, hBn⟩ := hB
  obtain ⟨u', hu', hu'c⟩ := hu.exists_witness_centralizer_singleton hr2 hsc
  obtain ⟨hd1, hd2, -⟩ := hu'.descend_singleton hBn hr2 hsc hu'c
  set E : Subgroup X := oTwoPrimeOf (B ⊓ centralizer ({r} : Set X)) with hE
  have hEC : E ≤ centralizer ({s} : Set X) ⊓ centralizer ({r} : Set X) := hd1.2.2.1.1
  have hEB : E ≤ B := (oTwoPrimeOf_le _).trans inf_le_left
  have hEK : E ≤ K0 X n (centralizer ({s} : Set X)) := hEB.trans (le_sSup ⟨⟨u, hu⟩, hBn⟩)
  have hle : E ≤ K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X) :=
    le_inf hEK (hEC.trans inf_le_right)
  have hI : IsIntrinsicIn X (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) E
      u' :=
    ⟨hd1.1, hd1.2.1, ⟨hle, isPComponent_subgroupOf_mono hle
      (inf_le_inf_right _ (K0_le n (centralizer ({s} : Set X)))) hd1.2.2.1.2⟩, hd1.2.2.2⟩
  have hEK0 : E ≤ K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) :=
    le_sSup ⟨⟨u', hI⟩, hd2⟩
  rw [hl.1] at hEK0
  exact ne_bot_of_isDoubleCoverOfAlt hd2 (le_bot_iff.1 hEK0)

theorem Sec5S.odd_card_hGrp_inf_ker (hS : Sec5S X n z Z S s) (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) :
    Odd (Nat.card ↥((hGrp s A).subgroupOf (normComps X n s) ⊓ (pAct hn hB M).ker)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have hdvd : 2 ∣ Nat.card ↥((hGrp s A).subgroupOf (normComps X n s) ⊓ (pAct hn hB M).ker) := by
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    exact hodd
  obtain ⟨w, hw2⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set wN : ↥(normComps X n s) := (w : ↥(normComps X n s)) with hwN
  have hwH : wN ∈ (hGrp s A).subgroupOf (normComps X n s) := w.2.1
  have hwK : wN ∈ (pAct hn hB M).ker := w.2.2
  have h1 : orderOf wN = 2 := by
    have := Subgroup.orderOf_coe w
    rw [hw2] at this; exact this
  have h2 : orderOf (wN : X) = 2 := by
    have := Subgroup.orderOf_coe wN
    rw [h1] at this; exact this
  have hHA := hGrp_le s A (Subgroup.mem_subgroupOf.1 hwH)
  have hsq : (wN : X) * (wN : X) = 1 := by
    have := pow_orderOf_eq_one (wN : X)
    rwa [h2, sq] at this
  have hne : (wN : X) ≠ 1 := by
    intro h; rw [h, orderOf_one] at h2; omega
  have hr : (wN : X) ∈ invsOf s A :=
    ⟨hHA.1, hne, hsq, Subgroup.mem_centralizer_singleton_iff.1 hHA.2⟩
  have hne1 := hS.pAct_ne_one hn hB M hA hr
  exact hne1 (MonoidHom.mem_ker.1 hwK)

omit [Finite X] in
theorem exists_involution_rep {A : Subgroup X} (a : ↥A)
    (h : (QuotientGroup.mk a : ↥A ⧸ pPrimeCore 2 ↥A) * QuotientGroup.mk a = 1) [Finite X] :
    ∃ y : ↥A, y * y = 1 ∧
      (QuotientGroup.mk y : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk a := by
  have haa : ((a * a : ↥A) : X) ∈ pPrimeCoreOf 2 A := by
    have : (QuotientGroup.mk (a * a) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 := by
      rw [QuotientGroup.mk_mul]; exact h
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 this, rfl⟩
  have hμ : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 A)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf A)
  obtain ⟨m, hm1, hm2⟩ := exists_zpow_twoElt_of_pow_mem hμ (j := 1)
    (a := (a : X)) (by simpa [sq] using haa)
  refine ⟨a ^ m, ?_, ?_⟩
  · apply Subtype.ext
    simpa [sq, Subgroup.coe_mul] using hm1
  · rw [eq_comm, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := hm2
    have : a⁻¹ * a ^ m = w := Subtype.ext (by simpa using hwe.symm)
    rw [this]; exact hw

omit [Finite X] in
theorem exists_inv_lift {A : Subgroup X} {s : X} [Finite X]
    (hA : IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n) (hs : s ∈ normalizer (A : Set X))
    (hs2 : s * s = 1) {x : ↥A ⧸ pPrimeCore 2 ↥A}
    (hx : (AhatModel.ofCover hA).autOf s hs x = x) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ r, r ∈ invsOf s A ∧ ∃ hrA : r ∈ A,
      (QuotientGroup.mk (⟨r, hrA⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have hsq : (s : X) ^ 2 = 1 := by rw [sq]; exact hs2
  have h1 : (QuotientGroup.mk (conjAut hs a) : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk a :=
    (AhatModel.autOf_mk (AhatModel.ofCover hA) hs a).symm.trans hx
  obtain ⟨b, hbb, hmkb'⟩ := exists_involution_rep a hx2
  have hmkb : (QuotientGroup.mk a : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk b := hmkb'.symm
  have hyA : (b : X) ∈ A := b.2
  have hmkc : (QuotientGroup.mk (conjAut hs b) : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk b := by
    have e1 : quotConj hs (QuotientGroup.mk b) = QuotientGroup.mk (conjAut hs b) :=
      QuotientGroup.congr_mk _ _ _ _ b
    have e2 : quotConj hs (QuotientGroup.mk a) = QuotientGroup.mk (conjAut hs a) :=
      QuotientGroup.congr_mk _ _ _ _ a
    rw [← e1, ← hmkb, e2, h1]
  have hu : (s * (b : X) * s⁻¹)⁻¹ * (b : X) ∈ pPrimeCoreOf 2 A := by
    have hm : ((conjAut hs b)⁻¹ * b : ↥A) ∈ pPrimeCore 2 ↥A := QuotientGroup.eq.1 hmkc
    exact ⟨_, hm, by simp [coe_conjAut]⟩
  have hcomm : ⁅(b : X), s⁆ ∈ pPrimeCoreOf 2 A := by
    have e : ⁅(b : X), s⁆ = (b : X) * ((s * (b : X) * s⁻¹)⁻¹ * (b : X)) * (b : X)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hyA) _).1 hu
  have hb2 : (b : X) ^ (2 ^ 1) = 1 := by
    have := congrArg Subtype.val hbb
    simpa [sq] using this
  obtain ⟨c, hc, hc2, hcy⟩ := exists_twoElt_centralizer_of_comm_mem hsq
    (mem_normalizer_oddCoreOf_of_mem_normalizer hs) hyA hcomm hb2
  have hcb : (QuotientGroup.mk (⟨c, hc.1⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) =
      QuotientGroup.mk b := by
    rw [QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := hcy
    have : (⟨c, hc.1⟩ : ↥A)⁻¹ * b = w := Subtype.ext (by simpa using hwe.symm)
    rw [this]; exact hw
  have hcx : (QuotientGroup.mk (⟨c, hc.1⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk a :=
    hcb.trans hmkb.symm
  refine ⟨c, ⟨hc.1, ?_, ?_, Subgroup.mem_centralizer_singleton_iff.1 hc.2⟩, hc.1, hcx⟩
  · rintro rfl
    apply hx1
    rw [← hcx]
    exact (QuotientGroup.eq_one_iff _).2 (one_mem _)
  · simpa [sq] using hc2

theorem Sec5Data.exists_sec5_inv (h : Sec5Data X n z Z S) : ∃ s, IsSec5Inv X Z s := by
  have hZS : Z ≤ Sec5Syl S :=
    le_map_sylow_of_isPGroup_normalizer h.isPGroup_Z rfl S
  by_contra hcon
  push Not at hcon
  apply h.l52.e
  refine Set.Subset.antisymm ?_ (fun x hx => ⟨hZS hx, 1, by simpa using hx⟩)
  rintro x ⟨hxS, g, hg⟩
  by_contra hxZ
  have hxN : x ∈ normalizer (Z : Set X) := Subgroup.map_subtype_le _ hxS
  have hsq : x * x = 1 := by
    have h1 := h.Z_sq_eq_one hg
    calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact hcon x ⟨hxN, hxZ, hsq, g, hg, fun h1 => hxZ (by
    have : x = 1 := by
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    rw [this]; exact one_mem _)⟩

theorem Sec5S.mk_of_hyps (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (h54 : Solomon75Lemma54p) (h : Sec5Data X n z Z S)
    (hk : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂)
    (hs : IsSec5Inv X Z s) : Sec5S X n z Z S s where
  data := h
  inv := hs
  norm A hA := mem_normalizer_of_map_conj_eq (hN X n z Z S h s hs A hA)
  frac := (hF X n z Z S h s hs).1
  l54 := h54 X n z Z S h hk s hs

end Setup

end CFSG.OddStandard.Solomon75
