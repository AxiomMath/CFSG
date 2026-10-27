module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33ZStar

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem IsIntrinsicIn.isTwoGenQuasi {H L : Subgroup X} {u : X} (h : IsIntrinsicIn X H L u) :
    IsTwoGenQuasi ↥L :=
  (isTwoGenQuasi_subgroupOf_iff h.2.2.1.1).1 (isPComponent_two_iff.1 h.2.2.1.2).2

omit [Finite X] in
theorem IsIntrinsicIn.comm_mem {H L : Subgroup X} {u : X} (h : IsIntrinsicIn X H L u) :
    ∀ l ∈ L, ⁅l, u⁆ ∈ pPrimeCoreOf 2 L := by
  intro l hl
  have huL : u ∈ L := h.2.1
  have heq : L = pPrimeCoreOf 2 L ⊔ oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) :=
    h.2.2.2.1
  have hEle : oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) ≤
      L ⊓ centralizer ({u} : Set X) := by
    rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact oTwoPrimeOf_le _
  have hEnorm : oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) ≤
      normalizer (pPrimeCoreOf 2 L : Set X) := fun e he =>
    mem_normalizer_pPrimeCoreOf_of_mem (hEle he).1
  have hl' : l ∈ pPrimeCoreOf 2 L ⊔ oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) := by
    rw [← heq]; exact hl
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hEnorm] at hl'
  obtain ⟨o, ho, e, he, rfl⟩ := hl'
  have heu : ⁅e, u⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEle he).2)
  have hid : ⁅o * e, u⁆ = o * ⁅e, u⁆ * o⁻¹ * ⁅o, u⁆ := by
    simp only [commutatorElement_def]; group
  have hun : u ∈ normalizer (pPrimeCoreOf 2 L : Set X) := mem_normalizer_pPrimeCoreOf_of_mem huL
  have hou : ⁅o, u⁆ = o * (u * o⁻¹ * u⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [hid, heu]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [hou]
  exact (pPrimeCoreOf 2 L).mul_mem ho
    ((Subgroup.mem_normalizer_iff.1 hun o⁻¹).1 ((pPrimeCoreOf 2 L).inv_mem ho))

omit [Finite X] in
theorem IsIntrinsicIn.mem_zStar {H L : Subgroup X} {u : X} (h : IsIntrinsicIn X H L u) :
    u ∈ zStar L :=
  ⟨h.2.1, Subgroup.le_normalizer h.2.1, mem_normalizer_pPrimeCoreOf_of_mem h.2.1,
    fun k hk => h.comm_mem k hk⟩

omit [Finite X] in
theorem IsIntrinsicIn.conj_witness {H L : Subgroup X} {u g : X} (h : IsIntrinsicIn X H L u)
    (hH : g ∈ normalizer (H : Set X)) (hL : g ∈ normalizer (L : Set X)) :
    IsIntrinsicIn X H L (g * u * g⁻¹) := by
  have h' := h.map_mulEquiv (MulAut.conj g)
  rw [map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hL] at h'
  simpa [MulAut.conj_apply] using h'

theorem IsIntrinsicIn.exists_witness_centralizer {H L T : Subgroup X} {u : X}
    (h : IsIntrinsicIn X H L u) (hT : IsPGroup 2 ↥T)
    (hTc : T ≤ centralizerSection L (pPrimeCoreOf 2 L)) :
    ∃ u' : X, IsIntrinsicIn X H L u' ∧ u' ∈ centralizer (T : Set X) := by
  have huL : u ∈ L := h.2.1
  have hu2 : u ^ (2 ^ 1) = 1 := by simpa [h.1] using pow_orderOf_eq_one u
  have hO : T ≤ normalizer (pPrimeCoreOf 2 L : Set X) := fun t ht => (hTc ht).2.1
  obtain ⟨c, hc, -, hcu⟩ := exists_twoElt_centralizer_of_comm_mem_pgroup hT hO huL
    (fun t ht => (hTc ht).2.2 u huL) hu2
  have hcL : c ∈ L := hc.1
  have hcT : c ∈ centralizer (T : Set X) := hc.2
  have hodd : Odd (Nat.card (pPrimeCoreOf 2 L)) := odd_card_oddCoreOf L
  have hAN : Subgroup.zpowers c ≤ normalizer (pPrimeCoreOf 2 L : Set X) :=
    Subgroup.zpowers_le.2 (mem_normalizer_pPrimeCoreOf_of_mem hcL)
  have hx : u ∈ Subgroup.zpowers c ⊔ pPrimeCoreOf 2 L := by
    have := Subgroup.mul_mem_sup (Subgroup.mem_zpowers c) hcu
    rwa [mul_inv_cancel_left] at this
  obtain ⟨o, ho, a, ha, -, hua⟩ := exists_conj_twoElt_of_mem_sup_odd_X hAN hodd hx hu2
  have hoL : o ∈ L := by
    obtain ⟨w, -, rfl⟩ := ho
    exact w.2
  have hoH : o ∈ H := h.2.2.1.1 hoL
  have hg : o⁻¹ ∈ normalizer (H : Set X) := Subgroup.le_normalizer (H.inv_mem hoH)
  have hgL : o⁻¹ ∈ normalizer (L : Set X) := Subgroup.le_normalizer (L.inv_mem hoL)
  refine ⟨o⁻¹ * u * (o⁻¹)⁻¹, h.conj_witness hg hgL, ?_⟩
  have hae : o⁻¹ * u * (o⁻¹)⁻¹ = a := by rw [hua]; group
  rw [hae]
  exact Subgroup.zpowers_le.2 hcT ha

omit [Finite X] in
theorem aux_dedekind {A O F : Subgroup X} (hFA : F ≤ A) (hFO : F ≤ normalizer (O : Set X))
    (hA : A ≤ O ⊔ F) : A ≤ (A ⊓ O) ⊔ F := by
  intro x hx
  have hx' : x ∈ ((O ⊔ F : Subgroup X) : Set X) := hA hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O F hFO] at hx'
  obtain ⟨o, ho, f, hf, rfl⟩ := hx'
  have hoA : o ∈ A := by
    have h1 : o = o * f * f⁻¹ := by group
    rw [h1]
    exact A.mul_mem hx (A.inv_mem (hFA hf))
  exact Subgroup.mul_mem_sup ⟨hoA, ho⟩ hf

omit [Finite X] in
theorem aux_mem_normalizer_centralizer_singleton {t u : X} (h : t * u = u * t) :
    t ∈ normalizer (centralizer ({u} : Set X) : Set X) := by
  apply mem_normalizer_of_map_conj_eq
  have h1 := centralizer_singleton_map_mulEquiv (MulAut.conj t) u
  have h2 : (MulAut.conj t) u = u := by
    rw [MulAut.conj_apply, h]
    group
  rw [h2] at h1
  exact h1.symm

theorem IsIntrinsicIn.descend {H L T : Subgroup X} {u : X} {n : ℕ} (h : IsIntrinsicIn X H L u)
    (hn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) (hT : IsPGroup 2 ↥T)
    (hTc : T ≤ centralizerSection L (pPrimeCoreOf 2 L)) (huT : u ∈ centralizer (T : Set X)) :
    IsIntrinsicIn X (H ⊓ centralizer (T : Set X)) (oTwoPrimeOf (L ⊓ centralizer (T : Set X))) u ∧
      IsDoubleCoverOfAlt
        (↥(oTwoPrimeOf (L ⊓ centralizer (T : Set X))) ⧸
          pPrimeCore 2 ↥(oTwoPrimeOf (L ⊓ centralizer (T : Set X)))) n ∧
      L ≤ pPrimeCoreOf 2 L ⊔ oTwoPrimeOf (L ⊓ centralizer (T : Set X)) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLquasi : IsTwoGenQuasi ↥L := h.isTwoGenQuasi
  have hLH : IsPCompIn 2 H L := h.2.2.1
  have hLL : L ≤ H := hLH.1
  have hu2 : u ^ 2 = 1 := by rw [← h.1]; exact pow_orderOf_eq_one u
  have hLeq : L = pPrimeCoreOf 2 L ⊔ oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) := by
    have := h.2.2.2.1
    rwa [oPrimeResidualOf_two_eq_oTwoPrimeOf] at this
  obtain ⟨Lu, hLu, hLueq'⟩ := h.2.2.2.2
  have hLueq : Lu = pPrimeCoreOf 2 Lu ⊔ oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) := by
    rwa [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLueq'
  set Eu : Subgroup X := oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) with hEu
  set ET : Subgroup X := oTwoPrimeOf (L ⊓ centralizer (T : Set X)) with hET
  set F0 : Subgroup X := oTwoPrimeOf (Eu ⊓ centralizer (T : Set X)) with hF0
  have hEuL : Eu ≤ L ⊓ centralizer ({u} : Set X) := oTwoPrimeOf_le _
  have hEuL' : Eu ≤ L := hEuL.trans inf_le_left
  have hEuC : Eu ≤ centralizer ({u} : Set X) := hEuL.trans inf_le_right
  have hETL : ET ≤ L ⊓ centralizer (T : Set X) := oTwoPrimeOf_le _
  have hETL' : ET ≤ L := hETL.trans inf_le_left
  have hETC : ET ≤ centralizer (T : Set X) := hETL.trans inf_le_right
  have hF0E : F0 ≤ Eu ⊓ centralizer (T : Set X) := oTwoPrimeOf_le _
  have hF0Eu : F0 ≤ Eu := hF0E.trans inf_le_left
  have hF0ET : F0 ≤ ET := oTwoPrimeOf_mono (inf_le_inf_right _ hEuL')
  have hTc' : ∀ t ∈ T, t ∈ normalizer (L : Set X) ∧ t ∈ normalizer (pPrimeCoreOf 2 L : Set X) ∧
      ∀ l ∈ L, ⁅l, t⁆ ∈ pPrimeCoreOf 2 L := fun t ht => hTc ht
  have hut : ∀ t ∈ T, t * u = u * t := fun t ht => (Subgroup.mem_centralizer_iff.1 huT) t ht
  have hTEu : T ≤ normalizer (Eu : Set X) := by
    refine oTwoPrimeOf_normalizes (A := T) (H := L ⊓ centralizer ({u} : Set X)) ?_
    intro t ht
    exact mem_normalizer_inf (hTc' t ht).1 (aux_mem_normalizer_centralizer_singleton (hut t ht))
  have hEuQ : primeResidual 2 ↥Eu = ⊤ := primeResidual_oTwoPrimeOf _
  have hEuO : T ≤ normalizer (pPrimeCoreOf 2 Eu : Set X) :=
    hTEu.trans (normalizer_le_normalizer_pPrimeCoreOf Eu)
  have hEucomm : ∀ k ∈ Eu, ∀ t ∈ T, ⁅k, t⁆ ∈ pPrimeCoreOf 2 Eu := by
    intro k hk t ht
    have h1 : ⁅k, t⁆ ∈ Eu := by
      have h2 : t * k⁻¹ * t⁻¹ ∈ Eu := by
        have := (Subgroup.mem_normalizer_iff.1 (hTEu ht) k⁻¹).1 (Eu.inv_mem hk)
        exact this
      have h3 : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
      rw [h3]
      exact Eu.mul_mem hk h2
    have h4 : ⁅k, t⁆ ∈ pPrimeCoreOf 2 L := (hTc' t ht).2.2 k (hEuL' hk)
    exact inf_pPrimeCoreOf_le_pPrimeCoreOf hEuL' ⟨h1, h4⟩
  have hcov0 : F0.subgroupOf Eu ⊔ pPrimeCore 2 ↥Eu = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers_pgroup hT hEuQ hEuO hEucomm
  have hcovEu : F0 ⊔ pPrimeCoreOf 2 Eu = Eu := (covers_subgroupOf_iff hF0Eu).1 hcov0
  have hcovL : Eu ⊔ pPrimeCoreOf 2 L = L := by
    rw [sup_comm]; exact hLeq.symm
  have hOEuL : pPrimeCoreOf 2 Eu ≤ pPrimeCoreOf 2 L :=
    (pPrimeCoreOf_eq_inf_of_covers hEuL' hcovL).le.trans inf_le_right
  have hL0 : L ≤ pPrimeCoreOf 2 L ⊔ F0 := by
    calc L = pPrimeCoreOf 2 L ⊔ Eu := hLeq
      _ ≤ pPrimeCoreOf 2 L ⊔ (F0 ⊔ pPrimeCoreOf 2 Eu) := sup_le_sup_left hcovEu.ge _
      _ ≤ pPrimeCoreOf 2 L ⊔ F0 :=
        sup_le le_sup_left (sup_le le_sup_right (hOEuL.trans le_sup_left))
  have hL1 : L ≤ pPrimeCoreOf 2 L ⊔ ET := hL0.trans (sup_le_sup_left hF0ET _)
  have hcovLET : ET ⊔ pPrimeCoreOf 2 L = L :=
    le_antisymm (sup_le hETL' (oddCoreOf_le L)) (by rw [sup_comm]; exact hL1)
  have hcovLET' : ET.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    (covers_subgroupOf_iff hETL').2 hcovLET
  have hETquasi : IsTwoGenQuasi ↥ET :=
    isTwoGenQuasi_of_covers hETL' hcovLET' (primeResidual_oTwoPrimeOf _) hLquasi
  have hETn : IsDoubleCoverOfAlt (↥ET ⧸ pPrimeCore 2 ↥ET) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hETL' hcovLET' n).2 hn
  set S : Subgroup X := H ⊓ centralizer (T : Set X) with hS
  have hSH : S ≤ H := inf_le_left
  have hETS : ET ≤ S := le_inf (hETL'.trans hLL) hETC
  have hLsub : (L.subgroupOf H).IsSubnormal := (isPComponent_two_iff.1 hLH.2).1
  have hLS : (L.subgroupOf S).IsSubnormal := by
    have := hLsub.comap (Subgroup.inclusion hSH)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hAeq : L ⊓ centralizer (T : Set X) = L ⊓ S := by
    ext x
    simp only [Subgroup.mem_inf, hS]
    constructor
    · rintro ⟨hxL, hxC⟩
      exact ⟨hxL, hLL hxL, hxC⟩
    · rintro ⟨hxL, -, hxC⟩
      exact ⟨hxL, hxC⟩
  have hLSA : ((L ⊓ centralizer (T : Set X)).subgroupOf S).IsSubnormal := by
    rw [hAeq, Subgroup.inf_subgroupOf_right]; exact hLS
  have hETsub : (ET.subgroupOf S).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_of_subnormal (A := L ⊓ centralizer (T : Set X)) (H := S)
      (B := ET) (by rw [hAeq]; exact inf_le_right) hETL hLSA (normal_subgroupOf_oTwoPrimeOf _)
  have hETpc : IsPCompIn 2 S ET :=
    ⟨hETS, isPComponent_two_iff.2 ⟨hETsub, (isTwoGenQuasi_subgroupOf_iff hETS).2 hETquasi⟩⟩
  have hETu : u ∈ ET := mem_oTwoPrimeOf (Subgroup.mem_inf.2 ⟨h.2.1, huT⟩) 1 (by simpa using hu2)
  set E' : Subgroup X := oTwoPrimeOf (ET ⊓ centralizer ({u} : Set X)) with hE'
  have hF0self : oTwoPrimeOf F0 = F0 :=
    oTwoPrimeOf_eq_self_of_primeResidual (primeResidual_oTwoPrimeOf _)
  have hF0E' : F0 ≤ E' := by
    have : F0 ≤ ET ⊓ centralizer ({u} : Set X) := le_inf hF0ET (hF0Eu.trans hEuC)
    calc F0 = oTwoPrimeOf F0 := hF0self.symm
      _ ≤ oTwoPrimeOf (ET ⊓ centralizer ({u} : Set X)) := oTwoPrimeOf_mono this
  have hE'Eu : E' ≤ Eu := oTwoPrimeOf_mono (inf_le_inf_right _ hETL')
  have hE'ET : E' ≤ ET := (oTwoPrimeOf_le _).trans inf_le_left
  have hET0 : ET ≤ pPrimeCoreOf 2 ET ⊔ F0 := by
    have hF0n : F0 ≤ normalizer (pPrimeCoreOf 2 L : Set X) := fun x hx =>
      le_normalizer_oddCoreOf L (hF0Eu.trans hEuL' hx)
    calc ET ≤ (ET ⊓ pPrimeCoreOf 2 L) ⊔ F0 := aux_dedekind hF0ET hF0n (hETL'.trans hL0)
      _ ≤ pPrimeCoreOf 2 ET ⊔ F0 :=
        sup_le_sup_right (inf_pPrimeCoreOf_le_pPrimeCoreOf hETL') _
  have hETeq : ET = pPrimeCoreOf 2 ET ⊔ E' :=
    le_antisymm (hET0.trans (sup_le_sup_left hF0E' _)) (sup_le (oddCoreOf_le ET) hE'ET)
  have hEuLu : Eu ≤ Lu := le_sup_right.trans hLueq.ge
  have hcovLu : Eu ⊔ pPrimeCoreOf 2 Lu = Lu := by
    rw [sup_comm]; exact hLueq.symm
  have hOEuLu : pPrimeCoreOf 2 Eu ≤ pPrimeCoreOf 2 Lu :=
    (pPrimeCoreOf_eq_inf_of_covers hEuLu hcovLu).le.trans inf_le_right
  have hLu1 : Lu = pPrimeCoreOf 2 Lu ⊔ E' := by
    refine le_antisymm ?_ (sup_le (oddCoreOf_le Lu) (hE'Eu.trans hEuLu))
    calc Lu = pPrimeCoreOf 2 Lu ⊔ Eu := hLueq
      _ ≤ pPrimeCoreOf 2 Lu ⊔ (F0 ⊔ pPrimeCoreOf 2 Eu) := sup_le_sup_left hcovEu.ge _
      _ ≤ pPrimeCoreOf 2 Lu ⊔ E' :=
        sup_le le_sup_left (sup_le (hF0E'.trans le_sup_right) (hOEuLu.trans le_sup_left))
  refine ⟨⟨h.1, hETu, hETpc, ?_, Lu, hLu, ?_⟩, hETn, hL1⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]; exact hETeq
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]; exact hLu1

omit [Finite X] in
theorem aux_isPGroup_zpowers_of_sq {s : X} (hs : s ^ 2 = 1) : IsPGroup 2 ↥(Subgroup.zpowers s) := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (by simpa using orderOf_dvd_of_pow_eq_one hs : orderOf s ∣ 2 ^ 1)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

omit [Finite X] in
theorem aux_centralizer_zpowers {s : X} :
    centralizer ((Subgroup.zpowers s : Subgroup X) : Set X) = centralizer ({s} : Set X) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact h s (Subgroup.mem_zpowers s)
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hs : s * x = x * s := h s rfl
    exact ((Commute.zpow_left (show Commute s x from hs) k).eq)

theorem IsIntrinsicIn.descend_singleton {H L : Subgroup X} {u s : X} {n : ℕ}
    (h : IsIntrinsicIn X H L u) (hn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n)
    (hs : s ^ 2 = 1) (hsc : s ∈ centralizerSection L (pPrimeCoreOf 2 L))
    (hus : u ∈ centralizer ({s} : Set X)) :
    IsIntrinsicIn X (H ⊓ centralizer ({s} : Set X))
        (oTwoPrimeOf (L ⊓ centralizer ({s} : Set X))) u ∧
      IsDoubleCoverOfAlt
        (↥(oTwoPrimeOf (L ⊓ centralizer ({s} : Set X))) ⧸
          pPrimeCore 2 ↥(oTwoPrimeOf (L ⊓ centralizer ({s} : Set X)))) n ∧
      L ≤ pPrimeCoreOf 2 L ⊔ oTwoPrimeOf (L ⊓ centralizer ({s} : Set X)) := by
  have hT : IsPGroup 2 ↥(Subgroup.zpowers s) := aux_isPGroup_zpowers_of_sq hs
  have hTc : Subgroup.zpowers s ≤ centralizerSection L (pPrimeCoreOf 2 L) :=
    (Subgroup.zpowers_le).2 hsc
  have := h.descend hn hT hTc (by rw [aux_centralizer_zpowers]; exact hus)
  rwa [aux_centralizer_zpowers] at this

theorem IsIntrinsicIn.exists_witness_centralizer_singleton {H L : Subgroup X} {u s : X}
    (h : IsIntrinsicIn X H L u) (hs : s ^ 2 = 1)
    (hsc : s ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    ∃ u' : X, IsIntrinsicIn X H L u' ∧ u' ∈ centralizer ({s} : Set X) := by
  have hT : IsPGroup 2 ↥(Subgroup.zpowers s) := aux_isPGroup_zpowers_of_sq hs
  have hTc : Subgroup.zpowers s ≤ centralizerSection L (pPrimeCoreOf 2 L) :=
    (Subgroup.zpowers_le).2 hsc
  obtain ⟨u', hu', hu'c⟩ := h.exists_witness_centralizer hT hTc
  exact ⟨u', hu', by rwa [aux_centralizer_zpowers] at hu'c⟩

end CFSG.OddStandard.Solomon75
