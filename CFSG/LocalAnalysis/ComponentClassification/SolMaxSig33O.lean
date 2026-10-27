module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33N
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33M

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem commutator_le_left_of_le_normalizer {M D : Subgroup X}
    (hD : D ≤ normalizer (M : Set X)) : ⁅M, D⁆ ≤ M := by
  rw [commutator_le]
  intro m hm d hd
  have h1 : d * m⁻¹ * d⁻¹ ∈ M := (mem_normalizer_iff.mp (hD hd) _).mp (inv_mem hm)
  rw [commutatorElement_def]
  have h2 := mul_mem hm h1
  simpa [mul_assoc] using h2

theorem commutator_le_right_of_le_normalizer {A N : Subgroup X}
    (hA : A ≤ normalizer (N : Set X)) : ⁅A, N⁆ ≤ N := by
  rw [commutator_comm]
  exact commutator_le_left_of_le_normalizer hA

namespace Sol33

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem exists_acts_like_E {b : X} (hb : b ∈ E ⊔ zpowers y) :
    ∃ e ∈ E, b * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J := by
  obtain ⟨e, he, hbe | hbe⟩ := S.mem_cases hb
  · refine ⟨e, he, ?_⟩
    rw [hbe, mul_inv_cancel]
    exact one_mem _
  · refine ⟨e, he, ?_⟩
    have h1 : b * e⁻¹ = y := by
      rw [hbe]
      calc e * y * e⁻¹ = (y * e) * e⁻¹ := by rw [S.y_comm he]
        _ = y := by group
    rw [h1]
    exact S.hyK

theorem coreImage_comm {e₁ e₂ : X} (h₁ : e₁ ∈ E) (h₂ : e₂ ∈ E) :
    coreImage θ (S.le h₁) * coreImage θ (S.le h₂) =
      coreImage θ (S.le h₂) * coreImage θ (S.le h₁) := by
  unfold coreImage
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 3
  exact Subtype.ext (S.comm_E h₁ h₂)

theorem exists_fixedLayer_unbalanced (hbal : Sol78.BalanceTwoComponentInput)
    (hPO : S.PumpOracle) {a b : X} (ha : a ∈ E ⊔ zpowers y) (ha1 : a ≠ 1)
    (hb : b ∈ E ⊔ zpowers y) (hb1 : b ≠ 1)
    {L : Subgroup X} (hLC : L ≤ centralizer ({b} : Set X))
    (hLpc : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))))
    (hLX : ¬ ⁅L, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({b} : Set X)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype)
    {f : X} (hfJ : f ∈ J) (hfB : f ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X))
    (hfo : orderOf f = 2) (hfD : Disjoint (coreImage θ hfJ).support D) :
    ∃ Lf : Subgroup X, Lf ≤ L ∧
      Lf ≤ centralizer ({b} : Set X) ⊓ centralizer ({f} : Set X) ∧
      IsPComponent 2 (Lf.subgroupOf (centralizer ({b} : Set X) ⊓ centralizer ({f} : Set X))) ∧
      Lf ⊔ (pPrimeCore 2 ↥L).map L.subtype = L ∧
      (pPrimeCore 2 ↥Lf).map Lf.subtype ≤ (pPrimeCore 2 ↥L).map L.subtype ∧
      ¬ ⁅Lf, ((pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype ⊓ centralizer ({b} : Set X)) ⊓
          centralizer ({f} : Set X)⁆ ≤
        (pPrimeCore 2 ↥(centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cb : Subgroup X := centralizer ({b} : Set X) with hCbdef
  set Cf : Subgroup X := centralizer ({f} : Set X) with hCfdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Ob := (pPrimeCore 2 ↥Cb).map Cb.subtype with hObdef
  set Of := (pPrimeCore 2 ↥Cf).map Cf.subtype with hOfdef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have hb2 := S.mul_self_of_mem hb
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hbB : b ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X) := by
    rw [mem_centralizer_iff]
    intro z hz
    exact S.comm_of_mem hz hb
  have htb := S.t_comm hb
  have hf2 : f * f = 1 := by rw [← sq, ← hfo, pow_orderOf_eq_one]
  have hfb : f * b = b * f := (mem_centralizer_iff.mp hfB b hb).symm
  have hfa : f * a = a * f := (mem_centralizer_iff.mp hfB a ha).symm
  obtain ⟨e₁, he₁, hce₁⟩ := S.exists_acts_like_E hb
  have hs4 : (coreImage θ (S.le he₁)).support.card ≤ 4 :=
    (Finset.card_le_card (S.supp e₁ (S.le he₁) he₁)).trans S.card.le
  have hdich : (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ (S.le he₁)).support) ∨
      (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ (S.le he₁)).supportᶜ) := by
    by_cases he1 : e₁ = 1
    · right
      intro e he
      have h1 : coreImage θ (S.le he₁) = 1 := by
        unfold coreImage
        have h2 : (⟨e₁, S.le he₁⟩ : ↥J) = 1 := Subtype.ext he1
        rw [h2, QuotientGroup.mk_one, map_one]
        rfl
      rw [h1, Perm.support_one, Finset.compl_empty]
      exact Finset.subset_univ _
    · left
      intro e he
      rw [S.support_eq he₁ he1]
      exact S.supp e (S.le he) he
  obtain ⟨Jb, Mb, -, hinvb, hMbC, hMbpc, hJbM, -, -, hbalb⟩ :=
    hPO hbB htb (S.mem_normalizer hb) hbo (S.le he₁) (S.mul_self_of_mem_E he₁) hce₁ hs4
      (fun e he => S.coreImage_comm he he₁) hdich
  obtain ⟨hbalM, hbalMt⟩ := hbalb a ha ha1
  have htCb : t ∈ Cb := mem_centralizer_singleton_iff.mpr htb
  obtain ⟨hMbtC, hMbtpc⟩ := isPComponent_conj hMbC hMbpc htCb
  have hne1 : L ≠ Mb := fun h => hLX (h ▸ hbalM)
  have hne2 : L ≠ Mb.map (MulAut.conj t).toMonoidHom := fun h => hLX (h ▸ hbalMt)
  have hfs : (coreImage θ hfJ).support ⊆ (coreImage θ (S.le he₁)).supportᶜ := by
    intro z hz
    rw [Finset.mem_compl]
    intro hz'
    exact Finset.disjoint_left.mp hfD hz (S.supp e₁ (S.le he₁) he₁ hz')
  have hfJb : f ∈ Jb := hinvb f hfJ hfb ⟨1, by rw [pow_one, sq]; exact hf2⟩ hfs
  have hfK : f ∈ UnbalancedLayer.coreActionKernel L :=
    (sup_le (GSThmB.B5a.le_coreActionKernel_of_ne hLC hMbC hLpc hMbpc hne1)
      (GSThmB.B5a.le_coreActionKernel_of_ne hLC hMbtC hLpc hMbtpc hne2)) (hJbM hfJb)
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers b ≠ ⊥ := fun h => hb1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact S.comm_of_mem ha hb
  obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers b) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact S.mul_self_of_mem ha))
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hb2)) hST
  have hCb' : centralizer ((zpowers b : Subgroup X) : Set X) = Cb := centralizer_zpowers_eq' b
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = Ca := centralizer_zpowers_eq' a
  rw [hCb', hCa'] at hbc
  obtain ⟨hXN, -⟩ := hbc L ⟨hLC, hLpc⟩
  have hXNL : Oa ⊓ Cb ≤ normalizer (L : Set X) :=
    le_normalizer_of_le_normalizer_sup hLC hLpc inf_le_right hXN
  have hCbN : Cb ≤ normalizer (Ob : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Cb)
  have hXf : ⁅Oa ⊓ Cb, zpowers f⁆ ≤ Ob := by
    have h1 : ⁅Oa ⊓ Cb, Mb ⊔ Mb.map (MulAut.conj t).toMonoidHom⁆ ≤ Ob :=
      commutator_sup_le hCbN hMbC hMbtC (by rw [commutator_comm]; exact hbalM)
        (by rw [commutator_comm]; exact hbalMt)
    exact (commutator_mono le_rfl (zpowers_le.mpr (hJbM hfJb))).trans h1
  have hLsub : (L.subgroupOf Cb).IsSubnormal := hLpc.choose_spec.2.1
  have hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Cb hLC).mp hLpc).2.2
  have hfCb : zpowers f ≤ Cb := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hfb)
  have hfKz : zpowers f ≤ UnbalancedLayer.coreActionKernel L := zpowers_le.mpr hfK
  have hf2' : IsPGroup 2 (zpowers f) := isPGroup_zpowers_of_mul_self hf2
  have hCfz : centralizer ((zpowers f : Subgroup X) : Set X) = Cf := centralizer_zpowers_eq' f
  have hLfpc := GSLit.fixedLayer_isPComponent hLC hLsub hfCb hfKz hf2' hLq
  rw [hCfz] at hLfpc
  obtain ⟨hLfsup, hLfcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hLq hfKz hf2'
  have hLfle := GSLit.fixedLayer_le_inf L (zpowers f)
  rw [hCfz] at hLfle
  set Lf := GSLit.fixedLayer L (zpowers f) with hLfdef
  have hLfL : Lf ≤ L := hLfle.trans inf_le_left
  have hLfC : Lf ≤ Cb ⊓ Cf := le_inf (hLfL.trans hLC) (hLfle.trans inf_le_right)
  have hcoreL : (pPrimeCore 2 ↥Lf).map Lf.subtype ≤ (pPrimeCore 2 ↥L).map L.subtype := by
    rw [hLfcore]
    exact inf_le_right
  have hOLb : (pPrimeCore 2 ↥L).map L.subtype ≤ Ob := pPrimeCore_le_of_isPComponent hLC hLpc
  have hfCa : f ∈ Ca := mem_centralizer_singleton_iff.mpr hfa
  have hCaN : Ca ≤ normalizer (Oa : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Ca)
  have hfNX : zpowers f ≤ normalizer ((Oa ⊓ Cb : Subgroup X) : Set X) :=
    zpowers_le.mpr (inf_mem_normalizer' (hCaN hfCa) (le_normalizer (hfCb (mem_zpowers f))))
  have hX₀odd : Odd (Nat.card ↥(Oa ⊓ Cb)) := by
    have h1 : Odd (Nat.card Oa) := by
      rw [hOadef, card_map_of_injective Ca.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hdec := GrSLit.le_commutator_sup_inf_centralizer_of_odd hf2' hfNX hX₀odd
  rw [hCfz] at hdec
  have hLXf : ¬ ⁅L, (Oa ⊓ Cb) ⊓ Cf⁆ ≤ Ob := by
    intro h
    apply hLX
    refine (commutator_mono le_rfl hdec).trans ?_
    refine commutator_sup_le hCbN (hXf.trans (map_subtype_le _))
      (inf_le_left.trans inf_le_right) ?_ h
    exact (commutator_mono le_rfl hXf).trans
      (commutator_le_right_of_le_normalizer (hLC.trans hCbN))
  have hLfXf : ¬ ⁅Lf, (Oa ⊓ Cb) ⊓ Cf⁆ ≤ Ob := by
    intro h
    apply hLXf
    rw [← hLfsup, commutator_comm]
    refine commutator_sup_le hCbN (hLfL.trans hLC) (hOLb.trans (map_subtype_le _)) ?_ ?_
    · rw [commutator_comm]
      exact h
    · exact (commutator_mono le_rfl hOLb).trans
        (commutator_le_right_of_le_normalizer ((inf_le_left.trans inf_le_right).trans hCbN))
  refine ⟨Lf, hLfL, hLfC, hLfpc, hLfsup, hcoreL, fun h => hLfXf ?_⟩
  have hXfN : (Oa ⊓ Cb) ⊓ Cf ≤ normalizer (Lf : Set X) := by
    intro x hx
    have hxf : x * f = f * x := mem_centralizer_singleton_iff.mp hx.2
    exact mem_normalizer_fixedLayer hLq hfKz hf2' (hXNL hx.1) hxf
  have h1 : ⁅Lf, (Oa ⊓ Cb) ⊓ Cf⁆ ≤ Lf ⊓ Of :=
    le_inf (commutator_le_left_of_le_normalizer hXfN) h
  exact h1.trans ((inf_pPrimeCore_le (hLfC.trans inf_le_right)).trans (hcoreL.trans hOLb))

end Sol33

end CFSG.ComponentClassification.SolMax
