module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.CaseB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Repeat

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.M12Std

section Standard

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.EvenSporadicStandard.Induction.StdBare.map_conj_eq_of_isCompIn
    {X I : Subgroup G} (hstd : StdBare I) (hI : IsCompIn I X) {g : G}
    (hg : g ∈ normalizer (X : Set G)) : I.map (MulAut.conj g).toMonoidHom = I := by
  by_contra hne
  have hcomm := IsCompIn.commute_of_ne hI (isCompIn_map_conj_of_mem_normalizer hI hg)
    (Ne.symm hne)
  refine hstd.1 g (Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha => ?_)
  exact mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm

end Standard

section Coincidence

variable {G : Type} [Group G] [Finite G] {n m : ℕ} {U T V TV Tl : ℕ → Subgroup G}
  {s sV sl : ℕ → G} {u x : G} {M : Subgroup G}

theorem TopData.exists_coincidence (hD : TopData G n U T s u x)
    (hlink : TLinks G 1 (seq2 (U (n - 2)) M) Tl sl) (hV : InCG G m V TV sV) (hV0 : V 0 = M)
    (hm : 2 ≤ m) : ∃ l ≤ n - 2, ∃ j < m, U l = V j := by
  by_contra hcon
  have hdisj : ∀ i ≤ n - 2, ∀ j ≤ m, U i ≠ V j := by
    intro i hi j hj heq
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact hcon ⟨i, hi, j, hjm, heq⟩
    · obtain rfl : j = m := le_antisymm hj hjm
      have h1 : U i = U n := heq.trans (hV.last.trans hD.chain.1.last.symm)
      have h2 := hD.chain.1.inj i (by omega) n le_rfl h1
      have h3 := hD.two_le
      omega
  obtain ⟨W, TW, sW, hW, hWi, -⟩ :=
    InCGb.exists_append_link hD.chain (a := n - 2) (by omega) hlink hV hV0 hdisj
  have h1 := hD.maximal _ W TW sW hW (hWi 0 (Nat.zero_le _))
  have h2 := hD.two_le
  omega

end Coincidence

section Certified

open _root_.Certificates


variable {G : Type} [Group G] [Finite G] {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G} {u x : G}

theorem TopData.false_caseC_of_not_fiveALink (hUG : Induction.Balance.UHered G)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hMcard : Nat.card MonsterY443Derived = monsterOrder)
    (hD : TopData G n U T s u x) (hNo : ∀ L' : Subgroup G, ¬ FiveALink (U (n - 2)) L')
    {I : Subgroup G} (hI : IsCompIn I (centralizer ((zpowers x : Subgroup G) : Set G)))
    (h5a : Sol78Link5a I (U (n - 2)) u)
    (hle : U (n - 2) ≤ I ⊔ I.map (MulAut.conj u).toMonoidHom)
    (hcl : I ⊔ I.map (MulAut.conj u).toMonoidHom =
      conjClosure (U (n - 2)) (layerIn (centralizer ((zpowers x : Subgroup G) : Set G)))) :
    False := by
  have hOu := hD.out
  have hxt : x ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hOu.mem x hD.xmem)
  have hzx : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hux' : u ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hxt).symm
  have hux : u ∈ normalizer ((zpowers x : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by rw [hzx]; exact hux')
  have hu2 : u ^ 2 ∈ zpowers x := by
    rw [sq_eq_one_of_orderOf_eq_two hOu.inv]
    exact one_mem _
  have hKc : IsCompIn (U (n - 2))
      (centralizer ((zpowers x ⊔ zpowers u : Subgroup G) : Set G)) := by
    rw [sup_comm, hD.jstar]
    exact isCompIn_jOf hD.facts hxt hD.xinv
  have hx2 : IsPGroup 2 ↥(zpowers x) := isPGroup_zpowers_of_orderOf_eq_two hD.xinv
  have hx1 : zpowers x ≠ ⊥ := by
    intro h
    have h1 := Subgroup.zpowers_eq_bot.1 h
    have h2 := hD.xinv
    rw [h1, orderOf_one] at h2
    omega
  have hlink : TLinks G 1 (seq2 (U (n - 2)) I) (seq2 (zpowers x ⊔ zpowers u) (zpowers x))
      (seq2 1 u) :=
    tLinks_single hx2 hux hu2 hKc hI (Or.inr h5a) hle hcl
  obtain ⟨m, V, TV, sV, hV, hV0⟩ := exists_inCG_of_isCompIn hUG hCIT hMcard hOu hx2 hx1 hI
  have hm : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by
      have := hV.one_le
      omega
    subst hm1
    have hstd : StdBare I := by simpa [hV0] using hV.top
    have hu : u ∈ normalizer
        ((centralizer ((zpowers x : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (by rw [hzx]; exact hux')
    exact h5a.1 (hstd.map_conj_eq_of_isCompIn hI hu).symm
  have hcol := hD.exists_coincidence hlink hV hV0 hm
  have hJX : U (n - 2) ≤ U (n - 1) := by
    rw [hD.jstar]
    exact (jOf_le_inf _ x).trans inf_le_left
  have hJu : (U (n - 2)).map (MulAut.conj u).toMonoidHom = U (n - 2) :=
    Solomon78.mem_normalizer_iff_map_conj_eq.1 (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hJX) hOu.mem))
  have hcq : cqOrd (V 0) = cqOrd (U (n - 2)) := by
    rw [hV0]
    obtain ⟨e⟩ := h5a.2
    exact Nat.card_congr e.toEquiv
  have hne : V 0 ≠ U (n - 2) := by
    rw [hV0]
    intro hIJ
    exact h5a.1 (by rw [hIJ]; exact hJu.symm)
  obtain ⟨J, hJ⟩ := InCG.exists_fiveALink_of_collision hOu.std.simple hOu.std.nonabelian
    hD.chain.1 hV hcq hne hcol
  exact hNo J hJ

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
