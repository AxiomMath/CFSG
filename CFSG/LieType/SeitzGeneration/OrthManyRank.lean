module

public import CFSG.LieType.SeitzGeneration.OrthFamily
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
public import CFSG.RankThree.PartOne.CTP.SpGeom

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

theorem manyRank_one_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V] (v : V) :
    (1 : V ≃ₗ[K] V) v = v :=
  rfl

theorem manyRank_natCast_ne_zero {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ringChar K) : (p : K) ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime hp).mp ((CharP.cast_eq_zero_iff K (ringChar K) p).mp h) with h1 | h1
  · exact CharP.char_ne_one K (ringChar K) h1
  · exact hpl h1.symm

theorem manyRank_card_natCast_ne_zero {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ringChar K) : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hq, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at h
  have hpq : p ∣ ringChar K := hp.dvd_of_dvd_pow h
  exact hpl ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq)

theorem manyRank_orderOf_pos {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ringChar K) : 0 < orderOf ((Nat.card K : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
  exact ⟨p - 1, by have := hp.one_lt; omega,
    ZMod.pow_card_sub_one_eq_one (manyRank_card_natCast_ne_zero hp hpl)⟩

section Sum

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem manyRank_finrank_three_le {S₁ S₂ S₃ : Submodule K V} (h₁ : PolarNondegOn Q S₁)
    (h₂ : PolarNondegOn Q S₂) (h₃ : PolarNondegOn Q S₃) (h12 : OrthSep Q S₁ S₂)
    (h13 : OrthSep Q S₁ S₃) (h23 : OrthSep Q S₂ S₃) :
    finrank K S₁ + finrank K S₂ + finrank K S₃ ≤ finrank K V := by
  have hd12 : S₁ ⊓ S₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    rw [Submodule.mem_bot]
    exact h₂ x hx2 (fun y hy => h12 x hx1 y hy)
  have hd : (S₁ ⊔ S₂) ⊓ S₃ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx12, hx3⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, hy1, z, hz2, rfl⟩ := Submodule.mem_sup.mp hx12
    have hy : y = 0 := by
      refine h₁ y hy1 (fun u hu => ?_)
      have h0 := h13.symm _ hx3 u hu
      rw [QuadraticMap.polar_add_left, h12.symm z hz2 u hu, add_zero] at h0
      exact h0
    have hz : z = 0 := by
      refine h₂ z hz2 (fun v hv => ?_)
      have h0 := h23.symm _ hx3 v hv
      rw [QuadraticMap.polar_add_left, h12 y hy1 v hv, zero_add] at h0
      exact h0
    rw [Submodule.mem_bot, hy, hz, add_zero]
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq S₁ S₂
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (S₁ ⊔ S₂) S₃
  rw [hd12, finrank_bot] at e1
  rw [hd, finrank_bot] at e2
  have e3 := Submodule.finrank_le (S₁ ⊔ S₂ ⊔ S₃)
  omega

end Sum

section NoSingularStruct

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem natDegree_eq_orderOf {x : V ≃ₗ[K] V} (hp : p.Prime) (hxp : x ^ p = 1)
    {h : Polynomial K} (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap)
    (hne : h ≠ Polynomial.X - 1) : h.natDegree = orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  have hirr : Irreducible h :=
    CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := CFSG.RankThree.PartOne.KCPrimary.monic_of_mem_primaryFactors hh
  have hμ : h ∣ minpoly K x.toLinearMap :=
    (CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hh).2.2
  have hxp' : x.toLinearMap ^ p = 1 := by
    apply LinearMap.ext
    intro v
    have h1 := congrArg (fun e : V ≃ₗ[K] V => e v) hxp
    simp only [LinearEquiv.coe_pow, manyRank_one_apply] at h1
    rw [Module.End.pow_apply, Module.End.one_apply]
    exact h1
  have hdvdX : h ∣ Polynomial.X ^ p - 1 :=
    hμ.trans (minpoly.dvd K _ (by simp [hxp']))
  have hne' : h ≠ Polynomial.X - Polynomial.C 1 := by rwa [Polynomial.C_1]
  by_cases hpl : p = ringChar K
  ·
    exfalso
    subst hpl
    haveI : Fact (ringChar K).Prime := ⟨hp⟩
    have hX : (Polynomial.X - 1 : Polynomial K) ^ ringChar K = Polynomial.X ^ ringChar K - 1 := by
      rw [sub_pow_char, one_pow]
    have h1 : h ∣ (Polynomial.X - 1 : Polynomial K) :=
      hirr.prime.dvd_of_dvd_pow (n := ringChar K) (by rw [hX]; exact hdvdX)
    have hX1 : Irreducible (Polynomial.X - 1 : Polynomial K) := by
      apply Polynomial.irreducible_of_degree_eq_one
      rw [← Polynomial.C_1]
      exact Polynomial.degree_X_sub_C 1
    have hass := hirr.associated_of_dvd hX1 h1
    have heq := Polynomial.eq_of_monic_of_associated hmon (Polynomial.monic_X_sub_C 1) hass
    rw [Polynomial.C_1] at heq
    exact hne heq
  · have hpos := manyRank_orderOf_pos hp hpl
    have hdvd : h.natDegree ∣ orderOf ((Nat.card K : ℕ) : ZMod p) := by
      rw [hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X]
      refine AdjoinRoot.mk_eq_zero.mp ?_
      have hα : AdjoinRoot.root h ^ p = 1 := by
        have h0 := AdjoinRoot.mk_eq_zero.mpr hdvdX
        rw [← AdjoinRoot.aeval_eq] at h0
        simpa [sub_eq_zero] using h0
      have hqd : ((Nat.card K ^ orderOf ((Nat.card K : ℕ) : ZMod p) : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_pow]
        exact pow_orderOf_eq_one _
      have hmod : Nat.card K ^ orderOf ((Nat.card K : ℕ) : ZMod p) % p = 1 := by
        have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (hqd.trans (Nat.cast_one).symm)
        rwa [Nat.mod_eq_of_lt hp.one_lt] at h2
      have hαN : AdjoinRoot.root h ^ (Nat.card K ^ orderOf ((Nat.card K : ℕ) : ZMod p)) =
          AdjoinRoot.root h := by
        rw [pow_eq_pow_mod _ hα, hmod, pow_one]
      rw [← AdjoinRoot.aeval_eq]
      simp [hαN]
    have hle1 : h.natDegree ≤ orderOf ((Nat.card K : ℕ) : ZMod p) := Nat.le_of_dvd hpos hdvd
    have hle2 : orderOf ((Nat.card K : ℕ) : ZMod p) ≤ h.natDegree :=
      CFSG.RankThree.PartOne.KCLinComm.orderOf_le_natDegree_of_mem_primaryFactors hp hxp' hh hne'
    exact le_antisymm hle1 hle2

theorem OrthBlk.IsBlock.orderOf_le_finrank {S : Submodule K V} {g : V ≃ₗ[K] V} (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hS : PolarNondegOn Q S) (hg : IsBlock Q p S g) :
    orderOf ((Nat.card K : ℕ) : ZMod p) ≤ finrank K S := by
  classical
  have hpK := manyRank_natCast_ne_zero hp hpl
  have hc : IsCompl S (perp Q S) := isCompl_perp hS
  obtain ⟨π, hπ⟩ : ∃ π : V →ₗ[K] S, π = S.projectionOnto (perp Q S) hc := ⟨_, rfl⟩
  have hπS : ∀ s : S, π (s : V) = s := fun s => by
    rw [hπ, Submodule.projectionOnto_apply_left]
  have hπT : ∀ t ∈ perp Q S, π t = 0 := fun t ht => by
    rw [hπ]
    exact Submodule.projectionOnto_apply_right hc ⟨t, ht⟩
  have hsub : ∀ v : V, v - (π v : V) ∈ perp Q S := fun v => by
    rw [hπ, Submodule.coe_projectionOnto_apply]
    exact Submodule.sub_projection_mem hc v
  have hgT : ∀ t ∈ perp Q S, g t = t := fun t ht => hg.fix t (mem_perp.mp ht)
  obtain ⟨A, hA⟩ : ∃ A : Module.End K S, ∀ x : S, A x = π (g (x : V)) :=
    ⟨π.comp ((g : V →ₗ[K] V).comp S.subtype), fun x => rfl⟩
  have hkey1 : ∀ v : V, π (g v) = A (π v) := by
    intro v
    have hT : g (v - (π v : V)) = v - (π v : V) := hgT _ (hsub v)
    have hsplit : g v = g (π v : V) + (v - (π v : V)) := by
      have h0 : g v = g ((π v : V) + (v - (π v : V))) := by congr 1; abel
      rw [h0, map_add, hT]
    rw [hA, hsplit, map_add, hπT _ (hsub v), add_zero]
  have hkeyn : ∀ (n : ℕ) (v : V), π ((g ^ n) v) = (A ^ n) (π v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih (g v), hkey1 v, pow_succ, Module.End.mul_apply]
  have hAp : A ^ p = 1 := by
    apply LinearMap.ext
    intro x
    have h3 := hkeyn p (x : V)
    rw [hg.pow, manyRank_one_apply, hπS x] at h3
    rw [Module.End.one_apply]
    exact h3.symm
  have hAne : A ≠ 1 := by
    intro hA1
    apply hg.ne
    apply LinearEquiv.ext
    intro v
    have hπ0 : π (g v) = π v := by rw [hkey1 v, hA1, Module.End.one_apply]
    have hd : g v - v ∈ perp Q S := by
      have h1 : π (g v - v) = 0 := by rw [map_sub, hπ0, sub_self]
      simpa [h1] using hsub (g v - v)
    have hpow : ∀ n : ℕ, (g ^ n) v = v + n • (g v - v) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hgT _ hd, succ_nsmul]
        abel
    have hp0 : p • (g v - v) = 0 := by
      have h := hpow p
      rw [hg.pow, manyRank_one_apply] at h
      simpa using h.symm
    rw [← Nat.cast_smul_eq_nsmul K] at hp0
    rcases smul_eq_zero.mp hp0 with h | h
    · exact absurd h hpK
    · rw [manyRank_one_apply]
      exact sub_eq_zero.mp h
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors A,
      h ≠ Polynomial.X - Polynomial.C 1 := by
    by_contra H
    push Not at H
    have hsub1 : CFSG.RankThree.PartOne.KCPrimary.primaryFactors A ⊆
        {Polynomial.X - Polynomial.C 1} :=
      fun h hh => Finset.mem_singleton.mpr (H h hh)
    have hsqX : Squarefree (Polynomial.X ^ p - 1 : Polynomial K) := by
      have := Polynomial.separable_X_pow_sub_C (n := p) (1 : K) hpK one_ne_zero
      rw [Polynomial.C_1] at this
      exact this.squarefree
    have hsqμ := CFSG.RankThree.PartOne.KCPrimary.squarefree_minpoly_of_aeval_eq_zero
      (x := A) hsqX (by simp [hAp])
    have hprod := CFSG.RankThree.PartOne.KCPrimary.prod_primaryFactors hsqμ
    have hdvd1 : minpoly K A ∣ Polynomial.X - Polynomial.C 1 := by
      rw [← hprod]
      rcases Finset.subset_singleton_iff.mp hsub1 with h0 | h1
      · rw [h0, Finset.prod_empty]
        exact one_dvd _
      · simp [h1]
    apply hAne
    have h2 := minpoly.dvd_iff.mp hdvd1
    simpa [sub_eq_zero] using h2
  have hdeg : h.natDegree ≤ finrank K S := by
    have h1 : h ∣ A.charpoly :=
      (CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hh).2.2.trans
        (LinearMap.minpoly_dvd_charpoly A)
    have h2 : A.charpoly ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
    have h3 := Polynomial.natDegree_le_of_dvd h1 h2
    rwa [LinearMap.charpoly_natDegree] at h3
  exact (CFSG.RankThree.PartOne.KCLinComm.orderOf_le_natDegree_of_mem_primaryFactors hp hAp hh
    hne).trans hdeg

end NoSingularStruct

section Rank

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem rankLE2_of_finrank_lt (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (hlt : finrank K V < 3 * orderOf ((Nat.card K : ℕ) : ZMod p)) :
    RankLE2 p (orthDerived Q) := by
  intro F hF
  by_contra hgt
  push Not at hgt
  have hpK := manyRank_natCast_ne_zero hp hpl
  have hel : ElemAbOrth Q p (F.map (orthDerived Q).subtype) :=
    { orth := fun a ha => by
        obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp ha
        exact CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q x.2
      pow := fun a ha => by
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        simpa using congrArg Subtype.val (hF.2 x hx)
      comm := fun a ha b hb => by
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
        have h1 := hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        simpa using congrArg (fun z : F => ((z : orthDerived Q) : V ≃ₗ[K] V)) h1 }
  obtain ⟨L, hL, hcard⟩ := exists_blockFamily_top hQ hp hpK hel
  have hinj : Function.Injective (orthDerived Q).subtype := Subtype.val_injective
  rw [Subgroup.card_map_of_injective hinj] at hcard
  have hlen : 2 < L.length := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_lt_of_le hgt hcard)
  obtain ⟨a, b, c, rest, rfl⟩ : ∃ a b c rest, L = a :: b :: c :: rest := by
    rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · exact ⟨a, b, c, rest, rfl⟩
  obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hL.orth
  obtain ⟨h3, _⟩ := List.pairwise_cons.mp h2
  have hra : PolarNondegOn Q a.1 := hL.reg a (by simp)
  have hrb : PolarNondegOn Q b.1 := hL.reg b (by simp)
  have hrc : PolarNondegOn Q c.1 := hL.reg c (by simp)
  have hfa := OrthBlk.IsBlock.orderOf_le_finrank hp hpl hra (hL.block a (by simp))
  have hfb := OrthBlk.IsBlock.orderOf_le_finrank hp hpl hrb (hL.block b (by simp))
  have hfc := OrthBlk.IsBlock.orderOf_le_finrank hp hpl hrc (hL.block c (by simp))
  have hsum := manyRank_finrank_three_le hra hrb hrc (h1 b (by simp)) (h1 c (by simp))
    (h3 c (by simp))
  omega

end Rank

end CFSG.LieType.SeitzGeneration
