module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBlockOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryContain
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityNonsplit
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityOne
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneLift

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Blocks

theorem card_idSpecialBlock (x : gramSU h (idGram K n)) (a : K[X]) :
    Nat.card (idSpecialBlock h x a) =
      Nat.card (specialBlock (idForm h n) (toLinU h n (liftUnitary x)) a) := by
  rw [← map_toLinU_idSpecialBlock x a]
  exact (Subgroup.card_map_of_injective toLinU_injective).symm

theorem xlin_pow_eq_one {x : gramSU h (idGram K n)} (L : PlaneData h n p x) :
    xlin h n x ^ p = 1 := by
  have hxp : (toLinU h n (liftUnitary x)) ^ p = 1 := by
    rw [← map_pow]
    have : (liftUnitary x) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact congrArg Subtype.val L.pow_eq_one)
    rw [this, map_one]
  have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (g : Module.End K (Fin n → K))) hxp
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h2

theorem dvd_card_idSpecialBlock_of_ne {x : gramSU h (idGram K n)} (L : PlaneData h n p x)
    (i : GoodBlockIdx h x) (hne : (i.1 : K[X]) ≠ X - C 1) :
    p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X])) := by
  have := h.finite
  have H := L.primaryData
  rw [card_idSpecialBlock]
  have hdvd : (i.1 : K[X]) ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp i.1.2).2.2.trans (minpoly.dvd K _ (by simp [xlin_pow_eq_one L]))
  have hpE := dvd_card_adjoinRoot_sub_one_of_ne L.prime (monic_of_mem_primaryFactors i.1.2)
    hdvd hne
  by_cases hself : dualPoly h.bar (i.1 : K[X]) = i.1
  · refine dvd_card_specialBlock_selfDual H i.1 hself le_rfl i.2.1 ?_
    have hE : Nat.card (AdjoinRoot (i.1 : K[X])) =
        ((ℓ ^ f) ^ (i.1 : K[X]).natDegree) ^ 2 := by
      rw [natCard_adjoinRoot h, ← pow_mul, ← pow_mul]
      ring_nf
    rw [hE] at hpE
    have h1 : 1 ≤ ((ℓ ^ f) ^ (i.1 : K[X]).natDegree) ^ 2 :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ (pow_ne_zero _ h.prime.ne_zero)))
    have h2 := Int.natCast_dvd_natCast.mpr hpE
    rw [Nat.cast_sub h1] at h2
    simpa using h2
  · exact dvd_card_specialBlock_paired i.1 (pairedPrimaryBlock H i.1 (Ne.symm hself)) i.2.1
      L.prime hpE

theorem dvd_card_idSpecialBlock_X_sub_one {x : gramSU h (idGram K n)} (L : PlaneData h n p x)
    (hmem : (X - C 1 : K[X]) ∈ primaryFactors (xlin h n x)) {j : ℕ} (hj : 2 ≤ j)
    (hjm : j ≤ Module.finrank K (primaryComponent (xlin h n x) (X - C 1)))
    (hpj : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ j - (-1) ^ j) :
    p ∣ Nat.card (idSpecialBlock h x (X - C 1)) := by
  rw [card_idSpecialBlock]
  refine dvd_card_specialBlock_selfDual L.primaryData ⟨X - C 1, hmem⟩ (dualPoly_X_sub_C_one _)
    hj ?_ ?_
  · rw [primaryMultiplicity_X_sub_C_one]
    exact hjm
  · rw [natDegree_X_sub_C, pow_one]
    exact hpj

theorem dvd_card_idBlockImage {x : gramSU h (idGram K n)} (L : PlaneData h n p x)
    (i : GoodBlockIdx h x) (hpd : p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X]))) :
    p ∣ Nat.card (idBlockImage h x (i.1 : K[X])) := by
  have := h.finite
  have : Fact p.Prime := ⟨L.prime⟩
  have GS := L.goodSetting ⊤ le_top
  set SB := idSpecialBlock h x (i.1 : K[X]) with hSB
  let φ : SB →* MulAut (primeFormP h (idGram K n)) :=
    (primeFormConjHom h (idGram K n)).comp SB.subtype
  have hrange : φ.range = idBlockImage h x (i.1 : K[X]) := by
    ext y
    constructor
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, Y.2, rfl⟩
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨⟨Y, hY⟩, rfl⟩
  have hsplit : Nat.card SB = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hker : ¬ p ∣ Nat.card φ.ker := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) p hdvd
    set Y : primeFormUnitary h (idGram K n) := ((z : SB) : primeFormUnitary h (idGram K n))
      with hYdef
    have hYSU : (Y : GL (Fin n) K) ∈ gramSU h (idGram K n) := GS.F_le_Hs i (z : SB).2
    have hY1 : primeFormConjHom h (idGram K n) Y = 1 := z.2
    have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hYp : (⟨Y, hYSU⟩ : gramSU h (idGram K n)) ^ p = 1 := by
      apply Subtype.ext
      have := congrArg (fun w : φ.ker => (((w : SB) : primeFormUnitary h (idGram K n)) :
        GL (Fin n) K)) hzp
      simpa using this
    have hYker : (⟨Y, hYSU⟩ : gramSU h (idGram K n)) ∈ (innerLift h n).ker := by
      rw [MonoidHom.mem_ker, innerLift_apply, ← primeFormConjHom_liftUnitary]
      exact hY1
    have hY1' : (⟨Y, hYSU⟩ : gramSU h (idGram K n)) ≠ 1 := by
      intro h1
      have hY1'' : Y = 1 := Subtype.ext (show (Y : GL (Fin n) K) =
        ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) from
          congrArg (fun w : gramSU h (idGram K n) => (w : GL (Fin n) K)) h1)
      have hz1 : z = 1 := Subtype.ext (Subtype.ext hY1'')
      rw [hz1, orderOf_one] at hz
      exact L.prime.one_lt.ne hz
    have hw : orderOf (⟨⟨Y, hYSU⟩, hYker⟩ : (innerLift h n).ker) = p := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => hY1' (congrArg Subtype.val h1)
      simpa using hYp
    have := orderOf_dvd_natCard (⟨⟨Y, hYSU⟩, hYker⟩ : (innerLift h n).ker)
    rw [hw] at this
    exact not_dvd_card_ker_innerLift L.three_le L.ne L.prime L.noTorsion this
  rw [hsplit] at hpd
  rcases (Nat.Prime.dvd_mul L.prime).1 hpd with h1 | h1
  · rwa [hrange] at h1
  · exact absurd h1 hker

end Blocks

section Commute

variable {Ahat : Subgroup (gramSU h (idGram K n))}

theorem commute_block_of_mem_localDeltaIn (S : PlaneSetup h n p Ahat)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hEmap : Ahat.map (innerLift h n) = E)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    {g : MulAut (primeFormP h (idGram K n))} (hg : g ∈ localDeltaIn p H E)
    {x : gramSU h (idGram K n)} (hx : x ∈ Ahat) (hx1 : x ≠ 1) (i : GoodBlockIdx h x)
    (hpd : p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X]))) :
    ∀ Y ∈ idSpecialBlock h x (i.1 : K[X]),
      g * primeFormConjHom h (idGram K n) Y = primeFormConjHom h (idGram K n) Y * g := by
  have := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hconj : innerLift h n x = primeFormConjHom h (idGram K n) (liftUnitary x) := by
    rw [primeFormConjHom_liftUnitary, innerLift_apply]
  have htE : primeFormConjHom h (idGram K n) (liftUnitary x) ∈ E := by
    rw [← hEmap, ← hconj]
    exact Subgroup.mem_map_of_mem _ hx
  have ht1 : primeFormConjHom h (idGram K n) (liftUnitary x) ≠ 1 := by
    intro h1
    rw [← hconj] at h1
    exact hx1 (eq_of_innerLift_eq S.three_le S.ne S.noTorsion (S.pow_eq_one hx) (one_pow p)
      (by rw [h1, map_one]))
  have GS := (S.planeData hx).goodSetting H hH
  have hcore := le_core_of_mem_localDeltaIn hg htE ht1
  have hJ : ¬ Nat.Coprime p (Nat.card ((idSpecialBlock h x (i.1 : K[X])).map
      (primeFormConjHom h (idGram K n)))) := by
    rw [Nat.Prime.coprime_iff_not_dvd S.prime, not_not]
    exact dvd_card_idBlockImage (S.planeData hx) i hpd
  intro Y hY
  exact commute_of_mem_gLAPPrimeCoreOf_of_isComponent S.prime (GS.map_le_centralizerB i)
    (GS.isComponent_image i) hJ hcore _ (Subgroup.mem_map_of_mem _ hY)

end Commute

section Numerics

theorem ordNegQ_eq_two_of_three_le (hp : p.Prime) (hp3 : 3 ≤ p) (hℓ : ℓ.Prime)
    (h2 : ordNegQ ℓ f p = 2) (hf : 1 ≤ f) : p ∣ ℓ ^ f - 1 ∧ 3 < ℓ ^ f := by
  have hne : ordNegQ ℓ f p ≠ 1 := by omega
  have hd := dvd_of_ordNegQ_eq hp h2
  have hq1 : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1 := by
    simpa [neg_sq] using hd
  have hfac : ((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1 =
      (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) + 1) := by ring
  rw [hfac] at hd'
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : ¬ p ∣ ℓ ^ f + 1 := fun h => hne ((ordNegQ_eq_one_iff hp).mpr h)
  rcases hpz.dvd_or_dvd hd' with h | h
  · have h' : p ∣ ℓ ^ f - 1 := by
      have : ((ℓ ^ f - 1 : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) - 1 := by
        rw [Nat.cast_sub hq1.le]
        simp
      rw [← this] at h
      exact_mod_cast h
    refine ⟨h', ?_⟩
    have := Nat.le_of_dvd (by omega) h'
    omega
  · exfalso
    apply hp1
    have : ((ℓ ^ f + 1 : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [← this] at h
    exact_mod_cast h

variable {Ahat : Subgroup (gramSU h (idGram K n))}

theorem nonsplitFacts_of (S : PlaneSetup h n p Ahat) (hp2 : p ≠ 2) (hpq : ¬ p ∣ ℓ ^ f + 1) :
    NonsplitFacts h n p Ahat := by
  have hp := S.prime
  have hpℓ := S.ne_char
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  refine ⟨planeKernelDecomposition hp hpℓ S.elem S.card, ?_, ?_, ?_, ?_⟩
  · have h1 : ordNegQ ℓ f p ≠ 1 := fun h1 => hpq ((ordNegQ_eq_one_iff hp).mp h1)
    have := pos_ordNegQ (f := f) hp hpℓ h.prime
    omega
  · exact fun h2 => ordNegQ_eq_two_of_three_le hp hp3 h.prime h2 h.one_le
  · intro hq
    rcases (by omega : p = 3 ∨ 3 < p) with h3 | h3
    · exact absurd (by rw [hq, h3]) hpq
    · exact four_le_ordNegQ_of_two hp h3 hpℓ h.prime hq
  · intro hq
    rcases (by omega : p = 3 ∨ 3 < p) with h3 | h3
    · exfalso
      have hℓ3 : ℓ ∣ 3 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
      have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp hℓ3
      exact hpℓ (by omega)
    · exact three_le_ordNegQ_of_three hp h3 hpℓ h.prime hq

theorem dvd_pow_ordNegQ_sub (hp : p.Prime) :
    (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ ordNegQ ℓ f p - (-1) ^ ordNegQ ℓ f p := by
  have hd := dvd_of_ordNegQ_eq (ℓ := ℓ) (f := f) hp rfl
  have e : ((ℓ ^ f : ℕ) : ℤ) ^ ordNegQ ℓ f p - (-1) ^ ordNegQ ℓ f p =
      (-1) ^ ordNegQ ℓ f p * ((-((ℓ ^ f : ℕ) : ℤ)) ^ ordNegQ ℓ f p - 1) := by
    rw [mul_sub, ← mul_pow, neg_one_mul, neg_neg, mul_one]
  rw [e]
  exact Dvd.dvd.mul_left hd _

theorem exists_orthonormal_eigenbasis_of_dvd (S : PlaneSetup h n p Ahat)
    (hpq : p ∣ ℓ ^ f + 1) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), IsOrthonormalFamily h b ∧
      ∀ x ∈ Ahat, ∀ i, ∃ c : K, xlin h n x (b i) = c • b i := by
  have hp := S.prime
  obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp hpq
  have : NeZero p := ⟨hp.ne_zero⟩
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have hP : IsPlane p ↥Ahat := isPlane_of_elementaryAbelian hp S.elem S.card
  have hel := S.elem
  have hcomm : ∀ x y : ↥Ahat, Commute (act (planeRep h n Ahat) x) (act (planeRep h n Ahat) y) :=
    fun x y => by
      have hxy : x * y = y * x := (IsMulCommutative.is_comm (M := ↥Ahat)).comm x y
      change act (planeRep h n Ahat) x * act (planeRep h n Ahat) y =
        act (planeRep h n Ahat) y * act (planeRep h n Ahat) x
      rw [← act_mul, ← act_mul, hxy]
  have hpow : ∀ x : ↥Ahat, act (planeRep h n Ahat) x ^ p = 1 := fun x => by
    rw [← act_pow, hP.pow x, act_one]
  have hiso : ∀ (x : ↥Ahat) (v w : Fin n → K),
      idForm h n (act (planeRep h n Ahat) x v) (act (planeRep h n Ahat) x w) =
        idForm h n v w := fun x v w => planeRep_mem Ahat x v w
  obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis h hζ hpq
    (idForm_isSymm h n) (idForm_separatingLeft h n)
    (fun x : ↥Ahat => act (planeRep h n Ahat) x) hcomm hpow hiso
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun K)), fun i j => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact ⟨μ ⟨x, hx⟩ _, hbμ ⟨x, hx⟩ _⟩

end Numerics

section Main

theorem localDeltaIn_eq_bot_primeFormP (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (h32 : ¬(p = 3 ∧ ℓ ^ f = 2))
    (E : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hEinn : E ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range)
    (hE : IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn p H E = ⊥ := by
  classical
  have := h.finite
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c hc hcn hcp
    have h1 : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hc
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hcp) with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · exact absurd (Nat.dvd_gcd (h3 ▸ orderOf_dvd_of_pow_eq_one hcn)
        (h3 ▸ orderOf_dvd_of_pow_eq_one h1)) hpg
  obtain ⟨Ahat, hAhat, -⟩ := exists_unique_planeLift hn hne hp hZp E hEinn hE hEc
  have S : PlaneSetup h n p Ahat := ⟨hn, hne, hp, hpℓ, hZp, hAhat.1, hAhat.2.1⟩
  have hEmap := hAhat.2.2.1
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hcent : ∀ x ∈ Ahat, g * primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) * g := by
    intro x hx
    refine commute_of_mem_localDeltaIn hg ?_
    rw [← hEmap, primeFormConjHom_liftUnitary]
    exact ⟨x, hx, (innerLift_apply x)⟩
  have hgood := fun {x : gramSU h (idGram K n)} (hx : x ∈ Ahat) (hx1 : x ≠ 1)
    (i : GoodBlockIdx h x) (hpd : p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X]))) =>
    commute_block_of_mem_localDeltaIn S hEmap hH hg hx hx1 i hpd
  by_cases hpq : p ∣ ℓ ^ f + 1
  ·
    have hq3 : 3 < ℓ ^ f := by
      by_contra hle
      have hq2 : 2 ≤ ℓ ^ f := two_le_pow_of h
      rcases (by omega : ℓ ^ f = 2 ∨ ℓ ^ f = 3) with hq | hq
      · rw [hq] at hpq
        exact h32 ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpq, hq⟩
      · rw [hq] at hpq
        have h4 : p ∣ 2 ^ 2 := hpq
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
    obtain ⟨b, hbON, hbeig⟩ := exists_orthonormal_eigenbasis_of_dvd S hpq
    refine rigidity_of_orthonormal_eigenbasis S hpq hq3 b hbON hbeig g hcent
      fun x hx hx1 i => hgood hx hx1 i ?_
    by_cases hne1 : (i.1 : K[X]) = X - C 1
    · have hmem : (X - C 1 : K[X]) ∈ primaryFactors (xlin h n x) := hne1 ▸ i.1.2
      have hm := i.2.1
      rw [hne1, primaryMultiplicity_X_sub_C_one] at hm
      rw [hne1]
      refine dvd_card_idSpecialBlock_X_sub_one (S.planeData hx) hmem le_rfl hm ?_
      have e : ((ℓ ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 =
          (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) + 1) := by ring
      rw [e]
      exact Dvd.dvd.mul_left (by exact_mod_cast hpq) _
    · exact dvd_card_idSpecialBlock_of_ne (S.planeData hx) i hne1
  ·
    have F := nonsplitFacts_of S hp2 hpq
    have hdec := F.decomp
    have he2 : 2 ≤ ordNegQ ℓ f p := F.e_gt
    refine rigidity_of_nonsplit F S g hcent fun x hx hx1 i => ?_
    by_cases hne1 : (i.1 : K[X]) = X - C 1
    · have hmem : (X - C 1 : K[X]) ∈ primaryFactors (xlin h n x) := hne1 ▸ i.1.2
      set x' : ↥Ahat := ⟨x, hx⟩ with hx'
      have hx'1 : x' ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
      have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x' = p :=
        orderOf_eq_prime (Subtype.ext (S.pow_eq_one hx)) hx'1
      set L : Subgroup ↥Ahat := Subgroup.zpowers x' with hLdef
      have hL : Nat.card L = p := by rw [Nat.card_zpowers, hord]
      have hxL : x' ∈ L := Subgroup.mem_zpowers x'
      have hW := hdec.ker_eq L hL x' hxL hx'1
      by_cases hVL : lineSpace (planeRep h n Ahat) (idForm h n) L = ⊥
      ·
        obtain ⟨L₀, -, hL₀, -, -, hV₀, -⟩ := hdec.exists_two_active
        obtain ⟨t, htL₀, ht1⟩ : ∃ t : ↥Ahat, t ∈ L₀ ∧ t ≠ 1 := by
          have h1 : Nontrivial ↥L₀ :=
            Finite.one_lt_card_iff_nontrivial.mp (by rw [hL₀]; exact hp.one_lt)
          obtain ⟨t, ht⟩ := exists_ne (1 : ↥L₀)
          exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
        have ht1' : t.1 ≠ 1 := fun h' => ht1 (Subtype.ext h')
        obtain ⟨hmem_t, hgood_t⟩ := isGoodBlock_X_sub_one F hL₀ hV₀ htL₀ ht1
        have hWt := primaryComponent_X_sub_one_eq F hL₀ htL₀ ht1
        have hpd_t : p ∣ Nat.card (idSpecialBlock h t.1 (X - C 1)) := by
          refine dvd_card_idSpecialBlock_X_sub_one (S.planeData t.2) hmem_t he2 ?_
            (dvd_pow_ordNegQ_sub hp)
          rw [hWt]
          exact (F.e_le_finrank hL₀ hV₀).trans (Submodule.finrank_mono le_sup_right)
        have hcomm_t := hgood t.2 ht1' ⟨⟨X - C 1, hmem_t⟩, hgood_t⟩ hpd_t
        intro Y hY
        refine hcomm_t Y ?_
        rw [hne1] at hY
        rw [mem_idSpecialBlock] at hY ⊢
        have hxt : Commute (xlin h n x) (xlin h n t.1) := by
          have h1 : liftUnitary x * liftUnitary t.1 = liftUnitary t.1 * liftUnitary x :=
            Subtype.ext (show ((x * t.1 : gramSU h (idGram K n)) : GL (Fin n) K) =
              ((t.1 * x : gramSU h (idGram K n)) : GL (Fin n) K) from
                congrArg Subtype.val (S.commute hx t.2))
          have h2 := congrArg (fun z : primeFormUnitary h (idGram K n) =>
            ((toLinU h n z : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K))) h1
          simp only [map_mul, Units.val_mul] at h2
          exact h2
        have hfix : ∀ v : Fin n → K, xlin h n x v = v → xlin h n t.1 v = v := by
          intro v hv
          have hv' : v ∈ LinearMap.ker (act (planeRep h n Ahat) x' - 1) := by
            rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
            exact hv
          rw [hW, hVL, sup_bot_eq] at hv'
          exact hv' t (Subgroup.mem_top t)
        exact specialBlock_X_sub_one_le (S.planeData hx).primaryData
          (S.planeData t.2).primaryData hxt hfix hmem hmem_t hY
      ·
        refine hgood hx hx1 i ?_
        rw [hne1]
        refine dvd_card_idSpecialBlock_X_sub_one (S.planeData hx) hmem he2 ?_
          (dvd_pow_ordNegQ_sub hp)
        rw [primaryComponent_X_sub_one_eq F hL hxL hx'1]
        exact (F.e_le_finrank hL hVL).trans (Submodule.finrank_mono le_sup_right)
    · exact hgood hx hx1 i (dvd_card_idSpecialBlock_of_ne (S.planeData hx) i hne1)

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
