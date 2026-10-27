module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Types
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Cited

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G]

section Omega

theorem omegaOneCenter_le_self (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hz => hz.1.1

theorem omegaOneCenter_le_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).2 fun _ hz => hz.1.2

theorem le_centralizer_omegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.1 (omegaOneCenter_le_centralizer T hz) t ht).symm

theorem characteristic_omegaOneCenter (T : Subgroup G) :
    ((quasithinOmegaOneCenter T).subgroupOf T).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have key : ∀ z ∈ quasithinOmegaOneCenter T, ∃ hzT : z ∈ T,
      ((φ ⟨z, hzT⟩ : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    intro z hz
    have hz' : z ∈ Subgroup.closure
        {z : G | z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ^ 2 = 1} := hz
    clear hz
    induction hz' using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨⟨hzT, hzc⟩, hz2⟩ := hz
      refine ⟨hzT, Subgroup.subset_closure ⟨⟨(φ ⟨z, hzT⟩).2, ?_⟩, ?_⟩⟩
      · refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
        have hcT : ∀ s : ↥T, s * ⟨z, hzT⟩ = ⟨z, hzT⟩ * s := fun s =>
          Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc s s.2)
        have : (⟨t, ht⟩ : ↥T) * φ ⟨z, hzT⟩ = φ ⟨z, hzT⟩ * ⟨t, ht⟩ := by
          obtain ⟨s, hs⟩ := φ.surjective ⟨t, ht⟩
          rw [← hs, ← map_mul, ← map_mul, hcT s]
        exact congrArg Subtype.val this
      · have h1 : (⟨z, hzT⟩ : ↥T) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
        have h2 : (φ ⟨z, hzT⟩) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
        simpa using congrArg Subtype.val h2
    | one =>
      refine ⟨T.one_mem, ?_⟩
      have : φ ⟨1, T.one_mem⟩ = 1 := map_one φ
      rw [this]
      exact (quasithinOmegaOneCenter T).one_mem
    | mul a b _ _ ha hb =>
      obtain ⟨haT, ha⟩ := ha
      obtain ⟨hbT, hb⟩ := hb
      refine ⟨T.mul_mem haT hbT, ?_⟩
      have : (⟨a * b, T.mul_mem haT hbT⟩ : ↥T) = ⟨a, haT⟩ * ⟨b, hbT⟩ := rfl
      rw [this, map_mul]
      exact (quasithinOmegaOneCenter T).mul_mem ha hb
    | inv a _ ha =>
      obtain ⟨haT, ha⟩ := ha
      refine ⟨T.inv_mem haT, ?_⟩
      have : (⟨a⁻¹, T.inv_mem haT⟩ : ↥T) = (⟨a, haT⟩ : ↥T)⁻¹ := rfl
      rw [this, map_inv]
      exact (quasithinOmegaOneCenter T).inv_mem ha
  obtain ⟨hxT, h⟩ := key x hx
  exact h

end Omega

section Basic

variable [Finite G]

theorem nontrivial_of_quasisimple_or_card_three {A : Type} [Group A]
    (h : CFSG.IsQuasisimple A ∨ Nat.card A = 3) : Nontrivial A := by
  rcases h with ⟨-, -, a, b, hab⟩ | h3
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center A) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center A) b
    refine ⟨⟨x, y, fun hxy => hab ?_⟩⟩
    subst hxy
    rfl
  · have : Finite A := Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.1 (by omega)

theorem isSylowTwoOf_inf_of_isSubnormal' {T H L : Subgroup G} (h : IsSubnormal L H) :
    IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := B6.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

end Basic

section Fitting

variable {V : Type} [CommGroup V]

theorem isSubnormal_of_le_center_fitting {G K : Subgroup (MulAut V)}
    (hK : K ≤ fittingOf G ⊓ Subgroup.centralizer (fittingOf G : Set (MulAut V))) :
    IsSubnormal K G := by
  have hKF : K ≤ fittingOf G := fun k hk => (hK hk).1
  have hnormK : (K.subgroupOf (fittingOf G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (n : MulAut V) ∈ Subgroup.centralizer (fittingOf G : Set (MulAut V)) := (hK hn).2
    have h1 := Subgroup.mem_centralizer_iff.1 hc (g : MulAut V) g.2
    have : (g : MulAut V) * n * (g : MulAut V)⁻¹ = n := by rw [h1]; group
    show ((g * n * g⁻¹ : ↥(fittingOf G)) : MulAut V) ∈ K
    simpa [this] using hn
  have hnormF : ((fittingOf G).subgroupOf G).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_fittingOf g.2 hn
  exact IsSubnormal.step hKF hnormK
    (IsSubnormal.step (fittingOf_le G) hnormF (IsSubnormal.refl G))

end Fitting

variable [Finite G]

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

omit [Finite G] in
theorem T_ne_bot : T ≠ ⊥ := by
  intro hT
  have hU : blockU K ≠ ⊥ := by
    intro h
    have := S.short.2.2.2.2.1
    rw [h] at this
    exact not_lt_bot this
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hU
  have hu2 : u ^ 2 = 1 := S.short.2.2.1.2 u hu
  have huX : u ∈ X := S.PX (S.KP (C1GN.blockU_le_self K hu))
  have hne1 : (⟨u, huX⟩ : ↥X) ≠ 1 := fun h => hu1 (Subtype.ext (by simpa using congrArg Subtype.val h))
  have hsq : (⟨u, huX⟩ : ↥X) ^ 2 = 1 := Subtype.ext (by simpa using hu2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (⟨u, huX⟩ : ↥X) = 2 := orderOf_eq_prime hsq hne1
  have hdvd : 2 ∣ Nat.card X := hord ▸ orderOf_dvd_natCard _
  apply S.sylow.2.2
  rw [hT, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact hdvd

theorem not_le_centralizer_omega (hP : P = T ⊔ conjClosure K T) (hcgs : ¬ P ≤ cgsIn X T) :
    ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hKC
  apply hcgs
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr S.T_ne_bot
    have hcen : Nontrivial (Subgroup.center T) := S.sylow.2.1.center_nontrivial
    have hcard : 2 ∣ Nat.card (Subgroup.center T) := by
      rcases (S.sylow.2.1.to_subgroup (Subgroup.center T)).card_eq_or_dvd with h1 | h2
      · exact absurd h1 (Finite.one_lt_card).ne'
      · exact h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2 hcard
    intro hbot
    have hx2 : (x : T) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    have hxmem : ((x : T) : G) ∈ quasithinOmegaOneCenter T := by
      apply Subgroup.subset_closure
      refine ⟨⟨(x : T).2, ?_⟩, by simpa using congrArg Subtype.val hx2⟩
      refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
      have := Subgroup.mem_center_iff.1 x.2 ⟨t, ht⟩
      exact congrArg Subtype.val this
    rw [hbot] at hxmem
    have hx1 : (x : T) = 1 := Subtype.ext (Subgroup.mem_bot.1 hxmem)
    have : (x : Subgroup.center T) = 1 := Subtype.ext hx1
    have h1 : orderOf x = 1 := by rw [this, orderOf_one]
    rw [hx] at h1
    omega
  have hPC : P ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [hP]
    refine sup_le (le_centralizer_omegaOneCenter T) (conjClosure_le fun t ht k hk => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : Commute z t :=
      Subgroup.mem_centralizer_iff.1 (le_centralizer_omegaOneCenter T ht) z hz
    have hzk : Commute z k := Subgroup.mem_centralizer_iff.1 (hKC hk) z hz
    exact ((hzt.mul_right hzk).mul_right hzt.inv_right).eq
  have hZN : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hPXN : P ≤ X ⊓ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    le_inf S.PX (hPC.trans hZN)
  refine hPXN.trans ?_
  exact le_iSup_of_le _ (le_iSup_of_le (omegaOneCenter_le_self T)
    (le_iSup_of_le hZne (le_iSup_of_le (characteristic_omegaOneCenter T) le_rfl)))

omit [Finite G] S in
theorem commutator_VZ_ne_bot
    (hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ⁅VZ T X, K⁆ ≠ ⊥ := by
  have hZV : quasithinOmegaOneCenter T ≤ VZ T X := le_conjClosure _ _
  intro h
  apply hKZ
  have h1 : ⁅quasithinOmegaOneCenter T, K⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hZV le_rfl).trans h.le)
  rw [Subgroup.commutator_comm] at h1
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1

theorem b113_concl (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (hSQ : IsSQTKCat ↥X)
    (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hne : ⁅VZ T X, K⁆ ≠ ⊥) : Bridge.B113Concl (autI hV X) (autI hV K) := by
  have hSQQ : Bridge.IsSQTKQuotient CFSG.SectionRank.IsKGroupCat ↥(autI hV X) :=
    ⟨↥X, inferInstance, inferInstance, toAutI hV X S.hXV, toAutI_surjective hV X S.hXV,
      fun p hp hp2 => isStronglyQuasithin_iff.mp hSQ.1 p hp hp2, hSQ.2⟩
  exact h113 (IntMod (VZ T X) hV) (fun v => IntMod.sq_eq_one v) (autI hV X) (autI hV T) (autI hV K)
    (offenderImages hV X) hSQQ (pCoreOf_autI_eq_bot hV S.hred)
    (B2F.isSylowTwoOf_autI hV S.hXV S.sylow) (S.isStableFF_offenderImages hV hKJ hne)
    (autI_mono hV (S.KP.trans S.PX)) (S.isQuasisimple_or_card_three_autI hV hUV)
    (S.isSubnormal_autI_sup hV) (S.commutator_ffJP_eq hV hKJ)

theorem exists_block_of_concl (hSQ : IsSQTKCat ↥X) (hodd : AltEvenExcluded)
    (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (hchi : (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ IsAltType K 3 ∨ IsAltType K 5)
    (hB : Bridge.B113Concl (autI hV X) (autI hV K)) :
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n) := by
  have hq0 := S.isQuasisimple_or_card_three_autI hV hUV
  have hKX : K ≤ X := S.KP.trans S.PX
  have hKaX : autI hV K ≤ autI hV X := autI_mono hV hKX
  have hself : IsSubnormal (autI hV K) (autI hV X) → ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧
      blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧ K = L := by
    intro hsub
    obtain ⟨L, hL, hKL, hUL, hULV, -, -, hLK⟩ := S.exists_block_lift hV hUV hKaX hsub le_rfl hq0
      (fun N hN _ hKN => le_antisymm hN hKN)
    exact ⟨L, hL, hKL, hUL, hULV, (hLK rfl).symm⟩
  rcases hB with ⟨-, hF⟩ | hcomp | ⟨Lstar, hLcomp, hKL, m, ⟨eL⟩, hrest⟩
  · obtain ⟨L, hL, hKL, hUL, hULV, hKe⟩ := hself (isSubnormal_of_le_center_fitting hF)
    exact ⟨L, hL, hKL, hUL, hULV, Or.inl hKe⟩
  · obtain ⟨L, hL, hKL, hUL, hULV, hKe⟩ := hself hcomp.2.1
    exact ⟨L, hL, hKL, hUL, hULV, Or.inl hKe⟩
  · obtain ⟨hLle, hLsub, hLqs⟩ := hLcomp
    have hqL : CFSG.IsQuasisimple ↥Lstar := B1Red.isQuasisimple_of_open hLqs
    have hm5 : 5 ≤ m := alt_five_le_of_quasisimple eL hqL
    have hsimpL : IsSimpleGroup ↥Lstar :=
      (MulEquiv.isSimpleGroup_congr eL).2 (Bridge.alt_isSimple hm5)
    have hKnt : Nontrivial ↥(autI hV K) := nontrivial_of_quasisimple_or_card_three hq0
    have hnc : ∀ N : Subgroup (MulAut (IntMod (VZ T X) hV)), N ≤ Lstar →
        (N.subgroupOf Lstar).Normal → autI hV K ≤ N → N = Lstar := by
      intro N hNL hNn hKN
      have : (N.subgroupOf Lstar).Normal := hNn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Lstar) with h | h
      · exfalso
        have hN0 : N = ⊥ := disjoint_self.1 ((Subgroup.subgroupOf_eq_bot.1 h).mono_right hNL)
        rw [hN0] at hKN
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hKnt (le_bot_iff.1 hKN)
      · exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 h)
    obtain ⟨L, hL, hKL', hUL, hULV, hautL, -, hLK⟩ :=
      S.exists_block_lift hV hUV hLle hLsub hKL (Or.inl hqL) hnc
    by_cases hKe : autI hV K = Lstar
    · exact ⟨L, hL, hKL', hUL, hULV, Or.inl (hLK hKe).symm⟩
    · refine ⟨L, hL, hKL', hUL, hULV, Or.inr ?_⟩
      have hLN : L ≤ Subgroup.normalizer (VZ T X : Set G) := hL.2.1.trans S.hXV
      have eL' : ↥(autI hV L) ≃* alternatingGroup (Fin m) :=
        (MulEquiv.subgroupCongr hautL).trans eL
      have hLalt := isAltQuotient_of_equiv hV hLN eL'
      rcases hrest with ⟨n, hnm, ⟨eK⟩⟩ | ⟨⟨eK3⟩, hm7⟩
      · have hn : n = 3 ∨ n = 5 := S.degree_eq_three_or_five hV hUV hchi eK
        have hm8 : m ≤ 8 := by
          by_contra hm9
          push Not at hm9
          obtain ⟨α, hαs, hαk⟩ := L246.exists_alt_pCore S.charTwo S.sylow hL hULV hLalt
          have h3L := L246.three_le_pRank_of_alt (by omega) α hαs hαk
          have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          have h4 : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 X :=
            CFSG.SectionRank.pRank_mono (by norm_num) hL.2.1
          have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
            pRank_top_subtype (p := 3) X
          have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 :=
            isStronglyQuasithin_iff.mp hSQ.1 3 Nat.prime_three (by norm_num)
          omega
        have hmodd : Odd m := by
          rcases Nat.even_or_odd m with he | ho
          · exfalso
            have h68 : m = 6 ∨ m = 8 := by
              obtain ⟨r, hr⟩ := he
              omega
            have hsyl : IsSylowTwoOf (autI hV T ⊓ Lstar) Lstar :=
              isSylowTwoOf_inf_of_isSubnormal' hLsub (B2F.isSylowTwoOf_autI hV S.hXV S.sylow)
            have hsubK : IsSubnormal (autI hV K) (autI hV K ⊔ (autI hV T ⊓ Lstar)) :=
              A3.subnormal_of_le_of_le (S.isSubnormal_autI_sup hV) le_sup_left
                (sup_le le_sup_left (inf_le_left.trans le_sup_right))
            exact hodd _ Lstar (autI hV K) (autI hV T ⊓ Lstar) m n h68 hn ⟨eL⟩ hKL ⟨eK⟩ hsyl hsubK
          · exact ho
        have hnodd : Odd n := by rcases hn with rfl | rfl <;> decide
        exact ⟨m, n, hmodd, hnodd, by omega, by rcases hn with rfl | rfl <;> omega, hLalt,
          isAltQuotient_of_equiv hV S.hKN eK⟩
      · exact ((S.isEmpty_equiv_sl3 hV hUV hchi).false eK3).elim

end Setting

theorem c127_of_cited (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat)
    (hodd : AltEvenExcluded) (X T P K : Subgroup G) (hX : CharTwo X) (hT : IsSylowTwoOf T X)
    (hSQ : IsSQTKCat ↥X) (hP : P ∈ uFamHat X T) (hK : IsChi0Block P K) (hcgs : ¬ P ≤ cgsIn X T)
    (hKJ : ⁅K, thompsonJ T⁆ = K) (hPK : P = T ⊔ conjClosure K T) :
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n) := by
  have S : Setting X T P K := ⟨hX, hT, hP.1.1, hP.1.2.1.le, hK.1⟩
  have hKZ := S.not_le_centralizer_omega hPK hcgs
  have hUV := S.blockU_le_VZ hKZ
  have hV : IsElemAbelian 2 (VZ T X) := S.hred.2.2.1
  have hne := Setting.commutator_VZ_ne_bot (X := X) hKZ
  exact S.exists_block_of_concl hSQ hodd hV hUV hK.2 (S.b113_concl h113 hSQ hV hUV hKJ hne)

end L246C127

end CFSG.QuasithinUnique
