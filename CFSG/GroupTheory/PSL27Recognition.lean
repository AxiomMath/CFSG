module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.GroupTheory.SuzukiTwoGroupsBasic
public import CFSG.GroupTheory.ABGDGroups.LinearOddSubgroups
public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW2

public section

namespace CFSG

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private lemma sylow_centralizer_data {X : Type} [Group X] [Finite X]
    (hcent : ∀ j : X, orderOf j = 2 →
      Nonempty (Subgroup.centralizer ({j} : Set X) ≃* DihedralGroup 4))
    (hEven : 2 ∣ Nat.card X) :
    ∃ (S : Sylow 2 X) (j : X), orderOf j = 2 ∧
      j ∈ (S : Subgroup X) ∧
      (∀ s ∈ (S : Subgroup X), s * j = j * s) ∧
      Subgroup.centralizer ({j} : Set X) = (S : Subgroup X) ∧
      Nat.card (S : Subgroup X) = 8 ∧
      Nonempty ((S : Subgroup X) ≃* DihedralGroup 4) := by
  classical
  let S : Sylow 2 X := Classical.choice Sylow.nonempty
  have hS2 : IsPGroup 2 (S : Subgroup X) := S.isPGroup'
  have hSnt : Nontrivial (S : Subgroup X) := by
    have hind : ¬ 2 ∣ S.index := S.not_dvd_index
    have hcard : Nat.card X = Nat.card (S : Subgroup X) * S.index :=
      (Subgroup.card_mul_index (S : Subgroup X)).symm
    have h2 : 2 ∣ Nat.card (S : Subgroup X) * S.index := by
      rw [← hcard]; exact hEven
    have h2S : 2 ∣ Nat.card (S : Subgroup X) := by
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
      · exact h
      · exact absurd h hind
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.card_pos) h2S)
  have hZnt : Nontrivial (Subgroup.center (S : Subgroup X)) := hS2.center_nontrivial
  obtain ⟨jZ, hjZord⟩ :=
    GroupTheory.SuzukiTwoGroup.exists_orderOf_eq_two (S := Subgroup.center (S : Subgroup X))
      (hS2.to_subgroup _)
  let j : X := (jZ : Subgroup.center (S : Subgroup X))
  have hjSord : orderOf (jZ : (S : Subgroup X)) = 2 :=
    (Subgroup.orderOf_coe jZ).trans hjZord
  have hjord : orderOf j = 2 :=
    (Subgroup.orderOf_coe (jZ : (S : Subgroup X))).trans hjSord
  have hjmems : j ∈ (S : Subgroup X) := jZ.1.2
  have hjcenter : ∀ s ∈ (S : Subgroup X), s * j = j * s := by
    intro s hs
    have hcomm : (⟨s, hs⟩ : (S : Subgroup X)) * (jZ : (S : Subgroup X)) =
        (jZ : (S : Subgroup X)) * (⟨s, hs⟩ : (S : Subgroup X)) :=
      Subgroup.mem_center_iff.mp jZ.2 ⟨s, hs⟩
    exact congrArg Subtype.val hcomm
  let C : Subgroup X := Subgroup.centralizer ({j} : Set X)
  obtain ⟨eC⟩ := hcent j hjord
  have hCcard : Nat.card C = 8 := by
    rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
  have hSC : (S : Subgroup X) ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (⟨s, hs⟩ : (S : Subgroup X)) * (jZ : (S : Subgroup X)) =
        (jZ : (S : Subgroup X)) * (⟨s, hs⟩ : (S : Subgroup X)) :=
      Subgroup.mem_center_iff.mp jZ.2 ⟨s, hs⟩
    exact congrArg Subtype.val hcomm
  have hC2 : IsPGroup 2 C := by
    have hD8 : IsPGroup 2 (DihedralGroup 4) := IsPGroup.of_card (n := 3) (by
      rw [DihedralGroup.nat_card]
      norm_num)
    exact hD8.of_equiv eC.symm
  have hSeq : (S : Subgroup X) = C := (S.is_maximal' hC2 hSC).symm
  refine ⟨S, j, hjord, hjmems, hjcenter, hSeq.symm, ?_, ?_⟩
  · rw [hSeq, hCcard]
  · exact ⟨(MulEquiv.subgroupCongr hSeq).trans eC⟩

theorem nat_card_centralizer_swap {n : ℕ} {x y : Fin n} (h : x ≠ y) :
    Nat.card (Subgroup.centralizer ({Equiv.swap x y} : Set (Equiv.Perm (Fin n)))) =
      2 * (n - 2).factorial := by
  have hcyc : (Equiv.swap x y).cycleType = {2} := by
    rw [(Equiv.Perm.isCycle_swap h).cycleType, Equiv.Perm.card_support_swap h]
  rw [Equiv.Perm.nat_card_centralizer, hcyc]
  simp [Nat.mul_comm]

private lemma false_of_mulEquiv_perm_of_swap {X : Type} [Group X] [Finite X]
    {n : ℕ} {x y : Fin n} (hxy : x ≠ y)
    (hcent : ∀ j : X, orderOf j = 2 →
      Nonempty (Subgroup.centralizer ({j} : Set X) ≃* DihedralGroup 4))
    (e : X ≃* Equiv.Perm (Fin n)) (hcard : 2 * (n - 2).factorial ≠ 8) : False := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap x y
  let j : X := e.symm τ
  have hτord : orderOf τ = 2 :=
    (show τ.IsSwap from ⟨x, y, hxy, rfl⟩).orderOf
  have hjord : orderOf j = 2 := by
    rw [← MulEquiv.orderOf_eq e, MulEquiv.apply_symm_apply]
    exact hτord
  obtain ⟨eC⟩ := hcent j hjord
  have hcardX : Nat.card (Subgroup.centralizer ({j} : Set X)) = 8 := by
    rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
  have hmap : Subgroup.map e.toMonoidHom (Subgroup.centralizer ({j} : Set X)) =
      Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n))) := by
    simpa [j] using CFSG.Walter.map_centralizer_singleton_mulEquiv e j
  have hcardτ : Nat.card (Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n)))) = 8 := by
    rw [← hmap, Subgroup.card_map_of_injective e.injective, hcardX]
  rw [nat_card_centralizer_swap hxy] at hcardτ
  exact hcard hcardτ

theorem statedClassicalModel_psl_two_seven_or_nine_of_centralizers {X : Type} [Group X]
    [Finite X] [Nontrivial X]
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hcent : ∀ j : X, orderOf j = 2 →
      Nonempty (Subgroup.centralizer ({j} : Set X) ≃* DihedralGroup 4)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 7 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 3 2 := by
  classical
  have hXodd : ¬ Odd (Nat.card X) := by
    intro hodd
    have htop : (⊤ : Subgroup X) = ⊥ := hO ⊤ inferInstance (by simpa using hodd)
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    apply hab
    have ha : a = 1 := by
      have : a ∈ (⊥ : Subgroup X) := by rw [← htop]; trivial
      simpa using this
    have hb : b = 1 := by
      have : b ∈ (⊥ : Subgroup X) := by rw [← htop]; trivial
      simpa using this
    rw [ha, hb]
  have hEven : 2 ∣ Nat.card X := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hXodd)
  have hO2 : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro N hN hcop
    exact hO N hN (Nat.coprime_two_left.mp hcop)
  obtain ⟨S, j₀, hj₀ord, hj₀mem, hj₀central, hCeqS, hScard, ⟨eS⟩⟩ :=
    sylow_centralizer_data hcent hEven
  have hDihX : GorensteinWalter.HasDihedralSylowTwo X := by
    intro T
    exact ⟨2, by norm_num, ⟨(Sylow.equiv S T).symm.trans eS⟩⟩
  have hD : GorensteinWalter.IsDGroup X := GorensteinWalter.gorensteinWalter X hDihX
  let eQ : (X ⧸ CFSG.pPrimeCore 2 X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (G := X) hO2).trans
      (QuotientGroup.quotientBot (G := X))
  rcases hD with ⟨_, hQ2⟩ | ⟨_, e7⟩ | ⟨_, K, hKpp, L, hLnormal, hLindex, hLmodel⟩
  ·
    have hX2 : IsPGroup 2 X := hQ2.of_equiv eQ
    have hStop : (S : Subgroup X) = ⊤ := by
      have htop2 : IsPGroup 2 (⊤ : Subgroup X) := hX2.of_equiv Subgroup.topEquiv.symm
      exact (S.is_maximal' htop2 le_top).symm
    have hScardX : Nat.card X = 8 := by
      have h : Nat.card (⊤ : Subgroup X) = 8 := by rw [← hStop, hScard]
      simpa using h
    let eX : X ≃* DihedralGroup 4 :=
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hStop.symm)).trans eS
    let c : DihedralGroup 4 := DihedralGroup.sr 0
    have hc2 : c * c = 1 := by decide
    have hc1 : c ≠ 1 := by decide
    have hcord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    let j : X := eX.symm c
    have hjord : orderOf j = 2 := by
      rw [← MulEquiv.orderOf_eq eX, MulEquiv.apply_symm_apply, hcord]
    obtain ⟨eC⟩ := hcent j hjord
    have hCcard : Nat.card (Subgroup.centralizer ({j} : Set X)) = 8 := by
      rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
    have hCtop : Subgroup.centralizer ({j} : Set X) = ⊤ := by
      apply Subgroup.eq_of_le_of_card_ge le_top
      rw [hCcard]
      simpa [hScardX]
    have hjcentral : j ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subgroup.mem_centralizer_singleton_iff.mp (by rw [hCtop]; trivial)
    have hccentral : c ∈ Subgroup.center (DihedralGroup 4) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := eX.surjective y
      have h := (Subgroup.mem_center_iff.mp hjcentral) x
      simpa [j] using congrArg eX h
    have hcnot : c ∉ Subgroup.center (DihedralGroup 4) := by decide
    exact (hcnot hccentral).elim
  ·
    obtain ⟨e7⟩ := e7
    let eX7 : X ≃* alternatingGroup (Fin 7) := eQ.symm.trans e7
    have ha7ord : orderOf (GorensteinWalter.a7t : alternatingGroup (Fin 7)) = 2 :=
      orderOf_eq_prime GorensteinWalter.a7t_involution.2 GorensteinWalter.a7t_involution.1
    let j : X := eX7.symm GorensteinWalter.a7t
    have hjord : orderOf j = 2 := by
      rw [← MulEquiv.orderOf_eq eX7, MulEquiv.apply_symm_apply]
      exact ha7ord
    obtain ⟨eC⟩ := hcent j hjord
    have hcardX : Nat.card (Subgroup.centralizer ({j} : Set X)) = 8 := by
      rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
    have hmapA7 : Subgroup.map eX7.toMonoidHom
        (Subgroup.centralizer ({j} : Set X)) =
        Subgroup.centralizer
          ({GorensteinWalter.a7t} : Set (alternatingGroup (Fin 7))) := by
      simpa [j] using CFSG.Walter.map_centralizer_singleton_mulEquiv eX7 j
    have hcardA7 : Nat.card (Subgroup.centralizer
        ({GorensteinWalter.a7t} : Set (alternatingGroup (Fin 7)))) = 8 := by
      rw [← hmapA7, Subgroup.card_map_of_injective eX7.injective, hcardX]
    rw [GorensteinWalter.a7t_centralizer_card] at hcardA7
    norm_num at hcardA7
  ·
    let L' : Subgroup X := L.map eQ.toMonoidHom
    have hL'normal : L'.Normal := by
      simpa [L'] using (hLnormal.map eQ.toMonoidHom eQ.surjective)
    have hL'index : Odd L'.index := by
      change Odd (L.map eQ.toMonoidHom).index
      rw [Subgroup.index_map]
      have hker : eQ.toMonoidHom.ker = ⊥ :=
        MonoidHom.ker_eq_bot eQ.toMonoidHom eQ.injective
      have hrange : eQ.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr eQ.surjective
      rw [hker, hrange, Subgroup.index_top, mul_one, sup_bot_eq]
      exact hLindex
    let eL' : L ≃* L' := Subgroup.equivMapOfInjective L eQ.toMonoidHom eQ.injective
    have hLmodel' : Nonempty (L' ≃* GorensteinWalter.PSL2 K) ∨
        Nonempty (L' ≃* GorensteinWalter.PGL2 K) := by
      rcases hLmodel with hPSL | hPGL
      · obtain ⟨e⟩ := hPSL
        exact Or.inl ⟨eL'.symm.trans e⟩
      · obtain ⟨e⟩ := hPGL
        exact Or.inr ⟨eL'.symm.trans e⟩
    have hSL' : (S : Subgroup X) ≤ L' :=
      GorensteinWalter.subgroup_le_of_isPGroup_coindex_odd L' hL'normal hL'index S S.isPGroup'
    rcases hLmodel' with hPSL | hPGL
    ·
      obtain ⟨eL⟩ := hPSL
      have hZ : Subgroup.center L' = ⊥ :=
        GorensteinWalter.center_eq_bot_of_mulEquiv eL (GorensteinWalter.psl2_center_eq_bot K)
      have hL'd : GorensteinWalter.HasDihedralSylowTwo L' :=
        GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eL
          (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hKpp)
      have hCL' : Subgroup.centralizer (L' : Set X) = ⊥ :=
        GorensteinWalter.centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
          hDihX hO2 L' hL'normal hZ hL'd
      let jL : L' := ⟨j₀, hSL' hj₀mem⟩
      have hjLord : orderOf jL = 2 := (Subgroup.orderOf_coe jL).symm.trans hj₀ord
      have hCL'jmap : Subgroup.map L'.subtype
          (Subgroup.centralizer ({jL} : Set L')) = (S : Subgroup X) := by
        apply le_antisymm
        · rintro _ ⟨x, hx, rfl⟩
          have hxX : (x : X) ∈ Subgroup.centralizer ({j₀} : Set X) := by
            refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
            have h := Subgroup.mem_centralizer_singleton_iff.mp hx
            exact congrArg Subtype.val h
          rwa [hCeqS] at hxX
        · intro s hs
          have hsL : s ∈ L' := hSL' hs
          refine Subgroup.mem_map.mpr ⟨⟨s, hsL⟩, ?_, rfl⟩
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          apply Subtype.ext
          exact hj₀central s hs
      have hCL'jcard : Nat.card (Subgroup.centralizer ({jL} : Set L')) = 8 := by
        rw [← Subgroup.card_map_of_injective L'.subtype_injective, hCL'jmap, hScard]
      let t : GorensteinWalter.PSL2 K := eL jL
      have htord : orderOf t = 2 := by
        rw [show t = eL jL from rfl, MulEquiv.orderOf_eq, hjLord]
      have hcardt : Nat.card (Subgroup.centralizer
          ({t} : Set (GorensteinWalter.PSL2 K))) = 8 := by
        have hmap : Subgroup.map eL.toMonoidHom
            (Subgroup.centralizer ({jL} : Set L')) =
            Subgroup.centralizer ({t} : Set (GorensteinWalter.PSL2 K)) := by
          simpa [t] using CFSG.Walter.map_centralizer_singleton_mulEquiv eL jL
        rw [← hmap, Subgroup.card_map_of_injective eL.injective, hCL'jcard]
      rcases hKpp with ⟨p, f, hp, hpodd, hf, hKcard⟩
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨hmod1, hmod3⟩ :=
        CFSG.Walter.psl2_centralizer_involution K hKcard hpodd hf htord
      have hqodd : Odd (p ^ f) := hpodd.pow
      have hqmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
        obtain ⟨k, hk⟩ := hqodd
        have hdiv := Nat.div_add_mod (p ^ f) 4
        have hlt : p ^ f % 4 < 4 := Nat.mod_lt _ (by norm_num)
        omega
      have hq : Nat.card K = 7 ∨ Nat.card K = 9 := by
        rcases hqmod with h4 | h4
        · right
          have hc := (hmod1 h4).1
          rw [hcardt] at hc
          have hpos : 0 < p ^ f := pow_pos hp.pos f
          have hq9 : p ^ f = 9 := by omega
          rw [hKcard]; exact hq9
        · left
          have hc := (hmod3 h4).1
          rw [hcardt] at hc
          have hq7 : p ^ f = 7 := by omega
          rw [hKcard]; exact hq7
      rcases hq with hq7 | hq9
      ·
        have hK71 : Nat.card K = 7 ^ 1 := by rw [hq7]; norm_num
        have hOutdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (GorensteinWalter.PSL2 K)) ∣ 2 := by
          have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
            (p := 7) (f := 1) Nat.prime_seven K hK71).1
          simpa using h
        have hIdxDvd : L'.index ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (GorensteinWalter.PSL2 K)) :=
          CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv L'
            (by rw [hCL']; exact bot_le) eL
        have hIdx1 : L'.index = 1 :=
          Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.pow_right 1 (Nat.coprime_two_right.mpr hL'index))
            (by simpa using hIdxDvd.trans hOutdvd)
        have hLtop : L' = ⊤ := Subgroup.index_eq_one.mp hIdx1
        let eXL : X ≃* L' := (Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr hLtop.symm)
        let eX : X ≃* GorensteinWalter.PSL2 K := eXL.trans eL
        have hAdm : CFSG.Open.StatedLieAdmissible CFSG.Open.StatedLieTag.PSL 2 7 1 := by
          refine ⟨Nat.prime_seven, by norm_num, by norm_num, by decide, by decide⟩
        refine Or.inl ⟨hAdm, K, inferInstance, inferInstance, hK71, ⟨eX.trans ?_⟩⟩
        exact CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
      ·
        have hK32 : Nat.card K = 3 ^ 2 := by rw [hq9]; norm_num
        have hOutdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (GorensteinWalter.PSL2 K)) ∣ 4 := by
          have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
            (p := 3) (f := 2) Nat.prime_three K hK32).1
          simpa using h
        have hIdxDvd : L'.index ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (GorensteinWalter.PSL2 K)) :=
          CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv L'
            (by rw [hCL']; exact bot_le) eL
        have hIdx1 : L'.index = 1 :=
          Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hL'index))
            (by
              have h4 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
                  (GorensteinWalter.PSL2 K)) ∣ 2 ^ 2 := by
                simpa using hOutdvd
              exact hIdxDvd.trans h4)
        have hLtop : L' = ⊤ := Subgroup.index_eq_one.mp hIdx1
        let eXL : X ≃* L' := (Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr hLtop.symm)
        let eX : X ≃* GorensteinWalter.PSL2 K := eXL.trans eL
        have hAdm : CFSG.Open.StatedLieAdmissible CFSG.Open.StatedLieTag.PSL 2 3 2 := by
          refine ⟨Nat.prime_three, by norm_num, by norm_num, by decide, by decide⟩
        refine Or.inr ⟨hAdm, K, inferInstance, inferInstance, hK32, ⟨eX.trans ?_⟩⟩
        exact CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
    ·
      obtain ⟨eL⟩ := hPGL
      have hqodd : Odd (Nat.card K) := by
        rcases hKpp with ⟨p, f, hp, hpodd, hf, hcard⟩
        rw [hcard]
        exact hpodd.pow
      obtain ⟨U, s, w, hUcyc, hUcard, hsU, hssq, hsne, hwU, hww, hwinv, hcentU, -⟩ :=
        GorensteinWalter.pgl2_split_torus_centralizer_data K hqodd
      have hsord : orderOf s = 2 := orderOf_eq_prime (by simpa [pow_two] using hssq) hsne
      have hcardSplit : Nat.card (Subgroup.centralizer
          ({s} : Set (GorensteinWalter.PGL2 K))) = 2 * (Nat.card K - 1) := by
        rw [hcentU, CFSG.ABGDGroups.card_sup_zpowers_of_inverts hwU hww hwinv, hUcard]
        omega
      let sL : L' := eL.symm s
      have hsLord : orderOf sL = 2 := by
        rw [← MulEquiv.orderOf_eq eL]
        simp [sL, hsord]
      have hcardL' : Nat.card (Subgroup.centralizer ({sL} : Set L')) =
          2 * (Nat.card K - 1) := by
        have hmap : Subgroup.map eL.toMonoidHom
            (Subgroup.centralizer ({sL} : Set L')) =
            Subgroup.centralizer ({s} : Set (GorensteinWalter.PGL2 K)) := by
          simpa [sL] using CFSG.Walter.map_centralizer_singleton_mulEquiv eL sL
        rw [← Subgroup.card_map_of_injective (f := eL.toMonoidHom) eL.injective, hmap, hcardSplit]
      have hsLXord : orderOf (sL : X) = 2 :=
        (Subgroup.orderOf_coe sL).trans hsLord
      have hCL'leC : Subgroup.map L'.subtype
          (Subgroup.centralizer ({sL} : Set L')) ≤
          Subgroup.centralizer ({(sL : X)} : Set X) := by
        rintro _ ⟨x, hx, rfl⟩
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have h := Subgroup.mem_centralizer_singleton_iff.mp hx
        exact congrArg Subtype.val h
      have hcardLe8 : Nat.card (Subgroup.centralizer ({sL} : Set L')) ≤ 8 := by
        obtain ⟨eC⟩ := hcent (sL : X) hsLXord
        have hcardC : Nat.card (Subgroup.centralizer ({(sL : X)} : Set X)) = 8 := by
          rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
        have h := Subgroup.card_le_of_le hCL'leC
        rw [Subgroup.card_map_of_injective L'.subtype_injective] at h
        omega
      have hqle : Nat.card K ≤ 5 := by
        have h := hcardLe8
        rw [hcardL'] at h
        omega
      have hqge : 3 ≤ Nat.card K := by
        rcases hKpp with ⟨p, f, hp, hpodd, hf, hcard⟩
        have hp3 : 3 ≤ p := by
          have hp2 := hp.two_le
          rcases hpodd with ⟨k, hk⟩
          omega
        have : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by omega) p)
        rw [hcard]; exact this
      have hq35 : Nat.card K = 3 ∨ Nat.card K = 5 := by
        have h1 := hqge
        have h2 := hqle
        interval_cases hK : Nat.card K
        · exact Or.inl rfl
        · norm_num at hqodd
        · exact Or.inr rfl
      rcases hq35 with hq3 | hq5
      ·
        letI : Fintype K := Fintype.ofFinite K
        have h3 : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hq3]
        let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three h3
        obtain ⟨N, hNnormal, hNleL, ⟨eN3⟩⟩ :=
          GorensteinWalter.exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three
            L' hL'normal (eL.trans (GorensteinWalter.pgl2RingEquiv eK).symm)
        let eN : N ≃* GorensteinWalter.PSL2 K :=
          eN3.trans (GorensteinWalter.psl2RingEquiv eK)
        obtain ⟨eA⟩ :=
          CFSG.ClassicalInvolution.Hat2A7.nonempty_psl2_equiv_alternating_four (k := K) hq3
        let eAN : N ≃* alternatingGroup (Fin 4) := eN.trans eA
        have hbij : Function.Bijective
            (MulAut.conjNormal (H := alternatingGroup (Fin 4)) :
              Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4))) :=
          GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
        have hAutA : Nat.card (MulAut (alternatingGroup (Fin 4))) =
            Nat.card (Equiv.Perm (Fin 4)) :=
          (Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv).symm
        have hZ : Subgroup.center N = ⊥ :=
          GorensteinWalter.center_eq_bot_of_mulEquiv eN (GorensteinWalter.psl2_center_eq_bot K)
        have hNd : GorensteinWalter.HasDihedralSylowTwo N :=
          GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eN
            (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hKpp)
        have hCN : Subgroup.centralizer (N : Set X) = ⊥ :=
          GorensteinWalter.centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
            hDihX hO2 N hNnormal hZ hNd
        have hφinj : Function.Injective
            (MulAut.conjNormal (H := N) : X →* MulAut N) := by
          rw [injective_iff_map_eq_one]
          intro x hx
          have hxcent : x ∈ Subgroup.centralizer (N : Set X) := by
            rw [Subgroup.mem_centralizer_iff]
            intro n hn
            have h := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : X)) hx
            rw [MulAut.conjNormal_apply, MulAut.one_apply] at h
            calc n * x = (x * n * x⁻¹) * x := by rw [h]
              _ = x * n := by group
          rw [hCN] at hxcent
          simpa using hxcent
        have hXleAut : Nat.card X ≤ Nat.card (MulAut N) :=
          Nat.card_le_card_of_injective _ hφinj
        have hAutNcard : Nat.card (MulAut N) = Nat.card (Equiv.Perm (Fin 4)) := by
          rw [Nat.card_congr (MulAut.congr eAN).toEquiv, hAutA]
        have hPGLcard : Nat.card (GorensteinWalter.PGL2 K) =
            Nat.card (Equiv.Perm (Fin 4)) := by
          rw [GorensteinWalter.pgl2_card_formula K, hq3, Nat.card_perm]
          norm_num
        have hL'card : Nat.card L' = Nat.card (GorensteinWalter.PGL2 K) :=
          Nat.card_congr eL.toEquiv
        have hAutNcard' : Nat.card (MulAut N) = Nat.card L' := by
          rw [hAutNcard, ← hPGLcard, ← hL'card]
        have hXge : Nat.card L' ≤ Nat.card X := by
          simpa using Subgroup.card_le_of_le (H := L') (K := ⊤) le_top
        have hXcard : Nat.card X = Nat.card (MulAut N) :=
          le_antisymm hXleAut (by rw [hAutNcard']; exact hXge)
        have hφbij : Function.Bijective
            (MulAut.conjNormal (H := N) : X →* MulAut N) :=
          (Nat.bijective_iff_injective_and_card _).mpr ⟨hφinj, by rw [hXcard]⟩
        let eXAut : X ≃* MulAut N := MulEquiv.ofBijective _ hφbij
        let eAutPerm : MulAut (alternatingGroup (Fin 4)) ≃* Equiv.Perm (Fin 4) :=
          (MulEquiv.ofBijective _ hbij).symm
        let eXPerm : X ≃* Equiv.Perm (Fin 4) :=
          eXAut.trans ((MulAut.congr eAN).trans eAutPerm)
        exact (false_of_mulEquiv_perm_of_swap (n := 4) (x := 0) (y := 1) (by decide)
          hcent eXPerm (by norm_num)).elim
      ·
        obtain ⟨N, hNnormal, hNleL, ⟨eN⟩⟩ :=
          GorensteinWalter.exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
            L' hL'normal K hKpp (by rw [hq5]; norm_num) eL
        obtain ⟨eA⟩ :=
          CFSG.ClassicalInvolution.Hat2A7.nonempty_psl2_equiv_alternating_five (k := K) hq5
        let eAN : N ≃* alternatingGroup (Fin 5) := eN.trans eA
        have hbij : Function.Bijective
            (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
              Equiv.Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) :=
          GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
            (by norm_num) (by norm_num)
        have hAutA : Nat.card (MulAut (alternatingGroup (Fin 5))) =
            Nat.card (Equiv.Perm (Fin 5)) :=
          (Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv).symm
        have hZ : Subgroup.center N = ⊥ :=
          GorensteinWalter.center_eq_bot_of_mulEquiv eN (GorensteinWalter.psl2_center_eq_bot K)
        have hNd : GorensteinWalter.HasDihedralSylowTwo N :=
          GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eN
            (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hKpp)
        have hCN : Subgroup.centralizer (N : Set X) = ⊥ :=
          GorensteinWalter.centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
            hDihX hO2 N hNnormal hZ hNd
        have hφinj : Function.Injective
            (MulAut.conjNormal (H := N) : X →* MulAut N) := by
          rw [injective_iff_map_eq_one]
          intro x hx
          have hxcent : x ∈ Subgroup.centralizer (N : Set X) := by
            rw [Subgroup.mem_centralizer_iff]
            intro n hn
            have h := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : X)) hx
            rw [MulAut.conjNormal_apply, MulAut.one_apply] at h
            calc n * x = (x * n * x⁻¹) * x := by rw [h]
              _ = x * n := by group
          rw [hCN] at hxcent
          simpa using hxcent
        have hXleAut : Nat.card X ≤ Nat.card (MulAut N) :=
          Nat.card_le_card_of_injective _ hφinj
        have hAutNcard : Nat.card (MulAut N) = Nat.card (Equiv.Perm (Fin 5)) := by
          rw [Nat.card_congr (MulAut.congr eAN).toEquiv, hAutA]
        have hPGLcard : Nat.card (GorensteinWalter.PGL2 K) =
            Nat.card (Equiv.Perm (Fin 5)) := by
          rw [GorensteinWalter.pgl2_card_formula K, hq5, Nat.card_perm]
          norm_num
        have hL'card : Nat.card L' = Nat.card (GorensteinWalter.PGL2 K) :=
          Nat.card_congr eL.toEquiv
        have hAutNcard' : Nat.card (MulAut N) = Nat.card L' := by
          rw [hAutNcard, ← hPGLcard, ← hL'card]
        have hXge : Nat.card L' ≤ Nat.card X := by
          simpa using Subgroup.card_le_of_le (H := L') (K := ⊤) le_top
        have hXcard : Nat.card X = Nat.card (MulAut N) :=
          le_antisymm hXleAut (by rw [hAutNcard']; exact hXge)
        have hφbij : Function.Bijective
            (MulAut.conjNormal (H := N) : X →* MulAut N) :=
          (Nat.bijective_iff_injective_and_card _).mpr ⟨hφinj, by rw [hXcard]⟩
        let eXAut : X ≃* MulAut N := MulEquiv.ofBijective _ hφbij
        let eAutPerm : MulAut (alternatingGroup (Fin 5)) ≃* Equiv.Perm (Fin 5) :=
          (MulEquiv.ofBijective _ hbij).symm
        let eXPerm : X ≃* Equiv.Perm (Fin 5) :=
          eXAut.trans ((MulAut.congr eAN).trans eAutPerm)
        exact (false_of_mulEquiv_perm_of_swap (n := 5) (x := 0) (y := 1) (by decide)
          hcent eXPerm (by norm_num)).elim

end CFSG
