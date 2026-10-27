module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3RankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Open

theorem comm_of_pow_three_of_card_six {L : Type*} [Group L] [Finite L] (h6 : Nat.card L = 6)
    (a b : L) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 L) := inferInstance
  have hS3 : Nat.card S = 3 := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have h := Subgroup.card_mul_index (S : Subgroup L)
    have hidx := S.not_dvd_index
    rw [hk, h6] at h
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < (S : Subgroup L).index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      nlinarith
    interval_cases k
    · exfalso
      apply hidx
      norm_num at h
      omega
    · simpa using hk
  have hSn : (S : Subgroup L).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have h := Subgroup.card_mul_index (S : Subgroup L)
    rw [hS3, h6] at h
    omega
  have := Sylow.unique_of_normal S hSn
  have hmem : ∀ x : L, x ^ 3 = 1 → x ∈ (S : Subgroup L) := by
    intro x hx
    have hp : IsPGroup 3 (Subgroup.zpowers x) := by
      intro y
      refine ⟨1, ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      apply Subtype.ext
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
    obtain ⟨S', hS'⟩ := hp.exists_le_sylow
    have : S' = S := Subsingleton.elim _ _
    exact this ▸ hS' (Subgroup.mem_zpowers x)
  have hcyc : IsCyclic (S : Subgroup L) := isCyclic_of_prime_card (p := 3) hS3
  have := (IsCyclic.commGroup (α := S)).mul_comm ⟨a, hmem a ha⟩ ⟨b, hmem b hb⟩
  exact congrArg Subtype.val this

variable {Ω : Type*} [Group Ω]

@[expose] def zcl (I : Finset (Subgroup Ω)) : Subgroup Ω :=
  Subgroup.closure {g | ∃ L ∈ I, g ∈ L ∧ g ^ 3 = 1}

theorem isElemAbelian_zcl [Finite Ω] {I : Finset (Subgroup Ω)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hcard : ∀ L ∈ I, Nat.card L = 6) : IsElemAbelian 3 (zcl I) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.isElemAbelian_closure (p := 3) ?_ ?_
  · rintro a ⟨L, hL, haL, ha3⟩ b ⟨L', hL', hbL', hb3⟩
    by_cases hLL : L = L'
    · subst hLL
      have := comm_of_pow_three_of_card_six (hcard L hL) ⟨a, haL⟩ ⟨b, hbL'⟩
        (Subtype.ext (by simpa using ha3)) (Subtype.ext (by simpa using hb3))
      exact congrArg Subtype.val this
    · exact hcomm L hL L' hL' hLL a haL b hbL'
  · rintro a ⟨L, hL, haL, ha3⟩
    exact ha3

theorem le_zcl_of_isPGroup_le_iSup [Finite Ω] {I : Finset (Subgroup Ω)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hcard : ∀ L ∈ I, Nat.card L = 6) {Q : Subgroup Ω} (hQ : IsPGroup 3 Q)
    (hQY : Q ≤ ⨆ L ∈ I, L) : Q ≤ zcl I := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : ∀ J : Finset (Subgroup Ω), J ⊆ I → ∀ y ∈ ⨆ L ∈ J, L, y ^ 2 ∈ zcl I := by
    intro J
    refine Finset.induction_on J ?_ ?_
    · intro _ y hy
      have h1 : y = 1 := by simpa using hy
      rw [h1]
      simp
    · intro L₀ J hL₀J ih hsub y hy
      have hL₀I : L₀ ∈ I := hsub (Finset.mem_insert_self _ _)
      have hJI : J ⊆ I := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hy
      have hcommY : ∀ a ∈ L₀, ∀ b ∈ (⨆ L ∈ J, L : Subgroup Ω), a * b = b * a := by
        intro a ha b hb
        have hle : (⨆ L ∈ J, L : Subgroup Ω) ≤ Subgroup.centralizer ({a} : Set Ω) := by
          refine iSup₂_le fun L hL => fun x hx => ?_
          have hLL : L₀ ≠ L := fun h => hL₀J (h ▸ hL)
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hcomm L₀ hL₀I L (hJI hL) hLL a ha x hx).symm
        have := Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
        exact this.symm
      have hnorm : L₀ ≤ Subgroup.normalizer ((⨆ L ∈ J, L : Subgroup Ω) : Set Ω) := fun a ha => by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hcommY a ha b hb).symm
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L₀ _ hnorm,
        Set.mem_mul] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      have ha6 : a ^ 6 = 1 := by
        have h := pow_card_eq_one' (G := L₀) (x := ⟨a, ha⟩)
        rw [hcard L₀ hL₀I] at h
        simpa using congrArg Subtype.val h
      have ha2 : a ^ 2 ∈ zcl I := by
        refine Subgroup.subset_closure ⟨L₀, hL₀I, L₀.pow_mem ha 2, ?_⟩
        rw [← pow_mul]
        exact ha6
      have hbZ := ih hJI b hb
      have hab := hcommY a ha b hb
      have e : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
        rw [Commute.mul_pow (show Commute a b from hab)]
      rw [e]
      exact (zcl I).mul_mem ha2 hbZ
  intro q hq
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hqk : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
  have hq2 := hsq I (fun x hx => hx) q (hQY hq)
  have hqm : q = ((q ^ 2) ^ m)⁻¹ := by
    have h1 : q ^ (3 ^ k) = (q ^ 2) ^ m * q := by
      rw [hm, pow_succ, pow_mul]
    rw [hqk] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  rw [hqm]
  exact (zcl I).inv_mem ((zcl I).pow_mem hq2 m)

theorem isElemAbelian_of_isPGroup_le_iSup [Finite Ω] {I : Finset (Subgroup Ω)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hcard : ∀ L ∈ I, Nat.card L = 6) {Q : Subgroup Ω} (hQ : IsPGroup 3 Q)
    (hQY : Q ≤ ⨆ L ∈ I, L) : IsElemAbelian 3 Q :=
  CFSG.AGLEmbeddingD2.isElemAbelian_of_le (isElemAbelian_zcl hcomm hcard)
    (le_zcl_of_isPGroup_le_iSup hcomm hcard hQ hQY)


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.PreuniquenessRankFour.Helpers

section MLevel

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

theorem isElemAbelian_of_le_preAutM_iSup (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {X : Subgroup G}
    (hXM : X ≤ M) (hXp : IsPGroup 3 X) (hXY : X ≤ preAutM hU hMN (⨆ L ∈ I, L)) :
    IsElemAbelian 3 X := by
  set ψ : ↥X →* MulAut (IntMod V hU) := (actM hU hMN).comp (Subgroup.inclusion hXM) with hψ
  have hinj : Function.Injective ψ := injective_actM_comp_inclusion hMN hC3 hXM hXp
  have hQp : IsPGroup 3 ψ.range := hXp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hQY : ψ.range ≤ ⨆ L ∈ I, L := by
    rintro _ ⟨x, rfl⟩
    exact ((mem_preAutM hU hMN).1 (hXY x.2)).2
  have hel := isElemAbelian_of_isPGroup_le_iSup (fun L hL L' hL' hne => hI.comm L hL L' hL' hne)
    hcard hQp hQY
  refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · apply congrArg Subtype.val
    apply hinj
    have h := isMulCommutative_iff.mp hel.1 ⟨ψ a, a, rfl⟩ ⟨ψ b, b, rfl⟩
    simpa [map_mul] using congrArg Subtype.val h
  · have h3 : ψ ⟨x, hx⟩ ^ 3 = 1 := hel.2 _ ⟨⟨x, hx⟩, rfl⟩
    have : (⟨x, hx⟩ : ↥X) ^ 3 = 1 := hinj (by rw [map_pow, h3, map_one])
    simpa using congrArg Subtype.val this

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.hasGoodE9_of_le_normal_elemAbelian
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {W Z E X F : Subgroup G} (hWM : W ≤ M)
    (hFW : F ≤ W) (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) (hZW : Z ≤ W)
    (hZel : IsElemAbelian 3 Z) (hZN : W ≤ Subgroup.normalizer (Z : Set G)) (hEZ : E ≤ Z)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEX : E ≤ X) : HasGoodE9 M X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 Z := fun x => ⟨1, Subtype.ext (by simpa using hZel.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hEc : Nat.card E ≤ Nat.card Z := Subgroup.card_le_of_le hEZ
  rw [hE9, hn] at hEc
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hn2' : n = 2
  ·
    have hZE : E = Z := Subgroup.eq_of_le_of_card_ge hEZ (by rw [hE9, hn, hn2']; norm_num)
    have hFN : F ≤ Subgroup.normalizer (Z : Set G) := hFW.trans hZN
    refine h.hasGoodE9_of_normalizes (hZE ▸ hEX) (hZW.trans hWM) hZel ?_ (hFW.trans hWM) hFel hF27
      hFN
    rw [hn, hn2']
    norm_num
  ·
    have h27 : 27 ∣ Nat.card Z := by
      rw [hn]
      exact (show 27 = 3 ^ 3 by norm_num) ▸ pow_dvd_pow 3 (by omega)
    obtain ⟨F', hF'Z, hF'el, hF'27⟩ :=
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.exists_sub_ea_of_dvd
        (isEA3_of_isElemAbelian hZel) (n := 3) (by simpa using h27)
    exact h.hasGoodE9_of_centralizes hEX (hEZ.trans (hZW.trans hWM)) hEel hE9
      ((hF'Z.trans hZW).trans hWM) (isElemAbelian_of_isEA3 hF'el) (by rw [hF'27]; norm_num)
      fun e he f hf => congrArg Subtype.val
        (isMulCommutative_iff.mp hZel.1 ⟨e, hEZ he⟩ ⟨f, hF'Z hf⟩)

theorem D2L34SideCtx3.hasGoodE9_of_le_preAutM_iSup
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    (hYn : ∀ g ∈ autI hU M, ∀ φ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))),
      g * φ * g⁻¹ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))))
    {X : Subgroup G} (hXM : X ≤ M) (hXp : IsPGroup 3 X)
    (hXY : X ≤ preAutM hU hMN (⨆ L ∈ I, L)) (hXc : ¬ IsCyclic X) : HasGoodE9 M X := by
  obtain ⟨W, hWM, hWp, hWidx, hXW⟩ := exists_sylow_le hXM hXp
  have hYn' : ((preAutM hU hMN (⨆ L ∈ I, L)).subgroupOf M).Normal := preAutM_normal hU hMN hYn
  have hYM : preAutM hU hMN (⨆ L ∈ I, L) ≤ M := preAutM_le hU hMN _
  have hMY : M ≤ Subgroup.normalizer ((preAutM hU hMN (⨆ L ∈ I, L) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYn'
  have hZW : W ⊓ preAutM hU hMN (⨆ L ∈ I, L) ≤ W := inf_le_left
  have hZN : W ≤ Subgroup.normalizer ((W ⊓ preAutM hU hMN (⨆ L ∈ I, L) : Subgroup G) : Set G) :=
    fun w hw => mem_normalizer_inf_of_mem_normalizers (Subgroup.le_normalizer hw)
      (hMY (hWM hw))
  have hZel : IsElemAbelian 3 (W ⊓ preAutM hU hMN (⨆ L ∈ I, L) : Subgroup G) :=
    isElemAbelian_of_le_preAutM_iSup hMN hI hcard hC3 (inf_le_left.trans hWM)
      (hWp.to_le inf_le_left) inf_le_right
  obtain ⟨E, hEX, hEel, hE9⟩ := exists_E9_le_of_not_isCyclic hXp hXc
  have hEZ : E ≤ W ⊓ preAutM hU hMN (⨆ L ∈ I, L) := le_inf (hEX.trans hXW) (hEX.trans hXY)
  obtain ⟨F, hFW, hFel, hF27⟩ := h.exists_E27_le_sylow hWM hWp hWidx
  exact h.hasGoodE9_of_le_normal_elemAbelian hWM hFW hFel hF27 hZW hZel hZN hEZ hEel hE9 hEX

end Ctx

end MLevel

end CFSG.LocalAnalysis.RankThreeTheoremC
