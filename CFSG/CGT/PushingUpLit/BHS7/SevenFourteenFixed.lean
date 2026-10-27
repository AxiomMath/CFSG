module

public import CFSG.CGT.PushingUpLit.BHS6.BlockThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.B1 CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender CFSG.SL2MinimalFaithful
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Faithful

variable {W : Type} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F] [CharP F 2]
  {E U : Subgroup (MulAut W)}

omit [CharP F 2] in
theorem sl_fixV_zpowers_eq (D : SLNatData E F) (hUE : U ≤ E) (hcardU : Nat.card U = Nat.card F)
    (hW : Nat.card W = Nat.card U * Nat.card (fixV U)) {u : MulAut W} (hu : u ∈ U) (hu1 : u ≠ 1) :
    fixV (Subgroup.zpowers u) = fixV U := by
  classical
  set e₀ : ↥E := ⟨u, hUE hu⟩ with he₀
  have he₀ne : e₀ ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  set g₀ := D.θ e₀ with hg₀
  have hg₀ne : g₀ ≠ 1 := fun h => he₀ne (D.θ.injective (by rw [← hg₀, h, map_one]))
  let K : Submodule F (Fin 2 → F) :=
    { carrier := {v | (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v = v}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [Matrix.mulVec_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun c v hv => by
        simp only [Set.mem_ofPred_eq] at *
        rw [Matrix.mulVec_smul, hv] }
  have hKne : K ≠ ⊤ := by
    intro h
    apply hg₀ne
    apply eq_one_of_forall_smul_vec
    intro v
    have : v ∈ K := by rw [h]; trivial
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact this
  have hKrank : Module.finrank F K < 2 := by
    have := Submodule.finrank_lt hKne
    simpa [Module.finrank_fin_fun] using this
  have hKcard : Nat.card K ≤ Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    calc Nat.card F ^ Module.finrank F K ≤ Nat.card F ^ 1 :=
          Nat.pow_le_pow_right Nat.card_pos (by omega)
      _ = Nat.card F := pow_one _
  set S : Subgroup W := fixV (Subgroup.zpowers u) with hS
  have huE : Subgroup.zpowers u ≤ E := Subgroup.zpowers_le.mpr (hUE hu)
  have hUz : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.mpr hu
  have hUS : fixV U ≤ S := fixV_le_fixV hUz
  have hkerS : D.β.ker ≤ S := by
    intro w hw
    have : w ∈ fixV E := (D.ker_iff w).mp hw
    exact fixV_le_fixV huE this
  have hSK : ∀ d ∈ S.map D.β, Multiplicative.toAdd d ∈ K := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := D.equivar' e₀ w
    have h2 : (e₀ : MulAut W) w = w := hw u (Subgroup.mem_zpowers u)
    rw [h2] at h1
    show (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (D.β w)) =
      Multiplicative.toAdd (D.β w)
    have := h1.symm
    rwa [Matrix.SpecialLinearGroup.smul_def] at this
  have hmapcard : Nat.card (S.map D.β) ≤ Nat.card F := by
    let ι : S.map D.β → K := fun d =>
      ⟨Multiplicative.toAdd (d : Multiplicative (Fin 2 → F)), hSK d d.2⟩
    have hιinj : Function.Injective ι := by
      intro a b h
      apply Subtype.ext
      exact Multiplicative.toAdd.injective (congrArg (fun k : ↥K => (k : Fin 2 → F)) h)
    exact (Nat.card_le_card_of_injective ι hιinj).trans hKcard
  have hidxS : (S.map D.β).index = S.index := Subgroup.index_map_eq S D.surj hkerS
  have hcardS : Nat.card (S.map D.β) * (S.map D.β).index =
      Nat.card F ^ 2 := by
    rw [Subgroup.card_mul_index, SLNatData.card_dual (F := F)]
  have hSge : Nat.card F ≤ S.index := by
    rw [← hidxS]
    have hFpos : 0 < Nat.card F := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card (S.map D.β) * (S.map D.β).index < Nat.card F * Nat.card F :=
      calc Nat.card (S.map D.β) * (S.map D.β).index
          ≤ Nat.card F * (S.map D.β).index := Nat.mul_le_mul_right _ hmapcard
        _ < Nat.card F * Nat.card F := Nat.mul_lt_mul_of_pos_left hlt hFpos
    rw [hcardS, sq] at this
    exact lt_irrefl _ this
  have hUidx : (fixV U).index = Nat.card U := by
    have h1 : Nat.card (fixV U) * (fixV U).index = Nat.card W := Subgroup.card_mul_index _
    have hpos : 0 < Nat.card (fixV U) := Nat.card_pos
    rw [hW, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hSle : S.index ≤ Nat.card F := by
    have := Nat.le_of_dvd (by rw [hUidx]; exact Nat.card_pos) (Subgroup.index_dvd_of_le hUS)
    rwa [hUidx, hcardU] at this
  have hSeq : S.index = (fixV U).index := by
    rw [hUidx, hcardU]
    exact le_antisymm hSle hSge
  have hcardeq : Nat.card S = Nat.card (fixV U) := by
    have h1 : Nat.card S * S.index = Nat.card W := Subgroup.card_mul_index _
    have h2 : Nat.card (fixV U) * (fixV U).index = Nat.card W := Subgroup.card_mul_index _
    rw [hSeq] at h1
    have hpos : 0 < (fixV U).index := by rw [hUidx]; exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  exact (Subgroup.eq_of_le_of_card_ge hUS hcardeq.le).symm

omit [Finite W] [Finite F] [CharP F 2] in
theorem mem_fixV_zpowers_iff {x : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers x) ↔ x v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite F] [CharP F 2] in
theorem index_fixV_of_card_eq (hW : Nat.card W = Nat.card U * Nat.card (fixV U)) :
    (fixV U).index = Nat.card U := by
  have h1 : Nat.card (fixV U) * (fixV U).index = Nat.card W := Subgroup.card_mul_index _
  have hpos : 0 < Nat.card (fixV U) := Nat.card_pos
  rw [hW, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

omit [CharP F 2] in
theorem sl_fix_iff (D : SLNatData E F) (hUE : U ≤ E) (hcardU : Nat.card U = Nat.card F)
    (hW : Nat.card W = Nat.card U * Nat.card (fixV U)) {u : MulAut W} (hu : u ∈ U) (hu1 : u ≠ 1)
    (w : W) : u w = w ↔ w ∈ fixV U := by
  constructor
  · intro h
    rw [← sl_fixV_zpowers_eq D hUE hcardU hW hu hu1]
    exact mem_fixV_zpowers_iff.mpr h
  · intro h
    exact h u hu

end Faithful

section Ambient

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem block_structure_sl_fixed (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {n : ℕ} (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) :
    (blockW E ⊓ Subgroup.centralizer (baum T : Set Γ)).relIndex (blockW E) = 2 ^ n ∧
      ∀ b ∈ baum T, b ∉ Subgroup.centralizer (blockW E : Set Γ) →
        blockW E ⊓ Subgroup.centralizer ({b} : Set Γ) =
          blockW E ⊓ Subgroup.centralizer (baum T : Set Γ) := by
  classical
  obtain ⟨hBE, hBcard, -⟩ := block_structure_sl hG hT hE hn2 hn
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hJBT : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hJ : thompsonJ T ≤ Subgroup.normalizer (E : Set Γ) := hJBT.trans hBN
  have h6 := six_four_d hG hT hE
  have hWE : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
  rw [hWE] at h6 hBE hBcard ⊢
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hE.perfect
  have hWT : W ≤ T := pCoreOf_le_sylow hG hT hE hT
  have hJW : thompsonJ T ≤ Subgroup.normalizer (W : Set Γ) :=
    hJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hnat : IsNatSL E W n := by
    have := isNatSL_of_isBTBlock hG hT hE hn
    rwa [blockW_eq_pCoreOf hE] at this
  obtain ⟨D⟩ := nonempty_slNatData hWe hEW hperf hnat
  have hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
    by_contra hcon
    apply h6
    have hAc : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.centralizer (W : Set Γ) := fun A hA => by
      by_contra hA'
      exact hcon ⟨A, hA, hA'⟩
    have hJC : thompsonJ T ≤ Subgroup.centralizer (W : Set Γ) :=
      iSup_le fun A => iSup_le fun hA => hAc A hA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw j hj
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hJC hj) w hw
  obtain ⟨A₁, hA₁, hA₁c⟩ := hB
  have hA₁J : A₁ ≤ thompsonJ T := B6.le_thompsonJ hA₁
  have hA₁N : A₁ ≤ Subgroup.normalizer (W : Set Γ) := hA₁J.trans hJW
  have hB₁e : IsElemAbelian2 (autOn A₁ W) := isElemAbelian2_autOn hWe hA₁.2.1 hA₁N
  have hB₁ne : autOn A₁ W ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hA₁N hA₁c
  have hB₁w : Nat.card ↥W ≤ Nat.card ↥(autOn A₁ W) * Nat.card ↥(fixV (autOn A₁ W)) := by
    rw [card_autOn_eq_relIndex hA₁N, card_fixV_autOn_eq hWe hA₁N]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA₁ hWe hWT hA₁N
  have hB₁N : autOn A₁ W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    (autOn_le_autOn W hA₁J).trans (autOn_le_normalizer_autOn hJW hJ)
  obtain ⟨-, hB₁card, -, hB₁W⟩ := sl_core_of_ne_bot D hB₁N hB₁e hB₁ne hB₁w
  have hF2 : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hB₁B : autOn A₁ W ≤ autOn (baum T) W := autOn_le_autOn W (hA₁J.trans hJBT)
  have hUeq : autOn A₁ W = autOn (baum T) W :=
    Subgroup.eq_of_le_of_card_ge hB₁B (by rw [hBcard, hB₁card, hF2])
  rw [hUeq] at hB₁W
  have hcardU : Nat.card ↥(autOn (baum T) W) = Nat.card (GaloisField 2 n) := by
    rw [hBcard, hF2]
  have hfixeq : fixV (autOn (baum T) W) = (Subgroup.centralizer (baum T : Set Γ)).subgroupOf W :=
    fixOn_eq hWe hBW
  refine ⟨?_, ?_⟩
  · have h1 : (W ⊓ Subgroup.centralizer (baum T : Set Γ)).relIndex W =
        ((Subgroup.centralizer (baum T : Set Γ)).subgroupOf W).index := by
      rw [Subgroup.inf_relIndex_left]; rfl
    rw [h1, ← hfixeq, index_fixV_of_card_eq hB₁W, hBcard]
  · intro b hb hbN
    ext w
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hwW, hwb⟩
      refine ⟨hwW, ?_⟩
      have hbn : b ∈ Subgroup.normalizer (W : Set Γ) := hBW hb
      have hu_mem : conjAct W ⟨b, hbn⟩ ∈ autOn (baum T) W :=
        mem_autOn_iff.mpr ⟨⟨b, hbn⟩, hb, rfl⟩
      have hu1 : conjAct W ⟨b, hbn⟩ ≠ 1 := fun h => hbN ((conjAct_eq_one_iff W ⟨b, hbn⟩).mp h)
      have hwfix : conjAct W ⟨b, hbn⟩ ⟨w, hwW⟩ = ⟨w, hwW⟩ := by
        apply Subtype.ext
        rw [conjAct_apply']
        have h1 := Subgroup.mem_centralizer_iff.mp hwb b (Set.mem_singleton b)
        show b * w * b⁻¹ = w
        rw [h1, mul_inv_cancel_right]
      have hmem := (sl_fix_iff D hBE hcardU hB₁W hu_mem hu1 ⟨w, hwW⟩).mp hwfix
      rw [hfixeq] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · rintro ⟨hwW, hwB⟩
      refine ⟨hwW, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subgroup.mem_centralizer_iff.mp hwB h hb

theorem block_structure_three_fixed (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hn : IsNaturalAltModule ↥E 1) :
    (blockW E ⊓ Subgroup.centralizer (baum T : Set Γ)).relIndex (blockW E) = 2 ∧
      ∀ b ∈ baum T, b ∉ Subgroup.centralizer (blockW E : Set Γ) →
        blockW E ⊓ Subgroup.centralizer ({b} : Set Γ) =
          blockW E ⊓ Subgroup.centralizer (baum T : Set Γ) := by
  classical
  have hWE : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
  have h6 := six_four_d hG hT hE
  rw [hWE] at h6 ⊢
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hcard4 : Nat.card ↥W = 4 := by
    obtain ⟨D, -, -, hβbij, -⟩ := block_structure_three hG hT hE hn hWdef hWe
    rw [Nat.card_congr (Equiv.ofBijective D.β hβbij)]
    exact card_coreMod_three'
  have hWT : W ≤ T := pCoreOf_le_sylow hG hT hE hT
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hW2 : IsPGroup 2 ↥W := hT2.to_le hWT
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le (inf_le_left : baum T ≤ T)
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hWne : W ≠ ⊥ := pCoreOf_ne_bot hE (charTwo_of_isBTBlock hG hT hE)
  have hBnc : ¬ baum T ≤ Subgroup.centralizer (W : Set Γ) := by
    intro hle
    apply h6
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw j hj
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hle (B6.thompsonJ_le_baum T hj)) w hw
  obtain ⟨w₀, hw₀W, hw₀1, hw₀fix⟩ := exists_ne_one_fixed_of_isPGroup hW2 hWne hB2 hBW
  have hw₀C : w₀ ∈ Subgroup.centralizer (baum T : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have := hw₀fix p hp
    calc p * w₀ = (p * w₀ * p⁻¹) * p := by group
      _ = w₀ * p := by rw [this]
  have hX : (Subgroup.centralizer (baum T : Set Γ)).relIndex W *
      Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) = 4 := by
    rw [Subgroup.relIndex_mul_card, hcard4]
  have hr1 : (Subgroup.centralizer (baum T : Set Γ)).relIndex W ≠ 1 := by
    intro h
    have hle : W ≤ Subgroup.centralizer (baum T : Set Γ) := Subgroup.relIndex_eq_one.mp h
    apply hBnc
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) b hb).symm
  have hc1 : Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    apply hw₀1
    have : w₀ ∈ Subgroup.centralizer (baum T : Set Γ) ⊓ W := ⟨hw₀C, hw₀W⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hr2 : (Subgroup.centralizer (baum T : Set Γ)).relIndex W = 2 ∧
      Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) = 2 := by
    have hr4 : (Subgroup.centralizer (baum T : Set Γ)).relIndex W ≤ 4 :=
      Nat.le_of_dvd (by norm_num) ⟨_, hX.symm⟩
    generalize (Subgroup.centralizer (baum T : Set Γ)).relIndex W = r at hX hr1 hr4 ⊢
    generalize Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) = c at hX hc1 ⊢
    interval_cases r <;> omega
  refine ⟨?_, ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    exact hr2.1
  · intro b hb hbN
    have hXY : W ⊓ Subgroup.centralizer (baum T : Set Γ) ≤ W ⊓ Subgroup.centralizer ({b} : Set Γ) :=
      inf_le_inf_left W (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    refine (Subgroup.eq_of_le_of_card_ge hXY ?_).symm
    have hs : (Subgroup.centralizer ({b} : Set Γ)).relIndex W *
        Nat.card ↥(Subgroup.centralizer ({b} : Set Γ) ⊓ W) = 4 := by
      rw [Subgroup.relIndex_mul_card, hcard4]
    have hs1 : (Subgroup.centralizer ({b} : Set Γ)).relIndex W ≠ 1 := by
      intro h
      have hle : W ≤ Subgroup.centralizer ({b} : Set Γ) := Subgroup.relIndex_eq_one.mp h
      apply hbN
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp (hle hw) b (Set.mem_singleton b)).symm
    have hYle : Nat.card ↥(Subgroup.centralizer ({b} : Set Γ) ⊓ W) ≤ 2 := by
      generalize (Subgroup.centralizer ({b} : Set Γ)).relIndex W = s at hs hs1
      generalize Nat.card ↥(Subgroup.centralizer ({b} : Set Γ) ⊓ W) = c at hs
      have : s ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨_, hs.symm⟩
      interval_cases s <;> omega
    have hXcard : Nat.card ↥(W ⊓ Subgroup.centralizer (baum T : Set Γ)) = 2 := by
      rw [inf_comm]; exact hr2.2
    have hYc : Nat.card ↥(W ⊓ Subgroup.centralizer ({b} : Set Γ)) ≤ 2 := by
      rw [inf_comm]; exact hYle
    omega

end Ambient

end CFSG.CGT.PushingUpLit.BHS7
