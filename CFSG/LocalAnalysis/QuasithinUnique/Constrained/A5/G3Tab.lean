module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25C
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {K L : Subgroup G} {z : G}

theorem Kc3Group.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : Kc3Group X) :
    Kc3Group Y := by
  rcases h with ⟨f, hf, hm | hm⟩ | ⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩⟩ | hm |
    ⟨n, hn, hm⟩ | ⟨s, hs, hm⟩
  · exact Or.inl ⟨f, hf, Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hm)⟩
  · exact Or.inl ⟨f, hf, Or.inr (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hm)⟩
  · exact Or.inr (Or.inl ⟨f, Or.inl ⟨hf, chevalleyExceptionalModel_of_mulEquiv e hm⟩⟩)
  · exact Or.inr (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, chevalleyExceptionalModel_of_mulEquiv e hm⟩)⟩)
  · exact Or.inr (Or.inl ⟨f, Or.inr (Or.inr ⟨hodd, hf, reeTitsModel_of_mulEquiv e hm⟩)⟩)
  · exact Or.inr (Or.inr (Or.inl (reeTitsModel_of_mulEquiv e hm)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
      CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, isoInv_spor s X Y e hm⟩)))

theorem card_of_psu_three_three {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem card_of_psl_three_three {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 3 1) : Nat.card X = 5616 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three h

theorem card_of_psl_three_two' {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem false_of_fusionIsBenderGroup (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (h : fusionIsBenderGroup ↥K) : False := by
  obtain ⟨q, k, hB⟩ := Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup h
  obtain ⟨Ub, hU1, hUe, -, hnorm, hns⟩ := exists_blockU_K_alt5 hs hL hLK
  exact Lin2.false_of_benderBorel hB hU1 (Lin2.OddRank.isPGroup_two_of_isElemAbelian hUe) hnorm hns

theorem false_of_psl_two_odd
    (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K) {p : ℕ}
    (hp : IsFermatOrMersennePrime p)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp.1 le_rfl hF
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact Lin2.OddRank.ne_two_of_fermat_or_mersenne hp
  obtain ⟨Ub, -, hUe, hcard, -, -⟩ := exists_blockU_K_alt5 hs hL hLK
  have h4 : Nat.card (Ub.map e.toMonoidHom) ≤ 4 :=
    Lin2.card_le_four_psl2 hF2 (Lin2.isElemAbelian_map' hUe e.toMonoidHom)
  have h5 : Nat.card (Ub.map e.toMonoidHom) = Nat.card Ub :=
    Lin2.card_map_of_inf_ker_eq_bot Ub e.toMonoidHom fun x _ hx =>
      e.injective ((show e x = 1 from hx).trans (map_one e).symm)
  omega

omit [Finite G] in
theorem center_eq_bot_of_simple (hq : CFSG.IsQuasisimple ↥K) (hs : IsSimpleGroup ↥K) :
    Subgroup.center ↥K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp hx y).symm

theorem center_eq_pCore_of_simple_quotient (hq : CFSG.IsQuasisimple ↥K) {X : Type} [Group X]
    [IsSimpleGroup X] (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) :
    Subgroup.center ↥K = CFSG.pCore 2 ↥K := by
  refine le_antisymm ?_ (Lin2.OddRank.pCore_le_center hq)
  have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e.isSimpleGroup
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hN : ((Subgroup.center ↥K).map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center ↥K).map π) with h | h
  · intro x hx
    have hmem : π x ∈ (Subgroup.center ↥K).map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    have hcenter : Subgroup.center ↥K = ⊤ := by
      refine eq_top_iff.mpr fun k _ => ?_
      have hk : π k ∈ (Subgroup.center ↥K).map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hck⟩ := hk
      have hn : c⁻¹ * k ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.mp hck
      have hz : c⁻¹ * k ∈ Subgroup.center ↥K := Lin2.OddRank.pCore_le_center hq hn
      have : k = c * (c⁻¹ * k) := by group
      rw [this]
      exact Subgroup.mul_mem _ hc hz
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ Subgroup.center ↥K := hcenter ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp hx y).symm

theorem kc3Group_of_charTwoLie (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (h : SQTKCharTwoLie ↥K) : Kc3Group ↥K := by
  have h64 := two_pow_six_dvd_card_of_le hs hL hLK
  have hB := false_of_fusionIsBenderGroup hs hL hLK
  unfold Kc3Group
  rcases h with ((⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hodd, hf3, hm⟩ | ⟨hodd, hf3, hm⟩⟩ | hT) | ⟨n, hn, hm⟩)
  · exact (hB (K1.fusionIsBenderGroup_of_stated_psl_two hf hm)).elim
  · by_cases hf2 : 2 ≤ f
    · exact Or.inl ⟨f, hf2, Or.inl hm⟩
    · have hf1 : f = 1 := by omega
      subst hf1
      rw [card_of_psl_three_two' hm] at h64
      omega
  · exact (hB (K1.fusionIsBenderGroup_of_stated_psu_three hf hm)).elim
  · exact Or.inl ⟨f, hf, Or.inr hm⟩
  · exact Or.inr (Or.inl ⟨f, Or.inl ⟨hf, hm⟩⟩)
  · exact Or.inr (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)
  · exact Or.inr (Or.inl ⟨f, Or.inr (Or.inr ⟨hodd, hf3, hm⟩)⟩)
  · exact (hB (K1.fusionIsBenderGroup_of_suzukiModel hm)).elim
  · exact Or.inr (Or.inr (Or.inl hT))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hm⟩)))

theorem kc3Group_of_lemma115LieCharTwo (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (h : Lemma115LieCharTwo ↥K) : Kc3Group ↥K := by
  have h64 := two_pow_six_dvd_card_of_le hs hL hLK
  rcases h with h | h | hU
  · exact kc3Group_of_charTwoLie hs hL hLK h
  · exfalso
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Id2519.card_alternatingGroup_six] at h64
    omega
  · exfalso
    rw [card_of_psu_three_three hU] at h64
    omega

theorem tab_of_caseA (hq : CFSG.IsQuasisimple ↥K) (hs : IsShort2 L) (hL : IsAltType L 5)
    (hLK : L ≤ K) (h : Lemma115CaseA K z) :
    Kc3Group (↥K ⧸ Subgroup.center ↥K) ∧ IsPGroup 2 ↥(Subgroup.center ↥K) := by
  obtain ⟨hsimple, hlie, -⟩ := h
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple hq hsimple
  refine ⟨?_, ?_⟩
  · let e : ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact Kc3Group.of_mulEquiv e (kc3Group_of_lemma115LieCharTwo hs hL hLK hlie)
  · rw [hZ]
    exact fun x => ⟨0, Subsingleton.elim _ _⟩

omit [Finite G] in
theorem tab_of_caseB (h : Lemma115CaseB K z) :
    Kc3Group (↥K ⧸ Subgroup.center ↥K) ∧ IsPGroup 2 ↥(Subgroup.center ↥K) := by
  obtain ⟨-, hc, hm, -⟩ := h
  refine ⟨?_, ?_⟩
  · let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ Subgroup.center ↥K) :=
      QuotientGroup.quotientMulEquivOfEq hc.symm
    unfold Kc3Group
    rcases hm with hm | hm
    · exact Or.inl ⟨2, le_rfl,
        Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hm)⟩
    · exact Or.inr (Or.inl ⟨2, Or.inl ⟨le_rfl, chevalleyExceptionalModel_of_mulEquiv e hm⟩⟩)
  · rw [hc]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥K)

omit [Finite G] in
theorem false_of_caseC (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (h : Lemma115CaseC K z) : False := by
  obtain ⟨φ, σ, hc, -⟩ := h
  have h64 := two_pow_six_dvd_card_of_le hs hL hLK
  have hq : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := by
    rw [Nat.card_congr φ.toEquiv]
    exact Id2519.card_alternatingGroup_six
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
  rw [hq] at hK
  rcases hc with hc | hc <;> rw [hc] at hK <;> rw [hK] at h64 <;> omega

omit [Finite G] in
theorem false_of_caseD (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (h : Lemma115CaseD K z) : False := by
  obtain ⟨φ, σ, hc, -⟩ := h
  have h64 := two_pow_six_dvd_card_of_le hs hL hLK
  have hq : Nat.card (↥K ⧸ Subgroup.center ↥K) = 2520 := by
    rw [Nat.card_congr φ.toEquiv]
    exact Id2519.card_alternatingGroup_seven
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
  rw [hq] at hK
  rcases hc with hc | hc <;> rw [hc] at hK <;> rw [hK] at h64 <;> omega

theorem false_of_caseE
    (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (h : Lemma115CaseE K z) : False := by
  obtain ⟨h | ⟨p, hp, h⟩, -⟩ := h
  · have h64 := two_pow_six_dvd_card_of_le hs hL hLK
    rw [card_of_psl_three_three h] at h64
    omega
  · exact false_of_psl_two_odd hs hL hLK hp h

@[expose] def TabKc3J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L : Subgroup G), CFSG.IsQuasisimple ↥K →
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.Carrier .J2) → L ≤ K → IsShort2 L →
    IsAltType L 5 → False

theorem tab_of_caseF
    (hJ2 : TabKc3J2) (hq : CFSG.IsQuasisimple ↥K) (hs : IsShort2 L)
    (hL : IsAltType L 5) (hLK : L ≤ K) (h : Lemma115CaseF K z) :
    Kc3Group (↥K ⧸ Subgroup.center ↥K) ∧ IsPGroup 2 ↥(Subgroup.center ↥K) := by
  obtain ⟨⟨s, hs', ⟨e⟩⟩, -⟩ := h
  obtain ⟨hsimple, -⟩ := Id2519.sporadic_data hs'
  have := hsimple
  have hcen : Subgroup.center ↥K = CFSG.pCore 2 ↥K := center_eq_pCore_of_simple_quotient hq e
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥K) := by
    rw [hcen]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  refine ⟨?_, hZ⟩
  have e' : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.Carrier s :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans e
  unfold Kc3Group
  rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exfalso
    have h960 := nineSixty_dvd_card_quot hs hL hLK hZ
    have h7920 : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
    rw [Nat.card_congr e'.toEquiv, h7920] at h960
    omega
  ·
    exfalso
    obtain ⟨H, n, hn, hH⟩ := exists_subgroup_card_quot hs hL hLK hZ
    exact false_of_m12 e' hn hH
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M22, Or.inl rfl, ⟨e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M23, Or.inr (Or.inl rfl), ⟨e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M24, Or.inr (Or.inr (Or.inl rfl)), ⟨e'⟩⟩)))
  · exact (hJ2 G K L hq ⟨e⟩ hLK hs hL).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.J4, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      ⟨e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.HS, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      ⟨e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.He,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), ⟨e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.Ru,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), ⟨e'⟩⟩)))

theorem tabKc3_of
    (hJ2 : TabKc3J2) : TabKc3 := by
  intro G _ _ K L z hq hcases hLK hs hL
  rcases hcases with hA | hB | hC | hD | hE | hF
  · exact tab_of_caseA hq hs hL hLK hA
  · exact tab_of_caseB hB
  · exact (false_of_caseC hs hL hLK hC).elim
  · exact (false_of_caseD hs hL hLK hD).elim
  · exact (false_of_caseE hs hL hLK hE).elim
  · exact tab_of_caseF hJ2 hq hs hL hLK hF

end CFSG.QuasithinUnique.A5.G3
