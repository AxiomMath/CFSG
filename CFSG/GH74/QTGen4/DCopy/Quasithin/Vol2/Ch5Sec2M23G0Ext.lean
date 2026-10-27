module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23G0Ext
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23G0
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23H

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem card_eq_128_of_setting_F4 (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) : Nat.card T = 128 := by
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hker := hS.ker_eq
  have hrange := hS.range_eq
  have hTM2 : T ≤ M2 := hS.T_le
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hTs : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM2
  have hcardM2 : Nat.card M2 = 40320 := by
    have h1 := card_map_mul_card_inf hker (le_refl M2)
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hrange, card_alternatingGroup_seven,
      inf_of_le_right hUM2, hU16] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTs.2.1
  have h2 := Subgroup.relIndex_mul_card (H := T) (K := M2)
  rw [inf_of_le_left hTM2, hk, hcardM2, mul_comm] at h2
  rw [hk, eq_seven_of_two_pow_mul_eq h2 hTs.2.2]
  norm_num

theorem isL34FieldExt_m23G0_of_F4
    (hset : Stmt5_2_10_setting_F4) (hfus : M23Fusion3_F4)
    (h515 : Stmt5_2_15_F4) (h527 : Stmt5_2_7_F4) (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ : Subgroup G}
    {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T) :
    IsL34FieldExt (m23G0 M L H B D) T := by
  have h := hyp.toHyp5_0_1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set G1 := L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ K) with hG1def
  set G2 := D ⊔ (sec52S M H ⊓ L) ⊔ K with hG2def
  set G0 := m23G0 M L H B D with hG0def
  have hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2) :=
    hM23.1
  obtain ⟨s, s', hs1, hs2, ht2, ht1, hss, htt, hst⟩ :=
    exists_involutions_m23_of_F4 hset hfus h515 hyp hM23
  have hLie : LieModel ↥G0 .PSL 3 2 2 :=
    lieModel_sup_of_isAmalgamOfGroup hα hs1 hs2 ht2 ht1 hss htt hst

  have hcardG0 : Nat.card G0 = 20160 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hLie]
    decide
  have hsimple : IsSimpleGroup ↥G0 :=
    (CFSG.LieType.Simplicity.fam_classical_converse _
      ((CFSG.Milestones.fam_classical_model_membership_alltags _).2
        ⟨_, _, _, _, CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hLie⟩)).2.2

  have hLM : L ≤ M := h.L_le
  have hTM : T ≤ M := h.T_le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := h.normal
  have hTH : T ≤ H := hyp.hStar.1.1
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoUpper H)
  have hDL : D ≤ L := hyp.notation59.2.1.1.trans inf_le_left
  have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
  have hG1G0 : G1 ≤ G0 := le_sup_left

  have hG0LK : G0 = L ⊔ K := by
    apply le_antisymm
    · exact sup_le (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_left))
        (inf_le_right.trans le_sup_right))
        (sup_le (sup_le (hDL.trans le_sup_left) (inf_le_right.trans le_sup_left)) le_sup_right)
    · exact sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_right)
  have hTN : T ≤ Subgroup.normalizer (G0 : Set G) := fun t ht =>
    mem_normalizer_of_map_conj_eq (by
      rw [hG0LK, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hMN (hTM ht)),
        map_conj_eq_of_mem_normalizer (hHK (hTH ht))])

  have hcardG1 : Nat.card G1 = 960 := card_eq_960_of_isAmalgamOfGroup hα
  have hLG1le : L ≤ G1 := le_sup_left.trans le_sup_left
  have hG1eq : G1 = L ⊔ (B ⊓ K) := by
    rw [hG1def, sup_eq_left.mpr (inf_le_right : sec52S M H ⊓ L ≤ L)]
  have hr : L.relIndex G1 ∣ Nat.card ↥(B ⊓ K) := by
    rw [hG1eq]
    exact relIndex_dvd_card_of_sup ((inf_le_left.trans hBM).trans hMN)
  have hrodd : Odd (L.relIndex G1) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hyp.notation59.1.2.1 (Subgroup.card_dvd_of_le inf_le_left)) hr
  have hcardL : Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.card ↥(pCoreOf 2 L) := by
    have hq : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h.lie]
      exact ordA_one_two_pow (by have := h.two_le; omega)
    rw [card_eq_card_modO2_mul L, hq]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hmul : L.relIndex G1 * Nat.card L = 960 := by
    have h1 := Subgroup.relIndex_mul_card (H := L) (K := G1)
    rwa [inf_of_le_left hLG1le, hcardG1] at h1
  have hr1 : L.relIndex G1 = 1 := by
    set r := L.relIndex G1 with hrdef
    set c := (2 ^ n) ^ 2 - 1 with hcdef
    have hn2 : 2 ≤ n := h.two_le
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hc15 : 15 ≤ c := by
      have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have hcodd : Odd c := Nat.Even.sub_odd (by omega)
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩) odd_one
    have hm : r * (2 ^ n * c * 2 ^ a) = 960 := by rw [← hmul, hcardL, ha]
    have hcd : c ∣ 64 * 15 :=
      ⟨r * 2 ^ n * 2 ^ a, by rw [show 64 * 15 = 960 by norm_num, ← hm]; ring⟩
    have hc64 : Nat.Coprime c 64 :=
      Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr hcodd)
    have hc15' : c = 15 := le_antisymm (Nat.le_of_dvd (by norm_num) (hc64.dvd_of_dvd_mul_left hcd))
      hc15
    have hr64 : r ∣ 64 := by
      refine ⟨2 ^ n * 2 ^ a, ?_⟩
      have : r * (2 ^ n * 2 ^ a) * 15 = 64 * 15 := by
        rw [show 64 * 15 = 960 by norm_num, ← hm, hc15']
        ring
      have h' := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 15) this
      exact h'.symm
    exact Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr hrodd)) hr64
  have hLG1 : L = G1 := le_antisymm hLG1le (Subgroup.relIndex_eq_one.mp hr1)

  obtain ⟨M2, π, hS⟩ := hset G T M L V H B D L₂ n hyp hM23
  have hcardT : Nat.card T = 128 := card_eq_128_of_setting_F4 hQ hyp hM23 hS
  have hTs' : IsSylowTwoOf T (G0 ⊔ T) := isSylowTwoOf_of_isSylowTwo hyp.sylow le_sup_right
  have hr2 : G0.relIndex (G0 ⊔ T) = 2 := by
    have hrd : G0.relIndex (G0 ⊔ T) ∣ 2 ^ 7 := by
      have := relIndex_dvd_card_of_sup hTN
      rwa [hcardT] at this
    obtain ⟨i, hi7, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrd
    have hc1 := Subgroup.relIndex_mul_card (H := G0) (K := G0 ⊔ T)
    rw [inf_of_le_left le_sup_left, hcardG0, hi] at hc1
    have hc2 := Subgroup.relIndex_mul_card (H := T) (K := G0 ⊔ T)
    rw [inf_of_le_left le_sup_right, hcardT] at hc2
    have hodd : ¬ 2 ∣ T.relIndex (G0 ⊔ T) := hTs'.2.2
    have key : 2 ^ i * 20160 = T.relIndex (G0 ⊔ T) * 128 := hc1.trans hc2.symm
    rw [hi]
    interval_cases i <;> first | rfl | (norm_num at key; omega)

  obtain ⟨F, hFf, hFfin, hF4, ⟨e₀⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have hF : Nat.card F = 4 := by rw [hF4]; norm_num
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF4])
  obtain ⟨t, htT, htG0⟩ : ∃ t ∈ T, t ∉ G0 := by
    by_contra hcon
    push Not at hcon
    have h1 : G0 ⊔ T = G0 := sup_eq_left.mpr hcon
    rw [h1, Subgroup.relIndex_self] at hr2
    norm_num at hr2

  have htN : t ∈ Subgroup.normalizer (G0 : Set G) := hTN htT
  set ct : MulAut ↥G0 := ((MulAut.conj t).subgroupMap G0).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer htN)) with hctdef
  have hct : ∀ x : ↥G0, ((ct x : ↥G0) : G) = t * x * t⁻¹ := fun x => rfl
  set α : MulAut (LinearFlag.projectiveSL 3 F) := (e₀.symm.trans ct).trans e₀ with hαdef
  have hαe : ∀ x : ↥G0, α (e₀ x) = e₀ (ct x) := fun x => by simp [hαdef]

  have hG1par : G1.subgroupOf G0 ∈ LinearFlag.maximalParabolics ↥G0 2 :=
    mem_maximalParabolics_of_isAmalgamOfGroup hα hs1 hs2 ht2 ht1 hss htt hst
  have hP := map_mem_maximalParabolics e₀ hG1par
  have hctG1 : (G1.subgroupOf G0).map ct.toMonoidHom = G1.subgroupOf G0 := by
    have htG1 : t ∈ Subgroup.normalizer (G1 : Set G) := hLG1 ▸ hMN (hTM htT)
    have hle : (G1.subgroupOf G0).map ct.toMonoidHom ≤ G1.subgroupOf G0 := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ G1 := Subgroup.mem_subgroupOf.mp hy
      exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp htG1 _).mp hy')
    have hinj : Function.Injective ct.toMonoidHom := ct.injective
    exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hinj).ge
  have hαfix : ((G1.subgroupOf G0).map e₀.toMonoidHom).map α.toMonoidHom =
      (G1.subgroupOf G0).map e₀.toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : α.toMonoidHom.comp e₀.toMonoidHom = e₀.toMonoidHom.comp ct.toMonoidHom := by
      ext x
      exact hαe x
    rw [hcomp, ← Subgroup.map_map, hctG1]
  obtain ⟨A, σ, hασ⟩ := exists_conjAut_mul_fieldAut_of_map_eq hP α hαfix

  have hσ : σ ≠ RingEquiv.refl F := by
    intro hσ1
    have hα' : α = LinearFlag.conjAut 3 F A := by
      rw [hασ, hσ1]
      have h1 : LinearFlag.fieldAut 3 F (RingEquiv.refl F) = 1 := map_one (LinearFlag.fieldAut 3 F)
      rw [h1, mul_one]
    obtain ⟨k, hk⟩ := hyp.sylow.1 ⟨t, htT⟩
    have htk : t ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hpowct : ∀ m : ℕ, ∀ x : ↥G0, (((ct ^ m) x : ↥G0) : G) = t ^ m * x * (t ^ m)⁻¹ := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, hct]
        group
    have hctk : ct ^ (2 ^ k) = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hpowct, htk, one_mul, inv_one, mul_one, MulAut.one_apply]
    have hpowα : ∀ m : ℕ, ∀ z, (α ^ m) z = e₀ ((ct ^ m) (e₀.symm z)) := by
      intro m
      induction m with
      | zero => intro z; simp
      | succ m ih =>
        intro z
        rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
        simp [hαdef]
    have hαk : LinearFlag.conjAut 3 F A ^ (2 ^ k) = 1 := by
      rw [← hα']
      ext z
      rw [hpowα, hctk, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]
    obtain ⟨y, hy⟩ := exists_conj_of_conjAut_pow_eq_one hF A hαk
    set g : ↥G0 := e₀.symm y with hgdef
    have hctx : ∀ x : ↥G0, ct x = g * x * g⁻¹ := by
      intro x
      apply e₀.injective
      rw [← hαe, hα', hy, MulAut.conj_apply, map_mul, map_mul, map_inv, hgdef,
        MulEquiv.apply_symm_apply]
    have hz : ∀ x ∈ G0, ((g : G)⁻¹ * t) * x * ((g : G)⁻¹ * t)⁻¹ = x := by
      intro x hx
      have e := congrArg Subtype.val (hctx ⟨x, hx⟩)
      rw [hct] at e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
      calc (g : G)⁻¹ * t * x * ((g : G)⁻¹ * t)⁻¹ = (g : G)⁻¹ * (t * x * t⁻¹) * g := by group
        _ = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g := by rw [e]
        _ = x := by group
    have hnab : ∃ Y : Subgroup ↥G0, Y ≠ ⊥ ∧ Y ≠ ⊤ := by
      refine ⟨G1.subgroupOf G0, fun hb => ?_, hG1par.1.1⟩
      have h1 : Nat.card ↥(G1.subgroupOf G0) = 960 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG1G0).toEquiv, hcardG1]
      rw [hb, Subgroup.card_bot] at h1
      norm_num at h1
    have hO2 : pCoreOf 2 (L ⊔ T) ≤ G0 := by
      obtain ⟨-, ⟨h72, -, -, -, -, -⟩, ⟨h73, -⟩⟩ := h527 G T M L V H B D L₂ n hyp
      have hLBD : L ⊔ B ⊔ D = L := by
        rw [← h72]
        exact hLG1.symm
      rw [← hLBD, ← h73]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (hLG1le.trans hG1G0)
    have hmem := mem_of_commute_of_relIndex_eq_two hnab hTN hr2
      ⟨hTs'.1, hTs'.2.1, hTs'.2.2⟩ (hLG1le.trans hG1G0) hO2
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((le_sup_left : G0 ≤ G0 ⊔ T) g.2))
        ((le_sup_right : T ≤ G0 ⊔ T) htT)) hz
    apply htG0
    have e : t = (g : G) * ((g : G)⁻¹ * t) := by group
    rw [e]
    exact G0.mul_mem g.2 hmem
  refine ⟨hTN, hr2, F, hFf, hFfin, hF, e₀, t, A, σ, htT, hσ, fun x y hxy => ?_⟩
  have hy : y = ct x := Subtype.ext (by rw [hct]; exact hxy)
  rw [hy, ← hαe, hασ, MulAut.mul_apply]

theorem stmt5_2_16_of_F4
    (hset : Stmt5_2_10_setting_F4) (hfus : M23Fusion3_F4) (h515 : Stmt5_2_15_F4)
    (h527 : Stmt5_2_7_F4) (hQ : Stmt5_2_8_Q_F4) : Stmt5_2_16_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hM23
  exact ⟨lieModel_m23G0_of_F4 hset hfus h515 hyp hM23,
    isL34FieldExt_m23G0_of_F4 hset hfus h515 h527 hQ hyp hM23⟩

end CFSG.Quasithin.H13
