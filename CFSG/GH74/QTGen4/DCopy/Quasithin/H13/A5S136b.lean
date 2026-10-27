module

public import CFSG.Quasithin.H13.A5S136b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S135
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem rParam_eq_three_F4 (h137 : Thm13_6_7_F4) (h1336 : Input1336_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) : rParam V = 3 := by
  apply le_antisymm
  · have hG1 : ¬ Subgroup.centralizer (S.V1 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
      rw [S.centralizer_V1]
      exact fun h => h1336 G T L V S (h.trans S.NV_le_M)
    have h := rParam_le_mQuot S.V1_le_V hG1
    rw [S.mQuot_V_V1] at h
    exact_mod_cast h
  · refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hC⟩ := hU
    by_contra hlt
    push Not at hlt
    have hm3 : mQuot V U < 3 := by exact_mod_cast hlt
    have hm : mQuot V U ≤ 2 := by omega

    have hcard := card_eq_two_pow_mul S.isPGroup_V hUV
    rw [S.card_V] at hcard
    have h4 : 4 ≤ Nat.card U := by
      have : 2 ^ mQuot V U ≤ 4 := (Nat.pow_le_pow_right (by norm_num) hm).trans (by norm_num)
      have hpos : 0 < Nat.card U := Nat.card_pos
      nlinarith
    obtain ⟨u, huU, hu1, hu⟩ := S.exists_nonsing_of_four_le hUV h4
    apply hC
    refine le_trans (Subgroup.centralizer_le ?_) (S.centralizer_le_of_nonsing_F4 h137 hab u hu1 hu)
    rw [Set.singleton_subset_iff]
    exact huU

theorem comm_of_mQuot_le_two_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hAT : A ≤ T)
    (hAV : A ≤ conjSubgroup V g) {x : G} (hx : x ∈ V)
    (hm : mQuot (conjSubgroup V g) (A ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 2) :
    ∀ a ∈ A, a * x = x * a := by
  set B := A ⊓ Subgroup.centralizer ({x} : Set G) with hBdef
  have hBV : B ≤ conjSubgroup V g := inf_le_left.trans hAV

  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer (conjSubgroup V g : Set G) := by
    by_contra hcon
    have h1 := rParam_le_mQuot hBV hcon
    rw [rParam_conj, hr] at h1
    have h2 : 3 ≤ mQuot (conjSubgroup V g) B := by exact_mod_cast h1
    omega
  have hxB : x ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hb).2
  have hxN := hCB hxB
  have hAV' : A ≤ conjSub g⁻¹ V := hAV
  intro a ha

  have hcV : ⁅x, a⁆ ∈ V := by
    rw [commutatorElement_def]
    have h1 : a * x⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (S.frame.T_le (hAT ha)) x⁻¹).mp (V.inv_mem hx)
    have h2 : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [h2]
    exact V.mul_mem hx h1
  have hcVg : ⁅x, a⁆ ∈ conjSubgroup V g := by
    rw [commutatorElement_def]
    have h1 : x * a * x⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.mp hxN a).mp (hAV ha)
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem (hAV ha))
  by_contra hne
  have hc1 : ⁅x, a⁆ ≠ 1 := fun h =>
    hne (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hne' : V ⊓ conjSub g⁻¹ V ≠ ⊥ := by
    intro h
    apply hc1
    have : ⁅x, a⁆ ∈ V ⊓ conjSub g⁻¹ V := ⟨hcV, hcVg⟩
    rw [h] at this
    exact (Subgroup.mem_bot).mp this
  have hcomm := S.lemma_13_6_24_two_F4 h137 h1326 hab hg hne'
  have := Subgroup.commutator_mem_commutator hx (hAV' ha)
  rw [hcomm] at this
  exact hc1 (Subgroup.mem_bot.mp this)

theorem false_of_pair_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hAT : A ≤ T)
    (hAV : A ≤ conjSubgroup V g) (hmA : mQuot (conjSubgroup V g) A ≤ 1) {x : G} (hx : x ∈ V)
    (hmove : ∃ a ∈ A, a * x ≠ x * a)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a * x ≠ x * a → b * x ≠ x * b → a * b * x = x * (a * b)) :
    False := by
  set C := A ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have hCA : C ≤ A := inf_le_left
  have hmem : ∀ a ∈ A, a ∈ C ↔ a * x = x * a := fun a ha => by
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact and_iff_right ha
  have h1 : mQuot A C ≤ 1 := mQuot_le_one_of_pair hCA fun a ha b hb haC hbC => by
    rw [hmem a ha] at haC
    rw [hmem b hb] at hbC
    rw [hmem (a * b) (A.mul_mem ha hb)]
    exact hpair a ha b hb haC hbC
  have h2 : mQuot (conjSubgroup V g) C ≤ 2 := by
    rw [mQuot_add hCA hAV]
    omega
  obtain ⟨a, ha, hax⟩ := hmove
  exact hax (S.comm_of_mQuot_le_two_F4 h137 h1326 hab hr hg hAT hAV hx h2 a ha)

theorem wClos_le_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) {i : ℕ} (hi : i ≤ 1) :
    wClos V i T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAV, hmA⟩ := hA
  refine le_inf hAT ?_
  by_cases hgN : g ∈ Subgroup.normalizer (V : Set G)
  ·
    have hVg : conjSubgroup V g = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hgN)
    rw [hVg] at hAV
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := S.elemAbelian_V.1.is_comm.comm ⟨v, hv⟩ ⟨a, hAV ha⟩
    exact congrArg Subtype.val this
  ·
    have hmA' : mQuot (conjSubgroup V g) A ≤ 1 := by rw [hmA]; exact hi
    by_contra hAC
    have hNT : ∀ a ∈ A, a ∈ Subgroup.normalizer (V : Set G) := fun a ha =>
      S.frame.T_le (hAT ha)
    have hD : ∀ a (ha : a ∈ A), InD (S.frame.ρ ⟨a, hNT a ha⟩) := fun a ha =>
      S.frame.T_D ⟨a, hNT a ha⟩ (hAT ha)
    have hρmul : ∀ a (ha : a ∈ A) b (hb : b ∈ A),
        S.frame.ρ ⟨a * b, hNT _ (A.mul_mem ha hb)⟩ =
          S.frame.ρ ⟨a, hNT a ha⟩ * S.frame.ρ ⟨b, hNT b hb⟩ := fun a ha b hb =>
      map_mul S.frame.ρ ⟨a, hNT a ha⟩ ⟨b, hNT b hb⟩

    let x₁ : ↥V := S.frame.ψ.symm E12
    let x₂ : ↥V := S.frame.ψ.symm E04
    let x₃ : ↥V := S.frame.ψ.symm E02
    have hx₁ : S.frame.ψ x₁ = E12 := S.frame.ψ.apply_symm_apply E12
    have hx₂ : S.frame.ψ x₂ = E04 := S.frame.ψ.apply_symm_apply E04
    have hx₃ : S.frame.ψ x₃ = E02 := S.frame.ψ.apply_symm_apply E02
    have hc : ∀ a (ha : a ∈ A) (x : ↥V),
        a * (x : G) = x * a ↔ pact (S.frame.ρ ⟨a, hNT a ha⟩) (S.frame.ψ x) = S.frame.ψ x :=
      fun a ha x => S.comm_iff_pact (hNT a ha) x
    by_cases hP1 : ∃ a ∈ A, a * (x₁ : G) ≠ x₁ * a
    · refine S.false_of_pair_F4 h137 h1326 hab hr hgN hAT hAV hmA' x₁.2 hP1 ?_
      intro a ha b hb hax hbx
      rw [Ne, hc a ha, hx₁] at hax
      rw [Ne, hc b hb, hx₁] at hbx
      rw [hc (a * b) (A.mul_mem ha hb), hx₁, hρmul a ha b hb]
      exact dPair_E12 _ _ (hD a ha) (hD b hb) hax hbx
    push Not at hP1
    have hf1 : ∀ a (ha : a ∈ A), pact (S.frame.ρ ⟨a, hNT a ha⟩) E12 = E12 := fun a ha => by
      rw [← hx₁, ← hc a ha]
      exact hP1 a ha
    by_cases hP2 : ∃ a ∈ A, a * (x₂ : G) ≠ x₂ * a
    · refine S.false_of_pair_F4 h137 h1326 hab hr hgN hAT hAV hmA' x₂.2 hP2 ?_
      intro a ha b hb hax hbx
      rw [Ne, hc a ha, hx₂] at hax
      rw [Ne, hc b hb, hx₂] at hbx
      rw [hc (a * b) (A.mul_mem ha hb), hx₂, hρmul a ha b hb]
      exact dPair2 _ _ (hf1 a ha) (hf1 b hb) (hD a ha) (hD b hb) hax hbx
    push Not at hP2
    have hf2 : ∀ a (ha : a ∈ A), pact (S.frame.ρ ⟨a, hNT a ha⟩) E04 = E04 := fun a ha => by
      rw [← hx₂, ← hc a ha]
      exact hP2 a ha

    have hP3 : ∃ a ∈ A, a * (x₃ : G) ≠ x₃ * a := by
      obtain ⟨a, ha, haV⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
      refine ⟨a, ha, fun h3 => haV ?_⟩
      have h3' := (hc a ha x₃).mp h3
      rw [hx₃] at h3'
      have hρ1 := dFix _ (hD a ha) (hf1 a ha) (hf2 a ha) h3'
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := (hc a ha ⟨v, hv⟩).mpr (by rw [hρ1, map_one, MulAut.one_apply])
      exact this.symm
    refine S.false_of_pair_F4 h137 h1326 hab hr hgN hAT hAV hmA' x₃.2 hP3 ?_
    intro a ha b hb hax hbx
    rw [Ne, hc a ha, hx₃] at hax
    rw [Ne, hc b hb, hx₃] at hbx
    rw [hc (a * b) (A.mul_mem ha hb), hx₃, hρmul a ha b hb]
    exact dPair3 _ _ (hf1 a ha) (hf1 b hb) (hf2 a ha) (hf2 b hb) (hD a ha) (hD b hb) hax hbx

theorem one_lt_wParam_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) : 1 < wParam T V := by
  have h := le_wParam_of_wClos_le (n := 2) (T := T) (V := V) fun j hj =>
    S.wClos_le_F4 h137 h1326 hab hr (by omega)
  exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)) h

theorem one_lt_nParam_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) : 1 < E1.nParam H := by
  have hr := S.rParam_eq_three_F4 h137 h1336 hab
  have hw := S.one_lt_wParam_F4 h137 h1326 hab hr
  by_contra hn
  push Not at hn
  apply hHM
  refine e3_35_one S.elemAbelian_V S.V_ne_bot_of_z S.hypE322 S.isUniqueM_normalizer
    (isSylowTwoOf_of_le S.h13.sylow hH.1) ?_ inf_le_left ?_
  · exact fun x hx => S.NV_le_M (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2)
  · rw [hr]
    exact lt_of_le_of_lt hn (lt_min hw (by norm_num))

theorem le_M_of_solvable_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {H : Subgroup G} (hH : InH T H)
    (hs : Group.IsSolvable ↥H) : H ≤ Subgroup.normalizer (L : Set G) := by
  have hr := S.rParam_eq_three_F4 h137 h1336 hab
  have hw := S.one_lt_wParam_F4 h137 h1326 hab hr
  refine e3_35_one_solvable S.elemAbelian_V S.V_ne_bot_of_z S.hypE322 S.isUniqueM_normalizer
    (isSylowTwoOf_of_le S.h13.sylow hH.1) ?_ inf_le_left hs ?_
  · exact fun x hx => S.NV_le_M (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2)
  · rw [hr]
    exact lt_min hw (by norm_num)

end Setting

end CFSG.Quasithin.H13.A5
