module

public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.RankThree.Coprime.CommutingActionGeneration
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Transport

variable {X : Type*} [Group X]

theorem map_subtype_top (H : Subgroup X) : (⊤ : Subgroup ↥H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_actionCommutator_conj {A H : Subgroup X} [MulDistribMulAction ↥A ↥H]
    (hsmul : ∀ (a : ↥A) (y : ↥H), ((a • y : ↥H) : X) = a * y * (a : X)⁻¹) (L : Subgroup ↥H) :
    (actionCommutator ↥A L).map H.subtype = ⁅A, L.map H.subtype⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨_, ⟨y, hy, a, rfl⟩, rfl⟩
    have e : H.subtype (y⁻¹ * (a • y)) = (⁅(a : X), ((y⁻¹ : ↥H) : X)⁆)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_subtype, hsmul, commutatorElement_def,
        InvMemClass.coe_inv]
      group
    rw [SetLike.mem_coe, e]
    exact inv_mem (subset_closure ⟨a, a.2, _, ⟨y⁻¹, inv_mem hy, rfl⟩, rfl⟩)
  · rw [closure_le]
    rintro _ ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
    have e : ⁅a, H.subtype y⁆ = (H.subtype (y⁻¹⁻¹ * ((⟨a, ha⟩ : ↥A) • y⁻¹)))⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_subtype, hsmul, commutatorElement_def,
        InvMemClass.coe_inv]
      group
    rw [SetLike.mem_coe, e]
    exact inv_mem (subset_closure ⟨_, ⟨y⁻¹, inv_mem hy, ⟨a, ha⟩, rfl⟩, rfl⟩)

theorem map_fixedPointSubgroup_conj {A H : Subgroup X} [MulDistribMulAction ↥A ↥H]
    (hsmul : ∀ (a : ↥A) (y : ↥H), ((a • y : ↥H) : X) = a * y * (a : X)⁻¹) (b : ↥A) :
    (CFSG.fixedPointSubgroup (zpowers b) ↥H).map H.subtype =
      centralizer ({(b : X)} : Set X) ⊓ H := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [CFSG.RankThree.Coprime.mem_fixedPointSubgroup_zpowers_iff_smul_eq] at hy
    have hy' : (b : X) * y * (b : X)⁻¹ = y := by rw [← hsmul, hy]
    refine ⟨?_, y.2⟩
    calc (y : X) * b = ((b : X) * y * (b : X)⁻¹) * b := by rw [hy']
      _ = b * y := by group
  · rintro ⟨hxc, hxH⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [CFSG.RankThree.Coprime.mem_fixedPointSubgroup_zpowers_iff_smul_eq]
    apply Subtype.ext
    rw [hsmul]
    change (b : X) * x * (b : X)⁻¹ = x
    rw [← hxc]
    group

end Transport

section Generation

variable {X : Type*} [Group X] [Finite X]

theorem commutator_zpowers_eq_iSup {Y W : Subgroup X} {t : X} (hY : Odd (Nat.card Y))
    (ht : orderOf t = 2) (htY : t ∈ normalizer (Y : Set X)) (hW4 : Nat.card W = 4)
    (hW2 : ∀ w ∈ W, w * w = 1) (hWY : W ≤ normalizer (Y : Set X))
    (hWt : W ≤ centralizer ({t} : Set X)) :
    ⁅zpowers t, Y⁆ = ⨆ w ∈ (W : Set X) \ {1}, ⁅zpowers t, centralizer ({w} : Set X) ⊓ Y⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTY : zpowers t ≤ normalizer (Y : Set X) := zpowers_le.mpr htY
  let : MulDistribMulAction ↥W ↥Y := MulDistribMulAction.compHom ↥Y (Subgroup.inclusion hWY)
  let : MulDistribMulAction ↥(zpowers t) ↥Y :=
    MulDistribMulAction.compHom ↥Y (Subgroup.inclusion hTY)
  have hsmulW : ∀ (a : ↥W) (y : ↥Y), ((a • y : ↥Y) : X) = a * y * (a : X)⁻¹ := fun _ _ => rfl
  have hsmulT : ∀ (a : ↥(zpowers t)) (y : ↥Y), ((a • y : ↥Y) : X) = a * y * (a : X)⁻¹ :=
    fun _ _ => rfl
  have hWinv : ∀ a : ↥W, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (Subtype.ext (hW2 a a.2))
  have : CFSG.IsElementaryAbelian 2 ↥W :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        calc a * b = (a * b)⁻¹ := (hWinv _).symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = b * a := by rw [hWinv, hWinv]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        rw [sq]
        exact Subtype.ext (hW2 a a.2) }
  have hcomm : ∀ (b : ↥W) (a : ↥(zpowers t)) (x : ↥Y), b • a • x = a • b • x := by
    intro b a x
    have htb : t ∈ centralizer ({(b : X)} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hWt b.2)).symm
    have hab : (a : X) * b = b * a :=
      Subgroup.mem_centralizer_singleton_iff.mp (zpowers_le.mpr htb a.2)
    apply Subtype.ext
    simp only [hsmulW, hsmulT]
    calc _ = ((b : X) * a) * x * ((b : X) * a)⁻¹ := by group
      _ = ((a : X) * b) * x * ((a : X) * b)⁻¹ := by rw [hab]
      _ = _ := by group
  have hcop : Nat.Coprime (Nat.card ↥W * Nat.card ↥(zpowers t)) (Nat.card ↥Y) := by
    rw [hW4, Nat.card_zpowers, ht, show (4 : ℕ) * 2 = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hY)
  have hgen := CFSG.RankThree.Coprime.solvable_commuting_action_fixed_commutator_generation
    (p := 2) (B := ↥W) (W := ↥(zpowers t)) (H := ↥Y) (le_of_eq_of_le (by norm_num) hW4.ge)
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY) hcomm hcop
  calc ⁅zpowers t, Y⁆ = (actionCommutator ↥(zpowers t) (⊤ : Subgroup ↥Y)).map Y.subtype := by
        rw [map_actionCommutator_conj hsmulT, map_subtype_top]
    _ = (⨆ (b : ↥W) (_ : b ≠ 1), actionCommutator ↥(zpowers t)
          (CFSG.fixedPointSubgroup (zpowers b) ↥Y)).map Y.subtype := by rw [hgen]
    _ = ⨆ (b : ↥W) (_ : b ≠ 1), ⁅zpowers t, centralizer ({(b : X)} : Set X) ⊓ Y⁆ := by
        simp only [Subgroup.map_iSup, map_actionCommutator_conj hsmulT,
          map_fixedPointSubgroup_conj hsmulW]
    _ = ⨆ w ∈ (W : Set X) \ {1}, ⁅zpowers t, centralizer ({w} : Set X) ⊓ Y⁆ := by
        apply le_antisymm
        · refine iSup₂_le fun b hb => ?_
          exact le_iSup₂_of_le (f := fun (w : X) (_ : w ∈ (W : Set X) \ {1}) =>
            ⁅zpowers t, centralizer ({w} : Set X) ⊓ Y⁆) (b : X)
            ⟨b.2, fun h => hb (Subtype.ext h)⟩ le_rfl
        · refine iSup₂_le fun w hw => ?_
          exact le_iSup₂_of_le (f := fun (b : ↥W) (_ : b ≠ 1) =>
            ⁅zpowers t, centralizer ({(b : X)} : Set X) ⊓ Y⁆) (⟨w, hw.1⟩ : ↥W)
            (fun h => hw.2 (congrArg Subtype.val h)) le_rfl

end Generation

section Lemma161

variable {X : Type} [Group X] [Finite X] {Z : Set X}

theorem commutator_zpowers_kGrp (M : Subgroup X) (hZ : IsInvariantInvolutionSet Z) {t : X}
    (ht : t ∈ Z) :
    Odd (Nat.card (kGrp M t)) ∧ t ∈ normalizer (kGrp M t : Set X) ∧
      ⁅zpowers t, kGrp M t⁆ = kGrp M t := by
  set O := pPrimeCoreIn (M ⊓ conjugate M t) with hO
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hTO : zpowers t ≤ normalizer (O : Set X) :=
    zpowers_le.mpr (mem_normalizer_pPrimeCoreIn (mem_normalizer_inf_conjugate ht2))
  have hKO : kGrp M t ≤ O := Subgroup.le_normalizer_iff_commutator_le_right.mp hTO
  have hOodd : Odd (Nat.card O) := odd_card_pPrimeCoreIn _
  refine ⟨Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hKO),
    Subgroup.normalizer_commutator_ge_left _ _ (mem_zpowers t), ?_⟩
  let : MulDistribMulAction ↥(zpowers t) ↥O :=
    MulDistribMulAction.compHom ↥O (Subgroup.inclusion hTO)
  have hsmul : ∀ (a : ↥(zpowers t)) (y : ↥O), ((a • y : ↥O) : X) = a * y * (a : X)⁻¹ :=
    fun _ _ => rfl
  have hcop : Nat.Coprime (Nat.card ↥O) (Nat.card ↥(zpowers t)) := by
    rw [Nat.card_zpowers, hZ.1 t ht]
    exact (Nat.coprime_two_left.mpr hOodd).symm
  have hidem := (CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization
    (A := ↥(zpowers t)) (H := ↥O) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd) hcop).2.2.2
  have hmap := congrArg (Subgroup.map O.subtype) hidem
  simp only [map_actionCommutator_conj hsmul, map_subtype_top] at hmap
  exact hmap

theorem ZDSetup.lemma161 {M : Subgroup X} (S : ZDSetup X Z M) : Lemma161Stmt Z M := by
  intro c W hW4 hW2 hWN hWt
  obtain ⟨hKodd, htK, hKK⟩ := commutator_zpowers_kGrp M S.invariant c.ht
  exact hKK.symm.trans
    (commutator_zpowers_eq_iSup hKodd (S.invariant.1 c.t c.ht) htK hW4 hW2 hWN hWt)

end Lemma161

end CFSG.GH74.Uniqueness
