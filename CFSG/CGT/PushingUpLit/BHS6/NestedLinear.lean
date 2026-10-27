module

public import CFSG.CGT.PushingUpLit.BHS6.NestedBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem eq_one_of_odd_of_smul_eq {F : Type*} [Field F] [CharP F 2]
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (hodd : Odd (orderOf g)) {v : Fin 2 → F}
    (hv : v ≠ 0) (h : g • v = v) : g = 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have hv' := h
  rw [Matrix.SpecialLinearGroup.smul_def] at hv'
  have hx := congrFun hv' 0
  have hy := congrFun hv' 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hx hy
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hx' : (a - 1) * v 0 + b * v 1 = 0 := by linear_combination hx
  have hy' : c * v 0 + (d - 1) * v 1 = 0 := by linear_combination hy
  have hdetN : (a - 1) * (d - 1) - b * c = 0 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have : ((a - 1) * (d - 1) - b * c) * v 1 = 0 := by
        linear_combination (a - 1) * hy' - c * hx'
      exact (mul_eq_zero.mp this).resolve_right h1
    · have : ((a - 1) * (d - 1) - b * c) * v 0 = 0 := by
        linear_combination (d - 1) * hx' - b * hy'
      exact (mul_eq_zero.mp this).resolve_right h0
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have had : a + d = 0 := by linear_combination hdet - hdetN + h2
  have hda : d = a := by linear_combination had - a * h2
  have hsq : g * g = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc, ← hd]
    · linear_combination hdet - a * hda + b * c * h2
    · linear_combination b * had
    · linear_combination c * had
    · linear_combination hdet + b * c * h2 + d * hda
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

variable {Γ : Type} [Group Γ]

theorem relIndex_of_isNatBy {S M : Type*} [Group S] [Group M] {act : S → M → M}
    {E W : Subgroup Γ} (h : IsNatBy act E W) :
    (E ⊓ Subgroup.centralizer (W : Set Γ)).relIndex E = Nat.card S ∧
      (W ⊓ Subgroup.centralizer (E : Set Γ)).relIndex W = Nat.card M := by
  obtain ⟨φ, ψ, hφ, hφk, hψ, hψk, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.relIndex, ← hφk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ,
      Subgroup.card_top]
  · rw [Subgroup.relIndex, ← hψk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψ,
      Subgroup.card_top]

theorem pow_mul_pow_lt_factorial {n : ℕ} (hn : 3 ≤ n) :
    2 ^ (n + 1) * 4 ^ n < (2 * n + 1).factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : (2 * (n + 1) + 1).factorial =
        (2 * n + 3) * ((2 * n + 2) * (2 * n + 1).factorial) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
    rw [h1, show 2 ^ (n + 1 + 1) * 4 ^ (n + 1) = 8 * (2 ^ (n + 1) * 4 ^ n) by ring]
    have h2 : 8 ≤ (2 * n + 3) * (2 * n + 2) := by nlinarith
    calc 8 * (2 ^ (n + 1) * 4 ^ n) < ((2 * n + 3) * (2 * n + 2)) * (2 ^ (n + 1) * 4 ^ n) := by
          apply Nat.mul_lt_mul_of_pos_right (by nlinarith) (by positivity)
      _ ≤ ((2 * n + 3) * (2 * n + 2)) * (2 * n + 1).factorial :=
          Nat.mul_le_mul_left _ ih.le
      _ = (2 * n + 3) * ((2 * n + 2) * (2 * n + 1).factorial) := by ring

section Finite

variable [Finite Γ] {G T E F : Subgroup Γ}

theorem eq_of_le_linear (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) {n : ℕ}
    (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) :
    F = E := by
  classical
  have hF' := hF
  obtain ⟨s, hs, hFs⟩ := hF'
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS : IsSylowOf 2 (A1b.conjSub s T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem hT' hs)
  have hcharE := charTwo_of_isBTBlock hG hT hE
  have hcharF := charTwo_of_isBTBlock hG hS hFs
  have hW'W := pCoreOf_le_of_le_block hG hT hE hF hFE
  have hcap := inf_centralizer_pCoreOf_nested hG hT hE hF hFE
  have hcomm := commutator_pCoreOf_le_nested hG hT hE hF
  have hWe : IsElemAbelian 2 (pCoreOf 2 E) :=
    isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, pCoreOf 2 E⁆ = pCoreOf 2 E := by
    rw [Subgroup.commutator_comm]
    exact hE.perfect
  have hnatE : IsNatSL E (pCoreOf 2 E) n := by
    have := isNatSL_of_isBTBlock hG hT hE hn
    rwa [blockW_eq_pCoreOf hE] at this
  have hFres : opResidual 2 F = F := opResidual_eq_of_isBTBlock hFs
  have hEres : opResidual 2 E = E := opResidual_eq_of_isBTBlock hE
  have hFne : pCoreOf 2 F ≠ ⊥ := pCoreOf_ne_bot hFs hcharF
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  set W' : Subgroup Γ := pCoreOf 2 F with hW'def
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hW2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  obtain ⟨D⟩ := nonempty_slNatData hWe hEW hperf hnatE
  obtain ⟨x, hxF, hxodd, hxC⟩ : ∃ x ∈ F, Odd (orderOf x) ∧
      x ∉ Subgroup.centralizer (W : Set Γ) := by
    by_contra hcon
    have hall : ∀ x ∈ F, Odd (orderOf x) → x ∈ Subgroup.centralizer (W : Set Γ) := by
      intro x hx hodd
      by_contra hx'
      exact hcon ⟨x, hx, hodd, hx'⟩
    have hFC : F ≤ Subgroup.centralizer (W : Set Γ) := le_of_forall_odd_le hFres hall
    have hFW : ⁅F, W⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro f hf w hw
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hFC hf) w hw).symm
    have h1 : ⁅W', F⁆ ≤ ⁅F, W⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl hW'W
    rw [hFs.perfect, hFW] at h1
    exact hFne (le_bot_iff.mp h1)
  have hxN : x ∈ Subgroup.normalizer (W : Set Γ) := hEW (hFE hxF)
  set xb : MulAut ↥W := conjAct W ⟨x, hxN⟩ with hxbdef
  have hxbE : xb ∈ autOn E W := mem_autOn_iff.mpr ⟨⟨x, hxN⟩, hFE hxF, rfl⟩
  have hxb1 : xb ≠ 1 := by
    intro h
    apply hxC
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have h1 := congrArg (fun a : MulAut ↥W => ((a ⟨w, hw⟩ : ↥W) : Γ)) h
    have h2 : x * w * x⁻¹ = w := by
      have := conjAct_apply' W ⟨x, hxN⟩ ⟨w, hw⟩
      exact this.trans h1
    calc w * x = (x * w * x⁻¹) * x := by rw [h2]
      _ = x * w := by group
  have hxbodd : Odd (orderOf xb) := by
    have h1 : orderOf xb ∣ orderOf x := by
      have := orderOf_map_dvd (conjAct W) (⟨x, hxN⟩ : ↥(Subgroup.normalizer (W : Set Γ)))
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hxodd h1
  have hfixker : ∀ w : ↥W, xb w = w → D.β w = 1 := by
    intro w hw
    by_contra hne
    have hv : Multiplicative.toAdd (D.β w) ≠ 0 := fun h0 =>
      hne (by simpa using congrArg Multiplicative.ofAdd h0)
    have h1 := D.equivar' ⟨xb, hxbE⟩ w
    have h1' : Multiplicative.toAdd (D.β w) = D.θ ⟨xb, hxbE⟩ • Multiplicative.toAdd (D.β w) := by
      have : ((⟨xb, hxbE⟩ : ↥(autOn E W)) : MulAut ↥W) w = w := hw
      rw [this] at h1
      exact h1
    have hodd' : Odd (orderOf (D.θ ⟨xb, hxbE⟩)) := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hxbodd
    have := eq_one_of_odd_of_smul_eq hodd' hv h1'.symm
    apply hxb1
    have h2 : (⟨xb, hxbE⟩ : ↥(autOn E W)) = 1 := D.θ.injective (by rw [this, map_one])
    exact congrArg Subtype.val h2
  have hXzodd : Odd (Nat.card ↥(Subgroup.zpowers xb)) := by
    rw [Nat.card_zpowers]
    exact hxbodd
  have hcompl := isCompl_fixV_commV_of_odd (Subgroup.zpowers xb) hXzodd hW2
  have hfixle : fixV (Subgroup.zpowers xb) ≤ fixV (autOn E W) := fun w hw =>
    (D.ker_iff w).mp (hfixker w (mem_fixV_zpowers_iff.mp hw))
  have hcommle : commV (Subgroup.zpowers xb) ≤ W'.subgroupOf W := by
    rw [commV_le_iff]
    intro y hy v
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_subgroupOf]
    have hxj : x ^ j ∈ F := F.zpow_mem hxF j
    have hxjN : x ^ j ∈ Subgroup.normalizer (W : Set Γ) := Subgroup.zpow_mem _ hxN j
    have e1 : (⟨x ^ j, hxjN⟩ : ↥(Subgroup.normalizer (W : Set Γ))) = ⟨x, hxN⟩ ^ j :=
      Subtype.ext (by simp)
    have e : xb ^ j = conjAct W ⟨x ^ j, hxjN⟩ := by
      rw [e1, map_zpow]
    rw [e]
    have h1 : (((conjAct W ⟨x ^ j, hxjN⟩) v * v⁻¹ : ↥W) : Γ) = ⁅x ^ j, (v : Γ)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply' W ⟨x ^ j, hxjN⟩ v]
      simp only [commutatorElement_def]
    rw [h1]
    exact hcomm (Subgroup.commutator_mem_commutator hxj v.2)
  have hsup : fixV (autOn E W) ⊔ W'.subgroupOf W = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hcompl.sup_eq_top]
    exact sup_le_sup hfixle hcommle
  have hfixmem : ∀ c : ↥W, c ∈ fixV (autOn E W) ↔ (c : Γ) ∈ Subgroup.centralizer (E : Set Γ) := by
    intro c
    have h := fixOn_eq hWe hEW
    have h' : c ∈ fixOn hWe E ↔ c ∈ (Subgroup.centralizer (E : Set Γ)).subgroupOf W := by
      rw [h]
    rw [Subgroup.mem_subgroupOf] at h'
    exact h'
  let f : ↥W' →* Multiplicative (Fin 2 → GaloisField 2 n) :=
    D.β.comp (Subgroup.inclusion hW'W)
  have hfsurj : Function.Surjective f := by
    intro m
    obtain ⟨w, rfl⟩ := D.surj m
    have hw : w ∈ fixV (autOn E W) ⊔ W'.subgroupOf W := by
      rw [hsup]
      exact Subgroup.mem_top w
    obtain ⟨c, hc, p, hp, hcp⟩ := Subgroup.mem_sup.mp hw
    refine ⟨⟨(p : Γ), Subgroup.mem_subgroupOf.mp hp⟩, ?_⟩
    have e : Subgroup.inclusion hW'W ⟨(p : Γ), Subgroup.mem_subgroupOf.mp hp⟩ = p :=
      Subtype.ext rfl
    show D.β (Subgroup.inclusion hW'W ⟨(p : Γ), Subgroup.mem_subgroupOf.mp hp⟩) = D.β w
    rw [e, ← hcp, map_mul, (D.ker_iff c).mpr hc, one_mul]
  have hfker : f.ker = (W' ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf W' := by
    ext w'
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show D.β (Subgroup.inclusion hW'W w') = 1 ↔ _
    rw [D.ker_iff, hfixmem]
    exact ⟨fun h => ⟨w'.2, h⟩, fun h => h.2⟩
  have hQE : (W' ⊓ Subgroup.centralizer (E : Set Γ)).relIndex W' =
      Nat.card (Multiplicative (Fin 2 → GaloisField 2 n)) := by
    rw [Subgroup.relIndex, ← hfker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfsurj,
      Subgroup.card_top]
  have hCeq : W' ⊓ Subgroup.centralizer (F : Set Γ) = W' ⊓ Subgroup.centralizer (E : Set Γ) := by
    refine le_antisymm ?_ (inf_le_inf_left _ (Subgroup.centralizer_le hFE))
    intro w hw
    refine Subgroup.mem_inf.mpr ⟨hw.1, ?_⟩
    have hwW : w ∈ W := hW'W hw.1
    have hfix : xb ⟨w, hwW⟩ = ⟨w, hwW⟩ := by
      apply Subtype.ext
      rw [hxbdef, conjAct_apply']
      have h1 : x * w = w * x := Subgroup.mem_centralizer_iff.mp hw.2 x hxF
      show x * w * x⁻¹ = w
      calc x * w * x⁻¹ = w * x * x⁻¹ := by rw [h1]
        _ = w := by group
    exact (hfixmem ⟨w, hwW⟩).mp ((D.ker_iff _).mp (hfixker _ hfix))
  have hFW : F ≤ Subgroup.normalizer (W : Set Γ) := hFE.trans hEW
  have hautF : Nat.card ↥(autOn F W) = W'.relIndex F := by
    rw [card_autOn_eq_relIndex hFW, hcap]
  have hautE : Nat.card ↥(autOn E W) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [card_autOn_eq_relIndex hEW]
    exact (relIndex_of_isNatBy (isNatSL_iff.mp hnatE)).1
  have hW'ab : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x := hFs.elemAbelian.1
  have hcapF : F ⊓ Subgroup.centralizer (W' : Set Γ) = W' :=
    le_antisymm hcharF fun w hw =>
      Subgroup.mem_inf.mpr ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F hw,
        Subgroup.mem_centralizer_iff.mpr fun y hy => hW'ab y hy w hw⟩
  have hbar : autOn F W = autOn E W := by
    refine Subgroup.eq_of_le_of_card_ge (autOn_le_autOn W hFE) ?_
    rcases hFs.type with ⟨k, hk2, hk⟩ | ⟨r, hr, hr'⟩
    · have hnatF : IsNatSL F W' k := by
        have := isNatSL_of_isBTBlock hG hS hFs hk
        rwa [blockW_eq_pCoreOf hFs] at this
      obtain ⟨hF1, hF2⟩ := relIndex_of_isNatBy (isNatSL_iff.mp hnatF)
      rw [hcapF] at hF1
      have hM : Nat.card (Multiplicative (Fin 2 → GaloisField 2 k)) =
          Nat.card (Multiplicative (Fin 2 → GaloisField 2 n)) := by
        rw [← hF2, hCeq, hQE]
      rw [SLNatData.card_dual (F := GaloisField 2 k),
        SLNatData.card_dual (F := GaloisField 2 n)] at hM
      have hQ : Nat.card (GaloisField 2 k) = Nat.card (GaloisField 2 n) :=
        Nat.pow_left_injective two_ne_zero hM
      rw [hautE, hautF, hF1, card_SL2_eq, card_SL2_eq, hQ]
    · have hnatF : IsNatAlt F W' (2 * r + 1) := by
        have := isNatAlt_of_isBTBlock hG hS hFs hr'
        rwa [blockW_eq_pCoreOf hFs] at this
      obtain ⟨hF1, hF2⟩ := relIndex_of_isNatBy hnatF
      rw [hcapF] at hF1
      have hM : Nat.card (coreMod (2 * r + 1)) =
          Nat.card (Multiplicative (Fin 2 → GaloisField 2 n)) := by
        rw [← hF2, hCeq, hQE]
      have hodd : Odd (2 * r + 1) := ⟨r, rfl⟩
      have hcm := card_coreMod_mul_two hodd
      rw [SLNatData.card_dual (F := GaloisField 2 n), GaloisField.card 2 n (by omega)] at hM
      have hrn : r = n := by
        have h1 : 2 ^ (2 * r + 1) = 2 ^ (2 * n + 1) := by
          rw [← hcm, hM]
          ring
        have h2 := Nat.pow_right_injective (le_refl 2) h1
        omega
      rw [hrn] at hF1
      have hA : Nat.card (alternatingGroup (Fin (2 * n + 1))) = (2 * n + 1).factorial / 2 := by
        have : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
        rw [nat_card_alternatingGroup, Nat.card_fin]
      have hle := Subgroup.card_le_of_le (autOn_le_autOn W hFE)
      rw [hautF, hF1, hA, hautE, card_SL2_eq, GaloisField.card 2 n (by omega)] at hle
      have hn2' : n = 2 := by
        by_contra hne
        have h3 : 3 ≤ n := by omega
        have hlt := pow_mul_pow_lt_factorial h3
        have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
          rw [← mul_pow]
          norm_num
        have hA2 : (2 * n + 1).factorial ≤ 2 * ((2 * n + 1).factorial / 2) + 1 := by omega
        have hu1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have hsq : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hu1
        have hle' : (2 * n + 1).factorial / 2 + 2 ^ n ≤ 2 ^ n * (2 ^ n) ^ 2 := by
          have : 2 ^ n * ((2 ^ n) ^ 2 - 1) + 2 ^ n = 2 ^ n * (2 ^ n) ^ 2 := by
            rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hsq]
          omega
        rw [pow_succ, h4] at hlt
        nlinarith
      rw [hautE, hautF, hF1, hA, card_SL2_eq, GaloisField.card 2 n (by omega), hn2']
      norm_num [Nat.factorial]
  have hEF : E ≤ F := by
    rw [← hEres]
    refine opResidual_le_of_pow_mem fun e he => ⟨1, ?_⟩
    rw [pow_one]
    have heN : e ∈ Subgroup.normalizer (W : Set Γ) := hEW he
    have hepre : e ∈ autPre W (autOn F W) :=
      mem_autPre.mpr ⟨heN, by
        rw [hbar]
        exact mem_autOn_iff.mpr ⟨⟨e, heN⟩, he, rfl⟩⟩
    obtain ⟨f, hf, hc⟩ := exists_mul_of_mem_autPre hepre
    have hc1E : e * f⁻¹ ∈ E := E.mul_mem he (E.inv_mem (hFE hf))
    have hc1W : e * f⁻¹ ∈ W := hcharE ⟨hc1E, hc⟩
    have hmem : (⟨e * f⁻¹, hc1W⟩ : ↥W) ∈ fixV (autOn E W) ⊔ W'.subgroupOf W := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨c, hc', p, hp, hcp⟩ := Subgroup.mem_sup.mp hmem
    have hcC : (c : Γ) ∈ Subgroup.centralizer (E : Set Γ) := (hfixmem c).mp hc'
    have hpF : (p : Γ) ∈ F :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F (Subgroup.mem_subgroupOf.mp hp)
    have hcp' : (c : Γ) * (p : Γ) = e * f⁻¹ := congrArg Subtype.val hcp
    have hf'F : (p : Γ) * f ∈ F := F.mul_mem hpF hf
    have he' : e = (c : Γ) * ((p : Γ) * f) := by
      calc e = (e * f⁻¹) * f := by group
        _ = ((c : Γ) * (p : Γ)) * f := by rw [hcp']
        _ = (c : Γ) * ((p : Γ) * f) := by group
    have hcc : (c : Γ) * (c : Γ) = 1 := by
      have := hW2 c
      rw [pow_two] at this
      exact congrArg Subtype.val this
    have hcomm' : ((p : Γ) * f) * (c : Γ) = (c : Γ) * ((p : Γ) * f) :=
      Subgroup.mem_centralizer_iff.mp hcC _ (hFE hf'F)
    have hE2 : e * e = ((p : Γ) * f) * ((p : Γ) * f) := by
      calc e * e = ((c : Γ) * ((p : Γ) * f)) * ((c : Γ) * ((p : Γ) * f)) := by rw [← he']
        _ = (c : Γ) * (((p : Γ) * f) * (c : Γ)) * ((p : Γ) * f) := by group
        _ = (c : Γ) * ((c : Γ) * ((p : Γ) * f)) * ((p : Γ) * f) := by rw [hcomm']
        _ = ((c : Γ) * (c : Γ)) * ((p : Γ) * f) * ((p : Γ) * f) := by group
        _ = ((p : Γ) * f) * ((p : Γ) * f) := by rw [hcc, one_mul]
    rw [pow_two, hE2]
    exact F.mul_mem hf'F hf'F
  exact le_antisymm hFE hEF

end Finite

end CFSG.CGT.PushingUpLit.BHS6
