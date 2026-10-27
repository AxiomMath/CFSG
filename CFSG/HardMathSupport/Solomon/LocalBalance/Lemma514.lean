module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace Lemma514Ns


theorem isPGroup_of_isElemAbelian' {Γ : Type*} [Group Γ] {p : ℕ} {E : Subgroup Γ}
    (hE : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem comm_of_isElemAbelian' {Γ : Type*} [Group Γ] {p : ℕ} {E : Subgroup Γ}
    (hE : IsElemAbelian p E) {x y : Γ} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  CFSG.Open.IsElemAbelian.comm hE hx hy

theorem isElemAbelian_sup_of_commute' {Γ : Type*} [Group Γ] {p : ℕ} {A B : Subgroup Γ}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

theorem isElemAbelian_map' {Γ Δ : Type*} [Group Γ] [Group Δ] {p : ℕ} {E : Subgroup Γ}
    (hE : IsElemAbelian p E) (f : Γ →* Δ) : IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem not_card_three_of_isMaximal_aux {Γ : Type*} [Group Γ] [Finite Γ]
    (E E9 : Subgroup Γ) (hEe : IsElemAbelian 3 E) (hE3 : Nat.card E = 3)
    (hmax : ∀ D : Subgroup Γ, IsElemAbelian 3 D → E ≤ D → D = E)
    (hE9e : IsElemAbelian 3 E9) (hE9c : Nat.card E9 = 9) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P1, hEP1⟩ := (isPGroup_of_isElemAbelian' hEe).exists_le_sylow
  obtain ⟨P2, hE9P2⟩ := (isPGroup_of_isElemAbelian' hE9e).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P2 P1
  have hconj : ∀ x ∈ E9, g * x * g⁻¹ ∈ (P1 : Subgroup Γ) := by
    intro x hx
    have h1 : MulAut.conj g • x ∈ MulAut.conj g • (P2 : Subgroup Γ) :=
      Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ (hE9P2 hx)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    simpa [MulAut.smul_def] using h1
  set E9' : Subgroup Γ := E9.map (MulAut.conj g).toMonoidHom with hE9'
  have hE9'P1 : E9' ≤ (P1 : Subgroup Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hconj x hx
  have hE9'e : IsElemAbelian 3 E9' := isElemAbelian_map' hE9e _
  have hE9'c : Nat.card E9' = 9 := by
    rw [hE9', Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9c]
  have hP1 : IsPGroup 3 (P1 : Subgroup Γ) := P1.isPGroup'
  have hnt : Nontrivial (P1 : Subgroup Γ) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have : (3 : ℕ) ∣ Nat.card (P1 : Subgroup Γ) := by
      have h3 : Nat.card E ∣ Nat.card (P1 : Subgroup Γ) := Subgroup.card_dvd_of_le hEP1
      rwa [hE3] at h3
    exact lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd Nat.card_pos this)
  have hcn := hP1.center_nontrivial
  obtain ⟨zc, hzc⟩ := exists_ne (1 : (Subgroup.center (P1 : Subgroup Γ)))
  set w : (P1 : Subgroup Γ) := (zc : (P1 : Subgroup Γ)) with hw
  have hw1 : w ≠ 1 := fun h => hzc (Subtype.ext h)
  have hwc : ∀ y : (P1 : Subgroup Γ), y * w = w * y := fun y => (Subgroup.mem_center_iff.1 zc.2 y)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hP1) w
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hw1 (orderOf_eq_one_iff.1 (by simpa using hm))
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hordH : orderOf (w : Γ) = 3 ^ (m' + 1) := by
    rw [← Subgroup.orderOf_coe w] at hm
    exact hm
  have hzord : orderOf ((w : Γ) ^ (3 ^ m')) = 3 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (by rw [hordH]; exact pow_dvd_pow 3 (Nat.le_succ m')),
      hordH]
    rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  set z : Γ := (w : Γ) ^ (3 ^ m') with hzdef
  have hzP : z ∈ (P1 : Subgroup Γ) := (P1 : Subgroup Γ).pow_mem w.2 _
  have hz3 : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzord] at h
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hzc : ∀ y ∈ (P1 : Subgroup Γ), y * z = z * y := by
    intro y hy
    exact (Commute.pow_right (show Commute y (w : Γ) from congrArg Subtype.val (hwc ⟨y, hy⟩)) (3 ^ m')).eq
  have hzel : IsElemAbelian 3 (Subgroup.zpowers z) := by
    refine ⟨inferInstance, fun u hu => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hzcom : ∀ y ∈ Subgroup.zpowers z, ∀ y' ∈ (P1 : Subgroup Γ), y' * y = y * y' := by
    intro y hy y' hy'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (show Commute y' z from hzc y' hy') k).eq
  have hzE : z ∈ E := by
    have h1 : IsElemAbelian 3 (E ⊔ Subgroup.zpowers z) :=
      isElemAbelian_sup_of_commute' hEe hzel fun a ha b hb => hzcom b hb a (hEP1 ha)
    have h2 := hmax _ h1 le_sup_left
    rw [← h2]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzp3 : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  have hEz : Subgroup.zpowers z = E := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzE) ?_
    rw [hE3, hzp3]
  have hEcom : ∀ e ∈ E, ∀ y ∈ E9', e * y = y * e := by
    intro e he y hy
    rw [← hEz] at he
    exact (hzcom e he y (hE9'P1 hy)).symm
  have h1 : IsElemAbelian 3 (E ⊔ E9') := isElemAbelian_sup_of_commute' hEe hE9'e hEcom
  have h2 := hmax _ h1 le_sup_left
  have h3 : E9' ≤ E := by rw [← h2]; exact le_sup_right
  have h4 := Subgroup.card_le_of_le h3
  rw [hE9'c, hE3] at h4
  omega



theorem exists_fixed_three_element {H : Type*} [Group H] [Finite H]
    (Bb Y : Subgroup H) (hBp : IsPGroup 3 Bb) (hBN : Bb ≤ Subgroup.normalizer (Y : Set H))
    (hY : 3 ∣ Nat.card Y) :
    ∃ z ∈ Y, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ b ∈ Bb, b * z = z * b := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPY, hP3, hPcard, hBP⟩ : ∃ P : Subgroup H, P ≤ Y ∧ IsPGroup 3 P ∧
      (∀ n : ℕ, 3 ^ n ∣ Nat.card Y → 3 ^ n ∣ Nat.card P) ∧ Bb ≤ Subgroup.normalizer (P : Set H) := by
    let φ : Bb →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
    let _ : MulDistribMulAction Bb Y := MulDistribMulAction.compHom Y φ
    let _ : MulAction Bb (Sylow 3 Y) := Sylow.pointwiseMulAction
    have hcard : ¬ 3 ∣ Nat.card (Sylow 3 Y) := by
      have h := card_sylow_modEq_one 3 Y
      intro hd
      have : Nat.card (Sylow 3 Y) ≡ 0 [MOD 3] := (Nat.modEq_zero_iff_dvd).2 hd
      have h2 := h.symm.trans this
      exact absurd h2 (by decide)
    obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 Y) hcard
    refine ⟨(Q₀ : Subgroup Y).map Y.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _,
      fun n hn => ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
      exact Q₀.pow_dvd_card_of_pow_dvd_card hn
    · rw [Subgroup.le_normalizer_iff]
      rintro b hb _ ⟨y, hy, rfl⟩
      have hfix : (⟨b, hb⟩ : Bb) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
      have hmem : (⟨b, hb⟩ : Bb) • y ∈ (Q₀ : Subgroup Y) := by
        have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : Bb) (Q₀ : Subgroup Y) hy
        rwa [← Sylow.pointwise_smul_def, hfix] at h
      refine ⟨_, hmem, ?_⟩
      change (((Y.normalizerMonoidHom) (Subgroup.inclusion hBN ⟨b, hb⟩)) y : H) = _
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
  have hPne : 3 ∣ Nat.card P := by
    have h := hPcard 1 (by simpa using hY)
    simpa using h
  let ψ : Bb →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  let _ : MulDistribMulAction Bb P := MulDistribMulAction.compHom P ψ
  have hmod := hBp.card_modEq_card_fixedPoints P
  have hfix3 : 3 ∣ Nat.card (MulAction.fixedPoints Bb P) := by
    have h1 : Nat.card P ≡ 0 [MOD 3] := (Nat.modEq_zero_iff_dvd).2 hPne
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans h1)
  have hone : (1 : P) ∈ MulAction.fixedPoints Bb P := fun g => smul_one g
  obtain ⟨w, hwfix, hw1⟩ : ∃ w ∈ MulAction.fixedPoints Bb P, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card (MulAction.fixedPoints Bb P) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, hone⟩⟩⟩
      rw [hcon a a.2, hcon b b.2]
    rw [this] at hfix3
    exact absurd hfix3 (by decide)
  have hwcomm : ∀ b ∈ Bb, b * (w : H) = (w : H) * b := by
    intro b hb
    have h := hwfix ⟨b, hb⟩
    have h2 : (((P.normalizerMonoidHom) (Subgroup.inclusion hBP ⟨b, hb⟩)) w : H) = (w : H) := by
      have : (⟨b, hb⟩ : Bb) • w = w := h
      exact congrArg Subtype.val this
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    simp only [Subgroup.coe_inclusion] at h2
    calc b * (w : H) = b * (w : H) * b⁻¹ * b := by group
      _ = (w : H) * b := by rw [h2]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hP3) w
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hw1 (orderOf_eq_one_iff.1 (by simpa using hm))
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hordH : orderOf (w : H) = 3 ^ (m' + 1) := by
    rw [← Subgroup.orderOf_coe w] at hm
    exact hm
  have hzord : orderOf ((w : H) ^ (3 ^ m')) = 3 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (by rw [hordH]; exact pow_dvd_pow 3 (Nat.le_succ m')),
      hordH]
    rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  refine ⟨(w : H) ^ (3 ^ m'), ?_, ?_, ?_, ?_⟩
  · exact Y.pow_mem (hPY w.2) _
  · intro h1
    rw [h1, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  · have h := pow_orderOf_eq_one ((w : H) ^ (3 ^ m'))
    rwa [hzord] at h
  · intro b hb
    exact ((Commute.pow_right (show Commute b (w : H) from hwcomm b hb) (3 ^ m')).eq)



theorem card_mul_le_of_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {E F Bb : Subgroup Γ}
    (hE : E ≤ Bb) (hF : F ≤ Bb) (hEF : E ⊓ F = ⊥) :
    Nat.card E * Nat.card F ≤ Nat.card Bb := by
  let f : E × F → Bb := fun p => ⟨(p.1 : Γ) * p.2, Bb.mul_mem (hE p.1.2) (hF p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨e, a⟩ ⟨e', a'⟩ h
    have h1 : (e : Γ) * a = e' * a' := congrArg Subtype.val h
    have h2 : (e' : Γ)⁻¹ * e = a' * (a : Γ)⁻¹ := by
      calc (e' : Γ)⁻¹ * e = (e' : Γ)⁻¹ * ((e : Γ) * a) * (a : Γ)⁻¹ := by group
        _ = (e' : Γ)⁻¹ * (e' * a') * (a : Γ)⁻¹ := by rw [h1]
        _ = a' * (a : Γ)⁻¹ := by group
    have h3 : (e' : Γ)⁻¹ * e ∈ E ⊓ F :=
      ⟨E.mul_mem (E.inv_mem e'.2) e.2, by rw [h2]; exact F.mul_mem a'.2 (F.inv_mem a.2)⟩
    rw [hEF, Subgroup.mem_bot] at h3
    have he : (e : Γ) = e' := by
      have := congrArg (fun t => (e' : Γ) * t) h3
      simpa using this
    have ha : (a : Γ) = a' := by
      rw [he] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext he) (Subtype.ext ha)
  calc Nat.card E * Nat.card F = Nat.card (E × F) := (Nat.card_prod E F).symm
    _ ≤ Nat.card Bb := Nat.card_le_card_of_injective f hf

theorem sup_zpowers_eq_of_card {Γ : Type*} [Group Γ] [Finite Γ] {Bb B1 : Subgroup Γ}
    (hB : Nat.card Bb = 81) (h1 : B1 ≤ Bb) (h27 : 27 ≤ Nat.card B1) {w : Γ} (hw : w ∈ Bb)
    (hwB1 : w ∉ B1) : B1 ⊔ Subgroup.zpowers w = Bb := by
  set S := B1 ⊔ Subgroup.zpowers w with hS
  have hSB : S ≤ Bb := sup_le h1 ((Subgroup.zpowers_le).2 hw)
  have hB1S : B1 ≤ S := le_sup_left
  have hwS : w ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hlt : Nat.card B1 < Nat.card S := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hB1S) fun h => hwB1 ?_
    have := Subgroup.eq_of_le_of_card_ge hB1S h.ge
    rw [this]
    exact hwS
  have hd : Nat.card S ∣ 81 := hB ▸ Subgroup.card_dvd_of_le hSB
  have hmem : Nat.card S ∈ Nat.divisors 81 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have hdiv : Nat.divisors 81 = {1, 3, 9, 27, 81} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have h81 : Nat.card S = 81 := by omega
  exact Subgroup.eq_of_le_of_card_ge hSB (by rw [hB, h81])

theorem three_mul_comm' {M : Type*} [Group M] (a0 a1 a2 b0 b1 b2 : M)
    (h10 : a1 * b0 = b0 * a1) (h20 : a2 * b0 = b0 * a2) (h21 : a2 * b1 = b1 * a2) :
    (a0 * a1 * a2) * (b0 * b1 * b2) = (a0 * b0) * (a1 * b1) * (a2 * b2) := by
  calc (a0 * a1 * a2) * (b0 * b1 * b2) = a0 * a1 * (a2 * b0) * b1 * b2 := by group
    _ = a0 * a1 * (b0 * a2) * b1 * b2 := by rw [h20]
    _ = a0 * (a1 * b0) * a2 * b1 * b2 := by group
    _ = a0 * (b0 * a1) * a2 * b1 * b2 := by rw [h10]
    _ = (a0 * b0) * a1 * (a2 * b1) * b2 := by group
    _ = (a0 * b0) * a1 * (b1 * a2) * b2 := by rw [h21]
    _ = (a0 * b0) * (a1 * b1) * (a2 * b2) := by group

theorem case_M {Γ : Type*} [Group Γ] [Finite Γ] (Bb Qs B1 : Subgroup Γ) (w : Γ)
    (hBe : IsElemAbelian 3 Bb)
    (hBmax : ∀ E : Subgroup Γ, IsElemAbelian 3 E → Bb ≤ E → E = Bb)
    (hgen : Bb ≤ B1 ⊔ Subgroup.zpowers w) (hB1 : B1 ≤ Bb) (hwB : w ∈ Bb)
    (hB1cen : ∀ y ∈ B1, ∀ s ∈ Qs, y * s = s * y)
    (hQcen : ∀ z ∈ Qs, (∀ s ∈ Qs, s * z = z * s) → z = 1)
    (hM : ∀ u ∈ Qs, ∀ v : Γ, w * v * w⁻¹ ∈ Qs → u * v = v * u)
    (u v : Γ) (hu : u ∈ Qs) (hv : v ∈ Qs) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    u * v = v * u := by
  have hw3 : w * w * w = 1 := by
    have := hBe.2 w hwB
    simpa [pow_succ] using this
  let φ : Γ ≃* Γ := MulAut.conj w⁻¹
  have hφ : ∀ x, φ x = w⁻¹ * x * w := fun x => by
    simp [φ]
  have hφ3 : ∀ x, φ (φ (φ x)) = x := by
    intro x
    rw [hφ, hφ, hφ]
    calc w⁻¹ * (w⁻¹ * (w⁻¹ * x * w) * w) * w = (w * w * w)⁻¹ * x * (w * w * w) := by group
      _ = x := by rw [hw3]; simp
  have F12 : ∀ s ∈ Qs, ∀ s' ∈ Qs, s * φ s' = φ s' * s := by
    intro s hs s' hs'
    refine hM s hs _ ?_
    rw [hφ]
    simpa [mul_assoc] using hs'
  have F23 : ∀ s ∈ Qs, ∀ s' ∈ Qs, φ s * φ (φ s') = φ (φ s') * φ s := by
    intro s hs s' hs'
    rw [← map_mul, ← map_mul, F12 s hs s' hs']
  have F13 : ∀ s ∈ Qs, ∀ s' ∈ Qs, s * φ (φ s') = φ (φ s') * s := by
    intro s hs s' hs'
    have h := F23 s' hs' s hs
    have h2 := congrArg φ h
    rw [map_mul, map_mul, hφ3] at h2
    exact h2.symm
  have hcube : ∀ x : Γ, x ^ 3 = 1 → (φ x) ^ 3 = 1 := by
    intro x hx
    rw [← map_pow, hx, map_one]
  let N : Γ → Γ := fun s => s * φ s * φ (φ s)
  have hN3 : ∀ s ∈ Qs, s ^ 3 = 1 → (N s) ^ 3 = 1 := by
    intro s hs hs3
    have c12 : Commute s (φ s) := F12 s hs s hs
    have c13 : Commute s (φ (φ s)) := F13 s hs s hs
    have c23 : Commute (φ s) (φ (φ s)) := F23 s hs s hs
    show (s * φ s * φ (φ s)) ^ 3 = 1
    rw [Commute.mul_pow (Commute.mul_left c13 c23) 3, Commute.mul_pow c12 3, hs3, hcube s hs3,
      hcube _ (hcube s hs3)]
    simp
  have hNφ : ∀ s ∈ Qs, φ (N s) = N s := by
    intro s hs
    have c12 : s * φ s = φ s * s := F12 s hs s hs
    have c13 : s * φ (φ s) = φ (φ s) * s := F13 s hs s hs
    show φ (s * φ s * φ (φ s)) = s * φ s * φ (φ s)
    rw [map_mul, map_mul, hφ3]
    calc φ s * φ (φ s) * s = φ s * (φ (φ s) * s) := by rw [mul_assoc]
      _ = φ s * (s * φ (φ s)) := by rw [← c13]
      _ = (φ s * s) * φ (φ s) := by rw [mul_assoc]
      _ = s * φ s * φ (φ s) := by rw [← c12]
  have hφc : ∀ y x : Γ, Commute y w → Commute y x → Commute y (φ x) := by
    intro y x hyw hyx
    rw [hφ]
    exact (hyw.inv_right.mul_right hyx).mul_right hyw
  have hNcomm : ∀ s ∈ Qs, ∀ b ∈ Bb, b * N s = N s * b := by
    intro s hs b hb
    have hle : B1 ⊔ Subgroup.zpowers w ≤ Subgroup.centralizer ({N s} : Set Γ) := by
      refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hyw : Commute y w := (comm_of_isElemAbelian' hBe (hB1 hy) hwB)
        have hys : Commute y s := hB1cen y hy s hs
        have h1 : Commute y (φ s) := hφc y s hyw hys
        have h2 : Commute y (φ (φ s)) := hφc y _ hyw h1
        exact ((hys.mul_right h1).mul_right h2).eq.symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have h := hNφ s hs
        rw [hφ] at h
        calc N s * w = w * (w⁻¹ * N s * w) := by group
          _ = w * N s := by rw [h]
    have := Subgroup.mem_centralizer_iff.1 (hle (hgen hb)) (N s) rfl
    exact this.symm
  have hNmem : ∀ s ∈ Qs, s ^ 3 = 1 → N s ∈ Bb := by
    intro s hs hs3
    have hel : IsElemAbelian 3 (Subgroup.zpowers (N s)) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hN3 s hs hs3, one_zpow]
    have h1 : IsElemAbelian 3 (Bb ⊔ Subgroup.zpowers (N s)) :=
      isElemAbelian_sup_of_commute' hBe hel fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute a (N s) from hNcomm s hs a ha) k).eq
    have h2 := hBmax _ h1 le_sup_left
    rw [← h2]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hNN : N u * N v = N v * N u :=
    comm_of_isElemAbelian' hBe (hNmem u hu hu3) (hNmem v hv hv3)
  have e1 := three_mul_comm' u (φ u) (φ (φ u)) v (φ v) (φ (φ v))
    (F12 v hv u hu).symm (F13 v hv u hu).symm (F23 v hv u hu).symm
  have e2 := three_mul_comm' v (φ v) (φ (φ v)) u (φ u) (φ (φ u))
    (F12 u hu v hv).symm (F13 u hu v hv).symm (F23 u hu v hv).symm
  have hXY : (u * v) * (φ u * φ v) * (φ (φ u) * φ (φ v)) =
      (v * u) * (φ v * φ u) * (φ (φ v) * φ (φ u)) := by
    rw [← e1, ← e2]
    exact hNN
  set X1 := u * v
  set X2 := φ u * φ v
  set X3 := φ (φ u) * φ (φ v)
  set Y1 := v * u
  set Y2 := φ v * φ u
  set Y3 := φ (φ v) * φ (φ u)
  have hc : Y1⁻¹ * X1 = Y2 * Y3 * (X2 * X3)⁻¹ := by
    refine eq_mul_inv_of_mul_eq ?_
    calc Y1⁻¹ * X1 * (X2 * X3) = Y1⁻¹ * (X1 * X2 * X3) := by group
      _ = Y1⁻¹ * (Y1 * Y2 * Y3) := by rw [hXY]
      _ = Y2 * Y3 := by group
  have hcQ : Y1⁻¹ * X1 ∈ Qs := by
    refine Qs.mul_mem (Qs.inv_mem (Qs.mul_mem hv hu)) (Qs.mul_mem hu hv)
  have hcc : ∀ s ∈ Qs, s * (Y1⁻¹ * X1) = (Y1⁻¹ * X1) * s := by
    intro s hs
    rw [hc]
    have a2 : Commute s Y2 := Commute.mul_right (show Commute s (φ v) from F12 s hs v hv) (show Commute s (φ u) from F12 s hs u hu)
    have a3 : Commute s Y3 := Commute.mul_right (show Commute s (φ (φ v)) from F13 s hs v hv) (show Commute s (φ (φ u)) from F13 s hs u hu)
    have b2 : Commute s X2 := Commute.mul_right (show Commute s (φ u) from F12 s hs u hu) (show Commute s (φ v) from F12 s hs v hv)
    have b3 : Commute s X3 := Commute.mul_right (show Commute s (φ (φ u)) from F13 s hs u hu) (show Commute s (φ (φ v)) from F13 s hs v hv)
    exact ((a2.mul_right a3).mul_right (b2.mul_right b3).inv_right).eq
  have h1 := hQcen _ hcQ fun s hs => hcc s hs
  have h2 : X1 = Y1 := by
    have := h1
    rwa [inv_mul_eq_one, eq_comm] at this
  exact h2

theorem isElemAbelian_subgroupOf' {Γ : Type*} [Group Γ] {p : ℕ} {E : Subgroup Γ}
    (hE : IsElemAbelian p E) (Y : Subgroup Γ) : IsElemAbelian p (E.subgroupOf Y) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE Y

theorem not_card_three_of_isMaximal {Γ : Type*} [Group Γ] [Finite Γ]
    (Y E E9 : Subgroup Γ) (hEY : E ≤ Y) (hEe : IsElemAbelian 3 E) (hE3 : Nat.card E = 3)
    (hmax : ∀ D : Subgroup Γ, D ≤ Y → IsElemAbelian 3 D → E ≤ D → D = E)
    (hE9Y : E9 ≤ Y) (hE9e : IsElemAbelian 3 E9) (hE9c : Nat.card E9 = 9) : False := by
  refine not_card_three_of_isMaximal_aux (E.subgroupOf Y) (E9.subgroupOf Y)
    (isElemAbelian_subgroupOf' hEe Y) ?_ ?_ (isElemAbelian_subgroupOf' hE9e Y) ?_
  · rw [← hE3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv
  · intro D' hD' hED'
    have hD : IsElemAbelian 3 (D'.map Y.subtype) := isElemAbelian_map' hD' _
    have hDY : D'.map Y.subtype ≤ Y := by
      rintro _ ⟨d, -, rfl⟩
      exact d.2
    have hED : E ≤ D'.map Y.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hEY]
      exact Subgroup.map_mono hED'
    have := hmax _ hDY hD hED
    rw [← Subgroup.map_subgroupOf_eq_of_le hEY] at this
    exact Subgroup.map_injective Y.subtype_injective this
  · rw [← hE9c]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE9Y).toEquiv

@[expose] def Good {Γ : Type*} [Group Γ] (R : Subgroup Γ) : Prop :=
  (∀ z ∈ R, (∀ s ∈ R, s * z = z * s) → z = 1) ∧
  (∃ u ∈ R, ∃ v ∈ R, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v ≠ v * u) ∧
  ∃ E : Subgroup Γ, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9

theorem isElemAbelian_inf_left' {Γ : Type*} [Group Γ] {p : ℕ} {E : Subgroup Γ}
    (hE : IsElemAbelian p E) (F : Subgroup Γ) : IsElemAbelian p (E ⊓ F) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hE.2 y hy.1⟩
  exact Subtype.ext (comm_of_isElemAbelian' hE a.2.1 b.2.1)

theorem abstract_main {Γ : Type*} [Group Γ] [Finite Γ]
    (Bb Q Qs : Subgroup Γ) (xb : Γ)
    (hBe : IsElemAbelian 3 Bb) (hBcard : Nat.card Bb = 81)
    (hBmax : ∀ E : Subgroup Γ, IsElemAbelian 3 E → Bb ≤ E → E = Bb)
    (hQcen : ∀ z ∈ Q, (∀ s ∈ Q, s * z = z * s) → z = 1)
    (hQs : Good Qs)
    (hcomm : ∀ u ∈ Q, ∀ v ∈ Qs, u * v = v * u)
    (hxB : xb ∈ Bb) (hx1 : xb ≠ 1) (hxc : ∀ h : Γ, h * xb = xb * h)
    (hE1 : 9 ≤ Nat.card ↥(Bb ⊓ Q))
    (hdich : ∀ w ∈ Bb, (∀ y, w * y * w⁻¹ ∈ Qs ↔ y ∈ Qs) ∨
        (∀ u ∈ Qs, ∀ v : Γ, w * v * w⁻¹ ∈ Qs → u * v = v * u)) : False := by
  obtain ⟨hQs1, ⟨u0, hu0, v0, hv0, hu03, hv03, hne⟩, E9, hE9Qs, hE9e, hE9c⟩ := hQs
  have hBc : ∀ x ∈ Bb, ∀ y ∈ Bb, x * y = y * x := fun x hx y hy => comm_of_isElemAbelian' hBe hx hy
  set E1 : Subgroup Γ := Bb ⊓ Q with hE1def
  set B1 : Subgroup Γ := Subgroup.zpowers xb ⊔ E1 with hB1def
  have hB1Bb : B1 ≤ Bb := sup_le ((Subgroup.zpowers_le).2 hxB) inf_le_left
  have hB1cen : B1 ≤ Subgroup.centralizer (Qs : Set Γ) := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro s _
      exact hxc s
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (hcomm q hq.2 s hs).symm
  have hB1cen' : ∀ y ∈ B1, ∀ s ∈ Qs, y * s = s * y := by
    intro y hy s hs
    exact (Subgroup.mem_centralizer_iff.1 (hB1cen hy) s hs).symm
  have hB1Qs : ∀ y ∈ B1, y ∈ Qs → y = 1 := by
    intro y hy hyQ
    exact hQs1 y hyQ fun s hs => (hB1cen' y hy s hs).symm
  have hxE1 : xb ∉ E1 := by
    intro h
    exact hx1 (hQcen xb h.2 fun s _ => hxc s)
  have hxB1 : xb ∈ B1 := Subgroup.mem_sup_left (Subgroup.mem_zpowers xb)
  have hE1B1 : E1 ≤ B1 := le_sup_right
  have h27 : 27 ≤ Nat.card B1 := by
    have hlt : Nat.card E1 < Nat.card B1 := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hE1B1) fun h => hxE1 ?_
      have := Subgroup.eq_of_le_of_card_ge hE1B1 h.ge
      rw [this]
      exact hxB1
    have hd1 : Nat.card B1 ∣ 81 := hBcard ▸ Subgroup.card_dvd_of_le hB1Bb
    have hd2 : Nat.card E1 ∣ 81 := hBcard ▸ Subgroup.card_dvd_of_le (inf_le_left : E1 ≤ Bb)
    have hm1 : Nat.card B1 ∈ Nat.divisors 81 := Nat.mem_divisors.2 ⟨hd1, by norm_num⟩
    have hm2 : Nat.card E1 ∈ Nat.divisors 81 := Nat.mem_divisors.2 ⟨hd2, by norm_num⟩
    have hdiv : Nat.divisors 81 = {1, 3, 9, 27, 81} := by decide
    rw [hdiv] at hm1 hm2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    omega
  have hu01 : u0 ≠ 1 := fun h => hne (by rw [h]; simp)
  by_cases hB1eq : B1 = Bb
  ·
    have hcen : ∀ y ∈ Bb, y * u0 = u0 * y := fun y hy => hB1cen' y (hB1eq ▸ hy) u0 hu0
    have hel : IsElemAbelian 3 (Subgroup.zpowers u0) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu03, one_zpow]
    have h1 : IsElemAbelian 3 (Bb ⊔ Subgroup.zpowers u0) :=
      isElemAbelian_sup_of_commute' hBe hel fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute a u0 from hcen a ha) k).eq
    have h2 := hBmax _ h1 le_sup_left
    have hu0B : u0 ∈ Bb := by
      rw [← h2]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact hu01 (hB1Qs u0 (hB1eq ▸ hu0B) hu0)
  · obtain ⟨w, hwBb, hwB1⟩ : ∃ w ∈ Bb, w ∉ B1 := by
      by_contra hcon
      push Not at hcon
      exact hB1eq (le_antisymm hB1Bb hcon)
    have hgen := sup_zpowers_eq_of_card hBcard hB1Bb h27 hwBb hwB1
    rcases hdich w hwBb with hN | hMc
    ·
      have hBN : Bb ≤ Subgroup.normalizer (Qs : Set Γ) := by
        rw [← hgen]
        refine sup_le (hB1cen.trans (Subgroup.centralizer_le_normalizer _)) ((Subgroup.zpowers_le).2 ?_)
        rw [Subgroup.mem_normalizer_iff]
        intro h
        exact (hN h).symm
      have hY3 : 3 ∣ Nat.card Qs := by
        have h9 : Nat.card E9 ∣ Nat.card Qs := Subgroup.card_dvd_of_le hE9Qs
        rw [hE9c] at h9
        exact (show 3 ∣ 9 by norm_num).trans h9
      obtain ⟨z, hzQ, hz1, hz3, hzc⟩ :=
        exists_fixed_three_element Bb Qs (isPGroup_of_isElemAbelian' hBe) hBN hY3
      have hzel : IsElemAbelian 3 (Subgroup.zpowers z) := by
        refine ⟨inferInstance, fun x hx => ?_⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
      have hzB : z ∈ Bb := by
        have h1 : IsElemAbelian 3 (Bb ⊔ Subgroup.zpowers z) :=
          isElemAbelian_sup_of_commute' hBe hzel fun a ha b hb => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
            exact (Commute.zpow_right (show Commute a z from hzc a ha) k).eq
        have h2 := hBmax _ h1 le_sup_left
        rw [← h2]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      have hzB1 : z ∉ B1 := fun h => hz1 (hB1Qs z h hzQ)
      have hgen' := sup_zpowers_eq_of_card hBcard hB1Bb h27 hzB  hzB1
      set E : Subgroup Γ := Bb ⊓ Qs with hEdef
      have hEe : IsElemAbelian 3 E := isElemAbelian_inf_left' hBe Qs
      have hzE : z ∈ E := ⟨hzB, hzQ⟩
      have hEB1 : E ⊓ B1 = ⊥ := by
        refine eq_bot_iff.2 fun y hy => ?_
        rw [Subgroup.mem_bot]
        exact hB1Qs y hy.2 hy.1.2
      have hE3 : Nat.card E = 3 := by
        have h1 := card_mul_le_of_inf_eq_bot (inf_le_left : E ≤ Bb) hB1Bb hEB1
        rw [hBcard] at h1
        have h2 : Nat.card (Subgroup.zpowers z) ∣ Nat.card E :=
          Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).2 hzE)
        have h3 : Nat.card (Subgroup.zpowers z) = 3 := by
          rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
        rw [h3] at h2
        have h4 : 0 < Nat.card E := Nat.card_pos
        have h5 : Nat.card E * 27 ≤ 81 := le_trans (Nat.mul_le_mul_left _ h27) h1
        omega
      refine not_card_three_of_isMaximal Qs E E9 inf_le_right hEe hE3 ?_ hE9Qs hE9e hE9c
      intro D hDQ hDe hED
      have hzD : z ∈ D := hED hzE
      have hcenD : ∀ d ∈ D, Bb ≤ Subgroup.centralizer ({d} : Set Γ) := by
        intro d hd
        rw [← hgen']
        refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (hB1cen' y hy h (hDQ hd)).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact comm_of_isElemAbelian' hDe hd hzD
      have h1 : IsElemAbelian 3 (Bb ⊔ D) :=
        isElemAbelian_sup_of_commute' hBe hDe fun a ha b hb =>
          (Subgroup.mem_centralizer_iff.1 (hcenD b hb ha) b (Set.mem_singleton b)).symm
      have h2 := hBmax _ h1 le_sup_left
      have hDB : D ≤ Bb := by rw [← h2]; exact le_sup_right
      exact le_antisymm (fun d hd => ⟨hDB hd, hDQ hd⟩) hED
    · exact hne (case_M Bb Qs B1 w hBe hBmax hgen.ge hB1Bb hwBb hB1cen' hQs1 hMc u0 v0 hu0 hv0
        hu03 hv03)


theorem center_quotient_eq_bot {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    (hNc : N ≤ Subgroup.center Γ) (hZN : Subgroup.center Γ ≤ N)
    (hperf : commutator (Γ ⧸ N) = ⊤) : Subgroup.center (Γ ⧸ N) = ⊥ := by
  rw [eq_bot_iff]
  intro zb hz
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zb
  have hn : ∀ a : Γ, z * a * z⁻¹ * a⁻¹ ∈ N := by
    intro a
    have := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk a)
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, ← this]
  have cen_conj : ∀ u X : Γ, (∀ g, g * u = u * g) → u * X * u⁻¹ = X := by
    intro u X cu
    rw [← cu X, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm : ∀ a b : Γ, z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    intro a b
    set u := z * a * z⁻¹ * a⁻¹ with hu
    set v := z * b * z⁻¹ * b⁻¹ with hv
    have hu' : z * a * z⁻¹ = u * a := by rw [hu]; group
    have hv' : z * b * z⁻¹ = v * b := by rw [hv]; group
    have cu : ∀ g, g * u = u * g := fun g => Subgroup.mem_center_iff.1 (hNc (hn a)) g
    have cv : ∀ g, g * v = v * g := fun g => Subgroup.mem_center_iff.1 (hNc (hn b)) g
    calc z * (a * b * a⁻¹ * b⁻¹) * z⁻¹
        = (z * a * z⁻¹) * (z * b * z⁻¹) * (z * a * z⁻¹)⁻¹ * (z * b * z⁻¹)⁻¹ := by group
      _ = (u * a) * (v * b) * (u * a)⁻¹ * (v * b)⁻¹ := by rw [hu', hv']
      _ = u * (a * v * b * a⁻¹) * u⁻¹ * (b⁻¹ * v⁻¹) := by group
      _ = (a * v * b * a⁻¹) * (b⁻¹ * v⁻¹) := by rw [cen_conj u _ cu]
      _ = (a * v) * (b * a⁻¹ * b⁻¹ * v⁻¹) := by group
      _ = v * a * (b * a⁻¹ * b⁻¹ * v⁻¹) := by rw [cv a]
      _ = v * (a * b * a⁻¹ * b⁻¹) * v⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := cen_conj v _ cv
  have hsup : commutator Γ ⊔ N = ⊤ := by
    have h1 : (commutator Γ).map (QuotientGroup.mk' N) = commutator (Γ ⧸ N) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have := Subgroup.comap_map_eq (QuotientGroup.mk' N) (commutator Γ)
    rw [h1, hperf, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  have hle : commutator Γ ⊔ N ≤ Subgroup.centralizer ({z} : Set Γ) := by
    refine sup_le ?_ (fun n hn' => ?_)
    · rw [commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := hcomm a b
      rw [commutatorElement_def]
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_center_iff.1 (hNc hn') h)
  have hzc : z ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_centralizer_iff.1 (hle (hsup ▸ Subgroup.mem_top g)) z rfl
    exact this.symm
  have : z ∈ N := hZN hzc
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff z).2 this


theorem scalars_subgroupOf_eq_center {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL (Fin 3) K))
    (hcard : Nat.card (Subgroup.center ↥H) = 3) (hr : Nat.card (rootsOfUnity 3 K) = 3)
    (hmem : ∀ ζ : Kˣ, ζ ^ 3 = 1 → Matrix.GeneralLinearGroup.scalar (Fin 3) ζ ∈ H) :
    (StatedScalars (Fin 3) K).subgroupOf H = Subgroup.center ↥H := by
  have hle : (StatedScalars (Fin 3) K).subgroupOf H ≤ Subgroup.center ↥H := by
    intro x hx
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 hx)
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : GL (Fin 3) K) * x = x * g
    rw [← hc]
    exact (Matrix.GeneralLinearGroup.scalar_commute c (g : GL (Fin 3) K)).symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard]
  let φ : rootsOfUnity 3 K → (StatedScalars (Fin 3) K).subgroupOf H := fun ζ =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Kˣ), hmem _ ((mem_rootsOfUnity 3 (ζ : Kˣ)).mp ζ.2)⟩,
      Subgroup.mem_subgroupOf.2 ⟨(ζ : Kˣ), rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro ζ₁ ζ₂ h
    have h' := congrArg (fun z : ↥((StatedScalars (Fin 3) K).subgroupOf H) =>
      ((((z : ↥H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)) h
    simp only [φ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h'
    exact Subtype.ext (Units.ext h')
  have := Nat.card_le_card_of_injective φ hφ
  rwa [hr] at this

theorem scalar_mem_statedSL {K : Type} [Field K] {c : Kˣ} (hc : c ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSL 3 K := by
  apply Subgroup.subset_closure
  show (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K).1.det = 1
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hc,
    Units.val_one]

theorem center_statedProj_SL {K : Type} [Field K] [Finite K] (h : Nat.card K % 3 = 1)
    (hperf : commutator (StatedProj (StatedSL 3 K)) = ⊤) :
    Subgroup.center (StatedProj (StatedSL 3 K)) = ⊥ := by
  have h3 : 3 ∣ Nat.card K - 1 := by omega
  have hZ : Nat.card (Subgroup.center ↥(StatedSL 3 K)) = 3 := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSL_three h3
  have hr := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_rootsOfUnity_three h3
  have heq := scalars_subgroupOf_eq_center (StatedSL 3 K) hZ hr (fun ζ hζ => scalar_mem_statedSL hζ)
  exact center_quotient_eq_bot _ heq.le heq.ge hperf

theorem center_statedProj_SU {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (h : q % 3 = 2) (hperf : commutator (StatedProj (StatedSU 3 q K)) = ⊤) :
    Subgroup.center (StatedProj (StatedSU 3 q K)) = ⊥ := by
  have hq3 : 3 ∣ q + 1 := by omega
  have hq2 := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.two_le_of_card_eq_sq hK
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [hK, CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left hq3 _
  have hZ : Nat.card (Subgroup.center ↥(StatedSU 3 q K)) = 3 := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSU_three hK hq3
  have hr := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_rootsOfUnity_three h3
  have heq := scalars_subgroupOf_eq_center (StatedSU 3 q K) hZ hr
    (fun ζ hζ => (CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.scalar_mem (by omega) hq3 hζ : _ ∈ StatedSU 3 q K))
  exact center_quotient_eq_bot _ heq.le heq.ge hperf


theorem perfect_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : commutator A = ⊤) : commutator B = ⊤ := by
  have h1 : (commutator A).map e.toMonoidHom = commutator B := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← h1, h, Subgroup.map_top_of_surjective _ e.surjective]

theorem center_eq_bot_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz a]
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using this)

theorem center_barX_of_isExtremalType {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (hty : IsExtremalType (barOf 3 L)) :
    Subgroup.center ↥(barX 3 X L) = ⊥ := by
  have e := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  have hperfX : commutator ↥(barX 3 X L) = ⊤ := hL.2.2.1.2.2.1
  have hperf : commutator (barOf 3 L) = ⊤ := perfect_of_mulEquiv' e.symm hperfX
  refine center_eq_bot_of_mulEquiv' e.symm ?_
  rcases hty with ⟨K, _, _, h, ⟨f⟩⟩ | ⟨K, _, _, q, hK, hq, -, ⟨f⟩⟩
  · exact center_eq_bot_of_mulEquiv' f (center_statedProj_SL h (perfect_of_mulEquiv' f hperf))
  · exact center_eq_bot_of_mulEquiv' f (center_statedProj_SU hK hq (perfect_of_mulEquiv' f hperf))

section GLevel

variable {G : Type*} [Group G] [Finite G]

theorem barX_gLBConj_eq' (p : ℕ) {M : Subgroup G} {g : G} (hg : g ∈ M) (K : Subgroup G) :
    barX p M (GLBConj g K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) (barX p M K) := by
  refine le_antisymm (barX_le_gLBConj p hg K) ?_
  have h := barX_le_gLBConj p (M.inv_mem hg) (GLBConj g K)
  rw [gLBConj_inv_gLBConj] at h
  have h2 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) h
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨g⁻¹, M.inv_mem hg⟩ : ↥M) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, gLBConj_gLBConj_inv] at h2
  exact h2

theorem gLBConj_eq_of_mem' {e : G} {H : Subgroup G} (he : e ∈ H) : GLBConj e H = H := by
  ext y
  rw [mem_gLBConj]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem (H.inv_mem he) h) he
    simpa [mul_assoc] using this
  · intro h
    exact H.mul_mem (H.mul_mem he h) (H.inv_mem he)

theorem mem_normalizer_of_barX_normalizer' {X J : Subgroup G} (hJ : GLAPComponent 3 X J) {e : G}
    (heX : e ∈ X)
    (hy : (QuotientGroup.mk (⟨e, heX⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈
      Subgroup.normalizer ((barX 3 X J : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) :
    e ∈ Subgroup.normalizer (J : Set G) := by
  have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ e
  rw [gLBConj_eq_of_mem' heX] at h1
  have hbar : barX 3 X (GLBConj e J) = barX 3 X J := by
    rw [barX_gLBConj_eq' 3 heX J]
    exact gLBConj_eq_of_mem_normalizer hy
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique h1 hJ hbar)

theorem mem_barX_iff' (p : ℕ) (X K : Subgroup G) (z : ↥X ⧸ GLAPPrimeCore p ↥X) :
    z ∈ barX p X K ↔ ∃ x : ↥X, (x : G) ∈ K ∧ (QuotientGroup.mk x : ↥X ⧸ GLAPPrimeCore p ↥X) = z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).2 hx, rfl⟩

theorem comp_le_normalizer {X L M : Subgroup G} (hL : GLAPComponent 3 X L)
    (hM : GLAPComponent 3 X M) : M ≤ Subgroup.normalizer (L : Set G) := by
  by_cases hML : M = L
  · subst hML
    exact Subgroup.le_normalizer
  intro m hm
  have hmX : m ∈ X := hM.1 hm
  have hbar : barX 3 X M ≠ barX 3 X L := fun h => hML (glaPComponent_unique hM hL h)
  have hcomm : ⁅barX 3 X M, barX 3 X L⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hM.2.2.1 hL.2.2.1 hbar
  refine mem_normalizer_of_barX_normalizer' hL hmX ?_
  have hmk : (QuotientGroup.mk (⟨m, hmX⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X M :=
    ⟨⟨m, hmX⟩, (Subgroup.mem_subgroupOf).2 hm, rfl⟩
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  exact Subgroup.centralizer_le_normalizer _ (hcen hmk)

theorem glaPLayer_le' (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ h => h.1

theorem normal_central_or_eq {H : Type*} [Group H] {Q N : Subgroup H} (hQ : CFSG.Open.IsQuasisimple ↥Q)
    (hNQ : N ≤ Q) (hnorm : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) :
    (∀ n ∈ N, ∀ q ∈ Q, n * q = q * n) ∨ N = Q := by
  have hN : (N.subgroupOf Q).Normal := ⟨fun n hn a => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm a a.2 n hn⟩
  obtain ⟨hperf, hs⟩ := hQ
  have hnorm' : ((N.subgroupOf Q).map (QuotientGroup.mk' (Subgroup.center ↥Q))).Normal :=
    Subgroup.Normal.map hN (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal ((N.subgroupOf Q).map (QuotientGroup.mk' (Subgroup.center ↥Q)))
    with h | h
  · left
    intro n hn q hq
    have h1 : QuotientGroup.mk' (Subgroup.center ↥Q) ⟨n, hNQ hn⟩ ∈
        (N.subgroupOf Q).map (QuotientGroup.mk' (Subgroup.center ↥Q)) :=
      Subgroup.mem_map_of_mem _ ((Subgroup.mem_subgroupOf).2 hn)
    rw [h, Subgroup.mem_bot] at h1
    have hc := (QuotientGroup.eq_one_iff _).mp h1
    have := (Subgroup.mem_center_iff.mp hc) ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  · right
    have hsup : N.subgroupOf Q ⊔ Subgroup.center ↥Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center ↥Q)) (N.subgroupOf Q)
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator ↥Q ≤ N.subgroupOf Q :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hle
    exact le_antisymm hNQ (Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp hle))

end GLevel

section GLevel2

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem barX_mono' (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hc)), rfl⟩

theorem barX_ne_bot_of_isPGroup {X F : Subgroup G} (hFX : F ≤ X) (hF3 : IsPGroup 3 F)
    (hFne : F ≠ ⊥) : barX 3 X F ≠ ⊥ := by
  intro h
  obtain ⟨f, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
  have hinj := injective_barX_comp Nat.prime_three hF3 hFX
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) ⟨(f : G), hFX f.2⟩ ∈ barX 3 X F :=
    ⟨⟨(f : G), hFX f.2⟩, (Subgroup.mem_subgroupOf).2 f.2, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have : (((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (F.subgroupOf X).subtype)
      ⟨⟨(f : G), hFX f.2⟩, (Subgroup.mem_subgroupOf).2 f.2⟩) =
      ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (F.subgroupOf X).subtype) 1 := by
    simpa using hmem
  have h2 := hinj this
  apply hf1
  have h3 := congrArg (fun t : ↥(F.subgroupOf X) => ((t : ↥X) : G)) h2
  exact Subtype.ext (by simpa using h3)

theorem layer_closure_eq {X L J F : Subgroup G} (hL : GLAPComponent 3 X L) (hJL : J ≤ L)
    (hFJ : F ≤ J) (hF3 : IsPGroup 3 F) (hFne : F ≠ ⊥)
    (hZ : Subgroup.center ↥(barX 3 X L) = ⊥) :
    (⨆ g ∈ GLAPLayer 3 X, GLBConj g J) = L := by
  set K : Subgroup G := ⨆ g ∈ GLAPLayer 3 X, GLBConj g J with hK
  have hLlay : L ≤ GLAPLayer 3 X := le_sSup hL
  have hlayN : GLAPLayer 3 X ≤ Subgroup.normalizer (L : Set G) :=
    sSup_le fun M hM => comp_le_normalizer hL hM
  have hKL : K ≤ L := by
    refine iSup₂_le fun g hg => ?_
    calc GLBConj g J ≤ GLBConj g L := gLBConj_mono g hJL
      _ = L := gLBConj_eq_of_mem_normalizer (hlayN hg)
  have hJK : J ≤ K := by
    have : GLBConj 1 J ≤ K := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 X) => GLBConj g J) 1
      (Subgroup.one_mem _)
    rwa [gLBConj_one] at this
  have hkey : ∀ l ∈ L, GLBConj l K ≤ K := by
    intro l hl
    have hlay : l ∈ GLAPLayer 3 X := hLlay hl
    have e : GLBConj l K = ⨆ g ∈ GLAPLayer 3 X, GLBConj l (GLBConj g J) := by
      simp only [hK, GLBConj, Subgroup.map_iSup]
    rw [e]
    refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 X) => GLBConj g J) (g * l)
      (Subgroup.mul_mem _ hg hlay) le_rfl
  have hKnorm : L ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (hkey l hl) ?_
    have h := gLBConj_mono l (hkey l⁻¹ (L.inv_mem hl))
    rwa [gLBConj_gLBConj_inv] at h
  have hKnormal : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hKnorm
  have hKsub : IsSubnormal K X := IsSubnormal.step hKL hKnormal hL.2.1
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 X L) := hL.2.2.1.2.2
  have hbKL : barX 3 X K ≤ barX 3 X L := barX_mono' 3 hKL
  have hnorm : ∀ q ∈ barX 3 X L, ∀ n ∈ barX 3 X K, q * n * q⁻¹ ∈ barX 3 X K := by
    intro q hq' n hn
    obtain ⟨l, hlL, rfl⟩ := (mem_barX_iff' 3 X L q).1 hq'
    obtain ⟨k, hkK, rfl⟩ := (mem_barX_iff' 3 X K n).1 hn
    refine (mem_barX_iff' 3 X K _).2 ⟨l * k * l⁻¹, ?_, by simp⟩
    have := (Subgroup.mem_normalizer_iff.1 (hKnorm hlL) (k : G)).1 hkK
    simpa using this
  have hF1 : F ≤ X := hFJ.trans (hJL.trans hL.1)
  have hKne : barX 3 X K ≠ ⊥ := by
    intro h
    have : barX 3 X F ≤ ⊥ := h ▸ barX_mono' 3 (hFJ.trans hJK)
    exact barX_ne_bot_of_isPGroup hF1 hF3 hFne (le_bot_iff.1 this)
  rcases normal_central_or_eq hq hbKL hnorm with hc | heq
  · exfalso
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hKne
    have hzc : (⟨z, hbKL z.2⟩ : ↥(barX 3 X L)) ∈ Subgroup.center ↥(barX 3 X L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (by simpa using (hc z z.2 w w.2).symm)
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hz1 (Subtype.ext (by simpa using congrArg Subtype.val hzc))
  · by_contra hne
    exact hL.2.2.2 K (lt_of_le_of_ne hKL hne) hKsub heq

end GLevel2

section GLevel3

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def KOf (L A : Subgroup G) (x : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
    GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))

theorem A_eq_sup {A : Subgroup G} {b x : G} (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9)
    (hbA : b ∈ A) (hxA : x ∈ A) (hb1 : b ≠ 1) (hxb : x ∉ Subgroup.zpowers b) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers b = A := by
  have hb3 : b ^ 3 = 1 := hA.2 b hbA
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hcard3 : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hcomm : ∀ h ∈ Subgroup.zpowers b, h * x = x * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute b x from comm_of_isElemAbelian' hA hbA hxA) k).eq
  have hcard := card_sup_zpowers_of_pow_three_eq_one hx3 hxb hcomm
  rw [hcard3] at hcard
  have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers x ≤ A :=
    sup_le ((Subgroup.zpowers_le).2 hbA) ((Subgroup.zpowers_le).2 hxA)
  have heq : Subgroup.zpowers b ⊔ Subgroup.zpowers x = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hAc, hcard])
  rw [sup_comm]
  exact heq

omit [Finite G] in
theorem inf_centralizer_eq_of_A {A L : Subgroup G} {b x : G} (hAeq : Subgroup.zpowers x ⊔ Subgroup.zpowers b = A)
    (hxA : x ∈ A) (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) :
    L ⊓ Subgroup.centralizer (A : Set G) = L ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨hyL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subgroup.mem_centralizer_iff.1 hyC h hxA
  · intro hy
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨hyL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (Subgroup.mem_centralizer_iff.1 hyC x rfl).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (Subgroup.mem_centralizer_iff.1 (hLb hyL) b (Set.mem_singleton b)).symm
    rw [hAeq] at hle
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) y rfl).symm

theorem centralizer_eq_of_mem_zpowers {B : Subgroup G} (hB : IsElemAbelian 3 B) {b x : G}
    (hbB : b ∈ B) (hb1 : b ≠ 1) (hx : x ∈ Subgroup.zpowers b) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hxz : Subgroup.zpowers x ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).2 hx
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    have hd : Nat.card (Subgroup.zpowers x) ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hxz
    have hn1 : Nat.card (Subgroup.zpowers x) ≠ 1 := by
      intro h
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
      exact hx1 h
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd h hn1
    · exact h
  have heq : Subgroup.zpowers x = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hxz (by rw [hcard, hxcard])
  have hcent : ∀ {u v : G}, v ∈ Subgroup.zpowers u →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({v} : Set G) := by
    intro u v hv y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hyu : u * y = y * u := hy u rfl
    exact (Commute.zpow_left (show Commute u y from hyu) k).eq
  exact le_antisymm (hcent (heq ▸ Subgroup.mem_zpowers b)) (hcent hx)

theorem kOf_data {B L A : Subgroup G} {b x : G} (hBe : IsElemAbelian 3 B)
    (hw : IsExtremalWitness B b L A) (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hZL : Subgroup.center ↥(barX 3 (Subgroup.centralizer ({b} : Set G)) L) = ⊥)
    (hZK : x ∉ Subgroup.zpowers b →
      Subgroup.center ↥(barX 3 (Subgroup.centralizer ({x} : Set G)) (KOf L A x)) = ⊥) :
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) (KOf L A x) ∧
      Subgroup.center ↥(barX 3 (Subgroup.centralizer ({x} : Set G)) (KOf L A x)) = ⊥ := by
  obtain ⟨hbB, hb1, hLcomp, -, -, ⟨hFcard, hA, hbA, hfld, hFJ, -⟩, hx3⟩ := hw
  by_cases hxb : x ∈ Subgroup.zpowers b
  · have hCx := centralizer_eq_of_mem_zpowers hBe hbB hb1 hxb hx1
    have hL' : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L := by
      rw [hCx]
      exact hLcomp
    have hZL' : Subgroup.center ↥(barX 3 (Subgroup.centralizer ({x} : Set G)) L) = ⊥ := by
      rw [hCx]
      exact hZL
    have hF3 : IsPGroup 3 ↥(B ⊓ L) := isPGroup_of_isElemAbelian' (isElemAbelian_inf_left' hBe L)
    have hFne : B ⊓ L ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hFcard
      omega
    have hJL : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≤ L :=
      (glaPLayer_le' 3 _).trans inf_le_left
    have := layer_closure_eq hL' hJL hFJ hF3 hFne hZL'
    unfold KOf
    rw [this]
    exact ⟨hL', hZL'⟩
  · have hAeq := A_eq_sup hA.2.1 (by simpa using hA.2.2) hbA hxA hb1 hxb
    have hinf := inf_centralizer_eq_of_A hAeq hxA hLcomp.1
    have h1 := (hx3 x (hA.1 hxA) hx1 (hfld x hxA)).1
    have hK : KOf L A x = pumpUp L x := by
      unfold KOf pumpUp
      rw [hinf]
    rw [← hK] at h1
    exact ⟨h1, hZK hxb⟩

end GLevel3

theorem exists_noncomm_three {Γ : Type*} [Group Γ] {Q : Subgroup Γ}
    (hq : CFSG.Open.IsQuasisimple ↥Q) (hZ : ∀ z ∈ Q, (∀ s ∈ Q, s * z = z * s) → z = 1) {u : Γ}
    (hu : u ∈ Q) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) :
    ∃ v ∈ Q, v ^ 3 = 1 ∧ u * v ≠ v * u := by
  by_contra hcon
  push Not at hcon
  set u' : ↥Q := ⟨u, hu⟩ with hu'
  set M : Subgroup ↥Q := Subgroup.normalClosure {u'} with hM
  set N : Subgroup Γ := M.map Q.subtype with hN
  have hNQ : N ≤ Q := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hnorm : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N := by
    rintro q hq' _ ⟨m, hm, rfl⟩
    refine ⟨⟨q, hq'⟩ * m * ⟨q, hq'⟩⁻¹, ?_, rfl⟩
    have hMn : M.Normal := Subgroup.normalClosure_normal
    exact hMn.conj_mem m hm ⟨q, hq'⟩
  have hu'M : u ∈ N := ⟨u', Subgroup.subset_normalClosure rfl, rfl⟩
  rcases normal_central_or_eq hq hNQ hnorm with hc | heq
  · exact hu1 (hZ u hu fun s hs => (hc u hu'M s hs).symm)
  · have hMle : M ≤ Subgroup.centralizer ({u'} : Set ↥Q) := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h3 : ((c * u' * c⁻¹ : ↥Q) : Γ) ^ 3 = 1 := by
        have : ((c * u' * c⁻¹ : ↥Q)) ^ 3 = 1 := by
          rw [conj_pow]
          have : u' ^ 3 = 1 := Subtype.ext hu3
          rw [this]; simp
        exact congrArg Subtype.val this
      exact Subtype.ext (hcon _ (c * u' * c⁻¹).2 h3)
    refine hu1 (hZ u hu fun s hs => ?_)
    have hsN : s ∈ N := heq ▸ hs
    obtain ⟨m, hm, rfl⟩ := hsN
    have := Subgroup.mem_centralizer_iff.1 (hMle hm) u' rfl
    exact (congrArg Subtype.val this).symm

theorem good_of_component {Γ : Type*} [Group Γ] {Q F : Subgroup Γ}
    (hq : CFSG.Open.IsQuasisimple ↥Q) (hZ : ∀ z ∈ Q, (∀ s ∈ Q, s * z = z * s) → z = 1)
    (hFQ : F ≤ Q) (hFe : IsElemAbelian 3 F) (hFc : Nat.card F = 9) : Good Q := by
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFc
    omega
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
  have hu3 : (u : Γ) ^ 3 = 1 := hFe.2 u u.2
  have hu1' : (u : Γ) ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨v, hv, hv3, hne⟩ := exists_noncomm_three hq hZ (hFQ u.2) hu1' hu3
  exact ⟨hZ, ⟨u, hFQ u.2, v, hv, hu3, hv3, hne⟩, F, hFQ, hFe, hFc⟩

theorem good_map {Γ : Type*} [Group Γ] {R : Subgroup Γ} (hR : Good R) (φ : Γ ≃* Γ) :
    Good (R.map φ.toMonoidHom) := by
  obtain ⟨hc, ⟨u, hu, v, hv, hu3, hv3, hne⟩, E, hER, hEe, hEc⟩ := hR
  refine ⟨?_, ⟨φ u, ⟨u, hu, rfl⟩, φ v, ⟨v, hv, rfl⟩, ?_, ?_, ?_⟩, E.map φ.toMonoidHom,
    Subgroup.map_mono hER, isElemAbelian_map' hEe _, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ hcomm
    have : z = 1 := hc z hz fun s hs => φ.injective (by
      simpa using hcomm (φ s) ⟨s, hs, rfl⟩)
    rw [this]
    simp
  · rw [← map_pow, hu3, map_one]
  · rw [← map_pow, hv3, map_one]
  · intro h
    apply hne
    exact φ.injective (by simpa [map_mul] using h)
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact hEc

section GLevel5

variable {G : Type} [Group G] [Finite G]

theorem card_barX' {C E : Subgroup G} (hE : IsPGroup 3 E) (hEC : E ≤ C) :
    Nat.card (barX 3 C E) = Nat.card E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).comp (E.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp Nat.prime_three hE hEC
  have hrange : f.range = barX 3 C E := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]

theorem barX_gLBConj_eq_map {X K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    barX 3 X (GLBConj g K) =
      (barX 3 X K).map (barAut 3 X ⟨g⁻¹, inv_mem hg⟩).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (mem_barX_iff' 3 X _ z).1 hz
    have hy' : g * (y : G) * g⁻¹ ∈ K := mem_gLBConj.1 hy
    have hyX : g * (y : G) * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hg (y : G)).1 y.2
    refine ⟨QuotientGroup.mk (⟨g * (y : G) * g⁻¹, hyX⟩ : ↥X), (mem_barX_iff' 3 X K _).2
      ⟨⟨g * (y : G) * g⁻¹, hyX⟩, hy', rfl⟩, ?_⟩
    show barAut 3 X ⟨g⁻¹, inv_mem hg⟩ (QuotientGroup.mk _) = _
    rw [barAut_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [mul_assoc]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_barX_iff' 3 X K w).1 hw
    show barAut 3 X ⟨g⁻¹, inv_mem hg⟩ (QuotientGroup.mk _) ∈ _
    rw [barAut_mk]
    refine (mem_barX_iff' 3 X _ _).2 ⟨_, ?_, rfl⟩
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, mem_gLBConj]
    simpa [mul_assoc] using hy

end GLevel5

@[expose] def Gap515CentreK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b : G, ∀ L A : Subgroup G, IsExtremalWitness B b L A →
      ∀ x ∈ A, x ≠ 1 → x ∉ Subgroup.zpowers b →
        Subgroup.center ↥(barX 3 (Subgroup.centralizer ({x} : Set G)) (KOf L A x)) = ⊥

theorem le_kOf {G : Type} [Group G] [Finite G] (L A : Subgroup G) (x : G) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≤ KOf L A x := by
  have : GLBConj 1 (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G))) ≤ KOf L A x :=
    le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G))) =>
      GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))) 1 (Subgroup.one_mem _)
  rwa [gLBConj_one] at this

theorem mem_normalizer_centralizer {G : Type*} [Group G] {x g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G), ∀ y : G,
      y ∈ Subgroup.centralizer ({x} : Set G) → g * y * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro g hg y hy
    have hxg : g⁻¹ * x * g ∈ Subgroup.zpowers x := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 (Subgroup.mem_zpowers x)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxg
    have hyx : x * y = y * x := (Subgroup.mem_centralizer_iff.1 hy x rfl)
    have hcomm : (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g) := by
      rw [← hk]
      exact (Commute.zpow_left (show Commute x y from hyx) k).eq
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = g * y * g⁻¹ * x := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro hy
    have := key g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using this

theorem lemma515_of_inputs (hZK : Gap515CentreK) : Lemma515 := by
  intro G _ _ m hS hC B hB b L A hw x hxA hx1
  have hBe : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 81 := by
    have h := hB.1.2.1
    rw [hC.2.1] at h
    simpa using h
  have hSC : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB
  have hw' := hw
  obtain ⟨hbB, hb1, hLcomp, -, hty, ⟨hFcard, hA, hbA, hfld, hFJ, -⟩, -⟩ := hw
  have hxB : x ∈ B := hA.1 hxA
  set X : Subgroup G := Subgroup.centralizer ({x} : Set G) with hXdef
  have hxX : x ∈ X := by
    rw [hXdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hBX : B ≤ X := by
    intro y hy
    rw [hXdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact comm_of_isElemAbelian' hBe hxB hy
  obtain ⟨hKc, hZK⟩ := kOf_data hBe hw' hxA hx1
    (center_barX_of_isExtremalType hLcomp hty)
    (fun hxb => hZK G m hS hC B hB b L A hw' x hxA hx1 hxb)
  set K : Subgroup G := KOf L A x with hKdef
  have hFK : B ⊓ L ≤ K := hFJ.trans (le_kOf L A x)
  have hFe : IsElemAbelian 3 (B ⊓ L) := isElemAbelian_inf_left' hBe L
  have hF3 : IsPGroup 3 ↥(B ⊓ L) := isPGroup_of_isElemAbelian' hFe
  have hFX : B ⊓ L ≤ X := inf_le_left.trans hBX
  have hFbarc : Nat.card (barX 3 X (B ⊓ L)) = 9 := by
    rw [card_barX' hF3 hFX]
    exact hFcard
  have hFbare : IsElemAbelian 3 (barX 3 X (B ⊓ L)) := isElemAbelian_barX hFe
  have hQcen : ∀ z ∈ barX 3 X K, (∀ s ∈ barX 3 X K, s * z = z * s) → z = 1 := by
    intro z hz hcomm
    have hzc : (⟨z, hz⟩ : ↥(barX 3 X K)) ∈ Subgroup.center ↥(barX 3 X K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcomm w w.2)
    rw [hZK, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  have hGoodQ : Good (barX 3 X K) :=
    good_of_component hKc.2.2.1.2.2 hQcen (barX_mono' 3 hFK) hFbare hFbarc
  intro g hg
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_centralizer hg
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  set K' : Subgroup G := GLBConj g K with hK'def
  have hK' : GLAPComponent 3 X K' := by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hKc g
    rwa [mem_normalizer_iff_gLBConj_eq.1 hgX] at this
  have hbar : barX 3 X K' ≠ barX 3 X K := fun h => hne (glaPComponent_unique hK' hKc h)
  have hcommQ : ⁅barX 3 X K, barX 3 X K'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hKc.2.2.1 hK'.2.2.1 hbar.symm
  have hQs : Good (barX 3 X K') := by
    rw [hK'def, barX_gLBConj_eq_map hgX]
    exact good_map hGoodQ _
  have hinj := injective_barX_comp Nat.prime_three (isPGroup_of_isElemAbelian' hBe) hBX
  refine abstract_main (barX 3 X B) (barX 3 X K) (barX 3 X K')
    (QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) (isElemAbelian_barX hBe) ?_
    (fun E hE hle => eq_barX_of_isSCp Nat.prime_three hBX hSC hE hle) hQcen hQs ?_ ?_ ?_ ?_ ?_ ?_
  · rw [card_barX' (isPGroup_of_isElemAbelian' hBe) hBX]
    exact hBcard
  · have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcommQ
    intro u hu v hv
    exact (Subgroup.mem_centralizer_iff.1 (h1 hu) v hv).symm
  · exact ⟨⟨x, hxX⟩, (Subgroup.mem_subgroupOf).2 hxB, rfl⟩
  · intro h
    have h2 := @hinj ⟨⟨x, hxX⟩, (Subgroup.mem_subgroupOf).2 hxB⟩ 1 (by simpa using h)
    have h3 := congrArg (fun t : ↥(B.subgroupOf X) => ((t : ↥X) : G)) h2
    exact hx1 (by simpa using h3)
  · intro h
    induction h using QuotientGroup.induction_on with | _ y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 y.2 x rfl).symm
  · have hle : barX 3 X (B ⊓ L) ≤ barX 3 X B ⊓ barX 3 X K :=
      le_inf (barX_mono' 3 inf_le_left) (barX_mono' 3 hFK)
    have := Subgroup.card_le_of_le hle
    rwa [hFbarc] at this
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := (mem_barX_iff' 3 X B w).1 hw
    have hyX : (y : G) ∈ X := y.2
    by_cases hyn : (y : G) ∈ Subgroup.normalizer (K' : Set G)
    · left
      have h1 := barX_gLBConj_eq' 3 hyX K'
      rw [mem_normalizer_iff_gLBConj_eq.1 hyn] at h1
      intro z
      have h2 := mem_gLBConj (g := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨(y : G), hyX⟩) (y := z)
        (H := barX 3 X K')
      rw [← h1] at h2
      exact h2.symm
    · right
      have hne'' : GLBConj (y : G) K' ≠ K' := fun h => hyn (mem_normalizer_iff_gLBConj_eq.2 h)
      have hK'' : GLAPComponent 3 X (GLBConj (y : G) K') := by
        have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK' (y : G)
        rwa [gLBConj_eq_of_mem' hyX] at this
      have hbar'' : barX 3 X (GLBConj (y : G) K') ≠ barX 3 X K' := fun h =>
        hne'' (glaPComponent_unique hK'' hK' h)
      have hcomm'' : ⁅barX 3 X K', barX 3 X (GLBConj (y : G) K')⁆ = ⊥ :=
        CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK'.2.2.1 hK''.2.2.1 hbar''.symm
      have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm''
      have h1 := barX_gLBConj_eq' 3 hyX K'
      intro u hu v hv
      have hvK'' : v ∈ barX 3 X (GLBConj (y : G) K') := by
        rw [h1, mem_gLBConj]
        exact hv
      exact (Subgroup.mem_centralizer_iff.1 (hcen hu) v hvK'').symm

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem layer_closure_le {X L J : Subgroup G} (hL : GLAPComponent 3 X L) (hJL : J ≤ L) :
    (⨆ g ∈ GLAPLayer 3 X, GLBConj g J) ≤ L := by
  have hlayN : GLAPLayer 3 X ≤ Subgroup.normalizer (L : Set G) :=
    sSup_le fun M hM => comp_le_normalizer hL hM
  refine iSup₂_le fun g hg => ?_
  calc GLBConj g J ≤ GLBConj g L := gLBConj_mono g hJL
    _ = L := gLBConj_eq_of_mem_normalizer (hlayN hg)

theorem mem_normalizer_primeCore {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

theorem commutator_le_primeCore {K J : Subgroup G} {b : G} (hJK : J ≤ K)
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hbJ : J ≤ Subgroup.centralizer ({b} : Set G)) :
    ⁅Subgroup.zpowers b, J ⊔ GLAPPrimeCoreOf 3 K⁆ ≤ GLAPPrimeCoreOf 3 K := by
  set O := GLAPPrimeCoreOf 3 K with hO
  have hbO : b ∈ Subgroup.normalizer (O : Set G) := mem_normalizer_primeCore hbK
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 K
  have hOK : O ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let S : Subgroup G :=
    { carrier := {k | k ∈ Subgroup.normalizer (O : Set G) ∧
        ∀ g ∈ Subgroup.zpowers b, g * k * g⁻¹ * k⁻¹ ∈ O}
      one_mem' := ⟨one_mem _, fun g _ => by simp⟩
      mul_mem' := by
        rintro k k' ⟨hk, hkc⟩ ⟨hk', hkc'⟩
        refine ⟨mul_mem hk hk', fun g hg => ?_⟩
        have h1 : g * (k * k') * g⁻¹ * (k * k')⁻¹ =
            (g * k * g⁻¹ * k⁻¹) * (k * (g * k' * g⁻¹ * k'⁻¹) * k⁻¹) := by group
        rw [h1]
        refine O.mul_mem (hkc g hg) ?_
        have := (Subgroup.mem_normalizer_iff.1 hk _).1 (hkc' g hg)
        simpa using this
      inv_mem' := by
        rintro k ⟨hk, hkc⟩
        refine ⟨inv_mem hk, fun g hg => ?_⟩
        have h1 : g * k⁻¹ * g⁻¹ * (k⁻¹)⁻¹ = k⁻¹ * (g * k * g⁻¹ * k⁻¹)⁻¹ * k := by group
        rw [h1]
        have h2 : (g * k * g⁻¹ * k⁻¹)⁻¹ ∈ O := O.inv_mem (hkc g hg)
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hk) _).1 h2
        simpa using this }
  have hJS : J ≤ S := fun j hj => ⟨hKO (hJK hj), fun g hg => by
    have hjg : g * j = j * g := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (Commute.zpow_left (show Commute b j from (Subgroup.mem_centralizer_iff.1 (hbJ hj) b rfl))
        k).eq
    have : g * j * g⁻¹ * j⁻¹ = 1 := by rw [hjg]; group
    rw [this]; exact O.one_mem⟩
  have hOS : O ≤ S := fun o ho => ⟨hKO (hOK ho), fun g hg => by
    have hgN : g ∈ Subgroup.normalizer (O : Set G) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact zpow_mem hbO k
    have := (Subgroup.mem_normalizer_iff.1 hgN o).1 ho
    exact O.mul_mem this (O.inv_mem ho)⟩
  refine Subgroup.commutator_le.2 fun g hg k hk => ?_
  have := (sup_le hJS hOS : J ⊔ O ≤ S) hk
  simpa [commutatorElement_def] using this.2 g hg

theorem kOf_eq_pumpUp {B L A : Subgroup G} {b x : G} (hw : IsExtremalWitness B b L A) (hxA : x ∈ A)
    (hxb : x ∉ Subgroup.zpowers b) : KOf L A x = pumpUp L x := by
  obtain ⟨hbB, hb1, hLcomp, -, -, ⟨hFcard, hA, hbA, hfld, hFJ, -⟩, hx3⟩ := hw
  have hAeq := A_eq_sup hA.2.1 (by simpa using hA.2.2) hbA hxA hb1 hxb
  have hinf := inf_centralizer_eq_of_A hAeq hxA hLcomp.1
  unfold KOf pumpUp
  rw [hinf]

@[expose] def Cover514 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b : G, ∀ L A : Subgroup G, IsExtremalWitness B b L A →
      ∀ a ∈ A, a ≠ 1 → a ∉ Subgroup.zpowers b →
        KOf L A a ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ⊔
          GLAPPrimeCoreOf 3 (KOf L A a)

theorem lemma514_of_cover (h : Cover514) : Lemma514 := by
  intro G _ _ m hS hC B hB b L A hw a haA ha1
  have hBe : IsElemAbelian 3 B := hB.1.1
  have hw' := hw
  obtain ⟨hbB, hb1, hLcomp, -, -, ⟨hFcard, hA, hbA, hfld, hFJ, -⟩, hx3⟩ := hw
  change ⁅Subgroup.zpowers b, KOf L A a⁆ ≤ GLAPPrimeCoreOf 3 (KOf L A a) ∧
    (a ∉ Subgroup.zpowers b → KOf L A a ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ⊔
      GLAPPrimeCoreOf 3 (KOf L A a))
  have hbL : L ≤ Subgroup.centralizer ({b} : Set G) := hLcomp.1
  have hJL : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≤ L :=
    (glaPLayer_le' 3 _).trans inf_le_left
  by_cases hab : a ∈ Subgroup.zpowers b
  · have hCa := centralizer_eq_of_mem_zpowers hBe hbB hb1 hab ha1
    have hL' : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) L := by
      rw [hCa]; exact hLcomp
    have hKL : KOf L A a ≤ L := layer_closure_le hL' hJL
    refine ⟨?_, fun h' => absurd hab h'⟩
    have hz : ⁅Subgroup.zpowers b, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      refine (Subgroup.zpowers_le).2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (hbL hy) b rfl).symm
    exact (Subgroup.commutator_mono le_rfl hKL).trans (hz ▸ bot_le)
  · have hcov := h G m hS hC B hB b L A hw' a haA ha1 hab
    refine ⟨?_, fun _ => hcov⟩
    have hpu := kOf_eq_pumpUp hw' haA hab
    have hbK : b ∈ Subgroup.normalizer (KOf L A a : Set G) := by
      obtain ⟨hn, -⟩ := (hx3 a (hA.1 haA) ha1 (hfld a haA)).2.1
      rw [hpu]
      exact hn
    have hJK : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≤ KOf L A a := le_kOf L A a
    have hbJ : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≤
        Subgroup.centralizer ({b} : Set G) := hJL.trans hbL
    exact (Subgroup.commutator_mono le_rfl hcov).trans (commutator_le_primeCore hJK hbK hbJ)

end Reduction

end Lemma514Ns

end CFSG.HardMathSupport.Solomon.LocalBalance
