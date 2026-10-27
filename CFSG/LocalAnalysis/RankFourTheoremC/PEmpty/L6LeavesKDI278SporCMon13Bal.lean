module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem inf_centralizer_eq_bot_of_conj {G : Type*} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 13)
    (hBz : ∀ R' Y' : Subgroup G, CFSG.Open.IsElemAbelian 13 R' → Nat.card R' = 13 ^ 2 →
      z ∈ R' → Y' ≤ centralizer ({z} : Set G) → ¬ 13 ∣ Nat.card Y' →
      R' ≤ normalizer (Y' : Set G) → Y' = ⊥)
    {R Y : Subgroup G} (hR : CFSG.Open.IsElemAbelian 13 R) (hR2 : Nat.card R = 13 ^ 2)
    (hY : ¬ 13 ∣ Nat.card Y) (hRY : R ≤ normalizer (Y : Set G))
    {a m : G} (ha : a ∈ R) {k : ℕ} (hk : k % 13 ≠ 0) (hmk : m * a * m⁻¹ = z ^ k) :
    Y ⊓ centralizer ({a} : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hcop : Nat.Coprime k 13 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).2
      fun h => hk (Nat.mod_eq_zero_of_dvd h)).symm
  obtain ⟨j, -, hj⟩ : ∃ j < 13, k * j % 13 = 1 :=
    Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  have hzj : (z ^ k) ^ j = z := by
    rw [← pow_mul]
    calc z ^ (k * j) = z ^ (k * j % orderOf z) := (pow_mod_orderOf z _).symm
      _ = z := by rw [hz, hj, pow_one]
  set θ : G →* G := (MulAut.conj m).toMonoidHom with hθdef
  have hθ : ∀ g : G, θ g = m * g * m⁻¹ := fun g => rfl
  have hθinj : Function.Injective θ := (MulAut.conj m).injective
  have hR_comm : ∀ r ∈ R, ∀ b ∈ R, r * b = b * r := fun r hr b hb =>
    congrArg Subtype.val (hR.1.is_comm.comm (⟨r, hr⟩ : R) ⟨b, hb⟩)
  set R' : Subgroup G := R.map θ with hR'def
  set Y' : Subgroup G := (Y ⊓ centralizer ({a} : Set G)).map θ with hY'def
  have hR'ab : CFSG.Open.IsElemAbelian 13 R' := hR.map θ
  have hR'2 : Nat.card R' = 13 ^ 2 := by
    rw [hR'def, card_map_of_injective hθinj, hR2]
  have hzR' : z ∈ R' := by
    refine ⟨a ^ j, pow_mem ha j, ?_⟩
    show m * a ^ j * m⁻¹ = z
    calc m * a ^ j * m⁻¹ = (m * a * m⁻¹) ^ j := conj_pow.symm
      _ = (z ^ k) ^ j := by rw [hmk]
      _ = z := hzj
  have hY'C : Y' ≤ centralizer ({z} : Set G) := by
    rintro g ⟨y, hy, rfl⟩
    have hyC : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    rw [Subgroup.mem_centralizer_singleton_iff, hθ]
    have hcomm : (m * y * m⁻¹) * z ^ k = z ^ k * (m * y * m⁻¹) := by
      rw [← hmk]
      calc m * y * m⁻¹ * (m * a * m⁻¹) = m * (y * a) * m⁻¹ := by group
        _ = m * (a * y) * m⁻¹ := by rw [hyC]
        _ = m * a * m⁻¹ * (m * y * m⁻¹) := by group
    have hcomm' : (m * y * m⁻¹) * (z ^ k) ^ j = (z ^ k) ^ j * (m * y * m⁻¹) :=
      Commute.pow_right (show Commute (m * y * m⁻¹) (z ^ k) from hcomm) j
    rw [hzj] at hcomm'
    exact hcomm'
  have hY'p : ¬ 13 ∣ Nat.card Y' := by
    rw [hY'def, card_map_of_injective hθinj]
    exact fun h => hY (dvd_trans h (Subgroup.card_dvd_of_le inf_le_left))
  have hstep : ∀ r ∈ R, ∀ y ∈ Y ⊓ centralizer ({a} : Set G),
      r * y * r⁻¹ ∈ Y ⊓ centralizer ({a} : Set G) := by
    intro r hr y hy
    refine ⟨(mem_normalizer_iff.1 (hRY hr) y).1 hy.1, ?_⟩
    have hra' : Commute a r := show a * r = r * a from (hR_comm r hr a ha).symm
    have hay : Commute a y := show a * y = y * a from
      (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm
    have hcw : Commute a (r * y * r⁻¹) :=
      ((hra'.mul_right hay).mul_right hra'.inv_right)
    exact Subgroup.mem_centralizer_singleton_iff.2 hcw.symm.eq
  have hfwd : ∀ g ∈ R', ∀ h ∈ Y', g * h * g⁻¹ ∈ Y' := by
    rintro g ⟨r, hr, rfl⟩ h ⟨y, hy, rfl⟩
    have e : θ r * θ y * (θ r)⁻¹ = θ (r * y * r⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem θ (hstep r hr y hy)
  have hR'N : R' ≤ normalizer (Y' : Set G) := by
    intro g hg
    refine mem_normalizer_iff.2 fun h => ⟨hfwd g hg h, fun hh => ?_⟩
    have := hfwd g⁻¹ (inv_mem hg) _ hh
    have e2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e2] at this
  have hbot : Y' = ⊥ := hBz R' Y' hR'ab hR'2 hzR' hY'C hY'p hR'N
  rw [eq_bot_iff]
  intro g hg
  have hmem : θ g ∈ Y' := Subgroup.mem_map_of_mem θ hg
  rw [hbot, Subgroup.mem_bot, hθ] at hmem
  rw [Subgroup.mem_bot]
  calc g = m⁻¹ * (m * g * m⁻¹) * m := by group
    _ = m⁻¹ * 1 * m := by rw [hmem]
    _ = 1 := by group

theorem balance_of_census_local {G : Type*} [Group G] [Finite G] {c x : G}
    (hc : orderOf c = 13) (hx : orderOf x = 13)
    (hcen : ∀ a : G, orderOf a = 13 → ∃ m : G, ∃ k : ℕ, k % 13 ≠ 0 ∧
      (m * a * m⁻¹ = c ^ k ∨ m * a * m⁻¹ = x ^ k))
    (hB : ∀ R Y : Subgroup G, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 → c ∈ R →
      Y ≤ centralizer ({c} : Set G) → ¬ 13 ∣ Nat.card Y → R ≤ normalizer (Y : Set G) → Y = ⊥)
    (hD : ∀ R Y : Subgroup G, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 → x ∈ R →
      Y ≤ centralizer ({x} : Set G) → ¬ 13 ∣ Nat.card Y → R ≤ normalizer (Y : Set G) → Y = ⊥) :
    ∀ R Y : Subgroup G, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 →
      ¬ 13 ∣ Nat.card Y → R ≤ normalizer (Y : Set G) → Y = ⊥ := by
  intro R Y hR hR2 hY hRY
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : CFSG.IsElementaryAbelian 13 R := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hR
  have hcov := le_iSup_centralizer_of_coprime
    (p := 13) (A := R) (U := Y) hR2.symm.le hY hRY
  refine eq_bot_iff.2 (hcov.trans (iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_))
  refine le_of_eq ?_
  have ha13 : orderOf a = 13 := orderOf_eq_prime (hR.2 a ha) hne
  obtain ⟨m, k, hk, hmk⟩ := hcen a ha13
  rcases hmk with hmk | hmk
  · exact inf_centralizer_eq_bot_of_conj hc hB hR hR2 hY hRY ha hk hmk
  · exact inf_centralizer_eq_bot_of_conj hx hD hR hR2 hY hRY ha hk hmk

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
