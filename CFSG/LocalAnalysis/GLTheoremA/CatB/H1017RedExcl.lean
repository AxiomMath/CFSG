module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Row
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Lift
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem isElemAbelian_bot_three : IsElemAbelian 3 (⊥ : Subgroup G) :=
  ⟨⟨⟨fun a b => Subtype.ext (by simp [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])⟩⟩,
    fun y hy => by rw [Subgroup.mem_bot.1 hy, one_pow]⟩

theorem le_glaTwoLocalRank_of_pQuot {L A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hAL : A ⊓ L = ⊥) (hAc : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a) {r : ℕ}
    {E₀ V : Subgroup (PQuot 3 L)} (hE₀ : IsElemAbelian 3 E₀) (hcard : Nat.card E₀ = 3 ^ r)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hEV : E₀ ≤ Subgroup.normalizer (V : Set (PQuot 3 L))) :
    3 ^ r * Nat.card A ≤ 3 ^ GLATwoLocalRank 3 G := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun l hl => (hAc a ha l hl).symm)
  have hAc' : ∀ a ∈ A, ∀ k ∈ L, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 L := by
    intro a ha k hk
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hAc a ha k hk).symm]
    exact Subgroup.one_mem _
  obtain ⟨P, W, hP, hP2, hWP, hW, hWc⟩ :=
    H1420.twoLocal_of_witness hA hAN hAL hAc' V E₀ hV hV2 hE₀ hEV hcard
  rw [← hWc]
  exact card_le_pow_glaTwoLocalRank Nat.prime_three hW hP hP2 hWP

private theorem pow_succ_le_of_center {L : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hLx : L ≤ cx x) (hZ : Nat.card (Subgroup.center (PQuot 3 L)) = 1) {r : ℕ}
    {E₀ V : Subgroup (PQuot 3 L)} (hE₀ : IsElemAbelian 3 E₀) (hcard : Nat.card E₀ = 3 ^ r)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hEV : E₀ ≤ Subgroup.normalizer (V : Set (PQuot 3 L))) :
    3 ^ (r + 1) ≤ 3 ^ GLATwoLocalRank 3 G := by
  have hxc : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hLx hl))
  have hAc : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
    (Subgroup.zpowers_le).2 hxc
  have hAL : Subgroup.zpowers x ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyL⟩
    have hcore := S8.L84.mem_core_of_centMod hZ hyL (centMod_of_mem_centralizer (hAc hyA))
    exact (Subgroup.mem_bot).2
      (S8.L84.eq_one_of_mem_core Nat.prime_three hcore ((isElemAbelian_zpowers hx3).2 y hyA))
  have h := le_glaTwoLocalRank_of_pQuot (isElemAbelian_zpowers hx3) hAL
    (fun a ha l hl => (Subgroup.mem_centralizer_iff.1 (hAc ha) l hl).symm) hE₀ hcard hV hV2 hEV
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rwa [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, ← pow_succ] at h

theorem i1017_not_fi22 (hA : I1017FiTwoTwoAttained) (hC : I1017CoverFiTwoTwo) {L : Subgroup G}
    {x : G} (hm : GLATwoLocalRank 3 G = 4) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hL : GLAPComponent 3 (cx x) L) (hs : catalogIs (PSimple 3 L) (sporIs .Fi22))
    (hZ : Nat.card (Subgroup.center (PQuot 3 L)) = 1 ∨
      Nat.card (Subgroup.center (PQuot 3 L)) = 3) : False := by
  rcases hZ with hZ | hZ
  · obtain ⟨E₀, V, hE₀, hcard, hV, hV2, hEV⟩ :=
      hA (PQuot 3 L) (S8.L84.catalogIs_pQuot_of_center hZ hs)
    have h := pow_succ_le_of_center hx3 hx1 hL.1 hZ hE₀ hcard hV hV2 hEV
    rw [hm] at h
    exact absurd (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3) |>.1 h) (by norm_num)
  · obtain ⟨E₀, V, hE₀, hcard, hV, hV2, hEV⟩ := hC (PQuot 3 L) hs hZ
    have h := le_glaTwoLocalRank_of_pQuot isElemAbelian_bot_three (bot_inf_eq _)
      (fun a ha l _ => by rw [Subgroup.mem_bot.1 ha, one_mul, mul_one]) hE₀ hcard hV hV2 hEV
    rw [hm, Subgroup.card_bot, mul_one] at h
    exact absurd (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3) |>.1 h) (by norm_num)

theorem i1017_not_fi23_baby (hF : I1017FiTwoThreeAttained) (hBa : I1017BabyAttained)
    {L : Subgroup G} {x : G} (hm : GLATwoLocalRank 3 G ≤ 5) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hL : GLAPComponent 3 (cx x) L)
    (hs : catalogIs (PSimple 3 L) (sporIs .Fi23) ∨ catalogIs (PSimple 3 L) (sporIs .B))
    (hZ : Nat.card (Subgroup.center (PQuot 3 L)) = 1) : False := by
  obtain ⟨E₀, V, hE₀, hcard, hV, hV2, hEV⟩ : ∃ E₀ V : Subgroup (PQuot 3 L), IsElemAbelian 3 E₀ ∧
      Nat.card E₀ = 3 ^ 5 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
        E₀ ≤ Subgroup.normalizer (V : Set (PQuot 3 L)) := by
    rcases hs with hs | hs
    · exact hF (PQuot 3 L) (S8.L84.catalogIs_pQuot_of_center hZ hs)
    · exact hBa (PQuot 3 L) (S8.L84.catalogIs_pQuot_of_center hZ hs)
  have h := pow_succ_le_of_center hx3 hx1 hL.1 hZ hE₀ hcard hV hV2 hEV
  have h' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h
  omega

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
