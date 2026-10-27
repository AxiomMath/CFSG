module

public import CFSG.GH74.Uniqueness.Section164Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec164

theorem exists_mem_gamma_ne
    (S : ZDSetup X Z M) (c : Conf16 Z M) :
    ∃ y ∈ Z ∩ ((c.B ⊓ M : Subgroup X) : Set X), y ≠ c.z := by
  obtain ⟨-, -, n, hn, hcard⟩ := S.corollary713Extra c.B (S.cor714_centralizer_ne_top c.hu2)
    c.not_B_le c.nonempty_BM (S.not_solvable_cenHull c)
  have h1 : 1 < (Z ∩ ((c.B ⊓ M : Subgroup X) : Set X)).ncard := by
    rw [hcard]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  exact Set.exists_ne_of_one_lt_ncard h1 c.z

theorem gamma_eq_of_mem_centralizer_Bzero (c : Conf16 Z M) {w : X}
    (hwC : w ∈ centralizer (c.Bzero : Set X)) (hwD : w ∈ c.D) (hw2 : orderOf w = 2) :
    Z ∩ ((centralizer ({w} : Set X) ⊓ M : Subgroup X) : Set X) =
      Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro g hg
    refine ⟨hg.1, mem_inf.mpr ⟨?_, (mem_inf.mp hg.2).2⟩⟩
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hwC g (gamma_subset_Bzero c hg)
  · exact c.hmax w hwD hw2
  · exact Set.toFinite _

theorem fZero_eq_Bzero (c : Conf16 Z M) {w : X}
    (hΓ : Z ∩ ((centralizer ({w} : Set X) ⊓ M : Subgroup X) : Set X) =
      Z ∩ ((c.B ⊓ M : Subgroup X) : Set X)) :
    fZero Z M (cenHull Z w) c.t = c.Bzero := by
  have h : Z ∩ ((M ⊓ cenHull Z w : Subgroup X) : Set X) =
      Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := by
    rw [← hΓ]
    ext g
    simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_inf]
    constructor
    · rintro ⟨hgZ, hgM, hgF⟩
      exact ⟨hgZ, Cor713.zHull_le _ hgF, hgM⟩
    · rintro ⟨hgZ, hgC, hgM⟩
      exact ⟨hgZ, hgM, subset_closure ⟨hgZ, hgC⟩⟩
  have h' : zHull Z (M ⊓ cenHull Z w) = zHull Z (c.B ⊓ M) := congrArg Subgroup.closure h
  change closure ((zHull Z (M ⊓ cenHull Z w) : Set X) ∪ {c.t}) =
    closure ((zHull Z (c.B ⊓ M) : Set X) ∪ {c.t})
  rw [h']

omit [Finite X] in
theorem mem_normalizer_centralizer {t w : X} (htw : t * w = w * t) :
    t ∈ normalizer ((centralizer ({w} : Set X) : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro g
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro hg
    calc t * g * t⁻¹ * w = t * g * (t⁻¹ * w * t) * t⁻¹ := by group
      _ = t * g * w * t⁻¹ := by
          rw [show t⁻¹ * w * t = w by
            calc t⁻¹ * w * t = t⁻¹ * (w * t) := by group
              _ = t⁻¹ * (t * w) := by rw [htw]
              _ = w := by group]
      _ = t * (w * g) * t⁻¹ := by rw [mul_assoc t g w, hg]
      _ = (t * w) * g * t⁻¹ := by group
      _ = (w * t) * g * t⁻¹ := by rw [htw]
      _ = w * (t * g * t⁻¹) := by group
  · intro hg
    have hw : t⁻¹ * w * t = w := by
      calc t⁻¹ * w * t = t⁻¹ * (w * t) := by group
        _ = t⁻¹ * (t * w) := by rw [htw]
        _ = w := by group
    calc g * w = t⁻¹ * (t * g * t⁻¹ * w) * t := by rw [show t⁻¹ * (t * g * t⁻¹ * w) * t =
            g * (t⁻¹ * w * t) by group, hw]
      _ = t⁻¹ * (w * (t * g * t⁻¹)) * t := by rw [hg]
      _ = (t⁻¹ * w * t) * g := by group
      _ = w * g := by rw [hw]

omit [Finite X] in
theorem mem_normalizer_inf {A B : Subgroup X} {t : X} (hA : t ∈ normalizer (A : Set X))
    (hB : t ∈ normalizer (B : Set X)) : t ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro g
  simp only [mem_inf]
  rw [mem_normalizer_iff.mp hA g, mem_normalizer_iff.mp hB g]

end Sec164

theorem ZDSetup.lemma164a
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (c : Conf16 Z M) :
    c.u ∈ centralizer (c.Bzero : Set X) ∧
      ∀ y ∈ c.B ⊓ centralizer (c.Bzero : Set X), orderOf y = 2 → y = c.u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Sec164.u_mem_centralizer_Bzero c, fun y hy hy2 => ?_⟩
  by_contra hyu
  have hyB := (mem_inf.mp hy).1
  have hyC := (mem_inf.mp hy).2
  have ha : c.u * c.u = 1 := c.u_mul_self
  have hb : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
  have hab : c.u * y = y * c.u := (mem_centralizer_singleton_iff.mp hyB).symm
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
  have hW4 : Nat.card (fourSub c.u y ha hb hab) = 4 :=
    card_fourSub c.u_ne_one hy1 (fun h => hyu h.symm)
  have hW2 : ∀ w ∈ fourSub c.u y ha hb hab, w * w = 1 := mul_self_of_mem_fourSub
  have hWC : fourSub c.u y ha hb hab ≤ centralizer (c.Bzero : Set X) :=
    fourSub_le (Sec164.u_mem_centralizer_Bzero c) hyC
  have hWD : fourSub c.u y ha hb hab ≤ c.D := hWC.trans (Sec164.centralizer_Bzero_le_D S c)
  have hWt : fourSub c.u y ha hb hab ≤ centralizer ({c.t} : Set X) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (Sec164.commute_t_of_mem_centralizer_Bzero c (hWC hw))
  have hWK : fourSub c.u y ha hb hab ≤ normalizer (kGrp M c.t : Set X) := fun w hw =>
    Sec164.mem_normalizer_kGrp (hWD hw) (Sec164.commute_t_of_mem_centralizer_Bzero c (hWC hw))
  have hKgen := h161 c.toCtx16 _ hW4 hW2 hWK hWt
  obtain ⟨hKodd, htK, -⟩ := commutator_zpowers_kGrp M S.invariant c.ht
  have hstep : ∀ w ∈ ((fourSub c.u y ha hb hab : Subgroup X) : Set X) \ {1},
      ⁅zpowers c.t, centralizer ({w} : Set X) ⊓ kGrp M c.t⁆ ≤ c.Bzero := by
    rintro w ⟨hwW, hw1⟩
    have hw1' : w ≠ 1 := hw1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 w hwW) hw1'
    have hwC := hWC hwW
    have hΓ := Sec164.gamma_eq_of_mem_centralizer_Bzero c hwC (hWD hwW) hw2
    obtain ⟨y', hy', hy'z⟩ := Sec164.exists_mem_gamma_ne S c
    have hy'w : y' ∈ Z ∩ ((centralizer ({w} : Set X) ⊓ M : Subgroup X) : Set X) := hΓ ▸ hy'
    have hne : ∃ y ∈ Z, y ∈ cenHull Z w ∧ y ∈ M ∧ y ≠ c.z :=
      ⟨y', hy'.1, subset_closure ⟨hy'.1, (mem_inf.mp hy'w.2).1⟩, (mem_inf.mp hy'.2).2, hy'z⟩
    have hzw : c.z * w = w * c.z := (Sec164.commute_z_of_mem_centralizer_Bzero c hwC).symm
    have htw : c.t * w = w * c.t := (Sec164.commute_t_of_mem_centralizer_Bzero c hwC).symm
    have hA : centralizer ({w} : Set X) ⊓ kGrp M c.t ≤ M ⊓ conjugate M c.t :=
      inf_le_right.trans (Sec164.kGrp_le_D S.invariant c.ht)
    have hAodd : Odd (Nat.card ↥(centralizer ({w} : Set X) ⊓ kGrp M c.t)) :=
      Odd.of_dvd_nat hKodd (card_dvd_of_le inf_le_right)
    have htA : c.t ∈ normalizer
        ((centralizer ({w} : Set X) ⊓ kGrp M c.t : Subgroup X) : Set X) :=
      Sec164.mem_normalizer_inf (Sec164.mem_normalizer_centralizer htw) htK
    have h := Sec164.commutator_le_fZero S h162 c.toCtx16 hw2 hzw htw hne hA inf_le_left hAodd htA
    rwa [Sec164.fZero_eq_Bzero c hΓ] at h
  have hKB : kGrp M c.t ≤ c.Bzero := by
    rw [hKgen]
    exact iSup₂_le hstep
  have hL : lSubgroup M c.z c.t ≤ c.Bzero :=
    sup_le (sup_le (zpowers_le.mpr (Sec164.z_mem_Bzero c)) (zpowers_le.mpr (Sec164.t_mem_Bzero c)))
      hKB
  rw [h121 c.t c.z c.ht c.htM c.hz c.hzM c.hD] at hL
  apply S.cor714_centralizer_ne_top c.hu2
  rw [eq_top_iff]
  intro g _
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (Sec164.u_mem_centralizer_Bzero c) g (hL (mem_top g)))

end CFSG.GH74.Uniqueness
