module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBA134Basic
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListMat
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBA134Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.SectionRank.QTK.CentreFact.LayerPair

open Subgroup CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank Matrix

theorem realLocalElement_of_involution {S : Type} [Group S] {t x d : S} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hxt : Commute x t) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hd : d * x * d⁻¹ = x⁻¹) : RealLocalElement S 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨zpowers t, fun h => ht1 (Subgroup.mem_bot.mp (h ▸ mem_zpowers t)),
    isPGroup_zpowers_of_sq ht2, x, mem_normalizer_zpowers hxt, orderOf_eq_prime hx3 hx1, d, hd⟩

theorem realLocalElement_of_six {S : Type} [Group S] {g d : S} (h6 : g ^ 6 = 1) (h2 : g ^ 2 ≠ 1)
    (h3 : g ^ 3 ≠ 1) (hd : d * g * d⁻¹ = g⁻¹) : RealLocalElement S 3 := by
  refine realLocalElement_of_involution (t := g ^ 3) (x := g ^ 2) (d := d) ?_ h3 ?_ ?_ h2 ?_
  · rw [← pow_mul]; exact h6
  · exact (Commute.refl g).pow_pow 2 3
  · rw [← pow_mul]; exact h6
  · rw [← conj_pow, hd, inv_pow]

theorem realLocalElement_of_klein {S : Type} [Group S] {x X Y d : S} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1) (hXY : Commute X Y) (hX1 : X ≠ 1)
    (hxX : x * X * x⁻¹ = X * Y) (hxY : x * Y * x⁻¹ = X) (hd : d * x * d⁻¹ = x⁻¹) :
    RealLocalElement S 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXs : X ∈ zpowers X ⊔ zpowers Y := mem_sup_left (mem_zpowers X)
  have hYs : Y ∈ zpowers X ⊔ zpowers Y := mem_sup_right (mem_zpowers Y)
  have hXYs : X * Y ∈ zpowers X ⊔ zpowers Y := mul_mem hXs hYs
  have hxX' : x⁻¹ * X * x = Y := by
    rw [← hxY]; group
  have hXYX : X * Y * X = Y :=
    calc X * Y * X = Y * X * X := by rw [hXY.eq]
      _ = Y * (X * X) := mul_assoc _ _ _
      _ = Y := by rw [← pow_two, hX2, mul_one]
  have hxY' : x⁻¹ * Y * x = X * Y := by
    have h1 : x * (X * Y) * x⁻¹ = Y := by
      calc x * (X * Y) * x⁻¹ = (x * X * x⁻¹) * (x * Y * x⁻¹) := by group
        _ = X * Y * X := by rw [hxX, hxY]
        _ = Y := hXYX
    calc x⁻¹ * Y * x = x⁻¹ * (x * (X * Y) * x⁻¹) * x := by rw [h1]
      _ = X * Y := by group
  refine ⟨zpowers X ⊔ zpowers Y, ?_, ?_, x, ?_, orderOf_eq_prime hx3 hx1, d, hd⟩
  · intro h
    rw [eq_bot_iff] at h
    exact hX1 (Subgroup.mem_bot.mp (h hXs))
  · exact IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_sq hX2) (isPGroup_zpowers_of_sq hY2)
      (zpowers_le.2 (mem_normalizer_zpowers hXY.symm))
  · refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
    · rw [hxX]; exact hXYs
    · rw [hxY]; exact hXs
    · rw [hxX']; exact hYs
    · rw [hxY']; exact hXYs

theorem realLocalElement_subgroup_of_klein {G : Type} [Group G] {H : Subgroup G} {x X Y d : G}
    (hx : x ∈ H) (hX : X ∈ H) (hY : Y ∈ H) (hd : d ∈ H) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1) (hXY : X * Y = Y * X) (hX1 : X ≠ 1)
    (hxX : x * X * x⁻¹ = X * Y) (hxY : x * Y * x⁻¹ = X) (hdx : d * x * d⁻¹ = x⁻¹) :
    RealLocalElement ↥H 3 := by
  refine realLocalElement_of_klein (x := (⟨x, hx⟩ : H)) (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩)
    (d := ⟨d, hd⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by simpa using hx3)
  · intro h; exact hx1 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hX2)
  · exact Subtype.ext (by simpa using hY2)
  · exact Subtype.ext hXY
  · intro h; exact hX1 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hxX)
  · exact Subtype.ext (by simpa using hxY)
  · exact Subtype.ext (by simpa using hdx)

theorem realLocalElement_subgroup_of_six {G : Type} [Group G] {H : Subgroup G} {g a : G}
    (hg : g ∈ H) (ha : a ∈ H) (h6 : g ^ 6 = 1) (h2 : g ^ 2 ≠ 1) (h3 : g ^ 3 ≠ 1)
    (hd : a * g * a⁻¹ = g⁻¹) : RealLocalElement ↥H 3 := by
  refine realLocalElement_of_six (g := (⟨g, hg⟩ : H)) (d := ⟨a, ha⟩) ?_ ?_ ?_ ?_
  · exact Subtype.ext (by simpa using h6)
  · intro h; exact h2 (by simpa using congrArg Subtype.val h)
  · intro h; exact h3 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hd)

section Alt

open Equiv

@[expose] def altCycle (n : ℕ) [NeZero n] : Perm (Fin n) := swap 0 1 * swap 1 2

@[expose] def altKleinX (n : ℕ) [NeZero n] : Perm (Fin n) := swap 0 1 * swap 2 3

@[expose] def altKleinY (n : ℕ) [NeZero n] : Perm (Fin n) := swap 0 2 * swap 1 3

@[expose] def altInvert (n : ℕ) [NeZero n] : Perm (Fin n) := swap 1 2 * swap 4 5

theorem alt6_rels : Perm.sign (altCycle 6) = 1 ∧ Perm.sign (altKleinX 6) = 1 ∧
    Perm.sign (altKleinY 6) = 1 ∧ Perm.sign (altInvert 6) = 1 ∧ altCycle 6 ^ 3 = 1 ∧
    altCycle 6 ≠ 1 ∧ altKleinX 6 ^ 2 = 1 ∧ altKleinY 6 ^ 2 = 1 ∧
    altKleinX 6 * altKleinY 6 = altKleinY 6 * altKleinX 6 ∧ altKleinX 6 ≠ 1 ∧
    altCycle 6 * altKleinX 6 * (altCycle 6)⁻¹ = altKleinX 6 * altKleinY 6 ∧
    altCycle 6 * altKleinY 6 * (altCycle 6)⁻¹ = altKleinX 6 ∧
    altInvert 6 * altCycle 6 * (altInvert 6)⁻¹ = (altCycle 6)⁻¹ := by
  decide +kernel

theorem alt7_rels : Perm.sign (altCycle 7) = 1 ∧ Perm.sign (altKleinX 7) = 1 ∧
    Perm.sign (altKleinY 7) = 1 ∧ Perm.sign (altInvert 7) = 1 ∧ altCycle 7 ^ 3 = 1 ∧
    altCycle 7 ≠ 1 ∧ altKleinX 7 ^ 2 = 1 ∧ altKleinY 7 ^ 2 = 1 ∧
    altKleinX 7 * altKleinY 7 = altKleinY 7 * altKleinX 7 ∧ altKleinX 7 ≠ 1 ∧
    altCycle 7 * altKleinX 7 * (altCycle 7)⁻¹ = altKleinX 7 * altKleinY 7 ∧
    altCycle 7 * altKleinY 7 * (altCycle 7)⁻¹ = altKleinX 7 ∧
    altInvert 7 * altCycle 7 * (altInvert 7)⁻¹ = (altCycle 7)⁻¹ := by
  decide +kernel

theorem realLocalElement_alternating_six : RealLocalElement (alternatingGroup (Fin 6)) 3 := by
  obtain ⟨s1, s2, s3, s4, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := alt6_rels
  exact realLocalElement_subgroup_of_klein (Equiv.Perm.mem_alternatingGroup.2 s1)
    (Equiv.Perm.mem_alternatingGroup.2 s2) (Equiv.Perm.mem_alternatingGroup.2 s3)
    (Equiv.Perm.mem_alternatingGroup.2 s4) h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem realLocalElement_alternating_seven : RealLocalElement (alternatingGroup (Fin 7)) 3 := by
  obtain ⟨s1, s2, s3, s4, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := alt7_rels
  exact realLocalElement_subgroup_of_klein (Equiv.Perm.mem_alternatingGroup.2 s1)
    (Equiv.Perm.mem_alternatingGroup.2 s2) (Equiv.Perm.mem_alternatingGroup.2 s3)
    (Equiv.Perm.mem_alternatingGroup.2 s4) h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem realLocalElement_alternating_six_seven {n : ℕ} (hn : n = 6 ∨ n = 7) :
    RealLocalElement (alternatingGroup (Fin n)) 3 := by
  rcases hn with rfl | rfl
  · exact realLocalElement_alternating_six
  · exact realLocalElement_alternating_seven

end Alt

section Mathieu

open CFSG.Blueprint

private theorem m11_rels : (abWord m11a m11b [0, 1, 1]) ^ 6 = 1 ∧
    (abWord m11a m11b [0, 1, 1]) ^ 2 ≠ 1 ∧ (abWord m11a m11b [0, 1, 1]) ^ 3 ≠ 1 ∧
    m11a * abWord m11a m11b [0, 1, 1] * m11a⁻¹ = (abWord m11a m11b [0, 1, 1])⁻¹ := by
  decide +kernel

private theorem m22_rels : (abWord m22a m22b [0, 1, 0, 1, 1, 1]) ^ 6 = 1 ∧
    (abWord m22a m22b [0, 1, 0, 1, 1, 1]) ^ 2 ≠ 1 ∧
    (abWord m22a m22b [0, 1, 0, 1, 1, 1]) ^ 3 ≠ 1 ∧
    m22a * abWord m22a m22b [0, 1, 0, 1, 1, 1] * m22a⁻¹ =
      (abWord m22a m22b [0, 1, 0, 1, 1, 1])⁻¹ := by
  decide +kernel

private theorem m23_rels : (abWord m23a m23b [0, 1, 1]) ^ 6 = 1 ∧
    (abWord m23a m23b [0, 1, 1]) ^ 2 ≠ 1 ∧ (abWord m23a m23b [0, 1, 1]) ^ 3 ≠ 1 ∧
    m23a * abWord m23a m23b [0, 1, 1] * m23a⁻¹ = (abWord m23a m23b [0, 1, 1])⁻¹ := by
  decide +kernel

theorem realLocalElement_M11 : RealLocalElement ↥NativeSporadic.M11 3 := by
  have ha : m11a ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m11b ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨h6, h2, h3, hd⟩ := m11_rels
  exact realLocalElement_subgroup_of_six (abWord_mem ha hb [0, 1, 1]) ha h6 h2 h3 hd

theorem realLocalElement_M22 : RealLocalElement ↥NativeSporadic.M22 3 := by
  have ha : m22a ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m22b ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨h6, h2, h3, hd⟩ := m22_rels
  exact realLocalElement_subgroup_of_six (abWord_mem ha hb [0, 1, 0, 1, 1, 1]) ha h6 h2 h3 hd

theorem realLocalElement_M23 : RealLocalElement ↥NativeSporadic.M23 3 := by
  have ha : m23a ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m23b ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨h6, h2, h3, hd⟩ := m23_rels
  exact realLocalElement_subgroup_of_six (abWord_mem ha hb [0, 1, 1]) ha h6 h2 h3 hd

theorem realLocalElement_mathieu {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M22 ∨ s = .M23) : RealLocalElement (NativeSporadic.Carrier s) 3 := by
  rcases hs with rfl | rfl | rfl
  · exact realLocalElement_M11
  · exact realLocalElement_M22
  · exact realLocalElement_M23

end Mathieu

section Matrices

variable {K : Type} [Field K]

theorem realLocalElement_statedProj_of_klein {H : Subgroup (GL (Fin 3) K)}
    {x X Y d : GL (Fin 3) K} (hx : x ∈ H) (hX : X ∈ H) (hY : Y ∈ H) (hd : d ∈ H)
    (hx3 : x ^ 3 = 1) (hxs : x ∉ StatedScalars (Fin 3) K) (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1)
    (hXY : X * Y = Y * X) (hXs : X ∉ StatedScalars (Fin 3) K) (hxX : x * X * x⁻¹ = X * Y)
    (hxY : x * Y * x⁻¹ = X) (hdx : d * x * d⁻¹ = x⁻¹) : RealLocalElement (StatedProj H) 3 := by
  let mk : H →* StatedProj H := QuotientGroup.mk' _
  let x' : H := ⟨x, hx⟩
  let X' : H := ⟨X, hX⟩
  let Y' : H := ⟨Y, hY⟩
  let d' : H := ⟨d, hd⟩
  have hne : ∀ g : H, (g : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K → mk g ≠ 1 := fun g hg h =>
    hg (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp h))
  refine realLocalElement_of_klein (x := mk x') (X := mk X') (Y := mk Y') (d := mk d') ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow]; exact (congrArg mk (Subtype.ext (by simpa using hx3))).trans (map_one mk)
  · exact hne x' hxs
  · rw [← map_pow]; exact (congrArg mk (Subtype.ext (by simpa using hX2))).trans (map_one mk)
  · rw [← map_pow]; exact (congrArg mk (Subtype.ext (by simpa using hY2))).trans (map_one mk)
  · show mk X' * mk Y' = mk Y' * mk X'
    rw [← map_mul, ← map_mul]; exact congrArg mk (Subtype.ext hXY)
  · exact hne X' hXs
  · rw [← map_inv, ← map_mul, ← map_mul]; exact congrArg mk (Subtype.ext (by simpa using hxX))
  · rw [← map_inv, ← map_mul, ← map_mul]; exact congrArg mk (Subtype.ext (by simpa using hxY))
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    exact congrArg mk (Subtype.ext (by simpa using hdx))

theorem s01GL_conj_cycGL : (s01GL : GL (Fin 3) K) * cycGL * s01GL⁻¹ = cycGL⁻¹ := by
  have h1 : (cycGL : GL (Fin 3) K) = s01GL * s12GL := s01GL_mul_s12GL.symm
  rw [h1, _root_.mul_inv_rev, s01GL_inv, s12GL_inv]
  calc (s01GL : GL (Fin 3) K) * (s01GL * s12GL) * s01GL
      = (s01GL * s01GL) * s12GL * s01GL := by group
    _ = s12GL * s01GL := by rw [← sq, s01GL_sq, one_mul]

private theorem scalar_eq_diagHom_const {n : ℕ} (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c = diagHom n (fun _ => c) :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply])

theorem realLocalElement_statedProj_of_monomialData (h2 : (2 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ} (hH : MonomialData H M) (hM : (-1 : Kˣ) ∈ M) :
    RealLocalElement (StatedProj H) 3 := by
  have hdiag : ∀ d : Fin 3 → Kˣ, (∀ i, d i = 1 ∨ d i = -1) → d 0 * d 1 * d 2 = 1 →
      diagHom 3 d ∈ H := fun d hd hp => hH.diag_mem d (fun i => by
        rcases hd i with h | h <;> rw [h]
        · exact M.one_mem
        · exact hM) hp
  have hne : ∀ d : Fin 3 → Kˣ, (∃ i j, d i ≠ d j) → diagHom 3 d ∉ StatedScalars (Fin 3) K := by
    rintro d ⟨i, j, hij⟩ ⟨c, hc⟩
    rw [scalar_eq_diagHom_const] at hc
    have h := diagHom_injective 3 hc
    exact hij ((congrFun h i).symm.trans (congrFun h j))
  have hm1 : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have := congrArg (fun u : Kˣ => (u : K)) h
    simp at this
    linear_combination -this)
  refine realLocalElement_statedProj_of_klein (x := cycGL) (X := diagHom 3 ![1, -1, -1])
    (Y := diagHom 3 ![-1, -1, 1]) (d := s01GL) hH.cyc_mem
    (hdiag _ (by intro i; fin_cases i <;> simp) (by simp))
    (hdiag _ (by intro i; fin_cases i <;> simp) (by simp)) hH.s01_mem cycGL_pow_three ?_ ?_ ?_ ?_
    ?_ ?_ ?_ s01GL_conj_cycGL
  · rintro ⟨c, hc⟩
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hc) 0) 2
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_cycGL, cycMat,
      Matrix.diagonal_apply] at this
  · rw [← map_pow]
    have : (![1, -1, -1] : Fin 3 → Kˣ) ^ 2 = 1 := by
      funext i; fin_cases i <;> simp
    rw [this, map_one]
  · rw [← map_pow]
    have : (![-1, -1, 1] : Fin 3 → Kˣ) ^ 2 = 1 := by
      funext i; fin_cases i <;> simp
    rw [this, map_one]
  · rw [← map_mul, ← map_mul, mul_comm]
  · exact hne _ ⟨0, 1, by simp [hm1.symm]⟩
  · rw [cycGL_conj_diagHom, ← map_mul]
    congr 1
    funext i; fin_cases i <;> simp
  · rw [cycGL_conj_diagHom]
    congr 1

private def tvMat (a b : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, a; 0, 1, b; 0, 0, 1]

private theorem tvMat_mul (a b a' b' : K) :
    tvMat a b * tvMat a' b' = tvMat (a + a') (b + b') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tvMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

private theorem tvMat_zero : tvMat (0 : K) 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tvMat]

private def tvGL (a b : K) : GL (Fin 3) K :=
  ⟨tvMat a b, tvMat (-a) (-b), by rw [tvMat_mul]; simp [tvMat_zero],
    by rw [tvMat_mul]; simp [tvMat_zero]⟩

private def rotMat : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; 1, -1, 0; 0, 0, 1]

private def rotInvMat : Matrix (Fin 3) (Fin 3) K := !![-1, 1, 0; -1, 0, 0; 0, 0, 1]

private theorem rotMat_mul_rotInvMat : rotMat * rotInvMat = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMat, rotInvMat, Matrix.mul_apply, Fin.sum_univ_three]

private theorem rotInvMat_mul_rotMat : rotInvMat * rotMat = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMat, rotInvMat, Matrix.mul_apply, Fin.sum_univ_three]

private def rotGL : GL (Fin 3) K :=
  ⟨rotMat, rotInvMat, rotMat_mul_rotInvMat, rotInvMat_mul_rotMat⟩

private def swapMat01 : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private theorem swapMat01_mul_self : swapMat01 * swapMat01 = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [swapMat01, Matrix.mul_apply, Fin.sum_univ_three]

private def swapGL01 : GL (Fin 3) K :=
  ⟨swapMat01, swapMat01, swapMat01_mul_self, swapMat01_mul_self⟩

private theorem coe_tvGL (a b : K) :
    ((tvGL a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = tvMat a b := rfl

private theorem coe_rotGL : ((rotGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = rotMat := rfl

private theorem coe_rotGL_inv :
    ((rotGL⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = rotInvMat := rfl

private theorem coe_swapGL01 :
    ((swapGL01 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat01 := rfl

private theorem coe_swapGL01_inv :
    ((swapGL01⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat01 := rfl

private theorem tvGL_mul (a b a' b' : K) :
    (tvGL a b : GL (Fin 3) K) * tvGL a' b' = tvGL (a + a') (b + b') :=
  Units.ext (tvMat_mul a b a' b')

private theorem rotGL_pow_three : (rotGL : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_rotGL, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem rotGL_conj_tvGL (a b : K) :
    (rotGL : GL (Fin 3) K) * tvGL a b * rotGL⁻¹ = tvGL (-b) (a - b) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rotGL, coe_rotGL_inv, coe_tvGL, coe_tvGL]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMat, rotInvMat, tvMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem swapGL01_conj_rotGL : (swapGL01 : GL (Fin 3) K) * rotGL * swapGL01⁻¹ = rotGL⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rotGL_inv, coe_swapGL01, coe_swapGL01_inv, coe_rotGL]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMat, rotInvMat, swapMat01, Matrix.mul_apply, Fin.sum_univ_three]

theorem realLocalElement_psl_three_char_two (h2 : (2 : K) = 0) :
    RealLocalElement (StatedProj (StatedSL 3 K)) 3 := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have hneg : (-1 : K) = 1 := by linear_combination (-1 : K) * h2
  have hx : (rotGL : GL (Fin 3) K) ∈ StatedSL 3 K := Subgroup.subset_closure (by
    change rotMat.det = 1; simp [rotMat, det_fin_three])
  have hX : (tvGL 0 1 : GL (Fin 3) K) ∈ StatedSL 3 K := Subgroup.subset_closure (by
    change (tvMat (0 : K) 1).det = 1; simp [tvMat, det_fin_three])
  have hY : (tvGL 1 0 : GL (Fin 3) K) ∈ StatedSL 3 K := Subgroup.subset_closure (by
    change (tvMat (1 : K) 0).det = 1; simp [tvMat, det_fin_three])
  have hd : (swapGL01 : GL (Fin 3) K) ∈ StatedSL 3 K := Subgroup.subset_closure (by
    change swapMat01.det = 1; simp [swapMat01, det_fin_three, hneg])
  refine realLocalElement_statedProj_of_klein (x := rotGL) (X := tvGL 0 1) (Y := tvGL 1 0)
    (d := swapGL01) hx hX hY hd rotGL_pow_three ?_ ?_ ?_ ?_ ?_ ?_ ?_ swapGL01_conj_rotGL
  · rintro ⟨c, hc⟩
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hc) 0) 1
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_rotGL, rotMat,
      Matrix.diagonal_apply] at this
  · rw [pow_two, tvGL_mul, add_zero, h11]
    exact Units.ext tvMat_zero
  · rw [pow_two, tvGL_mul, add_zero, h11]
    exact Units.ext tvMat_zero
  · simp only [tvGL_mul, add_comm]
  · rintro ⟨c, hc⟩
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hc) 1) 2
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_tvGL, tvMat,
      Matrix.diagonal_apply] at this
  · have h01 : (0 : K) - 1 = 1 := by rw [zero_sub]; exact hneg
    rw [rotGL_conj_tvGL, tvGL_mul, hneg, h01]
    simp
  · rw [rotGL_conj_tvGL]
    simp

theorem realLocalElement_psl_three : RealLocalElement (StatedProj (StatedSL 3 K)) 3 := by
  by_cases h2 : (2 : K) = 0
  · exact realLocalElement_psl_three_char_two h2
  · exact realLocalElement_statedProj_of_monomialData h2 monomialData_statedSL (mem_top _)

theorem realLocalElement_psu_three_odd {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    RealLocalElement (StatedProj (StatedSU 3 (p ^ f) K)) 3 := by
  have h2 : (2 : K) ≠ 0 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
    Nat.prime_two).1 ((CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)))
  refine realLocalElement_statedProj_of_monomialData h2 monomialData_statedSU ?_
  rw [mem_normOne]
  have hodd : Odd (p ^ f) := Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp2)
  exact Even.neg_one_pow (by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using hodd)

end Matrices

section Components

variable {H : Type} [Group H] [Finite H]

theorem false_of_realLocalElement_three (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂)
    (h3 : 3 ∣ Nat.card (center ↥L₁)) (hS : RealLocalElement (↥L₁ ⧸ center ↥L₁) 3) : False := by
  obtain ⟨R, hR, hR2, x, hxN, hx, d, hd⟩ := hS
  exact false_of_components he hc φ Nat.prime_three (by norm_num) hR hR2 hxN hx (Or.inl ⟨d, hd⟩)
    (fun h => absurd h3 h)

end Components

end CFSG.SectionRank.QTK.CentreFact.LayerPair
