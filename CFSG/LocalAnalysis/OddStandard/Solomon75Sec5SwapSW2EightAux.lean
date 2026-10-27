module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentMirror

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section EightAux

private theorem bcdEightAux_isPGroup_closure_pair {X : Type} [Group X] {s y : X} (hs2 : s * s = 1)
    (hy2 : y * y = 1) (hys : y * s = s * y) :
    IsPGroup 2 ↥(Subgroup.closure ({s, y} : Set X)) := by
  have hcomm : ({s, y} : Set X).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hys.symm
    · exact hys
    · exact Commute.refl _
  have hV := Subgroup.isMulCommutative_closure hcomm
  have hsq : ∀ g ∈ Subgroup.closure ({s, y} : Set X), g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hs2
      · exact hy2
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := setLike_mul_comm ha hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [sq] using hsq (g : X) g.2

end EightAux

section EightPieces

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem exists_datum_normalized (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    (hzs : z * s = s * z) {y : X} (hy2 : y * y = 1) (hyz : y * z = z * y) (hys : y * s = s * y)
    {M : Subgroup X} (hM : Sec5Comp X n (centralizer ({z} : Set X)) M)
    (hMs : M.map (MulAut.conj s).toMonoidHom ≠ M) :
    ∃ (Z' : Subgroup X) (S' : Sylow 2 ↥(normalizer (Z' : Set X))), Sec5Data X n z Z' S' ∧
      IsSec5Inv X Z' s ∧ y ∈ normalizer (Z' : Set X) := by
  have hVp : IsPGroup 2 ↥(Subgroup.closure ({s, y} : Set X)) :=
    bcdEightAux_isPGroup_closure_pair hs.sq hy2 hys
  have hsC : s ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hzs.symm
  have hyC : y ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hyz
  have hVC : Subgroup.closure ({s, y} : Set X) ≤ centralizer ({z} : Set X) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hsC
    · exact hyC
  have hsV : s ∈ Subgroup.closure ({s, y} : Set X) := Subgroup.subset_closure (by simp)
  have hyV : y ∈ Subgroup.closure ({s, y} : Set X) := Subgroup.subset_closure (by simp)
  obtain ⟨Zs, hZs, hVZs, -⟩ := exists_mirror_sylow_normalized X n (s := z) hVp hVC
  obtain ⟨c, hcK, hcZ⟩ := h.pair.sylow.exists_conj_eq hZs
  have hcC : c ∈ centralizer ({z} : Set X) := K0_le n _ hcK.1
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  obtain ⟨S', -, hS'⟩ := h.map (MulAut.conj c)
  have hcz' : (MulAut.conj c) z = z := by
    rw [MulAut.conj_apply, hcz]
    group
  rw [hcz'] at hS'
  subst hcZ
  refine ⟨_, S', hS', ⟨hVZs hsV, ?_, hs.sq, ?_⟩, hVZs hyV⟩
  ·
    intro hsZ'
    have hszs : s ∈ zStar (K0 X n (centralizer ({z} : Set X))) := hZs.1 hsZ'
    have hMK : M ≤ K0 X n (centralizer ({z} : Set X)) := le_sSup hM
    have hMK' : IsPCompIn 2 (K0 X n (centralizer ({z} : Set X))) M :=
      ⟨hMK, isPComponent_subgroupOf_mono hMK (K0_le n _) hM.isPCompIn.2⟩
    have hsK : s ∈ normalizer ((K0 X n (centralizer ({z} : Set X)) : Subgroup X) : Set X) :=
      mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hsC))
    have hsM : s ∈ centralizerSection M (pPrimeCoreOf 2 M) :=
      normalizes_isPCompIn_of_comm_mem (D := K0 X n (centralizer ({z} : Set X))) hMK' hsK
        (fun b hb => hszs.2.2.2 b (hMK hb))
    exact hMs (map_conj_eq_of_mem_normalizer hsM.1)
  ·
    obtain ⟨g, hg1, hg2⟩ := hs.conj
    refine ⟨g * c⁻¹, ?_, ?_⟩
    · have e : (g * c⁻¹)⁻¹ * s * (g * c⁻¹) = (MulAut.conj c) (g⁻¹ * s * g) := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact Subgroup.mem_map_of_mem _ hg1
    · intro h1
      apply hg2
      have e : (g * c⁻¹)⁻¹ * s * (g * c⁻¹) = (MulAut.conj c) (g⁻¹ * s * g) := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at h1
      exact (MulAut.conj c).injective (by simpa using h1)

theorem comm_mem_of_odd_commutator {G : Type*} [Group G] [Finite G] {Ĉ : Subgroup G} [Ĉ.Normal]
    {s : G} (hs : s ∈ Ĉ) {Q R : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hR : Odd (Nat.card ↥R)) {a b : G}
    (ha : a ∈ Q) (hb : b ∈ Q) (hab : ⁅a, s * b * s⁻¹⁆ ∈ R) : ⁅a, b⁆ ∈ Ĉ := by
  let π : G →* G ⧸ Ĉ := QuotientGroup.mk' Ĉ
  have hπs : π s = 1 := (QuotientGroup.eq_one_iff s).2 hs
  have hcomm : π ⁅a, s * b * s⁻¹⁆ = π ⁅a, b⁆ := by
    rw [map_commutatorElement, map_mul, map_mul, map_inv, hπs, one_mul, inv_one, mul_one,
      map_commutatorElement]
  have hQq : IsPGroup 2 ↥(Q.map π) := hQ.map π
  have hQab : ⁅a, b⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  obtain ⟨k, hk⟩ := hQq ⟨π ⁅a, b⁆, Subgroup.mem_map_of_mem π hQab⟩
  have hk' : (π ⁅a, b⁆) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf (π ⁅a, b⁆) ∣ Nat.card ↥R := by
    rw [← hcomm]
    exact (orderOf_map_dvd π _).trans (Subgroup.orderOf_dvd_natCard R hab)
  have h2 : orderOf (π ⁅a, b⁆) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : Nat.Coprime (2 ^ k) (Nat.card ↥R) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hR)
  have h4 : orderOf (π ⁅a, b⁆) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h3) h1
  exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h4)

end EightPieces

end CFSG.OddStandard.Solomon75
