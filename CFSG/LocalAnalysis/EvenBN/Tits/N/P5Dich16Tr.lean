module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5ExclSet
import CFSG.Goldschmidt.Steps.G310Comp

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N

variable {X : Type} [Group X] [Finite X]

theorem exists_lift_normalizer {A : Subgroup X} (hEA : IsElemAbelian 2 A) {nb : Mbar A}
    (hnb : nb ∈ normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))) :
    ∃ n : X, n ∈ nc A ∧ ∃ hn : n ∈ normalizer (A : Set X), ∀ a : ↥A,
      nb * piA A a * nb⁻¹ = piA A ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn a).1 a.2⟩ := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥(nc A)) nb
  have hker : Odd (Nat.card (proj A).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hA0 : IsPGroup 2 (A.subgroupOf (nc A)) := fun g => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    have := hEA.2 _ g.2
    simpa using this⟩
  obtain ⟨k, hk, n', hn', hmk⟩ := Lift.exists_mul_normalizer_of_normalizer_map (proj A) hker hA0
    (m := m) hnb
  have hnN : (n' : X) ∈ normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h0 := Subgroup.mem_normalizer_iff.1 hn'
    constructor
    · intro hy
      exact (h0 ⟨y, Subgroup.le_normalClosure hy⟩).1 hy
    · intro hy
      have hyM : y ∈ nc A := by
        have h1 : (n' : X)⁻¹ * ((n' : X) * y * (n' : X)⁻¹) * (n' : X) ∈ nc A :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ n'.2)
            (Subgroup.le_normalClosure hy)) n'.2
        have h2 : (n' : X)⁻¹ * ((n' : X) * y * (n' : X)⁻¹) * (n' : X) = y := by group
        rwa [h2] at h1
      exact (h0 ⟨y, hyM⟩).2 hy
  refine ⟨(n' : X), n'.2, hnN, fun a => ?_⟩
  have hkA : proj A k ∈ Abar A := ⟨k, hk, rfl⟩
  set a' : ↥A := ⟨(n' : X) * a * (n' : X)⁻¹, (Subgroup.mem_normalizer_iff.1 hnN a).1 a.2⟩ with ha'
  have hcomm : proj A k * piA A a' = piA A a' * proj A k :=
    congrArg Subtype.val ((isElemAbelian_Abar hEA).1.is_comm.comm ⟨_, hkA⟩
      ⟨_, piA_mem_Abar A a'⟩)
  have hconj : proj A n' * piA A a * (proj A n')⁻¹ = piA A a' := by
    rw [piA_apply, piA_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  calc proj A m * piA A a * (proj A m)⁻¹
      = proj A k * (proj A n' * piA A a * (proj A n')⁻¹) * (proj A k)⁻¹ := by
        rw [hmk]
        simp only [map_mul, mul_inv_rev]
        group
    _ = proj A k * piA A a' * (proj A k)⁻¹ := by rw [hconj]
    _ = piA A a' := by rw [hcomm]; group

@[expose] noncomputable def eAbar (A : Subgroup X) (hA2 : ∀ a ∈ A, a ^ 2 = 1) : ↥A ≃* ↥(Abar A) :=
  (MonoidHom.ofInjective (piA_injective hA2)).trans
    (MulEquiv.subgroupCongr (Abar_eq_range A).symm)

theorem coe_eAbar (A : Subgroup X) (hA2 : ∀ a ∈ A, a ^ 2 = 1) (a : ↥A) :
    ((eAbar A hA2 a : ↥(Abar A)) : Mbar A) = piA A a := rfl

theorem proj_conj_piA {A : Subgroup X} {g : X} (hgM : g ∈ nc A) (hg : g ∈ normalizer (A : Set X))
    (a : ↥A) : proj A ⟨g, hgM⟩ * piA A a * (proj A ⟨g, hgM⟩)⁻¹ =
      piA A ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg a).1 a.2⟩ := by
  rw [piA_apply, piA_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem proj_mem_normalizer_Abar {A : Subgroup X} {g : X} (hgM : g ∈ nc A)
    (hg : g ∈ normalizer (A : Set X)) :
    proj A ⟨g, hgM⟩ ∈ normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    obtain ⟨a, rfl⟩ := (mem_Abar_iff A).1 hq
    rw [proj_conj_piA hgM hg a]
    exact piA_mem_Abar A _
  · intro hq
    obtain ⟨b, hb⟩ := (mem_Abar_iff A).1 hq
    have hgM' : g⁻¹ ∈ nc A := Subgroup.inv_mem _ hgM
    have hg' : g⁻¹ ∈ normalizer (A : Set X) := Subgroup.inv_mem _ hg
    have h1 := proj_conj_piA hgM' hg' b
    have h2 : proj A ⟨g⁻¹, hgM'⟩ = (proj A ⟨g, hgM⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h2, hb] at h1
    have h3 : (proj A ⟨g, hgM⟩)⁻¹ * (proj A ⟨g, hgM⟩ * q * (proj A ⟨g, hgM⟩)⁻¹) *
        ((proj A ⟨g, hgM⟩)⁻¹)⁻¹ = q := by group
    rw [h3] at h1
    rw [h1]
    exact piA_mem_Abar A _

theorem congr_eAbar_apply (A : Subgroup X) (hA2 : ∀ a ∈ A, a ^ 2 = 1) (σ : MulAut ↥A) (a : ↥A) :
    (MulAut.congr (eAbar A hA2) σ) (eAbar A hA2 a) = eAbar A hA2 (σ a) := by
  simp [MulAut.congr_apply]

theorem congr_mem_imgIn {A : Subgroup X} (hA2 : ∀ a ∈ A, a ^ 2 = 1) {σ : MulAut ↥A}
    (hσ : σ ∈ imgIn A (nc A)) :
    MulAut.congr (eAbar A hA2) σ ∈
      imgIn (Abar A) (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))) := by
  obtain ⟨g, hgM, hg, rfl⟩ := (mem_imgIn_iff A (nc A)).1 hσ
  have hnb := proj_mem_normalizer_Abar hgM hg
  refine (mem_imgIn_normalizer_iff (Abar A)).2 ⟨proj A ⟨g, hgM⟩, hnb, ?_⟩
  refine MulEquiv.ext fun v => ?_
  obtain ⟨a, rfl⟩ := (eAbar A hA2).surjective v
  rw [congr_eAbar_apply]
  apply Subtype.ext
  rw [actFun_apply_coe (Abar A) hnb]
  have hact : actFun A g a =
      ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg a).1 a.2⟩ :=
    Subtype.ext (actFun_apply_coe A hg a)
  rw [coe_eAbar, coe_eAbar, hact]
  exact proj_conj_piA hgM hg a

theorem exists_congr_of_mem_imgIn {A : Subgroup X} (hEA : IsElemAbelian 2 A) {τ : MulAut ↥(Abar A)}
    (hτ : τ ∈ imgIn (Abar A) (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)))) :
    ∃ σ ∈ imgIn A (nc A), MulAut.congr (eAbar A hEA.2) σ = τ := by
  obtain ⟨nb, hnb, rfl⟩ := (mem_imgIn_normalizer_iff (Abar A)).1 hτ
  obtain ⟨n, hnM, hn, hact⟩ := exists_lift_normalizer hEA hnb
  refine ⟨actFun A n, actFun_mem_imgIn hnM hn, ?_⟩
  refine MulEquiv.ext fun v => ?_
  obtain ⟨a, rfl⟩ := (eAbar A hEA.2).surjective v
  rw [congr_eAbar_apply]
  apply Subtype.ext
  rw [actFun_apply_coe (Abar A) hnb]
  have hact' : actFun A n a =
      ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn a).1 a.2⟩ :=
    Subtype.ext (actFun_apply_coe A hn a)
  rw [coe_eAbar, coe_eAbar, hact']
  exact (hact a).symm

theorem map_congr_imgIn_nc {A : Subgroup X} (hEA : IsElemAbelian 2 A) :
    (imgIn A (nc A)).map (MulAut.congr (eAbar A hEA.2)).toMonoidHom =
      imgIn (Abar A) (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact congr_mem_imgIn hEA.2 hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_congr_of_mem_imgIn hEA hτ
    exact ⟨σ, hσ, h⟩

theorem card_imgIn_Abar (A : Subgroup X) :
    Nat.card (imgIn (Abar A) (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)))) =
      (centralizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))).relIndex
        (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))) := by
  set N := normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)) with hN
  set C := centralizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)) with hC
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have h1 := card_imgIn_mul_card (Abar A) N
  have h2 := Subgroup.relIndex_mul_card C N
  rw [inf_eq_right.2 hCN, inf_idem] at h1
  rw [inf_eq_left.2 hCN] at h2
  have hpos : 0 < Nat.card ↥C := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem exists_B₀ {A : Subgroup X} (hEA : IsElemAbelian 2 A)
    (htrans : ∀ a ∈ Abar A, ∀ b ∈ Abar A, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)), n⁻¹ * a * n = b)
    (hodd : Odd ((centralizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))).relIndex
      (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A))))) :
    ∃ B₀ : Subgroup (MulAut ↥A), B₀ ≤ imgIn A (normalizer (A : Set X)) ∧
      (∀ h ∈ imgIn A (normalizer (A : Set X)), ∀ b ∈ B₀, h * b * h⁻¹ ∈ B₀) ∧
      Odd (Nat.card B₀) ∧ ∀ a b : ↥A, a ≠ 1 → b ≠ 1 → ∃ g ∈ B₀, g a = b := by
  refine ⟨imgIn A (nc A), imgIn_le_range A (nc A), ?_, ?_, ?_⟩
  · intro h hh b hb
    obtain ⟨g, hg, rfl⟩ := (mem_imgIn_normalizer_iff A).1 hh
    have hmap := imgIn_map_conj A (nc A) hg
    rw [G310.map_conj_eq_of_normal (inferInstance : (nc A).Normal) g] at hmap
    have h1 : (MulAut.conj (actFun A g)) b ∈
        (imgIn A (nc A)).map (MulAut.conj (actFun A g)).toMonoidHom := ⟨b, hb, rfl⟩
    rw [← hmap] at h1
    simpa [MulAut.conj_apply] using h1
  · have hcard : Nat.card (imgIn A (nc A)) =
        Nat.card (imgIn (Abar A) (normalizer ((Abar A : Subgroup (Mbar A)) : Set (Mbar A)))) := by
      have hinj : Function.Injective (MulAut.congr (eAbar A hEA.2)).toMonoidHom :=
        (MulAut.congr (eAbar A hEA.2)).injective
      have h1 := Subgroup.card_map_of_injective (K := imgIn A (nc A)) hinj
      rw [map_congr_imgIn_nc hEA] at h1
      exact h1.symm
    rw [hcard, card_imgIn_Abar]
    exact hodd
  · intro a b ha hb
    have hne : ∀ c : ↥A, c ≠ 1 → piA A c ≠ 1 := fun c hc h =>
      hc (piA_injective hEA.2 (h.trans (map_one (piA A)).symm))
    obtain ⟨nb, hnb, hnab⟩ := htrans (piA A a) (piA_mem_Abar A a) (piA A b) (piA_mem_Abar A b)
      (hne a ha) (hne b hb)
    obtain ⟨n, hnM, hn, hact⟩ := exists_lift_normalizer hEA (Subgroup.inv_mem _ hnb)
    refine ⟨actFun A n, actFun_mem_imgIn hnM hn, ?_⟩
    have h1 := hact a
    rw [inv_inv, hnab] at h1
    apply Subtype.ext
    rw [actFun_apply_coe A hn]
    exact congrArg Subtype.val (piA_injective hEA.2 h1).symm

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
