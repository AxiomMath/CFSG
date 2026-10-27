module

public import CFSG.ClassicalInvolution.RouteD.TWT4Model

public section

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_inv_four twin_std_u)
open CFSG.ClassicalInvolution.RouteD.SCRSu4 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD.TwinY

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Inv

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem jEl_mul_u_mem_center {u : Su K p f 4} (hu2 : suMat u * suMat u = -1) (ε : K)
    (hε2 : ε * ε = -1) (hσε : unitaryInvolution K p f ε = -ε) :
    jEl u ε hε2 hσε * u ∈ Subgroup.center (Su K p f 4) := by
  have h : suMat (jEl u ε hε2 hσε * u) = (-ε) • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [suMat_mul, suMat_jEl, Matrix.smul_mul, hu2]
    simp
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective
  rw [suMat_mul g (jEl u ε hε2 hσε * u), suMat_mul (jEl u ε hε2 hσε * u) g, h,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem exists_inv_of_fund_centralizing (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {u : Su K p f 4} (hu2 : suMat u * suMat u = -1)
    (htr : (suMat u).trace = 0) {ι : K} (hι2 : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = -ι) {L : Subgroup (Su K p f 4)}
    (hL : L ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (hLc : ∀ x ∈ L, x * u = u * x) {X : Type*} [Group X] {θ : Su K p f 4 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) :
    ∃ r ∈ L, r * r = 1 ∧ θ r ≠ 1 ∧ r * u ∈ Subgroup.center (Su K p f 4) := by
  obtain ⟨hι2', hσι'⟩ := neg_iota_props _ hι2 hσι
  rcases eq_longRootGroupSU_jEl hK hp hq hu2 htr hι2 hσι hL hLc with h | h
  · have hr := exists_isLongRootSU2_jEl hK hp hu2 htr ι hι2 hσι
    refine ⟨jEl u ι hι2 hσι, ?_, jEl_mul_self hu2 ι hι2 hσι, ?_,
      jEl_mul_u_mem_center hu2 ι hι2 hσι⟩
    · rw [h]
      exact jEl_mem_longRootGroup hu2 ι hι2 hσι
    · exact CFSG.ClassicalInvolution.Models.Transfer.map_ne_one_of_isLongRootSU2 hK hp hq
        (by norm_num) hker hr
  · have hr := exists_isLongRootSU2_jEl hK hp hu2 htr (-ι) hι2' hσι'
    refine ⟨jEl u (-ι) hι2' hσι', ?_, jEl_mul_self hu2 (-ι) hι2' hσι', ?_,
      jEl_mul_u_mem_center hu2 (-ι) hι2' hσι'⟩
    · rw [h]
      exact jEl_mem_longRootGroup hu2 (-ι) hι2' hσι'
    · exact CFSG.ClassicalInvolution.Models.Transfer.map_ne_one_of_isLongRootSU2 hK hp hq
        (by norm_num) hker hr

end Inv

section Model

variable {p : ℕ} [Fact p.Prime]


theorem twinMF_inv_central (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) (hmod : (p ^ e) % 4 = 3)
    {R R' : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    {x x' : (modelUniv .PSU 4 p e Fact.out).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 p e Fact.out) R R' x x')
    {a a' : (modelUniv .PSU 4 p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    {X : Type} [Group X] (ψ : (modelUniv .PSU 4 p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    {S : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    (hS : S ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D)
    (hSc : ∀ s ∈ S, (a * a') * s = s * (a * a')) :
    ∃ r ∈ S, r * r = 1 ∧ ψ r ≠ 1 ∧
      r * (a * a') ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSU 4 p e :=
    ⟨Fact.out, he, by norm_num, fun h => by
      have : (4 : ℕ) = 3 := congrArg Prod.fst h
      omega⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hdat := su4_twin_sq_trace hK hp2
    ((hφ R).mp hd.mem) ((hφ R').mp hd.mem')
    (fun h => hd.ne (Subgroup.map_injective φ.injective h))
    (x := φ x) (x' := φ x') ⟨x, hd.hx, rfl⟩
    (by
      rintro _ ⟨r, hr, rfl⟩
      show φ x * φ r = φ r * φ x
      rw [← map_mul, ← map_mul, hd.cx r hr])
    (fun h => hd.nx (φ.injective (h.trans (map_one φ).symm))) ⟨x', hd.hx', rfl⟩
    (by
      rintro _ ⟨r, hr, rfl⟩
      show φ x' * φ r = φ r * φ x'
      rw [← map_mul, ← map_mul, hd.cx' r hr])
    (fun h => hd.nx' (φ.injective (h.trans (map_one φ).symm)))
    (by
      rw [← map_inv, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hd.same)
    (a := φ a) (a' := φ a') ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq)
    (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq')
  obtain ⟨ι, hι2, hσι⟩ := exists_iota hK hmod
  have hc' : ∀ y ∈ S.map φ.toMonoidHom, y * (φ a * φ a') = (φ a * φ a') * y := by
    rintro _ ⟨s, hs, rfl⟩
    show φ s * (φ a * φ a') = (φ a * φ a') * φ s
    rw [← map_mul, ← map_mul, ← map_mul, hSc s hs]
  have hker' : (ψ.comp φ.symm.toMonoidHom).ker ≤
      Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    intro s hs
    have hs' : φ.symm s ∈ ψ.ker := hs
    have := CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ (hker hs')
    simpa using this
  obtain ⟨r', hr'L, hr'2, hr'1, hr'c⟩ := exists_inv_of_fund_centralizing hK hp2 hq hdat.1 hdat.2
    hι2 hσι ((hφ S).mp hS) hc' hker'
  obtain ⟨r, hrS, rfl⟩ := hr'L
  refine ⟨r, hrS, ?_, ?_, ?_⟩
  · apply φ.injective
    rw [map_mul, map_one]
    exact hr'2
  · intro h
    apply hr'1
    show ψ (φ.symm (φ r)) = 1
    rw [MulEquiv.symm_apply_apply]
    exact h
  · have := CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ.symm hr'c
    simpa [map_mul] using this

end Model

end CFSG.ClassicalInvolution.RouteD.TWT4
