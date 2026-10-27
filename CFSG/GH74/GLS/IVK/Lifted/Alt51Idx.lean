module

public import CFSG.GH74.GLS.Stage1.Thm4.Closed
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

section AutCover

theorem mulAut_eq_one_of_central_diff {K : Type} [Group K] (hK : commutator K = ⊤) (φ : MulAut K)
    (h : ∀ k : K, φ k * k⁻¹ ∈ Subgroup.center K) : φ = 1 := by
  let lam : K →* Subgroup.center K :=
    { toFun := fun k => ⟨φ k * k⁻¹, h k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.1 (h b)
        show φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (φ b * b⁻¹)
        calc φ (a * b) * (a * b)⁻¹ = φ a * ((φ b * b⁻¹) * a⁻¹) := by rw [map_mul]; group
          _ = φ a * (a⁻¹ * (φ b * b⁻¹)) := by rw [← hb a⁻¹]
          _ = (φ a * a⁻¹) * (φ b * b⁻¹) := by group }
  have hker : commutator K ≤ lam.ker := Abelianization.commutator_subset_ker lam
  rw [hK] at hker
  ext k
  have h1 : lam k = 1 := hker (Subgroup.mem_top k)
  have h2 : φ k * k⁻¹ = 1 := congrArg Subtype.val h1
  show φ k = k
  exact mul_inv_eq_one.1 h2

noncomputable def autQuotCenter (K : Type) [Group K] : MulAut K →* MulAut (K ⧸ center K) where
  toFun φ := QuotientGroup.congr (center K) (center K) φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H a => ?_
    simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro φ ψ
    ext x
    induction x using QuotientGroup.induction_on with | H a => ?_
    simp [QuotientGroup.congr_mk]

theorem autQuotCenter_mk {K : Type} [Group K] (φ : MulAut K) (a : K) :
    autQuotCenter K φ (a : K ⧸ center K) = ((φ a : K) : K ⧸ center K) := by
  simp [autQuotCenter, QuotientGroup.congr_mk]

theorem exists_central_of_autQuot_eq_one {H : Type} [Group H] {K : Subgroup H} [K.Normal]
    (hperf : commutator ↥K = ⊤) (hcent : ∀ h : H, (∀ k ∈ K, h * k = k * h) → h ∈ K) {h : H}
    (hθ : autQuotCenter ↥K (MulAut.conjNormal h) = 1) :
    ∃ k : ↥K, k ∈ center ↥K ∧ (k : H) = h := by
  have hcen : ∀ k : ↥K, (MulAut.conjNormal h : MulAut ↥K) k * k⁻¹ ∈ center ↥K := by
    intro k
    have := DFunLike.congr_fun hθ (k : ↥K ⧸ center ↥K)
    rw [autQuotCenter_mk] at this
    have h3 := (QuotientGroup.eq_iff_div_mem).1 (by simpa using this)
    rwa [div_eq_mul_inv] at h3
  have h1 : (MulAut.conjNormal h : MulAut ↥K) = 1 :=
    mulAut_eq_one_of_central_diff hperf _ hcen
  have hcomm : ∀ k ∈ K, h * k = k * h := by
    intro k hk
    have := DFunLike.congr_fun h1 ⟨k, hk⟩
    have h2 : h * k * h⁻¹ = k := by
      simpa [MulAut.conjNormal_apply] using congrArg Subtype.val this
    calc h * k = (h * k * h⁻¹) * h := by group
      _ = k * h := by rw [h2]
  have hhK : h ∈ K := hcent h (fun k hk => hcomm k hk)
  exact ⟨⟨h, hhK⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hcomm g g.2).symm), rfl⟩

end AutCover

section Index

theorem ivk_5_1_index : IVK_5_1_index := by
  intro H _ _ K n hH
  classical
  have hn5 : 5 ≤ n := by have := hH.n_ge; omega
  have hn6 : n ≠ 6 := by have := hH.n_ge; omega
  obtain ⟨hKq, hZ, ⟨e⟩⟩ := hH.cover
  have hKn : K.Normal := hH.normal
  have hperf : commutator ↥K = ⊤ := by
    have := hKq.1
    exact Group.IsPerfect.commutator_eq_top
  have hperm : Nat.card (Equiv.Perm (Fin n)) =
      2 * Nat.card (alternatingGroup (Fin n)) := by
    have h2 : Nat.card (alternatingGroup (Fin n)) * (alternatingGroup (Fin n)).index =
        Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_mul_index _
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [alternatingGroup.index_eq_two] at h2
    omega
  have hKcard : Nat.card ↥K = Nat.card (Equiv.Perm (Fin n)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K)
    rw [hZ, Nat.card_congr e.toEquiv] at h1
    rw [h1, hperm]
    ring
  have hAutA : Nat.card (MulAut (alternatingGroup (Fin n))) = Nat.card (Equiv.Perm (Fin n)) :=
    (Nat.card_eq_of_bijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)).symm
  have hAutQ : Nat.card (MulAut (↥K ⧸ center ↥K)) = Nat.card (Equiv.Perm (Fin n)) := by
    rw [← hAutA]
    exact Nat.card_congr (MulAut.congr e).toEquiv
  have : Finite (MulAut (↥K ⧸ center ↥K)) :=
    Finite.of_injective (fun f : MulAut (↥K ⧸ center ↥K) => (f : (↥K ⧸ center ↥K) → _))
      DFunLike.coe_injective
  let θ : H →* MulAut (↥K ⧸ center ↥K) :=
    (autQuotCenter ↥K).comp (MulAut.conjNormal : H →* MulAut ↥K)
  have hrange : Nat.card θ.range ≤ Nat.card (Equiv.Perm (Fin n)) := by
    rw [← hAutQ]
    exact Subgroup.card_le_card_group _
  have hker : Nat.card θ.ker ≤ 2 := by
    have hle : θ.ker ≤ (center ↥K).map K.subtype := by
      intro h hh
      obtain ⟨k, hk, rfl⟩ := exists_central_of_autQuot_eq_one hperf hH.cent (show θ h = 1 from hh)
      exact ⟨k, hk, rfl⟩
    calc Nat.card θ.ker ≤ Nat.card ↥((center ↥K).map K.subtype) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(center ↥K) :=
        (Nat.card_congr ((center ↥K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm
      _ = 2 := hZ
  have hH2 : Nat.card H ≤ 2 * Nat.card ↥K := by
    have := Subgroup.card_ker_mul_card_range θ
    rw [← this, hKcard]
    exact Nat.mul_le_mul hker hrange
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have := Subgroup.index_mul_card K
  by_contra hlt
  push Not at hlt
  have : 3 * Nat.card ↥K ≤ K.index * Nat.card ↥K := Nat.mul_le_mul_right _ hlt
  omega

end Index

end CFSG.GH74.GLS.IVK.Lifted
