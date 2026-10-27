module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeParams
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeGen

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock longInv shortBlock planeTorusElt
  transvOne)
open CFSG.ClassicalInvolution.RouteD.LeviModel
open CFSG.ClassicalInvolution.WeakCT (torusHom torusHom_injective)
open scoped MatrixGroups

section Triple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem zf_two_eq (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (hZ : Subgroup.center G = ⊥) (Fr : Frame p f 2 Ω K z) : Fr.zf 2 = Fr.zf 0 * Fr.zf 1 := by
  have htrip := zf_mul_zf_mul_zf S hconn hZ Fr
  have hsq : ∀ i : Fin 3, Fr.zf i * Fr.zf i = 1 := fun i => by
    have h := pow_orderOf_eq_one (Fr.zf i)
    rw [(Fr.clsW S i).orderOf_eq_two, pow_two] at h
    exact h
  rw [eq_inv_of_mul_eq_one_right htrip, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq 0),
    inv_eq_of_mul_eq_one_right (hsq 1), Fr.zf_commW S 1 0]

theorem zf_zero_eq (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (hZ : Subgroup.center G = ⊥) (Fr : Frame p f 2 Ω K z) : Fr.zf 0 = Fr.zf 1 * Fr.zf 2 := by
  have h2 := zf_two_eq S hconn hZ Fr
  have hsq : ∀ i : Fin 3, Fr.zf i * Fr.zf i = 1 := fun i => by
    have h := pow_orderOf_eq_one (Fr.zf i)
    rw [(Fr.clsW S i).orderOf_eq_two, pow_two] at h
    exact h
  rw [h2, ← mul_assoc, Fr.zf_commW S 1 0, mul_assoc, hsq 1, mul_one]

end Triple

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {S : CSetupW p f 2 Ω K z} {Fr : Frame p f 2 Ω K z}
  (P : LeviParams S Fr)

namespace LeviParams

theorem zf_two_mem (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) : Fr.zf 2 ∈ P.T₀ := by
  have e0 : P.ψ₂ (longInv (GaloisField p f) 2 0) = Fr.zf 0 := P.ψ₂_longInv 0
  have e1 : P.ψ₂ (longInv (GaloisField p f) 2 1) = Fr.zf 1 := P.ψ₂_longInv 1
  have : Fr.zf 2 = P.ψ₂ (longInv (GaloisField p f) 2 0 * longInv (GaloisField p f) 2 1) := by
    rw [map_mul, e0, e1]
    exact zf_two_eq S hconn hZ Fr
  rw [this, P.T₀_eq]
  exact Subgroup.mem_map_of_mem _ LeviModel.neg_one_mem_range_shortBlock

theorem zf_zero_mem (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) :
    Fr.zf 0 ∈ P.T₁ := by
  have e0 : P.ψ₀ (longInv (GaloisField p f) 2 0) = Fr.zf 1 := P.ψ₀_longInv 0
  have e1 : P.ψ₀ (longInv (GaloisField p f) 2 1) = Fr.zf 2 := P.ψ₀_longInv 1
  have : Fr.zf 0 = P.ψ₀ (longInv (GaloisField p f) 2 0 * longInv (GaloisField p f) 2 1) := by
    rw [map_mul, e0, e1]
    exact zf_zero_eq S hconn hZ Fr
  rw [this, P.T₁_eq]
  exact Subgroup.mem_map_of_mem _ LeviModel.neg_one_mem_range_shortBlock

theorem nonempty_equiv₀ : Nonempty (SL(2, GaloisField p f) ≃* ↥P.T₀) := by
  rw [P.T₀_eq]
  exact nonempty_equiv_node P.ψ₂ P.ψ₂_injective

theorem nonempty_equiv₁ : Nonempty (SL(2, GaloisField p f) ≃* ↥P.T₁) := by
  rw [P.T₁_eq]
  exact nonempty_equiv_node P.ψ₀ P.ψ₀_injective

theorem not_commutes (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) :
    ¬ Commutes P.T₀ P.T₁ := by
  intro h
  have hz0 : Fr.zf 0 ∈ P.T₁ := P.zf_zero_mem hconn hZ
  have hs : P.ψ₂ (shortBlock (GaloisField p f) fin_two_zero_ne_one
      (transvOne (GaloisField p f))) ∈ P.T₀ := by
    rw [P.T₀_eq]
    exact Subgroup.mem_map_of_mem _ ⟨_, rfl⟩
  have hc := h _ hs _ hz0
  have e0 : P.ψ₂ (longInv (GaloisField p f) 2 0) = Fr.zf 0 := P.ψ₂_longInv 0
  refine Models.SymplecticPairs.not_commute_shortBlock_longInv fin_two_zero_ne_one S.two_ne_zero ?_
  show _ * _ = _ * _
  apply P.ψ₂_injective
  rw [map_mul, map_mul, e0]
  exact hc

theorem exists_torus_normalizing :
    ∃ t ∈ P.T₀, orderOf t = p ^ f - 1 ∧ conjSub t P.T₁ = P.T₁ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p f)ˣ)
  have hab : (0 : Fin 2) ≠ 1 := fin_two_zero_ne_one
  set t := P.ψ₂ (shortBlock (GaloisField p f) hab (torusHom (GaloisField p f) g)) with ht
  set u₀ := P.ψ₂ (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) g)) with hu₀
  set u₁ := P.ψ₂ (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) g⁻¹)) with hu₁
  have hfac : t = u₀ * u₁ := by
    rw [ht, shortBlock_torusHom hab, planeTorusElt, map_mul]
  have hu₀T : u₀ ∈ Fr.Tf 0 := P.ψ₂_torus 0 g
  have hu₁T : u₁ ∈ Fr.Tf 1 := P.ψ₂_torus 1 g⁻¹
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [P.T₀_eq]
    exact Subgroup.mem_map_of_mem _ ⟨_, rfl⟩
  · have hinj : Function.Injective
        ((P.ψ₂.comp (shortBlock (GaloisField p f) hab)).comp (torusHom (GaloisField p f))) :=
      (P.ψ₂_injective.comp (Models.SymplecticPairs.shortBlock_injective hab)).comp
        torusHom_injective
    have h1 := orderOf_injective _ hinj g
    have h2 : orderOf g = Nat.card (GaloisField p f)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [Nat.card_units, S.card_eq] at h2
    exact h1.trans h2
  · have hmul : ∀ {x : G} {k : Fin 3}, x ∈ Fr.Tf k → t * x = x * t := by
      intro x k hx
      rw [hfac, mul_assoc, Fr.Tf_mul_comm hu₁T hx, ← mul_assoc, Fr.Tf_mul_comm hu₀T hx, mul_assoc]
    have hz0 : t * Fr.zf 0 = Fr.zf 0 * t := by
      rw [hfac, mul_assoc, Fr.commute_zfW S 1 0 u₁ (Frame.Tf_le 1 hu₁T), ← mul_assoc,
        Fr.commute_zfW S 0 0 u₀ (Frame.Tf_le 0 hu₀T), mul_assoc]
    have hy : conjSub t (Mf Fr 1 2) = Mf Fr 1 2 :=
      conjSub_Mf_eq_of_commute S Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide)
        (by decide) hz0
    have hd : P.x₁ * P.x₂ ∈ Mf Fr 1 2 := (Mf Fr 1 2).mul_mem
      (Tf_le_Mf Fr 1 (Or.inl rfl) P.x₁_mem) (Tf_le_Mf Fr 2 (Or.inr rfl) P.x₂_mem)
    have hk : ∀ m ∈ Mf Fr 1 2, m * P.x₀ = P.x₀ * m := fun m hm =>
      commutes_Mf_Kf Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide) m hm P.x₀
        (Frame.Tf_le 0 P.x₀_mem)
    have hyh : t * (P.x₁ * P.x₂ * P.x₀) * t⁻¹ = P.x₁ * P.x₂ * P.x₀ := by
      refine mul_inv_eq_iff_eq_mul.mpr ?_
      exact ((show Commute t P.x₁ from hmul P.x₁_mem).mul_right
        (show Commute t P.x₂ from hmul P.x₂_mem)).mul_right
          (show Commute t P.x₀ from hmul P.x₀_mem) |>.eq
    exact conjSub_leviNode hd hk hy hyh

end LeviParams

end Levi

end CFSG.ClassicalInvolution.RouteD
