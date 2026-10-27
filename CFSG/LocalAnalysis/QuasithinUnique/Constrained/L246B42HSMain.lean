module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeTrans
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.QuasithinUnique.Bridge.HSExcl

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Blueprint
open scoped commutatorElement

section Trans

variable {G : Type*} [Group G] {S : Type*} [Group S]

theorem aut_model_of_conj {P R : Subgroup G} (hPR : P ≤ R) (θ : S ≃* ↥P) (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), ((e x p : ↥P) : G) = (x : G) * p * (x : G)⁻¹) :
    ∃ Φ : ↥R ≃* MulAut S, ∀ s : S, Φ ⟨(θ s : G), hPR (θ s).2⟩ = MulAut.conj s := by
  refine ⟨e.trans (MulAut.congr (G := ↥P) (H := S) θ.symm), fun s => ?_⟩
  refine MulEquiv.ext fun s' => ?_
  have h1 : e ⟨(θ s : G), hPR (θ s).2⟩ (θ s') = θ (s * s' * s⁻¹) := by
    apply Subtype.ext
    rw [he]
    simp [map_mul, map_inv]
  simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_symm, MulAut.conj_apply, h1,
    MulEquiv.symm_apply_apply]

theorem mem_range_conj_of_mem {P R : Subgroup G} (hPR : P ≤ R) (θ : S ≃* ↥P)
    (Φ : ↥R ≃* MulAut S) (hΦ : ∀ s : S, Φ ⟨(θ s : G), hPR (θ s).2⟩ = MulAut.conj s)
    (x : ↥R) (hxP : (x : G) ∈ P) : Φ x ∈ (MulAut.conj : S →* MulAut S).range := by
  refine ⟨θ.symm ⟨(x : G), hxP⟩, ?_⟩
  rw [← hΦ]
  congr 1
  apply Subtype.ext
  simp

theorem exists_inner_of_equiv_index_two [Finite G] {P R : Subgroup G} (hPR : P ≤ R)
    (θ : S ≃* ↥P) (Φ : ↥R ≃* MulAut S)
    (hΦ : ∀ s : S, Φ ⟨(θ s : G), hPR (θ s).2⟩ = MulAut.conj s)
    (hidx : (P.subgroupOf R).index ≤ 2) {B : Subgroup (MulAut S)} (hB : 4 ≤ Nat.card B) :
    ∃ ψ ∈ B, ψ ≠ 1 ∧ ψ ∈ (MulAut.conj : S →* MulAut S).range := by
  have hcard : Nat.card (B.comap Φ.toMonoidHom) = Nat.card B :=
    Nat.card_congr (Φ.toEquiv.subtypeEquiv (fun a => Iff.rfl))
  obtain ⟨x, hxB, hx1, hxN⟩ := exists_mem_of_index_two hidx (B := B.comap Φ.toMonoidHom)
    (by rw [hcard]; exact hB)
  exact ⟨Φ x, hxB, fun h => hx1 (Φ.injective (by rw [h, map_one])),
    mem_range_conj_of_mem hPR θ Φ hΦ x hxN⟩

end Trans

noncomputable def hsEquivC
    : NativeSporadic.Carrier .HS ≃* ↥hsP := hsPermEquiv

theorem hs_aut_model
    : ∃ Φ : ↥hsR ≃* MulAut (NativeSporadic.Carrier .HS),
    ∀ s : NativeSporadic.Carrier .HS,
      Φ ⟨(hsEquivC s : Equiv.Perm (Fin 3850)), hsP_le_hsR (hsEquivC s).2⟩ = MulAut.conj s := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  exact aut_model_of_conj hsP_le_hsR hsEquivC e he

theorem hs_rank
    : ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .HS)),
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6 := by
  obtain ⟨Φ, -⟩ := hs_aut_model
  exact rank_of_equiv Φ hs_rank_R

theorem hs_index_two
    : (hsP.subgroupOf hsR).index ≤ 2 := by
  have h1 := (hsP.subgroupOf hsR).card_mul_index
  have h2 : Nat.card (hsP.subgroupOf hsR) = 44352000 := by
    rw [← card_hsP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsP_le_hsR).toEquiv
  rw [h2, hs_normalizing_model.2.2.2.2.2.2.2.2.1] at h1
  omega

theorem hs_inn
    : ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .HS)),
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → 4 ≤ Nat.card B →
    ∃ ψ ∈ B, ψ ≠ 1 ∧ ψ ∈ (MulAut.conj : NativeSporadic.Carrier .HS →*
      MulAut (NativeSporadic.Carrier .HS)).range := by
  obtain ⟨Φ, hΦ⟩ := hs_aut_model
  intro B _ _ hB
  exact exists_inner_of_equiv_index_two hsP_le_hsR hsEquivC Φ hΦ hs_index_two hB

theorem hs_gen3
    : ∀ ψ : MulAut (NativeSporadic.Carrier .HS), ψ * ψ = 1 → ψ ≠ 1 →
    ψ ∈ (MulAut.conj : NativeSporadic.Carrier .HS →*
      MulAut (NativeSporadic.Carrier .HS)).range →
    ∃ cs : List (MulAut (NativeSporadic.Carrier .HS)), cs.length = 3 ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .HS →*
        MulAut (NativeSporadic.Carrier .HS)).range) ∧
      ∀ s : NativeSporadic.Carrier .HS,
        MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}) := by
  obtain ⟨Φ, hΦ⟩ := hs_aut_model
  exact gen_inner_of_equiv (G := Equiv.Perm (Fin 3850)) (H := hsR) (A := hsP) hsP_le_hsR Φ
    hsEquivC hΦ (k := 3) fun x hx hx2 hx1 => hs_gen_inner hx (by rw [sq]; exact hx2) hx1

theorem hs_gen4
    : ∀ ψ : MulAut (NativeSporadic.Carrier .HS), ψ * ψ = 1 → ψ ≠ 1 →
    ∃ cs : List (MulAut (NativeSporadic.Carrier .HS)), cs.length = 4 ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .HS →*
        MulAut (NativeSporadic.Carrier .HS)).range) ∧
      ∀ s : NativeSporadic.Carrier .HS,
        MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}) := by
  obtain ⟨Φ, hΦ⟩ := hs_aut_model
  exact gen_of_equiv (G := Equiv.Perm (Fin 3850)) (H := hsR) (A := hsP) hsP_le_hsR Φ hsEquivC hΦ
    (k := 4) fun x hx hx2 hx1 => hs_gen_all hx (by rw [sq]; exact hx2) hx1

theorem orderOf_two_zmod_5 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem dim_of_sylow5 {S : Type} [Group S] {x y : S} (hx : x ^ 5 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (V : Type) [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (σ : S →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 20 ≤ Nat.card V := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx' : (σ x) ^ 5 = 1 := by rw [← map_pow, hx, map_one]
  have hz' : ⁅σ x, σ y⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    exact fun h => hz (hσ (h.trans (map_one σ).symm))
  have hzx' : Commute ⁅σ x, σ y⁆ (σ x) := by
    rw [← map_commutatorElement]
    exact hzx.map σ
  have hzy' : Commute ⁅σ x, σ y⁆ (σ y) := by
    rw [← map_commutatorElement]
    exact hzy.map σ
  have h := two_pow_mul_le_card_of_extraspecial hV (p := 5) (by norm_num) hx' hz' hzx' hzy'
  rwa [orderOf_two_zmod_5] at h

theorem hs_dim
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (σ : NativeSporadic.Carrier .HS →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 20 ≤ Nat.card V := by
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
  exact dim_of_sylow5 (S := NativeSporadic.Carrier .HS) (x := x) (y := y) hx hz hzx hzy V hV σ hσ

theorem hs_cover
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.Carrier .HS) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ :=
  CFSG.SectionRank.HS_perfect_odd_cover_trivial π hπ hC hodd

theorem sporadicExclusion_HS
    : X1.SporadicExclusion .HS := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Nontrivial (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.2.1
  exact weight_lt_of_gen34 hW hq.1 hirr hE hEne hEel e (r := 6) (ρ := 20) (by norm_num)
    (by norm_num) (fun E _ _ _ π hπ hC hodd => hs_cover E π hπ hC hodd) hs_rank hs_inn hs_gen3
    hs_gen4 hs_dim

end CFSG.QuasithinUnique.Bridge.HSExcl
