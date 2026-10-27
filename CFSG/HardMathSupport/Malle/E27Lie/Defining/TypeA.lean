module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Unitriangular
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Adapters.LinearCatalog
public import CFSG.HardMathSupport.Foote.E27.SporKill

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.ComponentInitial TauCeti


theorem card_inf_centralizer_congr {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    {S : Subgroup G} {P : Subgroup H} (hSP : ∀ g, g ∈ S ↔ ψ g ∈ P) (s : G) :
    Nat.card (S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
      Nat.card (P ⊓ Subgroup.centralizer ({ψ s} : Set H) : Subgroup H) := by
  refine Nat.card_congr (ψ.toEquiv.subtypeEquiv fun g => ?_)
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, hSP]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← map_mul, ← map_mul, h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, ψ.injective (by rw [map_mul, map_mul, h2])⟩

theorem false_of_typeA_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (hp : q.p = 3) (hfr : 4 ≤ q.exponent * r)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFc : Nat.card F = 3 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp]
  have : CharP F 3 := hp ▸ (inferInstance : CharP F q.p)
  have hF81 : 81 ≤ Nat.card F ^ (r + 1 - 1) := by
    rw [hFc, Nat.add_sub_cancel, ← pow_mul]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (q.exponent * r) := Nat.pow_le_pow_right (by norm_num) hfr
  let ψ : ↥K ≃* LinearFlag.projectiveSL (r + 1) F :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) F)
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_projUnitriangular (K := F) 3 (n := r + 1) (by omega)
  let S₀ : Sylow 3 ↥K := P.comapOfInjective ψ.toMonoidHom ψ.injective (by
    rw [MonoidHom.range_eq_top_of_surjective _ ψ.surjective]; exact le_top)
  have hS₀ : ∀ g, g ∈ (S₀ : Subgroup ↥K) ↔ ψ g ∈ LinearFlag.projUnitriangular (r + 1) F := by
    intro g
    simp only [S₀, ← hP]
    rfl
  refine h.false_of_sylow_kill hz S₀ fun s hs _ => Or.inl ?_
  rw [card_inf_centralizer_congr ψ hS₀]
  exact dvd81_card_projUnitriangular_inf_centralizer (by omega) hF81 ((hS₀ s).mp hs)

end CFSG.HardMathSupport.Malle.E27Lie
