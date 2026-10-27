module

public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GorensteinWalter
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer

namespace P47SL2e

section Aut

variable {F : Type} [Field F] [Finite F]

theorem subsingleton_ringAut_of_card_five (hF : Nat.card F = 5) : Subsingleton (F ≃+* F) := by
  have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (p := 5) (n := 1)
    (by norm_num) F (by simpa using hF)).1
  exact (Nat.card_eq_one_iff_unique.1 h).1

theorem card_le_four_of_elemAbelian (hF : Nat.card F = 5) {K : Type} [Group K] [Finite K]
    (e : K ≃* L2 F) (A : Subgroup (MulAut K)) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x * x = 1) : Nat.card ↥A ≤ 4 := by
  have hL : L2Field F := ⟨by rw [hF]; decide, by rw [hF]; norm_num⟩
  have hA2 : IsPGroup 2 ↥A := fun g => ⟨1, by
    apply Subtype.ext
    simpa [sq] using hsq g.1 g.2⟩
  obtain ⟨T, hT⟩ := hA2.exists_le_sylow
  have : Subsingleton (F ≃+* F) := subsingleton_ringAut_of_card_five hF
  have hG : A ≤ innDiagSub e := fun x _ => (mem_innDiagSub_iff e x).2 (Subsingleton.elim _ _)
  exact card_le_four_of_le_inf e hL T A hT hG hcomm hsq

end Aut

section Count

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem card_le_four_mul_card_cent_e {X : Subgroup Y} (hc : C43e X) {E : Subgroup Y}
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card ↥E ≤ 4 * Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) := by
  classical
  obtain ⟨⟨F, _, _, hF5, ⟨φ⟩⟩, -⟩ := hc
  have hF5' : Nat.card F = 5 := hF5
  have hnormal : (ncl X).Normal := Subgroup.normalClosure_normal
  let ψ : ↥(ncl X) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    φ.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hodd : Odd (Nat.card F) := by rw [hF5']; decide
  have h3 : 3 < Nat.card F := by rw [hF5']; norm_num
  let ρ : ↥E →* MulAut (PSL2 F) :=
    (psl2AutHom.comp (MulAut.congr ψ).toMonoidHom).comp
      ((MulAut.conjNormal : Y →* MulAut ↥(ncl X)).comp E.subtype)
  have hρ : ∀ x : ↥E, ρ x = psl2AutHom (MulAut.congr ψ (MulAut.conjNormal (x : Y))) := fun x => rfl
  have hker : ∀ x : ↥E, ρ x = 1 ↔ (x : Y) ∈ centralizer ((ncl X : Subgroup Y) : Set Y) := by
    intro x
    rw [hρ, map_eq_one_iff _ (psl2AutHom_injective hodd h3), EmbeddingLike.map_eq_one_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
      have h2 : (x : Y) * k * (x : Y)⁻¹ = k := h1
      calc k * (x : Y) = ((x : Y) * k * (x : Y)⁻¹) * (x : Y) := by rw [h2]
        _ = (x : Y) * k := by group
    · intro h
      ext k
      show (x : Y) * (k : Y) * (x : Y)⁻¹ = k
      rw [mul_inv_eq_iff_eq_mul]
      exact (h k k.2).symm
  have hsq : ∀ α ∈ ρ.range, α * α = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simpa [sq] using hE.2 x x.2)
    rw [this, map_one]
  have hcomm : ∀ α ∈ ρ.range, ∀ β ∈ ρ.range, α * β = β * α := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact hE.1.is_comm.comm x y
  have hrange : Nat.card ρ.range ≤ 4 :=
    card_le_four_of_elemAbelian hF5' (L2.equivPSL F).symm ρ.range hcomm hsq
  have hkerCard : Nat.card ρ.ker = Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) := by
    have hmap : ρ.ker.map E.subtype = E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (hker x).1 (MonoidHom.mem_ker.1 hx)⟩
      · rintro ⟨hyE, hyC⟩
        exact ⟨⟨y, hyE⟩, MonoidHom.mem_ker.2 ((hker ⟨y, hyE⟩).2 hyC), rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective E.subtype_injective]
  calc Nat.card ↥E = Nat.card ρ.ker * Nat.card ρ.range := (Subgroup.card_ker_mul_card_range ρ).symm
    _ ≤ Nat.card ρ.ker * 4 := Nat.mul_le_mul_left _ hrange
    _ = 4 * Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) := by
      rw [hkerCard, mul_comm]

end Count

end P47SL2e

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
