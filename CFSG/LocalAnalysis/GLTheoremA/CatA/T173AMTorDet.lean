module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
import CFSG.RankThree.PartOne.CTP.SeitzDiag
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement MatrixGroups

theorem tor_toral_diag {p d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (htor : MToral p d F G) :
    (∃ P : GL (Fin d) F, MDiagAt d F P G) ∧
      (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d - 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hζ : ∃ ζ : F, IsPrimitiveRoot ζ p := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (by rwa [Nat.card_units F])
    have hzp : IsPrimitiveRoot z p := hz ▸ IsPrimitiveRoot.orderOf z
    exact ⟨(z : F), IsPrimitiveRoot.coe_units_iff.mpr hzp⟩
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  ·
    subst hd0
    constructor
    · refine ⟨1, fun g _ => ⟨fun _ => 0, Subsingleton.elim _ _⟩⟩
    · have hcardG : Nat.card ↥G = 1 :=
        Nat.card_of_subsingleton (⟨1, G.one_mem⟩ : ↥G)
      have hdvd := Subgroup.relIndex_dvd_card (H := LargeEvenScalars (Fin 0) F) (K := G)
      rw [hcardG] at hdvd
      have hle : (LargeEvenScalars (Fin 0) F).relIndex G ≤ 1 :=
        Nat.le_of_dvd one_pos hdvd
      simpa using hle
  letI : CommGroup ↥G :=
    { (inferInstance : Group ↥G) with
      mul_comm := fun a b => Subtype.ext (htor.1 a a.2 b b.2) }
  let K : Subgroup ↥G := (powMonoidHom (α := ↥G) p).ker
  let H : Subgroup (GL (Fin d) F) := K.map G.subtype
  have hHG : H ≤ G := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, _, rfl⟩
    exact k.2
  have hcommH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x :=
    fun x hx y hy => htor.1 x (hHG hx) y (hHG hy)
  have hexpH : ∀ x ∈ H, x ^ p = 1 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    have hk' : (powMonoidHom (α := ↥G) p) k = 1 := MonoidHom.mem_ker.mp hk
    have := congrArg (Subtype.val) hk'
    simpa [powMonoidHom_apply] using this
  obtain ⟨T, hT⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime hζ H hcommH hexpH
  have hdiagG : ∃ P : GL (Fin d) F, MDiagAt d F P G := by
    refine ⟨T, fun a ha => ?_⟩
    have hoff : ((T * a * T⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).IsDiag := by
      intro i j hij
      obtain ⟨b, hb⟩ := htor.2 a ha
      set h0 : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) b * a with h0def
      set s : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) b⁻¹ with sdef
      have hh0G : h0 ∈ G := by
        rw [h0def]
        exact mul_mem (hZG (MonoidHom.mem_range.mpr ⟨b, rfl⟩)) ha
      have hh0K : (⟨h0, hh0G⟩ : ↥G) ∈ K := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        simpa [h0def, powMonoidHom_apply] using hb
      have hh0H : h0 ∈ H := Subgroup.mem_map.mpr ⟨⟨h0, hh0G⟩, hh0K, rfl⟩
      have hoff0 : ((T * h0 * T⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0 :=
        hT h0 hh0H i j hij
      have haeq : a = s * h0 := by
        rw [sdef, h0def]
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      have hGL : (T * a * T⁻¹ : GL (Fin d) F) =
          (T * s * T⁻¹ : GL (Fin d) F) * (T * h0 * T⁻¹ : GL (Fin d) F) := by
        rw [haeq]
        group
      have hT1 : (T * s * T⁻¹ : GL (Fin d) F) = s := by
        rw [sdef, ← Matrix.GeneralLinearGroup.scalar_commute b⁻¹ T, mul_assoc,
          mul_inv_cancel, mul_one]
      have hscal : ((T * s * T⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          Matrix.diagonal (fun _ => ((b⁻¹ : Fˣ) : F)) := by
        rw [hT1, sdef, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      have hfac : ((T * a * T⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          Matrix.diagonal (fun _ => ((b⁻¹ : Fˣ) : F)) *
            ((T * h0 * T⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
        rw [hGL, Matrix.GeneralLinearGroup.coe_mul, hscal]
      rw [hfac, Matrix.diagonal_mul, hoff0, mul_zero]
    exact ⟨Matrix.diag ((T * a * T⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F),
      (Matrix.IsDiag.diagonal_diag hoff).symm⟩
  have hcenter_eq : ∀ A : GL (Fin d) F,
      A ∈ LargeEvenScalars (Fin d) F ↔ A ∈ Subgroup.center (GL (Fin d) F) := by
    intro A
    rw [largeEvenScalars_def, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  let N : Subgroup ↥G := (LargeEvenScalars (Fin d) F).subgroupOf G
  let Q := ↥G ⧸ N
  have hQpow : ∀ y : Q, y ^ p = 1 := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    obtain ⟨b, hb⟩ := htor.2 (a : GL (Fin d) F) a.2
    set s : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) b with sdef
    have hcomm : Commute s (a : GL (Fin d) F) :=
      Matrix.GeneralLinearGroup.scalar_commute b (a : GL (Fin d) F)
    have hsp : s ^ p * (a : GL (Fin d) F) ^ p = 1 := by
      rw [← hcomm.mul_pow]
      exact hb
    have hap : (a : GL (Fin d) F) ^ p = (s⁻¹) ^ p := by
      rw [eq_inv_of_mul_eq_one_right hsp, ← inv_pow]
    rw [hap]
    exact pow_mem (inv_mem (MonoidHom.mem_range.mpr ⟨b, rfl⟩)) p
  have hE : IsElemAbelian p (⊤ : Subgroup Q) := by
    refine ⟨inferInstance, fun x _ => hQpow x⟩
  have hker : ∀ A : ↥G, QuotientGroup.mk' N A = 1 ↔
      (A : GL (Fin d) F) ∈ Subgroup.center (GL (Fin d) F) := by
    intro A
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    exact hcenter_eq A
  have hrange : (QuotientGroup.mk' N : ↥G →* Q).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
    hp hp2 (by rwa [Nat.card_units F]) hd G (QuotientGroup.mk' N) hker
    (⊤ : Subgroup Q) (by rw [hrange]) hE
  have hcard : Nat.card (⊤ : Subgroup Q) = (LargeEvenScalars (Fin d) F).relIndex G := by
    rw [Subgroup.card_top, ← Subgroup.index_eq_card]
    rfl
  rw [hcard] at hbound
  exact ⟨hdiagG, hbound⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
