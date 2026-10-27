module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCover
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelCov

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU)
open CFSG.LocalAnalysis.RankThreeUC.S15.ACore (Mon monT monS monEmb monEmb_apply monEmb_monT
  monEmb_monS monPermGL_conj_diagHom monDet_monT monDet_monS)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L (sig5 sig5_symm_apply)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M (monSub mem_monSub monT_mem_PmC
  monS_mem_PmC pow_five_monSub det_monEmb_monSub diagHom_mem_primeFormUnitary
  monPermGL_mem_primeFormUnitary)
open CFSG.RankThree.Classical2 (exists_orderOf_eq_norm_one)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)

section Model

variable {m : ℕ} {F : Type} [Field F]

private theorem exists_exponent_five_of_dvd (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1) :
    ∃ P : Subgroup (gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)),
      (∀ g ∈ P, g ^ 5 = 1) ∧ ∃ a ∈ P, ∃ b ∈ P, ∀ c : Fˣ,
        ((b * a * b⁻¹ * a⁻¹ : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :
          GL (Fin 5) F) ≠ GeneralLinearGroup.scalar (Fin 5) c := by
  haveI := hF.finite
  obtain ⟨ζ, hζ, -⟩ := exists_orderOf_eq_norm_one hF Nat.prime_five h5
  have hCcard : Nat.card (Subgroup.zpowers ζ) = 5 ^ 1 := by rw [Nat.card_zpowers, hζ, pow_one]
  have hC5 : ∀ u : Subgroup.zpowers ζ, u ^ 5 = 1 := fun u => by
    have h1 : u ^ Nat.card (Subgroup.zpowers ζ) = 1 := pow_card_eq_one'
    rwa [hCcard, pow_one] at h1
  have hnorm : ∀ u : Subgroup.zpowers ζ,
      hF.norm (((Subgroup.zpowers ζ).subtype u : Fˣ) : F) = 1 := fun u => by
    have h1 : (u : Fˣ) ^ 5 = 1 := by rw [← Subgroup.coe_pow, hC5 u, Subgroup.coe_one]
    obtain ⟨k, hk⟩ := h5
    change ((u : Fˣ) : F) * hF.bar ((u : Fˣ) : F) = 1
    rw [hF.bar_apply, ← pow_succ', hk, pow_mul, ← Units.val_pow_eq_pow_val, h1, Units.val_one,
      one_pow]
  have hmem : ∀ y : monSub (Subgroup.zpowers ζ),
      monEmb (Subgroup.zpowers ζ).subtype 5 (y : Mon (Subgroup.zpowers ζ) 5) ∈
        gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := fun y => by
    refine ⟨?_, det_monEmb_monSub hCcard _ y⟩
    rw [monEmb_apply]
    exact mul_mem (diagHom_mem_primeFormUnitary hF fun i => hnorm _)
      (monPermGL_mem_primeFormUnitary hF _)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : monSub (Subgroup.zpowers ζ) →*
      gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      ∀ y, (ψ y : GL (Fin 5) F) =
        monEmb (Subgroup.zpowers ζ).subtype 5 (y : Mon (Subgroup.zpowers ζ) 5) :=
    ⟨((monEmb (Subgroup.zpowers ζ).subtype 5).comp
      (monSub (Subgroup.zpowers ζ)).subtype).codRestrict _ hmem, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Subgroup.zpowers ζ, (c : Fˣ) = ζ :=
    ⟨⟨ζ, Subgroup.mem_zpowers ζ⟩, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : monSub (Subgroup.zpowers ζ),
      (a : Mon (Subgroup.zpowers ζ) 5) = monT ![c, c⁻¹, 1, 1, 1] :=
    ⟨⟨monT ![c, c⁻¹, 1, 1, 1], mem_monSub.2 ⟨monT_mem_PmC _, by
      rw [monDet_monT]
      simp [Fin.prod_univ_five]⟩⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : monSub (Subgroup.zpowers ζ),
      (b : Mon (Subgroup.zpowers ζ) 5) = monS sig5 :=
    ⟨⟨monS sig5, mem_monSub.2 ⟨monS_mem_PmC, monDet_monS _⟩⟩, rfl⟩
  have hdiag : ∀ s : Fˣ, diagHom 5 (fun _ => s) = GeneralLinearGroup.scalar (Fin 5) s :=
    fun s => Units.ext (by rw [coe_diagHom, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply])
  refine ⟨ψ.range, ?_, ψ a, ⟨a, rfl⟩, ψ b, ⟨b, rfl⟩, fun s hs => ?_⟩
  · rintro _ ⟨y, rfl⟩
    have hy : y ^ 5 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_five_monSub hC5 y.2)
    rw [← map_pow, hy, map_one]
  ·
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      hψ, hψ, ha, hb, monEmb_monS, monEmb_monT, monPermGL_conj_diagHom, ← map_inv (diagHom 5),
      ← map_mul (diagHom 5), ← hdiag] at hs
    have hτ := diagHom_injective 5 hs
    have e3 : (Subgroup.zpowers ζ).subtype (![c, c⁻¹, 1, 1, 1] (sig5.symm 3)) *
        ((Subgroup.zpowers ζ).subtype (![c, c⁻¹, 1, 1, 1] 3))⁻¹ = s := congrFun hτ 3
    have e1 : (Subgroup.zpowers ζ).subtype (![c, c⁻¹, 1, 1, 1] (sig5.symm 1)) *
        ((Subgroup.zpowers ζ).subtype (![c, c⁻¹, 1, 1, 1] 1))⁻¹ = s := congrFun hτ 1
    rw [sig5_symm_apply] at e3
    rw [sig5_symm_apply] at e1
    change (Subgroup.zpowers ζ).subtype 1 * ((Subgroup.zpowers ζ).subtype 1)⁻¹ = s at e3
    change (Subgroup.zpowers ζ).subtype c * ((Subgroup.zpowers ζ).subtype c⁻¹)⁻¹ = s at e1
    rw [map_one, inv_one, mul_one] at e3
    rw [map_inv, inv_inv, ← e3] at e1
    change (c : Fˣ) * (c : Fˣ) = 1 at e1
    rw [hc, ← sq] at e1
    have h2 := orderOf_dvd_of_pow_eq_one e1
    rw [hζ] at h2
    norm_num at h2

end Model

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem exists_nonabelian_exponent_five_le (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) :
    ∃ H : Subgroup Ω, H ≤ K ∧ (∀ g ∈ H, g ^ 5 = 1) ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  obtain ⟨m, F, _, hFd, hpm, -, -, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hF
  obtain ⟨α, -, hα, -⟩ := exists_su5_cover hFd hperf θ
  obtain ⟨P, hP5, a, ha, b, hb, hab⟩ := exists_exponent_five_of_dvd hFd hpm
  have hker : ∀ g, α g = 1 → ∃ c : Fˣ,
      (g : GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c := fun g hg => by
    have h1 := hα g
    rw [hg, QuotientGroup.mk_one, map_one] at h1
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff g).1 h1.symm
    exact ⟨c, hc⟩
  refine ⟨P.map (K.subtype.comp α), ?_, ?_, _, Subgroup.mem_map_of_mem _ ha, _,
    Subgroup.mem_map_of_mem _ hb, fun h1 => ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact (α g).2
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hP5 g hg, map_one]
  · have h2 : α a * α b = α b * α a := Subtype.ext h1
    obtain ⟨c, hc⟩ := hker (b * a * b⁻¹ * a⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2, mul_inv_cancel_right,
        mul_inv_cancel])
    exact hab c hc

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
