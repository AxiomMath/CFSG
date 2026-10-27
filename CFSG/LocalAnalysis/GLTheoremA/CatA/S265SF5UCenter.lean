module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCover
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5ULift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UPair

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP primeFormConjHom
  primeFormConjSU)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU)

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem center_eq_bot_of_qsnl (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) : Subgroup.center ↥K = ⊥ := by
  obtain ⟨-, -, hDcard, -, -, hKcomp, hDK⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  obtain ⟨m, F, _, hFd, hpm, -, -, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hF
  obtain ⟨ρ, hρ1, hρk, hX, hBX, hnl⟩ := exists_act_nl h θ
  have hXc : Nat.card ρ.range = 5 ^ 2 := by
    have h1 := hBX
    rw [card_eq_of_qsnl h hF, hDcard] at h1
    have h2 : 5 ^ 2 * Nat.card ρ.range = 5 ^ 2 * 5 ^ 2 := by
      rw [← h1]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hXD := SF.le_primeFormD_of_nl hFd (by norm_num) (by norm_num) Nat.prime_five
    (by norm_num) hpm hX hnl
  obtain ⟨α, hαs, hα, hαZ⟩ := exists_su5_cover hFd hperf θ
  obtain ⟨y, ⟨hyB, hyK⟩, -, k₀, hk₀, hyk₀⟩ := exists_mem_inf_not_mem_center h hF
  obtain ⟨g₀, hg₀⟩ := hαs ⟨y, hyK⟩
  have hρy : ρ ⟨y, hyB⟩ =
      MulAut.conj (g₀ : primeFormP hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) := by
    rw [eq_mulAut_conj_of_act θ hyK (hρk ⟨y, hyB⟩), ← hg₀, hα]
  have hg₀1 : MulAut.conj (g₀ : primeFormP hFd ((1 : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F)) ≠ 1 := by
    rw [← hρy]
    intro h1
    have hyD := (hρ1 ⟨y, hyB⟩).1 h1
    rw [hDK] at hyD
    exact hyk₀ (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyD).2 k₀ hk₀).symm
  obtain ⟨A, ⟨b, hb⟩, c, hc5, hc1, hAgA⟩ := exists_conj_eq_scalar_mul_ne_one hFd hpm hXD hX hnl
    hXc (S := g₀) ⟨⟨y, hyB⟩, hρy⟩ hg₀1
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hBN := S171.B_norm_K h.cfg.elem hSN h.cfg.std
  have hbA : ∀ k k' : ↥K, (k' : Ω) = (b : Ω) * k * (b : Ω)⁻¹ →
      θ (k' : ↥K ⧸ Subgroup.center ↥K) =
        primeFormConjHom hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A
          (θ (k : ↥K ⧸ Subgroup.center ↥K)) :=
    fun k k' hk => by rw [← hb, hρk b k k' hk]
  have hαA : α (primeFormConjSU hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A g₀) =
      α g₀ := by
    refine Subtype.ext ?_
    rw [← conj_apply_eq_of_cover hFd θ hα (hBN b.2) hbA g₀, hg₀]
    change (b : Ω) * y * (b : Ω)⁻¹ = y
    rw [h.cfg.elem.comm b.2 hyB, mul_inv_cancel_right]
  obtain ⟨z, hαz, hzc⟩ : ∃ z : gramSU hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      α z = 1 ∧ (z : GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c := by
    refine ⟨primeFormConjSU hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A g₀ * g₀⁻¹,
      by rw [map_mul, map_inv, hαA, mul_inv_cancel], ?_⟩
    change (A : GL (Fin 5) F) * g₀ * (A : GL (Fin 5) F)⁻¹ * (g₀ : GL (Fin 5) F)⁻¹ = _
    rw [hAgA, mul_inv_cancel_right]
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hprim : IsPrimitiveRoot c 5 := by
    have h1 := IsPrimitiveRoot.orderOf c
    rwa [orderOf_eq_prime hc5 hc1] at h1
  rw [← hαZ, Subgroup.map_eq_bot_iff]
  rintro w ⟨d, -, hd5, hw⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 5 d).2 hd5)
  have hwz : w = z ^ i := Subtype.ext (by rw [hw, Subgroup.coe_pow, hzc, ← hi, map_pow])
  rw [MonoidHom.mem_ker, hwz, map_pow, hαz, one_pow]

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
