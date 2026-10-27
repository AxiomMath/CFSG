module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.CentralLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF3
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UReg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP)

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem exists_mem_inf_not_mem_center (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) :
    ∃ y ∈ B ⊓ K, y ^ 5 = 1 ∧ ∃ k ∈ K, y * k ≠ k * y := by
  obtain ⟨-, -, hDcard, -, -, hKcomp, -⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  obtain ⟨m, F, _, hFd, hpm, -, -, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hF
  obtain ⟨ρ, -, hρk, hX, hBX, hnl⟩ := exists_act_nl h θ
  have hXc : Nat.card ρ.range = 5 ^ 2 := by
    have h1 := hBX
    rw [card_eq_of_qsnl h hF, hDcard] at h1
    have h2 : 5 ^ 2 * Nat.card ρ.range = 5 ^ 2 * 5 ^ 2 := by
      rw [← h1]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hXD := SF.le_primeFormD_of_nl hFd (by norm_num) (by norm_num) Nat.prime_five
    (by norm_num) hpm hX hnl
  obtain ⟨r, hr1, hrX⟩ := exists_conj_mem_ne_one hFd hpm hXD hXc
  obtain ⟨hr5, w, hw⟩ := exists_inv_of_conj_mem hFd hpm hX hnl hrX
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥K →* primeFormP hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      ∀ k, φ k = θ (k : ↥K ⧸ Subgroup.center ↥K) :=
    ⟨θ.toMonoidHom.comp (QuotientGroup.mk' _), fun _ => rfl⟩
  have hφs : Function.Surjective φ := fun s => by
    obtain ⟨q, rfl⟩ := θ.surjective s
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨k, hφ k⟩
  have hφk : φ.ker ≤ Subgroup.center ↥K := fun k hk => by
    rwa [MonoidHom.mem_ker, hφ, map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at hk
  obtain ⟨y, hyr, hy5⟩ := exists_lift_pow_eq_one hφs hφk Nat.prime_five (by norm_num) hr5 hw
  have hy5' : (y : Ω) ^ 5 = 1 := by rw [← Subgroup.coe_pow, hy5, Subgroup.coe_one]
  obtain ⟨b, hb⟩ := hrX
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hBN := S171.B_norm_K h.cfg.elem hSN h.cfg.std
  have hc := inv_mul_mem_centralizer_of_mk_eq hperf (Subgroup.le_normalizer y.2) (hBN b.2)
    fun k k₁ k₂ hk₁ hk₂ => by
      have hk : k₁ = y * k * y⁻¹ := Subtype.ext hk₁
      apply θ.injective
      rw [← hρk b k k₂ hk₂, hb, MulAut.conj_apply, ← hyr, hk, hφ, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
  refine ⟨y, ⟨mem_of_inv_mul_mem_centralizer h hF b.2 y.2 hy5' hc, y.2⟩, hy5', ?_⟩
  by_contra hcomm
  push Not at hcomm
  have hyZ : y ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.2 fun k => Subtype.ext (hcomm k k.2).symm
  exact hr1 (by rw [← hyr, hφ, (QuotientGroup.eq_one_iff y).2 hyZ, map_one])

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
