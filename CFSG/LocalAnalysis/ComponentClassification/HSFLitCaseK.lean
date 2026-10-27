module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitCaseKModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv GorensteinWalter

theorem R8K_le_R8KP : R8K ≤ R8KP :=
  sup_le R8_le_R8KP (zpowers_le.mpr k8_mem_R8KP)

namespace L2Data

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : L2Data t L)

@[expose] def psi7 (C : A.CaseK) {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) :
    A.T →* Perm (Fin 7) where
  toFun g := phiK s r (A.ψ g)
  map_one' := by rw [map_one]; exact phiK_one s r
  map_mul' g h := by
    rw [map_mul]
    exact phiK_mul r hs (R8K_le_R8KP (C.range_le g)) (R8K_le_R8KP (C.range_le h))

omit [Finite X] in
theorem psi7_apply (C : A.CaseK) {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) (g : A.T) :
    A.psi7 C r hs g = phiK s r (A.ψ g) := rfl

omit [Finite X] in
theorem psi7_eq_one_iff (C : A.CaseK) {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) (g : A.T) :
    A.psi7 C r hs g = 1 ↔ A.ψ g = 1 := by
  rw [psi7_apply, phiK_eq_one r hs (R8K_le_R8KP (C.range_le g))]

theorem eq_of_psi7_eq (C : A.CaseK) {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) {g h : X}
    (hg : g ∈ A.R) (hh : h ∈ A.R) (he : A.psi7 C r hs ⟨g, hg.1⟩ = A.psi7 C r hs ⟨h, hh.1⟩) :
    g = h := by
  refine A.eq_of_ψ_eq hg hh ?_
  have h1 : A.psi7 C r hs ((⟨g, hg.1⟩ : A.T)⁻¹ * ⟨h, hh.1⟩) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [psi7_eq_one_iff, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem exists_psi7_eq (C : A.CaseK) {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3)
    {σ : Perm (Fin 7)} (hσ : σ ∈ R0) : ∃ g : A.T, (g : X) ∈ L ∧ A.psi7 C r hs g = σ := by
  let f : A.R → R0 := fun g =>
    ⟨A.psi7 C r hs ⟨g, g.2.1⟩, phiK_mem_R0 s r (A.ψ_mem_R8 ⟨g, g.2.1⟩ g.2.2)⟩
  have hinj : Function.Injective f := fun g h he =>
    Subtype.ext (A.eq_of_psi7_eq C r hs g.2 h.2 (congrArg Subtype.val he))
  obtain ⟨g, hg⟩ := (hinj.bijective_of_nat_card_le (by rw [card_R0, A.card_R])).2 ⟨σ, hσ⟩
  exact ⟨⟨g, g.2.1⟩, g.2.2, congrArg Subtype.val hg⟩

@[expose] def toA7Data (C : A.CaseK) {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) :
    A7Data t L where
  config := A.config
  syl := A.syl
  ψ := A.psi7 C r hs
  ψ_eq_one_iff g := by rw [psi7_eq_one_iff]; exact A.ψ_eq_one_iff g
  ψ_mem_alternatingGroup g hg := (phiK_mem_R0 s r (A.ψ_mem_R8 g hg)).2
  ψ_mem_P0 g := phiK_mem_P0 s r _
  exists_ψ_eq _ hσ := A.exists_psi7_eq C r hs hσ

theorem exists_a7Base (hKF : FritzL2KFacts) {F : Type} [Field F] [Finite F]
    (he : Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 F)) (C : A.CaseK) : Nonempty (A7Base X) := by
  obtain ⟨x, y, hx, hy, -, hyx, hox, hd1, hd2, hk1, hk2, hnc, hcz⟩ := hKF X t L F he A C
  have hx2 : A.ψ ⟨x, hx.1⟩ * A.ψ ⟨x, hx.1⟩ ≠ 1 := by
    intro h
    have hxx : x * x ∈ A.R := mul_mem hx hx
    have h1 : x * x = 1 := by
      refine A.eq_of_ψ_eq hxx (one_mem _) ?_
      rw [show (⟨x * x, hxx.1⟩ : A.T) = ⟨x, hx.1⟩ * ⟨x, hx.1⟩ from rfl, map_mul, h]
      exact (map_one A.ψ).symm
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h1])
    rw [hox] at h2
    exact absurd h2 (by decide)
  have hyx' : A.ψ ⟨y, hy.1⟩ * A.ψ ⟨x, hx.1⟩ = (A.ψ ⟨x, hx.1⟩)⁻¹ * A.ψ ⟨y, hy.1⟩ := by
    have h2 : (⟨y, hy.1⟩ : A.T) * ⟨x, hx.1⟩ = (⟨x, hx.1⟩ : A.T)⁻¹ * ⟨y, hy.1⟩ :=
      Subtype.ext (by
        change y * x = x⁻¹ * y
        rw [← hyx]
        group)
    rw [← map_mul, ← map_inv, ← map_mul, h2]
  obtain ⟨s, r, hs, hsx, hry⟩ := exists_pair_param (A.ψ_mem_R8' hx) (A.ψ_mem_R8' hy) hx2 hyx'
  have hxR : (A.toA7Data C r hs).xR = x := by
    change Classical.choose ((A.toA7Data C r hs).exists_mem_R_ψ_eq rho0_mem_R0) = x
    obtain ⟨h1, h2⟩ := Classical.choose_spec ((A.toA7Data C r hs).exists_mem_R_ψ_eq rho0_mem_R0)
    refine (A.toA7Data C r hs).eq_of_ψ_eq h1 hx ?_
    rw [h2]
    change rho0 = phiK s r (A.ψ ⟨x, hx.1⟩)
    rw [hsx, phiK_x r hs]
  have hyR : (A.toA7Data C r hs).yR = y := by
    change Classical.choose ((A.toA7Data C r hs).exists_mem_R_ψ_eq c0_b0_mem_R0) = y
    obtain ⟨h1, h2⟩ := Classical.choose_spec ((A.toA7Data C r hs).exists_mem_R_ψ_eq c0_b0_mem_R0)
    refine (A.toA7Data C r hs).eq_of_ψ_eq h1 hy ?_
    rw [h2]
    change c0 * b0 = phiK s r (A.ψ ⟨y, hy.1⟩)
    rw [hry, phiK_y r hs]
  subst hxR hyR
  exact ⟨{ t := t
           L := L
           data := A.toA7Data C r hs
           card_K := C.card_K
           k := C.k
           k_mem := C.k_mem
           k_sq := C.k_sq
           ψ_k := by
             change phiK s r (A.ψ ⟨C.k, C.k_mem⟩) = c0
             rw [C.ψ_k, phiK_k8 r hs]
           facts := Or.inl
             { d_xy := hd1
               d_y := hd2
               k_fixed := fun hn => hk1 _ hn
               zk_fixed := fun hn => hk2 _ hn
               not_conj := fun hg hE => hnc _ hg hE
               card_conj_z := hcz } }⟩

end L2Data

theorem fritzL2CaseK : FritzL2CaseK := by
  intro h48 hH X _ _ _ hnonab hnot t L F _ _ he A C
  obtain ⟨S⟩ := A.exists_a7Base fritzL2KFacts he C
  exact hnot (h48 hH X hnonab S)

end CFSG.ComponentClassification.HSFLit
