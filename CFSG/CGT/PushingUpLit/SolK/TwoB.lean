module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.SolK.RSmall
public import CFSG.CGT.PushingUpLit.SolK.SwapVec

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem card_Q_le_two_mul_cent (hR : RSmall S) {t : G} (htM : t ∈ M) {i j : Fin (2 * n + 1)}
    (hij : i ≠ j) (hθ : S.θ ⟨t, htM⟩ = swap i j) :
    Nat.card ↥(pCoreOf 2 M) ≤
      2 * Nat.card ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G)) := by
  classical
  have h1 := card_le_two_mul_fix_swap (d := 2 * n + 1) hij
  have hfix : ∀ v : {v : ↥(coreMod (2 * n + 1)) // coreAct (2 * n + 1) (swap i j) v = v},
      t * ((S.D.β.symm v.1 : ↥S.D.W) : G) * t⁻¹ = ((S.D.β.symm v.1 : ↥S.D.W) : G) := by
    intro v
    have hW : t * ((S.D.β.symm v.1 : ↥S.D.W) : G) * t⁻¹ ∈ S.D.W :=
      S.W_normalized htM (S.D.β.symm v.1).2
    have h2 := S.θ_spec ⟨t, htM⟩ (S.D.β.symm v.1) hW
    rw [hθ, MulEquiv.apply_symm_apply, v.2] at h2
    have h3 : (⟨t * ((S.D.β.symm v.1 : ↥S.D.W) : G) * t⁻¹, hW⟩ : ↥S.D.W) = S.D.β.symm v.1 :=
      S.D.β.injective (h2.trans (MulEquiv.apply_symm_apply _ _).symm)
    exact congrArg Subtype.val h3
  let f : {v : ↥(coreMod (2 * n + 1)) // coreAct (2 * n + 1) (swap i j) v = v} →
      {g : ↥S.D.W // t * (g : G) * t⁻¹ = (g : G)} := fun v => ⟨S.D.β.symm v.1, hfix v⟩
  have hf : Function.Injective f := by
    intro v v' h
    have := S.D.β.symm.injective (congrArg Subtype.val h)
    exact Subtype.ext this
  have h2 := Nat.card_le_card_of_injective f hf
  let hmap : {g : ↥S.D.W // t * (g : G) * t⁻¹ = (g : G)} × ↥(rOf M X) →
      ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G)) := fun p =>
    ⟨(p.1.1 : G) * p.2, Subgroup.mem_inf.2
      ⟨(pCoreOf 2 M).mul_mem (S.W_le_Q p.1.1.2) p.2.2.1,
        Subgroup.mem_centralizer_singleton_iff.2 (by
          have hr := SolCfg.RSmall.central S hR htM p.2.2
          have hc : t * ((p.1.1 : G) * p.2) * t⁻¹ = (p.1.1 : G) * p.2 :=
            calc t * ((p.1.1 : G) * p.2) * t⁻¹ = (t * (p.1.1 : G) * t⁻¹) * (t * p.2 * t⁻¹) := by
                  group
              _ = (p.1.1 : G) * p.2 := by rw [p.1.2, hr]
          calc ((p.1.1 : G) * p.2) * t = (t * ((p.1.1 : G) * p.2) * t⁻¹) * t := by rw [hc]
            _ = t * ((p.1.1 : G) * p.2) := by group)⟩⟩
  have hmapinj : Function.Injective hmap := by
    intro p p' h
    have h1' : (p.1.1 : G) * p.2 = (p'.1.1 : G) * p'.2 := congrArg Subtype.val h
    obtain ⟨hg, hr⟩ := S.decomp_unique p.1.1.2 p'.1.1.2 p.2.2 p'.2.2 h1'
    exact Prod.ext (Subtype.ext (Subtype.ext hg)) (Subtype.ext hr)
  have h3 := Nat.card_le_card_of_injective hmap hmapinj
  rw [Nat.card_prod] at h3
  have hcardQ := S.card_Q
  have hW : Nat.card ↥S.D.W = Nat.card ↥(coreMod (2 * n + 1)) := Nat.card_congr S.D.β.toEquiv
  rw [hcardQ, hW]
  calc Nat.card ↥(coreMod (2 * n + 1)) * Nat.card ↥(rOf M X)
      ≤ (2 * Nat.card {v : ↥(coreMod (2 * n + 1)) // coreAct (2 * n + 1) (swap i j) v = v}) *
        Nat.card ↥(rOf M X) := Nat.mul_le_mul_right _ h1
    _ ≤ (2 * Nat.card {g : ↥S.D.W // t * (g : G) * t⁻¹ = (g : G)}) * Nat.card ↥(rOf M X) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
    _ = 2 * (Nat.card {g : ↥S.D.W // t * (g : G) * t⁻¹ = (g : G)} * Nat.card ↥(rOf M X)) :=
        by ring
    _ ≤ 2 * Nat.card ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G)) :=
        Nat.mul_le_mul_left _ h3

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
