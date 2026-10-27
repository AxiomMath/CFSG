module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4N1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26C

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_g_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) :
    ∀ m ∈ M3 c.s, c.g * m = m * c.g := by
  intro m hm
  have h := congrArg (· * c.g) (hF.2.2.2.1 hRT m hm)
  simpa [mul_assoc] using h

private lemma y6b_conj_conj (x a : G) :
    (MulAut.conj x) (((MulAut.conj x)⁻¹) a) = a := by
  simp only [MulAut.conj_apply, MulAut.conj_inv_apply]
  group

theorem y6b_E16_le_M3g (c : Ctx5 G L) : y6bE16 c ≤ M3 c.s ⊔ zpowers c.g := by
  show c.s.fr.F ⊔ zpowers c.g ≤ M3 c.s ⊔ zpowers c.g
  exact sup_le ((le_sup_right : c.s.fr.F ≤ M3 c.s).trans le_sup_left) le_sup_right

theorem y6b_M3g_comm (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) :
    IsMulCommutative ↥(M3 c.s ⊔ zpowers c.g) := by
  haveI hM3 : IsMulCommutative ↥(M3 c.s) := y6e_M3_comm c hF
  have hgc := y6b_g_comm_M3 c hF hRT
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure ?_
  intro x hx y hy _
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact setLike_mul_comm hx hy
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcx : Commute c.g x := hgc x hx
    exact hcx.symm.zpow_right n
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcy : Commute c.g y := hgc y hy
    exact hcy.zpow_left n
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow_self c.g m n

theorem y6b_card_M3g (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : Nat.card ↥(M3 c.s ⊔ zpowers c.g) = 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgc := y6b_g_comm_M3 c hF hRT
  have hgH : c.g ∈ c.s.H := c.s.sylow_T.1 (y6b_g_mem_T c hRT)
  have hg_not_M3 : c.g ∉ M3 c.s := by
    intro hgM
    have hmem : c.g ∈ c.s.H ⊓ M3 c.s := ⟨hgH, hgM⟩
    rw [y54_H_inf_M3 c hH] at hmem
    exact y6b_g_not_mem_F c hH hRT hmem
  have hg_ne_one : c.g ≠ 1 := fun h => y6b_g_not_mem_F c hH hRT (h ▸ c.s.fr.F.one_mem)
  have hg2 : c.g ^ 2 = 1 := by rw [pow_two]; exact y6b_g_sq c hRT
  have hord : orderOf c.g = 2 := orderOf_eq_prime hg2 hg_ne_one
  have hgcent : zpowers c.g ≤ Subgroup.centralizer (M3 c.s : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro m hm
    exact (hgc m hm).symm
  have hgnorm : zpowers c.g ≤ normalizer (M3 c.s : Set G) :=
    hgcent.trans (Subgroup.centralizer_le_normalizer (M3 c.s : Set G))
  have hinf : zpowers c.g ⊓ M3 c.s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxg, hxM⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxg
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · have hk' : k % ((2 : ℕ) : ℤ) = 0 := hk
      rw [← zpow_mod_orderOf, hord, hk']; simp
    · have hk' : k % ((2 : ℕ) : ℤ) = 1 := hk
      have h1 : c.g ^ k = c.g := by rw [← zpow_mod_orderOf, hord, hk']; simp
      exact absurd (h1 ▸ hxM) hg_not_M3
  have hprod := y6e_card_sup_mul_inf (H := zpowers c.g) (N := M3 c.s) hgnorm
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hord, y6e_card_M3 c hH, mul_one] at hprod
  rw [sup_comm]
  omega

theorem y6b_not_conj_t (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : ∀ x : G, ∀ e ∈ y6bE16 c, x * c.s.t * x⁻¹ ≠ e := by
  intro x e he hconj
  set B : Subgroup G := M3 c.s ⊔ zpowers c.g with hBdef
  set U : Subgroup G := B.map (((MulAut.conj x)⁻¹).toMonoidHom) with hUdef
  have hBcomm : IsMulCommutative ↥B := by rw [hBdef]; exact y6b_M3g_comm c hF hRT
  have hBcard : Nat.card ↥B = 128 := by rw [hBdef]; exact y6b_card_M3g c hH hF hRT
  have hBp : IsPGroup 2 ↥B := IsPGroup.of_card (n := 7) (by rw [hBcard]; norm_num)
  have heB : e ∈ B := by rw [hBdef]; exact y6b_E16_le_M3g c he
  have hUcard : Nat.card ↥U = 128 := by
    rw [hUdef, Subgroup.card_map_of_injective (K := B) ((MulAut.conj x)⁻¹).injective, hBcard]
  have hUp : IsPGroup 2 ↥U := by
    rw [hUdef]
    exact hBp.map (((MulAut.conj x)⁻¹).toMonoidHom)
  have hUH : U ≤ c.s.H := by
    rw [hUdef]
    intro u hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hu
    have hx_u : (MulAut.conj x) (((MulAut.conj x)⁻¹) b) = b := y6b_conj_conj x b
    have hx_t : (MulAut.conj x) c.s.t = e := by
      rw [MulAut.conj_apply]; exact hconj
    have hcomm : b * e = e * b := setLike_mul_comm hb heB
    have hfin : (((MulAut.conj x)⁻¹) b) * c.s.t * (((MulAut.conj x)⁻¹) b)⁻¹ = c.s.t := by
      apply (MulAut.conj x).injective
      rw [map_mul, map_mul, map_inv, hx_u, hx_t]
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have htu : c.s.t * (((MulAut.conj x)⁻¹) b) = (((MulAut.conj x)⁻¹) b) * c.s.t := by
      have h := congrArg (· * (((MulAut.conj x)⁻¹) b)) hfin
      simpa [mul_assoc] using h.symm
    rw [show c.s.H = Subgroup.centralizer ({c.s.t} : Set G) from rfl]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact htu
  have hUc : IsMulCommutative ↥U := by
    haveI : IsMulCommutative ↥B := hBcomm
    rw [hUdef]
    infer_instance
  have hle := y6b_card_abelian_H_le (s := c.s) (e := c.e) hH hRT hUH hUp hUc
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
