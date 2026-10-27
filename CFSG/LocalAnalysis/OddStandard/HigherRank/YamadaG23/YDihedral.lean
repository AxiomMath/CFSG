module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem d8_check1 : ∀ x y : DihedralGroup 4, x ^ 2 = 1 → y ^ 2 = 1 → x * y ≠ y * x →
    (y * x) ^ 2 ≠ 1 ∧ (y * x) ^ 4 = 1 := by decide

set_option synthInstance.maxSize 400 in
private theorem d8_check2 : ∀ x y w : DihedralGroup 4, x ^ 2 = 1 → y ^ 2 = 1 → x * y ≠ y * x →
    w ^ 2 = 1 → w ≠ 1 → w * x = x * w → w * y = y * w → w = (y * x) ^ 2 := by decide

theorem dihedral_facts {C : Subgroup G} {t d z : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) (ht : orderOf t = 2) (hd : orderOf d = 2)
    (hzC : z ∈ C) (hzt : z * t = t * z) (hzd : z * d = d * z) (hz : orderOf z = 2) :
    orderOf (d * t) = 4 ∧ (d * t) ^ 2 = z := by
  obtain ⟨e⟩ := hD
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have hz2 : z ^ 2 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have htC : t ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hdC : d ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  let T : ↥C := ⟨t, htC⟩
  let Dd : ↥C := ⟨d, hdC⟩
  let W : ↥C := ⟨z, hzC⟩
  have hT2 : T ^ 2 = 1 := by apply Subtype.ext; show t ^ 2 = 1; exact ht2
  have hDd2 : Dd ^ 2 = 1 := by apply Subtype.ext; show d ^ 2 = 1; exact hd2
  have hW2 : W ^ 2 = 1 := by apply Subtype.ext; show z ^ 2 = 1; exact hz2
  have hWne : W ≠ 1 := by
    intro h
    have hz1 : z = 1 := congrArg Subtype.val h
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  have hzT : W * T = T * W := by apply Subtype.ext; show z * t = t * z; exact hzt
  have hzDd : W * Dd = Dd * W := by apply Subtype.ext; show z * d = d * z; exact hzd
  have hTDne : T * Dd ≠ Dd * T := by
    intro hTD
    have hcomm : t * d = d * t := by
      have := congrArg Subtype.val hTD
      simpa [T, Dd] using this
    have hall : ∀ a ∈ ({t, d} : Set G), ∀ b ∈ ({t, d} : Set G), Commute a b := by
      intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · rw [ha, hb]
        · rw [ha, hb]; show t * d = d * t; exact hcomm
      · rcases hb with hb | hb
        · rw [ha, hb]; show d * t = t * d; exact hcomm.symm
        · rw [ha, hb]
    have hpair : ({t, d} : Set G).Pairwise Commute := fun a ha b hb _ => hall a ha b hb
    have hCcomm : IsMulCommutative ↥C := hC.symm ▸ isMulCommutative_closure hpair
    have hD8comm : IsMulCommutative (DihedralGroup 4) := by
      letI := hCcomm
      exact IsMulCommutative.of_comm fun a b => by
        have h := congrArg e (mul_comm' (e.symm a) (e.symm b))
        simpa using h
    exact DihedralGroup.not_commutative (n := 4) (by norm_num) (by norm_num) hD8comm
  have hx2 : (e T) ^ 2 = 1 := by rw [← map_pow e T 2, hT2, map_one e]
  have hy2 : (e Dd) ^ 2 = 1 := by rw [← map_pow e Dd 2, hDd2, map_one e]
  have hw2 : (e W) ^ 2 = 1 := by rw [← map_pow e W 2, hW2, map_one e]
  have hwne : e W ≠ 1 := fun h => hWne (e.injective (by simpa using h))
  have hxyne : e T * e Dd ≠ e Dd * e T := by
    intro h
    apply hTDne
    apply e.injective
    simpa using h
  have hwT : e W * e T = e T * e W := by rw [← map_mul e W T, ← map_mul e T W, hzT]
  have hwDd : e W * e Dd = e Dd * e W := by rw [← map_mul e W Dd, ← map_mul e Dd W, hzDd]
  obtain ⟨hxy2ne, hxy4⟩ := d8_check1 (e T) (e Dd) hx2 hy2 hxyne
  have hC2ne : (Dd * T) ^ 2 ≠ 1 := by
    intro h
    apply hxy2ne
    rw [← map_mul e Dd T, ← map_pow e (Dd * T) 2, h, map_one e]
  have hC4 : (Dd * T) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow e (Dd * T) 4, map_mul e Dd T, map_one e, hxy4]
  have hg2ne : (d * t) ^ 2 ≠ 1 := by
    intro h
    apply hC2ne
    apply Subtype.ext
    show (d * t) ^ 2 = 1
    exact h
  have hg4 : (d * t) ^ 4 = 1 := by
    have := congrArg Subtype.val hC4
    simpa [Dd, T] using this
  have horder : orderOf (d * t) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := d * t)
      (by simpa using hg2ne) (by simpa using hg4)
    rwa [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
  have hWeq : e W = (e Dd * e T) ^ 2 :=
    d8_check2 (e T) (e Dd) (e W) hx2 hy2 hxyne hw2 hwne hwT hwDd
  have hWeq' : W = (Dd * T) ^ 2 := by
    apply e.injective
    rw [map_pow e (Dd * T) 2, map_mul e Dd T]
    exact hWeq
  have hzeq : z = (d * t) ^ 2 := by
    have := congrArg Subtype.val hWeq'
    simpa [W, Dd, T] using this
  exact ⟨horder, hzeq.symm⟩

theorem Ctx5pre.u_facts (c : Ctx5pre G L) (hz : orderOf c.s.fr.z = 2) :
    orderOf (c.d * c.s.t) = 4 ∧ (c.d * c.s.t) ^ 2 = c.s.fr.z := by
  have hbL : c.s.fr.b₁ ∈ L := c.s.lift.2.1.1
  have hzL : c.s.fr.z ∈ L := by
    show c.s.fr.b₁ ^ 2 ∈ L
    exact Subgroup.pow_mem L hbL 2
  have hzt : c.s.fr.z * c.s.t = c.s.t * c.s.fr.z :=
    (Subgroup.mem_centralizer_iff.mp c.s.t_mem) c.s.fr.z hzL
  have hzzt : c.s.fr.z ∈ zt c.s := by
    show c.s.fr.z ∈ closure {c.s.fr.z, c.s.t}
    exact Subgroup.subset_closure (by simp)
  have hzcentT : c.s.fr.z ∈ centIn c.s.T c.s.fr.A := by
    rw [c.intro5.centT]
    exact hzzt
  have hzC0 : c.s.fr.z ∈ C0 c.e := by
    show c.s.fr.z ∈ c.e.T₁ ⊓ centralizer (c.s.fr.A : Set G)
    exact inf_le_inf_right (centralizer (c.s.fr.A : Set G)) c.e.T_le hzcentT
  have hdCentA : c.d ∈ centralizer (c.s.fr.A : Set G) := by
    have h := c.d_mem
    simp only [C0, centIn] at h
    exact h.2
  have hbA : c.s.fr.b₁ ∈ c.s.fr.A := Subgroup.subset_closure (by simp)
  have hzA : c.s.fr.z ∈ c.s.fr.A := by
    show c.s.fr.b₁ ^ 2 ∈ c.s.fr.A
    exact Subgroup.pow_mem c.s.fr.A hbA 2
  have hzd : c.s.fr.z * c.d = c.d * c.s.fr.z :=
    (Subgroup.mem_centralizer_iff.mp hdCentA) c.s.fr.z hzA
  exact dihedral_facts (C := C0 c.e) (t := c.s.t) (d := c.d) (z := c.s.fr.z)
    c.intro5.gen c.intro5.dihedral c.s.t_order c.d_order hzC0 hzt hzd hz

end CFSG.OddStandard.HigherRank.YamadaG23
