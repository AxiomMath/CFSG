module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4N1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Frat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4A

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_t_ne_one (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.s.t ≠ 1 := by
  intro h
  exact s3_t_not_mem_L (s := c.s) hH.h31 (h ▸ Subgroup.one_mem L)

private lemma y6b_t_ne_g (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.s.t ≠ c.g := by
  have htH : c.s.t ∈ c.s.H := by
    show c.s.t ∈ centralizer ({c.s.t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htMem : c.s.t ∈ L ⊔ centIn c.s.H L :=
    Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨htH, c.s.t_mem⟩)
  intro h
  exact y6b_g_not_mem_M c hH hRT (h ▸ htMem)

private lemma y6b_mem_gt (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) {x : G} :
    x ∈ zpowers c.g ⊔ zpowers c.s.t ↔
      x = 1 ∨ x = c.g ∨ x = c.s.t ∨ x = c.g * c.s.t := by
  have hzz : c.g * c.g = 1 := y6b_g_sq c hRT
  have htt : c.s.t * c.s.t = 1 := y6b_t_sq c
  have hzt : c.s.t * c.g = c.g * c.s.t := (y6b_g_comm_t c hRT).symm
  have hK : zpowers c.g ⊔ zpowers c.s.t = closure ({c.g, c.s.t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure c.g, Subgroup.zpowers_eq_closure c.s.t,
      ← Subgroup.closure_union]
    rfl
  constructor
  · intro hx
    rw [hK] at hx
    refine Subgroup.closure_induction
      (p := fun w _ => w = 1 ∨ w = c.g ∨ w = c.s.t ∨ w = c.g * c.s.t) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro y z _ _ hy hz
      rcases hy with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl
      · left; rw [one_mul]
      · right; left; rw [one_mul]
      · right; right; left; rw [one_mul]
      · right; right; right; rw [one_mul]
      · right; left; rw [mul_one]
      · left; rw [hzz]
      · right; right; right; rfl
      · right; right; left; rw [← mul_assoc, hzz, one_mul]
      · right; right; left; rw [mul_one]
      · right; right; right; rw [hzt]
      · left; rw [htt]
      · right; left; rw [← mul_assoc, hzt, mul_assoc, htt, mul_one]
      · right; right; right; rw [mul_one]
      · right; right; left; rw [mul_assoc, hzt, ← mul_assoc, hzz, one_mul]
      · right; left; rw [mul_assoc, htt, mul_one]
      · left
        calc (c.g * c.s.t) * (c.g * c.s.t) = c.g * ((c.s.t * c.g) * c.s.t) := by group
          _ = c.g * ((c.g * c.s.t) * c.s.t) := by rw [hzt]
          _ = c.g * (c.g * (c.s.t * c.s.t)) := by group
          _ = 1 := by rw [htt, mul_one, hzz]
    · intro y _ hy
      rcases hy with rfl | rfl | rfl | rfl
      · left; rw [inv_one]
      · right; left; rw [inv_eq_of_mul_eq_one_right hzz]
      · right; right; left; rw [inv_eq_of_mul_eq_one_right htt]
      · right; right; right
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right htt, hzt]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c.g)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c.g))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))

private lemma y6b_conj_t_mem (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {n : G}
    (hnC : n ∈ centralizer ({c.g} : Set G))
    (hnN : n ∈ normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G)) :
    n * c.s.t * n⁻¹ = c.s.t ∨ n * c.s.t * n⁻¹ = c.g * c.s.t := by
  have htK : c.s.t ∈ zpowers c.g ⊔ zpowers c.s.t :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  have hmem : n * c.s.t * n⁻¹ ∈ zpowers c.g ⊔ zpowers c.s.t :=
    ((Subgroup.mem_normalizer_iff.mp hnN) c.s.t).mp htK
  rcases (y6b_mem_gt c hRT).mp hmem with h1 | hg | ht | hgt
  · exfalso
    refine y6b_t_ne_one c hH ?_
    calc c.s.t = n⁻¹ * (n * c.s.t * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  · exfalso
    have hcg : n * c.g = c.g * n := Subgroup.mem_centralizer_singleton_iff.mp hnC
    refine y6b_t_ne_g c hH hRT ?_
    calc c.s.t = n⁻¹ * (n * c.s.t * n⁻¹) * n := by group
      _ = n⁻¹ * c.g * n := by rw [hg]
      _ = c.g := by
            calc n⁻¹ * c.g * n = n⁻¹ * (c.g * n) := by group
              _ = n⁻¹ * (n * c.g) := by rw [← hcg]
              _ = c.g := by group
  · exact Or.inl ht
  · exact Or.inr hgt

@[expose] def Y6bHasX1 (c : Ctx5 G L) : Prop :=
  ∃ x ∈ y6bX c, x * c.s.t * x⁻¹ = c.g * c.s.t

theorem y6b_E_sylow_cent_g (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    IsSylowIn 2 (centralizer ({c.g} : Set G) ⊓ c.s.H) (y6bE c) := by
  have hE_H : y6bE c ≤ c.s.H := y6b_E_le_H c hH hRT
  have hgE : c.g ∈ y6bE c := y6b_E16_le_E c (y6b_g_mem_E16 c)
  have hE_C : y6bE c ≤ centralizer ({c.g} : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (y6b_E_comm c hH hRT hx hgE)
  have hE_inf : y6bE c ≤ centralizer ({c.g} : Set G) ⊓ c.s.H := le_inf hE_C hE_H
  let D : Subgroup G := centralizer ({c.g} : Set G) ⊓ c.s.H
  change IsSylowIn 2 D (y6bE c)
  have hD_H : D ≤ c.s.H := inf_le_right
  have hD_C : D ≤ centralizer ({c.g} : Set G) := inf_le_left
  refine ⟨hE_inf, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 5) (by rw [y6b_card_E c hH hRT]; norm_num)
  · intro h2
    have hcard : Nat.card ↥D = (y6bE c).relIndex D * 32 := by
      have h := Subgroup.relIndex_mul_card (H := y6bE c) (K := D)
      rw [inf_eq_left.mpr hE_inf, y6b_card_E c hH hRT] at h
      exact h.symm
    have hdvd : 2 ^ 6 ∣ Nat.card ↥D := by
      rw [hcard]
      have h26 : (2 : ℕ) ^ 6 = 2 * 2 ^ 5 := by norm_num
      rw [h26, show (32 : ℕ) = 2 ^ 5 by norm_num]
      exact Nat.mul_dvd_mul h2 (dvd_refl _)
    obtain ⟨U, hUcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 2 (n := 6) hdvd
    have hUD : U.map D.subtype ≤ D := Subgroup.map_subtype_le U
    have hUH : U.map D.subtype ≤ c.s.H := hUD.trans hD_H
    have hUg : U.map D.subtype ≤ centralizer ({c.g} : Set G) := hUD.trans hD_C
    have hU2 : IsPGroup 2 ↥(U.map D.subtype) := (IsPGroup.of_card hUcard).map D.subtype
    have hcardU : Nat.card ↥(U.map D.subtype) = 64 := by
      rw [Subgroup.card_map_of_injective (f := D.subtype) (K := U) D.subtype_injective, hUcard]
      norm_num
    have hle := y6b_card_cent_g_le c hH hRT hUH hUg hU2
    omega

theorem y6b_centH_le_NC (c : Ctx5 G L) :
    centralizer ({c.g} : Set G) ⊓ c.s.H ≤
      centralizer ({c.g} : Set G) ⊓
        normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
  intro x hx
  refine ⟨hx.1, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  have hxg : (MulAut.conj x) c.g = c.g := by
    have hcomm : x * c.g = c.g * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    rw [MulAut.conj_apply, hcomm]
    group
  have hxt : (MulAut.conj x) c.s.t = c.s.t := by
    have hcomm : x * c.s.t = c.s.t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (show x ∈ centralizer ({c.s.t} : Set G) from hx.2)
    rw [MulAut.conj_apply, hcomm]
    group
  have hxg' : (↑(MulAut.conj x) : G →* G) c.g = c.g := hxg
  have hxt' : (↑(MulAut.conj x) : G →* G) c.s.t = c.s.t := hxt
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hxg', hxt']

theorem y6b_centH_normal (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ((centralizer ({c.g} : Set G) ⊓ c.s.H).subgroupOf
      (centralizer ({c.g} : Set G) ⊓
        normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (y6b_centH_le_NC c)).mpr ?_
  intro h k hh hk
  have hhC : h * c.g = c.g * h := Subgroup.mem_centralizer_singleton_iff.mp hh.1
  have hkC : k * c.g = c.g * k := Subgroup.mem_centralizer_singleton_iff.mp hk.1
  have hhH : h * c.s.t = c.s.t * h :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (show h ∈ centralizer ({c.s.t} : Set G) from hh.2)
  have hconj_g : k⁻¹ * c.g * k = c.g := by
    calc k⁻¹ * c.g * k = k⁻¹ * (c.g * k) := by group
      _ = k⁻¹ * (k * c.g) := by rw [← hkC]
      _ = c.g := by group
  refine ⟨?_, ?_⟩
  · show k * h * k⁻¹ ∈ centralizer ({c.g} : Set G)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (k * h * k⁻¹) * c.g = k * (h * (k⁻¹ * c.g * k)) * k⁻¹ := by group
      _ = k * (h * c.g) * k⁻¹ := by rw [hconj_g]
      _ = k * (c.g * h) * k⁻¹ := by rw [hhC]
      _ = c.g * (k * h * k⁻¹) := by
            calc k * (c.g * h) * k⁻¹ = (k * c.g) * h * k⁻¹ := by group
              _ = (c.g * k) * h * k⁻¹ := by rw [hkC]
              _ = c.g * (k * h * k⁻¹) := by group
  · show k * h * k⁻¹ ∈ centralizer ({c.s.t} : Set G)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hkCinv : k⁻¹ ∈ centralizer ({c.g} : Set G) := Subgroup.inv_mem _ hk.1
    have hkNinv : k⁻¹ ∈ normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hk.2
    have hkconj : k⁻¹ * c.s.t * k = c.s.t ∨ k⁻¹ * c.s.t * k = c.g * c.s.t := by
      simpa using y6b_conj_t_mem c hH hRT hkCinv hkNinv
    have hhconj : h * (k⁻¹ * c.s.t * k) = (k⁻¹ * c.s.t * k) * h := by
      rcases hkconj with h1 | h1
      · rw [h1]; exact hhH
      · rw [h1]
        calc h * (c.g * c.s.t) = (h * c.g) * c.s.t := by group
          _ = (c.g * h) * c.s.t := by rw [hhC]
          _ = c.g * (h * c.s.t) := by group
          _ = c.g * (c.s.t * h) := by rw [hhH]
          _ = (c.g * c.s.t) * h := by group
    calc (k * h * k⁻¹) * c.s.t = k * (h * (k⁻¹ * c.s.t * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * c.s.t * k) * h) * k⁻¹ := by rw [hhconj]
      _ = c.s.t * (k * h * k⁻¹) := by group

theorem y6b_conj_t_of_mem_NC (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {n : G}
    (hnC : n ∈ centralizer ({c.g} : Set G))
    (hnN : n ∈ normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G))
    (hnH : n ∉ c.s.H) : n * c.s.t * n⁻¹ = c.g * c.s.t := by
  rcases y6b_conj_t_mem c hH hRT hnC hnN with h | h
  · exfalso
    apply hnH
    show n ∈ centralizer ({c.s.t} : Set G)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 := congrArg (· * n) h
    simpa [mul_assoc] using h1
  · exact h

theorem y6b_exists_x1 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    (hN : ¬ (centralizer ({c.g} : Set G) ⊓
      normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤ c.s.H)) :
    Y6bHasX1 c := by
  obtain ⟨n, hnNC, hnH⟩ := SetLike.not_le_iff_exists.mp hN
  let NC : Subgroup G := centralizer ({c.g} : Set G) ⊓
    normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G)
  let D : Subgroup G := centralizer ({c.g} : Set G) ⊓ c.s.H
  let A : Subgroup G := normalizer ((y6bE c : Subgroup G) : Set G) ⊓ NC
  have hKN : D ≤ NC := y6b_centH_le_NC c
  have hKn : (D.subgroupOf NC).Normal := y6b_centH_normal c hH hRT
  have hNCnorm : NC ≤ normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn
  have hAD : A ≤ normalizer (D : Set G) := inf_le_right.trans hNCnorm
  have hfr : n ∈ A ⊔ D :=
    y6_frattini (N := NC) (K := D) (C := y6bE c) hKN hKn
      (y6b_E_sylow_cent_g c hH hRT).1 (y6b_E_sylow_cent_g c hH hRT).2.1
      (y6b_E_sylow_cent_g c hH hRT).2.2 hnNC
  have hprod : (↑(A ⊔ D) : Set G) = (A : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A D hAD
  have hmem : n ∈ (A : Set G) * (D : Set G) := by
    rw [← hprod]
    exact hfr
  obtain ⟨x, hxA, d, hdD, hxd⟩ := Set.mem_mul.mp hmem
  refine ⟨x, hxA.1, ?_⟩
  have hdcomm : d * c.s.t = c.s.t * d :=
    Subgroup.mem_centralizer_singleton_iff.mp (show d ∈ centralizer ({c.s.t} : Set G) from hdD.2)
  have hdt : d * c.s.t * d⁻¹ = c.s.t := by
    rw [hdcomm]; group
  have hnconj : n * c.s.t * n⁻¹ = c.g * c.s.t :=
    y6b_conj_t_of_mem_NC c hH hRT hnNC.1 hnNC.2 hnH
  have hxconj : x * c.s.t * x⁻¹ = c.g * c.s.t := by
    have h1 : n * c.s.t * n⁻¹ = x * c.s.t * x⁻¹ := by
      rw [← hxd]
      calc (x * d) * c.s.t * (x * d)⁻¹ = x * (d * c.s.t * d⁻¹) * x⁻¹ := by group
        _ = x * c.s.t * x⁻¹ := by rw [hdt]
    exact h1.symm.trans hnconj
  exact hxconj

end CFSG.OddStandard.HigherRank.YamadaG23
