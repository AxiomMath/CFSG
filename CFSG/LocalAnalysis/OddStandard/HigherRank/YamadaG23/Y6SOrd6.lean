module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Set5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL110A
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma mem_sup_zpowers_of_le_normalizer {V : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ V ⊔ Subgroup.zpowers g) :
    ∃ v ∈ V, ∃ i : ℤ, x = v * g ^ i := by
  let M : Subgroup G := V ⊔ Subgroup.zpowers g
  have hnorm : M ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (Subgroup.le_normalizer (H := V)) (Subgroup.zpowers_le.mpr hg)
  haveI : (V.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have htop : (⊤ : Subgroup ↥M) =
      (V.subgroupOf M) ⊔ (Subgroup.zpowers g).subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup (show V ≤ M from le_sup_left)
      (show Subgroup.zpowers g ≤ M from le_sup_right), Subgroup.subgroupOf_self]
  have hxM : (⟨x, hx⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := Subgroup.mem_top _
  rw [htop] at hxM
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := V.subgroupOf M)
      (t := (Subgroup.zpowers g).subgroupOf M) (x := (⟨x, hx⟩ : ↥M))).mp hxM
  have hy' : (y : G) ∈ V := hy
  have hz' : (z : G) ∈ Subgroup.zpowers g := hz
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hz'
  refine ⟨(y : G), hy', i, ?_⟩
  rw [hi]
  exact (congrArg Subtype.val hyz).symm

private lemma orderOf_perm3_prod_swap :
    orderOf ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)),
      (Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3))) = 6 := by
  have h3 : orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 :
      Equiv.Perm (Fin 3)) = 3 :=
    orderOf_eq_prime (by ext i; fin_cases i <;> decide) (by
      intro h
      exact absurd (congrArg (fun f : Equiv.Perm (Fin 3) => f 0) h) (by decide))
  have h2 : orderOf (Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3)) = 2 :=
    orderOf_eq_prime (by ext i; fin_cases i <;> decide) (by
      intro h
      exact absurd (congrArg (fun f : Equiv.Perm (Fin 3) => f 0) h) (by decide))
  rw [Prod.orderOf]
  dsimp only
  rw [h3, h2]
  norm_num

theorem y6_exists_order6 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∃ y ∈ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G),
      y ^ 6 ∈ C1 c.e ∧ y ^ 2 ∉ C1 c.e ∧ y ^ 3 ∉ C1 c.e := by
  obtain ⟨hgT, hgR, hacts, hg2, -⟩ := c.g_spec hRT
  set Q : Subgroup G := normIn L c.s.fr.A ⊔ closure {c.g} with hQ
  have h110 : SecProp (normIn L c.s.fr.A ⊔ closure {c.g}) (zL L ⊔ c.s.fr.A)
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
    lf110_1_of hH.hS hH.hZ hH.hOut c.s hg2 hacts
  rw [← hQ] at h110
  rw [f3_zL_eq_bot hH, bot_sup_eq] at h110
  obtain ⟨hn, hne⟩ := h110
  haveI : (c.s.fr.A.subgroupOf Q).Normal := hn
  obtain ⟨e⟩ := hne
  set p : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2, Equiv.swap (0 : Fin 3) 1) with hp_def
  have hp6 : orderOf p = 6 := by simpa [hp_def] using orderOf_perm3_prod_swap
  set q : ↥Q ⧸ (c.s.fr.A.subgroupOf Q) := e.symm p with hq_def
  have hq : orderOf q = 6 := by
    have h := MulEquiv.orderOf_eq e q
    have he : e q = p := by rw [hq_def]; exact e.apply_symm_apply p
    rw [he, hp6] at h
    exact h.symm
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (c.s.fr.A.subgroupOf Q) q
  have hQY : Q ≤ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
    rw [hQ]
    refine sup_le (s5_NLA_le_Y c hH) ?_
    exact (Subgroup.closure_le _).mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact s5_T_le_Y c hH hgT)
  have hQH : Q ≤ c.s.H := by
    rw [hQ]
    refine sup_le ((inf_le_left : normIn L c.s.fr.A ≤ L).trans (s3_L_le_H c.s hH.hS)) ?_
    exact (Subgroup.closure_le _).mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact c.s.sylow_T.1 hgT)
  have hQLg : Q ≤ L ⊔ Subgroup.zpowers c.g := by
    rw [hQ]
    refine sup_le ((inf_le_left : normIn L c.s.fr.A ≤ L).trans le_sup_left) ?_
    rw [← Subgroup.zpowers_eq_closure c.g]
    exact le_sup_right
  have hAQ : c.s.fr.A ≤ Q := by
    rw [hQ]
    exact (le_inf (s3_A_le_L c.s) Subgroup.le_normalizer).trans le_sup_left
  have hnotC1 : ∀ u ∈ Q, u ∉ c.s.fr.A → u ∉ C1 c.e := by
    intro u huQ huA huC1
    have huH : u ∈ c.s.H := hQH huQ
    have huC : u ∈ Subgroup.centralizer ({c.s.t} : Set G) := huH
    have hu : u ∈ c.s.fr.A ⊔ Subgroup.zpowers c.s.t := by
      have h1 : u ∈ C1 c.e ⊓ Subgroup.centralizer ({c.s.t} : Set G) := ⟨huC1, huC⟩
      rw [show C1 c.e = c.s.fr.A ⊔ C0 c.e from rfl, y6_cent_C1_t (c.y6cfg5 hH)] at h1
      exact h1
    have htN : c.s.t ∈ Subgroup.normalizer (c.s.fr.A : Set G) :=
      Subgroup.centralizer_le_normalizer (c.s.fr.A : Set G)
        (Subgroup.mem_centralizer_iff.mpr (fun a ha => s3_comm_t_of_mem_A c.s ha))
    obtain ⟨a, haA, i, hai⟩ := mem_sup_zpowers_of_le_normalizer htN hu
    have ht2 : c.s.t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one c.s.t
      rwa [c.s.t_order] at h
    have hti : c.s.t ^ i = 1 ∨ c.s.t ^ i = c.s.t := by
      have hmod : c.s.t ^ i = c.s.t ^ (i % (2 : ℤ)) :=
        zpow_eq_zpow_emod i (by simpa using ht2)
      rcases Int.emod_two_eq_zero_or_one i with h | h
      · left; rw [hmod, h]; simp
      · right; rw [hmod, h]; simp
    have htQ : c.s.t ∈ Q := by
      rcases hti with h | h
      · exact absurd (by rw [hai, h, mul_one]; exact haA) huA
      · have heq : c.s.t = a⁻¹ * u := by rw [hai, h]; group
        rw [heq]
        exact Subgroup.mul_mem Q (Subgroup.inv_mem Q (hAQ haA)) huQ
    obtain ⟨ℓ, hℓL, j, htj⟩ := mem_sup_zpowers_of_le_normalizer
      (mem_normalizer_of_actsAs L hacts) (hQLg htQ)
    have hgj : c.g ^ j = 1 ∨ c.g ^ j = c.g := by
      have hmod : c.g ^ j = c.g ^ (j % (2 : ℤ)) :=
        zpow_eq_zpow_emod j (by simpa using hg2)
      rcases Int.emod_two_eq_zero_or_one j with h | h
      · left; rw [hmod, h]; simp
      · right; rw [hmod, h]; simp
    rcases hgj with h | h
    · exact s3_t_not_mem_L c.s hH.h31 (by rw [htj, h, mul_one]; exact hℓL)
    · apply s3_not_mem_M c.s hH.hS hgT hgR
      have hgeq : c.g = ℓ⁻¹ * c.s.t := by rw [htj, h]; group
      rw [hgeq]
      exact Subgroup.mul_mem_sup (Subgroup.inv_mem L hℓL)
        (show c.s.t ∈ centIn c.s.H L from
          ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, c.s.t_mem⟩)
  have hq2 : q ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hq] at hd
    exact absurd hd (by decide)
  have hq3 : q ^ 3 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hq] at hd
    exact absurd hd (by decide)
  have hy2A : (y₀ : G) ^ 2 ∉ c.s.fr.A := by
    intro hA
    apply hq2
    have hA' : ((y₀ ^ 2 : ↥Q) : G) ∈ c.s.fr.A := by simpa using hA
    have h1 : QuotientGroup.mk' (c.s.fr.A.subgroupOf Q) (y₀ ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff (N := c.s.fr.A.subgroupOf Q) (y₀ ^ 2)).mpr
        (Subgroup.mem_subgroupOf.mpr hA')
    rw [map_pow, hy₀] at h1
    exact h1
  have hy3A : (y₀ : G) ^ 3 ∉ c.s.fr.A := by
    intro hA
    apply hq3
    have hA' : ((y₀ ^ 3 : ↥Q) : G) ∈ c.s.fr.A := by simpa using hA
    have h1 : QuotientGroup.mk' (c.s.fr.A.subgroupOf Q) (y₀ ^ 3) = 1 :=
      (QuotientGroup.eq_one_iff (N := c.s.fr.A.subgroupOf Q) (y₀ ^ 3)).mpr
        (Subgroup.mem_subgroupOf.mpr hA')
    rw [map_pow, hy₀] at h1
    exact h1
  have hy6A : (y₀ : G) ^ 6 ∈ c.s.fr.A := by
    have hq6 : q ^ 6 = 1 := by
      have h := pow_orderOf_eq_one q
      rwa [hq] at h
    have h1 : QuotientGroup.mk' (c.s.fr.A.subgroupOf Q) (y₀ ^ 6) = 1 := by
      rw [map_pow, hy₀, hq6]
    have h2 : y₀ ^ 6 ∈ c.s.fr.A.subgroupOf Q :=
      (QuotientGroup.eq_one_iff (N := c.s.fr.A.subgroupOf Q) (y₀ ^ 6)).mp h1
    have h3 : ((y₀ ^ 6 : ↥Q) : G) ∈ c.s.fr.A := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  refine ⟨(y₀ : G), hQY y₀.2, ?_, ?_, ?_⟩
  · exact (show c.s.fr.A ≤ C1 c.e from le_sup_left) hy6A
  · exact hnotC1 ((y₀ : G) ^ 2) (Subgroup.pow_mem Q y₀.2 2) hy2A
  · exact hnotC1 ((y₀ : G) ^ 3) (Subgroup.pow_mem Q y₀.2 3) hy3A

end CFSG.OddStandard.HigherRank.YamadaG23
