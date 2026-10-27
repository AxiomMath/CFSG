module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DN
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5Cut
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5DK

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem cXU615_le_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) :
    cXU615 T L H ≤ M := by
  classical
  have h := c.hyp
  obtain ⟨z, ⟨hzY, hzJ, hz1, hzs⟩, huniq⟩ := c.toCx615B.existsUnique_ch615
  have hBY := c.borelL_le_normalizer_commutator_ch615 hN
  have hBJ := c.borelL_le_normalizer_thompsonJ_ch615
  have hYUH := commutator_le_UH_ch615 T H
  have hred := conjClosure_isTwoReducedIn_of_charTwo c.toCx615.isSylowTwoOf c.toCx615.charTwo
    (le_rfl : quasithinOmegaOneCenter T ≤ _)
  set Z := quasithinOmegaOneCenter T with hZdef
  set UH := Cx615.UH T H with hUHdef
  set K := oTwoUpper H with hKdef
  set Y := ⁅UH, K⁆ with hYdef
  set X := borelL T L ⊔ H with hXdef
  set C := cXU615 T L H with hCdef
  have hTH : T ≤ H := c.hH.1.1

  have hinv : ∀ g : G, g ∈ Subgroup.normalizer (Y : Set G) →
      g ∈ Subgroup.normalizer (thompsonJ T : Set G) →
      g ∈ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) → g * z * g⁻¹ = z := by
    intro g hgY hgJ hgK
    refine huniq (g * z * g⁻¹) ⟨(Subgroup.mem_normalizer_iff.mp hgY z).mp hzY, ?_,
      fun h1 => hz1 (conj_eq_one_iff.mp h1), fun g' hg' hg'z => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : g⁻¹ * j * g ∈ thompsonJ T := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgJ) j).mp hj
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.mp hzJ _ hj'
      calc j * (g * z * g⁻¹) = g * ((g⁻¹ * j * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * j * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * j := by group
    · have hg'' : g⁻¹ * g' * g ∈ kStar615 T L H := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) g').mp hg'
        rwa [inv_inv] at this
      have hz' : (g⁻¹ * g' * g) * z * (g⁻¹ * g' * g)⁻¹ = z := by
        have e : (g⁻¹ * g' * g) * z * (g⁻¹ * g' * g)⁻¹ =
            g⁻¹ * (g' * (g * z * g⁻¹) * g'⁻¹) * g := by group
        rw [e, hg'z]
        group
      have hcY := hzs _ hg'' hz'
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgY) y).mp hy
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.mp hcY _ hy'
      calc y * g' = g * ((g⁻¹ * y * g) * (g⁻¹ * g' * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * g' * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = g' * y := by group

  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTH.trans
    (le_normalizer_commutator_ch6 (le_normalizer_conjClosure _ _) (le_normalizer_oTwoUpper H))
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hTK : T ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H (hTH ht)
    have h2 : t ∈ Subgroup.normalizer (C : Set G) :=
      le_normalizer_cXU615 (Subgroup.mem_sup_right (hTH ht))
    show t ∈ Subgroup.normalizer ((K ⊔ C : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]

  have hzUH : z ∈ UH := hYUH hzY
  have hUHT : UH ≤ T :=
    hred.1.trans (inf_le_left.trans (F7.isSylowTwoOf_pCoreOf_le c.toCx615.isSylowTwoOf))
  have hz2 : z ^ 2 = 1 := c.hU.2 z hzUH
  have hzT : ∀ t ∈ T, t * z = z * t := fun t ht => by
    have := hinv t (hTY ht) (hTJ ht) (hTK ht)
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [this]
  have hzZ : z ∈ Z :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUHT hzUH, Subgroup.mem_centralizer_iff.mpr hzT, hz2⟩

  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨F, _, _, _, hF, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [c.V_eq]; exact hS.centralizer_le
  have hn2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hodd2 : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by have := h.two_le; omega⟩)
      odd_one
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := Odd.of_dvd_nat hodd2 hpd
  obtain ⟨d, hdD, hdp⟩ := hc.exists_orderOf_eq_ch615 (p := p) hCV c.toCx615.isSylowTwoOf_inf hD
    (by rw [hF]; exact hpd)
  have hdB : d ∈ borelL T L := hD.1 hdD
  have hdodd : Odd (orderOf d) := hdp ▸ hpodd
  have hd1 : d ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hdp
    exact hp.one_lt.ne hdp
  have hdz : d * z * d⁻¹ = z := hinv d (hBY hdB) (hBJ hdB) (hN hdB)
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := c.CZd d hdB hdodd hd1 ⟨hzZ, hzd⟩

  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers z ≠ ⊥ := fun h0 => hz1 (by
    have := Subgroup.mem_zpowers z
    rw [h0] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (fun l hl => mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hzL l hl))
      (fun t ht => mem_normalizer_zpowers_ch615 (hzT t ht))
  have hzU : z ∈ conjClosure Z X := conjClosure_mono le_rfl le_sup_right hzUH
  have hCz : C ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun x hx =>
    mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hx.2 z hzU).symm
  exact hCz.trans (le_of_isUniqueM_of_le_twoLocal (h.isUniqueM_F4 h432) hLT hloc)

end Cx615C

theorem res615D_of_F4 (h432 : Stmt4_3_2_F4) (hDSB : DSBLoc_F4) (hR1 : L2RankOneSylowFact) :
    Res615D_F4 := fun _ _ _ _ _ _ _ _ _ c hN =>
  c.false_of_le_ch615_F4 h432 hDSB hR1 (c.cXU615_le_ch615_F4 h432 hN) hN

end CFSG.Quasithin.H13
