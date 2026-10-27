module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615

variable (c : Cx615 G T M L V H n)
include c

theorem nat_F4 (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) : IsNatQuotCh5 L V n := by
  have h := c.hyp
  have hJ : ⁅L, thompsonJ T⁆ = L :=
    (h5172 G T M L V H n h.toHyp5_0_1 h.module c.hH c.commutator_ne).1.symm
  have hL : ⁅L, L⁆ = L := h.toHyp5_0_1.commutator_eq
  have hT : IsPGroup 2 T := h.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  rcases h512 G T M L V n h.toHyp5_0_1 h.module with ⟨hJV, -⟩ | ⟨-, h2⟩ | ⟨-, h3n, -, -, h3⟩
  · exfalso
    apply h.module.2.2
    have hJO : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← h.centralizer_eq]
      exact le_inf (GammaExtra.thompsonJ_le fun A hA => hA.1) (hJV.trans inf_le_right)
    have hLO : L ≤ pCoreOf 2 (L ⊔ T) := by
      have h1 : ⁅L, thompsonJ T⁆ ≤ pCoreOf 2 (L ⊔ T) :=
        (Subgroup.commutator_mono le_rfl hJO).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp
            (le_sup_left.trans (le_normalizer_pCoreOf 2 (L ⊔ T))))
      rwa [hJ] at h1
    have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
      rw [← h.centralizer_eq] at hLO
      exact hLO.trans inf_le_right
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC
  · exact h2
  · exact absurd ⟨h3n, isA5ModuleSum_of_s5 (Or.inl h3) hL hT hTL⟩ h.not_a5

theorem exists_z_F4 (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) :
    ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅V, L⁆, z ∉ Subgroup.centralizer (L : Set G) := by
  have h := c.hyp
  obtain ⟨hVel, hLTV, hVT⟩ := c.V_facts
  have hnat := (c.nat_F4 h512 h5172).commutator
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hLW : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_ch6 hLV Subgroup.le_normalizer

  have hne : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    obtain ⟨K, _, _, -, π, Y, -, hYs, hYk, -⟩ := hnat.exists_coord
    obtain ⟨x, hx⟩ := hYs (Multiplicative.ofAdd ![1, 0])
    intro h0
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
    have h1 := (hYk x).mpr (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (h0 x.2) l hl))
    rw [hx] at h1
    have h2 := congrArg (fun y : Multiplicative (Fin 2 → K) => Multiplicative.toAdd y 0) h1
    simp at h2
  have hCL : L ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ T :=
    (h.toHyp5_0_1.inf_centralizer_le hLW hne).trans
      ((F7.isSylowTwoOf_pCoreOf_le c.isSylowTwoOf_inf).trans inf_le_left)
  obtain ⟨z, hzW, hzT, hzL⟩ := hnat.exists_fixed_ch6 h.two_le
    (fun v hv => hVel.2 v (hWV hv)) h.sylow.1 hTL (le_normalizer_commutator_ch6 hTV hTL)
    (hWV.trans hVT) c.isSylowTwoOf_inf hCL
  refine ⟨z, ⟨Subgroup.subset_closure ⟨⟨hVT (hWV hzW), hzT⟩, hVel.2 z (hWV hzW)⟩, hzW⟩, hzL⟩

theorem CZd_F4 (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) :
    ∀ d ∈ borelL T L, Odd (orderOf d) → d ≠ 1 →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer ({d} : Set G) ≤
        Subgroup.centralizer (L : Set G) := by
  intro d hd hodd hd1 z hz
  have hdV : d ∉ Subgroup.centralizer (V : Set G) := by
    intro hdV
    have hdO : d ∈ pCoreOf 2 L :=
      c.hyp.toHyp5_0_1.inf_centralizer_le (le_sup_left.trans c.V_facts.2.1) c.hyp.module.2.2
        ⟨hd.1, hdV⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨d, hdO⟩
    exact hd1 (eq_one_of_odd_of_pow_ch615 hodd (by simpa using congrArg Subtype.val hk))
  have hdz : d * z * d⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hz.2 d rfl, mul_inv_cancel_right]
  exact (c.nat_F4 h512 h5172).mem_centralizer_of_odd_ch6 c.isSylowTwoOf_inf hd.1 hodd hdV
    (c.ZV hz.1) hdz

theorem CMZ_F4 (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) :
    M ⊓ Subgroup.centralizer ((quasithinOmegaOneCenter T ⊓ ⁅V, L⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨z, hz, hzL⟩ := c.exists_z_F4 h512 h5172
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  have hzT := hZT hz.1
  have hzS : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) hzT
  intro y hy
  apply mem_normalizer_of_conj_mem_ch6
  intro t ht
  have hl : y * t * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (c.hyp.normal hy.1) t).mp ht.2
  have hzy : z * y = y * z := Subgroup.mem_centralizer_iff.mp hy.2 z hz
  have e1 : y⁻¹ * z * y = z := by
    rw [mul_assoc, hzy, inv_mul_cancel_left]
  have e2 : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzT t ht.1, mul_inv_cancel_right]
  have e3 : y * z * y⁻¹ = z := by
    rw [← hzy, mul_inv_cancel_right]
  have hfix : y * t * y⁻¹ * z * (y * t * y⁻¹)⁻¹ = z := by
    calc y * t * y⁻¹ * z * (y * t * y⁻¹)⁻¹ = y * (t * (y⁻¹ * z * y) * t⁻¹) * y⁻¹ := by group
      _ = z := by rw [e1, e2, e3]
  exact (c.nat_F4 h512 h5172).mem_of_fixed_ch6 c.isSylowTwoOf_inf c.inf_centralizer_le_inf
    (c.ZV hz.1) hzS hzL hl hfix

theorem X_O2_F4 (h5172 : Stmt5_1_7_two_F4) : pCoreOf 2 (borelL T L ⊔ H) ≠ ⊥ := by
  have h := c.hyp
  rcases (h5172 G T M L V H n h.toHyp5_0_1 h.module c.hH c.commutator_ne).2.2 with
    h1 | ⟨h5S, h5, -⟩
  · exact h1
  · exact absurd ⟨h.toHyp5_0_1.n_eq_two_of_isBarS5 h.module h5S,
      isA5ModuleSum_of_s5 (Or.inl h5) h.toHyp5_0_1.commutator_eq h.sylow.1
        (h.T_le.trans h.normal)⟩ h.not_a5

theorem faithful_F4 (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) :
    (borelL T L ⊔ T) ⊓ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) : Set G) ≤ T := by
  classical
  have h := c.hyp
  set B := borelL T L with hBdef
  set U := conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) with hUdef
  obtain ⟨z, hz, hzL⟩ := c.exists_z_F4 h512 h5172
  have hzU : z ∈ U := le_conjClosure _ _ hz.1
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := h.toHyp5_0_1.T_le_normalizer_borel
  have hTH : T ≤ H := c.hH.1.1

  have hBTU : B ⊔ T ≤ Subgroup.normalizer (U : Set G) :=
    (sup_le_sup_left hTH B).trans (le_normalizer_conjClosure _ _)
  have hBTC : B ⊔ T ≤ Subgroup.normalizer
      (Subgroup.centralizer (U : Set G) : Set G) := le_normalizer_centralizer_ch6 hBTU

  have hodd1 : ∀ y ∈ (B ⊔ T) ⊓ Subgroup.centralizer (U : Set G), Odd (orderOf y) → y = 1 := by
    intro y hy hodd

    have hyB : y ∈ B := by
      have hy' : y ∈ ((B ⊔ T : Subgroup G) : Set G) := hy.1
      rw [Subgroup.coe_mul_of_right_le_normalizer_left B T hTB] at hy'
      obtain ⟨b, hb, t, ht, rfl⟩ := Set.mem_mul.mp hy'
      obtain ⟨e, he⟩ := h.sylow.1 ⟨t, ht⟩
      have ht2 : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
      obtain ⟨b', hb', hpow⟩ := pow_mul_mem_of_mem_normalizer hb (hTB ht) (2 ^ e)
      rw [ht2, mul_one] at hpow
      have hco : Nat.Coprime (2 ^ e) (orderOf (b * t)) :=
        Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
      obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hco
      rw [← hk, hpow]
      exact Subgroup.pow_mem _ hb' k
    have hyz : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hy.2 z hzU, mul_inv_cancel_right]
    by_cases hyV : y ∈ Subgroup.centralizer (V : Set G)
    · have hyO : y ∈ pCoreOf 2 L :=
        h.toHyp5_0_1.inf_centralizer_le (le_sup_left.trans c.V_facts.2.1) h.module.2.2
          ⟨hyB.1, hyV⟩
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨y, hyO⟩
      exact eq_one_of_odd_of_pow_ch615 hodd (by simpa using congrArg Subtype.val hk)
    · exact absurd ((c.nat_F4 h512 h5172).mem_centralizer_of_odd_ch6 c.isSylowTwoOf_inf hyB.1 hodd
        hyV (c.ZV hz.1) hyz) hzL

  have h2 : IsPGroup 2 ↥((B ⊔ T) ⊓ Subgroup.centralizer (U : Set G)) := by
    intro x
    obtain ⟨a, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
    refine ⟨a, Subtype.ext ?_⟩
    have hy := hodd1 ((x : G) ^ 2 ^ a) (Subgroup.pow_mem _ x.2 _) (by
      rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
      exact hr)
    simpa using hy
  have hle := le_pCoreOf_of_le_normalizer inf_le_left (fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hBTC hg⟩) h2
  exact hle.trans (F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right))

theorem QX_F4 (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4)
    (hcent : H ⊓ Subgroup.centralizer (UH T H : Set G) = pCoreOf 2 H) :
    pCoreOf 2 (borelL T L ⊔ H) = T ⊓ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) : Set G) := by
  have h := c.hyp
  set B := borelL T L with hBdef
  set X := B ⊔ H with hXdef
  set U := conjClosure (quasithinOmegaOneCenter T) X with hUdef
  have hTH : T ≤ H := c.hH.1.1
  have hTX : T ≤ X := hTH.trans le_sup_right
  have hsyl : IsSylowTwoOf T X := h.toHyp5_0_1.isSylowTwoOf hTX
  have hF : CharTwo X := charTwo_of_inH' h.qtke h.sylow ⟨hTX, c.X_O2_F4 h5172⟩
  obtain ⟨hUO, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hO2U : pCoreOf 2 X ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)

  have hUHU : UH T H ≤ U := conjClosure_mono le_rfl le_sup_right
  have hHC : H ⊓ Subgroup.centralizer (U : Set G) ≤ T := fun x hx => by
    have hx' : x ∈ H ⊓ Subgroup.centralizer (UH T H : Set G) :=
      ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUHU) hx.2⟩
    rw [hcent] at hx'
    exact F7.isSylowTwoOf_pCoreOf_le c.isSylowTwoOf hx'
  have e1 : T ⊓ Subgroup.centralizer (U : Set G) = H ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (inf_le_inf_right _ hTH) (le_inf hHC inf_le_right)
  have e2 : T ⊓ Subgroup.centralizer (U : Set G) =
      (B ⊔ T) ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf (c.faithful_F4 h512 h5172) inf_le_right)
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hXC : X ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    le_normalizer_centralizer_ch6 hXU
  have hHn : H ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := by
    rw [e1]
    exact fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hXC ((le_sup_right : H ≤ X) hg)⟩
  have hBn : B ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := by
    rw [e2]
    exact fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ((le_sup_left : B ≤ B ⊔ T) hg), hXC ((le_sup_left : B ≤ X) hg)⟩
  apply le_antisymm (le_inf (F7.isSylowTwoOf_pCoreOf_le hsyl) hO2U)
  exact le_pCoreOf_of_le_normalizer (inf_le_left.trans hTX) (sup_le hBn hHn)
    (h.sylow.1.to_le inf_le_left)

end Cx615

end CFSG.Quasithin.H13
