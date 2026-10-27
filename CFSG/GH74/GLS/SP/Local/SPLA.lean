module

public import CFSG.GH74.GLS.SP.Local.SPLADiag
public import CFSG.GH74.GLS.SP.Local.SPLACore
public import CFSG.GH74.GLS.SP.Local.SPLPGL2Cartan
public import CFSG.GH74.GLS.SP.Local.SPLADih
public import CFSG.GH74.GLS.SP.Local.SPLM1c
public import CFSG.GH74.GLS.SP.Local.SPLM2b

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

section Arith

variable {G : Type} [Group G]

theorem four_dvd_d (D : SPLNot0 G) (hodd : Odd D.q) : 4 ∣ D.d := by
  unfold SPLNot0.d
  obtain ⟨k, hk⟩ := hodd
  split_ifs with h <;> omega

theorem three_le_n (D : SPLNot0 G) (hodd : Odd D.q) (h5 : 5 ≤ D.q) : 3 ≤ D.n := by
  have h4 := four_dvd_d D hodd
  have hd0 : D.d ≠ 0 := by
    rintro h0
    unfold SPLNot0.d at h0
    split_ifs at h0
    all_goals omega
  have : 2 ≤ D.d.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hd0).mp (by simpa using h4)
  unfold SPLNot0.n
  omega

theorem fact_le_n (D : SPLNot0 G) (hodd : Odd D.q) (h5 : 5 ≤ D.q) :
    (D.q - 1).factorization 2 ≤ D.n - 1 := by
  have h3 := three_le_n D hodd h5
  by_cases h : D.q % 4 = 1
  · have hd : D.d = D.q - 1 := by unfold SPLNot0.d; simp [h]
    have : D.n - 1 = D.d.factorization 2 := by unfold SPLNot0.n; omega
    rw [this, hd]
  · have hq0 : D.q - 1 ≠ 0 := by omega
    have : ¬ 2 ≤ (D.q - 1).factorization 2 := by
      intro h2
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hq0).mpr h2
      obtain ⟨k, hk⟩ := hodd
      have h4 : 4 ∣ D.q - 1 := by simpa using this
      omega
    omega

end Arith


section Assembly

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem x_mem_Ct (hc : SPL2Ct D.toSPLNot2) : D.x ∈ D.Ct := by
  have := hc.Ct_eq
  show D.x ∈ D.toSPLNot2.Ct
  rw [this]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers _))

omit [Finite G] in
theorem I_normalized (hc : SPL2Ct D.toSPLNot2) : ∀ c ∈ D.Ct, ∀ i ∈ D.I, c * i * c⁻¹ ∈ D.I := by
  intro c hcC i hi
  have hI : D.I = IVK.Ez D.t := hc.I_eq
  rw [hI] at hi ⊢
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hi
  let g : ↥(centralizer ({D.t} : Set G)) := ⟨c, hcC⟩
  refine Subgroup.mem_map.mpr ⟨g * j * g⁻¹, ?_, by simp [g]⟩
  have hchar := CFSG.LocalCores.layer_characteristic (G := ↥(centralizer ({D.t} : Set G)))
  have hmap := (Subgroup.characteristic_iff_map_eq.mp hchar) (MulAut.conj g)
  have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hj
  rw [hmap] at this
  simpa [MulAut.conj_apply] using this

omit [Finite G] in
theorem center_I_trivial (hc : SPL2Ct D.toSPLNot2) :
    ∀ g : ↥D.I, (∀ i : ↥D.I, g * i = i * g) → g = 1 := by
  obtain ⟨F, hF1, hF2, hFq, ⟨e⟩⟩ := hc.I_L2
  intro g hg
  let e' := e.trans (IVK.L2.equivPSL F)
  have hcen : e' g ∈ Subgroup.center (CFSG.GorensteinWalter.PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨i, rfl⟩ := e'.surjective y
    rw [← map_mul, ← map_mul, hg i]
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot F] at hcen
  exact e'.map_eq_one_iff.mp (Subgroup.mem_bot.mp hcen)

omit [Finite G] in
theorem Z_inf_I (hc : SPL2Ct D.toSPLNot2) : D.I ⊓ zpowers (D.x ^ 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgI, hgZ⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hgZ
  have hcomm : ∀ i : ↥D.I, (⟨(D.x ^ 2) ^ j, hgI⟩ : ↥D.I) * i = i * ⟨(D.x ^ 2) ^ j, hgI⟩ := by
    intro i
    apply Subtype.ext
    exact ((show Commute (D.x ^ 2) i from hc.x2_cen i (Subgroup.mem_sup_left i.2)).zpow_left j)
  have := center_I_trivial D hc _ hcomm
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

omit [Finite G] in
theorem card_I (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.I = D.q * (D.q ^ 2 - 1) / 2 := by
  obtain ⟨F, hF1, hF2, hFq, ⟨e⟩⟩ := hc.I_L2
  have hq : Nat.card F = D.q := hFq
  let e' := e.trans (IVK.L2.equivPSL F)
  obtain ⟨k, hk1, hkq⟩ := hs.q_pow
  rw [Nat.card_congr e'.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F
    ⟨D.p, k, hs.prime, hs.prime.odd_of_ne_two hs.p_ne_two, hk1, by rw [hq, hkq]⟩, hq]

omit [Finite G] in
theorem M_le_Ct (hc : SPL2Ct D.toSPLNot2) : D.I ⊔ zpowers D.x ≤ D.Ct :=
  sup_le (I_le_Ct D hc) (by rw [zpowers_le]; exact x_mem_Ct D hc)

omit [Finite G] in
theorem z_inv_x (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    D.z * D.x * D.z⁻¹ = D.x⁻¹ :=
  inv_of_isDihedralOrder D.x D.z D.n (three_le_n D.toSPLNot0 hs.odd_q hs.q_ge) hc.xz_dih hc.x_ord
    hs.syl.z_inv


theorem splLeafA_of_cartan (hP : PGL2CartanStmt) : SPLLeafA := by
  intro G _ _ hG D hs h1 hc ho h3
  classical
  have hq5 := hs.q_ge
  have hodd := hs.odd_q
  have hn3 := three_le_n D.toSPLNot0 hodd hq5
  have hqn := fact_le_n D.toSPLNot0 hodd hq5
  have hxCt := x_mem_Ct D hc
  have hIn : ∀ i ∈ D.I, D.x * i * D.x⁻¹ ∈ D.I := I_normalized D hc D.x hxCt
  have hx2 : ∀ i ∈ D.I, D.x ^ 2 * i = i * D.x ^ 2 := fun i hi =>
    hc.x2_cen i (Subgroup.mem_sup_left hi)
  obtain ⟨hN, hquot⟩ := hc.quot
  have hN' : ((zpowers (D.x ^ 2)).subgroupOf (D.I ⊔ zpowers D.x)).Normal := hN
  obtain ⟨b, hb, u, huH, huu, haa, hawa, haH, haY, haM⟩ :=
    cartan_core hP D.I D.Y₀ D.H₀ (D.I ⊔ zpowers D.x) (zpowers (D.x ^ 2)) D.x D.w D.n D.q rfl rfl
      hq5 hodd hn3 hqn hIn hx2 (Z_inf_I D hc) (card_I D hs hc) hquot
      (Y₀_le_I D hs hc h3) (Y₀_card D hs h3) (H₀_le_I D hs h1 hc)
      (isCyclic_zpowers _) (H₀_card' D hs h1) (H₀_norm_Y₀ D hs h1 h3)
      (w_mem_I D hs h1 hc) (w_mul_w D hs h1) (w_not_mem_H₀ D hs h1) (w_inv_H₀ D hs h1)
  refine ⟨(b * D.x) ^ (2 ^ (D.n - 3)), ?_⟩
  set a : G := (b * D.x) ^ (2 ^ (D.n - 3)) with ha
  have hat : a ∈ D.Ct := M_le_Ct D hc haM
  have htx : D.x ^ (2 ^ (D.n - 2)) = D.t := hc.x_pow
  have h2m : 2 * 2 ^ (D.n - 3) = 2 ^ (D.n - 2) := by
    have : D.n - 2 = (D.n - 3) + 1 := by omega
    rw [this, pow_succ]; ring
  have htZ : D.t ∈ zpowers (D.x ^ 2) := by
    rw [← htx]
    exact mem_zpowers_iff.mpr ⟨((2 ^ (D.n - 3) : ℕ) : ℤ), by rw [zpow_natCast, ← pow_mul, h2m]⟩
  have htcomm : ∀ i ∈ D.I, D.t * i = i * D.t := by
    intro i hi
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp htZ
    rw [← hj]
    exact ((show Commute (D.x ^ 2) i from hx2 i hi).zpow_left j)
  have huI : u ∈ D.I := H₀_le_I D hs h1 hc huH
  have hut : a * a = u * D.t := by rw [haa, htx]
  have ht1 : D.t ≠ 1 := by
    intro h
    have := hs.syl.t_ord
    rw [h, orderOf_one] at this
    omega
  have hcu : D.t * u = u * D.t := htcomm u huI
  have ha2 : ¬ a ^ (2 ^ 1) = 1 := by
    intro h
    rw [pow_one, pow_two, hut] at h
    have hteq : D.t = u⁻¹ := by
      calc D.t = u⁻¹ * (u * D.t) := by group
        _ = u⁻¹ := by rw [h]; group
    have htI : D.t ∈ D.I := by rw [hteq]; exact D.I.inv_mem huI
    have : D.t ∈ D.I ⊓ zpowers (D.x ^ 2) := ⟨htI, htZ⟩
    rw [Z_inf_I D hc] at this
    exact ht1 (Subgroup.mem_bot.mp this)
  have ha4 : a ^ (2 ^ (1 + 1)) = 1 := by
    have e : a ^ (2 ^ (1 + 1)) = (a * a) * (a * a) := by
      have : (2 : ℕ) ^ (1 + 1) = 2 + 2 := rfl
      rw [this, pow_add, pow_two]
    rw [e, hut]
    calc u * D.t * (u * D.t) = u * (D.t * u) * D.t := by group
      _ = u * (u * D.t) * D.t := by rw [hcu]
      _ = (u * u) * (D.t * D.t) := by group
      _ = 1 := by rw [huu, t_mul_t D hs]; group
  have hord : orderOf a = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) ha2 ha4
    simpa using this
  have hzb : D.z * b = b * D.z := z_cen_I D hs hc b hb
  have hzx := z_inv_x D hs hc
  have hzτ : D.z * (b * D.x) * D.z⁻¹ = b * D.x⁻¹ := by
    calc D.z * (b * D.x) * D.z⁻¹ = (D.z * b * D.z⁻¹) * (D.z * D.x * D.z⁻¹) := by group
      _ = b * D.x⁻¹ := by rw [hzx, hzb]; group
  have hcomm' : Commute (b * D.x⁻¹) (D.x ^ 2) := by
    have h1' : Commute b (D.x ^ 2) := (hx2 b hb).symm
    have h2' : Commute D.x⁻¹ (D.x ^ 2) := ((Commute.refl D.x).pow_right 2).inv_left
    exact h1'.mul_left h2'
  have hsplit : b * D.x = (b * D.x⁻¹) * D.x ^ 2 := by group
  have hapow : a = (b * D.x⁻¹) ^ (2 ^ (D.n - 3)) * D.t := by
    rw [ha, hsplit, hcomm'.mul_pow, ← pow_mul, h2m, htx]
  have htt := t_mul_t D hs
  have hzaz : D.z * a * D.z⁻¹ = a * D.t := by
    have e1 : D.z * a * D.z⁻¹ = (D.z * (b * D.x) * D.z⁻¹) ^ (2 ^ (D.n - 3)) := by
      rw [ha, conj_pow]
    rw [e1, hzτ]
    calc (b * D.x⁻¹) ^ (2 ^ (D.n - 3)) = (b * D.x⁻¹) ^ (2 ^ (D.n - 3)) * (D.t * D.t) := by
          rw [htt]; group
      _ = ((b * D.x⁻¹) ^ (2 ^ (D.n - 3)) * D.t) * D.t := by group
      _ = a * D.t := by rw [← hapow]
  have hazz : a⁻¹ * D.z * a = D.z * D.t := by
    calc a⁻¹ * D.z * a = a⁻¹ * (D.z * a * D.z⁻¹) * D.z := by group
      _ = a⁻¹ * (a * D.t) * D.z := by rw [hzaz]
      _ = D.t * D.z := by group
      _ = D.z * D.t := t_comm_z D hs
  refine ⟨hat, hord, ⟨hazz, ⟨u, huH, huu, hut, hawa⟩, ?_⟩, ?_⟩
  · intro h hh
    rw [haH h hh]; exact hh
  · show conjBy a D.Y₀ = D.Y₀
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      simpa [MulAut.conj_apply] using haY y hy
    · rw [card_conjBy]

end Assembly


theorem pgl2CartanStmt : PGL2CartanStmt := by
  intro F _ _ hodd h5 M _ θ I hI Y H hY hHI hHc hH hHY w hw2 hwH hwinv
  exact pgl2_cartan hodd h5 θ I hI Y H hY hHI hHc hH hHY w hw2 hwH hwinv

theorem splLeafA : SPLLeafA := splLeafA_of_cartan pgl2CartanStmt

end CFSG.GH74.GLS.SP.Local
