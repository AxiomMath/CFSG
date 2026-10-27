module

public import CFSG.Quasithin.H13.A5S1327zn
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327w
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327y
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327za
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327zd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327zg
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1328Blk3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_s2a_F4 (h126 : TheoremC126) (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h5172 : Stmt5_1_7_two_F4) (h1332 : Stmt13_3_2_F4)
    (h137 : EmptyFaithfulMultiple.Input137) (h1391 : Theorem1391Statement) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    {hU : IsElemAbelian 2 (S.UH H)} {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))}
    (D : S2A S H hU K₁ K₂) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have B := D.blocks
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hUO, -, -⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl (S.charTwo_of_inH hH.1) le_rfl
  have hCU : H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H :=
    S.centralizer_UH_le_pCoreOf_all_F4 h331 h1222 h5172 hH hHZ hsolv
  have hRT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hUT : S.UH H ≤ T := fun u hu => hRT (hUO hu).1
  have hU2 : IsPGroup 2 ↥(S.UH H) := fun g => ⟨1, Subtype.ext (by simpa using hU.2 g g.2)⟩
  obtain ⟨htriple, hinf⟩ := S.goldschmidt_triple_F4 h331 h1222 h517 h5172 hH hHZ hsolv D
  have hG1G0 : S.G1e H ≤ S.G0e H := le_sup_left
  have hT0G1 : S.T0e ≤ S.G1e H := S.T0_le_G1 hTH
  have hsylT0 : IsSylowTwoOf S.T0e (S.G0e H) := by
    have := htriple.2.2.2
    rwa [hinf] at this
  have hsylG1 : IsSylowTwoOf S.T0e (S.G1e H) := C1GN.isSylowTwoOf_of_le hsylT0 hT0G1 hG1G0

  obtain ⟨c₁, hc₁L, hc₁N, hc₁3, hc₁K, hc₁1, hc₁G, hNU, hQU, -⟩ :=
    S.exists_side1_F4 h331 h1222 h5172 hH hHZ hsolv D
  have hX₁ := B.a4Data hc₁N hc₁3 hc₁K hc₁1
  have he1U : S.e1 ∈ blk hU K₁ := mem_blk.2 ⟨D.e1_mem, D.e1_U1⟩
  have hU₁G : blk hU K₁ ≤ S.G1e H := fun u hu =>
    ⟨hTH (hUT (blk_le K₁ hu)), Subgroup.mem_centralizer_singleton_iff.mpr
      (B2F.isElemAbelian_comm hU (blk_le K₁ hu) D.e2_mem)⟩
  have hcU₁ : ∀ u ∈ blk hU K₁, c₁ * u * c₁⁻¹ ∈ blk hU K₁ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hNU hc₁G) u).mp hu

  obtain ⟨e⟩ := S.quotient_G1_F4 h331 h1222 h5172 hH hHZ hsolv D
  have h6 : Nat.card (↥(S.G1e H) ⧸ CFSG.Open.pCore 2 ↥(S.G1e H)) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hnot2 : ¬ S.G1e H ≤ T := by
    intro hG1T
    have h2 : IsPGroup 2 ↥(S.G1e H) := S.isPGroup_T.to_le hG1T
    have htop : CFSG.Open.pCore 2 ↥(S.G1e H) = ⊤ :=
      eq_top_iff.mpr (CFSG.LieType.BorelTits.le_pCore 2 inferInstance (h2.to_subgroup ⊤))
    rw [htop] at h6
    have h1 : Nat.card (↥(S.G1e H) ⧸ (⊤ : Subgroup ↥(S.G1e H))) = 1 := Subgroup.index_top
    omega

  set Q₁ := pCoreOf 2 (S.G1e H) with hQ₁def
  have hcardG1 : Nat.card ↥(S.G1e H) = 6 * Nat.card ↥Q₁ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥(S.G1e H))
    rw [h6] at h1
    rw [h1]
    congr 1
    exact Nat.card_congr ((CFSG.Open.pCore 2 ↥(S.G1e H)).equivMapOfInjective _
      (S.G1e H).subtype_injective).toEquiv
  obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 (S.G1e H)).exists_card_eq
  have hcardG1' : Nat.card ↥(S.G1e H) = 3 * 2 ^ (b + 1) := by
    rw [hcardG1, hb, pow_succ]
    ring
  have hQ₁T0 : Q₁ ≤ S.T0e := pCoreOf_two_le_of_isSylowTwoOf hsylG1
  have hrel : Q₁.relIndex (S.G1e H) = 6 := by
    have := Subgroup.relIndex_mul_card (H := Q₁) (K := S.G1e H)
    rw [inf_eq_left.mpr (pCoreOf_le 2 _), hcardG1] at this
    have hpos : 0 < Nat.card ↥Q₁ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [this, mul_comm])
  have h3 : S.T0e.relIndex (S.G1e H) = 3 := by
    have h1 := Subgroup.relIndex_mul_relIndex Q₁ S.T0e (S.G1e H) hQ₁T0 hT0G1
    rw [hrel] at h1
    have hodd : ¬ 2 ∣ S.T0e.relIndex (S.G1e H) := hsylG1.2.2
    have hdvd : S.T0e.relIndex (S.G1e H) ∣ 6 := ⟨_, by rw [← h1, mul_comm]⟩
    have hne1 : S.T0e.relIndex (S.G1e H) ≠ 1 := fun h =>
      hnot2 ((Subgroup.relIndex_eq_one.mp h).trans inf_le_left)
    have hle : S.T0e.relIndex (S.G1e H) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : S.T0e.relIndex (S.G1e H) <;> simp_all
  have hnormal : ¬ S.G1e H ≤ Subgroup.normalizer (S.T0e : Set G) := by
    intro hN
    have hle : S.T0e ≤ Q₁ := le_pCoreOf_of_le_normalizer 2 hT0G1 hN hsylG1.2.1
    have heq : Q₁ = S.T0e := le_antisymm hQ₁T0 hle
    rw [heq, h3] at hrel
    exact absurd hrel (by norm_num)
  have hmp := minParabolic_of_relIndex_three hsylG1 h3 hnormal

  have hRG1 : pCoreOf 2 H ≤ S.G1e H := fun r hr => ⟨pCoreOf_le 2 H hr,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hUO D.e2_mem).2 r hr)⟩
  have hG1char : CharTwo (S.G1e H) :=
    charTwo_of_pCoreOf_le (S.charTwo_of_inH hH.1) inf_le_left hRG1
  have hRQ₁ : pCoreOf 2 H ≤ Q₁ :=
    le_pCoreOf_of_le_normalizer 2 hRG1 (fun g hg => le_normalizer_pCoreOf 2 H hg.1)
      (pCoreOf_isPGroup 2 _)
  have hQ₁ne : Q₁ ≠ ⊥ := fun h => hH.1.2 (le_bot_iff.mp (h ▸ hRQ₁))
  have hG1SQ : IsSQTKTC (S.G1e H) :=
    isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian (T := S.T0e) ⟨hT0G1, hQ₁ne⟩

  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  have hT0 : T ≠ ⊥ := fun h =>
    S.z_ne_one (Subgroup.mem_bot.mp (h.le (S.V_le_T S.z_mem_V)))
  have hT₀2 : IsPGroup 2 ↥S.T0e := S.isPGroup_T.to_le inf_le_left
  have hT₀ne : S.T0e ≠ ⊥ := fun h => S.e1_ne_one (Subgroup.mem_bot.mp (h.le S.e1_mem_T0e))
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, -, -⟩ := hC.pair T S.isPGroup_T hT0

  have hbaum : baum S.T0e = baum T := by
    unfold baum
    rw [S.thompsonJ_T0e, D.E_eq]
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun x hx => ⟨⟨hx.1, ?_⟩, hx.2⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx.2 S.e2 S.e2_mem_V2).symm
  have hC2 : C₂ S.T0e = C₂ T := by
    rw [hC.c2_eq _ hT₀2 hT₀ne, hC.c2_eq _ S.isPGroup_T hT0, hbaum]

  have hzC1T : S.z ∈ C₁ T := by
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := C₁ T)).1 h1ne
    have hcZ : (c : G) ∈ S.V1 := by
      rw [← D.Z_eq]
      exact h1Z c.2
    rcases S.mem_V1.1 hcZ with h | h
    · exact absurd (Subtype.ext h) hc1
    · rw [← h]; exact c.2
  have hzC1T0 : S.z ∈ C₁ S.T0e := by
    rw [hC.c1_eq _ hT₀2 hT₀ne, hbaum]
    have hzB : S.z ∈ C₁ (baum T) := by
      have := hzC1T
      rw [hC.c1_eq _ S.isPGroup_T hT0] at this
      exact this.2
    refine ⟨⟨⟨S.V_le_T S.z_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr
      (B2F.isElemAbelian_comm S.elemAbelian_V S.z_mem_V S.e2_mem_V)⟩, ?_⟩, hzB⟩
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    exact (Subgroup.mem_centralizer_iff.mp
      (mem_quasithinOmegaOneCenter_iff.mp S.z_mem_omegaOneCenter).2.1) t ht.1

  have hLTN : L ⊔ T ≤ Subgroup.normalizer (C₂ T : Set G) := by
    rcases S.c126_LT (h126 G C₁ C₂ hC) with h1 | h2 | ⟨hblk, h5⟩
    · exfalso
      have hzC : S.z ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_sup_left hl)) _ hzC1T).symm
      have hzL : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, hzC⟩
      rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzL
      exact S.z_ne_one hzL
    · exact h2
    · exact (S.false_of_pCoreOf_le_UH_F4 h331 h1222 h5172 h1332 h137 h1391 hH hHZ hsolv hS3
        D.blocks D.top D.cent (S.pCoreOf_le_UH_of_F4 h331 h1222 h5172 hH hHZ hsolv D
          (S.pCoreOf_LT_le_V hblk h5 D.CTL))).elim
  have hC₂2 : IsPGroup 2 ↥(C₂ T) := S.isPGroup_T.to_le (h2B.trans (C1GN.baum_le T))
  have hNM : Subgroup.normalizer (C₂ T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hloc : IsTwoLocal (Subgroup.normalizer (C₂ T : Set G)) := ⟨C₂ T, h2ne, hC₂2, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hM'eq : M' = Subgroup.normalizer (L : Set G) := S.uniqueM.2 M' ⟨hM', hLTN.trans hle⟩
    rw [← hM'eq]
    exact hle

  rcases c126_of_minParabolic (h126 G C₁ C₂ hC) hG1char hG1SQ hmp with h1 | h2 | ⟨Bk, hBk⟩
  ·
    have hcz : S.z * c₁ = c₁ * S.z := Subgroup.mem_centralizer_iff.mp (h1 hc₁G) _ hzC1T0
    have hce2 : c₁ * S.e2 = S.e2 * c₁ := Subgroup.mem_centralizer_singleton_iff.mp hc₁G.2
    apply hX₁.fpf S.e1 he1U S.e1_ne_one
    rw [← S.e1_mul_e2] at hcz
    calc c₁ * S.e1 * c₁⁻¹ = (c₁ * (S.e1 * S.e2)) * S.e2⁻¹ * c₁⁻¹ := by group
      _ = (S.e1 * S.e2 * c₁) * S.e2⁻¹ * c₁⁻¹ := by rw [← hcz]
      _ = S.e1 * (S.e2 * c₁ * S.e2⁻¹) * c₁⁻¹ := by group
      _ = S.e1 * (c₁ * S.e2 * S.e2⁻¹) * c₁⁻¹ := by rw [← hce2]
      _ = S.e1 := by group
  ·
    rw [hC2] at h2
    apply hnot2
    intro x hx
    rw [← S.inf_M_eq_T_F4 h331 h1222 h5172 hH hHZ hsolv D.blocks D.top]
    exact ⟨hx.1, hNM (h2 hx)⟩
  ·
    obtain ⟨hblk, htype⟩ := hBk
    have hBsh : IsShort2 Bk := hblk.1
    have hBG : Bk ≤ S.G1e H := hblk.2.1
    have hBdvd : Nat.card ↥Bk ∣ 3 * 2 ^ (b + 1) := hcardG1' ▸ Subgroup.card_dvd_of_le hBG
    have h3B : IsAltType Bk 3 := by
      rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
      · exfalso
        have hc := Lin2.lin2_card_L hlin
        have hm : ((2 ^ n) ^ 2 - 1) ∣ 3 * 2 ^ (b + 1) :=
          (Dvd.intro_left (Nat.card ↥(pCoreOf 2 Bk) * 2 ^ n) (by rw [hc, mul_assoc])).trans
            hBdvd
        have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
          have h4 : 4 ≤ (2 ^ n) ^ 2 := by
            have : 2 ≤ 2 ^ n := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
            nlinarith
          have hev : Even ((2 ^ n) ^ 2) := by
            rw [← pow_mul]
            exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
          exact Nat.Even.sub_odd (by omega) hev odd_one
        have hcop : Nat.Coprime ((2 ^ n) ^ 2 - 1) (2 ^ (b + 1)) :=
          Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
        have h3 : ((2 ^ n) ^ 2 - 1) ∣ 3 := hcop.dvd_of_dvd_mul_right hm
        have h16 : 16 ≤ (2 ^ n) ^ 2 := by
          have : 4 ≤ 2 ^ n := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          nlinarith
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      · exact h3
      · exfalso
        obtain ⟨α, hα, -⟩ := h5
        have h60 : 60 ∣ Nat.card ↥Bk := by
          have h1 := Subgroup.card_ker_mul_card_of_surjective hα
          have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := card_alt_five
          rw [h2] at h1
          exact ⟨_, by rw [← h1, mul_comm]⟩
        have h5 : 5 ∣ 3 * 2 ^ (b + 1) :=
          (Dvd.dvd.trans (by norm_num : (5 : ℕ) ∣ 60) h60).trans hBdvd
        have hcop : Nat.Coprime 5 (2 ^ (b + 1)) := Nat.Coprime.pow_right _ (by norm_num)
        have := hcop.dvd_of_dvd_mul_right h5
        omega

    have h3dvd : 3 ∣ Nat.card ↥Bk := by
      obtain ⟨α, hα, -⟩ := h3B
      have h1 := Subgroup.card_ker_mul_card_of_surjective hα
      have h2 : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
      rw [h2] at h1
      exact ⟨_, by rw [← h1, mul_comm]⟩
    have hBeq : Bk = twoResidual (S.G1e H) :=
      le_antisymm (le_twoResidual_of_isShort2 hBG hBsh)
        (twoResidual_le_of_subnormal hcardG1' hBG hblk.2.2 h3dvd)
    have hTN : S.T0e ≤ Subgroup.normalizer (Bk : Set G) := by
      rw [hBeq]
      exact hT0G1.trans (le_normalizer_twoResidual _)
    have hsup : Bk ⊔ S.T0e = S.G1e H := by
      rw [hBeq, sup_comm]
      exact sup_twoResidual_eq hsylG1
    have hsyl' : IsSylowTwoOf S.T0e (Bk ⊔ S.T0e) := by rw [hsup]; exact hsylG1
    have hO := VolI.pCoreOf_eq_sup_of_alt3 hBsh hsyl' hTN h3B
    rw [hsup] at hO
    have hc₁B : c₁ ∈ Bk := by
      rw [hBeq]
      refine F6.mem_twoResidual_of_odd hc₁G ?_
      have h1 : orderOf c₁ ∣ 3 := orderOf_dvd_of_pow_eq_one hc₁3
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · rw [h]; exact odd_one
      · rw [h]; decide

    have hcommU : ∀ x ∈ blockU Bk, ∀ y ∈ S.T0e ⊓ Subgroup.centralizer (Bk : Set G),
        x * y = y * x := by
      intro x hx y hy
      have hxB : x ∈ Bk := (C1.blockU_le_blockQ hBsh).trans (C1.blockQ_le Bk) hx
      exact Subgroup.mem_centralizer_iff.mp hy.2 x hxB
    have hQc : ∀ r ∈ Q₁, r * c₁ * r⁻¹ * c₁⁻¹ ∈ blockU Bk := by
      intro r hr
      rw [hQ₁def, hO] at hr
      obtain ⟨u, hu, d, hd, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hcommU hr
      have hdc : d * c₁ = c₁ * d := (Subgroup.mem_centralizer_iff.mp hd.2 c₁ hc₁B).symm
      have e : u * d * c₁ * (u * d)⁻¹ * c₁⁻¹ = u * (c₁ * u⁻¹ * c₁⁻¹) := by
        calc u * d * c₁ * (u * d)⁻¹ * c₁⁻¹ = u * (d * c₁) * d⁻¹ * u⁻¹ * c₁⁻¹ := by group
          _ = u * (c₁ * d) * d⁻¹ * u⁻¹ * c₁⁻¹ := by rw [hdc]
          _ = u * (c₁ * u⁻¹ * c₁⁻¹) := by group
      rw [e]
      exact (blockU Bk).mul_mem hu (AppC.conj_mem_blockU hc₁B ((blockU Bk).inv_mem hu))

    have hU₁Q₁ : blk hU K₁ ≤ Q₁ := le_pCoreOf_of_le_normalizer 2 hU₁G hNU
      (hU2.to_le (blk_le K₁))
    have hfpf₁ : ∀ w ∈ blk hU K₁, c₁ * w * c₁⁻¹ = w → w = 1 := fun w hw h => by
      by_contra hw1
      exact hX₁.fpf w hw hw1 h
    have hU₁B : blk hU K₁ ≤ blockU Bk := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := exists_eq_mul_conj_of_fpf hcU₁ hfpf₁ hw
      exact hQc v (hU₁Q₁ hv)
    have hcardB : Nat.card ↥(blockU Bk) = 4 := (hBsh.alt3_structure h3B).2.1
    have hUeq : blk hU K₁ = blockU Bk :=
      Subgroup.eq_of_le_of_card_ge hU₁B (by rw [hcardB, hX₁.card_W])

    have hcomm : ∀ r ∈ pCoreOf 2 H, r * c₁ * r⁻¹ * c₁⁻¹ ∈ blk hU K₁ := fun r hr => by
      rw [hUeq]
      exact hQc r (hRQ₁ hr)
    have hRU := B.le_of_comm_blk D.top hTH hRT (fun u hu => (hUO hu).1) (pCoreOf_isPGroup 2 H)
      (le_normalizer_pCoreOf 2 H) hCU
      (fun p hp u hu => Subgroup.mem_centralizer_iff.mp (hUO hu).2 p hp)
      D.cent hc₁L hc₁N hc₁3 hc₁K hc₁1 hcomm
    exact S.false_of_pCoreOf_le_UH_F4 h331 h1222 h5172 h1332 h137 h1391 hH hHZ hsolv hS3 D.blocks
      D.top D.cent hRU

end Setting

theorem caseS2A_1327_of_c126_F4 (h126 : TheoremC126) (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h5172 : Stmt5_1_7_two_F4) (h1332 : Stmt13_3_2_F4)
    (h137 : EmptyFaithfulMultiple.Input137) (h1391 : Theorem1391Statement) : CaseS2A_1327_F4 := by
  intro G _ _ T L V S H hH hHZ hsolv hS3 hO2
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hH.1.1
  obtain ⟨-, hU, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl (S.charTwo_of_inH hH.1) le_rfl
  obtain ⟨K₁, K₂, D⟩ := S.exists_s2a_F4 h331 h5172 hH hHZ hsolv hS3 hO2 hU
  exact S.false_of_s2a_F4 h126 h331 h1222 h517 h5172 h1332 h137 h1391 hH hHZ hsolv hS3 D

theorem stmt13_2_7_of_c126_F4
    (h331 : Stmt3_3_1_F4) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2_F4) (h523 : Stmt5_2_3_F4)
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h5172 : Stmt5_1_7_two_F4)
    (hE22 : E2.E22StatementNoN) (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big)
    (hL2 : FactL2Three) (h1332 : Stmt13_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h137 : EmptyFaithfulMultiple.Input137) (h1391 : Theorem1391Statement)
    (h126 : TheoremC126) : Stmt13_2_7_F4 :=
  stmt13_2_7_of_caseS2A_c126_F4 h331 h311 h432 h523 h1222 h5172 hE22 hF618 hBig hL2 h1332 h512 h137
    h126 (caseS2A_1327_of_c126_F4 h126 h331 h1222 h517 h5172 h1332 h137 h1391)

end CFSG.Quasithin.H13.A5
