module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddF81
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mulVec)
open scoped IsMulCommutative commutatorElement Pointwise

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem B_le_centralizer_F4 (h5114 : Stmt5_1_14_first_F4) (hI : L2OddInnerFact) (hB3 : Nat.card B ∣ 3)
    (c : OddCoord T L V n) : B ≤ Subgroup.centralizer (V : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  intro b hb
  have hbM : b ∈ M := (s.hyp.notation59.1.1 hb).1
  have hbH : b ∈ H := (s.hyp.notation59.1.1 hb).2
  have hZH := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hbZ : ∀ z ∈ quasithinOmegaOneCenter T, b * z * b⁻¹ = z := by
    intro z hz
    have hc : ⁅z, b⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hz hbH
      rw [hZH, Subgroup.mem_bot] at this
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at hc
    rw [← hc, mul_inv_cancel_right]

  have hbV : b ∈ Subgroup.normalizer (V : Set G) := by
    by_contra hbV
    have hti := s.ti b hbM hbV
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp s.Z₁_ne_bot
    have hzc : z ∈ CFSG.conjugate V b := by
      refine ⟨z, hzZ.2, ?_⟩
      show b⁻¹ * z * b⁻¹⁻¹ = z
      have := hbZ z hzZ.1
      calc b⁻¹ * z * b⁻¹⁻¹ = b⁻¹ * (b * z * b⁻¹) * b := by rw [inv_inv, this]
        _ = z := by group
    have hmem : z ∈ V ⊓ CFSG.conjugate V b := ⟨hzZ.2, hzc⟩
    rw [hti, Subgroup.mem_bot] at hmem
    exact hz1 (Subtype.ext hmem)
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := hh.normal hbM
  set bn : Subgroup.normalizer (V : Set G) := ⟨b, hbV⟩ with hbn
  obtain ⟨σ, hσ⟩ := c.semi bn hbL

  have hfix : ∀ x : c.K, c.act bn ![x, 0] = ![x, 0] := by
    intro x
    obtain ⟨v, hv⟩ := c.ε_bij.2 ![x, 0]
    have hvZ := (s.mem_Z_iff hI c v).mpr (by rw [hv]; rfl)
    rw [← hv]
    exact (c.conj_eq_iff bn v).mp (hbZ v hvZ)

  have hσ1 : ∀ a : c.K, σ a = a := by
    intro a
    have h1 := hσ a ![1, 0]
    have e1 : a • (![1, 0] : Fin 2 → c.K) = ![a, 0] := by
      funext i
      fin_cases i <;> simp
    rw [e1, hfix, hfix] at h1
    have := congrFun h1 0
    simp at this
    exact this.symm

  set u := c.act bn ![0, 1] with hu
  have hlin : ∀ w : Fin 2 → c.K, c.act bn w = ![w 0 + w 1 * u 0, w 1 * u 1] := by
    intro w
    have hw : c.act bn w = c.act bn (w 0 • ![1, 0] + w 1 • ![0, 1]) := by
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hw, c.act_add, hσ, hσ, hσ1, hσ1, hfix, ← hu]
    funext i
    fin_cases i <;> simp

  have hb3 : b ^ 3 = 1 := by
    have h1 : orderOf b ∣ 3 := by
      rw [← Subgroup.orderOf_mk b hb]
      exact (orderOf_dvd_natCard _).trans hB3
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hbn3 : bn * bn * bn = 1 := Subtype.ext (by
    show b * b * b = 1
    rw [← pow_three']
    exact hb3)
  have h3 : c.act bn (c.act bn (c.act bn ![0, 1])) = ![0, 1] := by
    rw [← c.act_mul, ← c.act_mul, hbn3, c.act_one]
  rw [hlin, hlin, hlin] at h3
  have hu1 : u 1 * u 1 * u 1 = 1 := by
    have := congrFun h3 1
    simpa using this
  have hu0 : u 0 + u 1 * u 0 + u 1 * u 1 * u 0 = 0 := by
    have := congrFun h3 0
    simp at this
    linear_combination this

  have hγ : u 1 = 1 := by
    have hne : u 1 ≠ 0 := fun h0 => by simp [h0] at hu1
    set γ := Units.mk0 (u 1) hne with hγdef
    have hγ3 : γ ^ 3 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hγdef, Units.val_mk0, Units.val_one, pow_three']
      exact hu1)
    have h1 : orderOf γ ∣ 3 := orderOf_dvd_of_pow_eq_one hγ3
    have h2 : orderOf γ ∣ 2 ^ n - 1 := by
      rw [← c.card, ← Nat.card_units]
      exact orderOf_dvd_natCard γ
    have h3' : orderOf γ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) s.not_three_dvd
    have := congrArg Units.val (orderOf_eq_one_iff.mp h3')
    simpa [hγdef] using this
  have hu0' : u 0 = 0 := by
    rw [hγ] at hu0
    have h2 : (2 : c.K) = 0 := CharP.cast_eq_zero c.K 2
    linear_combination hu0 - u 0 * h2
  refine (c.mem_centralizer_iff bn).mpr fun w => ?_
  rw [hlin, hγ, hu0', mul_zero, add_zero, mul_one]
  funext i
  fin_cases i <;> rfl

theorem hypF81_F4
    (h5114 : Stmt5_1_14_first_F4) (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h323 : Stmt3_2_3) (hB3 : Nat.card B ∣ 3)
    (hTI : IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤)
    (habel : ∀ H₁ : Subgroup G, H ⊔ D ≤ H₁ →
      H₁ ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) →
      IsElemAbelian 2 (conjClosure V H₁)) :
    HypF81 T V L (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := s.nonempty_coord
  have hh := s.hyp.hyp.toHyp5_0_1
  set Z := quasithinOmegaOneCenter T with hZdef
  set Z₁ := Z ⊓ V with hZ₁def
  set K := oTwoUpper H with hKdef
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hZH := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := by
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
    exact Subgroup.le_centralizer_iff.mp this
  have hHZ₁ : H ≤ Subgroup.normalizer (Z₁ : Set G) := by
    intro x hx
    apply mem_normalizer_of_forall_conj_mem'
    intro z hz
    have : x * z * x⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp (hHZ hx) z hz.1
      rw [← this, mul_inv_cancel_right]
    rw [this]
    exact hz
  have hH₁Z : H ⊔ D ≤ Subgroup.normalizer (Z₁ : Set G) := sup_le hHZ₁ (s.D_le_normalizer_Z₁ hI)
  have hVL : V ≤ L := by
    have h1 := s.natural.commutator_eq
    rw [← h1, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hh.T_le_normalizer (s.le_T hv)) l).mp hl)
      (L.inv_mem hl)
  have hV2 : IsPGroup 2 V := isPGroup_of_isElemAbelian s.elemAbelian
  have hVO : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL s.L_le_normalizer_V hV2

  have hHM : ¬ H ≤ M := s.hyp.hyp.hStar.2.1

  have hmemZ₁ : ∀ v : ↥V, (v : G) ∈ Z₁ ↔ c.ε v 1 = 0 := fun v =>
    ⟨fun h => (s.mem_Z_iff hI c v).mp h.1, fun h => ⟨(s.mem_Z_iff hI c v).mpr h, v.2⟩⟩
  have hεinv : ∀ v w : ↥V, c.ε (v * w⁻¹) = c.ε v - c.ε w := fun v w => by
    have := c.ε_mul (v * w⁻¹) w
    rw [inv_mul_cancel_right] at this
    rw [this]
    abel
  refine
    { sylow := hh.isSylowTwoOf le_top
      elemAbelian := s.elemAbelian
      normalizes_L := hh.T_le_normalizer
      oTwoRes_eq := ?_
      charTwo_L := ?_
      reduced := s.hyp.module.isTwoReducedIn
      cT := hh.centralizer_eq_pCoreOf s.hyp.module
      V₁_ne_bot := s.Z₁_ne_bot
      V₁_le_V := inf_le_right
      T_normalizes_V₁ := T_le_centralizer_Z₁.trans (Subgroup.centralizer_le_normalizer _)
      weak_a := ?_
      V₁_lt_V := ?_
      irred := ?_
      H_normalizes_V₁ := hH₁Z
      L₁T_le_H := ?_
      charTwo_H := ?_
      ker_le := ?_
      o2_trivial := ?_ }
  ·
    rw [oTwoRes_eq_oTwoUpper]
    exact hh.faithful.2.1 _ (oTwoUpper_le L)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
        (le_normalizer_oTwoUpper L)) fun x hx => exists_pow_mem_oTwoUpper L hx
  ·
    intro x hx
    exact hh.inf_centralizer_le s.L_le_normalizer_V s.hyp.module.2.2
      ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVO) hx.2⟩
  ·
    intro g hg
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
    have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
    obtain ⟨hyZ, hyV⟩ := Subgroup.mem_inf.mp hy
    rw [mem_conjSub, inv_inv] at hyV
    have hw1 : g * y * g⁻¹ ≠ 1 := by
      intro hw
      apply hy1'
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, hw]; group
    obtain ⟨l, hl, hlw⟩ := s.natural.exists_conj_eq hyV hyZ.2 hw1 hy1'
    set x := l * g with hx
    have hxy : x * y * x⁻¹ = y := by
      rw [show x * y * x⁻¹ = l * (g * y * g⁻¹) * l⁻¹ by rw [hx]; group, hlw]
    have hxN : x ∈ Subgroup.normalizer (Z₁ : Set G) := by
      by_contra hxN
      have hti := hTI x (Subgroup.mem_top x) hxN
      have hmem : y ∈ Z₁ ⊓ CFSG.conjugate Z₁ x := by
        refine ⟨hyZ, y, hyZ, ?_⟩
        show x⁻¹ * y * x⁻¹⁻¹ = y
        calc x⁻¹ * y * x⁻¹⁻¹ = x⁻¹ * (x * y * x⁻¹) * x := by rw [inv_inv, hxy]
          _ = y := by group
      rw [hti, Subgroup.mem_bot] at hmem
      exact hy1' hmem
    have hconj : conjSub g⁻¹ V = conjSub x⁻¹ V := by
      ext u
      rw [mem_conjSub, mem_conjSub, inv_inv, inv_inv]
      have hlV := s.L_le_normalizer_V hl
      constructor
      · intro hu
        have := (Subgroup.mem_normalizer_iff.mp hlV _).mp hu
        rwa [show l * (g * u * g⁻¹) * l⁻¹ = x * u * x⁻¹ by rw [hx]; group] at this
      · intro hu
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) _).mp hu
        rwa [show l⁻¹ * (x * u * x⁻¹) * l⁻¹⁻¹ = g * u * g⁻¹ by rw [hx]; group] at this
    have hab := habel _ hH₁Z le_rfl
    rw [hconj, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ conjClosure V (Subgroup.normalizer (Z₁ : Set G)) := by
      rw [SetLike.mem_coe, mem_conjSub, inv_inv] at hw
      have := mem_conjClosure (Subgroup.inv_mem _ hxN) hw
      rwa [show x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w by group] at this
    have hv' : v ∈ conjClosure V (Subgroup.normalizer (Z₁ : Set G)) := le_conjClosure V _ hv
    have := hab.1
    have := mul_comm (⟨w, hw'⟩ : ↥(conjClosure V (Subgroup.normalizer (Z₁ : Set G)))) ⟨v, hv'⟩
    exact congrArg Subtype.val this
  ·
    refine lt_of_le_of_ne inf_le_right fun heq => ?_
    obtain ⟨v, hv⟩ := c.ε_bij.2 ![0, 1]
    have hvZ : (v : G) ∈ Z₁ := by rw [heq]; exact v.2
    have := (hmemZ₁ v).mp hvZ
    rw [hv] at this
    exact one_ne_zero this
  ·
    intro W hW1 hW2 hWN
    have hDW : D ≤ Subgroup.normalizer (W : Set G) := by
      intro d hd
      refine hWN (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨hDL hd,
        s.D_le_normalizer_Z₁ hI hd⟩, orderOf d, ?_, pow_orderOf_eq_one d⟩))
      have h1 : orderOf d ∣ Nat.card D := by
        rw [← Subgroup.orderOf_mk d hd]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat s.hyp.notation59.2.1.2.1 h1
    by_cases hWZ : W = Z₁
    · exact Or.inl hWZ
    right
    obtain ⟨w, hwW, hwZ⟩ : ∃ w ∈ W, w ∉ Z₁ := by
      by_contra hcon
      exact hWZ (le_antisymm (fun w hw => by
        by_contra hw'
        exact hcon ⟨w, hw, hw'⟩) hW1)
    have hwV : w ∈ V := hW2 hwW
    have hw1 : c.ε ⟨w, hwV⟩ 1 ≠ 0 := fun h0 => hwZ ((hmemZ₁ ⟨w, hwV⟩).mpr h0)
    refine le_antisymm hW2 fun v hv => ?_
    by_cases hv1 : c.ε ⟨v, hv⟩ 1 = 0
    · exact hW1 ((hmemZ₁ ⟨v, hv⟩).mpr hv1)
    obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c (div_ne_zero hv1 hw1)
    have hdw : (d : G) * w * (d : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hDW hdD) w).mp hwW
    have hdwV : (d : G) * w * (d : G)⁻¹ ∈ V := hW2 hdw
    have hε : c.ε ⟨(d : G) * w * (d : G)⁻¹, hdwV⟩ 1 = c.ε ⟨v, hv⟩ 1 := by
      have h1 : c.ε ⟨(d : G) * w * (d : G)⁻¹, hdwV⟩ = c.act d (c.ε ⟨w, hwV⟩) := by
        rw [c.act_ε]
        exact congrArg c.ε (Subtype.ext (by rw [conjAct_apply_coe]))
      rw [h1, hd, div_mul_cancel₀ _ hw1]
    have hq : v * ((d : G) * w * (d : G)⁻¹)⁻¹ ∈ W := by
      refine hW1 ((hmemZ₁ ⟨_, V.mul_mem hv (V.inv_mem hdwV)⟩).mpr ?_)
      have := hεinv ⟨v, hv⟩ ⟨_, hdwV⟩
      have e : (⟨v * ((d : G) * w * (d : G)⁻¹)⁻¹, V.mul_mem hv (V.inv_mem hdwV)⟩ : ↥V) =
          ⟨v, hv⟩ * (⟨_, hdwV⟩ : ↥V)⁻¹ := rfl
      rw [e, this, Pi.sub_apply, hε, sub_self]
    have := W.mul_mem hq hdw
    rwa [inv_mul_cancel_right] at this
  ·
    refine sup_le ((oTwoRes_le _).trans ((s.inf_normalizer_le hI hF c).trans
      (sup_le_sup_right hTH D))) (hTH.trans le_sup_left)
  ·
    refine charTwo_of_inH' hh.qtke hh.sylow ⟨hTH.trans le_sup_left, fun hb => ?_⟩
    have hZn : H ⊔ D ≤ Subgroup.normalizer (Z : Set G) := by
      refine sup_le (hHZ.trans (Subgroup.centralizer_le_normalizer _)) ?_
      exact s.hyp.notation59.2.1.1.trans ((hh.borelL_le_normalizer_T_of_odd hI s.odd).trans
        normalizer_le_normalizer_Z)
    have hZT : Z ≤ T := fun z hz => (mem_quasithinOmegaOneCenter_iff.mp hz).1
    have hZ2 : IsPGroup 2 Z := (hh.isSylowTwoOf le_top).2.1.to_le hZT
    have hZO : Z ≤ pCoreOf 2 (H ⊔ D) :=
      le_pCoreOf_of_le_normalizer 2 (hZT.trans (hTH.trans le_sup_left)) hZn hZ2
    rw [hb] at hZO
    exact s.Z₁_ne_bot (eq_bot_iff.mpr (inf_le_left.trans hZO))
  ·
    set N := coreIn (centralizerMod Z₁ (H ⊔ D) V) (H ⊔ D) with hNdef
    have hNH : N ≤ H ⊔ D := coreIn_le_left _ _
    have hHN : H ⊔ D ≤ Subgroup.normalizer (N : Set G) := le_normalizer_coreIn _ _
    have hNC : N ≤ centralizerMod Z₁ (H ⊔ D) V := coreIn_le_right _ _
    have hNV : ∀ y ∈ N, y ∈ Subgroup.normalizer (V : Set G) := by
      intro y hy
      obtain ⟨-, -, hyc⟩ := hNC hy
      apply mem_normalizer_of_forall_conj_mem'
      intro u hu
      have h1 : y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
      rw [h1]
      exact V.mul_mem (hyc u hu).2 hu
    have hKH : K ≤ H := oTwoUpper_le H
    have hHeq : H = K ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' (hh.isSylowTwoOf hTH)
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_oTwoUpper H)

    have hNK : N ⊓ K ≤ pCoreOf 2 K := by
      have hsimp : IsSimpleGroup (O2Q K) := s.hyp.isSimple_K
      have hNKK : N ⊓ K ≤ K := inf_le_right
      have hKN : K ≤ Subgroup.normalizer ((N ⊓ K : Subgroup G) : Set G) := by
        intro k hk
        apply mem_normalizer_of_forall_conj_mem'
        intro x hx
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hHN (Subgroup.mem_sup_left (hKH hk))) x).mp hx.1,
          K.mul_mem (K.mul_mem hk hx.2) (K.inv_mem hk)⟩
      have hn : ((N ⊓ K).subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNKK).mpr hKN
      have hmap : (((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
        hn.map _ (QuotientGroup.mk'_surjective _)
      rcases hsimp.eq_bot_or_eq_top_of_normal
        (((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
      · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
        intro x hx
        have hxP : (⟨x, hNKK hx⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
          exact hb hx
        exact ⟨_, hxP, rfl⟩
      · exfalso

        have hodd : ∀ k ∈ K, Odd (orderOf k) → k ∈ N := by
          intro k hk hko
          have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨k, hk⟩ ∈
              ((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
            rw [ht]; exact Subgroup.mem_top _
          obtain ⟨n', hn', hn'k⟩ := hmem
          have hq : n'⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by
            rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
            change (QuotientGroup.mk' (CFSG.pCore 2 ↥K) n')⁻¹ *
              QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ = 1
            rw [hn'k, inv_mul_cancel]
          obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup ⟨_, hq⟩

          set Q := (N ⊓ K).subgroupOf K with hQ
          have hk1 : ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) ^ 2 ^ j = 1 := by
            have e : ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) = ((n'⁻¹ * ⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) := by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
                (QuotientGroup.eq_one_iff n').mpr hn', inv_one, one_mul]
            rw [e, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
            have := congrArg Subtype.val hj
            simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
            rw [this]
            exact Q.one_mem
          have hko0 : Odd (orderOf (⟨k, hk⟩ : ↥K)) := by
            rw [Subgroup.orderOf_mk]
            exact hko
          have hko' : Odd (orderOf ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q)) :=
            Odd.of_dvd_nat hko0 (orderOf_map_dvd (QuotientGroup.mk' Q) _)
          have hk2 : orderOf ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) = 1 := by
            have h1 := orderOf_dvd_of_pow_eq_one hk1
            exact Nat.Coprime.eq_one_of_dvd
              (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hko')) h1
          have := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hk2)
          exact (Subgroup.mem_subgroupOf.mp this).1
        have hKN' : K ≤ N := by
          rw [hKdef, oTwoUpper, Subgroup.closure_le]
          rintro x ⟨hx, hxo⟩
          exact hodd x (mem_oTwoUpper_of_odd hx hxo) hxo
        apply hHM
        rw [hHeq]
        exact sup_le (fun k hk => s.normalizer_V_le_M h323 (hNV k (hKN' hk)))
          (hh.T_le)

    have hDK : D ≤ Subgroup.normalizer (K : Set G) := s.D_le_normalizer
    have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
      s.hyp.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI s.odd)
    have hDH : D ≤ Subgroup.normalizer (H : Set G) := by
      intro d hd
      apply mem_normalizer_of_forall_conj_mem'
      intro x hx
      rw [hHeq] at hx ⊢
      have hx' : x ∈ (K : Set G) * (T : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T hTK]
        exact hx
      obtain ⟨k, hk, t, ht, rfl⟩ := hx'
      have e : d * (k * t) * d⁻¹ = (d * k * d⁻¹) * (d * t * d⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hDK hd) k).mp hk)
        ((Subgroup.mem_normalizer_iff.mp (hDT hd) t).mp ht)
    have hBH : B ≤ H := s.hyp.notation59.1.1.trans inf_le_right
    have hBC := s.B_le_centralizer_F4 h5114 hI hB3 c
    have hodd1 : ∀ y ∈ N, Odd (orderOf y) → y = 1 := by
      intro y hyN hyodd
      have hyV := hNV y hyN
      have hyM : y ∈ M := s.normalizer_V_le_M h323 hyV
      have hyHD : y ∈ (H : Set G) * (D : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left H D hDH]
        exact hNH hyN
      obtain ⟨h₀, hh₀, d, hd, rfl⟩ := hyHD
      have hDM : D ≤ M := hDL.trans hh.L_le
      have hh₀M : h₀ ∈ M := by
        have := M.mul_mem hyM (M.inv_mem (hDM hd))
        rwa [mul_inv_cancel_right] at this
      obtain ⟨t, ht, b, hb, rfl⟩ := s.exists_mem_T_mem_B ⟨hh₀M, hh₀⟩
      set tn : Subgroup.normalizer (V : Set G) :=
        ⟨t, s.le_normalizer_V (Subgroup.mem_sup_right ht)⟩
      set bn : Subgroup.normalizer (V : Set G) :=
        ⟨b, Subgroup.centralizer_le_normalizer _ (hBC hb)⟩
      set dn : Subgroup.normalizer (V : Set G) := ⟨d, s.L_le_normalizer_V (hDL hd)⟩
      have hbact : ∀ w, c.act bn w = w := (c.mem_centralizer_iff bn).mp (hBC hb)
      have hyact : ∀ w, (c.act (tn * bn * dn) w) 1 = w 1 := by
        intro w
        obtain ⟨u, rfl⟩ := c.ε_bij.2 w
        have hyc := (hNC hyN).2.2 u u.2
        rw [c.act_ε]
        set u' := conjAct V (tn * bn * dn) u with hu'
        have hu'c : ((u' * u⁻¹ : ↥V) : G) ∈ Z₁ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hu', conjAct_apply_coe]
          exact hyc
        have h1 := (hmemZ₁ (u' * u⁻¹)).mp hu'c
        rw [hεinv, Pi.sub_apply, sub_eq_zero] at h1
        exact h1
      have hdact : ∀ w, (c.act dn w) 1 = w 1 := by
        intro w
        have h1 := hyact w
        rw [c.act_mul, c.act_mul, hbact, s.T_act_snd hI c tn ht] at h1
        exact h1
      have hd1 : d = 1 := s.D_eq_one_of_act hI c hd hdact
      subst hd1
      simp only [mul_one] at hyN hyodd ⊢
      have hyH : t * b ∈ H := H.mul_mem (hTH ht) (hBH hb)
      have hyK : t * b ∈ K := mem_oTwoUpper_of_odd hyH hyodd
      have hyO := hNK ⟨hyN, hyK⟩
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 K) ⟨_, hyO⟩
      have hj' : (t * b) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h1 := orderOf_dvd_of_pow_eq_one hj'
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hyodd)) h1)

    refine le_pCoreOf_of_le_normalizer 2 hNH hHN ?_
    rintro ⟨x, hx⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hord : orderOf (x ^ 2 ^ k) = m := by
      rw [orderOf_pow' x (pow_ne_zero k two_ne_zero), hkm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    refine ⟨k, Subtype.ext ?_⟩
    have := hodd1 (x ^ 2 ^ k) (N.pow_mem hx _) (hord ▸ hm)
    simpa using this
  ·
    by_contra hne
    obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have heq := s.eq_M h323 hM'.1 (le_sup_left.trans hM'.2)
    exact hHM (heq ▸ (le_sup_left.trans (le_sup_right.trans hM'.2)))

end Setup5_1_17Odd

end CFSG.Quasithin.H13
