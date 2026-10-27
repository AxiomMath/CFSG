module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2i

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable (C : Ctx_F4 G T L V H Y)
include C

theorem faithful_LA_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good_F4 C γ γ' g e₁ e₂ b) (h36 : A36ForSQTK) {LA TA : Subgroup G}
    (hLA : LA ∈ cComp (Subgroup.normalizer
      ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G)))
    (htop : autOn LA ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ⊤) (hTAsyl : quasithinIsSylowTwo TA)
    (hTAN : TA ≤ Subgroup.normalizer
      ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G)) :
    quasithinIsFaithfulLocal TA LA := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ with hAdef
  set NA := Subgroup.normalizer (A : Set G) with hNAdef
  have hAU : A ≤ conjClosure V H :=
    (C.h98.F913_3 D.s (X := V) (Y := V) (Or.inl rfl) (Or.inl rfl)).trans inf_le_left
  have hAel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => C.h98.F911_3.2 x (hAU hx)⟩
    have := C.h98.F911_3.1.is_comm.comm ⟨a, hAU a.2⟩ ⟨b, hAU b.2⟩
    have h2 : (a : G) * b = b * a := congrArg Subtype.val this
    simpa using h2
  have h8 : Nat.card A = 8 := D.card
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAel.2 x x.2)⟩
  have hLAN : LA ≤ NA := le_of_mem_cComp hLA
  set X := LA ⊔ TA with hXdef
  have hXN : X ≤ NA := sup_le hLAN hTAN
  have hTX : TA ≤ X := le_sup_right

  have hAT : A ≤ TA := (le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hA2).trans
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hTAsyl hTAN))
  have hAO : A ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 (hAT.trans hTX) hXN hA2
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h8
    norm_num at h8
  have hO : pCoreOf 2 X ≠ ⊥ := fun h => hA1 (le_bot_iff.mp (h ▸ hAO))
  let ST : Sylow 2 G := hTAsyl.1.toSylow hTAsyl.2
  have hInH : InH (ST : Subgroup G) X := ⟨hTX, hO⟩
  have hLX : LA ∈ cComp X := cComp_mem_of_le hLA le_sup_left hXN
  have htfae := lemma_1_2_10_of_a36 C.S.hyp.fsu.qtke C.S.hyp.fsu.simple C.S.hyp.fsu.nonabelian
    h36 ST hInH hLX

  let _ : CommGroup ↥A := commGroupOfElemAbelian hAel
  obtain ⟨z, -, hz1, hzT⟩ := S153E57.exists_fixed_of_isPGroup (S := autOn TA A)
    ((hTAsyl.1.comap_of_injective NA.subtype NA.subtype_injective).map (conjAct A))
    (B := ⊤) (fun _ _ _ _ => Subgroup.mem_top _) (by
      intro h
      have := Subgroup.card_top (G := ↥A)
      rw [h, Subgroup.card_bot, h8] at this
      norm_num at this) (hA2.to_subgroup ⊤)
  have hzZ : (z : G) ∈ quasithinOmegaOneCenter TA := by
    refine Subgroup.subset_closure ⟨⟨hAT z.2, ?_⟩, hAel.2 _ z.2⟩
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    have h1 := hzT (conjAct A ⟨t, hTAN ht⟩) (Subgroup.mem_map.mpr ⟨⟨t, hTAN ht⟩, ht, rfl⟩)
    have h2 := congrArg Subtype.val h1
    rw [conjAct_apply_coe'] at h2
    calc t * (z : G) = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [h2]
  have hR := isTwoReducedIn_conjClosure_of_sylowIn hTX hTAsyl.1
    (isSylowTwoOf_of_quasithinIsSylowTwo hTAsyl hTX).2.2
    (charTwo_of_inH C.S.hyp.fsu.qtke.2.1 ST hInH) (Subgroup.zpowers_le.mpr hzZ)
  have hVL : ⁅conjClosure (Subgroup.zpowers (z : G)) X, LA⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨α, hα⟩ := E8.exists_mulAut_apply_ne hAel h8 hz1
    have hαt : α ∈ autOn LA A := htop ▸ Subgroup.mem_top α
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hαt
    have hl' : (l : G) ∈ LA := hl
    apply hα
    have h1 := Subgroup.commutator_mem_commutator
      (le_conjClosure (Subgroup.zpowers (z : G)) X (Subgroup.mem_zpowers (z : G))) hl'
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
    apply Subtype.ext
    rw [conjAct_apply_coe']
    calc (l : G) * z * (l : G)⁻¹ = ((z : G) * l * (z : G)⁻¹ * (l : G)⁻¹)⁻¹ * z := by group
      _ = z := by rw [h1]; group
  have hex : ∃ W, IsTwoReducedIn X W ∧ ⁅W, LA⁆ ≠ ⊥ := ⟨_, hR, hVL⟩
  exact (htfae.out 2 1).mp hex

theorem false_of_TA_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good_F4 C γ γ' g e₁ e₂ b) (h36 : A36ForSQTK) {LA TA : Subgroup G}
    (hLA : LA ∈ cComp (Subgroup.normalizer
      ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G)))
    (htop : autOn LA ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ⊤) (hTAsyl : quasithinIsSylowTwo TA)
    (hTAN : TA ≤ Subgroup.normalizer
      ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G))
    (hTAK : TA ≤ Subgroup.normalizer (oTwoUpper (C.Pe_F4 e₂) : Set G))
    (hLAK : LA ≤ Subgroup.normalizer (oTwoUpper (C.Pe_F4 e₂) : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hL := D.lines
  set A : Subgroup G := ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ with hAdef
  set NA := Subgroup.normalizer (A : Set G) with hNAdef
  set K := oTwoUpper (C.Pe_F4 e₂) with hKdef
  set K₁ := oTwoUpper (C.Pe_F4 e₁) with hK₁def
  have hAU : A ≤ conjClosure V H :=
    (C.h98.F913_3 D.s (X := V) (Y := V) (Or.inl rfl) (Or.inl rfl)).trans inf_le_left
  have hAel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => C.h98.F911_3.2 x (hAU hx)⟩
    have := C.h98.F911_3.1.is_comm.comm ⟨a, hAU a.2⟩ ⟨b, hAU b.2⟩
    have h2 : (a : G) * b = b * a := congrArg Subtype.val this
    simpa using h2
  have h8 : Nat.card A = 8 := D.card
  have hLAN : LA ≤ NA := le_of_mem_cComp hLA

  have hf := C.faithful_LA_F4 D h36 hLA htop hTAsyl hTAN
  obtain ⟨x, hx⟩ := exists_conj_of_sylow hTAsyl C.S.hyp.fsu.sylow
  have hf' := A5.quasithinIsFaithfulLocal_map (MulAut.conj x) hf
  rw [hx] at hf'
  obtain ⟨-, ⟨-, -, -, huniq⟩, -, -⟩ := C.h1332 G T L C.S.hyp.hyp.h13 _ hf'

  have hTH : T ≤ H := Setting147.TH' C.S
  let ST : Sylow 2 G := C.S.hyp.fsu.sylow.1.toSylow C.S.hyp.fsu.sylow.2
  have hcharH : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
    charTwo_of_inH C.S.hyp.fsu.qtke.2.1 ST ⟨hTH, C.S.hz.1.2⟩
  obtain ⟨z₂, hz₂K, hz₂1, -, -⟩ := C.exists_mem_K_F4 hL.h5₂ hL.symm.ne_one₁ D.e₂E
  have hQP : pCoreOf 2 H ≤ C.Pe_F4 e₂ := fun q hq => (C.mem_Pe_F4).mpr ⟨pCoreOf_le 2 H hq, by
    rw [(FixR.rho_eq_one_iff C.h91_F4 ⟨q, pCoreOf_le 2 H hq⟩).mpr hq]
    exact Subgroup.one_mem _⟩
  have hO2K : pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    have hKP : K ≤ C.Pe_F4 e₂ := oTwoUpper_le _
    have hKH : K ≤ H := hKP.trans (C.Pe_le_H_F4 e₂)

    have hint : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_oTwoUpper _ (hKP hk),
        le_normalizer_pCoreOf 2 H (hKH hk)⟩)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    have hzc : (z₂ : G) ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨z₂.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have h1 : (z₂ : G) * q * (z₂ : G)⁻¹ * q⁻¹ ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ (hQP hq)) _).mp
          (K.inv_mem hz₂K)
        have e : (z₂ : G) * q * (z₂ : G)⁻¹ * q⁻¹ = (z₂ : G) * (q * (z₂ : G)⁻¹ * q⁻¹) := by group
        rw [e]
        exact K.mul_mem hz₂K this
      have h2 : (z₂ : G) * q * (z₂ : G)⁻¹ * q⁻¹ ∈ pCoreOf 2 H := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H z₂.2) q).mp hq
        exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hq)
      have h3 := hint ⟨h1, h2⟩
      rw [hbot, Subgroup.mem_bot] at h3
      calc q * (z₂ : G) = ((z₂ : G) * q * (z₂ : G)⁻¹ * q⁻¹)⁻¹ * z₂ * q := by group
        _ = z₂ * q := by rw [h3]; group
    exact hz₂1 ((FixR.rho_eq_one_iff C.h91_F4 z₂).mpr (hcharH hzc))

  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (pCoreOf 2 K : Set G)) :=
    ⟨_, hO2K, pCoreOf_isPGroup 2 K, rfl⟩
  obtain ⟨M, hM, hMle⟩ := exists_maxTwoLocal_ge hloc
  have hNK : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 K
  have hLAM : LA ⊔ TA ≤ M := (sup_le hLAK hTAK).trans (hNK.trans hMle)
  have hM' := quasithinIsMaxTwoLocal_map (MulAut.conj x) hM
  have hle' : LA.map (MulAut.conj x).toMonoidHom ⊔ T ≤ M.map (MulAut.conj x).toMonoidHom := by
    rw [← hx, ← Subgroup.map_sup]
    exact Subgroup.map_mono hLAM
  have hMeq := huniq _ hM' hle'
  have hMN : M = Subgroup.normalizer (LA : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq] at hMeq
    exact Subgroup.map_injective (MulAut.conj x).injective hMeq

  have hK₁K : K₁ ≤ Subgroup.normalizer (K : Set G) := by
    intro k hk
    obtain ⟨hkH, hke⟩ := (C.mem_Pe_F4).mp (oTwoUpper_le _ hk)
    refine normalizer_le_normalizer_oTwoUpper _ (C.mem_normalizer_Pe_F4 ⟨k, hkH⟩ ?_)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hke
    have hc : FixR.rho C.h91_F4 ⟨k, hkH⟩ * e₂ = e₂ * FixR.rho C.h91_F4 ⟨k, hkH⟩ := by
      rw [← hj]
      exact (Commute.zpow_left hL.comm j).eq
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers e₂
  have hK₁LA : K₁ ≤ Subgroup.normalizer (LA : Set G) := hMN ▸ (hK₁K.trans (hNK.trans hMle))

  have hcl : A = conjClosure (fsuV1 T V) LA := by
    refine le_antisymm ?_ (conjClosure_le fun l hl v hv =>
      (Subgroup.mem_normalizer_iff.mp (hLAN hl) v).mp (D.V₁_le hv))
    have hB : (conjClosure (fsuV1 T V) LA).subgroupOf A = ⊤ := by
      refine E8.eq_top_of_invariant hAel h8 ?_ ?_
      · obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
          (show fsuV1 T V ≠ ⊥ from fun h => by
            have := C.h98.card_V₁
            rw [h, Subgroup.card_bot] at this
            norm_num at this)
        intro hbot
        have : (⟨v₀, D.V₁_le hv₀⟩ : ↥A) ∈ (conjClosure (fsuV1 T V) LA).subgroupOf A :=
          le_conjClosure _ _ hv₀
        rw [hbot, Subgroup.mem_bot] at this
        exact hv₀1 (Subtype.ext (by simpa using congrArg Subtype.val this))
      · intro α a ha
        have hαt : α ∈ autOn LA A := htop ▸ Subgroup.mem_top α
        obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hαt
        show ((conjAct A l a : ↥A) : G) ∈ conjClosure (fsuV1 T V) LA
        rw [conjAct_apply_coe']
        exact (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure (fsuV1 T V) LA (show (l : G) ∈ LA from hl)) (a : G)).mp ha
    intro a ha
    have : (⟨a, ha⟩ : ↥A) ∈ (conjClosure (fsuV1 T V) LA).subgroupOf A := hB ▸ Subgroup.mem_top _
    exact this

  have hK₁N : K₁ ≤ NA := by
    intro k hk
    have hkH : k ∈ H := C.Pe_le_H_F4 e₁ (oTwoUpper_le _ hk)
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    rw [hcl] at ha ⊢
    exact conj_mem_conjClosure (hK₁LA hk) (fun v hv => by rw [C.conj_V₁_F4 hkH hv]; exact hv) a ha
  have hK₁C : K₁ ≤ Subgroup.centralizer (A : Set G) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨hyP, hyo⟩ := hy
    have hyK : y ∈ K₁ := mem_oTwoUpper_of_odd hyP hyo
    have hy5 := C.pow_five_of_odd_F4 hL.h5₁ hyP hyo
    have h1 : conjAct A ⟨y, hK₁N hyK⟩ ^ 5 = 1 := by
      rw [← map_pow]
      have : (⟨y, hK₁N hyK⟩ : ↥NA) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
      rw [this, map_one]
    have h2 : orderOf (conjAct A ⟨y, hK₁N hyK⟩) = 1 := by
      have hd5 : orderOf (conjAct A ⟨y, hK₁N hyK⟩) ∣ 5 := orderOf_dvd_of_pow_eq_one h1
      have : Finite (MulAut ↥A) :=
        Nat.finite_of_card_ne_zero (by rw [E8.card_mulAut hAel h8]; norm_num)
      have hd168 : orderOf (conjAct A ⟨y, hK₁N hyK⟩) ∣ 168 :=
        E8.card_mulAut hAel h8 ▸ orderOf_dvd_natCard _
      exact Nat.eq_one_of_dvd_coprimes (by norm_num) hd5 hd168
    exact CFSG.Quasithin.A4.conjAct_eq_one_iff.mp (orderOf_eq_one_iff.mp h2)

  obtain ⟨z₁, hz₁K, -, -, he₁z⟩ := C.exists_mem_K_F4 hL.h5₁ hL.ne_one₁ D.e₁E
  have hfix : ∀ w ∈ cw b, FixR.rho C.h91_F4 z₁ w = w := by
    intro w hw
    obtain ⟨a, rfl⟩ := C.piU_surjective_F4 w
    have hAeq : A = ((cw b).comap C.piU_F4).map (conjClosure V H).subtype := D.A_eq
    have haA : (a : G) ∈ A := by rw [hAeq]; exact ⟨a, hw, rfl⟩
    rw [← C.piU_conj_F4 z₁ a]
    congr 1
    apply Subtype.ext
    show (z₁ : G) * a * (z₁ : G)⁻¹ = a
    have := Subgroup.mem_centralizer_iff.mp (hK₁C hz₁K) a haA
    rw [← this]
    group
  have hbot : cw b = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : w ∈ cw e₁ ⊓ fixV (Subgroup.zpowers e₁) := by
      refine ⟨D.cw_le hw, mem_fixV_zpowers_iff.mpr ?_⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp he₁z
      rw [← hj]
      have h2 : ∀ n : ℕ, (FixR.rho C.h91_F4 z₁ ^ n) w = w := fun n => pow_apply_eq_self (hfix w hw) n
      rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast, h2]
      · rw [zpow_neg, zpow_natCast]
        conv_lhs => rw [← h2 n]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rwa [hL.fpf₁] at h1
  have := D.rk_cw
  rw [hbot, rk_bot] at this
  omega

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
