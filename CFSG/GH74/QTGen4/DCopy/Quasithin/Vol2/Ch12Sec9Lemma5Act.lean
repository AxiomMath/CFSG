module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Act
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Final1291

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L1295A

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure Am_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ H₁ : Subgroup G) :
    Prop where

  h1222 : Stmt12_2_2_F4

  h37 : A37ForSQTK

  h38 : A38ForSQTK

  h39 : A39ForSQTK

  cx : Cx1291 G T L V n

  v1 : IsTSub T V V₁ 1

  ab : IsMulCommutative ↥(u128 V V₁)

  hstar : IsHStar T (Subgroup.normalizer (L : Set G)) H₁

  nV₁ : H₁ ≤ Subgroup.normalizer (V₁ : Set G)

  nL₁ : H₁ ≤ Subgroup.normalizer (lOne L V₁ : Set G)

  comm : ⁅lOne L V₁, oTwoUpper H₁⁆ ≤ pCoreOf 2 (lOne L V₁)

variable {T L V : Subgroup G} {n : ℕ} {V₁ H₁ : Subgroup G}

namespace Am_F4
open CFSG.Quasithin.H13.L1295A.Am_F4

variable (A : Am_F4 G T L V n V₁ H₁)
include A

theorem T_le_F4 : T ≤ H₁ := A.hstar.1.1

theorem le_normalizer_F4 : H₁ ⊔ lOne L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  sup_le A.nV₁ lOne_le_normalizer

theorem nLOne_F4 : H₁ ⊔ lOne L V₁ ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
  sup_le A.nL₁ Subgroup.le_normalizer

theorem V_le_T_F4 : V ≤ T := (A.cx.hyp.hyp.le_and_normalizes_F4 A.h1222).1

theorem V₁_ne_bot_F4 : V₁ ≠ ⊥ := by
  intro hb
  have h1 := A.v1.2.1
  rw [hb, Subgroup.card_bot] at h1
  norm_num at h1

theorem isHz_F4 : IsHzOne T L V₁ (H₁ ⊔ lOne L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₁H : V₁ ≤ H₁ ⊔ lOne L V₁ :=
    ((A.v1.1.trans A.V_le_T_F4).trans A.T_le_F4).trans le_sup_left
  have hV₁p : IsPGroup 2 V₁ := A.cx.hyp.hyp.sylow.1.to_le (A.v1.1.trans A.V_le_T_F4)
  have hO : V₁ ≤ pCoreOf 2 (H₁ ⊔ lOne L V₁) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV₁H A.le_normalizer_F4 hV₁p
  refine ⟨⟨sup_le le_sup_right (A.T_le_F4.trans le_sup_left), fun hb => A.V₁_ne_bot_F4 ?_⟩,
    A.le_normalizer_F4, fun hle => A.hstar.2.1 (le_sup_left.trans hle)⟩
  exact le_bot_iff.1 (hb ▸ hO)

theorem hF_F4 : HypF98 T V L V₁ V (H₁ ⊔ lOne L V₁) :=
  L1286.hypF98_of_abelian_F4 A.h1222 A.h37 A.h38 A.h39 A.cx.hyp A.v1 A.ab A.isHz_F4

theorem centralizerMod_eq_F4 :
    centralizerMod V₁ (H₁ ⊔ lOne L V₁) (conjClosure V (H₁ ⊔ lOne L V₁)) =
      pCoreOf 2 (H₁ ⊔ lOne L V₁) :=
  lemma12_8_4_four_F4 A.h1222 A.h37 A.h38 A.h39 G T L V n A.cx.hyp V₁ _ A.v1 A.isHz_F4

theorem pCoreOf_lOne_le_F4 : pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 (H₁ ⊔ lOne L V₁) :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_right)
    (A.nLOne_F4.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem elemAb_F4 : IsElemAbelian 2 (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  A.hF_F4.toHypF91.isElemAbelian_tilde

theorem secMk_mem_normalizer_F4 (x : ↥(H₁ ⊔ lOne L V₁)) :
    secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, A.le_normalizer_F4 x.2⟩ ∈
      Subgroup.normalizer
        ((tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)) :
          Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :
            Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
  secMk_mem_normalizer_secImg (le_normalizer_conjClosure V _ x.2)

omit A in

@[expose] noncomputable def rho_F4 (A : Am_F4 G T L V n V₁ H₁) :
    ↥(H₁ ⊔ lOne L V₁) →* MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  (conjAct _).comp
    (((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp
      (Subgroup.inclusion A.le_normalizer_F4)).codRestrict _ A.secMk_mem_normalizer_F4)

theorem rho_apply_F4 (x : ↥(H₁ ⊔ lOne L V₁))
    (u : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
    ((A.rho_F4 x u : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk _ V₁ ⟨x, A.le_normalizer_F4 x.2⟩ * u *
        (secMk _ V₁ ⟨x, A.le_normalizer_F4 x.2⟩)⁻¹ :=
  conjAct_apply_coe' _ _ u

theorem uH_le_F4 : conjClosure V (H₁ ⊔ lOne L V₁) ≤ Subgroup.normalizer (V₁ : Set G) :=
  A.hF_F4.toHypF91.conjClosure_Vp_le_pCoreOf.trans
    ((LieType.BorelTits.pCoreOf_le 2 _).trans A.le_normalizer_F4)

omit A in

@[expose] def uMk_F4 (A : Am_F4 G T L V n V₁ H₁) {w : G} (hw : w ∈ conjClosure V (H₁ ⊔ lOne L V₁)) :
    ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  ⟨secMk _ V₁ ⟨w, A.uH_le_F4 hw⟩, secMk_mem_secImg hw⟩

theorem exists_uMk_F4 (u : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
    ∃ w, ∃ hw : w ∈ conjClosure V (H₁ ⊔ lOne L V₁), A.uMk_F4 hw = u := by
  obtain ⟨⟨w, hwN⟩, hw, hwu⟩ := mem_secImg.1 u.2
  exact ⟨w, hw, Subtype.ext hwu⟩

theorem rho_uMk_eq_iff_F4 (x : ↥(H₁ ⊔ lOne L V₁)) {w : G}
    (hw : w ∈ conjClosure V (H₁ ⊔ lOne L V₁)) :
    A.rho_F4 x (A.uMk_F4 hw) = A.uMk_F4 hw ↔ (x : G) * w * (x : G)⁻¹ * w⁻¹ ∈ V₁ := by
  have key : A.rho_F4 x (A.uMk_F4 hw) = A.uMk_F4 hw ↔
      secMk _ V₁ ⟨x, A.le_normalizer_F4 x.2⟩ * secMk _ V₁ ⟨w, A.uH_le_F4 hw⟩ =
        secMk _ V₁ ⟨w, A.uH_le_F4 hw⟩ * secMk _ V₁ ⟨x, A.le_normalizer_F4 x.2⟩ := by
    rw [← Subtype.coe_inj, rho_apply_F4]
    constructor
    · intro h
      simp only [uMk_F4] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    · intro h
      simp only [uMk_F4]
      rw [mul_inv_eq_iff_eq_mul]
      exact h
  rw [key]
  constructor
  · intro h
    exact commutator_mem_of_secMk_commute
      (x := (⟨(x : G), A.le_normalizer_F4 x.2⟩ : ↥(Subgroup.normalizer (V₁ : Set G))))
      (y := (⟨w, A.uH_le_F4 hw⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))) h
  · intro h
    exact secMk_comm_of_commutator_mem
      (x := (⟨(x : G), A.le_normalizer_F4 x.2⟩ : ↥(Subgroup.normalizer (V₁ : Set G))))
      (y := (⟨w, A.uH_le_F4 hw⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))) h

theorem rho_eq_one_iff_F4 (x : ↥(H₁ ⊔ lOne L V₁)) :
    A.rho_F4 x = 1 ↔ (x : G) ∈ pCoreOf 2 (H₁ ⊔ lOne L V₁) := by
  rw [← A.centralizerMod_eq_F4]
  constructor
  · intro h
    refine ⟨x.2, A.le_normalizer_F4 x.2, fun w hw => ?_⟩
    rw [← A.rho_uMk_eq_iff_F4 x hw, h]
    rfl
  · rintro ⟨-, -, h⟩
    refine MulEquiv.ext fun u => ?_
    obtain ⟨w, hw, rfl⟩ := A.exists_uMk_F4 u
    exact (A.rho_uMk_eq_iff_F4 x hw).2 (h w hw)

theorem rho_comm_F4 {x y : ↥(H₁ ⊔ lOne L V₁)}
    (h : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 (H₁ ⊔ lOne L V₁)) :
    A.rho_F4 x * A.rho_F4 y = A.rho_F4 y * A.rho_F4 x := by
  have h1 : A.rho_F4 (x * y * x⁻¹ * y⁻¹) = 1 := (A.rho_eq_one_iff_F4 _).2 h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc A.rho_F4 x * A.rho_F4 y = (A.rho_F4 x * A.rho_F4 y * (A.rho_F4 x)⁻¹ * (A.rho_F4 y)⁻¹) * A.rho_F4 y *
        A.rho_F4 x := by group
    _ = A.rho_F4 y * A.rho_F4 x := by rw [h1, one_mul]

theorem autOn_eq_map_F4 {X : Subgroup G} (hX : X ≤ H₁ ⊔ lOne L V₁) :
    autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) =
      (X.subgroupOf (H₁ ⊔ lOne L V₁)).map A.rho_F4 := by
  ext a
  rw [mem_autOn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x', hx'X, hx's⟩ := mem_secImg.1 hs
    refine ⟨⟨x', hX hx'X⟩, hx'X, ?_⟩
    show conjAct _ _ = conjAct _ s
    congr 1
    exact Subtype.ext hx's
  · rintro ⟨x, hxX, rfl⟩
    exact ⟨⟨_, A.secMk_mem_normalizer_F4 x⟩, secMk_mem_secImg hxX, rfl⟩

omit A in

@[expose] noncomputable def Ls_F4 (A : Am_F4 G T L V n V₁ H₁) :
    Subgroup (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :=
  ((lOne L V₁).subgroupOf (H₁ ⊔ lOne L V₁)).map A.rho_F4

theorem rho_mem_cent_of_comm_F4 {x : ↥(H₁ ⊔ lOne L V₁)}
    (hx : ∀ l ∈ lOne L V₁, l * x * l⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 (lOne L V₁)) :
    A.rho_F4 x ∈ Subgroup.centralizer (A.Ls_F4 : Set _) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  exact A.rho_comm_F4 (A.pCoreOf_lOne_le_F4 (hx l hl))

theorem rho_mem_sup_F4 (x : ↥(H₁ ⊔ lOne L V₁)) :
    A.rho_F4 x ∈ Subgroup.centralizer (A.Ls_F4 : Set _) ⊔ A.Ls_F4 := by
  have hn : n ≠ 3 := by rcases A.cx.n45 with h | h <;> omega
  set K := ((Subgroup.centralizer (A.Ls_F4 : Set _) ⊔ A.Ls_F4).comap A.rho_F4).map
    (H₁ ⊔ lOne L V₁).subtype with hK
  have hmem : ∀ y (hy : y ∈ H₁ ⊔ lOne L V₁),
      A.rho_F4 ⟨y, hy⟩ ∈ Subgroup.centralizer (A.Ls_F4 : Set _) ⊔ A.Ls_F4 → y ∈ K :=
    fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
  have hL : lOne L V₁ ≤ K := fun y hy =>
    hmem y (Subgroup.mem_sup_right hy)
      (Subgroup.mem_sup_right ⟨⟨y, Subgroup.mem_sup_right hy⟩, hy, rfl⟩)
  have hO : oTwoUpper H₁ ≤ K := by
    intro y hy
    have hyH : y ∈ H₁ ⊔ lOne L V₁ := Subgroup.mem_sup_left (oTwoUpper_le H₁ hy)
    refine hmem y hyH (Subgroup.mem_sup_left (A.rho_mem_cent_of_comm_F4 fun l hl => ?_))
    have := A.comm (Subgroup.commutator_mem_commutator hl hy)
    rwa [commutatorElement_def] at this
  have hT : T ≤ K := by
    intro t ht
    have htH : t ∈ H₁ ⊔ lOne L V₁ := Subgroup.mem_sup_left (A.T_le_F4 ht)
    obtain ⟨b, hb, hbt⟩ := lOne_inner_F4 A.h1222 A.cx.hyp hn A.v1 (A.cx.hyp.hyp.normalizes ht)
      ((A.cx.hyp.hyp.le_and_normalizes_F4 A.h1222).2 ht) (A.v1.2.2 ht)
    have hbH : b ∈ H₁ ⊔ lOne L V₁ := Subgroup.mem_sup_right hb
    have hcH : b⁻¹ * t ∈ H₁ ⊔ lOne L V₁ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbH) htH
    have hc : A.rho_F4 ⟨b⁻¹ * t, hcH⟩ ∈ Subgroup.centralizer (A.Ls_F4 : Set _) := by
      refine A.rho_mem_cent_of_comm_F4 fun l hl => ?_
      have h1 := Subgroup.inv_mem _ (hbt l hl)
      rwa [show ((b⁻¹ * t) * l * (b⁻¹ * t)⁻¹ * l⁻¹)⁻¹ = l * (b⁻¹ * t) * l⁻¹ * (b⁻¹ * t)⁻¹ by
        group] at h1
    refine hmem t htH ?_
    have e : (⟨t, htH⟩ : ↥(H₁ ⊔ lOne L V₁)) = ⟨b, hbH⟩ * ⟨b⁻¹ * t, hcH⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨⟨b, hbH⟩, hb, rfl⟩)
      (Subgroup.mem_sup_left hc)
  have hH₁ : H₁ ≤ K := by
    have hsyl : IsSylowTwoOf T H₁ := isSylowTwoOf_of_quasithinIsSylowTwo A.cx.hyp.hyp.sylow A.T_le_F4
    rw [← sup_twoResidual_eq hsyl, F6.twoResidual_eq_oTwoUpper]
    exact sup_le hT hO
  obtain ⟨x', hx', hxx'⟩ := (sup_le hH₁ hL) x.2
  have : x' = x := Subtype.ext hxx'
  rw [← this]
  exact hx'

theorem rho_mem_cent_of_le_F4 {x : ↥(H₁ ⊔ lOne L V₁)}
    (hx : (x : G) ∈ pCoreOf 2 (lOne L V₁ ⊔ T)) :
    A.rho_F4 x ∈ Subgroup.centralizer (A.Ls_F4 : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine A.rho_mem_cent_of_comm_F4 fun l hl => ?_
  set R := pCoreOf 2 (lOne L V₁ ⊔ T) with hR
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne A.cx.hyp.hyp.normalizes A.v1.2.2
  have hLT : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    sup_le Subgroup.le_normalizer hTL₁
  have hRn : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hxN := hLT (LieType.BorelTits.pCoreOf_le 2 _ hx)
  have hmemL : l * x * l⁻¹ * (x : G)⁻¹ ∈ lOne L V₁ := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN l⁻¹).1 (inv_mem hl)
    have := (lOne L V₁).mul_mem hl h1
    rwa [show l * ((x : G) * l⁻¹ * (x : G)⁻¹) = l * x * l⁻¹ * (x : G)⁻¹ by group] at this
  have hmemR : l * x * l⁻¹ * (x : G)⁻¹ ∈ R := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hRn (Subgroup.mem_sup_left hl)) x).1 hx
    exact R.mul_mem h1 (R.inv_mem hx)
  have hLR : lOne L V₁ ⊓ R ≤ pCoreOf 2 (lOne L V₁) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T).trans hRn)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  exact hLR ⟨hmemL, hmemR⟩

theorem pCoreOf_range_eq_bot_F4 : pCoreOf 2 A.rho_F4.range = ⊥ := by
  have h4 := (lemma12_8_4_of_four_F4 A.h1222 (lemma12_8_4_four_F4 A.h1222 A.h37 A.h38 A.h39)) G T L V n
    A.cx.hyp V₁ _ A.v1 A.isHz_F4
  have hred := h4.2.1.2
  have h1 := pCoreOf_autOn_eq_bot_of_isTwoReducedIn hred
  rw [A.autOn_eq_map_F4 le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h1
  exact h1

end Am_F4

end L1295A

end CFSG.Quasithin.H13
