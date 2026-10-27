module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5W1618j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1617c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.GH74.QTGen4.U42.ModelP1
public import CFSG.GH74.QTGen4.U42.StubA4b
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Psi

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

local notation "StSL" => Assembly.LowTwoRank.StatedSL

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_lin2Block_of_baum_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hH : S.Hyp1367) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F)) {K₀ : Subgroup G}
    (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hK₀im : autOn K₀ (S.WK K) = S.plus K) (hblk : IsBlock2 (K₀ ⊔ S.Tv) K₀) {n : ℕ}
    (hn : 1 < n) (hlin : IsLin2Type K₀ n) {x : G} (hxK₀ : x ∈ K₀)
    (hxB : x ∈ Subgroup.normalizer (baum S.Tv : Set G))
    (hxW : x ∉ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G))
    (hx3 : x ^ 3 ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := S.WK K with hWdef
  have hF' := hH.hF
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF' hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) := hR.2.1
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) := hKHK.trans hHKW
  have hTW : S.Tv ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    (S.Tv_le_HK K).trans hHKW
  have hK₀W := hK₀K.trans hKW
  have hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₀K.trans hK.1
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀

  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  have hsimp : IsSimpleGroup ↥(S.plus K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo hF4.ge) e
  have h60 : Nat.card ↥(S.plus K) = 60 := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
    norm_num
  have h3 : 3 ∣ Nat.card ↥(S.plus K) := by rw [h60]; norm_num

  have hCQ := S.inf_centralizer_WK_eq hK₀W hK₀im hsimp h3 hn hlin
  set Q₀ := pCoreOf 2 K₀ with hQ₀
  have hQK₀ : Q₀ ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hQn : K₀ ≤ Subgroup.normalizer (Q₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hCW : ∀ y ∈ K₀, y ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) → y ∈ Q₀ :=
    fun y hy hyW => hCQ ▸ ⟨hy, hyW⟩
  have hQW : Q₀ ≤ Subgroup.centralizer ((W : Subgroup G) : Set G) := fun y hy => by
    rw [← hCQ] at hy
    exact hy.2

  have hsylH := S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hK.1
  have hsylX : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    B6.isSylowTwoOf_mono hsylH le_sup_right (sup_le (hK₀K.trans hKHK) (S.Tv_le_HK K))
  have hS₀ : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylX le_sup_left (sup_le Subgroup.le_normalizer hTK₀)

  obtain ⟨⟨-, -, ⟨hUQ, hU2⟩, -, -⟩, -, -⟩ := hblk
  obtain ⟨F', iF', iFt', hcard', α, -, hαk, β, -, hβk, hβe⟩ := hlin
  have hcharF' : CharP F' 2 := R3c.charP_two_of_natCard_eq_two_pow (f := n)
    (by rw [Nat.card_eq_fintype_card]; exact hcard')
  set U := blockU K₀ with hU
  have hUQ₀ : U ≤ Q₀ := hUQ.trans inf_le_left
  have hK₀NU : K₀ ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator hQn Subgroup.le_normalizer
  have hUcomm : IsMulCommutative ↥U := ⟨⟨fun u w => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (hUQ u.2).2 w (hUQ₀ w.2)).symm⟩⟩

  set x₂ := x ^ 2 with hx₂
  have hx₂K₀ : x₂ ∈ K₀ := K₀.pow_mem hxK₀ 2
  have hmemQ : ∀ y : ↥K₀, (y : G) ∈ Q₀ → y ∈ α.ker := by
    intro y hy
    rw [hαk, CFSG.pCore_eq_open]
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  have hαx3 : α ⟨x, hxK₀⟩ ^ 3 = 1 := by
    rw [← map_pow]
    exact hmemQ _ (by rw [Subgroup.coe_pow]; exact hCW _ (K₀.pow_mem hxK₀ 3) hx3)
  have hαx1 : α ⟨x, hxK₀⟩ ≠ 1 := by
    intro h
    have hk : (⟨x, hxK₀⟩ : ↥K₀) ∈ α.ker := h
    rw [hαk, CFSG.pCore_eq_open] at hk
    exact hxW (hQW ⟨_, hk, rfl⟩)
  have hx₂e : (⟨x₂, hx₂K₀⟩ : ↥K₀) = ⟨x, hxK₀⟩ ^ 2 := Subtype.ext (by rw [Subgroup.coe_pow])
  have hαx₂3 : α ⟨x₂, hx₂K₀⟩ ^ 3 = 1 := by
    rw [hx₂e, map_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hαx3, one_pow]
  have hαx₂1 : α ⟨x₂, hx₂K₀⟩ ≠ 1 := by
    intro h
    rw [hx₂e, map_pow] at h
    apply hαx1
    calc α ⟨x, hxK₀⟩ = α ⟨x, hxK₀⟩ ^ 3 * (α ⟨x, hxK₀⟩ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hαx3, h]; group

  have hx₂W : x₂ ∉ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
    intro h
    apply hxW
    have e2 : x = x ^ 3 * x₂⁻¹ := by rw [hx₂]; group
    rw [e2]
    exact Subgroup.mul_mem _ hx3 (Subgroup.inv_mem _ h)
  have hx₂3 : x₂ ^ 3 ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
    have e2 : x₂ ^ 3 = (x ^ 3) ^ 2 := by rw [hx₂, ← pow_mul, ← pow_mul]
    rw [e2]
    exact Subgroup.pow_mem _ hx3 2

  have hB : baum S.Tv = baum T := S.lemma_13_6_4.1
  have hxMV := S.lemma_13_6_5_F4 h1222 h517 ⟨hK₀G hxK₀, hB ▸ hxB⟩
  have hxa : x₂ * S.a * x₂⁻¹ = S.a := S.sq_conj_a hxMV.1 hxMV.2

  have haTv := S.a_mem_Tv
  have haW : S.a ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) := hTW haTv
  set aW : MulAut ↥W := conjAct W ⟨S.a, haW⟩ with haWdef
  have haWN : aW ∈ Subgroup.normalizer ((S.plus K : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    CFSG.Quasithin.H13.A5.autOn_le_normalizer_autOn hT
      (Setup.mem_autOn_iff.2 ⟨⟨S.a, haW⟩, haTv, rfl⟩)
  set ψ : MulAut ↥(S.plus K) := conjAct (S.plus K) ⟨aW, haWN⟩ with hψ
  have hψapp : ∀ y : ↥(S.plus K), ((ψ y : ↥(S.plus K)) : MulAut ↥W) = aW * y * aW⁻¹ :=
    fun y => InternalSec.coe_conjAct_apply _ y

  have hfixW : ∀ y : G, ∀ hy : y ∈ Subgroup.normalizer ((W : Subgroup G) : Set G),
      S.a * y * S.a⁻¹ * y⁻¹ ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) →
      aW * conjAct W ⟨y, hy⟩ * aW⁻¹ = conjAct W ⟨y, hy⟩ := by
    intro y hy hc
    have h1 : conjAct W (⟨S.a, haW⟩ * ⟨y, hy⟩ * ⟨S.a, haW⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 :=
      A4.conjAct_eq_one_iff.mpr hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    rw [haWdef]
    exact mul_inv_eq_one.mp h1

  have hvW : ∀ k : ℤ, S.v12 ^ k ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
    intro k
    refine Subgroup.zpow_mem _ ?_ k
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwG : w ∈ Subgroup.centralizer ({S.v12} : Set G) :=
      ((S.WK_le_Tv_F4 h1222 h517 hF' hK.1 hT).1 hw).2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hwG)
  set Fix : Subgroup ↥(S.plus K) := ψ.toMonoidHom.eqLocus (MonoidHom.id _) with hFix
  set S₀p : Subgroup ↥(S.plus K) := (autOn (S.Tv ⊓ K₀) W).subgroupOf (S.plus K) with hS₀p
  have hS₀pK : autOn (S.Tv ⊓ K₀) W ≤ S.plus K := hK₀im ▸ A4.autOn_mono inf_le_right
  have hx₂N : x₂ ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) := hK₀W hx₂K₀
  have hx₂Wp : conjAct W ⟨x₂, hx₂N⟩ ∈ S.plus K := by
    rw [← hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨x₂, hx₂N⟩, hx₂K₀, rfl⟩
  set y₂ : ↥(S.plus K) := ⟨conjAct W ⟨x₂, hx₂N⟩, hx₂Wp⟩ with hy₂
  have hS₀Fix : S₀p ≤ Fix := by
    intro y hy
    show ψ y = y
    apply Subtype.ext
    rw [hψapp]
    have hy' : (y : MulAut ↥W) ∈ autOn (S.Tv ⊓ K₀) W := hy
    obtain ⟨⟨s, hsN⟩, hs, hse⟩ := Setup.mem_autOn_iff.1 hy'
    rw [← hse]
    refine hfixW s hsN ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv hs.1)
    rw [← hk]
    exact hvW k
  have hy₂Fix : y₂ ∈ Fix := by
    show ψ y₂ = y₂
    apply Subtype.ext
    rw [hψapp]
    refine hfixW x₂ hx₂N ?_
    have : S.a * x₂ * S.a⁻¹ * x₂⁻¹ = 1 := by
      have h1 : S.a * x₂ = x₂ * S.a := by
        calc S.a * x₂ = (x₂ * S.a * x₂⁻¹) * x₂ := by rw [hxa]
          _ = x₂ * S.a := by group
      rw [h1]; group
    rw [this]
    exact Subgroup.one_mem _
  set H₁ : Subgroup ↥(S.plus K) := S₀p ⊔ Subgroup.zpowers y₂ with hH₁
  have hH₁Fix : H₁ ≤ Fix := sup_le hS₀Fix ((Subgroup.zpowers_le).mpr hy₂Fix)

  have hS₀card : Nat.card ↥(autOn (S.Tv ⊓ K₀) W) = 4 :=
    card_eq_four_of_isSylowTwoOf (Setup.isSylowTwoOf_autOn hS₀ hK₀W) (hK₀im ▸ h60)
  have h4H₁ : 4 ∣ Nat.card ↥H₁ := by
    have h1 : Nat.card ↥S₀p = 4 := by
      rw [hS₀p, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀pK).toEquiv, hS₀card]
    rw [← h1]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hy₂ord : orderOf y₂ = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
      have hp : (⟨x₂, hx₂N⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G))) ^ 3 =
          ⟨x₂ ^ 3, Subgroup.pow_mem _ hx₂N 3⟩ := Subtype.ext (by rw [Subgroup.coe_pow])
      rw [hp]
      exact A4.conjAct_eq_one_iff.mpr hx₂3
    · intro h
      apply hx₂W
      have h1 : conjAct W ⟨x₂, hx₂N⟩ = 1 := congrArg Subtype.val h
      exact A4.conjAct_eq_one_iff.mp h1
  have h3H₁ : 3 ∣ Nat.card ↥H₁ := by
    rw [← hy₂ord]
    have := orderOf_dvd_natCard (⟨y₂, le_sup_right (b := Subgroup.zpowers y₂)
      (Subgroup.mem_zpowers y₂)⟩ : ↥H₁)
    rwa [Subgroup.orderOf_mk] at this

  have : IsSimpleGroup ↥(S.plus K) := hsimp
  obtain ⟨e₅⟩ := CFSG.Quasithin.Dickson.nonempty_mulEquiv_alt_five_of_simple h60
  set ψ' := e₅.symm.trans (ψ.trans e₅) with hψ'
  have hψtriv : ∀ y : ↥(S.plus K), ψ y = y := by
    intro y
    have hfix' : ∀ z ∈ H₁.map e₅.toMonoidHom, ψ' z = z := by
      rintro _ ⟨h, hh, rfl⟩
      have := hH₁Fix hh
      change ψ h = h at this
      simp [hψ', this]
    have h4' : 4 ∣ Nat.card ↥(H₁.map e₅.toMonoidHom) := by
      rw [Subgroup.card_map_of_injective e₅.injective]; exact h4H₁
    have h3' : 3 ∣ Nat.card ↥(H₁.map e₅.toMonoidHom) := by
      rw [Subgroup.card_map_of_injective e₅.injective]; exact h3H₁
    have := eq_of_mulAut_alt_five_of_fix h4' h3' hfix' (e₅ y)
    simp only [hψ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    exact e₅.injective this

  have hstepA : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ Q₀ := by
    intro k hk
    have hkN := hK₀W hk
    have hkp : conjAct W ⟨k, hkN⟩ ∈ S.plus K := by
      rw [← hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
    have h1 := congrArg Subtype.val (hψtriv ⟨_, hkp⟩)
    rw [hψapp] at h1

    have hm : k⁻¹ * S.a * k * S.a⁻¹ ∈ K₀ := by
      have e2 : k⁻¹ * S.a * k * S.a⁻¹ = k⁻¹ * (S.a * k * S.a⁻¹) := by group
      rw [e2]
      exact K₀.mul_mem (K₀.inv_mem hk) ((Subgroup.mem_normalizer_iff.mp (hTK₀ haTv) k).mp hk)
    refine hCW _ hm ?_
    have hkN' : k⁻¹ * S.a * k * S.a⁻¹ ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) haW)
        hkN) (Subgroup.inv_mem _ haW)
    refine (A4.conjAct_eq_one_iff
      (g := (⟨_, hkN'⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G))))).mp ?_
    have e3 : (⟨k⁻¹ * S.a * k * S.a⁻¹, hkN'⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G))) =
        ⟨k, hkN⟩⁻¹ * ⟨S.a, haW⟩ * ⟨k, hkN⟩ * ⟨S.a, haW⟩⁻¹ := rfl
    have h1' : aW * conjAct W ⟨k, hkN⟩ * aW⁻¹ = conjAct W ⟨k, hkN⟩ := h1
    rw [e3, map_mul, map_mul, map_mul, map_inv, map_inv, ← haWdef]
    calc (conjAct W ⟨k, hkN⟩)⁻¹ * aW * conjAct W ⟨k, hkN⟩ * aW⁻¹
        = (conjAct W ⟨k, hkN⟩)⁻¹ * (aW * conjAct W ⟨k, hkN⟩ * aW⁻¹) := by group
      _ = 1 := by rw [h1']; group
  have hcommU : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ U :=
    comm_mem_commutator_of_perfect hQK₀ hQn hK₀p (hTK₀ haTv) hstepA

  let ρ : ↥K₀ →* MulAut ↥U := (conjAct U).comp (Subgroup.inclusion hK₀NU)
  have hρ : ∀ (g : ↥K₀) (u : ↥U), ((ρ g u : ↥U) : G) = g * u * (g : G)⁻¹ := fun g u =>
    InternalSec.coe_conjAct_apply _ u
  let δ : ↥K₀ → ↥U := fun k => ⟨(k : G)⁻¹ * S.a * k * S.a⁻¹, hcommU k k.2⟩
  have hδ : ∀ g h, δ (g * h) = ρ h⁻¹ (δ g) * δ h := by
    intro g h
    apply Subtype.ext
    rw [Subgroup.coe_mul, hρ]
    simp only [δ, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  set Z₀ : Subgroup ↥U := (Subgroup.zpowers S.v12).subgroupOf U with hZ₀def
  have hZ₀ : ∀ g, ∀ z ∈ Z₀, ρ g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hρ]
    have hzv : (z : G) ∈ Subgroup.zpowers S.v12 := hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzv
    rw [← hk]
    have hgv : Commute (g : G) S.v12 := Subgroup.mem_centralizer_singleton_iff.mp (hK₀G g.2)
    rw [(hgv.zpow_right k).eq, mul_inv_cancel_right]
  set D : Subgroup ↥K₀ := (S.Tv ⊓ K₀).subgroupOf K₀ with hDdef
  have hD : ∀ d ∈ D, δ d ∈ Z₀ := by
    intro d hd
    have hdT : (d : G) ∈ S.Tv := (Subgroup.mem_subgroupOf.mp hd).1
    show (d : G)⁻¹ * S.a * d * S.a⁻¹ ∈ Subgroup.zpowers S.v12
    have h1 := S.comm_a_Tv (S.Tv.inv_mem hdT)
    have e : (d : G)⁻¹ * S.a * d * S.a⁻¹ = (S.a * (d : G)⁻¹ * S.a⁻¹ * (d : G)⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hodd : ¬ 2 ∣ D.index := hS₀.2.2
  have hperf : commutator ↥K₀ = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hK₀p)
  have hA2 : ∀ u : ↥U, u ^ 2 = 1 := fun u =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hU2 u u.2)
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index hA2 ρ δ hδ Z₀ hZ₀ D hD hodd hperf
  have hmk : ∀ k : ↥K₀, (k : G)⁻¹ * S.a * k * S.a⁻¹ = (k : G)⁻¹ * m * k * (m : G)⁻¹ := by
    intro k
    have h1 := congrArg Subtype.val (hm k)
    rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv] at h1
    simp only [δ, Subgroup.coe_inv, inv_inv] at h1
    rw [h1]

  have hmx : (x₂ : G) * m * x₂⁻¹ = m := by
    have h1 := hmk ⟨x₂, hx₂K₀⟩
    have h2 : x₂⁻¹ * S.a * x₂ * S.a⁻¹ = 1 := by
      have h3 : S.a * x₂ = x₂ * S.a := by
        calc S.a * x₂ = (x₂ * S.a * x₂⁻¹) * x₂ := by rw [hxa]
          _ = x₂ * S.a := by group
      calc x₂⁻¹ * S.a * x₂ * S.a⁻¹ = x₂⁻¹ * (S.a * x₂) * S.a⁻¹ := by group
        _ = 1 := by rw [h3]; group
    have h4 : x₂⁻¹ * (m : G) * x₂ * (m : G)⁻¹ = 1 := by rw [← h2]; exact h1.symm
    calc (x₂ : G) * m * x₂⁻¹ = x₂ * (x₂⁻¹ * (m : G) * x₂ * (m : G)⁻¹)⁻¹ * x₂⁻¹ * m := by group
      _ = m := by rw [h4]; group
  have hmZ : (m : G) ∈ blockZ K₀ :=
    mem_blockZ_of_conj_eq (y := ⟨x₂, hx₂K₀⟩) hβk hβe hαx₂3 hαx₂1 hmx

  have hK₀a : K₀ ≤ Subgroup.centralizer ({S.a} : Set G) := by
    intro k hk
    have hmc : (m : G) ∈ Subgroup.centralizer (K₀ : Set G) := hmZ.2
    have h1 := hmk ⟨k, hk⟩
    have h2 : k * m = m * k := Subgroup.mem_centralizer_iff.mp hmc k hk
    have h3 : k⁻¹ * (m : G) * k * (m : G)⁻¹ = 1 := by
      calc k⁻¹ * (m : G) * k * (m : G)⁻¹ = k⁻¹ * (m * k) * (m : G)⁻¹ := by group
        _ = 1 := by rw [← h2]; group
    have h4 : k⁻¹ * S.a * k * S.a⁻¹ = 1 := h1.trans h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h5 : S.a * k = k * S.a := by
      calc S.a * k = k * (k⁻¹ * S.a * k * S.a⁻¹) * S.a := by group
        _ = k * S.a := by rw [h4]; group
    exact h5.symm

  have hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) := by
    intro hK₀z
    apply S.not_le_centralizer_z_of_inYz hK hT
    intro k hk
    have hkW := hKW hk
    have hkp : conjAct W ⟨k, hkW⟩ ∈ autOn K₀ W := by
      rw [hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨k, hkW⟩, hk, rfl⟩
    obtain ⟨⟨k₀, hk₀N⟩, hk₀, hk₀e⟩ := Setup.mem_autOn_iff.1 hkp
    have hc : k₀⁻¹ * k ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
      have h1 : conjAct W ((⟨k₀, hk₀N⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G)))⁻¹ *
          ⟨k, hkW⟩) = 1 := by
        rw [map_mul, map_inv, hk₀e, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have hzW : S.z ∈ W := le_conjClosure _ _ (Subgroup.mem_zpowers _)
    have h1 : k₀⁻¹ * k ∈ Subgroup.centralizer ({S.z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc _ hzW).symm
    have e : k = k₀ * (k₀⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hK₀z hk₀) h1
  obtain ⟨g, -, hga⟩ := S.exists_conj_a
  refine S.not_le_centralizer_conj_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF' hK₀G hK₀
    hTK₀ hz g (fun t ht => by rw [hga]; exact S.comm_a_Tv ht) ?_
  rw [hga]
  exact hK₀a

end Setting

end CFSG.Quasithin.H13.A5
