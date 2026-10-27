module

public import CFSG.Quasithin.H13.A5W1619a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem commutator_sup_blockZ_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hshort : IsShort2 K₀) :
    ⁅K₀, conjClosure S.V1 (K₀ ⊔ S.Tv)⁆ ≤ blockU K₀ ∧
      ⁅K₀, conjClosure S.V1 (K₀ ⊔ S.Tv)⁆ ≤ S.WK K ∧
      ⁅K₀, conjClosure S.V1 (K₀ ⊔ S.Tv)⁆ ⊔ blockZ K₀ = blockU K₀ := by
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀

  have hHK : K₀ ⊔ S.Tv ≤ S.HK K :=
    sup_le (hK₀K.trans (le_sup_left.trans le_sup_left)) (S.Tv_le_HK K)
  have hVW : conjClosure S.V1 (K₀ ⊔ S.Tv) ≤ S.WK K := by
    rw [S.WK_eq hT]
    exact conjClosure_mono le_rfl hHK
  have hzT : S.z ∈ S.Tv :=
    (Subgroup.closure_le _).mpr (fun x hx => hx.1.1) (S.V1_le_omega_Tv (Subgroup.mem_zpowers _))
  have hVH : conjClosure S.V1 (K₀ ⊔ S.Tv) ≤ K₀ ⊔ S.Tv := by
    refine conjClosure_le fun h hh x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (K₀ ⊔ S.Tv).mul_mem ((K₀ ⊔ S.Tv).mul_mem hh
      (Subgroup.mem_sup_right (S.Tv.zpow_mem hzT k))) ((K₀ ⊔ S.Tv).inv_mem hh)
  have hHV : K₀ ⊔ S.Tv ≤ Subgroup.normalizer
      ((conjClosure S.V1 (K₀ ⊔ S.Tv) : Subgroup G) : Set G) := le_normalizer_conjClosure _ _
  have hHK₀ : K₀ ⊔ S.Tv ≤ Subgroup.normalizer (K₀ : Set G) := sup_le Subgroup.le_normalizer hTK₀
  set V' := conjClosure S.V1 (K₀ ⊔ S.Tv) with hV'def
  have hV2 : ∀ x ∈ V', x ^ 2 = 1 := fun x hx => hR.2.2.1.2 x (hVW hx)

  have hzV : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hK₀V : ¬ K₀ ≤ Subgroup.centralizer (V' : Set G) := fun h =>
    hz fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h hk) _ hzV).symm

  have hQK : blockQ K₀ ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hQn : K₀ ≤ Subgroup.normalizer (blockQ K₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hcK₀ : ∀ a ∈ V', ∀ k ∈ K₀, k⁻¹ * a * k * a⁻¹ ∈ K₀ ⊓ V' := by
    intro a ha k hk
    have haK : a * k * a⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hHK₀ (hVH ha)) k).mp hk
    have hkV : k⁻¹ * a * k ∈ V' := by
      have := (Subgroup.mem_normalizer_iff.mp (hHV (Subgroup.mem_sup_left (K₀.inv_mem hk)))
        a).mp ha
      rwa [inv_inv] at this
    refine ⟨?_, V'.mul_mem hkV (V'.inv_mem ha)⟩
    have e : k⁻¹ * a * k * a⁻¹ = k⁻¹ * (a * k * a⁻¹) := by group
    rw [e]
    exact K₀.mul_mem (K₀.inv_mem hk) haK
  have hKVQ : K₀ ⊓ V' ≤ blockQ K₀ := by
    refine le_pCoreOf_of_normalizes inf_le_left (fun k hk => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, hHV (Subgroup.mem_sup_left hk)⟩
    · intro g
      exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hV2 _ g.2.2, Subgroup.coe_one])⟩
  have hcomm : ∀ a ∈ V', ∀ k ∈ K₀, k⁻¹ * a * k * a⁻¹ ∈ blockU K₀ := fun a ha =>
    comm_mem_commutator_of_perfect hQK hQn hK₀p (hHK₀ (hVH ha)) fun k hk => hKVQ (hcK₀ a ha k hk)
  set X : Subgroup G := ⁅K₀, V'⁆ with hXdef
  have hXU : X ≤ blockU K₀ := by
    rw [hXdef, Subgroup.commutator_le]
    intro k hk a ha
    have := hcomm a ha k⁻¹ (K₀.inv_mem hk)
    rwa [inv_inv, ← commutatorElement_def] at this
  have hXV : X ≤ V' := by
    rw [hXdef, Subgroup.commutator_le]
    intro k hk a ha
    have hkV : k * a * k⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (hHV (Subgroup.mem_sup_left hk)) a).mp ha
    rw [commutatorElement_def]
    exact V'.mul_mem hkV (V'.inv_mem ha)
  have hXn : K₀ ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer
      (fun k hk => hHV (Subgroup.mem_sup_left hk))

  obtain ⟨-, -, -, -, -, hirr⟩ := hshort
  have hUK : blockU K₀ ≤ K₀ :=
    (Subgroup.commutator_mono hQK le_rfl).trans (A3.commutator_self_le K₀)
  have hZK : blockZ K₀ ≤ K₀ := inf_le_left.trans hUK
  have hUn : K₀ ≤ Subgroup.normalizer (blockU K₀ : Set G) :=
    le_normalizer_commutator hQn Subgroup.le_normalizer
  have hZn : K₀ ≤ Subgroup.normalizer (blockZ K₀ : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hUn hk, mem_normalizer_centralizer_of_mem_normalizer (Subgroup.le_normalizer hk)⟩
  have hXZn : K₀ ≤ Subgroup.normalizer ((X ⊔ blockZ K₀ : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXn hk),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZn hk)]
  refine ⟨hXU, hXV.trans hVW, ?_⟩
  rcases hirr (X ⊔ blockZ K₀) le_sup_right (sup_le hXU inf_le_left) hXZn with hXZ | hXZ
  · exfalso
    have hXZ' : X ≤ blockZ K₀ := hXZ ▸ le_sup_left
    apply hK₀V
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ∀ k ∈ K₀, k⁻¹ * a * k * a⁻¹ ∈ blockZ K₀ := fun k hk => hXZ' (by
      have : ⁅k⁻¹, a⁆ ∈ X := Subgroup.commutator_mem_commutator (K₀.inv_mem hk) ha
      rwa [commutatorElement_def, inv_inv] at this)
    have h2 := comm_mem_commutator_of_perfect hZK hZn hK₀p (hHK₀ (hVH ha)) h1 k hk
    have hZc : ⁅blockZ K₀, K₀⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    rw [hZc, Subgroup.mem_bot] at h2
    calc a * k = k * (k⁻¹ * a * k * a⁻¹) * a := by group
      _ = k * a := by rw [h2, mul_one]
  · exact hXZ

theorem autOn_blockQ_le_centralizer_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} [IsMulCommutative ↥(S.WK K)] (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {K₀ : Subgroup G} (hK₀K : K₀ ≤ K)
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hshort : IsShort2 K₀) :
    ∀ r ∈ autOn (blockQ K₀) (S.WK K), ∀ g ∈ autOn K₀ (S.WK K), r * g = g * r := by
  obtain ⟨hXU, hXW, hXZ⟩ := S.commutator_sup_blockZ_F4 h1222 h517 hF hK hT hK₀K hK₀ hTK₀ hz hshort
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hQK : blockQ K₀ ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hUK : blockU K₀ ≤ K₀ :=
    (Subgroup.commutator_mono hQK le_rfl).trans (A3.commutator_self_le K₀)
  have hZK : blockZ K₀ ≤ K₀ := inf_le_left.trans hUK
  set X : Subgroup G := ⁅K₀, conjClosure S.V1 (K₀ ⊔ S.Tv)⁆ with hXdef
  set A := autOn K₀ (S.WK K) with hAdef

  have hcXZ : ∀ a ∈ X, ∀ b ∈ blockZ K₀, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ((hXU.trans hUK) ha)
  have hU : ∀ u (hu : u ∈ blockU K₀), ∀ g ∈ A, conjAct (S.WK K) ⟨u, hK₀W (hUK hu)⟩ * g =
      g * conjAct (S.WK K) ⟨u, hK₀W (hUK hu)⟩ := by
    intro u hu g hg
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 hg
    have hu' : u ∈ X ⊔ blockZ K₀ := by rw [hXZ]; exact hu
    obtain ⟨x, hx, c, hc, hxc⟩ := S1417.exists_mul_of_mem_sup_of_commute hcXZ hu'
    have hxW : x ∈ S.WK K := hXW hx
    have hxN : x ∈ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hxW
    have hcN := hK₀W (hZK hc)
    have e : (⟨u, hK₀W (hUK hu)⟩ : ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G))) =
        ⟨x, hxN⟩ * ⟨c, hcN⟩ := Subtype.ext hxc.symm
    have hx1 : conjAct (S.WK K) ⟨x, hxN⟩ = 1 := by
      refine InternalSec.conjAct_eq_one_of_mem_centralizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : ↥(S.WK K)) ⟨x, hxW⟩)
    have hck : (⟨c, hcN⟩ : ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G))) * ⟨k, hkN⟩ =
        ⟨k, hkN⟩ * ⟨c, hcN⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hc.2 k hk).symm
    rw [e, map_mul, hx1, one_mul, ← map_mul, hck, map_mul]

  have hAp : ⁅A, A⁆ = A := by rw [hAdef, ← autOn_commutator hK₀W hK₀W, hK₀p]
  set Z := A ⊓ Subgroup.centralizer (A : Set (MulAut ↥(S.WK K))) with hZdef
  have hZA : Z ≤ A := inf_le_left
  have hZAn : A ≤ Subgroup.normalizer (Z : Set (MulAut ↥(S.WK K))) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      mem_normalizer_centralizer_of_mem_normalizer (Subgroup.le_normalizer hg)⟩
  intro r hr g hg
  have hrA : r ∈ A := A4.autOn_mono hQK hr
  obtain ⟨⟨q, hqN⟩, hq, rfl⟩ := Setup.mem_autOn_iff.1 hr
  have h1 : ∀ g ∈ A, g⁻¹ * conjAct (S.WK K) ⟨q, hqN⟩ * g * (conjAct (S.WK K) ⟨q, hqN⟩)⁻¹ ∈ Z := by
    intro g hg
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 hg
    have hu : k⁻¹ * q * k * q⁻¹ ∈ blockU K₀ := by
      have : ⁅k⁻¹, q⁆ ∈ ⁅K₀, blockQ K₀⁆ := Subgroup.commutator_mem_commutator (K₀.inv_mem hk) hq
      rw [Subgroup.commutator_comm] at this
      rwa [commutatorElement_def, inv_inv] at this
    have e : conjAct (S.WK K) ⟨k⁻¹ * q * k * q⁻¹, hK₀W (hUK hu)⟩ =
        (conjAct (S.WK K) ⟨k, hkN⟩)⁻¹ * conjAct (S.WK K) ⟨q, hqN⟩ * conjAct (S.WK K) ⟨k, hkN⟩ *
          (conjAct (S.WK K) ⟨q, hqN⟩)⁻¹ := by
      have e₀ : (⟨k⁻¹ * q * k * q⁻¹, hK₀W (hUK hu)⟩ :
          ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G))) =
          (⟨k, hkN⟩)⁻¹ * ⟨q, hqN⟩ * ⟨k, hkN⟩ * (⟨q, hqN⟩)⁻¹ := rfl
      rw [e₀, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [← e]
    refine Subgroup.mem_inf.mpr ⟨Setup.mem_autOn_iff.2 ⟨_, hUK hu, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g' hg'
    exact (hU _ hu g' hg').symm
  have h2 := comm_mem_commutator_of_perfect hZA hZAn hAp (Subgroup.le_normalizer hrA) h1 g hg
  have hZc : ⁅Z, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  rw [hZc, Subgroup.mem_bot] at h2
  calc conjAct (S.WK K) ⟨q, hqN⟩ * g
      = g * (g⁻¹ * conjAct (S.WK K) ⟨q, hqN⟩ * g * (conjAct (S.WK K) ⟨q, hqN⟩)⁻¹) *
        conjAct (S.WK K) ⟨q, hqN⟩ := by group
    _ = g * conjAct (S.WK K) ⟨q, hqN⟩ := by rw [h2, mul_one]

theorem pCoreOf_autOn_le_centralizer_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} [IsMulCommutative ↥(S.WK K)] (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {K₀ : Subgroup G} (hK₀K : K₀ ≤ K)
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hshort : IsShort2 K₀)
    (hcases : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₀ n) ∨ IsAltType K₀ 5) :
    ∀ r ∈ pCoreOf 2 (autOn K₀ (S.WK K)), ∀ g ∈ autOn K₀ (S.WK K), r * g = g * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen := S.autOn_blockQ_le_centralizer_F4 h1222 h517 hF hK hT hK₀K hK₀ hTK₀ hz hshort
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  set A := autOn K₀ (S.WK K) with hAdef
  set φ := InternalSec.autOnHom hK₀W with hφdef
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hK₀W

  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [hAdef, autOn_eq_bot_iff hK₀W] at h
    exact hz fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h hk) _ hzW).symm

  set N : Subgroup ↥K₀ := (CFSG.Open.pCore 2 ↥A).comap φ with hNdef
  have hNn : N.Normal := (CFSG.LieType.BorelTits.pCore_normal 2).comap φ

  have hAp : ⁅A, A⁆ = A := by rw [hAdef, ← autOn_commutator hK₀W hK₀W, hK₀p]
  have hfalse : ∀ {Q : Type} [Group Q] (α : ↥K₀ →* Q), α.ker = CFSG.pCore 2 ↥K₀ →
      N.map α = ⊤ → False := by
    intro Q _ α hαk htop
    have hdec : ∀ x : ↥K₀, ∃ m ∈ N, m⁻¹ * x ∈ CFSG.pCore 2 ↥K₀ := by
      intro x
      have : α x ∈ N.map α := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨m, hm, hmx⟩ := this
      refine ⟨m, hm, ?_⟩
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
    have hO : (CFSG.Open.pCore 2 ↥K₀).map φ ≤ CFSG.Open.pCore 2 ↥A :=
      CFSG.LieType.BorelTits.map_pCore_le 2 φ hφs
    have htopA : ∀ a : ↥A, a ∈ CFSG.Open.pCore 2 ↥A := by
      intro a
      obtain ⟨x, rfl⟩ := hφs a
      obtain ⟨m, hm, hmx⟩ := hdec x
      have e : x = m * (m⁻¹ * x) := by group
      rw [e, map_mul]
      refine Subgroup.mul_mem _ hm (hO ⟨_, ?_, rfl⟩)
      rw [← CFSG.pCore_eq_open]
      exact hmx
    have h2A : IsPGroup 2 ↥A := fun a => by
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥A) ⟨a, htopA a⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Group.IsNilpotent ↥A := h2A.isNilpotent
    have hpc : perfectCore A = ⊥ := (isSolvable_iff_perfectCore_eq_bot A).mp inferInstance
    rw [perfectCore_eq_self_of_perfect hAp] at hpc
    exact hA1 hpc
  have hNO : N ≤ CFSG.pCore 2 ↥K₀ := by
    rcases hcases with ⟨n, hn, F, _, _, hF', α, hαs, hαk, -⟩ | ⟨α, hαs, hαk, -⟩
    · have hs := isSimpleGroup_sl2 hF' hn
      have hNα : (N.map α).Normal := hNn.map α hαs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map α) with h | h
      · rw [← hαk]
        exact (Subgroup.map_eq_bot_iff _).mp h
      · exact (hfalse α hαk h).elim
    · have hs : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hNα : (N.map α).Normal := hNn.map α hαs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map α) with h | h
      · rw [← hαk]
        exact (Subgroup.map_eq_bot_iff _).mp h
      · exact (hfalse α hαk h).elim

  intro r hr g hg
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
  obtain ⟨k, hk⟩ := hφs r'
  have hkN : k ∈ N := by
    show φ k ∈ CFSG.Open.pCore 2 ↥A
    rw [hk]
    exact hr'
  have hkQ : (k : G) ∈ blockQ K₀ := ⟨k, by rw [← CFSG.pCore_eq_open]; exact hNO hkN, rfl⟩
  have hrQ : ((r' : ↥A) : MulAut ↥(S.WK K)) ∈ autOn (blockQ K₀) (S.WK K) := by
    rw [← hk]
    exact Setup.mem_autOn_iff.2 ⟨⟨k, hK₀W k.2⟩, hkQ, rfl⟩
  exact hcen _ hrQ g hg

end Setting

end CFSG.Quasithin.H13.A5
