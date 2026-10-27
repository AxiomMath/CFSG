module

public import CFSG.ClassicalInvolution.Q3.TL3S8BEta

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section C8

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowData

variable (hd : TightSylowData K z S W)
include hd

theorem le_sec19X : W ≤ sec19X K z := by
  obtain ⟨η, S', hη, -, hWη, hηS⟩ := hd.exists_eta
  rw [hWη]
  refine iSup₂_le fun A hA => ?_
  exact tight_le_sec19X_of_mem (Or.inl (hη.1 hA).1) ((hηS A hA).trans hd.hSz)

theorem mem_centralizer_of_mem_inf_sec19Y {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxY : x ∈ sec19Y K z) :
    x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨-, -, -, hc⟩ := hxY
  have h1 : ⁅x, r⁆ ∈ oddCoreOf K := hc r hr.2
  have h2 : ⁅x, r⁆ ∈ (S : Subgroup G) ⊓ K := by
    rw [commutatorElement_def]
    have h3 : x * r * x⁻¹ ∈ (S : Subgroup G) ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp (hd.le_normalizer_inf hxS) r).mp hr
    exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hr)
  have h4 : ⁅x, r⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
    ((S.isPGroup'.to_le inf_le_left).to_le (Subgroup.zpowers_le.mpr h2))
  rw [commutatorElement_def] at h4
  calc r * x = (x * r * x⁻¹ * r⁻¹)⁻¹ * (x * r) := by group
    _ = x * r := by rw [h4, inv_one, one_mul]

theorem inf_sec19Y_eq :
    W ⊓ sec19Y K z = W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact fun x hx => ⟨hx.1, hd.mem_centralizer_of_mem_inf_sec19Y (hd.hWS hx.1) hx.2⟩
  · rintro x ⟨hxW, hxC⟩
    refine ⟨hxW, hd.le_sec19X hxW, hd.mem_normalizer_of_mem_W hxW,
      mem_normalizer_oddCoreOf_of_mem_normalizer (hd.mem_normalizer_of_mem_W hxW), ?_⟩
    intro l hl
    have hΩ := hd.tight.hypGen
    refine Sec6Gen.centSylow hΩ (CoreAssembly.mem_conjClass_self K) hd.isSylow2In_inf
      ((S.isPGroup'.to_le hd.hWS).to_le (Subgroup.zpowers_le.mpr hxW)) ?_ ?_
      l hl x (Subgroup.mem_zpowers x)
    · intro y hy
      exact mem_normalizer_iff_conjSub_eq.mp
        ((Subgroup.zpowers_le.mpr (hd.mem_normalizer_of_mem_W hxW)) hy)
    · intro r hr v hv
      have hvC : v ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
        (Subgroup.zpowers_le.mpr hxC) hv
      exact Subgroup.mem_centralizer_iff.mp hvC r hr

end TightSylowData

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem inf_inf_sec19Y_eq_bot : V ⊓ (W ⊓ sec19Y K z) = ⊥ := by
  rw [eq_bot_iff, ← hd.inf_sec19Y_eq_bot]
  intro x hx
  exact ⟨hx.1, hx.2.2⟩

theorem card_sup_inf_sec19Y :
    Nat.card ↥(V ⊔ (W ⊓ sec19Y K z)) = Nat.card V * Nat.card ↥(W ⊓ sec19Y K z) :=
  S1911.card_sup_of_comm (fun a ha b hb => hd.comm_of_mem a (hd.leW ha) b hb.1)
    hd.inf_inf_sec19Y_eq_bot

theorem sup_inf_sec19Y_eq : W = V ⊔ (W ⊓ sec19Y K z) := by
  have hd0 := hd.toTightSylowData
  have hcomm := hd0.comm_of_mem
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hle := S1911.card_le_card_inf_centralizer_mul hUR hd0.card_inf_eq (W := W)
    (fun w hw => hd0.le_normalizer_inf (hd.hWS hw)) (fun w hw u hu => hcomm w hw u hu.2)
  rw [← hd0.inf_sec19Y_eq, hd.card_inf_eq_card] at hle
  have hsub : V ⊔ (W ⊓ sec19Y K z) ≤ W := sup_le hd.leW inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hsub ?_).symm
  rw [hd.card_sup_inf_sec19Y, mul_comm]
  exact hle

theorem card_inf_sec19Y : Nat.card ↥(W ⊓ sec19Y K z) = Nat.card V := by
  have h1 := hd.card_eq_mul
  rw [hd.card_inf_eq_card] at h1
  have h2 : Nat.card W = Nat.card V * Nat.card ↥(W ⊓ sec19Y K z) := by
    conv_lhs => rw [hd.sup_inf_sec19Y_eq]
    exact hd.card_sup_inf_sec19Y
  have hV : 0 < Nat.card V := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hV (h2.symm.trans h1)

end TightSylowDataT

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem invol_mem_W {e : G} (heW : e ∈ W) (he2 : e * e = 1) (he1 : e ≠ 1) :
    e = z ∨ e = t ∨ e = t * z := by
  have hd0 := hd.toTightSylowData
  have hcomm := hd0.comm_of_mem
  have hI := hd.tight.isUniqueInvolution
  have hle : V ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have e1 : v * x * v⁻¹ = x := by rw [hcomm v (hd.leW hv) x hx.2]; group
      rw [e1]
      exact hx
    · intro hx
      have e1 : v * x * v⁻¹ = x := by
        have h := hcomm v (hd.leW hv) _ hx.2
        have h2 : v * (v * x * v⁻¹) = v * x := by rw [h]; group
        exact mul_left_cancel h2
      rw [← e1]
      exact hx
  have hmem : e ∈ ((K ⊓ W ⊔ V : Subgroup G) : Set G) := by
    rw [← hd.sup_eq_inf_sup]
    exact heW
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hmem
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hmem
  have huv : u * v = v * u := hcomm u hu.2 v (hd.leW hv)
  have h1 : u * u = (v * v)⁻¹ := by
    have : u * u * (v * v) = 1 := by
      calc u * u * (v * v) = u * (u * v) * v := by group
        _ = u * (v * u) * v := by rw [huv]
        _ = u * v * (u * v) := by group
        _ = 1 := he2
    exact eq_inv_of_mul_eq_one_left this
  have h2 : u * u ∈ K ⊓ W ⊓ V := ⟨Subgroup.mul_mem _ hu hu, h1 ▸ Subgroup.inv_mem _
    (Subgroup.mul_mem _ hv hv)⟩
  rw [hd.inf_inf_eq_bot, Subgroup.mem_bot] at h2
  have h3 : v * v = 1 := by
    have := h1
    rw [h2] at this
    exact inv_eq_one.mp this.symm
  have hu' := hI.unique u hu.1 h2
  have hv' := hd.invL.unique v (hd.le_member hv) h3
  have hzt : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp
    (hd.hSz (hd.hWS hd.mem_W))
  rcases hu' with hu1 | hu1 <;> rcases hv' with hv1 | hv1
  · exact absurd (by rw [hu1, hv1, one_mul]) he1
  · exact Or.inr (Or.inl (by rw [hu1, hv1, one_mul]))
  · exact Or.inl (by rw [hu1, hv1, mul_one])
  · exact Or.inr (Or.inr (by rw [hu1, hv1, hzt]))

theorem exists_sylow_member :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ (∀ w ∈ W, conjSub w RL = RL) ∧ V ≤ RL ∧
      Nat.card RL = 2 * Nat.card V := by
  have hd0 := hd.toTightSylowData
  have hΩ := hd.tight.hypGen
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (hd0.le_centralizer_of_mem hd.mem_W).trans
      (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL)
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  obtain ⟨RL, hRL, hRLW⟩ := exists_sylow_normalized hW2 hWL
  have hWRL : W ≤ Subgroup.normalizer (RL : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRLW w hw)
  have hP := IsPGroup.to_sup_of_normal_right' hW2 hRL.2.1 hWRL
  have hVRL : V ≤ RL := by
    have h1 : RL ⊔ V = RL := hRL.eq_of_le (hP.to_le (sup_le le_sup_right
      (hd.leW.trans le_sup_left))) (sup_le hRL.1 hd.le_member) le_sup_left
    rw [← h1]
    exact le_sup_right
  obtain ⟨R', -, J, hJ, hR'J, hVR', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hd.memV
  have hJL : J = L :=
    Sec6Gen.eq_of_mem_USet hΩ hd.memV hJ hd.memL (hVR'.trans hR'J.1) hd.le_member
  subst hJL
  exact ⟨RL, hRL, hRLW, hVRL, by rw [hRL.natCard_eq hR'J, hcard]⟩

theorem inf_centralizer_inf_eq_bot {RL : Subgroup G} (hRL : IsSylow2In RL L) :
    W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (RL : Set G) = ⊥ := by
  have hd0 := hd.toTightSylowData
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hRLmem : RL ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hd.memL hRL
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨i, hi⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup (S.isPGroup'.to_le hd.hWS) hx.1.1
  obtain ⟨e, he, he2, he1⟩ := AscL62.exists_involution_pow hx1 hi
  have heW : e ∈ W := (Subgroup.zpowers_le.mpr hx.1.1) he
  have heC : e ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx.1.2) he
  have heRL : e ∈ Subgroup.centralizer (RL : Set G) := (Subgroup.zpowers_le.mpr hx.2) he
  rcases hd.invol_mem_W heW he2 he1 with rfl | rfl | rfl
  · refine hd.tight.not_le_centralizer_of_mem_rSet hd.memL (CoreAssembly.mem_conjClass_self K)
      hd.member_ne hI hRLmem hRL.1 ?_
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp heRL r hr
  · exact hd.not_mem_centralizer_inf heC
  · obtain ⟨r, hr, hrt⟩ := hd.exists_conj_eq_mul
    have hrL : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
    have hne : conjSub r L ≠ K := by
      intro h
      have h1 : t * z = z := (h ▸ hrL).eq hI
      apply hd.invL.ne_one
      calc t = t * z * z⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    exact hd0.not_mem_centralizer_inf_of_member (hΩ.conjInvariant r L hd.memL) hne hrL heC

theorem isCyclic_inf_sec19Y : IsCyclic ↥(W ⊓ sec19Y K z) := by
  have hd0 := hd.toTightSylowData
  have hcomm := hd0.comm_of_mem
  obtain ⟨RL, hRL, hRLW, hVRL, hcardL⟩ := hd.exists_sylow_member
  have : IsCyclic ↥V := hd.isCyclic_V
  refine S1911.isCyclic_of_inf_centralizer_eq_bot hVRL hcardL (fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRLW x hx.1)) (fun x hx v hv =>
    hcomm x hx.1 v (hd.leW hv)) ?_
  rw [hd0.inf_sec19Y_eq]
  exact hd.inf_centralizer_inf_eq_bot hRL

end TightSylowDataT


variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem inf_member_eq : (S : Subgroup G) ⊓ L = V := by
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hVSL : V ≤ (S : Subgroup G) ⊓ L := le_inf (hd.leW.trans hd.hWS) hd.le_member
  have hle : (S : Subgroup G) ⊓ L ≤ L ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun x hx => ⟨hx.2, hd.hSz hx.1⟩
  obtain ⟨V'', hV'', hSLV''⟩ := IsSylow2In.exists_ge (S.isPGroup'.to_le inf_le_left) hle
  have htV'' : t ∈ V'' := hSLV'' (hVSL hd.memT)
  have htwin : L ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, z', hz'K, hz'L⟩
    exact hd.ne ((hd.invL.eq hz'L).trans (hz'K.eq hI))
  have h4 := hd.four_le_card_V
  have hVV'' : V ≤ V'' := hVSL.trans hSLV''
  have hcardV : Nat.card V ≤ Nat.card V'' := Subgroup.card_le_of_le hVV''
  rcases Sec6Gen.l6_2Gen G _ hΩ K (CoreAssembly.mem_conjClass_self K) z hI L hd.memL htwin t
    hd.invL V'' hV'' htV'' with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
  · exfalso
    rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hd.invL.sq)
      hd.invL.ne_one] at hcardV
    omega
  · exfalso
    rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hd.invL.sq)
      hd.invL.ne_one] at hcardV
    omega
  · have hcard := Sec6Gen.natCard_eq_of_mem_USet hΩ hd.memL hV3 hd.memV
      (hV''.1.trans inf_le_left) hd.le_member
    have heq : V = V'' := Subgroup.eq_of_le_of_card_ge hVV'' hcard.le
    exact le_antisymm (heq ▸ hSLV'') hVSL
  · exfalso
    refine S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hd.memL
      (CoreAssembly.mem_conjClass_self K) hd.member_ne hV4 (hV''.1.trans inf_le_left) ?_
    rw [hd.tight.normEq]
    exact hV''.1.trans inf_le_right

theorem mem_normalizer_V_of_mem_A {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) : a ∈ Subgroup.normalizer (V : Set G) := by
  have haL : a ∈ Subgroup.normalizer (L : Set G) :=
    hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hat
  rw [← hd.inf_member_eq, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxL⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ haS hxS) (Subgroup.inv_mem _ haS),
      (Subgroup.mem_normalizer_iff.mp haL x).mp hxL⟩
  · rintro ⟨hxS, hxL⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp haL x).mpr hxL⟩
    have h1 : a⁻¹ * (a * x * a⁻¹) * a ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haS) hxS) haS
    have e : a⁻¹ * (a * x * a⁻¹) * a = x := by group
    rwa [e] at h1

theorem exists_sylow_member_of_mem_A {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ conjSub a RL = RL ∧ (∀ w ∈ W, conjSub w RL = RL) ∧
      V ≤ RL ∧ Nat.card RL = 2 * Nat.card V := by
  have hd0 := hd.toTightSylowData
  have hΩ := hd.tight.hypGen
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (hd0.le_centralizer_of_mem hd.mem_W).trans
      (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL)
  have haL : a ∈ Subgroup.normalizer (L : Set G) :=
    hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hat
  have hT : Subgroup.zpowers a ⊔ W ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr haS) hd.hWS
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ W) := S.isPGroup'.to_le hT
  obtain ⟨RL, hRL, hRLT⟩ := exists_sylow_normalized hT2
    (sup_le (Subgroup.zpowers_le.mpr haL) hWL)
  have hTRL : Subgroup.zpowers a ⊔ W ≤ Subgroup.normalizer (RL : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRLT w hw)
  have hP := IsPGroup.to_sup_of_normal_right' hT2 hRL.2.1 hTRL
  have hVRL : V ≤ RL := by
    have h1 : RL ⊔ V = RL := hRL.eq_of_le (hP.to_le (sup_le le_sup_right
      (hd.leW.trans (le_sup_right.trans le_sup_left)))) (sup_le hRL.1 hd.le_member) le_sup_left
    rw [← h1]
    exact le_sup_right
  obtain ⟨R', -, J, hJ, hR'J, hVR', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hd.memV
  have hJL : J = L :=
    Sec6Gen.eq_of_mem_USet hΩ hd.memV hJ hd.memL (hVR'.trans hR'J.1) hd.le_member
  subst hJL
  exact ⟨RL, hRL, hRLT a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)),
    fun w hw => hRLT w (Subgroup.mem_sup_right hw), hVRL, by rw [hRL.natCard_eq hR'J, hcard]⟩

theorem inf_inf_centralizer_eq_bot {RL : Subgroup G} (hRL : IsSylow2In RL L) :
    K ⊓ W ⊓ Subgroup.centralizer (RL : Set G) = ⊥ := by
  have hI := hd.tight.isUniqueInvolution
  have hRLmem : RL ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hd.memL hRL
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have h2 : 2 ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    have h0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    omega
  have hzx : z ∈ Subgroup.zpowers x := S1911.mem_of_le_member hI
    (Subgroup.zpowers_le.mpr hx.1.1)
    ((S.isPGroup'.to_le hd.hWS).to_le (Subgroup.zpowers_le.mpr hx.1.2)) h2
  have hzC : z ∈ Subgroup.centralizer (RL : Set G) := (Subgroup.zpowers_le.mpr hx.2) hzx
  refine hd.tight.not_le_centralizer_of_mem_rSet hd.memL (CoreAssembly.mem_conjClass_self K)
    hd.member_ne hI hRLmem hRL.1 ?_
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hzC r hr

theorem comm_V_of_mem_A {a : G} (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) : ∀ v ∈ V, a * v = v * a := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := hd.exists_sylow_member_of_mem_A haS hat
  obtain ⟨b, hbR, hbV⟩ := S1911.exists_mem_not_mem hcardRL
  have hcomm := hd.comm_of_mem
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hcomm x (hd.leW hx) y (hd.leW hy)
  intro v hv
  obtain ⟨u, hu, hdef⟩ := S1911.exists_defect_eq hVRL hcardRL (C := K ⊓ W)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.2))
    (fun x hx y hy => hcomm x hx.2 y (hd.leW hy)) (hd.inf_inf_centralizer_eq_bot hRL)
    hd.card_inf_eq_card.ge hbR hbV hv
  have hau : a * u = u * a :=
    (Subgroup.mem_centralizer_iff.mp haC u ⟨hd.hWS hu.2, hu.1⟩).symm
  have h := S1911.conj_eq_of_defect hVRL hcardRL hVc hbR hbV
    (mem_normalizer_iff_conjSub_eq.mpr haRL) (hd.mem_normalizer_V_of_mem_A haS hat) hv
    (fun x hx => hcomm u hu.2 x (hd.leW hx)) hdef hau
  calc a * v = a * v * a⁻¹ * a := by group
    _ = v * a := by rw [h]

theorem exists_mul_eq_of_mem_A {a : G} (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ ∃ w ∈ W ⊓ Subgroup.centralizer
      (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
        a * w⁻¹ ∈ Subgroup.centralizer (RL : Set G) := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := hd.exists_sylow_member_of_mem_A haS hat
  obtain ⟨b, hbR, hbV⟩ := S1911.exists_mem_not_mem hcardRL
  have hcomm := hd.comm_of_mem
  have haV := hd.comm_V_of_mem_A haS haC hat
  have haN : a ∈ Subgroup.normalizer (RL : Set G) := mem_normalizer_iff_conjSub_eq.mpr haRL
  have hda : b⁻¹ * (a * b * a⁻¹) ∈ V := S1911.inv_mul_conj_mem hVRL hcardRL hbR haN haV
  have hcardZ : Nat.card V ≤ Nat.card ↥(W ⊓ Subgroup.centralizer
      (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) := by
    rw [← hd.inf_sec19Y_eq, hd.card_inf_sec19Y]
  obtain ⟨w, hw, hwdef⟩ := S1911.exists_defect_eq hVRL hcardRL
    (C := W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.1))
    (fun x hx y hy => hcomm x hx.1 y (hd.leW hy)) (hd.inf_centralizer_inf_eq_bot hRL)
    hcardZ hbR hbV hda
  refine ⟨RL, hRL, w, hw, ?_⟩
  exact S1911.mem_centralizer_of_defect_eq hVRL hcardRL hbR hbV
    (mem_normalizer_iff_conjSub_eq.mpr (hWRL w hw.1)) haV
    (fun x hx => hcomm w hw.1 x (hd.leW hx)) hwdef.symm

end TightSylowDataT


end C8

end CFSG.ClassicalInvolution.Q3
