module

public import CFSG.ClassicalInvolution.AschTight.S1911EtaY3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem inf_member_eq (hd : Sec19DataT p f K z S W L t V) : (S : Subgroup G) ⊓ L = V := by
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  have hI := isUniqueInvolution_of_tight htb
  have hVSL : V ≤ (S : Subgroup G) ⊓ L := le_inf (hd.leW.trans hd.hWS) (le_member hd)
  have hle : (S : Subgroup G) ⊓ L ≤ L ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun x hx => ⟨hx.2, hd.hSz hx.1⟩
  obtain ⟨V'', hV'', hSLV''⟩ := IsSylow2In.exists_ge (S.isPGroup'.to_le inf_le_left) hle
  have htV'' : t ∈ V'' := hSLV'' (hVSL hd.memT)
  have htwin : L ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, z', hz'K, hz'L⟩
    exact hd.ne ((hd.invL.eq hz'L).trans (hz'K.eq hI))
  have h4 := four_le_card hd
  have hVV'' : V ≤ V'' := hVSL.trans hSLV''
  have hcardV : Nat.card V ≤ Nat.card V'' := Subgroup.card_le_of_le hVV''
  rcases Asc77.l6_2 p f hp hd.tight.branch.five G _ hΩ K (CoreAssembly.mem_conjClass_self K) z
    hI L hd.memL htwin t hd.invL V'' hV'' htV'' with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
  · exfalso
    rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hd.invL.sq)
      hd.invL.ne_one] at hcardV
    omega
  · exfalso
    rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hd.invL.sq)
      hd.invL.ne_one] at hcardV
    omega
  · have hcard := hΩ.natCard_eq_of_mem_USet hp hd.memL hV3 hd.memV (hV''.1.trans inf_le_left)
      (le_member hd)
    have heq : V = V'' := Subgroup.eq_of_le_of_card_ge hVV'' hcard.le
    exact le_antisymm (heq ▸ hSLV'') hVSL
  · exfalso
    refine not_le_normalizer_of_mem_rSet hd.tight.edgeless hd.memL
      (CoreAssembly.mem_conjClass_self K) (member_ne hd) hV4 (hV''.1.trans inf_le_left) ?_
    rw [normalizer_eq_centralizer_of_tight htb]
    exact hV''.1.trans inf_le_right

variable {a : G}

omit [Finite G] [IsSimpleGroup G] in
theorem mem_centralizer_inf_of_mem_A
    (ha : a ∈ Subgroup.centralizer
      ((((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t) : Subgroup G) : Set G)) :
    a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) ha

omit [Finite G] [IsSimpleGroup G] in
theorem mem_centralizer_t_of_mem_A
    (ha : a ∈ Subgroup.centralizer
      ((((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t) : Subgroup G) : Set G)) :
    a ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp ha t
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))).symm

theorem mem_normalizer_V_of_mem_A (hd : Sec19DataT p f K z S W L t V) (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) : a ∈ Subgroup.normalizer (V : Set G) := by
  have haL : a ∈ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_member hd.tight.toTightBranch hd.memL hd.invL hat
  rw [← inf_member_eq hd, Subgroup.mem_normalizer_iff]
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

theorem mem_normalizer_W_of_mem_A (hd : Sec19DataT p f K z S W L t V) (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) : a ∈ Subgroup.normalizer (W : Set G) := by
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hU : conjSub a (K ⊓ W) = K ⊓ W :=
    conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le hUR haC))
  have hV : conjSub a V = V := conjSub_eq_of_mem_normalizer (mem_normalizer_V_of_mem_A hd haS hat)
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  calc conjSub a W = conjSub a ((K ⊓ W) ⊔ V) := by rw [← sup_eq_inf_sup hd]
    _ = conjSub a (K ⊓ W) ⊔ conjSub a V := Subgroup.map_sup _ _ _
    _ = W := by rw [hU, hV, ← sup_eq_inf_sup hd]

theorem exists_sylow_member_of_mem_A (hd : Sec19DataT p f K z S W L t V)
    (haS : a ∈ (S : Subgroup G)) (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ conjSub a RL = RL ∧ (∀ w ∈ W, conjSub w RL = RL) ∧
      V ≤ RL ∧ Nat.card RL = 2 * Nat.card V := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (le_centralizer_of_mem hd0 (mem_W hd)).trans
      (centralizer_le_normalizer_member htb hd.memL hd.invL)
  have haL : a ∈ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_member htb hd.memL hd.invL hat
  have hT : Subgroup.zpowers a ⊔ W ≤ (S : Subgroup G) := sup_le (Subgroup.zpowers_le.mpr haS) hd.hWS
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ W) := S.isPGroup'.to_le hT
  obtain ⟨RL, hRL, hRLT⟩ := exists_sylow_normalized hT2 (sup_le (Subgroup.zpowers_le.mpr haL) hWL)
  have hTRL : Subgroup.zpowers a ⊔ W ≤ Subgroup.normalizer (RL : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRLT w hw)
  have hP := IsPGroup.to_sup_of_normal_right' hT2 hRL.2.1 hTRL
  have hVRL : V ≤ RL := by
    have h1 : RL ⊔ V = RL := hRL.eq_of_le (hP.to_le (sup_le le_sup_right
      (hd.leW.trans (le_sup_right.trans le_sup_left)))) (sup_le hRL.1 (le_member hd)) le_sup_left
    rw [← h1]
    exact le_sup_right
  obtain ⟨R', -, J, hJ, hR'J, hVR', -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hd.memV
  have hJL : J = L := hΩ.eq_of_mem_USet hp hd.memV hJ hd.memL (hVR'.trans hR'J.1) (le_member hd)
  subst hJL
  exact ⟨RL, hRL, hRLT a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)),
    fun w hw => hRLT w (Subgroup.mem_sup_right hw), hVRL, by rw [hRL.natCard_eq hR'J, hcard]⟩

omit [IsSimpleGroup G] in
theorem inf_inf_centralizer_eq_bot (hd : Sec19DataT p f K z S W L t V) {RL : Subgroup G}
    (hRL : IsSylow2In RL L) : K ⊓ W ⊓ Subgroup.centralizer (RL : Set G) = ⊥ := by
  have htb := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
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
  have hzx : z ∈ Subgroup.zpowers x := mem_of_le_member hI (Subgroup.zpowers_le.mpr hx.1.1)
    ((S.isPGroup'.to_le hd.hWS).to_le (Subgroup.zpowers_le.mpr hx.1.2)) h2
  have hzC : z ∈ Subgroup.centralizer (RL : Set G) := (Subgroup.zpowers_le.mpr hx.2) hzx
  refine not_le_centralizer_of_mem_rSet hd.tight hd.memL (CoreAssembly.mem_conjClass_self K)
    (member_ne hd) hI hRLmem hRL.1 ?_
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hzC r hr

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
