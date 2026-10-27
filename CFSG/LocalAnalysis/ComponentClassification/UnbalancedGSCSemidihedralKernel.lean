module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCCentralTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSABasic
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.GroupTheory.QuaternionCentralizers

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace SemidihedralKernel

open Subgroup CentralTwoActionKernel


section General

variable {A : Type*} [Group A]

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem center_quotient_center_eq_bot [Group.IsPerfect A] : center (A ⧸ center A) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have h : centerQuotientHom A (MulAut.conj x) = 1 := by
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H w =>
      change onCenterQuotient (MulAut.conj x) (QuotientGroup.mk' _ w) = QuotientGroup.mk' _ w
      rw [onCenterQuotient_apply_mk, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have := mem_center_iff.mp hy (QuotientGroup.mk' _ w)
      change QuotientGroup.mk' _ w * QuotientGroup.mk' _ x = QuotientGroup.mk' _ x *
        QuotientGroup.mk' _ w at this
      rw [← this, mul_inv_cancel_right]
  have h1 := CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
    A (h.trans (map_one _).symm)
  have hx : x ∈ center A := (conj_eq_one_iff_mem_center x).mp h1
  rw [mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem quaternion_involution_unique {m : ℕ} [NeZero m] (x : QuaternionGroup m)
    (hx : orderOf x = 2) : x = QuaternionGroup.a (m : ZMod (2 * m)) := by
  cases x with
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hx
    norm_num at hx
  | a i =>
    have h2 : QuaternionGroup.a i ^ 2 = 1 := hx ▸ pow_orderOf_eq_one _
    rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq,
      ← two_mul] at h2
    rcases (CFSG.GroupTheory.two_mul_eq_zero_iff_zmod i).mp h2 with rfl | rfl
    · rw [QuaternionGroup.a_zero, orderOf_one] at hx
      norm_num at hx
    · rfl

end General

variable {X : Type*} [Group X]

abbrev CentralQuot (L : Subgroup X) (O : Subgroup L) [O.Normal] :=
  (L ⧸ O) ⧸ center (L ⧸ O)

@[expose] noncomputable def alphaN (L : Subgroup X) (O : Subgroup L) [O.Characteristic] :
    normalizer (L : Set X) →* MulAut (CentralQuot L O) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (L ⧸ O)).comp
    ((descendHom O).comp L.normalizerMonoidHom)

theorem sup_le_normalizer {L P : Subgroup X} (h : P ≤ normalizer (L : Set X)) :
    L ⊔ P ≤ normalizer (L : Set X) :=
  sup_le le_normalizer h

@[expose] noncomputable def alphaH (L : Subgroup X) (O : Subgroup L) [O.Characteristic]
    (P : Subgroup X) [hP : Fact (P ≤ normalizer (L : Set X))] :
    ↥(L ⊔ P) →* MulAut (CentralQuot L O) :=
  (alphaN L O).comp (inclusion (sup_le_normalizer hP.out))

section Action

variable (L : Subgroup X) (O : Subgroup L) [O.Characteristic] (P : Subgroup X)
  [hP : Fact (P ≤ normalizer (L : Set X))]

theorem alphaH_mk (h : ↥(L ⊔ P)) (l x : L) (hx : (x : X) = h * l * h⁻¹) :
    alphaH L O P h ((l : L ⧸ O) : CentralQuot L O) = ((x : L ⧸ O) : CentralQuot L O) := by
  have h1 : L.normalizerMonoidHom (inclusion (sup_le_normalizer hP.out) h) l = x :=
    Subtype.ext hx.symm
  change (((descendHom O (L.normalizerMonoidHom (inclusion (sup_le_normalizer hP.out) h)))
    (l : L ⧸ O) : L ⧸ O) : CentralQuot L O) = _
  rw [descendHom_mk, h1]

theorem conj_mem_oddMap (g : normalizer (L : Set X)) {l : L} (hl : l ∈ O) :
    (g : X) * l * (g : X)⁻¹ ∈ O.map L.subtype := by
  have hchar := (Subgroup.characteristic_iff_map_eq.mp (inferInstance : O.Characteristic))
    (L.normalizerMonoidHom g)
  have hmem : L.normalizerMonoidHom g l ∈ O := by
    rw [← hchar]
    exact mem_map_of_mem _ hl
  exact ⟨_, hmem, rfl⟩

instance oddMap_normal : ((O.map L.subtype).subgroupOf (L ⊔ P)).Normal := by
  refine ⟨fun x hx h => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨l, hl, hlx⟩ := hx
  have := conj_mem_oddMap L O ⟨h, sup_le_normalizer hP.out h.2⟩ hl
  simp only [coe_mul, coe_inv]
  rw [← hlx]
  exact this

end Action

theorem mk_mem_zpowers_iff_of_center {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g c : G)
    (hc : c ∈ center G) : (g : G ⧸ N) ∈ zpowers (c : G ⧸ N) ↔ g ∈ N ⊔ zpowers c := by
  rw [mem_sup_of_normal_left]
  constructor
  · rintro ⟨k, hk⟩
    dsimp only at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
    refine ⟨g * (c ^ k)⁻¹, ?_, c ^ k, zpow_mem_zpowers c k, inv_mul_cancel_right _ _⟩
    rw [mem_center_iff.mp (inv_mem (zpow_mem hc k)) g]
    exact hk
  · rintro ⟨o, ho, w, ⟨k, rfl⟩, rfl⟩
    refine ⟨k, ?_⟩
    change (c : G ⧸ N) ^ k = ((o * c ^ k : G) : G ⧸ N)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr ho, one_mul, QuotientGroup.mk_zpow]

end SemidihedralKernel

open Subgroup CentralTwoActionKernel SemidihedralKernel CFSG.Semidihedral CFSG.Open

theorem semidihedral_quaternion_odd_quotient_action_kernel {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (O : Subgroup L) [O.Characteristic] (hOodd : Odd (Nat.card O))
    (hA : CFSG.IsQuasisimple (L ⧸ O)) {z : X} (hzL : z ∈ L) (hzZ : (⟨z, hzL⟩ : L) ∈ center L)
    (hz2 : orderOf z = 2) (hZ : center (L ⧸ O) = zpowers ((⟨z, hzL⟩ : L) : L ⧸ O))
    (D : Subgroup X) (hDL : D ≤ L) (hDsyl : ∃ S : Sylow 2 L, (S : Subgroup L) = D.subgroupOf L)
    {r : ℕ} (hr : 3 ≤ r) (hDQ : Nonempty (D ≃* QuaternionGroup (2 ^ (r - 2))))
    (P : Subgroup X) [hPN : Fact (P ≤ normalizer (L : Set X))] (hP2 : IsPGroup 2 P)
    (hDP : D ≤ P) (hidx : D.relIndex P = 2) {n : ℕ} (hn : 4 ≤ n)
    (hPSD : Nonempty (P ≃* SemidihedralGroup n)) :
    P ⊓ L = D ∧
    (∃ S : Sylow 2 ↥(L ⊔ P), (S : Subgroup ↥(L ⊔ P)) = P.subgroupOf (L ⊔ P)) ∧
    (⟨z, mem_sup_left hzL⟩ : ↥(L ⊔ P)) ∈ center ↥(L ⊔ P) ∧
    ((O.map L.subtype).subgroupOf (L ⊔ P)).Normal ∧
    (∀ (h : ↥(L ⊔ P)) (l x : L), (x : X) = h * l * h⁻¹ →
      alphaH L O P h ((l : L ⧸ O) : CentralQuot L O) = ((x : L ⧸ O) : CentralQuot L O)) ∧
    (alphaH L O P).ker = (O.map L.subtype ⊔ zpowers z).subgroupOf (L ⊔ P) ∧
    (L.subgroupOf (L ⊔ P)).map (alphaH L O P) =
      (MulAut.conj : CentralQuot L O →* MulAut (CentralQuot L O)).range ∧
    ((L.subgroupOf (L ⊔ P)).map (alphaH L O P)).relIndex (alphaH L O P).range = 2 ∧
    centralizer (D : Set X) ⊓ P = zpowers z ∧
    ((alphaH L O P).comp (inclusion (le_sup_right : P ≤ L ⊔ P))).ker =
      (zpowers z).subgroupOf P ∧
    (∃ S : Sylow 2 ↥(alphaH L O P).range, (S : Subgroup ↥(alphaH L O P).range) =
      ((P.subgroupOf (L ⊔ P)).map (alphaH L O P)).subgroupOf (alphaH L O P).range) ∧
    Nonempty (((P.subgroupOf (L ⊔ P)).map (alphaH L O P)) ≃* DihedralGroup (2 ^ (n - 2))) ∧
    Nat.card ((P.subgroupOf (L ⊔ P)).map (alphaH L O P)) = 2 ^ (n - 1) ∧
    (∃ αbar : ↥(L ⊔ P) ⧸ (O.map L.subtype).subgroupOf (L ⊔ P) →* MulAut (CentralQuot L O),
      (∀ h : ↥(L ⊔ P), αbar h = alphaH L O P h) ∧
      αbar.ker = zpowers ((⟨z, mem_sup_left hzL⟩ : ↥(L ⊔ P)) :
        ↥(L ⊔ P) ⧸ (O.map L.subtype).subgroupOf (L ⊔ P)) ∧
      zpowers ((⟨z, mem_sup_left hzL⟩ : ↥(L ⊔ P)) :
        ↥(L ⊔ P) ⧸ (O.map L.subtype).subgroupOf (L ⊔ P)) ≤
          center (↥(L ⊔ P) ⧸ (O.map L.subtype).subgroupOf (L ⊔ P)) ∧
      Nat.card (zpowers ((⟨z, mem_sup_left hzL⟩ : ↥(L ⊔ P)) :
        ↥(L ⊔ P) ⧸ (O.map L.subtype).subgroupOf (L ⊔ P))) = 2) ∧
    (∃ S : Sylow 2 (↥(L ⊔ P) ⧸ (O.map L.subtype).subgroupOf (L ⊔ P)),
      (S : Subgroup _) = (P.subgroupOf (L ⊔ P)).map
        (QuotientGroup.mk' ((O.map L.subtype).subgroupOf (L ⊔ P))) ∧
      Nonempty (((P.subgroupOf (L ⊔ P)).map
        (QuotientGroup.mk' ((O.map L.subtype).subgroupOf (L ⊔ P)))) ≃* SemidihedralGroup n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hDsyl
  obtain ⟨eD⟩ := hDQ
  obtain ⟨eP⟩ := hPSD
  have hHN : L ⊔ P ≤ normalizer (L : Set X) := sup_le_normalizer hPN.out
  have : Group.IsPerfect (L ⧸ O) := hA.1
  set α := alphaH L O P with hαdef
  set ON := (O.map L.subtype).subgroupOf (L ⊔ P) with hON
  have hzD : z ∈ D := by
    have hnorm : (zpowers (⟨z, hzL⟩ : L)).Normal := normal_of_le_center (zpowers_le.mpr hzZ)
    have hp : IsPGroup 2 (zpowers (⟨z, hzL⟩ : L)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, hz2]
    have := hp.le_sylow_of_normal S (mem_zpowers _)
    rw [hS, mem_subgroupOf] at this
    exact this
  have hzP : z ∈ P := hDP hzD
  have hPL : P ⊓ L = D := by
    apply le_antisymm _ (le_inf hDP hDL)
    have hp : IsPGroup 2 ((P ⊓ L).subgroupOf L) :=
      (hP2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    have h1 := S.is_maximal' hp (by rw [hS]; exact fun x hx => le_inf hDP hDL hx)
    rw [hS, subgroupOf_inj, inf_of_le_left inf_le_right, inf_of_le_left hDL] at h1
    exact h1.le
  have hPcard : Nat.card P = 2 * Nat.card D := by
    have := relIndex_mul_card (H := D) (K := P)
    rw [hidx, inf_of_le_left hDP] at this
    exact this.symm
  have hD0 : 0 < Nat.card D := Nat.card_pos
  have hHcard : Nat.card (L ⊔ P : Subgroup X) = 2 * Nat.card L := by
    have := CFSG.ComponentClassification.UnbalancedGS.AHelpers.card_sup_mul_card_inf L P
      hPN.out
    rw [inf_comm, hPL, hPcard] at this
    have h2 : Nat.card (L ⊔ P : Subgroup X) * Nat.card D = (2 * Nat.card L) * Nat.card D := by
      rw [this]
      ring
    exact Nat.eq_of_mul_eq_mul_right hD0 h2
  have hScard : Nat.card S = Nat.card D := by
    rw [hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv
  have hSidx : ¬ 2 ∣ (S : Subgroup L).index := S.not_dvd_index
  have hLcard : Nat.card L = Nat.card D * (S : Subgroup L).index := by
    rw [← hScard]
    exact (card_mul_index (S : Subgroup L)).symm
  have hPHp : IsPGroup 2 (P.subgroupOf (L ⊔ P)) :=
    hP2.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  have hPHcard : Nat.card (P.subgroupOf (L ⊔ P)) = 2 * Nat.card D := by
    rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv, hPcard]
  have hPHidx : (P.subgroupOf (L ⊔ P)).index = (S : Subgroup L).index := by
    have h1 := card_mul_index (P.subgroupOf (L ⊔ P))
    rw [hPHcard, hHcard, hLcard] at h1
    have h2 : (2 * Nat.card D) * (P.subgroupOf (L ⊔ P)).index =
        (2 * Nat.card D) * (S : Subgroup L).index := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hDnormalP : (D.subgroupOf P).Normal := normal_of_index_eq_two hidx
  have hm0 : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hDz : eD ⟨z, hzD⟩ = QuaternionGroup.a _ :=
    quaternion_involution_unique _ (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2])
  have hDinv : ∀ d : X, d ∈ D → orderOf d = 2 → d = z := by
    intro d hd hd2
    have h1 : eD ⟨d, hd⟩ = QuaternionGroup.a _ :=
      quaternion_involution_unique _ (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hd2])
    exact congrArg Subtype.val (eD.injective (h1.trans hDz.symm))
  have hPz : P ≤ centralizer ({z} : Set X) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    have h1 := hDnormalP.conj_mem ⟨z, hzP⟩ (mem_subgroupOf.mpr hzD) ⟨p, hp⟩
    rw [mem_subgroupOf] at h1
    simp only [coe_mul, coe_inv] at h1
    have h2 : orderOf (p * z * p⁻¹) = 2 := by
      rw [← hz2]
      exact orderOf_injective (MulAut.conj p).toMonoidHom (MulAut.conj p).injective z
    have h3 := hDinv _ h1 h2
    calc p * z = p * z * p⁻¹ * p := by group
      _ = z * p := by rw [h3]
  have hLz : L ≤ centralizer ({z} : Set X) := by
    intro l hl
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_center_iff.mp hzZ ⟨l, hl⟩)
  have hHz : L ⊔ P ≤ centralizer ({z} : Set X) := sup_le hLz hPz
  have hzH : (⟨z, mem_sup_left hzL⟩ : ↥(L ⊔ P)) ∈ center ↥(L ⊔ P) :=
    mem_center_iff.mpr fun h => Subtype.ext (mem_centralizer_singleton_iff.mp (hHz h.2))
  have hαL : ∀ l : L, α ⟨l, mem_sup_left l.2⟩ =
      MulAut.conj ((l : L ⧸ O) : CentralQuot L O) := by
    intro l
    refine MulEquiv.ext fun t => ?_
    induction t using QuotientGroup.induction_on with
    | H w =>
      induction w using QuotientGroup.induction_on with
      | H v =>
        rw [hαdef, alphaH_mk L O P _ v (l * v * l⁻¹) (by simp), MulAut.conj_apply]
        rfl
  have hTcenter : center (CentralQuot L O) = ⊥ := center_quotient_center_eq_bot
  have hmap : (O ⊔ zpowers (⟨z, hzL⟩ : L)).map L.subtype = O.map L.subtype ⊔ zpowers z := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hkerL : ∀ l : L, α ⟨l, mem_sup_left l.2⟩ = 1 ↔
      (l : X) ∈ O.map L.subtype ⊔ zpowers z := by
    intro l
    rw [hαL, conj_eq_one_iff_mem_center, hTcenter, mem_bot, QuotientGroup.eq_one_iff, hZ,
      mk_mem_zpowers_iff_of_center O l ⟨z, hzL⟩ hzZ, ← hmap]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hOXL : O.map L.subtype ⊔ zpowers z ≤ L := sup_le (map_subtype_le _) (zpowers_le.mpr hzL)
  have hPcenter2 : Nat.card (center P) = 2 :=
    (supplied_index_two_and_element_structure n hn eP.symm).2.1
  have hzcP : (⟨z, hzP⟩ : P) ∈ center P := mem_center_iff.mpr fun p => Subtype.ext
    (mem_centralizer_singleton_iff.mp (hPz p.2))
  have hcenterP : center P = zpowers (⟨z, hzP⟩ : P) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzcP)
    rw [hPcenter2, Nat.card_zpowers, Subgroup.orderOf_mk, hz2]
  have hCPD : ∀ g ∈ P, g ∈ centralizer (D : Set X) → g ∈ D := by
    intro g hgP hgC
    by_contra hgD
    have hK : P ≤ D ⊔ zpowers g := by
      have hle : D ⊔ zpowers g ≤ P := sup_le hDP (zpowers_le.mpr hgP)
      have h1 := relIndex_mul_relIndex D (D ⊔ zpowers g) P le_sup_left hle
      rw [hidx] at h1
      have h2 : D.relIndex (D ⊔ zpowers g) ≠ 1 := by
        rw [Ne, relIndex_eq_one]
        intro h
        exact hgD (h (mem_sup_right (mem_zpowers g)))
      have h3 : (D ⊔ zpowers g).relIndex P = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp ⟨_, h1.symm⟩ with h | h
        · exact absurd h h2
        · rw [h] at h1
          omega
      exact relIndex_eq_one.mp h3
    have hDg : D ⊔ zpowers g ≤ centralizer ({g} : Set X) := by
      refine sup_le (fun d hd => ?_) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hgC d hd
    have hgcent : (⟨g, hgP⟩ : P) ∈ center P :=
      mem_center_iff.mpr fun p => Subtype.ext (mem_centralizer_singleton_iff.mp (hDg (hK p.2)))
    rw [hcenterP] at hgcent
    obtain ⟨k, hk⟩ := hgcent
    apply hgD
    have hgk : g = z ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [hgk]
    exact zpow_mem hzD k
  have hm2 : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQZ := (CFSG.GroupTheory.quaternion_centralizers hm2).2.2.1
  have hcenterD : ∀ g ∈ D, g ∈ centralizer (D : Set X) → g ∈ zpowers z := by
    intro g hgD hgC
    have hc : eD ⟨g, hgD⟩ ∈ center (QuaternionGroup (2 ^ (r - 2))) := by
      refine mem_center_iff.mpr fun q => ?_
      obtain ⟨d, rfl⟩ := eD.surjective q
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp hgC d d.2)
    rcases (hQZ _).mp hc with h | h
    · have h1 : (⟨g, hgD⟩ : D) = 1 := eD.injective (by rw [h, map_one, QuaternionGroup.one_def])
      have hg1 : g = 1 := congrArg Subtype.val h1
      rw [hg1]
      exact one_mem _
    · have h1 : (⟨g, hgD⟩ : D) = ⟨z, hzD⟩ := eD.injective (h.trans hDz.symm)
      have hgz : g = z := congrArg Subtype.val h1
      rw [hgz]
      exact mem_zpowers z
  have hCD : centralizer (D : Set X) ⊓ P = zpowers z := by
    apply le_antisymm
    · rintro g ⟨hgC, hgP⟩
      exact hcenterD g (hCPD g hgP hgC) hgC
    · rw [zpowers_le]
      refine ⟨mem_centralizer_iff.mpr fun d hd => ?_, hzP⟩
      exact mem_centralizer_singleton_iff.mp (hLz (hDL hd))
  have hOP : O.map L.subtype ⊓ P = ⊥ := by
    apply disjoint_iff.mp
    apply disjoint_of_coprime_natCard
    rw [card_map_of_injective L.subtype_injective]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP2
    rw [hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hOodd)
  have hαP : ∀ p : P, α ⟨p, mem_sup_right p.2⟩ = 1 ↔ (p : X) ∈ zpowers z := by
    intro p
    constructor
    · intro h1
      set g : normalizer (L : Set X) := ⟨p, hHN (mem_sup_right p.2)⟩ with hg
      have h2 : descendHom O (L.normalizerMonoidHom g) = 1 := by
        apply CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
          (L ⧸ O)
        rw [map_one]
        exact h1
      have hcomm : ∀ d ∈ D, (p : X) * d * (p : X)⁻¹ = d := by
        intro d hd
        have h3 := congrArg (fun φ : MulAut (L ⧸ O) => φ ((⟨d, hDL hd⟩ : L) : L ⧸ O)) h2
        simp only [MulAut.one_apply] at h3
        rw [descendHom_mk, QuotientGroup.eq] at h3
        have h4 : ((p : X) * d * (p : X)⁻¹)⁻¹ * d ∈ O.map L.subtype ⊓ P := by
          refine Subgroup.mem_inf.mpr ⟨⟨_, h3, rfl⟩, ?_⟩
          exact P.mul_mem (P.inv_mem (P.mul_mem (P.mul_mem p.2 (hDP hd)) (P.inv_mem p.2)))
            (hDP hd)
        rw [hOP, mem_bot] at h4
        exact inv_mul_eq_one.mp h4
      rw [← hCD]
      refine ⟨mem_centralizer_iff.mpr fun d hd => ?_, p.2⟩
      have := hcomm d hd
      calc d * (p : X) = (p : X) * d * (p : X)⁻¹ * p := by rw [this]
        _ = p * d := by group
    · intro hz
      obtain ⟨k, hk⟩ := hz
      have hpL : (p : X) ∈ L := hk ▸ zpow_mem hzL k
      exact (hkerL ⟨p, hpL⟩).mpr (mem_sup_right ⟨k, hk⟩)
  have hkerP : (α.comp (inclusion (le_sup_right : P ≤ L ⊔ P))).ker =
      (zpowers z).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mem_subgroupOf]
    exact hαP p
  have hαLrange : (L.subgroupOf (L ⊔ P)).map α =
      (MulAut.conj : CentralQuot L O →* MulAut (CentralQuot L O)).range := by
    ext φ
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hh' : (h : X) ∈ L := mem_subgroupOf.mp hh
      exact ⟨((⟨h, hh'⟩ : L) : L ⧸ O), (hαL ⟨h, hh'⟩).symm⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective t
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
      exact ⟨⟨v, mem_sup_left v.2⟩, mem_subgroupOf.mpr v.2, hαL v⟩
  have hzO : (⟨z, hzL⟩ : L) ∉ O := by
    intro h
    have h1 : orderOf (⟨z, hzL⟩ : L) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O h
    rw [Subgroup.orderOf_mk, hz2] at h1
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h1)
  have hZA : Nat.card (center (L ⧸ O)) = 2 := by
    rw [hZ, Nat.card_zpowers]
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow]
      have : (⟨z, hzL⟩ : L) ^ 2 = 1 := Subtype.ext (by
        rw [coe_pow]
        exact hz2 ▸ pow_orderOf_eq_one z)
      rw [this, QuotientGroup.mk_one]
    · intro h
      exact hzO ((QuotientGroup.eq_one_iff _).mp h)
  have hAcard : Nat.card L = Nat.card O * Nat.card (L ⧸ O) := by
    rw [← index_eq_card]
    exact (card_mul_index O).symm
  have hTcard : Nat.card (L ⧸ O) = 2 * Nat.card (CentralQuot L O) := by
    rw [← hZA, ← index_eq_card]
    exact (card_mul_index (center (L ⧸ O))).symm
  have hconj_inj : Function.Injective
      (MulAut.conj : CentralQuot L O →* MulAut (CentralQuot L O)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, conj_eq_one_iff_mem_center, hTcenter] at hx
    exact hx
  have hInncard : Nat.card (MulAut.conj : CentralQuot L O →* MulAut (CentralQuot L O)).range =
      Nat.card (CentralQuot L O) :=
    (Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv).symm
  set ψ := α.comp (inclusion (le_sup_right : P ≤ L ⊔ P)) with hψ
  have hψrange : ψ.range = (P.subgroupOf (L ⊔ P)).map α := by
    rw [hψ, MonoidHom.range_comp, inclusion_range]
  have hkerPcard : Nat.card ψ.ker = 2 := by
    rw [hkerP, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hzP)).toEquiv,
      Nat.card_zpowers, hz2]
  have hαPcard : Nat.card ((P.subgroupOf (L ⊔ P)).map α) = Nat.card D := by
    have := card_ker_mul_card_range ψ
    rw [hkerPcard, hψrange, hPcard] at this
    omega
  have hLHidx : (L.subgroupOf (L ⊔ P)).index = 2 := by
    have h1 := card_mul_index (L.subgroupOf (L ⊔ P))
    rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv, hHcard] at h1
    have hL0 : 0 < Nat.card L := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hL0 (h1.trans (mul_comm _ _))
  have hαLB : (L.subgroupOf (L ⊔ P)).map α ≤ α.range := map_le_range α _
  have hidxdvd : ((L.subgroupOf (L ⊔ P)).map α).relIndex α.range ∣ 2 := by
    have h1 := index_map_dvd (H := L.subgroupOf (L ⊔ P)) α.rangeRestrict_surjective
    rw [hLHidx] at h1
    have h2 : (L.subgroupOf (L ⊔ P)).map α.rangeRestrict =
        ((L.subgroupOf (L ⊔ P)).map α).subgroupOf α.range := by
      ext x
      rw [mem_subgroupOf, mem_map, mem_map]
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, hx⟩
        exact ⟨h, hh, Subtype.ext hx⟩
    rw [h2] at h1
    exact h1
  have hidx_ne_one : ((L.subgroupOf (L ⊔ P)).map α).relIndex α.range ≠ 1 := by
    intro h1
    rw [relIndex_eq_one] at h1
    have h2 : (P.subgroupOf (L ⊔ P)).map α ≤ (L.subgroupOf (L ⊔ P)).map α :=
      (map_le_range _ _).trans h1
    have h3 := card_dvd_of_le h2
    rw [hαPcard, hαLrange, hInncard] at h3
    obtain ⟨c, hc⟩ := h3
    apply hSidx
    have h4 : Nat.card D * (S : Subgroup L).index = Nat.card D * (2 * (Nat.card O * c)) := by
      rw [← hLcard, hAcard, hTcard, hc]
      ring
    rw [Nat.eq_of_mul_eq_mul_left hD0 h4]
    exact Dvd.intro _ rfl
  have hBidx : ((L.subgroupOf (L ⊔ P)).map α).relIndex α.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidxdvd with h | h
    · exact absurd h hidx_ne_one
    · exact h
  have hBcard : Nat.card α.range = 2 * Nat.card (CentralQuot L O) := by
    have h1 := relIndex_mul_card (H := (L.subgroupOf (L ⊔ P)).map α) (K := α.range)
    rw [hBidx, inf_of_le_left hαLB, hαLrange, hInncard] at h1
    exact h1.symm
  have hkercard : Nat.card α.ker = 2 * Nat.card O := by
    have h1 := card_ker_mul_card_range α
    rw [hBcard, hHcard, hAcard, hTcard] at h1
    have hT0 : 0 < Nat.card (CentralQuot L O) := Nat.card_pos
    have h2 : Nat.card α.ker * (2 * Nat.card (CentralQuot L O)) =
        (2 * Nat.card O) * (2 * Nat.card (CentralQuot L O)) := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  have hOXcard : Nat.card (O.map L.subtype ⊔ zpowers z : Subgroup X) = 2 * Nat.card O := by
    have hcomm : ∀ x ∈ O.map L.subtype, ∀ y ∈ zpowers z, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := hy
      have hxL : x ∈ L := map_subtype_le _ hx
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hLz hxL) : Commute x z) k).eq
    have hinf : O.map L.subtype ⊓ zpowers z = ⊥ := by
      apply disjoint_iff.mp
      apply disjoint_of_coprime_natCard
      rw [card_map_of_injective L.subtype_injective, Nat.card_zpowers, hz2]
      exact Nat.coprime_two_right.mpr hOodd
    have := card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [hinf, card_bot, mul_one, card_map_of_injective L.subtype_injective, Nat.card_zpowers,
      hz2] at this
    rw [this]
    ring
  have hkerα : α.ker = (O.map L.subtype ⊔ zpowers z).subgroupOf (L ⊔ P) := by
    symm
    apply eq_of_le_of_card_ge
    · intro h hh
      rw [mem_subgroupOf] at hh
      have hhL : (h : X) ∈ L := hOXL hh
      exact (hkerL ⟨h, hhL⟩).mpr hh
    · rw [hkercard, Nat.card_congr (subgroupOfEquivOfLe (hOXL.trans le_sup_left)).toEquiv,
        hOXcard]
  have hαPB : (P.subgroupOf (L ⊔ P)).map α ≤ α.range := map_le_range α _
  have hαPp : IsPGroup 2 (((P.subgroupOf (L ⊔ P)).map α).subgroupOf α.range) :=
    (hPHp.map α).of_equiv (subgroupOfEquivOfLe hαPB).symm
  have hαPBidx : ¬ 2 ∣ (((P.subgroupOf (L ⊔ P)).map α).subgroupOf α.range).index := by
    have h1 := card_mul_index (((P.subgroupOf (L ⊔ P)).map α).subgroupOf α.range)
    rw [Nat.card_congr (subgroupOfEquivOfLe hαPB).toEquiv, hαPcard, hBcard] at h1
    intro h2
    apply hSidx
    have h3 : Nat.card D * (S : Subgroup L).index = Nat.card D *
        (Nat.card O * (((P.subgroupOf (L ⊔ P)).map α).subgroupOf α.range).index) := by
      rw [← hLcard, hAcard, hTcard, ← h1]
      ring
    rw [Nat.eq_of_mul_eq_mul_left hD0 h3]
    exact Dvd.dvd.mul_left h2 _
  have hONker : ON ≤ α.ker := by
    rw [hkerα, hON]
    intro h hh
    rw [mem_subgroupOf] at hh ⊢
    exact mem_sup_left hh
  set zH : ↥(L ⊔ P) := ⟨z, mem_sup_left hzL⟩ with hzHdef
  have hzON : zH ∉ ON := by
    intro h
    rw [hON, mem_subgroupOf] at h
    have := Subgroup.mem_inf.mpr ⟨h, hzP⟩
    rw [hOP, mem_bot] at this
    have hz1 : z = 1 := this
    rw [hz1, orderOf_one] at hz2
    norm_num at hz2
  have hzON2 : (zH : ↥(L ⊔ P) ⧸ ON) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : zH ^ 2 = 1 := Subtype.ext (by
      rw [coe_pow]
      exact hz2 ▸ pow_orderOf_eq_one z)
    rw [this, QuotientGroup.mk_one]
  have hzONord : orderOf (zH : ↥(L ⊔ P) ⧸ ON) = 2 :=
    orderOf_eq_prime hzON2 (fun h => hzON ((QuotientGroup.eq_one_iff _).mp h))
  have hzz : (zpowers z).subgroupOf (L ⊔ P) = zpowers zH := by
    ext h
    rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [coe_zpow]; exact hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk, coe_zpow]⟩
  have hmemOz : ∀ h : ↥(L ⊔ P), h ∈ (O.map L.subtype ⊔ zpowers z).subgroupOf (L ⊔ P) ↔
      (h : ↥(L ⊔ P) ⧸ ON) ∈ zpowers (zH : ↥(L ⊔ P) ⧸ ON) := by
    intro h
    rw [mk_mem_zpowers_iff_of_center ON h zH hzH,
      subgroupOf_sup ((map_subtype_le _).trans le_sup_left) (zpowers_le.mpr (mem_sup_left hzL)),
      hzz]
  refine ⟨hPL, ⟨hPHp.toSylow (by rw [hPHidx]; exact hSidx), rfl⟩, hzH, inferInstance,
    alphaH_mk L O P, hkerα, hαLrange, hBidx, hCD, hkerP, ⟨hαPp.toSylow hαPBidx, rfl⟩, ?_, ?_,
    ?_, ?_⟩
  ·
    let δ : P →* DihedralGroup (half n) :=
      (CentralQuotients.toDihedral n hn).comp eP.toMonoidHom
    have hδsurj : Function.Surjective δ :=
      (CentralQuotients.toDihedral_surjective n hn).comp eP.surjective
    have hδker : δ.ker = (zpowers z).subgroupOf P := by
      ext p
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        ← MonoidHom.mem_ker, CentralQuotients.toDihedral_ker, ← center_eq_zpowers n hn]
      have hcent : eP p ∈ center (SemidihedralGroup n) ↔ p ∈ center P := by
        rw [mem_center_iff, mem_center_iff]
        constructor
        · intro h q
          apply eP.injective
          rw [map_mul, map_mul]
          exact h (eP q)
        · intro h q
          obtain ⟨q', rfl⟩ := eP.surjective q
          rw [← map_mul, ← map_mul, h q']
      rw [hcent, hcenterP, mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [← hk, coe_zpow]⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [coe_zpow]; exact hk)⟩
    exact ⟨((MulEquiv.subgroupCongr hψrange).symm.trans
      (QuotientGroup.quotientKerEquivRange ψ).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq (hkerP.trans hδker.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective δ hδsurj))⟩
  · rw [hαPcard]
    have hPn : Nat.card P = 2 ^ n := by
      rw [Nat.card_congr eP.toEquiv, CFSG.Semidihedral.card n (by omega)]
    rw [hPcard] at hPn
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  · refine ⟨QuotientGroup.lift ON α hONker, fun h => QuotientGroup.lift_mk _ _ _, ?_, ?_, ?_⟩
    · ext x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
      rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, ← MonoidHom.mem_ker, hkerα, hmemOz]
    · rw [zpowers_le]
      refine mem_center_iff.mpr fun y => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hzH g]
    · rw [Nat.card_zpowers, hzONord]
  · set π := QuotientGroup.mk' ON with hπ
    have hπinj : Function.Injective (π.comp (P.subgroupOf (L ⊔ P)).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro p hp
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hON, mem_subgroupOf] at hp
      have := Subgroup.mem_inf.mpr ⟨hp, mem_subgroupOf.mp p.2⟩
      rw [hOP, mem_bot] at this
      exact Subtype.ext (Subtype.ext this)
    have hrange : (π.comp (P.subgroupOf (L ⊔ P)).subtype).range =
        (P.subgroupOf (L ⊔ P)).map π := by
      rw [MonoidHom.range_comp, range_subtype]
    let e1 : (P.subgroupOf (L ⊔ P)).map π ≃* P.subgroupOf (L ⊔ P) :=
      ((MonoidHom.ofInjective hπinj).trans (MulEquiv.subgroupCongr hrange)).symm
    let e2 : (P.subgroupOf (L ⊔ P)).map π ≃* SemidihedralGroup n :=
      e1.trans ((subgroupOfEquivOfLe le_sup_right).trans eP)
    have himcard : Nat.card ((P.subgroupOf (L ⊔ P)).map π) = 2 * Nat.card D := by
      rw [Nat.card_congr e1.toEquiv, hPHcard]
    have himp : IsPGroup 2 ((P.subgroupOf (L ⊔ P)).map π) := hPHp.map π
    have himidx : ¬ 2 ∣ ((P.subgroupOf (L ⊔ P)).map π).index := by
      have h1 := card_mul_index ((P.subgroupOf (L ⊔ P)).map π)
      have hHO : Nat.card (↥(L ⊔ P) ⧸ ON) * Nat.card O = Nat.card (L ⊔ P : Subgroup X) := by
        rw [← index_eq_card, mul_comm]
        have := card_mul_index ON
        rw [hON, Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans
          le_sup_left)).toEquiv, card_map_of_injective L.subtype_injective] at this
        exact this
      rw [himcard] at h1
      intro h2
      apply hSidx
      have h3 : (2 * Nat.card D) * (S : Subgroup L).index =
          (2 * Nat.card D) * (((P.subgroupOf (L ⊔ P)).map π).index * Nat.card O) := by
        rw [← mul_assoc, h1, hHO, hHcard, hLcard]
        ring
      rw [Nat.eq_of_mul_eq_mul_left (by omega) h3]
      exact Dvd.dvd.mul_right h2 _
    exact ⟨himp.toSylow himidx, rfl, ⟨e2⟩⟩

end CFSG.ComponentClassification.UnbalancedGS
