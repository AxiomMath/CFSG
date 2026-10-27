module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3CoexistStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23FusionLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFischer
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

section Transport

variable {H : Type} [Group H] {L : Subgroup H} {Y : Type} [Group Y]

theorem inf_centralizer_subgroupOf_eq {x : H} (hx : x ∈ L) :
    (L ⊓ centralizer ({x} : Set H)).subgroupOf L =
      centralizer ({(⟨x, hx⟩ : ↥L)} : Set ↥L) := by
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨z.2, congrArg Subtype.val h⟩

noncomputable def infCentralizerEquiv (ψ : ↥L ≃* Y) {x : H} (hx : x ∈ L) :
    ↥(L ⊓ centralizer ({x} : Set H)) ≃* ↥(centralizer ({ψ ⟨x, hx⟩} : Set Y)) :=
  ((Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ centralizer ({x} : Set H) ≤ L)).symm.trans
    (MulEquiv.subgroupCongr (inf_centralizer_subgroupOf_eq hx))).trans
    (CFSG.Fischer.centralizerEquiv ψ ⟨x, hx⟩)

theorem card_centralizer_le_card_inf (ψ : ↥L ≃* Y) {x : H} (hx : x ∈ L) {a : Y}
    (ha : ψ ⟨x, hx⟩ = a) :
    Nat.card ↥(centralizer ({a} : Set Y)) ≤ Nat.card ↥(L ⊓ centralizer ({x} : Set H)) := by
  subst ha
  exact (Nat.card_congr (infCentralizerEquiv ψ hx).toEquiv).symm.le

theorem card_inf_inf_le [Finite Y] (ψ : ↥L ≃* Y) {x y : H} (hx : x ∈ L) (hy : y ∈ L) {a b : Y}
    (ha : ψ ⟨x, hx⟩ = a) (hb : ψ ⟨y, hy⟩ = b) :
    Nat.card ↥(L ⊓ centralizer ({x} : Set H) ⊓ centralizer ({y} : Set H)) ≤
      Nat.card ↥(centralizer ({a} : Set Y) ⊓ centralizer ({b} : Set Y)) := by
  subst ha hb
  have hz : ∀ z : ↥(L ⊓ centralizer ({x} : Set H) ⊓ centralizer ({y} : Set H)),
      (z : H) ∈ L ∧ (z : H) * x = x * z ∧ (z : H) * y = y * z := by
    intro z
    obtain ⟨⟨h1, h2⟩, h3⟩ := z.2
    exact ⟨h1, Subgroup.mem_centralizer_singleton_iff.1 h2,
      Subgroup.mem_centralizer_singleton_iff.1 h3⟩
  have hmem : ∀ z : ↥(L ⊓ centralizer ({x} : Set H) ⊓ centralizer ({y} : Set H)),
      ψ ⟨(z : H), (hz z).1⟩ ∈ centralizer ({ψ ⟨x, hx⟩} : Set Y) ⊓
        centralizer ({ψ ⟨y, hy⟩} : Set Y) := by
    intro z
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hz z).2.1)
    · rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hz z).2.2)
  refine Nat.card_le_card_of_injective (fun z => ⟨ψ ⟨(z : H), (hz z).1⟩, hmem z⟩) ?_
  intro a b hab
  have h1 : ψ ⟨(a : H), (hz a).1⟩ = ψ ⟨(b : H), (hz b).1⟩ := congrArg Subtype.val hab
  have h2 := ψ.injective h1
  exact Subtype.ext (congrArg (fun w : ↥L => (w : H)) h2)

@[expose] noncomputable def conjEquiv (ψ : ↥L ≃* Y) (c : Y) : ↥L ≃* Y :=
  ψ.trans (MulAut.conj c)

theorem conjEquiv_apply (ψ : ↥L ≃* Y) (c : Y) (x : ↥L) : conjEquiv ψ c x = c * ψ x * c⁻¹ := rfl

theorem not_forall_comm_of_equiv (ψ : ↥L ≃* Y) {u v : H} (hu : u ∈ L) (hv : v ∈ L) {a b : Y}
    (ha : ψ ⟨u, hu⟩ = a) (hb : ψ ⟨v, hv⟩ = b)
    (h : ¬ ∀ y : Y, y * b = b * y → y * a = a * y) :
    ¬ ∀ x ∈ L, x * v = v * x → x * u = u * x := by
  intro hx
  apply h
  subst ha hb
  intro y hy
  have h1 : (ψ.symm y : ↥L) * ⟨v, hv⟩ = ⟨v, hv⟩ * ψ.symm y := by
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy
  have h2 : ((ψ.symm y : ↥L) : H) * v = v * ((ψ.symm y : ↥L) : H) := congrArg Subtype.val h1
  have h3 := hx _ (ψ.symm y).2 h2
  have h4 : (ψ.symm y : ↥L) * ⟨u, hu⟩ = ⟨u, hu⟩ * ψ.symm y := Subtype.ext h3
  have h5 := congrArg ψ h4
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h5

theorem exists_conj_eq_symm (ψ : ↥L ≃* Y) {a : H} (ha : a ∈ L) {r : Y}
    (h : IsConj r (ψ ⟨a, ha⟩)) : ∃ l ∈ L, l * a * l⁻¹ = ((ψ.symm r : ↥L) : H) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  refine ⟨(((ψ.symm g)⁻¹ : ↥L) : H), ((ψ.symm g)⁻¹).2, ?_⟩
  have h1 : (ψ.symm g)⁻¹ * (⟨a, ha⟩ : ↥L) * ((ψ.symm g)⁻¹)⁻¹ = ψ.symm r := by
    apply ψ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← hg]
    group
  exact congrArg Subtype.val h1

end Transport

section JFacts

open CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore CFSG.Blueprint.Fischer

theorem fi23J_card_centralizer_ge {x : J} (hx : orderOf x = 2) :
    318504960 ≤ Nat.card ↥(centralizer ({x} : Set J)) := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  rcases involution_cover x hx2 hx1 with h | h | h
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj, card_centralizer_d]
    norm_num
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj]
    have h3 := fi23J_card_stabilizer_star
    have hle : Nat.card ↥(MulAction.stabilizer ↥Cd
        (⟨d1, d1_mem_localClass⟩ : ↥CFSG.Sporadic.Fi23.star)) ≤
        Nat.card ↥(centralizer ({d * d1} : Set J)) := by
      refine Nat.card_le_card_of_injective (fun a => ⟨(a : Cd), ?_⟩) ?_
      · have hd : (a : J) * d = d * (a : J) := mem_Cd.1 (a : Cd).2
        have hs := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 a.2)
        rw [starAction_val] at hs
        have hd1 : (a : J) * d1 = d1 * (a : J) := by
          calc (a : J) * d1 = (a : J) * d1 * (a : J)⁻¹ * (a : J) := by group
            _ = d1 * (a : J) := by rw [hs]
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc (a : J) * (d * d1) = ((a : J) * d) * d1 := by rw [mul_assoc]
          _ = (d * (a : J)) * d1 := by rw [hd]
          _ = d * ((a : J) * d1) := by rw [mul_assoc]
          _ = d * (d1 * (a : J)) := by rw [hd1]
          _ = (d * d1) * (a : J) := by rw [mul_assoc]
      · intro a b hab
        have hab' := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext hab')
    omega
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj]
    have h3 := CFSG.EvenSporadicStandard.Solomon78.Fi24Row.fi23_card_centralizer_u3
    obtain ⟨c', hc'⟩ := isConj_iff.1 isConj_fi23U2_fi23U3.2
    have h4 := CFSG.Fischer.card_centralizer_conj c' t2
    rw [hc', h3] at h4
    omega

theorem fi23J_card_pair_le_t2 :
    Nat.card ↥(centralizer ({d} : Set J) ⊓ centralizer ({t2} : Set J)) ≤ 2 * 53084160 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥((Cd : Subgroup J) ⊓ centralizer ({t2} : Set J)) =>
      (⟨⟨(x : J), x.2.1⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.1 x.2.2))⟩ :
        ↥(centralizer ({(⟨t2, fi23_t2_mem_Cd⟩ : Cd)} : Set Cd)))) ?_) fi23_card_centralizer_Cd_t2
  intro a b hab
  simp only [Subtype.mk.injEq] at hab
  exact Subtype.ext hab

theorem t2_eq : t2 = d * (d1 * c39) := by
  unfold t2
  rw [mul_assoc]

theorem fi23J_inf_d1c39_eq : centralizer ({d} : Set J) ⊓ centralizer ({d1 * c39} : Set J) =
    centralizer ({d} : Set J) ⊓ centralizer ({t2} : Set J) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [t2_eq]
    calc g * (d * (d1 * c39)) = (g * d) * (d1 * c39) := (mul_assoc g d (d1 * c39)).symm
      _ = (d * g) * (d1 * c39) := by rw [h1]
      _ = d * (g * (d1 * c39)) := mul_assoc d g (d1 * c39)
      _ = d * ((d1 * c39) * g) := by rw [h2]
      _ = (d * (d1 * c39)) * g := (mul_assoc d (d1 * c39) g).symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [t2_eq] at h2
    have h3 : d * (g * (d1 * c39)) = d * ((d1 * c39) * g) := by
      calc d * (g * (d1 * c39)) = (d * g) * (d1 * c39) := (mul_assoc d g (d1 * c39)).symm
        _ = (g * d) * (d1 * c39) := by rw [h1]
        _ = g * (d * (d1 * c39)) := mul_assoc g d (d1 * c39)
        _ = (d * (d1 * c39)) * g := h2
        _ = d * ((d1 * c39) * g) := mul_assoc d (d1 * c39) g
    exact mul_left_cancel h3

theorem fi23J_card_pair_le_d1c39 :
    Nat.card ↥(centralizer ({d} : Set J) ⊓ centralizer ({d1 * c39} : Set J)) ≤ 2 * 53084160 := by
  rw [fi23J_inf_d1c39_eq]
  exact fi23J_card_pair_le_t2

theorem c39_mem_localClass_d1 : c39 ∈ LocalClass D23 d1 := by
  refine ⟨(isConj_d_iff _).2 ⟨⟨39, by norm_num⟩, rfl⟩, fun h => ?_, c39_commute_d1⟩
  have h' : conjPt 39 = conjPt 1 := h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem isConj_d1c39 : IsConj (d * d1) (d1 * c39) :=
  isConj_d_mul_d1_of_mem d1_mem_localClass.1 c39_mem_localClass_d1

theorem fi23J_involution_reps {x : J} (hx : orderOf x = 2) :
    IsConj d x ∨ IsConj (d1 * c39) x ∨ IsConj t2 x := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  rcases involution_cover x hx2 hx1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (isConj_d1c39.symm.trans h))
  · exact Or.inr (Or.inr h)

theorem fi23J_not_le {s₁ : J} (hs₁ : s₁ ∈ LocalClass D23 d) :
    ¬ ∀ x : J, x * s₁ = s₁ * x → x * d = d * x := by
  intro hle
  have hdd1 : d * s₁ = s₁ * d := hs₁.2.2.symm
  have hloc : ∀ x ∈ LocalClass D23 s₁, d * x * d⁻¹ = x := by
    intro x hx
    have hxd : x * d = d * x := hle x hx.2.2
    calc d * x * d⁻¹ = (x * d) * d⁻¹ := by rw [← hxd]
      _ = x := by group
  rcases eq_of_centralizes_star hs₁.1 hdd1 hloc with h | h
  · exact d_ne_one h
  · exact hs₁.2.1 h.symm

theorem fi23J_t2_comm : t2 * d = d * t2 := mem_Cd.1 fi23_t2_mem_Cd

theorem fi23J_d1c39_comm : (d1 * c39) * d = d * (d1 * c39) := by
  have h : d1 * c39 = d * t2 := by
    rw [t2_eq, ← mul_assoc, d_sq, one_mul]
  rw [h]
  calc d * t2 * d = d * (t2 * d) := mul_assoc _ _ _
    _ = d * (d * t2) := by rw [fi23J_t2_comm]

theorem fi23J_card_pair_le {r : J} (hr : r = d1 * c39 ∨ r = t2) :
    Nat.card ↥(centralizer ({d} : Set J) ⊓ centralizer ({r} : Set J)) ≤ 2 * 53084160 := by
  rcases hr with rfl | rfl
  · exact fi23J_card_pair_le_d1c39
  · exact fi23J_card_pair_le_t2

theorem fi22_innerAut_index_le_two :
    (AutInner.innerAut (Carrier .Fi22)).index ≤ 2 := by
  have h := CFSG.RankThree.PartOne.card_outer_fi22_carrier
  have h2 : (AutInner.innerAut (Carrier .Fi22)).index =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        CFSG.Blueprint.NativeSporadic.Fi22) := Subgroup.index_eq_card _
  rw [h2]
  exact h.le

theorem fi23D_innerAut_index_le_two : (AutInner.innerAut Fi23D).index ≤ 2 :=
  AutInner.index_innerAut_le_two (Group.isPerfect_def.1 fi23D_isQuasisimple.1) fi23D_cq.some
    CFSG.EvenSporadicStandard.center_Fi22_eq_bot fi22_innerAut_index_le_two

@[expose] noncomputable def fi23JConj {H : Type} [Group H] {L : Subgroup H} (ψ : ↥L ≃* J)
    (c : J) : ↥L ≃* J :=
  @conjEquiv H _ L J (inferInstance) ψ c

theorem fi23JConj_apply {H : Type} [Group H] {L : Subgroup H} (ψ : ↥L ≃* J) (c : J) (x : ↥L) :
    fi23JConj ψ c x = c * ψ x * c⁻¹ :=
  @conjEquiv_apply H _ L J (inferInstance) ψ c x

theorem fi23J_card_centralizer_le_inf {H : Type} [Group H] {L : Subgroup H} (ψ : ↥L ≃* J)
    {x : H} (hx : x ∈ L) {a : J} (ha : ψ ⟨x, hx⟩ = a) :
    Nat.card ↥(centralizer ({a} : Set J)) ≤ Nat.card ↥(L ⊓ centralizer ({x} : Set H)) :=
  @card_centralizer_le_card_inf H _ L J (inferInstance) ψ x hx a ha

theorem fi23J_card_inf_inf_le {H : Type} [Group H] {L : Subgroup H} (ψ : ↥L ≃* J) {x y : H}
    (hx : x ∈ L) (hy : y ∈ L) {a b : J} (ha : ψ ⟨x, hx⟩ = a) (hb : ψ ⟨y, hy⟩ = b) :
    Nat.card ↥(L ⊓ centralizer ({x} : Set H) ⊓ centralizer ({y} : Set H)) ≤
      Nat.card ↥(centralizer ({a} : Set J) ⊓ centralizer ({b} : Set J)) :=
  @card_inf_inf_le H _ L J (inferInstance) (inferInstance) ψ x y hx hy a b ha hb

theorem fi23J_not_forall_comm {H : Type} [Group H] {L : Subgroup H} (ψ : ↥L ≃* J) {u v : H}
    (hu : u ∈ L) (hv : v ∈ L) {a b : J} (ha : ψ ⟨u, hu⟩ = a) (hb : ψ ⟨v, hv⟩ = b)
    (h : ¬ ∀ y : J, y * b = b * y → y * a = a * y) :
    ¬ ∀ x ∈ L, x * v = v * x → x * u = u * x :=
  @not_forall_comm_of_equiv H _ L J (inferInstance) ψ u v hu hv a b ha hb h

theorem fi23J_exists_conj_eq_symm {H : Type} [Group H] {L : Subgroup H} (ψ : ↥L ≃* J) {a : H}
    (ha : a ∈ L) {r : J} (h : IsConj r (ψ ⟨a, ha⟩)) :
    ∃ l ∈ L, l * a * l⁻¹ = ((ψ.symm r : ↥L) : H) :=
  @exists_conj_eq_symm H _ L J (inferInstance) ψ a ha r h

theorem not_isConj_of_rep {H : Type} [Group H] [Finite H] {L : Subgroup H} {t u : H}
    (hs : Setting612 H L t)
    (hbal : centralizer (L : Set H) ⊓ centralizer ({t} : Set H) = zpowers t)
    (hZ : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1)
    (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hCK : centralizer ((L ⊓ centralizer ({u} : Set H) : Subgroup H) : Set H) ≤
      (L ⊓ centralizer ({u} : Set H)) ⊔ centralizer (L : Set H))
    (hnorm : ∀ g ∈ centralizer ({u} : Set H), ∀ k ∈ L ⊓ centralizer ({u} : Set H),
      g * k * g⁻¹ ∈ L ⊓ centralizer ({u} : Set H))
    (hInn : (AutInner.innerAut ↥(L ⊓ centralizer ({u} : Set H))).index ≤ 2)
    (ψ : ↥L ≃* J) (hψu : ψ ⟨u, hu⟩ = d) {r : J} (hr : r = d1 * c39 ∨ r = t2) :
    ¬ IsConj t (t * ((ψ.symm r : ↥L) : H)) := by
  intro hcj
  have hrd : r * d = d * r := by
    rcases hr with rfl | rfl
    · exact fi23J_d1c39_comm
    · exact fi23J_t2_comm
  have ha₁ : ((ψ.symm r : ↥L) : H) ∈ L := (ψ.symm r).2
  have hψa₁ : ψ ⟨((ψ.symm r : ↥L) : H), ha₁⟩ = r := ψ.apply_symm_apply r
  have hau : ((ψ.symm r : ↥L) : H) * u = u * ((ψ.symm r : ↥L) : H) := by
    have h1 : (ψ.symm r : ↥L) * ⟨u, hu⟩ = ⟨u, hu⟩ * ψ.symm r := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hψu]
      exact hrd
    exact congrArg Subtype.val h1
  obtain ⟨p, hp, hp2, hp1, hcard⟩ :=
    fusion_centralizer_le hs hbal hZ hu hu2 hu1 ha₁ hau hCK hnorm hInn hcj
  have hpord : orderOf (ψ ⟨p, hp⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul]
      have h : (⟨p, hp⟩ : ↥L) * ⟨p, hp⟩ = 1 := Subtype.ext hp2
      rw [h, map_one]
    · intro h
      apply hp1
      have h' : ψ ⟨p, hp⟩ = ψ 1 := h.trans (map_one ψ).symm
      exact congrArg Subtype.val (ψ.injective h')
  have hlow := fi23J_card_centralizer_ge hpord
  have hlow' := fi23J_card_centralizer_le_inf ψ hp (rfl : ψ ⟨p, hp⟩ = ψ ⟨p, hp⟩)
  have hup := fi23J_card_inf_inf_le ψ hu ha₁ hψu hψa₁
  have hpair := fi23J_card_pair_le hr
  omega

theorem fi23Claim612EStarAt_of_balance (hmult : OddMultTrivial .Fi23) {H : Type} [Group H]
    [Finite H] (hBal : Fi23BalanceAt H) : Fi23Claim612EStarAt H := by
  intro N L K t u hN hidx hkp hcov hglob hfi hT _ hS a haL ha2 hna hconj
  obtain ⟨e⟩ := hcov.isSporadic_of_mult hmult
  have hL : IsSporadic ↥L .Fi23 := ⟨e⟩
  have hbal := hBal N L hN hidx hkp hglob.standardL hcov hS t hglob.t_mem hglob.t_order
  have hs := fi23_setting612 hmult hcov hglob.standardL hglob.t_mem hglob.t_order hbal
  have hZ0 : center ↥L = ⊥ := hcov.center_eq_bot hmult
  have hZ : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 := by
    intro x hx hc
    have h1 : (⟨x, hx⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [hZ0, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hinnL : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l :=
    AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  have hN' : normalizer (L : Set H) ≤ L ⊔ centralizer (L : Set H) :=
    normalizer_le_sup_centralizer_of_mulAut_inner hinnL
  obtain ⟨hKeq, hmaxK, l, hl, hlK, hlne⟩ := fi23_cover_facts hL hfi
  have hcenter := fi23_center_facts hL hfi
  obtain ⟨f⟩ := fi23_pair_equiv hL hfi
  have hglob35 := hglob.hyp35
  subst hKeq
  obtain ⟨huL, hu2, hcardu⟩ := hT
  have hu2' : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have hu1 : u ≠ 1 := ne_one_of_orderOf_eq_two hu2
  have huK : u ∈ L ⊓ centralizer ({u} : Set H) :=
    ⟨huL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hCL : ∀ y ∈ L, (∀ k ∈ L ⊓ centralizer ({u} : Set H), y * k = k * y) →
      y ∈ L ⊓ centralizer ({u} : Set H) := by
    intro y hy hc
    rcases hcenter y hy hc with rfl | rfl
    · exact (L ⊓ centralizer ({u} : Set H)).one_mem
    · exact huK
  have hnorm : ∀ g ∈ centralizer ({u} : Set H), ∀ k ∈ L ⊓ centralizer ({u} : Set H),
      g * k * g⁻¹ ∈ L ⊓ centralizer ({u} : Set H) := by
    intro g hg k hk
    have h : (L ⊓ centralizer ({u} : Set H)).map (MulAut.conj g).toMonoidHom =
        L ⊓ centralizer ({u} : Set H) := (map_conj_eq_of_hyp35 hglob35 hg).2
    have hmem : g * k * g⁻¹ ∈ (L ⊓ centralizer ({u} : Set H)).map (MulAut.conj g).toMonoidHom :=
      ⟨k, hk, rfl⟩
    rw [h] at hmem
    exact hmem
  let ψ0 : ↥L ≃* J := e.trans fi23EquivJ
  have hs2 : orderOf (ψ0 ⟨u, huL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
  have hcardJ : Nat.card ↥(centralizer ({ψ0 ⟨u, huL⟩} : Set J)) = 129123503308800 := by
    rw [← @fi23_card_inf_centralizer_eq H J _ (inferInstance) L ψ0 u huL]
    exact hcardu
  obtain ⟨c0, hc0⟩ := isConj_iff.1 (fi23J_isConj_d_of_card hs2 hcardJ)
  let ψ : ↥L ≃* J := fi23JConj ψ0 c0⁻¹
  have hψu : ψ ⟨u, huL⟩ = d := by
    rw [fi23JConj_apply, ← hc0]
    group
  have hu₁L : l * u * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl huL) (L.inv_mem hl)
  have hs₁ : ψ ⟨l * u * l⁻¹, hu₁L⟩ ∈ LocalClass D23 d := by
    have hmk : (⟨l * u * l⁻¹, hu₁L⟩ : ↥L) = ⟨l, hl⟩ * ⟨u, huL⟩ * ⟨l, hl⟩⁻¹ := rfl
    have hψu₁ : ψ ⟨l * u * l⁻¹, hu₁L⟩ = ψ ⟨l, hl⟩ * d * (ψ ⟨l, hl⟩)⁻¹ := by
      rw [hmk, map_mul, map_mul, map_inv, hψu]
    refine ⟨?_, ?_, ?_⟩
    · rw [hψu₁]
      exact conj_mem_D23 _ _ d_mem_D23
    · intro h
      apply hlne
      exact congrArg Subtype.val (ψ.injective (h.trans hψu.symm))
    · have hc : (l * u * l⁻¹) * u = u * (l * u * l⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.1 hlK.2
      have h1 : (⟨l * u * l⁻¹, hu₁L⟩ : ↥L) * ⟨u, huL⟩ = ⟨u, huL⟩ * ⟨l * u * l⁻¹, hu₁L⟩ :=
        Subtype.ext hc
      have h2 := congrArg ψ h1
      rwa [map_mul, map_mul, hψu] at h2
  have hne : ¬ ∀ x ∈ L, x * (l * u * l⁻¹) = (l * u * l⁻¹) * x → x * u = u * x :=
    fi23J_not_forall_comm ψ huL hu₁L hψu rfl (fi23J_not_le hs₁)
  have hCK := centralizer_inf_le_sup_centralizer hmaxK hnorm hl hlK hne hN' hCL
  have hInn : (AutInner.innerAut ↥(L ⊓ centralizer ({u} : Set H))).index ≤ 2 := by
    rw [← AutInner.index_innerAut_congr f]
    exact fi23D_innerAut_index_le_two
  have ha_ord : orderOf (ψ ⟨a, haL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ha2]
  have hna' : ¬ IsConj d (ψ ⟨a, haL⟩) := by
    intro hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    apply hna
    refine ⟨((ψ.symm g : ↥L) : H), (ψ.symm g).2, ?_⟩
    have h1 : (⟨a, haL⟩ : ↥L) = ψ.symm g * ⟨u, huL⟩ * (ψ.symm g)⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hψu, hg]
    exact congrArg Subtype.val h1
  have core : ∀ r : J, (r = d1 * c39 ∨ r = t2) → ¬ IsConj t (t * ((ψ.symm r : ↥L) : H)) :=
    fun r hr => not_isConj_of_rep hs hbal hZ huL hu2' hu1 hCK hnorm hInn ψ hψu hr
  rcases fi23J_involution_reps ha_ord with h | h | h
  · exact hna' h
  · obtain ⟨l', hl', hl'a⟩ := fi23J_exists_conj_eq_symm ψ haL h
    have h1 := hs.isConj_mul_conj hconj hl'
    rw [hl'a] at h1
    exact core _ (Or.inl rfl) h1
  · obtain ⟨l', hl', hl'a⟩ := fi23J_exists_conj_eq_symm ψ haL h
    have h1 := hs.isConj_mul_conj hconj hl'
    rw [hl'a] at h1
    exact core _ (Or.inr rfl) h1

theorem fi23Claim612EStarHered_of_balance (hmult : OddMultTrivial .Fi23)
    (hBal : Fi23BalanceHered) : Fi23Claim612EStarHered :=
  fun H _ _ hH => fi23Claim612EStarAt_of_balance hmult (hBal H hH)

end JFacts

end CFSG.EvenSporadicStandard.Induction.Fi.V3
