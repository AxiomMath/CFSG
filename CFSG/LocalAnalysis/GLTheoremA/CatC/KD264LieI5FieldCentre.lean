module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Field

open CFSG.Open
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem mem_center_iff_of_surjective_ker {L K : Type} [Group L] [Group K] [Group.IsPerfect L]
    (π : L →* K) (hs : Function.Surjective π) (hk : ∀ x : L, π x = 1 → x ∈ Subgroup.center L)
    (x : L) : π x ∈ Subgroup.center K ↔ x ∈ Subgroup.center L := by
  constructor
  · intro hx
    have hcomm : ∀ y : L, π x * π y = π y * π x := fun y =>
      ((Subgroup.mem_center_iff.mp hx) (π y)).symm
    have hcen : ∀ y : L, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center L := by
      intro y
      apply hk
      have h := hcomm y
      simp only [map_mul, map_inv]
      rw [h]
      group
    let φ : L →* Subgroup.center L :=
      { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hcen y⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y z => Subtype.ext (by
          have h := Subgroup.mem_center_iff.mp (hcen z) y
          show x * (y * z) * x⁻¹ * (y * z)⁻¹ =
            (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)
          calc x * (y * z) * x⁻¹ * (y * z)⁻¹
              = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
            _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [h]; group) }
    have hφ : φ = 1 := hom_eq_one_of_commutative φ
    have hy : ∀ y : L, x * y * x⁻¹ * y⁻¹ = 1 := by
      intro y
      have h := congrArg (fun f : L →* Subgroup.center L => ((f y : Subgroup.center L) : L)) hφ
      simpa [φ] using h
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : x * g * x⁻¹ = g := mul_inv_eq_one.mp (hy g)
    calc g * x = (x * g * x⁻¹) * x := by rw [h2]
      _ = x * g := by group
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨y, rfl⟩ := hs k
    have h := Subgroup.mem_center_iff.mp hx y
    show π y * π x = π x * π y
    rw [← map_mul, ← map_mul, h]

theorem card_three_torsion_le (G : Type) [Group G] [Finite G] [IsCyclic G] :
    Nat.card {x : G // x ^ 3 = 1} ≤ 3 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem card_le_three_of_isElemAbelian_le {K : Type} [Group K] [Finite K] {H E : Subgroup K}
    [IsCyclic H] (hEH : E ≤ H) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have h := card_three_torsion_le H
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : E => (⟨⟨x.1, hEH x.2⟩, by
      apply Subtype.ext
      exact hE.2 x.1 x.2⟩ : {x : H // x ^ 3 = 1})) ?_) h
  intro x y hxy
  have := congrArg (fun t : {x : H // x ^ 3 = 1} => (t.1 : K)) hxy
  exact Subtype.ext this

theorem mem_of_three_torsion_le {K : Type} [Group K] [Finite K] {H F : Subgroup K} [IsCyclic H]
    (hFH : F ≤ H) (hF : IsElemAbelian 3 F) (hcard : Nat.card F = 3) {x : K} (hxH : x ∈ H)
    (hx : x ^ 3 = 1) : x ∈ F := by
  by_contra hxF
  have hle := card_three_torsion_le H
  have hx' : (⟨x, hxH⟩ : H) ^ 3 = 1 := Subtype.ext hx
  have hinj : Function.Injective (fun o : Option F =>
      (match o with
        | none => (⟨⟨x, hxH⟩, hx'⟩ : {y : H // y ^ 3 = 1})
        | some f => ⟨⟨f.1, hFH f.2⟩, Subtype.ext (hF.2 f.1 f.2)⟩)) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some g =>
        exfalso
        apply hxF
        have := congrArg (fun t : {y : H // y ^ 3 = 1} => (t.1 : K)) hab
        simp only at this
        exact this ▸ g.2
    | some f =>
      cases b with
      | none =>
        exfalso
        apply hxF
        have := congrArg (fun t : {y : H // y ^ 3 = 1} => (t.1 : K)) hab
        simp only at this
        exact this ▸ f.2
      | some g =>
        have := congrArg (fun t : {y : H // y ^ 3 = 1} => (t.1 : K)) hab
        simp only at this
        congr 1
        exact Subtype.ext this
  have h4 := Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option, hcard] at h4
  omega

theorem pRank_three_le_one_of_isCyclic {K : Type} [Group K] [Finite K] (H : Subgroup K)
    [IsCyclic H] : CFSG.Open.pRank 3 H ≤ 1 := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, hEH, hE, hcard⟩
  have h := card_le_three_of_isElemAbelian_le hEH hE
  rw [hcard] at h
  have : 3 ^ k ≤ 3 ^ 1 := by simpa using h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

theorem le_pRank_three_of_card {K : Type} [Group K] [Finite K] {H E : Subgroup K}
    (hEH : E ≤ H) (hE : IsElemAbelian 3 E) {m : ℕ} (hm : Nat.card E = 3 ^ m) :
    m ≤ CFSG.Open.pRank 3 H := by
  unfold CFSG.Open.pRank
  have hbdd : BddAbove {k : ℕ | ∃ E' : Subgroup K, E' ≤ H ∧ IsElemAbelian 3 E' ∧
      Nat.card E' = 3 ^ k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨E', _, _, hk⟩
    have h1 : Nat.card E' ≤ Nat.card K := Subgroup.card_le_card_group E'
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  exact le_csSup hbdd ⟨E, hEH, hE, hm⟩

theorem exists_card_pRank_three {K : Type} [Group K] [Finite K] (H : Subgroup K) :
    ∃ E : Subgroup K, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ CFSG.Open.pRank 3 H := by
  have hbdd : BddAbove {k : ℕ | ∃ E' : Subgroup K, E' ≤ H ∧ IsElemAbelian 3 E' ∧
      Nat.card E' = 3 ^ k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨E', _, _, hk⟩
    have h1 : Nat.card E' ≤ Nat.card K := Subgroup.card_le_card_group E'
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have hne : {k : ℕ | ∃ E' : Subgroup K, E' ≤ H ∧ IsElemAbelian 3 E' ∧
      Nat.card E' = 3 ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
        rw [Subgroup.mem_bot] at hx
        rw [hx, one_pow]⟩, by simp⟩
  obtain ⟨E, hEH, hE, hcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEH, hE, hcard⟩

theorem isElemAbelian_map {L K : Type} [Group L] [Group K] {E : Subgroup L}
    (hE : IsElemAbelian 3 E) (π : L →* K) : IsElemAbelian 3 (E.map π) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : K) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hE ha' hb']
  · intro x hx
    obtain ⟨a', ha', ha⟩ := hx
    rw [← ha, ← map_pow, hE.2 a' ha', map_one]

theorem card_map_mul_card_inf_ker {L K : Type} [Group L] [Group K] [Finite L] (π : L →* K)
    (E : Subgroup L) : Nat.card ↥(E.map π) * Nat.card ↥(E ⊓ π.ker) = Nat.card ↥E := by
  have h := Subgroup.card_ker_mul_card_range (π.comp E.subtype)
  have h1 : (π.comp E.subtype).range = E.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : Nat.card ↥(π.comp E.subtype).ker = Nat.card ↥(E ⊓ π.ker) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1.1, by
          have hx := x.2
          rw [MonoidHom.mem_ker] at hx
          exact Subgroup.mem_inf.mpr ⟨x.1.2, (MonoidHom.mem_ker).mpr hx⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, by
          rw [MonoidHom.mem_ker]
          exact (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2)⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := fun y => by
          apply Subtype.ext
          rfl }
  rw [← h2, ← h1, mul_comm]
  exact h

theorem pow_three_eq_one_of_mem_zpowers {K : Type} [Group K] {z w : K} (hz3 : z ^ 3 = 1)
    (hw : w ∈ Subgroup.zpowers z) : w ^ 3 = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hz3]

theorem isElemAbelian_sup_zpowers {K : Type} [Group K] {E : Subgroup K}
    (hE : IsElemAbelian 3 E) {z : K} (hz : z ∈ Subgroup.center K) (hz3 : z ^ 3 = 1) :
    IsElemAbelian 3 (E ⊔ Subgroup.zpowers z) := by
  have hzc : ∀ n ∈ Subgroup.zpowers z, ∀ g : K, g * n = n * g := by
    intro n hn g
    have hn' : n ∈ Subgroup.center K := (Subgroup.zpowers_le.mpr hz) hn
    exact Subgroup.mem_center_iff.mp hn' g
  haveI : (Subgroup.zpowers z).Normal :=
    ⟨fun n hn g => by
      have e : g * n * g⁻¹ = n := by rw [hzc n hn g]; group
      rw [e]
      exact hn⟩
  have hcomm : ∀ a ∈ E ⊔ Subgroup.zpowers z, ∀ b ∈ E ⊔ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_sup_of_normal_right] at ha hb
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := ha
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := hb
    have e1 : y1 * y2 = y2 * y1 := isElemAbelian_commute hE hy1 hy2
    have h1 : z1 * y2 = y2 * z1 := (hzc z1 hz1 y2).symm
    have h2 : z2 * y1 = y1 * z2 := (hzc z2 hz2 y1).symm
    have h3 : z1 * z2 = z2 * z1 := (hzc z1 hz1 z2).symm
    calc y1 * z1 * (y2 * z2) = y1 * (z1 * y2) * z2 := by group
      _ = (y1 * y2) * (z1 * z2) := by rw [h1]; group
      _ = (y2 * y1) * (z2 * z1) := by rw [e1, h3]
      _ = y2 * (y1 * z2) * z1 := by group
      _ = y2 * (z2 * y1) * z1 := by rw [h2]
      _ = y2 * z2 * (y1 * z1) := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
  intro x hx
  rw [Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨y, hy, w, hw, rfl⟩ := hx
  have hyw : Commute y w := (hzc w hw y)
  rw [hyw.mul_pow, hE.2 y hy, pow_three_eq_one_of_mem_zpowers hz3 hw, one_mul]

theorem isElemAbelian_zpowers_of_pow {K : Type} [Group K] {g : K} (hg : g ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers g) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    show (a : K) * b = b * a
    rw [← hm, ← hn]
    exact Commute.zpow_zpow_self g m n
  · intro x hx
    exact pow_three_eq_one_of_mem_zpowers hg hx

theorem one_le_pRank_three_of_three_dvd {K : Type} [Group K] [Finite K] (H : Subgroup K)
    (h : 3 ∣ Nat.card H) : 1 ≤ CFSG.Open.pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card (G := H) 3 (by
    rw [← Nat.card_eq_fintype_card]; exact h)
  have hw3 : (w : K) ^ 3 = 1 := by
    have h1 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    simpa using congrArg Subtype.val h1
  have hEH : Subgroup.zpowers (w : K) ≤ H := by
    rw [Subgroup.zpowers_le]
    exact w.2
  have hcard : Nat.card (Subgroup.zpowers (w : K)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
  exact le_pRank_three_of_card hEH (isElemAbelian_zpowers_of_pow hw3) (m := 1)
    (by rw [hcard]; norm_num)

theorem apply_eq_self_of_orderOf_three {K : Type} [Group K] [Finite K]
    [IsCyclic (Subgroup.center K)] (β : MulAut K) (hβ : β ^ 3 = 1) {z : K}
    (hz : z ∈ Subgroup.center K) (hz3 : orderOf z = 3) : β z = z := by
  have hzc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  have hβz : β z ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg β (hzc (β.symm g))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  have hzpow3 : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have hβz3 : (β z) ^ 3 = 1 := by
    rw [← map_pow, hzpow3, map_one]
  have hzF : Subgroup.zpowers z ≤ Subgroup.center K := Subgroup.zpowers_le.mpr hz
  have hcardF : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_of_three_torsion_le (H := Subgroup.center K) (F := Subgroup.zpowers z) hzF
      (isElemAbelian_zpowers_of_pow hzpow3) hcardF hβz hβz3)
  have h3 : ∀ x : K, β (β (β x)) = x := by
    intro x
    have := congrArg (fun f : MulAut K => f x) hβ
    simpa [pow_succ] using this
  have e1 : β (β z) = z ^ (n * n) := by
    rw [← hn, map_zpow, ← hn, ← zpow_mul]
  have e2 : β (β (β z)) = z ^ (n * n * n) := by
    rw [e1, map_zpow, ← hn, ← zpow_mul, mul_assoc]
  have h4 : z ^ (n * n * n) = z := by rw [← e2]; exact h3 z
  have h5 : z ^ (n * n * n - 1) = 1 := by rw [zpow_sub_one, h4, mul_inv_cancel]
  have h6 : (orderOf z : ℤ) ∣ n * n * n - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h5
  rw [hz3] at h6
  have h8 : ((n * n * n - 1 : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h6)
  have h9 : (n : ZMod 3) * (n : ZMod 3) * (n : ZMod 3) - 1 = 0 := by
    push_cast at h8
    exact h8
  have key : ∀ x : ZMod 3, x * x * x - 1 = 0 → x = 1 := by decide
  have h7 : (n : ZMod 3) = 1 := key _ h9
  have h10 : ((n - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast
    rw [h7]
    ring
  have h11 : (3 : ℤ) ∣ n - 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h10
    exact_mod_cast this
  have h12 : z ^ (n - 1) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz3]; exact_mod_cast h11)
  rw [← hn]
  have h13 : z ^ n = z ^ (n - 1) * z := by
    rw [← zpow_add_one]
    congr 1
    ring
  rw [h13, h12, one_mul]

def centerMap {L K : Type} [Group L] [Group K] [Group.IsPerfect L] (π : L →* K)
    (hs : Function.Surjective π) (hk : ∀ x : L, π x = 1 → x ∈ Subgroup.center L) :
    Subgroup.center L →* Subgroup.center K :=
  (π.comp (Subgroup.center L).subtype).codRestrict (Subgroup.center K)
    (fun x => (mem_center_iff_of_surjective_ker π hs hk x.1).mpr x.2)

theorem centerMap_surjective {L K : Type} [Group L] [Group K] [Group.IsPerfect L] (π : L →* K)
    (hs : Function.Surjective π) (hk : ∀ x : L, π x = 1 → x ∈ Subgroup.center L) :
    Function.Surjective (centerMap π hs hk) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, rfl⟩ := hs z
  have hx : x ∈ Subgroup.center L := (mem_center_iff_of_surjective_ker π hs hk x).mp hz
  exact ⟨⟨x, hx⟩, rfl⟩

theorem isCyclic_center_of_surjective {L K : Type} [Group L] [Group K] [Group.IsPerfect L]
    [IsCyclic (Subgroup.center L)] (π : L →* K) (hs : Function.Surjective π)
    (hk : ∀ x : L, π x = 1 → x ∈ Subgroup.center L) : IsCyclic (Subgroup.center K) :=
  isCyclic_of_surjective (centerMap π hs hk) (centerMap_surjective π hs hk)

theorem exists_quotient_equiv {L K : Type} [Group L] [Group K] [Group.IsPerfect L]
    (π : L →* K) (hs : Function.Surjective π) (hk : ∀ x : L, π x = 1 → x ∈ Subgroup.center L) :
    ∃ θ : L ⧸ Subgroup.center L ≃* K ⧸ Subgroup.center K,
      ∀ x : L, θ (QuotientGroup.mk' (Subgroup.center L) x) =
        QuotientGroup.mk' (Subgroup.center K) (π x) := by
  have hle : Subgroup.center L ≤ (Subgroup.center K).comap π := by
    intro x hx
    exact (mem_center_iff_of_surjective_ker π hs hk x).mpr hx
  let f := QuotientGroup.map (Subgroup.center L) (Subgroup.center K) π hle
  have hfx : ∀ x : L, f (QuotientGroup.mk' (Subgroup.center L) x) =
      QuotientGroup.mk' (Subgroup.center K) (π x) := fun x => rfl
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    rw [hfx] at hq
    have h1 : π x ∈ Subgroup.center K := (QuotientGroup.eq_one_iff (π x)).mp hq
    have h2 : x ∈ Subgroup.center L := (mem_center_iff_of_surjective_ker π hs hk x).mp h1
    exact (QuotientGroup.eq_one_iff x).mpr h2
  have hf_surj : Function.Surjective f := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    obtain ⟨x, rfl⟩ := hs k
    exact ⟨QuotientGroup.mk' (Subgroup.center L) x, hfx x⟩
  exact ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩, fun x => hfx x⟩

theorem congr_onCenterQuotient {L K : Type} [Group L] [Group K]
    (θ : L ⧸ Subgroup.center L ≃* K ⧸ Subgroup.center K) (π : L →* K) (βL : MulAut L)
    (β : MulAut K) (hθ : ∀ x : L, θ (QuotientGroup.mk' (Subgroup.center L) x) =
      QuotientGroup.mk' (Subgroup.center K) (π x))
    (hβ : ∀ x : L, π (βL x) = β (π x)) :
    MulAut.congr θ (onCenterQuotient βL) = onCenterQuotient β := by
  apply MulEquiv.ext
  intro q
  obtain ⟨p, rfl⟩ := θ.surjective q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) p
  show θ (onCenterQuotient βL (θ.symm (θ (QuotientGroup.mk' (Subgroup.center L) x)))) =
    onCenterQuotient β (θ (QuotientGroup.mk' (Subgroup.center L) x))
  rw [MulEquiv.symm_apply_apply, onCenterQuotient_apply_mk, hθ, hβ, hθ, onCenterQuotient_apply_mk]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Field

end
