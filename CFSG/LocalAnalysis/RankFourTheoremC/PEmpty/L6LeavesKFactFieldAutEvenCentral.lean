module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open Subgroup CFSG.LieType.BorelTits
open CFSG.Open (pCoreOf)

theorem exists_lift_orderOf {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) {r : ℕ} (hr : r.Prime) (hrZ : ¬ r ∣ Nat.card Z)
    (s : G ⧸ Z) (hs : orderOf s = r) : ∃ g : G, orderOf g = r ∧ (g : G ⧸ Z) = s := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective s
  have hsr : s ^ r = 1 := hs ▸ pow_orderOf_eq_one s
  have hg₀r : g₀ ^ r ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg₀]
    exact hsr
  have hcop : (Nat.card Z).Coprime r :=
    ((Nat.Prime.coprime_iff_not_dvd hr).2 hrZ).symm
  obtain ⟨w, hw⟩ := (powCoprime hcop).surjective ⟨g₀ ^ r, hg₀r⟩
  have hwr : (w : G) ^ r = g₀ ^ r := by
    have := congrArg Subtype.val hw
    simpa [powCoprime_apply] using this
  have hcomm0 : Commute g₀ (w : G) := Subgroup.mem_center_iff.mp (hZc w.2) g₀
  have hcomm : Commute g₀ (w : G)⁻¹ := hcomm0.inv_right
  have hgr : (g₀ * (w : G)⁻¹) ^ r = 1 := by
    rw [hcomm.mul_pow, inv_pow, hwr, mul_inv_cancel]
  have hπ : ((g₀ * (w : G)⁻¹ : G) : G ⧸ Z) = s := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff (w : G)).2 w.2,
      inv_one, mul_one, hg₀]
  have hg1 : g₀ * (w : G)⁻¹ ≠ 1 := by
    intro h1
    rw [h1, QuotientGroup.mk_one] at hπ
    rw [← hπ, orderOf_one] at hs
    exact hr.one_lt.ne hs
  exact ⟨g₀ * (w : G)⁻¹, orderOf_eq_prime hgr hg1, hπ⟩

theorem exists_two_subgroup_preimage {G : Type*} [Group G] [Finite G] (Z : Subgroup G)
    [Z.Normal] (hZc : Z ≤ Subgroup.center G) (R : Subgroup (G ⧸ Z)) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) :
    pCoreOf 2 (R.comap (QuotientGroup.mk' Z)) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rt : Subgroup G := R.comap (QuotientGroup.mk' Z) with hRt
  have hmem : ∀ x : G, x ∈ Rt ↔ (x : G ⧸ Z) ∈ R := fun x => Iff.rfl
  let f : ↥Rt →* ↥R :=
    ((QuotientGroup.mk' Z).comp Rt.subtype).codRestrict R (fun x => x.2)
  have hfval : ∀ x : ↥Rt, ((f x : ↥R) : G ⧸ Z) = ((x : G) : G ⧸ Z) := fun x => rfl
  have hker : f.ker ≤ Subgroup.center ↥Rt := by
    intro x hx
    have hx1 : f x = 1 := hx
    have hπx : ((x : G) : G ⧸ Z) = 1 := by
      rw [← hfval x, hx1]
      rfl
    have hxZ : (x : G) ∈ Z := (QuotientGroup.eq_one_iff (x : G)).1 hπx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZc hxZ)) (y : G))
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  haveI : Group.IsNilpotent ↥Rt := _root_.isNilpotent_of_ker_le_center f hker
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : G ⧸ Z)
    refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
    · rw [hmem, hx]
      exact y.2
    · rw [hfval]
      exact hx
  have h2R : 2 ∣ Nat.card R := by
    obtain ⟨n, hn, hcard⟩ := (hR2.nontrivial_iff_card).1
      ((Subgroup.nontrivial_iff_ne_bot R).2 hR1)
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  have h2Rt : 2 ∣ Nat.card Rt := h2R.trans (Subgroup.card_dvd_of_surjective hfsurj)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥Rt))
  have hPcard : Nat.card (P : Subgroup ↥Rt) = 2 ^ (Nat.card Rt).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hfac : 1 ≤ (Nat.card Rt).factorization 2 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2Rt)
  set N : Subgroup G := (P : Subgroup ↥Rt).map Rt.subtype with hN
  have hNRt : N ≤ Rt := Subgroup.map_subtype_le _
  have hNP : N.subgroupOf Rt = (P : Subgroup ↥Rt) := by
    rw [hN, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Rt.subtype_injective]
  have hNnorm : (N.subgroupOf Rt).Normal := by
    rw [hNP]
    exact inferInstance
  have hNp : IsPGroup 2 N := P.isPGroup'.map Rt.subtype
  have hle : N ≤ pCoreOf 2 Rt := le_pCoreOf 2 hNRt hNnorm hNp
  intro hbot
  have hNbot : N = ⊥ := le_bot_iff.mp (hbot ▸ hle)
  have hPbot : (P : Subgroup ↥Rt) = ⊥ := by
    rw [hN] at hNbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ Rt.subtype_injective).1 hNbot
  rw [hPbot, Subgroup.card_bot] at hPcard
  have : 2 ≤ 2 ^ (Nat.card Rt).factorization 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (Nat.card Rt).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  omega

theorem exists_lift_normalizing {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) {r : ℕ} (hr : r.Prime) (hrZ : ¬ r ∣ Nat.card Z)
    (R : Subgroup (G ⧸ Z)) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hrN : r ∣ Nat.card (Subgroup.normalizer (R : Set (G ⧸ Z)))) :
    ∃ (g : G) (R' : Subgroup G), orderOf g = r ∧ IsPGroup 2 R' ∧ R' ≠ ⊥ ∧
      ∀ x : G, x ∈ R' ↔ g * x * g⁻¹ ∈ R' := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (R : Set (G ⧸ Z)))) r hrN
  have hs' : orderOf (s : G ⧸ Z) = r := by rw [Subgroup.orderOf_coe]; exact hs
  have hsN : (s : G ⧸ Z) ∈ Subgroup.normalizer (R : Set (G ⧸ Z)) := s.2
  obtain ⟨g, hgord, hgs⟩ := exists_lift_orderOf Z hZc hr hrZ (s : G ⧸ Z) hs'
  set Rt : Subgroup G := R.comap (QuotientGroup.mk' Z) with hRt
  have hgN : ∀ x : G, x ∈ Rt ↔ g * x * g⁻¹ ∈ Rt := by
    intro x
    have h := Subgroup.mem_normalizer_iff.mp hsN (x : G ⧸ Z)
    have e : ((g * x * g⁻¹ : G) : G ⧸ Z) = (s : G ⧸ Z) * (x : G ⧸ Z) * (s : G ⧸ Z)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgs]
    show (x : G ⧸ Z) ∈ R ↔ ((g * x * g⁻¹ : G) : G ⧸ Z) ∈ R
    rw [e]
    exact h
  have hgnorm : g ∈ Subgroup.normalizer (Rt : Set G) := Subgroup.mem_normalizer_iff.2 hgN
  have hgcore := normalizer_le_normalizer_pCoreOf 2 Rt hgnorm
  refine ⟨g, pCoreOf 2 Rt, hgord, pCoreOf_isPGroup 2 Rt,
    exists_two_subgroup_preimage Z hZc R hR2 hR1, ?_⟩
  exact Subgroup.mem_normalizer_iff.mp hgcore

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
