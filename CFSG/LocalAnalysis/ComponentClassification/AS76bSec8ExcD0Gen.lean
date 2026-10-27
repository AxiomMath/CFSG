module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcSub
public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

theorem exists_conj_le_of_odd [Finite X] {V R S : Subgroup X} (hRV : R ≤ normalizer (V : Set X))
    (hVR : V ⊓ R = ⊥) (hV2 : IsPGroup 2 V) (hS : S ≤ V ⊔ R) (hSodd : Odd (Nat.card S)) :
    ∃ v ∈ V, ∀ s ∈ S, v⁻¹ * s * v ∈ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := V ⊔ S with hF
  have hVF : V ≤ F := le_sup_left
  have hSF : S ≤ F := le_sup_right
  have hVRN : V ⊔ R ≤ normalizer (V : Set X) := sup_le le_normalizer hRV
  have hFN : F ≤ normalizer (V : Set X) := sup_le le_normalizer (hS.trans hVRN)
  set N := V.subgroupOf F with hN
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hVF).2 hFN
  have hVS : ∀ g ∈ V, g ∈ S → g = 1 := by
    intro g hgV hgS
    obtain ⟨k, hk⟩ := hV2 ⟨g, hgV⟩
    have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    have h2 : orderOf g ∣ Nat.card S := by
      have := orderOf_dvd_natCard (⟨g, hgS⟩ : S)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hj
    · exfalso
      rw [hj, pow_succ] at h2
      exact (Nat.not_even_iff_odd.2 hSodd) (even_iff_two_dvd.2 (dvd_of_mul_left_dvd h2))
  have hNH : (N : Set F) * ((S.subgroupOf F : Subgroup F) : Set F) = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    have hf : (f : X) ∈ ((V ⊔ S : Subgroup X) : Set X) := f.2
    rw [sup_comm, coe_mul_of_left_le_normalizer_right S V (hS.trans hVRN)] at hf
    obtain ⟨s, hs, v, hv, hsv⟩ := hf
    have hsv' : s * v = f := hsv
    refine ⟨⟨s * v * s⁻¹, hVF (by
      have := (mem_normalizer_iff.1 ((hS.trans hVRN) hs) v).1 hv
      exact this)⟩, mem_subgroupOf.2 (by
        have := (mem_normalizer_iff.1 ((hS.trans hVRN) hs) v).1 hv
        exact this), ⟨s, hSF hs⟩, mem_subgroupOf.2 hs, Subtype.ext ?_⟩
    show s * v * s⁻¹ * s = f
    rw [inv_mul_cancel_right, hsv']
  have hNK : (N : Set F) * ((R.subgroupOf F : Subgroup F) : Set F) = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    have hf : (f : X) ∈ ((V ⊔ R : Subgroup X) : Set X) :=
      (sup_le le_sup_left hS : V ⊔ S ≤ V ⊔ R) f.2
    rw [sup_comm, coe_mul_of_left_le_normalizer_right R V hRV] at hf
    obtain ⟨r, hr, v, hv, hrv⟩ := hf
    have hrv' : r * v = f := hrv
    have hv' : r * v * r⁻¹ ∈ V := (mem_normalizer_iff.1 (hRV hr) v).1 hv
    have hrF : r ∈ F := by
      have h1 : r = (r * v * r⁻¹)⁻¹ * f := by rw [← hrv']; group
      rw [h1]
      exact mul_mem (inv_mem (hVF hv')) f.2
    refine ⟨⟨r * v * r⁻¹, hVF hv'⟩, mem_subgroupOf.2 hv', ⟨r, hrF⟩, mem_subgroupOf.2 hr,
      Subtype.ext ?_⟩
    show r * v * r⁻¹ * r = f
    rw [inv_mul_cancel_right, hrv']
  have hNH' : N ⊓ S.subgroupOf F = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨hgV, hgS⟩ := mem_inf.1 hg
    rw [mem_bot]
    exact Subtype.ext (hVS _ (mem_subgroupOf.1 hgV) (mem_subgroupOf.1 hgS))
  have hNK' : N ⊓ R.subgroupOf F = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨hgV, hgR⟩ := mem_inf.1 hg
    have h1 : (g : X) ∈ V ⊓ R := mem_inf.2 ⟨mem_subgroupOf.1 hgV, mem_subgroupOf.1 hgR⟩
    rw [hVR, mem_bot] at h1
    rw [mem_bot]
    exact Subtype.ext h1
  have hN2 : IsPGroup 2 N := hV2.of_equiv (subgroupOfEquivOfLe hVF).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcard : Nat.card N * Nat.card (S.subgroupOf F) = Nat.card F :=
    (isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hNH') hNH).card_mul_card
  have hindex : N.index = Nat.card S := by
    have h1 := N.card_mul_index
    have h2 : Nat.card (S.subgroupOf F) = Nat.card S :=
      Nat.card_congr (subgroupOfEquivOfLe hSF).toEquiv
    have h0 : 0 < Nat.card N := Nat.card_pos
    rw [← h2]
    exact Nat.eq_of_mul_eq_mul_left h0 (h1.trans hcard.symm)
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk, hindex]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hSodd)
  obtain ⟨n, hn, hKH⟩ :=
    CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N hNsolv hcop hNH hNK hNH' hNK'
  refine ⟨n, mem_subgroupOf.1 hn, fun s hs => ?_⟩
  have h1 : (MulAut.conj n⁻¹).toMonoidHom ⟨s, hSF hs⟩ ∈ R.subgroupOf F := by
    rw [hKH]
    exact mem_map_of_mem _ (mem_subgroupOf.2 hs)
  have h2 := mem_subgroupOf.1 h1
  simpa [MulAut.conj_apply] using h2

theorem d0Data_of_semidirect [Finite X] {Γ : Subgroup X} {x : X} (hx : x ∈ Γ)
    {V R D Zx : Subgroup X} (hC : Γ ⊓ centralizer {x} = V ⊔ R)
    (hRV : R ≤ normalizer (V : Set X)) (hVR : V ⊓ R = ⊥) (hV2 : IsPGroup 2 V)
    (hDR : ∀ d ∈ D, ∀ r ∈ R, d * r = r * d) (hDΓ : D ≤ Γ) (hVΓ : V ≤ Γ) [IsSimpleGroup D]
    (hDnc : ∃ a b : D, a * b ≠ b * a) (hZD : Zx ≤ D) (hZc : ∀ a ∈ Zx, ∀ b ∈ Zx, a * b = b * a)
    (hVZ : ∀ v ∈ V, ∀ z ∈ Zx, v * z = z * v) :
    D0Data (⟨x, hx⟩ : Γ) (Zx.subgroupOf Γ) := by
  intro S hS hSodd
  set S₀ := S.map Γ.subtype with hS₀
  have hS₀le : S₀ ≤ V ⊔ R := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hC]
    exact mem_inf.2 ⟨s.2, mem_centralizer_singleton_iff.2 (mem_cent_iff.1 (hS hs))⟩
  have hS₀odd : Odd (Nat.card S₀) := by
    rwa [hS₀, Nat.card_congr (S.equivMapOfInjective _ Γ.subtype_injective).toEquiv.symm]
  obtain ⟨v, hv, hvS⟩ := exists_conj_le_of_odd hRV hVR hV2 hS₀le hS₀odd
  have hvΓ : v ∈ Γ := hVΓ hv
  set D' := D.map (MulAut.conj v).toMonoidHom with hD'
  have hmemD' : ∀ y, y ∈ D' ↔ v⁻¹ * y * v ∈ D := by
    intro y
    constructor
    · rintro ⟨d, hd, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hd
    · intro hy
      exact ⟨_, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hD'Γ : D' ≤ Γ := by
    rintro _ ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply] using mul_mem (mul_mem hvΓ (hDΓ hd)) (inv_mem hvΓ)
  have hDperf : ⁅D, D⁆ = D := commutator_eq_self_of_simple hDnc
  have hD'perf : ⁅D', D'⁆ = D' := by rw [hD', ← map_commutator, hDperf]
  refine ⟨D'.subgroupOf Γ, commutator_subgroupOf_of_perfect hD'Γ hD'perf, ?_, ?_, ?_⟩
  ·
    intro d hd
    rw [mem_centralizer_iff]
    intro s hs
    have hd' := (hmemD' _).1 (mem_subgroupOf.1 hd)
    have hs' : v⁻¹ * (s : X) * v ∈ R := hvS _ ⟨s, hs, rfl⟩
    have h1 := hDR _ hd' _ hs'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have e : (d : X) = v * (v⁻¹ * d * v) * v⁻¹ := by group
    have e' : (s : X) = v * (v⁻¹ * s * v) * v⁻¹ := by group
    rw [e, e']
    calc v * (v⁻¹ * ↑s * v) * v⁻¹ * (v * (v⁻¹ * ↑d * v) * v⁻¹) =
        v * ((v⁻¹ * ↑s * v) * (v⁻¹ * ↑d * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * ↑d * v) * (v⁻¹ * ↑s * v)) * v⁻¹ := by rw [h1]
      _ = _ := by group
  ·
    intro z hz
    refine mem_subgroupOf.2 ((hmemD' _).2 ?_)
    have h1 := hVZ v hv _ (mem_subgroupOf.1 hz)
    have e : v⁻¹ * (z : X) * v = z := by
      calc v⁻¹ * (z : X) * v = v⁻¹ * (v * z) := by rw [h1, mul_assoc]
        _ = z := by group
    rw [e]
    exact hZD (mem_subgroupOf.1 hz)
  ·
    intro W hWZ hW hN
    set W₀ := W.map Γ.subtype with hW₀
    have hW₀Z : W₀ ≤ Zx := by
      rintro _ ⟨w, hw, rfl⟩
      exact mem_subgroupOf.1 (hWZ hw)
    have hDN : ∀ d ∈ D, ∀ w ∈ W₀, d * w * d⁻¹ ∈ W₀ := by
      intro d hd w hw
      have hvd : v * d * v⁻¹ ∈ D' := (hmemD' _).2 (by simpa [mul_assoc] using hd)
      obtain ⟨w', hw', rfl⟩ := hw
      have hwv : v * (w' : X) * v⁻¹ = w' := by
        have h1 := hVZ v hv _ (mem_subgroupOf.1 (hWZ hw'))
        rw [h1, mul_inv_cancel_right]
      have hvd' : (⟨v * d * v⁻¹, hD'Γ hvd⟩ : Γ) ∈ D'.subgroupOf Γ := hvd
      have h2 := (mem_normalizer_iff.1 (hN hvd') w').1 hw'
      have h3 : ((⟨v * d * v⁻¹, hD'Γ hvd⟩ * w' * (⟨v * d * v⁻¹, hD'Γ hvd⟩ : Γ)⁻¹ : Γ) : X) ∈ W₀ :=
        ⟨_, h2, rfl⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      have e : d * (w' : X) * d⁻¹ =
          v⁻¹ * (v * d * v⁻¹ * w' * (v * d * v⁻¹)⁻¹) * v := by
        calc d * (w' : X) * d⁻¹ = v⁻¹ * (v * d * v⁻¹ * (v * w' * v⁻¹) * (v * d * v⁻¹)⁻¹) * v := by
              group
          _ = _ := by rw [hwv]
      have hW₀v : ∀ y ∈ W₀, v⁻¹ * y * v ∈ W₀ := by
        rintro _ ⟨y, hy, rfl⟩
        show v⁻¹ * (y : X) * v ∈ W₀
        have h4 := hVZ v hv _ (mem_subgroupOf.1 (hWZ hy))
        have e4 : v⁻¹ * (y : X) * v = y := by
          calc v⁻¹ * (y : X) * v = v⁻¹ * (v * y) := by rw [h4, mul_assoc]
            _ = y := by group
        rw [e4]
        exact ⟨y, hy, rfl⟩
      show d * (w' : X) * d⁻¹ ∈ W₀
      rw [e]
      exact hW₀v _ h3
    have hnorm : (W₀.subgroupOf D).Normal := by
      refine ⟨fun w hw d => mem_subgroupOf.2 ?_⟩
      simpa using hDN d d.2 w (mem_subgroupOf.1 hw)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W₀.subgroupOf D) with h | h
    · apply hW
      refine eq_bot_iff.2 fun w hw => ?_
      have h1 : (⟨(w : X), hZD (hW₀Z ⟨w, hw, rfl⟩)⟩ : D) ∈ W₀.subgroupOf D :=
        mem_subgroupOf.2 ⟨w, hw, rfl⟩
      rw [h, mem_bot] at h1
      rw [mem_bot]
      have h2 := congrArg (Subtype.val : D → X) h1
      exact Subtype.ext h2
    · obtain ⟨a, b, hab⟩ := hDnc
      apply hab
      have ha : (a : X) ∈ W₀ := mem_subgroupOf.1 (h ▸ mem_top a)
      have hb : (b : X) ∈ W₀ := mem_subgroupOf.1 (h ▸ mem_top b)
      exact Subtype.ext (hZc _ (hW₀Z ha) _ (hW₀Z hb))

end CFSG.ComponentClassification.RankTwoExceptional.Exc
