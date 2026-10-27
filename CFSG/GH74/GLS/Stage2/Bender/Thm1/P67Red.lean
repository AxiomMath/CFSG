module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67N2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Fam

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] noncomputable def actCenterQuot {N : Type*} [Group N] (J : Subgroup N) :
    ↥(normalizer (J : Set N)) →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
  (centerQuotientHom ↥J).comp J.normalizerMonoidHom

theorem commute_of_actCenterQuot_eq_one {N : Type*} [Group N] (J : Subgroup N)
    [Group.IsPerfect ↥J] (h : ↥(normalizer (J : Set N))) (hh : actCenterQuot J h = 1) :
    ∀ c ∈ J, (h : N) * c = c * h := by
  have h1 : J.normalizerMonoidHom h = 1 := by
    apply centerQuotientHom_injective ↥J
    rw [map_one]
    exact hh
  intro c hc
  have h2 := congrArg (fun φ : MulAut ↥J => ((φ ⟨c, hc⟩ : ↥J) : N)) h1
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem cf67_N2 (N : Type) [Group N] [Finite N] (J : Subgroup N) (hJ : IsComponent J)
    (r : ℕ) (hr : r.Prime) (hr2 : Odd r) (V Z : Subgroup N)
    (hVe : IsElementaryAbelian r ↥V) (hVc : Nat.card ↥V = r ^ 2)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZodd : Odd (Nat.card ↥Z))
    (hZcop : Nat.Coprime (Nat.card ↥Z) r) (hcomm : ∀ v ∈ V, ∀ w ∈ Z, v * w = w * v)
    (hVn : V ≤ normalizer (J : Set N)) (hZn : Z ≤ normalizer (J : Set N))
    (hfaith : ∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N))
    (hZnt : ¬ J ≤ centralizer (Z : Set N)) :
    ∃ (V' Z' : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J))),
      N2Cfg (↥J ⧸ Subgroup.center ↥J) r V' Z' := by
  have : Group.IsPerfect ↥J := hJ.1.1
  have : Fact r.Prime := ⟨hr⟩
  have := hVe
  set H : Subgroup N := normalizer (J : Set N) with hH
  set ψ : ↥H →* MulAut (↥J ⧸ Subgroup.center ↥J) := actCenterQuot J with hψ
  have hker : ∀ h : ↥H, ψ h = 1 → ∀ c ∈ J, (h : N) * c = c * h :=
    commute_of_actCenterQuot_eq_one J
  have hVinj : Function.Injective (ψ.domRestrict (V.subgroupOf H)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨v, hv⟩ hv1
    have hcen := hker v hv1
    have hv' : (v : N) ∈ V := mem_subgroupOf.mp hv
    by_contra hne
    have hne' : (v : N) ≠ 1 := fun h => hne (Subtype.ext (Subtype.ext h))
    refine hfaith _ hv' hne' ?_
    intro c hc
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hcen c hc
  have hVcard : Nat.card ↥(V.subgroupOf H) = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVn).toEquiv
  have hZcard : Nat.card ↥(Z.subgroupOf H) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZn).toEquiv
  have hZdvd : Nat.card ↥((Z.subgroupOf H).map ψ) ∣ Nat.card ↥Z :=
    (Subgroup.card_map_dvd _ ψ).trans (dvd_of_eq hZcard)
  refine ⟨(V.subgroupOf H).map ψ, (Z.subgroupOf H).map ψ, hr, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : IsElementaryAbelian r ↥(V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVn
    exact IsElementaryAbelian.map ψ
  · rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hVinj).toEquiv,
      hVcard, hVc]
  · rintro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hZab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy))
  · exact Odd.of_dvd_nat hZodd hZdvd
  · exact Nat.Coprime.coprime_dvd_left hZdvd hZcop
  · intro hbot
    apply hZnt
    intro c hc
    rw [mem_centralizer_iff]
    intro z hz
    have hz' : (⟨z, hZn hz⟩ : ↥H) ∈ Z.subgroupOf H := mem_subgroupOf.mpr hz
    have h1 : ψ ⟨z, hZn hz⟩ ∈ (Z.subgroupOf H).map ψ := mem_map_of_mem ψ hz'
    rw [hbot, mem_bot] at h1
    exact hker _ h1 c hc
  · rintro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy))

theorem cf67Fam_of_noN2 {F : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], F Y → NoN2 Y) : CF67Fam F := by
  intro N _ _ J hJ hF r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt _
  obtain ⟨V', Z', hcfg⟩ :=
    cf67_N2 N J hJ r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt
  exact h (↥J ⧸ Subgroup.center ↥J) hF r V' Z' hcfg

end CFSG.GH74.GLS.Stage2.Bender.Thm1
