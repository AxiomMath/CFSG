module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Lift


public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint Subgroup

private def u_a8σ : Equiv.Perm (Fin 8) :=
  Equiv.swap (0 : Fin 8) 1 * Equiv.swap (1 : Fin 8) 2

private def u_a8τ : Equiv.Perm (Fin 8) :=
  Equiv.swap (0 : Fin 8) 1 * Equiv.swap (1 : Fin 8) 3

private lemma u_a8σ_mem : u_a8σ ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private lemma u_a8τ_mem : u_a8τ ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private lemma u_a8_noncomm : u_a8σ * u_a8τ ≠ u_a8τ * u_a8σ := by
  decide

theorem card_inf_centralizer_ge_of_lieModel_l44 {G : Type} [Group G] [Finite G] {x : G}
    {N A : Subgroup G} (hNx : N ≤ centralizer ({x} : Set G))
    (hNn : (N.subgroupOf (centralizer ({x} : Set G))).Normal) (hN : ⁅N, N⁆ = N)
    (hS : LieModel (↥N ⧸ center ↥N) .PSL 4 2 2) (hAN : A ≤ N)
    (eA : ↥A ≃* alternatingGroup (Fin 8)) {t d : G}
    (ht : t ∈ centralizer ({x} : Set G)) (hd : d ∈ centralizer ({x} : Set G))
    (ht1 : ¬ ∀ n ∈ N, t * n = n * t) (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a = a * t)
    (hd2 : d * d = 1) (hdt : d * t = t * d) (hdA : ∀ a ∈ A, d * a * d⁻¹ ∈ A)
    (hdout : ¬ ∃ a ∈ A, ∀ y ∈ A, d * y * d⁻¹ = a * y * a⁻¹) :
    15360 ≤ Nat.card ↥(centralizer ({d} : Set G) ⊓ centralizer ({x} : Set G)) := by
  classical
  let Cx : Subgroup G := centralizer ({x} : Set G)
  let N' : Subgroup ↥Cx := N.subgroupOf Cx
  let D₀' : Subgroup ↥Cx := centralizer (N' : Set ↥Cx)
  haveI hN'norm : N'.Normal := hNn
  haveI hD₀'norm : D₀'.Normal := Subgroup.normal_centralizer
  have hN'map : N'.map Cx.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNx
  have hN' : ⁅N', N'⁆ = N' := by
    apply Subgroup.map_injective (f := Cx.subtype) Cx.subtype_injective
    rw [Subgroup.map_commutator (H₁ := N') (H₂ := N') (f := Cx.subtype), hN'map, hN]
  have hD : ∀ h : ↥Cx, h ∈ D₀' ↔ ∀ n ∈ N', h * n = n * h := by
    intro h
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hh n hn
      exact (hh n hn).symm
    · intro hh n hn
      exact (hh n hn).symm
  have hS' : LieModel (↥N' ⧸ Subgroup.center ↥N') .PSL 4 2 2 := by
    let e : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNx
    have he : (Subgroup.center ↥N').map e = Subgroup.center ↥N := Subgroup.map_center_eq e
    refine LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥N') (Subgroup.center ↥N) e he).symm hS
  have hA_le_H : A ≤ Cx := le_trans hAN hNx
  have hIsoA : ↥(A.subgroupOf Cx) ≃* alternatingGroup (Fin 8) :=
    (Subgroup.subgroupOfEquivOfLe hA_le_H).trans eA
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥(A.subgroupOf Cx) := hIsoA.isSimpleGroup
  have hnc : ∃ a b : ↥(A.subgroupOf Cx), a * b ≠ b * a := by
    refine ⟨hIsoA.symm ⟨u_a8σ, u_a8σ_mem⟩, hIsoA.symm ⟨u_a8τ, u_a8τ_mem⟩, ?_⟩
    intro h
    have hσ : (⟨u_a8σ, u_a8σ_mem⟩ : alternatingGroup (Fin 8)) * ⟨u_a8τ, u_a8τ_mem⟩ =
        ⟨u_a8τ, u_a8τ_mem⟩ * ⟨u_a8σ, u_a8σ_mem⟩ := by
      simpa using congrArg hIsoA h
    exact u_a8_noncomm (Subtype.ext_iff.mp hσ)
  have hcenterA : Subgroup.center ↥(A.subgroupOf Cx) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(A.subgroupOf Cx)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      have hb : b ∈ Subgroup.center ↥(A.subgroupOf Cx) := by rw [h]; trivial
      exact (hab (Subgroup.mem_center_iff.mp hb a)).elim
  let φ : ↥(A.subgroupOf Cx) →* ↥Cx ⧸ D₀' :=
    (QuotientGroup.mk' D₀').comp (A.subgroupOf Cx).subtype
  have hrange : φ.range = (A.subgroupOf Cx).map (QuotientGroup.mk' D₀') := by
    dsimp only [φ]
    rw [MonoidHom.range_comp (g := QuotientGroup.mk' D₀')
      (f := (A.subgroupOf Cx).subtype), Subgroup.range_subtype]
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hker : a⁻¹ * b ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hmem : ((a⁻¹ * b : ↥(A.subgroupOf Cx)) : ↥Cx) ∈ D₀' :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hker)
    have hcen : a⁻¹ * b ∈ Subgroup.center ↥(A.subgroupOf Cx) := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hcN : (c : ↥Cx) ∈ N' :=
        Subgroup.mem_subgroupOf.mpr (hAN (Subgroup.mem_subgroupOf.mp c.2))
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hmem) (c : ↥Cx) hcN)
    have h1 : a⁻¹ * b = 1 := by
      have := hcen
      rw [hcenterA] at this
      simpa using this
    exact inv_mul_eq_one.mp h1
  let A' : Subgroup (↥Cx ⧸ D₀') := (A.subgroupOf Cx).map (QuotientGroup.mk' D₀')
  have heA' : A' ≃* alternatingGroup (Fin 8) :=
    (MulEquiv.subgroupCongr hrange).symm.trans
      ((MonoidHom.ofInjective hφinj).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hA_le_H).trans eA))
  have hAS' : A' ≤ N'.map (QuotientGroup.mk' D₀') := by
    dsimp only [A']
    exact Subgroup.map_mono (f := QuotientGroup.mk' D₀') (Subgroup.subgroupOf_mono Cx hAN)
  let tH : ↥Cx := ⟨t, ht⟩
  let t' : ↥Cx ⧸ D₀' := QuotientGroup.mk tH
  have ht1' : t' ≠ 1 := by
    intro h1
    apply ht1
    intro n hn
    have hmem : tH ∈ D₀' := (QuotientGroup.eq_one_iff tH).mp h1
    have hc := (Subgroup.mem_centralizer_iff.mp hmem) (⟨n, hNx hn⟩ : ↥Cx)
      (Subgroup.mem_subgroupOf.mpr hn)
    exact (Subtype.ext_iff.mp hc).symm
  have ht2' : t' * t' = 1 := by
    have ht2H : tH * tH = 1 := Subtype.ext ht2
    change (QuotientGroup.mk' D₀') tH * (QuotientGroup.mk' D₀') tH = 1
    rw [← map_mul, ht2H, map_one]
  have htA' : ∀ a ∈ A', t' * a = a * t' := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    change (QuotientGroup.mk' D₀') tH * (QuotientGroup.mk' D₀') b =
      (QuotientGroup.mk' D₀') b * (QuotientGroup.mk' D₀') tH
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact htA (b : G) (Subgroup.mem_subgroupOf.mp hb)
  let dH : ↥Cx := ⟨d, hd⟩
  have hd2' : dH * dH = 1 := Subtype.ext hd2
  have hdt' : (dH : ↥Cx ⧸ D₀') * t' = t' * (dH : ↥Cx ⧸ D₀') := by
    change (QuotientGroup.mk' D₀') dH * (QuotientGroup.mk' D₀') tH =
      (QuotientGroup.mk' D₀') tH * (QuotientGroup.mk' D₀') dH
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hdt
  have hdA' : ∀ a ∈ A', (dH : ↥Cx ⧸ D₀') * a * (dH : ↥Cx ⧸ D₀')⁻¹ ∈ A' := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨dH * (b : ↥Cx) * dH⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hdA (b : G) (Subgroup.mem_subgroupOf.mp hb)
    · rw [map_mul, map_mul, map_inv]
      rfl
  have hdout' : ¬ ∃ a ∈ A', ∀ x ∈ A',
      (dH : ↥Cx ⧸ D₀') * x * (dH : ↥Cx ⧸ D₀')⁻¹ = a * x * a⁻¹ := by
    rintro ⟨a, ha, hconj⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    apply hdout
    refine ⟨(b : G), Subgroup.mem_subgroupOf.mp hb, fun y hy => ?_⟩
    have hy' : (QuotientGroup.mk' D₀') (⟨y, hA_le_H hy⟩ : ↥Cx) ∈ A' :=
      Subgroup.mem_map.mpr ⟨⟨y, hA_le_H hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hconjy := hconj (QuotientGroup.mk' D₀' (⟨y, hA_le_H hy⟩ : ↥Cx)) hy'
    have hz₁ : dH * (⟨y, hA_le_H hy⟩ : ↥Cx) * dH⁻¹ ∈ A.subgroupOf Cx := by
      rw [Subgroup.mem_subgroupOf]
      exact hdA y hy
    have hz₂ : (b : ↥Cx) * (⟨y, hA_le_H hy⟩ : ↥Cx) * (b : ↥Cx)⁻¹ ∈ A.subgroupOf Cx := by
      rw [Subgroup.mem_subgroupOf]
      exact A.mul_mem (A.mul_mem (Subgroup.mem_subgroupOf.mp hb) hy)
        (A.inv_mem (Subgroup.mem_subgroupOf.mp hb))
    have heq : (⟨dH * (⟨y, hA_le_H hy⟩ : ↥Cx) * dH⁻¹, hz₁⟩ : ↥(A.subgroupOf Cx)) =
        ⟨(b : ↥Cx) * (⟨y, hA_le_H hy⟩ : ↥Cx) * (b : ↥Cx)⁻¹, hz₂⟩ := by
      apply hφinj
      change (QuotientGroup.mk' D₀') (dH * (⟨y, hA_le_H hy⟩ : ↥Cx) * dH⁻¹) =
        (QuotientGroup.mk' D₀') ((b : ↥Cx) * (⟨y, hA_le_H hy⟩ : ↥Cx) * (b : ↥Cx)⁻¹)
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
      exact hconjy
    exact Subtype.ext_iff.mp (Subtype.ext_iff.mp heq)
  have hmapcentral : (Subgroup.centralizer ({dH} : Set ↥Cx)).map Cx.subtype =
      Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext g
    constructor
    · intro hg
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hz)
      · exact z.2
    · intro hg
      rw [Subgroup.mem_inf] at hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hg.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hg.1
  have hcard : Nat.card ↥(Subgroup.centralizer ({dH} : Set ↥Cx)) =
      Nat.card ↥(Subgroup.centralizer ({d} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G)) := by
    rw [← Subgroup.card_map_of_injective (K := Subgroup.centralizer ({dH} : Set ↥Cx))
      (f := Cx.subtype) Cx.subtype_injective, hmapcentral]
  obtain ⟨h1, -⟩ := card_centralizer_ge_and_seven_dvd_card_of_perfect
    N' D₀' hN' hD hS' A' hAS' heA' t' dH ht1' ht2' htA' hd2' hdt' hdA' hdout'
  rw [hcard] at h1
  exact h1

end CFSG.OddStandard.AltStdSec.SwapPartner
