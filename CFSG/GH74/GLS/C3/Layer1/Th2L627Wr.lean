module

public import CFSG.GH74.GLS.C3.Layer1.Th2L627Syl

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk

variable {G : Type} [Group G] [Finite G]

theorem wr_core
    (hrank : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 16)
    {T S Q : Subgroup G} {a t : G}
    (hT : IsPGroup 2 ↥T) (hS : IsPGroup 2 ↥S) (hTS : T ≤ S) (haS : a ∈ S)
    (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T) (ha2 : a * a ∈ T)
    (hT64 : Nat.card ↥T ≤ 64)
    (hQT : Q ≤ T) (hQn : ∀ τ ∈ T, ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hQ8 : IsD8 Q)
    (hdisj : Q ⊓ conjugate Q a = ⊥)
    (htQ : t ∈ Q) (ht1 : t ≠ 1) (htc : ∀ q ∈ Q, q * t = t * q)
    (hCS : ∀ s ∈ S, s * t = t * s → s ∈ T) :
    (∀ s ∈ S, s ∈ T ∨ a⁻¹ * s ∈ T) ∧ Nat.card ↥S = 2 * Nat.card ↥T ∧
      ∀ y ∈ S, (∀ s ∈ S, s * y = y * s) → y ≠ 1 → y = t * (a⁻¹ * t * a) := by
  obtain ⟨z, -, -, hzz, -, hzu⟩ := hQ8.exists_z
  have htz : t = z := (hzu t htQ htc).resolve_left ht1
  have htt : t * t = 1 := by rw [htz]; exact hzz
  obtain ⟨x, hx⟩ : ∃ x : G, x = a⁻¹ * t * a := ⟨_, rfl⟩
  have hax : a * x * a⁻¹ = t := by rw [hx]; group
  have ha_norm : ∀ τ ∈ T, a * τ * a⁻¹ ∈ T := fun τ hτ =>
    (Subgroup.mem_normalizer_iff.1 haN τ).1 hτ
  have ha_inv_norm : ∀ τ ∈ T, a⁻¹ * τ * a ∈ T := by
    intro τ hτ
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem haN) τ).1 hτ
    simpa using this
  have hQaT : conjugate Q a ≤ T := by
    intro y hy
    have h1 : a * y * a⁻¹ ∈ T := hQT (Back.mem_conjugate_iff'.1 hy)
    have := ha_inv_norm _ h1
    have e : a⁻¹ * (a * y * a⁻¹) * a = y := by group
    rwa [e] at this
  have hQan : ∀ τ ∈ T, ∀ y ∈ conjugate Q a, τ * y * τ⁻¹ ∈ conjugate Q a := by
    intro τ hτ y hy
    rw [Back.mem_conjugate_iff'] at hy ⊢
    have h1 := hQn (a * τ * a⁻¹) (ha_norm τ hτ) _ hy
    have e : a * τ * a⁻¹ * (a * y * a⁻¹) * (a * τ * a⁻¹)⁻¹ = a * (τ * y * τ⁻¹) * a⁻¹ := by group
    rwa [e] at h1
  have hcomm : ∀ q ∈ Q, ∀ y ∈ conjugate Q a, q * y = y * q := fun q hq y hy =>
    comm_of_normal_disjoint hQT hQaT hQn hQan hdisj hq hy
  have hQ8a : IsD8 (conjugate Q a) := hQ8.conjugate a
  have hcard64 : Nat.card ↥(Q ⊔ conjugate Q a) = 64 := by
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, Back.card_conjugate', hQ8.card_eq]
  have hTeq : T = Q ⊔ conjugate Q a :=
    (Subgroup.eq_of_le_of_card_ge (sup_le hQT hQaT) (by rw [hcard64]; exact hT64)).symm
  have hxQa : x ∈ conjugate Q a := by
    rw [Back.mem_conjugate_iff', hax]
    exact htQ
  have hx1 : x ≠ 1 := by
    intro h1
    apply ht1
    rw [← hax, h1]
    group
  have hx2 : x * x = 1 := by
    have : x * x = a⁻¹ * (t * t) * a := by rw [hx]; group
    rw [this, htt]
    group
  have hxcQa : ∀ g ∈ conjugate Q a, g * x = x * g := by
    intro g hg
    have hga : a * g * a⁻¹ ∈ Q := Back.mem_conjugate_iff'.1 hg
    have h1 := htc _ hga
    calc g * x = a⁻¹ * ((a * g * a⁻¹) * t) * a := by rw [hx]; group
      _ = a⁻¹ * (t * (a * g * a⁻¹)) * a := by rw [h1]
      _ = x * g := by rw [hx]; group
  have hxT : ∀ τ ∈ T, x * τ = τ * x := by
    intro τ hτ
    rw [hTeq] at hτ
    obtain ⟨q, hq, g, hg, rfl⟩ := mem_sup_of_commute hcomm hτ
    calc x * (q * g) = (x * q) * g := by group
      _ = (q * x) * g := by rw [hcomm q hq x hxQa]
      _ = q * (x * g) := by group
      _ = q * (g * x) := by rw [hxcQa g hg]
      _ = (q * g) * x := by group
  have hcentx : ∀ s ∈ S, s * x = x * s → s ∈ T := by
    intro s hs hsx
    have has : a * s * a⁻¹ ∈ S := S.mul_mem (S.mul_mem haS hs) (S.inv_mem haS)
    have hc : (a * s * a⁻¹) * t = t * (a * s * a⁻¹) := by
      calc (a * s * a⁻¹) * t = a * (s * x) * a⁻¹ := by rw [hx]; group
        _ = a * (x * s) * a⁻¹ := by rw [hsx]
        _ = (a * x * a⁻¹) * (a * s * a⁻¹) := by group
        _ = t * (a * s * a⁻¹) := by rw [hax]
    have hasT : a * s * a⁻¹ ∈ T := hCS _ has hc
    have := ha_inv_norm _ hasT
    have e : a⁻¹ * (a * s * a⁻¹) * a = s := by group
    rwa [e] at this
  obtain ⟨R, hRQa, hRel, hRcard, -⟩ := hQ8a.exists_four_containing hxQa hx2
  have hRT : R ≤ T := hRQa.trans hQaT
  have hRn' : ∀ g ∈ conjugate Q a, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    have hrel : R.relIndex (conjugate Q a) = 2 := by
      have h1 := Subgroup.relIndex_mul_card (H := R) (K := conjugate Q a)
      rw [inf_of_le_left hRQa, hRcard, Back.card_conjugate', hQ8.card_eq] at h1
      omega
    have : (R.subgroupOf (conjugate Q a)).Normal := Subgroup.normal_of_index_eq_two hrel
    intro g hg r hr
    have := (inferInstance : (R.subgroupOf (conjugate Q a)).Normal).conj_mem ⟨r, hRQa hr⟩
      (Subgroup.mem_subgroupOf.2 hr) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hRn : ∀ τ ∈ T, ∀ r ∈ R, τ * r * τ⁻¹ ∈ R := by
    intro τ hτ r hr
    rw [hTeq] at hτ
    obtain ⟨q, hq, g, hg, rfl⟩ := mem_sup_of_commute hcomm hτ
    have h1 : g * r * g⁻¹ ∈ R := hRn' g hg r hr
    have h2 : q * (g * r * g⁻¹) * q⁻¹ = g * r * g⁻¹ := by
      have := hcomm q hq (g * r * g⁻¹) (hRQa h1)
      calc q * (g * r * g⁻¹) * q⁻¹ = ((g * r * g⁻¹) * q) * q⁻¹ := by rw [this]
        _ = g * r * g⁻¹ := by group
    have e : q * g * r * (q * g)⁻¹ = q * (g * r * g⁻¹) * q⁻¹ := by group
    rw [e, h2]
    exact h1
  have hsec : Sec4Core a Q R T S :=
    { T_pgroup := hT
      S_pgroup := hS
      T_le_S := hTS
      a_mem := haS
      a_mem_norm := haN
      a_not_mem := haT
      a_sq_mem := ha2
      P_le := hQT
      Q_le := hRT
      P_norm := hQn
      Q_norm := hRn
      P_d8 := hQ8
      Q_shape := Or.inl hRel
      Q_card := hRcard
      PQ_comm := fun p hp q hq => hcomm p hp q (hRQa hq)
      PQ_disj := by
        rw [eq_bot_iff]
        intro y hy
        have : y ∈ Q ⊓ conjugate Q a := ⟨hy.1, hRQa hy.2⟩
        rwa [hdisj] at this
      cent6 := by
        intro u huR hu1 huT s hsS hsu
        have huQa : u ∈ conjugate Q a := hRQa huR
        have huc : ∀ p ∈ conjugate Q a, p * u = u * p := fun p hp => (huT p (hQaT hp)).symm
        have hux : u = x := by
          rcases hQ8a.central_eq hxQa hx1 hxcQa u huQa huc with h1 | h1
          · exact absurd h1 hu1
          · exact h1
        rw [hux] at hsu
        exact hcentx s hsS hsu
      rank4 := hrank }
  have hS_cases : ∀ s ∈ S, s ∈ T ∨ a⁻¹ * s ∈ T :=
    hsec.S_cases hTeq (fun n hnS hnN =>
      hsec.mem_T_or_of_normalizer hTeq htQ ht1 htc hxQa hx1 hx2 hxT hax hcentx hnS hnN)
  have hTS' : T ≠ S := by
    intro h
    apply haT
    rw [h]
    exact haS
  refine ⟨hS_cases, le_antisymm (card_le_of_subset_union hS_cases)
    (two_mul_card_le hS hTS hTS'), ?_⟩
  have htx : t ≠ x := by
    intro h
    have : t ∈ Q ⊓ conjugate Q a := ⟨htQ, h ▸ hxQa⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact ht1 this
  intro y hyS hyc hy1
  have htS : t ∈ S := hTS (hQT htQ)
  have hyT : y ∈ T := hCS y hyS (hyc t htS).symm
  have hycT : ∀ τ ∈ T, τ * y = y * τ := fun τ hτ => hyc τ (hTS hτ)
  rcases hsec.central_T_cases hTeq htQ ht1 htc hxQa hx1 hxcQa hyT hy1 hycT with h1 | h1 | h1
  ·
    exfalso
    apply htx
    have h2 : a * y = y * a := hyc a haS
    rw [h1] at h2
    calc t = a⁻¹ * (a * t) := by group
      _ = a⁻¹ * (t * a) := by rw [h2]
      _ = x := by rw [hx]; group
  ·
    exfalso
    apply htx
    have h2 : a * y = y * a := hyc a haS
    rw [h1] at h2
    calc t = a * x * a⁻¹ := hax.symm
      _ = x * a * a⁻¹ := by rw [h2]
      _ = x := by group
  · rw [h1, hx]

end CFSG.GH74.GLS.Th2.L627
