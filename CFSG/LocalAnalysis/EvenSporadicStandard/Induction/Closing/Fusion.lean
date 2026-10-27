module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.ZStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H} {t u : H}

omit [Finite H] in
theorem mem_map_conj_iff (P : Subgroup H) (c x : H) :
    x ∈ P.map (MulAut.conj c⁻¹).toMonoidHom ↔ c * x * c⁻¹ ∈ P := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have : c * ((MulAut.conj c⁻¹).toMonoidHom p) * c⁻¹ = p := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hp
  · intro h
    refine ⟨c * x * c⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite H] in
theorem act_mul_self {g : H} (hg : g ∈ normalizer (L : Set H)) (hgg : g * g = 1) :
    normalizerAction L ⟨g, hg⟩ * normalizerAction L ⟨g, hg⟩ = 1 := by
  rw [← map_mul, ← map_one (normalizerAction L)]
  congr 1
  exact Subtype.ext hgg

namespace ClosingSetup

variable (S : ClosingSetup H N L t u)
include S

theorem isolated_in_centralizer_u {m : H} (hm : m ∈ centralizer ({u} : Set H))
    (hc : (m * t * m⁻¹) * t = t * (m * t * m⁻¹)) : m * t * m⁻¹ = t := by
  have hmN : m ∈ normalizer (L : Set H) := S.hyp38 hm
  have hx : m * t * m⁻¹ ∈ centralizer (L : Set H) := conj_mem_centralizer hmN S.t_mem
  have hxx : (m * t * m⁻¹) * (m * t * m⁻¹) = 1 := by
    calc (m * t * m⁻¹) * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
      _ = 1 := by rw [S.t_mul_self]; group
  rcases S.eq_one_or_eq_t hx hxx hc with h1 | h1
  · exfalso
    apply ne_one_of_orderOf_eq_two S.t_order
    have : m * t * m⁻¹ = 1 := h1
    simpa using this
  · exact h1

theorem exists_oddNormal :
    ∃ P : Subgroup H, P ≤ centralizer ({u} : Set H) ∧ Odd (Nat.card P) ∧
      (∀ m ∈ centralizer ({u} : Set H), ∀ x ∈ P, m * x * m⁻¹ ∈ P) ∧
      ∀ m ∈ centralizer ({u} : Set H), m * t * m⁻¹ * t⁻¹ ∈ P := by
  classical
  set M : Subgroup H := centralizer ({u} : Set H) with hM
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 S.u_comm_t.symm
  have ht1 : (⟨t, htM⟩ : M) ≠ 1 := by
    intro h
    apply ne_one_of_orderOf_eq_two S.t_order
    exact congrArg Subtype.val h
  have ht2 : (⟨t, htM⟩ : M) * ⟨t, htM⟩ = 1 := Subtype.ext S.t_mul_self
  have := Fintype.ofFinite M
  obtain ⟨N₀, hN₀, hodd, hconj⟩ := CFSG.ZStar.glauberman_zStar M ⟨t, htM⟩ ht1 ht2 (by
    intro g hg
    refine Subtype.ext (S.isolated_in_centralizer_u g.2 ?_)
    have := congrArg Subtype.val hg
    exact this)
  refine ⟨N₀.map M.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hodd
  · rintro m hm _ ⟨n, hn, rfl⟩
    exact ⟨⟨m, hm⟩ * n * ⟨m, hm⟩⁻¹, hN₀.conj_mem n hn ⟨m, hm⟩, rfl⟩
  · intro m hm
    exact ⟨⟨m, hm⟩ * ⟨t, htM⟩ * ⟨m, hm⟩⁻¹ * ⟨t, htM⟩⁻¹, hconj ⟨m, hm⟩, rfl⟩

theorem exists_oddNormal_conj (c : H) :
    ∃ P₁ : Subgroup H, Odd (Nat.card P₁) ∧
      (∀ x ∈ P₁, x * (c⁻¹ * u * c) = (c⁻¹ * u * c) * x) ∧
      (∀ m : H, m * (c⁻¹ * u * c) = (c⁻¹ * u * c) * m → ∀ x ∈ P₁, m * x * m⁻¹ ∈ P₁) ∧
      ∀ m : H, m * (c⁻¹ * u * c) = (c⁻¹ * u * c) * m →
        m * (c⁻¹ * t * c) * m⁻¹ * (c⁻¹ * t * c)⁻¹ ∈ P₁ := by
  obtain ⟨P, hPle, hPodd, hPnorm, hPt⟩ := S.exists_oddNormal
  have hmu : ∀ m : H, m * (c⁻¹ * u * c) = (c⁻¹ * u * c) * m →
      c * m * c⁻¹ ∈ centralizer ({u} : Set H) := by
    intro m hm
    refine mem_centralizer_singleton_iff.2 ?_
    calc c * m * c⁻¹ * u = c * (m * (c⁻¹ * u * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * u * c) * m) * c⁻¹ := by rw [hm]
      _ = u * (c * m * c⁻¹) := by group
  refine ⟨P.map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hPodd
  · intro x hx
    rw [mem_map_conj_iff] at hx
    have := mem_centralizer_singleton_iff.1 (hPle hx)
    calc x * (c⁻¹ * u * c) = c⁻¹ * ((c * x * c⁻¹) * u) * c := by group
      _ = c⁻¹ * (u * (c * x * c⁻¹)) * c := by rw [this]
      _ = (c⁻¹ * u * c) * x := by group
  · intro m hm x hx
    rw [mem_map_conj_iff] at hx ⊢
    have h1 := hPnorm _ (hmu m hm) _ hx
    have e : c * (m * x * m⁻¹) * c⁻¹ = (c * m * c⁻¹) * (c * x * c⁻¹) * (c * m * c⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  · intro m hm
    rw [mem_map_conj_iff]
    have h1 := hPt _ (hmu m hm)
    have e : c * (m * (c⁻¹ * t * c) * m⁻¹ * (c⁻¹ * t * c)⁻¹) * c⁻¹ =
        (c * m * c⁻¹) * t * (c * m * c⁻¹)⁻¹ * t⁻¹ := by group
    rw [e]
    exact h1


theorem fix_of_oddCore (hoc : AutOddCoreTrivial (↥L ⧸ center ↥L)) (c : H) {u₁ t₂ : H}
    (hu₁ : u₁ = c⁻¹ * u * c) (ht₂ : t₂ = c⁻¹ * t * c)
    (hu₁N : u₁ ∈ normalizer (L : Set H)) (ht₂N : t₂ ∈ normalizer (L : Set H))
    (hu₁₂ : u₁ * u₁ = 1) (q : ↥L ⧸ center ↥L)
    (hq : normalizerAction L ⟨u₁, hu₁N⟩ q = q) : normalizerAction L ⟨t₂, ht₂N⟩ q = q := by
  classical
  obtain ⟨y, rfl, hy⟩ := exists_fixed_lift S.centre_odd hu₁N hu₁₂ hq
  obtain ⟨P₁, hP₁odd, hP₁u, hP₁norm, hP₁t⟩ := S.exists_oddNormal_conj c
  rw [← hu₁] at hP₁u hP₁norm
  rw [← hu₁, ← ht₂] at hP₁t
  have hyu : (y : H) * u₁ = u₁ * y := by
    have : u₁ * (y : H) * u₁⁻¹ = y := hy
    calc (y : H) * u₁ = (u₁ * y * u₁⁻¹) * u₁ := by rw [this]
      _ = u₁ * y := by group
  have hyi : (y : H)⁻¹ * u₁ = u₁ * (y : H)⁻¹ := by
    calc (y : H)⁻¹ * u₁ = (y : H)⁻¹ * (u₁ * y) * (y : H)⁻¹ := by group
      _ = (y : H)⁻¹ * (y * u₁) * (y : H)⁻¹ := by rw [hyu]
      _ = u₁ * (y : H)⁻¹ := by group
  have he := hP₁t _ hyi
  rw [inv_inv] at he
  have hmem : t₂ * (y : H) * t₂⁻¹ ∈ L := (mem_normalizer_iff.1 ht₂N y).1 y.2
  obtain ⟨yt, hyt⟩ : ∃ yt : ↥L, (yt : H) = t₂ * (y : H) * t₂⁻¹ := ⟨⟨_, hmem⟩, rfl⟩
  rw [normalizerAction_apply ⟨t₂, ht₂N⟩ y yt hyt]
  refine (QuotientGroup.eq.2 ?_).symm
  have heP : ((y⁻¹ * yt : ↥L) : H) ∈ P₁ := by
    have e : ((y⁻¹ * yt : ↥L) : H) = (y : H)⁻¹ * t₂ * (y : H) * t₂⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hyt]
      group
    rw [e]
    exact he
  set Q : Subgroup H := P₁ ⊓ L with hQ
  set Qb : Subgroup (↥L ⧸ center ↥L) :=
    (Q.subgroupOf L).map (QuotientGroup.mk' (center ↥L)) with hQb
  set ν : MulAut (↥L ⧸ center ↥L) := normalizerAction L ⟨u₁, hu₁N⟩ with hν
  have hνν : ν * ν = 1 := act_mul_self hu₁N hu₁₂
  have hQmem : ∀ x : ↥L, (x : H) ∈ P₁ → (x : ↥L ⧸ center ↥L) ∈ Qb := fun x hx =>
    ⟨x, mem_subgroupOf.2 ⟨hx, x.2⟩, rfl⟩
  have hle : Qb ≤ fixSubgroup ν := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : (x : H) ∈ P₁ := (mem_subgroupOf.1 hx).1
    have hcomm := hP₁u _ hxP
    show ν ((QuotientGroup.mk' (center ↥L)) x) = (QuotientGroup.mk' (center ↥L)) x
    rw [hν, QuotientGroup.mk'_apply, act_mk hu₁N]
    congr 1
    refine Subtype.ext ?_
    show u₁ * (x : H) * u₁⁻¹ = x
    calc u₁ * (x : H) * u₁⁻¹ = ((x : H) * u₁) * u₁⁻¹ := by rw [hcomm]
      _ = x := by group
  have hnormFix : ∀ f ∈ fixSubgroup ν, ∀ n ∈ Qb, f * n * f⁻¹ ∈ Qb := by
    intro f hf n hn
    obtain ⟨y', rfl, hy'⟩ := exists_fixed_lift S.centre_odd hu₁N hu₁₂ (show ν f = f from hf)
    obtain ⟨x, hx, rfl⟩ := hn
    have hxP : (x : H) ∈ P₁ := (mem_subgroupOf.1 hx).1
    have hy'u : (y' : H) * u₁ = u₁ * y' := by
      have : u₁ * (y' : H) * u₁⁻¹ = y' := hy'
      calc (y' : H) * u₁ = (u₁ * y' * u₁⁻¹) * u₁ := by rw [this]
        _ = u₁ * y' := by group
    have := hQmem (y' * x * y'⁻¹) (by
      have h1 := hP₁norm _ hy'u _ hxP
      simpa using h1)
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
  have hoddQ : Odd (Nat.card Qb) := by
    have h1 : Nat.card Qb ∣ Nat.card (Q.subgroupOf L) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Q.subgroupOf L) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ≤ L)).toEquiv
    have h3 : Nat.card Q ∣ Nat.card P₁ := Subgroup.card_dvd_of_le inf_le_left
    exact hP₁odd.of_dvd_nat ((h2 ▸ h1).trans h3)
  have hQb : Qb = ⊥ := by
    by_cases hν1 : ν = 1
    · have hnormal : Qb.Normal := ⟨fun n hn g => hnormFix g (by rw [hν1]; rfl) n hn⟩
      have := S.quasisimple.2.1
      have hna := S.quasisimple.2.2
      exact odd_normal_eq_bot_of_fStar (fStarSimple_top (↥L ⧸ center ↥L) hna) hnormal hoddQ
    · refine hoc ν hν1 hνν Qb hle ?_ hoddQ
      exact ⟨fun n hn g => mem_subgroupOf.2 (hnormFix g.1 g.2 n.1 (mem_subgroupOf.1 hn))⟩
  have hmemQ := hQmem _ heP
  rw [hQb, mem_bot] at hmemQ
  exact (QuotientGroup.eq_one_iff _).1 hmemQ

theorem fusion_pair (hoc : AutOddCoreTrivial (↥L ⧸ center ↥L)) {t' : H}
    (ht' : t' ∈ fusedSet u t) {c : H} (hc : c * t * c⁻¹ = t') :
    ∃ (u₁ : H) (hu₁N : u₁ ∈ normalizer (L : Set H)) (t₂ : H) (ht₂N : t₂ ∈ normalizer (L : Set H)),
      u₁ = c⁻¹ * u * c ∧ t₂ = c⁻¹ * t * c ∧ u₁ * u₁ = 1 ∧ u₁ * t = t * u₁ ∧
      normalizerAction L ⟨u₁, hu₁N⟩ * normalizerAction L ⟨u₁, hu₁N⟩ = 1 ∧
      normalizerAction L ⟨t₂, ht₂N⟩ * normalizerAction L ⟨t₂, ht₂N⟩ = 1 ∧
      normalizerAction L ⟨u₁, hu₁N⟩ * normalizerAction L ⟨t₂, ht₂N⟩ =
        normalizerAction L ⟨t₂, ht₂N⟩ * normalizerAction L ⟨u₁, hu₁N⟩ ∧
      (∀ q : ↥L ⧸ center ↥L, normalizerAction L ⟨u₁, hu₁N⟩ q = q →
        normalizerAction L ⟨t₂, ht₂N⟩ q = q) ∧
      (normalizerAction L ⟨t₂, ht₂N⟩ = 1 → t' ≠ t → False) ∧
      (normalizerAction L ⟨t₂, ht₂N⟩ = normalizerAction L ⟨u₁, hu₁N⟩ → t' = u * t) := by
  obtain ⟨hcu, hct⟩ := ht'.2
  have htt := S.t_mul_self
  have huu := S.u_mul_self
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, u₁ = c⁻¹ * u * c := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, t₂ = c⁻¹ * t * c := ⟨_, rfl⟩
  have hu₁t : u₁ * t = t * u₁ := by
    have h1 : c * t * c⁻¹ * u = u * (c * t * c⁻¹) := by rw [hc]; exact hcu
    calc u₁ * t = c⁻¹ * (u * (c * t * c⁻¹)) * c := by rw [hu₁]; group
      _ = c⁻¹ * (c * t * c⁻¹ * u) * c := by rw [h1]
      _ = t * u₁ := by rw [hu₁]; group
  have ht₂t : t₂ * t = t * t₂ := by
    have h2 : c * t * c⁻¹ * t = t * (c * t * c⁻¹) := by rw [hc]; exact hct
    calc t₂ * t = c⁻¹ * (t * (c * t * c⁻¹)) * c := by rw [ht₂]; group
      _ = c⁻¹ * (c * t * c⁻¹ * t) * c := by rw [h2]
      _ = t * t₂ := by rw [ht₂]; group
  have ht₂u₁ : t₂ * u₁ = u₁ * t₂ := by
    calc t₂ * u₁ = c⁻¹ * (t * u) * c := by rw [ht₂, hu₁]; group
      _ = c⁻¹ * (u * t) * c := by rw [S.u_comm_t.symm]
      _ = u₁ * t₂ := by rw [ht₂, hu₁]; group
  have hu₁₂ : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = c⁻¹ * (u * u) * c := by rw [hu₁]; group
      _ = 1 := by rw [huu]; group
  have ht₂₂ : t₂ * t₂ = 1 := by
    calc t₂ * t₂ = c⁻¹ * (t * t) * c := by rw [ht₂]; group
      _ = 1 := by rw [htt]; group
  have hMN := S.centralizer_t_le
  have hu₁N : u₁ ∈ normalizer (L : Set H) := hMN (mem_centralizer_singleton_iff.2 hu₁t)
  have ht₂N : t₂ ∈ normalizer (L : Set H) := hMN (mem_centralizer_singleton_iff.2 ht₂t)
  refine ⟨u₁, hu₁N, t₂, ht₂N, hu₁, ht₂, hu₁₂, hu₁t, act_mul_self hu₁N hu₁₂,
    act_mul_self ht₂N ht₂₂, ?_, fun q hq => S.fix_of_oddCore hoc c hu₁ ht₂ hu₁N ht₂N hu₁₂ q hq,
    ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ht₂u₁.symm
  · intro h1 hne
    have h2 : t₂ ∈ centralizer (L : Set H) :=
      (normalizerAction_eq_one_iff S.perfect ⟨t₂, ht₂N⟩).1 h1
    rcases S.eq_one_or_eq_t h2 ht₂₂ ht₂t with h3 | h3
    · apply ne_one_of_orderOf_eq_two S.t_order
      have h4 : c⁻¹ * t * c = 1 := ht₂.symm.trans h3
      have h5 : t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      rw [h5, h4]
      group
    · apply hne
      have h4 : c⁻¹ * t * c = t := ht₂.symm.trans h3
      have h5 : c * t = t * c := by
        calc c * t = c * (c⁻¹ * t * c) := by rw [h4]
          _ = t * c := by group
      rw [← hc, h5]
      group
  · intro h1
    have h2 : u₁⁻¹ * t₂ ∈ centralizer (L : Set H) := by
      have h3 : normalizerAction L (⟨u₁, hu₁N⟩⁻¹ * ⟨t₂, ht₂N⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact (normalizerAction_eq_one_iff S.perfect _).1 h3
    have hi : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁₂
    rw [hi] at h2
    have hsq : (u₁ * t₂) * (u₁ * t₂) = 1 := by
      calc u₁ * t₂ * (u₁ * t₂) = u₁ * (t₂ * u₁) * t₂ := by group
        _ = u₁ * (u₁ * t₂) * t₂ := by rw [ht₂u₁]
        _ = (u₁ * u₁) * (t₂ * t₂) := by group
        _ = 1 := by rw [hu₁₂, ht₂₂, mul_one]
    have hcom : (u₁ * t₂) * t = t * (u₁ * t₂) := by
      calc u₁ * t₂ * t = u₁ * (t₂ * t) := by group
        _ = u₁ * (t * t₂) := by rw [ht₂t]
        _ = (u₁ * t) * t₂ := by group
        _ = (t * u₁) * t₂ := by rw [hu₁t]
        _ = t * (u₁ * t₂) := by group
    rcases S.eq_one_or_eq_t h2 hsq hcom with h3 | h3
    · exfalso
      have h5 : u₁ = t₂ := by
        rw [eq_inv_of_mul_eq_one_left h3]
        exact inv_eq_of_mul_eq_one_right ht₂₂
      rw [hu₁, ht₂] at h5
      have h6 : u = t := by
        have := mul_right_cancel h5
        exact mul_left_cancel this
      exact S.t_not_mem (h6 ▸ S.u_mem)
    · have h5 : t₂ = u₁ * t := by
        calc t₂ = u₁ * (u₁⁻¹ * t₂) := by group
          _ = u₁ * (u₁ * t₂) := by rw [hi]
          _ = u₁ * t := by rw [h3]
      have h6 : t = u * t' := by
        calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
          _ = c * (u₁ * t) * c⁻¹ := by rw [← ht₂, h5]
          _ = c * (c⁻¹ * u * c * t) * c⁻¹ := by rw [hu₁]
          _ = u * (c * t * c⁻¹) := by group
          _ = u * t' := by rw [hc]
      calc t' = u * (u * t') := by rw [← mul_assoc, huu, one_mul]
        _ = u * t := by rw [← h6]

theorem sol78Fusion_of_data {E : MulAut (↥L ⧸ center ↥L) → Prop}
    (hacc : AutCenterCondExc (↥L ⧸ center ↥L) E) (hoc : AutOddCoreTrivial (↥L ⧸ center ↥L))
    (hexc : ∀ (u₁ : H) (hN : u₁ ∈ normalizer (L : Set H)), u₁ * u₁ = 1 → u₁ * t = t * u₁ →
      IsConj u u₁ → ¬ E (normalizerAction L ⟨u₁, hN⟩)) :
    Sol78Fusion u t := by
  intro t' ht'
  by_cases hne : t' = t
  · exact Or.inl hne
  right
  obtain ⟨c, hc⟩ := isConj_iff.1 ht'.1
  obtain ⟨u₁, hu₁N, t₂, ht₂N, hu₁, -, hu₁₂, hu₁t, hνν, hσσ, hνσ, hfix, h1, h2⟩ :=
    S.fusion_pair hoc ht' hc
  rcases hacc _ _ hνν hσσ hνσ hfix with h3 | h3 | h3
  · exact (h1 h3 hne).elim
  · exact h2 h3
  · exact absurd h3 (hexc u₁ hu₁N hu₁₂ hu₁t (isConj_iff.2 ⟨c⁻¹, by rw [hu₁]; group⟩))

theorem fusedSet_eq (hf : Sol78Fusion u t) {t' : H} (ht' : t' ∈ fusedSet u t) : t' = t := by
  rcases hf t' ht' with h1 | h1
  · exact h1
  · exfalso
    have hc : IsConj t (u * t) := h1 ▸ ht'.1
    have huu := S.u_mul_self
    have hu1 : (((⟨u, S.u_mem⟩ : ↥L)) : ↥L ⧸ center ↥L) ≠ 1 := fun h =>
      S.u_not_central ((QuotientGroup.eq_one_iff _).1 h)
    obtain ⟨y, hne, hcomm⟩ := exists_fused_lift S.quasisimple S.centre_odd
      (u := (⟨u, S.u_mem⟩ : ↥L)) (Subtype.ext huu) hu1
    have hne' : (y : H) * u * (y : H)⁻¹ ≠ u := fun h => hne (Subtype.ext h)
    have hcomm' : ((y : H) * u * (y : H)⁻¹) * u = u * ((y : H) * u * (y : H)⁻¹) :=
      congrArg Subtype.val hcomm
    have hwL : (y : H) * u * (y : H)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem y.2 S.u_mem) (L.inv_mem y.2)
    have hyt : (y : H) * t = t * y := S.t_comm y.2
    have hwt : ((y : H) * u * (y : H)⁻¹) * t = t * ((y : H) * u * (y : H)⁻¹) := S.t_comm hwL
    have hyt' : (y : H) * t * (y : H)⁻¹ = t := by rw [hyt]; group
    have hconj : (y : H) * (u * t) * (y : H)⁻¹ = ((y : H) * u * (y : H)⁻¹) * t := by
      calc (y : H) * (u * t) * (y : H)⁻¹
          = ((y : H) * u * (y : H)⁻¹) * ((y : H) * t * (y : H)⁻¹) := by group
        _ = ((y : H) * u * (y : H)⁻¹) * t := by rw [hyt']
    obtain ⟨w, hw⟩ : ∃ w, w = (y : H) * u * (y : H)⁻¹ := ⟨_, rfl⟩
    rw [← hw] at hne' hcomm' hwt hconj
    have hut : t * u = u * t := S.u_comm_t.symm
    have hmem : w * t ∈ fusedSet u t := by
      refine ⟨hc.trans (isConj_iff.2 ⟨y, hconj⟩), ?_, ?_⟩
      · calc w * t * u = w * (t * u) := mul_assoc w t u
          _ = w * (u * t) := by rw [hut]
          _ = (w * u) * t := (mul_assoc w u t).symm
          _ = (u * w) * t := by rw [hcomm']
          _ = u * (w * t) := mul_assoc u w t
      · calc w * t * t = (w * t) * t := rfl
          _ = (t * w) * t := by rw [hwt]
          _ = t * (w * t) := mul_assoc t w t
    rcases hf _ hmem with h3 | h3
    · have h4 : w = 1 := mul_eq_right.1 h3
      apply ne_one_of_orderOf_eq_two S.u_order
      have h5 : u = (y : H)⁻¹ * ((y : H) * u * (y : H)⁻¹) * y := by group
      rw [h5, ← hw, h4]
      group
    · exact hne' (mul_right_cancel h3)

end ClosingSetup

end CFSG.EvenSporadicStandard.Induction.Closing
