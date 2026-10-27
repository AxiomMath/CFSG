module

public import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.GH74.KGH
public import CFSG.GH74.Uniqueness.SU.KI1r3Struct
public import CFSG.GH74.Uniqueness.SU.KI1r3Y
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictions
public import CFSG.Walter.TwoRank

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3

structure Cfg (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H) : Prop where
  gh : SU0.GHGroup H
  odd : pPrimeCore 2 H = ⊥
  rank : 3 ≤ Open.twoRank H
  cen : center H ≠ ⊥
  gamma : Open.properTwoGenCoreGamma (T : Subgroup H) 2 ≤ H₀
  ne : H₀ ≠ ⊤

variable {H : Type} [Group H] [Finite H]

theorem exists_central_involution (hO : pPrimeCore 2 H = ⊥) (hc : center H ≠ ⊥) :
    ∃ t ∈ center H, orderOf t = 2 := by
  have hcard : Nat.card (center H) ≠ 1 := fun h => hc (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center H)) p hpd
  have hz' : orderOf (z : H) = p := (Subgroup.orderOf_coe z).trans hz
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨(z : H), z.2, hz'⟩
  · exfalso
    have hN : (zpowers (z : H)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
    have hcop : Nat.Coprime 2 (Nat.card (zpowers (z : H))) := by
      rw [Nat.card_zpowers, hz']
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have hle : zpowers (z : H) ≤ pPrimeCore 2 H :=
      le_sSup (show zpowers (z : H) ∈ {K : Subgroup H | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
        ⟨hN, hcop⟩)
    rw [hO] at hle
    have h1 : (z : H) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
    rw [h1, orderOf_one] at hz'
    exact hp.one_lt.ne hz'

theorem Cfg.pRank_sylow {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀) :
    2 ≤ Open.pRank 2 (T : Subgroup H) := by
  rw [sylow_two_rank_eq]
  have := h.rank
  omega

theorem Cfg.sylow_le {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀) :
    (T : Subgroup H) ≤ H₀ :=
  (sylow_le_gamma T h.pRank_sylow).trans h.gamma

theorem Cfg.center_le {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀) :
    center H ≤ H₀ := by
  intro z hz
  apply h.gamma
  apply sylow_normalizer_le_gamma T h.pRank_sylow
  have hzc : z ∈ centralizer ((T : Subgroup H) : Set H) :=
    Subgroup.mem_centralizer_iff.mpr (fun g _ => Subgroup.mem_center_iff.mp hz g)
  exact Subgroup.centralizer_le_normalizer _ hzc

theorem Cfg.centralizer_le_of_involution {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀)
    {t : H} (htc : t ∈ center H) (ht2 : orderOf t = 2) {u : H} (huH : u ∈ H₀)
    (hu2 : orderOf u = 2) (hut : u ≠ t) : centralizer ({u} : Set H) ≤ H₀ := by
  have hu2' : u * u = 1 := mul_self_eq_one_of_orderOf_two hu2
  have ht2' : t * t = 1 := mul_self_eq_one_of_orderOf_two ht2
  have hu1 : u ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hu2; omega
  have hcomm : u * t = t * u := Subgroup.mem_center_iff.mp htc u
  have hnot : t ∉ zpowers u := by
    intro hmem
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2' hmem with h1 | h1
    · rw [h1, orderOf_one] at ht2; omega
    · exact hut h1.symm
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := u) (y := t)
    (by rw [pow_two]; exact hu2') (by rw [pow_two]; exact ht2') hu1 hnot hcomm
  have hD : zpowers u ⊔ zpowers t ≤ H₀ :=
    sup_le (Subgroup.zpowers_le.mpr huH) (Subgroup.zpowers_le.mpr (h.center_le htc))
  have hrank : 2 ≤ Open.pRank 2 (zpowers u ⊔ zpowers t) :=
    SU1.le_pRank (p := 2) (by norm_num) le_rfl hel (k := 2) (by simp [hcard])
  intro x hx
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxt : x * t = t * x := Subgroup.mem_center_iff.mp htc x
  have hxc : zpowers u ⊔ zpowers t ≤ centralizer ({x} : Set H) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hxu.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hxt.symm
  have hxn : x ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup H) : Set H) := by
    have : x ∈ centralizer ((zpowers u ⊔ zpowers t : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_centralizer_singleton_iff.mp (hxc hg)
      exact this
    exact Subgroup.centralizer_le_normalizer _ this
  exact two_generated_core_subgroup_normalizer_le T H₀ h.sylow_le h.gamma _ hD hrank hxn


@[expose] def Concl (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H) : Prop :=
  ∃ K₁ : Subgroup H, IsComponent K₁ ∧ ¬ K₁ ≤ H₀ ∧
    Open.pRank 2 (centralizer (K₁ : Set H)) = 1 ∧
    (((K₁.Normal ∧ (IsSL25 ↥K₁ ∨ CFSG.BenderSuzuki.IsBenderGroup ↥K₁) ∧
        centralizer (K₁ : Set H) ≤ H₀ ∧
        Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤
          K₁ ⊔ centralizer (K₁ : Set H)) ∨
      (IsSL25 ↥K₁ ∧ ∃ K₂ : Subgroup H, IsComponent K₂ ∧ K₂ ≠ K₁ ∧ IsSL25 ↥K₂ ∧
        generalizedFitting H = K₁ ⊔ K₂ ∧
        Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ generalizedFitting H) ∨
      (K₁ = ⊤ ∧ IsTwoAlt ↥K₁ 9 ∧ IsTwoAlt ↥H₀ 8) ∨
      (IsTwoSz8 ↥K₁ ∧ K₁ ⊔ centralizer (K₁ : Set H) = ⊤ ∧
        Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ K₁)) ∧
      (CFSG.BenderSuzuki.IsBenderGroup ↥K₁ ∨ IsCyclic ↥(center ↥(T : Subgroup H))))

@[expose] def Bender34c : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.BenderSuzuki.IsBenderGroup L → ∀ α : MulAut L,
    α ^ 2 = 1 → ∀ D : Subgroup L, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder D →
      (∀ x : L, α x = x → x ∈ D) → ∃ l : L, ∀ x : L, α x = l * x * l⁻¹

omit [Finite H] in
theorem isComponentOf_top_of_isComponent {L : Subgroup H} (hL : IsComponent L) :
    Open.IsComponentOf L ⊤ :=
  ⟨le_top, (CFSG.Adapters.isSubnormal_top_iff L).mpr hL.2,
    ⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩⟩

omit [Finite H] in
theorem nonabelian_of_component {L : Subgroup H} (hL : IsComponent L) :
    ∃ a b : ↥L, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

omit [Finite H] in
theorem center_eq_bot_of_simple_component {L : Subgroup H} (hL : IsComponent L)
    (hs : IsSimpleGroup ↥L) : center ↥L = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center ↥L) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have : (a : ↥L ⧸ center ↥L) = 1 := (QuotientGroup.eq_one_iff a).mpr (by rw [h]; trivial)
    rw [this, one_mul, mul_one]


section Rank2

variable {T : Sylow 2 H} {H₀ : Subgroup H}

theorem Cfg.rank2_component (h : Cfg H T H₀) {L : Subgroup H} (hL : IsComponent L)
    (hrank : 2 ≤ Open.pRank 2 L) :
    L.Normal ∧ ¬ L ≤ H₀ ∧ centralizer (L : Set H) ≤ H₀ ∧
      Open.pRank 2 (centralizer (L : Set H)) = 1 ∧
      ∃ TL : Sylow 2 ↥L, Subgroup.map L.subtype (TL : Subgroup ↥L) = (T : Subgroup H) ⊓ L ∧
        Open.properTwoGenCoreGamma (TL : Subgroup ↥L) 2 ≤ H₀.subgroupOf L ∧
        H₀.subgroupOf L < ⊤ := by
  obtain ⟨t, htc, ht2⟩ := exists_central_involution h.odd h.cen
  have hLq := isComponentOf_top_of_isComponent hL
  have key : ∃ (hchar : L.Characteristic) (TL : Sylow 2 ↥L),
      Subgroup.map L.subtype (TL : Subgroup ↥L) = (T : Subgroup H) ⊓ L ∧
      Open.properTwoGenCoreGamma (TL : Subgroup ↥L) 2 ≤ H₀.subgroupOf L ∧
      H₀.subgroupOf L < ⊤ ∧ Open.pRank 2 (centralizer (L : Set H)) ≤ 1 := by
    obtain ⟨hchar, hres⟩ := proper_full_core_high_rank_component_restrictions T H₀ h.ne h.sylow_le
      h.gamma L hLq hrank
    let := hchar
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨hchar, CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T L, hres⟩
  obtain ⟨hchar, TL, hTL, hΓL, hDlt, hCrk⟩ := key
  have hLn : L.Normal := by
    have := hchar
    infer_instance
  have hLnotle : ¬ L ≤ H₀ := fun hle => hDlt.ne (Subgroup.subgroupOf_eq_top.mpr hle)
  have hpr : 2 ≤ Open.pRank 2 ((T : Subgroup H) ⊓ L) := by
    rw [← hTL, SU4.pRank_map_of_injective L.subtype L.subtype_injective, sylow_two_rank_eq]
    have h1 := SU4.pRank_map_of_injective L.subtype L.subtype_injective (⊤ : Subgroup ↥L)
    have h2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [Subgroup.map_top]; exact Subgroup.range_subtype _
    rw [h2] at h1
    unfold Open.twoRank
    omega
  have hCle : centralizer (L : Set H) ≤ H₀ := by
    refine le_trans (Subgroup.centralizer_le (s := (((T : Subgroup H) ⊓ L : Subgroup H) : Set H))
      (t := (L : Set H)) (fun x hx => hx.2)) ?_
    exact two_generated_core_subgroup_centralizer_le T H₀ h.sylow_le h.gamma _
      (inf_le_left.trans h.sylow_le) hpr
  have htcent : t ∈ centralizer (L : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun l _ => Subgroup.mem_center_iff.mp htc l
  exact ⟨hLn, hLnotle, hCle, le_antisymm hCrk (one_le_two_rank_of_involution_mem _ t htcent ht2),
    TL, hTL, hΓL, hDlt⟩

end Rank2

theorem ki6_simple
    (h34 : Bender34c) {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀)
    {L : Subgroup H} (hL : IsComponent L) (hLs : IsSimpleGroup ↥L) : Concl H T H₀ := by
  obtain ⟨t, htc, ht2⟩ := exists_central_involution h.odd h.cen
  have hnab := nonabelian_of_component hL
  have hLz := center_eq_bot_of_simple_component hL hLs
  have heven : Even (Nat.card ↥L) := CFSG.GH74.even_card_of_nonabelian_simple hnab
  have hrankL : 2 ≤ Open.twoRank ↥L := CFSG.Walter.two_le_twoRank ↥L hnab heven
  have hrankLH : 2 ≤ Open.pRank 2 L := by
    have h1 := SU4.pRank_map_of_injective L.subtype L.subtype_injective (⊤ : Subgroup ↥L)
    have h2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [Subgroup.map_top]; exact Subgroup.range_subtype _
    rw [h2] at h1
    unfold Open.twoRank at hrankL
    omega
  obtain ⟨hLn, hLnotle, hCle, hrk, TL, hTL, hΓL, hDlt⟩ := h.rank2_component hL hrankLH
  have := hLn
  set D : Subgroup ↥L := H₀.subgroupOf L with hD
  have hTLle : (TL : Subgroup ↥L) ≤ D := by
    intro x hx
    have hx' : (x : H) ∈ (T : Subgroup H) ⊓ L := by rw [← hTL]; exact ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (h.sylow_le hx'.1)
  have hcent : ∀ u ∈ D, orderOf u = 2 → centralizer ({u} : Set ↥L) ≤ D := by
    intro u hu hu2 x hx
    have huH : (u : H) ∈ H₀ := Subgroup.mem_subgroupOf.mp hu
    have hu2' : orderOf (u : H) = 2 := (Subgroup.orderOf_coe u).trans hu2
    have hut : (u : H) ≠ t := by
      intro hut
      have htL : t ∈ L := by rw [← hut]; exact u.2
      have hmem : (⟨t, htL⟩ : ↥L) ∈ center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.mp htc g)
      rw [hLz, Subgroup.mem_bot] at hmem
      have h1 : t = 1 := congrArg Subtype.val hmem
      rw [h1, orderOf_one] at ht2
      omega
    have hC := h.centralizer_le_of_involution htc ht2 huH hu2' hut
    have hx' : (x : H) ∈ centralizer ({(u : H)} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
    exact Subgroup.mem_subgroupOf.mpr (hC hx')
  have hSE := strongly_embedded_order_of_full_core_centralizer_closure (G := ↥L) TL D hDlt.ne
    hTLle hrankL hΓL hcent
  have hB : CFSG.BenderSuzuki.IsBenderGroup ↥L := CFSG.BenderSuzuki.bender_suzuki D hSE
  have htcent : t ∈ centralizer (L : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun l _ => Subgroup.mem_center_iff.mp htc l
  have hΩ : Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤
      L ⊔ centralizer (L : Set H) := by
    rw [Subgroup.closure_le]
    rintro g ⟨hgT, hg2⟩
    by_cases hg1 : g = 1
    · rw [hg1]; exact (L ⊔ centralizer (L : Set H)).one_mem
    by_cases hgt : g = t
    · rw [hgt]; exact Subgroup.mem_sup_right htcent
    have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
    have hC := h.centralizer_le_of_involution htc ht2 (h.sylow_le hgT) hgo hgt
    let α : MulAut ↥L := MulAut.conjNormal g
    have hα2 : α ^ 2 = 1 := by
      change (MulAut.conjNormal g : MulAut ↥L) ^ 2 = 1
      rw [← map_pow]
      have : g ^ 2 = 1 := by rw [pow_two]; exact hg2
      rw [this, map_one]
    have hfix : ∀ x : ↥L, α x = x → x ∈ D := by
      intro x hx
      have h1 : g * (x : H) * g⁻¹ = x := by
        have := congrArg Subtype.val hx
        simpa [α, MulAut.conjNormal_apply] using this
      have hxc : (x : H) ∈ centralizer ({g} : Set H) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (x : H) * g = g * (x : H) * g⁻¹ * g := by rw [h1]
          _ = g * x := by group
      exact Subgroup.mem_subgroupOf.mpr (hC hxc)
    obtain ⟨l, hl⟩ := h34 ↥L hB α hα2 D hSE hfix
    have hlg : (l : H)⁻¹ * g ∈ centralizer (L : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hl ⟨x, hx⟩
      have h2 : g * x * g⁻¹ = l * x * (l : H)⁻¹ := by
        have := congrArg Subtype.val h1
        simpa [α, MulAut.conjNormal_apply] using this
      calc x * ((l : H)⁻¹ * g) = (l : H)⁻¹ * (l * x * (l : H)⁻¹) * g := by group
        _ = (l : H)⁻¹ * (g * x * g⁻¹) * g := by rw [h2]
        _ = ((l : H)⁻¹ * g) * x := by group
    have : g = (l : H) * ((l : H)⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup l.2 hlg
  exact ⟨L, hL, hLnotle, hrk, Or.inl ⟨hLn, Or.inr hB, hCle, hΩ⟩, Or.inl hB⟩

end CFSG.GH74.Uniqueness.SU.K.R6
