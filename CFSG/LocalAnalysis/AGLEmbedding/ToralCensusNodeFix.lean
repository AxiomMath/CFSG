module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin le_perfectJoin perfectJoin_le perfectJoin_perfect
  exists_perfect_map_eq)

@[expose] def CentralizerEscapes (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (S : Sylow 2 X) (J : Subgroup X), Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ J →
    J ≠ Subgroup.normalizer ((S : Subgroup X) : Set X) → J ≠ ⊤ → CycPerfect p J →
    ∀ u ∈ perfectJoin J, u ^ p = 1 → u ∉ Subgroup.center X →
    ∃ g ∈ J, ∃ P : Subgroup X, ⁅P, P⁆ = P ∧
      (∀ x ∈ P, x * (g * u * g⁻¹) = g * u * g⁻¹ * x) ∧ ¬ P ≤ J

namespace ToralCensus

variable {G X : Type*} [Group G] [Group X]

theorem mem_of_map_mem_of_ker_le {ψ : G →* X} {J : Subgroup G} (hkJ : ψ.ker ≤ J) {x : G}
    (h : ψ x ∈ J.map ψ) : x ∈ J := by
  obtain ⟨j, hj, hje⟩ := h
  have : j⁻¹ * x ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hje, inv_mul_cancel]
  simpa using J.mul_mem hj (hkJ this)

theorem cycPerfect_subgroupOf {L J : Subgroup G} {p : ℕ} (hJ : CycPerfect p J) :
    CycPerfect p (J.subgroupOf L) := by
  intro V hVJ hV Q hQV hQ
  have hc := hJ (V.map L.subtype)
    (by rintro _ ⟨x, hx, rfl⟩; exact Subgroup.mem_subgroupOf.1 (hVJ hx))
    (by rw [← Subgroup.map_commutator, hV]) (Q.map L.subtype) (Subgroup.map_mono hQV) (hQ.map _)
  let e := Subgroup.equivMapOfInjective Q L.subtype L.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem cycPerfect_map [Finite G] {ψ : G →* X} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hkJ : ψ.ker ≤ J) (hJ : CycPerfect p J) : CycPerfect p (J.map ψ) := by
  intro V hVJ hV Q hQV hQ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨V₀, hV₀, -, hV₀e⟩ := exists_perfect_map_eq ψ hker hV
    (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
  have hV₀J : V₀ ≤ J := fun v hv => mem_of_map_mem_of_ker_le hkJ (hVJ (hV₀e ▸ ⟨v, hv, rfl⟩))
  set A := Q.comap ψ ⊓ V₀ with hA
  have hAQ : A.map ψ = Q := by
    refine le_antisymm (by rintro _ ⟨a, ha, rfl⟩; exact ha.1) fun q hq => ?_
    obtain ⟨v, hv, rfl⟩ : q ∈ V₀.map ψ := hV₀e ▸ hQV hq
    exact ⟨v, ⟨hq, hv⟩, rfl⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow p A) := inferInstance
  set P := (P₀ : Subgroup A).map A.subtype with hP
  have hPA : P ≤ A := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hPc : IsCyclic P := hJ V₀ hV₀J hV₀ P (hPA.trans inf_le_right) (P₀.isPGroup'.map _)
  have hQp : IsPGroup p (A.map ψ) := hAQ ▸ hQ
  set S := P₀.mapSurjective (ψ.subgroupMap_surjective A) with hS
  have hStop : (S : Subgroup (A.map ψ)) = ⊤ :=
    top_le_iff.1 ((hQp.to_subgroup ⊤).le_sylow_of_normal S)
  have hPQ : P.map ψ = Q := by
    refine le_antisymm ((Subgroup.map_mono hPA).trans hAQ.le) fun q hq => ?_
    have hq' : (⟨q, hAQ ▸ hq⟩ : A.map ψ) ∈ (S : Subgroup (A.map ψ)) := by
      rw [hStop]
      trivial
    rw [hS, Sylow.coe_mapSurjective] at hq'
    obtain ⟨x, hx, hxe⟩ := hq'
    refine ⟨x, ⟨x, hx, rfl⟩, ?_⟩
    have := congrArg Subtype.val hxe
    simpa using this
  rw [← hPQ]
  exact isCyclic_of_surjective (ψ.subgroupMap P) (ψ.subgroupMap_surjective P)

theorem mem_perfectJoin_subgroupOf {Y : Type*} [Group Y] {L J : Subgroup Y} (hJL : J ≤ L) {v : Y}
    (hv : v ∈ perfectJoin J) :
    (⟨v, hJL (perfectJoin_le J hv)⟩ : L) ∈ perfectJoin (J.subgroupOf L) := by
  set W := (perfectJoin J).subgroupOf L with hW
  have hWm : W.map L.subtype = perfectJoin J := by
    rw [hW, Subgroup.subgroupOf_map_subtype, inf_of_le_left ((perfectJoin_le J).trans hJL)]
  have hWp : ⁅W, W⁆ = W := Subgroup.map_injective L.subtype_injective (by
    rw [Subgroup.map_commutator, hWm, perfectJoin_perfect])
  refine le_perfectJoin (fun x hx => ?_) hWp (Subgroup.mem_subgroupOf.2 hv)
  exact Subgroup.mem_subgroupOf.2 (perfectJoin_le J (Subgroup.mem_subgroupOf.1 hx))

end ToralCensus

open ToralCensus in
theorem false_of_centralizerEscapes {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hP : CompParab L J) {p : ℕ} (hp : p.Prime) (hcyc : CycPerfect p J)
    (hX : CentralizerEscapes p (↥L ⧸ Subgroup.center ↥L)) {v : Y} (hvP : v ∈ perfectJoin J)
    (hvC : v ∉ Subgroup.centralizer (L : Set Y)) (hvp : v ^ p ∈ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, v * l * v⁻¹ = l → l ∈ J) : False := by
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP.parab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvL : v ∈ L := hJL (perfectJoin_le J hvP)
  set ψ := QuotientGroup.mk' (Subgroup.center ↥L) with hψdef
  have hψ : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hker : ψ.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card ψ.ker) := by rw [hker]; exact hP.odd
  set J' : Subgroup ↥L := J.subgroupOf L with hJ'
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  have hT'mem : ∀ t : ↥L, t ∈ (T' : Subgroup ↥L) ↔ (t : Y) ∈ T := fun t => Iff.rfl
  have hNT : ∀ x : ↥L, x ∈ Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) →
      (x : Y) ∈ L ⊓ Subgroup.normalizer (T : Set Y) := fun x hx =>
    ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => by
      have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 ((hT'mem _).2 ht)
      simpa [hT'mem] using h2⟩
  have hNJ' : Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) ≤ J' := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hNJ (hNT x hx))
  have hZJ : ψ.ker ≤ J' :=
    hker.le.trans ((Subgroup.center_le_normalizer ((T' : Subgroup ↥L) : Set ↥L)).trans hNJ')
  set S : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := T'.mapSurjective hψ with hS
  have hNmap : ∀ {M : Subgroup ↥L}, Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) ≤ M →
      Subgroup.normalizer ((S : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
        Set (↥L ⧸ Subgroup.center ↥L)) ≤ M.map ψ :=
    fun hM => by
      rw [hS, Sylow.coe_mapSurjective]
      exact normalizer_map_le_map ψ hψ hker.le hodd T'.isPGroup' hM
  have hNS := hNmap hNJ'
  have hne : J'.map ψ ≠ Subgroup.normalizer ((S : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
      Set (↥L ⧸ Subgroup.center ↥L)) := by
    intro he
    have hle : J' ≤ Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) := fun x hx =>
      mem_of_map_mem_of_ker_le (hker.le.trans (Subgroup.center_le_normalizer _))
        (hNmap le_rfl (he ▸ ⟨x, hx, rfl⟩))
    refine hP.ne_borel T ⟨hTL, hT2, hTi⟩ (le_antisymm (fun y hy => ?_) hNJ)
    exact hNT ⟨y, hJL hy⟩ (hle (Subgroup.mem_subgroupOf.2 hy))
  have htop : J'.map ψ ≠ ⊤ := by
    intro he
    refine hP.ne_top (le_antisymm hJL fun l hl => ?_)
    have : (⟨l, hl⟩ : ↥L) ∈ J' := mem_of_map_mem_of_ker_le hZJ (he ▸ Subgroup.mem_top _)
    exact Subgroup.mem_subgroupOf.1 this
  have hcyc' := cycPerfect_map hψ hker.le hp hZJ (cycPerfect_subgroupOf (L := L) hcyc)
  have hvZ : ∀ {w : ↥L}, w ∈ Subgroup.center ↥L ↔ (w : Y) ∈ Subgroup.centralizer (L : Set Y) :=
    fun {w} => by
      rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
      exact ⟨fun h l hl => congrArg Subtype.val (h ⟨l, hl⟩), fun h g => Subtype.ext (h g g.2)⟩
  have hu := ParabAutIrr.map_perfectJoin_le ψ le_rfl ⟨_, mem_perfectJoin_subgroupOf hJL hvP, rfl⟩
  have hup : ψ ⟨v, hvL⟩ ^ p = 1 := by
    rw [← map_pow, hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hvZ.2 (by simpa using hvp)
  have hu1 : ψ ⟨v, hvL⟩ ∉ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
    have : Group.IsPerfect ↥L := ⟨hP.comp.2.2.1⟩
    rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot]
    exact fun h => hvC (hvZ.1 ((QuotientGroup.eq_one_iff _).1 h))
  obtain ⟨g, hg, P, hP', hPc, hPJ⟩ := hX S (J'.map ψ) hNS hne htop hcyc' _ hu hup hu1
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  set v' : ↥L := g₀ * ⟨v, hvL⟩ * g₀⁻¹ with hv'
  have hfix' : ∀ l : ↥L, v' * l * v'⁻¹ = l → l ∈ J' := by
    intro l hl
    have h1 : (⟨v, hvL⟩ : ↥L) * (g₀⁻¹ * l * g₀) * (⟨v, hvL⟩ : ↥L)⁻¹ = g₀⁻¹ * l * g₀ := by
      calc _ = g₀⁻¹ * (v' * l * v'⁻¹) * g₀ := by rw [hv']; group
        _ = _ := by rw [hl]
    have h2 : ((g₀⁻¹ * l * g₀ : ↥L) : Y) ∈ J := hfix _ (g₀⁻¹ * l * g₀).2 (by
      have := congrArg Subtype.val h1
      simpa using this)
    have h3 : g₀⁻¹ * l * g₀ ∈ J' := Subgroup.mem_subgroupOf.2 h2
    have e : l = g₀ * (g₀⁻¹ * l * g₀) * g₀⁻¹ := by group
    rw [e]
    exact J'.mul_mem (J'.mul_mem hg₀ h3) (J'.inv_mem hg₀)
  refine hPJ (le_map_of_perfect_of_commute hψ hker.le hfix' hP' fun x hx => ?_)
  rw [hv', map_mul, map_mul, map_inv]
  exact hPc x hx

theorem exists_perfectJoin_of_join {Y : Type*} [Group Y] {L J : Subgroup Y} (hJL : J ≤ L)
    {p : ℕ} {u : Y} (hjoin : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y))
    (hup : u ^ p = 1) (hu : u ∉ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ v ∈ perfectJoin J, v ∉ Subgroup.centralizer (L : Set Y) ∧
      v ^ p ∈ Subgroup.centralizer (L : Set Y) ∧ ∀ l ∈ L, v * l * v⁻¹ = l → l ∈ J := by
  have hPL : perfectJoin J ≤ L := (perfectJoin_le J).trans hJL
  have hcomm : ∀ {x c : Y}, x ∈ L → c ∈ Subgroup.centralizer (L : Set Y) → x * c = c * x :=
    fun hx hc => Subgroup.mem_centralizer_iff.1 hc _ hx
  have hN : perfectJoin J ≤ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set Y) : Subgroup Y) : Set Y) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun c => by
      constructor
      · intro hc
        rw [show x * c * x⁻¹ = c by rw [hcomm (hPL hx) hc]; group]
        exact hc
      · intro hc
        have h1 : x * (x * c * x⁻¹) = (x * c * x⁻¹) * x := hcomm (hPL hx) hc
        have e : c = x * c * x⁻¹ :=
          calc c = x⁻¹ * ((x * c * x⁻¹) * x) := by group
            _ = x⁻¹ * (x * (x * c * x⁻¹)) := by rw [h1]
            _ = x * c * x⁻¹ := by group
        rw [e]
        exact hc
  have hu' : u ∈ ((perfectJoin J ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y) : Set Y) := hjoin
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hu'
  obtain ⟨v, hv, c, hc, rfl⟩ := hu'
  have hvL : v ∈ L := hPL hv
  have hvc : Commute v c := hcomm hvL hc
  refine ⟨v, hv, fun hvC => hu (mul_mem hvC hc), ?_, fun l hl hvl => hfix l hl ?_⟩
  · have h1 : v ^ p * c ^ p = 1 := by rw [← hvc.mul_pow, hup]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem hc p)
  · have hcl : c * l * c⁻¹ = l := by rw [← hcomm hl hc]; group
    calc v * c * l * (v * c)⁻¹ = v * (c * l * c⁻¹) * v⁻¹ := by group
      _ = l := by rw [hcl, hvl]

theorem FixThreeHyp.false_of_escapes {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} {u : Y} (h : FixThreeHyp L J u)
    (hX : CentralizerEscapes 3 (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨v, hv, hvC, hvp, hfix⟩ :=
    exists_perfectJoin_of_join h.parab.parab.1 h.join h.pow h.not_mem h.fix
  exact AGLEmbedding.false_of_centralizerEscapes h.parab Nat.prime_three h.cyc hX hv hvC hvp hfix

theorem FixPrimeHyp.false_of_escapes {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} {p : ℕ} {u : Y} (h : FixPrimeHyp L J p u)
    (hX : CentralizerEscapes p (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨v, hv, hvC, hvp, hfix⟩ :=
    exists_perfectJoin_of_join h.parab.parab.1 h.join h.pow h.not_mem h.fix
  exact AGLEmbedding.false_of_centralizerEscapes h.parab h.prime h.cyc hX hv hvC hvp hfix

end CFSG.AGLEmbedding
