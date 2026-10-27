module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)

theorem exists_hypCover {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ) (h : UnitaryFieldData 2 f K) (r ε : ℕ)
      (ρ : hypSU h r ε →* ↥L), 1 ≤ r ∧ ε ≤ 1 ∧
      (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f) ∧ Function.Surjective ρ ∧
      ∀ g, ρ g ∈ Subgroup.center ↥L ↔ g ∈ hypScalars h r ε := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r₀ q =>
    change q.p = 2 at hd
    have hc := SQTK.statedClassicalModel_twistedA r₀ q hv e
    rw [hd] at hc
    obtain ⟨⟨-, hf, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
      (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
    obtain ⟨r, ε, hr, hε, hn⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ r₀ + 1 = 2 * r + ε :=
      ⟨(r₀ + 1) / 2, (r₀ + 1) % 2, by omega, by omega, by omega⟩
    rw [hn] at e' hn3 hnq
    obtain ⟨ρ₀, hρ₀, -, hρ₀e⟩ := kFactCoverUnitary Y L hL hodd _ _ K hcard hn3 hnq e'
    have h := ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
    obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
    refine ⟨K, hK, hKfin, q.exponent, h, r, ε, ρ₀.comp (hypTransport h hR).toMonoidHom, hr, hε,
      fun r₁ q₁ h₁ => ?_, hρ₀.comp (hypTransport h hR).surjective, fun g => ?_⟩
    · injection h₁ with h₃ h₂
      rw [← h₂, hqc]
    rw [← QuotientGroup.eq_one_iff, ← ker_hypProj, MonoidHom.mem_ker,
      ← (hypPSUEquivStatedProj h hR (by omega)).map_eq_one_iff, hypPSUEquivStatedProj_hypProj,
      ← hρ₀e, e'.map_eq_one_iff]
    rfl
  | _ => exact hd.elim

section Lift

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {G : Type*} [Group G] [Finite G]
  {ρ : G →* ↥L} {Z : Subgroup G}

theorem le_normalizer_centralizer_twistedA (L : Subgroup Y) :
    L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) := by
  intro l hl
  refine Subgroup.mem_normalizer_fintype fun c hc => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro x hx
  have h1 := hc (l⁻¹ * x * l) (L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl)
  calc x * (l * c * l⁻¹) = l * ((l⁻¹ * x * l) * c) * l⁻¹ := by group
    _ = l * (c * (l⁻¹ * x * l)) * l⁻¹ := by rw [h1]
    _ = l * c * l⁻¹ * x := by group

theorem exists_mul_of_mem_sup_centralizer_of_le {H : Subgroup Y} (hHL : H ≤ L) {u : Y}
    (hu : u ∈ H ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ x ∈ H, ∃ c ∈ Subgroup.centralizer (L : Set Y), x * c = u := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hHL.trans (le_normalizer_centralizer_twistedA L))] at hu
  obtain ⟨x, hx, c, hc, rfl⟩ := hu
  exact ⟨x, hx, c, hc, rfl⟩

omit [Finite Y] in
theorem mem_center_of_mem_centralizer_twistedA {x : ↥L}
    (hx : (x : Y) ∈ Subgroup.centralizer (L : Set Y)) : x ∈ Subgroup.center ↥L :=
  Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)

variable (hρ : Function.Surjective ρ) (hZ : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ g ∈ Z)
include hρ

theorem exists_sylow_normalizer_le_comap_of_surjective (hP : IsParabolicTwo L J) :
    ∃ T : Sylow 2 G, Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ (J.subgroupOf L).comap ρ := by
  obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  obtain ⟨T₀, hT₀⟩ := Sylow.mapSurjective_surjective hρ 2 T'
  refine ⟨T₀, fun y hy => ?_⟩
  have h1 : ρ y ∈ Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) := by
    rw [← hT₀, Sylow.coe_mapSurjective]
    exact Subgroup.le_normalizer_map ρ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  refine hNJ ⟨(ρ y).2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
  have h2 : (⟨t, hTL ht⟩ : ↥L) ∈ (T' : Subgroup ↥L) := by
    simpa [T', Subgroup.mem_subgroupOf] using ht
  have h3 := (Subgroup.mem_normalizer_iff.1 h1 ⟨t, hTL ht⟩).1 h2
  simpa [T', Subgroup.mem_subgroupOf] using h3

omit [Finite Y] [Finite G] in
theorem comap_ne_top_of_ne (hJL : J ≤ L) (hne : J ≠ L) : (J.subgroupOf L).comap ρ ≠ ⊤ := by
  intro htop
  refine hne (le_antisymm hJL fun l hl => ?_)
  obtain ⟨g, hg⟩ := hρ ⟨l, hl⟩
  have : g ∈ (J.subgroupOf L).comap ρ := by rw [htop]; exact Subgroup.mem_top g
  rwa [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hg] at this

include hZ

omit [Finite G] in
theorem exists_lift_of_mem_sup {u : Y} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) {m : ℕ}
    (hum : u ^ m = 1) :
    ∃ (t : G) (c : Y), c ∈ Subgroup.centralizer (L : Set Y) ∧ u = (ρ t : Y) * c ∧ t ^ m ∈ Z := by
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer_of_le le_rfl hu
  obtain ⟨t, ht⟩ := hρ ⟨l, hl⟩
  refine ⟨t, c, hc, by rw [ht], (hZ _).mp (mem_center_of_mem_centralizer_twistedA ?_)⟩
  have hcomm : Commute l c := Subgroup.mem_centralizer_iff.mp hc l hl
  have hlm : l ^ m = (c ^ m)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hcomm.mul_pow, hum])
  rw [map_pow, Subgroup.coe_pow, ht, hlm]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc m)

omit [Finite Y] [Finite G] hρ hZ in
theorem forall_commute_mem_comap {u : Y} {t : G} {c : Y} (hc : c ∈ Subgroup.centralizer (L : Set Y))
    (hu : u = (ρ t : Y) * c) (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∀ y : G, Commute y t → y ∈ (J.subgroupOf L).comap ρ := by
  intro y hy
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  refine hfix _ (ρ y).2 ?_
  have hcy : c * (ρ y : Y) = (ρ y : Y) * c := (Subgroup.mem_centralizer_iff.mp hc _ (ρ y).2).symm
  have hty : (ρ t : Y) * (ρ y : Y) = (ρ y : Y) * (ρ t : Y) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hy.eq]
  rw [hu, mul_inv_rev, show (ρ t : Y) * c * (ρ y : Y) * (c⁻¹ * (ρ t : Y)⁻¹) =
    (ρ t : Y) * (c * (ρ y : Y)) * c⁻¹ * (ρ t : Y)⁻¹ by group, hcy,
    show (ρ t : Y) * ((ρ y : Y) * c) * c⁻¹ * (ρ t : Y)⁻¹ = (ρ t : Y) * (ρ y : Y) * (ρ t : Y)⁻¹ by
      group, hty, mul_inv_cancel_right]

omit [Finite Y] [Finite G] hρ hZ in
theorem perfectJoin_subgroupOf_le (hJL : J ≤ L) :
    (perfectJoin J).subgroupOf L ≤ perfectJoin (J.subgroupOf L) := by
  refine le_perfectJoin (fun x hx => ?_) ?_
  · rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact perfectJoin_le J hx
  · refine Subgroup.map_injective L.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left ((perfectJoin_le J).trans hJL), perfectJoin_perfect]

omit [Finite G] in
theorem mem_perfectJoin_sup_of_mul_mem (hZc : Z ≤ Subgroup.center G) (hJL : J ≤ L) {t : G}
    {c : Y} (hc : c ∈ Subgroup.centralizer (L : Set Y))
    (hu : (ρ t : Y) * c ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)) :
    t ∈ perfectJoin ((J.subgroupOf L).comap ρ) ⊔ Z := by
  obtain ⟨j, hj, c', hc', hjc⟩ :=
    exists_mul_of_mem_sup_centralizer_of_le ((perfectJoin_le J).trans hJL) hu
  have hjL : j ∈ L := hJL (perfectJoin_le J hj)
  have hker : ρ.ker ≤ Subgroup.center G := fun g hg =>
    hZc ((hZ g).mp (by rw [MonoidHom.mem_ker.mp hg]; exact Subgroup.one_mem _))
  have hkJ : ρ.ker ≤ (J.subgroupOf L).comap ρ := fun g hg => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
    exact Subgroup.one_mem _
  have hmap := ToralCensus.map_perfectJoin_eq ρ hρ hker hkJ
  rw [Subgroup.map_comap_eq_self_of_surjective hρ] at hmap
  have hj' : (⟨j, hjL⟩ : ↥L) ∈ perfectJoin (J.subgroupOf L) :=
    perfectJoin_subgroupOf_le hJL (Subgroup.mem_subgroupOf.mpr hj)
  rw [← hmap] at hj'
  obtain ⟨a, ha, haj⟩ := hj'
  have hrest : a⁻¹ * t ∈ Z := by
    refine (hZ _).mp (mem_center_of_mem_centralizer_twistedA ?_)
    have h1 : (ρ (a⁻¹ * t) : Y) = c' * c⁻¹ := by
      rw [map_mul, map_inv, haj, Subgroup.coe_mul, Subgroup.coe_inv]
      calc j⁻¹ * (ρ t : Y) = j⁻¹ * ((ρ t : Y) * c) * c⁻¹ := by group
        _ = c' * c⁻¹ := by rw [← hjc]; group
    rw [h1]
    exact Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)
  have : t = a * (a⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ha hrest

omit [Finite Y] [Finite G] hρ in
theorem cycPerfect_comap {m : ℕ} (hmZ : Nat.Coprime (Nat.card Z) m) (hcyc : CycPerfect m J) :
    ∀ V : Subgroup G, V ≤ (J.subgroupOf L).comap ρ → ⁅V, V⁆ = V →
      ∀ Q : Subgroup G, Q ≤ V → IsPGroup m Q → IsCyclic Q := by
  intro V hVJ hV Q hQV hQ
  set φ : G →* Y := L.subtype.comp ρ
  have hV' : V.map φ ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    have := hVJ hx
    rwa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at this
  have hVp : ⁅V.map φ, V.map φ⁆ = V.map φ := by rw [← Subgroup.map_commutator, hV]
  have hQc : IsCyclic (Q.map φ) :=
    hcyc _ hV' hVp _ (Subgroup.map_mono hQV) (hQ.map φ)
  refine isCyclic_of_injective (φ.subgroupMap Q) fun x y hxy => ?_
  have hρxy : ρ ((x : G)⁻¹ * y) = 1 := by
    have h1 : ((φ.subgroupMap Q x : ↥(Q.map φ)) : Y) = ((φ.subgroupMap Q y : ↥(Q.map φ)) : Y) := by
      rw [hxy]
    have : ρ (x : G) = ρ (y : G) := L.subtype_injective h1
    rw [map_mul, map_inv, this, inv_mul_cancel]
  have hZmem : (x : G)⁻¹ * y ∈ Z := (hZ _).mp (by rw [hρxy]; exact Subgroup.one_mem _)
  have hQmem : (x : G)⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem x.2) y.2
  obtain ⟨k, hk⟩ := hQ ⟨_, hQmem⟩
  have hord : orderOf ((x : G)⁻¹ * y) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hmZ.pow_right k) (Subgroup.orderOf_dvd_natCard Z hZmem)
      (orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk))
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at hord
  exact Subtype.ext hord

omit [Finite Y] [Finite G] in
theorem card_center_dvd_card_of_surjective : Nat.card (Subgroup.center ↥L) ∣ Nat.card Z := by
  have heq : Subgroup.center ↥L = Z.map ρ := by
    ext z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := hρ z
      exact ⟨g, (hZ g).mp hz, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact (hZ g).mpr hg
  rw [heq]
  exact Subgroup.card_map_dvd Z ρ

end Lift

end CFSG.AGLEmbedding.ToralCensus
