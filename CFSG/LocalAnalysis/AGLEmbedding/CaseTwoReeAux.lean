module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Generic

variable {X : Type*} [Group X]

theorem mem_normalizer_inf_of_mem_normalizer {A B : Subgroup X} {g : X}
    (hA : g ∈ Subgroup.normalizer (A : Set X)) (hB : g ∈ Subgroup.normalizer (B : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  exact ⟨fun hh => ⟨(hA h).mp hh.1, (hB h).mp hh.2⟩, fun hh => ⟨(hA h).mpr hh.1, (hB h).mpr hh.2⟩⟩

theorem card_sup_mul_card_inf_eq_of_le_normalizer {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N)
    (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  rw [inf_comm] at h2
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

theorem card_mul_card_inf_centralizer_eq [Finite X] {A U : Subgroup X} {J : X}
    (hAU : A ≤ Subgroup.normalizer (U : Set X))
    (hJ : ∀ y ∈ A ⊔ U, ∃ u ∈ U, y * J * y⁻¹ = u * J * u⁻¹) :
    Nat.card A * Nat.card (U ⊓ Subgroup.centralizer ({J} : Set X) : Subgroup X) =
      Nat.card ((A ⊔ U) ⊓ Subgroup.centralizer ({J} : Set X) : Subgroup X) *
        Nat.card (A ⊓ U : Subgroup X) := by
  set Y := A ⊔ U
  set XJ := Y ⊓ Subgroup.centralizer ({J} : Set X)
  have hYN : Y ≤ Subgroup.normalizer (U : Set X) := sup_le hAU Subgroup.le_normalizer
  have hUY : U ≤ Y := le_sup_right
  have hY : U ⊔ XJ = Y := by
    refine le_antisymm (sup_le hUY inf_le_left) fun y hy => ?_
    obtain ⟨u, hu, hyu⟩ := hJ y hy
    have hx : u⁻¹ * y ∈ XJ := by
      refine ⟨Y.mul_mem (Y.inv_mem (hUY hu)) hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u⁻¹ * y * J = u⁻¹ * (y * J * y⁻¹) * y := by group
        _ = u⁻¹ * (u * J * u⁻¹) * y := by rw [hyu]
        _ = J * (u⁻¹ * y) := by group
    rw [← mul_inv_cancel_left u y]
    exact Subgroup.mul_mem_sup hu hx
  have hUX : U ⊓ XJ = U ⊓ Subgroup.centralizer ({J} : Set X) := by
    rw [← inf_assoc, inf_of_le_left hUY]
  have h1 := card_sup_mul_card_inf_eq_of_le_normalizer hAU
  have h2 := card_sup_mul_card_inf_eq_of_le_normalizer (inf_le_left.trans hYN : XJ ≤ _)
  rw [sup_comm, inf_comm] at h1
  rw [hY, hUX] at h2
  have hU : 0 < Nat.card U := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hU ?_
  calc Nat.card U * (Nat.card A * Nat.card (U ⊓ Subgroup.centralizer ({J} : Set X) :
        Subgroup X)) = Nat.card Y * Nat.card (A ⊓ U : Subgroup X) *
          Nat.card (U ⊓ Subgroup.centralizer ({J} : Set X) : Subgroup X) := by
        rw [h1]; ring
    _ = Nat.card U * (Nat.card XJ * Nat.card (A ⊓ U : Subgroup X)) := by
        rw [mul_right_comm, h2]; ring

theorem exists_isPGroup_le_map_eq [Finite X] {Z : Type*} [Group Z] {p : ℕ} [Fact p.Prime]
    (f : X →* Z) {W : Subgroup X} {E : Subgroup Z} (hE : IsPGroup p E) (hEW : E ≤ W.map f) :
    ∃ T : Subgroup X, T ≤ W ∧ IsPGroup p T ∧ T.map f = E := by
  set V : Subgroup X := W ⊓ E.comap f
  let ψ : V →* E := (f.comp V.subtype).codRestrict E fun v => v.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    obtain ⟨w, hw, rfl⟩ := hEW he
    exact ⟨⟨w, hw, he⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow p V) := inferInstance
  have htop : (S : Subgroup V).map ψ = ⊤ := by
    have h := (S.mapSurjective hψ).is_maximal' (hE.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  refine ⟨(S : Subgroup V).map V.subtype, (Subgroup.map_subtype_le _).trans inf_le_left,
    S.isPGroup'.map _, le_antisymm ?_ fun e he => ?_⟩
  · rintro _ ⟨_, ⟨v, -, rfl⟩, rfl⟩
    exact v.2.2
  · obtain ⟨v, hv, hve⟩ : (⟨e, he⟩ : E) ∈ (S : Subgroup V).map ψ := htop ▸ Subgroup.mem_top _
    exact ⟨v, ⟨v, hv, rfl⟩, congrArg Subtype.val hve⟩

theorem exists_isPGroup_zpowers_pow_eq [Finite X] {Z : Type*} [Group Z] (f : X →* Z) {y : X}
    (hy : f y ^ 2 = 1) : ∃ m : ℕ, IsPGroup 2 (Subgroup.zpowers (y ^ m)) ∧ f (y ^ m) = f y := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have h1 : (y ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  refine ⟨m, IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi]), ?_⟩
  obtain ⟨t, rfl⟩ := hm
  rw [map_pow, pow_succ, pow_mul, hy, one_pow, one_mul]

theorem succ_le_pRank_of_isElemAbelian [Finite X] {p : ℕ} (hp : p.Prime) {V Y : Subgroup X}
    (hV : IsElemAbelian p V) {n : ℕ} (hVcard : Nat.card V = p ^ n) {x : X}
    (hxV : x ∈ Subgroup.centralizer (V : Set X)) (hxp : x ^ p = 1) (hx : x ∉ V) (hVY : V ≤ Y)
    (hxY : x ∈ Y) : n + 1 ≤ Open.pRank p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hE := isElemAbelian_sup_zpowers_of_mem_centralizer hV hxV hxp
  have hlt : V < V ⊔ Subgroup.zpowers x := lt_of_le_of_ne le_sup_left fun h =>
    hx (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (fun y : (V ⊔ Subgroup.zpowers x : Subgroup X) =>
    ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩)
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hVcard, hm, pow_lt_pow_iff_right₀ hp.one_lt] at hcard
  have hrank : m ≤ Open.pRank p Y :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, sup_le hVY (Subgroup.zpowers_le.mpr hxY), hE, hm⟩
  omega


end Generic

theorem card_le_of_inf_centralizer_eq_bot {X : Type} [Group X] [Finite X]
    (hL28 : KFactL28AutThree) {L : Subgroup X}
    (hLc : IsCaseTwoGroup 3 L) {S : Subgroup X} (hS : IsPGroup 3 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set X))
    (hSC : S ⊓ Subgroup.centralizer (L : Set X) = ⊥) : Nat.card S ≤ 27 := by
  set N := Subgroup.normalizer (L : Set X)
  set S' := S.subgroupOf N
  set φ : S' →* MulAut L := L.normalizerMonoidHom.comp S'.subtype
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hk : (s : N) ∈ L.normalizerMonoidHom.ker := hs
    rw [Subgroup.normalizerMonoidHom_ker] at hk
    have h1 : ((s : N) : X) ∈ S ⊓ Subgroup.centralizer (L : Set X) := ⟨s.2, hk⟩
    rw [hSC, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hcard : Nat.card S' = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hS' : IsPGroup 3 S' := hS.comap_subtype
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hcard]
  exact hL28 L hLc φ.range (hS'.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)

section Reduced

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {z : G}
  {Pbar : Sylow p (D1CzQuot p z)} {K : Subgroup (D1CzQuot p z)}

abbrev d1CzX0 (p : ℕ) (M : Subgroup G) (z : G) : Subgroup (D1CzQuot p z) :=
  ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p))

theorem D1ReducedCentralizer.normalizer_le (hRC : D1ReducedCentralizer p P M z Pbar K)
    {U : Subgroup (D1CzQuot p z)} (hUP : U ≤ Pbar) (hU : 3 ≤ Open.pRank p U) :
    Subgroup.normalizer (U : Set (D1CzQuot p z)) ≤ d1CzX0 p M z :=
  (normalizer_le_weakCore p hUP (by omega)
    (hU.trans (pRank_mono p hRC.red.prime le_sup_left))).trans hRC.red.weakCore_le

theorem D1ReducedCentralizer.not_le (hRC : D1ReducedCentralizer p P M z Pbar K) (T : Sylow p K)
    (hT : (T : Subgroup K).map K.subtype = (Pbar : Subgroup (D1CzQuot p z)) ⊓ K)
    (h3 : 3 ≤ Open.pRank p ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K)) : ¬ K ≤ d1CzX0 p M z := by
  have : Fact p.Prime := ⟨hRC.red.prime⟩
  have := hRC.normal
  intro hK
  apply hRC.red.ne_top
  rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top T, hT]
  exact sup_le (hRC.normalizer_le inf_le_left h3) hK

theorem D1ReducedCentralizer.not_map_le_of_isCoatom (hRC : D1ReducedCentralizer p P M z Pbar K)
    (T : Sylow p K)
    (hT : (T : Subgroup K).map K.subtype = (Pbar : Subgroup (D1CzQuot p z)) ⊓ K)
    (h3 : 3 ≤ Open.pRank p ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K))
    (hB : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K))) {Y : Subgroup K}
    (hY : ¬ Y ≤ Subgroup.normalizer ((T : Subgroup K) : Set K)) :
    ¬ Y.map K.subtype ≤ d1CzX0 p M z := by
  intro hYX
  have hBX : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map K.subtype ≤ d1CzX0 p M z := by
    refine (Subgroup.le_normalizer_map K.subtype).trans ?_
    rw [hT]
    exact hRC.normalizer_le inf_le_left h3
  have hK : K = (Subgroup.normalizer ((T : Subgroup K) : Set K) ⊔ Y).map K.subtype := by
    rw [(hB.not_le_iff_codisjoint.mp hY).eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  apply hRC.not_le T hT h3
  rw [hK, Subgroup.map_sup]
  exact sup_le hBX hYX

theorem D1Extremal.mem_of_mem_primeCore {H R : Subgroup G} (hext : D1Extremal p P M H R)
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) {o : Subgroup.centralizer ({z} : Set G)}
    (ho : o ∈ primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) : (o : G) ∈ M := by
  have hcore : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hext.prime P hext.sylow_le hext.weakCore_le
      (hext.three_le_pRank.trans (pRank_mono p hext.prime (le_inf hRz hext.le_M)))
  have ho' : o ∈ (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))).subgroupOf
      (Subgroup.centralizer ({z} : Set G)) := by
    rw [glbPrimeCore_subgroupOf]
    exact ho
  exact hcore ho'

theorem D1ReducedCentralizer.centralizer_not_le (hRC : D1ReducedCentralizer p P M z Pbar K) :
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M := fun hCM => hRC.red.ne_top (by
  rw [Subgroup.subgroupOf_eq_top.mpr (le_inf le_rfl hCM),
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)])

theorem D1Extremal.odd_card_primeCore {H R : Subgroup G} (hext : D1Extremal p P M H R)
    {P' : Sylow p G} (hP'M : (P' : Subgroup G) ≤ M) (hRP' : R ≤ P')
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) (hRC : D1ReducedCentralizer p P' M z Pbar K)
    (hR4 : Open.pRank p R < 4) :
    Odd (Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) := by
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G)
  set OC := primeComplementCore (G := C) p
  have hOC := primeComplementCore_coprime (G := C) p
  set Pz : Subgroup G := (P' : Subgroup G) ⊓ C
  have hPzp : IsPGroup p Pz := P'.isPGroup'.to_le inf_le_left
  have hPzM : Pz ≤ M := inf_le_left.trans hP'M
  have hRPz : R ≤ Pz := le_inf hRP' hRz
  have hPz4 : 4 ≤ Open.pRank p Pz := by
    have h := hRC.four_le_pRank
    rw [hRC.sylow_eq, pRank_map_mk_eq_pRank_map_subtype hp _ hOC,
      Subgroup.subgroupOf_map_subtype] at h
    exact h
  have hlt : Nat.card R < Nat.card Pz :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hRPz fun h => by rw [h] at hR4; omega)
  have hOsub : (OC.map C.subtype).subgroupOf C = OC :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective OC
  have hOn : ((OC.map C.subtype).subgroupOf C).Normal := by
    rw [hOsub]
    infer_instance
  have hOcard : Nat.card (OC.map C.subtype) = Nat.card OC :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hOM : OC.map C.subtype ≤ M := by
    rintro _ ⟨o, ho, rfl⟩
    exact hext.mem_of_mem_primeCore hRz ho
  have hodd := odd_card_of_twoLocals_le hp hPzp inf_le_right hRC.centralizer_not_le
    (Subgroup.map_subtype_le _) hOn (hOcard ▸ hOC) hOM fun T hT hT1 hPT =>
      hext.le_of_card_lt hPzM hPzp (by omega) hlt ⟨T, hT1, hT, rfl⟩ hPT
  rwa [hOcard] at hodd

end Reduced

end CFSG.AGLEmbedding
