module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveAbstract
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def Star5Data (x y : G) : Prop :=
  ∀ V : Subgroup G, (∀ v ∈ V, ¬ 5 ∣ orderOf v) → V ≤ Subgroup.centralizer {x} →
    y ∈ Subgroup.normalizer (V : Set G) → V = ⊥

theorem Star5Data.map {H : Type*} [Group H] {x y : G} (hS : Star5Data x y) (φ : G ≃* H) :
    Star5Data (φ x) (φ y) := by
  intro V hV hVx hVy
  have h := hS (V.comap φ.toMonoidHom) ?_ ?_ ?_
  · rw [eq_bot_iff] at h ⊢
    intro v hv
    have h1 : φ.symm v ∈ V.comap φ.toMonoidHom := by simpa using hv
    have h2 := h h1
    rw [Subgroup.mem_bot] at h2 ⊢
    simpa using congrArg φ h2
  · intro v hv
    have := hV (φ v) hv
    rwa [MulEquiv.orderOf_eq] at this
  · intro v hv
    have := hVx hv
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    exact φ.injective (by simpa using this)
  · refine Subgroup.mem_normalizer_iff.2 fun v => ?_
    have := Subgroup.mem_normalizer_iff.1 hVy (φ v)
    simpa using this

theorem not_five_dvd_orderOf {U : Subgroup G} (hU : ¬ 5 ∣ Nat.card U) {u : G} (hu : u ∈ U) :
    ¬ 5 ∣ orderOf u := fun h =>
  hU (h.trans (by rw [← Subgroup.orderOf_mk u hu]; exact orderOf_dvd_natCard _))

theorem coprime_core {G : Type} [Group G] [Finite G] {x y : G} (hD : PlaneData x y)
    (hN : NormData x y) (hS : Star5Data x y) (U : Subgroup G) (hU : ¬ 5 ∣ Nat.card U)
    (hSU : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  obtain ⟨hab, hcard, hmem⟩ := hD.closure_facts
  have hgen := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers (p := 5) (by norm_num) hab hcard
    hSU hU
  have hxy : x * y = y * x := hD.comm
  have hxy' : y⁻¹ * x = x * y⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hxy]
      _ = x * y⁻¹ := by group
  have hb : ∀ b : {s : Subgroup.closure ({x, y} : Set G) // s ≠ 1},
      U ⊓ Subgroup.centralizer {(b.val : G)} = ⊥ := by
    rintro ⟨⟨b, hbS⟩, hb1⟩
    obtain ⟨v, hv⟩ := hmem b hbS
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hb1 (Subtype.ext (by simpa [planeMap] using hv))
    obtain ⟨n, hn, hnx⟩ := hN v hv0
    rw [← hv] at hnx
    have hy : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
    have hs : n * y * n⁻¹ ∈ Subgroup.closure ({x, y} : Set G) :=
      (Subgroup.mem_normalizer_iff.1 hn y).1 hy
    have hsU := Subgroup.mem_normalizer_iff.1 (hSU hs)
    have hV := hS ((U.comap (MulAut.conj n).toMonoidHom) ⊓ Subgroup.centralizer {x}) ?_
      inf_le_right ?_
    · rw [eq_bot_iff]
      intro u hu
      obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
      have hub : u * b = b * u := Subgroup.mem_centralizer_singleton_iff.1 hu2
      have hu' : n⁻¹ * u * n ∈
          (U.comap (MulAut.conj n).toMonoidHom) ⊓ Subgroup.centralizer {x} := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · simpa [MulAut.conj_apply, mul_assoc] using hu1
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have : x = n⁻¹ * b * n := by rw [← hnx]; group
          rw [this]
          calc n⁻¹ * u * n * (n⁻¹ * b * n) = n⁻¹ * (u * b) * n := by group
            _ = n⁻¹ * (b * u) * n := by rw [hub]
            _ = n⁻¹ * b * n * (n⁻¹ * u * n) := by group
      rw [hV, Subgroup.mem_bot] at hu'
      rw [Subgroup.mem_bot]
      calc u = n * (n⁻¹ * u * n) * n⁻¹ := by group
        _ = 1 := by rw [hu']; group
    ·
      intro v hv
      obtain ⟨hv1, -⟩ := Subgroup.mem_inf.1 hv
      have h1 : MulAut.conj n v ∈ U := hv1
      have := not_five_dvd_orderOf hU h1
      rwa [MulEquiv.orderOf_eq] at this
    ·
      refine Subgroup.mem_normalizer_iff.2 fun g => ?_
      have hconj : n * (y * g * y⁻¹) * n⁻¹ =
          n * y * n⁻¹ * (n * g * n⁻¹) * (n * y * n⁻¹)⁻¹ := by group
      constructor
      · intro hg
        obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · show n * (y * g * y⁻¹) * n⁻¹ ∈ U
          rw [hconj]
          exact (hsU (n * g * n⁻¹)).1 (by simpa [MulAut.conj_apply] using hg1)
        · rw [Subgroup.mem_centralizer_singleton_iff] at hg2 ⊢
          calc y * g * y⁻¹ * x = y * g * (y⁻¹ * x) := by group
            _ = y * g * (x * y⁻¹) := by rw [hxy']
            _ = y * (g * x) * y⁻¹ := by group
            _ = y * (x * g) * y⁻¹ := by rw [hg2]
            _ = (y * x) * g * y⁻¹ := by group
            _ = (x * y) * g * y⁻¹ := by rw [hxy]
            _ = x * (y * g * y⁻¹) := by group
      · intro hg
        obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h : n * (y * g * y⁻¹) * n⁻¹ ∈ U := hg1
          rw [hconj] at h
          simpa [MulAut.conj_apply] using (hsU (n * g * n⁻¹)).2 h
        · rw [Subgroup.mem_centralizer_singleton_iff] at hg2 ⊢
          calc g * x = y⁻¹ * (y * g * y⁻¹) * (y * x) := by group
            _ = y⁻¹ * (y * g * y⁻¹) * (x * y) := by rw [hxy]
            _ = y⁻¹ * ((y * g * y⁻¹) * x) * y := by group
            _ = y⁻¹ * (x * (y * g * y⁻¹)) * y := by rw [hg2]
            _ = (y⁻¹ * x * y) * g := by group
            _ = x * g := by rw [hxy', inv_mul_cancel_right]
  refine eq_bot_iff.2 (hgen.trans (iSup_le fun b => (hb b).le))

theorem glbCore_map_le {K L : Type*} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (k : ℕ) (φ : K ≃* L) (P : Subgroup K) :
    (GLBCore p k P).map φ.toMonoidHom ≤ GLBCore p k (P.map φ.toMonoidHom) := by
  unfold GLBCore
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hQk, rfl⟩
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
  exact le_sSup ⟨Q.map φ.toMonoidHom, Subgroup.map_mono hQP,
    hQk.trans (CFSG.SectionRank.pRank_le_map hp.one_lt φ.toMonoidHom φ.injective Q), rfl⟩

theorem normalizer_le_glbCore' [Finite G] {k : ℕ} {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQk : k ≤ pRank 5 Q) : Subgroup.normalizer (Q : Set G) ≤ GLBCore 5 k P :=
  le_sSup ⟨Q, hQP, hQk, rfl⟩

theorem PlaneData.x_ne_one {x y : G} (hD : PlaneData x y) : x ≠ 1 := by
  intro h
  refine hD.ne (Pi.single 0 1) (fun h0 => ?_) ?_
  · have : (Pi.single 0 1 : Fin 2 → ZMod 5) 0 = (0 : Fin 2 → ZMod 5) 0 := congrFun h0 0
    revert this
    decide
  · simp [h]

theorem PlaneData.normalizer_zpowers_le [Finite G] {x y : G} (hD : PlaneData x y) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤
      GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) := by
  have hx1 := hD.x_ne_one
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf x = 5 := orderOf_eq_prime hD.x_pow hx1
  refine normalizer_le_glbCore' (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) ?_
  have hel : IsElemAbelian 5 (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun z hz => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hD.x_pow, one_zpow]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl hel (by rw [Nat.card_zpowers, hord, pow_one])

theorem PlaneData.normalizer_le [Finite G] {x y : G} (hD : PlaneData x y) :
    Subgroup.normalizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) ≤
      GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) := by
  obtain ⟨hab, hcard, -⟩ := hD.closure_facts
  exact normalizer_le_glbCore' le_rfl
    (le_trans (by norm_num) (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hab hcard))

structure CoreFacts {G : Type} [Group G] [Finite G] (x y : G) (M : Subgroup G) : Prop where
  plane : PlaneData x y
  norm : NormData x y
  star : Star5Data x y
  max : ∀ Y : Subgroup G, M ≤ Y → Y = M ∨ Y = ⊤
  le : M ≤ GLBCore 5 1 (Subgroup.closure ({x, y} : Set G))

theorem CoreFacts.map {G H : Type} [Group G] [Group H] [Finite G] [Finite H] {x y : G}
    {M : Subgroup G} (h : CoreFacts x y M) (φ : G ≃* H) :
    CoreFacts (φ x) (φ y) (M.map φ.toMonoidHom) where
  plane := h.plane.map φ
  norm := h.norm.map φ
  star := h.star.map φ
  max Y hY := by
    have h1 : M ≤ Y.comap φ.toMonoidHom := Subgroup.map_le_iff_le_comap.1 hY
    have hsurj : Function.Surjective φ.toMonoidHom := φ.surjective
    rcases h.max _ h1 with h2 | h2
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Y, h2]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Y, h2]
      exact Subgroup.map_top_of_surjective _ hsurj
  le := by
    refine (Subgroup.map_mono h.le).trans ?_
    refine (glbCore_map_le (by norm_num) 1 φ _).trans ?_
    rw [← closure_pair_map x y φ]

theorem CoreFacts.uPrime {G : Type} [Group G] [Finite G] {x y : G} {M : Subgroup G}
    (h : CoreFacts x y M)
    (hT : GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) ≠ ⊤) :
    (∀ Y : Subgroup G, GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) ≤ Y →
        Y = GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) ∨ Y = ⊤) ∧
      ∀ N : Subgroup G, N ≤ GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) →
        (N.subgroupOf (GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)))).Normal →
          Nat.Coprime 5 (Nat.card N) → N = ⊥ := by
  set Γ := GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) with hΓ
  have hΓM : Γ = M := by
    rcases h.max Γ h.le with h1 | h1
    · exact h1
    · exact absurd h1 hT
  refine ⟨fun Y hY => ?_, fun N hNΓ hNn hcop => ?_⟩
  · rw [hΓM] at hY ⊢
    exact h.max Y hY
  · have hTΓ : Subgroup.closure ({x, y} : Set G) ≤ Γ :=
      (Subgroup.le_normalizer).trans h.plane.normalizer_le
    have hTN : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.normalizer (N : Set G) := by
      intro t ht
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      have hnΓ : n ∈ Γ := hNΓ hn
      have hmem : (⟨n, hnΓ⟩ : Γ) ∈ N.subgroupOf Γ := hn
      have := hNn.conj_mem _ hmem ⟨t, hTΓ ht⟩
      exact this
    exact coprime_core h.plane h.norm h.star N
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 hcop) hTN

structure CoreData (G : Type) [Group G] [Finite G] : Prop where
  out : ∃ (x y : G) (m : ℕ) (M : Subgroup G), CoreFacts x y M ∧ Nat.card G = 5 ^ 2 * m ∧ ¬ 5 ∣ m

theorem CoreData.of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (hG : CoreData G) (φ : G ≃* H) : CoreData H := by
  obtain ⟨x, y, m, M, hF, hm, hm5⟩ := hG.out
  exact ⟨⟨φ x, φ y, m, M.map φ.toMonoidHom, hF.map φ,
    by rw [← hm]; exact Nat.card_congr φ.toEquiv.symm, hm5⟩⟩

theorem CoreData.uPrime {G : Type} [Group G] [Finite G] (hG : CoreData G) (T : Sylow 5 G)
    (hT : GLBCore 5 1 (T : Subgroup G) ≠ ⊤) :
    (∀ Y : Subgroup G, GLBCore 5 1 (T : Subgroup G) ≤ Y →
        Y = GLBCore 5 1 (T : Subgroup G) ∨ Y = ⊤) ∧
      ∀ N : Subgroup G, N ≤ GLBCore 5 1 (T : Subgroup G) →
        (N.subgroupOf (GLBCore 5 1 (T : Subgroup G))).Normal → Nat.Coprime 5 (Nat.card N) →
          N = ⊥ := by
  obtain ⟨x, y, m, M, hF, hm, hm5⟩ := hG.out
  obtain ⟨g, hg⟩ := hF.plane.exists_conj_closure hm hm5 T
  have h1 : g * x * g⁻¹ = MulAut.conj g x := rfl
  have h2 : g * y * g⁻¹ = MulAut.conj g y := rfl
  rw [h1, h2] at hg
  rw [← hg] at hT ⊢
  exact (hF.map (MulAut.conj g)).uPrime hT

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
