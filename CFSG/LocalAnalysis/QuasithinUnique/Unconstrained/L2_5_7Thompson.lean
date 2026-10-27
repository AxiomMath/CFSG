module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Conf
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {n : ℕ} {K₁ K₂ V V' : Subgroup G} {s : G}

namespace L257

omit [Finite G] in
theorem conjugate_eq_cjSub {A : Subgroup G} {g : G} : CFSG.conjugate A g = cjSub g⁻¹ A := by
  ext x
  rw [BenderBranch.mem_conjugate_iff, mem_cjSub]
  simp

end L257

namespace Conf257

variable (c : Conf257 N n K₁ K₂ V V' s)

include c in
theorem S_le_normalizer_K : N.S ≤ Subgroup.normalizer (N.K : Set G) :=
  N.S_le_normalizer_K_of_K0_eq c.setup.K0_eq

include c in
theorem SC_eq : N.SC = N.S ⊓ Subgroup.centralizer (N.K : Set G) :=
  N.SC_eq_inf_of_K0_eq c.setup.K0_eq

include c in
theorem S_le_normalizer_SK : N.S ≤ Subgroup.normalizer (N.SK : Set G) :=
  B2F.le_normalizer_inf Subgroup.le_normalizer c.S_le_normalizer_K

include c in
theorem SK_le_K₁ : N.SK ≤ K₁ :=
  (le_inf (L257.SK_le_K N) Subgroup.le_normalizer).trans c.setup.pair.lt₁.le

include c in
theorem SK_le_K₂ : N.SK ≤ K₂ :=
  (le_inf (L257.SK_le_K N) Subgroup.le_normalizer).trans c.setup.pair.lt₂.le

include c in
theorem isSylow_K₁ : IsSylowTwoOf N.SK K₁ := by
  refine isSylowTwoOf_of_card_eq c.SK_le_K₁ N.SK_sylow.isPGroup ?_
  have h1 : twoPart K₁ ≤ twoPart N.K := twoPart_mono c.setup.pair.lt_K₁.le
  have h2 : Nat.card N.SK ≤ twoPart K₁ := card_le_twoPart c.SK_le_K₁ N.SK_sylow.isPGroup
  have h3 : Nat.card N.SK = twoPart N.K := N.SK_sylow.card_eq
  omega

include c in
theorem isSylow_K₂ : IsSylowTwoOf N.SK K₂ := by
  refine isSylowTwoOf_of_card_eq c.SK_le_K₂ N.SK_sylow.isPGroup ?_
  have h1 : twoPart K₂ ≤ twoPart N.K := twoPart_mono c.setup.pair.lt_K₂.le
  have h2 : Nat.card N.SK ≤ twoPart K₂ := card_le_twoPart c.SK_le_K₂ N.SK_sylow.isPGroup
  have h3 : Nat.card N.SK = twoPart N.K := N.SK_sylow.card_eq
  omega

include c in
theorem conjugate_V_eq : CFSG.conjugate V s = V' := by
  rw [c.setup.hV, c.setup.hV', ← c.setup.swap]
  unfold CFSG.conjugate
  exact (pCoreOf_map_equiv 2 (MulAut.conj s⁻¹) K₁).symm

include c in
theorem V'_elem : IsElemAbelian 2 V' := by
  rw [← c.conjugate_V_eq, L257.conjugate_eq_cjSub]
  exact isElemAbelian_cjSub c.geom.V_elem

include c in
theorem card_V'_eq : Nat.card V' = Nat.card V := by
  rw [← c.conjugate_V_eq, BenderBranch.card_conjugate]

include c in
theorem V_le_SK : V ≤ N.SK := by
  rw [c.setup.hV]
  exact c.isSylow_K₁.pCoreOf_le

include c in
theorem V'_le_SK : V' ≤ N.SK := by
  rw [c.setup.hV']
  exact c.isSylow_K₂.pCoreOf_le

include c in
theorem K₁_le_normalizer_V : K₁ ≤ Subgroup.normalizer (V : Set G) := by
  rw [c.setup.hV]
  exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K₁

include c in
theorem K₂_le_normalizer_V' : K₂ ≤ Subgroup.normalizer (V' : Set G) := by
  rw [c.setup.hV']
  exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K₂

include c in
theorem not_K₁_le_M : ¬ K₁ ≤ M := by
  intro h
  have h1 : K₁ ≤ M ⊓ N.K := le_inf h c.setup.pair.lt_K₁.le
  rw [c.setup.borel] at h1
  exact c.setup.pair.lt₁.not_ge h1

include c in
theorem V_le_K : V ≤ N.K := c.V_le_SK.trans (L257.SK_le_K N)

include c in
theorem V'_le_K : V' ≤ N.K := c.V'_le_SK.trans (L257.SK_le_K N)

include c in
theorem V_le_S : V ≤ N.S := c.V_le_SK.trans (L257.SK_le_S N)

include c in
theorem V'_le_S : V' ≤ N.S := c.V'_le_SK.trans (L257.SK_le_S N)

include c in
theorem V_comm_centralizer {v x : G} (hv : v ∈ V) (hx : x ∈ Subgroup.centralizer (N.K : Set G)) :
    v * x = x * v :=
  Subgroup.mem_centralizer_iff.mp hx v (c.V_le_K hv)

include c in
theorem center_le_V : centerOf N.K ≤ V := by
  have hZ2 : IsPGroup 2 (centerOf N.K) := B2F.isPGroup_of_isElemAbelian c.center_elem
  have hZK : centerOf N.K ≤ N.K := inf_le_left
  have hKZ : N.K ≤ Subgroup.normalizer (centerOf N.K : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun k hk y hy => ?_
    have h1 : k * y = y * k := Subgroup.mem_centralizer_iff.mp hy.2 k hk
    have h2 : k * y * k⁻¹ = y := by rw [h1]; group
    rw [h2]
    exact hy
  have hZS : centerOf N.K ≤ N.SK := N.SK_sylow.le_of_normalizes hZK hKZ hZ2
  have hZK₁ : centerOf N.K ≤ K₁ := hZS.trans c.SK_le_K₁
  have hnorm : ((centerOf N.K).subgroupOf K₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZK₁).mpr
      (c.setup.pair.lt_K₁.le.trans hKZ)
  rw [c.setup.hV]
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ K₁ hZK₁ hnorm hZ2

include c in
theorem center_le_V' : centerOf N.K ≤ V' := by
  have hZ2 : IsPGroup 2 (centerOf N.K) := B2F.isPGroup_of_isElemAbelian c.center_elem
  have hZK : centerOf N.K ≤ N.K := inf_le_left
  have hKZ : N.K ≤ Subgroup.normalizer (centerOf N.K : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun k hk y hy => ?_
    have h1 : k * y = y * k := Subgroup.mem_centralizer_iff.mp hy.2 k hk
    have h2 : k * y * k⁻¹ = y := by rw [h1]; group
    rw [h2]
    exact hy
  have hZS : centerOf N.K ≤ N.SK := N.SK_sylow.le_of_normalizes hZK hKZ hZ2
  have hZK₂ : centerOf N.K ≤ K₂ := hZS.trans c.SK_le_K₂
  have hnorm : ((centerOf N.K).subgroupOf K₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZK₂).mpr
      (c.setup.pair.lt_K₂.le.trans hKZ)
  rw [c.setup.hV']
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ K₂ hZK₂ hnorm hZ2

include c in
theorem V_inf_centralizer : V ⊓ Subgroup.centralizer (N.K : Set G) = centerOf N.K :=
  le_antisymm (le_inf (inf_le_left.trans c.V_le_K) inf_le_right)
    (le_inf c.center_le_V inf_le_right)

include c in
theorem SC_le_centralizer : N.SC ≤ Subgroup.centralizer (N.K : Set G) := by
  rw [c.SC_eq]
  exact inf_le_right

include c in
theorem SC_le_S : N.SC ≤ N.S := by
  rw [c.SC_eq]
  exact inf_le_left

include c in
theorem rad_elem {W : Subgroup G} (hW : W = V ∨ W = V') : IsElemAbelian 2 W := by
  rcases hW with rfl | rfl
  · exact c.geom.V_elem
  · exact c.V'_elem

include c in
theorem rad_le_S {W : Subgroup G} (hW : W = V ∨ W = V') : W ≤ N.S := by
  rcases hW with rfl | rfl
  · exact c.V_le_S
  · exact c.V'_le_S

include c in
theorem rad_le_K {W : Subgroup G} (hW : W = V ∨ W = V') : W ≤ N.K := by
  rcases hW with rfl | rfl
  · exact c.V_le_K
  · exact c.V'_le_K

include c in
theorem rad_comm {W : Subgroup G} (hW : W = V ∨ W = V') {v x : G} (hv : v ∈ W)
    (hx : x ∈ Subgroup.centralizer (N.K : Set G)) : v * x = x * v :=
  Subgroup.mem_centralizer_iff.mp hx v (c.rad_le_K hW hv)

include c in
theorem rad_center_le {W : Subgroup G} (hW : W = V ∨ W = V') : centerOf N.K ≤ W := by
  rcases hW with rfl | rfl
  · exact c.center_le_V
  · exact c.center_le_V'

include c in
theorem rad_inf {W : Subgroup G} (hW : W = V ∨ W = V') :
    W ⊓ Subgroup.centralizer (N.K : Set G) = centerOf N.K :=
  le_antisymm (le_inf (inf_le_left.trans (c.rad_le_K hW)) inf_le_right)
    (le_inf (c.rad_center_le hW) inf_le_right)

include c in
theorem rad_card {W : Subgroup G} (hW : W = V ∨ W = V') : Nat.card W = Nat.card V := by
  rcases hW with rfl | rfl
  · rfl
  · exact c.card_V'_eq

include c in
theorem center_le_of_max {E : Subgroup G} (hE : IsMaxElemAbelian N.SC E) :
    centerOf N.K ≤ E := by
  have hZ : IsElemAbelian 2 (centerOf N.K) := c.center_elem
  have hZSC : centerOf N.K ≤ N.SC := by
    rw [c.SC_eq]
    refine le_inf ?_ inf_le_right
    exact c.center_le_V.trans c.V_le_S
  have hcomm : ∀ a ∈ E, ∀ b ∈ centerOf N.K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (c.SC_le_centralizer (hE.1 ha)) b hb.1).symm
  have hsup : IsElemAbelian 2 (E ⊔ centerOf N.K) :=
    B2F.isElemAbelian_sup_of_commute hE.2.1 hZ hcomm
  have hcard : Nat.card ↥(E ⊔ centerOf N.K) ≤ Nat.card E :=
    hE.2.2 _ (sup_le hE.1 hZSC) hsup
  have heq : E = E ⊔ centerOf N.K := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [heq]
  exact le_sup_right

include c in
theorem card_sup_rad {W E : Subgroup G} (hW : W = V ∨ W = V') (hE : IsMaxElemAbelian N.SC E) :
    Nat.card ↥(W ⊔ E) * Nat.card ↥(centerOf N.K) = Nat.card W * Nat.card E := by
  have h := B2F.card_sup_mul_card_inf_of_commute (A := W) (B := E)
    (fun a ha b hb => c.rad_comm hW ha (c.SC_le_centralizer (hE.1 hb)))
  have hinf : W ⊓ E = centerOf N.K := by
    refine le_antisymm ?_ (le_inf (c.rad_center_le hW) (c.center_le_of_max hE))
    rw [← c.rad_inf hW]
    exact inf_le_inf_left _ (hE.1.trans c.SC_le_centralizer)
  rwa [hinf] at h

include c in
theorem eq_sup_of_le_sup {W A : Subgroup G} (hW : W = V ∨ W = V') (hA : IsMaxElemAbelian N.S A)
    (hle : A ≤ W ⊔ Subgroup.centralizer (N.K : Set G)) :
    A = W ⊔ (A ⊓ Subgroup.centralizer (N.K : Set G)) := by
  have hWC : ∀ w ∈ W, ∀ x ∈ Subgroup.centralizer (N.K : Set G), w * x = x * w :=
    fun w hw x hx => c.rad_comm hW hw hx
  have hcomm : ∀ w ∈ W, ∀ a ∈ A, w * a = a * w := by
    intro w hw a ha
    obtain ⟨w', hw', x, hx, rfl⟩ := mem_sup_of_commute hWC (hle ha)
    have h1 : w * w' = w' * w := B2F.isElemAbelian_comm (c.rad_elem hW) hw hw'
    have h2 : w * x = x * w := hWC w hw x hx
    calc w * (w' * x) = (w * w') * x := by group
      _ = (w' * w) * x := by rw [h1]
      _ = w' * (w * x) := by group
      _ = w' * (x * w) := by rw [h2]
      _ = w' * x * w := by group
  have hWA : IsElemAbelian 2 (W ⊔ A) :=
    B2F.isElemAbelian_sup_of_commute (c.rad_elem hW) hA.2.1 hcomm
  have hcard : Nat.card ↥(W ⊔ A) ≤ Nat.card A := hA.2.2 _ (sup_le (c.rad_le_S hW) hA.1) hWA
  have heq : A = W ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  have hWle : W ≤ A := by
    rw [heq]
    exact le_sup_left.trans (le_of_eq (by rw [← heq]))
  refine le_antisymm (fun a ha => ?_) (sup_le hWle inf_le_left)
  obtain ⟨w', hw', x, hx, rfl⟩ := mem_sup_of_commute hWC (hle ha)
  have hxA : x ∈ A := by
    have := A.mul_mem (A.inv_mem (hWle hw')) ha
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw') (Subgroup.mem_sup_right ⟨hxA, hx⟩)

include c in
theorem exists_of_isMaxElemAbelian {A : Subgroup G} (hA : IsMaxElemAbelian N.S A) :
    ∃ E : Subgroup G, IsMaxElemAbelian N.SC E ∧ (A = V ⊔ E ∨ A = V' ⊔ E) := by
  obtain ⟨E₀, hE₀⟩ := exists_isMaxElemAbelian N.SC
  have hAK : A ≤ Subgroup.normalizer (N.K : Set G) := hA.1.trans c.S_le_normalizer_K
  have hAP : A ≤ Subgroup.normalizer (N.SK : Set G) := hA.1.trans c.S_le_normalizer_SK
  obtain ⟨hb, heq⟩ := c.maxrank A hAK hAP hA.2.1
  have hVCg : V ⊓ Subgroup.centralizer (N.K : Set G) = centerOf N.K := c.V_inf_centralizer
  rw [hVCg] at hb heq
  have hVE₀ : IsElemAbelian 2 (V ⊔ E₀) :=
    B2F.isElemAbelian_sup_of_commute c.geom.V_elem hE₀.2.1
      (fun a ha b hb => c.rad_comm (Or.inl rfl) ha (c.SC_le_centralizer (hE₀.1 hb)))
  have h1 : Nat.card ↥(V ⊔ E₀) ≤ Nat.card A :=
    hA.2.2 _ (sup_le c.V_le_S (hE₀.1.trans c.SC_le_S)) hVE₀
  have hACg : A ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.SC := by
    rw [c.SC_eq]
    exact inf_le_inf_right _ hA.1
  have h2 : Nat.card ↥(A ⊓ Subgroup.centralizer (N.K : Set G)) ≤ Nat.card E₀ :=
    hE₀.2.2 _ hACg (B2F.isElemAbelian_mono inf_le_left hA.2.1)
  have hcard := c.card_sup_rad (Or.inl rfl) hE₀
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hchain : Nat.card E₀ * Nat.card V ≤ Nat.card A * Nat.card ↥(centerOf N.K) := by
    calc Nat.card E₀ * Nat.card V = Nat.card ↥(V ⊔ E₀) * Nat.card ↥(centerOf N.K) := by
          rw [hcard, mul_comm]
      _ ≤ Nat.card A * Nat.card ↥(centerOf N.K) := Nat.mul_le_mul_right _ h1
  have e2 : Nat.card ↥(A ⊓ Subgroup.centralizer (N.K : Set G)) * Nat.card V =
      Nat.card E₀ * Nat.card V :=
    le_antisymm (Nat.mul_le_mul_right _ h2) (hchain.trans hb)
  have e3 : Nat.card ↥(A ⊓ Subgroup.centralizer (N.K : Set G)) = Nat.card E₀ :=
    Nat.eq_of_mul_eq_mul_right hVpos e2
  have e1 : Nat.card A * Nat.card ↥(centerOf N.K) =
      Nat.card ↥(A ⊓ Subgroup.centralizer (N.K : Set G)) * Nat.card V :=
    le_antisymm hb (by rw [e2]; exact hchain)
  have hE : IsMaxElemAbelian N.SC (A ⊓ Subgroup.centralizer (N.K : Set G)) :=
    ⟨hACg, B2F.isElemAbelian_mono inf_le_left hA.2.1, fun B hB hBe => by
      rw [e3]
      exact hE₀.2.2 B hB hBe⟩
  rcases heq e1 with hle | hle
  · exact ⟨_, hE, Or.inl (c.eq_sup_of_le_sup (Or.inl rfl) hA hle)⟩
  · exact ⟨_, hE, Or.inr (c.eq_sup_of_le_sup (Or.inr rfl) hA hle)⟩

include c in
theorem isMaxElemAbelian_of_exists {W E : Subgroup G} (hW : W = V ∨ W = V')
    (hE : IsMaxElemAbelian N.SC E) : IsMaxElemAbelian N.S (W ⊔ E) := by
  refine ⟨sup_le (c.rad_le_S hW) (hE.1.trans c.SC_le_S),
    B2F.isElemAbelian_sup_of_commute (c.rad_elem hW) hE.2.1
      (fun a ha b hb => c.rad_comm hW ha (c.SC_le_centralizer (hE.1 hb))), fun B hBS hB => ?_⟩
  have hBK : B ≤ Subgroup.normalizer (N.K : Set G) := hBS.trans c.S_le_normalizer_K
  have hBP : B ≤ Subgroup.normalizer (N.SK : Set G) := hBS.trans c.S_le_normalizer_SK
  obtain ⟨hb, -⟩ := c.maxrank B hBK hBP hB
  have hVCg : V ⊓ Subgroup.centralizer (N.K : Set G) = centerOf N.K := c.V_inf_centralizer
  rw [hVCg] at hb
  have hBC : B ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.SC := by
    rw [c.SC_eq]
    exact inf_le_inf_right _ hBS
  have h2 : Nat.card ↥(B ⊓ Subgroup.centralizer (N.K : Set G)) ≤ Nat.card E :=
    hE.2.2 _ hBC (B2F.isElemAbelian_mono inf_le_left hB)
  have hcard := c.card_sup_rad hW hE
  rw [c.rad_card hW] at hcard
  have hZpos : 0 < Nat.card ↥(centerOf N.K) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hZpos
  calc Nat.card B * Nat.card ↥(centerOf N.K)
      ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (N.K : Set G)) * Nat.card V := hb
    _ ≤ Nat.card E * Nat.card V := Nat.mul_le_mul_right _ h2
    _ = Nat.card ↥(W ⊔ E) * Nat.card ↥(centerOf N.K) := by rw [hcard, mul_comm]

include c in
theorem V_le_thompsonJ : V ≤ thompsonJ N.S := by
  obtain ⟨E, hE⟩ := exists_isMaxElemAbelian N.SC
  exact le_sup_left.trans (le_iSup₂_of_le _ (c.isMaxElemAbelian_of_exists (Or.inl rfl) hE) le_rfl)

include c in
theorem V'_le_thompsonJ : V' ≤ thompsonJ N.S := by
  obtain ⟨E, hE⟩ := exists_isMaxElemAbelian N.SC
  exact le_sup_left.trans (le_iSup₂_of_le _ (c.isMaxElemAbelian_of_exists (Or.inr rfl) hE) le_rfl)

include c in
theorem thompsonJ_SC_le : thompsonJ N.SC ≤ thompsonJ N.S := by
  refine iSup₂_le fun E hE => ?_
  exact le_sup_right.trans (le_iSup₂_of_le _ (c.isMaxElemAbelian_of_exists (Or.inl rfl) hE) le_rfl)

include c in
theorem thompsonJ_eq : thompsonJ N.S = N.SK ⊔ thompsonJ N.SC := by
  refine le_antisymm (iSup₂_le fun A hA => ?_) ?_
  · obtain ⟨E, hE, rfl | rfl⟩ := c.exists_of_isMaxElemAbelian hA
    · exact sup_le (c.V_le_SK.trans le_sup_left) (le_sup_of_le_right (le_iSup₂_of_le E hE le_rfl))
    · exact sup_le (c.V'_le_SK.trans le_sup_left) (le_sup_of_le_right (le_iSup₂_of_le E hE le_rfl))
  · refine sup_le ?_ c.thompsonJ_SC_le
    rw [c.geom.P_eq]
    exact sup_le c.V_le_thompsonJ c.V'_le_thompsonJ

end Conf257

end CFSG.QuasithinUnique
