module

public import CFSG.GH74.L5U5.IdentChain
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.GH74.L5U5

open CFSG.ClassicalInvolution.WeakCT CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section StandardPair

variable {K : Type} [Field K] {G : Type} [Group G]

theorem linearBlockStandardPair_of_blocks {θ : SL(3, K) →* G}
    (hker : θ.ker ≤ Subgroup.center SL(3, K)) {U V : Subgroup G} (hU : (B12 K).map θ = U)
    (hV : (B23 K).map θ = V) : LinearBlockStandardPair K θ.range U V := by
  have hc : ∀ H : Subgroup SL(3, K),
      H.map (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = H := fun H => by ext x; simp
  exact ⟨θ, 1, rfl, hker, Or.inl ⟨by rw [hc]; exact hU, by rw [hc]; exact hV⟩⟩

theorem linearBlockStandardPair_eq_sup {W U V : Subgroup G}
    (h : LinearBlockStandardPair K W U V) : W = U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hor⟩ := h
  have htop : (B12 K).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (B23 K).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, B12_sup_B23, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
  have hW : W = ((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_sup, htop]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem map_codRestrict_eq_subgroupOf {S : Type*} [Group S] (θ : S →* G) (N : Subgroup G)
    (hN : ∀ g, θ g ∈ N) (H : Subgroup S) :
    H.map (θ.codRestrict N hN) = (H.map θ).subgroupOf N := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    exact ⟨g, hg, Subtype.ext hgx⟩

theorem linearBlockStandardPair_subgroupOf {W U V : Subgroup G}
    (h : LinearBlockStandardPair K W U V) (N : Subgroup G) (hU : U ≤ N) (hV : V ≤ N) :
    LinearBlockStandardPair K (W.subgroupOf N) (U.subgroupOf N) (V.subgroupOf N) := by
  have hW : W ≤ N := (linearBlockStandardPair_eq_sup h) ▸ sup_le hU hV
  obtain ⟨θ, c, hrange, hker, hor⟩ := h
  have hN : ∀ g, θ g ∈ N := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict N hN, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, map_codRestrict_eq_subgroupOf, ← MonoidHom.range_eq_map, hrange]
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [map_codRestrict_eq_subgroupOf, map_codRestrict_eq_subgroupOf, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [map_codRestrict_eq_subgroupOf, map_codRestrict_eq_subgroupOf, h1, h2]
      exact ⟨rfl, rfl⟩

end StandardPair

section Identification

variable {K : Type} [Field K] [Finite K]

theorem exists_surjection_iSup (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 3 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j)) :
    ∃ ψ : SL(n + 1, K) →* G, ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧ CFSG.IsQuasisimple ↥(⨆ i, J i) ∧
      LieModel (↥(⨆ i, J i) ⧸ Subgroup.center ↥(⨆ i, J i)) StatedLieTag.PSL (n + 1) p f := by
  set N : Subgroup G := ⨆ i, J i with hN
  have hJN : ∀ i, J i ≤ N := fun i => le_iSup J i
  have hgen : ⨆ i, (J i).subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hJN _)]
    exact hN.symm
  obtain ⟨ψ', hsurj, hker, hqs, hmodel⟩ := weakCT_recognition_of_pairs_ge_three K p f hp hK hq hn
    (X := ↥N) (U := fun i => (J i).subgroupOf N)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x hx y hy))
    (fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf N, linearBlockStandardPair_subgroupOf hW N (hJN i) (hJN j)⟩)
    hgen
  refine ⟨N.subtype.comp ψ', ?_, ?_, hqs, hmodel⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective ψ' N.subtype N.subtype_injective]
    exact hker

theorem exists_surjection_A4 (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 3 ≤ p ^ f) {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j)) :
    ∃ ψ : SL(5, K) →* G, ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center SL(5, K) ∧ CFSG.IsQuasisimple ↥(⨆ i, J i) ∧
      LieModel (↥(⨆ i, J i) ⧸ Subgroup.center ↥(⨆ i, J i)) StatedLieTag.PSL 5 p f :=
  exists_surjection_iSup p f hp hK hq (n := 4) (by norm_num) J hcomm hpair

theorem center_eq_bot_of_isQuasisimple_of_isSimpleGroup {N : Type*} [Group N]
    (hq : CFSG.IsQuasisimple N) (hs : IsSimpleGroup N) : Subgroup.center N = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
  · exact h
  · exfalso
    have hperf : Group.IsPerfect N := hq.1
    have hcomm : IsMulCommutative N := ⟨⟨fun a b => by
      have hb : b ∈ Subgroup.center N := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a⟩⟩
    have : Subsingleton N := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact (not_subsingleton N) this

theorem lieModel_iSup_of_isSimpleGroup (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 3 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j))
    (hs : IsSimpleGroup ↥(⨆ i, J i)) :
    LieModel ↥(⨆ i, J i) StatedLieTag.PSL (n + 1) p f := by
  obtain ⟨-, -, -, hqs, hmodel⟩ := exists_surjection_iSup p f hp hK hq hn J hcomm hpair
  have hZ := center_eq_bot_of_isQuasisimple_of_isSimpleGroup hqs hs
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel

theorem lieModel_A4_of_isSimpleGroup (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 3 ≤ p ^ f) {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j))
    (hs : IsSimpleGroup ↥(⨆ i, J i)) :
    LieModel ↥(⨆ i, J i) StatedLieTag.PSL 5 p f :=
  lieModel_iSup_of_isSimpleGroup p f hp hK hq (n := 4) (by norm_num) J hcomm hpair hs

theorem lieModel_of_iSup_eq_top (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 3 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j))
    (hgen : ⨆ i, J i = ⊤) (hs : IsSimpleGroup G) : LieModel G StatedLieTag.PSL (n + 1) p f := by
  let e : ↥(⨆ i, J i) ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e
    (lieModel_iSup_of_isSimpleGroup p f hp hK hq hn J hcomm hpair
      ((MulEquiv.isSimpleGroup_congr e).mpr hs))

theorem lieModel_A4_of_iSup_eq_top (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 3 ≤ p ^ f) {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j))
    (hgen : ⨆ i, J i = ⊤) (hs : IsSimpleGroup G) : LieModel G StatedLieTag.PSL 5 p f :=
  lieModel_of_iSup_eq_top p f hp hK hq (n := 4) (by norm_num) J hcomm hpair hgen hs

end Identification

end CFSG.GH74.L5U5
