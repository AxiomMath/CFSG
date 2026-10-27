module

public import CFSG.ClassicalInvolution.Phan.Main
public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.GH74.L5U5.Ident

public section

namespace CFSG.GH74.L5U5

open CFSG.ClassicalInvolution.Phan CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits

section StandardPair

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem unitaryBlockStandardPair_of_blocks {θ : Su K p f 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {U V : Subgroup X}
    (hU : (B12 K p f).map θ = U) (hV : (B23 K p f).map θ = V) :
    UnitaryBlockStandardPair K p f θ.range U V := by
  have hc : ∀ H : Subgroup (Su K p f 3),
      H.map (MulAut.conj (1 : Su K p f 3)⁻¹).toMonoidHom = H := fun H => by
    rw [inv_one, map_one]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.one_apply, exists_eq_right]
  exact ⟨θ, 1, rfl, hker, Or.inl ⟨by rw [hc]; exact hU, by rw [hc]; exact hV⟩⟩

theorem unitaryBlockStandardPair_eq_sup (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    {W U V : Subgroup X} (h : UnitaryBlockStandardPair K p f W U V) : W = U ⊔ V := by
  obtain ⟨θ, hrange, -, h1, h2⟩ := pair_normalize h
  rw [← hrange, MonoidHom.range_eq_map, ← B12_sup_B23 hK hq, Subgroup.map_sup, h1, h2]

theorem unitaryBlockStandardPair_subgroupOf (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    {W U V : Subgroup X} (h : UnitaryBlockStandardPair K p f W U V) (N : Subgroup X) (hU : U ≤ N)
    (hV : V ≤ N) :
    UnitaryBlockStandardPair K p f (W.subgroupOf N) (U.subgroupOf N) (V.subgroupOf N) := by
  have hW : W ≤ N := (unitaryBlockStandardPair_eq_sup hK hq h) ▸ sup_le hU hV
  obtain ⟨θ, hrange, hker, h1, h2⟩ := pair_normalize h
  have hN : ∀ g, θ g ∈ N := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  have hrange' : (θ.codRestrict N hN).range = W.subgroupOf N := by
    rw [MonoidHom.range_eq_map, map_codRestrict_eq_subgroupOf, ← MonoidHom.range_eq_map, hrange]
  rw [← hrange']
  refine unitaryBlockStandardPair_of_blocks ?_ ?_ ?_
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · rw [map_codRestrict_eq_subgroupOf, h1]
  · rw [map_codRestrict_eq_subgroupOf, h2]

end StandardPair

section CenterQuotient

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

noncomputable def centerQuotientEquivStatedProjSu (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ}
    (hd : 3 ≤ d) (hdq : (d, p ^ f) ≠ (3, 2)) :
    Su K p f d ⧸ Subgroup.center (Su K p f d) ≃* StatedProj (StatedSU d (p ^ f) K) :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (SUid_eq_statedSU hK d))
      (map_center_mulEquiv _)).trans
    (QuotientGroup.quotientMulEquivOfEq (isQuasisimple_statedSU_of_card hK hd hdq).2)

theorem isQuasisimple_su (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ} (hd : 3 ≤ d)
    (hdq : (d, p ^ f) ≠ (3, 2)) : CFSG.IsQuasisimple (Su K p f d) :=
  isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hK d)).symm
    (isQuasisimple_statedSU_of_card hK hd hdq).1

end CenterQuotient

section Identification

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

theorem exists_surjection_iSup_unitary (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j)) :
    ∃ ψ : Su K p f (n + 1) →* G, ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center (Su K p f (n + 1)) ∧ CFSG.IsQuasisimple ↥(⨆ i, J i) ∧
      LieModel (↥(⨆ i, J i) ⧸ Subgroup.center ↥(⨆ i, J i)) StatedLieTag.PSU (n + 1) p f := by
  have hq2 : p ^ f ≠ 2 := by omega
  set N : Subgroup G := ⨆ i, J i with hN
  have hJN : ∀ i, J i ≤ N := fun i => le_iSup J i
  have hgen : ⨆ i, (J i).subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hJN _)]
    exact hN.symm
  have hstd : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W ((J i).subgroupOf N) ((J j).subgroupOf N) :=
    fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf N, unitaryBlockStandardPair_subgroupOf hK hq2 hW N (hJN i) (hJN j)⟩
  have hW : WeakPhanA K p f n (fun i => (J i).subgroupOf N)
      (fun i j => (J i).subgroupOf N ⊔ (J j).subgroupOf N) := by
    refine ⟨?_, fun _ _ _ => rfl, ?_, ?_, hgen⟩
    · intro i
      by_cases h : (i : ℕ) + 1 < n
      · obtain ⟨W, hW⟩ := hstd i ⟨i + 1, h⟩ rfl
        exact (nonempty_mulEquiv_of_standardPair hK hW).1
      · have hi : 0 < (i : ℕ) := by have := i.2; omega
        obtain ⟨W, hW⟩ := hstd ⟨(i : ℕ) - 1, by omega⟩ i (by simp only; omega)
        exact (nonempty_mulEquiv_of_standardPair hK hW).2
    · intro i j hij x hx y hy
      exact Subtype.ext (hcomm i j hij x hx y hy)
    · intro i j hj
      obtain ⟨W, hW⟩ := hstd i j hj
      rwa [unitaryBlockStandardPair_eq_sup hK hq2 hW] at hW
  obtain ⟨θ, hsurj, hker⟩ := weakPhan_recognition K p f hK hq hn hW
  have hdq : (n + 1, p ^ f) ≠ (3, 2) := fun h => by
    have : n + 1 = 3 := (Prod.mk.inj h).1
    omega
  have hquasi : CFSG.IsQuasisimple (Su K p f (n + 1)) := isQuasisimple_su hK (by omega) hdq
  have hnt : ∃ k, θ k ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcen : Subgroup.center (Su K p f (n + 1)) = ⊤ := by
      refine top_le_iff.mp fun x _ => hker ?_
      rw [MonoidHom.mem_ker]
      exact hall x
    obtain ⟨-, -, a, b, hab⟩ := hquasi
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Subgroup.center (Su K p f (n + 1)) := hcen ▸ Subgroup.mem_top x
    exact hab (congrArg QuotientGroup.mk (Subgroup.mem_center_iff.mp hx y).symm)
  have hqs : CFSG.IsQuasisimple ↥N :=
    isQuasisimple_of_surjective hquasi hsurj hnt
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by
    rw [h, pow_zero] at hq
    omega
  have hadm : StatedLieAdmissible .PSU (n + 1) p f := ⟨Fact.out, hf, by omega, hdq⟩
  refine ⟨N.subtype.comp θ, ?_, ?_, hqs, Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance,
    hK, ⟨((centralQuotientEquivOfIsQuasisimple hquasi hsurj hker).symm.trans
      (centerQuotientEquivStatedProjSu hK (by omega) hdq))⟩⟩⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective θ N.subtype N.subtype_injective]
    exact hker

theorem exists_surjection_A4_unitary (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j)) :
    ∃ ψ : Su K p f 5 →* G, ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center (Su K p f 5) ∧ CFSG.IsQuasisimple ↥(⨆ i, J i) ∧
      LieModel (↥(⨆ i, J i) ⧸ Subgroup.center ↥(⨆ i, J i)) StatedLieTag.PSU 5 p f :=
  exists_surjection_iSup_unitary K p f hK hq (n := 4) (by norm_num) J hcomm hpair

theorem exists_surjection_iSup_statedSU (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j)) :
    ∃ ψ : ↥(StatedSU (n + 1) (p ^ f) K) →* G, ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center ↥(StatedSU (n + 1) (p ^ f) K) ∧ CFSG.IsQuasisimple ↥(⨆ i, J i) ∧
      LieModel (↥(⨆ i, J i) ⧸ Subgroup.center ↥(⨆ i, J i)) StatedLieTag.PSU (n + 1) p f := by
  obtain ⟨ψ, hrange, hker, hqs, hmodel⟩ :=
    exists_surjection_iSup_unitary K p f hK hq hn J hcomm hpair
  let e : Su K p f (n + 1) ≃* ↥(StatedSU (n + 1) (p ^ f) K) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK (n + 1))
  refine ⟨ψ.comp e.symm.toMonoidHom, ?_, ?_, hqs, hmodel⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top,
      hrange]
  · intro x hx
    rw [← map_center_mulEquiv e]
    exact ⟨e.symm x, hker hx, e.apply_symm_apply x⟩

theorem exists_surjection_A4_statedSU (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j)) :
    ∃ ψ : ↥(StatedSU 5 (p ^ f) K) →* G, ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center ↥(StatedSU 5 (p ^ f) K) ∧ CFSG.IsQuasisimple ↥(⨆ i, J i) ∧
      LieModel (↥(⨆ i, J i) ⧸ Subgroup.center ↥(⨆ i, J i)) StatedLieTag.PSU 5 p f :=
  exists_surjection_iSup_statedSU K p f hK hq (n := 4) (by norm_num) J hcomm hpair

theorem lieModel_unitary_iSup_of_isSimpleGroup (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j))
    (hs : IsSimpleGroup ↥(⨆ i, J i)) :
    LieModel ↥(⨆ i, J i) StatedLieTag.PSU (n + 1) p f := by
  obtain ⟨-, -, -, hqs, hmodel⟩ := exists_surjection_iSup_unitary K p f hK hq hn J hcomm hpair
  have hZ := center_eq_bot_of_isQuasisimple_of_isSimpleGroup hqs hs
  exact lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel

theorem lieModel_A4_unitary_of_isSimpleGroup (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j))
    (hs : IsSimpleGroup ↥(⨆ i, J i)) :
    LieModel ↥(⨆ i, J i) StatedLieTag.PSU 5 p f :=
  lieModel_unitary_iSup_of_isSimpleGroup K p f hK hq (n := 4) (by norm_num) J hcomm hpair hs

theorem lieModel_unitary_of_iSup_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {G : Type} [Group G] (J : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j))
    (hgen : ⨆ i, J i = ⊤) (hs : IsSimpleGroup G) :
    LieModel G StatedLieTag.PSU (n + 1) p f := by
  let e : ↥(⨆ i, J i) ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  exact lieModel_of_mulEquiv e
    (lieModel_unitary_iSup_of_isSimpleGroup K p f hK hq hn J hcomm hpair
      ((MulEquiv.isSimpleGroup_congr e).mpr hs))

theorem lieModel_A4_unitary_of_iSup_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {G : Type} [Group G] (J : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 4, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j))
    (hgen : ⨆ i, J i = ⊤) (hs : IsSimpleGroup G) : LieModel G StatedLieTag.PSU 5 p f :=
  lieModel_unitary_of_iSup_eq_top K p f hK hq (n := 4) (by norm_num) J hcomm hpair hgen hs

end Identification

end CFSG.GH74.L5U5
