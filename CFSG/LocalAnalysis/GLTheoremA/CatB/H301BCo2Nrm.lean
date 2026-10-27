module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Six
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max
public import CFSG.Sporadic.Co2I301.SpecSix

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Nrm

open CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2I301
  CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.Sporadic.Co2Schreier hiding dP

private theorem wordVal_mem_of {M : Type*} [Group M] (H : Subgroup M) {g : List M}
    (hg : ∀ x ∈ g, x ∈ H) (w : List ℕ) : wordVal g w ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : g[i]? with
  | none => exact H.one_mem
  | some y => exact hg y (List.mem_of_getElem? h)

theorem le_locQ_of_normalized
    {T : Subgroup (Equiv.Perm (Fin 2300))} (hTC : T ≤ locC)
    (hT : IsPGroup 2 T) (h1 : k1P ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 2300))))
    (h2 : k2P ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 2300))))
    (h3 : dP ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 2300)))) : T ≤ locQ := by
  let φ : locC →* Equiv.Perm (Fin 63) := toPerm63.comp sixAction
  let TC : Subgroup locC := T.comap locC.subtype
  let S : Subgroup (Equiv.Perm (Fin 63)) := TC.map φ
  have hS2 : IsPGroup 2 S := hT.comap_subtype.map φ
  by_cases hS : S = ⊥
  · intro t ht
    have hmem : φ ⟨t, hTC ht⟩ ∈ S :=
      Subgroup.mem_map_of_mem φ (show (⟨t, hTC ht⟩ : locC) ∈ TC from ht)
    rw [hS, Subgroup.mem_bot] at hmem
    have h0 : sixAction ⟨t, hTC ht⟩ = 1 := toPerm63_injective (hmem.trans (map_one _).symm)
    have h4 : (⟨t, hTC ht⟩ : locC) ∈ locQ.subgroupOf locC := by
      rw [← sixAction_ker]
      exact MonoidHom.mem_ker.2 h0
    exact Subgroup.mem_subgroupOf.1 h4
  · exfalso
    obtain ⟨X, hXS, hX1, hX2, hXc⟩ := exists_central_involution hS2 hS
    have hnorm : ∀ c : locC, (c : Equiv.Perm (Fin 2300)) ∈
        Subgroup.normalizer (T : Set (Equiv.Perm (Fin 2300))) →
        φ c ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))) := fun c hc =>
      Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ
        (Subgroup.le_normalizer_comap locC.subtype hc))
    have hg := gens_mem_locC
    have n1 := hnorm ⟨k1P, hg.2.2.2.2.1⟩ h1
    have n2 := hnorm ⟨k2P, hg.2.2.2.2.2⟩ h2
    have n3 := hnorm ⟨dP, hg.1⟩ h3
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hXS
    obtain ⟨w, -, hw⟩ := six_facts ⟨k1P, hg.2.2.2.2.1⟩ ⟨k2P, hg.2.2.2.2.2⟩ ⟨dP, hg.1⟩ rfl rfl rfl
      (φ t) (Co2Six.toPerm63_sixAction_mem_closure t) hX2 hX1
    have hW := wordVal_mem_of (Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))))
      (g := [φ ⟨k1P, hg.2.2.2.2.1⟩, φ ⟨k2P, hg.2.2.2.2.2⟩, φ ⟨dP, hg.1⟩])
      (by
        intro y hy
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl | rfl
        exacts [n1, n2, n3]) w
    exact hw (hXc _ ((Subgroup.mem_normalizer_iff.1 hW _).1 hXS))

private theorem mem_locC_of_conj_mem
    {x : Equiv.Perm (Fin 2300)} (hx : x ∈ co2P) (h : ∀ q ∈ locQ, x * q * x⁻¹ ∈ locQ)
    (h' : ∀ q ∈ locQ, x⁻¹ * q * x ∈ locQ) : x ∈ locC := by
  have hz := locZ_mem_centerIn_Q
  have hc : x * locZ * x⁻¹ ∈ CFSG.centerIn locQ := by
    refine Subgroup.mem_inf.2 ⟨h _ (Subgroup.mem_inf.1 hz).1,
      Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 _ (h' q hq)
    calc q * (x * locZ * x⁻¹) = x * (x⁻¹ * q * x * locZ) * x⁻¹ := by group
      _ = x * (locZ * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]
      _ = x * locZ * x⁻¹ * q := by group
  have hne : x * locZ * x⁻¹ ≠ 1 := by
    intro h0
    apply locZ_ne_one
    calc locZ = x⁻¹ * (x * locZ * x⁻¹) * x := by group
      _ = 1 := by rw [h0]; group
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : CFSG.centerIn locQ)).1 card_centerIn_Q
  have e1 := huniq ⟨_, hc⟩ fun h0 => hne (congrArg Subtype.val h0)
  have e2 := huniq ⟨_, hz⟩ fun h0 => locZ_ne_one (congrArg Subtype.val h0)
  have heq : x * locZ * x⁻¹ = locZ := congrArg Subtype.val (e1.trans e2.symm)
  rw [locC_eq_centralizer]
  refine Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc x * locZ = x * locZ * x⁻¹ * x := by group
    _ = locZ * x := by rw [heq]

theorem exists_mem_locC_of_not_le_locQ
    {R : Subgroup (Equiv.Perm (Fin 2300))} (hRP : R ≤ co2P) (hR : IsPGroup 2 R)
    (hQR : locQ ≤ R) (hne : ¬ R ≤ locQ) : ∃ x, x ∈ R ∧ x ∈ locC ∧ x ∉ locQ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  set Q' : Subgroup R := locQ.subgroupOf R
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : R) ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  have hconj : ∀ u : R, u ∈ Subgroup.normalizer (Q' : Set R) → ∀ q ∈ locQ,
      (u : Equiv.Perm (Fin 2300)) * q * (u : Equiv.Perm (Fin 2300))⁻¹ ∈ locQ := by
    intro u hu q hq
    exact Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff.1 hu ⟨q, hQR hq⟩).1
      (Subgroup.mem_subgroupOf.2 hq))
  refine ⟨y, y.2, mem_locC_of_conj_mem (hRP y.2) (hconj y hyN) fun q hq => ?_,
    fun h => hyQ (Subgroup.mem_subgroupOf.2 h)⟩
  have h1 := hconj y⁻¹ (Subgroup.inv_mem _ hyN) q hq
  simpa only [InvMemClass.coe_inv, inv_inv] using h1

theorem eq_one_or_locZ_of_mem_zpowers
    {w : Equiv.Perm (Fin 2300)} (hw : w ∈ Subgroup.zpowers locZ) : w = 1 ∨ w = locZ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have ho : orderOf locZ = 2 := orderOf_eq_prime locZ_sq locZ_ne_one
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem exists_mem_locC_of_gt_locZ
    {R : Subgroup (Equiv.Perm (Fin 2300))} (hRP : R ≤ co2P) (hR : IsPGroup 2 R)
    (hlt : Subgroup.zpowers locZ < R) :
    ∃ x, x ∈ R ∧ x ∈ locC ∧ x ∉ Subgroup.zpowers locZ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  obtain ⟨r, hrR, hrZ⟩ := SetLike.exists_of_lt hlt
  have hzR : locZ ∈ R := hlt.le (Subgroup.mem_zpowers _)
  set Z' : Subgroup R := (Subgroup.zpowers locZ).subgroupOf R
  have hZ' : Z' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hrZ ?_
    have h1 : (⟨r, hrR⟩ : R) ∈ Z' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyZ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Z' hZ')
  have h2 : (y : Equiv.Perm (Fin 2300)) * locZ * (y : Equiv.Perm (Fin 2300))⁻¹ ∈
      Subgroup.zpowers locZ :=
    Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff.1 hyN ⟨locZ, hzR⟩).1
      (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _)))
  have h3 : (y : Equiv.Perm (Fin 2300)) * locZ * (y : Equiv.Perm (Fin 2300))⁻¹ = locZ := by
    rcases eq_one_or_locZ_of_mem_zpowers h2 with h | h
    · exact absurd (by simpa using h) locZ_ne_one
    · exact h
  refine ⟨y, y.2, ?_, fun h => hyZ (Subgroup.mem_subgroupOf.2 h)⟩
  rw [locC_eq_centralizer]
  refine Subgroup.mem_inf.2 ⟨hRP y.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc (y : Equiv.Perm (Fin 2300)) * locZ
      = (y : Equiv.Perm (Fin 2300)) * locZ * (y : Equiv.Perm (Fin 2300))⁻¹ * y := by group
    _ = locZ * y := by rw [h3]

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Nrm

end
