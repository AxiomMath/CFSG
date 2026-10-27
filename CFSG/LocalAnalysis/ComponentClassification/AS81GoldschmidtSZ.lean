module

public import CFSG.LocalAnalysis.ComponentClassification.AS81SZComponents
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools

namespace SZ

section Central

variable {H : Type} [Group H] [Finite H]

theorem normal_sup_oddCore_of_goldschmidt_mod (hGA : Asc76X.GoldschmidtTheoremA)
    {N₀ : Subgroup H} [N₀.Normal] (hN₀c : ∀ h : H, ∀ n ∈ N₀, h * n = n * h)
    (hN₀2 : IsPGroup 2 N₀) (S : Sylow 2 H) {Q : Subgroup H} (hQS : Q ≤ S) (hN₀Q : N₀ ≤ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ N₀)
    (hcl : ∀ x ∈ Q, ∀ h : H, h⁻¹ * x * h ∈ (S : Subgroup H) → h⁻¹ * x * h ∈ Q)
    (hnc : NoComponentMod N₀ Q) : (Q ⊔ CFSG.Assembly.oddCore H).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := N₀ with hNdef
  set π₀ := QuotientGroup.mk' N with hπ₀def
  have hπ₀ : Function.Surjective π₀ := QuotientGroup.mk'_surjective N
  have hker : π₀.ker = N := QuotientGroup.ker_mk' N
  have hNQ : N ≤ Q := hN₀Q
  have hNS : N ≤ S := hNQ.trans hQS
  let Sb : Sylow 2 (H ⧸ N) := S.mapSurjective hπ₀
  have hSb : (Sb : Subgroup (H ⧸ N)) = (S : Subgroup H).map π₀ := Sylow.coe_mapSurjective _ _
  set Qb : Subgroup (H ⧸ N) := Q.map π₀ with hQbdef
  have hQbS : Qb ≤ Sb := by
    rw [hSb]
    exact map_mono hQS
  have hQbab : IsMulCommutative Qb := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ₀def, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have := hQab _ (Q.inv_mem hb) _ (Q.inv_mem ha)
    simpa [mul_assoc] using this
  have hclb : ∀ a ∈ Qb, ∀ g : H ⧸ N, g⁻¹ * a * g ∈ (Sb : Subgroup (H ⧸ N)) →
      g⁻¹ * a * g ∈ Qb := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨h, rfl⟩ := hπ₀ g
    rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
    rw [hSb] at hg
    obtain ⟨s, hs, hse⟩ := hg
    have hmem : h⁻¹ * a * h ∈ (S : Subgroup H) := by
      have h1 : s⁻¹ * (h⁻¹ * a * h) ∈ N := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
      have h2 := (S : Subgroup H).mul_mem hs (hNS h1)
      simpa [mul_assoc] using h2
    exact ⟨_, hcl a ha h hmem, rfl⟩
  obtain ⟨ha, hb, -⟩ := hGA (H ⧸ N) Sb Qb hQbS hQbab hclb
  set M : Subgroup (H ⧸ N) := normalClosure (Qb : Set (H ⧸ N)) with hMdef
  have hnc' : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ := hnc
  rw [hnc', sup_bot_eq] at ha
  have hcl0 : closure {t : ↥M ⧸ goldschmidtOddCore ↥M |
      t ∈ (((Sb : Subgroup (H ⧸ N)).subgroupOf M).map
        (QuotientGroup.mk' (goldschmidtOddCore ↥M)) ⊓ goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M))
      ∧ t ^ 2 = 1} = ⊥ := by
    rw [closure_eq_bot_iff]
    rintro t ⟨ht, -⟩
    rw [hnc', inf_bot_eq] at ht
    exact ht
  rw [hcl0, sup_bot_eq, ha] at hb
  have hsup : Qb.subgroupOf M ⊔ goldschmidtOddCore ↥M = ⊤ := by
    have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (goldschmidtOddCore ↥M))) hb
    rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at h1
  have hQbM : Qb ≤ M := le_normalClosure
  set O' : Subgroup (H ⧸ N) := AS76b.oddCoreIn M with hO'def
  have hO'eq : O' = (goldschmidtOddCore ↥M).map M.subtype := rfl
  have hMeq : M = Qb ⊔ O' := by
    have h2 := congrArg (Subgroup.map M.subtype) hsup
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hQbM, ← hO'eq,
      ← MonoidHom.range_eq_map, range_subtype] at h2
    exact h2.symm
  have hMn : M.Normal := normalClosure_normal
  have hO'n : O'.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hMn]
    exact AS76b.normalizer_le_normalizer_oddCoreIn M
  set L : Subgroup H := O'.comap π₀ with hLdef
  have hLn : L.Normal := hO'n.comap π₀
  have hNL : N ≤ L := by
    rw [← hker]
    exact ker_le_comap π₀ O'
  have hmapL : L.map π₀ = O' := map_comap_eq_self_of_surjective hπ₀ O'
  have hrel : Odd (N.relIndex L) := by
    rw [← hker, relIndex_ker, hmapL]
    exact AS76b.odd_card_oddCoreIn M
  have hNc : N ≤ centralizer (L : Set H) := fun n hn =>
    mem_centralizer_iff.mpr fun h _ => hN₀c h n hn
  have hLeq := eq_sup_oddCoreIn_of_central hN₀2 hNL hNc hrel
  have hOL : AS76b.oddCoreIn L ≤ CFSG.Assembly.oddCore H := by
    refine le_sSup ⟨?_, AS76b.odd_card_oddCoreIn L⟩
    rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hLn]
    exact AS76b.normalizer_le_normalizer_oddCoreIn L
  have hcomapM : M.comap π₀ = Q ⊔ L := by
    rw [hMeq, ← hmapL, hQbdef, ← Subgroup.map_sup, comap_map_eq, hker,
      sup_eq_left.mpr (hNQ.trans le_sup_left)]
  have hQLn : (Q ⊔ L).Normal := hcomapM ▸ hMn.comap π₀
  have heq : Q ⊔ CFSG.Assembly.oddCore H = (Q ⊔ L) ⊔ CFSG.Assembly.oddCore H := by
    apply le_antisymm
    · exact sup_le_sup_right le_sup_left _
    · refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rw [hLeq]
      exact sup_le (hNQ.trans le_sup_left) (hOL.trans le_sup_right)
  rw [heq]
  have := hQLn
  infer_instance

end Central

section Centralizer

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_of_noComponentMod (hGA : Asc76X.GoldschmidtTheoremA)
    {Z S T : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hT : IsSylowOf 2 T (centralizer (Z : Set G))) (hST : S ≤ T) (hZS : Z ≤ S)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hcl : ∀ x ∈ S, ∀ h ∈ centralizer (Z : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ S)
    (hnc : NoComponentMod (Z.subgroupOf (centralizer (Z : Set G)))
      (S.subgroupOf (centralizer (Z : Set G)))) :
    centralizer (Z : Set G) ≤
      normalizer ((S ⊔ AS76b.oddCoreIn (centralizer (Z : Set G)) : Subgroup G) : Set G) := by
  set C := centralizer (Z : Set G) with hCdef
  obtain ⟨T₀, hT₀⟩ := hT
  have hTC : T ≤ C := hT₀ ▸ map_subtype_le _
  have hSC : S ≤ C := hST.trans hTC
  have hN₀c : ∀ h : ↥C, ∀ n ∈ Z.subgroupOf C, h * n = n * h := fun h n hn =>
    Subtype.ext (mem_centralizer_iff.mp h.2 n (mem_subgroupOf.mp hn)).symm
  have hN₀2 : IsPGroup 2 (Z.subgroupOf C) := fun n => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hZ.2 _ (mem_subgroupOf.mp n.2)⟩
  have hST' : S.subgroupOf C ≤ (T₀ : Subgroup C) := by
    intro x hx
    have hxS : (x : G) ∈ T := hST (mem_subgroupOf.mp hx)
    rw [← hT₀] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [← Subtype.ext hyx]
  have hZS' : Z.subgroupOf C ≤ S.subgroupOf C := fun x hx =>
    mem_subgroupOf.mpr (hZS (mem_subgroupOf.mp hx))
  have hSab' : ∀ x ∈ S.subgroupOf C, ∀ y ∈ S.subgroupOf C,
      x * y * x⁻¹ * y⁻¹ ∈ Z.subgroupOf C := fun x hx y hy => by
    rw [mem_subgroupOf]
    exact hSab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)
  have hcl' : ∀ x ∈ S.subgroupOf C, ∀ h : ↥C, h⁻¹ * x * h ∈ (T₀ : Subgroup C) →
      h⁻¹ * x * h ∈ S.subgroupOf C := fun x hx h hh => by
    rw [mem_subgroupOf]
    refine hcl _ (mem_subgroupOf.mp hx) _ h.2 ?_
    rw [← hT₀]
    exact ⟨_, hh, rfl⟩
  have key := normal_sup_oddCore_of_goldschmidt_mod hGA hN₀c hN₀2 T₀ hST' hZS' hSab' hcl' hnc
  have hmap : ((S.subgroupOf C) ⊔ CFSG.Assembly.oddCore ↥C).map C.subtype =
      S ⊔ AS76b.oddCoreIn C := by
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hSC]
    rfl
  rw [← hmap]
  exact AS76b.le_normalizer_map_subtype_of_normal C _

end Centralizer

end SZ

theorem goldschmidtSZ
    :
    ∀ (G : Type) [Group G] [Finite G] (Z S T N : Subgroup G),
      IsElemAbelian 2 Z → Nat.card Z = 4 →
      IsSylowOf 2 T (centralizer (Z : Set G)) → S ≤ T → Z ≤ S → Nat.card S = 2 ^ 14 →
      (∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z) → (∀ x ∈ S, x * x ∈ Z) →
      (∀ x ∈ S, ∀ h ∈ centralizer (Z : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ S) →
      N ≤ centralizer (Z : Set G) → N ≤ normalizer (S : Set G) →
      (∀ B : Subgroup G, Z ≤ B → B < S → N ≤ normalizer (B : Set G) → ∀ n : ℕ,
        ∃ k ∈ (derivedSeries N n).map N.subtype, ∃ x ∈ S, k⁻¹ * x * k * x⁻¹ ∉ B) →
      (∀ φ : ↥N →* Equiv.Perm (Fin 6), ∃ n : ℕ, derivedSeries ↥N n ≤ φ.ker) →
      centralizer (Z : Set G) ≤
        normalizer ((S ⊔ AS76b.oddCoreIn (centralizer (Z : Set G)) : Subgroup G) : Set G) := by
  intro G _ _ Z S T N hZ hZ4 hT hST hZS hS14 hSab _ hcl hNC hNS hN hperm
  exact SZ.centralizer_le_normalizer_of_noComponentMod Asc76X.goldschmidtTheoremA hZ hT hST hZS
    hSab hcl (SZ.noComponentMod_of_action hZ hZ4 hT hST hZS hS14 hSab hcl hNC hNS hN hperm)

end CFSG.ComponentClassification.AS81
