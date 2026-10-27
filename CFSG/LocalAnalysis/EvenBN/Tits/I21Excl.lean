module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl4

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

theorem order16_subgroupOf {G : Type} [Group G] {M L : Subgroup G} (hML : M ≤ L)
    (h : Sec622Order16 M) : Sec622Order16 (M.subgroupOf L) := by
  obtain ⟨hcard, ⟨a, ha, b, hb, hab⟩, c, hc, hc4, hcc⟩ := h
  refine ⟨?_, ⟨⟨a, hML ha⟩, ha, ⟨b, hML hb⟩, hb, fun h1 => hab (congrArg Subtype.val h1)⟩,
    ⟨c, hML hc⟩, hc, ?_, fun m hm => Subtype.ext (hcc m hm)⟩
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv
  · rw [Subgroup.orderOf_mk]
    exact hc4

theorem mem_closure_iff_subtype {G : Type} [Group G] {L : Subgroup G} (S : Set L) (x : L) :
    x ∈ closure S ↔ (x : G) ∈ closure (L.subtype '' S) := by
  rw [← MonoidHom.map_closure]
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

theorem exists_dihRel_of_prodDihedral {G : Type} [Group G] {M L : Subgroup G} (hML : M ≤ L)
    {n : ℕ} (hd : Sec622ProdDihedral M n) :
    ∃ c r s : L, DihRel c r s (n - 1) ∧ M.subgroupOf L = closure ({c, r, s} : Set L) := by
  obtain ⟨hn, c, r, s, hco, hro, hso, hsr, hcr, hcs, hMeq, hcn⟩ := hd
  have hmem : ∀ x ∈ ({c, r, s} : Set G), x ∈ M := fun x hx => hMeq ▸ Subgroup.subset_closure hx
  have hcL : c ∈ L := hML (hmem c (by simp))
  have hrL : r ∈ L := hML (hmem r (by simp))
  have hsL : s ∈ L := hML (hmem s (by simp))
  have hc2 : c ^ 2 = 1 := hco ▸ pow_orderOf_eq_one c
  have hs2 : s ^ 2 = 1 := hso ▸ pow_orderOf_eq_one s
  have himg3 : L.subtype '' ({⟨c, hcL⟩, ⟨r, hrL⟩, ⟨s, hsL⟩} : Set L) = {c, r, s} := by
    simp [Set.image_insert_eq]
  have himg2 : L.subtype '' ({⟨r, hrL⟩, ⟨s, hsL⟩} : Set L) = {r, s} := by
    simp [Set.image_insert_eq]
  refine ⟨⟨c, hcL⟩, ⟨r, hrL⟩, ⟨s, hsL⟩, ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Subtype.ext hc2
  · rw [Subgroup.orderOf_mk]
    exact hro
  · exact Subtype.ext hs2
  · exact Subtype.ext hsr
  · exact Subtype.ext hcr
  · exact Subtype.ext hcs
  · intro h1
    apply hcn
    have := (mem_closure_iff_subtype _ _).mp h1
    rwa [himg2] at this
  · ext x
    rw [Subgroup.mem_subgroupOf, mem_closure_iff_subtype, himg3, hMeq]

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem sec622_not_uniqueInv {L M : Subgroup G} [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hM : fusionIsSylowIn 2 M L)
    (hinv : ∃ e ∈ M, orderOf e = 2) (huniq : Sec622UniqueInv M) : False := by
  obtain ⟨P, hP⟩ := I21.Excl.exists_sylow hM
  obtain ⟨e, heM, he⟩ := hinv
  refine I21.Excl.uniqueInv_false hnonab P ⟨⟨e, hM.1 heM⟩, ?_, ?_⟩ ?_
  · rw [hP]; exact heM
  · rw [← Subgroup.orderOf_coe]; exact he
  · rw [hP]; exact I21.Excl.uniqueInv_subgroupOf huniq

theorem sec622_not_order16 {L M : Subgroup G} [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hM : fusionIsSylowIn 2 M L)
    (h16 : Sec622Order16 M) : False := by
  obtain ⟨P, hP⟩ := I21.Excl.exists_sylow hM
  refine I21.Excl.order16_false hnonab P ?_
  rw [hP]
  exact I21.Excl.order16_subgroupOf hM.1 h16

theorem sec622_not_centralInv {L M : Subgroup G} [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hM : fusionIsSylowIn 2 M L)
    (hc : Sec622CentralInv M) : False := by
  obtain ⟨P, hP⟩ := I21.Excl.exists_sylow hM
  refine I21.Excl.centralInv_false hnonab P ?_
  rw [hP]
  exact I21.Excl.centralInv_subgroupOf hM.1 hc

theorem sec622_not_prodDihedral {L M : Subgroup G} [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hM : fusionIsSylowIn 2 M L) {n : ℕ}
    (hd : Sec622ProdDihedral M n) : False := by
  obtain ⟨P, hP⟩ := I21.Excl.exists_sylow hM
  obtain ⟨c, r, s, h, hcl⟩ := I21.Excl.exists_dihRel_of_prodDihedral hM.1 hd
  exact I21.Excl.prodDihedral_false hnonab P h (hP.trans hcl)

end CFSG.LocalAnalysis.EvenBN.Tits
