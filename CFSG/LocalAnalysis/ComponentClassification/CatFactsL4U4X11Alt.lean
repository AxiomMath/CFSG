module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11AltMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Ord
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB

public section

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup Equiv

theorem normal_of_alternatingGroup_le {n : ℕ} {H : Subgroup (Perm (Fin n))}
    (h : alternatingGroup (Fin n) ≤ H) : H.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hc : g * x * g⁻¹ * x⁻¹ ∈ H := by
    apply h
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [Perm.sign_mul, Perm.sign_inv, mul_comm (Perm.sign g), mul_assoc]
  have := H.mul_mem hc hx
  rwa [inv_mul_cancel_right] at this

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem KConf.not_alt (h : KConf G N) {n : ℕ} (hn : 7 ≤ n) :
    ¬ Nonempty (↥N ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  obtain ⟨hNn, hC, -, b, K, hb, hKN, hKb, hKc, hKm⟩ := h
  have : N.Normal := hNn
  have hm5 : 5 ≤ n := by omega
  have hm6 : n ≠ 6 := by omega
  set ι := CatFactsL4U4.AltCent.toPerm e hm5 hm6 with hι
  have hinj : Function.Injective ι := CatFactsL4U4.AltCent.toPerm_injective e hm5 hm6 hC
  have hrange : (ι.range).Normal := normal_of_alternatingGroup_le (by
    rw [← CatFactsL4U4.AltCent.map_N e hm5 hm6]
    exact map_le_range ι N)
  set β := ι b with hβdef
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hβ : ∀ x, β (β x) = x := fun x => by
    have : β * β = 1 := by rw [hβdef, ← map_mul, hbb, map_one]
    exact congrArg (fun f : Perm (Fin n) => f x) this
  have hψmem : ∀ x : ↥(centralizer ({b} : Set G)),
      ι x ∈ centralizer ({β} : Set (Perm (Fin n))) := fun x => by
    rw [mem_centralizer_singleton_iff, hβdef, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp x.2]
  set ψ : ↥(centralizer ({b} : Set G)) →* ↥(centralizer ({β} : Set (Perm (Fin n)))) :=
    (ι.comp (centralizer ({b} : Set G)).subtype).codRestrict _ hψmem with hψ
  have hψinj : Function.Injective ψ := fun x y hxy =>
    Subtype.ext (hinj (congrArg Subtype.val hxy))
  have hψrange : ψ.range = (ι.range).subgroupOf (centralizer ({β} : Set (Perm (Fin n)))) := by
    ext c
    rw [mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      have hxb : x ∈ centralizer ({b} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        apply hinj
        rw [map_mul, map_mul, hx, ← hβdef]
        exact mem_centralizer_singleton_iff.mp c.2
      exact ⟨⟨x, hxb⟩, Subtype.ext hx⟩
  have hWn : ψ.range.Normal := by
    rw [hψrange]
    exact normal_subgroupOf
  set K₀ := K.subgroupOf (centralizer ({b} : Set G)) with hK₀
  have hK₀s : K₀.IsSubnormal := hKc.choose_spec.2.1
  set L := K₀.map ψ with hLdef
  have hLW : L ≤ ψ.range := map_le_range ψ K₀
  have hLs : L.IsSubnormal := by
    refine IsSubnormal.trans hLW ?_ hWn.isSubnormal
    have h1 : (K₀.map ψ.rangeRestrict).IsSubnormal :=
      hK₀s.map ψ.rangeRestrict_surjective
    have h2 : K₀.map ψ.rangeRestrict = L.subgroupOf ψ.range := by
      ext ⟨c, hc⟩
      rw [mem_subgroupOf, mem_map, mem_map]
      constructor
      · rintro ⟨x, hx, hxc⟩
        exact ⟨x, hx, congrArg Subtype.val hxc⟩
      · rintro ⟨x, hx, hxc⟩
        exact ⟨x, hx, Subtype.ext hxc⟩
    rwa [← h2]
  let eL : ↥K ≃* ↥L := (subgroupOfEquivOfLe hKb).symm.trans (K₀.equivMapOfInjective ψ hψinj)
  let φ : ↥L →* ↥K ⧸ pPrimeCore 2 ↥K := (QuotientGroup.mk' _).comp eL.symm.toMonoidHom
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp eL.symm.surjective
  have hs : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 3 1
      (GH74.statedClassicalModel_of_lieModel (by norm_num) hKm)
  exact Sym.false_of_subnormal_centralizer hβ hLs φ hφ (card_of_lieModel_psp_four_three hKm)

end CFSG.ComponentClassification.GSThmB.X11
