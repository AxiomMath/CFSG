module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTbl
public import CFSG.GH74.Exceptional.LinearFourTwo
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTbl
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinL42Inputs
public import Certificates.Certificate4046
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public meta import Certificates.Certificate113
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A8

open Equiv CFSG.QuasithinUnique.Unc25G2.Tbl

theorem a8_facts :
    List.range 8 ∈ P0tabs ∧
    (∀ a ∈ P0tabs, ∀ b ∈ P0tabs, mulT a b ∈ P0tabs) ∧
    (∀ a ∈ P0tabs, invT 8 a ∈ P0tabs) ∧
    (∀ σ ∈ P0perm, Perm.sign σ = 1) ∧
    P0perm.toFinset.card = 64 ∧
    (∀ x ∈ allTabs, (∀ v ∈ V0, mulT x v = mulT v x) → x ∈ V0) ∧
    (∀ x ∈ allTabs, x ≠ List.range 8 → (∀ p ∈ P0tabs, mulT x p = mulT p x) → x = tbl t0) ∧
    ((∀ v ∈ V0, mulT (mulT (tbl g0) v) (invT 8 (tbl g0)) ∈ V0) ∧
      (∀ v ∈ V0, mulT (mulT (invT 8 (tbl g0)) v) (tbl g0) ∈ V0) ∧
      mulT (tbl g0) (tbl t0) ≠ mulT (tbl t0) (tbl g0)) ∧
    Perm.sign g0 = 1 :=
  Certificates.certificate4046

theorem P0_even : ∀ σ ∈ P0perm, Perm.sign σ = 1 := a8_facts.2.2.2.1
theorem P0_card : P0perm.toFinset.card = 64 := a8_facts.2.2.2.2.1
theorem V0_selfCentralizing : ∀ x ∈ allTabs, (∀ v ∈ V0, mulT x v = mulT v x) → x ∈ V0 :=
  a8_facts.2.2.2.2.2.1
theorem centralizer_P0 : ∀ x ∈ allTabs, x ≠ List.range 8 → (∀ p ∈ P0tabs, mulT x p = mulT p x) →
    x = tbl t0 := a8_facts.2.2.2.2.2.2.1
theorem g0_witness : (∀ v ∈ V0, mulT (mulT (tbl g0) v) (invT 8 (tbl g0)) ∈ V0) ∧
    (∀ v ∈ V0, mulT (mulT (invT 8 (tbl g0)) v) (tbl g0) ∈ V0) ∧
    mulT (tbl g0) (tbl t0) ≠ mulT (tbl t0) (tbl g0) := a8_facts.2.2.2.2.2.2.2.1
theorem g0_even : Perm.sign g0 = 1 := a8_facts.2.2.2.2.2.2.2.2

@[expose] def P0 : TabGroup 8 := ⟨P0perm, a8_facts.1, a8_facts.2.1, a8_facts.2.2.1⟩

abbrev A := alternatingGroup (Fin 8)

theorem card_A : Nat.card A = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem P0_le_alt : P0.sub ≤ alternatingGroup (Fin 8) := fun σ hσ =>
  Perm.mem_alternatingGroup.mpr (P0_even σ ((P0.mem_sub_iff_mem_elts).mp hσ))

@[expose] def Q0 : Subgroup A := P0.sub.comap (alternatingGroup (Fin 8)).subtype

theorem map_Q0 : Q0.map (alternatingGroup (Fin 8)).subtype = P0.sub := by
  rw [Q0, Subgroup.map_comap_eq, Subgroup.range_subtype]
  exact inf_eq_right.mpr P0_le_alt

theorem card_P0sub : Nat.card P0.sub = 64 := by
  have h : Nat.card P0.sub = Nat.card {σ : Perm (Fin 8) // σ ∈ P0perm.toFinset} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun σ => by
      rw [P0.mem_sub_iff_mem_elts]
      simp [P0]))
  rw [h, Nat.card_eq_fintype_card, Fintype.card_coe, P0_card]

theorem card_Q0 : Nat.card Q0 = 64 := by
  have h : Nat.card Q0 = Nat.card P0.sub :=
    Nat.card_congr ((Subgroup.equivMapOfInjective Q0 (alternatingGroup (Fin 8)).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr map_Q0)).toEquiv
  rw [h, card_P0sub]

theorem Q0_isPGroup : IsPGroup 2 Q0 := IsPGroup.of_card (n := 6) (by rw [card_Q0]; norm_num)

theorem Q0_index : ¬ 2 ∣ Q0.index := by
  have h := Subgroup.card_mul_index Q0
  rw [card_Q0, card_A] at h
  have : Q0.index = 315 := by omega
  rw [this]
  norm_num

theorem l42_X {X : Type*} [Group X] (φ : X ≃* A) {P : Subgroup X}
    (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) {t : X} (ht1 : t ≠ 1)
    (htP : ∀ x ∈ P, t * x = x * t) :
    (∀ x : X, (∀ v ∈ commCentralizer P, x * v = v * x) → x ∈ commCentralizer P) ∧
      ∃ g ∈ Subgroup.normalizer (commCentralizer P : Set X), g * t ≠ t * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPA2 : IsPGroup 2 (P.map φ.toMonoidHom) := hP2.map _
  have hPAi : ¬ 2 ∣ (P.map φ.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective φ.bijective]
    exact hPi
  obtain ⟨a, ha⟩ := exists_conj_map_eq hPA2 hPAi Q0_isPGroup Q0_index
  let ψ : X ≃* A := φ.trans (MulAut.conj a)
  have hψP : P.map ψ.toMonoidHom = Q0 := by
    have : P.map ψ.toMonoidHom = (P.map φ.toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [this, ha]
  let ι : X →* Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp ψ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp ψ.injective
  have hιP : P.map ι = P0.sub := by
    show P.map ((alternatingGroup (Fin 8)).subtype.comp ψ.toMonoidHom) = P0.sub
    rw [← Subgroup.map_map, hψP, map_Q0]
  refine ⟨fun x hx => ?_, ?_⟩
  · have hxt : tbl (ι x) ∈ V0 := by
      apply V0_selfCentralizing _ (tbl_mem_permutations _)
      intro v hv
      have hv' : v ∈ vTabs 8 P0.tabs := hv
      have hvP : v ∈ P0.tabs := (List.mem_filter.mp hv').1
      obtain ⟨σ, hσ, rfl⟩ := P0.real hvP
      have hσV : σ ∈ commCentralizer P0.sub := (mem_commCentralizer_sub P0 σ).mpr hv'
      rw [← hιP] at hσ hσV
      obtain ⟨u, hu, rfl⟩ := hσ
      have hu' : u ∈ commCentralizer P := (mem_commCentralizer_map_iff hι P u).mp hσV
      rw [← tbl_mul, ← tbl_mul, ← map_mul, ← map_mul, hx u hu']
    have hxV : ι x ∈ commCentralizer P0.sub := (mem_commCentralizer_sub P0 _).mpr hxt
    rw [← hιP] at hxV
    exact (mem_commCentralizer_map_iff hι P x).mp hxV
  · have hg0 : g0 ∈ alternatingGroup (Fin 8) := Perm.mem_alternatingGroup.mpr g0_even
    let g : X := ψ.symm ⟨g0, hg0⟩
    have hιg : ι g = g0 := by simp [ι, g]
    have hιt : ι t = t0 := by
      apply tbl_injective
      apply centralizer_P0 _ (tbl_mem_permutations _)
      · intro h
        apply ht1
        apply hι
        rw [map_one]
        apply tbl_injective
        rw [h, tbl_one]
      · intro p hp
        obtain ⟨σ, hσ, rfl⟩ := P0.real hp
        rw [← hιP] at hσ
        obtain ⟨u, hu, rfl⟩ := hσ
        rw [← tbl_mul, ← tbl_mul, ← map_mul, ← map_mul, htP u hu]
    refine ⟨g, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [← mem_commCentralizer_map_iff hι P h, ← mem_commCentralizer_map_iff hι P (g * h * g⁻¹),
        hιP, mem_commCentralizer_sub, mem_commCentralizer_sub]
      have e1 : tbl (ι (g * h * g⁻¹)) = mulT (mulT (tbl g0) (tbl (ι h))) (invT 8 (tbl g0)) := by
        rw [map_mul, map_mul, map_inv, hιg, tbl_mul, tbl_mul, tbl_inv]
      have e2 : tbl (ι h) = mulT (mulT (invT 8 (tbl g0)) (tbl (ι (g * h * g⁻¹)))) (tbl g0) := by
        have : ι h = g0⁻¹ * ι (g * h * g⁻¹) * g0 := by
          rw [map_mul, map_mul, map_inv, hιg]
          group
        rw [this, tbl_mul, tbl_mul, tbl_inv]
      constructor
      · intro hv
        rw [e1]
        exact g0_witness.1 _ hv
      · intro hv
        rw [e2]
        exact g0_witness.2.1 _ hv
    · intro hcomm
      have : ι g * ι t = ι t * ι g := by rw [← map_mul, ← map_mul, hcomm]
      rw [hιg, hιt] at this
      exact g0_witness.2.2 (by rw [← tbl_mul, ← tbl_mul, this])

end A8

end CFSG.QuasithinUnique.Unc25G2

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Unc25G2

theorem l42Excluded : L42Excluded := by
  intro G _ _ L S₀ ML z zL hmodel _hout hproj hML hMLne hS₀2 hS₀N hsyl hS₀ML hS₀z hall
  obtain ⟨φ⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
    (Or.inl ⟨by decide, hmodel⟩)
  let P : Subgroup ↥L := (S₀ ⊓ L).subgroupOf L
  have hP2 : IsPGroup 2 P := hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  have hPi : ¬ 2 ∣ P.index := hsyl.2.2
  obtain ⟨hzLL, hzproj⟩ := hproj
  let t : ↥L := ⟨zL, hzLL⟩
  have ht1 : t ≠ 1 := by
    intro h
    have hz : zL = 1 := congrArg Subtype.val h
    apply hMLne
    have hcen : Subgroup.centralizer ({zL} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy, hz]
      exact Subgroup.one_mem _
    rw [hML, hcen, inf_top_eq]
  have htP : ∀ x ∈ P, t * x = x * t := by
    intro x hx
    have hxS : (x : G) ∈ S₀ := (Subgroup.mem_subgroupOf.mp hx).1
    have h1 : (x : G) * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hS₀z hxS)
    have h2 := hzproj (x : G) x.2
    have h3 : z⁻¹ * (x : G) * z = x := by
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h3] at h2
    apply Subtype.ext
    show zL * (x : G) = x * zL
    calc zL * (x : G) = zL * (zL⁻¹ * x * zL) := by rw [← h2]
      _ = x * zL := by group
  obtain ⟨hC, g, hgN, hgt⟩ := A8.l42_X φ hP2 hPi ht1 htP
  have hVP : commCentralizer P ≤ P := commCentralizer_le P
  have hV2 : IsPGroup 2 (commCentralizer P) := hP2.to_le hVP
  have hPinv : ∀ s (hs : s ∈ S₀), P.map (conjAut L s (hS₀N hs)).toMonoidHom = P := by
    intro s hs
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyS : (y : G) ∈ S₀ := (Subgroup.mem_subgroupOf.mp hy).1
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, (conjAut L s (hS₀N hs) y).2⟩
      show s * (y : G) * s⁻¹ ∈ S₀
      exact S₀.mul_mem (S₀.mul_mem hs hyS) (S₀.inv_mem hs)
    · intro hx
      have hxS : (x : G) ∈ S₀ := (Subgroup.mem_subgroupOf.mp hx).1
      refine ⟨conjAut L s⁻¹ (hS₀N (S₀.inv_mem hs)) x, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr ⟨?_, (conjAut L s⁻¹ _ x).2⟩
        show s⁻¹ * (x : G) * s⁻¹⁻¹ ∈ S₀
        exact S₀.mul_mem (S₀.mul_mem (S₀.inv_mem hs) hxS) (by simpa using hs)
      · apply Subtype.ext
        show s * (s⁻¹ * (x : G) * s⁻¹⁻¹) * s⁻¹ = x
        group
  have hVinv : ∀ s (hs : s ∈ S₀),
      (commCentralizer P).map (conjAut L s (hS₀N hs)).toMonoidHom = commCentralizer P :=
    fun s hs => map_commCentralizer_eq_self _ (hPinv s hs)
  have hNinv : ∀ s (hs : s ∈ S₀), ∀ x : ↥L,
      x ∈ Subgroup.normalizer (commCentralizer P : Set ↥L) →
        conjAut L s (hS₀N hs) x ∈ Subgroup.normalizer (commCentralizer P : Set ↥L) := by
    intro s hs x hx
    have h1 := Subgroup.map_equiv_normalizer_eq (commCentralizer P) (conjAut L s (hS₀N hs))
    rw [hVinv s hs] at h1
    have h2 : conjAut L s (hS₀N hs) x ∈
        (Subgroup.normalizer (commCentralizer P : Set ↥L)).map
          (conjAut L s (hS₀N hs)).toMonoidHom := ⟨x, hx, rfl⟩
    rw [h1] at h2
    exact h2
  have hSK := le_normalizer_map_subtype hS₀N (Subgroup.normalizer (commCentralizer P : Set ↥L)) hNinv
  have hchar : CharTwo ((Subgroup.normalizer (commCentralizer P : Set ↥L)).map L.subtype) :=
    charTwo_map_subtype_of_normal_pGroup Subgroup.le_normalizer le_rfl hV2 (fun x _ hx => hC x hx)
  have hKML := hall _ (Subgroup.map_subtype_le _) hSK hchar
  have hgK : (g : G) ∈ (Subgroup.normalizer (commCentralizer P : Set ↥L)).map L.subtype :=
    ⟨g, hgN, rfl⟩
  have hgML := hKML hgK
  rw [hML] at hgML
  have hcomm : (g : G) * zL = zL * g := Subgroup.mem_centralizer_singleton_iff.mp hgML.2
  exact hgt (Subtype.ext hcomm)

end CFSG.QuasithinUnique
