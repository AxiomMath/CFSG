module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBackSpin
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltNoHe
open scoped commutatorElement

section Image

variable {X : Type} [Group X] [Finite X]

@[expose] def tildeHom (X : Type) [Group X] :
    X →* (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X) :=
  (QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X))).comp (QuotientGroup.mk' (pPrimeCore 2 X))

omit [Finite X] in
theorem tildeHom_surjective : Function.Surjective (tildeHom X) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

omit [Finite X] in
theorem tildeHom_eq_one_iff (x : X) :
    tildeHom X x = 1 ↔ (QuotientGroup.mk x : X ⧸ pPrimeCore 2 X) ∈ center (X ⧸ pPrimeCore 2 X) :=
  QuotientGroup.eq_one_iff _

theorem isSubnormal_map_tilde {t : X} (htt : t * t = 1) {J : Subgroup X}
    (hJt : J ≤ centralizer {t}) (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal) :
    J.map (tildeHom X) ≤ centralizer {tildeHom X t} ∧
      ((J.map (tildeHom X)).subgroupOf (centralizer {tildeHom X t})).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 X) with hρ
  set σ := QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X)) with hσ
  set π := tildeHom X with hπ
  have hπ' : π = σ.comp ρ := rfl
  let C := centralizer ({t} : Set X)
  let Ct := centralizer ({π t} : Set ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)))
  have hC0 : C.map π ≤ Ct := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    change π c ∈ centralizer ({π t} : Set _)
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
  have hCρ : C.map ρ = centralizer {ρ t} :=
    UnbalancedLayer.map_centralizer_eq (odd_card_pPrimeCore_two X) htt
  have hC0n : ((C.map π).subgroupOf Ct).Normal := by
    rw [normal_subgroupOf_iff hC0]
    rintro _ b ⟨c, hc, rfl⟩ hb
    obtain ⟨y, rfl⟩ := tildeHom_surjective b
    have hb' : π y * π t = π t * π y := mem_centralizer_singleton_iff.mp hb
    have hn : (ρ y * ρ t)⁻¹ * (ρ t * ρ y) ∈ center (X ⧸ pPrimeCore 2 X) := by
      have h1 : σ (ρ y * ρ t) = σ (ρ t * ρ y) := by
        simpa only [hπ', MonoidHom.comp_apply, map_mul] using hb'
      exact QuotientGroup.eq.mp h1
    set n := (ρ y * ρ t)⁻¹ * (ρ t * ρ y) with hndef
    have hnc : ∀ g, g * n = n * g := fun g => mem_center_iff.mp hn g
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    have hct : ρ c * ρ t = ρ t * ρ c := by
      rw [← map_mul, ← map_mul, hc']
    have hty : ρ t * ρ y = ρ y * ρ t * n := by rw [hndef]; group
    have hyt : (ρ y)⁻¹ * ρ t = ρ t * n * (ρ y)⁻¹ := by
      calc (ρ y)⁻¹ * ρ t = (ρ y)⁻¹ * (ρ t * ρ y) * (ρ y)⁻¹ := by group
        _ = (ρ y)⁻¹ * (ρ y * ρ t * n) * (ρ y)⁻¹ := by rw [hty]
        _ = ρ t * n * (ρ y)⁻¹ := by group
    have hd : ρ y * ρ c * (ρ y)⁻¹ ∈ centralizer {ρ t} := by
      rw [mem_centralizer_singleton_iff]
      calc ρ y * ρ c * (ρ y)⁻¹ * ρ t = ρ y * ρ c * ((ρ y)⁻¹ * ρ t) := by group
        _ = ρ y * ρ c * (ρ t * n * (ρ y)⁻¹) := by rw [hyt]
        _ = ρ y * (ρ c * ρ t) * n * (ρ y)⁻¹ := by group
        _ = ρ y * (ρ t * ρ c) * n * (ρ y)⁻¹ := by rw [hct]
        _ = ρ y * ρ t * (ρ c * n) * (ρ y)⁻¹ := by group
        _ = ρ y * ρ t * n * ρ c * (ρ y)⁻¹ := by rw [hnc (ρ c)]; group
        _ = ρ t * ρ y * ρ c * (ρ y)⁻¹ := by rw [← hty]
        _ = ρ t * (ρ y * ρ c * (ρ y)⁻¹) := by group
    rw [← hCρ] at hd
    obtain ⟨c', hc', hc'eq⟩ := hd
    refine ⟨c', hc', ?_⟩
    change σ (ρ c') = π y * π c * (π y)⁻¹
    rw [show ρ c' = ρ y * ρ c * (ρ y)⁻¹ from hc'eq]
    simp only [hπ', MonoidHom.comp_apply, map_mul, map_inv]
  let γ : ↥C →* ↥Ct := (π.comp C.subtype).codRestrict Ct (fun c => hC0 (mem_map_of_mem π c.2))
  have hγr : γ.range = (C.map π).subgroupOf Ct := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, hcy⟩
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hγn : γ.range.Normal := by rw [hγr]; exact hC0n
  have hJle : J.map π ≤ Ct := (map_mono hJt).trans hC0
  refine ⟨hJle, ?_⟩
  have h1 := isSubnormal_map_of_range_normal γ hγn hJs
  convert h1 using 1
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hJt hx⟩, hx, rfl⟩
  · rintro ⟨c, hc, hcy⟩
    exact ⟨c, hc, congrArg Subtype.val hcy⟩

theorem isSubnormal_map_bar {t : X} (htt : t * t = 1) {J : Subgroup X}
    (hJt : J ≤ centralizer {t}) (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal)
    (hc : (QuotientGroup.mk t : X ⧸ pPrimeCore 2 X) ∈ center (X ⧸ pPrimeCore 2 X)) :
    (J.map (QuotientGroup.mk' (pPrimeCore 2 X))).IsSubnormal := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 X)
  let C := centralizer ({t} : Set X)
  let γ : ↥C →* X ⧸ pPrimeCore 2 X := ρ.comp C.subtype
  have hγr : γ.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      UnbalancedLayer.map_centralizer_eq (odd_card_pPrimeCore_two X) htt,
      Subgroup.centralizer_eq_top_iff_subset]
    rintro _ rfl
    exact hc
  have hγn : γ.range.Normal := by rw [hγr]; infer_instance
  have h1 := isSubnormal_map_of_range_normal γ hγn hJs
  convert h1 using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hJt hx⟩, hx, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem not_two_dvd_card_ker_bar (J : Subgroup X) :
    ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 X)).subgroupMap J).ker := by
  set K := ((QuotientGroup.mk' (pPrimeCore 2 X)).subgroupMap J).ker
  have hle : K.map J.subtype ≤ pPrimeCore 2 X := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : QuotientGroup.mk' (pPrimeCore 2 X) (k : X) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hc : Nat.card K ∣ Nat.card (pPrimeCore 2 X) := by
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  intro h2
  exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two X))
    (even_iff_two_dvd.mpr (h2.trans hc))

end Image

section Joint

variable {α : Type*} [Fintype α] [DecidableEq α] {G : Type} [Group G] [Finite G]
  {ε : G →* Perm α} {t : G}

theorem jointKer_commute_of_isTwoQuasisimple (hinj : Function.Injective ε)
    (ht2 : ε t * ε t = 1) {L : Subgroup (centralizer ({t} : Set G))}
    (hLq : IsTwoQuasisimple ↥L) : ∀ w ∈ jointKer ε t, w ∈ L → ∀ x ∈ L, ⁅w, x⁆ = 1 := by
  intro w hwN hwL x hxL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hρ
  set M := (jointKer ε t).subgroupOf L with hM
  have hMn : M.Normal := Subgroup.Normal.subgroupOf jointKer_normal L
  have hMbn : (M.map ρ).Normal := hMn.map ρ (QuotientGroup.mk'_surjective _)
  have hMc : M.map ρ ≤ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases LocalCores.quasisimple_normal_subgroups hLq.2 hMbn with h | h
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hLq.2
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have ha : a ∈ M.map ρ := by rw [h]; exact mem_top a
      have hb : b ∈ M.map ρ := by rw [h]; exact mem_top b
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (jointKer_comm hinj ht2 ha' hb')
    · exact h
  set w' : ↥L := ⟨w, hwL⟩
  set x' : ↥L := ⟨x, hxL⟩
  have hw'M : w' ∈ M := hwN
  have hcO : ⁅w', x'⁆ ∈ pPrimeCore 2 ↥L := by
    have hc := mem_center_iff.mp (hMc ⟨w', hw'M, rfl⟩) (ρ x')
    have h1 : ρ ⁅w', x'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc.symm
    rwa [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hodd : Odd (orderOf ⁅w, x⁆) := by
    have h1 : orderOf ⁅w, x⁆ = orderOf ⁅w', x'⁆ := Subgroup.orderOf_coe ⁅w', x'⁆
    rw [h1, ← Subgroup.orderOf_mk _ hcO]
    exact (odd_card_pPrimeCore_two ↥L).of_dvd_nat (orderOf_dvd_natCard _)
  have hcN : ⁅w, x⁆ ∈ jointKer ε t := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hwN ?_
    rw [← mul_assoc]
    exact jointKer_normal.conj_mem _ (inv_mem hwN) x
  exact eq_one_of_odd_of_mul_self hodd (jointKer_mul_self hinj ht2 hcN)

end Joint

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
