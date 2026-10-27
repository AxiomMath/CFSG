module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step9

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup G}

theorem S7Config.eq_of_central (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) {x : G} (hxS : x ∈ S) (hxL : x ∈ L)
    (hc : ∀ y ∈ S ⊓ L, x * y = y * x) : x = 1 ∨ x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  set φ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hφ
  have hA : IsSylowOf 2 (S ⊓ L) L := hS.inf_of_le_normalizer h.hL.1 hHN
  have hA' : IsSylowOf 2 ((S ⊓ L).subgroupOf L) ⊤ := (isSylowOf_map_subtype_iff L).mp (by
    rwa [subgroupOf_map_subtype, map_subtype_top', inf_eq_left.mpr inf_le_right])
  have hS₀ : IsSylowOf 2 (((S ⊓ L).subgroupOf L).map φ) ⊤ := by
    have h1 := IsSylowOf.map φ hA'
    rwa [Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective _)] at h1
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have hcen := lemma410a_three (by norm_num) h.hcov (mk_mem_center_of_mem_center hzc)
    (mk_ne_one_of_orderOf_two hz') (isSylowIn_iff_isSylowOf.mpr hS₀) (x := φ ⟨x, hxL⟩)
    ⟨⟨x, hxL⟩, mem_inf.mpr ⟨hxS, hxL⟩, rfl⟩ (by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext (hc _ hy)))
  have hzS : z ∈ S := IsSylowOf.mem_of_central hS (mem_centralizer_singleton_iff.mpr rfl)
    (fun k hk => mem_centralizer_singleton_iff.mp hk) (n := 1)
    (by rw [pow_one, ← h.hz, pow_orderOf_eq_one])
  have hodd := odd_card_pPrimeCore_map L
  rcases hcen with h1 | h1
  · left
    obtain ⟨n, hn⟩ := hS.isPGroup ⟨x, hxS⟩
    have h2 : (⟨x, hxL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    exact eq_one_of_two_pow_of_odd hodd ⟨_, h2, rfl⟩ (n := n)
      (by simpa using congrArg Subtype.val hn)
  · right
    have h2 : (⟨z, h.hzL⟩ : ↥L)⁻¹ * ⟨x, hxL⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.mp h1.symm
    obtain ⟨n, hn⟩ := hS.isPGroup ⟨z⁻¹ * x, mul_mem (inv_mem hzS) hxS⟩
    have h3 := eq_one_of_two_pow_of_odd hodd ⟨_, h2, rfl⟩ (n := n)
      (by simpa using congrArg Subtype.val hn)
    rw [show x = z * (z⁻¹ * x) by group]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    rw [h3, mul_one]

theorem S7Config.closure_inf_eq (hI : S7Inputs) (h : S7Config G z L) {t : G} (htL : t ∈ L)
    (ht : orderOf t = 2) (htZ : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : Bar L) ∉ center (Bar L))
    {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer {z} ⊓ centralizer {t})) :
    closure {x | x ∈ T ⊓ L ∧ x * x = 1} = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  set φ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hφ
  have hTt : T ≤ centralizer {t} := hT.le.trans inf_le_right
  have hNle : L ⊓ centralizer {t} ≤ centralizer {z} ⊓ centralizer {t} :=
    inf_le_inf_right _ h.hL.1
  have hNn : centralizer {z} ⊓ centralizer {t} ≤ normalizer ((L ⊓ centralizer {t} : Subgroup G) :
      Set G) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro x
    obtain ⟨hmz, hmt⟩ := mem_inf.mp hm
    have hmL := hHN hmz
    have hmt' := le_normalizer hmt
    simp only [mem_inf]
    exact and_congr (mem_normalizer_iff.mp hmL x) (mem_normalizer_iff.mp hmt' x)
  have hB : IsSylowOf 2 (T ⊓ L) (L ⊓ centralizer {t}) := by
    have h1 := hT.inf_of_le_normalizer hNle hNn
    rwa [inf_comm L (centralizer {t}), ← inf_assoc, inf_eq_left.mpr hTt,
      inf_comm (centralizer {t}) L] at h1
  have hB' : IsSylowOf 2 ((T ⊓ L).subgroupOf L) (centralizer ({⟨t, htL⟩} : Set ↥L)) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (isSylowOf_map_subtype_iff L).mp (by
      rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right,
        inf_eq_left.mpr inf_le_left])
  have htt : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 := by
    have ht' : orderOf (⟨t, htL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
    rw [← sq, ← ht', pow_orderOf_eq_one]
  have hT₀ : IsSylowOf 2 (((T ⊓ L).subgroupOf L).map φ) (centralizer {φ ⟨t, htL⟩}) := by
    have h1 := IsSylowOf.map φ hB'
    rwa [hφ, map_centralizer_eq (odd_card_pPrimeCore_two ↥L) htt] at h1
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have ht2 : orderOf (φ ⟨t, htL⟩) = 2 := orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥L)
    (by rw [Subgroup.orderOf_mk]; exact ht)
  have hcl := lemma410f_three (by norm_num) h.hcov ht2 htZ (isSylowIn_iff_isSylowOf.mpr hT₀)
  have hBp : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
    hB'.isPGroup
  have hcl' := closure_involutions_eq_of_map hBp φ (odd_card_ker_mk L) hcl
  have h1 := congrArg (fun K : Subgroup ↥L => K.map L.subtype) hcl'
  rw [MonoidHom.map_closure, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext x
  constructor
  · rintro ⟨hxB, hx2⟩
    exact ⟨⟨x, (mem_inf.mp hxB).2⟩, ⟨hxB, Subtype.ext hx2⟩, rfl⟩
  · rintro ⟨y, ⟨hyB, hy2⟩, rfl⟩
    exact ⟨hyB, congrArg Subtype.val hy2⟩

section Certified


theorem S7Config.isSylowOf_top (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) : IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hSP⟩ := exists_isSylowOf_le (le_top : S ≤ ⊤) hS.isPGroup
  rcases eq_or_lt_of_le hSP with heq | hlt
  · exact heq ▸ hP
  exfalso
  have : Group.IsNilpotent ↥P := hP.isPGroup.isNilpotent
  have hlt' : S.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr fun htop => hlt.not_ge fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥P) ∈ S.subgroupOf P := htop ▸ mem_top _
    exact h1
  obtain ⟨g, hgN, hgS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
  set g₀ : G := (g : G) with hg₀
  have hg₀S : g₀ ∉ S := hgS
  have hcS : ∀ s ∈ S, g₀ * s * g₀⁻¹ ∈ S := fun s hs =>
    (mem_normalizer_iff.mp hgN ⟨s, hSP hs⟩).mp hs
  have hcS' : ∀ s ∈ S, g₀⁻¹ * s * g₀ ∈ S := fun s hs => by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgN) ⟨s, hSP hs⟩).mp hs
    rw [inv_inv] at h1
    exact h1
  have hzS : z ∈ S := IsSylowOf.mem_of_central hS (mem_centralizer_singleton_iff.mpr rfl)
    (fun k hk => mem_centralizer_singleton_iff.mp hk) (n := 1)
    (by rw [pow_one, ← h.hz, pow_orderOf_eq_one])
  set u := g₀ * z * g₀⁻¹ with hu
  have huS : u ∈ S := hcS z hzS
  have huc : ∀ y ∈ S, u * y = y * u := by
    intro y hy
    have h1 : (g₀⁻¹ * y * g₀) * z = z * (g₀⁻¹ * y * g₀) :=
      mem_centralizer_singleton_iff.mp (hS.le (hcS' y hy))
    calc u * y = g₀ * (z * (g₀⁻¹ * y * g₀)) * g₀⁻¹ := by rw [hu]; group
      _ = g₀ * ((g₀⁻¹ * y * g₀) * z) * g₀⁻¹ := by rw [h1]
      _ = y * u := by rw [hu]; group
  have huL : u ∈ L := ((h.conj_iff hI (hS.le huS)).mp ⟨g₀, rfl⟩).1
  have hu1 : u ≠ 1 := fun h1 => by
    have h2 : z = 1 := by
      calc z = g₀⁻¹ * u * g₀ := by rw [hu]; group
        _ = 1 := by rw [h1]; group
    have h3 := h.hz
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have huz : u = z :=
    (h.eq_of_central hI hS huS huL fun y hy => huc y (mem_inf.mp hy).1).resolve_left hu1
  have hgH : g₀ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g₀ * z = u * g₀ := by rw [hu]; group
      _ = z * g₀ := by rw [huz]
  obtain ⟨n, hn⟩ := hP.isPGroup g
  have hgn : g₀ ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hgN' : zpowers g₀ ≤ normalizer (S : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hcS s hs, fun hs => ?_⟩
    have h1 := hcS' _ hs
    rwa [show g₀⁻¹ * (g₀ * s * g₀⁻¹) * g₀ = s by group] at h1
  have hsup : IsPGroup 2 ↥(S ⊔ zpowers g₀) :=
    IsPGroup.to_sup_of_normal_left' hS.isPGroup (isPGroup_zpowers_of_pow hgn) hgN'
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le (zpowers_le.mpr hgH)) hsup
  exact hg₀S (heq ▸ mem_sup_right (mem_zpowers g₀))

theorem S7Config.not_dvd_index (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) : ¬ 2 ∣ S.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isSylowOf_iff.mp (h.isSylowOf_top hI hS)).2.2
  rwa [relIndex_top_right] at h1

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
