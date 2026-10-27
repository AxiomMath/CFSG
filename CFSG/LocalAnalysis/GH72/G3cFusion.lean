module

public import CFSG.LocalAnalysis.GH72.DDSubgroups
import CFSG.LocalAnalysis.GH72.G3c
import CFSG.LocalAnalysis.GH72.L2Local
import CFSG.LocalAnalysis.GH72.Sec4Conj
import CFSG.LocalAnalysis.GH72.Sec4A
import CFSG.LocalAnalysis.GH72.Sec4Util
import CFSG.Quasithin.Vol2.Ch10SecQ34LA
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

namespace G3cF

section FourGroup

variable {G : Type*} [Group G]

theorem sq_not_mem_centralizer {V : Subgroup G} (hV : IsKleinFour V) {z c g t : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hc : c ∈ V) (hc1 : c ≠ 1) (hcz : c ≠ z)
    (hgV : g ∈ normalizer (V : Set G)) (hgc : g * c * g⁻¹ = z)
    (htV : t ∈ normalizer (V : Set G)) (htz : t * z * t⁻¹ = z)
    (htC : t ∉ centralizer (V : Set G)) :
    (g * t * g⁻¹ * t) ^ 2 ∉ centralizer (V : Set G) := by
  have hz2 : z * z = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hV hz
  have hc2 : c * c = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hV hc
  have htc : t * c * t⁻¹ = c * z := by
    have hmem : t * c * t⁻¹ ∈ V := (mem_normalizer_iff.1 htV c).1 hc
    rcases mem_kleinFour_cases hV hc hz hc1 hz1 hcz hmem with h | h | h | h
    · exact absurd (eq_of_conj_eq_conj (g := t) (by rw [h]; group)) hc1
    ·
      exfalso
      apply htC
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ V := hy
      rcases mem_kleinFour_cases hV hc hz hc1 hz1 hcz hy' with rfl | rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · exact mul_comm_of_conj_eq h
      · exact mul_comm_of_conj_eq htz
      · apply mul_comm_of_conj_eq
        calc t * (c * z) * t⁻¹ = (t * c * t⁻¹) * (t * z * t⁻¹) := by group
          _ = c * z := by rw [h, htz]
    · exact absurd (eq_of_conj_eq_conj (g := t) (by rw [h, htz])) hcz
    · exact h
  obtain ⟨w, hw⟩ : ∃ w : G, w = g * z * g⁻¹ := ⟨_, rfl⟩
  have hwV : w ∈ V := hw ▸ (mem_normalizer_iff.1 hgV z).1 hz
  have hw1 : w ≠ 1 := fun h => hz1 (eq_of_conj_eq_conj (g := g) (by rw [← hw, h]; group))
  have hwz : w ≠ z := fun h => hcz (eq_of_conj_eq_conj (g := g) (by rw [hgc, ← hw, h]))
  have htw : t * w * t⁻¹ = w * z := by
    rcases mem_kleinFour_cases hV hc hz hc1 hz1 hcz hwV with h | h | h | h
    · exact absurd h hw1
    · rw [h, htc]
    · exact absurd h hwz
    · rw [h]
      calc t * (c * z) * t⁻¹ = (t * c * t⁻¹) * (t * z * t⁻¹) := by group
        _ = c * z * z := by rw [htc, htz]
  have hb : g⁻¹ * z * g = c := by rw [← hgc]; group
  have hb' : g⁻¹ * w * g = z := by rw [hw]; group
  have hzc : z * (c * z) = c := by
    rw [← mul_assoc, ← mul_comm_of_mem_kleinFour hV hc hz, mul_assoc, hz2, mul_one]
  have hn1 : (g * t * g⁻¹ * t) * z * (g * t * g⁻¹ * t)⁻¹ = z * w := by
    calc (g * t * g⁻¹ * t) * z * (g * t * g⁻¹ * t)⁻¹
        = g * t * (g⁻¹ * (t * z * t⁻¹) * g) * t⁻¹ * g⁻¹ := by group
      _ = g * (t * c * t⁻¹) * g⁻¹ := by rw [htz, hb]; group
      _ = (g * c * g⁻¹) * (g * z * g⁻¹) := by rw [htc]; group
      _ = z * w := by rw [hgc, ← hw]
  have hn2 : (g * t * g⁻¹ * t) * w * (g * t * g⁻¹ * t)⁻¹ = z := by
    calc (g * t * g⁻¹ * t) * w * (g * t * g⁻¹ * t)⁻¹
        = g * t * (g⁻¹ * (t * w * t⁻¹) * g) * t⁻¹ * g⁻¹ := by group
      _ = g * t * ((g⁻¹ * w * g) * (g⁻¹ * z * g)) * t⁻¹ * g⁻¹ := by rw [htw]; group
      _ = g * ((t * z * t⁻¹) * (t * c * t⁻¹)) * g⁻¹ := by rw [hb', hb]; group
      _ = g * c * g⁻¹ := by rw [htz, htc, hzc]
      _ = z := hgc
  intro hC
  set n : G := g * t * g⁻¹ * t with hn
  have h3 : n ^ 2 * z * (n ^ 2)⁻¹ = w := by
    calc n ^ 2 * z * (n ^ 2)⁻¹ = n * (n * z * n⁻¹) * n⁻¹ := by rw [sq]; group
      _ = n * (z * w) * n⁻¹ := by rw [hn1]
      _ = (n * z * n⁻¹) * (n * w * n⁻¹) := by group
      _ = z * w * z := by rw [hn1, hn2]
      _ = w := by rw [mul_comm_of_mem_kleinFour hV hz hwV, mul_assoc, hz2, mul_one]
  have hcomm : z * n ^ 2 = n ^ 2 * z := (mem_centralizer_iff.1 hC) z hz
  apply hwz
  rw [← h3, ← hcomm]
  group

end FourGroup

section Fusion

variable {G : Type*} [Group G] [Finite G] (𝔖 : Sec3Setting G)

theorem conj_mem_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {x g : G} (hx : x ∈ 𝔖.S₁)
    (hx2 : orderOf x = 2) (hg : g * x * g⁻¹ ∈ (𝔖.S : Subgroup G)) : g * x * g⁻¹ ∈ 𝔖.S₁ := by
  have hS : (𝔖.S : Subgroup G) = 𝔖.S₁ ⊔ 𝔖.S₂ := 𝔖.decomp.sup_eq.symm
  exact ((hpf.separate x (mem_sup_left hx) (g * x * g⁻¹) (hS ▸ hg) hx2
    (isConj_iff.2 ⟨g, rfl⟩)).1).1 hx

theorem conj_mem_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {x g : G} (hx : x ∈ 𝔖.S₂)
    (hx2 : orderOf x = 2) (hg : g * x * g⁻¹ ∈ (𝔖.S : Subgroup G)) : g * x * g⁻¹ ∈ 𝔖.S₂ := by
  have hS : (𝔖.S : Subgroup G) = 𝔖.S₁ ⊔ 𝔖.S₂ := 𝔖.decomp.sup_eq.symm
  exact ((hpf.separate x (mem_sup_right hx) (g * x * g⁻¹) (hS ▸ hg) hx2
    (isConj_iff.2 ⟨g, rfl⟩)).2).1 hx

theorem mem_normalizer_inf_of_conj_mem {A P : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (hP : ∀ x ∈ P, orderOf x = 2 → ∀ g : G, g * x * g⁻¹ ∈ (𝔖.S : Subgroup G) →
      g * x * g⁻¹ ∈ P) {n : G} (hn : n ∈ normalizer (A : Set G)) :
    n ∈ normalizer ((A ⊓ P : Subgroup G) : Set G) := by
  have key : ∀ m ∈ normalizer (A : Set G), ∀ x ∈ A ⊓ P, m * x * m⁻¹ ∈ A ⊓ P := by
    intro m hm x hx
    obtain ⟨hxA, hxP⟩ := mem_inf.1 hx
    have hmx : m * x * m⁻¹ ∈ A := (mem_normalizer_iff.1 hm x).1 hxA
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, mul_inv_cancel]
      exact one_mem _
    · exact mem_inf.2 ⟨hmx,
        hP x hxP (G4b.orderOf_eq_two_of_isE16 hA hxA hx1) m (hAS hmx)⟩
  refine G4b.mem_normalizer_of_conj_mem (key n hn) fun x hx => ?_
  have h := key n⁻¹ (inv_mem hn) x hx
  rwa [inv_inv] at h

theorem normalizer_le_normalizer_inf_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {A : Subgroup G}
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) :
    normalizer (A : Set G) ≤ normalizer ((A ⊓ 𝔖.S₁ : Subgroup G) : Set G) := fun _ hn =>
  mem_normalizer_inf_of_conj_mem 𝔖 hAS hA (fun _ hx hx2 _ hg => conj_mem_left 𝔖 hpf hx hx2 hg) hn

theorem normalizer_le_normalizer_inf_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {A : Subgroup G}
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) :
    normalizer (A : Set G) ≤ normalizer ((A ⊓ 𝔖.S₂ : Subgroup G) : Set G) := fun _ hn =>
  mem_normalizer_inf_of_conj_mem 𝔖 hAS hA (fun _ hx hx2 _ hg => conj_mem_right 𝔖 hpf hx hx2 hg) hn

theorem isSylowOf_S {K : Subgroup G} (hSK : (𝔖.S : Subgroup G) ≤ K) :
    ABGLocalTools.IsSylowOf 2 (𝔖.S : Subgroup G) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ABGLocalTools.isSylowOf_iff.2 ⟨hSK, 𝔖.S.isPGroup', fun h => ?_⟩
  exact 𝔖.S.not_dvd_index (h.trans (relIndex_dvd_index_of_le hSK))

theorem exists_mem_normalizer_conj_eq {A : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    {x z : G} (hxA : x ∈ A) (hzS : (𝔖.S : Subgroup G) ≤ C z) (hxz : IsConj x z) :
    ∃ n ∈ normalizer (A : Set G), n * x * n⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hxz
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  have hBz : A.map (MulAut.conj g).toMonoidHom ≤ C z := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
      _ = g * (x * a) * g⁻¹ := by rw [G4b.comm_of_isE16 hA ha hxA]
      _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group
  obtain ⟨c, hcz, hc⟩ := exists_mem_map_conj_le_of_isSylowOf (isSylowOf_S 𝔖 hzS) hBz
    (hA2.map _)
  have hcz' : c * z = z * c := by
    exact mem_centralizer_singleton_iff.1 hcz
  have hB : A.map (MulAut.conj (c * g)).toMonoidHom ≤ 𝔖.S := by
    rw [← G4b.map_conj_map_conj]
    exact hc
  obtain ⟨s, hsS, hs⟩ := Sec3Setting.lemma_3_1 𝔖 A _ hAS hB hA
    (IsE16.map hA _ (MulAut.conj (c * g)).injective) (c * g) rfl
  have hsz : s * z = z * s := by
    have h := hzS hsS
    rw [mem_centralizer_singleton_iff] at h
    exact h
  refine ⟨s⁻¹ * (c * g), ?_, ?_⟩
  · rw [G4b.mem_normalizer_iff_map_conj_eq', ← G4b.map_conj_map_conj, ← hs, G4b.map_conj_map_conj,
      inv_mul_cancel, G4b.map_conj_one]
  · calc s⁻¹ * (c * g) * x * (s⁻¹ * (c * g))⁻¹ = s⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) * s := by group
      _ = s⁻¹ * (c * z * c⁻¹) * s := by rw [hg]
      _ = s⁻¹ * (z * s) := by rw [hcz']; group
      _ = z := by rw [← hsz]; group

omit [Finite G] in
theorem exists_mem_normalizer_not_mem_centralizer {D V : Subgroup G} (hD : IsDihNonab D)
    (hV : IsFourIn D V) :
    ∃ t ∈ D, t ∈ normalizer (V : Set G) ∧ t ∉ centralizer (V : Set G) := by
  obtain ⟨f, hfD, -, hfV, heq⟩ := IsDihNonab.exists_inf_normalizer_four_eq hD hV
  have hfN : f ∈ D ⊓ normalizer (V : Set G) := heq ▸ mem_sup_right (mem_zpowers f)
  refine ⟨f, hfD, (mem_inf.1 hfN).2, fun hfC => hfV ?_⟩
  rw [← IsDih.inf_centralizer_four (isDih_of_isDihNonab hD) hV]
  exact mem_inf.2 ⟨hfD, hfC⟩

theorem le_C_of_central {z : G} (hzc₁ : 𝔖.S₁ ≤ C z) (hzc₂ : 𝔖.S₂ ≤ C z) :
    (𝔖.S : Subgroup G) ≤ C z := by
  rw [← 𝔖.decomp.sup_eq]
  exact sup_le hzc₁ hzc₂

theorem exists_three_element_core {A V W : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (hV : IsKleinFour V) (hVA : V ≤ A) {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hzS : (𝔖.S : Subgroup G) ≤ C z) (hconj : ∀ c ∈ V, c ≠ 1 → IsConj c z)
    (hNV : normalizer (A : Set G) ≤ normalizer (V : Set G))
    (hNW : normalizer (A : Set G) ≤ normalizer (W : Set G)) {t : G}
    (htA : t ∈ normalizer (A : Set G)) (htz : t * z * t⁻¹ = z)
    (htC : t ∉ centralizer (V : Set G)) (htW : t ∈ centralizer (W : Set G)) :
    ∃ v ∈ normalizer (A : Set G), (∃ k : ℕ, orderOf v = 3 ^ k) ∧
      v ∈ centralizer (W : Set G) ∧ ∀ a ∈ V, a ≠ 1 → v * a * v⁻¹ ≠ a := by
  obtain ⟨c, hcV, hc1, hcz⟩ := exists_mem_kleinFour_ne hV hzV
  obtain ⟨g, hgA, hgc⟩ :=
    exists_mem_normalizer_conj_eq 𝔖 hAS hA (hVA hcV) hzS (hconj c hcV hc1)
  have hn2 := sq_not_mem_centralizer hV hzV hz1 hcV hc1 hcz (hNV hgA) hgc (hNV htA) htz htC
  have hnA : g * t * g⁻¹ * t ∈ normalizer (A : Set G) :=
    mul_mem (mul_mem (mul_mem hgA htA) (inv_mem hgA)) htA
  have hnW : g * t * g⁻¹ * t ∈ centralizer (W : Set G) := by
    have hgC : g ∈ normalizer (centralizer (W : Set G) : Set G) :=
      G4b.mem_normalizer_centralizer (hNW hgA)
    exact mul_mem ((mem_normalizer_iff.1 hgC t).1 htW) htW
  obtain ⟨m, hm3, hfix⟩ := exists_pow_three_element_of_sq_not_mem_centralizer hV (hNV hnA) hn2
  exact ⟨_, pow_mem hnA m, hm3, pow_mem hnW m, hfix⟩

theorem exists_three_element_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {A : Subgroup G}
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) :
    ∃ v ∈ normalizer (A : Set G), (∃ k : ℕ, orderOf v = 3 ^ k) ∧
      v ∈ centralizer ((A ⊓ 𝔖.S₁ : Subgroup G) : Set G) ∧
      ∀ a ∈ A ⊓ 𝔖.S₂, a ≠ 1 → v * a * v⁻¹ ≠ a := by
  obtain ⟨hsplit, -, hV₂⟩ := 𝔖.decomp.e16_split hAS hA
  obtain ⟨z, hzS₂, hz2, hzc⟩ := exists_central_involution 𝔖.S₂ 𝔖.decomp.isDih₂
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hzS : (𝔖.S : Subgroup G) ≤ C z :=
    le_C_of_central 𝔖 (fun x hx => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hx hzS₂)) hzc
  have hzA : z ∈ A := 𝔖.decomp.center_le hAS hA (𝔖.decomp.le_right hzS₂) hzS
  obtain ⟨t, htS₂, htV, htC⟩ := exists_mem_normalizer_not_mem_centralizer 𝔖.decomp.dih₂ hV₂
  have htW : t ∈ centralizer ((A ⊓ 𝔖.S₁ : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun h hh => 𝔖.decomp.comm (mem_inf.1 hh).2 htS₂
  have htA : t ∈ normalizer (A : Set G) := by
    have h₁ : t ∈ normalizer ((A ⊓ 𝔖.S₁ : Subgroup G) : Set G) :=
      centralizer_le_normalizer _ htW
    rw [hsplit]
    rw [G4b.mem_normalizer_iff_map_conj_eq'] at h₁ htV ⊢
    rw [Subgroup.map_sup, h₁, htV]
  have htz : t * z * t⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (hzc htS₂), mul_inv_cancel_right]
  exact exists_three_element_core 𝔖 hAS hA (isKleinFour_of_isFourIn hV₂) inf_le_left
    (mem_inf.2 ⟨hzA, hzS₂⟩) hz1 hzS
    (fun c hc hc1 => hpf.conj₂ c (mem_inf.1 hc).2 z hzS₂
      (G4b.orderOf_eq_two_of_isE16 hA (mem_inf.1 hc).1 hc1) hz2)
    (normalizer_le_normalizer_inf_right 𝔖 hpf hAS hA)
    (normalizer_le_normalizer_inf_left 𝔖 hpf hAS hA) htA htz htC htW

theorem exists_three_element_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂)
    (h₁ : IsDihNonab 𝔖.S₁) {A : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A) :
    ∃ v ∈ normalizer (A : Set G), (∃ k : ℕ, orderOf v = 3 ^ k) ∧
      v ∈ centralizer ((A ⊓ 𝔖.S₂ : Subgroup G) : Set G) ∧
      ∀ a ∈ A ⊓ 𝔖.S₁, a ≠ 1 → v * a * v⁻¹ ≠ a := by
  obtain ⟨hsplit, hV₁, -⟩ := 𝔖.decomp.e16_split hAS hA
  obtain ⟨z, hzS₁, hz2, hzc⟩ := exists_central_involution 𝔖.S₁ 𝔖.decomp.dih₁
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hzS : (𝔖.S : Subgroup G) ≤ C z :=
    le_C_of_central 𝔖 hzc (fun y hy => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hzS₁ hy).symm)
  have hzA : z ∈ A := 𝔖.decomp.center_le hAS hA (𝔖.decomp.le_left hzS₁) hzS
  obtain ⟨t, htS₁, htV, htC⟩ := exists_mem_normalizer_not_mem_centralizer h₁ hV₁
  have htW : t ∈ centralizer ((A ⊓ 𝔖.S₂ : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun h hh => (𝔖.decomp.comm htS₁ (mem_inf.1 hh).2).symm
  have htA : t ∈ normalizer (A : Set G) := by
    have h₂ : t ∈ normalizer ((A ⊓ 𝔖.S₂ : Subgroup G) : Set G) :=
      centralizer_le_normalizer _ htW
    rw [hsplit]
    rw [G4b.mem_normalizer_iff_map_conj_eq'] at h₂ htV ⊢
    rw [Subgroup.map_sup, htV, h₂]
  have htz : t * z * t⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (hzc htS₁), mul_inv_cancel_right]
  exact exists_three_element_core 𝔖 hAS hA (isKleinFour_of_isFourIn hV₁) inf_le_left
    (mem_inf.2 ⟨hzA, hzS₁⟩) hz1 hzS
    (fun c hc hc1 => hpf.conj₁ c (mem_inf.1 hc).2 z hzS₁
      (G4b.orderOf_eq_two_of_isE16 hA (mem_inf.1 hc).1 hc1) hz2)
    (normalizer_le_normalizer_inf_left 𝔖 hpf hAS hA)
    (normalizer_le_normalizer_inf_right 𝔖 hpf hAS hA) htA htz htC htW

theorem normalizer_le_normalizer_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂)
    (h₁ : IsKleinFour 𝔖.S₁) :
    normalizer ((𝔖.S : Subgroup G) : Set G) ≤ normalizer (𝔖.S₁ : Set G) := by
  have key : ∀ m ∈ normalizer ((𝔖.S : Subgroup G) : Set G), ∀ x ∈ 𝔖.S₁, m * x * m⁻¹ ∈ 𝔖.S₁ := by
    intro m hm x hx
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, mul_inv_cancel]
      exact one_mem _
    · have hx2 : orderOf x = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour h₁ hx) hx1
      exact conj_mem_left 𝔖 hpf hx hx2 ((mem_normalizer_iff.1 hm x).1 (𝔖.decomp.le_left hx))
  intro m hm
  refine G4b.mem_normalizer_of_conj_mem (key m hm) fun x hx => ?_
  have h := key m⁻¹ (inv_mem hm) x hx
  rwa [inv_inv] at h

theorem normalizer_le_normalizer_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) :
    normalizer ((𝔖.S : Subgroup G) : Set G) ≤ normalizer (𝔖.S₂ : Set G) := by
  obtain ⟨R, hRS₂, -, hRidx, hout, -⟩ := IsDihNonab.exists_cyclic_index_two 𝔖.decomp.dih₂
  have hinv : ∀ m ∈ normalizer ((𝔖.S : Subgroup G) : Set G), ∀ y ∈ 𝔖.S₂, y ∉ R →
      m * y * m⁻¹ ∈ 𝔖.S₂ := by
    intro m hm y hy hyR
    have hy1 : y ≠ 1 := fun h => hyR (h ▸ one_mem R)
    have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hout y hy hyR) hy1
    exact conj_mem_right 𝔖 hpf hy hy2 ((mem_normalizer_iff.1 hm y).1 (𝔖.decomp.le_right hy))
  obtain ⟨s, hsS₂, hsR⟩ : ∃ s ∈ 𝔖.S₂, s ∉ R := by
    by_contra h
    have h1 : R.relIndex 𝔖.S₂ = 1 := relIndex_eq_one.2 fun s hs => by
      by_contra hsR
      exact h ⟨s, hs, hsR⟩
    omega
  have key : ∀ m ∈ normalizer ((𝔖.S : Subgroup G) : Set G), ∀ y ∈ 𝔖.S₂, m * y * m⁻¹ ∈ 𝔖.S₂ := by
    intro m hm y hy
    by_cases hyR : y ∈ R
    · have hysR : y * s ∉ R := fun h => hsR (by simpa using R.mul_mem (R.inv_mem hyR) h)
      have hs2 : s * s = 1 := hout s hsS₂ hsR
      have hdec : m * y * m⁻¹ = (m * (y * s) * m⁻¹) * (m * s * m⁻¹) := by
        calc m * y * m⁻¹ = m * (y * (s * s)) * m⁻¹ := by rw [hs2, mul_one]
          _ = (m * (y * s) * m⁻¹) * (m * s * m⁻¹) := by group
      rw [hdec]
      exact mul_mem (hinv m hm _ (mul_mem hy hsS₂) hysR) (hinv m hm s hsS₂ hsR)
    · exact hinv m hm y hy hyR
  intro m hm
  refine G4b.mem_normalizer_of_conj_mem (key m hm) fun x hx => ?_
  have h := key m⁻¹ (inv_mem hm) x hx
  rwa [inv_inv] at h

theorem exists_three_element_normalizer (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂)
    (h₁ : IsKleinFour 𝔖.S₁) :
    ∃ u ∈ normalizer ((𝔖.S : Subgroup G) : Set G), (∃ k : ℕ, orderOf u = 3 ^ k) ∧
      u ∈ normalizer (𝔖.S₁ : Set G) ∧ u ∈ centralizer (𝔖.S₂ : Set G) ∧
      ∀ a ∈ 𝔖.S₁, a ≠ 1 → u * a * u⁻¹ ≠ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : ∀ x ∈ 𝔖.S₁, x ∈ centralizer ((𝔖.S : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := 𝔖.decomp.mem_iff.1 hy
    calc y₁ * y₂ * x = y₁ * (x * y₂) := by rw [mul_assoc, 𝔖.decomp.comm hx hy₂]
      _ = x * (y₁ * y₂) := by
        rw [← mul_assoc, mul_comm_of_mem_kleinFour h₁ hy₁ hx, mul_assoc]
  have hburn : ∀ a ∈ 𝔖.S₁, a ≠ 1 → ∀ b ∈ 𝔖.S₁, b ≠ 1 →
      ∃ n ∈ normalizer ((𝔖.S : Subgroup G) : Set G), n * a * n⁻¹ = b := by
    intro a ha ha1 b hb hb1
    obtain ⟨g, hg⟩ := isConj_iff.1 (hpf.conj₁ a ha b hb
      (orderOf_eq_prime (sq_eq_one_of_mem_kleinFour h₁ ha) ha1)
      (orderOf_eq_prime (sq_eq_one_of_mem_kleinFour h₁ hb) hb1))
    have hy : g⁻¹⁻¹ * a * g⁻¹ ∈ centralizer ((𝔖.S : Subgroup G) : Set G) := by
      rw [inv_inv, hg]
      exact hcen b hb
    obtain ⟨n, hn, hna⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer 𝔖.S a g⁻¹
      (hcen a ha) hy
    refine ⟨n⁻¹, inv_mem hn, ?_⟩
    rw [inv_inv, ← hna, inv_inv, hg]
  have hNS₁ := normalizer_le_normalizer_left 𝔖 hpf h₁
  obtain ⟨a, ha, ha1, -⟩ := exists_mem_kleinFour_ne h₁ (one_mem 𝔖.S₁)
  obtain ⟨b, hb, hb1, hba⟩ := exists_mem_kleinFour_ne h₁ ha
  have hab1 : a * b ≠ 1 := fun h => hba (by
    have h2 := sq_eq_one_of_mem_kleinFour h₁ ha
    rw [sq] at h2
    calc b = a * a * b := by rw [h2, one_mul]
      _ = a := by rw [mul_assoc, h, mul_one])
  obtain ⟨n₁, hn₁, hn₁a⟩ := hburn a ha ha1 b hb hb1
  obtain ⟨n₂, hn₂, hn₂a⟩ := hburn a ha ha1 (a * b) (mul_mem ha hb) hab1
  have hfixsq : ∀ m : G, m ^ 2 ∈ centralizer (𝔖.S₁ : Set G) → m * (m * a * m⁻¹) * m⁻¹ = a := by
    intro m hm
    have h := (mem_centralizer_iff.1 hm) a ha
    calc m * (m * a * m⁻¹) * m⁻¹ = m ^ 2 * a * (m ^ 2)⁻¹ := by rw [sq]; group
      _ = a := by rw [← h, mul_inv_cancel_right]
  obtain ⟨n, hnS, hn2⟩ : ∃ n ∈ normalizer ((𝔖.S : Subgroup G) : Set G),
      n ^ 2 ∉ centralizer (𝔖.S₁ : Set G) := by
    by_cases h1 : n₁ ^ 2 ∈ centralizer (𝔖.S₁ : Set G)
    · by_cases h2 : n₂ ^ 2 ∈ centralizer (𝔖.S₁ : Set G)
      · refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, fun h => hba ?_⟩
        have e₁ : n₁ * b * n₁⁻¹ = a := by rw [← hn₁a]; exact hfixsq n₁ h1
        have e₂ : n₂ * (a * b) * n₂⁻¹ = a := by rw [← hn₂a]; exact hfixsq n₂ h2
        have e₃ : n₁ * (a * b) * n₁⁻¹ = a * b := by
          calc n₁ * (a * b) * n₁⁻¹ = (n₁ * a * n₁⁻¹) * (n₁ * b * n₁⁻¹) := by group
            _ = b * a := by rw [hn₁a, e₁]
            _ = a * b := mul_comm_of_mem_kleinFour h₁ hb ha
        have e₄ : (n₁ * n₂) * a * (n₁ * n₂)⁻¹ = a * b := by
          calc (n₁ * n₂) * a * (n₁ * n₂)⁻¹ = n₁ * (n₂ * a * n₂⁻¹) * n₁⁻¹ := by group
            _ = a * b := by rw [hn₂a, e₃]
        have e₅ : (n₁ * n₂) * (a * b) * (n₁ * n₂)⁻¹ = b := by
          calc (n₁ * n₂) * (a * b) * (n₁ * n₂)⁻¹ = n₁ * (n₂ * (a * b) * n₂⁻¹) * n₁⁻¹ := by group
            _ = b := by rw [e₂, hn₁a]
        have e₆ := hfixsq (n₁ * n₂) h
        rw [e₄, e₅] at e₆
        exact e₆
      · exact ⟨n₂, hn₂, h2⟩
    · exact ⟨n₁, hn₁, h1⟩
  obtain ⟨m, ⟨k, hk⟩, hfix⟩ := exists_pow_three_element_of_sq_not_mem_centralizer h₁ (hNS₁ hnS) hn2
  have huS := pow_mem hnS m
  refine ⟨n ^ m, huS, ⟨k, hk⟩, hNS₁ huS, ?_, hfix⟩
  obtain ⟨e, he, ⟨φ⟩⟩ := 𝔖.decomp.dih₂
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  exact CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.mem_centralizer_of_dihedral h4 φ
    𝔖.decomp.isDih₂.isPGroup (normalizer_le_normalizer_right 𝔖 hpf huS)
    (by rw [hk]; exact Odd.pow (by decide))

end Fusion

section TwoResidual

variable {G : Type*} [Group G] [Finite G]

theorem le_twoResidualOf_of_fixedPointFree {K V : Subgroup G} (hV : IsKleinFour V)
    (hVK : V ≤ K) {v : G} (hvK : v ∈ K) (hv : Odd (orderOf v))
    (hvV : v ∈ normalizer (V : Set G)) (hfix : ∀ a ∈ V, a ≠ 1 → v * a * v⁻¹ ≠ a) :
    V ≤ O2 K := by
  have hvO : v ∈ O2 K := mem_twoResidualOf_of_odd hvK hv
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  obtain ⟨x, hx⟩ : ∃ x : G, x = v * y * v⁻¹ := ⟨_, rfl⟩
  have hxV : x ∈ V := hx ▸ (mem_normalizer_iff.1 hvV y).1 hy
  have hx1 : x ≠ 1 := fun h => hy1 (eq_of_conj_eq_conj (g := v) (by rw [← hx, h]; group))
  have hxy : x ≠ y := hx ▸ hfix y hy hy1
  have hx'V : v * x * v⁻¹ ∈ V := (mem_normalizer_iff.1 hvV x).1 hxV
  have hx'1 : v * x * v⁻¹ ≠ 1 := fun h => hx1 (eq_of_conj_eq_conj (g := v) (by rw [h]; group))
  have hx'x : v * x * v⁻¹ ≠ x := hfix x hxV hx1
  have hx'y : v * x * v⁻¹ ≠ y := by
    intro h
    have hxy1 : x * y ≠ 1 := by
      intro h'
      apply hxy
      have h2 := sq_eq_one_of_mem_kleinFour hV hy
      rw [sq] at h2
      calc x = x * y * y := by rw [mul_assoc, h2, mul_one]
        _ = y := by rw [h', one_mul]
    apply hfix (x * y) (mul_mem hxV hy) hxy1
    calc v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
      _ = y * x := by rw [h, ← hx]
      _ = x * y := mul_comm_of_mem_kleinFour hV hy hxV
  have hyx : y = x * (v * x * v⁻¹) := by
    rcases mem_kleinFour_cases hV hxV hx'V hx1 hx'1 (Ne.symm hx'x) hy with h | h | h | h
    · exact absurd h hy1
    · exact absurd h.symm hxy
    · exact absurd h.symm hx'y
    · exact h
  have hxinv : x⁻¹ = x := by
    have h2 := sq_eq_one_of_mem_kleinFour hV hxV
    rw [sq] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have h1 : x * v * x⁻¹ ∈ O2 K :=
    (mem_normalizer_iff.1 (le_normalizer_twoResidualOf K (hVK hxV)) v).1 hvO
  rw [hyx]
  have e : x * (v * x * v⁻¹) = (x * v * x⁻¹) * v⁻¹ := by
    rw [hxinv]
    group
  rw [e]
  exact mul_mem h1 (inv_mem hvO)

omit [Finite G] in
theorem le_of_forall_mul_self_eq_one {D L : Subgroup G} (hD : IsDih D)
    (h : ∀ y ∈ D, y * y = 1 → y ∈ L) : D ≤ L := by
  rcases IsDih.isKleinFour_or_isDihNonab hD with h4 | hna
  · intro y hy
    exact h y hy (by rw [← sq]; exact sq_eq_one_of_mem_kleinFour h4 hy)
  · obtain ⟨R, hRD, -, hRidx, hout, -⟩ := IsDihNonab.exists_cyclic_index_two hna
    obtain ⟨s, hsD, hsR⟩ : ∃ s ∈ D, s ∉ R := by
      by_contra hc
      have h1 : R.relIndex D = 1 := relIndex_eq_one.2 fun s hs => by
        by_contra hsR
        exact hc ⟨s, hs, hsR⟩
      omega
    intro y hy
    by_cases hyR : y ∈ R
    · have hysR : y * s ∉ R := fun h' => hsR (by simpa using R.mul_mem (R.inv_mem hyR) h')
      have hs2 : s * s = 1 := hout s hsD hsR
      have e : y = (y * s) * s := by rw [mul_assoc, hs2, mul_one]
      rw [e]
      exact mul_mem (h _ (mul_mem hy hsD) (hout _ (mul_mem hy hsD) hysR)) (h s hsD hs2)
    · exact h y hy (hout y hy hyR)

end TwoResidual

section Factors

variable {G : Type*} [Group G] [Finite G] (𝔖 : Sec3Setting G)

theorem le_twoResidualOf_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {K : Subgroup G}
    (hS₂K : 𝔖.S₂ ≤ K)
    (hC : ∀ A : Subgroup G, A ≤ 𝔖.S → IsE16 A →
      centralizer ((A ⊓ 𝔖.S₁ : Subgroup G) : Set G) ≤ K) :
    𝔖.S₂ ≤ O2 K := by
  refine le_of_forall_mul_self_eq_one 𝔖.decomp.isDih₂ fun y hy hyy => ?_
  obtain ⟨V₂, hV₂, hyV₂⟩ := IsDih.exists_four_mem 𝔖.decomp.isDih₂ hy hyy
  obtain ⟨V₁, hV₁⟩ := IsDih.exists_four 𝔖.decomp.dih₁
  set A : Subgroup G := V₁ ⊔ V₂ with hAdef
  have hA : IsE16 A := 𝔖.decomp.isE16_sup hV₁ hV₂
  have hAS : A ≤ 𝔖.S := sup_le (hV₁.1.trans 𝔖.decomp.le_left) (hV₂.1.trans 𝔖.decomp.le_right)
  have hA₂ : A ⊓ 𝔖.S₂ = V₂ := 𝔖.decomp.sup_inf_right hV₁.1 hV₂.1
  obtain ⟨v, hvA, ⟨k, hk⟩, hvC, hfix⟩ := exists_three_element_right 𝔖 hpf hAS hA
  have hvV : v ∈ normalizer (V₂ : Set G) :=
    hA₂ ▸ normalizer_le_normalizer_inf_right 𝔖 hpf hAS hA hvA
  have hle := le_twoResidualOf_of_fixedPointFree (isKleinFour_of_isFourIn hV₂)
    (hV₂.1.trans hS₂K) (hC A hAS hA hvC) (by rw [hk]; exact Odd.pow (by decide)) hvV
    (fun a ha ha1 => hfix a (hA₂ ▸ ha) ha1)
  exact hle hyV₂

theorem le_twoResidualOf_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {K : Subgroup G}
    (hS₁K : 𝔖.S₁ ≤ K)
    (hC : ∀ A : Subgroup G, A ≤ 𝔖.S → IsE16 A →
      centralizer ((A ⊓ 𝔖.S₂ : Subgroup G) : Set G) ≤ K) :
    𝔖.S₁ ≤ O2 K := by
  obtain ⟨V₂, hV₂⟩ := IsDih.exists_four 𝔖.decomp.isDih₂
  rcases IsDih.isKleinFour_or_isDihNonab 𝔖.decomp.dih₁ with h4 | hna
  · obtain ⟨u, -, ⟨k, hk⟩, huN, huC, hfix⟩ := exists_three_element_normalizer 𝔖 hpf h4
    have hV₁ : IsFourIn 𝔖.S₁ 𝔖.S₁ := ⟨le_rfl, fun x hx => by
      rw [← sq]; exact sq_eq_one_of_mem_kleinFour h4 hx, h4.card_four⟩
    set A : Subgroup G := 𝔖.S₁ ⊔ V₂ with hAdef
    have hA : IsE16 A := 𝔖.decomp.isE16_sup hV₁ hV₂
    have hAS : A ≤ 𝔖.S := sup_le 𝔖.decomp.le_left (hV₂.1.trans 𝔖.decomp.le_right)
    have huK : u ∈ K := hC A hAS hA (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right) huC)
    exact le_twoResidualOf_of_fixedPointFree h4 hS₁K huK (by rw [hk]; exact Odd.pow (by decide))
      huN hfix
  · refine le_of_forall_mul_self_eq_one 𝔖.decomp.dih₁ fun y hy hyy => ?_
    obtain ⟨V₁, hV₁, hyV₁⟩ := IsDih.exists_four_mem 𝔖.decomp.dih₁ hy hyy
    set A : Subgroup G := V₁ ⊔ V₂ with hAdef
    have hA : IsE16 A := 𝔖.decomp.isE16_sup hV₁ hV₂
    have hAS : A ≤ 𝔖.S := sup_le (hV₁.1.trans 𝔖.decomp.le_left) (hV₂.1.trans 𝔖.decomp.le_right)
    have hA₁ : A ⊓ 𝔖.S₁ = V₁ := 𝔖.decomp.sup_inf_left hV₁.1 hV₂.1
    obtain ⟨v, hvA, ⟨k, hk⟩, hvC, hfix⟩ := exists_three_element_left 𝔖 hpf hna hAS hA
    have hvV : v ∈ normalizer (V₁ : Set G) :=
      hA₁ ▸ normalizer_le_normalizer_inf_left 𝔖 hpf hAS hA hvA
    have hle := le_twoResidualOf_of_fixedPointFree (isKleinFour_of_isFourIn hV₁)
      (hV₁.1.trans hS₁K) (hC A hAS hA hvC) (by rw [hk]; exact Odd.pow (by decide)) hvV
      (fun a ha ha1 => hfix a (hA₁ ▸ ha) ha1)
    exact hle hyV₁

end Factors

section Thompson

variable {G : Type*} [Group G] [Finite G]

open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm
  card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (eq_one_or_eq_of_mem_zpowers)

omit [Finite G] in
theorem sup_inf_eq_left {P Q R : Subgroup G} (hRP : R ≤ P) (hPQ : P ⊓ Q = ⊥)
    (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) : (R ⊔ Q) ⊓ P = R := by
  refine le_antisymm (fun g hg => ?_) (le_inf le_sup_left hRP)
  obtain ⟨hgRQ, hgP⟩ := mem_inf.1 hg
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer
    (le_normalizer_of_comm fun x hx y hy => hcomm x (hRP hx) y hy)).1 hgRQ
  have hyP : y ∈ P := by
    have h := P.mul_mem (P.inv_mem (hRP hx)) hgP
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h
  have hy1 : y = 1 := by
    have h : y ∈ P ⊓ Q := mem_inf.2 ⟨hyP, hy⟩
    rw [hPQ] at h
    exact (mem_bot).1 h
  rw [hy1, mul_one]
  exact hx

omit [Finite G] in
theorem index_ne_two_of_twoResidualOf_eq {K : Subgroup G} (hK : O2 K = K) (N : Subgroup K)
    (hN : N.Normal) : N.index ≠ 2 := by
  intro hN2
  have hmem : N ∈ {M : Subgroup K | M.Normal ∧ ∃ n : ℕ, M.index = 2 ^ n} :=
    ⟨hN, ⟨1, by rw [hN2]; norm_num⟩⟩
  have hle : O2 K ≤ N.map K.subtype := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, sInf_le hmem hy, rfl⟩
  have heq : N.map K.subtype = K :=
    le_antisymm (Subgroup.map_subtype_le N) fun x hx => hle (hK.symm ▸ hx)
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : G) ∈ N.map K.subtype := heq.symm ▸ y.2
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hy
    rwa [show y' = y from Subtype.ext hyy'] at hy'
  rw [hNtop, index_top] at hN2
  exact absurd hN2 (by norm_num)

theorem false_of_isDih_inf {K P Q R₀ : Subgroup G} (hK : O2 K = K) (hR₀P : R₀ ≤ P)
    (hR₀K : R₀ ≤ K) (hR₀ : IsDih R₀) (hPQ : P ⊓ Q = ⊥)
    (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hsyl : ABGLocalTools.IsSylowOf 2 (R₀ ⊔ Q) K) {z : G} (hzR₀ : z ∈ R₀)
    (hz2 : orderOf z = 2) (hKz : K ≤ C z)
    (hfus : ∀ x ∈ P, orderOf x = 2 → ∀ g : G, g * x * g⁻¹ ∈ R₀ ⊔ Q → g * x * g⁻¹ ∈ P) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  obtain ⟨R, hRR₀, hRidx, x, hxR₀, hxR, hx2, hRinv⟩ : ∃ R : Subgroup G, R ≤ R₀ ∧
      R.relIndex R₀ = 2 ∧ ∃ x ∈ R₀, x ∉ R ∧ orderOf x = 2 ∧
        ∀ y ∈ R, orderOf y = 2 → y = z := by
    rcases IsDih.isKleinFour_or_isDihNonab hR₀ with h4 | hna
    · refine ⟨zpowers z, zpowers_le.2 hzR₀, ?_, ?_⟩
      · have h1 := relIndex_mul_card (zpowers z) R₀
        rw [inf_eq_left.2 (zpowers_le.2 hzR₀), Nat.card_zpowers, hz2, h4.card_four] at h1
        omega
      · obtain ⟨x, hx, hx1, hxz⟩ := exists_mem_kleinFour_ne h4 hzR₀
        refine ⟨x, hx, fun h => ?_, orderOf_eq_prime (sq_eq_one_of_mem_kleinFour h4 hx) hx1,
          fun y hy hy2 => ?_⟩
        · rcases eq_one_or_eq_of_mem_zpowers hzz h with h' | h'
          · exact hx1 h'
          · exact hxz h'
        · rcases eq_one_or_eq_of_mem_zpowers hzz hy with h' | h'
          · rw [h', orderOf_one] at hy2
            exact absurd hy2 (by norm_num)
          · exact h'
    · obtain ⟨R, hRR₀, -, hRidx, hout, hcen⟩ := IsDihNonab.exists_cyclic_index_two hna
      obtain ⟨z₀, -, hz₀2, hZ⟩ := IsDihNonab.exists_inf_centralizer_self_eq hna
      have hzZ : z ∈ zpowers z₀ := by
        rw [← hZ]
        refine mem_inf.2 ⟨hzR₀, mem_centralizer_iff.2 fun y hy => ?_⟩
        exact (mem_centralizer_singleton_iff.1 (hKz (hR₀K hy)))
      obtain ⟨x, hxR₀, hxR⟩ : ∃ x ∈ R₀, x ∉ R := by
        by_contra h
        have h1 : R.relIndex R₀ = 1 := relIndex_eq_one.2 fun x hx => by
          by_contra hxR
          exact h ⟨x, hx, hxR⟩
        omega
      have hx1 : x ≠ 1 := fun h => hxR (h ▸ one_mem R)
      refine ⟨R, hRR₀, hRidx, x, hxR₀, hxR,
        orderOf_eq_prime (by rw [sq]; exact hout x hxR₀ hxR) hx1, fun y hy hy2 => ?_⟩
      have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
      have hyZ : y ∈ zpowers z₀ := by
        rw [← hZ]
        exact mem_inf.2 ⟨hRR₀ hy, mem_centralizer_iff.2 fun w hw => hcen y hy hyy w hw⟩
      have hz₀ : z₀ * z₀ = 1 := by rw [← sq, ← hz₀2, pow_orderOf_eq_one]
      have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; exact absurd hy2 (by norm_num)
      rcases eq_one_or_eq_of_mem_zpowers hz₀ hyZ with h | h
      · exact absurd h hy1
      · rcases eq_one_or_eq_of_mem_zpowers hz₀ hzZ with h' | h'
        · exact absurd h' hz1
        · rw [h, h']
  set T : Subgroup G := R₀ ⊔ Q with hT
  set U : Subgroup G := R ⊔ Q with hU
  have hcommR₀ : ∀ a ∈ R₀, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => hcomm a (hR₀P ha) b hb
  have hcardT : Nat.card T = Nat.card R₀ * Nat.card Q :=
    card_sup_of_le_normalizer (le_normalizer_of_comm hcommR₀)
      (eq_bot_iff.2 fun g hg => hPQ ▸ mem_inf.2 ⟨hR₀P (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩)
  have hcardU : Nat.card U = Nat.card R * Nat.card Q :=
    card_sup_of_le_normalizer (le_normalizer_of_comm fun a ha b hb => hcommR₀ a (hRR₀ ha) b hb)
      (eq_bot_iff.2 fun g hg => hPQ ▸ mem_inf.2 ⟨hR₀P (hRR₀ (mem_inf.1 hg).1), (mem_inf.1 hg).2⟩)
  have hUT : U ≤ T := sup_le_sup_right hRR₀ Q
  have hUidx : U.relIndex T = 2 := by
    have h1 := relIndex_mul_card U T
    have h2 := relIndex_mul_card R R₀
    rw [inf_eq_left.2 hUT, hcardU, hcardT] at h1
    rw [inf_eq_left.2 hRR₀, hRidx] at h2
    have hpos : 0 < Nat.card R * Nat.card Q := Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← h2]
    ring
  have hTK : T ≤ K := hsyl.le
  have hxT : x ∈ T := mem_sup_left hxR₀
  have hxK : x ∈ K := hTK hxT
  have hxU : x ∉ U := fun h => hxR (by
    rw [← sup_inf_eq_left (le_trans hRR₀ hR₀P) hPQ hcomm]
    exact mem_inf.2 ⟨h, hR₀P hxR₀⟩)
  have hconj : ∀ g : K, g⁻¹ * (⟨x, hxK⟩ : K) * g ∉ U.subgroupOf K := by
    intro g hg
    rw [mem_subgroupOf] at hg
    have hy : (g : G)⁻¹ * x * g ∈ U := by simpa using hg
    have hyP : (g : G)⁻¹ * x * g ∈ P := by
      have h := hfus x (hR₀P hxR₀) hx2 (g : G)⁻¹ (by rw [inv_inv]; exact hUT hy)
      rwa [inv_inv] at h
    have hyR : (g : G)⁻¹ * x * g ∈ R := by
      rw [← sup_inf_eq_left (le_trans hRR₀ hR₀P) hPQ hcomm]
      exact mem_inf.2 ⟨hy, hyP⟩
    have hy2 : orderOf ((g : G)⁻¹ * x * g) = 2 := by
      rw [show (g : G)⁻¹ * x * g = (MulAut.conj (g : G)⁻¹) x by simp, MulEquiv.orderOf_eq]
      exact hx2
    have hyz := hRinv _ hyR hy2
    have hgz : (g : G) * z = z * g := mem_centralizer_singleton_iff.1 (hKz g.2)
    apply hxR
    have : x = z := by
      calc x = (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ := by group
        _ = (g : G) * z * (g : G)⁻¹ := by rw [hyz]
        _ = z := by rw [hgz, mul_inv_cancel_right]
    rw [this, ← hyz]
    exact hyR
  have hT2 : IsPGroup 2 (T.subgroupOf K) := hsyl.isPGroup.comap_subtype
  have hTidx : ¬ 2 ∣ (T.subgroupOf K).index := (ABGLocalTools.isSylowOf_iff.mp hsyl).2.2
  have hUTsub : U.subgroupOf K ≤ T.subgroupOf K := fun y hy =>
    mem_subgroupOf.mpr (hUT (mem_subgroupOf.mp hy))
  have hUidx' : (U.subgroupOf K).relIndex (T.subgroupOf K) = 2 :=
    (relIndex_subgroupOf (H := U) (K := T) (L := K) hTK).trans hUidx
  have hmin : ∀ y ∈ T.subgroupOf K, y ∉ U.subgroupOf K → orderOf (⟨x, hxK⟩ : K) ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ one_mem _)
    rw [← Subgroup.orderOf_coe (⟨x, hxK⟩ : K), hx2]
    have hpos : 0 < orderOf y := orderOf_pos y
    have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    omega
  obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    (G := K) (T := T.subgroupOf K) (U := U.subgroupOf K) hT2 hTidx hUTsub hUidx'
    (mem_subgroupOf.mpr hxT) (fun h => hxU (mem_subgroupOf.mp h)) hmin hconj
  exact index_ne_two_of_twoResidualOf_eq hK N hN hNidx

variable (𝔖 : Sec3Setting G)

theorem inf_left_eq_bot (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {K : Subgroup G} (hK : O2 K = K)
    (hS₂K : 𝔖.S₂ ≤ K) (hsyl : ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ K) ⊔ 𝔖.S₂) K) {z : G}
    (hzS₁ : z ∈ 𝔖.S₁) (hz2 : orderOf z = 2) (hzc : 𝔖.S₁ ≤ C z) (hKz : K ≤ C z) :
    𝔖.S₁ ⊓ K = ⊥ := by
  have hsyl' : ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ K) ⊔ (𝔖.S₂ ⊓ K)) K := by
    rwa [inf_eq_left.2 hS₂K]
  rcases (Sec3Setting.lemma_3_13 𝔖 hpf K hK hsyl').1 with h | hD
  · exact h
  · exfalso
    obtain ⟨V, hV⟩ := IsDih.exists_four hD
    have hV' : IsFourIn 𝔖.S₁ V := ⟨hV.1.trans inf_le_left, hV.2⟩
    have hzV : z ∈ V := IsDih.mem_four_of_central 𝔖.decomp.dih₁ hV' hzS₁ fun y hy =>
      (mem_centralizer_singleton_iff.1 (hzc hy))
    exact false_of_isDih_inf hK inf_le_left inf_le_right hD 𝔖.decomp.inf_eq
      (fun x hx y hy => 𝔖.decomp.comm hx hy) hsyl (hV.1 hzV) hz2 hKz
      (fun x hx hx2 g hg => conj_mem_left 𝔖 hpf hx hx2
        (sup_le (inf_le_left.trans 𝔖.decomp.le_left) 𝔖.decomp.le_right hg))

theorem inf_right_eq_bot (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {K : Subgroup G} (hK : O2 K = K)
    (hS₁K : 𝔖.S₁ ≤ K) (hsyl : ABGLocalTools.IsSylowOf 2 (𝔖.S₁ ⊔ (𝔖.S₂ ⊓ K)) K) {z : G}
    (hzS₂ : z ∈ 𝔖.S₂) (hz2 : orderOf z = 2) (hzc : 𝔖.S₂ ≤ C z) (hKz : K ≤ C z) :
    𝔖.S₂ ⊓ K = ⊥ := by
  have hsyl' : ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ K) ⊔ (𝔖.S₂ ⊓ K)) K := by
    rwa [inf_eq_left.2 hS₁K]
  rcases (Sec3Setting.lemma_3_13 𝔖 hpf K hK hsyl').2 with h | hD
  · exact h
  · exfalso
    obtain ⟨V, hV⟩ := IsDih.exists_four hD
    have hV' : IsFourIn 𝔖.S₂ V := ⟨hV.1.trans inf_le_left, hV.2⟩
    have hzV : z ∈ V := IsDih.mem_four_of_central 𝔖.decomp.isDih₂ hV' hzS₂ fun y hy =>
      (mem_centralizer_singleton_iff.1 (hzc hy))
    exact false_of_isDih_inf hK inf_le_left inf_le_right hD (by rw [inf_comm, 𝔖.decomp.inf_eq])
      (fun _ hx _ hy => (𝔖.decomp.comm hy hx).symm) (by rwa [sup_comm]) (hV.1 hzV) hz2 hKz
      (fun x hx hx2 g hg => conj_mem_right 𝔖 hpf hx hx2
        (sup_le (inf_le_left.trans 𝔖.decomp.le_right) 𝔖.decomp.le_left hg))

end Thompson

section Isolated

variable {G : Type*} [Group G] [Finite G]

open CFSG.CGT.Foote81L6 (card_sup_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct (eq_one_or_eq_of_mem_zpowers)

omit [Finite G] in
theorem card_sup_zpowers {K : Subgroup G} {f : G} (hf2 : orderOf f = 2)
    (hfN : f ∈ normalizer (K : Set G)) (hfK : f ∉ K) :
    Nat.card ↥(K ⊔ zpowers f) = Nat.card K * 2 := by
  have hff : f * f = 1 := by rw [← sq, ← hf2, pow_orderOf_eq_one]
  rw [card_sup_of_le_normalizer (zpowers_le.2 hfN), Nat.card_zpowers, hf2]
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgK, hgf⟩ := mem_inf.1 hg
  rcases eq_one_or_eq_of_mem_zpowers hff hgf with h | h
  · exact (mem_bot).2 h
  · exact absurd (h ▸ hgK) hfK

theorem isSylowOf_sup_zpowers {K Q : Subgroup G} (hQ : ABGLocalTools.IsSylowOf 2 Q K) {f : G}
    (hf2 : orderOf f = 2) (hfN : f ∈ normalizer (K : Set G)) (hfK : f ∉ K)
    (hfQ : ∀ y ∈ Q, f * y = y * f) :
    ABGLocalTools.IsSylowOf 2 (zpowers f ⊔ Q) (K ⊔ zpowers f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hff : f * f = 1 := by rw [← sq, ← hf2, pow_orderOf_eq_one]
  have hQK : Q ≤ K := hQ.le
  have hcardT : Nat.card ↥(zpowers f ⊔ Q) = 2 * Nat.card Q := by
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => by
      rcases eq_one_or_eq_of_mem_zpowers hff hx with rfl | rfl
      · rw [one_mul, mul_one]
      · exact hfQ y hy), Nat.card_zpowers, hf2]
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨hgf, hgQ⟩ := mem_inf.1 hg
    rcases eq_one_or_eq_of_mem_zpowers hff hgf with h | h
    · exact (mem_bot).2 h
    · exact absurd (h ▸ hQK hgQ) hfK
  have hle : zpowers f ⊔ Q ≤ K ⊔ zpowers f :=
    sup_le le_sup_right (hQK.trans le_sup_left)
  obtain ⟨k, hk⟩ := hQ.isPGroup.exists_card_eq
  refine ABGLocalTools.isSylowOf_iff.2 ⟨hle, IsPGroup.of_card (n := k + 1) (by
    rw [hcardT, hk, pow_succ, mul_comm]), fun h2 => ?_⟩
  have h1 := relIndex_mul_card (zpowers f ⊔ Q) (K ⊔ zpowers f)
  have h3 := relIndex_mul_card Q K
  rw [inf_eq_left.2 hle, hcardT, card_sup_zpowers hf2 hfN hfK] at h1
  rw [inf_eq_left.2 hQK] at h3
  have heq : (zpowers f ⊔ Q).relIndex (K ⊔ zpowers f) = Q.relIndex K := by
    have hpos : 0 < 2 * Nat.card Q := Nat.mul_pos (by norm_num) Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← h3]
    ring
  exact (ABGLocalTools.isSylowOf_iff.1 hQ).2.2 (heq ▸ h2)

theorem isIsolatedIn_sup_zpowers {K P Q : Subgroup G} (hQ : ABGLocalTools.IsSylowOf 2 Q K)
    (hPQ : P ⊓ Q = ⊥) (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {f : G} (hfP : f ∈ P)
    (hf2 : orderOf f = 2) (hfN : f ∈ normalizer (K : Set G)) (hfK : f ∉ K)
    (hfus : ∀ g : G, g * f * g⁻¹ ∈ zpowers f ⊔ Q → g * f * g⁻¹ ∈ P) :
    IsIsolatedIn (K ⊔ zpowers f) f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hff : f * f = 1 := by rw [← sq, ← hf2, pow_orderOf_eq_one]
  have hTsyl := isSylowOf_sup_zpowers hQ hf2 hfN hfK fun y hy => hcomm f hfP y hy
  have hTC : zpowers f ⊔ Q ≤ C f := sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    fun y hy => mem_centralizer_singleton_iff.2 (hcomm f hfP y hy).symm
  have hTsyl' : ABGLocalTools.IsSylowOf 2 (zpowers f ⊔ Q) ((K ⊔ zpowers f) ⊓ C f) :=
    hTsyl.of_le (le_inf hTsyl.le hTC) inf_le_left
  refine ⟨mem_sup_right (mem_zpowers f), hf2, fun h hh hcom => ?_⟩
  have hyF : h * f * h⁻¹ ∈ K ⊔ zpowers f :=
    mul_mem (mul_mem hh (mem_sup_right (mem_zpowers f))) (inv_mem hh)
  have hyC : h * f * h⁻¹ ∈ C f := mem_centralizer_singleton_iff.2 hcom
  have hy2 : orderOf (h * f * h⁻¹) = 2 := by
    rw [show h * f * h⁻¹ = (MulAut.conj h) f from rfl, MulEquiv.orderOf_eq]
    exact hf2
  have hyp : IsPGroup 2 (zpowers (h * f * h⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  obtain ⟨c, hc, hcy⟩ := exists_mem_conj_mem_of_isSylowOf hTsyl' (mem_inf.2 ⟨hyF, hyC⟩) hyp
  have hcf : c * f = f * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  have e : c * (h * f * h⁻¹) * c⁻¹ = (c * h) * f * (c * h)⁻¹ := by group
  rw [e] at hcy
  have hP : (c * h) * f * (c * h)⁻¹ ∈ zpowers f := by
    rw [← sup_inf_eq_left (zpowers_le.2 hfP) hPQ hcomm]
    exact mem_inf.2 ⟨hcy, hfus _ hcy⟩
  rcases eq_one_or_eq_of_mem_zpowers hff hP with h1 | h1
  · exfalso
    have : f = 1 := by
      calc f = (c * h)⁻¹ * ((c * h) * f * (c * h)⁻¹) * (c * h) := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hf2
    exact absurd hf2 (by norm_num)
  · calc h * f * h⁻¹ = c⁻¹ * ((c * h) * f * (c * h)⁻¹) * c := by group
      _ = c⁻¹ * f * c := by rw [h1]
      _ = f := by rw [mul_assoc, ← hcf, ← mul_assoc, inv_mul_cancel, one_mul]

variable (𝔖 : Sec3Setting G)

theorem isIsolatedIn_sup_zpowers_left (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {K : Subgroup G}
    (hS₂ : ABGLocalTools.IsSylowOf 2 𝔖.S₂ K) {f : G} (hf : f ∈ 𝔖.S₁) (hf2 : orderOf f = 2)
    (hfN : f ∈ normalizer (K : Set G)) (hfK : f ∉ K) : IsIsolatedIn (K ⊔ zpowers f) f :=
  isIsolatedIn_sup_zpowers hS₂ 𝔖.decomp.inf_eq (fun _ hx _ hy => 𝔖.decomp.comm hx hy) hf hf2 hfN
    hfK fun _ hg => conj_mem_left 𝔖 hpf hf hf2
      (sup_le (zpowers_le.2 (𝔖.decomp.le_left hf)) 𝔖.decomp.le_right hg)

theorem isIsolatedIn_sup_zpowers_right (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {K : Subgroup G}
    (hS₁ : ABGLocalTools.IsSylowOf 2 𝔖.S₁ K) {f : G} (hf : f ∈ 𝔖.S₂) (hf2 : orderOf f = 2)
    (hfN : f ∈ normalizer (K : Set G)) (hfK : f ∉ K) : IsIsolatedIn (K ⊔ zpowers f) f :=
  isIsolatedIn_sup_zpowers hS₁ (by rw [inf_comm, 𝔖.decomp.inf_eq])
    (fun _ hx _ hy => (𝔖.decomp.comm hy hx).symm) hf hf2 hfN hfK fun _ hg =>
      conj_mem_right 𝔖 hpf hf hf2 (sup_le (zpowers_le.2 (𝔖.decomp.le_right hf)) 𝔖.decomp.le_left hg)

end Isolated

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem conj_mul_inv_mem_O {K : Subgroup G} {f : G} (hiso : IsIsolatedIn (K ⊔ zpowers f) f)
    (hfN : f ∈ normalizer (K : Set G)) (hfK : f ∉ K) {k : G} (hk : k ∈ K) :
    k * f * k⁻¹ * f⁻¹ ∈ O K := by
  have h1 := hiso.conj_mul_inv_mem_O (mem_sup_left hk)
  refine G4b.le_O_of_odd (fun x hx => ?_) (le_sup_left.trans (le_normalizer_O _))
    (card_O_odd _) h1
  have hxF : x ∈ K ⊔ zpowers f := G4b.O_le_self _ hx
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (card_O_odd _) (Subgroup.orderOf_dvd_natCard _ hx)
  have hidx : (K.subgroupOf (K ⊔ zpowers f)).index = 2 := by
    have h := relIndex_mul_card K (K ⊔ zpowers f)
    rw [inf_eq_left.2 le_sup_left, card_sup_zpowers hiso.2.1 hfN hfK] at h
    have hpos : 0 < Nat.card K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))
  have hx' := mem_of_index_eq_two_of_odd_orderOf hidx
    (x := ⟨x, hxF⟩) (by rw [Subgroup.orderOf_mk]; exact hodd)
  exact mem_subgroupOf.1 hx'

end ZStar

end G3cF

end CFSG.GH72
