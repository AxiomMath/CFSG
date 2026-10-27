module

public import CFSG.GH74.Uniqueness.SU.SU8Glob
public import CFSG.Goldschmidt.Steps.Fusion

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU4
  CFSG.GH74.Uniqueness.SU.SU8.Setup

namespace Lem203

variable {G : Type} [Group G]

theorem perfect_of_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    _root_.commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

omit [Group G] in
theorem conj_comm {M : Type} [Group M] (X x y : M) (hxy : x * y = y * x) :
    X * x * X⁻¹ * (X * y * X⁻¹) = X * y * X⁻¹ * (X * x * X⁻¹) := by
  calc X * x * X⁻¹ * (X * y * X⁻¹) = X * (x * y) * X⁻¹ := by group
    _ = X * (y * x) * X⁻¹ := by rw [hxy]
    _ = X * y * X⁻¹ * (X * x * X⁻¹) := by group

theorem conj_mem_centralizerBar {H L : Subgroup G} (hL : H ≤ normalizer (L : Set G)) {h v : G}
    (hh : h ∈ H) (hv : v ∈ centralizerBar H L) : h * v * h⁻¹ ∈ centralizerBar H L := by
  obtain ⟨hvH, hc⟩ := mem_centralizerBar.mp hv
  have hvh : h * v * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hvH) (H.inv_mem hh)
  refine mem_centralizerBar.mpr ⟨hvh, fun l hl => ?_⟩
  obtain ⟨l', hl'L, hl'⟩ : ∃ l' : ↥H, (l' : G) ∈ L ∧ l = ⟨h, hh⟩ * l' * ⟨h, hh⟩⁻¹ := by
    refine ⟨⟨h, hh⟩⁻¹ * l * ⟨h, hh⟩, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (hL (H.inv_mem hh)) (l : G)).mp hl
    simpa using this
  have h1 := hc l' hl'L
  have e2 : (⟨h * v * h⁻¹, hvh⟩ : ↥H) = ⟨h, hh⟩ * ⟨v, hvH⟩ * ⟨h, hh⟩⁻¹ := by
    apply Subtype.ext; simp
  rw [hl', e2]
  simp only [map_mul, map_inv]
  exact conj_comm _ _ _ h1

end Lem203

section Hyp

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

theorem Hyp20A.exists_conj_le (hyp : Hyp20A z S L A) :
    ∃ h ∈ Hz z, ∀ a ∈ A, h⁻¹ * a * h ∈ S := by
  have hSH : S ≤ Hz z := hyp.S_sylow_H.1
  have hSp : IsPGroup 2 ↥(S.subgroupOf (Hz z)) :=
    hyp.S_sylow_H.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hSidx : ¬ 2 ∣ (S.subgroupOf (Hz z)).index := by
    have h1 : Odd (S.relIndex (Hz z)) := hyp.S_sylow_H.2.2
    intro h2
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  let P₀ : Sylow 2 ↥(Hz z) := hSp.toSylow hSidx
  have hAp : IsPGroup 2 ↥(A.subgroupOf (Hz z)) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    have := hyp.A_elem.2 (x : G) (Subgroup.mem_subgroupOf.mp x.2)
    simpa using this
  obtain ⟨P, hP⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(Hz z)) P₀ P
  refine ⟨(g : G), g.2, fun a ha => ?_⟩
  have haH : a ∈ Hz z := hyp.A_le_H ha
  have h1 : (⟨a, haH⟩ : ↥(Hz z)) ∈ (P : Subgroup ↥(Hz z)) :=
    hP (Subgroup.mem_subgroupOf.mpr ha)
  rw [← hg, Setup.mem_sylow_smul_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem Hyp20A.TI (hyp : Hyp20A z S L A) {g v : G}
    (hv : v ∈ A ⊓ centralizerBar (Hz z) L) (hv1 : v ≠ 1)
    (hgv : g * v * g⁻¹ ∈ A ⊓ centralizerBar (Hz z) L) : g ∈ normalizer (L : Set G) := by
  by_contra hg
  obtain ⟨h, hhH, hhS⟩ := hyp.exists_conj_le
  have hC : ∀ {y : G}, y ∈ centralizerBar (Hz z) L → h⁻¹ * y * h ∈ centralizerBar (Hz z) L := by
    intro y hy
    have := Lem203.conj_mem_centralizerBar hyp.L_normal ((Hz z).inv_mem hhH) hy
    simpa using this
  have hv' : h⁻¹ * v * h ∈ S ⊓ centralizerBar (Hz z) L := ⟨hhS v hv.1, hC hv.2⟩
  have hw' : h⁻¹ * (g * v * g⁻¹) * h ∈ S ⊓ centralizerBar (Hz z) L :=
    ⟨hhS _ hgv.1, hC hgv.2⟩
  have hxn : (h⁻¹ * g * h)⁻¹ ∉ normalizer (L : Set G) := by
    intro hxn
    apply hg
    have hhn : h ∈ normalizer (L : Set G) := hyp.L_normal hhH
    have hxN : h⁻¹ * g * h ∈ normalizer (L : Set G) := (Subgroup.inv_mem_iff _).mp hxn
    have : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    rw [this]
    exact (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem hhn hxN)
      ((normalizer (L : Set G)).inv_mem hhn)
  have hmem : h⁻¹ * v * h ∈ (S ⊓ centralizerBar (Hz z) L) ⊓
      conjSub (h⁻¹ * g * h)⁻¹ (S ⊓ centralizerBar (Hz z) L) := by
    refine ⟨hv', ⟨_, hw', ?_⟩⟩
    show (h⁻¹ * g * h)⁻¹ * (h⁻¹ * (g * v * g⁻¹) * h) * ((h⁻¹ * g * h)⁻¹)⁻¹ = h⁻¹ * v * h
    group
  rw [hyp.Q_tame _ hxn] at hmem
  have h1 : h⁻¹ * v * h = 1 := (Subgroup.mem_bot).mp hmem
  apply hv1
  calc v = h * (h⁻¹ * v * h) * h⁻¹ := by group
    _ = 1 := by rw [h1]; group

omit [Finite G] in
theorem Hyp20A.z_mem (hyp : Hyp20A z S L A) : z ∈ A ⊓ centralizerBar (Hz z) L := by
  have hzA : z ∈ A := hyp.A_ge (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  refine ⟨hzA, ?_⟩
  have hzH : z ∈ Hz z := Subgroup.mem_centralizer_iff.mpr (fun y hy => by
    rw [Set.mem_singleton_iff.mp hy])
  refine mem_centralizerBar.mpr ⟨hzH, fun l _ => ?_⟩
  have hl : z * (l : G) = (l : G) * z := Subgroup.mem_centralizer_iff.mp l.2 z (Set.mem_singleton z)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hl.symm

omit [Finite G] in
theorem Hyp20A.z_ne_one (hyp : Hyp20A z S L A) : z ≠ 1 := by
  intro h
  have := hyp.z_invol
  rw [h, orderOf_one] at this
  omega

omit [Finite G] in
theorem Hyp20A.A_exp (hyp : Hyp20A z S L A) : ∀ a ∈ A, a * a = 1 := by
  intro a ha
  simpa [sq] using hyp.A_elem.2 a ha

theorem Hyp20A.no_index_two (hyp : Hyp20A z S L A) :
    ∀ H₀ : Subgroup G, H₀ ≤ normalizer (A : Set G) →
      (H₀.subgroupOf (normalizer (A : Set G))).index ≠ 2 := by
  obtain ⟨S', hAS, hcl⟩ := hyp.A_strongly_closed
  have := hyp.simple
  exact CFSG.Goldschmidt.N5c G S' A (normalizer (A : Set G)) hAS hyp.A_elem.1 hcl
    (Lem203.perfect_of_simple hyp.nonab) le_rfl

structure Out203 (z : G) (S L A : Subgroup G) : Prop where
  bender : ∃ i e, BenderType ↥(hbarImage (Hz z) L) 2 i e
  act : Act.ActData A L (A ⊓ centralizerBar (Hz z) L) 2
  card_A : Nat.card A = 8
  card_AC : Nat.card ↥(A ⊓ centralizerBar (Hz z) L) = 2
  trans : ∀ u ∈ A, u ≠ 1 → ∀ v ∈ A, v ≠ 1 → ∃ g ∈ normalizer (A : Set G), g * u * g⁻¹ = v
  order : ∃ _ : ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).Normal,
    Nat.card (↥(normalizer (A : Set G)) ⧸
      (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))) = 21 ∧
    ∃ a b : ↥(normalizer (A : Set G)) ⧸
      (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)), a * b ≠ b * a

theorem out203 (hyp : Hyp20A z S L A)
    (hZ : center ↥(hbarImage (Hz z) L) = ⊥) : Out203 z S L A := by
  obtain ⟨n, i, e, hBT⟩ := hyp.exists_benderType hZ
  obtain ⟨h8, hAC, hn, htr, hord⟩ := Glob.lemma203_core (hyp.actData hBT) hyp.A_exp hyp.z_mem
    hyp.z_ne_one (fun g v hv hv1 hg => hyp.TI hv hv1 hg) hyp.irreducible hyp.no_index_two
  subst hn
  exact ⟨⟨i, e, hBT⟩, hyp.actData hBT, h8, hAC, htr, hord⟩

end Hyp

end CFSG.GH74.Uniqueness.SU.SU8
