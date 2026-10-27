module

public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.GroupTheory.TitsSystem.MinimalCoset
import CFSG.GroupTheory.TitsSystem.Automorphism

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type*} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

@[expose] def InvariantLink {Γ : Type*} [Group Γ] (B : Subgroup G) (φ : Γ →* MulAut G)
    (x y : G) : Prop :=
  x⁻¹ * y ∈ B ∨ ∃ P : Subgroup G, P ≠ ⊤ ∧ (∀ γ, P.map (φ γ).toMonoidHom = P) ∧
    B.map (MulAut.conj x).toMonoidHom ≤ P ∧ B.map (MulAut.conj y).toMonoidHom ≤ P

namespace IsBNPair

private lemma map_conj_parabolic_of_mem {J : Set (WeylGroup B N)} {c : G}
    (hc : c ∈ parabolic B N J) :
    (parabolic B N J).map (MulAut.conj c).toMonoidHom = parabolic B N J := by
  simpa using Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hc)

private lemma map_conj_parabolic_invariant {Γ : Type*} [Group Γ] (h : IsBNPair B N S)
    (φ : Γ →* MulAut G) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hPJmap : ∀ γ, (parabolic B N J).map (φ γ).toMonoidHom = parabolic B N J)
    {g : G} (hfix : ∀ γ, g⁻¹ * φ γ g ∈ B) (γ : Γ) :
    (((parabolic B N J).map (MulAut.conj g).toMonoidHom).map (φ γ).toMonoidHom) =
      (parabolic B N J).map (MulAut.conj g).toMonoidHom := by
  set c := g⁻¹ * φ γ g with hc_def
  have hcPJ : c ∈ parabolic B N J := by rw [hc_def]; exact h.le_parabolic hJ (hfix γ)
  have hconjc : (parabolic B N J).map (MulAut.conj c).toMonoidHom = parabolic B N J :=
    map_conj_parabolic_of_mem hcPJ
  have hconjgb : MulAut.conj (φ γ g) = MulAut.conj g * MulAut.conj c := by
    rw [show φ γ g = g * c by rw [hc_def]; group, map_mul]
  have hcomp : (φ γ).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (φ γ g)).toMonoidHom.comp (φ γ).toMonoidHom := by
    ext x
    change (φ γ) (g * x * g⁻¹) = (φ γ g) * (φ γ x) * (φ γ g)⁻¹
    simp only [map_mul, map_inv]
  have hmul : (MulAut.conj g * MulAut.conj c).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj c).toMonoidHom := by
    ext x; rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hPJmap γ, hconjgb, hmul,
    ← Subgroup.map_map, hconjc]

private lemma exists_invariant_parabolic {Γ : Type*} [Group Γ] (h : IsBNPair B N S)
    (φ : Γ →* MulAut G)
    (hS : ∀ s ∈ S, (⨆ γ, (parabolic B N {s}).map (φ γ).toMonoidHom) ≠ ⊤)
    {s : WeylGroup B N} (hs : s ∈ S) :
    ∃ J : Set (WeylGroup B N), J ⊆ S ∧ s ∈ J ∧ parabolic B N J ≠ ⊤ ∧
      (∀ δ, (parabolic B N J).map (φ δ).toMonoidHom = parabolic B N J) := by
  set Q : Subgroup G := ⨆ γ, (parabolic B N {s}).map (φ γ).toMonoidHom with hQ
  have hQne : Q ≠ ⊤ := by rw [hQ]; exact hS s hs
  have hQmap : ∀ δ, Q.map (φ δ).toMonoidHom = Q := by
    intro δ
    rw [hQ, Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le fun γ => ?_
      rw [Subgroup.map_map]
      have hc : (φ δ).toMonoidHom.comp (φ γ).toMonoidHom = (φ (δ * γ)).toMonoidHom := by
        ext x
        change (φ δ) ((φ γ) x) = (φ (δ * γ)) x
        simp only [map_mul, MulAut.mul_apply]
      rw [hc]
      exact le_iSup (fun γ => (parabolic B N {s}).map (φ γ).toMonoidHom) (δ * γ)
    · refine iSup_le fun γ => ?_
      have hc : (φ δ).toMonoidHom.comp (φ (δ⁻¹ * γ)).toMonoidHom = (φ γ).toMonoidHom := by
        ext x
        change (φ δ * φ (δ⁻¹ * γ)) x = (φ γ) x
        congr 1
        rw [← map_mul, show δ * (δ⁻¹ * γ) = γ by group]
      calc (parabolic B N {s}).map (φ γ).toMonoidHom
          = (parabolic B N {s}).map ((φ δ).toMonoidHom.comp (φ (δ⁻¹ * γ)).toMonoidHom) := by
            rw [hc]
        _ = ((parabolic B N {s}).map (φ (δ⁻¹ * γ)).toMonoidHom).map (φ δ).toMonoidHom := by
            rw [← Subgroup.map_map]
        _ ≤ ⨆ γ', ((parabolic B N {s}).map (φ γ').toMonoidHom).map (φ δ).toMonoidHom :=
            le_iSup (fun γ' => ((parabolic B N {s}).map (φ γ').toMonoidHom).map (φ δ).toMonoidHom)
              (δ⁻¹ * γ)
  have hmap1 : (parabolic B N {s}).map (φ 1).toMonoidHom = parabolic B N {s} := by
    have : (φ 1).toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [this, Subgroup.map_id]
  have hleQ : parabolic B N {s} ≤ Q := by
    rw [← hmap1]
    exact le_iSup (fun γ => (parabolic B N {s}).map (φ γ).toMonoidHom) 1
  have hBQ : B ≤ Q := (h.le_parabolic (Set.singleton_subset_iff.2 hs)).trans hleQ
  obtain ⟨J, hJ, hPJ⟩ := h.exists_parabolic hBQ
  have hPJne : parabolic B N J ≠ ⊤ := by
    intro htop
    exact hQne (by rw [hPJ, htop])
  have hsJ : s ∈ J := by
    have hle : parabolic B N {s} ≤ parabolic B N J := by rw [← hPJ]; exact hleQ
    exact (h.parabolic_le_iff (Set.singleton_subset_iff.2 hs) hJ).1 hle (Set.mem_singleton s)
  exact ⟨J, hJ, hsJ, hPJne, fun δ => by rw [← hPJ]; exact hQmap δ⟩

private lemma exists_minimal_coset_descent (h : IsBNPair B N S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {s : WeylGroup B N} (hs : s ∈ S) (hsJ : s ∈ J) {w : WeylGroup B N}
    (hdesc : wordLength S (w * s) + 1 = wordLength S w) :
    ∃ w₁ : WeylGroup B N, w₁⁻¹ * w ∈ Subgroup.closure J ∧
      (∀ u ∈ Subgroup.closure J, wordLength S (w₁ * u) = wordLength S w₁ + wordLength S u) ∧
      wordLength S w₁ < wordLength S w := by
  obtain ⟨w₁, hw₁mem, hw₁add⟩ := h.exists_wordLength_mul_add hJ w
  refine ⟨w₁, hw₁mem, hw₁add, ?_⟩
  have hsC : s ∈ Subgroup.closure J := Subgroup.subset_closure hsJ
  have hlen : wordLength S w = wordLength S w₁ + wordLength S (w₁⁻¹ * w) := by
    have := hw₁add _ hw₁mem
    rwa [show w₁ * (w₁⁻¹ * w) = w by group] at this
  have hu_ne : w₁⁻¹ * w ≠ 1 := by
    intro hu1
    have hw₁eq : w₁ = w := by
      have : w = w₁ * (w₁⁻¹ * w) := by group
      rw [hu1, mul_one] at this
      exact this.symm
    have hs1 : wordLength S s = 1 := by
      have hle := wordLength_gen_le_one (J := S) hs
      have hne : wordLength S s ≠ 0 := by
        intro h0
        exact h.ne_one hs ((wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure s)).1 h0)
      omega
    have hws : wordLength S (w * s) = wordLength S w + 1 := by
      rw [← hw₁eq, hw₁add s hsC, hs1]
    omega
  have hu_pos : 1 ≤ wordLength S (w₁⁻¹ * w) := by
    by_contra hlt
    have h0 : wordLength S (w₁⁻¹ * w) = 0 := Nat.eq_zero_of_le_zero (by omega)
    exact hu_ne ((wordLength_eq_zero_iff h.bnCore.mul_self_eq_one
      (Subgroup.closure_mono hJ hw₁mem)).1 h0)
  omega

private lemma conj_mem_parabolic {Γ : Type*} [Group Γ] (h : IsBNPair B N S)
    (φ : Γ →* MulAut G) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hPJmap : ∀ γ, (parabolic B N J).map (φ γ).toMonoidHom = parabolic B N J)
    {g h₀ : G} (hh₀g : h₀⁻¹ * g ∈ parabolic B N J)
    (hfix : ∀ γ, g⁻¹ * φ γ g ∈ B) (γ : Γ) :
    h₀⁻¹ * φ γ h₀ ∈ parabolic B N J := by
  have h2 : g⁻¹ * φ γ h₀ ∈ parabolic B N J := by
    have e : g⁻¹ * φ γ h₀ = (g⁻¹ * φ γ g) * φ γ (g⁻¹ * h₀) := by
      rw [map_mul, map_inv]; group
    rw [e]
    refine Subgroup.mul_mem _ (h.le_parabolic hJ (hfix γ)) ?_
    have hgh : g⁻¹ * h₀ = (h₀⁻¹ * g)⁻¹ := by group
    rw [hgh, map_inv]
    exact Subgroup.inv_mem _ (by
      have hm := Subgroup.mem_map_of_mem (φ γ).toMonoidHom hh₀g
      rwa [hPJmap γ] at hm)
  have : h₀⁻¹ * φ γ h₀ = (h₀⁻¹ * g) * (g⁻¹ * φ γ h₀) := by group
  rw [this]
  exact Subgroup.mul_mem _ hh₀g h2

private lemma conj_mem_B_of_mem_parabolic {Γ : Type*} [Group Γ] (h : IsBNPair B N S)
    (φ : Γ →* MulAut G) (hB : ∀ γ, B.map (φ γ).toMonoidHom = B)
    {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₁ : WeylGroup B N} {h₀ : G} (hh₀ : h₀ ∈ dc B N w₁)
    (hadd : ∀ v ∈ Subgroup.closure J,
      wordLength S (w₁ * v) = wordLength S w₁ + wordLength S v)
    (γ : Γ) (hp : h₀⁻¹ * φ γ h₀ ∈ parabolic B N J) :
    h₀⁻¹ * φ γ h₀ ∈ B := by
  obtain ⟨v, hv, hpv⟩ := (h.mem_parabolic_iff hJ).1 hp
  have hφh : φ γ h₀ ∈ dc B N (w₁ * v) := by
    have h1 : φ γ h₀ = h₀ * (h₀⁻¹ * φ γ h₀) := by group
    rw [h1, ← h.dc_mul_dc_of_wordLength_add (hadd v hv)]
    exact Set.mul_mem_mul hh₀ hpv
  have hlen : wordLength S (w₁ * v) = wordLength S w₁ :=
    h.wordLength_eq_of_map_mem_dc (hB γ) hh₀ hφh
  have hv0 : wordLength S v = 0 := by
    have := hadd v hv
    omega
  have hv1 : v = 1 :=
    (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (Subgroup.closure_mono hJ hv)).1 hv0
  rw [hv1] at hpv
  exact mem_dc_one.1 hpv

private lemma exists_fixed_mem_dc {Γ : Type*} [Group Γ] (h : IsBNPair B N S)
    (φ : Γ →* MulAut G) (hB : ∀ γ, B.map (φ γ).toMonoidHom = B)
    {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hPJmap : ∀ δ, (parabolic B N J).map (φ δ).toMonoidHom = parabolic B N J)
    {w₁ w : WeylGroup B N} {g : G}
    (hadd : ∀ u ∈ Subgroup.closure J,
      wordLength S (w₁ * u) = wordLength S w₁ + wordLength S u)
    (hu : w₁⁻¹ * w ∈ Subgroup.closure J) (hmem : g ∈ dc B N w)
    (hfix : ∀ γ, g⁻¹ * φ γ g ∈ B) :
    ∃ h₀ ∈ dc B N w₁, (h₀⁻¹ * g ∈ parabolic B N J) ∧
      (∀ γ, h₀⁻¹ * φ γ h₀ ∈ B) := by
  have hlen : wordLength S (w₁ * (w₁⁻¹ * w)) =
      wordLength S w₁ + wordLength S (w₁⁻¹ * w) := hadd _ hu
  have hprod : dc B N w₁ * dc B N (w₁⁻¹ * w) = dc B N w := by
    have := h.dc_mul_dc_of_wordLength_add hlen
    rwa [show w₁ * (w₁⁻¹ * w) = w by group] at this
  rw [← hprod] at hmem
  obtain ⟨h₀, hh₀, y, hy, rfl⟩ := Set.mem_mul.1 hmem
  have hyPJ : y ∈ parabolic B N J := h.dc_subset_parabolic hJ hu hy
  have hh₀g : h₀⁻¹ * (h₀ * y) ∈ parabolic B N J := by simpa using hyPJ
  refine ⟨h₀, hh₀, hh₀g, fun γ => ?_⟩
  exact conj_mem_B_of_mem_parabolic h φ hB hJ hh₀ hadd γ
    (conj_mem_parabolic h φ hJ hPJmap hh₀g hfix γ)

private lemma invariantLink_of_fixed {Γ : Type*} [Group Γ] (h : IsBNPair B N S)
    (φ : Γ →* MulAut G) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hPJne : parabolic B N J ≠ ⊤)
    (hPJmap : ∀ γ, (parabolic B N J).map (φ γ).toMonoidHom = parabolic B N J)
    {g h₀ : G} (hfix : ∀ γ, g⁻¹ * φ γ g ∈ B)
    (hh₀g : h₀⁻¹ * g ∈ parabolic B N J) : InvariantLink B φ h₀ g := by
  set P : Subgroup G := (parabolic B N J).map (MulAut.conj g).toMonoidHom with hP
  have hPne : P ≠ ⊤ := by
    intro hPtop
    have hmap_top : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
    exact hPJne (Subgroup.map_injective (MulAut.conj g).injective (hPtop.trans hmap_top.symm))
  have hPmap : ∀ γ, P.map (φ γ).toMonoidHom = P := fun γ => by
    rw [hP]
    exact map_conj_parabolic_invariant h φ hJ hPJmap hfix γ
  have hBg : B.map (MulAut.conj g).toMonoidHom ≤ P := by
    rw [hP]; exact Subgroup.map_mono (h.le_parabolic hJ)
  have hc : g⁻¹ * h₀ ∈ parabolic B N J := by
    have : g⁻¹ * h₀ = (h₀⁻¹ * g)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hh₀g
  have hBh₀ : B.map (MulAut.conj h₀).toMonoidHom ≤ P := by
    have hconjc : (parabolic B N J).map (MulAut.conj (g⁻¹ * h₀)).toMonoidHom =
        parabolic B N J := map_conj_parabolic_of_mem hc
    have hconjh : MulAut.conj h₀ = MulAut.conj g * MulAut.conj (g⁻¹ * h₀) := by
      conv_lhs => rw [show h₀ = g * (g⁻¹ * h₀) by group]
      rw [map_mul]
    have hmul : (MulAut.conj g * MulAut.conj (g⁻¹ * h₀)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.conj (g⁻¹ * h₀)).toMonoidHom := by
      ext x; rfl
    have hmap_eq : B.map (MulAut.conj h₀).toMonoidHom =
        (B.map (MulAut.conj (g⁻¹ * h₀)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [hconjh, hmul, Subgroup.map_map]
    rw [hmap_eq, hP]
    exact Subgroup.map_mono ((Subgroup.map_mono (h.le_parabolic hJ)).trans hconjc.le)
  exact Or.inr ⟨P, hPne, hPmap, hBh₀, hBg⟩

private lemma eqvGen_of_mem_dc {Γ : Type*} [Group Γ] (h : IsBNPair B N S) (φ : Γ →* MulAut G)
    (hB : ∀ γ, B.map (φ γ).toMonoidHom = B)
    (hS : ∀ s ∈ S, (⨆ γ, (parabolic B N {s}).map (φ γ).toMonoidHom) ≠ ⊤) :
    ∀ n, ∀ (w : WeylGroup B N) (g : G), wordLength S w = n → g ∈ dc B N w →
      (∀ γ, g⁻¹ * φ γ g ∈ B) → Relation.EqvGen (InvariantLink B φ) 1 g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w g hlen hmem hfix
    rcases eq_or_ne w 1 with rfl | hw1
    · exact Relation.EqvGen.rel _ _ (Or.inl (by simpa using mem_dc_one.1 hmem))
    · obtain ⟨s, hs, hdesc⟩ :=
        exists_right_descent h.bnCore.mul_self_eq_one (h.mem_closure w) hw1
      obtain ⟨J, hJ, hsJ, hPJne, hPJmap⟩ := exists_invariant_parabolic h φ hS hs
      obtain ⟨w₁, hw₁mem, hw₁add, hlt_w⟩ :=
        exists_minimal_coset_descent h hJ hs hsJ hdesc
      have hlt : wordLength S w₁ < n := by rw [← hlen]; exact hlt_w
      obtain ⟨h₀, hh₀, hh₀g, hh₀fix⟩ :=
        exists_fixed_mem_dc h φ hB hJ hPJmap hw₁add hw₁mem hmem hfix
      have hrec := ih (wordLength S w₁) hlt w₁ h₀ rfl hh₀ hh₀fix
      exact Relation.EqvGen.trans _ _ _ hrec (Relation.EqvGen.rel _ _
        (invariantLink_of_fixed h φ hJ hPJne hPJmap hfix hh₀g))

theorem eqvGen_invariantLink {Γ : Type*} [Group Γ] (h : IsBNPair B N S) (φ : Γ →* MulAut G)
    (hB : ∀ γ, B.map (φ γ).toMonoidHom = B)
    (hS : ∀ s ∈ S, (⨆ γ, (parabolic B N {s}).map (φ γ).toMonoidHom) ≠ ⊤)
    {g : G} (hg : ∀ γ, g⁻¹ * φ γ g ∈ B) : Relation.EqvGen (InvariantLink B φ) 1 g := by
  obtain ⟨w, hw⟩ := h.exists_mem_dc g
  exact eqvGen_of_mem_dc h φ hB hS (wordLength S w) w g rfl hw hg

end IsBNPair

end CFSG.GroupTheory.TitsSystem
