module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

theorem mem_normalizer_iff_map_conj_eq {K : Subgroup G} {h : G} :
    h ∈ normalizer (K : Set G) ↔ K.map (MulAut.conj h).toMonoidHom = K := by
  constructor
  · intro hh
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hh y).1 hy
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, by group⟩
      refine (Subgroup.mem_normalizer_iff.1 hh (h⁻¹ * x * h)).2 ?_
      have : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rw [this]
      exact hx
  · intro hmap
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hmap] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by
        have h1 : h * z * h⁻¹ = h * y * h⁻¹ := hzy
        simpa using h1
      rwa [this] at hz

theorem normal_of_component [Finite G] {L K X : Subgroup G} {t : G} {b n : ℕ} (hbn : b < n)
    (hK : IsCompIn K X)
    (htX : t ∈ X) (htK : t ∈ centralizer (K : Set G)) (ht2 : t * t = 1)
    (hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hΛs : Group.IsSolvable ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)))
    (hΛr : ∀ E : Subgroup G, E ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) →
      (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ b)
    (hrank : InvolutionFixesElem ↥K n) : (K.subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK.1]
  intro h hh
  have hKq := hK.isQuasisimple
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hNK
  set N : Subgroup G := K.map (MulAut.conj h).toMonoidHom with hNdef
  have hNcomp : IsCompIn N X := hK.map_conj hh
  have hcardN : Nat.card N = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hNcentK : ∀ a ∈ N, ∀ b ∈ K, b * a = a * b := fun a ha b hb =>
    (hNcomp.commute_of_ne hK hNK a ha b hb).symm
  by_cases htN : t ∈ normalizer (N : Set G)
  · exact false_of_second_copy hbn ht2 hCt hKq hΛs hΛr hrank
      (fun a ha => mem_centralizer_iff.2 (hNcentK a ha))
      (Subgroup.equivMapOfInjective K (MulAut.conj h).toMonoidHom (MulAut.conj h).injective).symm
      htN
  ·
    set N' : Subgroup G := N.map (MulAut.conj t).toMonoidHom with hN'def
    have hN'comp : IsCompIn N' X := hNcomp.map_conj htX
    have hN'N : N' ≠ N := fun heq => htN (mem_normalizer_iff_map_conj_eq.2 heq)
    have hcardN' : Nat.card N' = Nat.card N :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have htcomm : ∀ k ∈ K, t * k * t⁻¹ = k := fun k hk => by
      have := mem_centralizer_iff.1 htK k hk
      calc t * k * t⁻¹ = (k * t) * t⁻¹ := by rw [this]
        _ = k := by group
    have hN'K : N' ≠ K := by
      intro heq
      apply hNK
      have hle : N ≤ K := by
        intro n hn
        have h1 : t * n * t⁻¹ ∈ K := by
          rw [← heq]
          exact ⟨n, hn, rfl⟩
        have h6 : n = t * n * t⁻¹ := by
          have := htcomm _ h1
          calc n = (t * t) * n * (t * t)⁻¹ := by rw [ht2]; group
            _ = t * (t * n * t⁻¹) * t⁻¹ := by group
            _ = t * n * t⁻¹ := this
        rw [h6]
        exact h1
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hNN' : ∀ a ∈ N, ∀ b ∈ N', a * b = b * a := fun a ha b hb =>
      hNcomp.commute_of_ne hN'comp hN'N.symm a ha b hb
    have hN'cent : ∀ a ∈ N', ∀ b ∈ K, b * a = a * b := fun a ha b hb =>
      (hN'comp.commute_of_ne hK hN'K a ha b hb).symm
    have hmemN' : ∀ n : ↥N, t * (n : G) * t⁻¹ ∈ N' := fun n => ⟨n, n.2, rfl⟩
    let φ : ↥N →* G :=
      { toFun := fun n => (n : G) * (t * (n : G) * t⁻¹)
        map_one' := by simp
        map_mul' := by
          intro n m
          have hc := hNN' (m : G) m.2 _ (hmemN' n)
          show ((n * m : ↥N) : G) * (t * ((n * m : ↥N) : G) * t⁻¹) =
            ((n : G) * (t * (n : G) * t⁻¹)) * ((m : G) * (t * (m : G) * t⁻¹))
          calc ((n * m : ↥N) : G) * (t * ((n * m : ↥N) : G) * t⁻¹)
              = (n : G) * (m * (t * (n : G) * t⁻¹)) * (t * (m : G) * t⁻¹) := by
                simp only [Subgroup.coe_mul]; group
            _ = (n : G) * ((t * (n : G) * t⁻¹) * m) * (t * (m : G) * t⁻¹) := by rw [hc]
            _ = _ := by group }
    have hφ : ∀ n : ↥N, φ n = (n : G) * (t * (n : G) * t⁻¹) := fun n => rfl
    have hDΛ : φ.range ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) := by
      rintro _ ⟨n, rfl⟩
      rw [hφ]
      have hn' := hmemN' n
      refine ⟨hCt (mem_centralizer_singleton_iff.2 ?_), mem_centralizer_iff.2 ?_⟩
      ·
        have hc := hNN' (n : G) n.2 _ hn'
        have h1 : t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹ =
            (t * (n : G) * t⁻¹) * (n : G) := by
          calc t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹
              = (t * (n : G) * t⁻¹) * ((t * t) * (n : G) * (t * t)⁻¹) := by group
            _ = (t * (n : G) * t⁻¹) * (n : G) := by rw [ht2]; group
        have h2 : ((n : G) * (t * (n : G) * t⁻¹)) * t =
            t * ((n : G) * (t * (n : G) * t⁻¹)) := by
          have h3 : t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹ =
              (n : G) * (t * (n : G) * t⁻¹) := by rw [h1, ← hc]
          calc ((n : G) * (t * (n : G) * t⁻¹)) * t
              = (t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹) * t := by rw [h3]
            _ = t * ((n : G) * (t * (n : G) * t⁻¹)) := by group
        exact h2
      · intro k hk
        calc k * ((n : G) * (t * (n : G) * t⁻¹))
            = (k * (n : G)) * (t * (n : G) * t⁻¹) := by group
          _ = ((n : G) * k) * (t * (n : G) * t⁻¹) := by rw [hNcentK n n.2 k hk]
          _ = (n : G) * (k * (t * (n : G) * t⁻¹)) := by group
          _ = (n : G) * ((t * (n : G) * t⁻¹) * k) := by rw [hN'cent _ hn' k hk]
          _ = ((n : G) * (t * (n : G) * t⁻¹)) * k := by group
    have hDsolv : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDΛ)
        (Subgroup.inclusion_injective hDΛ)
    have hNperf : Group.IsPerfect ↥N := by
      have := CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective K (MulAut.conj h).toMonoidHom (MulAut.conj h).injective) hKq
      exact this.1
    have hDperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hDnontriv : Nontrivial ↥φ.range := by
      by_contra hsub
      rw [not_nontrivial_iff_subsingleton] at hsub
      apply hN'N
      have hle : N' ≤ N := by
        rintro _ ⟨n, hn, rfl⟩
        have h1 : φ ⟨n, hn⟩ = 1 := by
          have := hsub.elim ⟨φ ⟨n, hn⟩, ⟨_, rfl⟩⟩ 1
          exact congrArg Subtype.val this
        rw [hφ] at h1
        have h2 : t * n * t⁻¹ = n⁻¹ := by
          have := congrArg (fun z => n⁻¹ * z) h1
          simpa [mul_assoc] using this
        show t * n * t⁻¹ ∈ N
        rw [h2]
        exact N.inv_mem hn
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
    exact Group.IsPerfect.not_isSolvable ↥φ.range hDsolv

end CFSG.EvenSporadicStandard.Solomon78
