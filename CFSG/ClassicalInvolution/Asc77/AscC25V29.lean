module

public import CFSG.ClassicalInvolution.Asc77.AscC25V27
public import CFSG.ClassicalInvolution.Asc77.AscC25V28
public import CFSG.ClassicalInvolution.Asc77.AscC25V7
public import CFSG.ClassicalInvolution.Asc77.AscT7U8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def GC25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → (∃ g : G, g * z * g⁻¹ = t') →
          (¬ ∃ y : G, y * z * y⁻¹ = t' * z) → a * t' = t' * a →
          ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
            (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (n : G)
            (hn : n ∈ Subgroup.normalizer (K : Set G)) (_ : n * z = z * n)
            (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G)),
              Odd (orderOf (fieldChar hp hq e ⟨n, hn⟩ * (fieldChar hp hq e ⟨t' * n * t', hn'⟩)⁻¹))

end Defs

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem false_of_ff_gc (h11 : C25_11 p f) (hgc : GC25 p f) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ : G} (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hFa' : IsFAut R' a) :
    False := by
  classical
  by_cases hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))
  · exact false_of_zStar_ff h11 hyp haS ha2 hFa hFa' hZ
  obtain ⟨t', g, h, hg, hnf, hat⟩ := exists_comm_swap_of_ff h11 hyp haS ha2 hFa hFa'
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK
  have hfix := fix_of_isFAut h haS hFa'
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.1
  have hσ : fieldChar hp hq e ⟨a, haK⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hRsyl.1 h.hqR h.hzR hFa ha2 haK
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht'z : t' * z = z * t' := t'_comm_z h
  have ht'C : t' ∈ C := (hmemC t').mpr ht'z
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (hyp.hzS s hs)
  set N : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN
  have hconjN : ∀ n ∈ N, t' * n * t' ∈ N := by
    intro n hn
    have hnz : n * z = z * n := (hmemC n).mp hn.1
    have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn.2
    have hnK' : conjSub n K' = K' := (cz_fix_iff h hnz).mp hnK
    have hK2 : conjSub (t' * n * t') K = K := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K h, hnK', conjSub_t'_K' h]
    exact ⟨C.mul_mem (C.mul_mem ht'C hn.1) ht'C, mem_normalizer_iff_conjSub_eq.mpr hK2⟩
  let χ := fieldChar hp hq e
  have hmemN : ∀ n : N, (n : G) ∈ Subgroup.normalizer (K : Set G) := fun n => n.2.2
  let δ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    MonoidHom.mk' (fun n => χ ⟨n, hmemN n⟩ * (χ ⟨t' * n * t', (hconjN n n.2).2⟩)⁻¹) (by
      intro n m
      have e1 : (⟨((n * m : N) : G), hmemN (n * m)⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨n, hmemN n⟩ * ⟨m, hmemN m⟩ := rfl
      have e2 : (⟨t' * ((n * m : N) : G) * t', (hconjN _ (n * m).2).2⟩ :
          Subgroup.normalizer (K : Set G)) = ⟨t' * n * t', (hconjN n n.2).2⟩ *
            ⟨t' * m * t', (hconjN m m.2).2⟩ := by
        apply Subtype.ext
        show t' * ((n : G) * m) * t' = (t' * n * t') * (t' * m * t')
        calc t' * ((n : G) * m) * t' = t' * n * (t' * t') * m * t' := by rw [h.ht'2]; group
          _ = (t' * n * t') * (t' * m * t') := by group
      rw [e1, e2, map_mul, map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  have hδ : ∀ (n : G) (hn : n ∈ N), δ ⟨n, hn⟩ =
      χ ⟨n, hn.2⟩ * (χ ⟨t' * n * t', (hconjN n hn).2⟩)⁻¹ := fun n hn => rfl
  let D : Subgroup (GaloisField p f ≃+* GaloisField p f) := δ.range
  let ϕ₀ : N →* ((GaloisField p f ≃+* GaloisField p f) ⧸ D) :=
    MonoidHom.mk' (fun n => (QuotientGroup.mk (χ ⟨n, hmemN n⟩) :
      (GaloisField p f ≃+* GaloisField p f) ⧸ D)) (by
      intro n m
      have e1 : (⟨((n * m : N) : G), hmemN (n * m)⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨n, hmemN n⟩ * ⟨m, hmemN m⟩ := rfl
      rw [e1, map_mul, QuotientGroup.mk_mul])
  have hϕ₀ : ∀ (n : G) (hn : n ∈ N),
      ϕ₀ ⟨n, hn⟩ = (QuotientGroup.mk (χ ⟨n, hn.2⟩) :
        (GaloisField p f ≃+* GaloisField p f) ⧸ D) := fun n hn => rfl
  have hinv : ∀ (n : G) (hn : n ∈ N), ϕ₀ ⟨t' * n * t', hconjN n hn⟩ = ϕ₀ ⟨n, hn⟩ := by
    intro n hn
    rw [hϕ₀ (t' * n * t') (hconjN n hn), hϕ₀ n hn, QuotientGroup.eq]
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [hδ n hn, mul_comm]
  have hNC : N ≤ C := inf_le_left
  have hcov : ∀ g ∈ C, g ∈ N ∨ g * t' ∈ N := by
    intro g hg
    have hgz : g * z = z * g := (hmemC g).mp hg
    rcases cz_cover h hgz with h1 | h1
    · exact Or.inl ⟨hg, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hg ht'C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  obtain ⟨ϕ, hϕ⟩ := exists_hom_extension_of_index_two C N hNC t' h.ht'2 hcov hconjN ϕ₀ hinv
  have haz : a * z = z * a := hyp.hzS a haS
  have haC : a ∈ C := (hmemC a).mpr haz
  have haN : a ∈ N := ⟨haC, haK⟩
  have hne : ϕ ⟨a, haC⟩ ≠ 1 := by
    intro h1
    have h2 : ϕ ⟨a, haC⟩ = ϕ₀ ⟨a, haN⟩ := hϕ a haN
    rw [h2, hϕ₀ a haN, QuotientGroup.eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hodd := hgc G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h ⟨g, hg⟩ hnf hat
      hp hq e n (hmemN n) ((hmemC n).mp n.2.1) (hconjN n n.2).2
    have hn' : χ ⟨n, hmemN n⟩ * (χ ⟨t' * (n : G) * t', (hconjN n n.2).2⟩)⁻¹ =
        χ ⟨a, haK⟩ := hn
    rw [hn'] at hodd
    have hsq : χ ⟨a, haK⟩ ^ 2 = 1 := by
      have h3 : (⟨a, haK⟩ : Subgroup.normalizer (K : Set G)) ^ 2 = 1 :=
        Subtype.ext (by rw [pow_two]; exact ha2)
      rw [← map_pow, h3, map_one]
    have hord : orderOf (χ ⟨a, haK⟩) = 2 := orderOf_eq_prime hsq hσ
    rw [hord] at hodd
    exact absurd hodd (by decide)
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hFa'
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hyz : y * z = z * y := comm_z_of_mem h.hzR' hyR'
  have hnc4 : ∀ g : G, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y)
      (by rw [conjSub_one]; exact h.hyp.hR'.2.1 hyR') hy4 hg
    simpa using this
  exact hne (hom_centralizer_apply_eq_one (exists_noncomm_of_swap h) ha2 haz hya hyz hy4' hnc4 ϕ)

theorem c25_16inv_of_gc (h11 : C25_11 p f) (hmix : Mix25 p f) (hgc : GC25 p f) :
    T7U.C25_16inv p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  rcases hmix G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' with hin | ⟨r, hrR, ha'2, hFa'⟩
  · obtain ⟨e, heS, he2, hFe, hFe'⟩ := exists_ff_of_inner h11 hyp haS ha2 hF' hin
    exact (false_of_ff_gc h11 hgc hyp heS he2 hFe hFe').elim
  · obtain ⟨t₀, h₀⟩ := T7T.exists_hyp25T hyp
    have ha'S : a * r ∈ (S : Subgroup G) := S.mul_mem haS (h₀.hRS hrR)
    have hF'a' : IsFAut R' (a * r) :=
      T7U.isFAut_mul_of_centralizes (fun x hx => h₀.hcomm r hrR x hx) hF'
    exact (false_of_ff_gc h11 hgc hyp ha'S ha'2 hFa' hF'a').elim

theorem c25_16invEven_of_gc (h11 : C25_11 p f) (hmix : Mix25 p f) (hgc : GC25 p f) :
    Even f → T7U.C25_16inv p f :=
  fun _ => c25_16inv_of_gc h11 hmix hgc

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
