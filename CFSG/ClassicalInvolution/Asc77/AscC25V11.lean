module

public import CFSG.ClassicalInvolution.Asc77.AscC25V10
public import CFSG.ClassicalInvolution.Asc77.AscC25V1
public import CFSG.ClassicalInvolution.Asc77.AscC25V9
public import CFSG.ClassicalInvolution.Asc77.AscT7U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fieldChar_ne_one_of_swap (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a : G}
    (ha2 : a * a = 1) (hF : IsFAut R' a) {c : G} (hca : c * a = a * c) (hcz : c * z = z * c)
    (hcK : conjSub c K' = K) (haK : a ∈ Subgroup.normalizer (K : Set G)) :
    fieldChar hp hq e ⟨a, haK⟩ ≠ 1 := by
  have hFc : IsFAut (conjSub c R') (c * a * c⁻¹) := T7U.isFAut_conjSub hF c
  have hcac : c * a * c⁻¹ = a := by rw [hca]; group
  rw [hcac] at hFc
  have hRK : conjSub c R' ≤ K := by
    rw [← hcK]
    exact conjSub_mono h.hR'syl.1
  have hq' : IsQuatSub (conjSub c R') := T7U.isQuatSub_conjSub h.hqR' c
  have hz' : IsUniqueInvolution (conjSub c R') z := by
    have := h.hzR'.conj c
    have hczc : c * z * c⁻¹ = z := by rw [hcz]; group
    rwa [hczc] at this
  exact fieldChar_ne_one_of_isFAut hp hq e hRK hq' hz' hFc ha2 haK

theorem false_of_mix_fusion (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hχ : fieldChar hp hq e ⟨a, haK⟩ = 1)
    (hfus : ∀ x : G, x⁻¹ * a * x ∈ Subgroup.centralizer ({z} : Set G) →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), x⁻¹ * a * x = c⁻¹ * a * c) : False := by
  classical
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht'z : t' * z = z * t' := t'_comm_z h
  have ht'C : t' ∈ C := (hmemC t').mpr ht'z
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (h.hyp.hzS s hs)
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
  let ϕ₀ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    MonoidHom.mk' (fun n => χ ⟨n, hmemN n⟩ * χ ⟨t' * n * t', (hconjN n n.2).2⟩) (by
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
      rw [e1, e2, map_mul, map_mul]
      exact mul_mul_mul_comm _ _ _ _)
  have hϕ₀ : ∀ (n : G) (hn : n ∈ N),
      ϕ₀ ⟨n, hn⟩ = χ ⟨n, hn.2⟩ * χ ⟨t' * n * t', (hconjN n hn).2⟩ := fun n hn => rfl
  have hinv : ∀ (n : G) (hn : n ∈ N), ϕ₀ ⟨t' * n * t', hconjN n hn⟩ = ϕ₀ ⟨n, hn⟩ := by
    intro n hn
    have e3 : t' * (t' * n * t') * t' = n := by
      calc t' * (t' * n * t') * t' = (t' * t') * n * (t' * t') := by group
        _ = n := by rw [h.ht'2]; group
    have e4 : (⟨t' * (t' * n * t') * t', (hconjN _ (hconjN n hn)).2⟩ :
        Subgroup.normalizer (K : Set G)) = ⟨n, hn.2⟩ := Subtype.ext e3
    rw [hϕ₀ (t' * n * t') (hconjN n hn), hϕ₀ n hn, e4, mul_comm]
  have hNC : N ≤ C := inf_le_left
  have hcov : ∀ g ∈ C, g ∈ N ∨ g * t' ∈ N := by
    intro g hg
    have hgz : g * z = z * g := (hmemC g).mp hg
    rcases cz_cover h hgz with h1 | h1
    · exact Or.inl ⟨hg, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hg ht'C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  obtain ⟨ϕ, hϕ⟩ := exists_hom_extension_of_index_two C N hNC t' h.ht'2 hcov hconjN ϕ₀ hinv
  have haC : a ∈ C := hSC haS
  have haN : a ∈ N := ⟨haC, haK⟩
  have hfus' : ∀ (x : G) (hx : x⁻¹ * a * x ∈ C), ϕ ⟨x⁻¹ * a * x, hx⟩ = ϕ ⟨a, haC⟩ := by
    intro x hx
    obtain ⟨c, hcC, hxc⟩ := hfus x hx
    have e5 : (⟨x⁻¹ * a * x, hx⟩ : C) = (⟨c, hcC⟩ : C)⁻¹ * ⟨a, haC⟩ * ⟨c, hcC⟩ :=
      Subtype.ext hxc
    rw [e5, map_mul, map_mul, map_inv]
    calc (ϕ ⟨c, hcC⟩)⁻¹ * ϕ ⟨a, haC⟩ * ϕ ⟨c, hcC⟩
        = ϕ ⟨a, haC⟩ * ((ϕ ⟨c, hcC⟩)⁻¹ * ϕ ⟨c, hcC⟩) := by
          rw [mul_comm ((ϕ ⟨c, hcC⟩)⁻¹), mul_assoc]
      _ = ϕ ⟨a, haC⟩ := by rw [inv_mul_cancel, mul_one]
  have hne : ϕ ⟨a, haC⟩ ≠ 1 := by
    have h1 : ϕ ⟨a, haC⟩ = ϕ₀ ⟨a, haN⟩ := hϕ a haN
    rw [h1, hϕ₀ a haN, hχ, one_mul]
    have hFa : IsFAut R (t' * a * t') := by
      have := T7U.isFAut_conjSub hF t'
      rw [h.ht'R', h.ht'inv] at this
      exact this
    have ha2' : (t' * a * t') * (t' * a * t') = 1 := by
      calc (t' * a * t') * (t' * a * t') = t' * a * (t' * t') * a * t' := by group
        _ = t' * (a * a) * t' := by rw [h.ht'2]; group
        _ = 1 := by rw [ha2, mul_one]; exact h.ht'2
    exact fieldChar_ne_one_of_isFAut hp hq e h.hRsyl.1 h.hqR h.hzR hFa ha2' (hconjN a haN).2
  exact false_of_transfer_fusion (exists_noncomm_of_swap h) S C hSC ϕ a haC ha2 hfus' hne

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
