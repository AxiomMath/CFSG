module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private lemma relIndex_inf_map_conj {P C : Subgroup G} {g : G} (hg : g ∈ P) :
    (P ⊓ C.map (MulAut.conj g).toMonoidHom).relIndex (C.map (MulAut.conj g).toMonoidHom) =
      (P ⊓ C).relIndex C := by
  have hP : P.map (MulAut.conj g).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
  calc (P ⊓ C.map (MulAut.conj g).toMonoidHom).relIndex (C.map (MulAut.conj g).toMonoidHom)
      = (P.map (MulAut.conj g).toMonoidHom ⊓ C.map (MulAut.conj g).toMonoidHom).relIndex
          (C.map (MulAut.conj g).toMonoidHom) := by rw [hP]
    _ = ((P ⊓ C).map (MulAut.conj g).toMonoidHom).relIndex (C.map (MulAut.conj g).toMonoidHom) := by
        rw [map_inf_eq P C (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    _ = (P ⊓ C).relIndex C :=
        relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _
          (MulAut.conj g).injective

theorem smallRankPoint_of_mem_plane (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {b : G} (hb : b ∈ zpowers x ⊔ zpowers z)
    (hbz : b ∉ zpowers z) : SmallRankPoint P M b := by
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  have hbP : b ∈ (P : Subgroup G) := hB.isIsolatedPlane.1 hb
  have hb3 : b ^ 3 = 1 := hB.isElemAbelian.2 b hb
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
  obtain ⟨g, hg, hgx⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx hz hb hbz
  have hgP : g ∈ (P : Subgroup G) := hg.1
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({b} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom :=
    calc centralizer ({b} : Set G)
        = centralizer ((zpowers b : Subgroup G) : Set G) := hcz b
      _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [hgx]
      _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        (CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism _ _).symm
      _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]
  refine ⟨hbP, hb1, hb3, ?_, ?_⟩
  ·
    intro hle
    apply hx.not_centralizer_le
    intro c hc
    have hcM : g * c * g⁻¹ ∈ M := hle (by rw [hC]; exact ⟨c, hc, rfl⟩)
    have hgM : g ∈ M := hPM hgP
    have hc' := M.mul_mem (M.mul_mem (M.inv_mem hgM) hcM) hgM
    simpa [mul_assoc] using hc'
  ·
    have hrel := hx.sylow_centralizer
    rw [hC]
    show ¬ 3 ∣ ((P : Subgroup G) ⊓ (centralizer ({x} : Set G)).map
      (MulAut.conj g).toMonoidHom).relIndex ((centralizer ({x} : Set G)).map
        (MulAut.conj g).toMonoidHom)
    rw [relIndex_inf_map_conj hgP]
    exact hrel

theorem exists_mul_mem_centralizer_of_coprime {Q : Subgroup G} {b k : G} (hb : b ^ 3 = 1)
    (hbQ : b ∈ normalizer (Q : Set G)) (hQ : Nat.Coprime 3 (Nat.card Q))
    (hc : b * k * b⁻¹ * k⁻¹ ∈ Q) : ∃ q ∈ Q, q * k ∈ centralizer ({b} : Set G) := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let f : Function.End Q := fun q =>
    ⟨b * q * b⁻¹ * (b * k * b⁻¹ * k⁻¹), Q.mul_mem ((mem_normalizer_iff.mp hbQ q).mp q.2) hc⟩
  have hfk : ∀ q : Q, ((f q : Q) : G) * k = b * (q * k) * b⁻¹ := fun q => by
    simp only [f]
    group
  have hb3 : b * b * b = 1 := by rw [← pow_three']; exact hb
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    funext q
    apply Subtype.ext
    show ((f (f (f q)) : Q) : G) = (q : G)
    refine mul_right_cancel (b := k) ?_
    calc ((f (f (f q)) : Q) : G) * k
        = b * (b * (b * (q * k) * b⁻¹) * b⁻¹) * b⁻¹ := by rw [hfk, hfk, hfk]
      _ = (b * b * b) * (q * k) * (b * b * b)⁻¹ := by group
      _ = q * k := by rw [hb3]; simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hne : Nonempty (Function.fixedPoints f) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : Fintype.card (Function.fixedPoints f) = 0 := Fintype.card_eq_zero
    rw [h0, Nat.modEq_zero_iff_dvd, ← Nat.card_eq_fintype_card] at hmod
    exact absurd (hQ.eq_one_of_dvd hmod) (by norm_num)
  obtain ⟨⟨q, hq⟩⟩ := hne
  refine ⟨q, q.2, ?_⟩
  have hfix : (f q : Q) = q := hq
  have h1 : b * (q * k) * b⁻¹ = q * k := by rw [← hfk, hfix]
  rw [mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
