module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10T_pocket_dichotomy [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {s : G} (hs : s ∈ S) :
    ((∀ x ∈ K1, s * x * s⁻¹ ∈ K1) ∧ ∀ x ∈ K2, s * x * s⁻¹ ∈ K2) ∨
      ((∀ x ∈ K1, s * x * s⁻¹ ∈ K2) ∧ ∀ x ∈ K2, s * x * s⁻¹ ∈ K1) := by
  obtain ⟨hpsp, -, -, -, hN, -⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨K1', K2', -, -, _, huniq, -, -, -, -⟩ := hP5 G L hpsp z hctx.toSec10Z.pocket
  have hsN : s ∈ normalizer (L : Set G) := hN hs
  have hsz : s * z = z * s := hctx.central s hs
  have hzconj : s⁻¹ * z * s = z := by
    calc s⁻¹ * z * s = s⁻¹ * (z * s) := by rw [mul_assoc]
      _ = s⁻¹ * (s * z) := by rw [← hsz]
      _ = (s⁻¹ * s) * z := by rw [← mul_assoc]
      _ = z := by rw [inv_mul_cancel, one_mul]
  have hLconj : CFSG.conjugate L s = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hsN)
  have hp1 : Sl23PocketIn L z (CFSG.conjugate K1 s) := by
    have h := hctx.pocket1.conjugate s
    rwa [hLconj, hzconj] at h
  have hp2 : Sl23PocketIn L z (CFSG.conjugate K2 s) := by
    have h := hctx.pocket2.conjugate s
    rwa [hLconj, hzconj] at h
  have hcase : (K1 = K1' ∧ K2 = K2') ∨ (K1 = K2' ∧ K2 = K1') := by
    rcases huniq K1 hctx.pocket1 with h1 | h1 <;> rcases huniq K2 hctx.pocket2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hctx.ne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hctx.ne
  have huniq' : ∀ K : Subgroup G, Sl23PocketIn L z K → K = K1 ∨ K = K2 := by
    intro K hK
    rcases huniq K hK with h | h
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h.trans h1.symm)
      · exact Or.inr (h.trans h2.symm)
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (h.trans h2.symm)
      · exact Or.inl (h.trans h1.symm)
  have hphi1 : CFSG.conjugate K1 s = K1 ∨ CFSG.conjugate K1 s = K2 := huniq' _ hp1
  have hphi2 : CFSG.conjugate K2 s = K1 ∨ CFSG.conjugate K2 s = K2 := huniq' _ hp2
  have hinj : Function.Injective (fun K : Subgroup G => CFSG.conjugate K s) :=
    Subgroup.map_injective (f := (MulAut.conj s⁻¹).toMonoidHom) (MulAut.conj s⁻¹).injective
  have hgoal : (CFSG.conjugate K1 s = K1 ∧ CFSG.conjugate K2 s = K2) ∨
      (CFSG.conjugate K1 s = K2 ∧ CFSG.conjugate K2 s = K1) := by
    rcases hphi1 with h1 | h1
    · by_cases h2 : CFSG.conjugate K2 s = K1
      · exact absurd (hinj (h1.trans h2.symm)) hctx.ne
      · exact Or.inl ⟨h1, hphi2.resolve_left h2⟩
    · by_cases h2 : CFSG.conjugate K2 s = K2
      · exact absurd (hinj (h1.trans h2.symm)) hctx.ne
      · exact Or.inr ⟨h1, hphi2.resolve_right h2⟩
  rcases hgoal with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨fun x hx => mem_conjugate_iff'.mp (h1.symm ▸ hx),
      fun x hx => mem_conjugate_iff'.mp (h2.symm ▸ hx)⟩
  · exact Or.inr ⟨fun x hx => mem_conjugate_iff'.mp (h2.symm ▸ hx),
      fun x hx => mem_conjugate_iff'.mp (h1.symm ▸ hx)⟩

end CFSG.OddStandard.SmallF3.Omega
