module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherParabolicData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Emb

variable {A : Type} [Group A] {K : Subgroup A} {H : Type} [Group H]

@[expose] def emb (e : ↥K ≃* H) : H →* A := K.subtype.comp e.symm.toMonoidHom

theorem emb_apply (e : ↥K ≃* H) (h : H) : emb e h = ((e.symm h : ↥K) : A) := rfl

theorem emb_e (e : ↥K ≃* H) (k : ↥K) : emb e (e k) = (k : A) := by
  simp [emb_apply]

theorem emb_injective (e : ↥K ≃* H) : Function.Injective (emb e) := by
  intro a b h
  exact e.symm.injective (Subtype.ext h)

theorem range_emb (e : ↥K ≃* H) : (emb e).range = K := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact (e.symm h).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, emb_e e ⟨x, hx⟩⟩

theorem map_comap_emb (e : ↥K ≃* H) {Q : Subgroup A} (hQ : Q ≤ K) :
    (Q.comap (emb e)).map (emb e) = Q := by
  rw [Subgroup.map_comap_eq, range_emb]
  exact inf_eq_right.mpr hQ

theorem isMaxParabolicP_map_emb [Finite H] (p : ℕ) [Fact p.Prime] (e : ↥K ≃* H) {M : Subgroup H}
    (hM : M ∈ maximalParabolics H p) : IsMaxParabolicP p K (M.map (emb e)) := by
  obtain ⟨hcoatom, B₀, ⟨T, hT⟩, hB₀M⟩ := hM
  have hinj := emb_injective e
  have hPar : IsParabolicP p K (M.map (emb e)) := by
    refine ⟨?_, (T : Subgroup H).map (emb e), ?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact (e.symm m).2
    · have hs : Function.Surjective (e.symm.toMonoidHom : H →* ↥K) := e.symm.surjective
      refine ⟨Sylow.mapSurjective hs T, ?_⟩
      rw [Sylow.coe_mapSurjective, Subgroup.map_map]
      rfl
    · intro a ha
      obtain ⟨haK, haN⟩ := ha
      set h : H := e ⟨a, haK⟩ with hh
      have hah : emb e h = a := emb_e e ⟨a, haK⟩
      have hhN : h ∈ normalizer ((T : Subgroup H) : Set H) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have h1 : x ∈ (T : Subgroup H) ↔ emb e x ∈ (T : Subgroup H).map (emb e) :=
          (Subgroup.mem_map_iff_mem hinj).symm
        have h2 : h * x * h⁻¹ ∈ (T : Subgroup H) ↔
            emb e (h * x * h⁻¹) ∈ (T : Subgroup H).map (emb e) :=
          (Subgroup.mem_map_iff_mem hinj).symm
        rw [h1, h2, map_mul, map_mul, map_inv, hah]
        exact Subgroup.mem_normalizer_iff.mp haN (emb e x)
      refine ⟨h, hB₀M (hT ▸ hhN), hah⟩
  refine ⟨hPar, ?_, ?_⟩
  · intro hK
    apply hcoatom.1
    apply Subgroup.map_injective hinj
    rw [hK, ← MonoidHom.range_eq_map, range_emb]
  · intro Q hQ hQK hle
    obtain ⟨hQle, -⟩ := hQ
    have hQ' : M ≤ Q.comap (emb e) := Subgroup.map_le_iff_le_comap.mp hle
    have hne : Q.comap (emb e) ≠ ⊤ := by
      intro htop
      apply hQK
      rw [← map_comap_emb e hQle, htop, ← MonoidHom.range_eq_map, range_emb]
    have heq : Q.comap (emb e) = M := by
      rcases hcoatom.le_iff.mp hQ' with h | h
      · exact absurd h hne
      · exact h
    rw [← map_comap_emb e hQle, heq]

end Emb

section OpLemmas

variable {A : Type} [Group A]

theorem isPGroup_Op (p : ℕ) (L : Subgroup A) : IsPGroup p ↥(Op p L) :=
  (pCore_isPGroup (p := p) (G := ↥L)).map L.subtype

theorem le_normalizer_Op (p : ℕ) (L : Subgroup A) : L ≤ normalizer (Op p L : Set A) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ L, ∀ x ∈ Op p L, g * x * g⁻¹ ∈ Op p L := by
    intro g hg x hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, (pCore_normal (p := p) (G := ↥L)).conj_mem n hn ⟨g, hg⟩, by simp⟩
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (L.inv_mem hg) _ hx

theorem le_Op_of_normal' {p : ℕ} {L X : Subgroup A} (hXL : X ≤ L)
    (hn : L ≤ normalizer (X : Set A)) (hX : IsPGroup p ↥X) : X ≤ Op p L := by
  have hnorm : (X.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hn
  have hpg : IsPGroup p ↥(X.subgroupOf L) :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXL).injective
  have h1 : X.subgroupOf L ≤ pCore p ↥L := le_sSup ⟨hnorm, hpg⟩
  have h2 : (X.subgroupOf L).map L.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXL
  rw [← h2]
  exact Subgroup.map_mono h1

theorem Op_le' (p : ℕ) (L : Subgroup A) : Op p L ≤ L := Subgroup.map_subtype_le _

end OpLemmas

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
