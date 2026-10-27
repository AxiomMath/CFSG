module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec8Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Base G t L S z g B → S ⊓ L = Subgroup.closure (conjClassIn L z ∩ (S : Set G))

private theorem sec8l85_conj_comm {G : Type} [Group G] {t z s g : G} {S : Subgroup G}
    (hSt : S ≤ centralizer ({t} : Set G)) (hcentral : ∀ s ∈ S, s * z = z * s)
    (htz : g⁻¹ * t * g = t * z) (hs : s ∈ S) :
    (g * s * g⁻¹) * t = t * (g * s * g⁻¹) := by
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hSt hs)
  have hsz : s * z = z * s := hcentral s hs
  have ht' : g * (t * z) * g⁻¹ = t := by rw [← htz]; group
  calc (g * s * g⁻¹) * t
      = (g * s * g⁻¹) * (g * (t * z) * g⁻¹) := by rw [ht']
    _ = g * (s * (t * z)) * g⁻¹ := by group
    _ = g * ((s * t) * z) * g⁻¹ := by group
    _ = g * ((t * s) * z) * g⁻¹ := by rw [hst]
    _ = g * (t * (s * z)) * g⁻¹ := by group
    _ = g * (t * (z * s)) * g⁻¹ := by rw [hsz]
    _ = g * ((t * z) * s) * g⁻¹ := by group
    _ = (g * (t * z) * g⁻¹) * (g * s * g⁻¹) := by group
    _ = t * (g * s * g⁻¹) := by rw [ht']

theorem asc82Lemma85_of (h36 : Asc82Lemma36) (h84 : Asc82Lemma84Z) (hGen : Asc82Sec8Gen) :
    Asc82Lemma85 := by
  intro G _ _ t L S z g B hctx
  have hBase : Sec8Base G t L S z g B := hctx.toSec8Base
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS
  have hzL : z ∈ L := by
    obtain ⟨K, hK⟩ := hctx.pocket.2
    exact (hK.2.1 hK.1).1
  have hsub : conjClassIn L z ⊆ L := by
    rintro y ⟨l', hl', rfl⟩
    exact L.mul_mem (L.mul_mem hl' hzL) (L.inv_mem hl')
  have hle : S ⊓ L ≤ S ⊓ CFSG.conjugate L g := by
    rw [hGen G t L S z g B hBase, Subgroup.closure_le]
    rintro x ⟨hxclass, hxS⟩
    rcases hxclass with ⟨l, _, rfl⟩
    refine ⟨hxS, ?_⟩
    refine mem_conjugate_iff'.mpr ?_
    have hcent : g * (l * z * l⁻¹) * g⁻¹ ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (sec8l85_conj_comm hctx.sylow.1 hctx.central hctx.tz hxS)
    have hconj : IsConj z (g * (l * z * l⁻¹) * g⁻¹) :=
      isConj_iff.mpr ⟨g * l, by group⟩
    have hmem : g * (l * z * l⁻¹) * g⁻¹ ∈ conjClassIn L z := by
      rw [← h84 G t L S z g B hctx]
      exact ⟨hconj, hcent⟩
    exact hsub hmem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  let S₁ : Subgroup G := S.map (MulAut.conj g).toMonoidHom
  have hS₁p : IsPGroup 2 S₁ := by
    change IsPGroup 2 (S.map (MulAut.conj g).toMonoidHom)
    exact hctx.sylow.2.1.map (MulAut.conj g).toMonoidHom
  have hS₁c : S₁ ≤ centralizer ({t} : Set G) := by
    rintro y ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [MulAut.conj_apply] using sec8l85_conj_comm hctx.sylow.1 hctx.central hctx.tz hs
  obtain ⟨S'', hS''syl, hS₁S''⟩ := exists_isSylow2Of_ge hS₁p hS₁c
  obtain ⟨c, hcC, hc⟩ := hctx.sylow.exists_conj_mem hS''syl
  have hcC' : c⁻¹ ∈ centralizer ({t} : Set G) := inv_mem hcC
  have hcard1 : Nat.card ↥(S ⊓ CFSG.conjugate L g) ≤ Nat.card ↥(S'' ⊓ L) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(S ⊓ CFSG.conjugate L g) =>
        (⟨g * (x : G) * g⁻¹, ⟨?_, ?_⟩⟩ : ↥(S'' ⊓ L))) ?_
    · exact hS₁S'' (Subgroup.mem_map.mpr ⟨(x : G), x.2.1, rfl⟩)
    · exact mem_conjugate_iff'.mp x.2.2
    · intro x y hxy
      apply Subtype.ext
      have h : g⁻¹ * (g * (x : G) * g⁻¹) * g = g⁻¹ * (g * (y : G) * g⁻¹) * g :=
        congrArg (fun v : G => g⁻¹ * v * g) (congrArg Subtype.val hxy)
      have hx : g⁻¹ * (g * (x : G) * g⁻¹) * g = (x : G) := by group
      have hy : g⁻¹ * (g * (y : G) * g⁻¹) * g = (y : G) := by group
      rw [hx, hy] at h
      exact h
  have hcard3 : Nat.card ↥(S'' ⊓ L) ≤ Nat.card ↥(S ⊓ L) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(S'' ⊓ L) => (⟨c⁻¹ * (x : G) * c, ⟨?_, ?_⟩⟩ : ↥(S ⊓ L))) ?_
    · exact (hc (x : G)).mp x.2.1
    · have hxconj : (x : G) ∈ CFSG.conjugate L c⁻¹ := by
        rw [conjugate_eq_self_of_lemma36 h36 hS c⁻¹ hcC']
        exact x.2.2
      simpa using mem_conjugate_iff'.mp hxconj
    · intro x y hxy
      apply Subtype.ext
      have h : c * (c⁻¹ * (x : G) * c) * c⁻¹ = c * (c⁻¹ * (y : G) * c) * c⁻¹ :=
        congrArg (fun v : G => c * v * c⁻¹) (congrArg Subtype.val hxy)
      have hx : c * (c⁻¹ * (x : G) * c) * c⁻¹ = (x : G) := by group
      have hy : c * (c⁻¹ * (y : G) * c) * c⁻¹ = (y : G) := by group
      rw [hx, hy] at h
      exact h
  exact le_trans hcard1 hcard3

end CFSG.OddStandard.SmallF3.Omega
