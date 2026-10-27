module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AOm8Blk
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridgePlus
import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.Classical2 (orthDerived)

theorem NLAct.false_of_d4two_inner {Ω : Type} [Group Ω] [Finite Ω] {X J B D : Subgroup Ω}
    (h : NLAct 3 X J B D) (hB : IsElemAbelian 3 B) (hJ : catalogIs (PSimple 3 J) S9.isD4two)
    (hinn : ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (J : Set Ω),
      chevAut 3 J ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 J))
    (hr : 27 * Nat.card D ≤ Nat.card B) : False := by
  set S := PSimple 3 J
  set N := Subgroup.normalizer (J : Set Ω)
  set φ := chevAut 3 J
  set B' : Subgroup ↥N := B.subgroupOf N
  set P : Subgroup (MulAut S) := B'.map φ
  have hcard : Nat.card P * Nat.card D = Nat.card B := by
    have h1 : Nat.card P * Nat.card ↥(φ.ker ⊓ B') = Nat.card B' := by
      rw [← Subgroup.relIndex_ker φ (K := B'), Subgroup.relIndex_mul_card]
    have hker : φ.ker ⊓ B' = D.subgroupOf N := by
      ext ⟨g, hg⟩
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, B']
      exact ⟨fun ⟨h1, h2⟩ => (h.ker g h2 hg).1 h1,
        fun hD => ⟨(h.ker g (h.le hD) hg).2 hD, h.le hD⟩⟩
    rwa [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le.trans h.norm)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.norm).toEquiv] at h1
  have hZ := center_pSimple_eq_bot Nat.prime_three h.comp
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro s t hst
    have hc : t⁻¹ * s ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun g => by
      have h1 : s * g * s⁻¹ = t * g * t⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun β : MulAut S => β g) hst
      calc g * (t⁻¹ * s) = t⁻¹ * (t * g * t⁻¹) * s := by group
        _ = t⁻¹ * (s * g * s⁻¹) * s := by rw [h1]
        _ = t⁻¹ * s * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  have hfix : ∀ s : S, fixSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) :=
    fun s => by
      ext g
      rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
        Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hPinn : P ≤ (MulAut.conj : S →* MulAut S).range := by
    rintro _ ⟨⟨g, hgN⟩, hgB, rfl⟩
    exact hinn g (Subgroup.mem_subgroupOf.mp hgB) hgN
  set A : Subgroup S := P.comap MulAut.conj
  have hAcard : Nat.card A = Nat.card P := by
    rw [← Subgroup.map_comap_eq_self hPinn]
    exact Nat.card_congr (Subgroup.equivMapOfInjective A _ hconj).toEquiv
  have hAe : IsElemAbelian 3 A := ((hB.subgroupOf N).map φ).comap hconj
  have hlay : ∀ s ∈ A, s ≠ 1 → GLAPLayer 3 (Subgroup.centralizer ({s} : Set S)) = ⊥ := by
    intro s hs hs1
    obtain ⟨⟨g, hgN⟩, hgB, hgs⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hs)
    have hgB' : g ∈ B := Subgroup.mem_subgroupOf.mp hgB
    have hgD : g ∉ D := fun hgD => hs1 (hconj (by
      rw [map_one, ← hgs]
      exact (h.ker g hgB' hgN).2 hgD))
    have h1 := h.layer g hgB' hgD hgN
    rwa [show chevAut 3 J ⟨g, hgN⟩ = MulAut.conj s from hgs, hfix s] at h1
  obtain ⟨q, hv, hq, ⟨e₀⟩⟩ := CatB.lieIndex_isD4two hJ
  obtain ⟨F, _, _, _, V, _, _, _, Q, hF, hQ, hdim, -, hmod⟩ :=
    S172C.exists_omegaPlus_model (n := 4) (k := 1) le_rfl le_rfl
  have hcat : catalogIs S (isOmPA 4 (2 ^ 1)) := ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, Or.inl (by
    change 4 = 4 ∧ q.card = 2 ^ 1
    exact ⟨rfl, by rw [hq]; norm_num⟩), ⟨e₀⟩⟩
  obtain ⟨ψ⟩ := hmod S hcat
  haveI : Finite ↥(orthDerived Q) := Finite.of_equiv _ ψ.toEquiv
  have hcent : ∀ s : S, (Subgroup.centralizer ({s} : Set S)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ s} : Set ↥(orthDerived Q)) := fun s => by
    ext t
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    refine ⟨?_, fun ht => ⟨ψ.symm t, ?_, ψ.apply_symm_apply t⟩⟩
    · rintro ⟨g, hg, rfl⟩
      rw [← map_mul, hg, map_mul]
    · apply ψ.injective
      rw [map_mul, map_mul, ψ.apply_symm_apply, ht]
  obtain ⟨a, haA, ha1, haL⟩ := S265A.exists_glaPLayer_ne_bot_om8 (by simpa using hF) hQ
    (by simpa using hdim) (hAe.map ψ.toMonoidHom) (by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective A ψ.toMonoidHom ψ.injective).toEquiv,
        hAcard]
      have h27 : 27 * Nat.card D ≤ Nat.card P * Nat.card D := by rw [hcard]; exact hr
      exact Nat.le_of_mul_le_mul_right h27 Nat.card_pos)
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp haA
  have hs1 : s ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
  apply haL
  change GLAPLayer 3 (Subgroup.centralizer ({ψ s} : Set ↥(orthDerived Q))) = ⊥
  rw [← hcent s, ← CFSG.glaPLayer_map_eq_of_injective Nat.prime_three ψ.toMonoidHom ψ.injective,
    hlay s hs hs1, Subgroup.map_bot]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
