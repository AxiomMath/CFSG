module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.WeakClosure
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup AltStdBal CFSG.EvenSporadicStandard.Finkelstein77
open CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

theorem cycTwoBigHallFalse_holds :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
      ∀ n : ℕ, 9 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
        ∀ S : Sylow 2 (centralizer (L : Set G)),
          IsCyclic (S : Subgroup (centralizer (L : Set G))) → 4 ≤ Nat.card S →
            (∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
              P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
                normalizer (L : Set G) → IsPGroup 2 P → Nat.card P ≤ 2) → False := by
  intro G _ _ L hS n hn hθ S hcyc h4 hall
  obtain ⟨e⟩ := hθ
  obtain ⟨z, d⟩ := cyc_of_sylow hS S hcyc
  have hn8 : 8 ≤ n := by omega
  have h4Q : 4 ≤ Nat.card (sylowSub S) := by rw [card_sylowSub]; exact h4
  obtain ⟨x, hxQ, hx4⟩ := exists_mem_orderOf_four d.pgroup d.cyclic h4Q
  have hxK : x ∈ centralizer (L : Set G) := d.le hxQ
  have hW : WeaklyClosedInNormalizer (zpowers x) :=
    weaklyClosed_zpowers hS.standard S hcyc hall hxK hx4
  have hx2z : x ^ 2 = z :=
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.eq_of_orderOf_eq_two_of_isCyclic d.cyclic
      (pow_mem hxQ 2) d.mem (orderOf_eq_two_of_isConj hx4 (IsConj.refl (x ^ 2))) d.order
  obtain ⟨g, -, hcomm, haK, -⟩ := exists_zstar_partner hS d
  have haC : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have haN : g⁻¹ * z * g ∈ normalizer (L : Set G) := cent_le_normalizer hS d haC
  have ha2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [d.mul_self]; group
  have haconj : IsConj (x ^ 2) (g⁻¹ * z * g) := by
    rw [hx2z]
    exact isConj_iff.mpr ⟨g⁻¹, by simp⟩
  set a : normalizer (L : Set G) := ⟨g⁻¹ * z * g, haN⟩ with ha
  have hσ1 : rho e hn8 a ≠ 1 := fun h1 => haK ((rho_eq_one_iff e hn8 a).1 h1)
  have hσ2 : rho e hn8 a * rho e hn8 a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext ha2, map_one]
  obtain ⟨cP, hsign, hv2, hv1⟩ :=
    exists_even_commutator_involution (α := Fin n) (by simp only [Fintype.card_fin]; omega) hσ1 hσ2
  set c' : alternatingGroup (Fin n) := ⟨cP, Equiv.Perm.mem_alternatingGroup.2 hsign⟩ with hc'
  set cL : L := e.symm c' with hcL
  have hmem : (a : G) * (cL : G) * (a : G)⁻¹ ∈ L := (mem_normalizer_iff.mp haN (cL : G)).mp cL.2
  set uL : L := ⟨(a : G) * (cL : G) * (a : G)⁻¹, hmem⟩ * cL⁻¹ with huL
  have hconjρ := rho_conj e hn8 a c'
  have hecL : e cL = c' := e.apply_symm_apply c'
  have huLp : ((e uL : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
      rho e hn8 a * cP * (rho e hn8 a)⁻¹ * cP⁻¹ := by
    have h1 : ((e uL : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        ((e ⟨(a : G) * (cL : G) * (a : G)⁻¹, hmem⟩ : alternatingGroup (Fin n)) :
          Equiv.Perm (Fin n)) * ((c' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))⁻¹ := by
      rw [huL, map_mul, map_inv, hecL]
      rfl
    have h2 : ((e ⟨(a : G) * (cL : G) * (a : G)⁻¹, hmem⟩ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) = rho e hn8 a * cP * (rho e hn8 a)⁻¹ := hconjρ.symm
    rw [h1, h2]
  have huL2 : uL * uL = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, huLp]
    exact hv2
  have huL1 : uL ≠ 1 := by
    intro h1
    apply hv1
    rw [← huLp, h1, map_one]
    rfl
  have hux : ((uL : L) : G) * x = x * ((uL : L) : G) := mem_centralizer_iff.1 hxK _ uL.2
  have hu : ((uL : L) : G) = x ^ 2 :=
    eq_sq_of_commutator_involution hx4 hW (t := (a : G)) (c := (cL : G)) haconj
      (fun h1 => huL1 (Subtype.ext h1)) (congrArg Subtype.val huL2) hux
  have hx2K : x ^ 2 ∈ centralizer (L : Set G) := pow_mem hxK 2
  have hu1 : ((uL : L) : G) = 1 :=
    eq_one_of_mem_of_mem_centralizer e (by omega) uL.2 (hu ▸ hx2K)
  exact huL1 (Subtype.ext hu1)

end CFSG.OddStandard.AltStdCycTwo
