module

public import CFSG.LargeExtraspecial.S12LinAlg
public import CFSG.LargeExtraspecial.S12TriQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] {S : Setting G}

theorem isSolvable_of_commute_of_le_normalizer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {C : Subgroup S.O} (hCM : C ≤ S.Mbar)
    (hCt : ∀ c ∈ C, c * t = t * c) (hLC : S.Lbar g ≤ normalizer (C : Set S.O))
    (hC2 : S12NoNormalTwo C) : Group.IsSolvable C := by
  set W := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hW
  set K := C ⊓ S.fixSub12 W with hK
  have hKC : C ≤ normalizer (K : Set S.O) := by
    intro c hc
    have hc' : c⁻¹ ∈ C := C.inv_mem hc
    refine mem_normalizer_of_conj_le (fun k hk => ⟨?_, ?_⟩) (fun k hk => ⟨?_, ?_⟩)
    · exact C.mul_mem (C.mul_mem hc hk.1) hc'
    · exact conj_mem_fixSub12 (hCt c hc) hk.2
    · exact C.mul_mem (C.mul_mem hc' hk.1) (C.inv_mem hc')
    · exact conj_mem_fixSub12 (hCt _ hc') hk.2
  have hK2 : S12NoNormalTwo K := hC2.of_normal inf_le_left hKC
  have haW := (S.timmesfeld_12_6 haQ hne ht htA).1
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hLK : S.Lbar g ≤ normalizer (K : Set S.O) := by
    intro ℓ hℓ
    have hℓ' : ℓ⁻¹ ∈ S.Lbar g := (S.Lbar g).inv_mem hℓ
    refine mem_normalizer_of_conj_le (fun k hk => ⟨?_, ?_⟩) (fun k hk => ⟨?_, ?_⟩)
    · exact (mem_normalizer_iff.mp (hLC hℓ) k).mp hk.1
    · exact conj_mem_fixSub12 (hcomm hℓ) hk.2
    · exact (mem_normalizer_iff.mp (hLC hℓ') k).mp hk.1
    · exact conj_mem_fixSub12 (hcomm hℓ') hk.2
  have hKbot : K = ⊥ := S.s12_eq_bot_of_fix haQ hne hn hK2 (inf_le_left.trans hCM)
    (fun k hk => hk.2 _ haW) hLK
  refine isSolvable_of_pow_six fun c => Subtype.ext ?_
  have h6 := s12_pow_six_apply htA.2.2.2.1 (x := ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (fun w hw => apply_mem_commSpace_of_commute (hCt c c.2) hw)
    (fun w hw => apply_mem_commSpace_of_commute (hCt _ (C.inv_mem c.2)) hw)
  have hmem : (c : S.O) ^ 6 ∈ K :=
    ⟨C.pow_mem c.2 6, fun w hw => by rw [Subgroup.coe_pow, h6 w hw]⟩
  rw [hKbot, mem_bot] at hmem
  simpa using hmem

theorem isSolvable_fischerQ_inf_centralizer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (h2 : S12NoNormalTwo (fischerQ (S.Ebar12 g) ⊓ centralizer {t})) :
    Group.IsSolvable (fischerQ (S.Ebar12 g) ⊓ centralizer {t} : Subgroup S.O) := by
  refine isSolvable_of_commute_of_le_normalizer haQ hne hn ht htA
    (inf_le_left.trans (fischerQ_le_closure.trans Xbar12_le_Mbar))
    (fun c hc => mem_centralizer_singleton_iff.mp hc.2) (fun ℓ hℓ => ?_) h2
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hconj : ∀ {m : S.O}, m ∈ S.Lbar g → ∀ k ∈ fischerQ (S.Ebar12 g) ⊓ centralizer {t},
      m * k * m⁻¹ ∈ fischerQ (S.Ebar12 g) ⊓ centralizer {t} := by
    intro m hm k hk
    refine mem_inf.mpr
      ⟨conj_mem_fischerQ (fun e he => conj_mem_Ebar12 (S.Lbar_le_Mbar g hm) he) hk.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp hk.2
    have hmt := hcomm hm
    have hmt' : m⁻¹ * t = t * m⁻¹ := by
      calc m⁻¹ * t = m⁻¹ * (t * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * t) * m⁻¹ := by rw [hmt]
        _ = t * m⁻¹ := by group
    calc m * k * m⁻¹ * t = m * k * (m⁻¹ * t) := by group
      _ = m * k * (t * m⁻¹) := by rw [hmt']
      _ = m * (k * t) * m⁻¹ := by group
      _ = m * (t * k) * m⁻¹ := by rw [hkt]
      _ = m * t * k * m⁻¹ := by group
      _ = t * m * k * m⁻¹ := by rw [hmt]
      _ = t * (m * k * m⁻¹) := by group
  exact mem_normalizer_of_conj_le (hconj hℓ) (hconj ((S.Lbar g).inv_mem hℓ))

end Setting

end CFSG.LargeExtraspecial
