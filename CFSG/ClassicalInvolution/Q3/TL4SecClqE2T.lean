module

public import CFSG.ClassicalInvolution.Q3.TL4SecClique
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2K
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AET
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2B
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent)

namespace SecClq

theorem memBar_congr {m : ℕ} {α β : Finset (Fin m)} (h : α.card = 4) (h' : β.card = 4)
    (e : α = β) (b : Bool) : AE.memBar α h b = AE.memBar β h' b := by
  subst e
  rfl

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_of_label_eq (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    {m : ℕ} (hm : 5 ≤ m) (I : AEIdent (CoreAssembly.conjClass (tightCore R)) m)
    {K J : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {α : Finset (Fin m)} {h : α.card = 4}
    {b : Bool}
    (hlabK : (K.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map I.φ =
      AE.memBar α h b)
    (hlabJ : (J.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map I.φ =
      AE.memBar α h b) : K = J := by
  obtain ⟨a, haK, ha2⟩ := SecIdE2.exists_mul_self_ne_one_mem hd hc K hK
  refine SecIdE2.eq_of_phi_mem I.φ hd hc hO2 hm I.ker_le I.label hK hJ haK ha2 ?_
  rw [hlabJ, ← hlabK]
  exact ⟨⟨a, le_pSpan hK haK⟩, Subgroup.mem_subgroupOf.mpr haK, rfl⟩

theorem false_of_triangle_ae5 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (I : AEIdent (CoreAssembly.conjClass (tightCore R)) 5)
    (B : Fin 3 → Subgroup Y) (hB : ∀ i, B i ∈ CoreAssembly.conjClass (tightCore R))
    (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) :
    False := by
  choose α h b hlab using fun i => I.label (B i) (hB i)
  have hα : ∀ i j, i ≠ j → α i = α j := fun i j hij => by
    have hcomm := AlphaFr.E2A.commutes_of_mem_omegaNbr hd hc hO2 (hB i) (hadj i j hij)
    obtain ⟨u, hu⟩ := AlphaFr.E2A.exists_isUniqueInvolution hd (hB i)
    rcases AlphaFr.E2A.eq_or_disjoint_of_commutes hd hc hO2 (by norm_num) I.φ (hB i) hcomm
      (hlab i) (hlab j) hu with e | hdisj
    · exact e
    · exact absurd (AlphaFr.E2A.eight_le_of_disjoint (h i) (h j) hdisj) (by norm_num)
  have key : ∀ i j, i ≠ j → b i = b j → False := fun i j hij hb => by
    apply hinj.ne hij
    refine eq_of_label_eq hd hc hO2 (by norm_num) I (hB i) (hB j) (hlab i) ?_
    rw [hlab j, ← hb]
    exact memBar_congr (h j) (h i) (hα i j hij).symm (b i)
  have hbool : ∀ x y z : Bool, x ≠ y → x ≠ z → y = z := by decide
  by_cases h01 : b 0 = b 1
  · exact key 0 1 (by decide) h01
  by_cases h02 : b 0 = b 2
  · exact key 0 2 (by decide) h02
  exact key 1 2 (by decide) (hbool _ _ _ h01 h02)

end SecClq

section Cit3


theorem secIdE2Triangle_proved : SecIdE2Triangle := by
  intro n _ hP Y _ _ hn R S t hd hc hO2 B hB hinj hadj
  rcases SecIdE2.thmDConcl_of hP hn hd hc hO2 with
    h1 | ⟨W, hW1⟩ | ⟨E, hE⟩ | h64 | ⟨m, hm, ⟨I⟩⟩ | h29
  · exact absurd (h1 _ (hB 0) _ (hB 1)) (hinj.ne (by decide))
  · exact SecIdE2.dstarConnected_of_wSet hd hc hO2 hW1
  · exact SecIdE2.dstarConnected_of_e8 hd hc hO2 hE
  · obtain ⟨I⟩ := h64
    exact SecIdE2.dstarConnected_of_e64 hd hc hO2 I
  · by_cases hm6 : 6 ≤ m
    · exact SecIdE2.dstarConnected_of_aeIdent hd hc hO2 hm6 I
    · obtain rfl : m = 5 := by omega
      exact (SecClq.false_of_triangle_ae5 hd hc hO2 I B hB hinj hadj).elim
  · obtain ⟨I⟩ := h29
    exact SecIdE2.dstarConnected_of_e29 hd hc hO2 I

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
