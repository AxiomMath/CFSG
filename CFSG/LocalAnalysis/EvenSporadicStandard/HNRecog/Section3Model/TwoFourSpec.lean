module

public import Certificates.Certificate441692
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitRowSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIZ1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem orbGenOK_spec {cap m : ℕ} {kg : List (List ℕ)} {x : Table} {xg : Equiv.Perm (Fin 1408)}
    (hgens : gensOK = true) (hkg : kg.all wordOK = true)
    (hkginv : kg.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) = true)
    (hx : Rep 1408 x xg) (h : orbGenOK cap kg m x = true) (T : Subgroup (Equiv.Perm (Fin 1408)))
    (hxT : xg ∈ T)
    (hT : ∀ g ∈ closure (elemW '' {w | w ∈ kg}), ∀ s ∈ T, g * s * g⁻¹ ∈ T) : m ≤ Nat.card ↥T := by
  simp only [orbGenOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨htree, hStree⟩, hdist⟩, hsize⟩ := h
  set K : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ kg}) with hK
  set o := conjClosureH 1408 (p0Tabs kg) (p0Invs kg) x cap with ho
  set S := mulClosureH 1408 o.1 cap with hS
  have hconjSpec := conjTreeOK_spec K (kgens_spec hgens hkg hkginv) hx htree
  have horep : ∀ k < o.1.size, Rep 1408 o.1[k]! (tablePerm 1408 o.1[k]!) := by
    intro k hk
    obtain ⟨c', -, hrep⟩ := hconjSpec k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have homem : ∀ k < o.1.size, tablePerm 1408 o.1[k]! ∈ T := by
    intro k hk
    obtain ⟨c', hc', hrep⟩ := hconjSpec k hk
    rw [tablePerm_eq hrep]
    exact hT c' hc' xg hxT
  have hSspec := mulTreeOK_spec (n := 1408) (by norm_num) T
    (gg := fun l => tablePerm 1408 o.1[l]!) (fun l hl => ⟨horep l hl, homem l hl⟩) hStree
  have hSrep : ∀ k < S.1.size, Rep 1408 S.1[k]! (tablePerm 1408 S.1[k]!) := by
    intro k hk
    obtain ⟨c', -, hrep⟩ := hSspec k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hSmem : ∀ k < S.1.size, tablePerm 1408 S.1[k]! ∈ T := by
    intro k hk
    obtain ⟨c', hc', hrep⟩ := hSspec k hk
    rw [tablePerm_eq hrep]
    exact hc'
  have hSnodup : (S.1.toList.map (tablePerm 1408)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm hSrep) hdist
  have hle := length_le_card_of_nodup hSnodup fun x hx => by
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hSrep hx
    exact hSmem k hk
  rwa [List.length_map, Array.length_toList, hsize] at hle

theorem tfComm_le_derivedOf (h : twoFourOK = true) :
    closure (elemW '' {w | w ∈ sWords3}) ≤
      derivedOf (closure (elemW '' {w | w ∈ classz₁.centGens})) := by
  simp only [twoFourOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hgens, hcg⟩, -⟩, hs⟩, hcomm⟩, -⟩ := h
  rw [closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.1 hw
  rw [← hs] at hsm
  obtain ⟨⟨u, v, s'⟩, hp, rfl⟩ := List.mem_map.1 hsm
  have hc := List.all_eq_true.1 hcomm _ hp
  have hu : wordOK (specWord classz₁.centGens u) = true := wordOK_specWord hcg u
  have hv : wordOK (specWord classz₁.centGens v) = true := wordOK_specWord hcg v
  have hs'' : wordOK (specWord classz₁.centGens s') = true := wordOK_specWord hcg s'
  have hcomm' := commutatorEqOK_spec (rep_elemW_of_gensOK hgens hu)
    (rep_elemW_of_gensOK hgens hv) (rep_elemW_of_gensOK hgens hs'') hc
  show elemW (specWord classz₁.centGens s') ∈ _
  rw [← hcomm']
  exact commutator_mem_derivedOf (elemW_specWord_mem classz₁.centGens u)
    (elemW_specWord_mem classz₁.centGens v)

theorem tf_irreducible (h : twoFourOK = true)
    (hN : IsEnumSet 1408 (subgroupList capI nWords3)
      (closure (elemW '' {w | w ∈ nWords3}) : Set (Equiv.Perm (Fin 1408))))
    (hNcard : Nat.card ↥(closure (elemW '' {w | w ∈ nWords3})) = 16) :
    ∀ S : Subgroup (Equiv.Perm (Fin 1408)), S ≤ closure (elemW '' {w | w ∈ nWords3}) →
      (∀ g ∈ closure (elemW '' {w | w ∈ classz₁.centGens}), ∀ s ∈ S, g * s * g⁻¹ ∈ S) →
        S = ⊥ ∨ S = closure (elemW '' {w | w ∈ nWords3}) := by
  simp only [twoFourOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hgens, hcg⟩, hcginv⟩, -⟩, -⟩, hall⟩ := h
  intro S hSN hSinv
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨s, hs, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall S).2 hcon)
  obtain ⟨k, hk, hrep⟩ := hN.cov s (hSN hs)
  have hb := Array.all_eq_true'.1 hall _ (getElem!_mem_array hk)
  rw [Bool.or_eq_true] at hb
  rcases hb with hid | horb
  · exact absurd ((tblEq_iff_eq hrep (Rep.idT (by norm_num))).1 hid) hs1
  · have hle := orbGenOK_spec hgens hcg hcginv hrep horb S hs hSinv
    exact Subgroup.eq_of_le_of_card_ge hSN (by rw [hNcard]; exact hle)

section Cert

set_option linter.unusedSectionVars false


theorem twoFourData_model (hP : Nat.card ↥P1408 = 177408000) :
    TwoFourData (P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) := by
  have h4 : twoFourOK = true := Certificates.certificate441692
  have h3 := tableI3OK_true
  simp only [tableI3OK, Bool.and_eq_true, Bool.not_eq_true'] at h3
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hblk, himg⟩, hS⟩, hcomm⟩, hN⟩, htriv⟩, hmem⟩, hsq⟩, hnA⟩, hnZ⟩, hnAZ⟩ := h3
  obtain ⟨-, -, -, ⟨-, hcard, hcl⟩⟩ := invClasses_classSpec hP
  obtain ⟨φ, hφ, hrange, hker⟩ := blkData_spec hblk
  have hg : gensOK = true := gensOK_of_blkDataOK hblk
  obtain ⟨-, hNw⟩ := enumW_gens_words hN
  obtain ⟨hScard, hSenum⟩ := enumW_spec hS
  obtain ⟨hNcard, hNenum⟩ := enumW_spec hN
  have hNS : closure (elemW '' {w | w ∈ nWords3}) ≤
      closure (elemW '' {w | w ∈ blkData3.gens}) := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact (hSenum.memT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hNw w hw))).1
      (List.all_eq_true.1 hmem w hw)
  have hNker : ∀ (n : Equiv.Perm (Fin 1408)) (h : n ∈ closure (elemW '' {w | w ∈ nWords3})),
      φ ⟨n, hNS h⟩ = 1 := fun n h =>
    (hker ⟨n, hNS h⟩).2 (fun p => blkTriv_closure hg hNw htriv n h p)
  have hrange' : Nat.card ↥φ.range = 60 := by
    rw [hrange]
    exact blkImage_spec hblk (by show 5 < 2 ^ 32; norm_num) himg
  have hirr := tf_irreducible h4 hNenum hNcard
  have hYX := tfComm_le_derivedOf h4
  rw [hcl] at hirr hYX
  exact twoFourData_of_data (isShape_centralizer_z₁ hP) hcard hYX hScard hNS hNcard
    ((sqOneOK_iff hNenum).1 hsq) φ hrange' hNker hirr

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
