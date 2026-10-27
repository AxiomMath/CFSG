module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LTabs
public import CFSG.Certificates.NativeSchreierCard
public import Certificates.Certificate22240

public section


namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open Matrix Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Th.Native CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable def chainQ : RawSchreierDatum 80 :=
  RawSchreierDatum.ofArrays 80 (by norm_num) chainS 2 (by decide) chainBase (by decide) chainW

theorem chain_check :
    rawChainOK 80 (chainS.extract 0 2) chainS baseArr chainW 4 = true :=
  Certificates.certificate22240.1

theorem chain_orbits :
    (rawOrbitSizes 80 chainS baseArr).prod = 6065280 :=
  Certificates.certificate22240.2.1

theorem centTriv_check :
    centTrivOK 80 l43Sift l43CentTriv = true :=
  Certificates.certificate22240.2.2

theorem chainArrays_l43 :
    ChainArrays chainQ (chainS.extract 0 2) chainS baseArr chainW :=
  chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv

theorem card_chainQ :
    Nat.card chainQ.originalSubgroup = 6065280 := by
  rw [card_originalSubgroup_of_chainOK chainArrays_l43 (by norm_num) chain_check, chain_orbits]

theorem chainQ_eq :
    chainQ.originalSubgroup = Subgroup.closure {pi xElt, pi yElt} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [chainQ, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have e0 : permOfArr 80 chainS[0]! = pi xElt := h0.unique rep_tabA
  have e1 : permOfArr 80 chainS[1]! = pi yElt := h1.unique rep_tabB
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem card_closure_pi :
    Nat.card (Subgroup.closure {pi xElt, pi yElt}) = 6065280 := by
  rw [← chainQ_eq, card_chainQ]

theorem closure_xy :
    Subgroup.closure ({xElt, yElt} : Set (projectiveSL 4 (ZMod 3))) = ⊤ := by
  have : Finite (projectiveSL 4 (ZMod 3)) :=
    Nat.finite_of_card_ne_zero (by rw [card_P]; norm_num)
  apply Subgroup.eq_top_of_le_card
  have hmap : (Subgroup.closure ({xElt, yElt} : Set (projectiveSL 4 (ZMod 3)))).map pi =
      Subgroup.closure {pi xElt, pi yElt} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [card_P, ← card_closure_pi, ← hmap]
  exact Nat.card_le_card_of_surjective _ (pi.subgroupMap_surjective _)

theorem pi_injective : Function.Injective pi := by
  have : Finite (projectiveSL 4 (ZMod 3)) :=
    Nat.finite_of_card_ne_zero (by rw [card_P]; norm_num)
  have hle : Nat.card (projectiveSL 4 (ZMod 3)) ≤ Nat.card pi.range := by
    rw [card_P, ← card_closure_pi]
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xElt, rfl⟩
    · exact ⟨yElt, rfl⟩
  have hb := pi.rangeRestrict_surjective.bijective_of_nat_card_le hle
  exact fun g h hgh => hb.1 (Subtype.ext hgh)

theorem range_pi :
    pi.range = Subgroup.closure {pi xElt, pi yElt} := by
  rw [MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair]

@[expose] noncomputable def l43Gens (l : ℕ) : Equiv.Perm (Fin 80) :=
  if l = 0 then pi xElt else pi yElt

theorem l43_groupData :
    GroupData 80 pi.range pgTbls l43Gens l43Sift where
  lt := by norm_num
  rep l hl := by
    have hl2 : l < 2 := hl
    interval_cases l
    · exact rep_tbl rep_tabA
    · exact rep_tbl rep_tabB
  gen := by
    have himg : l43Gens '' {l | l < pgTbls.size} = {pi xElt, pi yElt} := by
      ext g
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl, rfl⟩
        have hl2 : l < 2 := hl
        interval_cases l
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    rw [himg, range_pi]
  sift T g hT := by
    rw [range_pi, ← chainQ_eq]
    exact siftA_iff_mem_originalSubgroup chainArrays_l43 (by norm_num) chain_check
      (co2Rep_natArr_iff.mpr hT)

theorem eq_one_of_commute_pi {c : Equiv.Perm (Fin 80)}
    (hc : ∀ g, c * pi g = pi g * c) : c = 1 :=
  eq_one_of_centTrivOK l43_groupData centTriv_check (by rintro _ ⟨g, rfl⟩; exact hc g)

end CFSG.ComponentClassification.HarrisLit.P1.L43
