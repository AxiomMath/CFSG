module

public import CFSG.LieType.Chevalley.E6SignedGraphBruhatMul

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {K : Type} [Field K]

theorem wordLength_mul_gen_of_pos
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) (i : Fin 4)
    (h : 0 < height (w • simpleVec i)) : wordLength (w * gen i) = wordLength w + 1 := by
  have hwp := weylGroup_le_parityGroup hw
  rw [wordLength_eq hw, wordLength_eq (mul_mem hw (gen_mem_weylGroup i))]
  have hv : w • simpleVec i ∈ vecs := smul_mem_vecs hwp (simpleVec_mem_posVecs i).1
  exact (card_invFinset_mul_gen (fun v hv => smul_mem_vecs hwp hv) i).2 ⟨hv, h⟩

theorem wordLength_gen_mul_of_pos
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) (i : Fin 4)
    (h : 0 < height (w⁻¹ • simpleVec i)) : wordLength (gen i * w) = wordLength w + 1 := by
  rw [← wordLength_inv (gen i * w), mul_inv_rev, gen_inv, ← wordLength_inv w]
  exact wordLength_mul_gen_of_pos (inv_mem hw) i h

theorem wordLength_one
    : wordLength (1 : WeylGroup TwistTag.E6.tag) = 0 :=
  Nat.sInf_eq_zero.2 (Or.inl ⟨[], rfl, rfl⟩)

theorem exists_reduced_word
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) :
    ∃ l : List (Fin 4), l.length = wordLength w ∧ (l.map gen).prod = w := by
  obtain ⟨l, -, hl⟩ := exists_word (weylGroup_le_parityGroup hw)
  exact Nat.sInf_mem (s := {n | ∃ l : List (Fin 4), l.length = n ∧ (l.map gen).prod = w})
    ⟨_, l, rfl, hl⟩

theorem wordLength_le
    (l : List (Fin 4)) : wordLength (l.map gen).prod ≤ l.length :=
  Nat.sInf_le ⟨l, rfl, rfl⟩

theorem adj_check : ∀ i j : Fin 4, (i.val + 1 = j.val ∨ j.val + 1 = i.val) →
    0 < height (genAct i (simpleVec j)) ∧ 0 < height (genAct j (genAct i (simpleVec j))) := by
  decide +kernel

theorem wordLength_adj
    {i j : Fin 4} (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    wordLength (gen j * gen i) = 2 ∧ wordLength (gen j * gen i * gen j) = 3 := by
  have h := adj_check i j hij
  have h1 : wordLength (gen i) = 1 := by
    have h' := wordLength_gen_mul_of_pos (one_mem _) i
      (by rw [inv_one, one_smul]; exact (simpleVec_mem_posVecs i).2)
    rwa [mul_one, wordLength_one] at h'
  have h2 : wordLength (gen j * gen i) = 2 := by
    rw [wordLength_gen_mul_of_pos (gen_mem_weylGroup i) j
      (by rw [gen_inv, gen_smul]; exact h.1), h1]
  refine ⟨h2, ?_⟩
  rw [wordLength_mul_gen_of_pos (mul_mem (gen_mem_weylGroup j) (gen_mem_weylGroup i)) j
    (by rw [mul_smul, gen_smul, gen_smul]; exact h.2), h2]

theorem exists_adj_of_ne : ∀ f : Fin 4 → Bool, (∃ i, f i = true) → (∃ j, f j = false) →
    ∃ i j : Fin 4, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ f i = true ∧ f j = false := by
  decide

theorem nSL_one_eq_mul : nSL (1 : Kˣ) = uSL 1 * vSL (-1) * uSL 1 := by
  rw [nSL_one]
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [SL2_mul_apply, coe_uSL, coe_vSL, coe_WSL]

theorem orbitFixed_simpleOrbit_le_posFixed
    (i : Fin 4) :
    orbitFixed K (simpleOrbit i) ≤ posFixed K :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent ((height_orbitVec_pos_iff (simpleOrbit_spec i).1).1
    (by rw [(simpleOrbit_spec i).2]; exact (simpleVec_mem_posVecs i).2)))

section Lifts

variable
    {v : Fin 4 → WeylGroup TwistTag.E6.tag} {a : Fin 4 → Fin TwistTag.E6.foldedTag.rank}
  (hva : ∀ i, v i ∈ relWeylTwist TwistTag.E6 ∧ orbitImage (v i) (a i) = simpleOrbit i)
include hva

theorem orbitSL2_mem_orbitFixed
    (i : Fin 4) (c : K) :
    orbitSL2 K (v i) (a i) (uSL c) ∈ orbitFixed K (simpleOrbit i) ∧
      orbitSL2 K (v i) (a i) (vSL c) ∈ orbitFixed K ((simpleOrbit i).image fun α => -α) := by
  obtain ⟨hwi, he⟩ := hva i
  have hOi : orbitImage (v i) (a i) ∈ orbits := he ▸ (simpleOrbit_spec i).1
  have hs := orbitSign_eq_one_of_mem_orbits (K := K) hOi
  have hupper := (orbitFixed_orbitImage_upper hwi hs).2
  have hlower := (orbitFixed_orbitImage_lower hwi hs).2
  rw [he] at hupper hlower
  refine ⟨?_, ?_⟩
  · rw [← SetLike.mem_coe, ← hupper]
    exact ⟨c, rfl⟩
  · rw [← SetLike.mem_coe, ← hlower]
    exact ⟨c, rfl⟩

theorem simpleLift_mem_of_le
    {E : Subgroup (ModGL TwistTag.E6.tag K)} (i : Fin 4)
    (hQ : orbitFixed K (simpleOrbit i) ≤ E)
    (hQ' : orbitFixed K ((simpleOrbit i).image fun α => -α) ≤ E) : simpleLift K v a i ∈ E := by
  rw [simpleLift, nSL_one_eq_mul, map_mul, map_mul]
  exact mul_mem (mul_mem (hQ (orbitSL2_mem_orbitFixed hva i 1).1)
    (hQ' (orbitSL2_mem_orbitFixed hva i (-1)).2)) (hQ (orbitSL2_mem_orbitFixed hva i 1).1)

theorem simpleLift_mem_of_reduced
    {E : Subgroup (ModGL TwistTag.E6.tag K)}
    (hB : borelPart K ≤ E) {l : List (Fin 4)} :
    ∀ {w : WeylGroup TwistTag.E6.tag} {d : ModGL TwistTag.E6.tag K}, (l.map gen).prod = w →
      l.length = wordLength w → d ∈ rootGenerated K → d ∈ monomialSubgroup TwistTag.E6.tag K →
        MapsRootLines d w → d ∈ E → ∀ i ∈ l, simpleLift K v a i ∈ E := by
  induction l with
  | nil =>
    intro _ _ _ _ _ _ _ _ i hi
    exact absurd hi List.not_mem_nil
  | cons i l ih =>
    intro w d hprod hlen hdS hdN hdw hdE j hj
    have hw : w ∈ weylGroup := hprod ▸ prod_mem_weylGroup (i :: l)
    have hw' : gen i * w = (l.map gen).prod := by
      rw [← hprod, List.map_cons, List.prod_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hl1 := wordLength_le l
    obtain ⟨l', hl', hl'p⟩ := exists_reduced_word (prod_mem_weylGroup l)
    have hl2 : wordLength w ≤ wordLength (l.map gen).prod + 1 := by
      have h := wordLength_le (i :: l')
      rw [List.map_cons, List.prod_cons, hl'p, ← hw', ← mul_assoc, gen_mul_gen, one_mul,
        List.length_cons, hl'] at h
      exact h
    rw [List.length_cons] at hlen
    have hlen' : wordLength (gen i * w) = wordLength w - 1 := by
      rw [hw']
      omega
    have hneg : height (w⁻¹ • simpleVec i) < 0 := (wordLength_gen_mul hw i).1 hlen'
    have hzE : simpleLift K v a i ∈ E := by
      refine simpleLift_mem_of_le hva i
        ((orbitFixed_simpleOrbit_le_posFixed i).trans ((le_sup_right).trans hB)) ?_
      intro x hx
      have hu := conj_inv_mem_posFixed_of_neg hw hdS hdN hdw i hneg hx
      have e : x = d * (d⁻¹ * x * d) * d⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem hdE (hB (le_sup_right (a := torusPart K) hu))) (inv_mem hdE)
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hzE
    · obtain ⟨hzS, -, hzw⟩ := simpleLift_mem (K := K) hva i
      have hzN : simpleLift K v a i ∈ monomialSubgroup TwistTag.E6.tag K :=
        orbitSL2_nSL_mem_monomialSubgroup _ _ _
      have hzw' : MapsRootLines (simpleLift K v a i)⁻¹ (gen i) := by
        have h := hzw.inv
        rwa [gen_inv] at h
      refine ih (w := gen i * w) (d := (simpleLift K v a i)⁻¹ * d) hw'.symm ?_
        (mul_mem (inv_mem hzS) hdS) (mul_mem (inv_mem hzN) hdN) (hzw'.mul hdw)
        (mul_mem (inv_mem hzE) hdE) j hj
      rw [hw']
      omega

theorem rootGenerated_le_of_simpleLift_mem
    (hK : ringChar K ≠ 2)
    {E : Subgroup (ModGL TwistTag.E6.tag K)} (hB : borelPart K ≤ E)
    (hz : ∀ i, simpleLift K v a i ∈ E) : rootGenerated K ≤ E := by
  intro x hx
  have hN : liftGroup K v a ≤ E :=
    sup_le (le_trans le_sup_left hB) ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 hz))
  have hxΓ := rootGenerated_le_fixedGroup hx
  obtain ⟨w, hw, hxw⟩ := exists_mem_bruhatCell hK hxΓ
  obtain ⟨d, hd, hdw⟩ := exists_mem_liftGroup_of_mem_weylGroup (K := K) hva hw
  have hdS := liftGroup_le_rootGenerated hva hd
  have hdN := liftGroup_le_monomialSubgroup v a hd
  obtain ⟨⟨u, h, v'⟩, ⟨hu, hh, hv⟩, rfl⟩ := (fixed_cell_bijOn (weylGroup_le_parityGroup hw).1
    (rootGenerated_le_fixedGroup hdS) hdN hdw).2.2 ⟨hxΓ, hxw⟩
  have hhT := mem_torusPart_of_factor hu hh hdS hv hx
  exact mul_mem (mul_mem (mul_mem (hB (le_sup_right (a := torusPart K) hu))
    (hB (le_sup_left (b := posFixed K) hhT))) (hN hd))
    (hB (le_sup_right (a := torusPart K) (inversionFixed_le_posFixed w hv)))

end Lifts

theorem conj_mem_torusGroup_of_mem_monomialSubgroup
    {d : ModGL TwistTag.E6.tag K}
    (hd : d ∈ monomialSubgroup TwistTag.E6.tag K) {t : ModGL TwistTag.E6.tag K}
    (ht : t ∈ torusGroup TwistTag.E6.tag K) : d * t * d⁻¹ ∈ torusGroup TwistTag.E6.tag K := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hd
  have h1 := (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) t).1 ht
  rw [show k * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * t *
    (k * canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
      k * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * t *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * k⁻¹ by group]
  exact mul_mem (mul_mem hk h1) (inv_mem hk)

theorem mem_torusPart_of_forall_conj
    (hK : ringChar K ≠ 2) {x : ModGL TwistTag.E6.tag K}
    (hxS : x ∈ rootGenerated K) (hx : ∀ s ∈ rootGenerated K, s * x * s⁻¹ ∈ borelPart K) :
    x ∈ torusPart K := by
  set w₀ := (longestWord.map gen).prod with hw₀
  have hw₀m : w₀ ∈ weylGroup := longest_mem
  obtain ⟨d, hdS, hdN, hdΓ, hdw⟩ := exists_lift_of_mem_weylGroup (K := K) hw₀m
  have hU : ∀ u ∈ posFixed K, d * u * d⁻¹ ∈ negUnipotent TwistTag.E6.tag K := by
    intro u hu
    obtain ⟨m, O, hO, hrange⟩ :=
      exists_ordering (X := {P | P ∈ orbits ∧ 0 < height (orbitVec P)})
        (finite_diagramRootOrbits.subset fun _ hP => hP.1.1)
    have hu' : u ∈ Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) := by
      rw [(posFixed_list_prod hK O hO hrange).2]
      exact hu
    obtain ⟨g, rfl⟩ := hu'
    simp only
    rw [conj_ofFn_prod]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hOi : O i ∈ orbits ∧ 0 < height (orbitVec (O i)) := by
      have h := Set.mem_range_self (f := O) i
      rw [hrange] at h
      exact h
    have hroots : ∀ α ∈ O i, IsRoot TwistTag.E6.tag α := fun α hα => by
      obtain ⟨⟨⟨β, hβ, hβO⟩, -⟩, -⟩ := hOi
      rw [← hβO] at hα
      exact TwistTag.E6.isRoot_of_mem_diagramOrbit hβ hα
    have hconj : d * (g i : ModGL TwistTag.E6.tag K) * d⁻¹ ∈
        orbitFixed K ((O i).image fun α => w₀ • α) := by
      rw [← map_orbitFixed_conj hdN hdw hdΓ hroots]
      exact ⟨_, (g i).2, rfl⟩
    obtain ⟨hP, hPv⟩ := smul_mem_orbits (weylGroup_le_parityGroup hw₀m) hOi.1
    have hneg : height (orbitVec ((O i).image fun α => w₀ • α)) < 0 := by
      rw [hPv, hw₀, longest_smul ⟨O i, hOi.1, rfl⟩, height_neg]
      linarith [hOi.2]
    exact rootSpan_le_negUnipotent ((height_orbitVec_neg_iff hP).1 hneg)
      (Subgroup.mem_inf.1 hconj).1
  have hy : d⁻¹ * x * d ∈ borelPart K := by
    have h := hx d⁻¹ (inv_mem hdS)
    rwa [inv_inv] at h
  have hy' : d⁻¹ * x * d ∈ (torusPart K : Set (ModGL TwistTag.E6.tag K)) *
      (posFixed K : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← coe_borelPart]
    exact hy
  obtain ⟨t, ht, u, hu, htu⟩ := hy'
  simp only at htu
  have hxe : x = (d * t * d⁻¹) * (d * u * d⁻¹) := by
    rw [show (d * t * d⁻¹) * (d * u * d⁻¹) = d * (t * u) * d⁻¹ by group, htu]
    group
  have hH : d * t * d⁻¹ ∈ torusGroup TwistTag.E6.tag K :=
    conj_mem_torusGroup_of_mem_monomialSubgroup hdN (Subgroup.mem_inf.1 ht).2
  have hV : d * u * d⁻¹ ∈ negUnipotent TwistTag.E6.tag K := hU u hu
  have hxB : x ∈ borelGroup TwistTag.E6.tag K := by
    have h := hx 1 (one_mem _)
    rw [one_mul, inv_one, mul_one] at h
    exact borelPart_le_borelGroup h
  have hV1 : d * u * d⁻¹ = 1 := by
    have hmem : d * u * d⁻¹ ∈ borelGroup TwistTag.E6.tag K ⊓ negUnipotent TwistTag.E6.tag K := by
      refine Subgroup.mem_inf.2 ⟨?_, hV⟩
      have e : d * u * d⁻¹ = (d * t * d⁻¹)⁻¹ * x := by rw [hxe]; group
      rw [e]
      exact mul_mem (inv_mem (torusGroup_le_borelGroup hH)) hxB
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hV1, mul_one] at hxe
  exact Subgroup.mem_inf.2 ⟨hxS, hxe ▸ hH⟩

theorem commute_of_forall_conj
    (hK : ringChar K ≠ 2) {x : ModGL TwistTag.E6.tag K}
    (hxS : x ∈ rootGenerated K) (hx : ∀ s ∈ rootGenerated K, s * x * s⁻¹ ∈ borelPart K)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ rootGenerated K) : g * x = x * g := by
  have hxT := mem_torusPart_of_forall_conj hK hxS hx
  have hxH₀ := torusPart_le_torusFixed hxT
  have hcore : ∀ u ∈ rootGenerated K, x * u * x⁻¹ * u⁻¹ ∈ torusPart K := fun u hu => by
    refine mem_torusPart_of_forall_conj hK (mul_mem (mul_mem (mul_mem hxS hu) (inv_mem hxS))
      (inv_mem hu)) fun s hs => ?_
    have e : s * (x * u * x⁻¹ * u⁻¹) * s⁻¹ = (s * x * s⁻¹) * ((s * u) * x⁻¹ * (s * u)⁻¹) := by
      group
    rw [e]
    have h1 := hx (s * u) (mul_mem hs hu)
    exact mul_mem (hx s hs) (by
      have h2 : (s * u) * x⁻¹ * (s * u)⁻¹ = ((s * u) * x * (s * u)⁻¹)⁻¹ := by group
      rw [h2]
      exact inv_mem h1)
  have hC : rootGenerated K ≤ Subgroup.centralizer {x} := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · have h1 := hcore u (le_sup_left (b := negFixed K) hu)
      have h2 : x * u * x⁻¹ * u⁻¹ ∈ posFixed K :=
        mul_mem ((Subgroup.mem_normalizer_iff.1 (torusFixed_le_normalizer_posFixed hxH₀) u).1 hu)
          (inv_mem hu)
      have h3 := Subgroup.mem_inf.2 ⟨torusPart_le_torusFixed h1, h2⟩
      rw [torusFixed_inf_posFixed, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 : x * u = u * x := by
        calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
          _ = u * x := by rw [h3, one_mul]
      exact h4.symm
    · have h1 := hcore u (le_sup_right (a := posFixed K) hu)
      have h2 : x * u * x⁻¹ * u⁻¹ ∈ negFixed K :=
        mul_mem ((Subgroup.mem_normalizer_iff.1 (torusFixed_le_normalizer_negFixed hxH₀) u).1 hu)
          (inv_mem hu)
      have h3 := Subgroup.mem_inf.2 ⟨torusPart_le_torusFixed h1, h2⟩
      rw [torusFixed_inf_negFixed, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 : x * u = u * x := by
        calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
          _ = u * x := by rw [h3, one_mul]
      exact h4.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hC hg)

theorem normalCore_borelPart_le_center
    (hK : ringChar K ≠ 2) :
    ((borelPart K).subgroupOf (rootGenerated K)).normalCore ≤
      Subgroup.center (rootGenerated K) := by
  intro x hx
  have hx' : ∀ b : rootGenerated K,
      b * x * b⁻¹ ∈ (borelPart K).subgroupOf (rootGenerated K) := hx
  refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
  have h := commute_of_forall_conj hK x.2 (fun s hs => by
    have h' := hx' ⟨s, hs⟩
    rw [Subgroup.mem_subgroupOf] at h'
    exact h') g.2
  exact h

end CFSG.LieType.Chevalley.E6SignedGraph
