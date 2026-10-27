module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi23Perf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23Braid
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23KInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi23

open CFSG.Sporadic.Fi23 CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Blueprint
  CFSG.Blueprint.Fischer CFSG.EvenSporadicStandard.Solomon78

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kCheckOf_sound {g1 g2 : List ℕ} {gs : List (List ℕ)} {par v wd we : List ℕ}
    (h : kCheckOf g1 g2 gs par v wd we = true) :
    ∃ (e1 c : J) (P : Subgroup J), e1 = wordJ g1 * d * (wordJ g1)⁻¹ ∧
      e1 ∈ LocalClass D23 d ∧ c ∈ LocalClass D23 d ∧ c ∈ LocalClass D23 e1 ∧
      P ≤ ⁅P, P⁆ ∧ d ∈ P ∧ e1 ∈ P ∧
      ∀ p ∈ P, p * d = d * p ∧ p * e1 = e1 * p ∧ p * c = c * p := by
  simp only [kCheckOf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, and_assoc] at h
  obtain ⟨hlet, hn0, hidx, hparc, hvev, hc01, hc02, hc12, hcD, hcD1, hcC, hn01, hn02, hn12, hTc,
    hbrc, hvT, hdW, heW⟩ := h
  rw [List.all_eq_true] at hlet hidx hparc hTc hbrc
  have hg1 : ∀ x ∈ g1, x < 2 := fun x hx => by
    simpa using (List.all_eq_true.1 (hlet g1 (by simp))) x hx
  have hg2 : ∀ x ∈ g2, x < 2 := fun x hx => by
    simpa using (List.all_eq_true.1 (hlet g2 (by simp))) x hx
  have hgs : ∀ g ∈ gs, ∀ x ∈ g, x < 2 := fun g hg x hx => by
    simpa using (List.all_eq_true.1 (hlet g (by simp [hg]))) x hx
  have gD : Good matD d := good_d
  have gD1 := good_conjW hg1
  have gC := good_conjW hg2
  have key : ∀ {X Y : Array W} {g h : J}, Good X g → Good Y h →
      commW X Y = true → g * h = h * g := fun hX hY hc => hX.mul hY |>.eq (hY.mul hX) hc
  have hTgood : ∀ x < (gs.map Solomon78.conjW).toArray.size,
      Good (gs.map Solomon78.conjW).toArray[x]!
        (wordJ (gs.getD x []) * d * (wordJ (gs.getD x []))⁻¹) := by
    intro x hx
    have hx' : x < gs.length := by simpa using hx
    rw [arr_getElem!_map hx']
    exact good_conjW (hgs _ (by rw [List.getD_eq_getElem _ _ hx']; exact List.getElem_mem hx'))
  have hprod : ∀ w : List ℕ, (∀ x ∈ w, x < gs.length) →
      Good (prodW 253 (gs.map Solomon78.conjW).toArray w)
        (w.map fun i => wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹).prod := by
    intro w hw
    have := good_foldl hTgood w (fun x hx => by simpa using hw x hx) (idW 253) 1 good_one
    rwa [one_mul] at this
  set Tf : ℕ → J := fun i => wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹ with hTf
  have hTsz : ∀ x < gs.length, Good (gs.map Solomon78.conjW).toArray[x]! (Tf x) := fun x hx =>
    hTgood x (by simpa using hx)
  have hvwd : ∀ x ∈ v, x < gs.length := fun x hx => by
    simpa using hidx x (by simp [hx])
  have hwd : ∀ x ∈ wd, x < gs.length := fun x hx => by
    simpa using hidx x (by simp [hx])
  have hwe : ∀ x ∈ we, x < gs.length := fun x hx => by
    simpa using hidx x (by simp [hx])
  have hT2 : ∀ i < gs.length, Tf i * Tf i = 1 := by
    intro i _
    show wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹ *
      (wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹) = 1
    calc _ = wordJ (gs.getD i []) * (d * d) * (wordJ (gs.getD i []))⁻¹ := by group
      _ = 1 := by rw [d_sq]; group
  have hpar : ∀ j, 1 ≤ j → j < gs.length → par.getD j 0 < j := by
    intro j hj1 hjn
    have := hparc j (List.mem_range.2 hjn)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    omega
  have hbr : ∀ j, 1 ≤ j → j < gs.length → (Tf (par.getD j 0) * Tf j) ^ 3 = 1 := by
    intro j hj1 hjn
    have hb := hbrc j (List.mem_range.2 hjn)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
    have hb' : braidW (gs.map Solomon78.conjW).toArray[par.getD j 0]!
        (gs.map Solomon78.conjW).toArray[j]! = true := by
      rcases hb with hb | hb
      · omega
      · exact hb
    have gX := hTsz _ ((hpar j hj1 hjn).trans hjn)
    have gY := hTsz j hjn
    have gP := gX.mul gY
    have e : (Tf (par.getD j 0) * Tf j) * ((Tf (par.getD j 0) * Tf j) * (Tf (par.getD j 0) * Tf j))
        = 1 := by
      refine (gP.mul (gP.mul gP)).eq good_one ?_
      simpa [braidW] using hb'
    rw [pow_three]
    exact e
  have huv : (([0] : List ℕ).map Tf).prod = (v.map Tf).prod := by
    have g0 := hprod [0] (fun x hx => by simp at hx; omega)
    have gv := hprod v hvwd
    exact g0.eq gv hvT
  have hperf := le_commutator_of_braid_tree (n := gs.length) hn0 Tf (fun j => par.getD j 0)
    hT2 hpar hbr [0] v (fun x hx => by simp at hx; omega) hvwd (by simp) hvev huv
  have hlistP : ∀ w : List ℕ, (∀ x ∈ w, x < gs.length) →
      (w.map Tf).prod ∈ Subgroup.closure (Tf '' {i | i < gs.length}) := by
    intro w hw
    refine Subgroup.list_prod_mem _ (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨i, hw i hi, rfl⟩
  have hdeq : d = (wd.map Tf).prod := gD.eq (hprod wd hwd) hdW
  have heeq : wordJ g1 * d * (wordJ g1)⁻¹ = (we.map Tf).prod := gD1.eq (hprod we hwe) heW
  have hcomm : ∀ {X : Array W} {z : J}, Good X z →
      (∀ i ∈ List.range gs.length, commW (gs.map Solomon78.conjW).toArray[i]! X = true) →
      Subgroup.closure (Tf '' {i | i < gs.length}) ≤ Subgroup.centralizer ({z} : Set J) := by
    intro X z gX hX
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < gs.length := hi
    exact Subgroup.mem_centralizer_singleton_iff.2
      (key (hTsz i hi') gX (hX i (List.mem_range.2 hi')))
  have hP1 := hcomm gD fun i hi => by
    have := hTc i hi
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have hP2 := hcomm gD1 fun i hi => by
    have := hTc i hi
    simp only [Bool.and_eq_true] at this
    exact this.1.2
  have hP3 := hcomm gC fun i hi => by
    have := hTc i hi
    simp only [Bool.and_eq_true] at this
    exact this.2
  have hdc : ∀ g : J, IsConj d (g * d * g⁻¹) := fun g => isConj_iff.2 ⟨g, rfl⟩
  refine ⟨wordJ g1 * d * (wordJ g1)⁻¹, wordJ g2 * d * (wordJ g2)⁻¹,
    Subgroup.closure (Tf '' {i | i < gs.length}), rfl, ⟨hdc _, ?_, ?_⟩, ⟨hdc _, ?_, ?_⟩,
    ⟨hdc _, ?_, ?_⟩, hperf, ?_, ?_, fun p hp => ⟨?_, ?_, ?_⟩⟩
  · exact (gD.ne gD1 hcD hcD1 hn01).symm
  · exact (key gD gD1 hc01).symm
  · exact (gD.ne gC hcD hcC hn02).symm
  · exact (key gD gC hc02).symm
  · exact (gD1.ne gC hcD1 hcC hn12).symm
  · exact (key gD1 gC hc12).symm
  · have := hlistP wd hwd
    rwa [← hdeq] at this
  · have := hlistP we hwe
    rwa [← heeq] at this
  · have h1 := hP1 hp
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1
  · have h1 := hP2 hp
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1
  · have h1 := hP3 hp
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1

end CFSG.EvenSporadicStandard.HypOne.Fi23
