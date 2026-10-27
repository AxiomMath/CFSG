module

public import Certificates.Certificate24550
public import CFSG.Sporadic.Co1.Cover.Iota

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Monster.Schur.M24 Matrix

@[expose] def orbitVec11 (v n i : ℕ) : Fin 11 → ZMod 2 := toVecD 11 (orbitOf11 v n).pts[i]!

theorem rho_gen0_toVecD (x : ℕ) :
    rho (gen 0) (toVecD 11 x) = toVecD 11 (vecMulN 11 colsAa x) := by
  rw [rho_gen0]
  exact rowsMatrix_mulVec 11 Aa x

theorem rho_gen1_toVecD (x : ℕ) :
    rho (gen 1) (toVecD 11 x) = toVecD 11 (vecMulN 11 colsBa x) := by
  rw [rho_gen1]
  exact rowsMatrix_mulVec 11 Ba x

theorem closure_gen01 :
    Subgroup.closure ({gen 0, gen 1} : Set PM24) = ⊤ := by
  have h : Set.range (gen : Fin 2 → PM24) = {gen 0, gen 1} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [← h]
  exact closure_gen

theorem orbit_spec11
    {v n : ℕ} {others : List ℕ} (h : orbitCheck11 v n others = true) :
    (Set.range fun p : PM24 => rho p (toVecD 11 v)) = orbitVec11 v n '' {i | i < n} ∧
      (∀ i < n, ∀ j < n, orbitVec11 v n i = orbitVec11 v n j → i = j) ∧
      (∀ w ∈ others, w < 2 ^ 11 → toVecD 11 w ∉ orbitVec11 v n '' {i | i < n}) := by
  classical
  let _ : MulAction PM24 (Fin 11 → ZMod 2) := MulAction.compHom _ rho
  unfold orbitCheck11 at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hOK, h0⟩, hsz⟩, hTOK⟩, hoth⟩ := h
  set O := orbitOf11 v n with hO
  set ls : Array Table := #[O.alpha, O.beta] with hls
  set T := CFSG.Perm.Native.treeBFS n 0 ls #[0, 1] with hT
  obtain ⟨hsize, hO'⟩ := vOrbitOK_facts hOK
  obtain ⟨hpos, hroot, hTk⟩ := treeOK_arith hTOK
  have hn : 0 < n := hsz ▸ hpos
  have hTk' : ∀ k < n, _ := fun k hk => hTk k (by rw [hsz]; exact hk)
  have hinj : ∀ i < n, ∀ j < n, orbitVec11 v n i = orbitVec11 v n j → i = j := by
    intro i hi j hj e
    have e' := toVecD_injective (hO' i hi).1 (hO' j hj).1 e
    rw [← (hO' i hi).2.1, ← (hO' j hj).2.1, e']
  have hA : ∀ i < n, rho (gen 0) (orbitVec11 v n i) = orbitVec11 v n (ap O.alpha i) := by
    intro i hi
    rw [orbitVec11, rho_gen0_toVecD, orbitVec11, ← (hO' i hi).2.2.2.1]
  have hB : ∀ i < n, rho (gen 1) (orbitVec11 v n i) = orbitVec11 v n (ap O.beta i) := by
    intro i hi
    rw [orbitVec11, rho_gen1_toVecD, orbitVec11, ← (hO' i hi).2.2.2.2.2]
  have hQlt : ∀ k < n, ap T.pts k < n := fun k hk => (hTk' k hk).1
  have hinjT : ∀ j < n, ∀ k < n, ap T.pts j = ap T.pts k → j = k := by
    intro j hj k hk e
    rw [← (hTk' j hj).2.1, ← (hTk' k hk).2.1, e]
  have hsurj : ∀ i < n, ∃ k < n, ap T.pts k = i := by
    intro i hi
    let f : Fin n → Fin n := fun k => ⟨ap T.pts k, hQlt k k.isLt⟩
    have hf : Function.Injective f := by
      intro j k e
      apply Fin.ext
      exact hinjT j j.isLt k k.isLt (by simpa [f] using congrArg Fin.val e)
    obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.1 hf ⟨i, hi⟩
    exact ⟨k, k.isLt, congrArg Fin.val hk⟩
  have himg : (fun k => orbitVec11 v n (ap T.pts k)) '' {k | k < n} =
      orbitVec11 v n '' {i | i < n} := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨ap T.pts k, hQlt k hk, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨k, hk, e⟩ := hsurj i hi
      exact ⟨k, hk, by show orbitVec11 v n (ap T.pts k) = _; rw [e]⟩
  have hroot' : orbitVec11 v n (ap T.pts 0) = toVecD 11 v := by
    rw [hroot, orbitVec11, h0]
  have hl0 : ls[0]! = O.alpha := rfl
  have hl1 : ls[1]! = O.beta := rfl
  have hclosed : ∀ k < n, ∀ s ∈ ({gen 0, gen 1} : Set PM24), ∃ j < n,
      orbitVec11 v n (ap T.pts j) = s • orbitVec11 v n (ap T.pts k) := by
    intro k hk s hs
    have hk' := hTk' k hk
    rcases hs with rfl | hs
    · have := hk'.2.2.1 0 (by simp)
      rw [hl0] at this
      refine ⟨_, hsz ▸ this.1, ?_⟩
      show orbitVec11 v n (ap T.pts (ap T.pos (ap O.alpha (ap T.pts k)))) = _
      rw [this.2]
      exact (hA _ (hQlt k hk)).symm
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      have := hk'.2.2.1 1 (by simp)
      rw [hl1] at this
      refine ⟨_, hsz ▸ this.1, ?_⟩
      show orbitVec11 v n (ap T.pts (ap T.pos (ap O.beta (ap T.pts k)))) = _
      rw [this.2]
      exact (hB _ (hQlt k hk)).symm
  have hpar : ∀ k, 0 < k → k < n → ap T.par k < k := by
    intro k hk0 hk
    rcases (hTk' k hk).2.2.2 with h | h
    · omega
    · exact h.1
  have htree : ∀ k, 0 < k → k < n → orbitVec11 v n (ap T.pts k) =
      (if ap T.lab k = 0 then gen 0 else gen 1) • orbitVec11 v n (ap T.pts (ap T.par k)) := by
    intro k hk0 hk
    rcases (hTk' k hk).2.2.2 with h | ⟨hp, hl, he⟩
    · omega
    · have hpk : ap T.par k < n := lt_trans hp hk
      have hlab : ap T.lab k = 0 ∨ ap T.lab k = 1 := by simpa using hl
      rcases hlab with hlab | hlab
      · rw [show (if ap T.lab k = 0 then gen 0 else gen 1) = gen 0 by simp [hlab]]
        rw [hlab, hl0] at he
        have he' : ap O.alpha (ap T.pts (ap T.par k)) = ap T.pts k := he
        show _ = rho (gen 0) _
        rw [hA _ (hQlt _ hpk), he']
      · rw [show (if ap T.lab k = 0 then gen 0 else gen 1) = gen 1 by simp [hlab]]
        rw [hlab, hl1] at he
        have he' : ap O.beta (ap T.pts (ap T.par k)) = ap T.pts k := he
        show _ = rho (gen 1) _
        rw [hB _ (hQlt _ hpk), he']
  have horb := CFSG.Perm.orbitTree_orbit_eq (G := PM24) (S := ({gen 0, gen 1} : Set PM24))
    (n := n) (P := fun k => orbitVec11 v n (ap T.pts k)) (par := fun k => ap T.par k)
    (lab := fun k => ap T.lab k) (ℓ := fun l => if l = 0 then gen 0 else gen 1)
    closure_gen01 hn hclosed hpar htree
  have horb' : MulAction.orbit PM24 (toVecD 11 v) = orbitVec11 v n '' {i | i < n} := by
    rw [← hroot', ← himg]
    exact horb
  refine ⟨horb', hinj, ?_⟩
  rintro w hw hw11 ⟨i, hi, e⟩
  have hi' : i < n := hi
  have hw' : w = O.pts[i]! := toVecD_injective hw11 (hO' i hi').1 e.symm
  have hmem : O.pts[i]! ∈ O.pts := by
    rw [getElem!_pos O.pts i (by rw [hsize]; exact hi')]
    exact Array.getElem_mem _
  have := hoth w hw
  rw [hw'] at this
  have h2 := Array.contains_iff_mem.2 hmem
  rw [this] at h2
  exact absurd h2 (by decide)

theorem ncard_orbit_of_check11
    {v n : ℕ} {others : List ℕ} (h : orbitCheck11 v n others = true) :
    (Set.range fun p : PM24 => rho p (toVecD 11 v)).ncard = n := by
  obtain ⟨h1, h2, -⟩ := orbit_spec11 h
  rw [h1, Set.InjOn.ncard_image (s := {i | i < n}) fun i hi j hj e => h2 i hi j hj e]
  exact Set.ncard_Iio_nat n

theorem pts_size_of_check11 {v n : ℕ} {others : List ℕ} (h : orbitCheck11 v n others = true) :
    (orbitOf11 v n).pts.size = n := by
  unfold orbitCheck11 at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at h
  exact (vOrbitOK_facts h.1.1.1.1).1

theorem toVecD_mem_orbit_of_mem_pts
    {v n : ℕ} {others : List ℕ} (h : orbitCheck11 v n others = true) {m : ℕ}
    (hm : m ∈ (orbitOf11 v n).pts) :
    toVecD 11 m ∈ Set.range fun p : PM24 => rho p (toVecD 11 v) := by
  rw [(orbit_spec11 h).1]
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hm
  refine ⟨i, ?_, ?_⟩
  · rw [← pts_size_of_check11 h]
    exact hi
  · simp only [orbitVec11, getElem!_pos (orbitOf11 v n).pts i hi]

theorem orbit_xC_card :
    (Set.range fun p : PM24 => rho p (toVecD 11 eMaskC)).ncard = 1288 :=
  ncard_orbit_of_check11 Certificates.certificate24550.1

theorem orbit_xA_card :
    (Set.range fun p : PM24 => rho p (toVecD 11 eMaskA)).ncard = 759 :=
  ncard_orbit_of_check11 Certificates.certificate24550.2.1

theorem orbit_cover
    (w : Fin 11 → ZMod 2) (hw : w ≠ 0) :
    w ∈ (Set.range fun p : PM24 => rho p (toVecD 11 eMaskA)) ∨
      w ∈ (Set.range fun p : PM24 => rho p (toVecD 11 eMaskC)) := by
  obtain ⟨m, hm, rfl⟩ := CFSG.Sporadic.Co1.Cover.exists_toVecD w
  have h := Certificates.certificate24550.2.2
  simp only [coverCheck11, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Array.contains_iff_mem] at h
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hw (toVecD_zero 11)
  rcases h m hm with (h0 | hC) | hA
  · exact absurd h0 hm0
  · exact Or.inr (toVecD_mem_orbit_of_mem_pts Certificates.certificate24550.1 hC)
  · exact Or.inl (toVecD_mem_orbit_of_mem_pts Certificates.certificate24550.2.1 hA)

theorem card_stab_mul_ncard_orbit
    (x : Fin 11 → ZMod 2) :
    Nat.card {p : PM24 // rho p x = x} * (Set.range fun p : PM24 => rho p x).ncard =
      Nat.card PM24 := by
  let _ : MulAction PM24 (Fin 11 → ZMod 2) := MulAction.compHom _ rho
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer PM24 x)
  rw [MulAction.index_stabilizer] at h1
  have e : Nat.card {p : PM24 // rho p x = x} = Nat.card (MulAction.stabilizer PM24 x) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => Iff.rfl)
  have e2 : Nat.card (MulAction.orbit PM24 x) = (Set.range fun p : PM24 => rho p x).ncard :=
    Nat.card_coe_set_eq _
  rw [e, ← e2]
  exact h1

theorem card_stab_xC :
    Nat.card {p : PM24 // rho p (toVecD 11 eMaskC) = toVecD 11 eMaskC} = 190080 := by
  have h := card_stab_mul_ncard_orbit (toVecD 11 eMaskC)
  rw [orbit_xC_card, natCard_PM24] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem card_stab_xA :
    Nat.card {p : PM24 // rho p (toVecD 11 eMaskA) = toVecD 11 eMaskA} = 322560 := by
  have h := card_stab_mul_ncard_orbit (toVecD 11 eMaskA)
  rw [orbit_xA_card, natCard_PM24] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

end CFSG.EvenSporadicStandard.TwoCo1
