module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211NatHexa
public import CFSG.CharacterTheory.SteinbergBYAlternatingSixData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Hexa

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open CFSG.CharacterTheory.SteinbergBY.AlternatingSix Equiv

@[expose] def synTV : Vector (Vector (Vector (Fin 6) 6) 6) 6 :=
  #v[#v[#v[0, 1, 2, 3, 4, 5], #v[1, 0, 3, 2, 5, 4], #v[5, 2, 1, 4, 3, 0], #v[4, 3, 5, 1, 0, 2],
      #v[3, 5, 4, 0, 2, 1], #v[2, 4, 0, 5, 1, 3]],
    #v[#v[1, 0, 3, 2, 5, 4], #v[0, 1, 2, 3, 4, 5], #v[3, 4, 5, 0, 1, 2], #v[2, 5, 0, 4, 3, 1],
      #v[4, 2, 1, 5, 0, 3], #v[5, 3, 4, 1, 2, 0]],
    #v[#v[5, 2, 1, 4, 3, 0], #v[3, 4, 5, 0, 1, 2], #v[0, 1, 2, 3, 4, 5], #v[1, 0, 4, 5, 2, 3],
      #v[2, 3, 0, 1, 5, 4], #v[4, 5, 3, 2, 0, 1]],
    #v[#v[4, 3, 5, 1, 0, 2], #v[2, 5, 0, 4, 3, 1], #v[1, 0, 4, 5, 2, 3], #v[0, 1, 2, 3, 4, 5],
      #v[5, 4, 3, 2, 1, 0], #v[3, 2, 1, 0, 5, 4]],
    #v[#v[3, 5, 4, 0, 2, 1], #v[4, 2, 1, 5, 0, 3], #v[2, 3, 0, 1, 5, 4], #v[5, 4, 3, 2, 1, 0],
      #v[0, 1, 2, 3, 4, 5], #v[1, 0, 5, 4, 3, 2]],
    #v[#v[2, 4, 0, 5, 1, 3], #v[5, 3, 4, 1, 2, 0], #v[4, 5, 3, 2, 0, 1], #v[3, 2, 1, 0, 5, 4],
      #v[1, 0, 5, 4, 3, 2], #v[0, 1, 2, 3, 4, 5]]]

@[expose] def synT (j j' x : Fin 6) : Fin 6 := synTV[j][j'][x]

@[expose] def witT (j j' : Fin 6) : Fin 5 :=
  (#v[#v[0, 0, 4, 3, 2, 1], #v[0, 0, 2, 1, 3, 4], #v[4, 2, 0, 0, 1, 3], #v[3, 1, 0, 0, 4, 2],
    #v[2, 3, 1, 4, 0, 0], #v[1, 4, 3, 2, 0, 0]] : Vector (Vector (Fin 5) 6) 6)[j][j']

theorem synT_eq_partner : ∀ j j' : Fin 6, j ≠ j' → ∀ x,
    synT j j' x = partner j (witT j j') x := by
  decide

theorem synT_comm : ∀ j j' x : Fin 6, synT j j' x = synT j' j x := by decide

theorem synT_ne : ∀ j j' : Fin 6, j ≠ j' → ∀ x, synT j j' x ≠ x := by decide

theorem synT_mem {j j' : Fin 6} (h : j ≠ j') :
    (∃ a : Fin 5, ∀ x, synT j j' x = partner j a x) ∧
      ∃ a : Fin 5, ∀ x, synT j j' x = partner j' a x :=
  ⟨⟨witT j j', synT_eq_partner j j' h⟩, ⟨witT j' j, fun x => by
    rw [synT_comm]; exact synT_eq_partner j' j h.symm x⟩⟩

theorem eq_synT {j j' : Fin 6} (h : j ≠ j') {a a' : Fin 5}
    (haa : ∀ x, partner j a x = partner j' a' x) (x : Fin 6) : partner j a x = synT j j' x := by
  obtain ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ := synT_mem h
  by_cases hab : a = b
  · rw [hab, hb]
  · exact absurd (total_eq_of_two_synthemes j j' a b a' b' hab haa
      (fun y => (hb y).symm.trans (hb' y))) h

@[expose] def rep2V : Vector (Vector (Fin 64) 6) 6 :=
  #v[#v[0, 5, 24, 29, 23, 18], #v[5, 0, 22, 19, 28, 25], #v[24, 22, 0, 7, 17, 31],
    #v[29, 19, 7, 0, 26, 20], #v[23, 28, 17, 26, 0, 6], #v[18, 25, 31, 20, 6, 0]]

@[expose] def rep2 (j j' : Fin 6) : Fin 64 := rep2V[j][j']

@[expose] def rep2W1 (j j' : Fin 6) : Fin 64 :=
  (#v[#v[0, 10, 44, 38, 41, 35], #v[10, 0, 43, 33, 36, 46], #v[44, 43, 0, 9, 34, 37],
    #v[38, 33, 9, 0, 47, 40], #v[41, 36, 34, 47, 0, 11], #v[35, 46, 37, 40, 11, 0]] :
    Vector (Vector (Fin 64) 6) 6)[j][j']

@[expose] def rep2W2 (j j' : Fin 6) : Fin 64 :=
  (#v[#v[0, 15, 52, 59, 62, 49], #v[15, 0, 61, 50, 56, 55], #v[52, 61, 0, 14, 51, 58],
    #v[59, 50, 14, 0, 53, 60], #v[62, 56, 51, 53, 0, 13], #v[49, 55, 58, 60, 13, 0]] :
    Vector (Vector (Fin 64) 6) 6)[j][j']

theorem rep2_comm : ∀ j j' : Fin 6, rep2 j j' = rep2 j' j := by decide

theorem rep2W1_eq : ∀ j j' : Fin 6, rep2W1 j j' = omegaF (rep2 j j') := by decide

theorem rep2W2_eq : ∀ j j' : Fin 6, rep2W2 j j' = omegaF (omegaF (rep2 j j')) := by decide

@[expose] def secMask (x y : Fin 6) : ℕ :=
  (#v[#v[0, 61152, 3940709804408832, 8070462626889465856, 936749206482190336,
      49768294437093376],
    #v[61152, 0, 1229501458975555584, 614812010508582912, 2315562726434537472,
      4901044641694482432],
    #v[3940709804408832, 1229501458975555584, 0, 297378452548387872, 4647787383255745152,
      2882312833029122112],
    #v[8070462626889465856, 614812010508582912, 297378452548387872, 0, 5647100327503936,
      72620647339278976],
    #v[936749206482190336, 2315562726434537472, 4647787383255745152, 5647100327503936, 0,
      1155174421113242656],
    #v[49768294437093376, 4901044641694482432, 2882312833029122112, 72620647339278976,
      1155174421113242656, 0]] : Vector (Vector ℕ 6) 6)[x][y]

@[expose] def inSecM (x y : Fin 6) (u : Fin 64) : Bool := (secMask x y).testBit u.val

theorem inSecM_of_mem_aux : ∀ x y : Fin 6, x ≠ y → ∀ a ∈ hexaOval[(x : ℕ)]!,
    ∀ c ∈ hexaOval[(y : ℕ)]!, a ≠ 0 → c ≠ 0 → (secMask x y).testBit (a ^^^ c) = true := by
  decide

theorem inSecM_of_mem {x y : Fin 6} (hxy : x ≠ y) {a c : Fin 64} (ha0 : a ≠ 0) (hc0 : c ≠ 0)
    (ha : a.val ∈ hexaOval[(x : ℕ)]!) (hc : c.val ∈ hexaOval[(y : ℕ)]!) :
    inSecM x y (xorF a c) = true :=
  inSecM_of_mem_aux x y hxy a.val ha c.val hc (fun h => ha0 (Fin.ext h)) fun h => hc0 (Fin.ext h)

@[expose] def ovalNz (x : Fin 6) : List (Fin 64) :=
  (#v[[1, 2, 3], [4, 8, 12], [16, 32, 48], [21, 42, 63], [30, 39, 57], [27, 45, 54]] :
    Vector (List (Fin 64)) 6)[x]

theorem ovalNz_spec : ∀ x : Fin 6, ∀ a ∈ ovalNz x, a ≠ 0 ∧ a.val ∈ hexaOval[(x : ℕ)]! := by
  decide

@[expose] def decA (j j' x : Fin 6) : Fin 64 :=
  (#v[#v[#v[0, 0, 0, 0, 0, 0], #v[1, 4, 16, 21, 30, 27], #v[3, 8, 16, 63, 39, 27],
      #v[3, 8, 48, 21, 30, 45], #v[2, 12, 48, 21, 39, 27], #v[2, 12, 16, 63, 30, 45]],
    #v[#v[1, 4, 16, 21, 30, 27], #v[0, 0, 0, 0, 0, 0], #v[3, 8, 32, 21, 30, 54],
      #v[3, 8, 16, 42, 57, 27], #v[2, 12, 16, 42, 30, 54], #v[2, 12, 32, 21, 57, 27]],
    #v[#v[3, 8, 16, 63, 39, 27], #v[3, 8, 32, 21, 30, 54], #v[0, 0, 0, 0, 0, 0],
      #v[3, 4, 32, 42, 39, 45], #v[1, 4, 16, 21, 39, 54], #v[1, 4, 32, 63, 30, 27]],
    #v[#v[3, 8, 48, 21, 30, 45], #v[3, 8, 16, 42, 57, 27], #v[3, 4, 32, 42, 39, 45],
      #v[0, 0, 0, 0, 0, 0], #v[1, 4, 48, 42, 30, 27], #v[1, 4, 16, 21, 57, 45]],
    #v[#v[2, 12, 48, 21, 39, 27], #v[2, 12, 16, 42, 30, 54], #v[1, 4, 16, 21, 39, 54],
      #v[1, 4, 48, 42, 30, 27], #v[0, 0, 0, 0, 0, 0], #v[2, 4, 48, 63, 57, 54]],
    #v[#v[2, 12, 16, 63, 30, 45], #v[2, 12, 32, 21, 57, 27], #v[1, 4, 32, 63, 30, 27],
      #v[1, 4, 16, 21, 57, 45], #v[2, 4, 48, 63, 57, 54], #v[0, 0, 0, 0, 0, 0]]] :
    Vector (Vector (Vector (Fin 64) 6) 6) 6)[j][j'][x]

theorem decA_spec : ∀ j j' : Fin 6, j ≠ j' → ∀ x : Fin 6, decA j j' x ∈ ovalNz x ∧
    decA j j' (synT j j' x) ∈ ovalNz (synT j j' x) ∧
    xorF (decA j j' x) (decA j j' (synT j j' x)) = rep2 j j' := by
  decide

theorem rep2_decomp {j j' : Fin 6} (h : j ≠ j') (x : Fin 6) :
    ∃ a ∈ ovalNz x, ∃ c ∈ ovalNz (synT j j' x), xorF a c = rep2 j j' :=
  ⟨_, (decA_spec j j' h x).1, _, (decA_spec j j' h x).2.1, (decA_spec j j' h x).2.2⟩

theorem secMask_inter : ∀ j j' : Fin 6, j ≠ j' →
    secMask 0 (synT j j' 0) &&& secMask 1 (synT j j' 1) &&& secMask 2 (synT j j' 2) &&&
      secMask 3 (synT j j' 3) &&& secMask 4 (synT j j' 4) &&& secMask 5 (synT j j' 5) =
    2 ^ (rep2 j j').val ||| 2 ^ (rep2W1 j j').val ||| 2 ^ (rep2W2 j j').val := by
  decide +kernel

theorem eq_rep2_of_inSecM {j j' : Fin 6} (h : j ≠ j') {u : Fin 64}
    (hu : ∀ x, inSecM x (synT j j' x) u = true) :
    u = rep2 j j' ∨ u = omegaF (rep2 j j') ∨ u = omegaF (omegaF (rep2 j j')) := by
  have h1 := congrArg (fun n => n.testBit u.val) (secMask_inter j j' h)
  simp only [Nat.testBit_land, Nat.testBit_lor, Nat.testBit_two_pow] at h1
  have hu' : ∀ x, (secMask x (synT j j' x)).testBit u.val = true := hu
  rw [hu' 0, hu' 1, hu' 2, hu' 3, hu' 4, hu' 5] at h1
  rw [← rep2W2_eq, ← rep2W1_eq]
  simp only [Bool.and_self, Bool.true_eq, Bool.or_eq_true, decide_eq_true_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact Or.inl (Fin.ext h1.symm)
  · exact Or.inr (Or.inl (Fin.ext h1.symm))
  · exact Or.inr (Or.inr (Fin.ext h1.symm))

@[expose] def ovalOfV : Vector ℕ 64 :=
  #v[0, 0, 0, 0, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 2, 6, 6, 6, 6, 3, 6, 6, 6, 6, 6, 5, 6, 6, 4,
    6, 2, 6, 6, 6, 6, 6, 6, 4, 6, 6, 3, 6, 6, 5, 6, 6, 2, 6, 6, 6, 6, 6, 5, 6, 6, 4, 6, 6, 6, 6, 6,
    3]

@[expose] def pairJ (u : Fin 64) : Fin 6 :=
  (#v[0, 0, 0, 0, 0, 0, 4, 2, 0, 2, 0, 4, 0, 4, 2, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 1, 3, 0, 1, 0, 0,
    2, 0, 1, 2, 0, 1, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 3, 0, 0, 1, 2, 0, 3, 0, 1, 1, 0, 2, 0, 3, 1, 0,
    0] : Vector (Fin 6) 64)[u]

@[expose] def pairJ' (u : Fin 64) : Fin 6 :=
  (#v[1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5, 1, 5, 3, 1, 1, 4, 5, 3, 5, 1, 2, 4, 2, 5, 4, 1, 4, 3, 1,
    5, 1, 3, 4, 5, 4, 5, 3, 1, 5, 4, 1, 2, 2, 1, 5, 4, 1, 5, 3, 4, 2, 4, 1, 5, 4, 1, 5, 3, 5, 2, 4,
    1] : Vector (Fin 6) 64)[u]

theorem classify_aux : ∀ u : Fin 64, (ovalOfV[u] < 6 → u.val ∈ hexaOval[ovalOfV[u]]!) ∧
    (ovalOfV[u] = 6 → pairJ u ≠ pairJ' u ∧ (u = rep2 (pairJ u) (pairJ' u) ∨
      u = rep2W1 (pairJ u) (pairJ' u) ∨ u = rep2W2 (pairJ u) (pairJ' u))) ∧
    (ovalOfV[u] < 6 ∨ ovalOfV[u] = 6) := by
  decide

theorem mem_or_exists_rep2 (u : Fin 64) : (∃ i < 6, u.val ∈ hexaOval[i]!) ∨ ∃ j j' : Fin 6,
    j ≠ j' ∧ (u = rep2 j j' ∨ u = omegaF (rep2 j j') ∨ u = omegaF (omegaF (rep2 j j'))) := by
  obtain ⟨h1, h2, h3⟩ := classify_aux u
  rcases h3 with h3 | h3
  · exact Or.inl ⟨_, h3, h1 h3⟩
  · obtain ⟨h4, h5⟩ := h2 h3
    refine Or.inr ⟨_, _, h4, ?_⟩
    rwa [← rep2W2_eq, ← rep2W1_eq]

theorem conj_synT (σ : Perm (Fin 6)) {j j' : Fin 6} (h : j ≠ j') (y : Fin 6) :
    σ (synT j j' (σ⁻¹ y)) = synT (totalPerm σ j) (totalPerm σ j') y := by
  obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := synT_mem h
  obtain ⟨b, hb⟩ := mapsTotal_totalIdx σ j a
  obtain ⟨b', hb'⟩ := mapsTotal_totalIdx σ j' a'
  have hne : totalPerm σ j ≠ totalPerm σ j' := fun h' => h ((totalPerm σ).injective h')
  have hbb : ∀ z, partner (totalPerm σ j) b z = partner (totalPerm σ j') b' z := fun z => by
    obtain ⟨w, rfl⟩ := σ.surjective z
    rw [totalPerm_apply, totalPerm_apply, ← hb w, ← hb' w, ← ha w, ← ha' w]
  have h1 := hb (σ⁻¹ y)
  have hy : σ (σ⁻¹ y) = y := σ.apply_symm_apply y
  rw [hy] at h1
  rw [ha (σ⁻¹ y), h1, ← totalPerm_apply]
  exact eq_synT hne hbb y

section Rel

variable {M : Type*} [CommGroup M] {q : Fin 64 → M} {b : Fin 64 → Fin 64 → M}
  (h : IsQuadMap q b) (hov : ∀ o : Fin 64, (∃ i : Fin 6, o.val ∈ hexaOval[(i : ℕ)]!) → q o = 1)

include h hov

theorem prod_map_q_eq_one_of_cert {l D : List (Fin 64)}
    (hD : ∀ o ∈ D, ∃ i : Fin 6, o.val ∈ hexaOval[(i : ℕ)]!)
    (h1 : coefSum1 l = coefSum1 D) (h2 : coefSum2 l = coefSum2 D) : (l.map q).prod = 1 :=
  h.prod_map_q_eq_one (fun o ho => hov o (hD o ho)) h1 h2

theorem quad_rel_lt : ∀ j j' : Fin 6, 0 < j → j < j' →
    q (rep2 0 j) * q (rep2 0 j') * q (rep2 j j') = 1 := by
  have key : ∀ (l D : List (Fin 64)), (∀ o ∈ D, ∃ i : Fin 6, o.val ∈ hexaOval[(i : ℕ)]!) →
      coefSum1 l = coefSum1 D → coefSum2 l = coefSum2 D → (l.map q).prod = 1 :=
    fun l D hD h1 h2 => prod_map_q_eq_one_of_cert h hov hD h1 h2
  have k3 : ∀ u v w : Fin 64, ∀ D : List (Fin 64),
      (∀ o ∈ D, ∃ i : Fin 6, o.val ∈ hexaOval[(i : ℕ)]!) →
      coefSum1 [u, v, w] = coefSum1 D → coefSum2 [u, v, w] = coefSum2 D →
      q u * q v * q w = 1 := fun u v w D hD h1 h2 => by
    have := key [u, v, w] D hD h1 h2
    simpa [mul_assoc] using this
  intro j j' hj hjj'
  fin_cases j <;> fin_cases j' <;>
    first | exact absurd hj (by decide) | exact absurd hjj' (by decide) | skip
  · exact k3 _ _ _ [1, 8, 12, 32, 21, 42, 39, 27, 45] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [1, 8, 12, 16, 32, 42, 30, 39, 45] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [2, 3, 4, 16, 32, 42, 39, 27, 45] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [2, 3, 4, 32, 21, 42, 30, 39, 45] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [1, 2, 4, 30, 27] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [1, 2, 3, 4, 8, 12, 16, 32, 21, 42, 39, 27, 45] (by decide) (by decide)
      (by decide)
  · exact k3 _ _ _ [32, 21, 42, 39, 45] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [16, 32, 42, 39, 45] (by decide) (by decide) (by decide)
  · exact k3 _ _ _ [1, 2, 3, 4, 8, 12, 16, 32, 21, 42, 30, 39, 45] (by decide) (by decide)
      (by decide)
  · exact k3 _ _ _ [1, 3, 4, 16, 21] (by decide) (by decide) (by decide)

theorem quad_rel {j j' : Fin 6} (hj : j ≠ 0) (hj' : j' ≠ 0) (hjj' : j ≠ j') :
    q (rep2 0 j) * q (rep2 0 j') * q (rep2 j j') = 1 := by
  have hj0 : 0 < j := Fin.pos_iff_ne_zero.mpr hj
  have hj0' : 0 < j' := Fin.pos_iff_ne_zero.mpr hj'
  rcases lt_or_gt_of_ne hjj' with h' | h'
  · exact quad_rel_lt h hov j j' hj0 h'
  · rw [mul_comm (q (rep2 0 j)), rep2_comm j j']
    exact quad_rel_lt h hov j' j hj0' h'

theorem quad_rel_one :
    q (rep2 0 1) * q (rep2 0 2) * q (rep2 0 3) * q (rep2 0 4) * q (rep2 0 5) = 1 := by
  have := prod_map_q_eq_one_of_cert h hov (l := [rep2 0 1, rep2 0 2, rep2 0 3, rep2 0 4, rep2 0 5])
    (D := [1, 4, 16, 21, 30, 27]) (by decide) (by decide) (by decide)
  simpa [mul_assoc] using this

end Rel

theorem sign_totalPerm (σ : Perm (Fin 6)) : Perm.sign (totalPerm σ) = Perm.sign σ := by
  have hgen : ∀ i : Fin 5, Perm.sign (totalPerm (swap i.castSucc i.succ)) =
      Perm.sign (swap i.castSucc i.succ) := by
    decide +kernel
  have hmul : ∀ x y : Perm (Fin 6), totalPerm (x * y) = totalPerm x * totalPerm y :=
    fun x y => totalPermHom.map_mul x y
  have hone : totalPerm 1 = 1 := totalPermHom.map_one
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
    rw [Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | one => rw [hone]
  | mul x y _ _ hx hy => rw [hmul, map_mul, map_mul, hx, hy]

theorem totalPerm_mem_alternatingGroup {σ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    totalPerm σ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup] at hσ ⊢
  rw [sign_totalPerm, hσ]

@[expose] def totalPermAlt : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
  (totalPermHom.comp (alternatingGroup (Fin 6)).subtype).codRestrict _ fun σ =>
    totalPerm_mem_alternatingGroup σ.2

theorem coe_totalPermAlt (σ : alternatingGroup (Fin 6)) :
    (totalPermAlt σ : Perm (Fin 6)) = totalPerm σ :=
  rfl

theorem totalPermAlt_bijective : Function.Bijective totalPermAlt := by
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hinj : Function.Injective totalPermAlt := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal totalPermAlt.ker with h | h
    · exact h
    · exfalso
      have hc : (⟨swap 0 2 * swap 0 1, by
          rw [Perm.mem_alternatingGroup]; simp [Perm.sign_mul]⟩ :
          alternatingGroup (Fin 6)) ∈ totalPermAlt.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hc
      have h1 := congrArg Subtype.val hc
      rw [coe_totalPermAlt] at h1
      exact absurd h1 (by decide)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

end CFSG.ComponentClassification.AS81.Hexa
