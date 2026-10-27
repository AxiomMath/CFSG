module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistDefs
public import CFSG.Sporadic.FischerOddCore.Fi23NoComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Sporadic.FischerOddCore


private theorem d1_ne_d : d1 ≠ d := d1_mem_localClass.2.1

private theorem c39_ne_d : c39 ≠ d := by
  have h := conjPt_ne (i := 39) (j := 0) (by norm_num) (by norm_num) (by norm_num)
  rwa [conjPt_zero] at h

private theorem c39_ne_d1 : c39 ≠ d1 := conjPt_ne (by norm_num) (by norm_num) (by norm_num)

private theorem mem_centralizer_of_conj {x u : J} (h : x * u * x⁻¹ = u) :
    x ∈ Subgroup.centralizer ({u} : Set J) :=
  (Subgroup.mem_centralizer_singleton_iff (G := J)).2 (mul_inv_eq_iff_eq_mul.1 h)

private theorem conj_of_mem_centralizer {x u : J} (h : x ∈ Subgroup.centralizer ({u} : Set J)) :
    x * u * x⁻¹ = u := by
  rw [(Subgroup.mem_centralizer_singleton_iff (G := J)).1 h, mul_inv_cancel_right]

private theorem conj_commute {g u v : J} (huv : u * v = v * u) (hv : g * v * g⁻¹ = v) :
    g * u * g⁻¹ * v = v * (g * u * g⁻¹) := by
  calc g * u * g⁻¹ * v = g * u * g⁻¹ * (g * v * g⁻¹) := by rw [hv]
    _ = g * (u * v) * g⁻¹ := by group
    _ = g * (v * u) * g⁻¹ := by rw [huv]
    _ = g * v * g⁻¹ * (g * u * g⁻¹) := by group
    _ = v * (g * u * g⁻¹) := by rw [hv]

private theorem map_conj_inv_le {h u : J} {D : Subgroup J}
    (hD : D ≤ Subgroup.centralizer ({h * u * h⁻¹} : Set J)) :
    D.map (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.centralizer ({u} : Set J) := by
  have := map_conj_le_centralizer_singleton h⁻¹ hD
  rwa [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group] at this

private theorem card_map_conj (g : J) (D : Subgroup J) :
    Nat.card (D.map (MulAut.conj g).toMonoidHom) = Nat.card D :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

private theorem isPGroup_of_elem {D : Subgroup J} (hD : IsElemAbelian 3 D) : IsPGroup 3 D :=
  fun g => ⟨1, Subtype.ext (by simpa using hD.2 g g.2)⟩

private theorem fix_of_fix_d
    {x : J} {a : ℕ}
    (hx3 : x ^ 3 ^ a = 1) (ht : x ∈ Subgroup.centralizer ({t2} : Set J)) (hd : x * d * x⁻¹ = d) :
    x * d1 * x⁻¹ = d1 ∧ x * c39 * x⁻¹ = c39 := by
  have inj : ∀ {u v : J}, x * u * x⁻¹ = x * v * x⁻¹ → u = v :=
    fun h => mul_left_cancel (mul_right_cancel h)
  have h1 := fi23_triple_invariant x ht d1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h2 := fi23_triple_invariant x ht c39
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h2 with h2 | h2 | h2
  · exact absurd (inj (h2.trans hd.symm)) c39_ne_d
  · rcases h1 with h1 | h1 | h1
    · exact absurd (inj (h1.trans hd.symm)) d1_ne_d
    · exact absurd (inj (h2.trans h1.symm)) c39_ne_d1
    · exact (not_swap hx3 c39_ne_d1.symm h1 h2).elim
  · rcases h1 with h1 | h1 | h1
    · exact absurd (inj (h1.trans hd.symm)) d1_ne_d
    · exact ⟨h1, h2⟩
    · exact absurd (inj (h2.trans h1.symm)) c39_ne_d1

private theorem orbit_root_subset
    {P : Subgroup J}
    (hP : P ≤ Subgroup.centralizer ({t2} : Set J)) :
    MulAction.orbit P root ⊆
      ({root, ⟨1, by norm_num⟩, ⟨39, by norm_num⟩} : Set (Fin 31671)) := by
  intro y hy
  obtain ⟨p, rfl⟩ := MulAction.mem_orbit_iff.1 hy
  have e : conjPt (p • root).val = (p : J) * d * (p : J)⁻¹ := by
    rw [Subgroup.smul_def, conjPt_smul]
    show (p : J) * conjPt 0 * (p : J)⁻¹ = _
    rw [conjPt_zero]
  have h := fi23_triple_invariant (p : J) (hP p.2) d (Set.mem_insert _ _)
  rw [← e] at h
  have hv : (p • root).val < orb.keys.size := by rw [orb_size]; exact (p • root).isLt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with h | h | h
  · exact Or.inl (Fin.ext (conjPt_inj (j := 0) hv (by rw [orb_size]; norm_num)
      (h.trans conjPt_zero.symm)))
  · exact Or.inr (Or.inl (Fin.ext (conjPt_inj (j := 1) hv (by rw [orb_size]; norm_num) h)))
  · exact Or.inr (Or.inr (Fin.ext (conjPt_inj (j := 39) hv (by rw [orb_size]; norm_num) h)))

private theorem card_lt_of_le_cdc (hB : FactB) {S : Subgroup J}
    (hS : IsPGroup 3 S)
    (hH : S ≤ Subgroup.centralizer ({d} : Set J) ⊓ Subgroup.centralizer ({d1} : Set J))
    (hc : S ≤ Subgroup.centralizer ({c39} : Set J)) : Nat.card S < 243 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQH, hQ, -, h4⟩ := hB
  obtain ⟨g, hgH, hg⟩ := exists_conj_into_of_card hQH
    (by rw [hQ, factorization_centralizer_d_d1]; norm_num) hH hS
  have hgd : g * d * g⁻¹ = d := conj_of_mem_centralizer (Subgroup.mem_inf.1 hgH).1
  have hgd1 : g * d1 * g⁻¹ = d1 := conj_of_mem_centralizer (Subgroup.mem_inf.1 hgH).2
  obtain ⟨i, hk⟩ : ∃ i : Fin 31671, conjPt i.val = g * c39 * g⁻¹ :=
    ⟨_, conjPt_smul g ⟨39, by norm_num⟩⟩
  have inj : ∀ {u v : J}, g * u * g⁻¹ = g * v * g⁻¹ → u = v :=
    fun h => mul_left_cancel (mul_right_cancel h)
  have hk0 : i.val ≠ 0 := fun h0 => by
    rw [h0, conjPt_zero, ← hgd] at hk
    exact c39_ne_d (inj hk).symm
  have hk1 : i.val ≠ 1 := fun h1 => by
    rw [h1, show conjPt 1 = d1 from rfl, ← hgd1] at hk
    exact c39_ne_d1 (inj hk).symm
  have hle : S.map (MulAut.conj g).toMonoidHom ≤
      Q ⊓ Subgroup.centralizer ({conjPt i.val} : Set J) := by
    refine le_inf hg ?_
    rw [hk]
    exact map_conj_le_centralizer_singleton g hc
  have := (Subgroup.card_le_of_le hle).trans_lt (h4 i.val i.isLt hk0 hk1
    (by rw [hk]; exact conj_commute c39_commute_d hgd)
    (by rw [hk]; exact conj_commute c39_commute_d1 hgd1))
  rwa [card_map_conj] at this

private theorem not_card_729
    (hB : FactB) {P : Subgroup J}
    (hP : P ≤ Subgroup.centralizer ({t2} : Set J)) (hcard : Nat.card P = 729) : False := by
  have hind : (MulAction.stabilizer P root).index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard (orbit_root_subset hP) (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
        (by rw [Set.ncard_singleton]))))
  have hS : 243 ≤ Nat.card (MulAction.stabilizer P root) := by
    have h1 := (MulAction.stabilizer P root).card_mul_index
    rw [hcard] at h1
    have := Nat.mul_le_mul_left (Nat.card (MulAction.stabilizer P root)) hind
    omega
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  have hS0 : ∀ x ∈ (MulAction.stabilizer P root).map P.subtype,
      x * d * x⁻¹ = d ∧ x * d1 * x⁻¹ = d1 ∧ x * c39 * x⁻¹ = c39 := by
    rintro _ ⟨p, hp, rfl⟩
    have hpd : (p : J) * d * (p : J)⁻¹ = d := by
      have hs : p • root = root := MulAction.mem_stabilizer_iff.1 hp
      rw [Subgroup.smul_def] at hs
      have := (smul_eq_iff (p : J) root root).1 hs
      change (p : J) * conjPt 0 * (p : J)⁻¹ = conjPt 0 at this
      rwa [conjPt_zero] at this
    have hp3 : p ^ 3 ^ 6 = 1 := by
      have h0 : p ^ Nat.card P = 1 := pow_card_eq_one'
      rwa [hcard, show (729 : ℕ) = 3 ^ 6 by norm_num] at h0
    have hp3' : (p : J) ^ 3 ^ 6 = 1 := by rw [← Subgroup.coe_pow, hp3, Subgroup.coe_one]
    exact ⟨hpd, fix_of_fix_d hp3' (hP p.2) hpd⟩
  have hlt := card_lt_of_le_cdc hB (hPp.to_le (Subgroup.map_subtype_le _))
    (fun x hx => Subgroup.mem_inf.2 ⟨mem_centralizer_of_conj (hS0 x hx).1,
      mem_centralizer_of_conj (hS0 x hx).2.1⟩)
    (fun x hx => mem_centralizer_of_conj (hS0 x hx).2.2)
  rw [Subgroup.card_map_of_injective P.subtype_injective] at hlt
  omega

theorem factorization_centralizer_t2
    (hB : FactB) (hC : FactC) :
    (Nat.card ↥(Subgroup.centralizer ({t2} : Set J))).factorization 3 = 5 := by
  have hn : Nat.card ↥(Subgroup.centralizer ({t2} : Set J)) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨Q, hQ, hQc, -⟩ := hC
  have h5 : 5 ≤ (Nat.card ↥(Subgroup.centralizer ({t2} : Set J))).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn).1
      (by rw [show 3 ^ 5 = 243 by norm_num, ← hQc]; exact Subgroup.card_dvd_of_le hQ)
  refine le_antisymm (not_lt.1 fun h6 => ?_) h5
  obtain ⟨P, hP, -, hPC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 6)
    (H := ⊥) (by rw [Subgroup.card_bot]; exact one_dvd _)
    ((Nat.prime_three.pow_dvd_iff_le_factorization hn).2 (by omega)) bot_le
  exact not_card_729 hB hPC (by rw [hP]; norm_num)

theorem closed_of_twoC
    (hB : FactB) (hC : FactC)
    {D : Subgroup J} (hD : IsElemAbelian 3 D) (hc : Nat.card D = 81) {z : J}
    (hz : IsConj t2 z) (hDz : D ≤ Subgroup.centralizer ({z} : Set J)) :
    PElemsClosed 3 (Subgroup.centralizer (D : Set J)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 := factorization_centralizer_t2 hB hC
  obtain ⟨Q, hQ, hQc, hcl⟩ := hC
  obtain ⟨h, rfl⟩ := isConj_iff.1 hz
  have hD' := isElemAbelian_map' (MulAut.conj h⁻¹).toMonoidHom hD
  obtain ⟨g, -, hg⟩ := exists_conj_into_of_card hQ (by rw [hQc, h5]; norm_num)
    (map_conj_inv_le hDz) (isPGroup_of_elem hD')
  exact pElemsClosed_of_map_conj h⁻¹ (pElemsClosed_of_map_conj g
    (hcl _ hg (isElemAbelian_map' _ hD') (by rw [card_map_conj, card_map_conj, hc])))

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist
