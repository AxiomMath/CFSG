module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Setting
public import CFSG.Geometry.GeneralizedQuadrangles.Counting.Variance

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

@[expose] def centreSet (Γ : SimpleGraph V) (x y z : V) : Set V :=
  traceSet Γ x y ∩ {w | Γ.dist z w = 2}

theorem ncard_centreSet (hΓ : IsThasQuadrangle Γ c q) {x y z : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) (hxz : Γ.dist x z = 4) (hyz : Γ.dist y z = 4)
    (hz : z ∉ clSet Γ x y) : (centreSet Γ x y z).ncard = q + 1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := by
    have hcz : c z = c x :=
      (hP.eq_iff_even_dist c z x).2 (by rw [SimpleGraph.dist_comm, hxz]; exact ⟨2, rfl⟩)
    exact hcz.trans hx
  haveI : Fintype (spanSet Γ x y) := (Set.toFinite _).fintype
  let X : Finset V := (spanSet Γ x y).toFinset
  have hXsub : (X : Set V) ⊆ spanSet Γ x y := by
    intro a ha
    simpa [X] using ha
  have hXcard : X.card = q + 1 := by
    change (spanSet Γ x y).toFinset.card = q + 1
    rw [← Set.ncard_eq_toFinset_card' (spanSet Γ x y)]
    exact hΓ.span x y hx hxy
  have hm : 2 ≤ X.card := by
    rw [hXcard]
    exact Nat.le_succ_of_le hΓ.two_le
  have hqle : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  have hmt : X.card ≤ q ^ 3 := by
    rw [hXcard]
    have h2 : q + 1 ≤ q * q := by
      calc
        q + 1 ≤ q + q := by omega
        _ = 2 * q := by ring
        _ ≤ q * q := Nat.mul_le_mul_right q hΓ.two_le
    have h3 : q * q ≤ q ^ 3 := by
      calc
        q * q = q ^ 2 := by ring
        _ ≤ q ^ 3 := Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 2 ≤ 3)
    omega
  have heq : (X.card - 1) * q ^ 3 = (q ^ 2) ^ 2 := by
    rw [hXcard]
    have hq1 : q + 1 - 1 = q := by omega
    rw [hq1]
    ring
  have hzZ : z ∈ varianceZ Γ c X := by
    rw [mem_varianceZ]
    refine ⟨hz0, ?_⟩
    intro a ha
    have haS : a ∈ spanSet Γ x y := hXsub (by simpa [X] using ha)
    by_contra hlt
    have hle : Γ.dist z a ≤ 2 := by omega
    have hznot : ¬ ∃ w ∈ spanSet Γ x y, Γ.dist z w ≤ 2 := by
      simpa [clSet] using hz
    exact hznot ⟨a, haS, hle⟩
  obtain ⟨k, hk⟩ := centres_const_of_eq hP hT c (s := q ^ 2) (t := q ^ 3)
    hΓ.deg hx hxy hXsub hm hmt heq
  have hsum := sum_centres hP hT c (s := q ^ 2) (t := q ^ 3)
    hΓ.deg hx hxy hXsub hm
  have hsum_const : ∑ w ∈ varianceZ Γ c X, varianceTz Γ (varianceTrace Γ x y) w
      = (varianceZ Γ c X).card * k := by
    rw [Finset.sum_congr rfl (fun w hw => hk w hw), Finset.sum_const, smul_eq_mul]
  have hZk : (varianceZ Γ c X).card * k
      = (q ^ 3 + 1) * (q ^ 3 + 1 - X.card) * q ^ 2 := by
    rw [← hsum_const]
    exact hsum
  have hq_sub : q ^ 3 + 1 - X.card = q ^ 3 - q := by
    rw [hXcard]
    omega
  have hZkNat : (varianceZ Γ c X).card * k
      = (q ^ 3 + 1) * (q ^ 3 - q) * q ^ 2 := by
    rw [hq_sub] at hZk
    exact hZk
  have hle : q ^ 3 ≤ q ^ 5 + q ^ 2 := by
    have h1 : q ^ 3 ≤ q ^ 5 := by
      calc
        q ^ 3 = q ^ 3 * 1 := (Nat.mul_one _).symm
        _ ≤ q ^ 3 * q ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow 2 q (by omega))
        _ = q ^ 5 := by rw [← pow_add]
    omega
  have hZadd : (varianceZ Γ c X).card + q * (q ^ 5 + q ^ 2 - q ^ 3) = q ^ 7 := by
    have h := card_noncollinear_add hP hT c (s := q ^ 2) (t := q ^ 3)
      hΓ.deg hx hxy hXsub hm
    rw [hXcard] at h
    have hq1 : q + 1 - 1 = q := by omega
    rw [hq1] at h
    have h1 : q ^ 2 * q ^ 3 = q ^ 5 := by rw [← pow_add]
    rw [h1] at h
    have h2 : (q ^ 2) ^ 2 * q ^ 3 = q ^ 7 := by
      rw [← pow_mul, ← pow_add]
    rw [h2] at h
    exact h
  have hZaddZ : ((varianceZ Γ c X).card : ℤ)
      + (q : ℤ) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2 - (q : ℤ) ^ 3) = (q : ℤ) ^ 7 := by
    have hcast : ((varianceZ Γ c X).card : ℤ)
        + ((q * (q ^ 5 + q ^ 2 - q ^ 3) : ℕ) : ℤ) = ((q ^ 7 : ℕ) : ℤ) := by
      exact_mod_cast hZadd
    have hcast_sub : ((q * (q ^ 5 + q ^ 2 - q ^ 3) : ℕ) : ℤ)
        = (q : ℤ) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2 - (q : ℤ) ^ 3) := by
      rw [Nat.cast_mul, Nat.cast_sub hle]
      push_cast
      ring
    rw [hcast_sub] at hcast
    push_cast at hcast
    exact hcast
  have hZval : ((varianceZ Γ c X).card : ℤ)
      = (q : ℤ) ^ 7 - (q : ℤ) * ((q : ℤ) ^ 5 + (q : ℤ) ^ 2 - (q : ℤ) ^ 3) := by
    linarith
  have hZfactor : ((varianceZ Γ c X).card : ℤ)
      = (q : ℤ) ^ 3 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) := by
    rw [hZval]
    ring
  have hZkZ : ((varianceZ Γ c X).card : ℤ) * (k : ℤ)
      = ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 - (q : ℤ)) * (q : ℤ) ^ 2 := by
    have hnat : (((varianceZ Γ c X).card * k : ℕ) : ℤ)
        = (((q ^ 3 + 1) * (q ^ 3 - q) * q ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hZkNat
    calc
      ((varianceZ Γ c X).card : ℤ) * (k : ℤ)
          = (((varianceZ Γ c X).card * k : ℕ) : ℤ) := by rw [Nat.cast_mul]
      _ = (((q ^ 3 + 1) * (q ^ 3 - q) * q ^ 2 : ℕ) : ℤ) := hnat
      _ = ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 - (q : ℤ)) * (q : ℤ) ^ 2 := by
            rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hqle]
            push_cast
            ring
  have hmain : ((varianceZ Γ c X).card : ℤ) * (k : ℤ)
      = ((varianceZ Γ c X).card : ℤ) * ((q : ℤ) + 1) := by
    calc
      ((varianceZ Γ c X).card : ℤ) * (k : ℤ)
          = ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 - (q : ℤ)) * (q : ℤ) ^ 2 := hZkZ
      _ = ((q : ℤ) ^ 3 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1)) * ((q : ℤ) + 1) := by
            ring
      _ = ((varianceZ Γ c X).card : ℤ) * ((q : ℤ) + 1) := by rw [hZfactor]
  have hZpos : (0 : ℤ) < (varianceZ Γ c X).card := by
    have hpos : 0 < (varianceZ Γ c X).card := Finset.card_pos.mpr ⟨z, hzZ⟩
    exact_mod_cast hpos
  have hkq : k = q + 1 := by
    have hkqZ : (k : ℤ) = (q : ℤ) + 1 :=
      mul_left_cancel₀ (ne_of_gt hZpos) hmain
    exact_mod_cast hkqZ
  have htz : varianceTz Γ (varianceTrace Γ x y) z = q + 1 := by
    rw [hk z hzZ, hkq]
  have hfilter_eq : (varianceTrace Γ x y).filter (fun u => Γ.dist z u = 2)
      = (varianceTrace Γ x y).filter (fun u => Γ.dist z u ≤ 2) := by
    refine Finset.filter_congr fun u hu => ?_
    exact ⟨fun h => le_of_eq h,
      fun h => dist_eq_two_of_le_two_of_mem_varianceZ_of_mem_varianceTrace hP hT c hΓ.deg
        hx hxy hXsub hm hzZ hu h⟩
  have hcentre_eq : centreSet Γ x y z
      = ↑((varianceTrace Γ x y).filter (fun u => Γ.dist z u = 2)) := by
    ext u
    simp [centreSet, mem_varianceTrace]
  rw [hcentre_eq, Set.ncard_coe_finset, hfilter_eq]
  exact htz

theorem centreSet_eq_spanSet (hΓ : IsThasQuadrangle Γ c q) {x y z : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) (hxz : Γ.dist x z = 4) (hyz : Γ.dist y z = 4)
    (hz : z ∉ clSet Γ x y) {u v : V} (hu : u ∈ centreSet Γ x y z) (hv : v ∈ centreSet Γ x y z)
    (huv : u ≠ v) : centreSet Γ x y z = spanSet Γ u v := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hcentre_card : (centreSet Γ x y z).ncard = q + 1 :=
    ncard_centreSet hΓ hx hxy hxz hyz hz
  have hu_trace : u ∈ traceSet Γ x y := hu.1
  have hv_trace : v ∈ traceSet Γ x y := hv.1
  have hzu : Γ.dist z u = 2 := hu.2
  have hzv : Γ.dist z v = 2 := hv.2
  have huv4 : Γ.dist u v = 4 :=
    dist_eq_four_of_mem_trace hP hxy hu_trace hv_trace huv
  have hu0 : c u = 0 := by
    rw [← hx]
    exact (hP.eq_iff_even_dist c u x).2
      (by rw [SimpleGraph.dist_comm, hu_trace.1]; norm_num)
  have hx_trace : x ∈ traceSet Γ u v :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hu_trace.1,
      by rw [SimpleGraph.dist_comm]; exact hv_trace.1⟩
  have hy_trace : y ∈ traceSet Γ u v :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hu_trace.2,
      by rw [SimpleGraph.dist_comm]; exact hv_trace.2⟩
  have hz_trace : z ∈ traceSet Γ u v :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hzu,
      by rw [SimpleGraph.dist_comm]; exact hzv⟩
  have hspan_subset : spanSet Γ u v ⊆ centreSet Γ x y z := by
    intro w hw
    have hwx : Γ.dist w x = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT huv4 hw hx_trace
    have hwy : Γ.dist w y = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT huv4 hw hy_trace
    have hwz : Γ.dist w z = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT huv4 hw hz_trace
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show Γ.dist x w = 2
      simpa only [SimpleGraph.dist_comm] using hwx
    · show Γ.dist y w = 2
      simpa only [SimpleGraph.dist_comm] using hwy
    · show Γ.dist z w = 2
      simpa only [SimpleGraph.dist_comm] using hwz
  have hspan_card : (spanSet Γ u v).ncard = q + 1 := hΓ.span u v hu0 huv4
  have hle : (centreSet Γ x y z).ncard ≤ (spanSet Γ u v).ncard := by
    rw [hcentre_card, hspan_card]
  exact (Set.eq_of_subset_of_ncard_le hspan_subset hle).symm

end CFSG.Geometry.GeneralizedQuadrangles
