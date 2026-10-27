module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Lift
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Count
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedTorus

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.Open CFSG.SectionRank

section Torus

variable {K : Type} [Field K] [Finite K]

theorem torusGroup_le_adjointGroup' : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨q, rfl⟩
    exact torusElt_mem_adjointGroup q.1 q.2)

@[expose] noncomputable def torusCoordAdj :
    (Fin Tag.E6.rank → Kˣ) →* adjointGroup Tag.E6 K where
  toFun c := ⟨(torusCoordHom Tag.E6 K c : (Module.End K (RootModule Tag.E6 K))ˣ),
    torusGroup_le_adjointGroup' (torusCoordHom Tag.E6 K c).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' c d := Subtype.ext (by simp)

theorem coe_torusCoordAdj (c : Fin Tag.E6.rank → Kˣ) :
    ((torusCoordAdj (K := K) c : adjointGroup Tag.E6 K) :
      (Module.End K (RootModule Tag.E6 K))ˣ) =
      (torusCoordHom Tag.E6 K c : (Module.End K (RootModule Tag.E6 K))ˣ) := rfl

theorem torusCoordAdj_eq_one_iff (c : Fin Tag.E6.rank → Kˣ) :
    torusCoordAdj (K := K) c = 1 ↔ zpowMatrix Tag.E6.cartan c = 1 := by
  rw [← torusCoordHom_eq_one_iff]
  constructor
  · intro h
    refine Subtype.ext ?_
    have := congrArg
      (fun x : adjointGroup Tag.E6 K => (x : (Module.End K (RootModule Tag.E6 K))ˣ)) h
    exact this
  · intro h
    refine Subtype.ext ?_
    have := congrArg (fun x : torusGroup Tag.E6 K =>
      (x : (Module.End K (RootModule Tag.E6 K))ˣ)) h
    exact this

theorem card_ker_torusCoordAdj :
    Nat.card (torusCoordAdj (K := K)).ker = (Nat.card K - 1).gcd 3 := by
  have h := card_torusGroup_mul (τ := Tag.E6) (K := K)
  have h2 := card_torusGroup_E6 (K := K)
  have hker : (torusCoordAdj (K := K)).ker = (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, torusCoordAdj_eq_one_iff]
  rw [hker]
  have hpos : 0 < Nat.card (torusGroup Tag.E6 K) := Nat.card_pos
  have h2' : Nat.card (torusGroup Tag.E6 K) * (Nat.card K - 1).gcd 3 =
      (Nat.card K - 1) ^ Tag.E6.rank := h2
  exact Nat.eq_of_mul_eq_mul_left hpos (h.trans h2'.symm)

theorem pow_three_eq_one_of_mem_ker (h3 : 3 ∣ Nat.card K - 1)
    {z : Fin Tag.E6.rank → Kˣ} (hz : z ∈ (torusCoordAdj (K := K)).ker) : z ^ 3 = 1 := by
  have hc : Nat.card (torusCoordAdj (K := K)).ker = 3 := by
    rw [card_ker_torusCoordAdj, Nat.gcd_eq_right h3]
  have := pow_card_eq_one' (G := (torusCoordAdj (K := K)).ker) (x := ⟨z, hz⟩)
  rw [hc] at this
  exact congrArg Subtype.val this

theorem card_ker_pow_three (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (powMonoidHom 3 : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ)).ker =
      3 ^ Tag.E6.rank := by
  have h := card_ker_zpowMatrix_diagonal (G := Kˣ) (n := Tag.E6.rank) (fun _ => 3)
  have heq : (zpowMatrix (G := Kˣ) (Matrix.diagonal fun _ : Fin Tag.E6.rank => ((3 : ℕ) : ℤ))) =
      (powMonoidHom 3 : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ)) := by
    refine MonoidHom.ext fun t => funext fun j => ?_
    rw [zpowMatrix_apply, Finset.prod_eq_single j (fun i _ hij => by
      rw [Matrix.diagonal_apply_ne _ hij, zpow_zero]) (fun h => absurd (Finset.mem_univ j) h),
      Matrix.diagonal_apply_eq, zpow_natCast, powMonoidHom_apply, Pi.pow_apply]
  rw [heq] at h
  rw [h]
  simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.gcd_eq_right h3]

theorem exists_elemAbelian_E6_torus (h3 : 3 ∣ Nat.card K - 1) (h9 : 9 ∣ Nat.card K - 1) :
    ∃ E : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  have h9' : 9 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact h9
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_of_cube_kernel (torusCoordAdj (K := K))
    (fun z hz => by
      have hz3 := pow_three_eq_one_of_mem_ker h3 hz
      refine ⟨fun i => (exists_cube_of_pow_eq_one h9' (x := z i) (by
        have := congrFun hz3 i
        simpa using this)).choose, funext fun i => ?_⟩
      exact (exists_cube_of_pow_eq_one h9' (x := z i) (by
        have := congrFun hz3 i
        simpa using this)).choose_spec)
  refine ⟨E, hE, ?_⟩
  rw [hcard, card_ker_pow_three h3]
  rfl

theorem mem_zpowers_of_pow_three {ζ : Kˣ} (hζ : orderOf ζ = 3) (h3 : 3 ∣ Nat.card K - 1)
    {y : Kˣ} (hy : y ^ 3 = 1) : y ∈ Subgroup.zpowers ζ := by
  have hle : Subgroup.zpowers ζ ≤ (powMonoidHom 3 : Kˣ →* Kˣ).ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker, powMonoidHom_apply, ← hζ]
    exact pow_orderOf_eq_one ζ
  have hcard : Nat.card (powMonoidHom 3 : Kˣ →* Kˣ).ker ≤ Nat.card (Subgroup.zpowers ζ) := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_eq_right h3,
      Nat.card_zpowers, hζ]
  have := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [this, MonoidHom.mem_ker, powMonoidHom_apply]
  exact hy

theorem weylElt_conj_torusCoordAdj (i : Fin Tag.E6.rank) (c : Fin Tag.E6.rank → Kˣ) :
    (⟨weylElt Tag.E6 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup Tag.E6 K) *
        torusCoordAdj c *
        (⟨weylElt Tag.E6 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup Tag.E6 K)⁻¹ =
      torusCoordAdj (coordReflect Tag.E6 i c) := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  exact weylElt_conj_torusCoordHom i c

theorem six_le_pRank_of_cover_E6 (h3 : 3 ∣ Nat.card K - 1) {L : Type} [Group L] [Finite L]
    (π : L →* adjointGroup Tag.E6 K) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center L) (hZ : 3 ∣ Nat.card (Subgroup.center L)) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h3)
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  set g : (Fin Tag.E6.rank → Kˣ) →* adjointGroup Tag.E6 K := torusCoordAdj with hg
  set e : Fin Tag.E6.rank → adjointGroup Tag.E6 K := fun i => g (Pi.mulSingle i ζ) with he
  set n : Fin Tag.E6.rank → adjointGroup Tag.E6 K := fun i =>
    ⟨weylElt Tag.E6 K i 1, weylElt_mem_adjointGroup i 1⟩ with hn
  have hsingle_zpow : ∀ (i : Fin Tag.E6.rank) (m : ℤ),
      (Pi.mulSingle i (ζ ^ m) : Fin Tag.E6.rank → Kˣ) = (Pi.mulSingle i ζ) ^ m := by
    intro i m
    exact (MonoidHom.mulSingle (fun _ : Fin Tag.E6.rank => Kˣ) i).map_zpow ζ m
  have hrel' : ∀ i j, n i * e j * (n i)⁻¹ = e j * e i ^ (-Tag.E6.cartan j i) := by
    intro i j
    have h1 : coordReflect Tag.E6 i (Pi.mulSingle j ζ : Fin Tag.E6.rank → Kˣ) =
        Pi.mulSingle j ζ * (Pi.mulSingle i ζ) ^ (-Tag.E6.cartan j i) := by
      rw [coordReflect, ← hsingle_zpow]
      congr 2
      rw [Finset.prod_eq_single j]
      · simp
      · intro k _ hk
        simp [Pi.mulSingle_apply, hk]
      · simp
    calc n i * e j * (n i)⁻¹ = g (coordReflect Tag.E6 i (Pi.mulSingle j ζ)) :=
          weylElt_conj_torusCoordAdj i _
      _ = e j * e i ^ (-Tag.E6.cartan j i) := by rw [h1, map_mul, map_zpow]
  have hrel : ∀ i j, ∃ k : ℤ, n i * e j * (n i)⁻¹ = e j * e i ^ k := fun i j =>
    ⟨_, hrel' i j⟩
  have hinv : ∀ i, n i * e i * (n i)⁻¹ = (e i)⁻¹ := by
    intro i
    have hk := hrel' i i
    rw [Tag.cartan_self] at hk
    rw [hk]
    group
  have hcomm : ∀ i j, e i * e j = e j * e i := fun i j => by
    simp only [he, ← map_mul, mul_comm]
  have he3 : ∀ i, e i ^ 3 = 1 := by
    intro i
    simp only [he, ← map_pow]
    have : (Pi.mulSingle i ζ : Fin Tag.E6.rank → Kˣ) ^ 3 = 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hζ3]
      · simp [Pi.mulSingle_apply, hj]
    rw [this, map_one]
  obtain ⟨R, hR3, hRc, hRmap⟩ := exists_elemAbelian_of_reflection_lifts π hπ
    (fun x hx => (hker x).1 hx) e n hcomm he3 hinv hrel
  set cl0 : Subgroup (Fin Tag.E6.rank → Kˣ) :=
    Subgroup.closure (Set.range fun i => (Pi.mulSingle i ζ : Fin Tag.E6.rank → Kˣ)) with hcl0
  have hker_cl0 : (powMonoidHom 3 : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ)).ker ≤
      cl0 := by
    intro x hx
    have hx3 : x ^ 3 = 1 := hx
    have hxi : ∀ i, ∃ m : ℤ, ζ ^ m = x i := fun i =>
      Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_three hζ h3 (by
        have := congrFun hx3 i
        simpa using this))
    choose m hm using hxi
    have hxeq : x = ∏ i, (Pi.mulSingle i ζ : Fin Tag.E6.rank → Kˣ) ^ m i := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle x]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hsingle_zpow, hm]
    rw [hxeq]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _
      (Subgroup.subset_closure (Set.mem_range_self i)) _
  have hD0 : ((powMonoidHom 3 : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ)).ker).map g ≤
      R.map π := by
    rw [hRmap]
    refine (Subgroup.map_mono hker_cl0).trans ?_
    rw [hcl0, MonoidHom.map_closure, ← Set.range_comp]
    exact le_rfl
  have hcardker := card_ker_pow_le_card_map_mul g
  rw [card_ker_pow_three h3] at hcardker
  have hgker : Nat.card g.ker = 3 := by
    rw [hg, card_ker_torusCoordAdj, Nat.gcd_eq_right h3]
  rw [hgker] at hcardker
  have hbig : 3 ^ 5 ≤ Nat.card (R.map π) := by
    have h1 : 3 ^ 6 ≤ Nat.card ((R.map π)) * 3 :=
      hcardker.trans (Nat.mul_le_mul_right _ (Nat.card_mono (Set.toFinite _) hD0))
    have h6 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
    exact Nat.le_of_mul_le_mul_right (h6 ▸ h1) (by norm_num)
  have := pRank_ge_of_lift π hker R hR3 hRc hZ hbig
  simpa using this

end Torus

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
