module

public import Certificates.Certificate450101
public import CFSG.Quasithin.Background.HMathieuO2Data

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

theorem testBit_foldl_or (l : List ℕ) : ∀ (b n : ℕ),
    (l.foldl (fun b m => b ||| 1 <<< m) b).testBit n = (b.testBit n || decide (n ∈ l)) := by
  induction l with
  | nil => intro b n; simp
  | cons a l ih =>
    intro b n
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h1 : a = n <;> by_cases h2 : n ∈ l <;> simp [h1, h2, eq_comm]

theorem testBit_bitsOf (l : List ℕ) (n : ℕ) : (bitsOf l).testBit n = decide (n ∈ l) := by
  rw [bitsOf, testBit_foldl_or, Nat.zero_testBit, Bool.false_or]

@[expose] def Duad : Set W11 := {v | ∃ m ∈ o2Masks24, toW 11 m = v}

theorem o2_lt : ∀ m ∈ o2Masks24, m < 2048 :=
  (Certificates.certificate450101).1.2.2

theorem o2_nodup :
    o2Masks24.Nodup ∧ ∀ m ∈ o2Masks24, (1 ||| 1 <<< 31).testBit m = false :=
  nodup_of_nodupB _ _ (Certificates.certificate450101).1.1

theorem mem_Duad_toW {m : ℕ} (hm : m < 2048) :
    toW 11 m ∈ Duad ↔ m ∈ o2Masks24 := by
  refine ⟨fun ⟨m', hm', h⟩ => ?_, fun h => ⟨m, h, rfl⟩⟩
  rw [toW_inj (o2_lt m' hm') hm h] at hm'
  exact hm'

theorem one_not_mem_Duad : (1 : W11) ∉ Duad := by
  rintro ⟨m, hm, h⟩
  have hm0 : m = 0 := toW_inj (o2_lt m hm) (by norm_num) (h.trans (toW_zero 11).symm)
  have := o2_nodup.2 m hm
  rw [hm0] at this
  exact absurd this (by decide)

theorem z0_not_mem_Duad : z0 ∉ Duad := by
  rintro ⟨m, hm, h⟩
  have hm0 : m = 31 := toW_inj (o2_lt m hm) (by norm_num) h
  have := o2_nodup.2 m hm
  rw [hm0] at this
  exact absurd this (by decide)

theorem pair_z0_ne_one : z0 ≠ 1 := by
  intro h
  have : (31 : ℕ) = 0 := toW_inj (by norm_num) (by norm_num) (h.trans (toW_zero 11).symm)
  omega

theorem kappa_pairVec_mem_Duad (k l : Fin 24) (hkl : k ≠ l) :
    cocodeCoords.κ (pairVec k l) ∈ Duad := by
  rw [kappa11_pairVec_mask k l hkl]
  refine ⟨pairImg11 k l, ?_, rfl⟩
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h | h
  · simp only [o2Masks24, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨k, k.2, l, ⟨l.2, h⟩, rfl⟩
  · have e : pairImg11 k l = pairImg11 l k := by
      simp only [pairImg11, pairMask]
      rw [Nat.xor_comm]
    rw [e]
    simp only [o2Masks24, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨l, l.2, k, ⟨k.2, h⟩, rfl⟩

theorem apply_mem_Duad {g : MulAut W11} (hg : g ∈ img11 AutPerm) {v : W11} (hv : v ∈ Duad) :
    g v ∈ Duad := by
  obtain ⟨σ, -, rfl⟩ := hg
  obtain ⟨m, hm, rfl⟩ := hv
  obtain ⟨i, j, hij, hmij⟩ := toW_o2_24 hm
  rw [hmij, rho11_pairVec AutPerm le_rfl σ i j]
  exact kappa_pairVec_mem_Duad _ _ (fun h => hij ((σ : Equiv.Perm (Fin 24)).injective h))

theorem ncard_Duad : Duad.ncard = 276 := by
  classical
  have hinj : (o2Masks24.map (toW 11)).Nodup :=
    o2_nodup.1.map_on fun a ha b hb hab => toW_inj (o2_lt a ha) (o2_lt b hb) hab
  have hset : Duad = ((o2Masks24.map (toW 11)).toFinset : Set W11) := by
    ext v
    simp only [Duad, Set.mem_setOf_eq, List.coe_toFinset, List.mem_map]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, List.length_map,
    (Certificates.certificate450101).1.2.1]

theorem orbit_subset :
    MulAction.orbit ↥(img11 AutPerm) z0 ⊆ {v | v ≠ 1 ∧ v ∉ Duad} := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  refine ⟨fun h => pair_z0_ne_one (g.injective (h.trans (map_one g).symm)), fun h => ?_⟩
  have hg' : g⁻¹ ∈ img11 AutPerm := (img11 AutPerm).inv_mem hg
  have h2 : g⁻¹ (g z0) ∈ Duad := apply_mem_Duad hg' h
  have e : g⁻¹ (g z0) = z0 := MulAut.inv_apply_self _ _ z0
  exact z0_not_mem_Duad ((congrArg (· ∈ Duad) e).mp h2)

theorem ncard_nonDuad :
    ({v | v ≠ 1 ∧ v ∉ Duad} : Set W11).ncard = 1771 := by
  have hset : ({v | v ≠ 1 ∧ v ∉ Duad} : Set W11) = (insert 1 Duad)ᶜ := by
    ext v
    simp [not_or]
  rw [hset, Set.ncard_compl, Set.ncard_insert_of_notMem one_not_mem_Duad, ncard_Duad,
    natCard_W11]
  norm_num

theorem orbit_eq :
    MulAction.orbit ↥(img11 AutPerm) z0 = {v | v ≠ 1 ∧ v ∉ Duad} :=
  Set.eq_of_subset_of_ncard_le orbit_subset (by rw [ncard_nonDuad]; exact le_card_orbit)

@[expose] def D0 : Set W11 :=
  {v | v ≠ 1 ∧ v ∉ MulAction.orbit ↥(img11 AutPerm) z0 ∧ v * z0 ≠ 1 ∧
    v * z0 ∉ MulAction.orbit ↥(img11 AutPerm) z0}

theorem mem_D0_iff {v : W11} :
    v ∈ D0 ↔ v ∈ Duad ∧ v * z0 ∈ Duad := by
  have h1 : ∀ w : W11, (w ≠ 1 ∧ w ∉ MulAction.orbit ↥(img11 AutPerm) z0) ↔ w ∈ Duad := by
    intro w
    rw [orbit_eq]
    constructor
    · rintro ⟨hw, hn⟩
      by_contra hd
      exact hn ⟨hw, hd⟩
    · intro hd
      exact ⟨fun h => one_not_mem_Duad (h ▸ hd), fun h => h.2 hd⟩
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨(h1 v).1 ⟨a, b⟩, (h1 (v * z0)).1 ⟨c, d⟩⟩,
    fun ⟨a, b⟩ => ⟨((h1 v).2 a).1, ((h1 v).2 a).2, ((h1 _).2 b).1, ((h1 _).2 b).2⟩⟩

theorem toW_mul_z0 (m : ℕ) : toW 11 m * z0 = toW 11 (m ^^^ 31) := (toW_xor 11 m 31).symm

theorem d0_lt : ∀ m ∈ d0Data, m < 2048 := by
  intro m hm
  have h := List.all_eq_true.1 (Certificates.certificate450101).2.2.1 m hm
  rw [Bool.and_eq_true, duadBits, testBit_bitsOf, testBit_bitsOf] at h
  exact o2_lt m (of_decide_eq_true h.1)

theorem mem_D0_toW {m : ℕ} (hm : m < 2048) :
    toW 11 m ∈ D0 ↔ m ∈ d0Data := by
  have hm' : m < 2 ^ 11 := hm
  rw [mem_D0_iff, toW_mul_z0, mem_Duad_toW hm,
    mem_Duad_toW (Nat.xor_lt_two_pow hm' (by norm_num : 31 < 2 ^ 11))]
  constructor
  · rintro ⟨h1, h2⟩
    have h := List.all_eq_true.1 (Certificates.certificate450101).2.2.2.1 m h1
    have hb : duadBits.testBit (m ^^^ 31) = true := by
      rw [duadBits, testBit_bitsOf]
      exact decide_eq_true h2
    rw [hb, Bool.not_true, Bool.false_or, d0Bits, testBit_bitsOf] at h
    exact of_decide_eq_true h
  · intro hd
    have h := List.all_eq_true.1 (Certificates.certificate450101).2.2.1 m hd
    rw [Bool.and_eq_true, duadBits, testBit_bitsOf, testBit_bitsOf] at h
    exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

theorem D0_eq :
    D0 = ((d0Data.map (toW 11)).toFinset : Set W11) := by
  classical
  ext v
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  rw [mem_D0_toW hm]
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  constructor
  · intro h
    exact ⟨m, h, rfl⟩
  · rintro ⟨m', hm', h⟩
    rw [toW_inj (d0_lt m' hm') hm h] at hm'
    exact hm'

theorem ncard_D0 : D0.ncard = 36 := by
  classical
  have hinj : (d0Data.map (toW 11)).Nodup :=
    (nodup_of_nodupB _ _ (Certificates.certificate450101).2.1.1).1.map_on
      fun a ha b hb hab => toW_inj (d0_lt a ha) (d0_lt b hb) hab
  rw [D0_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, List.length_map,
    (Certificates.certificate450101).2.1.2]

theorem D0_invariant {g : MulAut W11}
    (hg : g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) {v : W11} (hv : v ∈ D0) :
    g v ∈ D0 := by
  rw [mem_D0_iff] at hv ⊢
  refine ⟨apply_mem_Duad hg.1 hv.1, ?_⟩
  have hz : g z0 = z0 := mem_centSub_zpowers.1 hg.2
  have e : g v * z0 = g (v * z0) := by rw [map_mul, hz]
  rw [e]
  exact apply_mem_Duad hg.1 hv.2

abbrev t0 : W11 := toW 11 32

theorem t0_mem_D0 : t0 ∈ D0 :=
  (mem_D0_toW (by norm_num)).2 (by decide)

theorem t0_mul_z0 : t0 * z0 = toW 11 63 := by
  rw [toW_mul_z0]
  rfl

theorem t0_mul_z0_mem_D0 : t0 * z0 ∈ D0 := by
  rw [t0_mul_z0]
  exact (mem_D0_toW (by norm_num)).2 (by decide)

theorem exists_apply_t0_eq {v : W11} (hv : v ∈ D0) :
    ∃ g ∈ img11 Lz, g t0 = v := by
  rw [D0_eq] at hv
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hv
  obtain ⟨m, hm, rfl⟩ := hv
  have hbit : pairOrb.testBit m = true :=
    List.all_eq_true.1 (Certificates.certificate450101).2.2.2.2 m hm
  refine (orbitBits_lz_spec (fun m => ∃ g ∈ img11 Lz, g (toW 11 32) = toW 11 m) ?_
    (by norm_num : 32 < 2 ^ 11) ⟨1, (img11 Lz).one_mem, rfl⟩ m hbit).2
  rintro m' _ ⟨g, hg, hgm⟩ x hx k hxk _
  exact ⟨x * g, (img11 Lz).mul_mem hx hg, by rw [MulAut.mul_apply, hgm, hxk]⟩

theorem exists_swap : ∃ g ∈ img11 Lz, g t0 = t0 * z0 :=
  exists_apply_t0_eq t0_mul_z0_mem_D0

theorem orbit_t0_eq {H : Subgroup (MulAut W11)}
    (hLH : img11 Lz ≤ H) (hHS : H ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) :
    MulAction.orbit ↥H t0 = D0 := by
  ext v
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact D0_invariant (hHS hh) t0_mem_D0
  · intro hv
    obtain ⟨g, hg, hgv⟩ := exists_apply_t0_eq hv
    exact ⟨⟨g, hLH hg⟩, hgv⟩

theorem card_eq_mul_card_stab {H : Subgroup (MulAut W11)}
    (hLH : img11 Lz ≤ H) (hHS : H ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) :
    Nat.card H = 36 * Nat.card ↥(H ⊓ centSub (Subgroup.zpowers t0)) := by
  have e : ↥(H ⊓ centSub (Subgroup.zpowers t0)) ≃ ↥(MulAction.stabilizer ↥H t0) :=
    { toFun := fun y => ⟨⟨y, y.2.1⟩, mem_centSub_zpowers.1 y.2.2⟩
      invFun := fun y => ⟨y.1, y.1.2, mem_centSub_zpowers.2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥H t0)
  rw [MulAction.index_stabilizer, orbit_t0_eq hLH hHS, ncard_D0, ← Nat.card_congr e] at h1
  omega

theorem card_stab_t0_Sz
    (hSz : Nat.card ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) = 138240) :
    Nat.card ↥((img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ⊓
      centSub (Subgroup.zpowers t0)) = 3840 := by
  have h := card_eq_mul_card_stab img11_Lz_le_stab (le_refl _)
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
