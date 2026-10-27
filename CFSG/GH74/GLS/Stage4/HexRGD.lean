module

public import CFSG.GH74.GLS.Stage4.HexComm

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley

namespace CFSG.GH74.GLS.Stage4.Hex

section Data

variable {K : Type*} [Group K]

structure G2Data
    (X : (Fin 2 → ℤ) → Subgroup K) (n : Fin 2 → K) (H : Fin 2 → Subgroup K) :
    Prop where
  ct : IsCTGroupDatum (coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem
    (weylAction (g2Shape X).isFiniteType) (g2Shape X).roots (g2Shape X).rootGroup n H
  ext : SteinbergExtras (g2Shape X) n H
  bruhat : BruhatExtras (g2Shape X) H
  comm : CFSG.LieType.TitsSimplicity.RootGroupCommutators (g2Shape X)

end Data

section BN

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

theorem coxeterM_G2_zero_one
    : (coxeterMatrix (g2Shape X).isFiniteType).M 0 1 = 6 := by
  have h01 : cartanG2 0 1 = -1 := by decide
  have h10 : cartanG2 1 0 = -3 := by decide
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  show TauCeti.coxeterOrder (cartanG2 0 1 * cartanG2 1 0) = 6
  rw [h01, h10]
  norm_num

theorem coxeterM_G2_one_zero
    : (coxeterMatrix (g2Shape X).isFiniteType).M 1 0 = 6 := by
  rw [CoxeterMatrix.symmetric]
  exact coxeterM_G2_zero_one

theorem card_coxeterMatrix_G2 :
    Nat.card (coxeterMatrix (g2Shape X).isFiniteType).Group = 12 := by
  have h := card_coxeterGroup_fin_two (coxeterMatrix (g2Shape X).isFiniteType)
  rw [coxeterM_G2_zero_one] at h
  omega

theorem hexT_le_hexN : ⨆ i, H i ≤ weylN n H := le_sup_left

variable (hd : G2Data X n H)

include hd

theorem hexB_inf_hexN : borel (g2Shape X) H ⊓ weylN n H = ⨆ i, H i :=
  borel_inf_weylN hd.ct hd.ext

theorem hexT_conj_mem {m h : K} (hm : m ∈ weylN n H) (hh : h ∈ ⨆ i, H i) :
    m * h * m⁻¹ ∈ ⨆ i, H i :=
  conj_mem_iSup_of_mem_weylN hd.ct hm hh

theorem hexB_sup_hexN : borel (g2Shape X) H ⊔ weylN n H = ⊤ :=
  (splitBN_of_datum hd.ct hd.ext (CFSG.LieType.TitsSimplicity.isNilpotent_posUnipotent hd.ext hd.comm)).2.1

end BN

section Action

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K}

theorem conjBy_hexGroup_simple
    {m : K} {k : Fin 2}
    (hm : ActsAs (g2Shape X) m ((coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem.simple k))
    {i : ℤ} (h0 : i ≠ 0) (h6 : i.natAbs ≤ 6) :
    conjBy m (hexGroup X i) = X (reflection cartanG2 k (hexPos i)) :=
  map_conj_inv_simple (g2Shape X) hm (hexPos_mem_roots X h0 h6)

theorem hexAction₁
    {m : K}
    (hm : ActsAs (g2Shape X) m
      ((coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (hexGroup X 1) = hexGroup X (-1) ∧ conjBy m (hexGroup X (-1)) = hexGroup X 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ ((6 : ℕ) : ℤ) →
        conjBy m (hexGroup X i) = hexGroup X (((6 : ℕ) : ℤ) + 2 - i) ∧
          conjBy m (hexGroup X (-i)) = hexGroup X (-(((6 : ℕ) : ℤ) + 2 - i)) := by
  have key : ∀ {i j : ℤ}, i ≠ 0 → i.natAbs ≤ 6 → reflection cartanG2 1 (hexPos i) = hexPos j →
      conjBy m (hexGroup X i) = hexGroup X j := fun hi0 hi6 hj =>
    (conjBy_hexGroup_simple hm hi0 hi6).trans (congrArg X hj)
  obtain ⟨r1, r2⟩ := reflection_one_hexPos_one
  refine ⟨key (by norm_num) (by norm_num) r1, key (by norm_num) (by norm_num) r2, fun i h2 h6 => ?_⟩
  have h6' : i ≤ 6 := by exact_mod_cast h6
  obtain ⟨r3, r4⟩ := reflection_one_hexPos h2 h6'
  have e : ((6 : ℕ) : ℤ) + 2 - i = 8 - i := by push_cast; ring
  rw [e]
  exact ⟨key (by omega) (by omega) r3, key (by omega) (by omega) r4⟩

theorem hexAction₂
    {m : K}
    (hm : ActsAs (g2Shape X) m
      ((coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem.simple (0 : Fin 2))) :
    conjBy m (hexGroup X ((6 : ℕ) : ℤ)) = hexGroup X (-((6 : ℕ) : ℤ)) ∧
      conjBy m (hexGroup X (-((6 : ℕ) : ℤ))) = hexGroup X ((6 : ℕ) : ℤ) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ ((6 : ℕ) : ℤ) - 1 →
        conjBy m (hexGroup X i) = hexGroup X (((6 : ℕ) : ℤ) - i) ∧
          conjBy m (hexGroup X (-i)) = hexGroup X (-(((6 : ℕ) : ℤ) - i)) := by
  have key : ∀ {i j : ℤ}, i ≠ 0 → i.natAbs ≤ 6 → reflection cartanG2 0 (hexPos i) = hexPos j →
      conjBy m (hexGroup X i) = hexGroup X j := fun hi0 hi6 hj =>
    (conjBy_hexGroup_simple hm hi0 hi6).trans (congrArg X hj)
  obtain ⟨r1, r2⟩ := reflection_zero_hexPos_six
  simp only [Nat.cast_ofNat]
  refine ⟨key (by norm_num) (by norm_num) r1, key (by norm_num) (by norm_num) r2, fun i h1 h5 => ?_⟩
  have h5' : i ≤ 5 := by push_cast at h5; omega
  obtain ⟨r3, r4⟩ := reflection_zero_hexPos h1 h5'
  exact ⟨key (by omega) (by omega) r3, key (by omega) (by omega) r4⟩

end Action

section Unipotent

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K}

theorem hexGroup_le_posUnipotent
    {k : ℤ} (h1 : 1 ≤ k) (h6 : k ≤ 6) :
    hexGroup X k ≤ posUnipotent (g2Shape X) :=
  rootGroup_le_posUnipotent (hexPos_mem_roots X (by omega) (by omega)) (ht_hexPos_pos h1 h6)

theorem hexGroup_neg_le_negUnipotent
    {k : ℤ} (h1 : 1 ≤ k) (h6 : k ≤ 6) :
    hexGroup X (-k) ≤ negUnipotent (g2Shape X) :=
  rootGroup_le_negUnipotent (hexPos_mem_roots X (by omega) (by omega)) (ht_hexPos_neg h1 h6)

theorem posUnipotent_eq_iSup_hexGroup :
    posUnipotent (g2Shape X) = ⨆ k ∈ intList 1 ((6 : ℕ) : ℤ), hexGroup X k := by
  refine le_antisymm ?_ (iSup₂_le fun k hk => ?_)
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hr, hp⟩ := hγ
    obtain ⟨k, h1, h6, rfl⟩ := pos_root_cases ((mem_g2Shape_roots X).1 hr) hp
    exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((6 : ℕ) : ℤ)) => hexGroup X k) k
      (mem_intList_iff.2 ⟨h1, by exact_mod_cast h6⟩) le_rfl
  · obtain ⟨h1, h6⟩ := mem_intList_iff.1 hk
    exact hexGroup_le_posUnipotent h1 (by exact_mod_cast h6)

theorem negGen_hexGroup_le
    : negGen 6 (hexGroup X) ≤ negUnipotent (g2Shape X) :=
  iSup₂_le fun k hk => hexGroup_neg_le_negUnipotent hk.1 (by exact_mod_cast hk.2)

end Unipotent

theorem hexN_mem
    {K : Type*} [Group K] (X : (Fin 2 → ℤ) → Subgroup K) (n : Fin 2 → K)
    (H : Fin 2 → Subgroup K) (i : Fin 2) : n i ∈ weylN n H :=
  n_mem_weylN (D := g2Shape X) (n := n) (H := H) i

section RGD

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

theorem hexPos_one_eq_single : hexPos 1 = Pi.single (1 : Fin 2) 1 :=
  CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])

theorem hexPos_neg_one_eq_single : hexPos (-1) = -Pi.single (1 : Fin 2) 1 :=
  CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])

theorem hexPos_six_eq_single : hexPos 6 = Pi.single (0 : Fin 2) 1 :=
  CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])

theorem hexPos_neg_six_eq_single : hexPos (-6) = -Pi.single (0 : Fin 2) 1 :=
  CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])

variable (hd : G2Data X n H)

include hd

theorem hexN_pow : (n 1 * n 0) ^ 6 ∈ ⨆ i, H i := by
  have := cartan_normal_of_datum hd.ct hd.ext
  have hord := (coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem.orderOf_simple_mul_simple 1 0
  rw [coxeterM_G2_one_zero] at hord
  have h1 : ((((⟨n 1, hexN_mem X n H 1⟩ : weylN n H) * ⟨n 0, hexN_mem X n H 0⟩) ^ 6 : weylN n H) :
      WeylGroup (borel (g2Shape X) H) (weylN n H)) = 1 := by
    apply (weylEquiv hd.ct hd.ext).injective
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, map_pow, map_mul,
      weylEquiv_n hd.ct hd.ext 1, weylEquiv_n hd.ct hd.ext 0, map_one, ← hord]
    exact pow_orderOf_eq_one _
  rw [QuotientGroup.eq_one_iff] at h1
  rw [cartan, Subgroup.mem_subgroupOf, borel_inf_weylN hd.ct hd.ext] at h1
  exact h1

end RGD

section RGDmain

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

theorem actsAs_inv_simple_g2
    (i : Fin 2) {m : K}
    (h : ActsAs (g2Shape X) m ((coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem.simple i)) :
    ActsAs (g2Shape X) m⁻¹ ((coxeterMatrix (g2Shape X).isFiniteType).toCoxeterSystem.simple i) := by
  have := h.inv
  rwa [CoxeterSystem.inv_simple] at this

variable (hd : G2Data X n H)

include hd

theorem hexRGD2 :
    RGD2 6 (⨆ i, H i) (n 1) (n 0) (posUnipotent (g2Shape X)) (hexGroup X) where
  three_le := by norm_num
  comm_H a ha b hb := (commute_of_mem_iSup hd.ext ha hb).eq
  nilpotent := CFSG.LieType.TitsSimplicity.isNilpotent_posUnipotent hd.ext hd.comm
  conj_H₁ h hh := hexT_conj_mem hd (hexN_mem X n H 1) hh
  conj_H₂ h hh := hexT_conj_mem hd (hexN_mem X n H 0) hh
  sq₁ := by
    have h := hd.ct.sq_mem 1
    rw [sq] at h
    exact le_iSup H 1 h
  sq₂ := by
    have h := hd.ct.sq_mem 0
    rw [sq] at h
    exact le_iSup H 0 h
  pow := hexN_pow hd
  U_inf_H := by
    rw [inf_comm]
    exact hd.ext.torus_inf_posPart
  ne_bot i hi := hd.ext.ne_bot _ (hexPos_mem_roots X hi.1 hi.2)
  invariant i hi h hh x hx :=
    (Subgroup.mem_normalizer_iff.1
      (iSup_le_normalizer_rootGroup hd.ct (hexPos_mem_roots X hi.1 hi.2) hh) x).1 hx
  carrier_eq := by
    have h := (hexComm hd.ext).carrier_eq (i := 1) (j := ((6 : ℕ) : ℤ)) le_rfl le_rfl
    rw [← posUnipotent_eq_iSup_hexGroup] at h
    exact h
  unique := hexUnique hd.ext
  reverse_eq i j hi _ hj := (hexComm hd.ext).reverse_eq hi hj
  subgroup i j hi _ hj := (hexComm hd.ext).exists_subgroup (U := posUnipotent (g2Shape X))
    (fun k h1 h6 => hexGroup_le_posUnipotent h1 (by exact_mod_cast h6)) hi hj
  act₁ := hexAction₁ (actsAs_inv_simple_g2 1 (actsAs_n hd.ct 1))
  act₂ := hexAction₂ (actsAs_inv_simple_g2 0 (actsAs_n hd.ct 0))
  meet_one x hx hxneg := by
    have hmem : x ∈ borel (g2Shape X) H ⊓ negUnipotent (g2Shape X) :=
      Subgroup.mem_inf.2 ⟨hx, negGen_hexGroup_le hxneg⟩
    rw [hd.bruhat.borel_inf_negUnipotent] at hmem
    exact Subgroup.mem_bot.1 hmem
  rank₁ y hy hy1 := by
    have hyL : y ∈ rankOne (g2Shape X).rootGroup (1 : Fin 2) := by
      refine Subgroup.mem_sup_right ?_
      have e : hexGroup X (-1) = X (-Pi.single (1 : Fin 2) 1) := by
        rw [hexGroup, hexPos_neg_one_eq_single]
      have hy2 : y ∈ X (-Pi.single (1 : Fin 2) 1) := e ▸ hy
      exact hy2
    have hyU : y ∈ negUnipotent (g2Shape X) :=
      hexGroup_neg_le_negUnipotent (k := 1) le_rfl (by norm_num) hy
    rcases hd.ext.rankOne_bruhat (1 : Fin 2) y hyL with
      ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · exfalso
      have hu' : u ∈ hexGroup X 1 := by
        rw [hexGroup, hexPos_one_eq_single]
        exact hu
      have hmem : h * u ∈ borel (g2Shape X) H ⊓ negUnipotent (g2Shape X) :=
        Subgroup.mem_inf.2 ⟨Subgroup.mul_mem_sup (le_iSup H (1 : Fin 2) hh)
          (hexGroup_le_posUnipotent le_rfl (by norm_num) hu'), hyU⟩
      rw [hd.bruhat.borel_inf_negUnipotent] at hmem
      exact hy1 (Subgroup.mem_bot.1 hmem)
    · have hu' : u ∈ hexGroup X 1 := by
        rw [hexGroup, hexPos_one_eq_single]
        exact hu
      have hv' : v ∈ hexGroup X 1 := by
        rw [hexGroup, hexPos_one_eq_single]
        exact hv
      have hh' : n 1 * h * (n 1)⁻¹ ∈ ⨆ i, H i :=
        hexT_conj_mem hd (hexN_mem X n H 1) (le_iSup H (1 : Fin 2) hh)
      refine Set.mem_mul.2 ⟨u * (n 1 * h * (n 1)⁻¹) * n 1,
        Set.mem_mul.2 ⟨u * (n 1 * h * (n 1)⁻¹),
          Set.mem_mul.2 ⟨u, hu', _, hh', rfl⟩, n 1, rfl, rfl⟩, v, hv', ?_⟩
      group
  rank₂ y hy hy1 := by
    have hy' : y ∈ hexGroup X (-6) := by simpa using hy
    have hyL : y ∈ rankOne (g2Shape X).rootGroup (0 : Fin 2) := by
      refine Subgroup.mem_sup_right ?_
      have e : hexGroup X (-6) = X (-Pi.single (0 : Fin 2) 1) := by
        rw [hexGroup, hexPos_neg_six_eq_single]
      have hy2 : y ∈ X (-Pi.single (0 : Fin 2) 1) := e ▸ hy'
      exact hy2
    have hyU : y ∈ negUnipotent (g2Shape X) :=
      hexGroup_neg_le_negUnipotent (k := 6) (by norm_num) le_rfl hy'
    rcases hd.ext.rankOne_bruhat (0 : Fin 2) y hyL with
      ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · exfalso
      have hu' : u ∈ hexGroup X 6 := by
        rw [hexGroup, hexPos_six_eq_single]
        exact hu
      have hmem : h * u ∈ borel (g2Shape X) H ⊓ negUnipotent (g2Shape X) :=
        Subgroup.mem_inf.2 ⟨Subgroup.mul_mem_sup (le_iSup H (0 : Fin 2) hh)
          (hexGroup_le_posUnipotent (by norm_num) le_rfl hu'), hyU⟩
      rw [hd.bruhat.borel_inf_negUnipotent] at hmem
      exact hy1 (Subgroup.mem_bot.1 hmem)
    · have hu' : u ∈ hexGroup X ((6 : ℕ) : ℤ) := by
        have : u ∈ hexGroup X 6 := by
          rw [hexGroup, hexPos_six_eq_single]
          exact hu
        simpa using this
      have hv' : v ∈ hexGroup X ((6 : ℕ) : ℤ) := by
        have : v ∈ hexGroup X 6 := by
          rw [hexGroup, hexPos_six_eq_single]
          exact hv
        simpa using this
      have hh' : n 0 * h * (n 0)⁻¹ ∈ ⨆ i, H i :=
        hexT_conj_mem hd (hexN_mem X n H 0) (le_iSup H (0 : Fin 2) hh)
      refine Set.mem_mul.2 ⟨u * (n 0 * h * (n 0)⁻¹) * n 0,
        Set.mem_mul.2 ⟨u * (n 0 * h * (n 0)⁻¹),
          Set.mem_mul.2 ⟨u, hu', _, hh', rfl⟩, n 0, rfl, rfl⟩, v, hv', ?_⟩
      group

end RGDmain

section Generation

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}
  (hd : G2Data X n H)

theorem hexRGD2_N : (hexRGD2 hd).N = weylN n H := by
  unfold RGD2.N
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 (Set.union_subset hexT_le_hexN ?_)
    rintro _ (rfl | rfl)
    · exact hexN_mem X n H 1
    · exact hexN_mem X n H 0
  · refine sup_le ?_ ?_
    · exact fun x hx => Subgroup.subset_closure (Or.inl hx)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
      · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem hexRGD2_gen :
    ((⨆ i, H i) ⊔ posUnipotent (g2Shape X)) ⊔ (hexRGD2 hd).N = ⊤ := by
  rw [hexRGD2_N hd]
  exact hexB_sup_hexN hd

end Generation

end CFSG.GH74.GLS.Stage4.Hex
