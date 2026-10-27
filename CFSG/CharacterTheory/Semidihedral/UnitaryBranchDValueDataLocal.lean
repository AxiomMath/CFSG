module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchDValueDataProjective
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchOrder

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Semidihedral.Principal

variable {G : Type} [Group G]

theorem mem_N_of_mem_NZ_of_odd {t : G} (ht : orderOf t = 2) {c : C t} (hc : c ∈ NZ t)
    (hodd : Odd (orderOf c)) : c ∈ N t := by
  obtain ⟨m, hm⟩ := hodd
  have h : c = (c ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, show (m + 1) * 2 = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h]
  exact actualLayer_sq_mem_N_of_mem_NZ ht (pow_mem hc _)

theorem coprime_half_succ_mul_pred {q : ℕ} (hq : q % 4 = 1) :
    Nat.Coprime ((q + 1) / 2) (q * (q - 1)) := by
  refine Nat.Coprime.mul_right ?_ (coprime_half_succ_pred hq)
  refine Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (by omega)) ?_
  rw [Nat.coprime_self_add_left]
  exact Nat.coprime_one_left q

theorem centralizer_le_of_torus [Finite G] {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) {s₀ : G}
    (hDcard : Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀}) = 2 * Nat.card (N t) * (p ^ f + 1))
    (hDcomm : ∀ a ∈ C t ⊓ Subgroup.centralizer {s₀}, ∀ b ∈ C t ⊓ Subgroup.centralizer {s₀},
      a * b = b * a)
    {w : G} (hwD : w ∈ C t ⊓ Subgroup.centralizer {s₀}) (hwodd : orderOf w ∣ (p ^ f + 1) / 2)
    (hwA : w ∉ (N t).map (C t).subtype) :
    C t ⊓ Subgroup.centralizer {w} ≤ Subgroup.centralizer {s₀} := by
  classical
  obtain ⟨-, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  set q := p ^ f with hqdef
  have hcardF : Nat.card F = q := hD.card_field
  have hq4 : q % 4 = 1 := hD.mod_four
  have hoddq : Odd ((q + 1) / 2) := ⟨q / 4, by omega⟩
  have hcop := coprime_half_succ_mul_pred hq4
  let w' : C t := ⟨w, hwD.1⟩
  have hw'o : orderOf w' = orderOf w := Subgroup.orderOf_mk w hwD.1
  set e := κ w' with he
  have heD : ∀ k : ℕ, e ^ k ∈ coordinateD F := fun k => by
    rw [← hD.range_eq]
    exact ⟨w' ^ k, by rw [map_pow]⟩
  have hedvd : orderOf e ∣ (q + 1) / 2 := (orderOf_map_dvd κ w').trans (hw'o ▸ hwodd)
  have he1 : e ≠ 1 := by
    intro h
    have hker : w' ∈ κ.ker := h
    rw [hD.ker_eq] at hker
    have hodd : Odd (orderOf w') := hw'o ▸ hoddq.of_dvd_nat hwodd
    exact hwA ⟨w', mem_N_of_mem_NZ_of_odd hD.orderOf_t hker hodd, rfl⟩
  have he3 : 3 ≤ orderOf e := by
    have hodd : Odd (orderOf e) := hoddq.of_dvd_nat hedvd
    have hne : orderOf e ≠ 1 := fun h => he1 (orderOf_eq_one_iff.mp h)
    obtain ⟨m, hm⟩ := hodd
    omega
  have hfree : ∀ k : ℕ, e ^ k ≠ 1 → ∀ x : Omega F, (e ^ k) x ≠ x := by
    intro k hk x
    refine fixedPointFree_of_coprime F (heD k) hk ?_ x
    rw [hcardF]
    exact Nat.Coprime.coprime_dvd_left ((orderOf_pow_dvd k).trans hedvd) hcop
  have hcent := card_centralizer_le_of_fixedPointFree F he3 hfree
  rw [hcardF] at hcent
  set X := C t ⊓ Subgroup.centralizer {w} with hXdef
  have hXC : X ≤ C t := inf_le_left
  let ψ : X →* Equiv.Perm (Omega F) := κ.comp (Subgroup.inclusion hXC)
  have hker : Nat.card ψ.ker ≤ 2 * Nat.card (N t) := by
    rw [← hNZcard, ← hD.ker_eq]
    refine Nat.card_le_card_of_injective
      (fun x : ψ.ker => (⟨Subgroup.inclusion hXC x, x.2⟩ : κ.ker)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun z : κ.ker => ((z : C t) : G)) hxy
    exact h
  have hrange : ψ.range ≤ Subgroup.centralizer {e} ⊓ coordinateD F := by
    rintro _ ⟨x, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have hxw : Subgroup.inclusion hXC x * w' = w' * Subgroup.inclusion hXC x := by
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      change κ (Subgroup.inclusion hXC x) * κ w' = κ w' * κ (Subgroup.inclusion hXC x)
      rw [← map_mul, ← map_mul, hxw]
    · rw [← hD.range_eq]
      exact ⟨_, rfl⟩
  have hXcard : Nat.card X ≤ 2 * Nat.card (N t) * (q + 1) := by
    have h3 : Nat.card X = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, mul_comm,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    rw [h3]
    exact Nat.mul_le_mul hker ((Subgroup.card_le_of_le hrange).trans hcent)
  have hDX : C t ⊓ Subgroup.centralizer {s₀} ≤ X := by
    intro c hc
    exact ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm c hc w hwD)⟩
  have hXD : C t ⊓ Subgroup.centralizer {s₀} = X :=
    Subgroup.eq_of_le_of_card_ge hDX (by rw [hDcard]; exact hXcard)
  intro c hc
  rw [← hXD] at hc
  exact hc.2

theorem exists_extend_of_index_two {K M : Type*} [Group K] [Group M] {Y : Subgroup K}
    (hY : Y.index = 2) (πY : Y →* M) {s : K} (hs : s ∉ Y) (hs2 : s * s = 1)
    (hinv : ∀ (y : K) (hy : y ∈ Y) (hy' : s * y * s⁻¹ ∈ Y), πY ⟨s * y * s⁻¹, hy'⟩ = πY ⟨y, hy⟩) :
    ∃ π : K →* M, ∀ (y : K) (hy : y ∈ Y), π y = πY ⟨y, hy⟩ := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hYn : Y.Normal := Subgroup.normal_of_index_eq_two hY
  have hmem : ∀ k : K, k ∉ Y → k * s ∈ Y := fun k hk =>
    (Subgroup.mul_mem_iff_of_index_two hY).mpr (iff_of_false hk hs)
  have hconj : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := fun y hy => hYn.conj_mem y hy s
  let fn : K → M := fun k => if hk : k ∈ Y then πY ⟨k, hk⟩ else πY ⟨k * s, hmem k hk⟩
  refine ⟨{ toFun := fn, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · simp only [fn, Y.one_mem, ↓reduceDIte]
    exact map_one πY
  · intro a b
    by_cases ha : a ∈ Y <;> by_cases hb : b ∈ Y
    · have hab : a * b ∈ Y := Y.mul_mem ha hb
      simp only [fn, ha, hb, hab, ↓reduceDIte]
      rw [← map_mul]
      rfl
    · have hab : a * b ∉ Y := fun h => hb ((Y.mul_mem_cancel_left ha).mp h)
      simp only [fn, ha, hb, hab, ↓reduceDIte]
      rw [← map_mul]
      congr 1
      exact Subtype.ext (mul_assoc a b s)
    · have hab : a * b ∉ Y := fun h => ha ((Y.mul_mem_cancel_right hb).mp h)
      simp only [fn, ha, hb, hab, ↓reduceDIte]
      have h1 : (⟨a * b * s, hmem _ hab⟩ : Y) = ⟨a * s, hmem a ha⟩ * ⟨s * b * s⁻¹, hconj b hb⟩ := by
        apply Subtype.ext
        change a * b * s = a * s * (s * b * s⁻¹)
        rw [hsinv]
        calc a * b * s = a * (s * s) * b * s := by rw [hs2, mul_one]
          _ = a * s * (s * b * s) := by group
      rw [h1, map_mul, hinv b hb]
    · have hab : a * b ∈ Y := (Subgroup.mul_mem_iff_of_index_two hY).mpr (iff_of_false ha hb)
      simp only [fn, ha, hb, hab, ↓reduceDIte]
      have h1 : (⟨a * b, hab⟩ : Y) =
          ⟨a * s, hmem a ha⟩ * ⟨s * (b * s) * s⁻¹, hconj _ (hmem b hb)⟩ := by
        apply Subtype.ext
        change a * b = a * s * (s * (b * s) * s⁻¹)
        rw [hsinv]
        calc a * b = a * (s * s) * b * (s * s) := by rw [hs2, mul_one, mul_one]
          _ = a * s * (s * (b * s) * s) := by group
      rw [h1, map_mul, hinv _ (hmem b hb)]
  · intro y hy
    change fn y = _
    simp only [fn, hy, ↓reduceDIte]

theorem exists_retraction_of_index_two {K : Type*} [Group K] {J N Y : Subgroup K}
    (hY : Y.index = 2) (hsup : J ⊔ N = Y) (hinf : J ⊓ N = ⊥) (hNc : N ≤ Subgroup.center K)
    (hJ : J.Normal) {s : K} (hs : s ∉ Y) (hs2 : s * s = 1) :
    ∃ π : K →* N, ∀ y : N, π y = y := by
  classical
  have hc : ∀ (a : J) (b : N), Commute (J.subtype a) (N.subtype b) := fun a b =>
    (Subgroup.mem_center_iff.mp (hNc b.2)) a
  set φ := MonoidHom.noncommCoprod J.subtype N.subtype hc with hφ
  have hφapp : ∀ x : J × N, φ x = (x.1 : K) * x.2 := fun x => rfl
  have hinj : Function.Injective φ :=
    Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hinf)
  have hrange : φ.range = Y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
  let e : J × N ≃* Y := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have heapp : ∀ x : J × N, (e x : K) = (x.1 : K) * x.2 := fun x => rfl
  let πY : Y →* N := (MonoidHom.snd J N).comp e.symm.toMonoidHom
  have hπY : ∀ (j : J) (m : N) (hy : (j : K) * m ∈ Y), πY ⟨(j : K) * m, hy⟩ = m := by
    intro j m hy
    have h : e.symm ⟨(j : K) * m, hy⟩ = (j, m) := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (heapp (j, m)).symm
    change (e.symm ⟨(j : K) * m, hy⟩).2 = m
    rw [h]
  have hdec : ∀ (y : K), y ∈ Y → ∃ (j : J) (m : N), y = (j : K) * m := by
    intro y hy
    refine ⟨(e.symm ⟨y, hy⟩).1, (e.symm ⟨y, hy⟩).2, ?_⟩
    have h := heapp (e.symm ⟨y, hy⟩)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hinv : ∀ (y : K) (hy : y ∈ Y) (hy' : s * y * s⁻¹ ∈ Y),
      πY ⟨s * y * s⁻¹, hy'⟩ = πY ⟨y, hy⟩ := by
    intro y hy hy'
    obtain ⟨j, m, rfl⟩ := hdec y hy
    have hms : s * (m : K) * s⁻¹ = m := by
      rw [Subgroup.mem_center_iff.mp (hNc m.2) s, mul_assoc, mul_inv_cancel, mul_one]
    have hj' : s * (j : K) * s⁻¹ ∈ J := hJ.conj_mem _ j.2 s
    have h1 : s * ((j : K) * m) * s⁻¹ = ((⟨s * (j : K) * s⁻¹, hj'⟩ : J) : K) * m := by
      change s * ((j : K) * m) * s⁻¹ = s * (j : K) * s⁻¹ * m
      calc s * ((j : K) * m) * s⁻¹ = s * (j : K) * s⁻¹ * (s * (m : K) * s⁻¹) := by group
        _ = s * (j : K) * s⁻¹ * m := by rw [hms]
    have h2 : (⟨s * ((j : K) * m) * s⁻¹, hy'⟩ : Y) =
        ⟨((⟨s * (j : K) * s⁻¹, hj'⟩ : J) : K) * m, h1 ▸ hy'⟩ := Subtype.ext h1
    rw [h2, hπY, hπY]
  obtain ⟨π, hπ⟩ := exists_extend_of_index_two hY πY hs hs2 hinv
  refine ⟨π, fun m => ?_⟩
  have hmY : (m : K) ∈ Y := hsup ▸ Subgroup.mem_sup_right m.2
  rw [hπ _ hmY]
  have hmY' : ((1 : J) : K) * m ∈ Y := by simpa using hmY
  have h2 : (⟨(m : K), hmY⟩ : Y) = ⟨((1 : J) : K) * m, hmY'⟩ := Subtype.ext (by simp)
  rw [h2, hπY]

theorem unitary_retraction [Finite G] (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hNcent : N t ≤ Subgroup.center (C t)) (hNdvd : Nat.card (N t) ∣ (p ^ f + 1) / 2) :
    ∃ π : C t →* N t, ∀ y : N t, π y = y := by
  classical
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hcover := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage
    t (fS (s n) : G) hcov
  obtain ⟨-, hJnormal, -, hYJN, hne9, h9⟩ :=
    Local.all_local_prime_covers_split_actual_layer_except_central_three_at_nine n hn S fS hG t ht2
      hnonab hcentral hnc p f hp hpodd hf hq5.le hmodel (Or.inl hcover)
  set T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  set Y := T₀.comap (nu t)
  set H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
  set J := (CFSG.perfectResidual H₀).map H₀.subtype
  have hE : J ⊓ N t = ⊥ := by
    by_cases h9' : p ^ f = 9
    · obtain ⟨-, hEcard, -⟩ := h9 h9'
      have hdvd : Nat.card ↥(J ⊓ N t) ∣ 5 := by
        have h1 : Nat.card ↥(J ⊓ N t) ∣ Nat.card (N t) := Subgroup.card_dvd_of_le inf_le_right
        rw [h9'] at hNdvd
        exact h1.trans hNdvd
      rcases hEcard with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · rw [h3] at hdvd
        norm_num at hdvd
    · exact (hne9 h9').1
  let sC : C t := ⟨(fS (s n) : G), hsC⟩
  have hsC2 : orderOf sC = 2 := by
    rw [← hs2, ← Subgroup.orderOf_coe]
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hsY : sC ∉ Y :=
    SimpleLayerFrontier.noncentral_involution_not_mem_layer_preimage n hn S fS hG t ht2 hnonab sC
      hsC2 hsCt
  have hss : sC * sC = 1 := by rw [← sq, ← hsC2, pow_orderOf_eq_one]
  exact exists_retraction_of_index_two hY hYJN.symm hE hNcent hJnormal hsY hss

theorem exists_cycling_element [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t s₀ : G}
    (htS : t ∈ (S : Subgroup G)) (hsS : s₀ ∈ (S : Subgroup G)) (ht : orderOf t = 2)
    (hs : orderOf s₀ = 2) (hsC : s₀ ∈ C t) (hts : t ≠ s₀) :
    ∃ g : G, g * t * g⁻¹ = s₀ ∧ g * s₀ * g⁻¹ = t * s₀ := by
  classical
  set V : Subgroup G := Subgroup.closure {t, s₀} with hVdef
  have hVK : IsKleinFour V :=
    StationaryOddLocalization.actual_involution_pair_isKleinFour t s₀ ht hs hsC hts
  have hVS : V ≤ (S : Subgroup G) := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htS
    · exact hsS
  have hsurj : Function.Surjective V.normalizerMonoidHom :=
    MonoidHom.range_eq_top.mp ((Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS
      hVK).1
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hsV : s₀ ∈ V := Subgroup.subset_closure (by simp)
  have huV : t * s₀ ∈ V := V.mul_mem htV hsV
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  have hs1 : s₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hs; omega
  have hs2 : s₀ * s₀ = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hu1 : t * s₀ ≠ 1 := by
    intro h
    apply hts
    calc t = t * s₀ * s₀ := by rw [mul_assoc, hs2, mul_one]
      _ = s₀ := by rw [h, one_mul]
  let a : {x : V // x ≠ 1} := ⟨⟨t, htV⟩, fun h => ht1 (congrArg Subtype.val h)⟩
  let b : {x : V // x ≠ 1} := ⟨⟨s₀, hsV⟩, fun h => hs1 (congrArg Subtype.val h)⟩
  let c : {x : V // x ≠ 1} := ⟨⟨t * s₀, huV⟩, fun h => hu1 (congrArg Subtype.val h)⟩
  have hab : a ≠ b := fun h => hts (congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) h)
  have hac : a ≠ c := by
    intro h
    have h' : t = t * s₀ := congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) h
    exact hs1 (by simpa using h'.symm)
  have hbc : b ≠ c := by
    intro h
    have h' : s₀ = t * s₀ := congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) h
    exact ht1 (by simpa using h'.symm)
  obtain ⟨σ, hσ⟩ := (Local.nontrivialPerm_bijective (V := V)).2
    (Equiv.swap a c * Equiv.swap a b)
  obtain ⟨g, hg⟩ := hsurj σ
  have hσa : Local.nontrivialPerm V σ a = b := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
  have hσb : Local.nontrivialPerm V σ b = c := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  refine ⟨g, ?_, ?_⟩
  · have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe V g ⟨t, htV⟩
    rw [hg] at h1
    rw [← h1]
    exact congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) hσa
  · have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe V g ⟨s₀, hsV⟩
    rw [hg] at h1
    rw [← h1]
    exact congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) hσb

theorem centralizer_closure_pair_eq (t s₀ : G) :
    Subgroup.centralizer (Subgroup.closure ({t, s₀} : Set G) : Set G) =
      Subgroup.centralizer {t} ⊓ Subgroup.centralizer {s₀} := by
  ext x
  rw [FieldFactorOneFixedCore.mem_centralizer_closure_pair_iff, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]

theorem torus_product_facts {t s₀ : G} (hts : t * s₀ = s₀ * t) (ht2 : t * t = 1)
    (hs2 : s₀ * s₀ = 1) (hVK : IsKleinFour (Subgroup.closure ({t, s₀} : Set G)))
    {A₀ W : Subgroup G}
    (e : (Subgroup.closure ({t, s₀} : Set G) × A₀ × W) ≃*
      Subgroup.centralizer (Subgroup.closure ({t, s₀} : Set G) : Set G))
    (he : ∀ x, (e x : G) = x.1 * x.2.1 * x.2.2)
    (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hW : IsCyclic W)
    (hA₀odd : ∀ a ∈ A₀, Odd (orderOf a)) (hWodd : ∀ w ∈ W, Odd (orderOf w)) :
    (∀ a ∈ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {s₀},
      ∀ b ∈ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {s₀}, a * b = b * a) ∧
    (∀ c ∈ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {s₀}, c * c = 1 →
      c = 1 ∨ c = t ∨ c = s₀ ∨ c = t * s₀) ∧
    W ⊓ A₀ = ⊥ := by
  have hD := centralizer_closure_pair_eq t s₀
  have hWc : ∀ a b : W, a * b = b * a := fun a b => by
    let := IsCyclic.commGroup (α := W)
    exact mul_comm a b
  have hP : ∀ x y : Subgroup.closure ({t, s₀} : Set G) × A₀ × W, x * y = y * x := by
    intro x y
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact mul_comm_of_exponent_two hVK.exponent_two x.1 y.1
    · exact Subtype.ext (hA₀ _ x.2.1.2 _ y.2.1.2)
    · exact hWc x.2.2 y.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [← hD] at ha hb
    have h1 : ((e (e.symm ⟨a, ha⟩ * e.symm ⟨b, hb⟩) : _) : G) = a * b := by
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      rfl
    have h2 : ((e (e.symm ⟨b, hb⟩ * e.symm ⟨a, ha⟩) : _) : G) = b * a := by
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      rfl
    rw [← h1, ← h2, hP]
  · intro c hc hcc
    rw [← hD] at hc
    set x := e.symm ⟨c, hc⟩ with hx
    have hxx : x * x = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_mul, hx, MulEquiv.apply_symm_apply, map_one]
      exact hcc
    have ha : x.2.1 = 1 := by
      have h : x.2.1 * x.2.1 = 1 :=
        congrArg (fun y : Subgroup.closure ({t, s₀} : Set G) × A₀ × W => y.2.1) hxx
      apply Subtype.ext
      refine FieldFactorOneFixedCore.eq_one_of_sq_eq_one_of_odd (hA₀odd _ x.2.1.2) ?_
      rw [sq]
      exact congrArg Subtype.val h
    have hw : x.2.2 = 1 := by
      have h : x.2.2 * x.2.2 = 1 :=
        congrArg (fun y : Subgroup.closure ({t, s₀} : Set G) × A₀ × W => y.2.2) hxx
      apply Subtype.ext
      refine FieldFactorOneFixedCore.eq_one_of_sq_eq_one_of_odd (hWodd _ x.2.2.2) ?_
      rw [sq]
      exact congrArg Subtype.val h
    have hcx : c = x.1 := by
      have h := he x
      rw [hx, MulEquiv.apply_symm_apply, ← hx, ha, hw] at h
      simpa using h
    rw [hcx]
    exact FieldFactorOneFixedCore.mem_closure_pair_cases hts ht2 hs2 x.1.2
  · rw [eq_bot_iff]
    rintro w ⟨hwW, hwA⟩
    have h1 : (e (1, ⟨w, hwA⟩, 1) : G) = (e (1, 1, ⟨w, hwW⟩) : G) := by
      rw [he, he]
      simp
    have h2 := congrArg (fun y : Subgroup.closure ({t, s₀} : Set G) × A₀ × W => (y.2.1 : G))
      (e.injective (Subtype.ext h1))
    simpa using h2

end CFSG.Semidihedral.UnitaryBranch
