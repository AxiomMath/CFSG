module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSp62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer
public import Certificates.Certificate12646

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62

open Subgroup CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Sec21 CFSG.AGLEmbeddingD2.Wilson

set_option linter.unusedSectionVars false

theorem map_centralizer_inf_normalizer {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x k : X) :
    (centralizer ({x} : Set X) ⊓ normalizer ((zpowers k : Subgroup X) : Set X)).map
        φ.toMonoidHom =
      centralizer ({φ x} : Set Y) ⊓ normalizer ((zpowers (φ k) : Subgroup Y) : Set Y) := by
  rw [Subgroup.map_inf_eq _ _ _ φ.injective, Proving.centralizer_map_mulEquiv_wilson]
  congr 1
  rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
  rfl

theorem card_centralizer_inf_normalizer_eq {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (x k : X) :
    Nat.card (centralizer ({x} : Set X) ⊓ normalizer ((zpowers k : Subgroup X) : Set X) :
        Subgroup X) =
      Nat.card (centralizer ({φ x} : Set Y) ⊓
        normalizer ((zpowers (φ k) : Subgroup Y) : Set Y) : Subgroup Y) := by
  rw [← map_centralizer_inf_normalizer φ, Subgroup.card_map_of_injective φ.injective]

theorem card_centralizer_eq {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({φ x} : Set Y)) := by
  rw [← Proving.centralizer_map_mulEquiv_wilson,
    Subgroup.card_map_of_injective φ.injective]

theorem threeFiveData228_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : ThreeFiveData228 Y) : ThreeFiveData228 X := by
  intro x k hx hk hxk
  have h' := h (φ x) (φ k) (by rw [MulEquiv.orderOf_eq]; exact hx)
    (by rw [MulEquiv.orderOf_eq]; exact hk) (by rw [← map_mul, ← map_mul, hxk])
  rwa [← card_centralizer_inf_normalizer_eq φ, ← card_centralizer_eq φ] at h'

section Model


theorem sp62_parts : eltsOK = true ∧
    tabsOK (orbitK ()) (orbitX ()) (tabK ()) (tabX ()) (tabN ()) = true := by
  have h := Certificates.certificate12646
  unfold sp62OK at h
  rw [Bool.and_eq_true] at h
  exact h

theorem elts_parts : genP.all pairCheck = true ∧ pairCheck k0P = true ∧ pairCheck x0P = true ∧
    gkP.all pairCheck = true ∧ gxP.all pairCheck = true ∧ gnP.all pairCheck = true ∧
    mul6 k0C (mul6 k0C (mul6 k0C (mul6 k0C k0C))) = one6 ∧ (k0C == one6) = false ∧
    mul6 x0C (mul6 x0C x0C) = one6 ∧ (x0C == one6) = false ∧ commutes6 x0C k0C = true ∧
    gkP.all (fun p => commutes6 p.1 k0C) = true ∧ gxP.all (fun p => commutes6 p.1 x0C) = true := by
  have h := sp62_parts.1
  unfold eltsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by simpa using h8, h9, by simpa using h10, h11, h12, h13⟩

theorem tabs_parts :
    orbitOK (orbitK ()) 48384 = true ∧ orbitOK (orbitX ()) 672 = true ∧
      closureOK (gkP.map Prod.fst) (tabK ()) 30 = true ∧
      closureOK (gxP.map Prod.fst) (tabX ()) 2160 = true ∧
      closureOK (gnP.map Prod.fst) (tabN ()) 60 = true ∧
      allCheck (fun c => !(mul6 c (mul6 c c) == one6) || c == one6 || c == x0C ||
        c == mul6 x0C x0C) (tabK ()) = true ∧
      allCheck (fun y => !(normK y) || found (tabN ()) (indexMap (tabN ())) y) (tabX ()) =
        true := by
  have h := sp62_parts.2
  unfold tabsOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem gpsH_spec' :
    ∀ gp ∈ gpsH, ∃ g : H6, dec6 (gp.take 36) = mat6 g ∧ dec6 (gp.drop 36) = mat6 g⁻¹ := by
  have hg := List.all_eq_true.mp elts_parts.1
  intro gp hgp
  simp only [gpsH, List.mem_cons, List.not_mem_nil, or_false] at hgp
  rcases hgp with rfl | rfl
  · refine ⟨ofCode (aC, aI) (hg _ (List.mem_cons_self ..)), ?_, ?_⟩
    · rw [List.take_left' (by rfl), mat6_ofCode]
    · rw [List.drop_left' (by rfl), mat6_ofCode_inv]
  · refine ⟨ofCode (bC, bI) (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), ?_, ?_⟩
    · rw [List.take_left' (by rfl), mat6_ofCode]
    · rw [List.drop_left' (by rfl), mat6_ofCode_inv]

theorem card_centralizer_mul_le_of_orbit {cc : List ℕ × List ℕ} (hcc : pairCheck cc = true)
    {par : List (ℕ × ℕ)} {n : ℕ} (hok : orbitOK (orbitBuild6 cc.1 gpsH par) n = true) :
    Nat.card (centralizer ({ofCode cc hcc} : Set H6)) * n ≤ Nat.card H6 := by
  set es := orbitBuild6 cc.1 gpsH par with hes
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hsize, hdist⟩, hcanon⟩ := hok
  have hex : ∀ k : Fin n, ∃ g : H6, dec6 (es.getD k []) = mat6 (g * ofCode cc hcc * g⁻¹) := by
    intro k
    have hk : (k : ℕ) < es.size := by rw [hsize]; exact k.2
    have hx : es.getD k [] ∈ es := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
      exact Array.getElem_mem hk
    exact orbitBuild6_spec mat6 (mat6_ofCode _ _).symm gpsH gpsH_spec' _ _ hx
  choose g hg using hex
  let f : Fin n → H6 := fun k => g k * ofCode cc hcc * (g k)⁻¹
  have hf : Function.Injective f := by
    intro k k' e
    have hk : (k : ℕ) < es.size := by rw [hsize]; exact k.2
    have hk' : (k' : ℕ) < es.size := by rw [hsize]; exact k'.2
    have e' : dec6 (es.getD k []) = dec6 (es.getD k' []) := by
      rw [hg k, hg k']; exact congrArg mat6 e
    exact Fin.ext (distinctCheck_spec hdist hk hk'
      (dec6_injective (allCheck_spec hcanon hk) (allCheck_spec hcanon hk') e'))
  exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_centralizer_mul_le f hf
    (fun k => ⟨g k, rfl⟩)

@[expose] noncomputable def k0H : H6 := ofCode k0P elts_parts.2.1

@[expose] noncomputable def x0H : H6 := ofCode x0P elts_parts.2.2.1

@[expose] noncomputable def CK : Subgroup H6 := closure (genSet gkP elts_parts.2.2.2.1)

@[expose] noncomputable def CX : Subgroup H6 := closure (genSet gxP elts_parts.2.2.2.2.1)

@[expose] noncomputable def NN : Subgroup H6 := closure (genSet gnP elts_parts.2.2.2.2.2.1)

theorem mat6_k0 : mat6 k0H = dec6 k0C := mat6_ofCode _ _

theorem mat6_x0 : mat6 x0H = dec6 x0C := mat6_ofCode _ _

theorem card_CK : Nat.card CK = 30 := card_closure_genSet _ _ _ tabs_parts.2.2.1

theorem card_CX : Nat.card CX = 2160 := card_closure_genSet _ _ _ tabs_parts.2.2.2.1

theorem card_NN : Nat.card NN = 60 := card_closure_genSet _ _ _ tabs_parts.2.2.2.2.1

theorem closure_le_centralizer {l : List (List ℕ × List ℕ)} (hl : l.all pairCheck = true)
    {t : H6} {c : List ℕ} (ht : mat6 t = dec6 c) (hc : l.all (fun p => commutes6 p.1 c) = true) :
    Subgroup.closure (genSet l hl) ≤ centralizer ({t} : Set H6) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨cc, hm, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact commute_of_commutes6 (mat6_ofCode _ _) ht (List.all_eq_true.mp hc cc hm)

theorem centralizer_k0 : centralizer ({k0H} : Set H6) = CK := by
  have hle : CK ≤ centralizer ({k0H} : Set H6) :=
    closure_le_centralizer _ mat6_k0 elts_parts.2.2.2.2.2.2.2.2.2.2.2.1
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h : Nat.card (centralizer ({k0H} : Set H6)) * 48384 ≤ Nat.card H6 :=
    card_centralizer_mul_le_of_orbit elts_parts.2.1 tabs_parts.1
  rw [card_H6] at h
  rw [card_CK]
  exact Nat.le_of_mul_le_mul_right (h.trans (by norm_num)) (by norm_num)

theorem centralizer_x0 : centralizer ({x0H} : Set H6) = CX := by
  have hle : CX ≤ centralizer ({x0H} : Set H6) :=
    closure_le_centralizer _ mat6_x0 elts_parts.2.2.2.2.2.2.2.2.2.2.2.2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h : Nat.card (centralizer ({x0H} : Set H6)) * 672 ≤ Nat.card H6 :=
    card_centralizer_mul_le_of_orbit elts_parts.2.2.1 tabs_parts.2.1
  rw [card_H6] at h
  rw [card_CX]
  exact Nat.le_of_mul_le_mul_right (h.trans (by norm_num)) (by norm_num)

theorem k0_pow_five : k0H ^ 5 = 1 := by
  have e := congrArg dec6 elts_parts.2.2.2.2.2.2.1
  rw [dec6_mul6, dec6_mul6, dec6_mul6, dec6_mul6, dec6_one6] at e
  apply mat6_injective
  rw [map_pow, map_one, mat6_k0, ← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem x0_pow_three : x0H ^ 3 = 1 := by
  have e := congrArg dec6 elts_parts.2.2.2.2.2.2.2.2.1
  rw [dec6_mul6, dec6_mul6, dec6_one6] at e
  apply mat6_injective
  rw [map_pow, map_one, mat6_x0, ← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem canon_k0 : canon6 k0C = true := (pairCheck_spec elts_parts.2.1).1

theorem canon_x0 : canon6 x0C = true := (pairCheck_spec elts_parts.2.2.1).1

theorem k0_ne_one : k0H ≠ 1 := by
  intro h
  have e := congrArg mat6 h
  rw [map_one, mat6_k0, ← dec6_one6] at e
  have h1 := dec6_injective canon_k0 canon6_one6 e
  have h2 := elts_parts.2.2.2.2.2.2.2.1
  rw [h1, beq_self_eq_true] at h2
  exact Bool.noConfusion h2

theorem x0_ne_one : x0H ≠ 1 := by
  intro h
  have e := congrArg mat6 h
  rw [map_one, mat6_x0, ← dec6_one6] at e
  have h1 := dec6_injective canon_x0 canon6_one6 e
  have h2 := elts_parts.2.2.2.2.2.2.2.2.2.1
  rw [h1, beq_self_eq_true] at h2
  exact Bool.noConfusion h2

theorem orderOf_k0 : orderOf k0H = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime k0_pow_five k0_ne_one

theorem orderOf_x0 : orderOf x0H = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime x0_pow_three x0_ne_one

theorem mat6_x0_sq : mat6 (x0H ^ 2) = dec6 (mul6 x0C x0C) := by
  rw [map_pow, mat6_x0, dec6_mul6, pow_two]

theorem eq_of_mem_CK {y : H6} (hy : y ∈ CK) (hy3 : y ^ 3 = 1) : y = 1 ∨ y = x0H ∨ y = x0H ^ 2 := by
  obtain ⟨t, ht, hdec, hcan⟩ := exists_code_closure gkP elts_parts.2.2.2.1 30 tabs_parts.2.2.1 hy
  have hc := allCheck_spec tabs_parts.2.2.2.2.2.1 ht
  set c := (closureT (gkP.map Prod.fst)).getD t [] with hcdef
  have h3 : mul6 c (mul6 c c) = one6 := by
    apply dec6_injective (canon6_mul6 _ _) canon6_one6
    rw [dec6_mul6, dec6_mul6, hdec, dec6_one6, ← map_mul, ← map_mul, ← pow_three, hy3, map_one]
  change (!(mul6 c (mul6 c c) == one6) || c == one6 || c == x0C || c == mul6 x0C x0C) = true at hc
  rw [h3, beq_self_eq_true, Bool.not_true, Bool.false_or] at hc
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with (h | h) | h
  · left
    apply mat6_injective
    rw [← hdec, h, dec6_one6, map_one]
  · right; left
    apply mat6_injective
    rw [← hdec, h, mat6_x0]
  · right; right
    apply mat6_injective
    rw [← hdec, h, mat6_x0_sq]

theorem kPows_spec : ∀ r, 0 < r → r < 5 → ∃ p ∈ kPows, dec6 p = mat6 (k0H ^ r) := by
  intro r hr0 hr5
  interval_cases r
  · exact ⟨k0C, by simp [kPows], by rw [pow_one, mat6_k0]⟩
  · exact ⟨mul6 k0C k0C, by simp [kPows], by rw [map_pow, mat6_k0, dec6_mul6, pow_two]⟩
  · refine ⟨mul6 k0C (mul6 k0C k0C), by simp [kPows], ?_⟩
    rw [map_pow, mat6_k0, dec6_mul6, dec6_mul6, pow_three]
  · refine ⟨mul6 k0C (mul6 k0C (mul6 k0C k0C)), by simp [kPows], ?_⟩
    rw [map_pow, mat6_k0, dec6_mul6, dec6_mul6, dec6_mul6]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem inf_normalizer_le_NN :
    centralizer ({x0H} : Set H6) ⊓ normalizer ((zpowers k0H : Subgroup H6) : Set H6) ≤ NN := by
  intro y hy
  obtain ⟨hyC, hyN⟩ := mem_inf.1 hy
  rw [centralizer_x0] at hyC
  obtain ⟨t, ht, hdec, hcan⟩ := exists_code_closure gxP elts_parts.2.2.2.2.1 2160
    tabs_parts.2.2.2.1 hyC
  have hc := allCheck_spec tabs_parts.2.2.2.2.2.2 ht
  set c := (closureT (gxP.map Prod.fst)).getD t [] with hcdef
  have hmem : y * k0H * y⁻¹ ∈ zpowers k0H := (mem_normalizer_iff.1 hyN k0H).1 (mem_zpowers k0H)
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hmem
  have h5 : k0H ^ (5 : ℤ) = 1 := by rw [zpow_ofNat]; exact k0_pow_five
  have hmod : k0H ^ m = k0H ^ (m % 5) := zpow_eq_zpow_emod m h5
  have hr0 := Int.emod_nonneg m (by norm_num : (5 : ℤ) ≠ 0)
  have hr5 := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 5)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = m % 5 := ⟨(m % 5).toNat, Int.toNat_of_nonneg hr0⟩
  have hkr : y * k0H * y⁻¹ = k0H ^ r := by rw [← hm, hmod, ← hr, zpow_natCast]
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hkr
      apply k0_ne_one
      have : k0H = y⁻¹ * (y * k0H * y⁻¹) * y := by group
      rw [this, hkr]
      group
    · exact h0
  have hrlt : r < 5 := by omega
  obtain ⟨p, hp, hpdec⟩ := kPows_spec r hrpos hrlt
  have hyk : y * k0H = k0H ^ r * y := by rw [← hkr]; group
  have hnorm : normK c = true := by
    rw [normK, List.any_eq_true]
    refine ⟨p, hp, ?_⟩
    rw [beq_iff_eq]
    apply dec6_injective (canon6_mul6 _ _) (canon6_mul6 _ _)
    rw [dec6_mul6, dec6_mul6, hdec, hpdec, ← mat6_k0, ← map_mul, ← map_mul, hyk]
  change (!(normK c) || found (tabN ()) (indexMap (tabN ())) c) = true at hc
  rw [hnorm, Bool.not_true, Bool.false_or] at hc
  obtain ⟨u, hu, hue⟩ := found_spec hc
  have himg := image_closure_eq dec6 one6 mul6 (gnP.map Prod.fst) mat6 dec6_one6 dec6_mul6
    (genSet gnP elts_parts.2.2.2.2.2.1) (image_genSet gnP _) _
    (by
      have h := tabs_parts.2.2.2.2.1
      simp only [closureOK, Bool.and_eq_true] at h
      exact h.1.1.2)
  have hy' : mat6 y ∈ mat6 '' (NN : Set H6) := by
    rw [NN, himg]
    refine ⟨u, hu, ?_⟩
    change dec6 ((tabN ()).getD u []) = mat6 y
    rw [hue, hdec]
  obtain ⟨z, hz, hzy⟩ := hy'
  rw [← mat6_injective hzy]
  exact hz

theorem threeFiveData228_H6 : ThreeFiveData228 H6 := by
  intro x k hx hk hxk
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQ : Nat.card (zpowers k0H) = 5 ^ 1 := by rw [Nat.card_zpowers, orderOf_k0, pow_one]
  obtain ⟨g, hg⟩ := NormalizerAction.exists_conj_mem_of_orderOf_prime 5 1 (zpowers k0H) hQ
    (by rw [card_H6]; norm_num) hk
  let φ : H6 ≃* H6 := MulAut.conj g⁻¹
  have hφ : ∀ z, φ z = g⁻¹ * z * g := fun z => by
    simp only [φ, MulAut.conj_apply, inv_inv]
  rw [card_centralizer_inf_normalizer_eq φ, card_centralizer_eq φ]
  have hk' : φ k ∈ zpowers k0H := by rw [hφ]; exact hg
  have hk'o : orderOf (φ k) = 5 := by rw [MulEquiv.orderOf_eq]; exact hk
  have hx'o : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hxk' : φ x * φ k = φ k * φ x := by rw [← map_mul, ← map_mul, hxk]
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hk'
  have hk'1 : φ k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk'o
    norm_num at hk'o
  have hCk : centralizer ({φ k} : Set H6) = centralizer ({k0H} : Set H6) := by
    rw [← hj]
    exact Coordinator.KS155.centralizer_zpow_eq_of_ne_one (by rw [orderOf_k0]; norm_num)
      (by rw [hj]; exact hk'1)
  have hx'C : φ x ∈ CK := by
    rw [← centralizer_k0, ← hCk, mem_centralizer_singleton_iff]
    exact hxk'
  have hx'3 : φ x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (φ x)
    rw [hx'o] at h
    exact h
  have hx'1 : φ x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx'o
    norm_num at hx'o
  have hCx : centralizer ({φ x} : Set H6) = centralizer ({x0H} : Set H6) := by
    rcases eq_of_mem_CK hx'C hx'3 with h1 | h1 | h1
    · exact absurd h1 hx'1
    · rw [h1]
    · rw [h1]
      have := Coordinator.KS155.centralizer_zpow_eq_of_ne_one (x := x0H) (n := 2)
        (by rw [orderOf_x0]; norm_num) (by rw [zpow_ofNat, ← h1]; exact hx'1)
      rwa [zpow_ofNat] at this
  have hZ : zpowers (φ k) = zpowers k0H := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [zpowers_le]; exact hk'
    · rw [Nat.card_zpowers, Nat.card_zpowers, hk'o, orderOf_k0]
  rw [hCx, hZ, centralizer_x0, card_CX]
  have hle : Nat.card (centralizer ({x0H} : Set H6) ⊓
      normalizer ((zpowers k0H : Subgroup H6) : Set H6) : Subgroup H6) ≤ 60 := by
    rw [← card_NN]
    exact Subgroup.card_le_of_le inf_normalizer_le_NN
  rw [centralizer_x0] at hle
  omega

end Model

theorem census228Sp62Data : Census228Sp62Data :=
  threeFiveData228_of_mulEquiv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.sp62Equiv
    threeFiveData228_H6

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62
