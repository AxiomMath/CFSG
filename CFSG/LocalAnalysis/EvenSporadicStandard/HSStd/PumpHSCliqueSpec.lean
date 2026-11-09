module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveAut
public import Certificates.Certificate27265
public import Certificates.Certificate117041
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Spec

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.HSStd.FiveY

theorem cliqueOK_parts (h : cliqueOK = true) :
    validA 100 Zassenhaus.HSFive.u0 = true ∧ (∀ i < 100, Zassenhaus.HSFive.u0[i]! ≠ i) ∧
      ∀ b ∈ nbrL, fixedA (compA 100 x3 b) = true ∨
        ∀ c ∈ nbrL, adjA b c = true → ∀ d ∈ nbrL, adjA b d = true → adjA c d = false := by
  simp only [cliqueOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨hv, hu⟩, hb⟩ := h
  refine ⟨hv, fun i hi => hu i hi, fun b hb' => ?_⟩
  have := hb b hb'
  simp only [Bool.or_eq_true] at this
  rcases this with h1 | h2
  · exact Or.inl h1
  · right
    intro c hc hbc d hd hbd
    simp only [List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at h2
    exact h2 c ⟨hc, hbc⟩ d ⟨hd, hbd⟩

theorem exists_idx_of_mem_closure {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ}
    (hgs : ∀ k < gs.size, validA n gs[k]! = true) {x : Array ℕ} {c : ArrCert}
    (hc : arrCertOK (fun k a => conjA n gs[k]! a) gs.size (validA n) (keyA n ps) x c = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.closure (permsA n gs)) :
    ∃ i < c.pts.size, permOfArr n c.pts[i]! = g * permOfArr n x * g⁻¹ := by
  classical
  set R := Subgroup.closure (permsA n gs) with hR
  let gens' : ℕ → ConjAct (Equiv.Perm (Fin n)) := fun k =>
    ConjAct.toConjAct (permOfArr n gs[k]!)
  have hact : ∀ k < gs.size, ∀ a, validA n a = true →
      permOfArr n (conjA n gs[k]! a) = gens' k • permOfArr n a := by
    intro k hk a ha
    rw [ConjAct.smul_def]
    exact permOfArr_eq_of_rep (rep_conjA (hgs k hk) (rep_of_validA ha))
  have horb := orbit_of_arrCertOK (G := ConjAct (Equiv.Perm (Fin n)))
    (X := Equiv.Perm (Fin n)) (dec := permOfArr n) («gens» := gens') hc hact
  set H : Subgroup (ConjAct (Equiv.Perm (Fin n))) :=
    Subgroup.closure (gens' '' {k | k < gs.size}) with hH
  have hHR : H = R.map (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom := by
    rw [hH, hR, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, permsA, Set.mem_ofPred_eq, gens']
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨permOfArr n gs[k]!, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hHmem : ConjAct.toConjAct g ∈ H := by
    rw [hHR, Subgroup.mem_map_equiv]
    exact hg
  have hmem : g * permOfArr n x * g⁻¹ ∈ MulAction.orbit H (permOfArr n x) :=
    ⟨⟨ConjAct.toConjAct g, hHmem⟩, by simp [ConjAct.smul_def]⟩
  rw [horb] at hmem
  obtain ⟨i, hi, e⟩ := hmem
  exact ⟨i, hi, e⟩

theorem adjA_of_orderOf_two {a b : Array ℕ} {g h : Equiv.Perm (Fin 100)} (ra : Rep 100 a g)
    (rb : Rep 100 b h) (ho : orderOf (g * h) = 2) : adjA a b = true := by
  have rab : Rep 100 (compA 100 a b) (g * h) := rep_compA ra rb
  have hsq : (g * h) * (g * h) = 1 := by
    have := pow_orderOf_eq_one (g * h)
    rw [ho] at this
    simpa [pow_two] using this
  have hne : g * h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ho
    omega
  simp only [adjA, involA, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨(eqA_iff (rep_compA rab rab) rep_idA).2 hsq, ?_⟩
  by_contra hcon
  have h1 : eqA 100 (compA 100 a b) (idA 100) = true := by simpa using hcon
  exact hne ((eqA_iff rab rep_idA).1 h1)

theorem getElem!_mem_toList (A : Array (Array ℕ)) {i : ℕ} (hi : i < A.size) :
    A[i]! ∈ A.toList := by
  rw [getElem!_pos A i hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

theorem mem_nbrL_of_conj {x : Array ℕ} {c : ArrCert}
    (hc : arrCertOK (fun k a => conjA 100 Zassenhaus.PartA.S0.pGens[k]! a)
      Zassenhaus.PartA.S0.pGens.size (validA 100) (keyA 100 Zassenhaus.PartA.S0.keys) x c = true)
    (hsub : ∀ a ∈ c.pts.toList, a ∈ invPtsL) {y g : Equiv.Perm (Fin 100)} (hg : g ∈ hs100P)
    (hy3 : orderOf y = 3) (hu : X3 * y = g * permOfArr 100 x * g⁻¹) :
    ∃ b ∈ nbrL, Rep 100 b y := by
  have f := x3Facts_of_check Certificates.certificate27261
  have hgs := (Zassenhaus.PartA.S0.basic_spec
    (Zassenhaus.PartA.S0.s0_parts Certificates.certificate117041).1).1
  have hcl : g ∈ Subgroup.closure (permsA 100 Zassenhaus.PartA.S0.pGens) := by
    rw [Zassenhaus.PartA.S0.closure_pGens]
    exact hg
  obtain ⟨i, hi, e⟩ := exists_idx_of_mem_closure hgs hc hcl
  have ra : Rep 100 c.pts[i]! (X3 * y) := by
    rw [hu, ← e]
    exact rep_of_validA (arrCertOK_valid hc hi)
  have rx : Rep 100 x3 X3 := rep_of_validA f.valid
  have hx3 : X3 ^ 3 = 1 := by
    rw [← f.order]
    exact pow_orderOf_eq_one X3
  have hy : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hxy : X3 * X3 * (X3 * y) = y := by
    calc X3 * X3 * (X3 * y) = X3 ^ 3 * y := by simp only [pow_three, mul_assoc]
      _ = y := by rw [hx3, one_mul]
  have rb : Rep 100 (compA 100 (compA 100 x3 x3) c.pts[i]!) y :=
    hxy ▸ rep_compA (rep_compA rx rx) ra
  refine ⟨_, ?_, rb⟩
  simp only [nbrL, List.mem_filter, List.mem_map]
  refine ⟨⟨_, hsub _ (getElem!_mem_toList _ hi), rfl⟩, ?_⟩
  have hy' : y * (y * y) = 1 := by
    calc y * (y * y) = y ^ 3 := (pow_three y).symm
      _ = 1 := hy
  exact (eqA_iff (rep_compA rb (rep_compA rb rb)) rep_idA).2 hy'

theorem exists_nbrL {y : Equiv.Perm (Fin 100)} (hy : y ∈ hs100R) (hy3 : orderOf y = 3)
    (hp : orderOf (X3 * y) = 2) : ∃ b ∈ nbrL, Rep 100 b y := by
  have f := x3Facts_of_check Certificates.certificate27261
  obtain ⟨hb, hc, -, hk, -⟩ := Zassenhaus.PartA.S0.s0_parts Certificates.certificate117041
  obtain ⟨-, -, hZP, hZ2, hZ1, -, -, -, hX, -⟩ := Zassenhaus.PartA.S0.basic_spec hb
  obtain ⟨cZ, cU, -⟩ := Zassenhaus.PartA.S0.classes_spec hb hc
  have hc' := hc
  simp only [Zassenhaus.PartA.S0.classesOK, Zassenhaus.PartA.S0.classOK, Bool.and_eq_true,
    and_assoc] at hc'
  obtain ⟨hz, -, hu, -⟩ := hc'
  have hYP := mem_hs100P_of_order_three hy hy3
  have hXP := mem_hs100P_of_order_three f.mem f.order
  set u : ↥hs100P := ⟨X3 * y, mul_mem hXP hYP⟩ with hu'
  have huo : orderOf u = 2 := (Subgroup.orderOf_mk _ _).trans hp
  have hY : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  have key : ∀ (x : Array ℕ) (c : ArrCert) (v : ↥hs100P), (v : Equiv.Perm (Fin 100)) =
      permOfArr 100 x →
      arrCertOK (fun k a => conjA 100 Zassenhaus.PartA.S0.pGens[k]! a)
        Zassenhaus.PartA.S0.pGens.size (validA 100) (keyA 100 Zassenhaus.PartA.S0.keys) x c =
        true →
      (∀ a ∈ c.pts.toList, a ∈ invPtsL) → IsConj u v → ∃ b ∈ nbrL, Rep 100 b y := by
    intro x c v hv hcx hsub hconj
    obtain ⟨d, hd⟩ := isConj_iff.1 hconj
    refine mem_nbrL_of_conj hcx hsub (d⁻¹ : ↥hs100P).2 hy3 ?_
    have h1 : u = d⁻¹ * v * d⁻¹⁻¹ := by
      rw [← hd]
      group
    have h2 := congrArg Subtype.val h1
    rw [← hv]
    exact h2
  rcases Zassenhaus.card_centralizer_of_involution_hs hY u huo with h | h
  · set Z' : ↥hs100P := ⟨Zassenhaus.PartA.S0.Zp, hZP⟩
    have hZo : orderOf Z' = 2 :=
      (Subgroup.orderOf_mk _ _).trans (orderOf_eq_prime (by rw [pow_two]; exact hZ2) hZ1)
    have hcZ : Nat.card ↥(centralizer ({Z'} : Set ↥hs100P)) = 7680 := by
      rw [Zassenhaus.PartA.S0.s0_card_cent_subtype]
      exact cZ
    exact key Zassenhaus.PartA.S0.z0 Zassenhaus.PartA.S0.zOrbit Z' rfl hz (fun a ha => List.mem_append_left _ ha)
      (Zassenhaus.isConj_of_card_centralizer_eq_hs hY u Z' huo hZo (h.trans hcZ.symm))
  · have hUP : Zassenhaus.PartA.S0.Up ∈ hs100P := (hX 0 (by norm_num)).2
    set U' : ↥hs100P := ⟨Zassenhaus.PartA.S0.Up, hUP⟩
    have hUo : orderOf U' = 2 :=
      (Subgroup.orderOf_mk _ _).trans (Zassenhaus.PartA.S0.u_order hb hk)
    have hcU : Nat.card ↥(centralizer ({U'} : Set ↥hs100P)) = 2880 := by
      rw [Zassenhaus.PartA.S0.s0_card_cent_subtype]
      exact cU
    exact key Zassenhaus.PartA.S0.u0 Zassenhaus.PartA.S0.uOrbit U' rfl hu (fun a ha => List.mem_append_right _ ha)
      (Zassenhaus.isConj_of_card_centralizer_eq_hs hY u U' huo hUo (h.trans hcU.symm))

theorem fixed_of_clique
    {y1 y2 y3 : Equiv.Perm (Fin 100)}
    (h1 : y1 ∈ hs100R) (h2 : y2 ∈ hs100R) (h3 : y3 ∈ hs100R) (o1 : orderOf y1 = 3)
    (o2 : orderOf y2 = 3) (o3 : orderOf y3 = 3) (p1 : orderOf (X3 * y1) = 2)
    (p2 : orderOf (X3 * y2) = 2) (p3 : orderOf (X3 * y3) = 2) (q12 : orderOf (y1 * y2) = 2)
    (q13 : orderOf (y1 * y3) = 2) (q23 : orderOf (y2 * y3) = 2) :
    ∃ i : Fin 100, (X3 * y1) i = i := by
  have f := x3Facts_of_check Certificates.certificate27261
  have rx : Rep 100 x3 X3 := rep_of_validA f.valid
  obtain ⟨b1, hbn, rb⟩ := exists_nbrL h1 o1 p1
  obtain ⟨b2, hcn, rc⟩ := exists_nbrL h2 o2 p2
  obtain ⟨b3, hdn, rd⟩ := exists_nbrL h3 o3 p3
  rcases (cliqueOK_parts Certificates.certificate27265).2.2 _ hbn with hfix | hcl
  · simp only [fixedA, List.any_eq_true, List.mem_range, beq_iff_eq] at hfix
    obtain ⟨j, hj, hjfix⟩ := hfix
    have rxb : Rep 100 (compA 100 x3 b1) (X3 * y1) := rep_compA rx rb
    exact ⟨⟨j, hj⟩, Fin.ext (by rw [← rxb.apply hj]; exact hjfix)⟩
  · exfalso
    have h12 := adjA_of_orderOf_two rb rc q12
    have h13 := adjA_of_orderOf_two rb rd q13
    have h23 := adjA_of_orderOf_two rc rd q23
    have := hcl _ hcn h12 _ hdn h13
    rw [this] at h23
    exact absurd h23 (by simp)

theorem card_centralizer_eq_of_fixed
    {u : ↥hs100P} (hu : orderOf u = 2)
    (hfix : ∃ i : Fin 100, (u : Equiv.Perm (Fin 100)) i = i) :
    Nat.card ↥(centralizer ({u} : Set ↥hs100P)) = 7680 := by
  have hY : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  rcases Zassenhaus.card_centralizer_of_involution_hs hY u hu with h | h
  · exact h
  · exfalso
    obtain ⟨hU0P, hU02, hU0c⟩ := Zassenhaus.HSFive.u0_spec
    set U0' : ↥hs100P := ⟨Zassenhaus.HSFive.U0, hU0P⟩ with hU0'
    have hc' : Nat.card ↥(centralizer ({U0'} : Set ↥hs100P)) = 2880 := by
      rw [Nat.card_congr (centralizerSubtypeEquiv hs100P U0').toEquiv, inf_comm]
      exact hU0c
    have hU0ord : orderOf U0' = 2 := (Subgroup.orderOf_mk _ _).trans hU02
    have hconj : IsConj u U0' :=
      Zassenhaus.isConj_of_card_centralizer_eq_hs hY u U0' hu hU0ord (h.trans hc'.symm)
    obtain ⟨c, hcu⟩ := isConj_iff.1 hconj
    obtain ⟨i, hi⟩ := hfix
    have hfixU : Zassenhaus.HSFive.U0 ((c : Equiv.Perm (Fin 100)) i) =
        (c : Equiv.Perm (Fin 100)) i := by
      have := congrArg Subtype.val hcu
      rw [← show ((c * u * c⁻¹ : ↥hs100P) : Equiv.Perm (Fin 100)) = Zassenhaus.HSFive.U0 from this]
      simp [Equiv.Perm.mul_apply, hi]
    obtain ⟨hvalid, hnofix, -⟩ := cliqueOK_parts Certificates.certificate27265
    have rU : Rep 100 Zassenhaus.HSFive.u0 Zassenhaus.HSFive.U0 := rep_of_validA hvalid
    have hlt := ((c : Equiv.Perm (Fin 100)) i).2
    have h1 := rU.apply hlt
    rw [Fin.eta] at h1
    have h2 : (Zassenhaus.HSFive.U0 ((c : Equiv.Perm (Fin 100)) i) : ℕ) =
        ((c : Equiv.Perm (Fin 100)) i : ℕ) := congrArg Fin.val hfixU
    exact hnofix _ hlt (by rw [h1]; exact h2)

theorem orderOf_conj_eq {G : Type*} [Group G] (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x

theorem card_centralizer_mulEquiv_PH {A B : Type*} [Group A] [Group B] (ε : A ≃* B) (a : A) :
    Nat.card ↥(centralizer ({a} : Set A)) = Nat.card ↥(centralizer ({ε a} : Set B)) := by
  have hmap : (centralizer ({a} : Set A)).map ε.toMonoidHom = centralizer ({ε a} : Set B) := by
    ext y
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨ε.symm y, ?_, by simp⟩
      apply ε.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  rw [← hmap]
  exact Nat.card_congr (ε.subgroupMap _).toEquiv

theorem card_centralizer_four_clique
    {Y : Type} [Group Y] (hY : IsSporadic Y .HS)
    {y0 y1 y2 y3 : Y} (o0 : orderOf y0 = 3) (o1 : orderOf y1 = 3) (o2 : orderOf y2 = 3)
    (o3 : orderOf y3 = 3) (p01 : orderOf (y0 * y1) = 2) (p02 : orderOf (y0 * y2) = 2)
    (p03 : orderOf (y0 * y3) = 2) (p12 : orderOf (y1 * y2) = 2) (p13 : orderOf (y1 * y3) = 2)
    (p23 : orderOf (y2 * y3) = 2) : Nat.card ↥(centralizer ({y0 * y1} : Set Y)) = 7680 := by
  obtain ⟨e₀⟩ := hY
  let ε : Y ≃* ↥hs100P := (e₀ : Y ≃* NativeSporadic.HS).trans hs100Equiv
  have f := x3Facts_of_check Certificates.certificate27261
  have hL : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  have hX3P : X3 ∈ hs100P := mem_hs100P_of_order_three f.mem f.order
  set X3P : ↥hs100P := ⟨X3, hX3P⟩ with hX3P'
  have hX3o : orderOf X3P = 3 := (Subgroup.orderOf_mk _ _).trans f.order
  set z0 := ε y0
  set z1 := ε y1
  set z2 := ε y2
  set z3 := ε y3
  have hz0 : orderOf z0 = 3 := by rw [MulEquiv.orderOf_eq]; exact o0
  have hz1 : orderOf z1 = 3 := by rw [MulEquiv.orderOf_eq]; exact o1
  have hz2 : orderOf z2 = 3 := by rw [MulEquiv.orderOf_eq]; exact o2
  have hz3 : orderOf z3 = 3 := by rw [MulEquiv.orderOf_eq]; exact o3
  have q01 : orderOf (z0 * z1) = 2 := by
    show orderOf (ε y0 * ε y1) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]; exact p01
  have q02 : orderOf (z0 * z2) = 2 := by
    show orderOf (ε y0 * ε y2) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]; exact p02
  have q03 : orderOf (z0 * z3) = 2 := by
    show orderOf (ε y0 * ε y3) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]; exact p03
  have q12 : orderOf (z1 * z2) = 2 := by
    show orderOf (ε y1 * ε y2) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]; exact p12
  have q13 : orderOf (z1 * z3) = 2 := by
    show orderOf (ε y1 * ε y3) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]; exact p13
  have q23 : orderOf (z2 * z3) = 2 := by
    show orderOf (ε y2 * ε y3) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]; exact p23
  obtain ⟨l, hlP, hl⟩ := Zassenhaus.hs_three_conj hL (a := (z0 : Equiv.Perm (Fin 100)))
    (b := X3) z0.2 hX3P (by rw [Subgroup.orderOf_coe]; exact hz0) f.order
  set c : ↥hs100P := ⟨l, hlP⟩ with hc
  have hcz0 : c * z0 * c⁻¹ = X3P := Subtype.ext hl
  set w1 : ↥hs100P := c * z1 * c⁻¹ with hw1
  set w2 : ↥hs100P := c * z2 * c⁻¹ with hw2
  set w3 : ↥hs100P := c * z3 * c⁻¹ with hw3
  have hprod : ∀ z : ↥hs100P, X3P * (c * z * c⁻¹) = c * (z0 * z) * c⁻¹ := by
    intro z
    rw [← hcz0]
    group
  have hprodw : ∀ z z' : ↥hs100P, (c * z * c⁻¹) * (c * z' * c⁻¹) = c * (z * z') * c⁻¹ := by
    intro z z'
    group
  have hR : ∀ w : ↥hs100P, (w : Equiv.Perm (Fin 100)) ∈ hs100R := fun w => hs100P_le_R w.2
  have hord : ∀ (w : ↥hs100P) (n : ℕ), orderOf w = n → orderOf (w : Equiv.Perm (Fin 100)) = n := by
    intro w n h
    rw [Subgroup.orderOf_coe]
    exact h
  have key := fixed_of_clique (y1 := (w1 : Equiv.Perm (Fin 100)))
    (y2 := (w2 : Equiv.Perm (Fin 100))) (y3 := (w3 : Equiv.Perm (Fin 100))) (hR w1) (hR w2) (hR w3)
    (hord _ _ (by rw [hw1, orderOf_conj_eq]; exact hz1))
    (hord _ _ (by rw [hw2, orderOf_conj_eq]; exact hz2))
    (hord _ _ (by rw [hw3, orderOf_conj_eq]; exact hz3))
    (by
      have := hord _ _ (show orderOf (X3P * w1) = 2 by
        rw [hw1, hprod, orderOf_conj_eq]; exact q01)
      simpa using this)
    (by
      have := hord _ _ (show orderOf (X3P * w2) = 2 by
        rw [hw2, hprod, orderOf_conj_eq]; exact q02)
      simpa using this)
    (by
      have := hord _ _ (show orderOf (X3P * w3) = 2 by
        rw [hw3, hprod, orderOf_conj_eq]; exact q03)
      simpa using this)
    (by
      have := hord _ _ (show orderOf (w1 * w2) = 2 by
        rw [hw1, hw2, hprodw, orderOf_conj_eq]; exact q12)
      simpa using this)
    (by
      have := hord _ _ (show orderOf (w1 * w3) = 2 by
        rw [hw1, hw3, hprodw, orderOf_conj_eq]; exact q13)
      simpa using this)
    (by
      have := hord _ _ (show orderOf (w2 * w3) = 2 by
        rw [hw2, hw3, hprodw, orderOf_conj_eq]; exact q23)
      simpa using this)
  have hcent : Nat.card ↥(centralizer ({X3P * w1} : Set ↥hs100P)) = 7680 := by
    refine card_centralizer_eq_of_fixed (u := X3P * w1) ?_ ?_
    · rw [hw1, hprod, orderOf_conj_eq]; exact q01
    · simpa using key
  have hconj : IsConj (z0 * z1) (X3P * w1) := isConj_iff.2 ⟨c, by rw [hw1, hprod]⟩
  rw [card_centralizer_mulEquiv_PH ε (y0 * y1), map_mul,
    Zassenhaus.card_centralizer_eq_of_isConj hconj, hcent]

end CFSG.EvenSporadicStandard.HSStd.PumpHS
