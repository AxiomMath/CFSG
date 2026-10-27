module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT2Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem exists_bits (p : ℕ → Bool) : ∀ n, ∃ b, b < 2 ^ n ∧ ∀ j, j < n → b.testBit j = p j
  | 0 => ⟨0, by norm_num, fun j hj => by omega⟩
  | n + 1 => by
    obtain ⟨b, hb, hbj⟩ := exists_bits p n
    refine ⟨if p n then 2 ^ n + b else b, ?_, fun j hj => ?_⟩
    · have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      split <;> omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · split
        · rw [Nat.testBit_two_pow_add_gt hj, hbj j hj]
        · exact hbj j hj
      · split
        · rename_i h
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb, h]
          rfl
        · rename_i h
          rw [Nat.testBit_lt_two_pow hb]
          simpa using h

namespace CodeIso

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul)

theorem length_kInv_filter (h0 : mul 0 0 = 0) (q : ℕ → Bool) :
    ((kInv mul N).filter q).length = Nat.card {h : H // h * h = 1 ∧ h ≠ 1 ∧ q (Φ.f h) = true} := by
  unfold kInv
  rw [List.filter_filter]
  have e1 : ∀ x : H, (q (Φ.f x) && (mul (Φ.f x) (Φ.f x) == 0 && Φ.f x != 0)) = true ↔
      x * x = 1 ∧ x ≠ 1 ∧ q (Φ.f x) = true := by
    intro x
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Φ.map_mul, f_eq_zero Φ h0]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight e1).symm]
  exact (Φ.card_eq (fun c => q c && (mul c c == 0 && c != 0))).symm

theorem length_kOrd4_filter (h0 : mul 0 0 = 0) (q : ℕ → Bool) :
    ((kOrd4 mul N).filter q).length =
      Nat.card {h : H // h * h ≠ 1 ∧ h * h * (h * h) = 1 ∧ q (Φ.f h) = true} := by
  unfold kOrd4
  rw [List.filter_filter]
  have e1 : ∀ x : H, (q (Φ.f x) && (mul (Φ.f x) (Φ.f x) != 0 &&
      mul (mul (Φ.f x) (Φ.f x)) (mul (Φ.f x) (Φ.f x)) == 0)) = true ↔
      x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ q (Φ.f x) = true := by
    intro x
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Φ.map_mul, f_eq_zero Φ h0]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight e1).symm]
  exact (Φ.card_eq (fun c => q c && (mul c c != 0 && mul (mul c c) (mul c c) == 0))).symm

end CodeIso

theorem card_conj_eq {T S : Subgroup G} (hST : S ≤ T) {y : G} (hyN : y ∈ normalizer (T : Set G))
    (P : G → Prop) (hP : ∀ g, P (y⁻¹ * g * y) ↔ P g) :
    Nat.card {g : T // P g ∧ y⁻¹ * g * y ∈ S} = Nat.card {s : S // P s} := by
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨y⁻¹ * g * y, g.2.2⟩, (hP g).2 g.2.1⟩
      invFun := fun s => ⟨⟨y * s * y⁻¹, (mem_normalizer_iff.1 hyN _).1 (hST s.1.2)⟩, ?_, ?_⟩
      left_inv := fun g => ?_
      right_inv := fun s => ?_ }
  · have h := hP (y * s * y⁻¹)
    rw [show y⁻¹ * (y * s * y⁻¹) * y = s by group] at h
    exact h.1 s.2
  · show y⁻¹ * (y * s * y⁻¹) * y ∈ S
    rw [show y⁻¹ * (y * s * y⁻¹) * y = s by group]
    exact s.1.2
  · apply Subtype.ext; apply Subtype.ext
    show y * (y⁻¹ * g * y) * y⁻¹ = g
    group
  · apply Subtype.ext; apply Subtype.ext
    show y⁻¹ * (y * s * y⁻¹) * y = s
    group

@[expose] noncomputable def idxTwoChar {H : Type*} [Group H] (K : Subgroup H) (hK : K.index = 2) :
    H →* Multiplicative (ZMod 2) where
  toFun g := by classical exact if g ∈ K then 1 else Multiplicative.ofAdd 1
  map_one' := by simp [K.one_mem]
  map_mul' a b := by
    classical
    have h := Subgroup.mul_mem_iff_of_index_two hK (a := a) (b := b)
    by_cases ha : a ∈ K <;> by_cases hb : b ∈ K
    · simp [ha, hb, h.2 (iff_of_true ha hb)]
    · simp [ha, hb, show a * b ∉ K from fun hab => hb ((h.1 hab).1 ha)]
    · simp [ha, hb, show a * b ∉ K from fun hab => ha ((h.1 hab).2 hb)]
    · simp only [ha, hb, ite_false, h.2 (iff_of_false ha hb), ite_true]
      rfl

theorem idxTwoChar_of_mem {H : Type*} [Group H] {K : Subgroup H} (hK : K.index = 2) {g : H}
    (h : g ∈ K) : idxTwoChar K hK g = 1 := by
  classical
  show (if g ∈ K then 1 else Multiplicative.ofAdd 1) = _
  rw [ite_eq_left h]

theorem idxTwoChar_of_not_mem {H : Type*} [Group H] {K : Subgroup H} (hK : K.index = 2) {g : H}
    (h : g ∉ K) : idxTwoChar K hK g = Multiplicative.ofAdd 1 := by
  classical
  show (if g ∈ K then 1 else Multiplicative.ofAdd 1) = _
  rw [ite_eq_right h]

@[expose] def conjSub (T S : Subgroup G) (y : G) : Subgroup T where
  carrier := {g | y⁻¹ * g * y ∈ S}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have e : y⁻¹ * ((a * b : T) : G) * y = (y⁻¹ * a * y) * (y⁻¹ * b * y) := by
      simp only [coe_mul]; group
    show y⁻¹ * ((a * b : T) : G) * y ∈ S
    rw [e]; exact S.mul_mem ha hb
  inv_mem' {a} ha := by
    have e : y⁻¹ * ((a⁻¹ : T) : G) * y = (y⁻¹ * a * y)⁻¹ := by
      simp only [coe_inv]; group
    show y⁻¹ * ((a⁻¹ : T) : G) * y ∈ S
    rw [e]; exact S.inv_mem ha

theorem mem_conjSub {T S : Subgroup G} {y : G} {g : T} : g ∈ conjSub T S y ↔ y⁻¹ * g * y ∈ S :=
  Iff.rfl

theorem card_conjSub {T S : Subgroup G} (hST : S ≤ T) {y : G} (hyN : y ∈ normalizer (T : Set G)) :
    Nat.card (conjSub T S y) = Nat.card S := by
  have h := card_conj_eq hST hyN (fun _ => True) (fun _ => Iff.rfl)
  rw [← Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun _ : S => True) fun _ => trivial)]
  rw [← h]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.1, trivial, g.2⟩
      invFun := fun g => ⟨g.1, g.2.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

theorem mem_iff_chiV {T : Type*} [Group T] {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T 131072 mul)
    (h0 : mul 0 0 = 0) {K : Subgroup T} (hK : K.index = 2) {par pj dep vec : ℕ → ℕ}
    (htree : treeOK mul t1Gens 131072 par pj dep = true) (hvec : vecOK 131072 par pj vec = true)
    (hgens : ∀ g ∈ t1Gens, g < 131072) :
    ∃ b, b < 1024 ∧ (∀ c, c < 131072 → (Φ.g c ∈ K ↔ chiV 10 b (vec c) = false)) ∧
      ∀ i, i < 10 → (Φ.g (t1Gens.getD i 0) ∈ K ↔ b.testBit i = false) := by
  classical
  obtain ⟨b, hb, hbits⟩ := exists_bits (fun j => decide (Φ.g (t1Gens.getD j 0) ∉ K)) 10
  have hbK : ∀ i, i < 10 → (Φ.g (t1Gens.getD i 0) ∈ K ↔ b.testBit i = false) := by
    intro i hi
    rw [hbits i hi]
    simp
  refine ⟨b, by simpa using hb, fun c hc => ?_, hbK⟩
  have hlen : t1Gens.length = 10 := rfl
  have hξ := Φ.xi_eq_chiV h0 hgens htree hvec (idxTwoChar K hK) (b := b) (fun j hj => by
    rw [hlen] at hj
    by_cases h : Φ.g (t1Gens.getD j 0) ∈ K
    · rw [idxTwoChar_of_mem hK h, ((hbK j hj).1 h)]; rfl
    · rw [idxTwoChar_of_not_mem hK h, show b.testBit j = true by
        have := (hbK j hj).not.1 h; simpa using this]; rfl) hc
  rw [hlen] at hξ
  constructor
  · intro h
    rw [idxTwoChar_of_mem hK h] at hξ
    by_contra h'
    rw [Bool.not_eq_false] at h'
    rw [ite_eq_left h'] at hξ
    exact absurd (Multiplicative.ofAdd.injective hξ) (by decide)
  · intro h
    by_contra h'
    rw [idxTwoChar_of_not_mem hK h', h] at hξ
    exact absurd (Multiplicative.ofAdd.injective hξ) (by decide)

theorem mem_normalizer_of_maps [Finite G] {K : Subgroup G} {p : G}
    (h : ∀ y ∈ K, p * y * p⁻¹ ∈ K) : p ∈ normalizer (K : Set G) := by
  have hinj : Set.InjOn (fun y => p * y * p⁻¹) (K : Set G) := fun a _ b _ hab => by
    simpa using hab
  have hsurj : Set.SurjOn (fun y => p * y * p⁻¹) (K : Set G) (K : Set G) := by
    have hfin : (K : Set G).Finite := Set.toFinite _
    exact (Set.Finite.injOn_iff_bijOn_of_mapsTo hfin (fun y hy => h y hy)).1 hinj |>.surjOn
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hsurj hy
  simp only at hzy
  have : z = y := by simpa using hzy
  rw [← this]
  exact hz

theorem conj_eq_one_iff' (y g : G) : y⁻¹ * g * y = 1 ↔ g = 1 := by
  constructor
  · intro h
    have := congrArg (fun z => y * z * y⁻¹) h
    simpa [mul_assoc] using this
  · intro h; simp [h]

theorem sPrime_iff [Finite G] {T₁ S : Subgroup G} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul)
    (h0 : mul 0 0 = 0) (hS : ∀ g : T₁, (g : G) ∈ S ↔ Φ.f g < 65536) (hST : S ≤ T₁)
    (hcard : Nat.card S = 65536)
    (hIS : Nat.card {s : S // (s : G) * s = 1 ∧ (s : G) ≠ 1} = 3839)
    (hOS : Nat.card {s : S // (s : G) * s ≠ 1 ∧ (s : G) * s * ((s : G) * s) = 1} = 41216)
    {y : G} (hyN : y ∈ normalizer (T₁ : Set G)) (hyS : y ∉ normalizer (S : Set G))
    {tr : Array ℕ × Array ℕ × Array ℕ × Array ℕ} {W : Array (ℕ × ℕ)}
    (hchk : s2CharOK mul tr (kInv mul 131072) (kOrd4 mul 131072) (s2RelV mul tr.2.2.2 W) = true) :
    ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp tr.2.2.2 (Φ.f g) = true := by
  have hgens : ∀ g ∈ t1Gens, g < 131072 := by decide
  set K := conjSub T₁ S y with hKdef
  have hKidx : K.index = 2 := by
    have h1 := K.card_mul_index
    rw [card_conjSub hST hyN, hcard, Φ.card_univ] at h1
    omega
  unfold s2CharOK at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hchk
  obtain ⟨⟨⟨htree, hvec⟩, hall⟩, hlast⟩ := hchk
  obtain ⟨b, hb, hbK, hbgen⟩ := mem_iff_chiV Φ h0 hKidx htree hvec hgens
  have hK : ∀ g : T₁, g ∈ K ↔ chiV 10 b tr.2.2.2[Φ.f g]! = false := by
    intro g
    have := hbK _ (Φ.lt g)
    rwa [Φ.g_f] at this
  have hb' := hall b hb
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at hb'
  rcases hb' with ((((h512 | h768) | ⟨r, hr, hrb⟩) | hI) | hO)
  ·
    exfalso
    subst h512
    apply hyS
    have hmaps : ∀ s ∈ S, y⁻¹ * s * y⁻¹⁻¹ ∈ S := by
      intro s hs
      have hsT : s ∈ T₁ := hST hs
      have h1 := beq_iff_eq.1 (hlast (Φ.f ⟨s, hsT⟩) (Φ.lt _))
      have h3 : Φ.f ⟨s, hsT⟩ < 65536 := (hS ⟨s, hsT⟩).1 hs
      rw [decide_eq_true h3, Bool.not_eq_true'] at h1
      have h2 : (⟨s, hsT⟩ : T₁) ∈ K := (hK _).2 h1
      rw [inv_inv]
      exact h2
    have := mem_normalizer_of_maps hmaps
    simpa using inv_mem this
  ·
    subst h768
    intro g
    rw [← mem_conjSub (T := T₁), ← hKdef, hK g]
    unfold s2InSp
    cases chiV 10 768 tr.2.2.2[Φ.f g]! <;> simp
  ·
    exfalso
    unfold s2RelV at hr
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hr
    obtain ⟨-, ⟨hc, hi⟩, hrel⟩ := hr
    set c := W[r]!.1
    set i := W[r]!.2
    have hgi : t1Gens.getD i 0 < 131072 := by
      have hi' : i < t1Gens.length := by rw [show t1Gens.length = 10 from rfl]; exact hi
      rw [List.getD_eq_getElem _ _ hi']
      exact hgens _ (List.getElem_mem _)
    have hd : mul c (t1Gens.getD i 0) = Φ.f (Φ.g c * Φ.g (t1Gens.getD i 0)) := by
      rw [Φ.map_mul, Φ.f_g hc, Φ.f_g hgi]
    have hdlt : mul c (t1Gens.getD i 0) < 131072 := by rw [hd]; exact Φ.lt _
    have hgd : Φ.g (mul c (t1Gens.getD i 0)) = Φ.g c * Φ.g (t1Gens.getD i 0) := by
      rw [hd, Φ.g_f]
    have hmm := Subgroup.mul_mem_iff_of_index_two hKidx (a := Φ.g c) (b := Φ.g (t1Gens.getD i 0))
    rw [← hgd, hbK _ hdlt, hbK _ hc, hbgen i hi] at hmm
    unfold s2Rel at hrel
    rw [← hrel, chiV_xor, chiV_xor, chiV_two_pow b hi] at hrb
    have key : ∀ p q s : Bool, (p = false ↔ (q = false ↔ s = false)) → ((p ^^ q) ^^ s) = false := by
      decide
    rw [key _ _ _ hmm] at hrb
    exact absurd hrb (by decide)
  ·
    exfalso
    apply hI
    rw [Φ.length_kInv_filter h0, ← hIS]
    have hP : ∀ g : G, (y⁻¹ * g * y * (y⁻¹ * g * y) = 1 ∧ y⁻¹ * g * y ≠ 1) ↔
        (g * g = 1 ∧ g ≠ 1) := by
      intro g
      rw [show y⁻¹ * g * y * (y⁻¹ * g * y) = y⁻¹ * (g * g) * y by group, ne_eq, ne_eq,
        conj_eq_one_iff', conj_eq_one_iff']
    have hc := card_conj_eq hST hyN (fun g : G => g * g = 1 ∧ g ≠ 1) hP
    rw [← hc]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => ?_)
    have e1 : h * h = 1 ↔ (h : G) * h = 1 := by
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one]
    have e2 : h ≠ 1 ↔ (h : G) ≠ 1 := by rw [ne_eq, ne_eq, Subtype.ext_iff, Subgroup.coe_one]
    have e3 : (!chiV 10 b tr.2.2.2[Φ.f h]!) = true ↔ y⁻¹ * h * y ∈ S := by
      rw [← mem_conjSub (T := T₁), ← hKdef, hK h]
      cases chiV 10 b tr.2.2.2[Φ.f h]! <;> simp
    rw [e1, e2, e3, and_assoc]
  ·
    exfalso
    apply hO
    rw [Φ.length_kOrd4_filter h0, ← hOS]
    have hP : ∀ g : G, (y⁻¹ * g * y * (y⁻¹ * g * y) ≠ 1 ∧
        y⁻¹ * g * y * (y⁻¹ * g * y) * (y⁻¹ * g * y * (y⁻¹ * g * y)) = 1) ↔
        (g * g ≠ 1 ∧ g * g * (g * g) = 1) := by
      intro g
      rw [show y⁻¹ * g * y * (y⁻¹ * g * y) = y⁻¹ * (g * g) * y by group,
        show y⁻¹ * (g * g) * y * (y⁻¹ * (g * g) * y) = y⁻¹ * (g * g * (g * g)) * y by group,
        ne_eq, ne_eq, conj_eq_one_iff', conj_eq_one_iff']
    have hc := card_conj_eq hST hyN (fun g : G => g * g ≠ 1 ∧ g * g * (g * g) = 1) hP
    rw [← hc]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => ?_)
    have e1 : h * h ≠ 1 ↔ (h : G) * h ≠ 1 := by
      rw [ne_eq, ne_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one]
    have e2 : h * h * (h * h) = 1 ↔ (h : G) * h * (h * h) = 1 := by
      rw [Subtype.ext_iff]; simp only [Subgroup.coe_mul, Subgroup.coe_one]
    have e3 : (!chiV 10 b tr.2.2.2[Φ.f h]!) = true ↔ y⁻¹ * h * y ∈ S := by
      rw [← mem_conjSub (T := T₁), ← hKdef, hK h]
      cases chiV 10 b tr.2.2.2[Φ.f h]! <;> simp
    rw [e1, e2, e3, and_assoc]

end CFSG.EvenSmallLie.OmegaEight.SpBranch
