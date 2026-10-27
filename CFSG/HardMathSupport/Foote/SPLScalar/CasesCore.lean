module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryLattice
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar.Core

open CFSG CFSG.AGLEmbedding CFSG.Open CFSG.LocalAnalysis.ComponentInitial

private theorem pow_nine_mod_five (k : ℕ) : 9 ^ k % 5 = 1 ∨ 9 ^ k % 5 = 4 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private theorem pow_nine_mod_eight (k : ℕ) : 9 ^ k % 8 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private theorem three_pow_mod_five {n : ℕ} (h : Odd n) : 3 ^ n % 5 = 3 ∨ 3 ^ n % 5 = 2 := by
  obtain ⟨k, rfl⟩ := h
  have : 3 ^ (2 * k + 1) = 3 * 9 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [this]; rcases pow_nine_mod_five k with h | h <;> omega

private theorem three_pow_mod_eight {n : ℕ} (h : Odd n) : 3 ^ n % 8 = 3 := by
  obtain ⟨k, rfl⟩ := h
  have : 3 ^ (2 * k + 1) = 3 * 9 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [this]; have := pow_nine_mod_eight k; omega

private theorem five_not_dvd_of_mod {q : ℕ} (h : q % 5 = 3 ∨ q % 5 = 2) :
    ¬ 5 ∣ q ∧ q ^ 2 % 5 = 4 ∧ (q ^ 3 % 5 = 2 ∨ q ^ 3 % 5 = 3) := by
  rcases h with h | h
  · refine ⟨by omega, ?_, Or.inl ?_⟩ <;> rw [Nat.pow_mod, h]
  · refine ⟨by omega, ?_, Or.inr ?_⟩ <;> rw [Nat.pow_mod, h]

theorem not_five_dvd_psl2_numerator {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
  obtain ⟨h1, h2, -⟩ := five_not_dvd_of_mod (three_pow_mod_five hn)
  have hp : Nat.Prime 5 := by norm_num
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact h1 h
  · have hpos : 1 ≤ (3 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega

theorem not_five_dvd_unitary_numerator {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * ((3 ^ n) ^ 2 - 1) := by
  obtain ⟨h1, h2, h3⟩ := five_not_dvd_of_mod (three_pow_mod_five hn)
  have hp : Nat.Prime 5 := by norm_num
  intro h
  have hpos : 1 ≤ (3 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact h1 (hp.dvd_of_dvd_pow h)
    · omega
  · omega

theorem not_five_dvd_ree_order {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) := by
  obtain ⟨h1, h2, h3⟩ := five_not_dvd_of_mod (three_pow_mod_five hn)
  have hq := three_pow_mod_five hn
  have hp : Nat.Prime 5 := by norm_num
  have hpos : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by positivity)
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact h1 (hp.dvd_of_dvd_pow h)
    · omega
  · omega

theorem not_thirtyTwo_dvd_ree_order {n : ℕ} (hn : Odd n) :
    ¬ 32 ∣ (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) := by
  have h8 := three_pow_mod_eight hn
  have h3 : (3 ^ n) ^ 3 % 8 = 3 := by rw [Nat.pow_mod, h8]
  have hpos : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by positivity)
  have hodd3 : Odd ((3 ^ n) ^ 3) := Odd.pow (Odd.pow (by decide))
  obtain ⟨X, hX⟩ : ∃ X, (3 ^ n) ^ 3 + 1 = 4 * X ∧ Odd X := ⟨((3 ^ n) ^ 3 + 1) / 4, by omega, by
    rw [Nat.odd_iff]; omega⟩
  obtain ⟨Y, hY⟩ : ∃ Y, 3 ^ n - 1 = 2 * Y ∧ Odd Y := ⟨(3 ^ n - 1) / 2, by omega, by
    rw [Nat.odd_iff]; omega⟩
  rw [hX.1, hY.1]
  intro h
  have : 32 ∣ 8 * ((3 ^ n) ^ 3 * X * Y) := by
    have e : (3 ^ n) ^ 3 * (4 * X) * (2 * Y) = 8 * ((3 ^ n) ^ 3 * X * Y) := by ring
    rwa [e] at h
  have h4 : 4 ∣ (3 ^ n) ^ 3 * X * Y := by
    have := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8)).mp (by simpa using this : 8 * 4 ∣ 8 * ((3 ^ n) ^ 3 * X * Y))
    exact this
  have hodd : Odd ((3 ^ n) ^ 3 * X * Y) := (hodd3.mul hX.2).mul hY.2
  have := (Nat.even_iff.mpr (Nat.mod_eq_zero_of_dvd (dvd_trans (by norm_num : 2 ∣ 4) h4)))
  exact (Nat.not_even_iff_odd.mpr hodd) this

theorem card_dvd_of_surjective {KC L : Type} [Group KC] [Group L] [Finite KC]
    {W : Subgroup KC} (f : W →* L) (hf : Function.Surjective f) :
    Nat.card L ∣ Nat.card KC := by
  have e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have h1 : Nat.card L ∣ Nat.card W := by
    rw [← Nat.card_congr e.toEquiv]
    exact ⟨Nat.card f.ker, by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]⟩
  exact h1.trans (Subgroup.card_subgroup_dvd_card W)

theorem exists_equiv_of_map_eq {KC L : Type} [Group KC] [Group L] {W : Subgroup KC}
    (f : W →* L) (hker : ∀ w : W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup KC}
    (hEW : E ≤ W) (hE : IsPGroup 3 E) {TL : Subgroup L} (hmap : (E.subgroupOf W).map f = TL) :
    ∃ φ : E ≃* TL, ∀ x : E, ((φ x : TL) : L) = f ⟨x, hEW x.2⟩ := by
  let g : E →* L := f.comp (Subgroup.inclusion hEW)
  have hg : ∀ x : E, g x = f ⟨x, hEW x.2⟩ := fun x => rfl
  have hmem : ∀ x : E, g x ∈ TL := by
    intro x
    rw [← hmap]
    exact ⟨Subgroup.inclusion hEW x, by simp [Subgroup.mem_subgroupOf], rfl⟩
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : f (Subgroup.inclusion hEW x) = 1 := hx
    have h2 := hker _ h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE) x
    have h3 : orderOf (Subgroup.inclusion hEW x) = orderOf x :=
      orderOf_injective _ (Subgroup.inclusion_injective hEW) x
    rw [h3, hk] at h2
    have hk0 : k = 0 := by
      by_contra hne
      have : 3 ∣ 3 ^ k := dvd_pow_self 3 hne
      exact absurd ((Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hne) 3 3).mp h2) (by decide)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  refine ⟨MulEquiv.ofBijective (g.codRestrict TL hmem) ⟨?_, ?_⟩, fun x => rfl⟩
  · intro x y hxy
    apply hinj
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨⟨(w : KC), by simpa [Subgroup.mem_subgroupOf] using hw⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem card_eq_of_altSix {L : Type} [Group L]
    (h : Nonempty (L ≃* alternatingGroup (Fin 6))) : Nat.card L = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem thirtyTwo_dvd_of_smallUnitary (hUO : KFactUnitaryOrder) {L : Type} [Group L] [Finite L]
    (h : IsSmallUnitary 3 L) : 32 ∣ Nat.card L := by
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨e⟩⟩ := h
  have hU : IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  have h := hUO L 3 d hU ⟨e⟩
  have hfe : d.1.fieldExponent = 1 := by rw [hdq]; simp [hqe]
  rw [hfe] at h
  norm_num at h
  omega

theorem not_five_dvd_card_psl2GF {n : ℕ} (hn : Odd n) : ¬ 5 ∣ Nat.card (PSL2GF 3 n) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : Nat.card (GaloisField 3 n) = 3 ^ n := GaloisField.card 3 n (by rintro rfl; exact (Nat.not_odd_zero hn))
  have hc := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear (GaloisField 3 n) 2
    (by norm_num)
  rw [hq] at hc
  simp only [Finset.Icc_self, Finset.prod_singleton] at hc
  have hc' : Nat.card (PSL2GF 3 n) = (3 ^ n * ((3 ^ n) ^ 2 - 1)) / Nat.gcd 2 (3 ^ n - 1) := by
    simpa using hc
  intro h5
  apply not_five_dvd_psl2_numerator hn
  refine h5.trans ?_
  rw [hc']
  apply Nat.div_dvd_of_dvd
  refine (Nat.gcd_dvd_right 2 (3 ^ n - 1)).trans ?_
  refine Dvd.dvd.mul_left ?_ _
  simpa using Nat.sub_dvd_pow_sub_pow (3 ^ n) 1 2

theorem altSix_sylow {L : Type} [Group L] [Finite L]
    (h : Nonempty (L ≃* alternatingGroup (Fin 6))) (TL : Sylow 3 L) :
    Nat.card (TL : Subgroup L) = 9 ∧ IsElemAbelian 3 (TL : Subgroup L) := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h360 : Nat.card L = 360 := card_eq_of_altSix ⟨e⟩
  have hcard : Nat.card (TL : Subgroup L) = 9 := by
    rw [Sylow.card_eq_multiplicity, h360, Nat.factorization_def _ Nat.prime_three]
    have : (360 : ℕ) = 3 ^ 2 * 40 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num)]
    rw [padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  refine ⟨hcard, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (G := (TL : Subgroup L)) (by rw [hcard]; norm_num), fun x hx => ?_⟩⟩
  have hdvd : orderOf (⟨x, hx⟩ : (TL : Subgroup L)) ∣ 9 := by
    rw [← hcard]; exact orderOf_dvd_natCard _
  have h9 : (⟨x, hx⟩ : (TL : Subgroup L)) ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hx9 : x ^ 9 = 1 := by simpa using congrArg Subtype.val h9
  have hperm : ∀ y : Equiv.Perm (Fin 6), y ^ 9 = 1 → y ^ 3 = 1 := by decide +kernel
  have hy : (e x : Equiv.Perm (Fin 6)) ^ 3 = 1 := by
    apply hperm
    have := congrArg (fun z => ((e z : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) hx9
    simpa using this
  apply e.injective
  apply Subtype.ext
  simpa using hy

theorem not_comm_smallUnitary (hUS : KFactUnitarySylowStructure) {L : Type} [Group L] [Finite L]
    (h : IsSmallUnitary 3 L) (TL : Sylow 3 L) :
    ¬ ∀ x ∈ (TL : Subgroup L), ∀ y ∈ (TL : Subgroup L), x * y = y * x := by
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨e⟩⟩ := h
  have hU : IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, hcomm, -, -⟩ := hUS L 3 d (by norm_num) hU ⟨e⟩ TL
  have hfe : d.1.fieldExponent = 1 := by rw [hdq]; simp [hqe]
  rw [hfe] at hcard
  intro hc
  have hle : (TL : Subgroup L) ≤ Subgroup.centralizer ((TL : Subgroup L) : Set L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hc y hy x hx
  have h1 : ⁅(TL : Subgroup L), (TL : Subgroup L)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  rw [h1] at hcomm
  have h2 : (TL : Subgroup L) = ⊥ := by
    rw [inf_eq_left.mpr hle] at hcomm
    exact hcomm.symm
  rw [h2, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem false_of_ree (hRO : KFactReeOrder) (hUO : KFactUnitaryOrder) {KC L : Type} [Group KC]
    [Finite KC] [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d)
    (e : KC ≃* CatGroup d) (hL : Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ IsSmallUnitary 3 L)
    {W : Subgroup KC} (f : W →* L) (hf : Function.Surjective f) : False := by
  have hdvd := card_dvd_of_surjective f hf
  have hord := hRO KC d hd ⟨e⟩
  have hodd := hd.odd_fieldExponent
  rcases hL with hA | hU
  · rw [card_eq_of_altSix hA, hord] at hdvd
    exact not_five_dvd_ree_order hodd ((by norm_num : 5 ∣ 360).trans hdvd)
  · rw [hord] at hdvd
    exact not_thirtyTwo_dvd_ree_order hodd ((thirtyTwo_dvd_of_smallUnitary hUO hU).trans hdvd)

theorem sylow_comm_of_linTwo {KC : Type} [Group KC] [Finite KC] {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hn : 1 ≤ n) (hd : IsLinTwoIndex 3 n d) (e : KC ≃* CatGroup d) (T' : Sylow 3 KC) :
    ∀ x ∈ (T' : Subgroup KC), ∀ y ∈ (T' : Subgroup KC), x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₁⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  let eK : KC ≃* PSL2GF 3 n := e.trans e₁
  have hfs : Function.Surjective (eK : KC →* PSL2GF 3 n) := eK.surjective
  let U : Sylow 3 (PSL2GF 3 n) := T'.mapSurjective hfs
  have hUT : (U : Subgroup (PSL2GF 3 n)) = (T' : Subgroup KC).map (eK : KC →* PSL2GF 3 n) :=
    Sylow.coe_mapSurjective hfs T'
  have hU := (psl2GF_sylow 3 n hn U).1
  intro x hx y hy
  have hx' : eK x ∈ (U : Subgroup (PSL2GF 3 n)) := by rw [hUT]; exact ⟨x, hx, rfl⟩
  have hy' : eK y ∈ (U : Subgroup (PSL2GF 3 n)) := by rw [hUT]; exact ⟨y, hy, rfl⟩
  have := hU.1.is_comm.comm ⟨eK x, hx'⟩ ⟨eK y, hy'⟩
  apply eK.injective
  simpa using congrArg Subtype.val this

theorem even_of_lin_altSix {KC L : Type} [Group KC] [Finite KC] [Group L] {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (hd : IsLinTwoIndex 3 n d) (e : KC ≃* CatGroup d)
    (hA : Nonempty (L ≃* alternatingGroup (Fin 6))) {W : Subgroup KC} (f : W →* L)
    (hf : Function.Surjective f) : Even n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₁⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  let eK : KC ≃* PSL2GF 3 n := e.trans e₁
  by_contra hev
  have hodd : Odd n := Nat.not_even_iff_odd.mp hev
  have h1 := (card_dvd_of_surjective f hf)
  rw [card_eq_of_altSix hA, Nat.card_congr eK.toEquiv] at h1
  exact not_five_dvd_card_psl2GF hodd ((by norm_num : 5 ∣ 360).trans h1)

theorem false_of_lin_unitaryThree (hUS : KFactUnitarySylowStructure) {KC L : Type} [Group KC]
    [Finite KC] [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex} {n : ℕ} (hn : 1 ≤ n)
    (hd : IsLinTwoIndex 3 n d) (e : KC ≃* CatGroup d) (hL : IsSmallUnitary 3 L)
    (TL : Sylow 3 L) (T' : Sylow 3 KC) {E : Subgroup KC} (hET : E ≤ (T' : Subgroup KC))
    (φ : E ≃* (TL : Subgroup L)) : False := by
  have hT := sylow_comm_of_linTwo hn hd e T'
  refine not_comm_smallUnitary hUS hL TL (fun x hx y hy => ?_)
  obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
  obtain ⟨b, hb⟩ := φ.surjective ⟨y, hy⟩
  have hx' : x = ((φ a : (TL : Subgroup L)) : L) := by rw [ha]
  have hy' : y = ((φ b : (TL : Subgroup L)) : L) := by rw [hb]
  have h : a * b = b * a := Subtype.ext (hT a (hET a.2) b (hET b.2))
  have := congrArg (fun z => ((φ z : (TL : Subgroup L)) : L)) h
  rw [hx', hy']
  simpa [map_mul] using this

theorem unitary_alt_case (hUO : KFactUnitaryOrder) {KC L : Type} [Group KC] [Finite KC]
    [Group L] {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex 3 d) (e : KC ≃* CatGroup d)
    (hA : Nonempty (L ≃* alternatingGroup (Fin 6))) {W : Subgroup KC} (f : W →* L)
    (hf : Function.Surjective f) : Even d.1.fieldExponent := by
  by_contra hev
  have hodd : Odd d.1.fieldExponent := Nat.not_even_iff_odd.mp hev
  have h1 := card_dvd_of_surjective f hf
  rw [card_eq_of_altSix hA] at h1
  have h5 : 5 ∣ Nat.card KC := (by norm_num : 5 ∣ 360).trans h1
  have hord := hUO KC 3 d hd ⟨e⟩
  exact not_five_dvd_unitary_numerator hodd (hord ▸ h5.trans (Dvd.intro _ rfl))

theorem elemAbelian_of_altSix {KC L : Type} [Group KC] [Group L] [Finite L] {W : Subgroup KC}
    (f : W →* L) (hker : ∀ w : W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup KC}
    (hEW : E ≤ W) (hE : IsPGroup 3 E) (hA : Nonempty (L ≃* alternatingGroup (Fin 6)))
    (TL : Sylow 3 L) (hmap : (E.subgroupOf W).map f = (TL : Subgroup L)) :
    IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨φ, hφ⟩ := exists_equiv_of_map_eq f hker hEW hE hmap
  obtain ⟨h9, hTL⟩ := altSix_sylow hA TL
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, by rw [Nat.card_congr φ.toEquiv, h9]⟩
  · apply φ.injective
    rw [map_mul, map_mul]
    exact hTL.1.is_comm.comm (φ a) (φ b)
  · have := hTL.2 (φ ⟨x, hx⟩) (φ ⟨x, hx⟩).2
    have h : φ ⟨x, hx⟩ ^ 3 = 1 := Subtype.ext (by simpa using this)
    rw [← map_pow] at h
    have := φ.injective (h.trans (map_one φ).symm)
    simpa using congrArg Subtype.val this

theorem center_le_of_unitary_unitaryThree (hUS : KFactUnitarySylowStructure) {KC L : Type}
    [Group KC] [Finite KC] [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex 3 d) (e : KC ≃* CatGroup d) (hL : IsSmallUnitary 3 L) (TL : Sylow 3 L)
    (T' : Sylow 3 KC) {E : Subgroup KC} (hET : E ≤ (T' : Subgroup KC))
    (φ : E ≃* (TL : Subgroup L)) :
    E ⊓ Subgroup.centralizer (E : Set KC) ≤
      (T' : Subgroup KC) ⊓ Subgroup.centralizer ((T' : Subgroup KC) : Set KC) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d', ⟨q, hqp, hqe, hdq⟩, ⟨eL⟩⟩ := hL
  obtain ⟨-, hcommL, -, -⟩ := hUS L 3 d' (by norm_num) ⟨q, hqp, hdq⟩ ⟨eL⟩ TL
  obtain ⟨-, hcommK, -, -⟩ := hUS KC 3 d (by norm_num) hd ⟨e⟩ T'
  have hEE : ⁅E, E⁆ ≤ ⁅(T' : Subgroup KC), (T' : Subgroup KC)⁆ :=
    Subgroup.commutator_mono hET hET
  rw [hcommK] at hEE
  intro x hx
  have hxE : x ∈ E := hx.1
  have hxC := Subgroup.mem_centralizer_iff.mp hx.2
  refine hEE ?_
  let ι : E →* L := (TL : Subgroup L).subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hιtop : (⊤ : Subgroup E).map ι = (TL : Subgroup L) := by
    ext y
    constructor
    · rintro ⟨a, -, rfl⟩
      exact (φ a).2
    · intro hy
      obtain ⟨a, ha⟩ := φ.surjective ⟨y, hy⟩
      exact ⟨a, trivial, by simp [ι, ha]⟩
  have hxTL : ι ⟨x, hxE⟩ ∈ (TL : Subgroup L) ⊓
      Subgroup.centralizer ((TL : Subgroup L) : Set L) := by
    refine ⟨(φ ⟨x, hxE⟩).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    have hyy : y = ι y' := by simp [ι, hy']
    have h2 : y' * ⟨x, hxE⟩ = ⟨x, hxE⟩ * y' := Subtype.ext (hxC y' y'.2)
    have h3 := congrArg ι h2
    simpa [hyy, map_mul] using h3
  rw [← hcommL, ← hιtop, ← Subgroup.map_commutator] at hxTL
  obtain ⟨w, hw, hwx⟩ := hxTL
  have hw' : w = ⟨x, hxE⟩ := hι hwx
  have hmem : ((w : E) : KC) ∈ ⁅E, E⁆ := by
    have := Subgroup.mem_map_of_mem E.subtype hw
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    exact this
  rw [hw'] at hmem
  exact hmem

end CFSG.HardMathSupport.Foote.SPLScalar.Core
