module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank
public import CFSG.Sporadic.Co2Cert.Faithful
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Sporadic.Fi23.SlpSpec
public import Certificates.Certificate16960
public import CFSG.Certificates.InvariantMerge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Seven

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem subLetters_size' (L : Array Table) (ws : Array ℕ) :
    (subLetters L ws).size = 2 * ws.size := by
  simp [subLetters]

theorem subLetters_even' (L : Array Table) (ws : Array ℕ) {t : ℕ} (ht : t < ws.size) :
    (subLetters L ws)[2 * t]! = L[2 * ws[t]!]! := by
  rw [subLetters, getElem!_pos _ (2 * t) (by simp; omega), Array.getElem_ofFn]
  simp only [Nat.mul_mod_right, ite_true]
  congr 3
  omega

theorem subLetters_odd' (L : Array Table) (ws : Array ℕ) {t : ℕ} (ht : t < ws.size) :
    (subLetters L ws)[2 * t + 1]! = L[2 * ws[t]! + 1]! := by
  rw [subLetters, getElem!_pos _ (2 * t + 1) (by simp; omega), Array.getElem_ofFn]
  have h1 : (2 * t + 1) % 2 = 1 := by omega
  have h2 : (2 * t + 1) / 2 = t := by omega
  simp only [h1, h2, one_ne_zero, ite_false]

theorem card_centralizer_of_conj_pow {K K' : Type*} [Group K] [Group K'] [Finite K']
    (φ : K ≃* K') {y : K} {p : ℕ} [Fact p.Prime] (hy : orderOf (φ y) = p)
    (hfac : (Nat.card K').factorization p = 1) {c : ℕ}
    (hc : Nat.card (Subgroup.centralizer ({y} : Set K)) = c) {x : K'} (hx : orderOf x = p) :
    Nat.card (Subgroup.centralizer ({x} : Set K')) = c := by
  obtain ⟨g, k, hxk⟩ := exists_conj_pow_of_factorization_eq_one hfac hy hx
  have hk1 : (φ y) ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxk
    rw [hxk, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  rw [hxk, card_centralizer_conj_eq, centralizer_pow_eq_of_prime hy hk1,
    card_centralizer_mulEquiv_apply, hc]

theorem eq_bot_of_card_dvd_fiftySix {G : Type*} [Group G] {K : Subgroup G}
    (hd : Nat.card K ∣ 56) (hodd : Odd (Nat.card K)) (h7 : ¬ 7 ∣ Nat.card K) : K = ⊥ := by
  have key : ∀ d ≤ 56, d ∣ 56 → d % 2 = 1 → d % 7 ≠ 0 → d = 1 := by decide
  refine Subgroup.eq_bot_of_card_eq K (key _ (Nat.le_of_dvd (by norm_num) hd) hd
    (Nat.odd_iff.1 hodd) fun h => h7 (Nat.dvd_of_mod_eq_zero h))

@[expose] noncomputable def gen0 : co2P :=
  ⟨co2Gen 0, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def gen1 : co2P :=
  ⟨co2Gen 1, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] noncomputable def genG (z : ℤ) : co2P :=
  if z = 1 then gen0 else if z = -1 then gen0⁻¹ else if z = 2 then gen1 else gen1⁻¹

theorem idx_co2P (g : co2P) {i : ℕ} (hi : i < 2300) :
    idx 2300 g i = ((g : Equiv.Perm (Fin 2300)) ⟨i, hi⟩ : ℕ) := by
  rw [idx_of_lt _ hi]
  rfl

theorem ap_co2T (k : ℕ) (i : ℕ) (h : (co2OrigArrs[k]!)[i]! < 2 ^ 32) :
    ap (co2T k) i = (co2OrigArrs[k]!)[i]! := by
  unfold ap co2T
  by_cases hi : i < (co2OrigArrs[k]!).size
  · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by rwa [getElem!_pos _ i hi] at h), getElem!_pos _ i hi]
  · rw [getElem!_neg _ i (by simpa using hi), getElem!_neg _ i hi]
    rfl

theorem rep_co2T {k : ℕ} (hk : k < 2) {g : co2P}
    (hg : (g : Equiv.Perm (Fin 2300)) = co2Gen k) : Rep 2300 (co2T k) g := by
  intro i hi
  have h := rep_co2Gen hk ⟨i, hi⟩
  have hlt : (co2OrigArrs[k]!)[i]! < 2 ^ 32 := by
    rw [h]
    exact lt_trans (Fin.isLt _) (by norm_num)
  rw [ap_co2T k i hlt, idx_co2P g hi, hg]
  exact h

theorem eq_of_eqTab2 {A B : Table} {g h : co2P} (hA : Rep 2300 A g) (hB : Rep 2300 B h)
    (e : eqTab2 A B = true) : g = h := by
  unfold eqTab2 at e
  rw [List.all_eq_true] at e
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have h1 := hA x.1 x.2
  have h2 := hB x.1 x.2
  rw [idx_co2P g x.2] at h1
  rw [idx_co2P h x.2] at h2
  rw [← h1, ← h2]
  exact beq_iff_eq.1 (e x.1 (List.mem_range.2 x.2))

theorem ne_of_eqTab2_false {A : Table} {g : co2P} (hA : Rep 2300 A g)
    (e : eqTab2 A (idT 2300) = false) : g ≠ 1 := by
  rintro rfl
  have : eqTab2 A (idT 2300) = true := by
    unfold eqTab2
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [hA i hi, (Rep.idT (G := co2P) (by norm_num)) i hi]
    exact beq_self_eq_true _
  rw [this] at e
  exact Bool.noConfusion e

local notation "LL" => slpLetters 2300 (co2Gens (co2T 0) (co2T 1)) co2SevenData.words

local notation "YY" => LL[2 * co2SevenData.is]!

local notation "ωω" => ap LL[2 * co2SevenData.ih]! 0

set_option quotPrecheck false in
local notation "DD" => co2SevenData.id.map fun j => LL[2 * j]!

set_option quotPrecheck false in
local notation "BB" => (Array.range 7).map fun i => iterAp YY i ωω

local notation "LCC" => subLetters LL co2SevenData.chain

local notation "TT" => chainTrees 2300 LCC BB

local notation "CT" => centTabs7 2300 YY DD

theorem co2Seven_parts :
    invOK 2300 (co2T 0) (invT 2300 (co2T 0)) = true ∧
      invOK 2300 (co2T 1) (invT 2300 (co2T 1)) = true ∧
      slpOK co2SevenData.words = true ∧ co2SevenData.is < co2SevenData.words.size ∧
      co2SevenData.id.size = 8 ∧
      (∀ r < 8, co2SevenData.id[r]! < co2SevenData.words.size) ∧
      (∀ j < co2SevenData.words.size, invOK 2300 LL[2 * j]! LL[2 * j + 1]! = true) ∧
      (∀ t < co2SevenData.chain.size, co2SevenData.chain[t]! < co2SevenData.words.size) ∧
      ωω < 2300 ∧
      eqTab2 (powT 2300 7 YY) (idT 2300) = true ∧ eqTab2 YY (idT 2300) = false ∧
      (∀ r < 8, eqTab2 (compT 2300 (DD)[r]! YY) (compT 2300 YY (DD)[r]!) = true) ∧
      (∀ i < 7, treeOK 2300 (BB)[i]! (TT)[i]! LCC (levelLetters LCC BB i) = true) ∧
      (List.range 7).foldl (fun acc i => acc * (TT)[i]!.pts.size) 1 = cardCo2 () ∧
      Nat.count (fun p => sift TT LCC (Array.range 7) BB 0 (tupleOf YY 7 p) = true) 2300 ≤ 56 ∧
      imagesDistinct CT ωω = true := by
  have h := Certificates.certificate16960
  unfold co2SevenOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, -⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩ := h
  refine ⟨h1, h2, h3, h4, h6, fun r hr => ?_, fun j hj => ?_, fun t ht => ?_, h10, h12, h13,
    fun r hr => ?_, fun i hi => ?_, h16, h17, h18⟩
  · rw [Array.all_eq_true] at h7
    rw [getElem!_pos _ r (by rw [h6]; exact hr)]
    exact of_decide_eq_true (h7 r (by rw [h6]; exact hr))
  · rw [List.all_eq_true] at h8
    exact h8 j (List.mem_range.2 hj)
  · rw [Array.all_eq_true] at h9
    rw [getElem!_pos _ t ht]
    exact of_decide_eq_true (h9 t ht)
  · rw [Array.all_eq_true] at h14
    have hr' : r < (DD).size := by rw [Array.size_map, h6]; exact hr
    rw [getElem!_pos _ r hr']
    exact h14 r hr'
  · rw [List.all_eq_true] at h15
    exact h15 i (List.mem_range.2 hi)

@[expose] noncomputable def g7 (j : ℕ) : co2P :=
  CFSG.Sporadic.Fi23.slpG genG co2SevenData.words j

theorem rep_gen7 : ∀ z, Rep 2300 (co2Gens (co2T 0) (co2T 1) z) (genG z) := by
  have h0 : Rep 2300 (co2T 0) gen0 := rep_co2T (by norm_num) rfl
  have h1 : Rep 2300 (co2T 1) gen1 := rep_co2T (by norm_num) rfl
  obtain ⟨hi0, hi1, -⟩ := co2Seven_parts
  intro z
  unfold co2Gens genG
  split_ifs
  · exact h0
  · exact h0.inv_of_invOK hi0
  · exact h1
  · exact h1.inv_of_invOK hi1

theorem rep_g7 : ∀ j < co2SevenData.words.size, Rep 2300 LL[2 * j]! (g7 j) :=
  CFSG.Sporadic.Fi23.rep_slpLetters (by norm_num) rep_gen7 co2Seven_parts.2.2.1
    co2Seven_parts.2.2.2.2.2.2.1

@[expose] noncomputable def sG : co2P := g7 co2SevenData.is

@[expose] noncomputable def dG (r : ℕ) : co2P := g7 co2SevenData.id[r]!

@[expose] noncomputable def centG (t : ℕ) : co2P := sG ^ (t / 8) * dG (t % 8)

theorem rep_YY : Rep 2300 YY sG := rep_g7 _ co2Seven_parts.2.2.2.1

theorem rep_DD {r : ℕ} (hr : r < 8) : Rep 2300 (DD)[r]! (dG r) := by
  have h6 := co2Seven_parts.2.2.2.2.1
  rw [getElem!_pos _ r (by rw [Array.size_map, h6]; exact hr), Array.getElem_map,
    ← getElem!_pos co2SevenData.id r (by rw [h6]; exact hr)]
  exact rep_g7 _ (co2Seven_parts.2.2.2.2.2.1 r hr)

theorem rep_centTabs {t : ℕ} (ht : t < 56) : Rep 2300 (CT)[t]! (centG t) := by
  have hCT : (CT)[t]! = compT 2300 (powT 2300 (t / 8) YY) (DD)[t % 8]! := by
    rw [centTabs7, getElem!_pos _ t (by simpa using ht), Array.getElem_map, Array.getElem_range]
  rw [hCT]
  exact (rep_YY.powT (by norm_num) _).compT (rep_DD (Nat.mod_lt _ (by norm_num)))

theorem sG_pow : sG ^ 7 = 1 :=
  eq_of_eqTab2 (rep_YY.powT (by norm_num) 7) (Rep.idT (by norm_num))
    co2Seven_parts.2.2.2.2.2.2.2.2.2.1

theorem orderOf_sG : orderOf sG = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime sG_pow (ne_of_eqTab2_false rep_YY co2Seven_parts.2.2.2.2.2.2.2.2.2.2.1)

theorem commute_dG {r : ℕ} (hr : r < 8) : Commute sG (dG r) :=
  (eq_of_eqTab2 ((rep_DD hr).compT rep_YY) (rep_YY.compT (rep_DD hr))
    (co2Seven_parts.2.2.2.2.2.2.2.2.2.2.2.1 r hr)).symm

theorem centG_mem (t : ℕ) : centG t ∈ Subgroup.centralizer ({sG} : Set co2P) := by
  have hc : Commute sG (centG t) :=
    ((Commute.refl sG).pow_right _).mul_right (commute_dG (Nat.mod_lt _ (by norm_num)))
  exact Subgroup.mem_centralizer_singleton_iff.2 hc.eq.symm

theorem card_centralizer_sG_le :
    Nat.card (Subgroup.centralizer ({sG} : Set co2P)) ≤ 56 := by
  obtain ⟨-, -, -, -, -, -, hinv, hch, -, -, -, -, htree, hprod, hcount, -⟩ := co2Seven_parts
  have hrepC : ∀ t < (LCC).size / 2, Rep 2300 (LCC)[2 * t]! (g7 co2SevenData.chain[t]!) := by
    intro t ht
    rw [subLetters_size'] at ht
    have ht' : t < co2SevenData.chain.size := by omega
    rw [subLetters_even' _ _ ht']
    exact rep_g7 _ (hch t ht')
  have h2C : (LCC).size % 2 = 0 := by rw [subLetters_size']; omega
  have hinvC : ∀ t < (LCC).size / 2, invOK 2300 (LCC)[2 * t]! (LCC)[2 * t + 1]! = true := by
    intro t ht
    rw [subLetters_size'] at ht
    have ht' : t < co2SevenData.chain.size := by omega
    rw [subLetters_even' _ _ ht', subLetters_odd' _ _ ht']
    exact hinv _ (hch t ht')
  have hbsz : (BB).size = 7 := by simp
  have htree' : ∀ i < (BB).size, Perm.Native.treeOK 2300 (BB)[i]! (TT)[i]! LCC
      (levelLetters LCC BB i) = true := by
    intro i hi
    rw [hbsz] at hi
    exact htree i hi
  have hfold : (List.range 7).foldl (fun acc i => acc * (TT)[i]!.pts.size) 1 =
      ∏ i ∈ Finset.range 7, (TT)[i]!.pts.size := by
    simp [Finset.prod_range_succ, List.range_succ]
  have hcard : ∏ l ∈ Finset.range (BB).size, (TT)[l]!.pts.size = Nat.card co2P := by
    rw [hbsz, ← hfold, hprod, card_co2P]
    rfl
  have hbase : ∀ i < (BB).size, (BB)[i]! = iterAp YY i (BB)[0]! := by
    intro i hi
    have h0 : (BB)[0]! = ωω := by
      rw [getElem!_pos _ 0 (by simp), Array.getElem_map, Array.getElem_range]
      rfl
    rw [h0, getElem!_pos _ i (by simpa using hi), Array.getElem_map, Array.getElem_range]
  have hcardC := card_centralizer_le_of_tupleSift (G := co2P)
    (gs := fun t => g7 co2SevenData.chain[t]!) hrepC h2C hinvC (by simp [chainTrees]) htree'
    hcard rep_YY (by rw [hbsz]; norm_num) hbase
  rw [hbsz] at hcardC
  exact hcardC.trans hcount

theorem centG_injective {s t : ℕ} (hs : s < 56) (ht : t < 56) (h : centG s = centG t) :
    s = t := by
  obtain ⟨-, -, -, -, -, -, -, -, hω, -, -, -, -, -, -, hdist⟩ := co2Seven_parts
  by_contra hne
  unfold imagesDistinct at hdist
  rw [List.all_eq_true] at hdist
  have hsz : (CT).size = 56 := by simp [centTabs7]
  have h1 := hdist s (List.mem_range.2 (by rw [hsz]; exact hs))
  rw [List.all_eq_true] at h1
  have h2 := h1 t (List.mem_range.2 (by rw [hsz]; exact ht))
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
  rcases h2 with h2 | h2
  · exact hne h2
  · apply h2
    rw [rep_centTabs hs _ hω, rep_centTabs ht _ hω, h]

theorem card_centralizer_sG :
    Nat.card (Subgroup.centralizer ({sG} : Set co2P)) = 56 := by
  have : Finite co2P := Nat.finite_of_card_ne_zero (by rw [card_co2P]; norm_num)
  let f : Fin 56 → Subgroup.centralizer ({sG} : Set co2P) := fun t => ⟨centG t, centG_mem t⟩
  have hf : Function.Injective f := fun s t hst =>
    Fin.ext (centG_injective s.2 t.2 (congrArg Subtype.val hst))
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  exact le_antisymm card_centralizer_sG_le hle

theorem co2_seven_card_centralizer
    (x : CFSG.Blueprint.NativeSporadic.Co2) (hx : orderOf x = 7) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co2)) = 56 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.Co2 = 42305421312000 := by
    rw [Nat.card_congr co2PermEquiv.toEquiv, card_co2P]
  have : Finite CFSG.Blueprint.NativeSporadic.Co2 :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hy : orderOf (co2PermEquiv.symm sG) = 7 := by
    rw [MulEquiv.orderOf_eq]; exact orderOf_sG
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.Co2).factorization 7 = 1 := by
    rw [hcard, show (42305421312000 : ℕ) = 7 * 6043631616000 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  exact @card_centralizer_of_conj_pow co2P CFSG.Blueprint.NativeSporadic.Co2 _ Units.instGroup _
    co2PermEquiv.symm sG 7 _ hy hfac 56 card_centralizer_sG x hx

theorem co2_seven_eq_bot
    (x : CFSG.Blueprint.NativeSporadic.Co2) (hx : orderOf x = 7)
    {K : Subgroup CFSG.Blueprint.NativeSporadic.Co2}
    (hK : K ≤ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co2))
    (hodd : Odd (Nat.card K)) (h7 : ¬ 7 ∣ Nat.card K) : K = ⊥ := by
  have hd : Nat.card K ∣ 56 := by
    rw [← co2_seven_card_centralizer x hx]
    exact Subgroup.card_dvd_of_le hK
  exact eq_bot_of_card_dvd_fiftySix hd hodd h7

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Seven
