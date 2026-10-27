module

public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore

theorem gLAPPrimeCoreOf_eq_bot_of_classSize {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C : Subgroup G} {a r : ℕ} (hC : Nat.card C = p ^ a * r) (hr : ¬ p ∣ r)
    (h : ∀ w ∈ C, (orderOf w).Prime → orderOf w ∣ r →
      Nat.card ↥(C ⊓ Subgroup.centralizer ({w} : Set G)) * r < Nat.card C) :
    GLAPPrimeCoreOf p C = ⊥ := by
  by_contra hL
  set L := GLAPPrimeCoreOf p C with hLdef
  have hLC : L ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card L) := coprime_card_GLAPPrimeCoreOf hp C
  have hLr : Nat.card L ∣ r := by
    have h1 : Nat.card L ∣ p ^ a * r := hC ▸ Subgroup.card_dvd_of_le hLC
    exact (Nat.Coprime.pow_left a hcop).symm.dvd_of_dvd_mul_left h1
  have hLne : Nat.card L ≠ 1 := fun h => hL (Subgroup.card_eq_one.1 h)
  obtain ⟨q, hq, hqL⟩ := Nat.exists_prime_and_dvd hLne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) q hqL
  set w : G := (x : G) with hw
  have hwo : orderOf w = q := by rw [hw, Subgroup.orderOf_coe, hx]
  have hwL : w ∈ L := x.2
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := C)
    rw [hC, mul_zero] at this
    exact lt_irrefl _ this
  have hcls : conjClass C w ⊆ (L : Set G) := by
    rintro _ ⟨g, hg, rfl⟩
    exact GLAPPrimeCoreOf_conj_mem g hg w hwL
  have hncard : (conjClass C w).ncard ≤ r := by
    calc (conjClass C w).ncard ≤ (L : Set G).ncard := Set.ncard_le_ncard hcls (Set.toFinite _)
      _ = Nat.card L := (Nat.card_coe_set_eq (L : Set G)).symm
      _ ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hLr
  have horb := ncard_conjClass_mul_card C w
  have hlt := h w (hLC hwL) (by rw [hwo]; exact hq) (by rw [hwo]; exact hqL.trans hLr)
  have : Nat.card C ≤ Nat.card ↥(C ⊓ Subgroup.centralizer ({w} : Set G)) * r := by
    rw [← horb, mul_comm]
    exact Nat.mul_le_mul_left _ hncard
  omega

section Hyperplanes

variable {p k : ℕ} [hp : Fact p.Prime]

omit hp in
theorem card_vec : Nat.card (Multiplicative (Fin k → ZMod p)) = p ^ k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem ofAdd_eq_prod (a : Fin k → ZMod p) :
    Multiplicative.ofAdd a =
      ∏ i, (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) ^ (a i).val := by
  have h1 : a = ∑ i, (a i).val • (Pi.single i (1 : ZMod p) : Fin k → ZMod p) := by
    conv_lhs => rw [← Finset.univ_sum_single a]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  conv_lhs => rw [h1]
  rw [ofAdd_sum]
  exact Finset.prod_congr rfl fun i _ => ofAdd_nsmul _ _

theorem exists_dot_eq_zero_imp_mem {G : Type*} [Group G]
    (φ : Multiplicative (Fin k → ZMod p) →* G) (hφ : Function.Injective φ) {B : Subgroup G}
    (hB : B ≤ φ.range) (hcard : Nat.card B * p = p ^ k) :
    ∃ f : Fin k → ZMod p, f ≠ 0 ∧ ∀ a : Fin k → ZMod p, ∑ i, f i * a i = 0 →
      φ (Multiplicative.ofAdd a) ∈ B := by
  classical
  have hp1 := hp.out.one_lt
  set W : Subgroup (Multiplicative (Fin k → ZMod p)) := B.comap φ with hWdef
  have hWB : Nat.card W = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hφ, hWdef, Subgroup.map_comap_eq_self hB]
  have hBpos : 0 < Nat.card B := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hcard
    exact (pow_pos hp.out.pos k).ne' hcard.symm
  have hidx : W.index = p := by
    have h1 := W.card_mul_index
    rw [hWB, card_vec, ← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hBpos h1
  have hmemW : ∀ a : Fin k → ZMod p, Multiplicative.ofAdd a ∈ W → φ (Multiplicative.ofAdd a) ∈ B :=
    fun a ha => ha
  have hWtop : ¬ ∀ a : Fin k → ZMod p, Multiplicative.ofAdd a ∈ W := by
    intro hall
    have : W = ⊤ := eq_top_iff.2 fun x _ => by
      simpa using hall (Multiplicative.toAdd x)
    rw [this, Subgroup.index_top] at hidx
    omega
  set π := QuotientGroup.mk' W with hπ
  have hex : ∃ i₀, Multiplicative.ofAdd (Pi.single i₀ (1 : ZMod p)) ∉ W := by
    by_contra hno
    push Not at hno
    apply hWtop
    intro a
    rw [ofAdd_eq_prod a]
    exact Subgroup.prod_mem W fun i _ => W.pow_mem (hno i) _
  obtain ⟨i₀, hi₀⟩ := hex
  set u := π (Multiplicative.ofAdd (Pi.single i₀ (1 : ZMod p))) with hu
  have hu1 : u ≠ 1 := fun h => hi₀ ((QuotientGroup.eq_one_iff _).1 h)
  have hQ : Nat.card (Multiplicative (Fin k → ZMod p) ⧸ W) = p := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have huo : orderOf u = p := by
    have h1 : u ^ Nat.card (Multiplicative (Fin k → ZMod p) ⧸ W) = 1 := pow_card_eq_one'
    rw [hQ] at h1
    exact orderOf_eq_prime h1 hu1
  have hgen : ∀ q : Multiplicative (Fin k → ZMod p) ⧸ W, ∃ n : ℕ, q = u ^ n := by
    intro q
    have htop : Subgroup.zpowers u = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, huo, hQ]
    have hq : q ∈ Subgroup.zpowers u := htop ▸ Subgroup.mem_top q
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    refine ⟨(z % (p : ℤ)).toNat, ?_⟩
    have hz : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (by exact_mod_cast hp.out.ne_zero)
    rw [← zpow_natCast, Int.toNat_of_nonneg hz, ← zpow_mod_orderOf u z, huo]
  choose n hn using fun i => hgen (π (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))))
  set e : Fin k → (Fin k → ZMod p) := fun i => Pi.single i (1 : ZMod p) with he
  have hw : ∀ i, Multiplicative.ofAdd (e i - n i • e i₀) ∈ W := by
    intro i
    have h1 : π (Multiplicative.ofAdd (e i)) = π (Multiplicative.ofAdd (n i • e i₀)) := by
      rw [hn i, ofAdd_nsmul, map_pow]
    have h2 := (QuotientGroup.eq (s := W)).1 h1
    have h3 : Multiplicative.ofAdd (e i - n i • e i₀) =
        ((Multiplicative.ofAdd (e i))⁻¹ * Multiplicative.ofAdd (n i • e i₀))⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_ofAdd, toAdd_inv, toAdd_mul]
      abel
    rw [h3]
    exact W.inv_mem h2
  set u0 : Multiplicative (Fin k → ZMod p) := Multiplicative.ofAdd (e i₀) with hu0
  have hu0p : u0 ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, hu0, toAdd_ofAdd]
    funext j
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hsplit : ∀ i, Multiplicative.ofAdd (e i) =
      Multiplicative.ofAdd (e i - n i • e i₀) * u0 ^ n i := by
    intro i
    apply Multiplicative.toAdd.injective
    simp only [hu0, toAdd_ofAdd, toAdd_mul, toAdd_pow]
    abel
  have hmain : ∀ a : Fin k → ZMod p, ∑ i, (n i : ZMod p) * a i = 0 →
      Multiplicative.ofAdd a ∈ W := by
    intro a ha
    have hcast : ((∑ i, n i * (a i).val : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sum, ← ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    have hdvd : p ∣ ∑ i, n i * (a i).val := (ZMod.natCast_eq_zero_iff _ _).1 hcast
    have hu0s : u0 ^ (∑ i, n i * (a i).val) = 1 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, hu0p, one_pow]
    have hprod : Multiplicative.ofAdd a =
        (∏ i, (Multiplicative.ofAdd (e i - n i • e i₀)) ^ (a i).val) *
          u0 ^ (∑ i, n i * (a i).val) := by
      rw [ofAdd_eq_prod a, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show (Pi.single i (1 : ZMod p) : Fin k → ZMod p) = e i from rfl, hsplit i, mul_pow,
        ← pow_mul]
    rw [hprod, hu0s, mul_one]
    exact Subgroup.prod_mem W fun i _ => W.pow_mem (hw i) _
  refine ⟨fun i => (n i : ZMod p), fun hf0 => hWtop fun a => hmain a ?_,
    fun a ha => hmemW a (hmain a ha)⟩
  have : (fun i => (n i : ZMod p)) = 0 := hf0
  simp only [funext_iff, Pi.zero_apply] at this
  simp [this]

end Hyperplanes

section VecProd

variable {G : Type*} [Group G] {p k : ℕ}

theorem list_prod_map_mul_of_commute {ι : Type*} (l : List ι) (f g : ι → G)
    (h : ∀ i ∈ l, ∀ j ∈ l, Commute (g i) (f j)) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih fun i hi j hj => h i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)]
    have hc : Commute (g i) (l.map f).prod := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact h i List.mem_cons_self j (List.mem_cons_of_mem _ hj)
    rw [mul_assoc, ← mul_assoc (g i), Commute.eq hc, mul_assoc, mul_assoc]

theorem pow_val_add_of_pow_eq_one [NeZero p] {x : G} (hx : x ^ p = 1) (m n : ZMod p) :
    x ^ (m + n).val = x ^ m.val * x ^ n.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (m.val + n.val) p, pow_add, pow_mul, hx, one_pow, one_mul]

@[expose] def vecProd (d : Fin k → G) (a : Fin k → ZMod p) : G :=
  ((List.finRange k).map fun i => d i ^ (a i).val).prod

theorem vecProd_add [NeZero p] {d : Fin k → G} (hcomm : ∀ i j, Commute (d i) (d j))
    (hpow : ∀ i, d i ^ p = 1) (a b : Fin k → ZMod p) :
    vecProd d (a + b) = vecProd d a * vecProd d b := by
  have hc : ∀ i ∈ List.finRange k, ∀ j ∈ List.finRange k,
      Commute (d i ^ (b i).val) (d j ^ (a j).val) := fun i _ j _ => (hcomm i j).pow_pow _ _
  unfold vecProd
  rw [← list_prod_map_mul_of_commute _ _ _ hc]
  simp only [Pi.add_apply, pow_val_add_of_pow_eq_one (hpow _)]

theorem vecProd_zero (d : Fin k → G) : vecProd d (0 : Fin k → ZMod p) = 1 := by
  unfold vecProd
  simp

@[expose] noncomputable def vecProdHom [NeZero p] (d : Fin k → G)
    (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ p = 1) :
    Multiplicative (Fin k → ZMod p) →* G where
  toFun a := vecProd d a.toAdd
  map_one' := vecProd_zero d
  map_mul' a b := vecProd_add hcomm hpow a.toAdd b.toAdd

theorem vecProdHom_apply [NeZero p] {d : Fin k → G} (hcomm : ∀ i j, Commute (d i) (d j))
    (hpow : ∀ i, d i ^ p = 1) (a : Fin k → ZMod p) :
    vecProdHom d hcomm hpow (Multiplicative.ofAdd a) = vecProd d a := rfl

end VecProd

theorem exists_conj_mem_of_full {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    [Finite P] (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {x : G}
    (hx : x ∈ P) (hxo : orderOf x = p) : ∃ g ∈ P, g⁻¹ * x * g ∈ Q := by
  let S0 : Sylow p P := Sylow.ofCard (Q.subgroupOf P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ])
  let x' : P := ⟨x, hx⟩
  have hx'o : orderOf x' = p := by rw [Subgroup.orderOf_mk]; exact hxo
  have hpg : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S0 S
  have hmem : x' ∈ ((g • S0 : Sylow p P) : Subgroup P) := by
    rw [hg]
    exact hS (Subgroup.mem_zpowers x')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  refine ⟨g, g.2, ?_⟩
  have : ((g⁻¹ * x' * g : P) : G) ∈ Q := hmem
  simpa using this

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer

theorem centralizer_eq_of_centOKP {n p chunks : ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W)
    (hc0 : 0 < chunks) (hc : rawChainOK n O S base W chunks = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {cC : ArrCert} {N : ℕ} (hps : ∀ q ∈ ps, q < n)
    (hcent : centOKP p n S base x rels gs ps cC N = true) :
    Subgroup.closure (permsA n gs) = Subgroup.centralizer {X} ⊓ Q.originalSubgroup ∧
      Nat.card (Subgroup.closure (permsA n gs)) = N := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  refine ⟨le_antisymm ?_ ?_, (enumOK_spec hps hC).2.1.trans hsize⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hC hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 (allLt_spec hcomm hk)
    · exact (siftA_iff_mem_originalSubgroup hA hc0 hc hrep).1 (allLt_spec hsift hk)
  · intro g hg
    have htail' : ptailOK n (rawLevels n S base) base x (powPA p n x) rels cC.pts.toList
        Q.baseCount 0 (idA n) = true := by
      rw [← hA.base_size]
      exact htail
    obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK hA (chainCheckFacts hc)
      (validSchreier_of_chainOK hA hc0 hc).1 hx (rep_powPA hx) (relsOKP_spec hrels) htail' hg
    exact enumOK_mem_of_mem hps hC hre he

theorem card_closure_inf_centralizer_le {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ q ∈ ps, q < n) (hc : enumOK n gs ps c = true) {w : Array ℕ}
    {W : Equiv.Perm (Fin n)} (hw : Rep n w W) :
    Nat.card ↥(Subgroup.closure (permsA n gs) ⊓
        Subgroup.centralizer ({W} : Set (Equiv.Perm (Fin n)))) ≤
      ((Finset.range c.pts.size).filter fun j =>
        CFSG.RankThree.Native.commA n c.pts[j]! w = true).card := by
  classical
  set X := Subgroup.closure (permsA n gs) ⊓ Subgroup.centralizer ({W} : Set (Equiv.Perm (Fin n)))
  set S := (Finset.range c.pts.size).filter fun j =>
    CFSG.RankThree.Native.commA n c.pts[j]! w = true
  have hsel : ∀ x : ↥X, ∃ j, j ∈ S ∧ Rep n c.pts[j]! (x : Equiv.Perm (Fin n)) := by
    intro x
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 x.2
    obtain ⟨j, hj, hrep⟩ := enumOK_exists_rep hps hc hx1
    refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩, hrep⟩
    exact (CFSG.RankThree.Native.commA_iff hrep hw).2
      (Subgroup.mem_centralizer_singleton_iff.1 hx2)
  choose j hjS hjrep using hsel
  have hinj : Function.Injective fun x : ↥X => (⟨j x, hjS x⟩ : ↥S) := by
    intro x y hxy
    have hxy' : j x = j y := congrArg Subtype.val hxy
    apply Subtype.ext
    have h1 := hjrep x
    rw [hxy'] at h1
    exact h1.unique (hjrep y)
  calc Nat.card ↥X ≤ Nat.card ↥S := Nat.card_le_card_of_injective _ hinj
    _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
