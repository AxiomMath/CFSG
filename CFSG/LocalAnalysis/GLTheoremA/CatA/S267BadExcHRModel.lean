module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHR
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13Gen
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelAGen)
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

section Diag


theorem rootDiagUnit_cartanChar_mem_torusGroup (c : Fin τ.rank → Kˣ) :
    rootDiagUnit τ (cartanChar c) ∈ torusGroup τ K := by
  rw [← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

theorem rootDiagUnit_mem_torusGroup_of_pow_eq_one {p : ℕ} (hp : p.Prime)
    (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ p = 1) :
    rootDiagUnit τ a ∈ torusGroup τ K := by
  classical
  set N := τ.cartan.det with hN
  set B := τ.cartan.adjugate with hBdef
  have hB : B * τ.cartan = N • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := Matrix.adjugate_mul _
  have hcop : IsCoprime N (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime p N.natAbs := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      hdet (Int.natCast_dvd.2 h)
    rw [Int.gcd, Int.natAbs_natCast]
    exact Nat.Coprime.symm h1
  obtain ⟨u, v, huv⟩ := hcop
  set s : Fin τ.rank → Kˣ := fun m => a m ^ u with hs
  have hsN : ∀ m, s m ^ N = a m := by
    intro m
    have h1 : a m ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact ha m
    calc s m ^ N = a m ^ (u * N) := by rw [hs, ← zpow_mul]
      _ = a m ^ (1 - v * p) := by rw [show u * N = 1 - v * p by linarith]
      _ = a m := by
        rw [zpow_sub, zpow_one, show v * (p : ℤ) = (p : ℤ) * v from mul_comm _ _, zpow_mul, h1,
          one_zpow, inv_one, mul_one]
  set c : Fin τ.rank → Kˣ := fun j => ∏ m, s m ^ B m j with hcdef
  have hc : cartanChar c = a := by
    funext l
    have h1 : ∀ j, (∏ m, s m ^ B m j) ^ τ.cartan j l = ∏ m, s m ^ (B m j * τ.cartan j l) := by
      intro j
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun m _ => (zpow_mul _ _ _).symm
    simp only [cartanChar, hcdef, h1]
    rw [Finset.prod_comm]
    have h2 : ∀ m, ∏ j, s m ^ (B m j * τ.cartan j l) =
        s m ^ (N • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) m l := fun m => by
      rw [Finset.prod_zpow_eq_zpow_sum, ← hB, Matrix.mul_apply]
    simp only [h2, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.prod_eq_single l (fun m _ hm => by simp [hm])
      (fun h => absurd (Finset.mem_univ l) h)]
    simp [hsN l]
  rw [← hc]
  exact rootDiagUnit_cartanChar_mem_torusGroup c

theorem rootDiagUnit_mulSingle_mem_torusGroup {n : Fin τ.rank → ℤ}
    (hn : ∀ l, ∑ j, n j * τ.cartan j l = if l = highNode τ then 1 else 0) (c : Kˣ) :
    rootDiagUnit τ (Pi.mulSingle (highNode τ) c) ∈ torusGroup τ K := by
  have hc : cartanChar (fun j => c ^ n j) = Pi.mulSingle (highNode τ) c := by
    funext l
    simp only [cartanChar, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum, hn]
    by_cases hl : l = highNode τ
    · rw [if_pos hl, zpow_one, hl, Pi.mulSingle_eq_same]
    · rw [if_neg hl, zpow_zero, Pi.mulSingle_eq_of_ne hl]
  rw [← hc]
  exact rootDiagUnit_cartanChar_mem_torusGroup _

end Diag

section Torus

variable {p : ℕ}

@[expose] def zetaPow (ζ : Kˣ) (x : Fin τ.rank → ZMod p) : Fin τ.rank → Kˣ :=
  fun i => ζ ^ (x i).val

theorem zetaPow_add [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1) (x y : Fin τ.rank → ZMod p) :
    zetaPow ζ (x + y) = zetaPow ζ x * zetaPow ζ y := by
  funext i
  simp only [zetaPow, Pi.add_apply, Pi.mul_apply, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hζ).symm

theorem zetaPow_zero (ζ : Kˣ) : zetaPow (p := p) (τ := τ) ζ 0 = 1 := by
  funext i
  simp only [zetaPow, Pi.zero_apply, ZMod.val_zero, pow_zero, Pi.one_apply]

theorem zetaPow_pow_eq_one {ζ : Kˣ} (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    zetaPow ζ x i ^ p = 1 := by
  change (ζ ^ (x i).val) ^ p = 1
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem zetaPow_injective [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) :
    Function.Injective (zetaPow (τ := τ) ζ : (Fin τ.rank → ZMod p) → Fin τ.rank → Kˣ) := by
  intro x y h
  funext i
  have hi := congrFun h i
  simp only [zetaPow] at hi
  have hx : (x i).val < orderOf ζ := by rw [hζ]; exact ZMod.val_lt (x i)
  have hy : (y i).val < orderOf ζ := by rw [hζ]; exact ZMod.val_lt (y i)
  exact ZMod.val_injective _ (pow_injOn_Iio_orderOf hx hy hi)

theorem rootDiagUnit_zetaPow_mem (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p) :
    rootDiagUnit τ (zetaPow ζ x) ∈ adjointGroup τ K :=
  CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
    (rootDiagUnit_mem_torusGroup_of_pow_eq_one hp hdet (zetaPow_pow_eq_one hζ _))

@[expose] noncomputable def hrTorusHom [NeZero p] (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) : Multiplicative (Fin τ.rank → ZMod p) →* ↥(adjointGroup τ K) where
  toFun x := ⟨rootDiagUnit τ (zetaPow ζ (Multiplicative.toAdd x)),
    rootDiagUnit_zetaPow_mem hp hdet hζ _⟩
  map_one' := Subtype.ext (by
    change rootDiagUnit τ (zetaPow ζ 0) = 1
    rw [zetaPow_zero, rootDiagUnit_one])
  map_mul' x y := Subtype.ext (by
    change rootDiagUnit τ (zetaPow ζ (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [zetaPow_add hζ, rootDiagUnit_mul]
    rfl)

theorem coe_hrTorusHom [NeZero p] (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (x : Multiplicative (Fin τ.rank → ZMod p)) :
    ((hrTorusHom hp hdet hζ x : ↥(adjointGroup τ K)) : ModGL τ K) =
      rootDiagUnit τ (zetaPow ζ (Multiplicative.toAdd x)) :=
  rfl

theorem hrTorusHom_injective [NeZero p] (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det)
    {ζ : Kˣ} (hζ : orderOf ζ = p) :
    Function.Injective (hrTorusHom (K := K) (τ := τ) hp hdet (hζ ▸ pow_orderOf_eq_one ζ)) := by
  intro x y h
  have h' := congrArg (fun g : ↥(adjointGroup τ K) => (g : ModGL τ K)) h
  simp only [coe_hrTorusHom] at h'
  exact zetaPow_injective hζ (rootDiagUnit_injective h')

end Torus

section Coord

variable {p : ℕ}

@[expose] def singleHom (j : Fin τ.rank) :
    Multiplicative (ZMod p) →* Multiplicative (Fin τ.rank → ZMod p) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ => ZMod p) j)

@[expose] def pairHom (j k : Fin τ.rank) :
    Multiplicative (ZMod p × ZMod p) →* Multiplicative (Fin τ.rank → ZMod p) :=
  AddMonoidHom.toMultiplicative
    ((AddMonoidHom.single (fun _ => ZMod p) j).comp (AddMonoidHom.fst _ _) +
      (AddMonoidHom.single (fun _ => ZMod p) k).comp (AddMonoidHom.snd _ _))

theorem toAdd_singleHom (j : Fin τ.rank) (s : Multiplicative (ZMod p)) :
    Multiplicative.toAdd (singleHom j s) = Pi.single j (Multiplicative.toAdd s) :=
  rfl

theorem toAdd_pairHom (j k : Fin τ.rank) (s : Multiplicative (ZMod p × ZMod p)) :
    Multiplicative.toAdd (pairHom j k s) =
      Pi.single j (Multiplicative.toAdd s).1 + Pi.single k (Multiplicative.toAdd s).2 :=
  rfl

theorem singleHom_injective (j : Fin τ.rank) : Function.Injective (singleHom (p := p) j) :=
  fun s t h => by
    have h1 := congrFun (congrArg Multiplicative.toAdd h) j
    rw [toAdd_singleHom, toAdd_singleHom, Pi.single_eq_same, Pi.single_eq_same] at h1
    exact h1

theorem pairHom_injective {j k : Fin τ.rank} (hjk : j ≠ k) :
    Function.Injective (pairHom (p := p) j k) := fun s t h => by
  have h1 := congrFun (congrArg Multiplicative.toAdd h) j
  have h2 := congrFun (congrArg Multiplicative.toAdd h) k
  simp only [toAdd_pairHom, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk,
    Pi.single_eq_of_ne hjk.symm, add_zero, zero_add] at h1 h2
  exact Multiplicative.toAdd.injective (Prod.ext h1 h2)

theorem pairHom_singleHom (j k : Fin τ.rank) (s : Multiplicative (ZMod p)) :
    pairHom j k (Multiplicative.ofAdd (Multiplicative.toAdd s, 0)) = singleHom j s := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pairHom, toAdd_singleHom]
  simp

theorem zetaPow_single (ζ : Kˣ) (j : Fin τ.rank) (s : ZMod p) :
    zetaPow ζ (Pi.single j s) = Pi.mulSingle j (ζ ^ s.val) := by
  funext i
  by_cases hi : i = j
  · subst hi
    rw [zetaPow, Pi.single_eq_same, Pi.mulSingle_eq_same]
  · rw [zetaPow, Pi.single_eq_of_ne hi, ZMod.val_zero, pow_zero, Pi.mulSingle_eq_of_ne hi]

theorem card_multiplicative_fun [NeZero p] :
    Nat.card (Multiplicative (Fin τ.rank → ZMod p)) = p ^ τ.rank := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_multiplicative_zmod [NeZero p] : Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_multiplicative_prod [NeZero p] :
    Nat.card (Multiplicative (ZMod p × ZMod p)) = p ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, sq]

theorem card_range_of_injective' {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) : Nat.card f.range = Nat.card G := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hf, Subgroup.card_top]

end Coord

theorem rootChar_mul (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_single (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  unfold rootChar
  rw [Finset.prod_eq_single i (fun m _ hm => by rw [Pi.single_eq_of_ne hm, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

section Witness


theorem cartan_self_eq_two (τ : Tag) (i : Fin τ.rank) : τ.cartan i i = 2 := by
  cases τ <;> revert i <;> decide

theorem rootDiagUnit_pow_hr (b : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ b ^ n = rootDiagUnit τ (b ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]

theorem torusElt_mem_rootSpan_hr {S : Set (Fin τ.rank → ℤ)} {i : Fin τ.rank}
    (h1 : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ S) (h2 : (-Pi.single i 1 : Fin τ.rank → ℤ) ∈ S)
    (t : Kˣ) : torusElt τ K i t ∈ rootSpan τ K S := by
  have hx : ∀ c, xUnit τ K i c ∈ rootSpan τ K S := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan h1 c
  have hy : ∀ c, yUnit τ K i c ∈ rootSpan τ K S := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan h2 c
  have hw : ∀ s : Kˣ, weylElt τ K i s ∈ rootSpan τ K S := fun s => by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  exact mul_mem (hw t) (hw (-1))

theorem dvd_card_rootSpan {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = p)
    {S : Set (Fin τ.rank → ℤ)} {i : Fin τ.rank} (h1 : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ S)
    (h2 : (-Pi.single i 1 : Fin τ.rank → ℤ) ∈ S) : p ∣ Nat.card (rootSpan τ K S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem := torusElt_mem_rootSpan_hr (K := K) h1 h2 ζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hord : orderOf (torusElt τ K i ζ) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [torusElt_eq_rootDiagUnit, rootDiagUnit_pow_hr, ← rootDiagUnit_one (τ := τ) (K := K)]
      congr 1
      funext j
      rw [Pi.pow_apply, Pi.one_apply, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζp, one_zpow]
    · intro h1'
      rw [torusElt_eq_rootDiagUnit, ← rootDiagUnit_one (τ := τ) (K := K)] at h1'
      have h3 := congrFun (rootDiagUnit_injective h1') i
      rw [Pi.one_apply, cartan_self_eq_two] at h3
      have h4 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by exact_mod_cast h3)
      rw [hζ] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard _ hmem

theorem mem_toralCentralizer_of_commute {a : Fin τ.rank → Kˣ} {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K) (h : g * rootDiagUnit τ a = rootDiagUnit τ a * g) :
    g ∈ toralCentralizer τ K a :=
  Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 h⟩

theorem commute_of_mem_toralCentralizer {a : Fin τ.rank → Kˣ} {g : ModGL τ K}
    (hg : g ∈ toralCentralizer τ K a) : g * rootDiagUnit τ a = rootDiagUnit τ a * g :=
  Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2

theorem modelAGen_hr_gen [Finite K] {p : ℕ} (hK2 : ringChar K ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    {n : Fin τ.rank → ℤ} (hn : ∀ l, ∑ j, n j * τ.cartan j l = if l = highNode τ then 1 else 0)
    (hJq : CFSG.Open.IsQuasisimple ↥(rootSpan τ K (perpRoots τ)))
    {k' i₂ : Fin τ.rank} (hk' : k' ≠ highNode τ) (S₂ : Set (Fin τ.rank → ℤ))
    (hS₂ : ∀ γ ∈ S₂, IsRoot τ γ ∧ γ (highNode τ) = 0 ∧ γ k' = 0)
    (he₂ : (Pi.single i₂ 1 : Fin τ.rank → ℤ) ∈ S₂ ∧ (-Pi.single i₂ 1 : Fin τ.rank → ℤ) ∈ S₂)
    (hnorm : toralCentralizer τ K (Pi.mulSingle (highNode τ) ζ) ⊓
        toralCentralizer τ K (Pi.mulSingle k' ζ) ≤
      Subgroup.normalizer (rootSpan τ K S₂ : Set (ModGL τ K)))
    (hJ₂q : CFSG.Open.IsQuasisimple ↥(rootSpan τ K S₂)) :
    ModelAGen p τ.rank ↥(adjointGroup τ K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  set j₀ := highNode τ with hj₀
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hζ1 : ζ ≠ 1 := fun h => hζ2 (by rw [h, one_pow])
  set E := hrTorusHom (K := K) (τ := τ) hp hdet hζp with hE
  have hEinj : Function.Injective E := hrTorusHom_injective hp hdet hζ
  have hEsingle : ∀ s, ((E (singleHom j₀ s) : ↥(adjointGroup τ K)) : ModGL τ K) =
      rootDiagUnit τ (Pi.mulSingle j₀ (ζ ^ (Multiplicative.toAdd s).val)) := fun s => by
    rw [hE, coe_hrTorusHom, toAdd_singleHom, zetaPow_single]
  have hEpair : ∀ s, ((E (pairHom j₀ k' s) : ↥(adjointGroup τ K)) : ModGL τ K) =
      rootDiagUnit τ (Pi.mulSingle j₀ (ζ ^ (Multiplicative.toAdd s).1.val) *
        Pi.mulSingle k' (ζ ^ (Multiplicative.toAdd s).2.val)) := fun s => by
    rw [hE, coe_hrTorusHom, toAdd_pairHom, zetaPow_add hζp, zetaPow_single, zetaPow_single]
  have hEtorus : ∀ x, ((E x : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K := fun x =>
    rootDiagUnit_mem_torusGroup_of_pow_eq_one hp hdet (zetaPow_pow_eq_one hζp _)
  set dζ : ↥(adjointGroup τ K) := E (singleHom j₀ (Multiplicative.ofAdd 1)) with hdζ
  have hdζc : (dζ : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle j₀ ζ) := by
    rw [hdζ, hEsingle, toAdd_ofAdd, ZMod.val_one, pow_one]
  set dζ₁ : ↥(adjointGroup τ K) := E (pairHom j₀ k' (Multiplicative.ofAdd (1, 0))) with hdζ₁
  have hdζ₁c : (dζ₁ : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle j₀ ζ) := by
    rw [hdζ₁, hEpair, toAdd_ofAdd, ZMod.val_one, pow_one, ZMod.val_zero, pow_zero,
      Pi.mulSingle_one, mul_one]
  set d₃ : ↥(adjointGroup τ K) := E (pairHom j₀ k' (Multiplicative.ofAdd (0, 1))) with hd₃
  have hd₃c : (d₃ : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle k' ζ) := by
    rw [hd₃, hEpair, toAdd_ofAdd, ZMod.val_one, pow_one, ZMod.val_zero, pow_zero,
      Pi.mulSingle_one, one_mul]
  set A : Subgroup ↥(adjointGroup τ K) := E.range with hA
  set A₁ : Subgroup ↥(adjointGroup τ K) := (E.comp (singleHom j₀)).range with hA₁
  set A₁₂ : Subgroup ↥(adjointGroup τ K) := (E.comp (pairHom j₀ k')).range with hA₁₂
  set J : Subgroup ↥(adjointGroup τ K) :=
    (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) with hJ
  set J₂ : Subgroup ↥(adjointGroup τ K) :=
    (rootSpan τ K S₂).subgroupOf (adjointGroup τ K) with hJ₂
  have hdζA₁ : dζ ∈ A₁ := ⟨_, rfl⟩
  have hdζ₁A₁₂ : dζ₁ ∈ A₁₂ := ⟨_, rfl⟩
  have hd₃A₁₂ : d₃ ∈ A₁₂ := ⟨_, rfl⟩
  have htmem : rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) ∈ adjointGroup τ K :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (rootDiagUnit_mulSingle_mem_torusGroup hn _)
  set t : ↥(adjointGroup τ K) := ⟨_, htmem⟩ with ht
  have hker₃perp : S₂ ⊆ perpRoots τ := fun γ hγ => ⟨(hS₂ γ hγ).1, (hS₂ γ hγ).2.1⟩
  have hpJ : p ∣ Nat.card (rootSpan τ K (perpRoots τ)) :=
    dvd_card_rootSpan hp hp2 hζ (hker₃perp he₂.1) (hker₃perp he₂.2)
  have hpJ₂ : p ∣ Nat.card (rootSpan τ K S₂) :=
    dvd_card_rootSpan hp hp2 hζ he₂.1 he₂.2
  have hJcomp : GLAPComponent p (Subgroup.centralizer ((A₁ : Subgroup _) : Set ↥(adjointGroup τ K)))
      J := by
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.glaPComponent_subgroupOf _ hp _
      (rootSpan_le_adjointGroup K _) ?_ ?_ hJq hpJ
    · rintro l hl _ ⟨s, rfl⟩
      have hc := commute_of_mem_toralCentralizer
        (rootSpan_perpRoots_le_toralCentralizer (ζ ^ (Multiplicative.toAdd s).val) hl)
      rw [MonoidHom.comp_apply, hEsingle]
      exact hc
    · intro g hg hcomm l hl
      have hgc := hcomm dζ hdζA₁
      rw [hdζc] at hgc
      exact (Subgroup.mem_normalizer_iff.1 (toralCentralizer_mulSingle_le_normalizer hζ1 hζ2 hk
        (mem_toralCentralizer_of_commute hg hgc)) l).1 hl
  have hJX : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).symm hJq
  have hpJX : p ∣ Nat.card ↥J := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).toEquiv]
    exact hpJ
  have hAN : A ≤ Subgroup.normalizer (J : Set ↥(adjointGroup τ K)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hN := Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (S := perpRoots τ) (K := K) (fun _ hα => hα.1)
        (hEtorus x)) (h : ModGL τ K)
    simp only [hJ, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN
  refine ⟨A, A₁, A₁₂, J, t, ?_, ?_, ?_, ?_, ?_, ?_, hJcomp, hAN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      change (x : ↥(adjointGroup τ K)) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        funext i
        rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply, ZMod.natCast_self, zero_mul]
      rw [this, map_one]
  · rw [hA, card_range_of_injective' hEinj, card_multiplicative_fun]
  · rintro _ ⟨s, rfl⟩
    exact ⟨Multiplicative.ofAdd ((Multiplicative.toAdd s, 0) : ZMod p × ZMod p), by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, pairHom_singleHom]⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · have hinj : Function.Injective (E.comp (singleHom (p := p) j₀)) := by
      rw [MonoidHom.coe_comp]; exact hEinj.comp (singleHom_injective j₀)
    rw [hA₁, card_range_of_injective' hinj, card_multiplicative_zmod]
  · have hinj : Function.Injective (E.comp (pairHom (p := p) j₀ k')) := by
      rw [MonoidHom.coe_comp]; exact hEinj.comp (pairHom_injective hk'.symm)
    rw [hA₁₂, card_range_of_injective' hinj, card_multiplicative_prod]
  ·
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨-, hcomm⟩ := hx
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp hJX
      hpJX (MulAut.conj (E x)).toMonoidHom fun j hj => by
        have h1 := hcomm (Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers (E x)))
        have h2 := (GLAPPrimeCoreOf p J).inv_mem h1
        rw [commutatorElement_inv, commutatorElement_def] at h2
        exact h2
    have hcoord : ∀ i, i ≠ j₀ → Multiplicative.toAdd x i = 0 := by
      intro i hi
      have hjmem : xUnit τ K i 1 ∈ adjointGroup τ K := xUnit_mem_adjointGroup i 1
      have hjJ : (⟨xUnit τ K i 1, hjmem⟩ : ↥(adjointGroup τ K)) ∈ J := by
        rw [hJ, Subgroup.mem_subgroupOf]
        change xUnit τ K i 1 ∈ rootSpan τ K (perpRoots τ)
        rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (S := perpRoots τ) (α := Pi.single i 1)
          ⟨IsRoot.basis i, Pi.single_eq_of_ne' hi 1⟩ 1
      have h := congrArg (fun g : ↥(adjointGroup τ K) => (g : ModGL τ K)) (hfix _ hjJ)
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [coe_hrTorusHom, ← pinnedX_single, rootDiagUnit_conj_pinnedX _ (IsRoot.basis i),
        mul_one] at h
      have h' := pinnedX_injective (R := K) (τ := τ) (Pi.single i 1) h
      rw [rootChar_single, zetaPow] at h'
      have h'' : ζ ^ (Multiplicative.toAdd x i).val = 1 := Units.ext h'
      have hdvd := orderOf_dvd_of_pow_eq_one h''
      rw [hζ] at hdvd
      exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
    refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd x j₀), ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_singleHom, toAdd_ofAdd]
    funext i
    by_cases hi : i = j₀
    · subst hi
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hi, hcoord i hi]
  ·
    have hJ₂comp : GLAPComponent p (Subgroup.centralizer ((A₁₂ : Subgroup _) :
        Set ↥(adjointGroup τ K))) J₂ := by
      refine CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.glaPComponent_subgroupOf _ hp _
        (rootSpan_le_adjointGroup K _) ?_ ?_ hJ₂q hpJ₂
      · rintro l hl _ ⟨s, rfl⟩
        have hsub : S₂ ⊆ rootCharKernel
            (Pi.mulSingle j₀ (ζ ^ (Multiplicative.toAdd s).1.val) *
              Pi.mulSingle k' (ζ ^ (Multiplicative.toAdd s).2.val)) := fun γ hγ => by
          obtain ⟨hr, h0, h1⟩ := hS₂ γ hγ
          exact ⟨hr, by rw [rootChar_mul, rootChar_mulSingle, rootChar_mulSingle, h0, h1,
            zpow_zero, zpow_zero, mul_one]⟩
        have hc := Subgroup.mem_centralizer_singleton_iff.1
          (rootSpan_le_centralizer _ hsub hl)
        rw [MonoidHom.comp_apply, hEpair]
        exact hc
      · intro g hg hcomm l hl
        have hgc := hcomm d₃ hd₃A₁₂
        have hgc₁ := hcomm dζ₁ hdζ₁A₁₂
        rw [hd₃c] at hgc
        rw [hdζ₁c] at hgc₁
        exact (Subgroup.mem_normalizer_iff.1 (hnorm ⟨mem_toralCentralizer_of_commute hg hgc₁,
          mem_toralCentralizer_of_commute hg hgc⟩) l).1 hl
    have hJ₂J : J₂ ≤ J := fun x hx =>
      Subgroup.mem_subgroupOf.2 (rootSpan_mono hker₃perp (Subgroup.mem_subgroupOf.1 hx))
    have hJ₂c : GLAPComponent p (J ⊓ Subgroup.centralizer ((A₁₂ : Subgroup _) :
        Set ↥(adjointGroup τ K))) J₂ :=
      glaPComponent_of_le hp hJ₂comp (le_inf hJ₂J hJ₂comp.1) inf_le_right
    intro hbot
    have hle : J₂ ≤ GLAPLayer p (J ⊓ Subgroup.centralizer ((A₁₂ : Subgroup _) :
        Set ↥(adjointGroup τ K))) := le_sSup hJ₂c
    rw [hbot, le_bot_iff] at hle
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ₂c hle
  ·
    intro h1
    have h := congrArg (fun g : ↥(adjointGroup τ K) => (g : ModGL τ K)) h1
    change rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) = 1 at h
    rw [← rootDiagUnit_one (τ := τ) (K := K)] at h
    have h' := congrFun (rootDiagUnit_injective h) j₀
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h'
    exact hK2 ((neg_one_eq_one_iff (R := K)).1 (by simpa using congrArg Units.val h'))
  ·
    apply Subtype.ext
    change rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) ^ 2 = 1
    rw [rootDiagUnit_pow_hr, ← rootDiagUnit_one (τ := τ) (K := K)]
    congr 1
    rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  ·
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (j : ModGL τ K) * rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) =
      rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) * (j : ModGL τ K)
    exact commute_of_mem_toralCentralizer
      (rootSpan_perpRoots_le_toralCentralizer (-1 : Kˣ) (Subgroup.mem_subgroupOf.1 hj))
  ·
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show ((E x : ↥(adjointGroup τ K)) : ModGL τ K) * rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) =
      rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) * ((E x : ↥(adjointGroup τ K)) : ModGL τ K)
    rw [coe_hrTorusHom, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem modelAGen_hr [Finite K] {p : ℕ} (hK2 : ringChar K ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    {n : Fin τ.rank → ℤ} (hn : ∀ l, ∑ j, n j * τ.cartan j l = if l = highNode τ then 1 else 0)
    (hJq : CFSG.Open.IsQuasisimple ↥(rootSpan τ K (perpRoots τ)))
    {k' i₂ : Fin τ.rank} (hk' : k' ≠ highNode τ) (hi₂ : i₂ ≠ highNode τ) (hi₂' : i₂ ≠ k')
    (hker : ∀ γ ∈ rootCharKernel (Pi.mulSingle (highNode τ) ζ * Pi.mulSingle k' ζ),
      γ (highNode τ) = 0 ∧ γ k' = 0)
    (hJ₂q : CFSG.Open.IsQuasisimple
      ↥(rootSpan τ K (rootCharKernel (Pi.mulSingle (highNode τ) ζ * Pi.mulSingle k' ζ)))) :
    ModelAGen p τ.rank ↥(adjointGroup τ K) := by
  refine modelAGen_hr_gen hK2 hp hp2 hdet hζ hk hn hJq hk' _ (fun γ hγ => ⟨hγ.1, hker γ hγ⟩)
    ⟨⟨IsRoot.basis i₂, ?_⟩, ⟨IsRoot.neg (IsRoot.basis i₂), ?_⟩⟩ ?_ hJ₂q
  · rw [rootChar_mul, rootChar_mulSingle, rootChar_mulSingle, Pi.single_eq_of_ne' hi₂ 1,
      Pi.single_eq_of_ne' hi₂' 1, zpow_zero, mul_one]
  · rw [rootChar_mul, rootChar_mulSingle, rootChar_mulSingle, Pi.neg_apply, Pi.neg_apply,
      Pi.single_eq_of_ne' hi₂ 1, Pi.single_eq_of_ne' hi₂' 1, neg_zero, zpow_zero, mul_one]
  · rintro g ⟨h1, h2⟩
    have c1 := commute_of_mem_toralCentralizer h1
    have c2 := commute_of_mem_toralCentralizer h2
    refine toralCentralizer_le_normalizer_rootSpan_rootCharKernel _
      (mem_toralCentralizer_of_commute (Subgroup.mem_inf.1 h1).1 ?_)
    rw [rootDiagUnit_mul]
    calc g * (rootDiagUnit τ (Pi.mulSingle (highNode τ) ζ) * rootDiagUnit τ (Pi.mulSingle k' ζ))
        = (g * rootDiagUnit τ (Pi.mulSingle (highNode τ) ζ)) *
            rootDiagUnit τ (Pi.mulSingle k' ζ) := by rw [mul_assoc]
      _ = rootDiagUnit τ (Pi.mulSingle (highNode τ) ζ) *
            (g * rootDiagUnit τ (Pi.mulSingle k' ζ)) := by rw [c1, mul_assoc]
      _ = _ := by rw [c2, mul_assoc]

end Witness

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
