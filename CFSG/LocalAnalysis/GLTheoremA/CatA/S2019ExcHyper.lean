module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcBinary
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.QuasithinUnique.Setup.X1

section Index

variable {M : Type*} [Group M] [Finite M]

private theorem eq_of_le_of_ne_of_card {q : ℕ} (hq : q.Prime) {N S A : Subgroup M} (hNS : N ≤ S)
    (hSA : S ≤ A) (hne : N ≠ S) (hN : Nat.card A = q * Nat.card N) : S = A := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hNS
  obtain ⟨l, hl⟩ := Subgroup.card_dvd_of_le hSA
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hkl : q = k * l := by
    have : Nat.card N * q = Nat.card N * (k * l) := by rw [mul_comm, ← hN, hl, hk, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [hkl] at hq
  rcases Nat.prime_mul_iff.1 hq with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Subgroup.eq_of_le_of_card_ge hSA (by rw [hl, mul_one])
  · exact absurd (Subgroup.eq_of_le_of_card_ge hNS (by rw [hk, mul_one])) hne

private theorem sup_eq_of_card {q : ℕ} (hq : q.Prime) {N N' A : Subgroup M} (hNA : N ≤ A)
    (hN'A : N' ≤ A) (hN : Nat.card A = q * Nat.card N) (hN' : Nat.card A = q * Nat.card N')
    (hne : N ≠ N') : N ⊔ N' = A := by
  refine eq_of_le_of_ne_of_card hq le_sup_left (sup_le hNA hN'A) (fun h => hne ?_) hN
  have hle : N' ≤ N := le_sup_right.trans h.symm.le
  have hcard : Nat.card N = Nat.card N' := Nat.eq_of_mul_eq_mul_left hq.pos (hN.symm.trans hN')
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

private theorem sup_zpowers_eq {q : ℕ} (hq : q.Prime) {N A : Subgroup M} (hNA : N ≤ A)
    (hN : Nat.card A = q * Nat.card N) {a : M} (ha : a ∈ A) (haN : a ∉ N) :
    N ⊔ Subgroup.zpowers a = A :=
  eq_of_le_of_ne_of_card hq le_sup_left (sup_le hNA ((Subgroup.zpowers_le).2 ha))
    (fun h => haN (by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))) hN

private theorem exists_mem_not_mem {q : ℕ} (hq : q.Prime) {N A : Subgroup M}
    (hN : Nat.card A = q * Nat.card N) : ∃ a ∈ A, a ∉ N := by
  by_contra h
  push Not at h
  have hle := Subgroup.card_le_of_le (show A ≤ N from fun a ha => h a ha)
  have hpos : 0 < Nat.card N := Nat.card_pos
  rw [hN] at hle
  nlinarith [hq.two_le]

private theorem odd_card_of_le {q : ℕ} [Fact q.Prime] (hq : Odd q) {A N : Subgroup M}
    (hAq : ∀ a ∈ A, a ^ q = 1) (hNA : N ≤ A) : Odd (Nat.card N) := by
  have hp : IsPGroup q N := fun n => ⟨1, Subtype.ext (by simpa using hAq _ (hNA n.2))⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk]
  exact hq.pow

private theorem mem_map_conj {g x : M} {N : Subgroup M} :
    x ∈ N.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ N := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa [mul_assoc] using hn
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

private theorem conj_mem_iff {A : Subgroup M} {y : M} (hy : y ∈ Subgroup.normalizer (A : Set M))
    (x : M) :
    y⁻¹ * x * y ∈ A ↔ x ∈ A := by
  have := Subgroup.mem_normalizer_iff.1 (inv_mem hy) x
  rw [inv_inv] at this
  exact this.symm

private theorem exists_iterate_fixed {G : Type*} [CommGroup G] [Finite G] {q : ℕ}
    [hq : Fact q.Prime] {N : Subgroup G} (hN : Nat.card G = q * Nat.card N) (σ : G →* G)
    (hσ : Function.Injective σ) (hσN : ∀ n ∈ N, σ n ∈ N) : ∃ a : G, a ≠ 1 ∧ σ^[q - 1] a = a := by
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hQ : Nat.card (G ⧸ N) = q := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hN] at h
    exact (Nat.eq_of_mul_eq_mul_right hNpos h).symm
  haveI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hQ
  obtain ⟨m, hm⟩ := (QuotientGroup.map N N σ (fun n hn => hσN n hn)).map_cyclic
  have hmk : ∀ x : G, ((σ x : G) : G ⧸ N) = (x : G ⧸ N) ^ m := fun x =>
    (QuotientGroup.map_mk N N σ (fun n hn => hσN n hn) x).symm.trans (hm x)
  have hpowq : ∀ x : G ⧸ N, x ^ q = 1 := fun x => by rw [← hQ]; exact pow_card_eq_one'
  have hiter : ∀ (k : ℕ) (b : G), ((σ^[k] b : G) : G ⧸ N) = (b : G ⧸ N) ^ (m ^ k) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih => intro b; rw [Function.iterate_succ_apply', hmk, ih, ← zpow_mul, pow_succ]
  by_cases hqm : (q : ℤ) ∣ m
  · exfalso
    obtain ⟨c, rfl⟩ := hqm
    have hall : ∀ b, σ b ∈ N := fun b => by
      rw [← QuotientGroup.eq_one_iff, hmk, zpow_mul, zpow_natCast, hpowq, one_zpow]
    have hle : Nat.card G ≤ Nat.card N :=
      Nat.card_le_card_of_injective (fun b => (⟨σ b, hall b⟩ : N))
        fun a b h => hσ (congrArg Subtype.val h)
    rw [hN] at hle
    nlinarith [hq.out.two_le]
  · have hcop : IsCoprime m q :=
      ((Nat.prime_iff_prime_int.1 hq.out).coprime_iff_not_dvd.2 hqm).symm
    obtain ⟨c, hc⟩ := (Int.ModEq.pow_card_sub_one_eq_one hq.out hcop).symm.dvd
    have hfix : ∀ b : G, σ^[q - 1] b * b⁻¹ ∈ N := by
      intro b
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hiter,
        show m ^ (q - 1) = 1 + (q : ℤ) * c by linarith, zpow_add, zpow_one, zpow_mul,
        zpow_natCast, hpowq, one_zpow, mul_one, mul_inv_cancel]
    let ψ : G →* G :=
      { toFun := fun b => σ^[q - 1] b * b⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [iterate_map_mul, mul_inv]
          exact mul_mul_mul_comm _ _ _ _ }
    by_contra hcon
    push Not at hcon
    have hψ : Function.Injective ψ := (injective_iff_map_eq_one ψ).2 fun a ha => by
      by_contra ha1
      exact hcon a ha1 (mul_inv_eq_one.1 ha)
    have hle : Nat.card G ≤ Nat.card N :=
      Nat.card_le_card_of_injective (fun b => (⟨ψ b, hfix b⟩ : N))
        fun a b h => hψ (congrArg Subtype.val h)
    rw [hN] at hle
    nlinarith [hq.out.two_le]

private theorem exists_comm_pow_sub_one {q : ℕ} [Fact q.Prime] {A N : Subgroup M}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hNA : N ≤ A) (hN : Nat.card A = q * Nat.card N)
    {y : M} (hy : y ∈ Subgroup.normalizer (A : Set M)) (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N) :
    ∃ a ∈ A, a ≠ 1 ∧ y ^ (q - 1) * a = a * y ^ (q - 1) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hA a a.2 b b.2) }
  let σ : A →* A :=
    { toFun := fun a => ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy a).1 a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hσa : ∀ a : A, ((σ a : A) : M) = y * a * y⁻¹ := fun a => rfl
  have hσ : ∀ (k : ℕ) (a : A), ((σ^[k] a : A) : M) = y ^ k * a * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih => intro a; rw [Function.iterate_succ_apply', hσa, ih, pow_succ']; group
  have hσinj : Function.Injective σ := fun a b h => by
    have h' := congrArg Subtype.val h
    rw [hσa, hσa] at h'
    exact Subtype.ext (by simpa using h')
  have hN' : Nat.card A = q * Nat.card (N.subgroupOf A) := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv]
  obtain ⟨a, ha1, ha⟩ := exists_iterate_fixed hN' σ hσinj fun n hn => hyN _ hn
  refine ⟨a, a.2, fun h => ha1 (Subtype.ext h), ?_⟩
  have h' := congrArg Subtype.val ha
  rw [hσ] at h'
  calc y ^ (q - 1) * a = (y ^ (q - 1) * a * (y ^ (q - 1))⁻¹) * y ^ (q - 1) := by group
    _ = a * y ^ (q - 1) := by rw [h']

end Index

section Hyper

variable {W : Type} [CommGroup W] [Finite W] [Finite (MulAut W)]

@[expose] noncomputable def avgW (H : Subgroup (MulAut W)) : W →* W :=
  letI := Fintype.ofFinite H
  { toFun := fun w => ∏ h : H, (h : MulAut W) w
    map_one' := by simp
    map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }

theorem avgW_apply (H : Subgroup (MulAut W)) (w : W) :
    letI := Fintype.ofFinite H
    avgW H w = ∏ h : H, (h : MulAut W) w := rfl

variable {H N N' A : Subgroup (MulAut W)}

theorem apply_avgW {g : MulAut W} (hg : g ∈ H) (w : W) : g (avgW H w) = avgW H w := by
  letI := Fintype.ofFinite H
  rw [avgW_apply, map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : H)) _ _ fun b => rfl

theorem avgW_apply_apply {g : MulAut W} (hg : g ∈ H) (w : W) : avgW H (g w) = avgW H w := by
  letI := Fintype.ofFinite H
  rw [avgW_apply, avgW_apply]
  exact Fintype.prod_equiv (Equiv.mulRight (⟨g, hg⟩ : H)) _ _ fun b => rfl

theorem avgW_comm (hc : ∀ n ∈ N, ∀ n' ∈ N', n * n' = n' * n) (w : W) :
    avgW N (avgW N' w) = avgW N' (avgW N w) := by
  letI := Fintype.ofFinite N
  letI := Fintype.ofFinite N'
  calc avgW N (avgW N' w) = ∏ n' : N', ∏ n : N, (n : MulAut W) ((n' : MulAut W) w) := by
        simp only [avgW_apply, map_prod]
    _ = ∏ n' : N', ∏ n : N, (n' : MulAut W) ((n : MulAut W) w) := by
        refine Finset.prod_congr rfl fun n' _ => Finset.prod_congr rfl fun n _ => ?_
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, hc n n.2 n' n'.2]
    _ = ∏ n : N, ∏ n' : N', (n' : MulAut W) ((n : MulAut W) w) := Finset.prod_comm
    _ = avgW N' (avgW N w) := by simp only [avgW_apply, map_prod]

theorem apply_avgW_of_comm {g : MulAut W} (hc : ∀ n ∈ H, g * n = n * g) (w : W) :
    g (avgW H w) = avgW H (g w) := by
  letI := Fintype.ofFinite H
  rw [avgW_apply, avgW_apply, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [← MulAut.mul_apply, hc n n.2, MulAut.mul_apply]

theorem avgW_map_conj (g : MulAut W) (N : Subgroup (MulAut W)) (w : W) :
    avgW (N.map (MulAut.conj g).toMonoidHom) (g w) = g (avgW N w) := by
  letI := Fintype.ofFinite N
  letI := Fintype.ofFinite (N.map (MulAut.conj g).toMonoidHom)
  rw [avgW_apply, avgW_apply, map_prod]
  refine (Fintype.prod_equiv
    (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv _ _
    fun n => ?_).symm
  change g ((n : MulAut W) w) = ((MulAut.conj g) (n : MulAut W)) (g w)
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

private theorem fixed_sup {K L : Subgroup (MulAut W)} {w : W} (hK : ∀ g ∈ K, g w = w)
    (hL : ∀ g ∈ L, g w = w) : ∀ g ∈ K ⊔ L, g w = w := by
  have h : K ⊔ L ≤ MulAction.stabilizer (MulAut W) w :=
    sup_le (fun g hg => by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hK g hg)
      (fun g hg => by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hL g hg)
  intro g hg
  have := h hg
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

private theorem fixed_zpowers {a : MulAut W} {w : W} (h : a w = w) :
    ∀ g ∈ Subgroup.zpowers a, g w = w := by
  have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut W) w :=
    (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h)
  intro g hg
  have := hle hg
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

variable (hW : ∀ w : W, w * w = 1)
include hW

theorem avgW_of_fixed (hodd : Odd (Nat.card H)) {w : W} (hw : ∀ h ∈ H, h w = w) :
    avgW H w = w := by
  letI := Fintype.ofFinite H
  rw [avgW_apply, Finset.prod_congr rfl fun (h : H) _ => hw h h.2, Finset.prod_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact pow_odd_eq_self_W hW hodd w

theorem avgW_avgW_of_le (hNA : N ≤ A) (hN : Odd (Nat.card N)) (w : W) :
    avgW N (avgW A w) = avgW A w :=
  avgW_of_fixed hW hN fun _ hn => apply_avgW (hNA hn) w

theorem avgW_of_le_avgW (hNA : N ≤ A) (hN : Odd (Nat.card N)) (w : W) :
    avgW A (avgW N w) = avgW A w := by
  letI := Fintype.ofFinite N
  rw [avgW_apply N, map_prod, Finset.prod_congr rfl fun (n : N) _ => avgW_apply_apply (hNA n.2) w,
    Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact pow_odd_eq_self_W hW hN _

theorem avgW_avgW_of_sup (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hNA : N ≤ A) (hN'A : N' ≤ A) (hsup : N ⊔ N' = A) (hodd : Odd (Nat.card A))
    (hN : Odd (Nat.card N)) (hN' : Odd (Nat.card N')) (w : W) :
    avgW N (avgW N' w) = avgW A w := by
  set u := avgW N (avgW N' w) with hu
  have hfixN : ∀ n ∈ N, n u = u := fun n hn => apply_avgW hn _
  have hfixN' : ∀ n ∈ N', n u = u := by
    intro n hn
    rw [hu, avgW_comm (fun a ha b hb => hA a (hNA ha) b (hN'A hb)), apply_avgW hn]
  let St : Subgroup (MulAut W) :=
    { carrier := {g | g u = u}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        change a (b u) = u
        rw [show b u = u from hb, show a u = u from ha]
      inv_mem' := fun {a} ha => by
        change a⁻¹ u = u
        conv_lhs => rw [← show a u = u from ha]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] }
  have hA' : A ≤ St := by
    rw [← hsup]
    exact sup_le (fun n hn => hfixN n hn) (fun n hn => hfixN' n hn)
  have h1 : avgW A u = u := avgW_of_fixed hW hodd fun a ha => hA' ha
  rw [← h1, hu, avgW_of_le_avgW hW hNA hN, avgW_of_le_avgW hW hN'A hN']

omit hW in
@[expose] noncomputable def eW (N A : Subgroup (MulAut W)) : W →* W :=
  avgW N * avgW A

omit hW in
theorem eW_apply (w : W) : eW N A w = avgW N w * avgW A w := rfl

theorem eW_eW (hNA : N ≤ A) (hN : Odd (Nat.card N)) (hodd : Odd (Nat.card A)) (w : W) :
    eW N A (eW N A w) = eW N A w := by
  simp only [eW_apply, map_mul, avgW_avgW_of_le hW hNA hN, avgW_of_le_avgW hW hNA hN,
    avgW_avgW_of_le hW le_rfl hodd, avgW_avgW_of_le hW le_rfl hN]
  rw [mul_assoc, hW, mul_one]

theorem eW_eW_of_ne (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hNA : N ≤ A) (hN'A : N' ≤ A) (hsup : N ⊔ N' = A) (hodd : Odd (Nat.card A))
    (hN : Odd (Nat.card N)) (hN' : Odd (Nat.card N')) (w : W) : eW N A (eW N' A w) = 1 := by
  simp only [eW_apply, map_mul, avgW_avgW_of_sup hW hA hNA hN'A hsup hodd hN hN',
    avgW_avgW_of_le hW hNA hN, avgW_of_le_avgW hW hN'A hN', avgW_avgW_of_le hW le_rfl hodd]
  simp only [hW, one_mul]

omit hW in
theorem card_range_eW_le_map_conj {g : MulAut W} (hg : g ∈ Subgroup.normalizer (A : Set (MulAut W)))
    (N : Subgroup (MulAut W)) :
    Nat.card (eW N A).range ≤ Nat.card (eW (N.map (MulAut.conj g).toMonoidHom) A).range := by
  have hAg : A.map (MulAut.conj g).toMonoidHom = A := by
    ext x
    rw [mem_map_conj, conj_mem_iff hg]
  have h : ∀ v, eW (N.map (MulAut.conj g).toMonoidHom) A (g v) = g (eW N A v) := by
    intro v
    have hA' := avgW_map_conj g A v
    rw [hAg] at hA'
    rw [eW_apply, eW_apply, map_mul, avgW_map_conj, hA']
  refine Nat.card_le_card_of_injective
    (fun x => ⟨g x, ?_⟩) fun x y hxy => Subtype.ext (g.injective (congrArg Subtype.val hxy))
  obtain ⟨v, hv⟩ := x.2
  exact ⟨g v, by rw [h, hv]⟩

theorem prod_card_range_le (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hodd : Odd (Nat.card A))
    {s : ℕ} (N : Fin s → Subgroup (MulAut W)) (hNA : ∀ i, N i ≤ A)
    (hN : ∀ i, Odd (Nat.card (N i))) (hsup : ∀ i j, i ≠ j → N i ⊔ N j = A) :
    ∏ i, Nat.card (eW (N i) A).range ≤ Nat.card W := by
  classical
  let f : (∀ i, (eW (N i) A).range) → W := fun x => ∏ i, (x i : W)
  have key : ∀ (x : ∀ i, (eW (N i) A).range) j, eW (N j) A (f x) = x j := by
    intro x j
    simp only [f, map_prod]
    rw [Finset.prod_eq_single j]
    · obtain ⟨v, hv⟩ := (x j).2
      rw [← hv, eW_eW hW (hNA j) (hN j) hodd]
    · intro i _ hij
      obtain ⟨v, hv⟩ := (x i).2
      rw [← hv, eW_eW_of_ne hW hA (hNA j) (hNA i) (hsup j i (Ne.symm hij)) hodd (hN j) (hN i)]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hinj : Function.Injective f := by
    intro x y hxy
    funext j
    apply Subtype.ext
    rw [← key x j, ← key y j, hxy]
  calc ∏ i, Nat.card (eW (N i) A).range = Nat.card (∀ i, (eW (N i) A).range) := by
        rw [Nat.card_pi]
    _ ≤ Nat.card W := Nat.card_le_card_of_injective f hinj

theorem eq_one_of_mem_range_eW {q : ℕ} [Fact q.Prime] (hq : Odd q) (hAq : ∀ a ∈ A, a ^ q = 1)
    (hNA : N ≤ A) (hN : Nat.card A = q * Nat.card N) {a : MulAut W} (haA : a ∈ A) (haN : a ∉ N)
    {w : W} (hw : w ∈ (eW N A).range) (haw : a w = w) : w = 1 := by
  obtain ⟨v, rfl⟩ := hw
  have hsupA := sup_zpowers_eq (Fact.out : q.Prime) hNA hN haA haN
  have hoddA : Odd (Nat.card A) := odd_card_of_le hq hAq le_rfl
  have hoddN : Odd (Nat.card N) := odd_card_of_le hq hAq hNA
  have hfixN : ∀ n ∈ N, n (eW N A v) = eW N A v := fun n hn => by
    rw [eW_apply, map_mul, apply_avgW hn, apply_avgW (hNA hn)]
  have hfixA : ∀ b ∈ A, b (eW N A v) = eW N A v := by
    intro b hb
    rw [← hsupA] at hb
    exact fixed_sup hfixN (fixed_zpowers haw) b hb
  calc eW N A v = eW N A (eW N A v) := (eW_eW hW hNA hoddN hoddA v).symm
    _ = 1 := by
      rw [eW_apply, avgW_of_fixed hW hoddN hfixN, avgW_of_fixed hW hoddA hfixA, hW]

theorem two_pow_le_card_range_eW {q : ℕ} [Fact q.Prime] (hq : Odd q)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAq : ∀ a ∈ A, a ^ q = 1) (hNA : N ≤ A)
    (hN : Nat.card A = q * Nat.card N) (hne : (eW N A).range ≠ ⊥) :
    2 ^ orderOf (2 : ZMod q) ≤ Nat.card (eW N A).range := by
  obtain ⟨a, haA, haN⟩ := exists_mem_not_mem (Fact.out : q.Prime) hN
  have hcomm : ∀ n ∈ N, a * n = n * a := fun n hn => hA a haA n (hNA hn)
  have heW : ∀ v, a (eW N A v) = eW N A (a v) := by
    intro v
    rw [eW_apply, eW_apply, map_mul, apply_avgW_of_comm hcomm, apply_avgW haA,
      avgW_apply_apply haA]
  refine two_pow_le_card_of_fixedPointFree hW (hAq a haA) hne ?_ ?_
  · rintro x ⟨v, rfl⟩
    exact ⟨a v, (heW v).symm⟩
  · exact fun x hx hax => eq_one_of_mem_range_eW hW hq hAq hNA hN haA haN hx hax

theorem exists_range_eW_ne_bot {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAq : ∀ a ∈ A, a ^ q = 1) (hA1 : A ≠ ⊥) :
    ∃ N ≤ A, Nat.card A = q * Nat.card N ∧ (eW N A).range ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hA a a.2 b b.2) }
  haveI : @CFSG.IsElementaryAbelian q A CommGroup.toGroup :=
    { toIsMulCommutative := ⟨⟨mul_comm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hAq a a.2) }
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  have hcop : ¬ q ∣ Nat.card W := by
    obtain ⟨m, hm⟩ := card_eq_two_pow_W hW (⊤ : Subgroup W)
    rw [Subgroup.card_top] at hm
    rw [hm]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 (hq.out.dvd_of_dvd_pow h))
  have htop := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top q hq.out A.subtype hcop
  have hqodd : Odd q := hq.out.odd_of_ne_two hq2
  have hoddA : Odd (Nat.card A) := odd_card_of_le hqodd hAq le_rfl
  have hle : (⨆ (B : Subgroup A) (_ : B.index = q),
      CFSG.SolvableSignalizer.fixedBySubgroup A.subtype B) ≤
        CFSG.SolvableSignalizer.fixedBySubgroup A.subtype ⊤ := by
    refine iSup₂_le fun B hB w hw => ?_
    rw [CFSG.SolvableSignalizer.mem_fixedBySubgroup] at hw ⊢
    have hNA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
    have hcardA : Nat.card A = q * Nat.card (B.map A.subtype) := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, ← hB, Subgroup.index_mul_card]
    have hoddN := odd_card_of_le hqodd hAq hNA
    have hfixN : ∀ n ∈ B.map A.subtype, n w = w := by
      rintro _ ⟨b, hb, rfl⟩
      exact hw b hb
    have h1 : eW (B.map A.subtype) A w = 1 := by
      have hmem : eW (B.map A.subtype) A w ∈ (eW (B.map A.subtype) A).range := ⟨w, rfl⟩
      rw [hcon _ hNA hcardA] at hmem
      exact (Subgroup.mem_bot).1 hmem
    rw [eW_apply, avgW_of_fixed hW hoddN hfixN] at h1
    have hw' : w = avgW A w := by
      calc w = w * (w * avgW A w) := by rw [h1, mul_one]
        _ = avgW A w := by rw [← mul_assoc, hW, one_mul]
    intro b _
    change (b : MulAut W) w = w
    rw [hw']
    exact apply_avgW b.2 w
  rw [htop] at hle
  apply hA1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext w
  exact (CFSG.SolvableSignalizer.mem_fixedBySubgroup _ _ _).1 (hle (Subgroup.mem_top w))
    ⟨a, ha⟩ (Subgroup.mem_top _)

theorem exists_orbit_two_pow_le {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAq : ∀ a ∈ A, a ^ q = 1) (hA1 : A ≠ ⊥)
    {g : MulAut W} (hg : g ∈ Subgroup.normalizer (A : Set (MulAut W)))
    (hsemi : ∀ k : ℕ, (∃ a ∈ A, a ≠ 1 ∧ g ^ k * a = a * g ^ k) →
      ∀ a ∈ A, g ^ k * a = a * g ^ k) :
    ∃ d : ℕ, 0 < d ∧ (∀ a ∈ A, g ^ (d * (q - 1)) * a = a * g ^ (d * (q - 1))) ∧
      2 ^ (orderOf (2 : ZMod q) * d) ≤ Nat.card W := by
  classical
  have hqodd : Odd q := hq.out.odd_of_ne_two hq2
  obtain ⟨N₀, hN₀A, hN₀, hne⟩ := exists_range_eW_ne_bot hW hq2 hA hAq hA1
  have hoddA : Odd (Nat.card A) := odd_card_of_le hqodd hAq le_rfl
  let Ni : ℕ → Subgroup (MulAut W) := fun k => N₀.map (MulAut.conj (g ^ k)).toMonoidHom
  have hmemNi : ∀ k x, x ∈ Ni k ↔ (g ^ k)⁻¹ * x * g ^ k ∈ N₀ := fun k x => mem_map_conj
  have hgk : ∀ k : ℕ, g ^ k ∈ Subgroup.normalizer (A : Set (MulAut W)) := fun k =>
    pow_mem hg k
  have hNiA : ∀ k, Ni k ≤ A := fun k x hx =>
    (conj_mem_iff (hgk k) x).1 (hN₀A ((hmemNi k x).1 hx))
  have hNicard : ∀ k, Nat.card A = q * Nat.card (Ni k) := fun k => by
    rw [hN₀]
    exact congrArg (q * ·)
      (Subgroup.card_map_of_injective (MulAut.conj (g ^ k)).injective).symm
  have hex : ∃ k, 0 < k ∧ Ni k = N₀ :=
    ⟨orderOf g, orderOf_pos g, Subgroup.ext fun x => by rw [hmemNi, pow_orderOf_eq_one]; simp⟩
  obtain ⟨hdpos, hdN⟩ := Nat.find_spec hex
  set d := Nat.find hex with hd
  have hdist : ∀ i j, i < j → j < d → Ni i ≠ Ni j := by
    intro i j hij hjd hNij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine Nat.find_min hex (m := k + 1) (by omega) ⟨by omega, Subgroup.ext fun z => ?_⟩
    have h := Subgroup.ext_iff.1 hNij (g ^ i * z * (g ^ i)⁻¹)
    rw [hmemNi, hmemNi] at h
    rw [hmemNi]
    have e1 : (g ^ i)⁻¹ * (g ^ i * z * (g ^ i)⁻¹) * g ^ i = z := by group
    have e2 : (g ^ (i + k + 1))⁻¹ * (g ^ i * z * (g ^ i)⁻¹) * g ^ (i + k + 1) =
        (g ^ (k + 1))⁻¹ * z * g ^ (k + 1) := by
      rw [show i + k + 1 = i + (k + 1) by omega, pow_add]
      group
    rw [e1, e2] at h
    exact h.symm
  have hsupNi : ∀ i j : Fin d, i ≠ j → Ni i ⊔ Ni j = A := by
    intro i j hij
    refine sup_eq_of_card hq.out (hNiA i) (hNiA j) (hNicard i) (hNicard j) ?_
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hdist i j h j.2
    · exact (hdist j i h i.2).symm
  have hbound : ∀ i : Fin d, 2 ^ orderOf (2 : ZMod q) ≤ Nat.card (eW (Ni i) A).range := fun i =>
    (two_pow_le_card_range_eW hW hqodd hA hAq hN₀A hN₀ hne).trans
      (card_range_eW_le_map_conj (hgk i) N₀)
  have hprod := prod_card_range_le hW hA hoddA (fun i : Fin d => Ni i) (fun i => hNiA i)
    (fun i => odd_card_of_le hqodd hAq (hNiA i)) hsupNi
  have hyN : ∀ n ∈ N₀, g ^ d * n * (g ^ d)⁻¹ ∈ N₀ := by
    intro n hn
    rw [← hdN, hmemNi]
    simpa [mul_assoc] using hn
  obtain ⟨a, haA, ha1, hac⟩ := exists_comm_pow_sub_one hA hN₀A hN₀ (hgk d) hyN
  refine ⟨d, hdpos, hsemi (d * (q - 1)) ⟨a, haA, ha1, by rw [pow_mul]; exact hac⟩, ?_⟩
  calc 2 ^ (orderOf (2 : ZMod q) * d) =
        (2 ^ orderOf (2 : ZMod q)) ^ (Finset.univ : Finset (Fin d)).card := by
        rw [Finset.card_univ, Fintype.card_fin, pow_mul]
    _ ≤ ∏ i : Fin d, Nat.card (eW (Ni i) A).range :=
        Finset.pow_card_le_prod _ _ _ fun i _ => hbound i
    _ ≤ Nat.card W := hprod

end Hyper

end CFSG.LocalAnalysis.GLTheoremA.S2019
