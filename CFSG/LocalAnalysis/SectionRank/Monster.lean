module

public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank

open CFSG.Open
open scoped commutatorElement

section Dihedral

variable {G : Type*} [Group G]

theorem inv_eq_self_of_sq_eq_one {u : G} (hu : u ^ 2 = 1) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_left (by rw [← sq, hu])

theorem conj_mul_eq_inv {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) :
    u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
  rw [mul_inv_rev, inv_eq_self_of_sq_eq_one hu, inv_eq_self_of_sq_eq_one hv, ← mul_assoc,
    ← sq, hu, one_mul]

theorem commutatorElement_eq_sq {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) :
    ⁅u, v⁆ = (u * v) ^ 2 := by
  rw [commutatorElement_def, inv_eq_self_of_sq_eq_one hu, inv_eq_self_of_sq_eq_one hv, sq]
  group

variable {p : ℕ} [hp : Fact p.Prime]

theorem independent_dihedral_odd_subgroups (hp2 : p ≠ 2) {r : ℕ} (u v : Fin r → G)
    (hu : ∀ i, u i ^ 2 = 1) (hv : ∀ i, v i ^ 2 = 1) (hx : ∀ i, orderOf (u i * v i) = p)
    (huu : ∀ i j, i ≠ j → Commute (u i) (u j)) (huv : ∀ i j, i ≠ j → Commute (u i) (v j))
    (hvv : ∀ i j, i ≠ j → Commute (v i) (v j)) :
    ∃ φ : (Fin r → Multiplicative (ZMod p)) →* G, Function.Injective φ ∧
      φ.range ≤ commutator G ∧ ∀ i (a : Multiplicative (ZMod p)),
        φ (Pi.mulSingle i a) = (u i * v i) ^ (Multiplicative.toAdd a).val := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set x : Fin r → G := fun i => u i * v i with hxdef
  have hxp : ∀ i, x i ^ p = 1 := fun i => by rw [← hx i]; exact pow_orderOf_eq_one _
  have hcomm : ∀ i j, i ≠ j → Commute (x i) (x j) := fun i j hij =>
    ((huu i j hij).mul_right (huv i j hij)).mul_left
      (((huv j i hij.symm).symm).mul_right (hvv i j hij))
  have hux : ∀ i j, i ≠ j → Commute (u i) (x j) := fun i j hij =>
    (huu i j hij).mul_right (huv i j hij)
  let ψ : ∀ i, Multiplicative (ZMod p) →* G := fun i => zmodPowHom (x i) (hxp i)
  let φ : (Fin r → Multiplicative (ZMod p)) →* G :=
    MonoidHom.noncommPiCoprod ψ fun i j hij a b => (hcomm i j hij).pow_pow _ _
  have hφs : ∀ i a, φ (Pi.mulSingle i a) = x i ^ (Multiplicative.toAdd a).val := fun i a =>
    MonoidHom.noncommPiCoprod_mulSingle ψ i a
  have hkey : ∀ i (n : ℕ), Commute (u i) (x i ^ n) → x i ^ n = 1 := by
    intro i n hc
    have h1 : u i * x i ^ n * (u i)⁻¹ = (x i ^ n)⁻¹ := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, conj_mul_eq_inv (hu i) (hv i),
        inv_pow]
    rw [hc.eq, mul_inv_cancel_right] at h1
    have h2 : x i ^ (2 * n) = 1 := by
      rw [two_mul, pow_add]
      nth_rewrite 1 [h1]
      exact inv_mul_cancel _
    have hdvd : p ∣ 2 * n := by
      have := orderOf_dvd_of_pow_eq_one h2
      rwa [hx i] at this
    have hpn : p ∣ n := (Nat.Coprime.dvd_mul_left
      ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)).1 hdvd
    rw [← hx i] at hpn
    exact orderOf_dvd_iff_pow_eq_one.1 hpn
  have hψinj : ∀ i, Function.Injective (ψ i) := fun i => by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    change x i ^ (Multiplicative.toAdd k).val = 1 at hk
    have hdvd : p ∣ (Multiplicative.toAdd k).val := by
      have := orderOf_dvd_of_pow_eq_one hk
      rwa [hx i] at this
    have h0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    rw [ZMod.val_eq_zero] at h0
    exact (Subgroup.mem_bot).2 (Multiplicative.toAdd.injective h0)
  have hind : iSupIndep fun i => (ψ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨k, rfl⟩, hg⟩
    have hle : (⨆ (j : Fin r) (_ : j ≠ i), (ψ j).range) ≤ Subgroup.centralizer {u i} := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (((hux i j (Ne.symm hj)).pow_right _).eq).symm
    have hc := hle hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    exact (Subgroup.mem_bot).2 (hkey i _ (Commute.symm hc.symm).symm)
  refine ⟨φ, MonoidHom.injective_noncommPiCoprod_of_iSupIndep ψ hind hψinj, ?_, hφs⟩
  · have hr : φ.range = ⨆ i, (ψ i).range := by apply MonoidHom.noncommPiCoprod_range
    rw [hr]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    simp only [ψ, zmodPowHom_apply]
    refine Subgroup.pow_mem _ ?_ _
    have hc : ⁅u i, v i⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [commutatorElement_eq_sq (hu i) (hv i)] at hc
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    have hxe : x i = (x i ^ 2) ^ ((p + 1) / 2) := by
      rw [← pow_mul, show 2 * ((p + 1) / 2) = p + 1 by omega, pow_succ, hxp, one_mul]
    rw [hxe]
    exact Subgroup.pow_mem _ hc _

theorem exists_isElemAbelian_of_dihedral (hp2 : p ≠ 2) {r : ℕ} (u v : Fin r → G)
    (hu : ∀ i, u i ^ 2 = 1) (hv : ∀ i, v i ^ 2 = 1) (hx : ∀ i, orderOf (u i * v i) = p)
    (huu : ∀ i j, i ≠ j → Commute (u i) (u j)) (huv : ∀ i j, i ≠ j → Commute (u i) (v j))
    (hvv : ∀ i j, i ≠ j → Commute (v i) (v j)) :
    ∃ E : Subgroup G, E ≤ commutator G ∧ IsElemAbelian p E ∧ Nat.card E = p ^ r := by
  obtain ⟨φ, hφ, hφG, -⟩ := independent_dihedral_odd_subgroups hp2 u v hu hv hx huu huv hvv
  refine ⟨φ.range, hφG, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have : x ^ p = 1 := by
      funext i
      apply Multiplicative.toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero,
        zero_mul]
    rw [← map_pow, this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end Dihedral

section Coxeter

variable {V : Type*} (Γ : SimpleGraph V) {G : Type*} [Group G]

theorem eq_of_adj_of_collapsed (htri : Γ.CliqueFree 3) (s : V → G) (hs : ∀ v, s v ^ 2 = 1)
    (hedge : ∀ u v, Γ.Adj u v → (s u * s v) ^ 3 = 1)
    (hnon : ∀ u v, u ≠ v → ¬ Γ.Adj u v → Commute (s u) (s v)) {a b c : V} (hab : Γ.Adj a b)
    (heq : s a = s b) (hac : Γ.Adj a c) : s c = s a := by
  classical
  by_cases hbc : b = c
  · rw [← hbc, heq]
  have hnbc : ¬ Γ.Adj b c := fun h =>
    htri {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, h⟩)
  have hc := hnon b c hbc hnbc
  have h2 : (s a * s c) ^ 2 = 1 := by
    rw [heq, hc.mul_pow, hs, hs, one_mul]
  have h3 := hedge a c hac
  have h1 : s a * s c = 1 := by
    have : (s a * s c) ^ 3 = (s a * s c) ^ 2 * (s a * s c) := pow_succ _ 2
    rw [h3, h2, one_mul] at this
    exact this.symm
  have := eq_inv_of_mul_eq_one_left h1
  rw [inv_eq_self_of_sq_eq_one (hs c)] at this
  exact this.symm

theorem orderOf_mul_eq_three_of_adj (hconn : Γ.Connected) (htri : Γ.CliqueFree 3) (s : V → G)
    (hgen : Subgroup.closure (Set.range s) = ⊤) (hs : ∀ v, s v ^ 2 = 1)
    (hedge : ∀ u v, Γ.Adj u v → (s u * s v) ^ 3 = 1)
    (hnon : ∀ u v, u ≠ v → ¬ Γ.Adj u v → Commute (s u) (s v)) (hG : commutator G ≠ ⊥)
    {u v : V} (huv : Γ.Adj u v) : orderOf (s u * s v) = 3 := by
  have h3 : orderOf (s u * s v) ∣ 3 := orderOf_dvd_of_pow_eq_one (hedge u v huv)
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    have heq : s u = s v := by
      have := eq_inv_of_mul_eq_one_left h
      rwa [inv_eq_self_of_sq_eq_one (hs v)] at this
    let P : V → Prop := fun a => ∃ b, Γ.Adj a b ∧ s a = s b
    have hstep : ∀ a c, P a → Γ.Adj a c → P c ∧ s c = s a := by
      rintro a c ⟨b, hab, hb⟩ hac
      have hca := eq_of_adj_of_collapsed Γ htri s hs hedge hnon hab hb hac
      exact ⟨⟨a, hac.symm, hca⟩, hca⟩
    have hwalk : ∀ {a b : V} (w : Γ.Walk a b), P a → P b ∧ s b = s a := by
      intro a b w
      induction w with
      | nil => exact fun h => ⟨h, rfl⟩
      | cons hadj _ ih =>
        intro hPa
        obtain ⟨hPc, hc⟩ := hstep _ _ hPa hadj
        obtain ⟨hPb, hb⟩ := ih hPc
        exact ⟨hPb, hb.trans hc⟩
    have hall : ∀ w, s w = s u := fun w => by
      obtain ⟨walk⟩ := hconn.preconnected u w
      exact (hwalk walk ⟨v, huv, heq⟩).2
    have hrange : Set.range s = {s u} := by
      ext g
      constructor
      · rintro ⟨w, rfl⟩
        exact hall w
      · rintro rfl
        exact ⟨u, rfl⟩
    have hz : ∀ g : G, g ∈ Subgroup.zpowers (s u) := fun g => by
      rw [Subgroup.zpowers_eq_closure, ← hrange, hgen]
      exact Subgroup.mem_top g
    apply hG
    rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    obtain ⟨m, rfl⟩ := hz g
    obtain ⟨n, rfl⟩ := hz h
    exact (Commute.zpow_zpow_self (s u) n m).eq
  · exact h

end Coxeter

section Y443

open CFSG.Blueprint.NativeSporadic

@[expose] def y443AdjB (i j : Fin 12) : Bool :=
  (i.val == 0 && (j.val == 1 || j.val == 5 || j.val == 9)) ||
  (j.val == 0 && (i.val == 1 || i.val == 5 || i.val == 9)) ||
  (i.val + 1 == j.val && (i.val == 1 || i.val == 2 || i.val == 3 || i.val == 5 || i.val == 6 ||
    i.val == 7 || i.val == 9 || i.val == 10)) ||
  (j.val + 1 == i.val && (j.val == 1 || j.val == 2 || j.val == 3 || j.val == 5 || j.val == 6 ||
    j.val == 7 || j.val == 9 || j.val == 10))

theorem y443Adjacent_iff (i j : Fin 12) : y443Adjacent i j ↔ y443AdjB i j = true := by
  simp only [y443Adjacent, y443AdjB, Set.mem_insert_iff, Set.mem_singleton_iff, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, or_assoc]

theorem y443Adjacent_parity {i j : Fin 12} (h : y443Adjacent i j) : i.val % 2 ≠ j.val % 2 := by
  simp only [y443Adjacent, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  omega

@[expose] def y443Graph : SimpleGraph (Fin 12) where
  Adj := y443Adjacent
  symm := ⟨fun i j h => by
    simp only [y443Adjacent] at h ⊢
    tauto⟩
  loopless := ⟨fun i h => y443Adjacent_parity h rfl⟩

theorem y443Graph_cliqueFree : y443Graph.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.1 ht.card_eq
  obtain ⟨hab, hac, hbc⟩ := SimpleGraph.is3Clique_triple_iff.1 ht
  have h1 := y443Adjacent_parity (show y443Adjacent a b from hab)
  have h2 := y443Adjacent_parity (show y443Adjacent a c from hac)
  have h3 := y443Adjacent_parity (show y443Adjacent b c from hbc)
  omega

theorem y443Graph_adj (i j : Fin 12) (h : y443AdjB i j = true) : y443Graph.Adj i j :=
  show y443Adjacent i j from (y443Adjacent_iff i j).2 h

theorem y443Graph_connected : y443Graph.Connected := by
  have h0 : ∀ w : Fin 12, y443Graph.Reachable 0 w := by
    have e : ∀ i j : Fin 12, y443AdjB i j = true → y443Graph.Reachable i j :=
      fun i j h => (y443Graph_adj i j h).reachable
    have r1 := e 0 1 rfl
    have r2 := r1.trans (e 1 2 rfl)
    have r3 := r2.trans (e 2 3 rfl)
    have r4 := r3.trans (e 3 4 rfl)
    have r5 := e 0 5 rfl
    have r6 := r5.trans (e 5 6 rfl)
    have r7 := r6.trans (e 6 7 rfl)
    have r8 := r7.trans (e 7 8 rfl)
    have r9 := e 0 9 rfl
    have r10 := r9.trans (e 9 10 rfl)
    have r11 := r10.trans (e 10 11 rfl)
    intro w
    fin_cases w
    · exact SimpleGraph.Reachable.refl _
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact r7
    · exact r8
    · exact r9
    · exact r10
    · exact r11
  exact ⟨fun u w => (h0 u).symm.trans (h0 w)⟩

noncomputable abbrev y443Gen (i : Fin 12) : Y443 := PresentedGroup.of i

theorem y443_rel {w : FreeGroup (Fin 12)} (hw : w ∈ y443Relations) :
    (QuotientGroup.mk w : Y443) = 1 :=
  (QuotientGroup.eq_one_iff w).2 (Subgroup.subset_normalClosure hw)

theorem y443Gen_sq (i : Fin 12) : y443Gen i ^ 2 = 1 := by
  have h := y443_rel (w := FreeGroup.of i ^ 2) (Or.inl (Or.inl ⟨i, rfl⟩))
  rwa [QuotientGroup.mk_pow] at h

open scoped Classical in
theorem y443Gen_rel (i j : Fin 12) (hij : i.val < j.val) :
    (y443Gen i * y443Gen j) ^ (if y443Adjacent i j then 3 else 2) = 1 := by
  classical
  have h := y443_rel (w := (FreeGroup.of i * FreeGroup.of j) ^
    (if y443Adjacent i j then 3 else 2)) (Or.inl (Or.inr ⟨i, j, hij, by congr⟩))
  rwa [QuotientGroup.mk_pow, QuotientGroup.mk_mul] at h

theorem commute_of_sq_mul_eq_one {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (h : (a * b) ^ 2 = 1) : Commute a b := by
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left (by rw [← sq, h])).symm
  rw [mul_inv_rev, inv_eq_self_of_sq_eq_one ha, inv_eq_self_of_sq_eq_one hb] at h1
  exact h1

theorem y443Gen_edge (i j : Fin 12) (h : y443Graph.Adj i j) :
    (y443Gen i * y443Gen j) ^ 3 = 1 := by
  classical
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · have := y443Gen_rel i j hlt
    simpa only [show y443Adjacent i j from h, ↓reduceIte] using this
  · exact absurd (Fin.ext heq) (fun e => y443Graph.loopless.irrefl i (e ▸ h))
  · have := y443Gen_rel j i hgt
    simp only [show y443Adjacent j i from h.symm, ↓reduceIte] at this
    have hinv : y443Gen i * y443Gen j = (y443Gen j * y443Gen i)⁻¹ := by
      rw [mul_inv_rev, inv_eq_self_of_sq_eq_one (y443Gen_sq i),
        inv_eq_self_of_sq_eq_one (y443Gen_sq j)]
    rw [hinv, inv_pow, this, inv_one]

theorem y443Gen_commute (i j : Fin 12) (hij : i ≠ j) (h : ¬ y443Graph.Adj i j) :
    Commute (y443Gen i) (y443Gen j) := by
  classical
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
  · have := y443Gen_rel i j hlt
    simp only [show ¬ y443Adjacent i j from h, ↓reduceIte] at this
    exact commute_of_sq_mul_eq_one (y443Gen_sq i) (y443Gen_sq j) this
  · have := y443Gen_rel j i hgt
    have hn : ¬ y443Adjacent j i := fun h' =>
      h (y443Graph.adj_symm (show y443Graph.Adj j i from h'))
    simp only [hn, ↓reduceIte] at this
    exact (commute_of_sq_mul_eq_one (y443Gen_sq j) (y443Gen_sq i) this).symm

theorem y443_closure : Subgroup.closure (Set.range y443Gen) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact PresentedGroup.generated_by _ _ (fun j => Subgroup.subset_closure (Set.mem_range_self j)) x

theorem M_nontrivial_elementary_three_rank_four [Nontrivial M] :
    ∃ E : Subgroup M, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG : commutator Y443 ≠ ⊥ := by
    intro h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M
    apply hxy
    have hx : (x : Y443) ∈ (⊥ : Subgroup Y443) := by rw [← h]; exact x.2
    have hy : (y : Y443) ∈ (⊥ : Subgroup Y443) := by rw [← h]; exact y.2
    rw [Subgroup.mem_bot] at hx hy
    exact Subtype.ext (hx.trans hy.symm)
  have hord : ∀ i j, y443AdjB i j = true → orderOf (y443Gen i * y443Gen j) = 3 :=
    fun i j h => orderOf_mul_eq_three_of_adj y443Graph y443Graph_connected
      y443Graph_cliqueFree y443Gen y443_closure y443Gen_sq y443Gen_edge y443Gen_commute hG
      (y443Graph_adj i j h)
  have hc : ∀ i j : Fin 12, i ≠ j → y443AdjB i j = false → Commute (y443Gen i) (y443Gen j) :=
    fun i j hij h => y443Gen_commute i j hij (fun h' => by
      have := (y443Adjacent_iff i j).1 h'
      rw [h] at this
      exact absurd this (by decide))
  let a : Fin 4 → Fin 12 := ![0, 3, 6, 10]
  let b : Fin 4 → Fin 12 := ![1, 4, 7, 11]
  obtain ⟨E, hEG, hE, hcard⟩ := exists_isElemAbelian_of_dihedral (p := 3) (by norm_num)
    (fun i => y443Gen (a i)) (fun i => y443Gen (b i)) (fun i => y443Gen_sq _)
    (fun i => y443Gen_sq _) (fun i => hord _ _ (by fin_cases i <;> rfl))
    (fun i j hij => hc _ _ (by fin_cases i <;> fin_cases j <;> simp_all [a]) (by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl))
    (fun i j hij => hc _ _ (by fin_cases i <;> fin_cases j <;> simp_all [a, b]) (by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl))
    (fun i j hij => hc _ _ (by fin_cases i <;> fin_cases j <;> simp_all [b]) (by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl))
  refine ⟨E.subgroupOf (commutator Y443), ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have hcomm := hE.1
    have h := congrArg Subtype.val (mul_comm' (⟨((x : M) : Y443), x.2⟩ : E)
      ⟨((y : M) : Y443), y.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 (x : Y443) hx
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv

theorem M_nontrivial_central_quotient_exclusion {G : Type} [Group G] [Finite G]
    (hSQT : IsStronglyQuasithin G) (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G)
    (hnt : Nontrivial (G ⧸ A)) : IsEmpty (G ⧸ A ≃* M) := by
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hnt
  have : Nontrivial M := e.injective.nontrivial
  have : Finite M := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE, hcard⟩ := M_nontrivial_elementary_three_rank_four
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup M) := le_pRank (by norm_num) le_top hE hcard
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h4
  have h3 := pRank_quotient_le_three (by norm_num)
    (isStronglyQuasithin_iff.1 hSQT 3 Nat.prime_three (by norm_num)) A hAZ
  omega

end Y443

end CFSG.SectionRank
