module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def K3 (G : Type*) [Group G] : Prop :=
  ∀ x : G, orderOf x = 3 → 4 ∣ Nat.card (centralizer ({x} : Set G))

section Group

variable {G : Type*} [Group G]

theorem centralizer_conj_eq (c x : G) :
    centralizer ({c * x * c⁻¹} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_map]
  constructor
  · intro h
    refine ⟨c⁻¹ * y * c, ?_, by simp [mul_assoc]⟩
    rw [mem_centralizer_singleton_iff]
    have : c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
    rw [this, h]
    group
  · rintro ⟨z, hz, rfl⟩
    rw [mem_centralizer_singleton_iff] at hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * z * c⁻¹ * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by group
      _ = c * (x * z) * c⁻¹ := by rw [hz]
      _ = c * x * c⁻¹ * (c * z * c⁻¹) := by group

theorem card_centralizer_conj (c x : G) :
    Nat.card (centralizer ({c * x * c⁻¹} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  rw [centralizer_conj_eq, card_map_of_injective (MulAut.conj c).injective]

theorem centralizer_sq_eq {x : G} (hx : orderOf x = 3) :
    centralizer ({x ^ 2} : Set G) = centralizer ({x} : Set G) := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h4 : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ← hx, pow_orderOf_eq_one, one_mul,
        pow_one]
    rw [h4]
    exact (Commute.pow_right h 2).eq
  · intro h
    exact (Commute.pow_right h 2).eq

theorem four_dvd_card_of_orderOf [Finite G] {H : Subgroup G} {w : G} (hw : w ∈ H)
    (h4 : orderOf w = 4) : 4 ∣ Nat.card H := by
  have hle : zpowers w ≤ H := (zpowers_le).2 hw
  rw [← h4, ← Nat.card_zpowers]
  exact card_dvd_of_le hle

theorem four_dvd_card_of_klein [Finite G] {H : Subgroup G} {u v : G} (hu : u ∈ H) (hv : v ∈ H)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (huv : u ≠ v) (hc : u * v = v * u) :
    4 ∣ Nat.card H := by
  classical
  have uu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have vv : v * v = 1 := by rw [← pow_two, ← hv2, pow_orderOf_eq_one]
  have u1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have v1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv2; exact absurd hv2 (by norm_num)
  have uinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right uu
  have vinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right vv
  have uux : ∀ y : G, u * (u * y) = y := fun y => by rw [← mul_assoc, uu, one_mul]
  have vux : ∀ y : G, v * (u * y) = u * (v * y) := fun y => by rw [← mul_assoc, ← hc, mul_assoc]
  have vu : v * u = u * v := hc.symm
  let S : Finset G := {1, u, v, u * v}
  let K : Subgroup G :=
    { carrier := (S : Set G)
      mul_mem' := by
        intro a b ha hb
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [mul_assoc, uu, vv, uux, vux, vu]
      one_mem' := by simp [S]
      inv_mem' := by
        intro a ha
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · simp [uinv]
        · simp [vinv]
        · right; right; right; rw [mul_inv_rev, uinv, vinv, hc] }
  have hK : K ≤ H := by
    intro a ha
    change a ∈ (S : Set G) at ha
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact hu
    · exact hv
    · exact H.mul_mem hu hv
  have hcard : Nat.card K = 4 := by
    have e : Nat.card K = S.card := by
      rw [← Nat.card_eq_finsetCard]
      rfl
    rw [e]
    have h1 : u * v ≠ 1 := fun h => huv (by rw [← vinv]; exact eq_inv_of_mul_eq_one_left h)
    have h2 : u * v ≠ u := fun h => v1 (by simpa using h)
    have h3 : u * v ≠ v := fun h => u1 (by simpa using h)
    simp only [S]
    rw [Finset.card_insert_of_notMem (by simp [u1.symm, v1.symm, h1.symm]),
      Finset.card_insert_of_notMem (by simp [huv, h2.symm]),
      Finset.card_insert_of_notMem (by simp [h3.symm]), Finset.card_singleton]
  rw [← hcard]
  exact card_dvd_of_le hK

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hx : IsPGroup p (zpowers x)) : ∃ c : G, c * x * c⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have hxQ : x ∈ (Q : Subgroup G) := hQ (mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
  simpa [mul_assoc] using hxQ

theorem K3.of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') (h : K3 G') : K3 G := by
  intro x hx
  have hx' : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  have h' := h (e x) hx'
  have hmap : centralizer ({e x} : Set G') = (centralizer ({x} : Set G)).map e.toMonoidHom := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_map]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      simp [map_mul, hy]
    · rintro ⟨z, hz, rfl⟩
      rw [mem_centralizer_singleton_iff] at hz
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, hz, map_mul]
  rw [hmap, card_map_of_injective e.injective] at h'
  exact h'

end Group

section Tables

variable {n : ℕ}

theorem order3OK_of_pow {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) (h3 : g ^ 3 = 1) :
    order3OK n T = true := by
  rw [order3OK, allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hT i hi, hT _ (idx_lt g hi), hT _ (idx_lt g (idx_lt g hi)), ← idx_mul,
    ← idx_mul, show g * g * g = g ^ 3 by rw [pow_three, mul_assoc], h3, idx_one]

theorem isOrd3_of_orderOf (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g)
    (h : orderOf g = 3) : isOrd3 n T = true := by
  rw [isOrd3, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · cases e : tblEq n T (idT n)
    · rfl
    · rw [(tblEq_idT_iff hn hT).1 e, orderOf_one] at h
      exact absurd h (by norm_num)
  · exact order3OK_of_pow hT (by rw [← h, pow_orderOf_eq_one])

theorem getElem!_mem_of_lt {A : Array Table} {l : ℕ} (hl : l < A.size) : A[l]! ∈ A := by
  rw [getElem!_pos A l hl]
  exact Array.getElem_mem hl

theorem rep_ofNatArr (hn : n < 2 ^ 32) {a : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n a g) : Rep n (a.map UInt32.ofNat) g := by
  intro i hi
  have h1 := h ⟨i, hi⟩
  rw [idx_of_lt _ hi]
  unfold ap
  by_cases hs : i < a.size
  · rw [getElem!_pos (a.map UInt32.ofNat) i (by simpa using hs), Array.getElem_map,
      UInt32.toNat_ofNat', ← getElem!_pos a i hs, h1, Nat.mod_eq_of_lt ((g _).isLt.trans hn)]
    rfl
  · rw [getElem!_neg (a.map UInt32.ofNat) i (by simpa using hs)]
    rw [getElem!_neg a i hs] at h1
    rw [show (g • (⟨i, hi⟩ : Fin n) : Fin n) = g ⟨i, hi⟩ from rfl, ← h1]
    rfl

theorem pair_gens {T : Subgroup (Equiv.Perm (Fin n))} {x y : Equiv.Perm (Fin n)} {tx ty : Table}
    (hx : Rep n tx x) (hy : Rep n ty y) (hxT : x ∈ T) (hyT : y ∈ T) :
    ∀ l < (#[tx, ty] : Array Table).size,
      Rep n (#[tx, ty] : Array Table)[l]! (if l = 0 then x else y) ∧
        (if l = 0 then x else y) ∈ T := by
  intro l hl
  have hl2 : l < 2 := by simpa using hl
  interval_cases l
  · exact ⟨hx, hxT⟩
  · exact ⟨hy, hyT⟩

theorem witOK_spec (hn : n < 2 ^ 32) {T : Subgroup (Equiv.Perm (Fin n))} {regs : Array Table}
    {gR : ℕ → Equiv.Perm (Fin n)} (hR : ∀ r < regs.size, Rep n regs[r]! (gR r) ∧ gR r ∈ T)
    {x : Table} {r : Equiv.Perm (Fin n)} (hx : Rep n x r) (hrT : r ∈ T) {w : Wit}
    (h : witOK n regs x w = true) :
    4 ∣ Nat.card (centralizer ({(⟨r, hrT⟩ : T)} : Set T)) := by
  have hcomm : ∀ {g : Equiv.Perm (Fin n)} (hg : g ∈ T), g * r = r * g →
      (⟨g, hg⟩ : T) ∈ centralizer ({(⟨r, hrT⟩ : T)} : Set T) := by
    intro g hg e
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext e
  cases w with
  | z4 w =>
    simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hw, hc⟩, h2⟩, h4⟩ := h
    obtain ⟨hrep, hmem⟩ := hR w hw
    have h4' : gR w ^ 4 = 1 := (tblEq_idT_iff hn (Rep.powT hn hrep 4)).1 h4
    have h2' : ¬ gR w ^ 2 ^ 1 = 1 := by
      intro e
      rw [pow_one, pow_two] at e
      rw [(tblEq_idT_iff hn (Rep.compT hrep hrep)).2 e] at h2
      exact Bool.noConfusion h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (gR w) = 2 ^ (1 + 1) := orderOf_eq_prime_pow h2' (by simpa using h4')
    exact four_dvd_card_of_orderOf (hcomm hmem ((commTT_iff hrep hx).1 hc))
      (by rw [Subgroup.orderOf_mk, hord]; norm_num)
  | v4 u v =>
    simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hu, hv⟩, hu2⟩, hv2⟩, huv⟩, hc⟩, hcu⟩, hcv⟩ := h
    obtain ⟨hrepu, hmemu⟩ := hR u hu
    obtain ⟨hrepv, hmemv⟩ := hR v hv
    refine four_dvd_card_of_klein (hcomm hmemu ((commTT_iff hrepu hx).1 hcu))
      (hcomm hmemv ((commTT_iff hrepv hx).1 hcv))
      (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_two_of_involOK hn hrepu hu2)
      (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_two_of_involOK hn hrepv hv2) ?_ ?_
    · intro e
      have e' : gR u = gR v := congrArg Subtype.val e
      rw [(tblEq_iff_eq hrepu hrepv).2 e'] at huv
      exact Bool.noConfusion huv
    · exact Subtype.ext ((commTT_iff hrepu hrepv).1 hc)

end Tables

section Check

variable {n : ℕ}

theorem k3_of_checkCore (hn : n < 2 ^ 32) {T : Subgroup (Equiv.Perm (Fin n))} {order : ℕ}
    {regs : Array Table} {gR : ℕ → Equiv.Perm (Fin n)}
    (hR : ∀ r < regs.size, Rep n regs[r]! (gR r) ∧ gR r ∈ T) {syl reps : List ℕ}
    {wits : List Wit} (h : checkCore n order regs syl reps wits = true) {a m : ℕ}
    (hcard : Nat.card T = 3 ^ a * m) (hm : ¬ 3 ∣ m) (hord : order = 3 ^ a) : K3 T := by
  simp only [checkCore, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  set A : Array Table := (syl.map fun r => regs[r]!).toArray with hA
  set E := mulClosureH n A (order + 1) with hE
  have hAmem : ∀ x ∈ A, ∃ r < regs.size, x = regs[r]! := by
    intro x hx
    rw [hA, List.mem_toArray, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨r, by simpa using (List.all_eq_true.1 h1) r hr, rfl⟩
  have hperm : ∀ x ∈ A, permOK n x = true := Array.all_eq_true_iff_forall_mem.1 h2
  have hinv : ∀ x ∈ A, invOK n x (invT n x) = true := Array.all_eq_true_iff_forall_mem.1 h3
  obtain ⟨hEP, hPE, hPcard⟩ := enum_spec hn hperm hinv h4 h5 h6
  set P := closure (tp n '' {x | x ∈ A}) with hP
  have hPT : P ≤ T := by
    rw [hP, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hAmem x hx
    rw [rep_unique (rep_tp (hperm _ hx)) (hR r hr).1]
    exact (hR r hr).2
  have hPsub : Nat.card (P.subgroupOf T) = 3 ^ a := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPT).toEquiv, hPcard, h7, hord]
  have hidx : (P.subgroupOf T).index = m := by
    have e := (P.subgroupOf T).card_mul_index
    rw [hPsub, hcard] at e
    exact Nat.eq_of_mul_eq_mul_left (by positivity) e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 (P.subgroupOf T) := IsPGroup.of_card hPsub
  have hPidx : ¬ 3 ∣ (P.subgroupOf T).index := by rw [hidx]; exact hm
  have hgA : ∀ l < A.size, Rep n A[l]! (tp n A[l]!) ∧ Rep n (A.map (invT n))[l]! (tp n A[l]!)⁻¹ ∧
      tp n A[l]! ∈ P := by
    intro l hl
    have hx := getElem!_mem_of_lt hl
    refine ⟨rep_tp (hperm _ hx), ?_, subset_closure ⟨_, hx, rfl⟩⟩
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos A l hl]
    exact rep_invT (rep_tp (hperm _ hx)) (hinv _ hx)
  intro x hx3
  have hxp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (hPp.toSylow hPidx) hxp
  rw [IsPGroup.toSylow_coe, mem_subgroupOf] at hc
  rw [← card_centralizer_conj c x]
  set y : T := c * x * c⁻¹ with hy
  have hy3 : orderOf y = 3 := by
    rw [hy, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hy3' : orderOf (y : Equiv.Perm (Fin n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hy3
  obtain ⟨k, hk, hkrep⟩ := hPE _ hc
  have hcov := (Array.all_eq_true_iff_forall_mem.1 h11) E.1[k]! (getElem!_mem_of_lt hk)
  rw [isOrd3_of_orderOf hn hkrep hy3', Bool.not_true, Bool.false_or, List.any_eq_true] at hcov
  obtain ⟨cl, hcl, hmem⟩ := hcov
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
  simp only [List.length_map] at hi
  have hik : reps[i] < E.1.size := by
    simpa using (List.all_eq_true.1 h8) _ (List.getElem_mem hi)
  obtain ⟨hrrep, hrP⟩ := hEP _ hik
  set r := tablePerm n E.1[reps[i]]! with hr
  have hrT : r ∈ T := hPT hrP
  have htree := (List.all_eq_true.1 h10) _ (List.getElem_mem (l := (reps.map fun i => E.1[i]!).zip
    ((reps.map fun i => E.1[i]!).map fun x => conjClosureH n A (A.map (invT n)) x (order + 1)))
    (show i < _ by simpa using hi))
  simp only [List.getElem_zip, List.getElem_map] at htree
  have hcls := conjTreeOK_spec P hgA hrrep htree
  set Cl := conjClosureH n A (A.map (invT n)) E.1[reps[i]]! (order + 1) with hCl
  have hClrep : ∀ j < Cl.1.size, Rep n Cl.1[j]! (tablePerm n Cl.1[j]!) := by
    intro j hj
    obtain ⟨c', -, hc'⟩ := hcls j hj
    rw [tablePerm_eq hc']
    exact hc'
  have hwit : 4 ∣ Nat.card (centralizer ({(⟨r, hrT⟩ : T)} : Set T)) := by
    have hw := (List.all_eq_true.1 h12) _ (List.getElem_mem (l := (reps.map fun i => E.1[i]!).zip
      wits) (show i < _ by simpa [h9] using hi))
    simp only [List.getElem_zip, List.getElem_map] at hw
    exact witOK_spec hn hR hrrep hrT hw
  have key : ∀ z : T, (∃ j < Cl.1.size, (z : Equiv.Perm (Fin n)) = tablePerm n Cl.1[j]!) →
      4 ∣ Nat.card (centralizer ({z} : Set T)) := by
    rintro z ⟨j, hj, hzj⟩
    obtain ⟨c', hc'P, hc'⟩ := hcls j hj
    rw [tablePerm_eq hc'] at hzj
    have hc'T : c' ∈ T := hPT hc'P
    have hz : z = (⟨c', hc'T⟩ : T) * ⟨r, hrT⟩ * (⟨c', hc'T⟩ : T)⁻¹ := Subtype.ext hzj
    rw [hz, card_centralizer_conj]
    exact hwit
  simp only [List.getElem_map, Bool.or_eq_true] at hmem
  rcases hmem with hm1 | hm2
  · exact key y (memT_spec hClrep hkrep hm1)
  · rw [← centralizer_sq_eq hy3]
    refine key (y ^ 2) (memT_spec hClrep ?_ hm2)
    rw [Subgroup.coe_pow, pow_two]
    exact Rep.compT hkrep hkrep

theorem runSLPG_mem {G : Type*} [Group G] (K : Subgroup G) (prog : List Instr) :
    ∀ regs : ℕ → G, (∀ r, regs r ∈ K) → ∀ r, runSLPG prog regs r ∈ K := by
  induction prog with
  | nil => intro regs h r; exact h r
  | cons ins prog ih =>
    intro regs h r
    apply ih (stepG regs ins)
    intro s
    cases ins with
    | mu i j k =>
      simp only [stepG, Function.update_apply]
      split_ifs
      · exact K.mul_mem (h i) (h j)
      · exact h s
    | pwr e i k =>
      simp only [stepG, Function.update_apply]
      split_ifs
      · exact K.pow_mem (h i) e
      · exact h s
    | iv i k =>
      simp only [stepG, Function.update_apply]
      split_ifs
      · exact K.inv_mem (h i)
      · exact h s

theorem instrRegsLt_of_instrLtB {r : ℕ} {ins : Instr} (h : instrLtB r ins = true) :
    instrRegsLt r ins := by
  cases ins <;> simp_all [instrLtB, instrRegsLt]

theorem k3_of_check_aux {D : Data} (hn : D.n < 2 ^ 32) {T : Subgroup (Equiv.Perm (Fin D.n))}
    {gG : ℕ → Equiv.Perm (Fin D.n)}
    (hgens : ∀ l < D.gens.size, Rep D.n D.gens[l]! (gG l) ∧ gG l ∈ T) (h : check D = true)
    {a m : ℕ} (hcard : Nat.card T = 3 ^ a * m) (hm : ¬ 3 ∣ m) (hord : D.order = 3 ^ a) :
    K3 T := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hsize, hprog⟩, hok⟩, hcore⟩ := h
  let regsG : ℕ → Equiv.Perm (Fin D.n) := fun r => if r < D.gens.size then gG r else 1
  have hsz0 : (regs0 D).size = D.regs := by simp [regs0]; omega
  have hregs : ∀ r < (regs0 D).size, Rep D.n (regs0 D)[r]! (regsG r) := by
    intro r hr
    unfold regs0 at hr ⊢
    rw [getElem!_pos _ r hr]
    by_cases hr' : r < D.gens.size
    · simp only [regsG, hr', ite_true]
      rw [Array.getElem_append_left hr', ← getElem!_pos D.gens r hr']
      exact (hgens r hr').1
    · simp only [regsG, hr', ite_false]
      rw [Array.getElem_append_right (by omega)]
      simp only [Array.getElem_replicate]
      exact Rep.idT hn
  have hprog' : ∀ ins ∈ D.prog, instrRegsLt (regs0 D).size ins := fun ins hins => by
    rw [hsz0]
    exact instrRegsLt_of_instrLtB (hprog ins hins)
  obtain ⟨hsz, hrep⟩ := runSLP_rep hn D.prog (regs0 D) regsG hprog' hregs hok
  have hmem : ∀ r, runSLPG D.prog regsG r ∈ T := runSLPG_mem T D.prog regsG fun r => by
    by_cases hr : r < D.gens.size
    · simp only [regsG, hr, ite_true]
      exact (hgens r hr).2
    · simp only [regsG, hr, ite_false]
      exact T.one_mem
  exact k3_of_checkCore hn (gR := runSLPG D.prog regsG)
    (fun r hr => ⟨hrep r (hsz ▸ hr), hmem r⟩) hcore hcard hm hord

theorem k3_of_check {n : ℕ} {D : Data} (hDn : D.n = n) (hn : n < 2 ^ 32)
    {T : Subgroup (Equiv.Perm (Fin n))} {gG : ℕ → Equiv.Perm (Fin n)}
    (hgens : ∀ l < D.gens.size, Rep n D.gens[l]! (gG l) ∧ gG l ∈ T) (h : check D = true)
    {a m : ℕ} (hcard : Nat.card T = 3 ^ a * m) (hm : ¬ 3 ∣ m) (hord : D.order = 3 ^ a) :
    K3 T := by
  subst hDn
  exact k3_of_check_aux hn hgens h hcard hm hord

end Check

end CFSG.EvenSmallLie.Child3.SelK3
