module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltPerm
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] {k : ℕ} {K : Subgroup (MulAut V)}

private def fxComm {W : Type*} [CommGroup W] (x : MulAut W) : W →* W :=
  MonoidHom.mk' (fun v => x v * v⁻¹) fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

private theorem fxComm_apply {W : Type*} [CommGroup W] (x : MulAut W) (v : W) :
    fxComm x v = x v * v⁻¹ := rfl

private theorem fx_commV_zpowers {W : Type*} [CommGroup W] (x : MulAut W) :
    commV (Subgroup.zpowers x) = (fxComm x).range := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨y, hy, v, rfl⟩
    rw [Subgroup.zpowers_eq_closure] at hy
    induction hy using Subgroup.closure_induction generalizing v with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨v, rfl⟩
    | one =>
      rw [MulAut.one_apply, mul_inv_cancel]
      exact (fxComm x).range.one_mem
    | mul a b _ _ ha hb =>
      have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
        simp [MulAut.mul_apply]
      rw [this]
      exact mul_mem (ha (b v)) (hb v)
    | inv a _ ha =>
      have : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
        simp
      rw [this]
      exact inv_mem (ha (a⁻¹ v))
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, v, rfl⟩

private theorem fxEmb (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) :
    ∃ ι : ↥(G6.coreMod k) →* V, Function.Injective ι ∧ ι.range = commV K ∧
      ∀ (y : K) (u : ↥(G6.coreMod k)),
        ι (G6.coreAct k (θ y : Equiv.Perm (Fin k)) u) = (y : MulAut V) (ι u) := by
  obtain ⟨hinv, β, hsurj, hker, heq⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  let e : ↥(commV K) ≃* ↥(G6.coreMod k) := MulEquiv.ofBijective β ⟨hinj, hsurj⟩
  refine ⟨(commV K).subtype.comp e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact (e.symm u).2
    · intro hv
      exact ⟨e ⟨v, hv⟩, by simp⟩
  · intro y u
    have hp : (y : MulAut V) (e.symm u : V) ∈ commV K := hinv y y.2 _ (e.symm u).2
    have h1 : β ⟨(y : MulAut V) (e.symm u : V), hp⟩ =
        G6.coreAct k (θ y : Equiv.Perm (Fin k)) u := by
      have := heq y (e.symm u) hp
      have h2 : β (e.symm u) = u := e.apply_symm_apply u
      rw [h2] at this
      exact this
    have h3 : e.symm (G6.coreAct k (θ y : Equiv.Perm (Fin k)) u) =
        ⟨(y : MulAut V) (e.symm u : V), hp⟩ := by
      rw [← h1]
      exact e.symm_apply_apply _
    simp [h3]

private def fxUnit {m : ℕ} (a : Fin m) : G6.PermMod m := Multiplicative.ofAdd (Pi.single a 1)

private theorem toAdd_fxUnit {m : ℕ} (a i : Fin m) :
    Multiplicative.toAdd (fxUnit a) i = (Pi.single a 1 : Fin m → ZMod 2) i := rfl

private theorem permAct_fxUnit {m : ℕ} (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    G6.permAct m σ (fxUnit a) = fxUnit (σ a) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, toAdd_fxUnit, Pi.single_apply, Equiv.symm_apply_eq]

private theorem fx_mul_self {m : ℕ} (x : G6.PermMod m) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem fx_inv {m : ℕ} (x : G6.PermMod m) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (fx_mul_self x)

private theorem fxUnit_mul_mem {m : ℕ} (a b : Fin m) :
    fxUnit a * fxUnit b ∈ G6.coreMod m := by
  rw [G6.mem_coreMod]
  simp [toAdd_fxUnit, Finset.sum_add_distrib]
  decide

private def fxPair {m : ℕ} (a b : Fin m) : ↥(G6.coreMod m) :=
  ⟨fxUnit a * fxUnit b, fxUnit_mul_mem a b⟩

private theorem toAdd_fxPair {m : ℕ} (a b i : Fin m) :
    Multiplicative.toAdd ((fxPair a b : ↥(G6.coreMod m)) : G6.PermMod m) i =
      (Pi.single a 1 : Fin m → ZMod 2) i + (Pi.single b 1 : Fin m → ZMod 2) i := rfl

private theorem coreAct_fxPair {m : ℕ} (σ : Equiv.Perm (Fin m)) (a b : Fin m) :
    G6.coreAct m σ (fxPair a b) = fxPair (σ a) (σ b) := by
  apply Subtype.ext
  show G6.permAct m σ (fxUnit a * fxUnit b) = fxUnit (σ a) * fxUnit (σ b)
  rw [map_mul, permAct_fxUnit, permAct_fxUnit]

private theorem fxPair_self {m : ℕ} (a : Fin m) : fxPair a a = 1 :=
  Subtype.ext (fx_mul_self _)

private theorem fxPair_inv {m : ℕ} (a b : Fin m) : (fxPair a b)⁻¹ = fxPair a b :=
  Subtype.ext (fx_inv _)

private theorem fxPair_comm {m : ℕ} (a b : Fin m) : fxPair a b = fxPair b a :=
  Subtype.ext (mul_comm _ _)

private theorem fxPair_mul_fxPair {m : ℕ} (a b c : Fin m) :
    fxPair a c * fxPair b c = fxPair a b := by
  apply Subtype.ext
  show fxUnit a * fxUnit c * (fxUnit b * fxUnit c) = fxUnit a * fxUnit b
  rw [mul_mul_mul_comm, fx_mul_self, mul_one]

private theorem fxPair_mul_trans {m : ℕ} (a b c : Fin m) :
    fxPair a b * fxPair b c = fxPair a c := by
  apply Subtype.ext
  show fxUnit a * fxUnit b * (fxUnit b * fxUnit c) = fxUnit a * fxUnit c
  rw [mul_assoc, ← mul_assoc (fxUnit b), fx_mul_self, one_mul]

private theorem fx_threeCycle {m : ℕ} {σ : Equiv.Perm (Fin m)} (h3 : σ.IsThreeCycle) :
    ∃ a b c : Fin m, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σ a = b ∧ σ b = c ∧ σ c = a ∧
      ∀ i, i ≠ a → i ≠ b → i ≠ c → σ i = i := by
  obtain ⟨a, ha⟩ : σ.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    exact h3.ne_one (Equiv.Perm.support_eq_empty_iff.mp h0)
  have hsupp := (Equiv.Perm.IsThreeCycle.support_eq_iff_mem_support h3).mpr ha
  have hnd := (Equiv.Perm.IsThreeCycle.nodup_iff_mem_support h3).mpr ha
  have hpow : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [h3.orderOf] at this
  have hcyc : σ (σ (σ a)) = a := by
    have := congrArg (fun f : Equiv.Perm (Fin m) => f a) hpow
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil, and_true,
    not_false_eq_true] at hnd
  obtain ⟨⟨h1, h2⟩, h3'⟩ := hnd
  refine ⟨a, σ a, σ (σ a), h1, h2, h3', rfl, rfl, hcyc, fun i hia hib hic => ?_⟩
  have : i ∉ σ.support := by
    rw [hsupp]
    simp [hia, hib, hic]
  exact Equiv.Perm.notMem_support.mp this

private theorem fx_coord {m : ℕ} (σ : Equiv.Perm (Fin m)) (u : ↥(G6.coreMod m)) (i : Fin m) :
    Multiplicative.toAdd ((G6.coreAct m σ u * u⁻¹ : ↥(G6.coreMod m)) : G6.PermMod m) i =
      Multiplicative.toAdd (u : G6.PermMod m) (σ⁻¹ i) +
        Multiplicative.toAdd (u : G6.PermMod m) i := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, G6.coreAct_coe, toAdd_mul,
    toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply]
  rw [ZMod.neg_eq_self_mod_two]

private theorem fx_ext3 {m : ℕ} {a b c : Fin m} {x y : ↥(G6.coreMod m)}
    (hoff : ∀ i, i ≠ a → i ≠ b → i ≠ c →
      Multiplicative.toAdd (x : G6.PermMod m) i = Multiplicative.toAdd (y : G6.PermMod m) i)
    (ha : Multiplicative.toAdd (x : G6.PermMod m) a = Multiplicative.toAdd (y : G6.PermMod m) a)
    (hb : Multiplicative.toAdd (x : G6.PermMod m) b = Multiplicative.toAdd (y : G6.PermMod m) b)
    (hc : Multiplicative.toAdd (x : G6.PermMod m) c = Multiplicative.toAdd (y : G6.PermMod m) c) :
    x = y := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hia : i = a
  · subst hia
    exact ha
  by_cases hib : i = b
  · subst hib
    exact hb
  by_cases hic : i = c
  · subst hic
    exact hc
  exact hoff i hia hib hic

private theorem fx_ne_of_coord {m : ℕ} {x y : ↥(G6.coreMod m)} (i : Fin m)
    (h : Multiplicative.toAdd (x : G6.PermMod m) i ≠ Multiplicative.toAdd (y : G6.PermMod m) i) :
    x ≠ y := fun hxy => h (by rw [hxy])

private theorem fx_key4 : ∀ z1 z2 z3 : ZMod 2, (z3 + z1 = 0 ∧ z1 + z2 = 0 ∧ z2 + z3 = 0) ∨
    (z3 + z1 = 1 ∧ z1 + z2 = 1 ∧ z2 + z3 = 0) ∨ (z3 + z1 = 1 ∧ z1 + z2 = 0 ∧ z2 + z3 = 1) ∨
    (z3 + z1 = 0 ∧ z1 + z2 = 1 ∧ z2 + z3 = 1) := by decide

private theorem fx_ncard_range {m : ℕ} {σ : Equiv.Perm (Fin m)} (h3 : σ.IsThreeCycle) :
    (Set.range fun u : ↥(G6.coreMod m) => G6.coreAct m σ u * u⁻¹).ncard = 4 := by
  obtain ⟨a, b, c, hab, hac, hbc, hσa, hσb, hσc, hσo⟩ := fx_threeCycle h3
  have hia : σ⁻¹ a = c := Equiv.Perm.inv_eq_iff_eq.mpr hσc.symm
  have hib : σ⁻¹ b = a := Equiv.Perm.inv_eq_iff_eq.mpr hσa.symm
  have hic : σ⁻¹ c = b := Equiv.Perm.inv_eq_iff_eq.mpr hσb.symm
  have hio : ∀ i, i ≠ a → i ≠ b → i ≠ c → σ⁻¹ i = i := fun i h1 h2 h3 => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hσo i h1 h2 h3).symm
  have key : ∀ u : ↥(G6.coreMod m), G6.coreAct m σ u * u⁻¹ = 1 ∨
      G6.coreAct m σ u * u⁻¹ = fxPair a b ∨ G6.coreAct m σ u * u⁻¹ = fxPair a c ∨
      G6.coreAct m σ u * u⁻¹ = fxPair b c := by
    intro u
    have hoff : ∀ i, i ≠ a → i ≠ b → i ≠ c → Multiplicative.toAdd
        ((G6.coreAct m σ u * u⁻¹ : ↥(G6.coreMod m)) : G6.PermMod m) i = 0 := by
      intro i h1 h2 h3
      rw [fx_coord, hio i h1 h2 h3]
      exact CharTwo.add_self_eq_zero _
    have hA := fx_coord σ u a
    have hB := fx_coord σ u b
    have hC := fx_coord σ u c
    rw [hia] at hA
    rw [hib] at hB
    rw [hic] at hC
    rcases fx_key4 (Multiplicative.toAdd (u : G6.PermMod m) a)
      (Multiplicative.toAdd (u : G6.PermMod m) b) (Multiplicative.toAdd (u : G6.PermMod m) c)
      with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · left
      refine fx_ext3 (a := a) (b := b) (c := c) (fun i h1 h2 h3 => ?_) ?_ ?_ ?_
      · rw [hoff i h1 h2 h3]
        simp
      · rw [hA, e1]
        simp
      · rw [hB, e2]
        simp
      · rw [hC, e3]
        simp
    · right; left
      refine fx_ext3 (a := a) (b := b) (c := c) (fun i h1 h2 h3 => ?_) ?_ ?_ ?_
      · rw [hoff i h1 h2 h3]
        simp [toAdd_fxPair, h1, h2]
      · rw [hA, e1]
        simp [toAdd_fxPair, hab]
      · rw [hB, e2]
        simp [toAdd_fxPair, hab.symm]
      · rw [hC, e3]
        simp [toAdd_fxPair, hac.symm, hbc.symm]
    · right; right; left
      refine fx_ext3 (a := a) (b := b) (c := c) (fun i h1 h2 h3 => ?_) ?_ ?_ ?_
      · rw [hoff i h1 h2 h3]
        simp [toAdd_fxPair, h1, h3]
      · rw [hA, e1]
        simp [toAdd_fxPair, hac]
      · rw [hB, e2]
        simp [toAdd_fxPair, hab.symm, hbc]
      · rw [hC, e3]
        simp [toAdd_fxPair, hac.symm]
    · right; right; right
      refine fx_ext3 (a := a) (b := b) (c := c) (fun i h1 h2 h3 => ?_) ?_ ?_ ?_
      · rw [hoff i h1 h2 h3]
        simp [toAdd_fxPair, h2, h3]
      · rw [hA, e1]
        simp [toAdd_fxPair, hab.symm, hac.symm]
      · rw [hB, e2]
        simp [toAdd_fxPair, hbc]
      · rw [hC, e3]
        simp [toAdd_fxPair, hbc.symm]
  have hset : (Set.range fun u : ↥(G6.coreMod m) => G6.coreAct m σ u * u⁻¹) =
      {1, fxPair a b, fxPair a c, fxPair b c} := by
    ext w
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      exact key u
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨1, by simp⟩
      · refine ⟨fxPair b c, ?_⟩
        show G6.coreAct m σ (fxPair b c) * (fxPair b c)⁻¹ = _
        rw [coreAct_fxPair, hσb, hσc, fxPair_inv, mul_comm, fxPair_mul_trans, fxPair_comm]
      · refine ⟨fxPair a b, ?_⟩
        show G6.coreAct m σ (fxPair a b) * (fxPair a b)⁻¹ = _
        rw [coreAct_fxPair, hσa, hσb, fxPair_inv, mul_comm, fxPair_mul_trans]
      · refine ⟨fxPair c a, ?_⟩
        show G6.coreAct m σ (fxPair c a) * (fxPair c a)⁻¹ = _
        rw [coreAct_fxPair, hσc, hσa, fxPair_inv, mul_comm, fxPair_mul_trans, fxPair_comm]
  have n1 : (1 : ↥(G6.coreMod m)) ≠ fxPair a b :=
    fx_ne_of_coord a (by simp [toAdd_fxPair, hab])
  have n2 : (1 : ↥(G6.coreMod m)) ≠ fxPair a c :=
    fx_ne_of_coord a (by simp [toAdd_fxPair, hac])
  have n3 : (1 : ↥(G6.coreMod m)) ≠ fxPair b c :=
    fx_ne_of_coord b (by simp [toAdd_fxPair, hbc])
  have n4 : fxPair a b ≠ fxPair a c :=
    fx_ne_of_coord b (by simp [toAdd_fxPair, hab.symm, hbc])
  have n5 : fxPair a b ≠ fxPair b c :=
    fx_ne_of_coord a (by simp [toAdd_fxPair, hab, hac])
  have n6 : fxPair a c ≠ fxPair b c :=
    fx_ne_of_coord a (by simp [toAdd_fxPair, hac, hab])
  rw [hset, Set.ncard_insert_of_notMem (by simp [n1, n2, n3]),
    Set.ncard_insert_of_notMem (by simp [n4, n5]), Set.ncard_pair n6]

private theorem fx_mem_stab {m : ℕ} {σ : alternatingGroup (Fin m)} {c : Fin m} :
    σ ∈ altStabilizer m {c} ↔ (σ : Equiv.Perm (Fin m)) c = c := by
  simp only [altStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, Finset.mem_singleton,
    forall_eq]
  exact Iff.rfl

private def fxWc {m : ℕ} (c : Fin m) : G6.PermMod m :=
  Multiplicative.ofAdd fun i => if i = c then 0 else 1

private theorem toAdd_fxWc {m : ℕ} (c i : Fin m) :
    Multiplicative.toAdd (fxWc c) i = if i = c then 0 else 1 := rfl

private theorem fxWc_mem {m : ℕ} (hm : Odd m) (c : Fin m) : fxWc c ∈ G6.coreMod m := by
  rw [G6.mem_coreMod]
  simp only [toAdd_fxWc]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c),
    Finset.sum_congr rfl (g := fun _ => (1 : ZMod 2))
      (fun i hi => by simp [Finset.ne_of_mem_erase hi]),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have h : Even (m - 1) := by
    obtain ⟨n, rfl⟩ := hm
    exact ⟨n, by omega⟩
  simpa using (ZMod.natCast_eq_zero_iff_even (n := m - 1)).mpr h

private theorem fxWc_ne_one {m : ℕ} (hm : 2 ≤ m) (c : Fin m) : fxWc c ≠ 1 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨i, hi⟩ := exists_ne c
  intro h
  have := congrArg (fun x : G6.PermMod m => Multiplicative.toAdd x i) h
  simp [toAdd_fxWc, hi] at this

private theorem permAct_fxWc {m : ℕ} {σ : Equiv.Perm (Fin m)} {c : Fin m} (hσ : σ c = c) :
    G6.permAct m σ (fxWc c) = fxWc c := by
  apply Multiplicative.toAdd.injective
  funext i
  have : σ⁻¹ i = c ↔ i = c := by
    rw [Equiv.Perm.inv_eq_iff_eq, hσ]
  simp only [G6.permAct_apply, toAdd_fxWc]
  exact if_congr this rfl rfl

private theorem fx_exists_two_off {m : ℕ} (hm : 5 ≤ m) (i j c : Fin m) :
    ∃ l n : Fin m, l ≠ n ∧ l ≠ i ∧ l ≠ j ∧ l ≠ c ∧ n ≠ i ∧ n ≠ j ∧ n ≠ c := by
  have hcard : 1 < ({i, j, c} : Finset (Fin m))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_three (a := i) (b := j) (c := c)
    omega
  obtain ⟨l, hl, n, hn, hln⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hl hn
  exact ⟨l, n, hln, hl.1, hl.2.1, hl.2.2, hn.1, hn.2.1, hn.2.2⟩

private theorem fx_exists_stab {m : ℕ} (hm : 5 ≤ m) {c i j : Fin m} (hi : i ≠ c) (hj : j ≠ c) :
    ∃ σ : alternatingGroup (Fin m), (σ : Equiv.Perm (Fin m)) c = c ∧
      (σ : Equiv.Perm (Fin m)) i = j := by
  by_cases hij : i = j
  · exact ⟨1, rfl, hij⟩
  obtain ⟨l, n, hln, hli, hlj, hlc, hni, hnj, hnc⟩ := fx_exists_two_off hm i j c
  refine ⟨⟨Equiv.swap i j * Equiv.swap l n, ?_⟩, ?_, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hij, hln]
  · show (Equiv.swap i j) ((Equiv.swap l n) c) = c
    rw [Equiv.swap_apply_of_ne_of_ne hlc.symm hnc.symm,
      Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm]
  · show (Equiv.swap i j) ((Equiv.swap l n) i) = j
    rw [Equiv.swap_apply_of_ne_of_ne hli.symm hni.symm, Equiv.swap_apply_left]

private theorem fx_eq_one_of_off {m : ℕ} {c : Fin m} {v : G6.PermMod m} (hv : v ∈ G6.coreMod m)
    (h : ∀ l, l ≠ c → Multiplicative.toAdd v l = 0) : v = 1 := by
  have hc : Multiplicative.toAdd v c = 0 := by
    have := G6.mem_coreMod.mp hv
    rwa [Finset.sum_eq_single c (fun l _ hl => h l hl)
      (fun hc => absurd (Finset.mem_univ c) hc)] at this
  apply Multiplicative.toAdd.injective
  funext l
  by_cases hl : l = c
  · subst hl
    simpa using hc
  · simpa using h l hl

private theorem fx_mem_of_pairs {m : ℕ} {M : Subgroup (G6.PermMod m)} {c i0 : Fin m}
    (h : ∀ i : Fin m, i ≠ c → fxUnit i0 * fxUnit i ∈ M) {u : G6.PermMod m}
    (hu : u ∈ G6.coreMod m) (huc : Multiplicative.toAdd u c = 0) : u ∈ M := by
  have hprod : u = ∏ i : Fin m, (fxUnit i0 * fxUnit i) ^ (Multiplicative.toAdd u i).val := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_prod, toAdd_pow, Finset.sum_apply, Pi.smul_apply, toAdd_mul, Pi.add_apply]
    simp only [toAdd_fxUnit, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_add, Finset.sum_add_distrib]
    have h1 : ∑ i, Multiplicative.toAdd u i * (Pi.single i 1 : Fin m → ZMod 2) j =
        Multiplicative.toAdd u j := by
      simp [Pi.single_apply]
    have h2 : ∑ i, Multiplicative.toAdd u i * (Pi.single i0 1 : Fin m → ZMod 2) j = 0 := by
      rw [← Finset.sum_mul, G6.mem_coreMod.mp hu, zero_mul]
    rw [h1, h2, zero_add]
  rw [hprod]
  refine M.prod_mem fun i _ => ?_
  by_cases hic : i = c
  · subst hic
    rw [huc, ZMod.val_zero, pow_zero]
    exact M.one_mem
  · exact M.pow_mem (h i hic) _

private theorem fx_eq_of_fixed {m : ℕ} (hm : 5 ≤ m) (hodd : Odd m) {c : Fin m}
    {u : ↥(G6.coreMod m)}
    (hfix : ∀ σ : alternatingGroup (Fin m), (σ : Equiv.Perm (Fin m)) c = c →
      G6.coreAct m (σ : Equiv.Perm (Fin m)) u = u) :
    u = 1 ∨ (u : G6.PermMod m) = fxWc c := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i1, hi1⟩ := exists_ne c
  have hconst : ∀ l, l ≠ c → Multiplicative.toAdd (u : G6.PermMod m) l =
      Multiplicative.toAdd (u : G6.PermMod m) i1 := by
    intro l hl
    obtain ⟨σ, hσc, hσi⟩ := fx_exists_stab hm hi1 hl
    have h1 := congrArg (fun x : ↥(G6.coreMod m) => Multiplicative.toAdd (x : G6.PermMod m) l)
      (hfix σ hσc)
    simp only [G6.coreAct_coe, G6.permAct_apply] at h1
    have h2 : (σ : Equiv.Perm (Fin m))⁻¹ l = i1 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hσi.symm
    rw [h2] at h1
    exact h1.symm
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
    (Multiplicative.toAdd (u : G6.PermMod m) i1) with hd | hd
  · left
    apply Subtype.ext
    exact fx_eq_one_of_off u.2 (fun l hl => by rw [hconst l hl, hd])
  · right
    have hv : (u : G6.PermMod m) * fxWc c = 1 := by
      refine fx_eq_one_of_off (c := c) (mul_mem u.2 (fxWc_mem hodd c)) (fun l hl => ?_)
      have h1 : (if l = c then (0 : ZMod 2) else 1) = 1 := by simp [hl]
      rw [toAdd_mul, Pi.add_apply, hconst l hl, hd, toAdd_fxWc, h1]
      decide
    rw [eq_inv_of_mul_eq_one_left hv, fx_inv]

theorem card_commV_threeCycle (hk : 3 ≤ k) (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) (hsplit : commV K ⊔ fixV K = ⊤)
    {x : MulAut V} (hx : x ∈ K)
    (h3 : ((θ ⟨x, hx⟩ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)).IsThreeCycle) :
    Nat.card ↥(commV (Subgroup.zpowers x)) = 4 := by
  have _ := hk
  obtain ⟨ι, hinj, hrange, heq⟩ := fxEmb θ h
  have h2 : ((fxComm x).range : Set V) = ι '' Set.range (fun u : ↥(G6.coreMod k) =>
      G6.coreAct k ((θ ⟨x, hx⟩ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) u * u⁻¹) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      have hv : v ∈ commV K ⊔ fixV K := by
        rw [hsplit]
        trivial
      obtain ⟨e, he, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
      obtain ⟨u, rfl⟩ : e ∈ ι.range := by
        rw [hrange]
        exact he
      have hc1 : fxComm x c = 1 := by
        rw [fxComm_apply, mem_fixV.mp hc x hx, mul_inv_cancel]
      refine ⟨_, ⟨u, rfl⟩, ?_⟩
      rw [map_mul (fxComm x), hc1, mul_one, fxComm_apply, map_mul, map_inv, heq ⟨x, hx⟩ u]
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨ι u, ?_⟩
      rw [fxComm_apply, map_mul, map_inv, heq ⟨x, hx⟩ u]
  rw [fx_commV_zpowers]
  show Nat.card ↥((fxComm x).range : Set V) = 4
  rw [Nat.card_coe_set_eq, h2, Set.ncard_image_of_injective _ hinj]
  exact fx_ncard_range h3

theorem exists_fixed_pair_of_natural (hk : Odd k) (hk5 : 5 ≤ k)
    (θ : K ≃* alternatingGroup (Fin k)) (h : IsNatSectionWith (altAct k) θ (commV K) ⊥)
    {N : Subgroup (MulAut V)} (hNK : N ≤ K) (c : Fin k)
    (hN : (N.subgroupOf K).map θ.toMonoidHom = altStabilizer k {c}) :
    ∃ w : V, w ≠ 1 ∧ w ∈ commV N ∧ w ∈ fixV N ∧
      ∀ u ∈ commV K, u ∈ fixV N → u = 1 ∨ u = w := by
  obtain ⟨ι, hinj, hrange, heq⟩ := fxEmb θ h
  have hfix : ∀ y : K, (y : MulAut V) ∈ N →
      ((θ y : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) c = c := by
    intro y hy
    have : θ y ∈ altStabilizer k {c} := by
      rw [← hN]
      exact ⟨y, hy, rfl⟩
    exact fx_mem_stab.mp this
  have hlift : ∀ σ : alternatingGroup (Fin k), (σ : Equiv.Perm (Fin k)) c = c →
      ∃ y : K, (y : MulAut V) ∈ N ∧ θ y = σ := by
    intro σ hσ
    have : σ ∈ (N.subgroupOf K).map θ.toMonoidHom := by
      rw [hN]
      exact fx_mem_stab.mpr hσ
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨y, hy, rfl⟩
  have hpair : ∀ i i0 : Fin k, i ≠ c → i0 ≠ c → ι (fxPair i0 i) ∈ commV N := by
    intro i i0 hi hi0
    by_cases hii : i0 = i
    · subst hii
      rw [fxPair_self, map_one]
      exact one_mem _
    obtain ⟨σ, hσc, hσi⟩ := fx_exists_stab (by omega : 5 ≤ k) hi hi0
    obtain ⟨y, hyN, hyσ⟩ := hlift σ hσc
    have key := heq y (fxPair i c)
    rw [hyσ, coreAct_fxPair, hσc, hσi] at key
    refine Subgroup.subset_closure ⟨y, hyN, ι (fxPair i c), ?_⟩
    rw [← key, ← map_inv, fxPair_inv, ← map_mul, fxPair_mul_fxPair]
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i0, hi0⟩ := exists_ne c
  refine ⟨ι ⟨fxWc c, fxWc_mem hk c⟩, ?_, ?_, ?_, ?_⟩
  · intro h1
    have := hinj (h1.trans (map_one ι).symm)
    exact fxWc_ne_one (by omega) c (congrArg Subtype.val this)
  · have hM : fxWc c ∈ ((commV N).comap ι).map (G6.coreMod k).subtype := by
      refine fx_mem_of_pairs (c := c) (i0 := i0) (fun i hi => ?_) (fxWc_mem hk c) ?_
      · exact ⟨fxPair i0 i, hpair i i0 hi hi0, rfl⟩
      · simp [toAdd_fxWc]
    obtain ⟨y, hy, hyw⟩ := hM
    have : y = ⟨fxWc c, fxWc_mem hk c⟩ := Subtype.ext hyw
    rw [← this]
    exact hy
  · intro y hy
    have := heq ⟨y, hNK hy⟩ ⟨fxWc c, fxWc_mem hk c⟩
    rw [← show ((⟨y, hNK hy⟩ : K) : MulAut V) = y from rfl, ← this]
    congr 1
    exact Subtype.ext (permAct_fxWc (hfix ⟨y, hNK hy⟩ hy))
  · intro u hu hufix
    obtain ⟨u', rfl⟩ : u ∈ ι.range := by
      rw [hrange]
      exact hu
    have hfx : ∀ σ : alternatingGroup (Fin k), (σ : Equiv.Perm (Fin k)) c = c →
        G6.coreAct k (σ : Equiv.Perm (Fin k)) u' = u' := by
      intro σ hσ
      obtain ⟨y, hyN, rfl⟩ := hlift σ hσ
      apply hinj
      rw [heq y u']
      exact mem_fixV.mp hufix y hyN
    rcases fx_eq_of_fixed (by omega) hk hfx with h1 | h1
    · left
      rw [h1, map_one]
    · right
      congr 1
      exact Subtype.ext h1

theorem commV_subgroup_eq_bot_or_top_of_natural (hk : Odd k) (hk5 : 5 ≤ k)
    (θ : K ≃* alternatingGroup (Fin k)) (h : IsNatSectionWith (altAct k) θ (commV K) ⊥)
    {A : Subgroup V} (hA : ∀ x ∈ K, ∀ a ∈ A, (x : MulAut V) a ∈ A) (hle : A ≤ commV K) :
    A = ⊥ ∨ A = commV K := by
  obtain ⟨ι, hinj, hrange, heq⟩ := fxEmb θ h
  have hinv : ∀ σ ∈ alternatingGroup (Fin k), ∀ u ∈ A.comap ι,
      G6.coreAct k σ u ∈ A.comap ι := by
    intro σ hσ u hu
    have hy : (θ (θ.symm ⟨σ, hσ⟩) : Equiv.Perm (Fin k)) = σ := by
      rw [θ.apply_symm_apply]
    have h1 := heq (θ.symm ⟨σ, hσ⟩) u
    rw [hy] at h1
    rw [Subgroup.mem_comap, h1]
    exact hA _ (θ.symm ⟨σ, hσ⟩).2 _ hu
  rcases coreMod_subgroup_eq_bot_or_top hk hk5 (A.comap ι) hinv with h0 | h1
  · left
    refine (Subgroup.eq_bot_iff_forall A).mpr fun a ha => ?_
    obtain ⟨u, rfl⟩ : a ∈ ι.range := by rw [hrange]; exact hle ha
    have hu : u ∈ A.comap ι := ha
    rw [h0] at hu
    rw [Subgroup.mem_bot.mp hu, map_one]
  · right
    refine le_antisymm hle fun e he => ?_
    obtain ⟨u, rfl⟩ : e ∈ ι.range := by rw [hrange]; exact he
    have hu : u ∈ A.comap ι := by rw [h1]; trivial
    exact hu

theorem fix_commV_of_commute_natural (hV : ∀ v : V, v ^ 2 = 1) (hk : Odd k) (hk5 : 5 ≤ k)
    (θ : K ≃* alternatingGroup (Fin k)) (h : IsNatSectionWith (altAct k) θ (commV K) ⊥)
    {t : MulAut V} (ht : t ^ 2 = 1) (hc : ∀ y ∈ K, t * y = y * t) :
    ∀ e ∈ commV K, t e = e := by
  have hcomm : ∀ y ∈ K, ∀ v : V, t (y v) = y (t v) := by
    intro y hy v
    have := congrArg (fun f : MulAut V => f v) (hc y hy)
    simpa [MulAut.mul_apply] using this
  have htE : ∀ e ∈ commV K, t e ∈ commV K := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨y, hy, v, rfl⟩ := hw
      rw [map_mul, map_inv, hcomm y hy v]
      exact Subgroup.subset_closure ⟨y, hy, t v, rfl⟩
    | one => rw [map_one]; exact one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have htt : ∀ v : V, t (t v) = v := by
    intro v
    have := congrArg (fun f : MulAut V => f v) ht
    simpa [pow_two, MulAut.mul_apply] using this
  have hinv2 : ∀ v : V, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)
  have hAK : ∀ x ∈ K, ∀ a ∈ (commV K).map (fxComm t), (x : MulAut V) a ∈
      (commV K).map (fxComm t) := by
    rintro y hy _ ⟨e, he, rfl⟩
    refine ⟨y e, h.1 y hy e he, ?_⟩
    rw [fxComm_apply, fxComm_apply, map_mul, map_inv, hcomm y hy e]
  have hAle : (commV K).map (fxComm t) ≤ commV K := by
    rintro _ ⟨e, he, rfl⟩
    rw [fxComm_apply]
    exact mul_mem (htE e he) (inv_mem he)
  rcases commV_subgroup_eq_bot_or_top_of_natural hk hk5 θ h hAK hAle with h0 | h1
  · intro e he
    have : fxComm t e ∈ (commV K).map (fxComm t) := ⟨e, he, rfl⟩
    rw [h0, Subgroup.mem_bot, fxComm_apply, mul_inv_eq_one] at this
    exact this
  · intro e he
    have heA : e ∈ (commV K).map (fxComm t) := by rw [h1]; exact he
    obtain ⟨e', he', rfl⟩ := heA
    rw [fxComm_apply, map_mul, map_inv, htt, hinv2 (t e'), hinv2 e']
    exact mul_comm _ _

end CFSG.CGT.PushingUpLit.CGT6
