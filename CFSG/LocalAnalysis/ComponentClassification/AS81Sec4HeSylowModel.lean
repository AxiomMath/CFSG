module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open Subgroup CFSG.Open

section Dihedral

variable {T : Type*} [Group T] {k : ℕ} [NeZero k] {w s : T}

theorem pow_val_add_of_pow_eq_one (hw : w ^ k = 1) (i j : ZMod k) :
    w ^ (i + j).val = w ^ i.val * w ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add]

theorem pow_val_mul_eq_of_conj (hw : w ^ k = 1) (hs : s * w * s⁻¹ = w⁻¹) (i : ZMod k) :
    w ^ i.val * s = s * w ^ (-i).val := by
  have h : s * w ^ (-i).val * s⁻¹ = w ^ i.val := by
    rw [← conj_pow, hs, inv_pow]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_val_add_of_pow_eq_one hw, neg_add_cancel, ZMod.val_zero, pow_zero]
  rw [← h, inv_mul_cancel_right]

theorem pow_val_mul_mul_pow_val (hw : w ^ k = 1) (hs : s * w * s⁻¹ = w⁻¹) (i j : ZMod k) :
    w ^ i.val * (s * w ^ j.val) = s * w ^ (j - i).val := by
  rw [← mul_assoc, pow_val_mul_eq_of_conj hw hs, mul_assoc, ← pow_val_add_of_pow_eq_one hw,
    neg_add_eq_sub]

theorem mul_pow_val_mul_mul_pow_val (hw : w ^ k = 1) (hs : s * w * s⁻¹ = w⁻¹) (i j : ZMod k) :
    s * w ^ i.val * (s * w ^ j.val) = s * s * w ^ (j - i).val := by
  rw [mul_assoc, pow_val_mul_mul_pow_val hw hs, ← mul_assoc]

@[expose] def dihedralHom (hw : w ^ k = 1) (hs : s * s = 1) (hsw : s * w * s⁻¹ = w⁻¹) :
    DihedralGroup k →* T where
  toFun
    | .r i => w ^ i.val
    | .sr i => s * w ^ i.val
  map_one' := by
    change w ^ (0 : ZMod k).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · exact pow_val_add_of_pow_eq_one hw i j
    · exact (pow_val_mul_mul_pow_val hw hsw i j).symm
    · change s * w ^ (i + j).val = s * w ^ i.val * w ^ j.val
      rw [mul_assoc, pow_val_add_of_pow_eq_one hw]
    · change w ^ (j - i).val = s * w ^ i.val * (s * w ^ j.val)
      rw [mul_pow_val_mul_mul_pow_val hw hsw, hs, one_mul]

end Dihedral

section Quotient

variable {H : Type} [Group H] [Finite H]

theorem exists_dihedral_quotient {X Q : Subgroup H} {r s : H} {k : ℕ} [NeZero k]
    (hQX : Q ≤ X) (hn : X ≤ normalizer (Q : Set H)) (hcard : Nat.card X = 2 * k * Nat.card Q)
    (hr : r ∈ X) (hs : s ∈ X) (hrk : r ^ k ∈ Q) (hs2 : s * s ∈ Q) (hsr : s * r * (s * r) ∈ Q)
    (hrne : ∀ i, 0 < i → i < k → r ^ i ∉ Q) (hsne : ∀ i, i < k → s * r ^ i ∉ Q) :
    ∃ φ : ↥X →* DihedralGroup k, Function.Surjective φ ∧ φ.ker = Q.subgroupOf X := by
  have hN : (Q.subgroupOf X).Normal := ⟨fun a ha b => by
    rw [mem_subgroupOf] at ha ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hn b.2) a).mp ha⟩
  let π := QuotientGroup.mk' (Q.subgroupOf X)
  have hmem : ∀ x : ↥X, π x = 1 ↔ (x : H) ∈ Q := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', mem_subgroupOf]
  have hw : π ⟨r, hr⟩ ^ k = 1 := by
    rw [← map_pow, hmem]
    simpa using hrk
  have ht : π ⟨s, hs⟩ * π ⟨s, hs⟩ = 1 := by
    rw [← map_mul, hmem]
    exact hs2
  have htw : π ⟨s, hs⟩ * π ⟨r, hr⟩ * (π ⟨s, hs⟩)⁻¹ = (π ⟨r, hr⟩)⁻¹ := by
    have h1 : π ⟨s, hs⟩ * π ⟨r, hr⟩ * (π ⟨s, hs⟩ * π ⟨r, hr⟩) = 1 := by
      rw [← map_mul, ← map_mul, hmem]
      exact hsr
    rw [inv_eq_of_mul_eq_one_right ht]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc (π ⟨s, hs⟩ * π ⟨r, hr⟩)]; exact h1)
  let ψ := dihedralHom hw ht htw
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro (i | i) hi
    · rw [MonoidHom.mem_ker] at hi
      change π ⟨r, hr⟩ ^ i.val = 1 at hi
      rw [← map_pow, hmem] at hi
      rcases Nat.eq_zero_or_pos i.val with h0 | h0
      · rw [mem_bot, (ZMod.val_eq_zero i).mp h0]
        rfl
      · exact absurd (by simpa using hi) (hrne i.val h0 (ZMod.val_lt i))
    · rw [MonoidHom.mem_ker] at hi
      change π ⟨s, hs⟩ * π ⟨r, hr⟩ ^ i.val = 1 at hi
      rw [← map_pow, ← map_mul, hmem] at hi
      exact absurd (by simpa using hi) (hsne i.val (ZMod.val_lt i))
  have hcardq : Nat.card (↥X ⧸ Q.subgroupOf X) = 2 * k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf X)
    rw [Nat.card_congr (subgroupOfEquivOfLe hQX).toEquiv, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have hbij : Function.Bijective ψ :=
    hinj.bijective_of_nat_card_le (by rw [hcardq, DihedralGroup.nat_card])
  let e := MulEquiv.ofBijective ψ hbij
  refine ⟨e.symm.toMonoidHom.comp π, e.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

end Quotient

section Facts

variable {H : Type} [Group H]

@[expose] def CommZ (z x y : H) : Prop := x * y = y * x ∨ x * y = y * x * z

@[expose] def setYP (X : Subgroup H) (z x : H) : Set H :=
  {y | y ∈ X ∧ (y * y = 1 ∨ y * y = z) ∧ CommZ z x y}

@[expose] def GoodQ (X : Subgroup H) (z x : H) : Prop :=
  Nat.card (setYP X z x) < 128 ∨
    (Nat.card (setYP X z x) = 128 ∧ ∃ y ∈ setYP X z x, ∃ y' ∈ setYP X z x, ¬ CommZ z y y')

@[expose] def badQ (X Q : Subgroup H) (z : H) : Set H :=
  {x | x ∈ X ∧ x ∉ Q ∧ (x * x = 1 ∨ x * x = z) ∧ ¬ GoodQ X z x}

@[expose] def setIP (X : Subgroup H) (x : H) : Set H := {y | y ∈ X ∧ y * y = 1 ∧ x * y = y * x}

structure SylFacts (X Q E F U : Subgroup H) (z r s : H) (k : ℕ) : Prop where
  cardX : Nat.card X = 2 * k * 128
  cardQ : Nat.card Q = 128
  cardE : Nat.card E = 64
  cardF : Nat.card F = 64
  cardU : Nat.card U = 16
  QX : Q ≤ X
  EX : E ≤ X
  FX : F ≤ X
  UQ : U ≤ Q
  zQ : z ∈ Q
  rX : r ∈ X
  sX : s ∈ X
  normQ : X ≤ normalizer (Q : Set H)
  normE : Q ≤ normalizer (E : Set H)
  normF : Q ≤ normalizer (F : Set H)
  z2 : z * z = 1
  z1 : z ≠ 1
  zc : ∀ x ∈ X, x * z = z * x
  cen : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x = 1 ∨ x = z
  Qsq : ∀ x ∈ Q, x * x = 1 ∨ x * x = z
  Qcen : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = z
  Qnab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x
  Esq : ∀ x ∈ E, x * x = 1
  Ecomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  Fsq : ∀ x ∈ F, x * x = 1
  Fcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  Usq : ∀ x ∈ U, x * x = 1
  Ucomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x
  EF : E ≠ F
  rk : r ^ k ∈ Q
  s2 : s * s ∈ Q
  sr2 : s * r * (s * r) ∈ Q
  rne : ∀ i, 0 < i → i < k → r ^ i ∉ Q
  sne : ∀ i, i < k → s * r ^ i ∉ Q
  uniqQ : Nat.card (badQ X Q z) < 64
  uniqE : ∀ x ∈ X, x * x = 1 → x ≠ 1 → x ∉ E → x ∉ F → Nat.card (setIP X x) < 64

structure SylModel (X Q E F U : Subgroup H) (z : H) (k : ℕ) : Prop where
  QX : Q ≤ X
  EX : E ≤ X
  FX : F ≤ X
  UQ : U ≤ Q
  cardQ : Nat.card Q = 2 ^ 7
  cardE : Nat.card E = 2 ^ 6
  cardF : Nat.card F = 2 ^ 6
  cardU : Nat.card U = 16
  order_z : orderOf z = 2
  extraspecial : CFSG.IsExtraspecialPGroup 2 Q
  center_Q : centerIn Q = zpowers z
  center_X : centerIn X = zpowers z
  unique : ∀ Q' : Subgroup H, Q' ≤ X → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
    (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q
  elemE : IsElemAbelian 2 E
  elemF : IsElemAbelian 2 F
  EF : E ≠ F
  uniqE : ∀ V : Subgroup H, V ≤ X → IsElemAbelian 2 V → Nat.card V = 2 ^ 6 → V = E ∨ V = F
  normE : Q ≤ normalizer (E : Set H)
  normF : Q ≤ normalizer (F : Set H)
  quot : ∃ φ : ↥X →* DihedralGroup k, Function.Surjective φ ∧ φ.ker = Q.subgroupOf X
  elemU : IsElemAbelian 2 U

theorem mem_centerIn' {K : Subgroup H} {x : H} :
    x ∈ centerIn K ↔ x ∈ K ∧ ∀ y ∈ K, x * y = y * x := by
  simp only [centerIn, mem_inf, mem_centralizer_iff]
  exact and_congr_right fun _ => forall₂_congr fun _ _ => eq_comm

theorem le_or_le_of_forall_mem_or_mem {V E F : Subgroup H} (h : ∀ x ∈ V, x ∈ E ∨ x ∈ F) :
    V ≤ E ∨ V ≤ F := by
  by_contra hc
  obtain ⟨hVE, hVF⟩ := not_or.mp hc
  obtain ⟨a, haV, haE⟩ := IsConcreteLE.not_le_iff_exists.mp hVE
  obtain ⟨b, hbV, hbF⟩ := IsConcreteLE.not_le_iff_exists.mp hVF
  have haF : a ∈ F := (h a haV).resolve_left haE
  have hbE : b ∈ E := (h b hbV).resolve_right hbF
  rcases h (a * b) (V.mul_mem haV hbV) with hab | hab
  · exact haE (by simpa using E.mul_mem hab (E.inv_mem hbE))
  · exact hbF (by simpa using F.mul_mem (F.inv_mem haF) hab)

namespace SylFacts

variable {X Q E F U : Subgroup H} {z r s : H} {k : ℕ}

theorem orderOf_z (hf : SylFacts X Q E F U z r s k) : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact hf.z2) hf.z1

theorem mem_zpowers_z_iff (hf : SylFacts X Q E F U z r s k) {x : H} :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hf.z2]
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · left
      rw [← Int.mul_ediv_add_emod m 2, h, add_zero, zpow_mul, h2, one_zpow]
    · right
      rw [← Int.mul_ediv_add_emod m 2, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers z

theorem mem_zpowers_of_mul_self (hf : SylFacts X Q E F U z r s k) {x : H}
    (h : x * x = 1 ∨ x * x = z) : x * x ∈ zpowers z :=
  hf.mem_zpowers_z_iff.mpr h

theorem comm_mem (hf : SylFacts X Q E F U z r s k) {x y : H} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  have hzc : ∀ w ∈ zpowers z, w * y = y * w := by
    intro w hw
    rcases hf.mem_zpowers_z_iff.mp hw with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hf.zc y (hf.QX hy)).symm
  have ha := hf.mem_zpowers_of_mul_self (hf.Qsq x hx)
  have hb := hf.mem_zpowers_of_mul_self (hf.Qsq y hy)
  have hc := hf.mem_zpowers_of_mul_self (hf.Qsq _ (Q.mul_mem hx hy))
  have e : x * y * x⁻¹ * y⁻¹ = x * y * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hzc _ (inv_mem ha)]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem hc (inv_mem ha)) (inv_mem hb)

theorem centerIn_Q (hf : SylFacts X Q E F U z r s k) : centerIn Q = zpowers z := by
  ext x
  rw [mem_centerIn', hf.mem_zpowers_z_iff]
  constructor
  · rintro ⟨hx, hxc⟩
    exact hf.Qcen x hx hxc
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, fun y _ => by rw [one_mul, mul_one]⟩
    · exact ⟨hf.zQ, fun y hy => (hf.zc y (hf.QX hy)).symm⟩

theorem centerIn_X (hf : SylFacts X Q E F U z r s k) : centerIn X = zpowers z := by
  ext x
  rw [mem_centerIn', hf.mem_zpowers_z_iff]
  constructor
  · rintro ⟨hx, hxc⟩
    exact hf.cen x hx hxc
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, fun y _ => by rw [one_mul, mul_one]⟩
    · exact ⟨hf.QX hf.zQ, fun y hy => (hf.zc y hy).symm⟩

theorem extraspecial [Finite H] (hf : SylFacts X Q E F U z r s k) :
    CFSG.IsExtraspecialPGroup 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 Q := IsPGroup.of_card (n := 7) (by rw [hf.cardQ]; norm_num)
  refine (CFSG.LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall hP hf.zQ
    hf.orderOf_z (fun x hx => ?_) (fun x hx y hy => ?_) (fun x hx => ?_) hf.Qnab).1
  · constructor
    · intro hc
      exact hf.mem_zpowers_z_iff.mpr (hf.Qcen x hx hc)
    · intro hz y hy
      rcases hf.mem_zpowers_z_iff.mp hz with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (hf.zc y (hf.QX hy)).symm
  · rw [commutatorElement_def]
    exact hf.comm_mem hx hy
  · rw [sq]
    exact hf.mem_zpowers_of_mul_self (hf.Qsq x hx)

theorem unique' [Finite H] (hf : SylFacts X Q E F U z r s k) {Q' : Subgroup H} (hQ'X : Q' ≤ X)
    (hcard : Nat.card Q' = 128) (hsq : ∀ x ∈ Q', x ^ 2 ∈ zpowers z)
    (hcomm : ∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) : Q' = Q := by
  by_contra hne
  have hcz : ∀ {x y : H}, x ∈ Q' → y ∈ Q' → CommZ z x y := by
    intro x y hx hy
    rcases hf.mem_zpowers_z_iff.mp (hcomm x hx y hy) with h | h
    · left
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [h, one_mul]
    · right
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = z * (y * x) := by rw [h]
        _ = y * x * z := (hf.zc _ (X.mul_mem (hQ'X hy) (hQ'X hx))).symm
  have hsq' : ∀ {y : H}, y ∈ Q' → y * y = 1 ∨ y * y = z := fun hy => by
    rw [← sq]
    exact hf.mem_zpowers_z_iff.mp (hsq _ hy)
  have hbad : (Q' : Set H) \ Q ⊆ badQ X Q z := by
    rintro x ⟨hx, hxQ⟩
    refine ⟨hQ'X hx, hxQ, hsq' hx, ?_⟩
    have hsub : (Q' : Set H) ⊆ setYP X z x := fun y hy => ⟨hQ'X hy, hsq' hy, hcz hx hy⟩
    have hle : (Q' : Set H).ncard ≤ (setYP X z x).ncard := Set.ncard_le_ncard hsub
    have e2 : (Q' : Set H).ncard = 128 := hcard
    rintro (hlt | ⟨heq, y, hy, y', hy', hnc⟩)
    · have e1 : (setYP X z x).ncard < 128 := hlt
      omega
    · have e1 : (setYP X z x).ncard = 128 := heq
      have hE : (Q' : Set H) = setYP X z x := Set.eq_of_subset_of_ncard_le hsub (by omega)
      rw [← hE] at hy hy'
      exact hnc (hcz hy hy')
  have hinter : Nat.card (Q' ⊓ Q : Subgroup H) ≤ 64 := by
    have hne' : Nat.card (Q' ⊓ Q : Subgroup H) ≠ 128 := by
      intro h
      have h1 : Q' ⊓ Q = Q' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      have h2 : Q' ≤ Q := h1 ▸ inf_le_right
      exact hne (Subgroup.eq_of_le_of_card_ge h2 (by rw [hf.cardQ, hcard]))
    have hdvd : Nat.card (Q' ⊓ Q : Subgroup H) ∣ 2 ^ 7 := by
      rw [show (2 : ℕ) ^ 7 = 128 by norm_num, ← hcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hj'] at hne' ⊢
    have hj7 : j ≠ 7 := fun h => hne' (by rw [h]; norm_num)
    calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 64 := by norm_num
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (Q' : Set H) (Q : Set H)
  have h1 : ((Q' : Set H) ∩ Q).ncard = Nat.card (Q' ⊓ Q : Subgroup H) := by
    rw [← coe_inf]
    rfl
  have h2 : (Q' : Set H).ncard = 128 := hcard
  have h3 : ((Q' : Set H) \ Q).ncard ≤ (badQ X Q z).ncard := Set.ncard_le_ncard hbad
  have h4 : (badQ X Q z).ncard < 64 := hf.uniqQ
  omega

theorem uniqE' [Finite H] (hf : SylFacts X Q E F U z r s k) {V : Subgroup H} (hVX : V ≤ X)
    (hV : IsElemAbelian 2 V) (hcard : Nat.card V = 64) : V = E ∨ V = F := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := isMulCommutative_iff_of_setLike.mp hV.1
  have hsub : ∀ x ∈ V, x ∈ E ∨ x ∈ F := by
    intro x hx
    by_contra hc
    obtain ⟨hxE, hxF⟩ := not_or.mp hc
    have hx1 : x ≠ 1 := fun h => hxE (h ▸ one_mem E)
    have hx2 : x * x = 1 := by rw [← sq]; exact hV.2 x hx
    have hlt : (setIP X x).ncard < 64 := hf.uniqE x (hVX hx) hx2 hx1 hxE hxF
    have hsubV : (V : Set H) ⊆ setIP X x := fun y hy =>
      ⟨hVX hy, by rw [← sq]; exact hV.2 y hy, hcomm x hx y hy⟩
    have hle := Set.ncard_le_ncard hsubV
    have h64 : (V : Set H).ncard = 64 := hcard
    omega
  rcases le_or_le_of_forall_mem_or_mem hsub with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, hf.cardE]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, hf.cardF]))

theorem isElemAbelian {K : Subgroup H} (hsq : ∀ x ∈ K, x * x = 1)
    (hc : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) : IsElemAbelian 2 K :=
  ⟨isMulCommutative_iff_of_setLike.mpr hc, fun x hx => by rw [sq]; exact hsq x hx⟩

theorem toModel [Finite H] [NeZero k] (hf : SylFacts X Q E F U z r s k) :
    SylModel X Q E F U z k where
  QX := hf.QX
  EX := hf.EX
  FX := hf.FX
  UQ := hf.UQ
  cardQ := by rw [hf.cardQ]; norm_num
  cardE := by rw [hf.cardE]; norm_num
  cardF := by rw [hf.cardF]; norm_num
  cardU := hf.cardU
  order_z := hf.orderOf_z
  extraspecial := hf.extraspecial
  center_Q := hf.centerIn_Q
  center_X := hf.centerIn_X
  unique _ hle hc hsq hcomm := hf.unique' hle (by rw [hc]; norm_num) hsq hcomm
  elemE := isElemAbelian hf.Esq hf.Ecomm
  elemF := isElemAbelian hf.Fsq hf.Fcomm
  EF := hf.EF
  uniqE _ hle hV hc := hf.uniqE' hle hV (by rw [hc]; norm_num)
  normE := hf.normE
  normF := hf.normF
  quot := exists_dihedral_quotient hf.QX hf.normQ (by rw [hf.cardX, hf.cardQ]) hf.rX hf.sX hf.rk
    hf.s2 hf.sr2 hf.rne hf.sne
  elemU := isElemAbelian hf.Usq hf.Ucomm

end SylFacts

end Facts

section Transport

variable {H G : Type} [Group H] [Group G] {X : Subgroup H} (f : ↥X →* G)

@[expose] def trS (K : Subgroup H) : Subgroup G := (K.subgroupOf X).map f

@[expose] def untrS (K : Subgroup G) : Subgroup H := (K.comap f).map X.subtype

variable {f}

theorem mem_trS {K : Subgroup H} {y : G} : y ∈ trS f K ↔ ∃ x : ↥X, (x : H) ∈ K ∧ f x = y := by
  simp only [trS, mem_map, mem_subgroupOf]

theorem mem_untrS {K : Subgroup G} {x : H} : x ∈ untrS f K ↔ ∃ hx : x ∈ X, f ⟨x, hx⟩ ∈ K := by
  simp only [untrS, mem_map, mem_comap, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem apply_mem_trS_iff (hf : Function.Injective f) {K : Subgroup H} {x : ↥X} :
    f x ∈ trS f K ↔ (x : H) ∈ K := by
  rw [mem_trS]
  constructor
  · rintro ⟨y, hy, he⟩
    rwa [← hf he]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem trS_le_range (K : Subgroup H) : trS f K ≤ f.range := map_le_range _ _

theorem untrS_le (K : Subgroup G) : untrS f K ≤ X := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem trS_mono {K L : Subgroup H} (h : K ≤ L) : trS f K ≤ trS f L :=
  map_mono (subgroupOf_mono _ h)

theorem trS_untrS {K : Subgroup G} (hK : K ≤ f.range) : trS f (untrS f K) = K := by
  ext y
  rw [mem_trS]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx', h⟩ := mem_untrS.mp hx
    exact h
  · intro hy
    obtain ⟨x, rfl⟩ := hK hy
    exact ⟨x, mem_untrS.mpr ⟨x.2, hy⟩, rfl⟩

theorem untrS_trS (hf : Function.Injective f) {K : Subgroup H} (hK : K ≤ X) :
    untrS f (trS f K) = K := by
  ext x
  rw [mem_untrS]
  constructor
  · rintro ⟨hx, h⟩
    exact (apply_mem_trS_iff hf).mp h
  · intro hx
    exact ⟨hK hx, (apply_mem_trS_iff hf).mpr hx⟩

theorem card_trS (hf : Function.Injective f) {K : Subgroup H} (hK : K ≤ X) :
    Nat.card (trS f K) = Nat.card K := by
  rw [trS, card_map_of_injective hf]
  exact Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv

theorem card_untrS (hf : Function.Injective f) {K : Subgroup G} (hK : K ≤ f.range) :
    Nat.card (untrS f K) = Nat.card K := by
  conv_rhs => rw [← trS_untrS hK]
  exact (card_trS hf (untrS_le K)).symm

theorem trS_self : trS f X = f.range := by
  rw [trS, subgroupOf_self, ← MonoidHom.range_eq_map]

theorem trS_zpowers {z : H} (hz : z ∈ X) : trS f (zpowers z) = zpowers (f ⟨z, hz⟩) := by
  have h : (zpowers z).subgroupOf X = zpowers (⟨z, hz⟩ : ↥X) := by
    ext x
    rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, Subtype.ext (by simpa using hm)⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by simp⟩
  rw [trS, h, MonoidHom.map_zpowers]

theorem centerIn_trS (hf : Function.Injective f) {K : Subgroup H} (hK : K ≤ X) :
    centerIn (trS f K) = trS f (centerIn K) := by
  ext y
  rw [mem_centerIn']
  constructor
  · rintro ⟨hy, hyc⟩
    obtain ⟨x, hx, rfl⟩ := mem_trS.mp hy
    refine (apply_mem_trS_iff hf).mpr (mem_centerIn'.mpr ⟨hx, fun v hv => ?_⟩)
    have h := hyc (f ⟨v, hK hv⟩) ((apply_mem_trS_iff hf).mpr hv)
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hf h)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_trS.mp hy
    obtain ⟨hxK, hxc⟩ := mem_centerIn'.mp hx
    refine ⟨(apply_mem_trS_iff hf).mpr hxK, fun v hv => ?_⟩
    obtain ⟨u, hu, rfl⟩ := mem_trS.mp hv
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hxc u hu))

theorem isElemAbelian_trS {K : Subgroup H} (hK : IsElemAbelian 2 K) :
    IsElemAbelian 2 (trS f K) := by
  have hc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := isMulCommutative_iff_of_setLike.mp hK.1
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := mem_trS.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_trS.mp hb
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hc _ hx _ hy))
  · obtain ⟨x, hx, rfl⟩ := mem_trS.mp ha
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hK.2 _ hx)
    rw [this, map_one]

theorem isElemAbelian_untrS (hf : Function.Injective f) {K : Subgroup G}
    (hK : IsElemAbelian 2 K) : IsElemAbelian 2 (untrS f K) := by
  have hc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := isMulCommutative_iff_of_setLike.mp hK.1
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨hxa, ha'⟩ := mem_untrS.mp ha
    obtain ⟨hxb, hb'⟩ := mem_untrS.mp hb
    have h := hc _ ha' _ hb'
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hf h)
  · obtain ⟨hxa, ha'⟩ := mem_untrS.mp ha
    have h := hK.2 _ ha'
    rw [← map_pow, ← map_one f] at h
    simpa using congrArg Subtype.val (hf h)

theorem trS_le_normalizer (hf : Function.Injective f) {K L : Subgroup H}
    (hKL : K ≤ normalizer (L : Set H)) : trS f K ≤ normalizer (trS f L : Set G) := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_trS.mp hy
  have hn := hKL ha
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨b, hb, rfl⟩ := mem_trS.mp hw
    rw [← map_inv, ← map_mul, ← map_mul, apply_mem_trS_iff hf]
    simpa using (mem_normalizer_iff.mp hn b).mp hb
  · intro hw
    obtain ⟨c, hc, hce⟩ := mem_trS.mp hw
    have hw' : w = f (a⁻¹ * c * a) := by
      rw [map_mul, map_mul, map_inv, hce]
      group
    rw [hw', apply_mem_trS_iff hf]
    simpa using (mem_normalizer_iff.mp (inv_mem hn) c).mp hc

theorem quot_trS (hf : Function.Injective f) {Q : Subgroup H} {k : ℕ}
    (h : ∃ φ : ↥X →* DihedralGroup k, Function.Surjective φ ∧ φ.ker = Q.subgroupOf X) :
    ∃ φ : ↥f.range →* DihedralGroup k, Function.Surjective φ ∧
      φ.ker = (trS f Q).subgroupOf f.range := by
  obtain ⟨φ, hs, hk⟩ := h
  refine ⟨φ.comp (MonoidHom.ofInjective hf).symm.toMonoidHom,
    hs.comp (MonoidHom.ofInjective hf).symm.surjective, ?_⟩
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hk, mem_subgroupOf,
    mem_subgroupOf]
  have hy : (y : G) = f ((MonoidHom.ofInjective hf).symm y) := by
    rw [← MonoidHom.ofInjective_apply hf, MulEquiv.apply_symm_apply]
  rw [hy, apply_mem_trS_iff hf]
  rfl

end Transport

section Map

variable {H G : Type} [Group H] [Group G] {X Q E F U : Subgroup H} {z : H} {k : ℕ}

theorem SylModel.z_mem (hm : SylModel X Q E F U z k) : z ∈ X := by
  have : z ∈ centerIn X := by rw [hm.center_X]; exact mem_zpowers z
  exact this.1

theorem SylModel.map (hm : SylModel X Q E F U z k) (f : ↥X →* G) (hf : Function.Injective f) :
    SylModel f.range (trS f Q) (trS f E) (trS f F) (trS f U) (f ⟨z, hm.z_mem⟩) k where
  QX := trS_le_range Q
  EX := trS_le_range E
  FX := trS_le_range F
  UQ := trS_mono hm.UQ
  cardQ := by rw [card_trS hf hm.QX, hm.cardQ]
  cardE := by rw [card_trS hf hm.EX, hm.cardE]
  cardF := by rw [card_trS hf hm.FX, hm.cardF]
  cardU := by rw [card_trS hf (hm.UQ.trans hm.QX), hm.cardU]
  order_z := by rw [orderOf_injective f hf, Subgroup.orderOf_mk, hm.order_z]
  extraspecial :=
    CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      ((subgroupOfEquivOfLe hm.QX).symm.trans ((Q.subgroupOf X).equivMapOfInjective f hf))
      hm.extraspecial
  center_Q := by rw [centerIn_trS hf hm.QX, hm.center_Q, trS_zpowers]
  center_X := by rw [← trS_self, centerIn_trS hf le_rfl, hm.center_X, trS_zpowers]
  unique Q' hle hc hsq hcomm := by
    have key : ∀ w : ↥X, f w ∈ zpowers (f ⟨z, hm.z_mem⟩) → (w : H) ∈ zpowers z := fun w hw => by
      rwa [← trS_zpowers hm.z_mem, apply_mem_trS_iff hf] at hw
    have hsq' : ∀ x ∈ untrS f Q', x ^ 2 ∈ zpowers z := by
      intro x hx
      obtain ⟨hx', hxQ⟩ := mem_untrS.mp hx
      have h := hsq _ hxQ
      rw [← map_pow] at h
      simpa using key _ h
    have hcomm' : ∀ x ∈ untrS f Q', ∀ y ∈ untrS f Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
      intro x hx y hy
      obtain ⟨hx', hxQ⟩ := mem_untrS.mp hx
      obtain ⟨hy', hyQ⟩ := mem_untrS.mp hy
      have h := hcomm _ hxQ _ hyQ
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h
      simpa using key _ h
    have h := hm.unique (untrS f Q') (untrS_le Q') (by rw [card_untrS hf hle, hc]) hsq' hcomm'
    rw [← h, trS_untrS hle]
  elemE := isElemAbelian_trS hm.elemE
  elemF := isElemAbelian_trS hm.elemF
  EF := fun h => hm.EF (by rw [← untrS_trS hf hm.EX, h, untrS_trS hf hm.FX])
  uniqE V hle hV hc := by
    rcases hm.uniqE (untrS f V) (untrS_le V) (isElemAbelian_untrS hf hV)
      (by rw [card_untrS hf hle, hc]) with h | h
    · left
      rw [← h, trS_untrS hle]
    · right
      rw [← h, trS_untrS hle]
  normE := trS_le_normalizer hf hm.normE
  normF := trS_le_normalizer hf hm.normF
  quot := quot_trS hf hm.quot
  elemU := isElemAbelian_trS hm.elemU

end Map

end CFSG.ComponentClassification.AS81.HeSylow
