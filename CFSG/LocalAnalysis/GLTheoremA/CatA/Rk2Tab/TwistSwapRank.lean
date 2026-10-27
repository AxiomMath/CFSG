module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint.Chevalley

private theorem eq_one_of_pow_eq_one_of_mem_central {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {K : Subgroup H} (hKp : ¬ p ∣ Nat.card K) {k : H} (hk : k ∈ K)
    (h : k ^ p = 1) : k = 1 := by
  have h1 : orderOf k ∣ p := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf k ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hk
  have hcop : Nat.Coprime (orderOf k) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact fun hd => hKp (hd.trans h2)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h1)

private theorem commute_of_pow_eq_one_of_central {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {K : Subgroup H} (hKc : ∀ k ∈ K, ∀ x : H, Commute k x)
    (hKp : ¬ p ∣ Nat.card K) (hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ K)
    {x y : H} (hx : x ^ p = 1) (hy : y ^ p = 1) : Commute x y := by
  set c : H := y * x * y⁻¹ * x⁻¹ with hc
  have hcK : c ∈ K := hcomm y x
  have hconj : (y * x * y⁻¹) ^ p = 1 := by
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hdecomp : y * x * y⁻¹ = c * x := by
    simp only [hc]
    group
  have hcx : Commute c x := hKc c hcK x
  have hcpow : c ^ p = 1 := by
    rw [hdecomp, hcx.mul_pow, hx, mul_one] at hconj
    exact hconj
  have hc1 : c = 1 := eq_one_of_pow_eq_one_of_mem_central hp hKp hcK hcpow
  have hyx : y * x = x * y := by
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [hdecomp, hc1, one_mul]
  exact hyx.symm

private theorem mem_closure_pow_eq_one_iff {H : Type*} [Group H] {p : ℕ}
    (hmul : ∀ x y : H, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1)
    (hinv : ∀ x : H, x ^ p = 1 → x⁻¹ ^ p = 1) {x : H} :
    x ∈ Subgroup.closure {y : H | y ^ p = 1} ↔ x ^ p = 1 := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun y _ => y ^ p = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact hy
    · simp
    · intro y z _ _ ihy ihz
      exact hmul y z ihy ihz
    · intro y _ ihy
      exact hinv y ihy
  · intro hx
    exact Subgroup.subset_closure hx

private theorem pow_surjective_of_central {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {K : Subgroup H} (hKc : ∀ k ∈ K, ∀ x : H, Commute k x)
    (hKp : ¬ p ∣ Nat.card K) : Function.Surjective (fun k : K => k ^ p) := by
  have hinj : Function.Injective (fun k : K => k ^ p) := by
    intro a b hab
    have hKab : Commute a (b⁻¹ : K) := Subtype.ext (hKc a a.2 (b⁻¹ : K)).eq
    have hab' : a ^ p = b ^ p := hab
    have h1 : (a * b⁻¹) ^ p = 1 := by
      rw [hKab.mul_pow, inv_pow, hab', mul_inv_cancel]
    have h1H : (((a * b⁻¹ : K)) : H) ^ p = 1 := by
      simpa [Subgroup.coe_pow] using congrArg Subtype.val h1
    have h2 : ((a * b⁻¹ : K) : H) = 1 :=
      eq_one_of_pow_eq_one_of_mem_central hp hKp (K.mul_mem a.2 (K.inv_mem b.2)) h1H
    exact mul_inv_eq_one.1 (Subtype.ext h2)
  exact Finite.injective_iff_surjective.1 hinj

private theorem exists_pow_eq_one_mul_mem_of_central {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {K : Subgroup H} (hKc : ∀ k ∈ K, ∀ x : H, Commute k x)
    (hKp : ¬ p ∣ Nat.card K) (hexp : ∀ x : H, x ^ p ∈ K) (x : H) :
    ∃ y : H, y ^ p = 1 ∧ y⁻¹ * x ∈ K := by
  obtain ⟨k, hk⟩ := pow_surjective_of_central hp hKc hKp ⟨(x ^ p)⁻¹, K.inv_mem (hexp x)⟩
  have hk' : (k : H) ^ p = (x ^ p)⁻¹ := congrArg Subtype.val hk
  refine ⟨x * (k : H), ?_, ?_⟩
  · rw [(hKc k k.2 x).symm.mul_pow, hk', mul_inv_cancel]
  · have hval : (x * (k : H))⁻¹ * x = ((k : H))⁻¹ := by group
    rw [hval]
    exact K.inv_mem k.2

private theorem pTorsion_subgroup_of_central {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {K : Subgroup H} (hKc : ∀ k ∈ K, ∀ x : H, Commute k x)
    (hKp : ¬ p ∣ Nat.card K) (hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ K)
    (hexp : ∀ x : H, x ^ p ∈ K) :
    ∃ P : Subgroup H, IsElemAbelian p P ∧ P ⊓ K = ⊥ ∧
      (∀ x : H, x ∈ P ↔ x ^ p = 1) ∧
      (∀ x : H, ∃ y ∈ P, y⁻¹ * x ∈ K) := by
  classical
  have hmul : ∀ x y : H, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
    intro x y hx hy
    rw [(commute_of_pow_eq_one_of_central hp hKc hKp hcomm hx hy).mul_pow, hx, hy, one_mul]
  have hinv : ∀ x : H, x ^ p = 1 → x⁻¹ ^ p = 1 := by
    intro x hx
    rw [inv_pow, hx, inv_one]
  have hPmem : ∀ x : H, x ∈ Subgroup.closure {y : H | y ^ p = 1} ↔ x ^ p = 1 :=
    fun x => mem_closure_pow_eq_one_iff hmul hinv
  refine ⟨Subgroup.closure {y : H | y ^ p = 1}, ?_, ?_, hPmem, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (commute_of_pow_eq_one_of_central hp hKc hKp hcomm
        ((hPmem a).1 a.2) ((hPmem b).1 b.2)).eq
    · exact (hPmem x).1 hx
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    exact eq_one_of_pow_eq_one_of_mem_central hp hKp hx.2 ((hPmem x).1 hx.1)
  · intro x
    obtain ⟨y, hyp, hyK⟩ := exists_pow_eq_one_mul_mem_of_central hp hKc hKp hexp x
    exact ⟨y, (hPmem y).2 hyp, hyK⟩

private theorem range_eq_sup_of_apply_eq_mul {G : Type*} [Group G] {X Y : Subgroup G}
    (Φ : ↥X × ↥Y →* G) (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G)) :
    Φ.range = X ⊔ Y := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨z, rfl⟩
    rw [hΦ z]
    exact Subgroup.mul_mem (X ⊔ Y) (Subgroup.mem_sup_left z.1.2) (Subgroup.mem_sup_right z.2.2)
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨(⟨x, hx⟩, 1), by rw [hΦ]; simp⟩
    · intro y hy
      exact ⟨(1, ⟨y, hy⟩), by rw [hΦ]; simp⟩

private theorem ker_central_of_apply_eq_mul {G : Type*} [Group G] {X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (Φ : ↥X × ↥Y →* G)
    (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G)) :
    ∀ z ∈ Φ.ker, ∀ w : ↥X × ↥Y, Commute z w := by
  intro z hz w
  have hzG : (z.1 : G) * (z.2 : G) = 1 := by
    have := MonoidHom.mem_ker.1 hz
    rwa [hΦ z] at this
  have hz1Y : (z.1 : G) ∈ Y := by
    rw [eq_inv_of_mul_eq_one_left hzG]
    exact Y.inv_mem z.2.2
  have hz2X : (z.2 : G) ∈ X := by
    rw [eq_inv_of_mul_eq_one_right hzG]
    exact X.inv_mem z.1.2
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact (hXY w.1 w.1.2 z.1 hz1Y).eq.symm
  · exact (hXY z.2 hz2X w.2 w.2.2).eq

private theorem card_ker_dvd_inf_of_apply_eq_mul {G : Type*} [Group G] {X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (Φ : ↥X × ↥Y →* G)
    (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G)) :
    Nat.card Φ.ker ∣ Nat.card ↥(X ⊓ Y) := by
  let f : Φ.ker →* ↥(X ⊓ Y) :=
    { toFun := fun z => ⟨z.1.1, ⟨z.1.1.2, by
        have hzG : (z.1.1 : G) * (z.1.2 : G) = 1 := by
          have := MonoidHom.mem_ker.1 z.2
          rwa [hΦ z.1] at this
        rw [eq_inv_of_mul_eq_one_left hzG]
        exact Y.inv_mem z.1.2.2⟩⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (a.1.1 : G) = (b.1.1 : G) := congrArg (fun z : ↥(X ⊓ Y) => (z : G)) hab
    have ha2 : (a.1.2 : G) = (a.1.1 : G)⁻¹ := by
      have := MonoidHom.mem_ker.1 a.2
      rw [hΦ a.1] at this
      exact eq_inv_of_mul_eq_one_right this
    have hb2 : (b.1.2 : G) = (b.1.1 : G)⁻¹ := by
      have := MonoidHom.mem_ker.1 b.2
      rw [hΦ b.1] at this
      exact eq_inv_of_mul_eq_one_right this
    apply Subtype.ext
    refine Prod.ext (Subtype.ext h1) (Subtype.ext ?_)
    rw [ha2, hb2, h1]
  calc Nat.card Φ.ker = Nat.card ↥f.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ ∣ Nat.card ↥(X ⊓ Y) := Subgroup.card_subgroup_dvd_card f.range

private theorem not_dvd_card_ker_of_apply_eq_mul {G : Type*} [Group G] {p : ℕ} {X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (hinf : ¬ p ∣ Nat.card ↥(X ⊓ Y))
    (Φ : ↥X × ↥Y →* G) (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G)) :
    ¬ p ∣ Nat.card Φ.ker :=
  fun hd => hinf (hd.trans (card_ker_dvd_inf_of_apply_eq_mul hXY Φ hΦ))

private theorem ker_subgroupOf_central_of_apply_eq_mul {G : Type*} [Group G] {X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (Φ : ↥X × ↥Y →* G)
    (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G)) (E : Subgroup G) :
    ∀ k ∈ Φ.ker.subgroupOf (E.comap Φ), ∀ x : E.comap Φ, Commute k x := by
  intro k hk x
  apply Subtype.ext
  exact (ker_central_of_apply_eq_mul hXY Φ hΦ (k : ↥X × ↥Y) (Subgroup.mem_subgroupOf.1 hk)
    (x : ↥X × ↥Y)).eq

private theorem commutator_mem_ker_subgroupOf {G : Type*} [Group G] {X Y : Subgroup G} {p : ℕ}
    (Φ : ↥X × ↥Y →* G) {E : Subgroup G} (hEel : IsElemAbelian p E) :
    ∀ x y : E.comap Φ, x * y * x⁻¹ * y⁻¹ ∈ Φ.ker.subgroupOf (E.comap Φ) := by
  intro x y
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hxE : Φ (x : ↥X × ↥Y) ∈ E := x.2
  have hyE : Φ (y : ↥X × ↥Y) ∈ E := y.2
  have h1 : Φ (((x * y * x⁻¹ * y⁻¹ : E.comap Φ) : ↥X × ↥Y)) =
      Φ (x : ↥X × ↥Y) * Φ (y : ↥X × ↥Y) * (Φ (x : ↥X × ↥Y))⁻¹ *
        (Φ (y : ↥X × ↥Y))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [h1, hEel.comm hxE hyE]
  group

private theorem pow_mem_ker_subgroupOf {G : Type*} [Group G] {X Y : Subgroup G} {p : ℕ}
    (Φ : ↥X × ↥Y →* G) {E : Subgroup G} (hEel : IsElemAbelian p E) :
    ∀ x : E.comap Φ, x ^ p ∈ Φ.ker.subgroupOf (E.comap Φ) := by
  intro x
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hxE : Φ (x : ↥X × ↥Y) ∈ E := x.2
  have h1 : Φ (((x ^ p : E.comap Φ) : ↥X × ↥Y)) = (Φ (x : ↥X × ↥Y)) ^ p := by
    simp only [Subgroup.coe_pow, map_pow]
  rw [h1, hEel.2 _ hxE]

private theorem not_dvd_card_ker_subgroupOf {G : Type*} [Group G] {p : ℕ} {X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (hinf : ¬ p ∣ Nat.card ↥(X ⊓ Y))
    (Φ : ↥X × ↥Y →* G) (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G)) (E : Subgroup G) :
    ¬ p ∣ Nat.card (Φ.ker.subgroupOf (E.comap Φ)) := by
  have hKle : Φ.ker ≤ E.comap Φ := by
    intro z hz
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
    exact E.one_mem
  have hcard : Nat.card (Φ.ker.subgroupOf (E.comap Φ)) = Nat.card Φ.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  rw [hcard]
  exact not_dvd_card_ker_of_apply_eq_mul hXY hinf Φ hΦ

private theorem exists_pTorsion_complement_of_le_sup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y)
    (hinf : ¬ p ∣ Nat.card ↥(X ⊓ Y))
    (Φ : ↥X × ↥Y →* G) (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G))
    {E : Subgroup G} (hEel : IsElemAbelian p E) :
    ∃ P : Subgroup (E.comap Φ), IsElemAbelian p P ∧
      P ⊓ (Φ.ker.subgroupOf (E.comap Φ)) = ⊥ ∧
      (∀ x : E.comap Φ, x ∈ P ↔ x ^ p = 1) ∧
      (∀ x : E.comap Φ, ∃ y ∈ P, y⁻¹ * x ∈ Φ.ker.subgroupOf (E.comap Φ)) :=
  pTorsion_subgroup_of_central hp
    (ker_subgroupOf_central_of_apply_eq_mul hXY Φ hΦ E)
    (not_dvd_card_ker_subgroupOf hXY hinf Φ hΦ E)
    (commutator_mem_ker_subgroupOf Φ hEel)
    (pow_mem_ker_subgroupOf Φ hEel)

private theorem eq_of_Phi_eq_of_pTorsion {G : Type*} [Group G] {X Y : Subgroup G}
    (Φ : ↥X × ↥Y →* G) {E : Subgroup G} (P : Subgroup (E.comap Φ))
    (hPinf : P ⊓ (Φ.ker.subgroupOf (E.comap Φ)) = ⊥) :
    ∀ u v : P, Φ ((u : E.comap Φ) : ↥X × ↥Y) = Φ ((v : E.comap Φ) : ↥X × ↥Y) → u = v := by
  intro u v huv
  have h2 : ((u : E.comap Φ)⁻¹ * (v : E.comap Φ)) ∈ Φ.ker.subgroupOf (E.comap Φ) := by
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    show Φ ((u : ↥X × ↥Y)⁻¹ * (v : ↥X × ↥Y)) = 1
    rw [map_mul, map_inv, huv, inv_mul_cancel]
  have h3 : ((u : E.comap Φ)⁻¹ * (v : E.comap Φ)) ∈ (⊥ : Subgroup (E.comap Φ)) := by
    rw [← hPinf]
    exact ⟨P.mul_mem (P.inv_mem u.2) v.2, h2⟩
  rw [Subgroup.mem_bot] at h3
  apply Subtype.ext
  calc (u : E.comap Φ) = (u : E.comap Φ) * 1 := (mul_one _).symm
    _ = (u : E.comap Φ) * ((u : E.comap Φ)⁻¹ * (v : E.comap Φ)) := by rw [h3]
    _ = (v : E.comap Φ) := by group

private theorem exists_pTorsion_preimage {G : Type*} [Group G] {X Y : Subgroup G}
    (Φ : ↥X × ↥Y →* G) {E : Subgroup G} (hE : E ≤ X ⊔ Y)
    (hΦrange : Φ.range = X ⊔ Y) (P : Subgroup (E.comap Φ))
    (hPcover : ∀ x : E.comap Φ, ∃ y ∈ P, y⁻¹ * x ∈ Φ.ker.subgroupOf (E.comap Φ)) :
    ∀ e : E, ∃ y : P, Φ ((y : E.comap Φ) : ↥X × ↥Y) = (e : G) := by
  intro e
  have he : (e : G) ∈ Φ.range := by rw [hΦrange]; exact hE e.2
  obtain ⟨z, hz⟩ := he
  have hzEt : z ∈ E.comap Φ := by
    rw [Subgroup.mem_comap, hz]
    exact e.2
  obtain ⟨y, hyP, hyK⟩ := hPcover ⟨z, hzEt⟩
  have hΦy : Φ ((y : E.comap Φ) : ↥X × ↥Y) = (e : G) := by
    have hy : Φ ((((y : E.comap Φ))⁻¹ * (⟨z, hzEt⟩ : E.comap Φ) :
        E.comap Φ) : ↥X × ↥Y) = 1 := by
      have h := hyK
      rwa [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at h
    have hy1 : (Φ ((y : E.comap Φ) : ↥X × ↥Y))⁻¹ * Φ z = 1 := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hy
    rw [eq_of_inv_mul_eq_one hy1, hz]
  exact ⟨⟨y, hyP⟩, hΦy⟩

private theorem exists_mulEquiv_pTorsion {G : Type*} [Group G] {X Y : Subgroup G}
    (Φ : ↥X × ↥Y →* G) {E : Subgroup G} (hE : E ≤ X ⊔ Y)
    (hΦrange : Φ.range = X ⊔ Y) (P : Subgroup (E.comap Φ))
    (hPinf : P ⊓ (Φ.ker.subgroupOf (E.comap Φ)) = ⊥)
    (hPcover : ∀ x : E.comap Φ, ∃ y ∈ P, y⁻¹ * x ∈ Φ.ker.subgroupOf (E.comap Φ)) :
    ∃ e : P ≃* E, ∀ z : P, (e z : G) = Φ ((z : E.comap Φ) : ↥X × ↥Y) := by
  let ΦP : P →* E :=
    { toFun := fun z => ⟨Φ ((z : E.comap Φ) : ↥X × ↥Y), Subgroup.mem_comap.1 (z : E.comap Φ).2⟩
      map_one' := Subtype.ext (map_one Φ)
      map_mul' := fun a b => Subtype.ext (map_mul Φ _ _) }
  have hinj : Function.Injective ΦP := fun u v huv =>
    eq_of_Phi_eq_of_pTorsion Φ P hPinf u v (congrArg Subtype.val huv)
  have hsurj : Function.Surjective ΦP := fun e =>
    let ⟨y, hy⟩ := exists_pTorsion_preimage Φ hE hΦrange P hPcover e
    ⟨y, Subtype.ext hy⟩
  exact ⟨MulEquiv.ofBijective ΦP ⟨hinj, hsurj⟩, fun _ => rfl⟩

private theorem exists_pSection {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y)
    (hinf : ¬ p ∣ Nat.card ↥(X ⊓ Y))
    (Φ : ↥X × ↥Y →* G) (hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G))
    {E : Subgroup G} (hE : E ≤ X ⊔ Y) (hEel : IsElemAbelian p E) :
    ∃ σ : E →* ↥X × ↥Y,
      (∀ e : E, Φ (σ e) = (e : G)) ∧
      (∀ e : E, (σ e) ^ p = 1) ∧
      (∀ (z : ↥X × ↥Y) (e : E), Φ z = (e : G) → z ^ p = 1 → z = σ e) := by
  classical
  have hΦrange : Φ.range = X ⊔ Y := range_eq_sup_of_apply_eq_mul Φ hΦ
  obtain ⟨P, _, hPinf, hPmem, hPcover⟩ :=
    exists_pTorsion_complement_of_le_sup hp hXY hinf Φ hΦ hEel
  obtain ⟨eΦ, heΦ⟩ := exists_mulEquiv_pTorsion Φ hE hΦrange P hPinf hPcover
  refine ⟨(E.comap Φ).subtype.comp P.subtype |>.comp eΦ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro e
    have h := heΦ (eΦ.symm e)
    rw [eΦ.apply_symm_apply] at h
    exact h.symm
  · intro e
    have h := (hPmem ((eΦ.symm e : P) : E.comap Φ)).1 (eΦ.symm e).2
    simpa [Subgroup.coe_pow] using congrArg (fun z : E.comap Φ => ((z : ↥X × ↥Y))) h
  · intro z e hz hzp
    have hzEt : z ∈ E.comap Φ := by
      rw [Subgroup.mem_comap, hz]
      exact e.2
    have hzP : (⟨z, hzEt⟩ : E.comap Φ) ∈ P := (hPmem ⟨z, hzEt⟩).2 (Subtype.ext hzp)
    have h1 : eΦ ⟨⟨z, hzEt⟩, hzP⟩ = e := by
      apply Subtype.ext
      rw [heΦ ⟨⟨z, hzEt⟩, hzP⟩]
      exact hz
    have h3 : (⟨⟨z, hzEt⟩, hzP⟩ : P) = eΦ.symm e := by
      apply eΦ.injective
      rw [h1, eΦ.apply_symm_apply]
    have h4 : z = ((E.comap Φ).subtype.comp P.subtype |>.comp eΦ.symm.toMonoidHom) e := by
      have := congrArg (fun w : P => ((w : E.comap Φ) : ↥X × ↥Y)) h3
      simpa using this
    exact h4

private theorem card_le_of_pSection_of_swap {G : Type*} [Group G] [Finite G] {p k : ℕ}
    {X Y : Subgroup G} (hX : ∀ F : Subgroup G, F ≤ X → IsElemAbelian p F → Nat.card F ≤ p ^ k)
    {E : Subgroup G} (σ : E →* ↥X × ↥Y) (φ : G →* G)
    (hσinj : Function.Injective σ)
    (hσφ : ∀ e : E, ((σ e).2 : G) = φ ((σ e).1 : G))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ k := by
  let pr₁ : ↥X × ↥Y →* ↥X := MonoidHom.fst ↥X ↥Y
  have hinj : Function.Injective (pr₁.comp σ) := by
    intro e e' heq
    have h1 : (σ e).1 = (σ e').1 := heq
    have hσeq : σ e = σ e' := by
      refine Prod.ext h1 ?_
      apply Subtype.ext
      rw [hσφ e, hσφ e', congrArg Subtype.val h1]
    exact hσinj hσeq
  let R : Subgroup ↥X := (pr₁.comp σ).range
  have hRcard : Nat.card R = Nat.card E :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hRel : IsElemAbelian p R :=
    (isElemAbelian_iff_isElementaryAbelian).2
      (CFSG.IsElementaryAbelian.of_mulEquiv (MonoidHom.ofInjective hinj) hEel.isElementaryAbelian)
  let F : Subgroup G := R.map X.subtype
  have hFle : F ≤ X := by
    have h := Subgroup.map_le_range X.subtype R
    rwa [Subgroup.range_subtype] at h
  have hFel : IsElemAbelian p F := hRel.map X.subtype
  have hFcard : Nat.card F = Nat.card R := Subgroup.card_map_of_injective X.subtype_injective
  calc Nat.card E = Nat.card R := hRcard.symm
    _ = Nat.card F := hFcard.symm
    _ ≤ p ^ k := hX F hFle hFel

private theorem card_range_le_of_fixed_section {G : Type*} [Group G] [Finite G] {p k : ℕ}
    {Z : Subgroup G} (φ : G →* G)
    (hZ : ∀ F : Subgroup G, F ≤ Z → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k)
    {E : Subgroup G} (τ : E →* ↥Z)
    (hfix : ∀ e : E, φ (τ e : G) = (τ e : G))
    (hEel : IsElemAbelian p E) : Nat.card τ.range ≤ p ^ k := by
  have hTopEl : IsElemAbelian p (⊤ : Subgroup E) := by
    have h := hEel.subgroupOf E
    rwa [Subgroup.subgroupOf_self] at h
  have hRel : IsElemAbelian p τ.range := by
    have h := hTopEl.map τ
    rwa [Subgroup.map_top] at h
  have hle : τ.range.map Z.subtype ≤ Z :=
    (Subgroup.map_le_range Z.subtype τ.range).trans (le_of_eq (Subgroup.range_subtype Z))
  have hfix' : ∀ r ∈ τ.range.map Z.subtype, φ r = r := by
    rintro _ ⟨z, ⟨e, rfl⟩, rfl⟩
    exact hfix e
  have hcard : Nat.card (τ.range.map Z.subtype) = Nat.card τ.range :=
    Subgroup.card_map_of_injective Z.subtype_injective
  rw [← hcard]
  exact hZ _ hle (hRel.map Z.subtype) hfix'

private theorem projections_card_le_of_pSection_of_fixed {G : Type*} [Group G] [Finite G]
    {p k₁ k₂ : ℕ} {X W : Subgroup G} (φ : G →* G)
    (hX : ∀ F : Subgroup G, F ≤ X → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k₁)
    (hW : ∀ F : Subgroup G, F ≤ W → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k₂)
    {E : Subgroup G} (σ : E →* ↥X × ↥W)
    (hσ₁ : ∀ e : E, φ ((σ e).1 : G) = ((σ e).1 : G))
    (hσ₂ : ∀ e : E, φ ((σ e).2 : G) = ((σ e).2 : G))
    (hEel : IsElemAbelian p E) :
    Nat.card ((MonoidHom.fst ↥X ↥W).comp σ).range ≤ p ^ k₁ ∧
      Nat.card ((MonoidHom.snd ↥X ↥W).comp σ).range ≤ p ^ k₂ :=
  ⟨card_range_le_of_fixed_section φ hX ((MonoidHom.fst ↥X ↥W).comp σ) hσ₁ hEel,
   card_range_le_of_fixed_section φ hW ((MonoidHom.snd ↥X ↥W).comp σ) hσ₂ hEel⟩

private theorem card_le_of_pSection_of_fixed {G : Type*} [Group G] [Finite G] {p k₁ k₂ : ℕ}
    {X W : Subgroup G} (φ : G →* G)
    (hX : ∀ F : Subgroup G, F ≤ X → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k₁)
    (hW : ∀ F : Subgroup G, F ≤ W → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k₂)
    {E : Subgroup G} (σ : E →* ↥X × ↥W)
    (hσinj : Function.Injective σ)
    (hσ₁ : ∀ e : E, φ ((σ e).1 : G) = ((σ e).1 : G))
    (hσ₂ : ∀ e : E, φ ((σ e).2 : G) = ((σ e).2 : G))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ (k₁ + k₂) := by
  let pr₁ : ↥X × ↥W →* ↥X := MonoidHom.fst ↥X ↥W
  let pr₂ : ↥X × ↥W →* ↥W := MonoidHom.snd ↥X ↥W
  let R₁ : Subgroup ↥X := (pr₁.comp σ).range
  let R₂ : Subgroup ↥W := (pr₂.comp σ).range
  have hb := projections_card_le_of_pSection_of_fixed φ hX hW σ hσ₁ hσ₂ hEel
  have hinj : Function.Injective (fun e : E =>
      (⟨(pr₁.comp σ) e, ⟨e, rfl⟩⟩, ⟨(pr₂.comp σ) e, ⟨e, rfl⟩⟩) :
      E → ↥R₁ × ↥R₂) := by
    intro e e' heq
    have h1 : (pr₁.comp σ) e = (pr₁.comp σ) e' :=
      congrArg Subtype.val (congrArg (fun z : ↥R₁ × ↥R₂ => (z.1 : ↥R₁)) heq)
    have h2 : (pr₂.comp σ) e = (pr₂.comp σ) e' :=
      congrArg Subtype.val (congrArg (fun z : ↥R₁ × ↥R₂ => (z.2 : ↥R₂)) heq)
    exact hσinj (Prod.ext h1 h2)
  have hEcard : Nat.card E ≤ Nat.card R₁ * Nat.card R₂ := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hinj
  calc Nat.card E ≤ Nat.card R₁ * Nat.card R₂ := hEcard
    _ ≤ p ^ k₁ * p ^ k₂ := Nat.mul_le_mul hb.1 hb.2
    _ = p ^ (k₁ + k₂) := (pow_add p k₁ k₂).symm

private theorem exists_pSection_of_swap {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y)
    (hinf : ¬ p ∣ Nat.card ↥(X ⊓ Y)) (φ : G →* G) (hφX : ∀ x ∈ X, φ x ∈ Y)
    (hφY : ∀ y ∈ Y, φ y ∈ X)
    {E : Subgroup G} (hE : E ≤ X ⊔ Y) (hEel : IsElemAbelian p E)
    (hfix : ∀ e ∈ E, φ e = e) :
    ∃ σ : E →* ↥X × ↥Y,
      Function.Injective σ ∧ (∀ e : E, ((σ e).2 : G) = φ ((σ e).1 : G)) := by
  classical
  let Φ : ↥X × ↥Y →* G := X.subtype.noncommCoprod Y.subtype (fun a b => hXY a a.2 b b.2)
  have hΦ : ∀ z : ↥X × ↥Y, Φ z = (z.1 : G) * (z.2 : G) := fun _ => rfl
  obtain ⟨σ, hσΦ, hσp, hσuniq⟩ := exists_pSection hp hXY hinf Φ hΦ hE hEel
  let φt : ↥X × ↥Y →* ↥X × ↥Y :=
    { toFun := fun z =>
        (⟨φ (z.2 : G), hφY (z.2 : G) z.2.2⟩, ⟨φ (z.1 : G), hφX (z.1 : G) z.1.2⟩)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp }
  have hΦφt : ∀ z : ↥X × ↥Y, Φ (φt z) = φ (Φ z) := by
    intro z
    rw [hΦ (φt z), hΦ z, map_mul]
    exact (hXY (φ (z.2 : G)) (hφY (z.2 : G) z.2.2) (φ (z.1 : G))
      (hφX (z.1 : G) z.1.2)).eq
  have hσfixed : ∀ e : E, φt (σ e) = σ e := by
    intro e
    have hpp : (φt (σ e)) ^ p = 1 := by
      rw [← map_pow, hσp e, map_one]
    exact hσuniq (φt (σ e)) e (by rw [hΦφt, hσΦ e, hfix (e : G) e.2]) hpp
  have hσinj : Function.Injective σ := by
    intro e e' h
    have := congrArg Φ h
    rw [hσΦ e, hσΦ e'] at this
    exact Subtype.ext this
  have hσφ : ∀ e : E, ((σ e).2 : G) = φ ((σ e).1 : G) := by
    intro e
    have h := congrArg (fun w : ↥X × ↥Y => (w.2 : G)) (hσfixed e).symm
    simpa [φt] using h
  exact ⟨σ, hσinj, hσφ⟩

private theorem exists_pSection_of_fixed {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X W : Subgroup G} (hXW : ∀ x ∈ X, ∀ w ∈ W, Commute x w)
    (hinf : ¬ p ∣ Nat.card ↥(X ⊓ W)) (φ : G →* G) (hφX : ∀ x ∈ X, φ x ∈ X)
    (hφW : ∀ w ∈ W, φ w ∈ W)
    {E : Subgroup G} (hE : E ≤ X ⊔ W) (hEel : IsElemAbelian p E)
    (hfix : ∀ e ∈ E, φ e = e) :
    ∃ σ : E →* ↥X × ↥W,
      Function.Injective σ ∧
      (∀ e : E, φ ((σ e).1 : G) = ((σ e).1 : G)) ∧
      (∀ e : E, φ ((σ e).2 : G) = ((σ e).2 : G)) := by
  classical
  let Φ : ↥X × ↥W →* G := X.subtype.noncommCoprod W.subtype (fun a b => hXW a a.2 b b.2)
  have hΦ : ∀ z : ↥X × ↥W, Φ z = (z.1 : G) * (z.2 : G) := fun _ => rfl
  obtain ⟨σ, hσΦ, hσp, hσuniq⟩ := exists_pSection hp hXW hinf Φ hΦ hE hEel
  let φt : ↥X × ↥W →* ↥X × ↥W :=
    { toFun := fun z =>
        (⟨φ (z.1 : G), hφX (z.1 : G) z.1.2⟩, ⟨φ (z.2 : G), hφW (z.2 : G) z.2.2⟩)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp }
  have hΦφt : ∀ z : ↥X × ↥W, Φ (φt z) = φ (Φ z) := by
    intro z
    rw [hΦ (φt z), hΦ z, map_mul]
    rfl
  have hσfixed : ∀ e : E, φt (σ e) = σ e := by
    intro e
    have hpp : (φt (σ e)) ^ p = 1 := by
      rw [← map_pow, hσp e, map_one]
    exact hσuniq (φt (σ e)) e (by rw [hΦφt, hσΦ e, hfix (e : G) e.2]) hpp
  have hσinj : Function.Injective σ := by
    intro e e' h
    have := congrArg Φ h
    rw [hσΦ e, hσΦ e'] at this
    exact Subtype.ext this
  have hσ₁ : ∀ e : E, φ ((σ e).1 : G) = ((σ e).1 : G) := by
    intro e
    have h := congrArg (fun w : ↥X × ↥W => (w.1 : G)) (hσfixed e).symm
    simpa [φt] using h.symm
  have hσ₂ : ∀ e : E, φ ((σ e).2 : G) = ((σ e).2 : G) := by
    intro e
    have h := congrArg (fun w : ↥X × ↥W => (w.2 : G)) (hσfixed e).symm
    simpa [φt] using h.symm
  exact ⟨σ, hσinj, hσ₁, hσ₂⟩

theorem card_le_of_le_sup_of_swap {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y)
    (hinf : ¬ p ∣ Nat.card ↥(X ⊓ Y)) (φ : G →* G) (hφX : ∀ x ∈ X, φ x ∈ Y)
    (hφY : ∀ y ∈ Y, φ y ∈ X)
    (hX : ∀ F : Subgroup G, F ≤ X → IsElemAbelian p F → Nat.card F ≤ p ^ k)
    {E : Subgroup G} (hE : E ≤ X ⊔ Y) (hEel : IsElemAbelian p E)
    (hfix : ∀ e ∈ E, φ e = e) : Nat.card E ≤ p ^ k := by
  obtain ⟨σ, hσinj, hσφ⟩ := exists_pSection_of_swap hp hXY hinf φ hφX hφY hE hEel hfix
  exact card_le_of_pSection_of_swap hX σ φ hσinj hσφ hEel

theorem card_le_of_le_sup_of_fixed {G : Type*} [Group G] [Finite G] {p k₁ k₂ : ℕ}
    (hp : p.Prime) {X W : Subgroup G} (hXW : ∀ x ∈ X, ∀ w ∈ W, Commute x w)
    (hinf : ¬ p ∣ Nat.card ↥(X ⊓ W)) (φ : G →* G) (hφX : ∀ x ∈ X, φ x ∈ X)
    (hφW : ∀ w ∈ W, φ w ∈ W)
    (hX : ∀ F : Subgroup G, F ≤ X → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k₁)
    (hW : ∀ F : Subgroup G, F ≤ W → IsElemAbelian p F → (∀ e ∈ F, φ e = e) →
      Nat.card F ≤ p ^ k₂)
    {E : Subgroup G} (hE : E ≤ X ⊔ W) (hEel : IsElemAbelian p E)
    (hfix : ∀ e ∈ E, φ e = e) : Nat.card E ≤ p ^ (k₁ + k₂) := by
  obtain ⟨σ, hσinj, hσ₁, hσ₂⟩ := exists_pSection_of_fixed hp hXW hinf φ hφX hφW hE hEel hfix
  exact card_le_of_pSection_of_fixed φ hX hW σ hσinj hσ₁ hσ₂ hEel

section TwistImage

open CFSG.LieType.Chevalley


theorem twistHom_mem_subsystemGroup_image {K : Type} [Field K] (σ : K →+* K)
    {S : Set (Fin TwistTag.E6.tag.rank)} {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ subsystemGroup TwistTag.E6.tag K S) :
    twistHom TwistTag.E6 K σ g ∈
      subsystemGroup TwistTag.E6.tag K (TwistTag.E6.perm '' S) := by
  refine ((Subgroup.closure_le
    ((subsystemGroup TwistTag.E6.tag K (TwistTag.E6.perm '' S)).comap
      (twistHom TwistTag.E6 K σ))).2 ?_) hg
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_xUnit]
    exact Subgroup.subset_closure ⟨_, ⟨i, hi, rfl⟩, σ c, Or.inl rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_yUnit]
    exact Subgroup.subset_closure ⟨_, ⟨i, hi, rfl⟩, σ c, Or.inr rfl⟩

end TwistImage

end CFSG.LocalAnalysis.GLTheoremA
