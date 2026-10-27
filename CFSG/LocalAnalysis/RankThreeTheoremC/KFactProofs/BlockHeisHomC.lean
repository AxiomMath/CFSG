module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisAutChain
public import CFSG.GroupTheory.WeirSylow.Defs
public import CFSG.GroupTheory.WeirSylow.SylowTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.GroupTheory.WeirSylow
open CFSG.RankThree.PartOne.OutStructure (Inn)

abbrev HomC (p a r : ℕ) : Type := Fin r → Multiplicative (ZMod (p ^ a))

section HomC

variable {p : ℕ}

theorem zmod_pth_power {a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (c : Multiplicative (ZMod (p ^ a)))
    (hc : c ^ p = 1) : ∃ y : Multiplicative (ZMod (p ^ a)), y ^ p = c := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have h1 : (p : ZMod (p ^ a)) * (Multiplicative.toAdd c) = 0 := by
    have := congrArg Multiplicative.toAdd hc
    simpa [toAdd_pow, nsmul_eq_mul] using this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ZMod (p ^ a)) = Multiplicative.toAdd c :=
    ⟨(Multiplicative.toAdd c).val, ZMod.natCast_zmod_val _⟩
  rw [← hn] at h1
  have h2 : p ^ a ∣ p * n := by
    have : ((p * n : ℕ) : ZMod (p ^ a)) = 0 := by push_cast; exact h1
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have h3 : p ^ (b + 1) ∣ n := by
    have : p * p ^ (b + 1) ∣ p * n := by
      rw [← pow_succ']
      exact h2
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
  obtain ⟨s, hs⟩ := h3
  refine ⟨Multiplicative.ofAdd ((p ^ b * s : ℕ) : ZMod (p ^ (b + 2))), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, ← hn, hs]
  simp only [toAdd_ofAdd, nsmul_eq_mul]
  push_cast
  ring

theorem homC_pth_power {a r : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (x : HomC p a r) (hx : x ^ p = 1) :
    ∃ y : HomC p a r, y ^ p = x := by
  have h : ∀ i, ∃ y : Multiplicative (ZMod (p ^ a)), y ^ p = x i := fun i =>
    zmod_pth_power hp ha (x i) (congrFun hx i)
  choose y hy using h
  exact ⟨y, funext fun i => hy i⟩

theorem zmod_card_torsion_le {a : ℕ} (hp : p.Prime) :
    Nat.card {c : Multiplicative (ZMod (p ^ a)) // c ^ p = 1} ≤ p := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  classical
  haveI : Fintype (Multiplicative (ZMod (p ^ a))) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (p ^ a))) hp.pos
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem homC_card_torsion_le {a r : ℕ} (hp : p.Prime) (hr : r ≤ 1) :
    Nat.card {x : HomC p a r // x ^ p = 1} ≤ p := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
  · have : Subsingleton (HomC p a 0) := inferInstance
    have h1 : Nat.card {x : HomC p a 0 // x ^ p = 1} ≤ 1 := by
      have : Subsingleton {x : HomC p a 0 // x ^ p = 1} := inferInstance
      exact Finite.card_le_one_iff_subsingleton.2 this
    exact h1.trans hp.one_le
  · let e : {x : HomC p a 1 // x ^ p = 1} ≃ {c : Multiplicative (ZMod (p ^ a)) // c ^ p = 1} :=
      { toFun := fun x => ⟨x.1 0, congrFun x.2 0⟩
        invFun := fun c => ⟨fun _ => c.1, funext fun _ => c.2⟩
        left_inv := fun x => by
          apply Subtype.ext
          funext i
          have : i = 0 := Subsingleton.elim _ _
          subst this
          rfl
        right_inv := fun c => rfl }
    rw [Nat.card_congr e]
    exact zmod_card_torsion_le hp

end HomC

section Transport

variable {X : Type*} [Group X] {p : ℕ}

theorem homC_comm {S : Subgroup X} {a r : ℕ} (e : ↥S ≃* HomC p a r) :
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => by
  have := e.injective (a₁ := ⟨x, hx⟩ * ⟨y, hy⟩) (a₂ := ⟨y, hy⟩ * ⟨x, hx⟩)
    (by rw [map_mul, map_mul]; exact mul_comm (e ⟨x, hx⟩) (e ⟨y, hy⟩))
  exact congrArg Subtype.val this

theorem homC_sylow_data (hp : p.Prime) {S : Subgroup X} {a r : ℕ}
    (e : ↥S ≃* HomC p a r) (h : r ≤ 1 ∨ 2 ≤ a) :
    Nat.card {x : S // x ^ p = 1} ≤ p ∨ ∀ x ∈ S, x ^ p = 1 → ∃ y ∈ S, y ^ p = x := by
  rcases h with hr | ha
  · left
    let f : {x : S // x ^ p = 1} ≃ {x : HomC p a r // x ^ p = 1} :=
      { toFun := fun x => ⟨e x.1, by rw [← map_pow, x.2, map_one]⟩
        invFun := fun x => ⟨e.symm x.1, by rw [← map_pow, x.2, map_one]⟩
        left_inv := fun x => by simp
        right_inv := fun x => by simp }
    rw [Nat.card_congr f]
    exact homC_card_torsion_le hp hr
  · right
    intro x hx hxp
    obtain ⟨y, hy⟩ := homC_pth_power hp ha (e ⟨x, hx⟩) (by
      rw [← map_pow]
      have : (⟨x, hx⟩ : S) ^ p = 1 := Subtype.ext hxp
      rw [this, map_one])
    refine ⟨(e.symm y : S), (e.symm y).2, ?_⟩
    have : (e.symm y) ^ p = ⟨x, hx⟩ := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hy]
    exact congrArg Subtype.val this

def torsionSubgroup (S : Subgroup X) (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (p : ℕ) :
    Subgroup X where
  carrier := {x | x ∈ S ∧ x ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haS, hap⟩ ⟨hbS, hbp⟩
    refine ⟨S.mul_mem haS hbS, ?_⟩
    rw [(Commute.mul_pow (hab a haS b hbS) p), hap, hbp, one_mul]
  one_mem' := ⟨S.one_mem, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haS, hap⟩
    exact ⟨S.inv_mem haS, by rw [inv_pow, hap, inv_one]⟩

theorem mem_torsionSubgroup (S : Subgroup X) (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (p : ℕ)
    {x : X} : x ∈ torsionSubgroup S hab p ↔ x ∈ S ∧ x ^ p = 1 := Iff.rfl

theorem torsionSubgroup_card (S : Subgroup X) (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (p : ℕ) :
    Nat.card (torsionSubgroup S hab p) = Nat.card {x : S // x ^ p = 1} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem torsionSubgroup_comm (S : Subgroup X) (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (p : ℕ) :
    IsMulCommutative (torsionSubgroup S hab p) :=
  ⟨⟨fun x y => Subtype.ext (hab x x.2.1 y y.2.1)⟩⟩

end Transport

section Interface

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem noHeisAut_of_abelian_sylow (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) (hCyc : OutPCyc p X)
    (hrk : ∀ A : Subgroup X, IsMulCommutative A → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ 3)
    (hSyl : ∀ S : Sylow p X, (∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x) ∧
      ((∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) →
        Nat.card {x : S // x ^ p = 1} ≤ p ∨
          ∀ x ∈ (S : Subgroup X), x ^ p = 1 → ∃ y ∈ (S : Subgroup X), y ^ p = x)) :
    NoHeisAut p X := by
  refine noHeisAut_of_sylow hp hp5 hZ hCyc fun S => ?_
  obtain ⟨hab, hc3⟩ := hSyl S
  refine ⟨hab, ?_, hc3⟩
  have h1 := hrk _ (torsionSubgroup_comm (S : Subgroup X) hab p) fun x hx => hx.2
  rw [torsionSubgroup_card (S : Subgroup X) hab p] at h1
  exact h1

theorem noHeisAut_of_homC_sylow (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) (hCyc : OutPCyc p X)
    (hrk : ∀ A : Subgroup X, IsMulCommutative A → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ 3)
    (hSyl : ∀ S : Sylow p X, ∃ a r : ℕ, Nonempty (↥(S : Subgroup X) ≃* HomC p a r) ∧
      (r ≤ 1 ∨ ((∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) → 2 ≤ a))) :
    NoHeisAut p X := by
  refine noHeisAut_of_abelian_sylow hp hp5 hZ hCyc hrk fun S => ?_
  obtain ⟨a, r, ⟨e⟩, h⟩ := hSyl S
  refine ⟨homC_comm e, fun hout => homC_sylow_data hp e ?_⟩
  rcases h with hr | h2
  · exact Or.inl hr
  · exact Or.inr (h2 hout)

end Interface

section Sigma

@[expose] def sigmaOf (p a : ℕ) (L : List ℕ) : Type :=
  (i : Fin L.length) → Fin L[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i

instance (p a : ℕ) (L : List ℕ) : Group (sigmaOf p a L) :=
  inferInstanceAs (Group ((i : Fin L.length) → Fin L[i] →
    wreathTower p (Multiplicative (ZMod (p ^ a))) i))

noncomputable def sigmaOfSingle (p a m : ℕ) : sigmaOf p a [m] ≃* HomC p a m where
  toFun f := f ⟨0, by simp⟩
  invFun g := fun i => match i with | ⟨0, _⟩ => g
  left_inv f := by
    funext i
    rcases i with ⟨i, hi⟩
    have : i = 0 := by simpa using hi
    subst this
    rfl
  right_inv g := rfl
  map_mul' f g := rfl

noncomputable def sigmaOfNil (p a : ℕ) : sigmaOf p a [] ≃* HomC p a 0 where
  toFun _ := 1
  invFun _ := fun i => (Fin.elim0 i)
  left_inv f := funext fun i => Fin.elim0 i
  right_inv g := Subsingleton.elim _ _
  map_mul' _ _ := by simp

theorem sigmaOf_equiv_of_eq_single {p a m : ℕ} {L : List ℕ} (h : L = [m]) :
    Nonempty (sigmaOf p a L ≃* HomC p a m) := by
  subst h
  exact ⟨sigmaOfSingle p a m⟩

theorem sigmaOf_equiv_of_eq_nil {p a : ℕ} {L : List ℕ} (h : L = []) :
    Nonempty (sigmaOf p a L ≃* HomC p a 0) := by
  subst h
  exact ⟨sigmaOfNil p a⟩

theorem sigmaModel_equiv_homC {p e a N : ℕ} (hp : p.Prime) (hlt : N / e < p) :
    Nonempty (sigmaModel p e a N ≃* HomC p a (N / e)) := by
  rcases Nat.eq_zero_or_pos (N / e) with h0 | hpos
  · have hd : Nat.digits p (N / e) = [] := by rw [h0]; exact Nat.digits_zero p
    rw [h0]
    exact sigmaOf_equiv_of_eq_nil (p := p) (a := a) hd
  · have hd : Nat.digits p (N / e) = [N / e] := Nat.digits_of_lt p (N / e) hpos.ne' hlt
    exact sigmaOf_equiv_of_eq_single (p := p) (a := a) hd

theorem sylow_equiv_homC_of_sigmaModel {p e a N : ℕ} (hp : p.Prime) (hlt : N / e < p) {G : Type}
    [Group G] (h : ∀ P : Sylow p G, Nonempty (↥P ≃* sigmaModel p e a N)) :
    ∀ P : Sylow p G, Nonempty (↥P ≃* HomC p a (N / e)) := fun P => by
  obtain ⟨φ⟩ := h P
  obtain ⟨ψ⟩ := sigmaModel_equiv_homC (a := a) hp hlt
  exact ⟨φ.trans ψ⟩

end Sigma

section SylowTransfer

variable {p : ℕ} [Fact p.Prime]

theorem sylowShape_of_injective {G H M : Type*} [Group G] [Group H] [Group M] [Finite G]
    (φ : H →* G) (hφ : Function.Injective φ)
    (h : (Nat.card H).factorization p = (Nat.card G).factorization p)
    (hG : ∀ P : Sylow p G, Nonempty (↥P ≃* M)) : ∀ S : Sylow p H, Nonempty (↥S ≃* M) := by
  intro S
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  obtain ⟨e⟩ := hG P
  obtain ⟨f⟩ := nonempty_sylow_mulEquiv_sylow_of_injective φ hφ h P S
  exact ⟨f.symm.trans e⟩

theorem injective_comp_subtype_of_isPGroup {G Q : Type*} [Group G] [Group Q] (ψ : G →* Q)
    (hker : ¬ p ∣ Nat.card ψ.ker) {P : Subgroup G} (hP : IsPGroup p P) :
    Function.Injective (ψ.comp P.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxk : (x : G) ∈ ψ.ker := by simpa using hx
  obtain ⟨k, hk⟩ := hP x
  have h1 : orderOf (x : G) ∣ p ^ k := by
    rw [Subgroup.orderOf_coe x]
    exact orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (x : G) ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hxk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact Subtype.ext hj
  · exfalso
    apply hker
    rw [hj] at h2
    exact (dvd_pow_self p hjpos.ne').trans h2

theorem sylowShape_of_surjective {G Q M : Type*} [Group G] [Group Q] [Group M] [Finite G]
    (π : G →* Q) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    (hG : ∀ P : Sylow p G, Nonempty (↥P ≃* M)) : ∀ S : Sylow p Q, Nonempty (↥S ≃* M) := by
  intro S
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  obtain ⟨e⟩ := hG P
  have hcardG : Nat.card G = Nat.card π.ker * Nat.card Q := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv] at h1
    rw [h1, mul_comm]
  have hQfin : Finite Q := Finite.of_surjective π hπ
  have hfact : (Nat.card G).factorization p = (Nat.card Q).factorization p := by
    rw [hcardG, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  have hinj : Function.Injective (π.comp (P : Subgroup G).subtype) :=
    injective_comp_subtype_of_isPGroup π hker P.isPGroup'
  let H' : Subgroup Q := (π.comp (P : Subgroup G).subtype).range
  have hP : Nat.card (P : Subgroup G) = p ^ (Nat.card G).factorization p := P.card_eq_multiplicity
  have hH' : Nat.card H' = p ^ (Nat.card Q).factorization p := by
    rw [← hfact, ← hP]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact ⟨(Sylow.equiv S (Sylow.ofCard H' hH')).trans
    ((MonoidHom.ofInjective hinj).symm.trans e)⟩

end SylowTransfer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
