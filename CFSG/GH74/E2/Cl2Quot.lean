module

public import CFSG.GH74.E2.Cl2Defs

public section

namespace CFSG.GH74.E2

open Subgroup

variable {P : Type*} [Group P]

@[expose] def quotAut (g : MulAut P) (N : Subgroup P) [N.Normal] (hN : ∀ x, g x ∈ N ↔ x ∈ N) :
    MulAut (P ⧸ N) :=
  QuotientGroup.congr N N g (by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hN x).2 hx
    · intro hy
      refine ⟨g⁻¹ y, ?_, by simp⟩
      rw [← hN]
      simpa using hy)

theorem quotAut_mk (g : MulAut P) (N : Subgroup P) [N.Normal] (hN : ∀ x, g x ∈ N ↔ x ∈ N)
    (x : P) : quotAut g N hN (x : P ⧸ N) = ((g x : P) : P ⧸ N) := by
  simp [quotAut]

theorem quotAut_mul (g h : MulAut P) (N : Subgroup P) [N.Normal] (hg : ∀ x, g x ∈ N ↔ x ∈ N)
    (hh : ∀ x, h x ∈ N ↔ x ∈ N) (hgh : ∀ x, (g * h) x ∈ N ↔ x ∈ N) :
    quotAut (g * h) N hgh = quotAut g N hg * quotAut h N hh := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H x => simp [quotAut_mk, MulAut.mul_apply]

theorem quotAut_one (N : Subgroup P) [N.Normal] (h1 : ∀ x, (1 : MulAut P) x ∈ N ↔ x ∈ N) :
    quotAut (1 : MulAut P) N h1 = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H x => simp [quotAut_mk]

theorem quotAut_pow_three (g : MulAut P) (N : Subgroup P) [N.Normal]
    (hN : ∀ x, g x ∈ N ↔ x ∈ N) (hg : g ^ 3 = 1) : quotAut g N hN ^ 3 = 1 := by
  have h3 : ∀ x, g (g (g x)) = x := fun x => by
    have := congrArg (fun f : MulAut P => f x) hg
    simpa [pow_succ, MulAut.mul_apply] using this
  ext z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have : (quotAut g N hN ^ 3) (x : P ⧸ N) = ((g (g (g x)) : P) : P ⧸ N) := by
      simp [pow_succ, MulAut.mul_apply, quotAut_mk]
    rw [this, h3]
    rfl

theorem exists_fixed_mul_mem [Finite P] (hP : IsPGroup 2 P) {g : MulAut P} (hg : g ^ 3 = 1)
    {N : Subgroup P} [N.Normal] (hN : ∀ x, g x ∈ N ↔ x ∈ N) {x : P} (hx : x⁻¹ * g x ∈ N) :
    ∃ n ∈ N, g (x * n) = x * n := by
  classical
  have h3 : ∀ y, g (g (g y)) = y := fun y => by
    have := congrArg (fun f : MulAut P => f y) hg
    simpa [pow_succ, MulAut.mul_apply] using this
  let X : Set P := {y | x⁻¹ * y ∈ N}
  have hmaps : ∀ y ∈ X, g y ∈ X := by
    intro y hy
    have h1 : x⁻¹ * g y = (x⁻¹ * g x) * g (x⁻¹ * y) := by
      rw [map_mul, map_inv]; group
    show x⁻¹ * g y ∈ N
    rw [h1]
    exact N.mul_mem hx ((hN _).2 hy)
  let φ : X → X := fun y => ⟨g y.1, hmaps y.1 y.2⟩
  let σ : Equiv.Perm X :=
    { toFun := φ
      invFun := fun y => φ (φ y)
      left_inv := fun y => Subtype.ext (h3 y.1)
      right_inv := fun y => Subtype.ext (h3 y.1) }
  have hσ : ∀ y, σ y = φ y := fun y => rfl
  have hσ3' : ∀ y, σ (σ (σ y)) = y := fun y =>
    Subtype.ext (show g (g (g y.1)) = y.1 from h3 y.1)
  have hσ3 : σ ^ 3 = 1 := by
    ext y
    simp [pow_succ, Equiv.Perm.mul_apply, hσ3']
  have hpg : IsPGroup 3 (Subgroup.zpowers σ) := by
    rintro ⟨τ, hτ⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    refine ⟨1, Subtype.ext ?_⟩
    show (σ ^ m) ^ (3 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hσ3]
  have hmod := hpg.card_modEq_card_fixedPoints X
  have hNcard : Nat.card X = Nat.card N := by
    refine (Nat.card_congr (Equiv.mk (fun y : X => (⟨x⁻¹ * y.1, y.2⟩ : N))
      (fun n : N => (⟨x * n.1, by show x⁻¹ * (x * n.1) ∈ N; simp⟩ : X))
      (fun y => Subtype.ext (by simp)) (fun n => Subtype.ext (by simp)))).trans ?_
    rfl
  have hNp : ∃ m, Nat.card N = 2 ^ m := (IsPGroup.iff_card).mp (hP.to_subgroup N)
  have hne : (MulAction.fixedPoints (Subgroup.zpowers σ) X).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have h0 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) X) = 0 := by
      rw [hempty]; simp
    rw [h0] at hmod
    have h3d : 3 ∣ Nat.card X := Nat.modEq_zero_iff_dvd.mp hmod
    obtain ⟨m, hm⟩ := hNp
    rw [hNcard, hm] at h3d
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    omega
  obtain ⟨y, hy⟩ := hne
  have hfix : σ y = y := by
    have := hy ⟨σ, Subgroup.mem_zpowers σ⟩
    exact this
  have hgy : g y.1 = y.1 := congrArg Subtype.val hfix
  exact ⟨x⁻¹ * y.1, y.2, by rw [mul_inv_cancel_left]; exact hgy⟩

theorem fixSub_quotAut [Finite P] (hP : IsPGroup 2 P) {g : MulAut P} (hg : g ^ 3 = 1)
    (N : Subgroup P) [N.Normal] (hN : ∀ x, g x ∈ N ↔ x ∈ N) :
    fixSub (quotAut g N hN) = (fixSub g).map (QuotientGroup.mk' N) := by
  ext z
  rw [mem_fixSub, Subgroup.mem_map]
  constructor
  · intro hz
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [quotAut_mk] at hz
      have hx : x⁻¹ * g x ∈ N := by
        rw [← QuotientGroup.eq]; exact hz.symm
      obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_mem hP hg hN hx
      refine ⟨x * n, hfix, ?_⟩
      show ((x * n : P) : P ⧸ N) = (x : P ⧸ N)
      rw [QuotientGroup.eq]
      simpa using N.inv_mem hn
  · rintro ⟨c, hc, rfl⟩
    rw [mem_fixSub] at hc
    show quotAut g N hN (c : P ⧸ N) = (c : P ⧸ N)
    rw [quotAut_mk, hc]

theorem frattini_inv (g : MulAut P) {x : P} (hx : x ∈ frattini P) : g x ∈ frattini P := by
  have h := frattini_le_comap_frattini_of_surjective
    (φ := (g : P →* P)) (MulEquiv.surjective g)
  exact h hx

private theorem mem_of_mem_map_mk {N A : Subgroup P} [N.Normal] (hNA : N ≤ A) {x : P}
    (hx : (x : P ⧸ N) ∈ A.map (QuotientGroup.mk' N)) : x ∈ A := by
  obtain ⟨m, hm, hmx⟩ := hx
  have h1 : m⁻¹ * x ∈ N := QuotientGroup.eq.mp hmx
  have h2 : x = m * (m⁻¹ * x) := by group
  rw [h2]
  exact A.mul_mem hm (hNA h1)

private theorem mem_frattini_of_forall_coatom {x : P}
    (h : ∀ M : Subgroup P, IsCoatom M → x ∈ M) : x ∈ frattini P := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  exact h M hM

theorem frattini_quotient [Finite P] (N : Subgroup P) [N.Normal] (hN : N ≤ frattini P) :
    frattini (P ⧸ N) = (frattini P).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · intro z hz
    induction z using QuotientGroup.induction_on with
    | H x =>
      refine ⟨x, ?_, rfl⟩
      refine mem_frattini_of_forall_coatom fun M hM => ?_
      have hNM : N ≤ M := hN.trans (frattini_le_coatom hM)
      have hker : (QuotientGroup.mk' N).ker ≤ M := by rwa [QuotientGroup.ker_mk']
      have hcoatom : IsCoatom (M.map (QuotientGroup.mk' N)) := by
        refine ⟨?_, ?_⟩
        · intro htop
          apply hM.1
          have := Subgroup.comap_map_eq_self hker
          rw [htop, Subgroup.comap_top] at this
          exact this.symm
        · intro L hL
          have h1 : M ≤ L.comap (QuotientGroup.mk' N) := by
            have := Subgroup.comap_map_eq_self hker
            rw [← this]
            exact Subgroup.comap_mono hL.le
          have h2 : M < L.comap (QuotientGroup.mk' N) := by
            refine lt_of_le_of_ne h1 fun heq => ?_
            have : L = M.map (QuotientGroup.mk' N) := by
              rw [heq, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
            exact hL.ne this.symm
          have h3 := hM.2 _ h2
          rw [eq_top_iff]
          intro y _
          obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N y
          have : w ∈ L.comap (QuotientGroup.mk' N) := by rw [h3]; trivial
          exact this
      exact mem_of_mem_map_mk hNM (frattini_le_coatom hcoatom hz)
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective N)

theorem BPair.quotient {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) {a b : MulAut Q}
    (h : BPair Q a b) (N : Subgroup Q) [N.Normal] (hNa : ∀ x, a x ∈ N ↔ x ∈ N)
    (hNb : ∀ x, b x ∈ N ↔ x ∈ N) (hNf : N ≤ frattini Q) :
    BPair (Q ⧸ N) (quotAut a N hNa) (quotAut b N hNb) := by
  have ha := fixSub_quotAut hQ h.a_cube N hNa
  have hb := fixSub_quotAut hQ h.b_cube N hNb
  have hf := frattini_quotient N hNf
  have hmapA : fixSub (quotAut a N hNa) ⊔ frattini (Q ⧸ N) =
      (fixSub a ⊔ frattini Q).map (QuotientGroup.mk' N) := by
    rw [ha, hf, Subgroup.map_sup]
  have hmapB : fixSub (quotAut b N hNb) ⊔ frattini (Q ⧸ N) =
      (fixSub b ⊔ frattini Q).map (QuotientGroup.mk' N) := by
    rw [hb, hf, Subgroup.map_sup]
  have hNA : N ≤ fixSub a ⊔ frattini Q := hNf.trans le_sup_right
  have hNB : N ≤ fixSub b ⊔ frattini Q := hNf.trans le_sup_right
  have hab : ∀ x, a (b x) = b (a x) := fun x => by
    have := congrArg (fun f : MulAut Q => f x) h.comm
    simpa [MulAut.mul_apply] using this
  refine ⟨quotAut_pow_three a N hNa h.a_cube, quotAut_pow_three b N hNb h.b_cube, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    induction z using QuotientGroup.induction_on with
    | H x => simp [quotAut_mk, MulAut.mul_apply, hab]
  · rw [hmapA, hmapB, ← Subgroup.map_sup, h.sup_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  · intro z hz
    rw [hmapA, hmapB] at hz
    obtain ⟨hzA, hzB⟩ := hz
    induction z using QuotientGroup.induction_on with
    | H x =>
      have hxA := mem_of_mem_map_mk hNA hzA
      have hxB := mem_of_mem_map_mk hNB hzB
      rw [hf]
      exact ⟨x, h.inf_le ⟨hxA, hxB⟩, rfl⟩
  · intro htop
    apply h.a_ne
    rw [hmapA] at htop
    rw [eq_top_iff]
    intro x _
    exact mem_of_mem_map_mk hNA (by rw [htop]; trivial)
  · intro htop
    apply h.b_ne
    rw [hmapB] at htop
    rw [eq_top_iff]
    intro x _
    exact mem_of_mem_map_mk hNB (by rw [htop]; trivial)

theorem card_modEq_three_fixed [Finite P] {g : MulAut P} (hg : g ^ 3 = 1) (X : Set P)
    (hX : ∀ y ∈ X, g y ∈ X) :
    Nat.card X ≡ Nat.card {y : P | y ∈ X ∧ g y = y} [MOD 3] := by
  classical
  have h3 : ∀ y, g (g (g y)) = y := fun y => by
    have := congrArg (fun f : MulAut P => f y) hg
    simpa [pow_succ, MulAut.mul_apply] using this
  let φ : X → X := fun y => ⟨g y.1, hX y.1 y.2⟩
  let σ : Equiv.Perm X :=
    { toFun := φ
      invFun := fun y => φ (φ y)
      left_inv := fun y => Subtype.ext (h3 y.1)
      right_inv := fun y => Subtype.ext (h3 y.1) }
  have hσ3' : ∀ y, σ (σ (σ y)) = y := fun y =>
    Subtype.ext (show g (g (g y.1)) = y.1 from h3 y.1)
  have hσ3 : σ ^ 3 = 1 := by
    ext y
    simp [pow_succ, Equiv.Perm.mul_apply, hσ3']
  have hpg : IsPGroup 3 (Subgroup.zpowers σ) := by
    rintro ⟨τ, hτ⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    refine ⟨1, Subtype.ext ?_⟩
    show (σ ^ m) ^ (3 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hσ3]
  have hmod := hpg.card_modEq_card_fixedPoints X
  have hcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) X) =
      Nat.card {y : P | y ∈ X ∧ g y = y} := by
    refine Nat.card_congr (Equiv.mk
      (fun y => ⟨y.1.1, y.1.2, by
        have := y.2 ⟨σ, Subgroup.mem_zpowers σ⟩
        exact congrArg Subtype.val this⟩)
      (fun p => ⟨⟨p.1, p.2.1⟩, by
        rintro ⟨τ, hτ⟩
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
        show (σ ^ m) ⟨p.1, p.2.1⟩ = ⟨p.1, p.2.1⟩
        exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
          (Subtype.ext (show g p.1 = p.1 from p.2.2)) m⟩)
      (fun y => Subtype.ext (Subtype.ext rfl)) (fun p => Subtype.ext rfl))
  rw [← hcard]
  exact hmod

end CFSG.GH74.E2
