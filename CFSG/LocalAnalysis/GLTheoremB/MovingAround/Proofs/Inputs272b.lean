module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245
public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.LieType.SeitzGeneration.SingerUCayley

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs272b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245
open CFSG.LieType.SeitzGeneration (companionMat heisDiagMat)

section Lift

variable {Y K : Type*} [Group Y] [Group K]

theorem eq_one_of_pow_coprime {p m : ℕ} {z : Y} (hcop : Nat.Coprime p m) (hz : z ^ m = 1) {k : ℕ}
    (hzk : z ^ p ^ k = 1) : z = 1 := by
  have h1 : orderOf z ∣ Nat.gcd m (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz) (orderOf_dvd_of_pow_eq_one hzk)
  have h2 : Nat.gcd m (p ^ k) = 1 := Nat.Coprime.pow_right k hcop.symm
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem coprime_card_of_pow_eq_one {p m : ℕ} (hp : p.Prime) (hm : Nat.Coprime p m) (S : Subgroup Y)
    [Finite S] (hS : ∀ x ∈ S, x ^ m = 1) : Nat.Coprime p (Nat.card S) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : (x : Y) ^ m = 1 := hS x x.2
  have h2 : (x : Y) ^ p ^ 1 = 1 := by
    rw [pow_one, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have h3 : (x : Y) = 1 := eq_one_of_pow_coprime hm h1 h2
  have h4 : x = 1 := Subtype.ext h3
  rw [h4, orderOf_one] at hx
  exact hp.one_lt.ne hx

end Lift

section Lift2

variable {Y : Type} {K : Type*} [Group Y] [Group K] [Finite Y]

theorem exists_lift {p : ℕ} (hp : p.Prime) (π : Y →* K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (hZ : IsPGroup p π.ker) (X : Subgroup K)
    (hX : Nat.Coprime p (Nat.card X)) :
    ∃ (X₀ : Subgroup Y) (m : ℕ), Nat.Coprime p m ∧ (∀ y, y ∈ X₀ ↔ π y ∈ X ∧ y ^ m = 1) ∧
      X₀.map π = X := by
  classical
  set G : Subgroup Y := X.comap π with hG
  set N : Subgroup G := π.ker.subgroupOf G with hN
  have hNc : N ≤ Subgroup.center G := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 (hker hg) h
  set f : G →* K := π.comp G.subtype with hf
  have hfker : f.ker = N := by
    ext g
    simp [hf, hN, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hfrange : f.range = X := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact g.2
    · intro hx
      obtain ⟨y, rfl⟩ := hπ x
      exact ⟨⟨y, hx⟩, rfl⟩
  have hidx : N.index = Nat.card X := by
    rw [← hfker, Subgroup.index_ker, hfrange]
  have hNp : IsPGroup p N := by
    intro g
    obtain ⟨k, hk⟩ := hZ ⟨(g : G), (Subgroup.mem_subgroupOf.1 g.2)⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : π.ker => (x : Y)) hk
    simpa using this
  have hcop : (Nat.card N).Coprime N.index := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk, hidx]
    exact Nat.Coprime.pow_left k hX
  set K₀ : Subgroup G := CFSG.Semidihedral.centralHallComplement N hNc hcop with hK₀
  have hmem : ∀ g : G, g ∈ K₀ ↔ g ^ N.index = 1 :=
    CFSG.Semidihedral.centralHallComplement_mem_iff N hNc hcop
  refine ⟨K₀.map G.subtype, Nat.card X, hX, fun y => ?_, ?_⟩
  · constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      have h1 := (hmem g).1 hg
      rw [hidx] at h1
      have h2 := congrArg Subtype.val h1
      simpa using h2
    · rintro ⟨hy, hym⟩
      refine ⟨⟨y, hy⟩, (hmem _).2 ?_, rfl⟩
      rw [hidx]
      exact Subtype.ext (by simpa using hym)
  · apply le_antisymm
    · rintro _ ⟨_, ⟨g, -, rfl⟩, rfl⟩
      exact g.2
    · intro x hx
      obtain ⟨y, rfl⟩ := hπ x
      obtain ⟨⟨a, k⟩, hak⟩ :=
        (CFSG.Semidihedral.centralHallComplement_isComplement N hNc hcop).2 (⟨y, hx⟩ : G)
      have ha : π ((a : G) : Y) = 1 := Subgroup.mem_subgroupOf.1 a.2
      refine ⟨((k : G) : Y), ⟨(k : G), k.2, rfl⟩, ?_⟩
      have e1 : ((a : G) : Y) * ((k : G) : Y) = y := by
        have := congrArg Subtype.val hak
        simpa using this
      rw [← e1, map_mul, ha, one_mul]

theorem exists_lift_le_core {p : ℕ} (hp : p.Prime) (π : Y →* K) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center Y) (hZ : IsPGroup p (Subgroup.center Y)) (α : MulAut Y)
    (ᾱ : MulAut K) (hα : ∀ y, π (α y) = ᾱ (π y)) (X : Subgroup K) (hX : Nat.Coprime p (Nat.card X))
    (hfix : ∀ x ∈ X, ᾱ x = x) (hnorm : ∀ c : Y, α c = c → ∀ x ∈ X, π c * x * (π c)⁻¹ ∈ X) :
    ∃ X₀ : Subgroup Y, X₀ ≤ GLAPPrimeCoreOf p (fixSub α) ∧ X₀.map π = X ∧
      ∀ (e : MulAut Y) (ē : MulAut K), (∀ y, π (e y) = ē (π y)) → (∀ x ∈ X, ē x ∈ X) →
        ∀ x ∈ X₀, e x ∈ X₀ := by
  have hZ' : IsPGroup p π.ker := by rw [hker]; exact hZ
  obtain ⟨X₀, m, hm, hmem, hmap⟩ := exists_lift hp π hπ hker.le hZ' X hX
  have hinv : ∀ (e : MulAut Y) (ē : MulAut K), (∀ y, π (e y) = ē (π y)) → (∀ x ∈ X, ē x ∈ X) →
      ∀ x ∈ X₀, e x ∈ X₀ := by
    intro e ē he hē x hx
    obtain ⟨hx1, hx2⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨?_, ?_⟩
    · rw [he]
      exact hē _ hx1
    · rw [← map_pow, hx2, map_one]
  have hfixY : X₀ ≤ fixSub α := by
    intro x hx
    show α x = x
    have hαx : α x ∈ X₀ := hinv α ᾱ hα (fun y hy => by rw [hfix y hy]; exact hy) x hx
    have hz : x⁻¹ * α x ∈ X₀ := X₀.mul_mem (X₀.inv_mem hx) hαx
    have hzk : x⁻¹ * α x ∈ Subgroup.center Y := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hα, hfix _ ((hmem x).1 hx).1, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hZ ⟨_, hzk⟩
    have hk' : (x⁻¹ * α x) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h1 := eq_one_of_pow_coprime hm ((hmem _).1 hz).2 hk'
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  refine ⟨X₀, ?_, hmap, hinv⟩
  apply CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal hfixY
  · intro c hc x hx
    obtain ⟨hx1, hx2⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact hnorm c hc _ hx1
    · rw [conj_pow, hx2, mul_one, mul_inv_cancel]
  · exact coprime_card_of_pow_eq_one hp hm X₀ fun x hx => ((hmem x).1 hx).2

end Lift2

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizer_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A W : Subgroup G}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) (hW2 : IsPGroup 2 W)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    ∃ α ∈ A, α ≠ 1 ∧ ∃ w ∈ W, w ≠ 1 ∧ w * α = α * w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p A := by
    haveI : IsMulCommutative A := hA.1
    refine { exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro a
    exact Subtype.ext (by simpa using hA.2 a a.2)
  haveI : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hAc]
    exact Nat.one_lt_pow two_ne_zero hp.one_lt
  have hWp : ¬ p ∣ Nat.card W := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    exact hp2 this
  have hle := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hAW hWp
  by_contra hcon
  push Not at hcon
  apply hW
  rw [eq_bot_iff]
  refine hle.trans (iSup₂_le fun B hB => ?_)
  intro w hw
  rw [Subgroup.mem_bot]
  obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hw
  have hB1 : B ≠ ⊥ := by
    intro hB0
    rw [hB0, Subgroup.index_bot, hAc] at hB
    have h3 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h3
    omega
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have hbA : ((b : A) : G) ≠ 1 := by
    intro h
    apply hb1
    exact Subtype.ext (Subtype.ext h)
  by_contra hw1
  apply hcon ((b : A) : G) (b : A).2 hbA w hwW hw1
  have := Subgroup.mem_centralizer_iff.1 hwC ((b : A) : G) ⟨(b : A), (b : B).2, rfl⟩
  exact this.symm

theorem eq_of_normalizer_le {W S : Subgroup G} (hW : IsPGroup 2 W) (hSW : S ≤ W)
    (h : ∀ w ∈ W, w ∈ Subgroup.normalizer (S : Set G) → w ∈ S) : S = W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent W := hW.isNilpotent
  have hnc := normalizerCondition_of_isNilpotent (G := W)
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hnc
  have h1 : S.subgroupOf W = ⊤ := by
    apply hnc
    apply le_antisymm _ (Subgroup.le_normalizer)
    intro w hw
    rw [Subgroup.mem_subgroupOf]
    apply h w w.2
    rw [Subgroup.mem_normalizer_iff] at hw ⊢
    intro x
    constructor
    · intro hx
      have h2 := (hw ⟨x, hSW hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 h2
    · intro hx
      have hxW : x ∈ W := by
        have h2 : (w : G) * x * (w : G)⁻¹ ∈ W := hSW hx
        have h3 : (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w : G) ∈ W :=
          W.mul_mem (W.mul_mem (W.inv_mem w.2) h2) w.2
        simpa [mul_assoc] using h3
      have h2 := (hw ⟨x, hxW⟩).2 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 h2
  apply le_antisymm hSW
  intro w hw
  have : (⟨w, hw⟩ : W) ∈ S.subgroupOf W := by rw [h1]; exact Subgroup.mem_top _
  exact this

end Coprime

section Acts

variable {p : ℕ} {F : Type} [Field F] {Y : Type} [Group Y] {H Γ : Subgroup (GL (Fin p) F)}

@[expose] noncomputable def projY (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) : Y →* StatedProj H :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))

theorem projY_apply (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (y : Y) :
    projY θ y = θ (QuotientGroup.mk y) := rfl

theorem projY_surjective (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) :
    Function.Surjective (projY θ) := by
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (θ.symm x)
  exact ⟨y, by rw [projY_apply, hy, MulEquiv.apply_symm_apply]⟩

theorem ker_projY (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) :
    (projY θ).ker = Subgroup.center Y := by
  ext y
  rw [MonoidHom.mem_ker, projY_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem scalar_mul_conj (c : Fˣ) (g A : GL (Fin p) F) :
    (Matrix.GeneralLinearGroup.scalar (Fin p) c * g) * A *
      (Matrix.GeneralLinearGroup.scalar (Fin p) c * g)⁻¹ = g * A * g⁻¹ := by
  calc (Matrix.GeneralLinearGroup.scalar (Fin p) c * g) * A *
        (Matrix.GeneralLinearGroup.scalar (Fin p) c * g)⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin p) c * (g * A * g⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin p) c)⁻¹ := by group
    _ = g * A * g⁻¹ := by
      rw [Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem inducedByConj_scalar_mul {g : GL (Fin p) F} {φ : MulAut (StatedProj H)}
    (h : InducedByConj H g φ) (c : Fˣ) :
    InducedByConj H (Matrix.GeneralLinearGroup.scalar (Fin p) c * g) φ := by
  refine ⟨?_, fun A A' hA => h.2 A A' (by rw [hA, scalar_mul_conj])⟩
  rw [Subgroup.mem_normalizer_iff]
  intro A
  rw [scalar_mul_conj]
  exact Subgroup.mem_normalizer_iff.1 h.1 A

theorem inducedByConj_ext {g : GL (Fin p) F} {φ φ' : MulAut (StatedProj H)}
    (h : InducedByConj H g φ) (h' : InducedByConj H g φ') : φ = φ' := by
  ext x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  have hA : g * (A : GL (Fin p) F) * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 h.1 A).1 A.2
  rw [h.2 A ⟨_, hA⟩ rfl, h'.2 A ⟨_, hA⟩ rfl]

theorem actsAsConj_scalar_mul {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {g : GL (Fin p) F}
    {b : MulAut Y} (h : ActsAsConj H θ g b) (c : Fˣ) :
    ActsAsConj H θ (Matrix.GeneralLinearGroup.scalar (Fin p) c * g) b := by
  obtain ⟨φ, hφ, hb⟩ := h
  exact ⟨φ, inducedByConj_scalar_mul hφ c, hb⟩

theorem actsAsConj_pow {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {g : GL (Fin p) F}
    {b : MulAut Y} (h : ActsAsConj H θ g b) (n : ℕ) : ActsAsConj H θ (g ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using actsAsConj_one H θ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ActsAsConj.mul ih h

theorem actsAsConj_eq [Group.IsPerfect Y] {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {g : GL (Fin p) F} {b b' : MulAut Y} (h : ActsAsConj H θ g b) (h' : ActsAsConj H θ g b') :
    b = b' := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨φ', hφ', hb'⟩ := h'
  have e := inducedByConj_ext hφ hφ'
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) x
  show CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient b _ =
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient b' _
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  apply θ.injective
  have h1 := hb y
  have h2 := hb' y
  simp only [QuotientGroup.mk'_apply]
  rw [h1, h2, e]

@[expose] def CentScalar (H Γ : Subgroup (GL (Fin p) F)) : Prop :=
  ∀ u ∈ Γ, (∀ A ∈ H, ∃ c : Fˣ, u * A * u⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) c * A) →
    ∃ c : Fˣ, u = Matrix.GeneralLinearGroup.scalar (Fin p) c

theorem actsAsConj_exists_scalar (hH1 : CentScalar H Γ) {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {g g' : GL (Fin p) F} (hg : g ∈ Γ) (hg' : g' ∈ Γ) {b : MulAut Y} (h : ActsAsConj H θ g b)
    (h' : ActsAsConj H θ g' b) : ∃ c : Fˣ, g' = Matrix.GeneralLinearGroup.scalar (Fin p) c * g := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨φ', hφ', hb'⟩ := h'
  have e : φ = φ' := by
    ext x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (θ.symm x)
    have hx : x = θ (QuotientGroup.mk y) := by rw [hy, MulEquiv.apply_symm_apply]
    rw [hx, ← hb y, ← hb' y]
  subst e
  obtain ⟨c, hc⟩ := hH1 (g⁻¹ * g') (Γ.mul_mem (Γ.inv_mem hg) hg') (by
    intro A hA
    have h1 : g * A * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hφ.1 A).1 hA
    have h2 : g' * A * g'⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hφ'.1 A).1 hA
    have e1 := hφ.2 ⟨A, hA⟩ ⟨_, h1⟩ rfl
    have e2 := hφ'.2 ⟨A, hA⟩ ⟨_, h2⟩ rfl
    rw [e1, QuotientGroup.eq, Subgroup.mem_subgroupOf] at e2
    obtain ⟨c, hc⟩ := e2
    refine ⟨c, ?_⟩
    have hc' : g' * A * g'⁻¹ = (g * A * g⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin p) c := by
      have : ((⟨_, h1⟩ : H)⁻¹ * ⟨_, h2⟩ : H) = (⟨g * A * g⁻¹, h1⟩ : H)⁻¹ * ⟨g' * A * g'⁻¹, h2⟩ := rfl
      have h3 : (Matrix.GeneralLinearGroup.scalar (Fin p) c : GL (Fin p) F) =
          (g * A * g⁻¹)⁻¹ * (g' * A * g'⁻¹) := hc
      rw [h3]
      group
    calc g⁻¹ * g' * A * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * A * g'⁻¹) * g := by group
      _ = g⁻¹ * ((g * A * g⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin p) c) * g := by rw [hc']
      _ = A * (g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin p) c * g) := by group
      _ = A * Matrix.GeneralLinearGroup.scalar (Fin p) c := by
        rw [mul_assoc g⁻¹, Matrix.GeneralLinearGroup.scalar_commute c g, inv_mul_cancel_left]
      _ = Matrix.GeneralLinearGroup.scalar (Fin p) c * A :=
        (Matrix.GeneralLinearGroup.scalar_commute c A).symm)
  refine ⟨c, ?_⟩
  calc g' = g * (g⁻¹ * g') := by group
    _ = g * Matrix.GeneralLinearGroup.scalar (Fin p) c := by rw [hc]
    _ = Matrix.GeneralLinearGroup.scalar (Fin p) c * g :=
      (Matrix.GeneralLinearGroup.scalar_commute c g).symm

theorem actsAsConj_one_scalar (hH1 : CentScalar H Γ) {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {g : GL (Fin p) F} (hg : g ∈ Γ) (h : ActsAsConj H θ g 1) :
    ∃ c : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin p) c := by
  obtain ⟨c, hc⟩ := actsAsConj_exists_scalar hH1 Γ.one_mem hg (actsAsConj_one H θ) h
  exact ⟨c, by rw [hc, mul_one]⟩

theorem actsAsConj_scalar (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (c : Fˣ) :
    ActsAsConj H θ (Matrix.GeneralLinearGroup.scalar (Fin p) c) 1 := by
  have h := actsAsConj_scalar_mul (actsAsConj_one H θ) c
  rwa [mul_one] at h

theorem actsAsConj_comm (hH1 : CentScalar H Γ) {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {g g' : GL (Fin p) F} (hg : g ∈ Γ) (hg' : g' ∈ Γ) {b b' : MulAut Y} (h : ActsAsConj H θ g b)
    (h' : ActsAsConj H θ g' b') (hbb : b * b' = b' * b) :
    ∃ c : Fˣ, g' * g = Matrix.GeneralLinearGroup.scalar (Fin p) c * (g * g') := by
  have h1 := ActsAsConj.mul h h'
  have h2 := ActsAsConj.mul h' h
  rw [← hbb] at h2
  exact actsAsConj_exists_scalar hH1 (Γ.mul_mem hg hg') (Γ.mul_mem hg' hg) h1 h2

theorem scalar_mul_comm (c : Fˣ) (g : GL (Fin p) F) :
    Matrix.GeneralLinearGroup.scalar (Fin p) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin p) c :=
  Matrix.GeneralLinearGroup.scalar_commute c g

end Acts

section Rot

variable {p : ℕ} [NeZero p]

theorem exists_nsmul_eq_of_ne_zero (hp : p.Prime) {d : Fin p} (hd : d ≠ 0) (b : Fin p) :
    ∃ m : ℕ, m • d = b := by
  have hord : addOrderOf d = p := by
    have h1 : addOrderOf d ∣ p := by
      have := addOrderOf_dvd_card (x := d)
      simpa using this
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hd
    · exact h
  have htop : AddSubgroup.zmultiples d = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hb : b ∈ AddSubgroup.zmultiples d := by rw [htop]; exact AddSubgroup.mem_top b
  rw [← mem_multiples_iff_mem_zmultiples] at hb
  obtain ⟨m, hm⟩ := hb
  exact ⟨m, hm⟩

theorem perm_eq_bot_of_addRight (hp : p.Prime) (G' : Subgroup (Equiv.Perm (Fin p)))
    (hG : ¬ p ∣ Nat.card G')
    (hrot : ∀ σ ∈ G', Equiv.addRight (1 : Fin p) * σ * (Equiv.addRight (1 : Fin p))⁻¹ ∈ G')
    (hrot' : ∀ σ ∈ G', (Equiv.addRight (1 : Fin p))⁻¹ * σ * Equiv.addRight (1 : Fin p) ∈ G') :
    G' = ⊥ := by
  classical
  have hrotm : ∀ (m : ℕ), ∀ σ ∈ G', Equiv.addRight ((m : ℕ) • (1 : Fin p)) * σ *
      (Equiv.addRight ((m : ℕ) • (1 : Fin p)))⁻¹ ∈ G' := by
    intro m
    induction m with
    | zero => intro σ hσ; simpa using hσ
    | succ m ih =>
      intro σ hσ
      have e : Equiv.addRight ((m + 1 : ℕ) • (1 : Fin p)) =
          Equiv.addRight (1 : Fin p) * Equiv.addRight ((m : ℕ) • (1 : Fin p)) := by
        ext x
        simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight, succ_nsmul]
        rw [add_assoc]
      rw [e, mul_inv_rev]
      have := hrot _ (ih σ hσ)
      simpa [mul_assoc] using this
  have hrotm' : ∀ (m : ℕ), ∀ σ ∈ G', (Equiv.addRight ((m : ℕ) • (1 : Fin p)))⁻¹ * σ *
      Equiv.addRight ((m : ℕ) • (1 : Fin p)) ∈ G' := by
    intro m
    induction m with
    | zero => intro σ hσ; simpa using hσ
    | succ m ih =>
      intro σ hσ
      have e : Equiv.addRight ((m + 1 : ℕ) • (1 : Fin p)) =
          Equiv.addRight ((m : ℕ) • (1 : Fin p)) * Equiv.addRight (1 : Fin p) := by
        ext x
        simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight, succ_nsmul]
        rw [add_assoc, add_comm (1 : Fin p)]
      rw [e, mul_inv_rev]
      have := hrot' _ (ih σ hσ)
      simpa [mul_assoc] using this
  have h10 : (1 : Fin p) ≠ 0 := by
    rw [Ne, Fin.ext_iff, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt hp.one_lt]
    exact one_ne_zero
  have hsh : ∀ a : Fin p, ∀ σ ∈ G', Equiv.addRight a * σ * (Equiv.addRight a)⁻¹ ∈ G' := by
    intro a σ hσ
    obtain ⟨m, hm⟩ := exists_nsmul_eq_of_ne_zero hp h10 a
    have := hrotm m σ hσ
    rwa [hm] at this
  have hsh' : ∀ a : Fin p, ∀ σ ∈ G', (Equiv.addRight a)⁻¹ * σ * Equiv.addRight a ∈ G' := by
    intro a σ hσ
    obtain ⟨m, hm⟩ := exists_nsmul_eq_of_ne_zero hp h10 a
    have := hrotm' m σ hσ
    rwa [hm] at this
  have hadd : ∀ σ₁ ∈ G', ∀ σ₂ ∈ G', ∃ τ ∈ G', τ 0 = σ₂ 0 + σ₁ 0 := by
    intro σ₁ h₁ σ₂ h₂
    refine ⟨(Equiv.addRight (σ₁ 0) * σ₂ * (Equiv.addRight (σ₁ 0))⁻¹) * σ₁,
      G'.mul_mem (hsh _ σ₂ h₂) h₁, ?_⟩
    simp
  by_cases hex : ∃ σ ∈ G', σ 0 ≠ 0
  · exfalso
    obtain ⟨σ, hσ, hσ0⟩ := hex
    have hmul : ∀ m : ℕ, ∃ τ ∈ G', τ 0 = m • σ 0 := by
      intro m
      induction m with
      | zero => exact ⟨1, G'.one_mem, by simp⟩
      | succ m ih =>
        obtain ⟨τ, hτ, hτ0⟩ := ih
        obtain ⟨τ', hτ', hτ'0⟩ := hadd σ hσ τ hτ
        exact ⟨τ', hτ', by rw [hτ'0, hτ0, succ_nsmul]⟩
    have horb : MulAction.orbit G' (0 : Fin p) = Set.univ := by
      ext b
      simp only [Set.mem_univ, iff_true]
      obtain ⟨m, hm⟩ := exists_nsmul_eq_of_ne_zero hp hσ0 b
      obtain ⟨τ, hτ, hτ0⟩ := hmul m
      exact ⟨⟨τ, hτ⟩, by rw [← hm, ← hτ0]; rfl⟩
    have hidx := MulAction.index_stabilizer G' (0 : Fin p)
    rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hidx
    apply hG
    have h1 := Subgroup.index_dvd_card (MulAction.stabilizer G' (0 : Fin p))
    rwa [hidx] at h1
  · push Not at hex
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    ext j
    have h1 := hex _ (hsh' j σ hσ)
    simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight, zero_add] at h1
    rw [Equiv.Perm.inv_eq_iff_eq, Equiv.coe_addRight] at h1
    simp only [zero_add] at h1
    simp [h1]

end Rot

section Mat

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem eq_diagonal_of_mul_diagonal {X : Matrix (Fin p) (Fin p) F} {δ : Fin p → F}
    (hδ : Function.Injective δ) (h : X * diagonal δ = diagonal δ * X) :
    X = diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [diagonal_apply_ne _ hij]
    have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    have h2 : X i j * (δ j - δ i) = 0 := by rw [mul_sub, h1]; ring
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (hδ (sub_eq_zero.1 h3)).symm hij

theorem exists_ne_zero_row {U : Matrix (Fin p) (Fin p) F} (hU : IsUnit U) (i : Fin p) :
    ∃ j, U i j ≠ 0 := by
  by_contra h
  push Not at h
  exact ((Matrix.isUnit_iff_isUnit_det U).1 hU).ne_zero (Matrix.det_eq_zero_of_row_eq_zero i h)

theorem exists_ne_zero_col {U : Matrix (Fin p) (Fin p) F} (hU : IsUnit U) (j : Fin p) :
    ∃ i, U i j ≠ 0 := by
  by_contra h
  push Not at h
  exact ((Matrix.isUnit_iff_isUnit_det U).1 hU).ne_zero (Matrix.det_eq_zero_of_column_eq_zero j h)

theorem exists_perm_of_rows {U : Matrix (Fin p) (Fin p) F} (hU : IsUnit U)
    (hrow : ∀ i j j', U i j ≠ 0 → U i j' ≠ 0 → j = j') :
    ∃ τ : Equiv.Perm (Fin p), ∀ t : Fin p → F, U * diagonal t = diagonal (t ∘ τ) * U := by
  classical
  choose f hf using exists_ne_zero_row hU
  have hfu : ∀ i j, U i j ≠ 0 → j = f i := fun i j h => hrow i j (f i) h (hf i)
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := exists_ne_zero_col hU j
    exact ⟨i, (hfu i j hi).symm⟩
  have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  refine ⟨Equiv.ofBijective f hbij, fun t => ?_⟩
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases h : U i j = 0
  · rw [h, zero_mul, mul_zero]
  · have hj := hfu i j h
    subst hj
    simp [mul_comm]

theorem exists_perm_of_separating {U : Matrix (Fin p) (Fin p) F} (hU : IsUnit U)
    (T : Set (Fin p → F)) (hT : ∀ j j', j ≠ j' → ∃ t ∈ T, t j ≠ t j')
    (hUT : ∀ t ∈ T, ∃ t' : Fin p → F, U * diagonal t = diagonal t' * U) :
    ∃ τ : Equiv.Perm (Fin p), ∀ t : Fin p → F, U * diagonal t = diagonal (t ∘ τ) * U := by
  apply exists_perm_of_rows hU
  intro i j j' hj hj'
  by_contra hne
  obtain ⟨t, htT, htj⟩ := hT j j' hne
  obtain ⟨t', ht'⟩ := hUT t htT
  have e : ∀ k, U i k ≠ 0 → t k = t' i := by
    intro k hk
    have h1 := congrFun (congrFun ht' i) k
    rw [mul_diagonal, diagonal_mul] at h1
    have h2 : (t k - t' i) * U i k = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hk
  exact htj ((e j hj).trans (e j' hj').symm)

theorem eq_diagonal_of_forall {U : Matrix (Fin p) (Fin p) F}
    (h : ∀ t : Fin p → F, U * diagonal t = diagonal t * U) : U = diagonal (fun i => U i i) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [diagonal_apply_ne _ hij]
    have h1 := congrFun (congrFun (h (Pi.single j 1)) i) j
    rw [mul_diagonal, diagonal_mul] at h1
    simpa [Pi.single_apply, hij] using h1

theorem card_ne_eq_of_conj {X : Matrix (Fin p) (Fin p) F} (hX : IsUnit X) {e f : Fin p → F}
    (h : X * diagonal e = diagonal f * X) (a : F) :
    Nat.card {i // e i - a ≠ 0} = Nat.card {i // f i - a ≠ 0} := by
  classical
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  have h1 : X * diagonal (fun i => e i - a) = diagonal (fun i => f i - a) * X := by
    have ha : X * diagonal (fun _ => a) = diagonal (fun _ => a) * X := by
      ext i j
      rw [mul_diagonal, diagonal_mul, mul_comm]
    rw [← diagonal_sub, ← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, h, ha]
  have h2 := congrArg Matrix.rank h1
  rw [rank_mul_eq_right_of_isUnit_det X _ hdet, rank_mul_eq_left_of_isUnit_det X _ hdet,
    rank_diagonal, rank_diagonal] at h2
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end Mat

section Claim

open Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem diag_of_claim (hp : p.Prime) (M h : GL (Fin p) F) {c : F}
    (hh : ((M⁻¹ * h * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p c)
    (S R : Subgroup (GL (Fin p) F))
    (hSd : ∀ x ∈ S, ∃ t, ((M⁻¹ * x * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal t)
    (hSh : ∀ x ∈ S, h * x * h⁻¹ ∈ S)
    (hSn : ∃ x ∈ S, ∀ a : Fˣ, x ≠ Matrix.GeneralLinearGroup.scalar (Fin p) a)
    (hRS : ∀ y ∈ R, ∀ x ∈ S, y * x * y⁻¹ ∈ S)
    (hRh : ∀ y ∈ R, h * y * h⁻¹ ∈ R) (hRh' : ∀ y ∈ R, h⁻¹ * y * h ∈ R)
    (hRp : ∀ y ∈ R, ∃ m, Nat.Coprime p m ∧
      ∃ a : Fˣ, y ^ m = Matrix.GeneralLinearGroup.scalar (Fin p) a) :
    ∀ y ∈ R, ∃ t, ((M⁻¹ * y * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal t := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set U : GL (Fin p) F → Matrix (Fin p) (Fin p) F :=
    fun x => ((M⁻¹ * x * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) with hUdef
  have hUmul : ∀ x y, U (x * y) = U x * U y := by
    intro x y
    simp only [hUdef]
    rw [← Units.val_mul]
    congr 1
    group
  have hUone : U 1 = 1 := by simp [hUdef]
  have hUinv : ∀ x, U x⁻¹ * U x = 1 := by intro x; rw [← hUmul, inv_mul_cancel, hUone]
  have hUinv' : ∀ x, U x * U x⁻¹ = 1 := by intro x; rw [← hUmul, mul_inv_cancel, hUone]
  have hUunit : ∀ x, IsUnit (U x) := fun x => (M⁻¹ * x * M).isUnit
  have hUpow : ∀ x (n : ℕ), U (x ^ n) = U x ^ n := by
    intro x n
    induction n with
    | zero => simp [hUone]
    | succ n ih => rw [pow_succ, hUmul, ih, pow_succ]
  have hUsc : ∀ a : Fˣ, U (Matrix.GeneralLinearGroup.scalar (Fin p) a) = (a : F) • 1 := by
    intro a
    simp only [hUdef]
    rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute a M, ← mul_assoc, inv_mul_cancel,
      one_mul, CFSG.LieType.SeitzGeneration.coe_scalarGL]
  set χ : GL (Fin p) F → Fin p → F := fun x i => U x i i with hχ
  have hSχ : ∀ x ∈ S, U x = diagonal (χ x) := by
    intro x hx
    obtain ⟨t, ht⟩ := hSd x hx
    have e : χ x = t := funext fun i => by simp only [hχ]; rw [show U x = diagonal t from ht]; simp
    rw [e]
    exact ht
  have hCd : ∀ t : Fin p → F, U h * diagonal t = diagonal (fun i => t (i - 1)) * U h := by
    intro t
    rw [show U h = companionMat p c from hh]
    exact CFSG.LieType.SeitzGeneration.thmU_companionMat_mul_diagonal c t
  have hCd' : ∀ t : Fin p → F, U h⁻¹ * diagonal t = diagonal (fun i => t (i + 1)) * U h⁻¹ := by
    intro t
    have h1 := hCd (fun i => t (i + 1))
    simp only [sub_add_cancel] at h1
    calc U h⁻¹ * diagonal t = U h⁻¹ * (diagonal t * U h) * U h⁻¹ := by
          rw [Matrix.mul_assoc (U h⁻¹), Matrix.mul_assoc (diagonal t), hUinv', Matrix.mul_one]
      _ = U h⁻¹ * (U h * diagonal (fun i => t (i + 1))) * U h⁻¹ := by rw [h1]
      _ = diagonal (fun i => t (i + 1)) * U h⁻¹ := by
          rw [← Matrix.mul_assoc, hUinv, Matrix.one_mul]
  have hshift : ∀ x ∈ S, χ (h * x * h⁻¹) = fun i => χ x (i - 1) := by
    intro x hx
    have e : U (h * x * h⁻¹) = diagonal (fun i => χ x (i - 1)) := by
      rw [hUmul, hUmul, hSχ x hx, hCd, Matrix.mul_assoc, hUinv', Matrix.mul_one]
    funext i
    show U (h * x * h⁻¹) i i = χ x (i - 1)
    rw [e, diagonal_apply_eq]
  have hshiftm : ∀ m : ℕ, ∀ x ∈ S, h ^ m * x * (h ^ m)⁻¹ ∈ S ∧
      χ (h ^ m * x * (h ^ m)⁻¹) = fun i => χ x (i - m • (1 : Fin p)) := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      have e : h ^ (m + 1) * x * (h ^ (m + 1))⁻¹ = h * (h ^ m * x * (h ^ m)⁻¹) * h⁻¹ := by
        rw [pow_succ']; group
      rw [e]
      refine ⟨hSh _ h1, ?_⟩
      rw [hshift _ h1, h2]
      funext i
      simp only
      rw [show i - 1 - m • (1 : Fin p) = i - (m + 1) • (1 : Fin p) by rw [succ_nsmul]; abel]
  have h10 : (1 : Fin p) ≠ 0 := by
    rw [Ne, Fin.ext_iff, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt hp.one_lt]
    exact one_ne_zero
  have hsep : ∀ i j : Fin p, i ≠ j → ∃ x ∈ S, χ x i ≠ χ x j := by
    intro i₀ j₀ hij
    by_contra hcon
    push Not at hcon
    have hd : ∀ x ∈ S, ∀ i, χ x i = χ x (i + (j₀ - i₀)) := by
      intro x hx i
      obtain ⟨m, hm⟩ := exists_nsmul_eq_of_ne_zero hp h10 (i₀ - i)
      obtain ⟨h1, h2⟩ := hshiftm m x hx
      have e := hcon _ h1
      rw [h2] at e
      simp only at e
      rw [hm] at e
      rw [show i = i₀ - (i₀ - i) by abel, show i₀ - (i₀ - i) + (j₀ - i₀) = j₀ - (i₀ - i) by abel]
      exact e
    have hdm : ∀ m : ℕ, ∀ x ∈ S, ∀ i, χ x i = χ x (i + m • (j₀ - i₀)) := by
      intro m
      induction m with
      | zero => intro x hx i; simp
      | succ m ih =>
        intro x hx i
        rw [ih x hx i, hd x hx (i + m • (j₀ - i₀)), succ_nsmul, add_assoc]
    have hd0 : j₀ - i₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hij)
    obtain ⟨m₁, hm₁⟩ := exists_nsmul_eq_of_ne_zero hp hd0 1
    have hd1 : ∀ x ∈ S, ∀ i, χ x i = χ x (i + 1) := by
      intro x hx i
      have := hdm m₁ x hx i
      rwa [hm₁] at this
    have hconst : ∀ x ∈ S, ∀ i, χ x i = χ x 0 := by
      intro x hx i
      obtain ⟨m, rfl⟩ := exists_nsmul_eq_of_ne_zero hp h10 i
      induction m with
      | zero => simp
      | succ m ih => rw [succ_nsmul, ← hd1 x hx, ih]
    obtain ⟨x, hx, hxs⟩ := hSn
    have hx0 : χ x 0 ≠ 0 := by
      intro h0
      have : U x = 0 := by
        rw [hSχ x hx]
        ext i j
        by_cases hij : i = j
        · subst hij; simp [hconst x hx i, h0]
        · simp [diagonal_apply_ne _ hij]
      have h1 := hUinv' x
      rw [this, Matrix.zero_mul] at h1
      exact zero_ne_one (congrFun (congrFun h1 0) 0)
    apply hxs (Units.mk0 _ hx0)
    have e1 : U x = (χ x 0) • 1 := by
      rw [hSχ x hx]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hconst x hx i]
      · simp [diagonal_apply_ne _ hij, hij]
    apply Units.ext
    have e2 : (x : Matrix (Fin p) (Fin p) F) = (M : Matrix (Fin p) (Fin p) F) * U x *
        ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      simp only [hUdef]
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e2, e1, CFSG.LieType.SeitzGeneration.coe_scalarGL, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rfl
  have hmono : ∀ y ∈ R, ∃ τ : Equiv.Perm (Fin p), ∀ t, U y * diagonal t = diagonal (t ∘ τ) * U y := by
    intro y hy
    refine exists_perm_of_separating (hUunit y) {t | ∃ x ∈ S, χ x = t} ?_ ?_
    · intro j j' hjj'
      obtain ⟨x, hx, hne⟩ := hsep j j' hjj'
      exact ⟨χ x, ⟨x, hx, rfl⟩, hne⟩
    · rintro t ⟨x, hx, rfl⟩
      refine ⟨χ (y * x * y⁻¹), ?_⟩
      rw [← hSχ x hx, ← hSχ _ (hRS y hy x hx), ← hUmul, ← hUmul]
      congr 1
      group
  let G' : Subgroup (Equiv.Perm (Fin p)) :=
    { carrier := {σ | ∃ y ∈ R, ∀ t, U y * diagonal t = diagonal (t ∘ σ) * U y}
      mul_mem' := by
        rintro σ₁ σ₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
        refine ⟨y₂ * y₁, R.mul_mem hy₂ hy₁, fun t => ?_⟩
        rw [hUmul, Matrix.mul_assoc, h₁, ← Matrix.mul_assoc, h₂, Matrix.mul_assoc]
        rfl
      one_mem' := ⟨1, R.one_mem, fun t => by rw [hUone]; simp⟩
      inv_mem' := by
        rintro σ ⟨y, hy, hσ⟩
        refine ⟨y⁻¹, R.inv_mem hy, fun t => ?_⟩
        have h1 := hσ (t ∘ ⇑σ⁻¹)
        have e : (t ∘ ⇑σ⁻¹) ∘ ⇑σ = t := by
          funext i
          simp
        rw [e] at h1
        calc U y⁻¹ * diagonal t = U y⁻¹ * (diagonal t * U y) * U y⁻¹ := by
              rw [Matrix.mul_assoc (U y⁻¹), Matrix.mul_assoc (diagonal t), hUinv', Matrix.mul_one]
          _ = U y⁻¹ * (U y * diagonal (t ∘ ⇑σ⁻¹)) * U y⁻¹ := by rw [h1]
          _ = diagonal (t ∘ ⇑σ⁻¹) * U y⁻¹ := by rw [← Matrix.mul_assoc, hUinv, Matrix.one_mul] }
  have hGpow : ∀ σ ∈ G', ∀ y ∈ R, (∀ t, U y * diagonal t = diagonal (t ∘ σ) * U y) →
      ∀ n : ℕ, ∀ t, U (y ^ n) * diagonal t = diagonal (t ∘ ⇑(σ ^ n)) * U (y ^ n) := by
    intro σ _ y _ hσ n
    induction n with
    | zero => intro t; simp [hUone]
    | succ n ih =>
      intro t
      rw [pow_succ, hUmul, Matrix.mul_assoc, hσ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        pow_succ']
      rfl
  have hGp : ¬ p ∣ Nat.card G' := by
    intro hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨y, hy, hyσ⟩ := (σ : Equiv.Perm (Fin p)).2 |> fun h => (σ.2 : (σ : Equiv.Perm (Fin p)) ∈ G')
    obtain ⟨m, hm, a, ha⟩ := hRp y hy
    have h1 := hGpow σ σ.2 y hy hyσ m
    rw [ha, hUsc] at h1
    have h2 : (σ : Equiv.Perm (Fin p)) ^ m = 1 := by
      apply Equiv.ext
      intro j
      have h3 := congrFun (congrFun (h1 (Pi.single j 1)) j) j
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply,
        Matrix.smul_apply, diagonal_apply_eq, diagonal_apply_eq] at h3
      simp only [Function.comp_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
      have h4 := mul_left_cancel₀ a.ne_zero (h3.symm.trans (mul_one (a : F)).symm)
      rw [Pi.single_apply] at h4
      split_ifs at h4 with hc
      · rw [hc]; rfl
      · exact absurd h4 zero_ne_one
    have h5 : orderOf σ ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext h2
    rw [hσ] at h5
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hm h5
  have hconj : ∀ (g : GL (Fin p) F) (ρ : Equiv.Perm (Fin p)),
      (∀ t, U g * diagonal t = diagonal (t ∘ ⇑ρ) * U g) →
      ∀ (y : GL (Fin p) F) (σ : Equiv.Perm (Fin p)), (∀ t, U y * diagonal t = diagonal (t ∘ ⇑σ) * U y) →
      ∀ t, U (g * y * g⁻¹) * diagonal t = diagonal (t ∘ ⇑(ρ⁻¹ * σ * ρ)) * U (g * y * g⁻¹) := by
    intro g ρ hρ y σ hσ t
    have hρ' : ∀ t, U g⁻¹ * diagonal t = diagonal (t ∘ ⇑ρ⁻¹) * U g⁻¹ := by
      intro t
      have h1 := hρ (t ∘ ⇑ρ⁻¹)
      have e : (t ∘ ⇑ρ⁻¹) ∘ ⇑ρ = t := by funext i; simp
      rw [e] at h1
      calc U g⁻¹ * diagonal t = U g⁻¹ * (diagonal t * U g) * U g⁻¹ := by
            rw [Matrix.mul_assoc (U g⁻¹), Matrix.mul_assoc (diagonal t), hUinv', Matrix.mul_one]
        _ = U g⁻¹ * (U g * diagonal (t ∘ ⇑ρ⁻¹)) * U g⁻¹ := by rw [h1]
        _ = diagonal (t ∘ ⇑ρ⁻¹) * U g⁻¹ := by rw [← Matrix.mul_assoc, hUinv, Matrix.one_mul]
    rw [hUmul, hUmul]
    calc U g * U y * U g⁻¹ * diagonal t
        = U g * (U y * (U g⁻¹ * diagonal t)) := by simp only [Matrix.mul_assoc]
      _ = U g * ((U y * diagonal (t ∘ ⇑ρ⁻¹)) * U g⁻¹) := by
          rw [hρ']; simp only [Matrix.mul_assoc]
      _ = (U g * diagonal ((t ∘ ⇑ρ⁻¹) ∘ ⇑σ)) * (U y * U g⁻¹) := by
          rw [hσ]; simp only [Matrix.mul_assoc]
      _ = diagonal (((t ∘ ⇑ρ⁻¹) ∘ ⇑σ) ∘ ⇑ρ) * (U g * U y * U g⁻¹) := by
          rw [hρ]; simp only [Matrix.mul_assoc]
      _ = diagonal (t ∘ ⇑(ρ⁻¹ * σ * ρ)) * (U g * U y * U g⁻¹) := rfl
  have hCdρ : ∀ t, U h * diagonal t = diagonal (t ∘ ⇑(Equiv.addRight (1 : Fin p))⁻¹) * U h := by
    intro t
    rw [hCd]
    congr 2
    funext i
    simp [Equiv.Perm.inv_def, sub_eq_add_neg]
  have hCdρ' : ∀ t, U h⁻¹ * diagonal t = diagonal (t ∘ ⇑(Equiv.addRight (1 : Fin p))) * U h⁻¹ := by
    intro t
    rw [hCd']
    rfl
  have hrot : ∀ σ ∈ G', Equiv.addRight (1 : Fin p) * σ * (Equiv.addRight (1 : Fin p))⁻¹ ∈ G' := by
    rintro σ ⟨y, hy, hσ⟩
    refine ⟨h * y * h⁻¹, hRh y hy, fun t => ?_⟩
    have := hconj h _ hCdρ y σ hσ t
    rwa [inv_inv] at this
  have hrot' : ∀ σ ∈ G', (Equiv.addRight (1 : Fin p))⁻¹ * σ * Equiv.addRight (1 : Fin p) ∈ G' := by
    rintro σ ⟨y, hy, hσ⟩
    refine ⟨h⁻¹ * y * h, hRh' y hy, fun t => ?_⟩
    have := hconj h⁻¹ _ hCdρ' y σ hσ t
    rwa [inv_inv] at this
  have hG' := perm_eq_bot_of_addRight hp G' hGp hrot hrot'
  intro y hy
  obtain ⟨τ, hτ⟩ := hmono y hy
  have hτ1 : τ = 1 := by
    have : τ ∈ G' := ⟨y, hy, hτ⟩
    rw [hG'] at this
    exact Subgroup.mem_bot.1 this
  subst hτ1
  refine ⟨_, eq_diagonal_of_forall fun t => ?_⟩
  have := hτ t
  rw [Equiv.Perm.coe_one, Function.comp_id] at this
  exact this

end Claim

section Normal

open Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem exists_normal_form (hp : p.Prime) {x y : GL (Fin p) F} {w c l : Fˣ}
    (hw : IsPrimitiveRoot (w : F) p) (hxp : x ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) c)
    (hyp : y ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) (l ^ p))
    (hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin p) w * (x * y)) :
    ∃ (M : GL (Fin p) F) (δ₀ : F), δ₀ ≠ 0 ∧
      ((M⁻¹ * y * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        diagonal (fun k : Fin p => δ₀ * (w : F) ^ (k : ℕ)) ∧
      ((M⁻¹ * x * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p (c : F) := by
  set y' : GL (Fin p) F := Matrix.GeneralLinearGroup.scalar (Fin p) l⁻¹ * y with hy'
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin p) l⁻¹) y :=
    Matrix.GeneralLinearGroup.scalar_commute l⁻¹ y
  have hy'p : y' ^ p = 1 := by
    rw [hy', hcomm.mul_pow, hyp, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hxp' : (x : Matrix (Fin p) (Fin p) F) ^ p = (c : F) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hxp, CFSG.LieType.SeitzGeneration.coe_scalarGL]
  have hy'p' : (y' : Matrix (Fin p) (Fin p) F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy'p, Units.val_one]
  have hrel : y' * x = Matrix.GeneralLinearGroup.scalar (Fin p) w * (x * y') := by
    have hs : ∀ g : GL (Fin p) F, Commute (Matrix.GeneralLinearGroup.scalar (Fin p) l⁻¹) g :=
      fun g => Matrix.GeneralLinearGroup.scalar_commute l⁻¹ g
    rw [hy', mul_assoc, hyx, (hs _).left_comm, (hs x).left_comm]
  have hrel' : (y' : Matrix (Fin p) (Fin p) F) * (x : Matrix (Fin p) (Fin p) F) =
      (w : F) • ((x : Matrix (Fin p) (Fin p) F) * (y' : Matrix (Fin p) (Fin p) F)) := by
    have h := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) hrel
    simp only [Units.val_mul, CFSG.LieType.SeitzGeneration.coe_scalarGL, Matrix.smul_mul,
      Matrix.one_mul] at h
    exact h
  obtain ⟨M, ξ, hξ, hY, hX⟩ :=
    CFSG.LieType.SeitzGeneration.exists_heisenberg_basis_gl_p hp hw ⟨(w : F), hw⟩ hxp' hy'p' hrel'
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hξ
    exact zero_ne_one hξ
  refine ⟨M, (l : F) * ξ, mul_ne_zero l.ne_zero hξ0, ?_, ?_⟩
  · have hyy : y = Matrix.GeneralLinearGroup.scalar (Fin p) l * y' := by
      rw [hy', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [Units.val_mul, Units.val_mul, hyy, Units.val_mul, CFSG.LieType.SeitzGeneration.coe_scalarGL,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hY,
      CFSG.LieType.SeitzGeneration.heisDiagMat, smul_smul, ← diagonal_smul]
    congr 1
  · rw [Units.val_mul, Units.val_mul]
    exact hX

variable {Y : Type} [Group Y] {H Γ : Subgroup (GL (Fin p) F)}

theorem exists_heis_pair [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hH1 : CentScalar H Γ)
    {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {A : Subgroup (MulAut Y)} (hAel : IsElemAbelian p A)
    (hIm : IsImageOfNonabelianP p H Γ θ A) :
    ∃ (x y : GL (Fin p) F) (ex ey : MulAut Y) (w c l : Fˣ), x ∈ Γ ∧ y ∈ Γ ∧ ex ∈ A ∧ ey ∈ A ∧
      ActsAsConj H θ x ex ∧ ActsAsConj H θ y ey ∧ IsPrimitiveRoot (w : F) p ∧
      x ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) c ∧
      y ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) (l ^ p) ∧
      y * x = Matrix.GeneralLinearGroup.scalar (Fin p) w * (x * y) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp hp2
  obtain ⟨P, hPΓ, -, ⟨gA, hgA, gB, hgB, hAB⟩, -, hPA⟩ := hIm
  obtain ⟨eA, heA, hgeA⟩ := hPA gA hgA
  obtain ⟨eB, heB, hgeB⟩ := hPA gB hgB
  have hAΓ := hPΓ hgA
  have hBΓ := hPΓ hgB
  have hcommAB : eA * eB = eB * eA :=
    congrArg Subtype.val (hAel.1.is_comm.comm (⟨eA, heA⟩ : ↥A) ⟨eB, heB⟩)
  obtain ⟨u, hu⟩ := actsAsConj_comm hH1 hAΓ hBΓ hgeA hgeB hcommAB
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hAB
    rw [map_one, one_mul] at hu
    exact hu.symm
  have hup : u ^ p = 1 := by
    have hdet := congrArg Matrix.GeneralLinearGroup.det hu
    rw [map_mul, map_mul, map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units,
      mul_comm (Matrix.GeneralLinearGroup.det gB)] at hdet
    exact mul_right_cancel (b := Matrix.GeneralLinearGroup.det gA * Matrix.GeneralLinearGroup.det gB)
      (by rw [one_mul, ← hdet])
  have hprim : IsPrimitiveRoot u p := by
    rw [← orderOf_eq_prime hup hu1]
    exact IsPrimitiveRoot.orderOf u
  have hpowA : ∃ a : Fˣ, gA ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) a := by
    have h1 := actsAsConj_pow hgeA p
    rw [hAel.2 eA heA] at h1
    exact actsAsConj_one_scalar hH1 (Γ.pow_mem hAΓ p) h1
  have hpowB : ∃ b : Fˣ, gB ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
    have h1 := actsAsConj_pow hgeB p
    rw [hAel.2 eB heB] at h1
    exact actsAsConj_one_scalar hH1 (Γ.pow_mem hBΓ p) h1
  obtain ⟨a, ha⟩ := hpowA
  obtain ⟨b, hb⟩ := hpowB
  obtain ⟨i, j, hij, l, hl⟩ := CFSG.LieType.SeitzGeneration.sgo_exists_pow_isPow hp hprim a b
  have hz : ∀ g : GL (Fin p) F, Matrix.GeneralLinearGroup.scalar (Fin p) u * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin p) u := fun g => scalar_mul_comm u g
  have hzn : ∀ (n : ℕ) (g : GL (Fin p) F), (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ n * g =
      g * (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ n :=
    fun n g => (Commute.pow_left (hz g) n).eq
  have hzp : (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ p = 1 := by
    rw [← map_pow, hup, map_one]
  have hy0p : (gA ^ i * gB ^ j) ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) (l ^ p) := by
    have hBj : gB ^ j * gA = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j * (gA * gB ^ j) :=
      CFSG.LieType.SeitzGeneration.sgo_pow_left_comm hz hu j
    have hBji : gB ^ j * gA ^ i =
        ((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i * (gA ^ i * gB ^ j) :=
      CFSG.LieType.SeitzGeneration.sgo_comm_pow_right (hzn j) hBj i
    have hcen : ∀ g : GL (Fin p) F, ((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i * g =
        g * ((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i := fun g =>
      (Commute.pow_left (Commute.pow_left (hz g) j) i).eq
    rw [CFSG.LieType.SeitzGeneration.sgo_mul_pow hcen hBji p]
    have hw : ((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i =
        (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ (j * i) := (pow_mul _ _ _).symm
    have hwp : (((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i) ^ p = 1 := by
      rw [hw, ← pow_mul, mul_comm (j * i) p, pow_mul, hzp, one_pow]
    obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 < p)
    have hzk : (((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i) ^ (p.choose 2) = 1 := by
      rw [hk, pow_mul, hwp, one_pow]
    rw [hzk, one_mul]
    have e1 : (gA ^ i) ^ p = (Matrix.GeneralLinearGroup.scalar (Fin p) a) ^ i := by
      rw [← pow_mul, mul_comm i p, pow_mul, ha]
    have e2 : (gB ^ j) ^ p = (Matrix.GeneralLinearGroup.scalar (Fin p) b) ^ j := by
      rw [← pow_mul, mul_comm j p, pow_mul, hb]
    rw [e1, e2, ← map_pow, ← map_pow, ← map_mul, hl]
  have hyΓ : gA ^ i * gB ^ j ∈ Γ := Γ.mul_mem (Γ.pow_mem hAΓ i) (Γ.pow_mem hBΓ j)
  have heyA : eA ^ i * eB ^ j ∈ A := A.mul_mem (A.pow_mem heA i) (A.pow_mem heB j)
  have hgey : ActsAsConj H θ (gA ^ i * gB ^ j) (eA ^ i * eB ^ j) :=
    ActsAsConj.mul (actsAsConj_pow hgeA i) (actsAsConj_pow hgeB j)
  by_cases hj : p ∣ j
  · have hi : ¬ p ∣ i := fun hi => hij ⟨hi, hj⟩
    have hcop : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hi).symm
    have hprimw : IsPrimitiveRoot (((u ^ i)⁻¹ : Fˣ) : F) p :=
      IsPrimitiveRoot.coe_units_iff.2 ((hprim.pow_of_coprime i hcop).inv)
    have hBi : gB * gA ^ i = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ i * (gA ^ i * gB) :=
      CFSG.LieType.SeitzGeneration.sgo_comm_pow_right hz hu i
    have hBy0 : gB * (gA ^ i * gB ^ j) =
        (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ i * ((gA ^ i * gB ^ j) * gB) := by
      calc gB * (gA ^ i * gB ^ j) = (gB * gA ^ i) * gB ^ j := (mul_assoc _ _ _).symm
        _ = ((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ i * (gA ^ i * gB)) * gB ^ j := by
            rw [hBi]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ i * ((gA ^ i * gB) * gB ^ j) := by
            rw [mul_assoc]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ i * ((gA ^ i * gB ^ j) * gB) := by
            rw [mul_assoc (gA ^ i) gB (gB ^ j), (Commute.self_pow gB j).eq]
            simp only [mul_assoc]
    refine ⟨gB, gA ^ i * gB ^ j, eB, eA ^ i * eB ^ j, (u ^ i)⁻¹, b, l, hBΓ, hyΓ, heB, heyA, hgeB,
      hgey, hprimw, hb, hy0p, ?_⟩
    rw [hBy0, ← map_pow, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · have hcop : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hj).symm
    have hprimw : IsPrimitiveRoot (((u ^ j : Fˣ)) : F) p :=
      IsPrimitiveRoot.coe_units_iff.2 (hprim.pow_of_coprime j hcop)
    have hBj : gB ^ j * gA = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j * (gA * gB ^ j) :=
      CFSG.LieType.SeitzGeneration.sgo_pow_left_comm hz hu j
    have hy0A : (gA ^ i * gB ^ j) * gA =
        (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j * (gA * (gA ^ i * gB ^ j)) := by
      calc (gA ^ i * gB ^ j) * gA = gA ^ i * (gB ^ j * gA) := mul_assoc _ _ _
        _ = gA ^ i * ((Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j * (gA * gB ^ j)) := by
            rw [hBj]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j * (gA ^ i * (gA * gB ^ j)) := by
            rw [← mul_assoc, (hzn j (gA ^ i)).symm, mul_assoc]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin p) u) ^ j * (gA * (gA ^ i * gB ^ j)) := by
            rw [← mul_assoc (gA ^ i) gA (gB ^ j), ← (Commute.self_pow gA i).eq, mul_assoc gA]
    refine ⟨gA, gA ^ i * gB ^ j, eA, eA ^ i * eB ^ j, u ^ j, a, l, hAΓ, hyΓ, heA, heyA, hgeA,
      hgey, hprimw, ha, hy0p, ?_⟩
    rw [hy0A, map_pow]

end Normal

section CentPow

open Matrix

variable {F : Type} [Field F] {p : ℕ}

@[expose] def centPow (H : Subgroup (GL (Fin p) F)) (g : GL (Fin p) F) (m : ℕ)
    (hc : ∀ u v : GL (Fin p) F, u * g = g * u → v * g = g * v → u * v = v * u) :
    Subgroup (GL (Fin p) F) where
  carrier := {u | u ∈ H ∧ u * g = g * u ∧ u ^ m = 1}
  mul_mem' := by
    rintro u v ⟨hu, hug, hum⟩ ⟨hv, hvg, hvm⟩
    refine ⟨H.mul_mem hu hv, ?_, ?_⟩
    · rw [mul_assoc, hvg, ← mul_assoc, hug, mul_assoc]
    · rw [(show Commute u v from hc u v hug hvg).mul_pow, hum, hvm, one_mul]
  one_mem' := ⟨H.one_mem, by simp, one_pow m⟩
  inv_mem' := by
    rintro u ⟨hu, hug, hum⟩
    refine ⟨H.inv_mem hu, ?_, by rw [inv_pow, hum, inv_one]⟩
    calc u⁻¹ * g = u⁻¹ * (g * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * g) * u⁻¹ := by rw [hug]
      _ = g * u⁻¹ := by group

theorem centPow_conj_mem {H : Subgroup (GL (Fin p) F)} {g : GL (Fin p) F} {m : ℕ}
    {hc : ∀ u v : GL (Fin p) F, u * g = g * u → v * g = g * v → u * v = v * u} {v : GL (Fin p) F}
    (hv : v ∈ Subgroup.normalizer (H : Set (GL (Fin p) F))) {c : Fˣ}
    (hvg : v * g * v⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) c * g) {u : GL (Fin p) F}
    (hu : u ∈ centPow H g m hc) : v * u * v⁻¹ ∈ centPow H g m hc := by
  obtain ⟨huH, hug, hum⟩ := hu
  refine ⟨(Subgroup.mem_normalizer_iff.1 hv u).1 huH, ?_, ?_⟩
  · have h1 : (v * u * v⁻¹) * (v * g * v⁻¹) = (v * g * v⁻¹) * (v * u * v⁻¹) := by
      calc (v * u * v⁻¹) * (v * g * v⁻¹) = v * (u * g) * v⁻¹ := by group
        _ = v * (g * u) * v⁻¹ := by rw [hug]
        _ = (v * g * v⁻¹) * (v * u * v⁻¹) := by group
    rw [hvg] at h1
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin p) c * ((v * u * v⁻¹) * g) =
        Matrix.GeneralLinearGroup.scalar (Fin p) c * (g * (v * u * v⁻¹)) := by
      calc Matrix.GeneralLinearGroup.scalar (Fin p) c * ((v * u * v⁻¹) * g)
          = (v * u * v⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin p) c * g) := by
            rw [← mul_assoc, scalar_mul_comm c (v * u * v⁻¹), mul_assoc]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin p) c * g) * (v * u * v⁻¹) := h1
        _ = _ := mul_assoc _ _ _
    exact mul_left_cancel h2
  · rw [conj_pow, hum, mul_one, mul_inv_cancel]

theorem conj_scalar_of_fix {H : Subgroup (GL (Fin p) F)} {g : GL (Fin p) F}
    {φ : MulAut (StatedProj H)} (hφ : InducedByConj H g φ) (v : H)
    (hv : φ (QuotientGroup.mk v) = QuotientGroup.mk v) :
    ∃ c : Fˣ, (v : GL (Fin p) F) * g * (v : GL (Fin p) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin p) c * g := by
  have h1 : g * (v : GL (Fin p) F) * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hφ.1 v).1 v.2
  have e1 := hφ.2 v ⟨_, h1⟩ rfl
  rw [hv, QuotientGroup.eq, Subgroup.mem_subgroupOf] at e1
  obtain ⟨s, hs⟩ := e1
  have hs' : (Matrix.GeneralLinearGroup.scalar (Fin p) s : GL (Fin p) F) =
      (v : GL (Fin p) F)⁻¹ * (g * (v : GL (Fin p) F) * g⁻¹) := hs
  have h2 : g * (v : GL (Fin p) F) * g⁻¹ =
      (v : GL (Fin p) F) * Matrix.GeneralLinearGroup.scalar (Fin p) s := by
    rw [hs']; group
  have h4 : g = Matrix.GeneralLinearGroup.scalar (Fin p) s *
      ((v : GL (Fin p) F) * g * (v : GL (Fin p) F)⁻¹) := by
    calc g = (g * (v : GL (Fin p) F) * g⁻¹) * g * (v : GL (Fin p) F)⁻¹ := by group
      _ = ((v : GL (Fin p) F) * Matrix.GeneralLinearGroup.scalar (Fin p) s) * g *
            (v : GL (Fin p) F)⁻¹ := by rw [h2]
      _ = Matrix.GeneralLinearGroup.scalar (Fin p) s *
            ((v : GL (Fin p) F) * g * (v : GL (Fin p) F)⁻¹) := by
          rw [← scalar_mul_comm s (v : GL (Fin p) F)]; group
  refine ⟨s⁻¹, ?_⟩
  calc (v : GL (Fin p) F) * g * (v : GL (Fin p) F)⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin p) s⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin p) s *
          ((v : GL (Fin p) F) * g * (v : GL (Fin p) F)⁻¹)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = Matrix.GeneralLinearGroup.scalar (Fin p) s⁻¹ * g := by rw [← h4]

variable {Y : Type} [Group Y] {H : Subgroup (GL (Fin p) F)}

theorem exists_lift_centPow [Finite Y] [Finite F] (hp : p.Prime) (hZ : IsPGroup p (Subgroup.center Y))
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) {g : GL (Fin p) F} {α : MulAut Y}
    (hgα : ActsAsConj H θ g α) {m : ℕ} (hm : Nat.Coprime p m)
    (hc : ∀ u v : GL (Fin p) F, u * g = g * u → v * g = g * v → u * v = v * u) :
    ∃ X₀ : Subgroup Y, X₀ ≤ GLAPPrimeCoreOf p (fixSub α) ∧
      (∀ x ∈ X₀, ∃ u : H, (u : GL (Fin p) F) * g = g * u ∧ (u : GL (Fin p) F) ^ m = 1 ∧
        projY θ x = QuotientGroup.mk u) ∧
      (∀ u : H, (u : GL (Fin p) F) * g = g * u → (u : GL (Fin p) F) ^ m = 1 →
        ∃ x ∈ X₀, projY θ x = QuotientGroup.mk u) ∧
      (∀ (e : MulAut Y) (k : GL (Fin p) F), ActsAsConj H θ k e →
        (∃ c : Fˣ, k * g * k⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) c * g) →
          ∀ x ∈ X₀, e x ∈ X₀) := by
  classical
  obtain ⟨φ, hφ, hαφ⟩ := hgα
  set X : Subgroup (StatedProj H) :=
    ((centPow H g m hc).subgroupOf H).map (QuotientGroup.mk' _) with hXdef
  have hXmem : ∀ x : StatedProj H, x ∈ X ↔ ∃ u : H, (u : GL (Fin p) F) * g = g * u ∧
      (u : GL (Fin p) F) ^ m = 1 ∧ QuotientGroup.mk u = x := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : (u : GL (Fin p) F) ∈ centPow H g m hc := Subgroup.mem_subgroupOf.1 hu
      exact ⟨u, hu'.2.1, hu'.2.2, rfl⟩
    · rintro ⟨u, hug, hum, rfl⟩
      exact ⟨u, Subgroup.mem_subgroupOf.2 ⟨u.2, hug, hum⟩, rfl⟩
  have hXc : Nat.Coprime p (Nat.card X) := by
    apply coprime_card_of_pow_eq_one hp hm X
    intro x hx
    obtain ⟨u, -, hum, rfl⟩ := (hXmem x).1 hx
    have : u ^ m = 1 := Subtype.ext (by simpa using hum)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hconjX : ∀ (k : GL (Fin p) F) (ψ : MulAut (StatedProj H)), InducedByConj H k ψ →
      (∃ c : Fˣ, k * g * k⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) c * g) →
        ∀ x ∈ X, ψ x ∈ X := by
    rintro k ψ hψ ⟨c, hc'⟩ x hx
    obtain ⟨u, hug, hum, rfl⟩ := (hXmem x).1 hx
    have hku : k * (u : GL (Fin p) F) * k⁻¹ ∈ centPow H g m hc :=
      centPow_conj_mem hψ.1 hc' ⟨u.2, hug, hum⟩
    rw [hψ.2 u ⟨_, hku.1⟩ rfl]
    exact (hXmem _).2 ⟨_, hku.2.1, hku.2.2, rfl⟩
  obtain ⟨X₀, hX₀, hmap, hinv⟩ := exists_lift_le_core hp (projY θ) (projY_surjective θ)
    (ker_projY θ) hZ α φ (fun y => hαφ y) X hXc
    (fun x hx => by
      obtain ⟨u, hug, -, rfl⟩ := (hXmem x).1 hx
      have h1 : g * (u : GL (Fin p) F) * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hφ.1 u).1 u.2
      rw [hφ.2 u ⟨_, h1⟩ rfl]
      congr 1
      apply Subtype.ext
      show g * (u : GL (Fin p) F) * g⁻¹ = u
      rw [← hug, mul_inv_cancel_right])
    (fun c hc' x hx => by
      obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (projY θ c)
      have hfix : φ (QuotientGroup.mk v) = QuotientGroup.mk v := by
        rw [hv]
        have := hαφ c
        rw [hc'] at this
        exact this.symm
      have hconj : ∃ c : Fˣ, (v : GL (Fin p) F) * g * (v : GL (Fin p) F)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin p) c * g := conj_scalar_of_fix hφ v hfix
      obtain ⟨u, hug, hum, rfl⟩ := (hXmem x).1 hx
      obtain ⟨c₀, hc₀⟩ := hconj
      have hvu : (v : GL (Fin p) F) * u * (v : GL (Fin p) F)⁻¹ ∈ centPow H g m hc :=
        centPow_conj_mem (Subgroup.le_normalizer v.2) hc₀ ⟨u.2, hug, hum⟩
      rw [← hv]
      refine (hXmem _).2 ⟨⟨_, hvu.1⟩, hvu.2.1, hvu.2.2, ?_⟩
      rfl)
  refine ⟨X₀, hX₀, ?_, ?_, ?_⟩
  · intro x hx
    have : projY θ x ∈ X := by rw [← hmap]; exact ⟨x, hx, rfl⟩
    obtain ⟨u, hug, hum, hu⟩ := (hXmem _).1 this
    exact ⟨u, hug, hum, hu.symm⟩
  · intro u hug hum
    have : (QuotientGroup.mk u : StatedProj H) ∈ X := (hXmem _).2 ⟨u, hug, hum, rfl⟩
    rw [← hmap] at this
    obtain ⟨x, hx, hxu⟩ := this
    exact ⟨x, hx, hxu⟩
  · rintro e k ⟨ψ, hψ, heψ⟩ hk x hx
    exact hinv e ψ (fun y => heψ y) (hconjX k ψ hψ hk) x hx

theorem comm_of_diag {M y : GL (Fin p) F} {δ : Fin p → F} (hδ : Function.Injective δ)
    (hy : ((M⁻¹ * y * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal δ) :
    ∀ u v : GL (Fin p) F, u * y = y * u → v * y = y * v → u * v = v * u := by
  have key : ∀ u : GL (Fin p) F, u * y = y * u →
      ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        diagonal (fun i => ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) i i) := by
    intro u hu
    apply eq_diagonal_of_mul_diagonal hδ
    rw [← hy, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc M⁻¹ * u * M * (M⁻¹ * y * M) = M⁻¹ * (u * y) * M := by group
      _ = M⁻¹ * (y * u) * M := by rw [hu]
      _ = M⁻¹ * y * M * (M⁻¹ * u * M) := by group
  intro u v hu hv
  have h1 : M⁻¹ * u * M * (M⁻¹ * v * M) = M⁻¹ * v * M * (M⁻¹ * u * M) := by
    apply Units.ext
    have e1 := Units.val_mul (M⁻¹ * u * M) (M⁻¹ * v * M)
    have e2 := Units.val_mul (M⁻¹ * v * M) (M⁻¹ * u * M)
    rw [e1, e2, key u hu, key v hv, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  calc u * v = M * (M⁻¹ * u * M * (M⁻¹ * v * M)) * M⁻¹ := by group
    _ = M * (M⁻¹ * v * M * (M⁻¹ * u * M)) * M⁻¹ := by rw [h1]
    _ = v * u := by group

theorem eq_aeval_of_comm_companion [NeZero p] (c : F) {X : Matrix (Fin p) (Fin p) F}
    (hX : X * companionMat p c = companionMat p c * X) :
    X = Polynomial.aeval (companionMat p c)
      (∑ k : Fin p, Polynomial.monomial (k : ℕ) (X k 0)) := by
  classical
  set f : Polynomial F := ∑ k : Fin p, Polynomial.monomial (k : ℕ) (X k 0) with hf
  have hcomm : Commute (companionMat p c) (Polynomial.aeval (companionMat p c) f) := by
    simpa using (Polynomial.commute_X f).map (Polynomial.aeval (companionMat p c))
  have hfC : Polynomial.aeval (companionMat p c) f * companionMat p c =
      companionMat p c * Polynomial.aeval (companionMat p c) f := hcomm.eq.symm
  apply CFSG.LieType.SeitzGeneration.thmU_commute_companion_eq_of_col0 c hX hfC
  intro i
  have hsum : Polynomial.aeval (companionMat p c) f =
      ∑ k : Fin p, X k 0 • companionMat p c ^ (k : ℕ) := by
    rw [hf, map_sum]
    congr 1
    funext k
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  rw [hsum, Matrix.sum_apply]
  have hcol : ∀ k : Fin p, (X k 0 • companionMat p c ^ (k : ℕ)) i 0 = if i = k then X k 0 else 0 := by
    intro k
    have h1 := congrFun (CFSG.LieType.SeitzGeneration.thmU_companionMat_pow_mulVec_single
      (p := p) c k.isLt) i
    rw [mulVec_single_one, col_apply, Fin.cast_val_eq_self, Pi.single_apply] at h1
    rw [Matrix.smul_apply, h1, smul_eq_mul]
    split_ifs <;> simp
  simp only [hcol, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem comm_of_companion [NeZero p] {M g : GL (Fin p) F} {c : F}
    (hg : ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p c) :
    ∀ u v : GL (Fin p) F, u * g = g * u → v * g = g * v → u * v = v * u := by
  have key : ∀ u : GL (Fin p) F, u * g = g * u →
      ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * companionMat p c =
        companionMat p c * ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    intro u hu
    rw [← hg, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc M⁻¹ * u * M * (M⁻¹ * g * M) = M⁻¹ * (u * g) * M := by group
      _ = M⁻¹ * (g * u) * M := by rw [hu]
      _ = M⁻¹ * g * M * (M⁻¹ * u * M) := by group
  intro u v hu hv
  have h1 : M⁻¹ * u * M * (M⁻¹ * v * M) = M⁻¹ * v * M * (M⁻¹ * u * M) := by
    apply Units.ext
    have e1 := Units.val_mul (M⁻¹ * u * M) (M⁻¹ * v * M)
    have e2 := Units.val_mul (M⁻¹ * v * M) (M⁻¹ * u * M)
    rw [e1, e2, eq_aeval_of_comm_companion c (key u hu),
      eq_aeval_of_comm_companion c (key v hv), ← map_mul, ← map_mul, mul_comm]
  calc u * v = M * (M⁻¹ * u * M * (M⁻¹ * v * M)) * M⁻¹ := by group
    _ = M * (M⁻¹ * v * M * (M⁻¹ * u * M)) * M⁻¹ := by rw [h1]
    _ = v * u := by group

end CentPow

section Misc

theorem isPGroup_center {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore p Y = ⊥) : IsPGroup p (Subgroup.center Y) := by
  have h := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112_isPGroup_inf_centralizer hp hO
    (N := ⊤) (CFSG.Open.IsSubnormal.refl ⊤)
  have e : (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ((⊤ : Subgroup Y) : Set Y) =
      Subgroup.center Y := by
    rw [top_inf_eq, Subgroup.coe_top, Subgroup.centralizer_univ]
  rwa [e] at h

theorem mk_eq_of_comm_conj {Y : Type} [Group Y] {z : MulAut Y} {x : Y}
    (h : z * MulAut.conj x = MulAut.conj x * z) :
    (QuotientGroup.mk (z x) : Y ⧸ Subgroup.center Y) = QuotientGroup.mk x := by
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro w
  have h2 : z x * w * (z x)⁻¹ = x * w * x⁻¹ := by
    have h4 : z (x * z.symm w * x⁻¹) = z x * w * (z x)⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← h4]
    have h5 := congrArg (fun e : MulAut Y => e (z.symm w)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at h5
    exact h5
  calc w * ((z x)⁻¹ * x) = (z x)⁻¹ * (z x * w * (z x)⁻¹) * x := by group
    _ = (z x)⁻¹ * (x * w * x⁻¹) * x := by rw [h2]
    _ = (z x)⁻¹ * x * w := by group

theorem not_two_pow_dvd {Q₀ a r : ℕ} (hQ : Odd Q₀) (hr : Odd r) (h : Q₀ ^ 2 - 1 = 2 ^ a * r) :
    ¬ 2 ^ a ∣ Q₀ - 1 ∧ ¬ 2 ^ a ∣ Q₀ + 1 := by
  obtain ⟨Q₁, rfl⟩ := hQ
  have e : (2 * Q₁ + 1) ^ 2 - 1 = (2 * Q₁) * (2 * Q₁ + 2) := by
    have : (2 * Q₁ + 1) ^ 2 = (2 * Q₁) * (2 * Q₁ + 2) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  rw [e] at h
  have hpos : 0 < 2 ^ a := pow_pos two_pos a
  constructor
  · rintro ⟨k, hk⟩
    rw [show 2 * Q₁ + 1 - 1 = 2 * Q₁ by omega] at hk
    have h2 : 2 ^ a * r = 2 ^ a * (k * (2 * Q₁ + 2)) := by rw [← h, ← mul_assoc, ← hk]
    have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
    rw [h3] at hr
    exact (Nat.not_even_iff_odd.2 hr) ⟨k * (Q₁ + 1), by ring⟩
  · rintro ⟨k, hk⟩
    rw [show 2 * Q₁ + 1 + 1 = 2 * Q₁ + 2 by omega] at hk
    have h2 : 2 ^ a * r = 2 ^ a * (2 * Q₁ * k) := by rw [← h, hk]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
    rw [h3] at hr
    exact (Nat.not_even_iff_odd.2 hr) ⟨Q₁ * k, by ring⟩

end Misc

section Eigen

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem eq_of_conj_diagonal (hp3 : 3 ≤ p) {N N' B B' M M' : Matrix (Fin p) (Fin p) F}
    (hN : N * N' = 1) (hB : B * B' = 1) (hM : M * M' = 1)
    {e f : Fin p → F} {e₀ f₀ c : F}
    (he : ∀ i : Fin p, (i : ℕ) ≠ p - 1 → e i = e₀) (hf : ∀ i : Fin p, (i : ℕ) ≠ p - 1 → f i = f₀)
    (h : B * (N * diagonal e * N') * B' = c • (M * diagonal f * M')) : e₀ = c * f₀ := by
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hB' : B' * B = 1 := mul_eq_one_comm.1 hB
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  set X := M' * B * N with hX
  set X' := N' * B' * M with hX'
  have hXX' : X * X' = 1 := by
    simp only [hX, hX', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc N, hN, Matrix.one_mul, ← Matrix.mul_assoc B, hB, Matrix.one_mul, hM']
  have hX'X : X' * X = 1 := mul_eq_one_comm.1 hXX'
  have hXu : IsUnit X := ⟨⟨X, X', hXX', hX'X⟩, rfl⟩
  have hconj : X * diagonal e = diagonal (fun i => c * f i) * X := by
    calc X * diagonal e = X * diagonal e * (X' * X) := by rw [hX'X, Matrix.mul_one]
      _ = (M' * (B * (N * diagonal e * N') * B') * M) * X := by
          simp only [hX, hX', Matrix.mul_assoc]
      _ = (M' * (c • (M * diagonal f * M')) * M) * X := by rw [h]
      _ = diagonal (fun i => c * f i) * X := by
          have e1 : M' * (M * diagonal f * M') * M = diagonal f := by
            simp only [← Matrix.mul_assoc]
            rw [hM', Matrix.one_mul, Matrix.mul_assoc, hM', Matrix.mul_one]
          rw [Matrix.mul_smul, Matrix.smul_mul, e1, ← diagonal_smul]
          rfl
  have hcard := card_ne_eq_of_conj hXu hconj e₀
  by_contra hne
  have h1 : Nat.card {i // e i - e₀ ≠ 0} ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    constructor
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : (i : ℕ) = p - 1 := by
      by_contra h'
      exact hi (by rw [he i h', sub_self])
    have hj' : (j : ℕ) = p - 1 := by
      by_contra h'
      exact hj (by rw [he j h', sub_self])
    exact Subtype.ext (Fin.ext (hi'.trans hj'.symm))
  have h2 : 1 < Nat.card {i // c * f i - e₀ ≠ 0} := by
    rw [Finite.one_lt_card_iff_nontrivial]
    have h0 : c * f ⟨0, by omega⟩ - e₀ ≠ 0 := by
      rw [hf _ (by simp; omega)]
      exact sub_ne_zero.2 (Ne.symm hne)
    have h1' : c * f ⟨1, by omega⟩ - e₀ ≠ 0 := by
      rw [hf _ (by simp; omega)]
      exact sub_ne_zero.2 (Ne.symm hne)
    refine ⟨⟨⟨_, h0⟩, ⟨_, h1'⟩, ?_⟩⟩
    intro h01
    have := congrArg (fun x : {i // c * f i - e₀ ≠ 0} => ((x : Fin p) : ℕ)) h01
    simp at this
  omega

end Eigen

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

variable {F : Type} [Field F] {p : ℕ}

theorem centScalar_SL [Finite F] (hp3 : 3 ≤ p) : CentScalar (StatedSL p F) ⊤ := by
  intro u _ hu
  have h1 : LinearFlag.conjAut p F u = 1 := by
    ext x
    obtain ⟨v, rfl⟩ := proj_surjective p F x
    have hv : (SpecialLinearGroup.toGL v : GL (Fin p) F) ∈ StatedSL p F := by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
      exact v.2
    obtain ⟨c, hc⟩ := hu _ hv
    have hcp : c ^ p = 1 := by
      have h2 := congrArg Matrix.GeneralLinearGroup.det hc
      rw [map_mul, map_mul, map_mul, map_inv,
        CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units,
        mul_comm (Matrix.GeneralLinearGroup.det u), mul_assoc, mul_inv_cancel, mul_one] at h2
      exact mul_right_cancel (b := Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL v))
        (by rw [one_mul]; exact h2.symm)
    rw [conjAut_proj, MulAut.one_apply]
    have e : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation p F u v =
        scalarElement c hcp * v := by
      apply SpecialLinearGroup.toGL_injective
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hc, map_mul]
      congr 1
      apply Units.ext
      rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_scalarElement,
        Matrix.GeneralLinearGroup.coe_scalar]
    rw [e, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hcp), one_mul]
  obtain ⟨c, hc⟩ := (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_one_iff hp3 u).1 h1
  exact ⟨c, hc.symm⟩

variable {Y : Type} [Group Y]

theorem projAct_eq_conjAut {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL p F)}
    {g : GL (Fin p) F} {b : MulAut Y} (hgb : ActsAsConj (StatedSL p F) θ g b) :
    projAct θ b = LinearFlag.conjAut p F g := by
  obtain ⟨φ, ⟨-, hφ⟩, hb⟩ := hgb
  ext x
  obtain ⟨u, rfl⟩ := proj_surjective p F x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (θ.symm (QuotientGroup.mk
    (specialLinearGroupEquivStatedSL p F u)))
  have hθy : θ (QuotientGroup.mk y) = QuotientGroup.mk (specialLinearGroupEquivStatedSL p F u) := by
    rw [hy, MulEquiv.apply_symm_apply]
  have hu : proj p F u = statedToProj p F (θ (QuotientGroup.mk y)) := by
    rw [hθy, statedToProj_mk]
  have hφu : φ (QuotientGroup.mk (specialLinearGroupEquivStatedSL p F u)) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL p F
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation p F g u)) := by
    refine hφ _ _ ?_
    apply Units.ext
    rw [Units.val_mul, Units.val_mul,
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, coe_slConjugation,
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  calc projAct θ b (proj p F u)
      = projAct θ b (statedToProj p F (θ (QuotientGroup.mk y))) := by rw [← hu]
    _ = statedToProj p F (θ (QuotientGroup.mk (b y))) := projAct_apply θ b y
    _ = statedToProj p F (φ (QuotientGroup.mk (specialLinearGroupEquivStatedSL p F u))) := by
        rw [hb, hθy]
    _ = proj p F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation p F g u) := by
        rw [hφu, statedToProj_mk]
    _ = LinearFlag.conjAut p F g (proj p F u) := (conjAut_proj g u).symm

theorem exists_smul_of_proj_eq {w u : SpecialLinearGroup (Fin p) F} (h : proj p F w = proj p F u) :
    ∃ c : F, c ^ p = 1 ∧ (w : Matrix (Fin p) (Fin p) F) = c • (u : Matrix (Fin p) (Fin p) F) := by
  obtain ⟨c, hc, hcu⟩ := proj_eq_proj_iff.1 h
  refine ⟨((c⁻¹ : Fˣ) : F), by rw [← Units.val_pow_eq_pow_val, inv_pow, hc, inv_one, Units.val_one], ?_⟩
  have hs : w⁻¹ * u = scalarElement c hc := Subtype.ext (hcu.trans (coe_scalarElement c hc).symm)
  have hu : u = w * scalarElement c hc := by rw [← hs]; group
  have e1 : (u : Matrix (Fin p) (Fin p) F) = (c : F) • (w : Matrix (Fin p) (Fin p) F) := by
    rw [hu]
    show (w : Matrix (Fin p) (Fin p) F) * (scalarElement c hc : Matrix (Fin p) (Fin p) F) = _
    rw [coe_scalarElement, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  rw [e1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem conjField_proj (B : GL (Fin p) F) (σ : F ≃+* F) (u : SpecialLinearGroup (Fin p) F) :
    ∃ w : SpecialLinearGroup (Fin p) F, (LinearFlag.conjAut p F B * fieldAut p F σ) (proj p F u) =
      proj p F w ∧ (w : Matrix (Fin p) (Fin p) F) = (B : Matrix (Fin p) (Fin p) F) *
        (u : Matrix (Fin p) (Fin p) F).map σ * ((B⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation p F B
    (SpecialLinearGroup.map σ.toRingHom u), ?_, ?_⟩
  · rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  · rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rfl

theorem conjFieldDual_proj (B : GL (Fin p) F) (σ : F ≃+* F) (u : SpecialLinearGroup (Fin p) F) :
    ∃ w : SpecialLinearGroup (Fin p) F,
      (LinearFlag.conjAut p F B * fieldAut p F σ * dualAut p F) (proj p F u) = proj p F w ∧
      (w : Matrix (Fin p) (Fin p) F) = (B : Matrix (Fin p) (Fin p) F) *
        ((u⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F)ᵀ.map σ *
          ((B⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation p F B
    (SpecialLinearGroup.map σ.toRingHom (u⁻¹).transpose), ?_, ?_⟩
  · rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  · rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      SpecialLinearGroup.coe_transpose]
    rfl

theorem prod_last {p : ℕ} (hp : 0 < p) {G : Type*} [CommGroup G] (s : G) :
    ∏ i : Fin p, (if (i : ℕ) = p - 1 then s⁻¹ ^ (p - 1) else s) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  have h1 : ∀ i : Fin m, ((Fin.castSucc i : Fin (m + 1)) : ℕ) ≠ m := by
    intro i
    simp only [Fin.coe_castSucc]
    omega
  simp only [add_tsub_cancel_right, h1, if_false, Fin.val_last, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, if_true, inv_pow, mul_inv_cancel]

theorem comm_of_both_diag {M u v : GL (Fin p) F} {t t' : Fin p → F}
    (hu : ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal t)
    (hv : ((M⁻¹ * v * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal t') : u * v = v * u := by
  have h1 : M⁻¹ * u * M * (M⁻¹ * v * M) = M⁻¹ * v * M * (M⁻¹ * u * M) := by
    apply Units.ext
    have e1 := Units.val_mul (M⁻¹ * u * M) (M⁻¹ * v * M)
    have e2 := Units.val_mul (M⁻¹ * v * M) (M⁻¹ * u * M)
    rw [e1, e2, hu, hv, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  calc u * v = M * (M⁻¹ * u * M * (M⁻¹ * v * M)) * M⁻¹ := by group
    _ = M * (M⁻¹ * v * M * (M⁻¹ * u * M)) * M⁻¹ := by rw [h1]
    _ = v * u := by group

theorem inverseTranspose_scalar (w : Fˣ) :
    Matrix.GeneralLinearGroup.inverseTranspose (Matrix.GeneralLinearGroup.scalar (Fin p) w) =
      Matrix.GeneralLinearGroup.scalar (Fin p) w⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_transpose]

theorem pow_sub_one_eq_one {F : Type*} [Field F] {p Q₀ : ℕ} {s : Fˣ} {c : F} (hc : c ^ p = 1)
    (hQ : 1 ≤ Q₀) (h : (s : F) ^ Q₀ = c * s) : s ^ (p * (Q₀ - 1)) = 1 := by
  have h1 : s ^ (Q₀ * p) = s ^ p := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, h, mul_pow, hc, one_mul]
  have h2 : s ^ (Q₀ * p) = s ^ p * s ^ (p * (Q₀ - 1)) := by
    rw [← pow_add]
    congr 1
    obtain ⟨Q₁, rfl⟩ : ∃ Q₁, Q₀ = Q₁ + 1 := ⟨Q₀ - 1, by omega⟩
    simp only [add_tsub_cancel_right]
    ring
  rw [h2] at h1
  exact mul_eq_left.1 h1

theorem pow_add_one_eq_one {F : Type*} [Field F] {p Q₀ : ℕ} {s : Fˣ} {c : F} (hc : c ^ p = 1)
    (h : ((s⁻¹ : Fˣ) : F) ^ Q₀ = c * s) : s ^ (p * (Q₀ + 1)) = 1 := by
  have h1 : (s⁻¹) ^ (Q₀ * p) = s ^ p := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, h, mul_pow, hc, one_mul]
  rw [inv_pow] at h1
  have h2 : s ^ (p * (Q₀ + 1)) = s ^ p * s ^ (Q₀ * p) := by
    rw [← pow_add]
    congr 1
    ring
  rw [h2, ← h1, inv_mul_cancel]

theorem false_of_two_pow {F : Type*} [Field F] {p a r Q₀ : ℕ} {s : Fˣ} (hs : orderOf s = 2 ^ a)
    (hp : Nat.Coprime (2 ^ a) p) (hQ : Odd Q₀) (hr : Odd r) (h : Q₀ ^ 2 - 1 = 2 ^ a * r)
    (h1 : s ^ (p * (Q₀ - 1)) = 1 ∨ s ^ (p * (Q₀ + 1)) = 1) : False := by
  have h2 := not_two_pow_dvd hQ hr h
  rcases h1 with h1 | h1
  · have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hs] at h3
    exact h2.1 (hp.dvd_of_dvd_mul_left h3)
  · have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hs] at h3
    exact h2.2 (hp.dvd_of_dvd_mul_left h3)

theorem mul_scalar_mul_mul_scalar {F : Type*} [Field F] {p : ℕ} (a b : Fˣ) (g h : GL (Fin p) F) :
    (g * Matrix.GeneralLinearGroup.scalar (Fin p) a) * (h * Matrix.GeneralLinearGroup.scalar (Fin p) b) =
      Matrix.GeneralLinearGroup.scalar (Fin p) (a * b) * (g * h) := by
  calc (g * Matrix.GeneralLinearGroup.scalar (Fin p) a) * (h * Matrix.GeneralLinearGroup.scalar (Fin p) b)
      = g * (Matrix.GeneralLinearGroup.scalar (Fin p) a * h) *
          Matrix.GeneralLinearGroup.scalar (Fin p) b := by group
    _ = g * (h * Matrix.GeneralLinearGroup.scalar (Fin p) a) *
          Matrix.GeneralLinearGroup.scalar (Fin p) b := by
        rw [Matrix.GeneralLinearGroup.scalar_commute a h]
    _ = (g * h) * (Matrix.GeneralLinearGroup.scalar (Fin p) a *
          Matrix.GeneralLinearGroup.scalar (Fin p) b) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin p) (a * b) * (g * h) := by
        rw [← map_mul]
        exact (Matrix.GeneralLinearGroup.scalar_commute (a * b) (g * h)).symm

theorem input27_2_outerL_holds : Inputs245.Input27_2_outerL := by
  intro p q n hp hp2 hq hq2 hqp Y _ _ hY hYO F _ _ hcard hdvd θ A hAel hAc hIm z hz2 hzD hzA hzJ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp3 := three_le_of_prime_ne_two hp hp2
  have hH1 : CentScalar (StatedSL p F) ⊤ := centScalar_SL hp3
  have hZ : IsPGroup p (Subgroup.center Y) := isPGroup_center hp hYO
  obtain ⟨x, y, ex, ey, w, c, l, -, -, hexA, heyA, hgex, hgey, hw, hxp, hyp, hyx⟩ :=
    exists_heis_pair hp hp2 hH1 hAel hIm
  obtain ⟨M, δ₀, hδ₀, hMy, hMx⟩ := exists_normal_form hp hw hxp hyp hyx
  have hδinj : Function.Injective (fun k : Fin p => δ₀ * (w : F) ^ (k : ℕ)) := by
    intro k k' hkk'
    exact Fin.ext (hw.pow_inj k.2 k'.2 (mul_left_cancel₀ hδ₀ hkk'))
  have hcy := comm_of_diag hδinj hMy
  have hw1 : (w : F) ≠ 1 := hw.ne_one hp.one_lt
  have hey1 : ey ≠ 1 := by
    intro h1
    rw [h1] at hgey
    obtain ⟨d, hd⟩ := actsAsConj_one_scalar hH1 (Subgroup.mem_top y) hgey
    have h2 : y * x = x * y := by rw [hd, scalar_mul_comm]
    rw [h2] at hyx
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin p) w = 1 :=
      mul_right_cancel (b := x * y) (by rw [one_mul]; exact hyx.symm)
    have h4 : w = 1 := scalar_injective' (m := p) hp.one_lt.le (by rw [h3, map_one])
    exact hw1 (by rw [h4, Units.val_one])
  have hq1 : 1 < q ^ n := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rwa [hcard] at h1
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hq1; omega
    · exact h0
  obtain ⟨a, r, hr, hqr⟩ := Nat.exists_eq_two_pow_mul_odd (show q ^ n - 1 ≠ 0 by omega)
  have hrpos : 0 < r := hr.pos
  have hFcard : Nat.card Fˣ = q ^ n - 1 := by rw [Nat.card_units, hcard]
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g₀ = q ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, hFcard]
  set s : Fˣ := g₀ ^ r with hsdef
  have hs : orderOf s = 2 ^ a := by
    rw [hsdef, orderOf_pow_of_dvd hrpos.ne' (by rw [hord, hqr]; exact dvd_mul_left r _), hord, hqr,
      Nat.mul_div_cancel _ hrpos]
  have hs2 : s ^ 2 ^ a = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  set Du : Fin p → Fˣ := fun i => if (i : ℕ) = p - 1 then s⁻¹ ^ (p - 1) else s with hDu
  set Dg : GL (Fin p) F := TauCeti.diagGL Du with hDg
  set dg : GL (Fin p) F := M * Dg * M⁻¹ with hdg
  have hDgc : ((M⁻¹ * dg * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal (fun i => (Du i : F)) := by
    rw [show M⁻¹ * dg * M = Dg by rw [hdg]; group, hDg, TauCeti.diagGL_coe]
  have hdgy : dg * y = y * dg := comm_of_both_diag hDgc hMy
  have hdgpow : dg ^ 2 ^ a = 1 := by
    rw [hdg, conj_pow, hDg, ← map_pow]
    have h1 : Du ^ 2 ^ a = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply, hDu]
      split_ifs
      · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hs2, inv_one, one_pow]
      · exact hs2
    rw [h1, map_one, mul_one, mul_inv_cancel]
  have hdgdet : (dg : Matrix (Fin p) (Fin p) F).det = 1 := by
    rw [hdg, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul, hDg,
      TauCeti.diagGL_coe, Matrix.det_diagonal, ← Units.coe_prod, hDu, prod_last hp.pos s, Units.val_one]
  have hdgSL : dg ∈ StatedSL p F := CFSG.Open.StatedAPI.mem_statedSL_iff.2 hdgdet
  have hm : Nat.Coprime p (2 ^ a) :=
    Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨X₀, hX₀core, -, hX₀lift, -⟩ := exists_lift_centPow hp hZ θ hgey hm hcy
  obtain ⟨x₀, hx₀, hx₀d⟩ := hX₀lift ⟨dg, hdgSL⟩ hdgy hdgpow
  have hzx : z * MulAut.conj x₀ = MulAut.conj x₀ * z := hzJ ey heyA hey1 x₀ (hX₀core hx₀)
  have hmk := mk_eq_of_comm_conj hzx
  set Zt := projAct θ z with hZtdef
  set ud : SpecialLinearGroup (Fin p) F := ⟨(dg : Matrix (Fin p) (Fin p) F), hdgdet⟩ with hud
  have hud' : specialLinearGroupEquivStatedSL p F ud = ⟨dg, hdgSL⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  have hZtd : Zt (proj p F ud) = proj p F ud := by
    have e1 : proj p F ud = statedToProj p F (θ (QuotientGroup.mk x₀)) := by
      rw [← statedToProj_mk, hud', ← hx₀d]
      rfl
    rw [e1, hZtdef, projAct_apply, hmk]
  have hZtnot : Zt ∉ linearAutGroup p F := fun h => hzD ((mem_innDiag_iff_projAct θ z).2 h)
  have hZt2 : Zt * Zt = 1 := by
    rw [hZtdef, ← map_mul, ← sq, hz2, map_one]
  have hZc : ∀ (g : GL (Fin p) F) (e : MulAut Y), e ∈ A → ActsAsConj (StatedSL p F) θ g e →
      Zt * LinearFlag.conjAut p F g = LinearFlag.conjAut p F g * Zt := by
    intro g e he hge
    rw [← projAct_eq_conjAut hge, hZtdef, ← map_mul, ← map_mul, hzA e he]
  have htrans := standard_automorphism_transport (K := F) (n := p)
  obtain ⟨B, σ, ε, hε, hZt⟩ := (automorphism_generation (K := F) hp3).2 Zt
  have hδδ : dualAut p F * dualAut p F = 1 := htrans.2.2.2.1
  have hσσ : σ * σ = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · rw [pow_zero, mul_one] at hZt
      have h2 : LinearFlag.conjAut p F (B * Matrix.GeneralLinearGroup.map (σ : F →+* F) B) *
          fieldAut p F (σ * σ) = 1 := by
        rw [← hZt2, hZt, ← htrans.1, ← htrans.2.1, ← htrans.2.2.1 σ B]
        group
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one hp3 _ _ h2).1
    · rw [pow_one] at hZt
      have h2 : LinearFlag.conjAut p F (B * Matrix.GeneralLinearGroup.map (σ : F →+* F)
          (Matrix.GeneralLinearGroup.inverseTranspose B)) * fieldAut p F (σ * σ) = 1 := by
        rw [← hZt2, hZt]
        calc LinearFlag.conjAut p F (B * Matrix.GeneralLinearGroup.map (σ : F →+* F)
              (Matrix.GeneralLinearGroup.inverseTranspose B)) * fieldAut p F (σ * σ)
            = LinearFlag.conjAut p F B * (fieldAut p F σ * LinearFlag.conjAut p F
                (Matrix.GeneralLinearGroup.inverseTranspose B) * (fieldAut p F σ)⁻¹) *
                (fieldAut p F σ * fieldAut p F σ) := by
              rw [htrans.2.2.1 σ, htrans.2.1, htrans.1]
          _ = LinearFlag.conjAut p F B * fieldAut p F σ *
                (dualAut p F * LinearFlag.conjAut p F B * dualAut p F) *
                (dualAut p F * fieldAut p F σ * dualAut p F) := by
              rw [htrans.2.2.2.2.1 B, htrans.2.2.2.2.2.1 σ]
              group
          _ = LinearFlag.conjAut p F B * fieldAut p F σ * dualAut p F *
                (LinearFlag.conjAut p F B * fieldAut p F σ * dualAut p F) := by
              simp only [mul_assoc]
              rw [← mul_assoc (dualAut p F) (dualAut p F), hδδ, one_mul]
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one hp3 _ _ h2).1
  have hudM : (ud : Matrix (Fin p) (Fin p) F) = (M : Matrix (Fin p) (Fin p) F) *
      diagonal (fun i => (Du i : F)) * ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    show (dg : Matrix (Fin p) (Fin p) F) = _
    rw [hdg, Units.val_mul, Units.val_mul, hDg, TauCeti.diagGL_coe]
  have hMM : (M : Matrix (Fin p) (Fin p) F) * ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBB : (B : Matrix (Fin p) (Fin p) F) * ((B⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDu_ne : ∀ i : Fin p, (i : ℕ) ≠ p - 1 → Du i = s := fun i hi => by
    simp only [hDu, if_neg hi]
  have hQodd : Odd (q ^ (n / 2)) := (hq.odd_of_ne_two hq2).pow
  have hQ1 : 1 ≤ q ^ (n / 2) := Nat.one_le_pow _ _ hq.pos
  have hQsq : ∀ (_ : Even n), (q ^ (n / 2)) ^ 2 - 1 = 2 ^ a * r := by
    intro hn
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hn), ← hqr]
  have hcop2 : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hZt
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      apply hZtnot
      rw [hZt, map_one, mul_one]
      exact conjAut_mem_linearAutGroup B
    obtain ⟨hn_even, hσpow⟩ := even_and_eq_pow_of_involution_prime hq hn1 hcard hσ1 hσσ
    obtain ⟨w', hw'1, hw'2⟩ := conjField_proj B σ ud
    rw [← hZt, hZtd] at hw'1
    obtain ⟨c', hc'p, hc'⟩ := exists_smul_of_proj_eq hw'1.symm
    have hN : (M : Matrix (Fin p) (Fin p) F).map σ *
        ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).map σ = 1 := by
      rw [← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero σ) (map_one σ)]
    have key : σ (s : F) = c' * s := by
      refine eq_of_conj_diagonal hp3 hN hBB hMM (e := fun i => σ (Du i : F))
        (f := fun i => (Du i : F)) (fun i hi => by simp only [hDu_ne i hi])
        (fun i hi => by simp only [hDu_ne i hi]) ?_
      rw [← hudM, ← hc', hw'2, hudM, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero σ)]
    rw [hσpow] at key
    exact false_of_two_pow hs hcop2 hQodd hr (hQsq hn_even)
      (Or.inl (pow_sub_one_eq_one hc'p hQ1 key))
  ·
    rw [pow_one] at hZt
    by_cases hσ1 : σ = 1
    ·
      rw [hσ1, map_one, mul_one] at hZt
      have hcomm : ∀ (g : GL (Fin p) F) (e : MulAut Y), e ∈ A → ActsAsConj (StatedSL p F) θ g e →
          ∃ m : Fˣ, B * Matrix.GeneralLinearGroup.inverseTranspose g * B⁻¹ =
            g * Matrix.GeneralLinearGroup.scalar (Fin p) m := by
        intro g e he hge
        have h1 := hZc g e he hge
        rw [hZt] at h1
        have h2 : LinearFlag.conjAut p F (B * Matrix.GeneralLinearGroup.inverseTranspose g * B⁻¹) =
            LinearFlag.conjAut p F g := by
          calc LinearFlag.conjAut p F (B * Matrix.GeneralLinearGroup.inverseTranspose g * B⁻¹)
              = LinearFlag.conjAut p F B * (dualAut p F * LinearFlag.conjAut p F g * dualAut p F) *
                  (LinearFlag.conjAut p F B)⁻¹ := by
                rw [map_mul, map_mul, map_inv, ← htrans.2.2.2.2.1 g]
            _ = (LinearFlag.conjAut p F B * dualAut p F * LinearFlag.conjAut p F g) * dualAut p F *
                  (LinearFlag.conjAut p F B)⁻¹ := by group
            _ = (LinearFlag.conjAut p F g * (LinearFlag.conjAut p F B * dualAut p F)) *
                  dualAut p F * (LinearFlag.conjAut p F B)⁻¹ := by rw [h1]
            _ = LinearFlag.conjAut p F g * LinearFlag.conjAut p F B * (dualAut p F * dualAut p F) *
                  (LinearFlag.conjAut p F B)⁻¹ := by group
            _ = LinearFlag.conjAut p F g := by rw [hδδ, mul_one, mul_inv_cancel_right]
        exact (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_conjAut_iff hp3 _ _).1 h2
      obtain ⟨mx, hmx⟩ := hcomm x ex hexA hgex
      obtain ⟨my, hmy⟩ := hcomm y ey heyA hgey
      have hφ : ∀ g g' : GL (Fin p) F, B * Matrix.GeneralLinearGroup.inverseTranspose (g * g') * B⁻¹ =
          (B * Matrix.GeneralLinearGroup.inverseTranspose g * B⁻¹) *
            (B * Matrix.GeneralLinearGroup.inverseTranspose g' * B⁻¹) := by
        intro g g'
        rw [map_mul]
        group
      have hsc : B * Matrix.GeneralLinearGroup.inverseTranspose
          (Matrix.GeneralLinearGroup.scalar (Fin p) w) * B⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin p) w⁻¹ := by
        rw [inverseTranspose_scalar, ← Matrix.GeneralLinearGroup.scalar_commute w⁻¹ B,
          mul_inv_cancel_right]
      have e1 : B * Matrix.GeneralLinearGroup.inverseTranspose (y * x) * B⁻¹ =
          B * Matrix.GeneralLinearGroup.inverseTranspose
            (Matrix.GeneralLinearGroup.scalar (Fin p) w * (x * y)) * B⁻¹ := by rw [hyx]
      rw [hφ, hφ, hφ, hmx, hmy, hsc, mul_scalar_mul_mul_scalar, mul_scalar_mul_mul_scalar,
        mul_comm mx my] at e1
      have e2 : y * x = Matrix.GeneralLinearGroup.scalar (Fin p) w⁻¹ * (x * y) := by
        have e3 : Matrix.GeneralLinearGroup.scalar (Fin p) (my * mx) * (y * x) =
            Matrix.GeneralLinearGroup.scalar (Fin p) (my * mx) *
              (Matrix.GeneralLinearGroup.scalar (Fin p) w⁻¹ * (x * y)) := by
          rw [e1]
          simp only [← mul_assoc, ← map_mul, mul_comm w⁻¹]
        exact mul_left_cancel e3
      rw [hyx] at e2
      have e4 : Matrix.GeneralLinearGroup.scalar (Fin p) w = Matrix.GeneralLinearGroup.scalar (Fin p) w⁻¹ :=
        mul_right_cancel e2
      have e5 : w = w⁻¹ := scalar_injective' (m := p) hp.one_lt.le e4
      have e6 : (w : F) ^ 2 = 1 := by
        rw [sq]
        have := congrArg Units.val (mul_eq_one_iff_eq_inv.2 e5)
        rwa [Units.val_mul, Units.val_one] at this
      have e7 := hw.dvd_of_pow_eq_one 2 e6
      have := Nat.le_of_dvd two_pos e7
      omega
    ·
      obtain ⟨hn_even, hσpow⟩ := even_and_eq_pow_of_involution_prime hq hn1 hcard hσ1 hσσ
      obtain ⟨w', hw'1, hw'2⟩ := conjFieldDual_proj B σ ud
      rw [← hZt, hZtd] at hw'1
      obtain ⟨c', hc'p, hc'⟩ := exists_smul_of_proj_eq hw'1.symm
      have hudinv : ((ud⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
          (M : Matrix (Fin p) (Fin p) F) * diagonal (fun i => (((Du i)⁻¹ : Fˣ) : F)) *
            ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
        have h1 : SpecialLinearGroup.toGL ud = dg := Units.ext rfl
        have h2 : ((ud⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
            ((dg⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
          rw [← SpecialLinearGroup.coe_GL_coe_matrix, map_inv, h1]
        rw [h2, hdg, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul,
          hDg, ← map_inv, TauCeti.diagGL_coe]
        rfl
      have hN : (((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)ᵀ).map σ *
          ((M : Matrix (Fin p) (Fin p) F)ᵀ).map σ = 1 := by
        rw [← Matrix.map_mul, ← Matrix.transpose_mul, hMM, Matrix.transpose_one,
          Matrix.map_one _ (map_zero σ) (map_one σ)]
      have key : σ ((s⁻¹ : Fˣ) : F) = c' * s := by
        refine eq_of_conj_diagonal hp3 hN hBB hMM (e := fun i => σ (((Du i)⁻¹ : Fˣ) : F))
          (f := fun i => (Du i : F)) (fun i hi => by simp only [hDu_ne i hi])
          (fun i hi => by simp only [hDu_ne i hi]) ?_
        rw [← hudM, ← hc', hw'2, hudinv, Matrix.transpose_mul, Matrix.transpose_mul,
          diagonal_transpose, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero σ)]
        simp only [Matrix.mul_assoc]
      rw [hσpow] at key
      exact false_of_two_pow hs hcop2 hQodd hr (hQsq hn_even)
        (Or.inr (pow_add_one_eq_one hc'p key))

end Linear

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs272b

end
