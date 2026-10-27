module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMOrbit

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def conjOnHom {P Q : Subgroup G} (hPQ : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) :
    ↥P →* MulAut ↥Q where
  toFun g :=
    { toFun := fun x => ⟨(g : G) * x * (g : G)⁻¹, hPQ g g.2 x x.2⟩
      invFun := fun x => ⟨(g : G)⁻¹ * x * g, by
        have := hPQ g⁻¹ (P.inv_mem g.2) x x.2
        simpa using this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by
    show ((g : G) * h) * x * ((g : G) * h)⁻¹ = g * (h * x * (h : G)⁻¹) * (g : G)⁻¹
    group)

theorem conjOnHom_apply {P Q : Subgroup G} (hPQ : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (g : ↥P) (x : ↥Q) : ((conjOnHom hPQ g x : ↥Q) : G) = (g : G) * x * (g : G)⁻¹ := rfl

theorem exists_sylow_invariant [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {P Q : Subgroup G} (hPp : IsPGroup p P) (hPQ : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hcop : Nat.Coprime p (Nat.card Q)) :
    ∃ T : Sylow q ↥Q, ∀ (g : G) (hg : g ∈ P), ∀ x : ↥Q, x ∈ (T : Subgroup ↥Q) →
      (⟨g * x * g⁻¹, hPQ g hg x x.2⟩ : ↥Q) ∈ (T : Subgroup ↥Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  let _ : MulAction ↥P (Sylow q ↥Q) := MulAction.compHom _ (conjOnHom hPQ)
  have hmod := hPp.card_modEq_card_fixedPoints (Sylow q ↥Q)
  obtain ⟨T₀⟩ : Nonempty (Sylow q ↥Q) := inferInstance
  have hdvd : Nat.card (Sylow q ↥Q) ∣ Nat.card ↥Q :=
    (Sylow.card_dvd_index T₀).trans (Subgroup.index_dvd_card _)
  have hnz : ¬ p ∣ Nat.card (MulAction.fixedPoints ↥P (Sylow q ↥Q)) := by
    intro h
    have h1 : p ∣ Nat.card (Sylow q ↥Q) := (Nat.modEq_zero_iff_dvd.1 (hmod.trans
      (Nat.modEq_zero_iff_dvd.2 h)))
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (h1.trans hdvd)
  have hne : Nonempty (MulAction.fixedPoints ↥P (Sylow q ↥Q)) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hnz (by rw [Nat.card_of_isEmpty]; exact dvd_zero p)
  obtain ⟨⟨T, hT⟩⟩ := hne
  refine ⟨T, fun g hg x hx => ?_⟩
  have h1 : (⟨g, hg⟩ : ↥P) • T = T := hT ⟨g, hg⟩
  have h2 : (conjOnHom hPQ ⟨g, hg⟩ x) ∈ ((⟨g, hg⟩ : ↥P) • T : Sylow q ↥Q) :=
    Subgroup.smul_mem_pointwise_smul x (conjOnHom hPQ ⟨g, hg⟩) (T : Subgroup ↥Q) hx
  rw [h1] at h2
  exact h2

theorem exists_involution_pow [Finite G] {x : G} {m : ℕ} (hx : x ^ (2 ^ m) = 1) (hx1 : x ≠ 1) :
    ∃ j : ℕ, x ^ j * x ^ j = 1 ∧ x ^ j ≠ 1 := by
  have h2 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hio
    exact hx1 hio
  refine ⟨2 ^ (i - 1), ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0), ← hio,
      pow_orderOf_eq_one]
  · intro h
    have := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))) h
    rw [hio] at this
    have : 2 ^ i ≤ 2 ^ (i - 1) := this
    have : i ≤ i - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    omega

theorem odd_card_gLAPPrimeCoreOf_of_large_pGroup [Finite G] {p : ℕ} (hp : p.Prime)
    {C P : Subgroup G} (hPC : P ≤ C) (hPp : IsPGroup p P) {a k : ℕ}
    (hPcard : Nat.card P = p ^ a)
    (hinv : ∀ w : G, w * w = 1 → w ≠ 1 → ∀ R : Subgroup G, IsPGroup p R →
      R ≤ Subgroup.centralizer ({w} : Set G) → Nat.card R * p ^ k ≤ p ^ a)
    (h2 : ∀ m : ℕ, 2 ^ m ∣ Nat.card G → 2 ^ m ≡ 1 [MOD p ^ k] → m = 0) :
    Odd (Nat.card (GLAPPrimeCoreOf p C)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := GLAPPrimeCoreOf p C with hQ
  have hcop : Nat.Coprime p (Nat.card Q) := coprime_card_GLAPPrimeCoreOf hp C
  have hPQ : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun g hg x hx =>
    GLAPPrimeCoreOf_conj_mem g (hPC hg) x hx
  obtain ⟨T, hT⟩ := exists_sylow_invariant hp Nat.prime_two hPp hPQ hcop
  set T' : Subgroup G := (T : Subgroup ↥Q).map Q.subtype with hT'
  have hT'card : Nat.card T' = Nat.card (T : Subgroup ↥Q) :=
    Subgroup.card_map_of_injective Q.subtype_injective
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 T.isPGroup'
  have hT'n : ∀ g ∈ P, ∀ x ∈ T', g * x * g⁻¹ ∈ T' := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨_, hT g hg x hx, rfl⟩
  let X := {x : ↥T' // x ≠ 1}
  let act : MulAction ↥P X :=
    { smul := fun g x => ⟨⟨g * x.1 * (g : G)⁻¹, hT'n g g.2 x.1 x.1.2⟩, fun h => x.2 (by
        have h1 : (g : G) * x.1 * (g : G)⁻¹ = 1 := congrArg Subtype.val h
        have h2 : ((x.1 : ↥T') : G) = 1 := by
          calc ((x.1 : ↥T') : G) = (g : G)⁻¹ * ((g : G) * x.1 * (g : G)⁻¹) * g := by group
            _ = 1 := by rw [h1]; group
        exact Subtype.ext h2)⟩
      one_smul := fun x => Subtype.ext (Subtype.ext (by
        change (1 : G) * x.1 * (1 : G)⁻¹ = x.1
        simp))
      mul_smul := fun g h x => Subtype.ext (Subtype.ext (by
        change ((g : G) * h) * x.1 * ((g : G) * h)⁻¹ =
          g * ((h : G) * x.1 * (h : G)⁻¹) * (g : G)⁻¹
        group)) }
  have hsmul : ∀ (g : ↥P) (x : X), (((g • x : X) : ↥T') : G) = (g : G) * x.1 * (g : G)⁻¹ :=
    fun _ _ => rfl
  have horb : ∀ x : X, p ^ k ∣ Nat.card (MulAction.orbit ↥P x) := by
    intro x
    have hstab : MulAction.stabilizer ↥P x =
        (Subgroup.centralizer ({((x.1 : ↥T') : G)} : Set G)).subgroupOf P := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h1 : (g : G) * x.1 * (g : G)⁻¹ = x.1 :=
          (hsmul g x).symm.trans (congrArg (fun z : X => ((z : ↥T') : G)) h)
        calc (g : G) * x.1 = (g : G) * x.1 * (g : G)⁻¹ * g := by group
          _ = x.1 * g := by rw [h1]
      · intro h
        apply Subtype.ext
        apply Subtype.ext
        rw [hsmul]
        calc (g : G) * x.1 * (g : G)⁻¹ = x.1 * g * (g : G)⁻¹ := by rw [h]
          _ = x.1 := by group
    have hxT : ((x.1 : ↥T') : G) ∈ T' := x.1.2
    obtain ⟨y, hy, hyx⟩ := hxT
    have hy2 : ((y : ↥Q) : G) ^ (2 ^ m) = 1 := by
      have := pow_card_eq_one' (G := ↥(T : Subgroup ↥Q)) (x := ⟨y, hy⟩)
      rw [hm] at this
      have h := congrArg (fun z : ↥(T : Subgroup ↥Q) => ((z : ↥Q) : G)) this
      simpa using h
    have hx1 : ((x.1 : ↥T') : G) ≠ 1 := fun h => x.2 (Subtype.ext h)
    rw [← hyx] at hx1
    obtain ⟨j, hj2, hj1⟩ := exists_involution_pow hy2 hx1
    set w : G := ((y : ↥Q) : G) ^ j with hw
    have hcent : Subgroup.centralizer ({((x.1 : ↥T') : G)} : Set G) ≤
        Subgroup.centralizer ({w} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      rw [← hyx] at hg
      exact (Commute.pow_right (show Commute g ((y : ↥Q) : G) from hg) j).eq
    set R : Subgroup G := P ⊓ Subgroup.centralizer ({((x.1 : ↥T') : G)} : Set G) with hR
    have hRp : IsPGroup p R := hPp.to_le inf_le_left
    have hRle : R ≤ Subgroup.centralizer ({w} : Set G) := le_trans inf_le_right hcent
    have hRbound := hinv w hj2 hj1 R hRp hRle
    have hRcard : Nat.card (MulAction.stabilizer ↥P x) = Nat.card R := by
      rw [hstab, hR, ← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have horbit : Nat.card (MulAction.orbit ↥P x) * Nat.card R = p ^ a := by
      rw [← hRcard, ← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥P x),
        hPcard]
    have hdvd : Nat.card (MulAction.orbit ↥P x) ∣ p ^ a := Dvd.intro _ horbit
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hle : p ^ k ≤ Nat.card (MulAction.orbit ↥P x) := by
      by_contra hlt
      push Not at hlt
      have : Nat.card (MulAction.orbit ↥P x) * Nat.card R < p ^ k * Nat.card R :=
        Nat.mul_lt_mul_of_pos_right hlt hRpos
      nlinarith
    exact pow_dvd_of_le_of_dvd_pow hp hdvd hle
  have hX := dvd_card_of_forall_dvd_card_orbit (G := ↥P) (X := X) horb
  have hXcard : Nat.card X + 1 = Nat.card T' := by
    classical
    rw [← Finite.card_option]
    exact Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥T'))
  have hT2 : Nat.card X + 1 = 2 ^ m := by rw [hXcard, hT'card, hm]
  have hmod : 2 ^ m ≡ 1 [MOD p ^ k] := by
    rw [← hT2]
    have := (Nat.modEq_zero_iff_dvd.2 hX).add_right 1
    simpa using this
  have hdvdG : 2 ^ m ∣ Nat.card G := by
    rw [← hm, ← hT'card]
    exact Subgroup.card_subgroup_dvd_card T'
  have hm0 := h2 m hdvdG hmod
  have hT1 : Nat.card (T : Subgroup ↥Q) = 1 := by rw [hm, hm0, pow_zero]
  have hfac : (Nat.card ↥Q).factorization 2 = 0 := by
    have h := Sylow.card_eq_multiplicity T
    rw [hT1] at h
    have h' : 2 ^ (Nat.card ↥Q).factorization 2 = 2 ^ 0 := by rw [← h, pow_zero]
    exact Nat.pow_right_injective le_rfl h'
  have hQ0 : Nat.card ↥Q ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_eq_zero_iff] at hfac
  rcases hfac with h | h | h
  · exact absurd Nat.prime_two h
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  · exact absurd h hQ0

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
