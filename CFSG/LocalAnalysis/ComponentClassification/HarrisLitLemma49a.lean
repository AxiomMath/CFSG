module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma44
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralAut

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem ncard_conj_orbit {G : Type*} [Group G] (A : Subgroup G) {x : G} (hx : x ∈ A) :
    {y : G | ∃ a ∈ A, a * x * a⁻¹ = y}.ncard = (centralizer ({x} : Set G)).relIndex A := by
  have h1 := Subgroup.index_centralizer_eq_ncard (⟨x, hx⟩ : A)
  have hc : centralizer ({(⟨x, hx⟩ : A)} : Set A) = (centralizer ({x} : Set G)).subgroupOf A := by
    ext a
    simp only [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subtype.ext_iff,
      Subgroup.coe_mul]
  rw [hc] at h1
  rw [Subgroup.relIndex, h1]
  have hset : {y : G | ∃ a ∈ A, a * x * a⁻¹ = y} =
      Subtype.val '' conjugatesOf (⟨x, hx⟩ : A) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a * x * a⁻¹, A.mul_mem (A.mul_mem ha hx) (A.inv_mem ha)⟩, ?_, rfl⟩
      show IsConj (⟨x, hx⟩ : A) _
      exact isConj_iff.mpr ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp (hy' : IsConj _ _)
      exact ⟨c, c.2, by rw [← hc]; rfl⟩
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem exists_eq_of_isPGroup_range {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ}
    [Fact p.Prime] (ψ : G →* H) (hψ : IsPGroup p ψ.range) (P : Sylow p G) (g : G) :
    ∃ x ∈ (P : Subgroup G), ψ g = ψ x := by
  have hS := isSylowOf_map_range ψ P
  have heq := hS.eq_of_le (map_le_range ψ _) le_rfl hψ
  have : ψ g ∈ (P : Subgroup G).map ψ := by
    rw [← heq]
    exact ⟨g, rfl⟩
  obtain ⟨x, hx, hxg⟩ := this
  exact ⟨x, hx, hxg.symm⟩

theorem exists_odd_two_parts {G : Type*} [Group G] (g : G) (hg : 0 < orderOf g) :
    ∃ (a b : ℕ) (i j : ℤ), Odd b ∧ orderOf g = 2 ^ a * b ∧
      g = (g ^ 2 ^ a) ^ i * (g ^ b) ^ j := by
  set n := orderOf g with hn
  refine ⟨n.factorization 2, ordCompl[2] n, Nat.gcdA (2 ^ n.factorization 2) (ordCompl[2] n),
    Nat.gcdB (2 ^ n.factorization 2) (ordCompl[2] n), ?_,
    (Nat.ordProj_mul_ordCompl_eq_self n 2).symm, ?_⟩
  · rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hg.ne'
  · have hcop : Nat.Coprime (2 ^ n.factorization 2) (ordCompl[2] n) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hg.ne')
    have hbez := Nat.gcd_eq_gcd_ab (2 ^ n.factorization 2) (ordCompl[2] n)
    rw [hcop, Nat.cast_one] at hbez
    calc g = g ^ (1 : ℤ) := (zpow_one g).symm
      _ = g ^ (((2 ^ n.factorization 2 : ℕ) : ℤ) * Nat.gcdA (2 ^ n.factorization 2)
          (ordCompl[2] n) + ((ordCompl[2] n : ℕ) : ℤ) * Nat.gcdB (2 ^ n.factorization 2)
            (ordCompl[2] n)) := by rw [← hbez]
      _ = _ := by rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem card_X_le [Finite X] (hσ : Setup42 h hS w z) :
    Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) ≤ 8 := by
  classical
  let F : Bool × Bool × Bool → X := fun q =>
    (bif q.1 then t else 1) * (bif q.2.1 then w ^ (orderOf w / 2) else 1) *
      (bif q.2.2 then z else 1)
  have key : ∀ {a g : X}, (a = 1 ∨ a = g) → (bif decide (a = g) then g else 1) = a := by
    intro a g ha
    by_cases hag : a = g
    · simp [hag]
    · rcases ha with ha | ha
      · subst ha
        simp [hag]
      · exact absurd ha hag
  have hsurj : ∀ x : (closure {t, w ^ (orderOf w / 2), z} : Subgroup X),
      ∃ q, F q = (x : X) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := hσ.mem_X hx
    exact ⟨(decide (a = t), decide (b = w ^ (orderOf w / 2)), decide (c = z)), by
      simp only [F, key ha, key hb, key hc]⟩
  have hle : Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) ≤
      Nat.card (Bool × Bool × Bool) := by
    let G : Bool × Bool × Bool → (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) := fun q =>
      if hq : F q ∈ closure {t, w ^ (orderOf w / 2), z} then ⟨F q, hq⟩ else 1
    refine Nat.card_le_card_of_surjective G fun x => ?_
    obtain ⟨q, hq⟩ := hsurj x
    refine ⟨q, ?_⟩
    simp only [G, hq, x.2, dite_true]
  simpa using hle

theorem eq_one_or_eq_z_of_mem_X_of_mem_L [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxL : x ∈ L) : x = 1 ∨ x = z := by
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := hσ.mem_X hxX
  have hcL : c ∈ L := by
    rcases hc with hc | hc <;> rw [hc]
    · exact one_mem _
    · exact hσ.z_mem.2
  have haL : a ∈ zpowers t := by
    rcases ha with ha | ha <;> rw [ha]
    · exact one_mem _
    · exact mem_zpowers t
  rcases hb with rfl | rfl
  ·
    have ha1 : a = 1 := by
      refine h.eq_one_of_mem_zpowers_of_mem haL ?_
      have : a = a * 1 * c * c⁻¹ := by group
      rw [this]
      exact L.mul_mem hxL (L.inv_mem hcL)
    rw [ha1]
    rcases hc with hc | hc <;> rw [hc]
    · left
      group
    · right
      group
  ·
    exfalso
    apply hσ.rho_u_not_mem_inn
    have hu : w ^ (orderOf w / 2) = a⁻¹ * (a * w ^ (orderOf w / 2) * c) * c⁻¹ := by group
    have hmem : a⁻¹ * (a * w ^ (orderOf w / 2) * c) * c⁻¹ ∈ zpowers t ⊔ L :=
      mul_mem (mul_mem (mem_sup_left (inv_mem haL)) (mem_sup_right hxL))
        (mem_sup_right (inv_mem hcL))
    have := h.rho_mem_innAut hmem (hS.le (hu ▸ hσ.u_mem))
    convert this using 2
    exact Subtype.ext hu

theorem exists_conj_eq_z [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z) {d : X}
    (hd : d ∈ S ⊓ L) (hd2 : d ^ 2 = 1) (hd1 : d ≠ 1) :
    ∃ g ∈ centralizer ({t} : Set X), g * d * g⁻¹ = z := by
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_left.trans' le_sup_right
  obtain ⟨g, hgH, hgX⟩ := hσ.exists_conj_mem_X hKF (hDT hd) hd2
  have hgL : g * d * g⁻¹ ∈ L := (mem_normalizer_iff.mp (h.centralizer_le_normalizer hgH) d).mp hd.2
  rcases hσ.eq_one_or_eq_z_of_mem_X_of_mem_L hgX hgL with h1 | h1
  · exfalso
    apply hd1
    calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · exact ⟨g, hgH, h1⟩

theorem comm_of_odd [Finite X] (hσ : Setup42 h hS w z) {g : X} (hg : Odd (orderOf g))
    (hgD : ∀ d ∈ S ⊓ L, g * d * g⁻¹ ∈ S ⊓ L) {d : X} (hd : d ∈ S ⊓ L) : g * d = d * g := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  have hgDn : ∀ n : ℕ, ∀ d ∈ S ⊓ L, g ^ n * d * (g ^ n)⁻¹ ∈ S ⊓ L := by
    intro n
    induction n with
    | zero =>
      intro d hd
      simpa using hd
    | succ n ih =>
      intro d hd
      rw [pow_succ, show g ^ n * g * d * (g ^ n * g)⁻¹ = g ^ n * (g * d * g⁻¹) * (g ^ n)⁻¹ by
        group]
      exact ih _ (hgD d hd)
  let f : DihedralGroup (2 ^ m) →* DihedralGroup (2 ^ m) :=
    { toFun := fun x => e ⟨g * (e.symm x : X) * g⁻¹, hgD _ (e.symm x).2⟩
      map_one' := by
        rw [← map_one e]
        congr 1
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul]
        group }
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 := e.injective hxy
    have h2 : g * (e.symm x : X) * g⁻¹ = g * (e.symm y : X) * g⁻¹ := congrArg Subtype.val h1
    have h3 : (e.symm x : X) = e.symm y := by simpa using h2
    exact e.symm.injective (Subtype.ext h3)
  let ψ : MulAut (DihedralGroup (2 ^ m)) :=
    MulEquiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  have hψ : ∀ x, ψ x = f x := fun x => rfl
  have hiter : ∀ n : ℕ, ∀ x, (ψ ^ n) x =
      e ⟨g ^ n * (e.symm x : X) * (g ^ n)⁻¹, hgDn n _ (e.symm x).2⟩ := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, MulAut.one_apply]
      apply e.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hψ]
      congr 1
      apply Subtype.ext
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.symm_apply_apply]
      group
  have hψk : ψ ^ orderOf g = 1 := by
    ext x
    rw [hiter, MulAut.one_apply]
    apply e.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    simp [pow_orderOf_eq_one]
  have h1 := dihedral_mulAut_eq_one_of_odd (by omega) ψ hg hψk
  have h2 : ψ (e ⟨d, hd⟩) = e ⟨d, hd⟩ := by rw [h1, MulAut.one_apply]
  rw [hψ] at h2
  have h3 := e.injective h2
  have h4 : g * d * g⁻¹ = d := by
    have := congrArg Subtype.val h3
    simpa using this
  calc g * d = g * d * g⁻¹ * g := by group
    _ = d * g := by rw [h4]

theorem exists_mul_of_sq_eq_one [Finite X] (hσ : Setup42 h hS w z) {d : X} (hd : d ∈ S ⊓ L) :
    ∃ y₁ ∈ S ⊓ L, ∃ y₂ ∈ S ⊓ L, y₁ ^ 2 = 1 ∧ y₂ ^ 2 = 1 ∧ d = y₁ * y₂ := by
  obtain ⟨m, -, ⟨e⟩⟩ := hσ.dihedral
  have hsq : ∀ j : ZMod (2 ^ m), (e.symm (DihedralGroup.sr j)) ^ 2 = 1 := by
    intro j
    rw [← map_pow, sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero, map_one]
  rcases hde : e ⟨d, hd⟩ with i | j
  · refine ⟨e.symm (DihedralGroup.sr 0), (e.symm _).2, e.symm (DihedralGroup.sr i), (e.symm _).2,
      congrArg Subtype.val (hsq 0), congrArg Subtype.val (hsq i), ?_⟩
    have : (⟨d, hd⟩ : ↥(S ⊓ L)) = e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.sr i) := by
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, DihedralGroup.sr_mul_sr,
        sub_zero, hde]
    exact congrArg Subtype.val this
  · refine ⟨d, hd, 1, one_mem _, ?_, one_pow 2, (mul_one d).symm⟩
    have : (⟨d, hd⟩ : ↥(S ⊓ L)) = e.symm (DihedralGroup.sr j) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, hde]
    have h2 := hsq j
    rw [← this] at h2
    exact congrArg Subtype.val h2

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
