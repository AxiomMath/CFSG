module

public import CFSG.Dihedral.Glauberman.DicksonMaxTrace

public section

namespace CFSG.Glauberman.Dickson.MaxCases

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.GorensteinWalter
open CFSG.Glauberman.Dickson.MaxStructure CFSG.Glauberman.Dickson.MaxUp
open CFSG.Glauberman.Dickson.MaxDown CFSG.Glauberman.Dickson.MaxSubfield
open CFSG.Glauberman.Dickson.MaxTrace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open scoped MatrixGroups

section Groups

variable {G : Type*} [Group G]

theorem klein_of_mulEquiv {X : Type*} [Group X] {M : Subgroup G} (e : M ≃* X) {a₀ b₀ : X}
    (ha : a₀ * a₀ = 1) (hb : b₀ * b₀ = 1) (ha1 : a₀ ≠ 1) (hb1 : b₀ ≠ 1) (hab : a₀ ≠ b₀)
    (hc : a₀ * b₀ = b₀ * a₀) :
    ∃ a ∈ M, ∃ b ∈ M, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a := by
  let ψ : X →* G := M.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hne : ∀ {x y : X}, x ≠ y → ψ x ≠ ψ y := fun h h' => h (hψ h')
  refine ⟨ψ a₀, (e.symm a₀).2, ψ b₀, (e.symm b₀).2, ?_, ?_, hne hab, ?_, ?_, ?_⟩
  · rw [← map_one ψ]
    exact hne ha1
  · rw [← map_one ψ]
    exact hne hb1
  · rw [← map_mul, ha, map_one]
  · rw [← map_mul, hb, map_one]
  · rw [← map_mul, ← map_mul, hc]

theorem alternatingFour_klein : ∃ a b : alternatingGroup (Fin 4), a * a = 1 ∧ b * b = 1 ∧
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    by decide⟩

theorem permFour_klein : ∃ a b : Equiv.Perm (Fin 4), a * a = 1 ∧ b * b = 1 ∧
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩

theorem alternatingFive_klein : ∃ a b : alternatingGroup (Fin 5), a * a = 1 ∧ b * b = 1 ∧
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    by decide⟩

theorem alternatingFour_sq_mul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    a * b * (a * b) = 1 := by
  decide

@[expose] def kleinFour : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {σ | σ * σ = 1}
  mul_mem' {a b} ha hb := alternatingFour_sq_mul a b ha hb
  one_mem' := mul_one 1
  inv_mem' {a} ha := by
    change a⁻¹ * a⁻¹ = 1
    rw [← mul_inv_rev, show a * a = 1 from ha, inv_one]

theorem card_kleinFour : Nat.card kleinFour = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := (· ∈ kleinFour))
    (q := fun σ => σ * σ = 1) (fun _ => Iff.rfl)), Nat.card_eq_fintype_card]
  decide

theorem exists_kleinFour {N : Subgroup G} (e : N ≃* alternatingGroup (Fin 4)) :
    ∃ V : Subgroup G, Nat.card V = 4 ∧ ∀ x, x ∈ V ↔ x ∈ N ∧ x * x = 1 := by
  refine ⟨(kleinFour.comap e.toMonoidHom).map N.subtype, ?_, fun x => ?_⟩
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.card_map_of_injective e.symm.injective, card_kleinFour]
  · constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have hy' : e y * e y = 1 := hy
      rw [← map_mul, ← map_one e] at hy'
      change ((y * y : N) : G) = 1
      rw [e.injective hy', Subgroup.coe_one]
    · rintro ⟨hx, hxx⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      change e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1
      rw [← map_mul, show (⟨x, hx⟩ : N) * ⟨x, hx⟩ = 1 from Subtype.ext hxx, map_one]

theorem pow_of_mulEquiv_alternatingFour {N : Subgroup G} (e : N ≃* alternatingGroup (Fin 4))
    {x : G} (hx : x ∈ N) : x ^ 2 = 1 ∨ x ^ 3 = 1 := by
  rcases orderOf_dvd_of_equiv_alternating_four e ⟨x, hx⟩ with h | h
  · exact Or.inl (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h))
  · exact Or.inr (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h))

theorem pow_of_mulEquiv_permFour {N : Subgroup G} (e : N ≃* Equiv.Perm (Fin 4))
    {x : G} (hx : x ∈ N) : x ^ 3 = 1 ∨ x ^ 4 = 1 := by
  rcases orderOf_dvd_of_equiv_perm_four e ⟨x, hx⟩ with h | h
  · exact Or.inl (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h))
  · exact Or.inr (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h))

theorem pow_of_mulEquiv_alternatingFive {N : Subgroup G} (e : N ≃* alternatingGroup (Fin 5))
    {x : G} (hx : x ∈ N) : x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  rcases orderOf_dvd_of_equiv_alternating_five e ⟨x, hx⟩ with h | h | h
  · exact Or.inl (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h))
  · exact Or.inr (Or.inl (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h)))
  · exact Or.inr (Or.inr (by simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h)))

theorem mem_of_pow_eight {N V : Subgroup G} (horder : ∀ x ∈ N, x ^ 2 = 1 ∨ x ^ 3 = 1)
    (hV : ∀ x, x ∈ V ↔ x ∈ N ∧ x * x = 1) {x : G} (hx : x ∈ N) (h8 : x ^ 8 = 1) : x ∈ V := by
  rw [hV]
  refine ⟨hx, ?_⟩
  rcases horder x hx with h | h
  · rwa [← pow_two]
  · have e1 : x = (x ^ 3) ^ 3 * (x ^ 8)⁻¹ := by group
    rw [e1, h, h8, one_pow, inv_one, mul_one, mul_one]

theorem eq_normalizer_of_isCoatom {M V : Subgroup G} (hM : IsCoatom M)
    (hMV : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (hN : Subgroup.normalizer (V : Set G) ≠ ⊤) : M = Subgroup.normalizer (V : Set G) := by
  refine eq_of_isCoatom_le hM (fun g hg => ?_) hN
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hMV g hg h, fun hh => ?_⟩
  have := hMV g⁻¹ (M.inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem normalizer_ne_top [Finite G] [IsSimpleGroup G] {V : Subgroup G} (hV1 : Nat.card V ≠ 1)
    (hVG : Nat.card V < Nat.card G) : Subgroup.normalizer (V : Set G) ≠ ⊤ := by
  intro h
  have : V.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h' | h'
  · rw [h', Subgroup.card_bot] at hV1
    exact hV1 rfl
  · rw [h', Subgroup.card_top] at hVG
    exact lt_irrefl _ hVG

theorem exists_normalizing_two_element [Finite G] {V Y : Subgroup G} (hVY : V ≤ Y)
    (hV : Nat.card V = 4) (h8 : 8 ∣ Nat.card Y) :
    ∃ s ∈ Y, s ∉ V ∧ s ∈ Subgroup.normalizer (V : Set G) ∧ s ^ 8 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV' : Nat.card (V.subgroupOf Y) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv, hV]
    norm_num
  obtain ⟨K', hK'card, hVK'⟩ := Sylow.exists_subgroup_card_pow_succ (G := Y) (p := 2) (n := 2)
    (by norm_num; exact h8) hV'
  let K : Subgroup G := K'.map Y.subtype
  have hKcard : Nat.card K = 8 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hK'card]
    norm_num
  have hVK : V ≤ K := by
    intro v hv
    exact ⟨⟨v, hVY hv⟩, hVK' (show (⟨v, hVY hv⟩ : Y) ∈ V.subgroupOf Y from hv), rfl⟩
  have hKY : K ≤ Y := Subgroup.map_subtype_le K'
  have hidx : (V.subgroupOf K).index = 2 := by
    have h1 := (V.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV, hKcard] at h1
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨s, hsK, hsV⟩ : ∃ s ∈ K, s ∉ V := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show K ≤ V from hcon)
    omega
  refine ⟨s, hKY hsK, hsV, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hnorm.conj_mem ⟨h, hVK hh⟩ hh ⟨s, hsK⟩
    · intro hh
      have := hnorm.conj_mem ⟨s * h * s⁻¹, hVK hh⟩ hh (⟨s, hsK⟩ : K)⁻¹
      change s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ ∈ V at this
      rwa [show s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h by group] at this
  · have := pow_card_eq_one' (G := K) (x := ⟨s, hsK⟩)
    rw [hKcard] at this
    exact congrArg Subtype.val this

theorem not_isCoatom_normalizer_of_sylow [Finite G] {r : ℕ} [Fact r.Prime]
    {V D A K : Subgroup G} (hV : IsPGroup r V) (hVidx : ¬ r ∣ V.index) (hD : IsPGroup r D)
    (hcard : Nat.card D = Nat.card V) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hAcard : Nat.card (Subgroup.normalizer (V : Set G)) ≤ Nat.card A) (hAK : A ≤ K)
    (hK : K ≠ ⊤) (hlt : Nat.card A < Nat.card K) :
    ¬ IsCoatom (Subgroup.normalizer (V : Set G)) := by
  have hDidx : ¬ r ∣ D.index := by
    have h1 := V.card_mul_index
    have h2 := D.card_mul_index
    rw [hcard] at h2
    have : D.index = V.index := Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
    rwa [this]
  let PV := hV.toSylow hVidx
  let PD := hD.toSylow hDidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PD PV
  have hVeq : V = D.map (MulAut.conj g).toMonoidHom := by
    have : ((g • PD : Sylow r G) : Subgroup G) = D.map (MulAut.conj g).toMonoidHom := rfl
    rw [← this, hg]
    rfl
  have hND : Nat.card (Subgroup.normalizer (D : Set G)) ≤ Nat.card A := by
    rw [hVeq, normalizer_map_conj, card_map_conj] at hAcard
    exact hAcard
  have hAeq : A = Subgroup.normalizer (D : Set G) := Subgroup.eq_of_le_of_card_ge hAD hND
  have hNV : Subgroup.normalizer (V : Set G) = A.map (MulAut.conj g).toMonoidHom := by
    rw [hVeq, normalizer_map_conj, hAeq]
  rw [hNV]
  refine not_isCoatom_of_lt (Subgroup.map_mono hAK) ?_ ?_
  · rw [card_map_conj, card_map_conj]
    exact hlt
  · intro h
    apply hK
    rw [← Subgroup.comap_map_eq_self_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective K, h, Subgroup.comap_top]

theorem le_normalizer_of_sq {M N V : Subgroup G} (hNM : ∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hV : ∀ x, x ∈ V ↔ x ∈ N ∧ x * x = 1) : M ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hV, hV]
  constructor
  · rintro ⟨hh, hh2⟩
    refine ⟨hNM g hg h hh, ?_⟩
    calc g * h * g⁻¹ * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
      _ = 1 := by rw [hh2]; group
  · rintro ⟨hh, hh2⟩
    have hh' := hNM g⁻¹ (M.inv_mem hg) _ hh
    rw [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at hh'
    refine ⟨hh', ?_⟩
    calc h * h = g⁻¹ * (g * h * g⁻¹ * (g * h * g⁻¹)) * g := by group
      _ = 1 := by rw [hh2]; group

theorem conj_mem_self {N : Subgroup G} : ∀ g ∈ N, ∀ x ∈ N, g * x * g⁻¹ ∈ N :=
  fun _ hg _ hx => N.mul_mem (N.mul_mem hg hx) (N.inv_mem hg)

theorem inv_mul_mem_alternating {σ τ : Equiv.Perm (Fin 4)} (hσ : σ ∉ alternatingGroup (Fin 4))
    (hτ : τ ∉ alternatingGroup (Fin 4)) : σ⁻¹ * τ ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup] at *
  rw [map_mul, map_inv]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact absurd h hσ
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h' | h'
  · exact absurd h' hτ
  rw [h, h']
  decide

end Groups

end CFSG.Glauberman.Dickson.MaxCases

namespace CFSG.Glauberman.Dickson.MaxCases

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.GorensteinWalter
open CFSG.Glauberman.Dickson.MaxStructure CFSG.Glauberman.Dickson.MaxUp
open CFSG.Glauberman.Dickson.MaxDown CFSG.Glauberman.Dickson.MaxSubfield
open CFSG.Glauberman.Dickson.MaxTrace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open scoped MatrixGroups LinearAlgebra.Projectivization

theorem lt_half_of_sq_le {x y : ℕ} (hx : 3 ≤ x) (hxy : x ^ 2 ≤ y) :
    x * (x ^ 2 - 1) < y * (y ^ 2 - 1) / 2 := by
  apply lt_card_psl2_of
  have h1 : x ^ 2 * ((x ^ 2) ^ 2 - 1) ≤ y * (y ^ 2 - 1) :=
    Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
  have h2 : 2 * (x * (x ^ 2 - 1)) + 2 ≤ x ^ 2 * ((x ^ 2) ^ 2 - 1) := by
    have h9 : 9 ≤ x ^ 2 := by nlinarith
    obtain ⟨a, ha⟩ : ∃ a, x ^ 2 = a + 1 := ⟨x ^ 2 - 1, by omega⟩
    have hxa : x ≤ a + 1 := by rw [← ha]; exact Nat.le_self_pow (by norm_num) x
    have ha8 : 8 ≤ a := by omega
    rw [ha, Nat.add_sub_cancel, show (a + 1) ^ 2 - 1 = a * (a + 2) from
      Nat.sub_eq_of_eq_add (by ring)]
    nlinarith [Nat.mul_le_mul_right a hxa, Nat.mul_le_mul ha8 ha8]
  omega

theorem half_lt_half_of_sq_le {x y : ℕ} (hx : 3 ≤ x) (hxy : x ^ 2 ≤ y) :
    x * (x ^ 2 - 1) / 2 < y * (y ^ 2 - 1) / 2 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (lt_half_of_sq_le hx hxy)

theorem sq_mod_sixteen_of_mod_eight' {p : ℕ} (hp : p % 8 = 1 ∨ p % 8 = 7) : p ^ 2 % 16 = 1 := by
  have h := Nat.pow_mod p 2 16
  have hlt : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h8 : p % 8 = (p % 16) % 8 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  rw [h]
  interval_cases hr : p % 16 <;> omega

theorem mod_eight_of_sq_mod_sixteen {p : ℕ} (hp : p ^ 2 % 16 = 1) : p % 8 = 1 ∨ p % 8 = 7 := by
  have h := Nat.pow_mod p 2 16
  have hlt : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h8 : p % 8 = (p % 16) % 8 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  rw [h] at hp
  interval_cases hr : p % 16 <;> omega

theorem sq_mod_five_of_mod_ten' {p : ℕ} (hp : p % 10 = 1 ∨ p % 10 = 9) : p ^ 2 % 5 = 1 := by
  have h := Nat.pow_mod p 2 5
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h5 : p % 5 = (p % 10) % 5 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  rw [h]
  interval_cases hr : p % 5 <;> omega

theorem not_sixteen_dvd {p f : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) (hf : ¬ 2 ∣ f) :
    ¬ 16 ∣ p ^ (2 * f) - 1 := by
  intro h
  have h9 := sq_mod_sixteen_of_mod_eight hp
  have hodd : Odd f := Nat.odd_iff.mpr (by omega)
  have hpow : p ^ (2 * f) % 16 = 9 := by
    rw [pow_mul, Nat.pow_mod, h9]
    exact (nine_pow_odd hodd).1
  have hpos : 1 ≤ p ^ (2 * f) := by
    rcases Nat.eq_zero_or_pos (p ^ (2 * f)) with h0 | h0
    · rw [h0] at hpow
      norm_num at hpow
    · exact h0
  omega

theorem not_five_dvd {p f : ℕ} (hp : p ^ 2 % 5 = 4) (hf : ¬ 2 ∣ f) :
    ¬ 5 ∣ p ^ (2 * f) - 1 := by
  intro h
  have hodd : Odd f := Nat.odd_iff.mpr (by omega)
  obtain ⟨k, rfl⟩ := hodd
  have hpow : p ^ (2 * (2 * k + 1)) % 5 = 4 := by
    rw [show 2 * (2 * k + 1) = 2 * 2 * k + 2 by ring, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod,
      show (p ^ (2 * 2)) % 5 = 1 by
        rw [pow_mul, Nat.pow_mod, hp],
      hp]
    norm_num
  have hpos : 1 ≤ p ^ (2 * (2 * k + 1)) := by
    rcases Nat.eq_zero_or_pos (p ^ (2 * (2 * k + 1))) with h0 | h0
    · rw [h0] at hpow
      norm_num at hpow
    · exact h0
  omega

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

omit [Field F] [Finite F] in
theorem three_le_of_ne_two (hp2 : p ≠ 2) : 3 ≤ p := by
  have h2 := hp.out.two_le
  rcases hp.out.odd_of_ne_two hp2 with ⟨j, hj⟩
  omega

theorem isSquare_of_mem_fixField [CharP F p] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 * k ∣ f) {x : F} (hx : x ∈ fixField F p k) : IsSquare x := by
  let : Fintype F := Fintype.ofFinite F
  by_cases hx0 : x = 0
  · rw [hx0]
    exact ⟨0, by rw [mul_zero]⟩
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  rw [FiniteField.isSquare_iff hF2 hx0]
  rw [mem_fixField] at hx
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  have hx1 : x ^ (p ^ k - 1) = 1 := by
    have h : x ^ (p ^ k - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hpk, one_mul, hx]
    exact mul_right_cancel₀ hx0 h
  have hFcard : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨s, hs⟩ := hk
  have hodd : Odd (p ^ k) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨r, hr⟩ := hodd
  have hdvd : p ^ k - 1 ∣ Fintype.card F / 2 := by
    have h1 : p ^ (2 * k) - 1 ∣ p ^ f - 1 := by
      rw [hs, pow_mul p (2 * k) s]
      simpa using Nat.sub_dvd_pow_sub_pow (p ^ (2 * k)) 1 s
    have h2' : 2 * (p ^ k - 1) ∣ p ^ (2 * k) - 1 := by
      refine ⟨r + 1, ?_⟩
      rw [show p ^ (2 * k) = p ^ k * p ^ k by ring, hr]
      have : (2 * r + 1) * (2 * r + 1) - 1 = 2 * r * (2 * r + 2) := by
        rw [show (2 * r + 1) * (2 * r + 1) = 2 * r * (2 * r + 2) + 1 by ring]
        simp
      rw [this, show 2 * r + 1 - 1 = 2 * r by omega]
      ring
    have h3 : Fintype.card F / 2 = (p ^ f - 1) / 2 := by
      rw [hFcard]
      have : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
      obtain ⟨t, ht⟩ := this
      omega
    rw [h3]
    exact Nat.dvd_div_of_mul_dvd (h2'.trans h1)
  obtain ⟨d, hd⟩ := hdvd
  rw [hd, pow_mul, hx1, one_pow]

theorem card_overgroup_fixField
    [CharP F p] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {k : ℕ}
    (hk0 : k ≠ 0) (hkf : k ∣ f) (hk : k < f) (c : PGL2 F) :
    p ^ k * ((p ^ k) ^ 2 - 1) / 2 ≤ Nat.card (overgroup (fixField F p k) c) ∧
      Nat.card (overgroup (fixField F p k) c) ≤ p ^ k * ((p ^ k) ^ 2 - 1) ∧
      overgroup (fixField F p k) c ≠ ⊤ := by
  have hp' := hp.out
  have hf0 : f ≠ 0 := by omega
  have hp3 := three_le_of_ne_two hp2
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp', hp'.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hf0, hF⟩
  have h2kf : 2 * k ≤ f := two_mul_le_of_dvd_of_ne hkf (Nat.ne_of_lt hk) hf0
  have hq3 : 3 < Nat.card F := by
    rw [hF]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ f := Nat.pow_le_pow_left hp3 f
  have hKcard : Nat.card (fixField F p k) = p ^ k := card_fixField hF hkf hk0
  have hOcard := card_overgroup hodd hq3 (fixField F p k) c
  have hoddK : IsOddPrimePower (Nat.card (fixField F p k)) :=
    ⟨p, k, hp', hp'.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk0, hKcard⟩
  have hlow : p ^ k * ((p ^ k) ^ 2 - 1) / 2 ≤ Nat.card (overgroup (fixField F p k) c) := by
    have h1 : Nat.card (PSL2MatrixGroup (fixField F p k)) ≤
        Nat.card (subfieldSubgroup (fixField F p k)) := card_subfieldSubgroup_ge _
    have h2 : Nat.card (PSL2MatrixGroup (fixField F p k)) =
        Nat.card (fixField F p k) * (Nat.card (fixField F p k) ^ 2 - 1) / 2 :=
      psl2_card_formula _ hoddK
    rw [h2, hKcard] at h1
    rw [hOcard]
    exact h1
  have hup : Nat.card (overgroup (fixField F p k) c) ≤ p ^ k * ((p ^ k) ^ 2 - 1) := by
    have h1 : Nat.card (subfieldSubgroup (fixField F p k)) ≤
        Nat.card (PGL2 (fixField F p k)) := card_subfieldSubgroup_le _
    rw [pgl2_card_formula, hKcard] at h1
    rw [hOcard]
    exact h1
  refine ⟨hlow, hup, ne_top_of_card_lt ?_⟩
  rw [card_psl2_odd hF hp2]
  refine lt_of_le_of_lt hup (lt_half_of_sq_le (le_trans hp3 (Nat.le_self_pow hk0 p)) ?_)
  rw [← pow_mul, mul_comm]
  exact Nat.pow_le_pow_right hp'.pos h2kf

theorem card_ge_of_isCoatom_subfield
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) {c : PGL2 F} {K₀ : Subfield F}
    {m : ℕ} (hK₀ : Nat.card K₀ = p ^ m)
    (hMc : ∀ x ∈ M, c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage K₀)
    {k : ℕ} (hmk : m ∣ k) (hkf : k ∣ f) (hk : k < f) :
    p ^ k * ((p ^ k) ^ 2 - 1) / 2 ≤ Nat.card M := by
  have hf0 : f ≠ 0 := by omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hf0 (Nat.eq_zero_of_zero_dvd hkf)
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  obtain ⟨hlow, -, hne⟩ := card_overgroup_fixField hF hp2 hk0 hkf hk c
  have hle : K₀ ≤ fixField F p k := (le_fixField_of_card hK₀).trans (fixField_mono hmk)
  rw [eq_of_isCoatom_le hM (le_overgroup hMc hle) hne]
  exact hlow

theorem card_eq_of_isCoatom_subfield
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) {c : PGL2 F} {K₀ : Subfield F}
    {m : ℕ} (hK₀ : Nat.card K₀ = p ^ m)
    (hMc : ∀ x ∈ M, c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage K₀)
    {k : ℕ} (hmk : m ∣ k) (hkf : 2 * k ∣ f) :
    Nat.card M = p ^ k * ((p ^ k) ^ 2 - 1) := by
  have hp' := hp.out
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hf0 (Nat.eq_zero_of_zero_dvd (by simpa using hkf))
  have hkf' : k ∣ f := dvd_of_mul_left_dvd hkf
  have hk : k < f := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hkf
    omega
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  obtain ⟨-, -, hne⟩ := card_overgroup_fixField hF hp2 hk0 hkf' hk c
  have hle : K₀ ≤ fixField F p k := (le_fixField_of_card hK₀).trans (fixField_mono hmk)
  rw [eq_of_isCoatom_le hM (le_overgroup hMc hle) hne]
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp', hp'.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hf0, hF⟩
  have hq3 : 3 < Nat.card F := by
    rw [hF]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ f := Nat.pow_le_pow_left (three_le_of_ne_two hp2) f
  rw [card_overgroup hodd hq3, card_subfieldSubgroup_eq _
    (fun x => isSquare_of_mem_fixField hF hp2 hkf x.2), pgl2_card_formula,
    card_fixField hF hkf' hk0]

theorem card_psl2_galoisField' {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : m ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField p m)) = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
  rw [card_psl2_galoisField hp2 hm, ← pow_mul, mul_comm m 2]

theorem card_pgl2_galoisField' {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) = p ^ m * ((p ^ m) ^ 2 - 1) := by
  rw [card_pgl2_galoisField hm, ← pow_mul, mul_comm m 2]

theorem nonempty_psl2_galoisField_five [Fact (Nat.Prime 5)] :
    Nonempty (PSL2MatrixGroup (GaloisField 5 1) ≃* alternatingGroup (Fin 5)) := by
  have hK : Nat.card (GaloisField 5 1) = 5 := by rw [GaloisField.card 5 1 one_ne_zero, pow_one]
  have hΩ : Nat.card (ℙ (GaloisField 5 1) (Fin 2 → GaloisField 5 1)) = 6 := by
    rw [Projectivization.card_of_finrank_two _ _ (Module.finrank_fin_fun _), hK]
  have hG : Nat.card (PSL2MatrixGroup (GaloisField 5 1)) = 60 :=
    (card_psl2_galoisField (p := 5) (m := 1) (by norm_num) one_ne_zero).trans (by norm_num)
  exact huppert_II_8_25_transitive_degree_six_order_sixty inferInstance hΩ hG

end CFSG.Glauberman.Dickson.MaxCases
