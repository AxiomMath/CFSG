module

public import CFSG.Sporadic.Recognition.LyonsSimsCover

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.Alternating.Multipliers
  CFSG.Alternating.Multipliers.Spin CFSG.RankThree.PerfectCover
open scoped commutatorElement

theorem negOne_comm {n : ℕ} (x : monomial n) : x * negOne = negOne * x := by
  apply Subtype.ext
  apply Units.ext
  simp [negOne]

theorem mul_dd_swap {n : ℕ} {a₁ b₁ a₂ b₂ : Fin n} (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁)
    (h1b2 : a₁ ≠ b₂) (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) (g : monomial n)
    (e1 : perm g a₁ = b₁) (e2 : perm g a₂ = b₂) (e3 : perm g b₁ = a₁) (e4 : perm g b₂ = a₂) :
    g * dd h12 hbb = negOne * (dd h12 hbb * g) := by
  apply Subtype.ext
  apply Units.ext
  set X : Cl n := ((g : (Cl n)ˣ) : Cl n) with hX
  change X * (half * r a₁ a₂ * r b₁ b₂) = -1 * ((half * r a₁ a₂ * r b₁ b₂) * X)
  have hxh : X * half = half * X := (half_comm _).symm
  have m1 : X * r a₁ a₂ = r b₁ b₂ * X := by rw [hX, mul_r, e1, e2]
  have m2 : X * r b₁ b₂ = r a₁ a₂ * X := by rw [hX, mul_r, e3, e4]
  calc X * (half * r a₁ a₂ * r b₁ b₂) = half * (X * r a₁ a₂) * r b₁ b₂ := by
        rw [← mul_assoc, ← mul_assoc, hxh, mul_assoc half]
    _ = half * r b₁ b₂ * (X * r b₁ b₂) := by
        rw [m1, ← mul_assoc half, mul_assoc (half * r b₁ b₂)]
    _ = half * (r b₁ b₂ * r a₁ a₂) * X := by
        rw [m2, ← mul_assoc, mul_assoc half]
    _ = -1 * ((half * r a₁ a₂ * r b₁ b₂) * X) := by
        rw [r_mul_r (Ne.symm h1b1) (Ne.symm h2b1) (Ne.symm h1b2) (Ne.symm h2b2)]
        simp only [mul_neg, neg_mul, one_mul, mul_assoc]

theorem commutator_dd_swap {n : ℕ} {a₁ b₁ a₂ b₂ : Fin n} (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁)
    (h1b2 : a₁ ≠ b₂) (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) (g : monomial n)
    (e1 : perm g a₁ = b₁) (e2 : perm g a₂ = b₂) (e3 : perm g b₁ = a₁) (e4 : perm g b₂ = a₂) :
    ⁅g, dd h12 hbb⁆ = negOne := by
  rw [commutatorElement_def, mul_dd_swap h12 h1b1 h1b2 h2b1 h2b2 hbb g e1 e2 e3 e4]
  group

theorem commutator_E_ne_one {m : ℕ} {a₁ b₁ a₂ b₂ : Fin (m + 2)} (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁)
    (h1b2 : a₁ ≠ b₂) (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) (g h : E (m + 2))
    (e1 : (psi g : Perm (Fin (m + 2))) a₁ = b₁) (e2 : (psi g : Perm (Fin (m + 2))) a₂ = b₂)
    (e3 : (psi g : Perm (Fin (m + 2))) b₁ = a₁) (e4 : (psi g : Perm (Fin (m + 2))) b₂ = a₂)
    (hh : (psi h : Perm (Fin (m + 2))) = swap a₁ a₂ * swap b₁ b₂) : ⁅g, h⁆ ≠ 1 := by
  set g0 : monomial (m + 2) := (((g : H (m + 2))) : monomial (m + 2)) with hg0
  set h0 : monomial (m + 2) := (((h : H (m + 2))) : monomial (m + 2)) with hh0
  set d : monomial (m + 2) := dd h12 hbb with hd
  set c : monomial (m + 2) := h0 * d⁻¹ with hc
  have hph : perm h0 = (psi h : Perm (Fin (m + 2))) := rfl
  have hpc : perm c = 1 := by
    rw [hc, map_mul, map_inv, hph, hh, hd, perm_dd, mul_inv_cancel]
  have hcg : g0 * c = c * g0 := by
    have hmem : g0 ∈ H (m + 2) := (g : H (m + 2)).2
    have := H_le_centralizer hpc hmem
    exact mem_centralizer_singleton_iff.1 this
  have hcomm : ⁅g0, h0⁆ = negOne := by
    have hh1 : h0 = c * d := by rw [hc]; group
    calc ⁅g0, h0⁆ = ⁅g0, c * d⁆ := by rw [hh1]
      _ = g0 * c * d * g0⁻¹ * d⁻¹ * c⁻¹ := by simp only [commutatorElement_def]; group
      _ = c * g0 * d * g0⁻¹ * d⁻¹ * c⁻¹ := by rw [hcg]
      _ = c * ⁅g0, d⁆ * c⁻¹ := by simp only [commutatorElement_def]; group
      _ = c * negOne * c⁻¹ := by
        rw [commutator_dd_swap h12 h1b1 h1b2 h2b1 h2b2 hbb g0 e1 e2 e3 e4]
      _ = negOne := by rw [negOne_comm c, mul_assoc, mul_inv_cancel, mul_one]
  intro h1
  have h2 : ⁅g0, h0⁆ = 1 := by
    have := congrArg (fun x : E (m + 2) => ((x : H (m + 2)) : monomial (m + 2))) h1
    simpa [commutatorElement_def, hg0, hh0] using this
  exact negOne_ne_one (hcomm.symm.trans h2)

theorem comm_swap_pairs {α : Type*} [DecidableEq α] {a₁ b₁ a₂ b₂ : α}
    (h1b1 : a₁ ≠ b₁) (h1b2 : a₁ ≠ b₂) (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂)
    (σ : Perm α) (e1 : σ a₁ = b₁) (e2 : σ a₂ = b₂) (e3 : σ b₁ = a₁) (e4 : σ b₂ = a₂) :
    σ * (swap a₁ a₂ * swap b₁ b₂) = (swap a₁ a₂ * swap b₁ b₂) * σ := by
  have h1 : σ * swap a₁ a₂ * σ⁻¹ = swap b₁ b₂ := by rw [← swap_apply_apply, e1, e2]
  have h2 : σ * swap b₁ b₂ * σ⁻¹ = swap a₁ a₂ := by rw [← swap_apply_apply, e3, e4]
  have hc : swap b₁ b₂ * swap a₁ a₂ = swap a₁ a₂ * swap b₁ b₂ := by
    ext x
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
    split_ifs <;> grind
  have h3 : σ * (swap a₁ a₂ * swap b₁ b₂) * σ⁻¹ = swap a₁ a₂ * swap b₁ b₂ := by
    calc σ * (swap a₁ a₂ * swap b₁ b₂) * σ⁻¹
        = (σ * swap a₁ a₂ * σ⁻¹) * (σ * swap b₁ b₂ * σ⁻¹) := by group
      _ = swap a₁ a₂ * swap b₁ b₂ := by rw [h1, h2, hc]
  calc σ * (swap a₁ a₂ * swap b₁ b₂)
      = σ * (swap a₁ a₂ * swap b₁ b₂) * σ⁻¹ * σ := by group
    _ = (swap a₁ a₂ * swap b₁ b₂) * σ := by rw [h3]

theorem commutator_ne_one_of_doubleCover {n : ℕ} (hn : 8 ≤ n) {X : Type} [Group X]
    (hX : IsDoubleCoverOfAlt X n) {π : X →* alternatingGroup (Fin n)}
    (hπs : Function.Surjective π) (hπk : π.ker = center X) {a₁ b₁ a₂ b₂ : Fin n} (h12 : a₁ ≠ a₂)
    (h1b1 : a₁ ≠ b₁) (h1b2 : a₁ ≠ b₂) (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂)
    {x y : X} (e1 : (π x : Perm (Fin n)) a₁ = b₁) (e2 : (π x : Perm (Fin n)) a₂ = b₂)
    (e3 : (π x : Perm (Fin n)) b₁ = a₁) (e4 : (π x : Perm (Fin n)) b₂ = a₂)
    (hy : (π y : Perm (Fin n)) = swap a₁ a₂ * swap b₁ b₂) : ⁅x, y⁆ ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 3 ≤ m := by omega
  have hperf : Group.IsPerfect (alternatingGroup (Fin (m + 2))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  have hXperf : Group.IsPerfect X := hX.1.1
  have hker : π.ker ≤ center X := hπk.le
  set uX : HopfCover (alternatingGroup (Fin (m + 2))) →* X := hopfLift π hπs hker with huX
  set uE : HopfCover (alternatingGroup (Fin (m + 2))) →* E (m + 2) :=
    hopfLift psi (psi_surjective hm) ker_psi_le_center with huE
  obtain ⟨xU, hxU⟩ := hopfCoverMap_surjective (S := alternatingGroup (Fin (m + 2))) (π x)
  obtain ⟨yU, hyU⟩ := hopfCoverMap_surjective (S := alternatingGroup (Fin (m + 2))) (π y)
  have hxE : psi (uE xU) = π x := by
    have := congrArg (fun f => f xU) (comp_hopfLift psi (psi_surjective hm) ker_psi_le_center)
    simpa [hxU] using this
  have hyE : psi (uE yU) = π y := by
    have := congrArg (fun f => f yU) (comp_hopfLift psi (psi_surjective hm) ker_psi_le_center)
    simpa [hyU] using this
  have hxX : π (uX xU) = π x := by
    have := congrArg (fun f => f xU) (comp_hopfLift π hπs hker)
    simpa [hxU] using this
  have hyX : π (uX yU) = π y := by
    have := congrArg (fun f => f yU) (comp_hopfLift π hπs hker)
    simpa [hyU] using this
  have hπc : ⁅π x, π y⁆ = 1 := by
    have h1 := comm_swap_pairs h1b1 h1b2 h2b1 h2b2 (π x : Perm (Fin (m + 2))) e1 e2 e3 e4
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy, h1, OneMemClass.coe_one]
    group
  have hmem : ⁅xU, yU⁆ ∈ hopfMultiplier (alternatingGroup (Fin (m + 2))) := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hxU, hyU, hπc]
  have hne : ⁅xU, yU⁆ ≠ 1 := by
    intro h
    have h1 : ⁅uE xU, uE yU⁆ = 1 := by rw [← map_commutatorElement, h, map_one]
    refine commutator_E_ne_one h12 h1b1 h1b2 h2b1 h2b2 hbb (uE xU) (uE yU) ?_ ?_ ?_ ?_ ?_ h1
    · rw [hxE]; exact e1
    · rw [hxE]; exact e2
    · rw [hxE]; exact e3
    · rw [hxE]; exact e4
    · rw [hyE]; exact hy
  have hMcard : Nat.card (hopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_hopfMultiplier_alternatingGroup hn
  have hmap : (hopfMultiplier (alternatingGroup (Fin (m + 2)))).map uX = π.ker :=
    map_hopfMultiplier_hopfLift π hπs hker
  have hkcard : Nat.card π.ker = 2 := by rw [hπk]; exact hX.2.1
  have hfin : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hkcard]; norm_num)
  have hfinM : Finite (hopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    Nat.finite_of_card_ne_zero (by rw [hMcard]; norm_num)
  let f : hopfMultiplier (alternatingGroup (Fin (m + 2))) → π.ker := fun k =>
    ⟨uX k, by rw [← hmap]; exact ⟨k, k.2, rfl⟩⟩
  have hfsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact ⟨⟨k, hk⟩, rfl⟩
  have hfbij : Function.Bijective f :=
    Function.Surjective.bijective_of_nat_card_le hfsurj (by rw [hMcard, hkcard])
  intro hxy
  have h1 : ⁅uX xU, uX yU⁆ = 1 := by
    have e : ∀ (u : HopfCover (alternatingGroup (Fin (m + 2)))), π (uX u) = π x → ∃ c ∈ center X,
        uX u = x * c := by
      intro u hu
      refine ⟨x⁻¹ * uX u, ?_, by group⟩
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
    obtain ⟨c₁, hc₁, h₁⟩ := e xU hxX
    obtain ⟨c₂, hc₂, h₂⟩ := (fun u (hu : π (uX u) = π y) => (by
      refine ⟨y⁻¹ * uX u, ?_, by group⟩
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel] :
        ∃ c ∈ center X, uX u = y * c)) yU hyX
    rw [h₁, h₂, CFSG.SectionRank.commutatorElement_mul_mem_center x y hc₁ hc₂, hxy]
  have h2 : f ⟨⁅xU, yU⁆, hmem⟩ = f 1 := by
    apply Subtype.ext
    simp only [f, map_commutatorElement, h1]
    rfl
  exact hne (congrArg Subtype.val (hfbij.1 h2))

theorem exists_swap_pairs {n : ℕ} {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n))
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ a₁ b₁ a₂ b₂ : Fin n, a₁ ≠ a₂ ∧ a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ ∧ b₁ ≠ b₂ ∧
      σ a₁ = b₁ ∧ σ a₂ = b₂ ∧ σ b₁ = a₁ ∧ σ b₂ = a₂ := by
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun p : Perm (Fin n) => p x) h2
    simpa using this
  obtain ⟨a₁, ha₁⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  by_cases hex : ∃ a₂, σ a₂ ≠ a₂ ∧ a₂ ≠ a₁ ∧ a₂ ≠ σ a₁
  · obtain ⟨a₂, h2ne, h2a, h2b⟩ := hex
    have hb1 : σ a₂ ≠ a₁ := fun h => h2b (by rw [← h, hinv])
    have hb2 : σ a₂ ≠ σ a₁ := fun h => h2a (σ.injective h)
    exact ⟨a₁, σ a₁, a₂, σ a₂, h2a.symm, ha₁.symm, hb1.symm, h2b, h2ne.symm, hb2.symm, rfl, rfl,
      hinv a₁, hinv a₂⟩
  · exfalso
    push Not at hex
    have hs : σ = swap a₁ (σ a₁) := by
      ext x
      by_cases hx : σ x = x
      · have hxa : x ≠ a₁ := fun h => ha₁ (h ▸ hx)
        have hxb : x ≠ σ a₁ := fun h => by
          apply ha₁
          have := hx
          rw [h, hinv] at this
          exact this.symm
        rw [swap_apply_of_ne_of_ne hxa hxb, hx]
      · by_cases hxa1 : x = a₁
        · rw [hxa1, swap_apply_left]
        · have hxb := hex x hx hxa1
          rw [hxb, swap_apply_right, hinv]
    have hsign : sign σ = 1 := mem_alternatingGroup.1 hσ
    rw [hs, sign_swap ha₁.symm] at hsign
    exact absurd hsign (by decide)

theorem centralizer_eq_comap_conjAct {E : Type*} [Group E] (y : E) :
    centralizer ({y} : Set E) =
      (MulAction.stabilizer (ConjAct E) y).comap
        (ConjAct.toConjAct : E ≃* ConjAct E).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Subgroup.mem_comap,
    MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem index_centralizer_eq_ncard_orbit {E : Type*} [Group E] (y : E) :
    (centralizer ({y} : Set E)).index = (MulAction.orbit (ConjAct E) y).ncard := by
  rw [centralizer_eq_comap_conjAct, Subgroup.index_comap_of_surjective _
    (ConjAct.toConjAct : E ≃* ConjAct E).surjective, MulAction.index_stabilizer]

theorem even_index_centralizer {X : Type*} [Group X] [Finite X] {z y p : X} (hzc : z ∈ center X)
    (hz1 : z ≠ 1) (hz2 : z * z = 1) (hp : p * y * p⁻¹ = y * z) :
    Even (centralizer ({y} : Set X)).index := by
  classical
  have hzc' : ∀ g : X, g * z = z * g := mem_center_iff.1 hzc
  set O := MulAction.orbit (ConjAct X) y with hO
  have hmem : ∀ x ∈ O, x * z ∈ O := by
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨ConjAct.toConjAct (ConjAct.ofConjAct c * p), ?_⟩
    simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_rev]
    calc ConjAct.ofConjAct c * p * y * (p⁻¹ * (ConjAct.ofConjAct c)⁻¹)
        = ConjAct.ofConjAct c * (p * y * p⁻¹) * (ConjAct.ofConjAct c)⁻¹ := by group
      _ = ConjAct.ofConjAct c * (y * z) * (ConjAct.ofConjAct c)⁻¹ := by rw [hp]
      _ = ConjAct.ofConjAct c * y * ((ConjAct.ofConjAct c)⁻¹ * z) := by
        rw [hzc' (ConjAct.ofConjAct c)⁻¹]
        group
      _ = ConjAct.ofConjAct c * y * (ConjAct.ofConjAct c)⁻¹ * z := by group
  let f : Function.End O := fun x => ⟨x.1 * z, hmem x.1 x.2⟩
  have : Fintype O := Fintype.ofFinite O
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    simp only [pow_one, pow_two]
    show x.1 * z * z = x.1
    rw [mul_assoc, hz2, mul_one]
  have hfix : Function.fixedPoints f = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have h1 : x.1 * z = x.1 := congrArg Subtype.val hx
    apply hz1
    simpa using h1
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2
  have : IsEmpty ↑(Function.fixedPoints f) := Set.isEmpty_coe_sort.mpr hfix
  have hz0 : Fintype.card ↑(Function.fixedPoints f) = 0 := Fintype.card_eq_zero
  rw [hz0] at hmod
  have h0 : Fintype.card O % 2 = 0 := hmod
  rw [index_centralizer_eq_ncard_orbit, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Nat.even_iff.mpr h0

theorem mem_center_of_mem_center_sylow {n : ℕ} (hn : 8 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsDoubleCoverOfAlt X n) (S : Sylow 2 X) {w : X}
    (hwc : ∀ s ∈ (S : Subgroup X), s * w = w * s) (hw2 : w * w = 1) : w ∈ center X := by
  obtain ⟨π, hπs, hπk⟩ :=
    CFSG.Sporadic.Recognition.LyonsSims.exists_centralExtension_of_doubleCover hX
  by_contra hwn
  have hπw : π w ≠ 1 := fun h => hwn (hπk ▸ h)
  have hπw2 : (π w : Perm (Fin n)) * (π w : Perm (Fin n)) = 1 := by
    have : π (w * w) = 1 := by rw [hw2, map_one]
    rw [map_mul] at this
    exact congrArg Subtype.val this
  have hπw1 : (π w : Perm (Fin n)) ≠ 1 := fun h => hπw (Subtype.ext h)
  obtain ⟨a₁, b₁, a₂, b₂, h12, h1b1, h1b2, h2b1, h2b2, hbb, e1, e2, e3, e4⟩ :=
    exists_swap_pairs (π w).2 hπw2 hπw1
  have hsmem : swap a₁ a₂ * swap b₁ b₂ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap h12, sign_swap hbb]
    decide
  obtain ⟨y, hy⟩ := hπs ⟨swap a₁ a₂ * swap b₁ b₂, hsmem⟩
  have hy' : (π y : Perm (Fin n)) = swap a₁ a₂ * swap b₁ b₂ := congrArg Subtype.val hy
  have hne : ⁅w, y⁆ ≠ 1 :=
    commutator_ne_one_of_doubleCover hn hX hπs hπk h12 h1b1 h1b2 h2b1 h2b2 hbb e1 e2 e3 e4 hy'
  have hπc : ⁅π w, π y⁆ = 1 := by
    have h1 := comm_swap_pairs h1b1 h1b2 h2b1 h2b2 (π w : Perm (Fin n)) e1 e2 e3 e4
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy', h1, OneMemClass.coe_one]
    group
  have hzc : ⁅w, y⁆ ∈ center X := by
    rw [← hπk, MonoidHom.mem_ker, map_commutatorElement, hπc]
  have hz2 : ⁅w, y⁆ * ⁅w, y⁆ = 1 := by
    have h1 : orderOf (⟨⁅w, y⁆, hzc⟩ : center X) ∣ Nat.card (center X) :=
      orderOf_dvd_natCard _
    rw [hX.2.1] at h1
    have h2 : (⟨⁅w, y⁆, hzc⟩ : center X) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    have h3 := congrArg Subtype.val h2
    simpa [pow_two] using h3
  have hp : y * w * y⁻¹ = w * ⁅w, y⁆ := by
    have e : ⁅w, y⁆ ⁻¹ = ⁅w, y⁆ := inv_eq_of_mul_eq_one_right hz2
    have hzc' := mem_center_iff.1 hzc
    have h1 : y * w * y⁻¹ = ⁅w, y⁆⁻¹ * w := by
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      group
    rw [h1, e]
    exact (hzc' w).symm
  have hev := even_index_centralizer hzc hne hz2 hp
  have hle : (S : Subgroup X) ≤ centralizer ({w} : Set X) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hwc s hs)
  have h1 : (centralizer ({w} : Set X)).index ∣ (S : Subgroup X).index :=
    Subgroup.index_dvd_of_le hle
  have h3 : ¬ 2 ∣ (S : Subgroup X).index := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact S.not_dvd_index
  exact h3 ((even_iff_two_dvd.mp hev).trans h1)

end CFSG.OddStandard.Solomon75
