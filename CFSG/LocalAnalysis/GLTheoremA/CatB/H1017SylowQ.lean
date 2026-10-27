module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open

theorem isElemAbelian_map' {G H : Type*} [Group G] [Group H] (f : G →* H) {p : ℕ}
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    have := congrArg Subtype.val (hE.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at this ⊢
    rw [← map_mul, ← map_mul, this]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (K : Subgroup G) : IsElemAbelian p (E.subgroupOf K) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, ?_⟩
  · have := congrArg Subtype.val
      (hE.1.1.comm ⟨(a : K), Subgroup.mem_subgroupOf.1 a.2⟩ ⟨(b : K), Subgroup.mem_subgroupOf.1 b.2⟩)
    exact this
  · intro x hx
    exact Subtype.ext (hE.2 _ (Subgroup.mem_subgroupOf.1 hx))

theorem comm_of_isElemAbelian' {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)

section Sylow

variable {X : Type} [Group X] [Finite X] {V : Type} [Finite V] {n m : ℕ}

theorem elemAbelian_le_of_conj_action (A P₀ : Subgroup X) (hAP : A ≤ P₀)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (ι : V → X) (hι : Function.Injective ι)
    (hA : ∀ x, x ∈ A ↔ ∃ v, ι v = x) (hV : Nat.card V = 3 ^ n)
    (μ : P₀ →* Equiv.Perm V) (hμ : ∀ (g : P₀) v, ι (μ g v) = (g : X) * ι v * (g : X)⁻¹)
    (hrange : Nat.card μ.range = 3 ^ m) (hX : ¬ 3 ^ (n + m + 1) ∣ Nat.card X)
    (hbound : ∀ H : Subgroup (Equiv.Perm V), H ≤ μ.range → IsElemAbelian 3 H → H ≠ ⊥ →
      Nat.card H * Nat.card {v // ∀ h ∈ H, h v = v} < 3 ^ n)
    (E : Subgroup X) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ n ∧ (Nat.card E = 3 ^ n → ∃ g : X, E = A.map (MulAut.conj g).toMonoidHom) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardA : Nat.card A = 3 ^ n := by
    rw [← hV]
    refine (Nat.card_congr (Equiv.ofBijective (fun v => (⟨ι v, (hA _).2 ⟨v, rfl⟩⟩ : A))
      ⟨fun v w h => hι (congrArg Subtype.val h), fun x => ?_⟩)).symm
    obtain ⟨v, hv⟩ := (hA x).1 x.2
    exact ⟨v, Subtype.ext hv⟩
  set A₀ : Subgroup P₀ := A.subgroupOf P₀ with hA₀def
  have hcardA₀ : Nat.card A₀ = 3 ^ n := by
    rw [← hcardA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
  have hA₀n : A₀.Normal := ⟨fun a ha g => by
    rw [hA₀def, Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨v, hv⟩ := (hA _).1 ha
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hv, ← hμ]
    exact (hA _).2 ⟨_, rfl⟩⟩
  have hA₀ker : A₀ ≤ μ.ker := by
    intro a ha
    rw [hA₀def, Subgroup.mem_subgroupOf] at ha
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun v => hι ?_
    rw [hμ, Equiv.Perm.one_apply, hAc _ ha _ ((hA _).2 ⟨v, rfl⟩), mul_inv_cancel_right]
  have hP₀ : Nat.card P₀ = Nat.card μ.ker * 3 ^ m := by
    rw [← hrange, Subgroup.card_ker_mul_card_range]
  have hP₀X : Nat.card P₀ ∣ Nat.card X := Subgroup.card_subgroup_dvd_card P₀
  have hkerA : 3 ^ n ∣ Nat.card μ.ker := hcardA₀ ▸ Subgroup.card_dvd_of_le hA₀ker
  have hker : ¬ 3 ^ (n + 1) ∣ Nat.card μ.ker := fun h => hX (by
    refine dvd_trans ?_ hP₀X
    rw [hP₀, show n + m + 1 = (n + 1) + m by ring, pow_add]
    exact Nat.mul_dvd_mul_right h _)
  have hXne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hP₀ne : Nat.card P₀ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 P₀))
  have hS₀card : Nat.card S₀ = 3 ^ (n + m) := by
    rw [Sylow.card_eq_multiplicity]
    congr 1
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      apply hX
      refine dvd_trans ?_ hP₀X
      exact (Nat.pow_dvd_pow 3 hlt).trans (Nat.ordProj_dvd _ _)
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hP₀ne, hP₀, pow_add]
      exact Nat.mul_dvd_mul_right hkerA _
  have hA₀S₀ : A₀ ≤ S₀ := IsPGroup.le_sylow_of_normal (IsPGroup.of_card hcardA₀) S₀
  have hS₀ker : (S₀ : Subgroup P₀) ⊓ μ.ker = A₀ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (le_inf hA₀S₀ hA₀ker) ?_
    rw [hcardA₀]
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 ((S₀.isPGroup').to_le (inf_le_left :
      (S₀ : Subgroup P₀) ⊓ μ.ker ≤ S₀))
    rw [hj]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hlt
    push Not at hlt
    apply hker
    refine dvd_trans (Nat.pow_dvd_pow 3 hlt) ?_
    rw [← hj]
    exact Subgroup.card_dvd_of_le inf_le_right
  set S : Subgroup X := (S₀ : Subgroup P₀).map P₀.subtype with hSdef
  have hScard : Nat.card S = 3 ^ (n + m) := by
    rw [hSdef, Subgroup.card_map_of_injective P₀.subtype_injective, hS₀card]
  have hfX : (Nat.card X).factorization 3 = n + m := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      exact hX ((Nat.pow_dvd_pow 3 hlt).trans (Nat.ordProj_dvd _ _))
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hXne, ← hScard]
      exact Subgroup.card_subgroup_dvd_card S
  let SX : Sylow 3 X := Sylow.ofCard S (by rw [hScard, hfX])
  obtain ⟨Q, hEQ⟩ := IsPGroup.exists_le_sylow (isPGroup_of_elemAbelian3' hE)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X SX Q
  set E' : Subgroup X := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'def
  have hE'S : E' ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup X) := hEQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    have e : (MulAut.conj g)⁻¹ • x = (MulAut.conj g⁻¹).toMonoidHom x := by
      rw [← map_inv]
      rfl
    rw [← e]
    exact hxQ
  have hE'e : IsElemAbelian 3 E' := isElemAbelian_map' _ hE
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hE'P : E' ≤ P₀ := hE'S.trans (Subgroup.map_subtype_le _)
  set F : Subgroup P₀ := E'.subgroupOf P₀ with hFdef
  have hcardF : Nat.card F = Nat.card E' := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'P).toEquiv
  have hFS : F ≤ S₀ := by
    intro x hx
    rw [hFdef, Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hE'S hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hFe : IsElemAbelian 3 F := isElemAbelian_subgroupOf hE'e P₀
  set ρ : F →* Equiv.Perm V := μ.comp F.subtype with hρ
  have hsplit : Nat.card F = Nat.card ρ.ker * Nat.card (F.map μ) := by
    rw [← Subgroup.card_ker_mul_card_range ρ, hρ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerF : Nat.card ρ.ker ≤ Nat.card {v // ∀ h ∈ F.map μ, h v = v} := by
    have hmemA : ∀ x : ρ.ker, ((x : F) : P₀) ∈ A₀ := fun x => by
      rw [← hS₀ker]
      exact ⟨hFS (x : F).2, by
        have := x.2
        rw [MonoidHom.mem_ker] at this
        exact this⟩
    have hex : ∀ x : ρ.ker, ∃ v, ι v = (((x : F) : P₀) : X) := fun x =>
      (hA _).1 (Subgroup.mem_subgroupOf.1 (hmemA x))
    choose w hw using hex
    refine Nat.card_le_card_of_injective (fun x => ⟨w x, ?_⟩) ?_
    · rintro _ ⟨y, hy, rfl⟩
      apply hι
      rw [hμ, hw x]
      have hc := comm_of_isElemAbelian' hFe hy (x : F).2
      have hc' : (y : X) * (((x : F) : P₀) : X) = (((x : F) : P₀) : X) * (y : X) :=
        congrArg Subtype.val hc
      rw [hc', mul_inv_cancel_right]
    · intro x y hxy
      have h1 : w x = w y := congrArg Subtype.val hxy
      have h2 := (hw x).symm.trans ((congrArg ι h1).trans (hw y))
      exact Subtype.ext (Subtype.ext (Subtype.ext h2))
  have hmain : Nat.card F ≤ 3 ^ n ∧ (Nat.card F = 3 ^ n → F = A₀) := by
    by_cases hbot : F.map μ = ⊥
    · have hFker : F ≤ μ.ker := (Subgroup.map_eq_bot_iff F).1 hbot
      have hFA : F ≤ A₀ := hS₀ker ▸ le_inf hFS hFker
      refine ⟨hcardA₀ ▸ Subgroup.card_le_of_le hFA, fun h => ?_⟩
      exact Subgroup.eq_of_le_of_card_ge hFA (by rw [h, hcardA₀])
    · have hb := hbound (F.map μ) (Subgroup.map_le_range μ F) (isElemAbelian_map' μ hFe) hbot
      have hlt : Nat.card F < 3 ^ n := by
        rw [hsplit]
        calc Nat.card ρ.ker * Nat.card (F.map μ)
            ≤ Nat.card {v // ∀ h ∈ F.map μ, h v = v} * Nat.card (F.map μ) :=
              Nat.mul_le_mul_right _ hkerF
          _ = Nat.card (F.map μ) * Nat.card {v // ∀ h ∈ F.map μ, h v = v} := mul_comm _ _
          _ < 3 ^ n := hb
      exact ⟨hlt.le, fun h => absurd h hlt.ne⟩
  rw [hcardF, hcardE'] at hmain
  refine ⟨hmain.1, fun h => ⟨g, ?_⟩⟩
  have hFA := hmain.2 h
  have hE'A : E' = A := by
    have h1 : E' ⊓ P₀ = A ⊓ P₀ := (Subgroup.subgroupOf_inj).1 hFA
    rwa [inf_of_le_left hE'P, inf_of_le_left hAP] at h1
  rw [← hE'A, hE'def, Subgroup.map_map]
  ext x
  constructor
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  · rintro ⟨y, hy, rfl⟩
    have : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) y = y := by
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [this]
    exact hy

end Sylow

section Checks

variable {V : Type} [Finite V]

theorem card_mul_fix_lt_of_checks (R : Subgroup (Equiv.Perm V))
    (h27 : ∀ H : Subgroup (Equiv.Perm V), H ≤ R → IsElemAbelian 3 H → Nat.card H ≤ 27)
    (c1 : ∀ x ∈ R, x ≠ 1 → Nat.card {v // x v = v} ≤ 27)
    (c2 : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x → x ≠ 1 → y ≠ 1 → y ≠ x → y ≠ x * x →
      Nat.card {v // x v = v ∧ y v = v} ≤ 9)
    (c3 : ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x * y = y * x → x * z = z * x → y * z = z * y → x ≠ 1 →
      y ≠ 1 → y ≠ x → y ≠ x * x →
      (∀ i < 3, ∀ j < 3, z ≠ x ^ i * y ^ j) →
      Nat.card {v // x v = v ∧ y v = v ∧ z v = v} ≤ 3)
    (H : Subgroup (Equiv.Perm V)) (hHR : H ≤ R) (hH : IsElemAbelian 3 H) (hne : H ≠ ⊥) :
    Nat.card H * Nat.card {v // ∀ h ∈ H, h v = v} < 3 ^ 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Equiv.Perm V) := inferInstance
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian3' hH)
  have hj27 : 3 ^ j ≤ 27 := hj ▸ h27 H hHR hH
  have hj1 : 1 ≤ j := by
    by_contra h0
    push Not at h0
    interval_cases j
    exact hne ((Subgroup.card_eq_one).1 (by rw [hj, pow_zero]))
  have hj3 : j ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ 4 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  obtain ⟨⟨x, hxH⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb => comm_of_isElemAbelian' hH ha hb
  have hout : ∀ s : Finset (Equiv.Perm V), s.card < Nat.card H → ∃ y ∈ H, y ∉ s := by
    intro s hs
    by_contra hall
    push Not at hall
    have : Nat.card H ≤ s.card := by
      have h := Nat.card_le_card_of_injective
        (fun y : H => (⟨y.1, Finset.mem_coe.2 (hall y.1 y.2)⟩ : ((s : Set (Equiv.Perm V)))))
        (fun a b h => by
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext h)
      rwa [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h
    omega
  have hfix_le : ∀ (p : V → Prop), (∀ v, (∀ h ∈ H, h v = v) → p v) →
      Nat.card {v // ∀ h ∈ H, h v = v} ≤ Nat.card {v // p v} := fun p hp =>
    Nat.card_le_card_of_injective (fun v => ⟨v.1, hp v.1 v.2⟩) fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h
  interval_cases j
  ·
    have := hfix_le (fun v => x v = v) fun v hv => hv x hxH
    have := c1 x (hHR hxH) hx1
    rw [hj]
    nlinarith
  ·
    obtain ⟨y, hyH, hy⟩ := hout {1, x, x * x} (by
      rw [hj]; exact (Finset.card_le_three).trans_lt (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    have := hfix_le (fun v => x v = v ∧ y v = v) fun v hv => ⟨hv x hxH, hv y hyH⟩
    have := c2 x (hHR hxH) y (hHR hyH) (hcomm x hxH y hyH) hx1 hy.1 hy.2.1 hy.2.2
    rw [hj]
    nlinarith
  ·
    obtain ⟨y, hyH, hy⟩ := hout {1, x, x * x} (by
      rw [hj]; exact (Finset.card_le_three).trans_lt (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    obtain ⟨z, hzH, hz⟩ := hout ((Finset.range 3 ×ˢ Finset.range 3).image
      fun ij => x ^ ij.1 * y ^ ij.2) (by
        rw [hj]
        refine Finset.card_image_le.trans_lt ?_
        simp)
    have hz' : ∀ i < 3, ∀ k < 3, z ≠ x ^ i * y ^ k := fun i hi k hk e =>
      hz (Finset.mem_image.2 ⟨(i, k), by simp [hi, hk], e.symm⟩)
    have := hfix_le (fun v => x v = v ∧ y v = v ∧ z v = v) fun v hv =>
      ⟨hv x hxH, hv y hyH, hv z hzH⟩
    have := c3 x (hHR hxH) y (hHR hyH) z (hHR hzH) (hcomm x hxH y hyH) (hcomm x hxH z hzH)
      (hcomm y hyH z hzH) hx1 hy.1 hy.2.1 hy.2.2 hz'
    rw [hj]
    nlinarith

end Checks

theorem apply_eq_of_unique_stab {W V : Type} (ι : V → Equiv.Perm W) {σ : Equiv.Perm W}
    (hσ : ∀ v, σ * ι v = ι v * σ) (hσ2 : σ * σ = 1) (p : W)
    (huniq : ∀ q, (∀ v, ι v p = p ↔ ι v q = q) → ∃ v, ι v p = q)
    (hsq : ∀ v, ι v (ι v p) = p → ι v p = p) : σ p = p := by
  have hst : ∀ v, ι v p = p ↔ ι v (σ p) = σ p := fun v => by
    have e : ι v (σ p) = σ (ι v p) := by
      rw [← Equiv.Perm.mul_apply, ← hσ v, Equiv.Perm.mul_apply]
    rw [e]
    exact ⟨fun h => by rw [h], fun h => σ.injective h⟩
  obtain ⟨v, hv⟩ := huniq (σ p) hst
  have h2 : σ (σ p) = p := by rw [← Equiv.Perm.mul_apply, hσ2, Equiv.Perm.one_apply]
  have h3 : ι v (ι v p) = p := by
    rw [hv]
    have e : ι v (σ p) = σ (ι v p) := by
      rw [← Equiv.Perm.mul_apply, ← hσ v, Equiv.Perm.mul_apply]
    rw [e, hv, h2]
  rw [← hv]
  exact hsq v h3

end CFSG.LocalAnalysis.GLTheoremA.H1017
