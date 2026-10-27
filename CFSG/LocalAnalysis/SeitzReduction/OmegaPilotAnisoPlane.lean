module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Plane
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap Module

section ArtinSchreier

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem exists_sq_add_mul_eq_add {b c c' : K} (hb : b ≠ 0) (hc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hc' : ∀ s : K, s ^ 2 + b * s + c' ≠ 0) : ∃ s : K, s ^ 2 + b * s = c + c' := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let φ : K →+ K :=
    { toFun := fun s => s ^ 2 + b * s
      map_zero' := by ring
      map_add' := fun s t => by linear_combination (s * t) * h2 }
  have hφ : ∀ s, φ s = s ^ 2 + b * s := fun s => rfl
  have hker : (φ.ker : Set K) = {0, b} := by
    ext s
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff,
      hφ]
    constructor
    · intro h
      have : s * (s + b) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by linear_combination h0 - b * h2)
    · rintro (h | h) <;> rw [h]
      · ring
      · linear_combination b ^ 2 * h2
  have hcardker : Nat.card φ.ker = 2 := by
    have : Nat.card φ.ker = ((φ.ker : AddSubgroup K) : Set K).ncard := Nat.card_coe_set_eq _
    rw [this, hker, Set.ncard_pair hb.symm]
  have hidx : φ.range.index = 2 := by
    have h1 := AddSubgroup.card_mul_index φ.range
    have h3 := AddSubgroup.card_mul_index φ.ker
    rw [AddSubgroup.index_ker, hcardker] at h3
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos ((h1.trans h3.symm).trans (mul_comm 2 _))
  have hcH : c ∉ φ.range := by
    rintro ⟨s, hs⟩
    rw [hφ] at hs
    exact hc s (by linear_combination hs + c * h2)
  have hc'H : c' ∉ φ.range := by
    rintro ⟨s, hs⟩
    rw [hφ] at hs
    exact hc' s (by linear_combination hs + c' * h2)
  obtain ⟨s, hs⟩ := (AddSubgroup.add_mem_iff_of_index_two hidx).mpr (iff_of_false hcH hc'H)
  exact ⟨s, hs⟩

end ArtinSchreier

section Plane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite K] [CharP K 2]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.ClassicalGroups.Orthogonal in
theorem exists_anisoPair_of_codim_fix_le_two (hQ : (polarBilin Q).Nondegenerate)
    {y : V ≃ₗ[K] V} (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hyodd : Odd (orderOf y)) (hyq : y ^ Nat.card K ≠ y)
    (hF : finrank K V ≤ finrank K (fixSub y) + 2) {b c : K} (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    finrank K (fixSub y) + 2 = finrank K V ∧
      ∃ e e' : V, Q e = 1 ∧ Q e' = c ∧ polar Q e e' = b ∧
        ∀ x, polar Q x e = 0 → polar Q x e' = 0 → y x = x := by
  classical
  have := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Nat.card_eq_fintype_card] at hyq
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyq (one_pow _)
  have hm : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  set π := avgOp y (orderOf y) with hπ
  set E := LinearMap.ker π with hE
  have hπF : ∀ x, y (π x) = π x := fun x => apply_avgOp hm x
  have hπw : ∀ w, y w = w → π w = w := fun w hw => avgOp_apply_of_fix hyodd hw
  have hEF : ∀ x ∈ E, ∀ w, y w = w → polar Q x w = 0 := by
    intro x hx w hw
    rw [← polar_avgOp_left hyO hyodd x hw, LinearMap.mem_ker.mp hx, polar_zero_left]
  have hsubE : ∀ x, x - π x ∈ E := fun x => by
    rw [LinearMap.mem_ker, map_sub, hπw _ (hπF x), sub_self]
  have hEy : ∀ x ∈ E, y x ∈ E := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hπ, avgOp_apply_apply hm, ← hπ, hx]
  have hFE : fixSub y ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwF, hwE⟩ := Submodule.mem_inf.mp hw
    rw [Submodule.mem_bot, ← hπw w hwF]
    exact LinearMap.mem_ker.mp hwE
  have hFE' : fixSub y ⊔ E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = π x + (x - π x) := by abel
    rw [hx]
    exact Submodule.add_mem_sup (hπF x) (hsubE x)
  have hdim : finrank K (fixSub y) + finrank K E = finrank K V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSub y) E
    rw [hFE, hFE', finrank_bot, add_zero, finrank_top] at h
    exact h.symm
  have hE2 : finrank K E ≤ 2 := by omega
  have hEnd : ∀ x ∈ E, (∀ x' ∈ E, polar Q x x' = 0) → x = 0 := by
    intro x hxE hx
    apply eq_zero_of_polar_eq_zero hQ
    intro z
    have hz : z = π z + (z - π z) := by abel
    rw [hz, polar_add_right, hx _ (hsubE z), hEF x hxE _ (hπF z), add_zero]
  have hEne : Nontrivial E := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hy1
    refine LinearEquiv.ext fun x => ?_
    have h0 : (⟨x - π x, hsubE x⟩ : E) = 0 := Subsingleton.elim _ _
    have hx : x = π x := sub_eq_zero.mp (congrArg Subtype.val h0)
    change y x = x
    rw [hx, hπF]
  have hpow : ∀ k : ℕ, (∀ w ∈ E, (y ^ k) w = w) → y ^ k = 1 := by
    intro k hk
    refine LinearEquiv.ext fun x => ?_
    have hx : x = π x + (x - π x) := by abel
    change (y ^ k) x = x
    rw [hx, map_add, hk _ (hsubE x), pow_apply_of_mem_fixSub (hπF x) k]
  have hanis : ∀ u ∈ E, Q u = 0 → u = 0 := by
    intro u huE hQu
    by_contra hu0
    obtain ⟨v', hv'E, hv'⟩ : ∃ v' ∈ E, polar Q u v' ≠ 0 := by
      by_contra! h
      exact hu0 (hEnd u huE h)
    obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, v₁ = (polar Q u v')⁻¹ • v' := ⟨_, rfl⟩
    have hv₁E : v₁ ∈ E := hv₁ ▸ E.smul_mem _ hv'E
    have huv₁ : polar Q u v₁ = 1 := by
      rw [hv₁, polar_smul_right_eq, inv_mul_cancel₀ hv']
    obtain ⟨v, hvdef⟩ : ∃ v : V, v = v₁ + Q v₁ • u := ⟨_, rfl⟩
    have hvE : v ∈ E := hvdef ▸ E.add_mem hv₁E (E.smul_mem _ huE)
    have huv : polar Q u v = 1 := by
      rw [hvdef, polar_add_right, huv₁, polar_smul_right_eq, polar_self_eq_zero hQu, mul_zero,
        add_zero]
    have hvu : polar Q v u = 1 := by rw [polar_comm, huv]
    have hQv : Q v = 0 := by
      rw [hvdef, QuadraticMap.map_add Q, map_smul_eq_sq, hQu, polar_smul_right_eq,
        polar_comm Q v₁ u, huv₁]
      linear_combination Q v₁ * h2
    have hvv : polar Q v v = 0 := polar_self_eq_zero hQv
    have huu : polar Q u u = 0 := polar_self_eq_zero hQu
    have hdecomp : ∀ w ∈ E, w = polar Q w v • u + polar Q w u • v := by
      intro w hwE
      by_contra hne
      set w' := w - (polar Q w v • u + polar Q w u • v) with hw'
      have hw'0 : w' ≠ 0 := fun h => hne (sub_eq_zero.mp h)
      have hw'E : w' ∈ E := E.sub_mem hwE (E.add_mem (E.smul_mem _ huE) (E.smul_mem _ hvE))
      have hw'u : polar Q w' u = 0 := by
        rw [hw', polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, huu, hvu]
        ring
      have hw'v : polar Q w' v = 0 := by
        rw [hw', polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, huv, hvv]
        ring
      have hli : LinearIndependent K ![u, v, w'] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
        have h1 := congrArg (fun z => polar Q z u) hg
        have h3 := congrArg (fun z => polar Q z v) hg
        simp only [polar_add_left, polar_smul_left_eq, huu, hvu, hw'u, polar_zero_left] at h1
        simp only [polar_add_left, polar_smul_left_eq, huv, hvv, hw'v, polar_zero_left] at h3
        have hg1 : g 1 = 0 := by linear_combination h1
        have hg0 : g 0 = 0 := by linear_combination h3
        rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add, smul_eq_zero] at hg
        have hg2 : g 2 = 0 := hg.resolve_right hw'0
        intro i
        fin_cases i
        · exact hg0
        · exact hg1
        · exact hg2
      have h3 := finrank_span_eq_card hli
      have hle : Submodule.span K (Set.range ![u, v, w']) ≤ E := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact huE
        · exact hvE
        · exact hw'E
      have h4 := Submodule.finrank_mono hle
      rw [h3, Fintype.card_fin] at h4
      omega
    have hyu := hdecomp _ (hEy u huE)
    have hyv := hdecomp _ (hEy v hvE)
    set α := polar Q (y u) v with hα
    set β := polar Q (y u) u with hβ
    set γ := polar Q (y v) v with hγ
    set δ := polar Q (y v) u with hδ
    have hQyu : α * β = 0 := by
      have h : Q (y u) = 0 := by rw [map_of_mem hyO, hQu]
      rw [hyu, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, hQv,
        polar_smul_left_eq, polar_smul_right_eq, huv] at h
      linear_combination h
    have hQyv : γ * δ = 0 := by
      have h : Q (y v) = 0 := by rw [map_of_mem hyO, hQv]
      rw [hyv, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, hQv,
        polar_smul_left_eq, polar_smul_right_eq, huv] at h
      linear_combination h
    have hByuv : α * δ + β * γ = 1 := by
      have h : polar Q (y u) (y v) = 1 := by rw [polar_map_of_mem hyO, huv]
      rw [hyu, hyv] at h
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, huu,
        huv, hvu, hvv] at h
      linear_combination h
    rcases mul_eq_zero.mp hQyu with hα0 | hβ0
    ·
      have hβγ : β * γ = 1 := by rw [hα0, zero_mul, zero_add] at hByuv; exact hByuv
      have hδ0 : δ = 0 := (mul_eq_zero.mp hQyv).resolve_left (right_ne_zero_of_mul_eq_one hβγ)
      have hyy : y ^ 2 = 1 := by
        apply hpow 2
        intro w hw
        have h1 : (y ^ 2) u = u := by
          rw [pow_two, LinearEquiv.mul_apply, hyu, hα0, zero_smul, zero_add, map_smul, hyv,
            hδ0, zero_smul, add_zero, smul_smul, hβγ, one_smul]
        have h3 : (y ^ 2) v = v := by
          rw [pow_two, LinearEquiv.mul_apply, hyv, hδ0, zero_smul, add_zero, map_smul, hyu, hα0,
            zero_smul, zero_add, smul_smul, mul_comm, hβγ, one_smul]
        rw [hdecomp w hw, map_add, map_smul, map_smul, h1, h3]
      apply hy1
      have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hyy
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · rw [h1] at hyodd
        exact absurd hyodd (by decide)
    ·
      have hαδ : α * δ = 1 := by rw [hβ0, zero_mul, add_zero] at hByuv; exact hByuv
      have hγ0 : γ = 0 := (mul_eq_zero.mp hQyv).resolve_right (right_ne_zero_of_mul_eq_one hαδ)
      have hα1 : α ≠ 0 := left_ne_zero_of_mul_eq_one hαδ
      have hδ1 : δ ≠ 0 := right_ne_zero_of_mul_eq_one hαδ
      have hyu' : y u = α • u := by rw [hyu, hβ0, zero_smul, add_zero]
      have hyv' : y v = δ • v := by rw [hyv, hγ0, zero_smul, zero_add]
      have hku : ∀ k : ℕ, (y ^ k) u = α ^ k • u := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hyu', smul_smul, pow_succ]
      have hkv : ∀ k : ℕ, (y ^ k) v = δ ^ k • v := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hyv', smul_smul, pow_succ]
      have hyq1 : y ^ (Fintype.card K - 1) = 1 := by
        apply hpow
        intro w hw
        rw [hdecomp w hw, map_add, map_smul, map_smul, hku, hkv,
          FiniteField.pow_card_sub_one_eq_one α hα1, FiniteField.pow_card_sub_one_eq_one δ hδ1,
          one_smul, one_smul]
      apply hyq
      have h1 : 1 < Fintype.card K := Fintype.one_lt_card
      rw [show Fintype.card K = (Fintype.card K - 1) + 1 by omega, pow_succ, hyq1, one_mul]
  obtain ⟨e₁, he₁⟩ := exists_ne (0 : E)
  have he₁0 : (e₁ : V) ≠ 0 := fun h => he₁ (Subtype.ext h)
  have hQe₁ : Q e₁ ≠ 0 := fun h => he₁0 (hanis _ e₁.2 h)
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (Q e₁)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hQe₁ hr
  obtain ⟨e, hedef⟩ : ∃ e : V, e = r⁻¹ • (e₁ : V) := ⟨_, rfl⟩
  have heE : e ∈ E := hedef ▸ E.smul_mem _ e₁.2
  have hQe : Q e = 1 := by
    rw [hedef, map_smul_eq_sq, hr]
    field_simp
  have he0 : e ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hQe
    exact zero_ne_one hQe
  have hee : polar Q e e = 0 := by
    rw [polar_self_eq_two_mul, h2, zero_mul]
  obtain ⟨w, hwE, hw⟩ : ∃ w ∈ E, polar Q e w ≠ 0 := by
    by_contra! h
    exact he0 (hEnd e heE h)
  obtain ⟨e₂, he₂def⟩ : ∃ e₂ : V, e₂ = (b / polar Q e w) • w := ⟨_, rfl⟩
  have he₂E : e₂ ∈ E := he₂def ▸ E.smul_mem _ hwE
  have hee₂ : polar Q e e₂ = b := by
    rw [he₂def, polar_smul_right_eq]
    field_simp
  have hirr₂ : ∀ s : K, s ^ 2 + b * s + Q e₂ ≠ 0 := by
    intro s hs
    have hmem : s • e + e₂ ∈ E := E.add_mem (E.smul_mem _ heE) he₂E
    have hQ0 : Q (s • e + e₂) = 0 := by
      rw [QuadraticMap.map_add Q, map_smul_eq_sq, hQe, polar_smul_left_eq, hee₂]
      linear_combination hs
    have h0 := congrArg (polar Q e) (hanis _ hmem hQ0)
    rw [polar_add_right, polar_smul_right_eq, hee, mul_zero, zero_add, hee₂,
      polar_zero_right] at h0
    exact hb h0
  obtain ⟨s, hs⟩ := exists_sq_add_mul_eq_add hb hirr₂ hirr
  obtain ⟨e', he'def⟩ : ∃ e' : V, e' = e₂ + s • e := ⟨_, rfl⟩
  have he'E : e' ∈ E := he'def ▸ E.add_mem he₂E (E.smul_mem _ heE)
  have hQe' : Q e' = c := by
    rw [he'def, QuadraticMap.map_add Q, map_smul_eq_sq, hQe, polar_smul_right_eq,
      polar_comm Q e₂ e, hee₂]
    linear_combination hs + Q e₂ * h2
  have hee' : polar Q e e' = b := by
    rw [he'def, polar_add_right, polar_smul_right_eq, hee, mul_zero, add_zero, hee₂]
  have hli : LinearIndependent K ![e, e'] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have h1 := congrArg (polar Q e) hαβ
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hee, hee',
      polar_zero_right] at h1
    have hβ : β = 0 := by
      have : β * b = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right hb
    rw [hβ, zero_smul, add_zero, smul_eq_zero] at hαβ
    exact ⟨hαβ.resolve_right he0, hβ⟩
  set S := Submodule.span K (Set.range ![e, e']) with hS
  have hSE : S ≤ E := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact heE
    · exact he'E
  have hS2 : finrank K S = 2 := by rw [hS, finrank_span_eq_card hli, Fintype.card_fin]
  have hSeq : S = E := Submodule.eq_of_le_of_finrank_le hSE (by omega)
  have hE2' : finrank K E = 2 := hSeq ▸ hS2
  refine ⟨by omega, e, e', hQe, hQe', hee', fun x hxe hxe' => ?_⟩
  have hπe : polar Q (π x) e = 0 := by rw [polar_comm]; exact hEF e heE _ (hπF x)
  have hπe' : polar Q (π x) e' = 0 := by rw [polar_comm]; exact hEF e' he'E _ (hπF x)
  have hx0 : x - π x = 0 := by
    apply hEnd _ (hsubE x)
    intro z hz
    rw [← hSeq, hS] at hz
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hz
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      polar_add_right, polar_smul_right_eq, polar_sub_left, hxe, hxe', hπe, hπe']
    ring
  have hx : x = π x := sub_eq_zero.mp hx0
  rw [hx]
  exact hπF x

end Plane

end CFSG.SeitzReduction.OmegaPilot
