module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusNatSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp

theorem noAlt_exists_unit : ∃ ω : (Fq 2)ˣ, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  have h4 : Nat.card (Fq 2) = 4 := by
    have := GaloisField.card 2 2 (by norm_num)
    simpa using this
  have hu : Nat.card (Fq 2)ˣ = 3 := by
    rw [Nat.card_units, h4]
  have hnt : Nontrivial (Fq 2)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨ω, hω⟩ := exists_ne (1 : (Fq 2)ˣ)
  exact ⟨ω, hω, by rw [← hu]; exact pow_card_eq_one'⟩

theorem noAlt_card_support_le {N : ℕ} (σ : Equiv.Perm (Fin N)) (h3 : σ ^ 3 = 1)
    (F : Finset (Fin N)) (hF : ∀ i ∈ F, σ i = i) (hcard : N ≤ F.card + 5) :
    σ.support.card ≤ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) (σ := σ) (by simpa using h3)
  rw [Finset.card_compl, Fintype.card_fin] at h1
  have h2 : σ.support ⊆ Fᶜ := by
    intro i hi
    rw [Equiv.Perm.mem_support] at hi
    rw [Finset.mem_compl]
    exact fun hiF => hi (hF i hiF)
  have h3' := Finset.card_le_card h2
  rw [Finset.card_compl, Fintype.card_fin] at h3'
  have h4 : σ.support.card ≤ N := by
    simpa using Finset.card_le_univ σ.support
  unfold Nat.ModEq at h1
  omega

theorem noAlt_supported {N : ℕ} {E : Type*} [CommGroup E]
    (w : E →* Multiplicative (Fin N → ZMod 2)) (f : MulAut E) (σ : Equiv.Perm (Fin N))
    (h3 : f ^ 3 = 1) (hfree : ∀ e, f e = e → e = 1)
    (heq : ∀ e, Multiplicative.toAdd (w (f e)) = permActionTwo σ (Multiplicative.toAdd (w e)))
    (e : E) {i : Fin N} (hi : σ i = i) : Multiplicative.toAdd (w e) i = 0 := by
  have hff : f (f (f e)) = e := by
    have := congrArg (fun g : MulAut E => g e) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hfix : f (e * f e * f (f e)) = e * f e * f (f e) := by
    rw [map_mul, map_mul, hff]
    exact (mul_rotate _ _ _).symm
  have h1 := hfree _ hfix
  have h2 := congrArg (fun x => Multiplicative.toAdd (w x)) h1
  simp only [map_mul, toAdd_mul, map_one, toAdd_one] at h2
  have h3e := congrFun h2 i
  have hσ : σ⁻¹ i = i := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hi.symm
  rw [heq (f e), heq e] at h3e
  simp only [Pi.add_apply, permActionTwo, hσ, Pi.zero_apply] at h3e
  have key : ∀ x : ZMod 2, x + x + x = x := by decide
  rw [key] at h3e
  exact h3e

theorem noAlt_card_le {N : ℕ} {E : Type*} [Group E] [Finite E]
    (w : E →* Multiplicative (Fin N → ZMod 2)) (hw : Function.Injective w) (S : Finset (Fin N))
    (hS : ∀ (e : E) (i : Fin N), i ∉ S → Multiplicative.toAdd (w e) i = 0) :
    Nat.card E ≤ 2 ^ S.card := by
  let g : E → (↥S → ZMod 2) := fun e i => Multiplicative.toAdd (w e) i
  have hg : Function.Injective g := by
    intro e e' h
    apply hw
    apply Multiplicative.toAdd.injective
    funext i
    by_cases hi : i ∈ S
    · exact congrFun h ⟨i, hi⟩
    · rw [hS e i hi, hS e' i hi]
  calc Nat.card E ≤ Nat.card (↥S → ZMod 2) := Nat.card_le_card_of_injective g hg
    _ = 2 ^ S.card := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem noAlt_card_commV {V : Type} [CommGroup V] {D : Subgroup (MulAut V)}
    (hnat : IsNatSectionBy (slAct 2) D (commV D) ⊥) : Nat.card ↥(commV D) = 16 := by
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hnat
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have h1 : Nat.card ↥(commV D) = Nat.card (Multiplicative (Fin 2 → Fq 2)) :=
    Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)
  have h4 : Nat.card (Fq 2) = 4 := by
    have := GaloisField.card 2 2 (by norm_num)
    simpa using this
  rw [h1, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → Fq 2) ≃ _), Nat.card_fun,
    h4, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem arrowNat_eq_of_natSL (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {D X₁ : Subgroup (MulAut V)} (hnat : IsNatSectionBy (slAct n) D (commV D) ⊥) (hDX : D ≤ X₁)
    (harr : ArrowNat (yuHol D) (yuHol X₁)) : D = X₁ := by
  classical
  rcases harr with heq | ⟨a, b, φ, F, ⟨ρ⟩, ⟨ψ, -, -, hψk, hψe⟩, hF, hU, -, himg⟩
  · exact yuHol_inj heq
  exfalso
  have hnat0 := hnat
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  have hnatW : IsNatSectionWith (slAct n) θ (commV D) ⊥ := ⟨hinv, β, hβs, hβk, hβe⟩
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have h0 : pCore 2 ↥D = ⊥ := pCore_eq_bot_of_equiv θ (pCore_sl2_eq_bot hn)
  have e1 : alternatingGroup (Fin (2 * b + 1)) ≃* SLq n :=
    ρ.symm.trans ((yuTop' D hV h0).trans θ)
  have hm5 : 5 ≤ 2 * b + 1 := by
    by_contra hlt
    have hs : Group.IsSolvable (alternatingGroup (Fin (2 * b + 1))) :=
      alternatingGroup.isSolvable (by simp; omega)
    exact sl2_not_isSolvable hn
      (Group.isSolvable_of_surjective (f := e1.toMonoidHom) e1.surjective)
  obtain ⟨hb5, hn2⟩ := alt_sl2_iso hm5 hn e1
  subst hn2
  let yI : ↥(commV D) →* ↥(yuHol X₁) := (yuInc X₁).comp (Subgroup.inclusion (commV_mono hDX))
  have hyI : ∀ e : ↥(commV D), yI e ∈ shortU ↥(yuHol X₁) := by
    intro e
    have h1 : yuInc D e ∈ shortU ↥(yuHol D) := by
      rw [slLift_shortU hV hn hnatW]
      exact ⟨e, rfl⟩
    obtain ⟨u, hu, hue⟩ := hU ⟨yuInc D e, h1, rfl⟩
    have hu' : u = yI e := Subtype.ext hue
    rwa [← hu']
  let ψE : ↥(commV D) →* Multiplicative (Fin (2 * a + 1) → ZMod 2) :=
    ψ.comp (yI.codRestrict (shortU ↥(yuHol X₁)) hyI)
  have hψEi : Function.Injective ψE := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    have h1 : (⟨yI e, hyI e⟩ : ↥(shortU ↥(yuHol X₁))) ∈ ψ.ker := he
    rw [hψk, Subgroup.mem_subgroupOf] at h1
    have hc : yI e ∈ Subgroup.center ↥(yuHol X₁) := h1.2
    have hfix : (e : V) ∈ fixV D := by
      refine mem_fixV.mpr fun g hg => ?_
      have h2 := conj_yuInc X₁ (yuSec X₁ ⟨g, hDX hg⟩) ⟨e, commV_mono hDX e.2⟩
      have h3 : yuSec X₁ ⟨g, hDX hg⟩ * yuInc X₁ ⟨e, commV_mono hDX e.2⟩ *
          (yuSec X₁ ⟨g, hDX hg⟩)⁻¹ = yuInc X₁ ⟨e, commV_mono hDX e.2⟩ := by
        rw [mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_center_iff.mp hc _
      rw [h3] at h2
      exact (congrArg (fun y : ↥(commV X₁) => (y : V)) (yuInc_injective X₁ h2)).symm
    have h4 : (e : V) ∈ commV D ⊓ fixV D := ⟨e.2, hfix⟩
    rw [slLift_commV_inf_fixV hnatW, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  let σh : ↥D →* Equiv.Perm (Fin (2 * a + 1)) :=
    (alternatingGroup (Fin (2 * a + 1))).subtype.comp
      (φ.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 ↥(yuHol X₁))).comp
        ((yuSec X₁).comp (Subgroup.inclusion hDX))))
  have hstab : ∀ d : ↥D, ∀ i ∈ F, σh d i = i := by
    intro d i hi
    have hmem : φ (QuotientGroup.mk' (pCore 2 ↥(yuHol X₁))
        (yuSec X₁ (Subgroup.inclusion hDX d))) ∈ altStabilizer (2 * a + 1) F := by
      rw [← himg]
      exact ⟨_, ⟨_, Subgroup.mem_subgroupOf.mpr ⟨one_mem _, d.2⟩, rfl⟩, rfl⟩
    exact mem_altStabilizer'.mp hmem i hi
  have hequiv : ∀ (d : ↥D) (e : ↥(commV D)),
      Multiplicative.toAdd (ψE (resHom D d e)) =
        permActionTwo (σh d) (Multiplicative.toAdd (ψE e)) := by
    intro d e
    set l : ↥(yuHol X₁) := yuSec X₁ (Subgroup.inclusion hDX d) with hl
    have hc : l * yI e * l⁻¹ = yI (resHom D d e) :=
      conj_yuInc X₁ l ⟨e, commV_mono hDX e.2⟩
    have hu' : l * yI e * l⁻¹ ∈ shortU ↥(yuHol X₁) := by
      rw [hc]
      exact hyI _
    have key := hψe l (yI e) (hyI e) hu'
    have e2 : (⟨l * yI e * l⁻¹, hu'⟩ : ↥(shortU ↥(yuHol X₁))) =
        ⟨yI (resHom D d e), hyI _⟩ := Subtype.ext hc
    rw [e2] at key
    show Multiplicative.toAdd (ψ ⟨yI (resHom D d e), hyI _⟩) = _
    rw [key]
    rfl
  obtain ⟨ω, hω1, hω3⟩ := noAlt_exists_unit
  let d3 : ↥D := θ.symm (TwoThree.diagSL ω)
  have hθd3 : θ d3 = TwoThree.diagSL ω := θ.apply_symm_apply _
  have hd3 : d3 ^ 3 = 1 := by
    apply θ.injective
    rw [map_pow, hθd3, map_one]
    have : (TwoThree.diagSL ω) = TwoThree.diagHom ω := rfl
    rw [this, ← map_pow, hω3, map_one]
  have hf3 : (resHom D d3) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hfree : ∀ e : ↥(commV D), resHom D d3 e = e → e = 1 := by
    intro e he
    have h1 := hβe d3 e (hinv d3 d3.2 e e.2)
    have h2 : (⟨(d3 : MulAut V) (e : V), hinv d3 d3.2 e e.2⟩ : ↥(commV D)) = e := he
    rw [h2, hθd3] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simp only [slAct, toAdd_ofAdd, TwoThree.diagSL_mulVec] at h3
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h30 h31
    have hω1' : (ω : Fq 2) - 1 ≠ 0 := by
      intro h
      exact hω1 (Units.ext (sub_eq_zero.mp h))
    have hω1'' : ((ω⁻¹ : (Fq 2)ˣ) : Fq 2) - 1 ≠ 0 := by
      intro h
      exact hω1 (inv_eq_one.mp (Units.ext (sub_eq_zero.mp h)))
    have h40 : Multiplicative.toAdd (β e) 0 = 0 := by
      have : ((ω : Fq 2) - 1) * Multiplicative.toAdd (β e) 0 = 0 := by linear_combination -h30
      exact (mul_eq_zero.mp this).resolve_left hω1'
    have h41 : Multiplicative.toAdd (β e) 1 = 0 := by
      have : (((ω⁻¹ : (Fq 2)ˣ) : Fq 2) - 1) * Multiplicative.toAdd (β e) 1 = 0 := by
        linear_combination -h31
      exact (mul_eq_zero.mp this).resolve_left hω1''
    have h5 : β e = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact h40
      · exact h41
    exact hβi (h5.trans (map_one β).symm)
  have hsupp : ∀ (e : ↥(commV D)) (i : Fin (2 * a + 1)), σh d3 i = i →
      Multiplicative.toAdd (ψE e) i = 0 :=
    fun e i hi => noAlt_supported ψE (resHom D d3) (σh d3) hf3 hfree (hequiv d3) e hi
  have hσ3 : σh d3 ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hcardF : 2 * a + 1 ≤ F.card + 5 := by omega
  have hS : (σh d3).support.card ≤ 3 := noAlt_card_support_le (σh d3) hσ3 F (hstab d3) hcardF
  have hle := noAlt_card_le ψE hψEi (σh d3).support fun e i hi =>
    hsupp e i (by simpa [Equiv.Perm.mem_support] using hi)
  rw [noAlt_card_commV hnat0] at hle
  have h8 : 2 ^ (σh d3).support.card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hS
  omega

end Main

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
