module

public import CFSG.LargeExtraspecial.AS35QCoCent
public import CFSG.LargeExtraspecial.AS35QCoSp6
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Co2Smith
open scoped commutatorElement

section Conj

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem isTypeA_conj {t g : V ≃ₗ[ZMod 2] V} {l : ℕ} (ht : IsTypeA q t l)
    (hg : ∀ v, q (g v) = q v) : IsTypeA q (g * t * g⁻¹) l := by
  have hgi : ∀ v, q (g⁻¹ v) = q v := fun v => by rw [← hg (g⁻¹ v), mul_inv_apply]
  refine ⟨fun v => ?_, fun h => ht.2.1 ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, ht.1, hgi]
  · calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht.2.2.1]; group
  · rw [commSpace_conj, finrank_map_equiv, ht.2.2.2.1]
  · intro v hv
    rw [commSpace_conj] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [LinearEquiv.coe_coe, hg]
    exact ht.2.2.2.2 w hw

end Conj

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_conj_eq (hst : S.Asc512Standing) (θ : S.LbarAsc ≃* Sp62) {m : S.O}
    (hm : m ∈ S.Mbar) : ∃ l ∈ S.LbarAsc, ∀ a ∈ S.LbarAsc, m * a * m⁻¹ = l * a * l⁻¹ := by
  have hmi : m⁻¹ ∈ S.Mbar := S.Mbar.inv_mem hm
  let α : S.LbarAsc ≃* S.LbarAsc :=
    { toFun := fun a => ⟨m * a * m⁻¹, hst.normal m hm a a.2⟩
      invFun := fun a => ⟨m⁻¹ * a * m⁻¹⁻¹, hst.normal m⁻¹ hmi a a.2⟩
      left_inv := fun a => Subtype.ext (by simp only; group)
      right_inv := fun a => Subtype.ext (by simp only; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_statedSp
    ((θ.symm.trans α).trans θ)
  refine ⟨(θ.symm g : S.O), (θ.symm g).2, fun a ha => ?_⟩
  have h := congrArg (fun γ : MulAut Sp62 => θ.symm (γ (θ ⟨a, ha⟩))) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul,
    map_inv] at h
  exact congrArg Subtype.val h

theorem eq_of_conj_eq (hZ : center S.LbarAsc = ⊥) {l l' : S.O} (hl : l ∈ S.LbarAsc)
    (hl' : l' ∈ S.LbarAsc) (h : ∀ a ∈ S.LbarAsc, l * a * l⁻¹ = l' * a * l'⁻¹) : l = l' := by
  have hc : (⟨l⁻¹ * l', S.LbarAsc.mul_mem (S.LbarAsc.inv_mem hl) hl'⟩ : S.LbarAsc) ∈
      center S.LbarAsc := by
    rw [mem_center_iff]
    intro b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have e := h b b.2
    calc (b : S.O) * (l⁻¹ * l') = l⁻¹ * (l * b * l⁻¹) * l' := by group
      _ = l⁻¹ * (l' * b * l'⁻¹) * l' := by rw [e]
      _ = l⁻¹ * l' * b := by group
  rw [hZ, mem_bot] at hc
  have e : l⁻¹ * l' = 1 := congrArg Subtype.val hc
  exact (inv_mul_eq_one.mp e)

theorem exists_retraction (hst : S.Asc512Standing) (θ : S.LbarAsc ≃* Sp62)
    (hZ : center S.LbarAsc = ⊥) :
    ∃ Φ : S.Mbar →* Sp62, ∀ (l : S.O) (hl : l ∈ S.LbarAsc),
      Φ ⟨l, lbar_le_mbar S hl⟩ = θ ⟨l, hl⟩ := by
  choose! L hLmem hLconj using fun (m : S.O) (hm : m ∈ S.Mbar) => exists_conj_eq S hst θ hm
  have huniq : ∀ m ∈ S.Mbar, ∀ l ∈ S.LbarAsc,
      (∀ a ∈ S.LbarAsc, m * a * m⁻¹ = l * a * l⁻¹) → L m = l := fun m hm l hl h =>
    eq_of_conj_eq S hZ (hLmem m hm) hl fun a ha => (hLconj m hm a ha).symm.trans (h a ha)
  have hmul : ∀ m₁ ∈ S.Mbar, ∀ m₂ ∈ S.Mbar, L (m₁ * m₂) = L m₁ * L m₂ := by
    intro m₁ h₁ m₂ h₂
    refine huniq _ (S.Mbar.mul_mem h₁ h₂) _ (S.LbarAsc.mul_mem (hLmem m₁ h₁) (hLmem m₂ h₂))
      fun a ha => ?_
    have hb : L m₂ * a * (L m₂)⁻¹ ∈ S.LbarAsc :=
      S.LbarAsc.mul_mem (S.LbarAsc.mul_mem (hLmem m₂ h₂) ha) (S.LbarAsc.inv_mem (hLmem m₂ h₂))
    calc m₁ * m₂ * a * (m₁ * m₂)⁻¹ = m₁ * (m₂ * a * m₂⁻¹) * m₁⁻¹ := by group
      _ = m₁ * (L m₂ * a * (L m₂)⁻¹) * m₁⁻¹ := by rw [hLconj m₂ h₂ a ha]
      _ = L m₁ * (L m₂ * a * (L m₂)⁻¹) * (L m₁)⁻¹ := hLconj m₁ h₁ _ hb
      _ = L m₁ * L m₂ * a * (L m₁ * L m₂)⁻¹ := by group
  have hself : ∀ l ∈ S.LbarAsc, L l = l := fun l hl =>
    huniq l (lbar_le_mbar S hl) l hl fun _ _ => rfl
  refine ⟨{ toFun := fun m => θ ⟨L m, hLmem m m.2⟩
            map_one' := ?_
            map_mul' := fun m₁ m₂ => ?_ }, fun l hl => ?_⟩
  · have e : L 1 = 1 := hself 1 (one_mem _)
    rw [← map_one θ]
    congr 1
    exact Subtype.ext e
  · rw [← map_mul]
    congr 1
    exact Subtype.ext (hmul m₁ m₁.2 m₂ m₂.2)
  · show θ ⟨L l, _⟩ = θ ⟨l, hl⟩
    congr 1
    exact Subtype.ext (hself l hl)

@[expose] def fixL : Submodule (ZMod 2) S.Qt where
  carrier := {v | ∀ g ∈ S.LbarAsc, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  add_mem' := fun ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg]

theorem mem_fixL {v : S.Qt} : v ∈ fixL S ↔ ∀ g ∈ S.LbarAsc, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

theorem fixL_invariant (hst : S.Asc512Standing) {m : S.O} (hm : m ∈ S.Mbar) {w : S.Qt}
    (hw : w ∈ fixL S) : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ fixL S := by
  intro g hg
  have hg' : m⁻¹ * g * m⁻¹⁻¹ ∈ S.LbarAsc := hst.normal m⁻¹ (S.Mbar.inv_mem hm) g hg
  have e := hw _ hg'
  rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply] at e
  calc (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹
        ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) := (mul_inv_apply _ _).symm
    _ = (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by rw [e]

theorem natCard_fixL_le (hsp : S.Asc512SpSix) : Nat.card (fixL S) ≤ 4 := by
  have := finite_Qt S
  obtain ⟨x, hxL, hx7, hx1⟩ := exists_seven S hsp
  obtain ⟨hF2, -, -⟩ := (seven_hyp S hsp.1 hx7 hx1).finrank_fixSpace
  have hle : fixL S ≤ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun v hv =>
    mem_fixSpace.mpr (hv x hxL)
  have h := Submodule.finrank_mono hle
  rw [hF2] at h
  rw [natCard_submodule]
  calc 2 ^ finrank (ZMod 2) (fixL S) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
    _ = 4 := by norm_num

theorem exists_dbar (hsp : S.Asc512SpSix) :
    ∃ (g : G) (_ : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M),
      S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := by
  obtain ⟨x, hxL, -, hx1⟩ := exists_seven S hsp
  obtain ⟨a, haD⟩ : S.DbarAsc.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : S.LbarAsc = ⊥ := by
      change closure S.DbarAsc = ⊥
      rw [hne, Subgroup.closure_empty]
    rw [hbot, mem_bot] at hxL
    exact hx1 hxL
  obtain ⟨t, htD, htM, rfl⟩ := haD
  obtain ⟨g, hgt, -, -⟩ := htD.1
  subst hgt
  exact ⟨g, htD, htM, ⟨_, htD, htM, rfl⟩⟩

theorem pbar_facts {P : Subgroup S.O} {τ : S.O} (hext : CFSG.IsExtraspecialPGroup 2 P)
    (hcent : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = τ) :
    (∀ p ∈ P, p * τ = τ * p) ∧ ∀ y ∈ P, y ≠ 1 → y ≠ τ → ∃ p ∈ P, p * y * p⁻¹ = τ * y := by
  have hτc : ∀ p ∈ P, p * τ = τ * p := by
    obtain ⟨c, hc1⟩ : ∃ c : center P, c ≠ 1 := by
      by_contra h
      push Not at h
      have h1 : Nat.card (center P) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
      rw [hext.2.2.2] at h1
      exact absurd h1 (by norm_num)
    have hcc : ∀ yy ∈ P, ((c : P) : S.O) * yy = yy * c := fun yy hyy =>
      congrArg Subtype.val (mem_center_iff.mp c.2 ⟨yy, hyy⟩).symm
    rcases hcent _ (c : P).2 hcc with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hc1
    · intro p hp
      rw [← h]
      exact (hcc p hp).symm
  refine ⟨hτc, fun y hyP hy1 hyτ => ?_⟩
  have hnc : ¬ ∀ yy ∈ P, y * yy = yy * y := fun h => by
    rcases hcent y hyP h with h' | h'
    · exact hy1 h'
    · exact hyτ h'
  push Not at hnc
  obtain ⟨p, hpP, hpne⟩ := hnc
  refine ⟨p, hpP, ?_⟩
  have hmem : ⁅(⟨p, hpP⟩ : P), ⟨y, hyP⟩⁆ ∈ center P := by
    rw [← hext.2.1, _root_.commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hval : ((⁅(⟨p, hpP⟩ : P), ⟨y, hyP⟩⁆ : P) : S.O) = p * y * p⁻¹ * y⁻¹ := by
    rw [commutatorElement_def]
    rfl
  have hcomm : ∀ yy ∈ P, (p * y * p⁻¹ * y⁻¹) * yy = yy * (p * y * p⁻¹ * y⁻¹) := by
    intro yy hyy
    rw [← hval]
    exact congrArg Subtype.val (mem_center_iff.mp hmem ⟨yy, hyy⟩).symm
  have hPmem : p * y * p⁻¹ * y⁻¹ ∈ P := hval ▸ (⁅(⟨p, hpP⟩ : P), ⟨y, hyP⟩⁆ : P).2
  rcases hcent _ hPmem hcomm with h | h
  · exfalso
    apply hpne
    calc y * p = (p * y * p⁻¹ * y⁻¹)⁻¹ * (p * y) := by group
      _ = p * y := by rw [h, inv_one, one_mul]
  · calc p * y * p⁻¹ = (p * y * p⁻¹ * y⁻¹) * y := by group
      _ = τ * y := by rw [h]

theorem exists_config (hS : S.SixHyp) (hst : S.Asc512Standing) (hsp : S.Asc512SpSix)
    (hSym : S14.Asc512SymStmt) (hP : S14.Asc512PbarStmt) {f₀ : S.Qt} (hf₀ : S.q f₀ = 1)
    (hfix : f₀ ∈ fixL S) :
    ∃ (τ y p : S.O) (Y : Subgroup S.O), τ ∈ S.LbarAsc ∧ IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
      τ ∈ Y ∧ y ∈ Y ∧ y ≠ 1 ∧ y ≠ τ ∧ y ∈ S.Mbar ∧ y * τ = τ * y ∧ p ∈ S.Mbar ∧
      p * τ = τ * p ∧ p * y * p⁻¹ = τ * y ∧ Nat.card Y ≤ 8 ∧
      ∀ c ∈ S.Mbar, c * τ = τ * c → ∀ w ∈ Y, c * w * c⁻¹ ∈ Y := by
  obtain ⟨g, htD, htM, hτD⟩ := exists_dbar S hsp
  have hτL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure hτD
  have hτA := isTypeA_of_mem_dbar S hS hτD
  obtain ⟨Y, hYP, hτY, hYnot, hYcard, hYnorm⟩ := hSym G S hS g htD htM (fixL S)
    (fun m hm w hw => fixL_invariant S hst hm hw)
    (fun w hw => mem_fixSpace.mpr (hw _ hτL))
    (fun hle => by
      have h0 := hτA.2.2.2.2 f₀ (hle hfix)
      rw [hf₀] at h0
      exact one_ne_zero h0)
  obtain ⟨-, hext, -, hcent, -, -, -⟩ := hP G S hS g htD htM
  generalize S.ρ ⟨g * S.z * g⁻¹, htM⟩ = τ at hτD hτL hτA hτY hYnot hYnorm hext hcent
  obtain ⟨hτc, hconjP⟩ := pbar_facts S hext hcent
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  obtain ⟨y, hyY, hyz⟩ : ∃ y ∈ Y, y ∉ zpowers τ := by
    by_contra h
    push Not at h
    exact hYnot h
  have hy1 : y ≠ 1 := fun h => hyz (h ▸ one_mem _)
  have hyτ : y ≠ τ := fun h => hyz (h ▸ mem_zpowers τ)
  have hyP : y ∈ S.PbarAsc g := hYP hyY
  obtain ⟨p, hpP, hpy⟩ := hconjP y hyP hy1 hyτ
  have h4 := natCard_fixL_le S hsp
  exact ⟨τ, y, p, Y, hτL, hτA, hτY, hyY, hy1, hyτ, hPM hyP, hτc y hyP, hPM hpP, hτc p hpP, hpy,
    by omega, hYnorm⟩

theorem orderOf_mem_of_typeA (θ : S.LbarAsc ≃* Sp62) {τ : S.O} (hτL : τ ∈ S.LbarAsc)
    (hτA : IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (k : Sp62) :
    orderOf (θ ⟨τ, hτL⟩ * (k * θ ⟨τ, hτL⟩ * k⁻¹)) ∈ ({1, 2, 3, 4} : Set ℕ) := by
  have := finite_Qt S
  obtain ⟨l, rfl⟩ := θ.surjective k
  have e : θ ⟨τ, hτL⟩ * (θ l * θ ⟨τ, hτL⟩ * (θ l)⁻¹) = θ (⟨τ, hτL⟩ * (l * ⟨τ, hτL⟩ * l⁻¹)) := by
    simp only [map_mul, map_inv]
  rw [e, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  have h37 := (aschbacher_3_7 S.q_nondegenerate hτA (isTypeA_conj hτA (isom S (l : S.O)))).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h37
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h37

theorem ncard_conj_le (θ : S.LbarAsc ≃* Sp62) (Φ : S.Mbar →* Sp62)
    (hΦ : ∀ (l : S.O) (hl : l ∈ S.LbarAsc), Φ ⟨l, lbar_le_mbar S hl⟩ = θ ⟨l, hl⟩)
    {τ y : S.O} (hτL : τ ∈ S.LbarAsc) (hτ1 : τ ≠ 1) {Y : Subgroup S.O} (hτY : τ ∈ Y)
    (hyY : y ∈ Y) (hy1 : y ≠ 1) (hyτ : y ≠ τ) (hyM : y ∈ S.Mbar) (hYcard : Nat.card Y ≤ 8)
    (hYnorm : ∀ c ∈ S.Mbar, c * τ = τ * c → ∀ w ∈ Y, c * w * c⁻¹ ∈ Y) :
    ((fun h : Sp62 => h * Φ ⟨y, hyM⟩ * h⁻¹) ''
      (centralizer ({θ ⟨τ, hτL⟩} : Set Sp62) : Set Sp62)).ncard ≤ 6 := by
  classical
  have := finite_lin S
  obtain ⟨Yset, hYset⟩ : ∃ T : Set S.O, T = (Y : Set S.O) \ {1, τ} := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : S.O → Sp62, ∀ (w : S.O) (hw : w ∈ S.Mbar), F w = Φ ⟨w, hw⟩ :=
    ⟨fun w => if hw : w ∈ S.Mbar then Φ ⟨w, hw⟩ else 1, fun w hw => by
      simp only [hw, ↓reduceDIte]⟩
  have hsub : (fun h : Sp62 => h * Φ ⟨y, hyM⟩ * h⁻¹) ''
      (centralizer ({θ ⟨τ, hτL⟩} : Set Sp62) : Set Sp62) ⊆ F '' Yset := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨l, rfl⟩ := θ.surjective k
    have hlM := lbar_le_mbar S l.2
    have hlτ : (l : S.O) * τ = τ * l := by
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hk
      have e : θ (l * ⟨τ, hτL⟩) = θ (⟨τ, hτL⟩ * l) := by
        simp only [map_mul]
        exact hk
      exact congrArg Subtype.val (θ.injective e)
    obtain ⟨w, hw⟩ : ∃ w : S.Mbar, w = ⟨l, hlM⟩ * ⟨y, hyM⟩ * (⟨l, hlM⟩ : S.Mbar)⁻¹ := ⟨_, rfl⟩
    refine ⟨(w : S.O), ?_, ?_⟩
    · rw [hYset, hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine Set.mem_sdiff_of_mem (hYnorm _ hlM hlτ y hyY) fun h => ?_
      rcases Set.mem_insert_iff.mp h with h | h
      · exact hy1 (mul_left_cancel ((mul_inv_eq_one.mp h).trans (mul_one _).symm))
      · rw [Set.mem_singleton_iff] at h
        exact hyτ (mul_left_cancel ((mul_inv_eq_iff_eq_mul.mp h).trans hlτ.symm))
    · have hFw : F (w : S.O) = Φ w := hF (w : S.O) w.2
      rw [hFw, hw]
      simp only [map_mul, map_inv, hΦ _ l.2, Subtype.coe_eta]
  have hfinO : Finite S.O := Subtype.finite
  have hYfin : Yset.Finite := Set.toFinite Yset
  have hYn : Yset.ncard ≤ 6 := by
    have h1 : ({1, τ} : Set S.O) ⊆ Y :=
      Set.insert_subset_iff.mpr ⟨one_mem Y, Set.singleton_subset_iff.mpr hτY⟩
    have hc : Nat.card Y = (Y : Set S.O).ncard := Nat.card_coe_set_eq (Y : Set S.O)
    have hd := Set.ncard_sdiff h1 ((Set.finite_singleton τ).insert 1)
    have hp : ({1, τ} : Set S.O).ncard = 2 := Set.ncard_pair hτ1.symm
    rw [hYset, hd, hp]
    omega
  exact (Set.ncard_le_ncard hsub (hYfin.image F)).trans ((Set.ncard_image_le hYfin).trans hYn)

theorem false_of_fixL (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hsp : S.Asc512SpSix) (hSym : S14.Asc512SymStmt) (hP : S14.Asc512PbarStmt) {f₀ : S.Qt}
    (hf₀ : S.q f₀ = 1) (hfix : f₀ ∈ fixL S) : False := by
  obtain ⟨θ⟩ := exists_lbar_equiv S hS hst hsp
  obtain ⟨Φ, hΦ⟩ := exists_retraction S hst θ (center_lbar_eq_bot S hS hst hsp)
  obtain ⟨τ, y, p, Y, hτL, hτA, hτY, hyY, hy1, hyτ, hyM, hyτc, hpM, hpτ, hpy, hYcard, hYnorm⟩ :=
    exists_config S hS hst hsp hSym hP hf₀ hfix
  have hττ : τ * τ = 1 := Subtype.ext hτA.2.2.1
  have hτ1 : τ ≠ 1 := fun h => hτA.2.1 (congrArg Subtype.val h)
  have hτM := lbar_le_mbar S hτL
  have hsmall := ncard_conj_le S θ Φ hΦ hτL hτ1 hτY hyY hy1 hyτ hyM hYcard hYnorm
  have hprod := orderOf_mem_of_typeA S θ hτL hτA
  have hΦτ : Φ ⟨τ, hτM⟩ = θ ⟨τ, hτL⟩ := hΦ τ hτL
  generalize hθτ : θ ⟨τ, hτL⟩ = τ' at hsmall hprod hΦτ
  generalize hy' : Φ ⟨y, hyM⟩ = y' at hsmall
  generalize hh₀ : Φ ⟨p, hpM⟩ = h₀
  have hcomm' : ∀ (a b : S.O) (ha : a ∈ S.Mbar) (hb : b ∈ S.Mbar), a * b = b * a →
      Φ ⟨a, ha⟩ * Φ ⟨b, hb⟩ = Φ ⟨b, hb⟩ * Φ ⟨a, ha⟩ := fun a b ha hb h => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  have hτ'τ' : τ' * τ' = 1 := by
    rw [← hθτ, ← map_mul, ← map_one θ]
    congr 1
    exact Subtype.ext hττ
  have hτ'1 : τ' ≠ 1 := fun h => hτ1 (by
    have h' : θ ⟨τ, hτL⟩ = θ 1 := hθτ.trans (h.trans (map_one θ).symm)
    exact congrArg Subtype.val (θ.injective h'))
  have hy'τ' : y' * τ' = τ' * y' := by
    rw [← hy', ← hΦτ]
    exact hcomm' _ _ hyM hτM hyτc
  have hh₀τ' : h₀ * τ' = τ' * h₀ := by
    rw [← hh₀, ← hΦτ]
    exact hcomm' _ _ hpM hτM hpτ
  have hconj : h₀ * y' * h₀⁻¹ = τ' * y' := by
    have e : Φ (⟨p, hpM⟩ * ⟨y, hyM⟩ * (⟨p, hpM⟩ : S.Mbar)⁻¹) = Φ (⟨τ, hτM⟩ * ⟨y, hyM⟩) := by
      congr 1
      exact Subtype.ext hpy
    simp only [map_mul, map_inv, hy', hh₀, hΦτ] at e
    exact e
  have hy'1 : y' ≠ 1 := by
    intro h
    rw [h, mul_one, mul_inv_cancel, mul_one] at hconj
    exact hτ'1 hconj.symm
  have hy'τ'' : y' ≠ τ' := by
    intro h
    rw [h, hτ'τ', hh₀τ', mul_assoc, mul_inv_cancel, mul_one] at hconj
    exact hτ'1 hconj
  have hy'C : y' ∈ centralizer ({τ'} : Set Sp62) := mem_centralizer_singleton_iff.mpr hy'τ'
  have hh₀C : h₀ ∈ centralizer ({τ'} : Set Sp62) := mem_centralizer_singleton_iff.mpr hh₀τ'
  exact false_of_small_conj hτ'τ' hτ'1 hprod hy'C hy'1 hy'τ'' hsmall hh₀C hconj

end CFSG.LargeExtraspecial.AS35QCo
