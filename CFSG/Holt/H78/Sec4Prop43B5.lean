module

public import CFSG.Holt.H78.Sec4Prop43B4

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Half

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem exists_half_system_strong {Λ : Set X} {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card ↥Λᶜ = 2 ^ n)
    {V Q : Subgroup (Perm X)}
    (hV : fusionIsSylowIn 2 V (alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ))
    (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q) (hQΛ : Q ≤ fixingSubgroup (Perm X) Λ) :
    ∃ H₁ : Set X, H₁ ⊆ Λᶜ ∧ 2 * Nat.card H₁ = 2 ^ n ∧
      (∀ q ∈ Q, (∀ x, q x ∈ H₁ ↔ x ∈ H₁) ∨ (∀ x ∈ Λᶜ, q x ∈ H₁ ↔ x ∉ H₁)) ∧
      (∃ s ∈ V, s ^ 2 = 1 ∧ (∀ x ∈ Λᶜ, s x ∈ H₁ ↔ x ∉ H₁) ∧
        ∃ r ∈ V, r ^ 2 = 1 ∧ (∀ x, r x ∈ H₁ ↔ x ∈ H₁) ∧ (∀ x ∈ Λᶜ, r x ≠ x) ∧
          Commute s r) ∧
      (3 ≤ n → fixSet X (V ⊓ fixingSubgroup (Perm X) H₁) = Λ ∪ H₁) := by
  classical
  have hVΛ : V ≤ fixingSubgroup (Perm X) Λ := hV.1.trans inf_le_right
  obtain ⟨V', hV', rfl⟩ := exists_fusionIsSylowIn_alternatingGroup_compl hV
  set φ : Perm ↥Λᶜ →* Perm X := ofSubtype
  have hQrange : ∀ q ∈ Q, ∃ q' : Perm ↥Λᶜ, φ q' = q := fun q hq =>
    exists_ofSubtype_eq_of_mem_fixingSubgroup (hQΛ hq)
  set Q' := Q.comap φ
  have hQ' : IsPGroup 2 Q' := hQ.comap_of_injective φ ofSubtype_injective
  have hVQ' : V' ≤ Q' := fun v hv => hVQ ⟨v, hv, rfl⟩
  obtain ⟨P', hQP', hP'⟩ := exists_fusionIsSylowIn_ge hQ' le_top
  have hV'P : P' ⊓ alternatingGroup ↥Λᶜ = V' :=
    hV'.2.2 _ inf_le_right (hP'.2.1.to_le inf_le_left) (le_inf (hVQ'.trans hQP') hV'.1)
  have hcardY : Fintype.card ↥Λᶜ = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨H, hHc, hperm, ⟨s', hs'V, hs'2, hs'sw, r', hr'V, hr'2, hr'H, hr'free, hsr⟩, hiv⟩ :=
    exists_half_system_of_fusionIsSylowIn_top hP' hn hcardY
  rw [hV'P] at hs'V hr'V
  have hφ : ∀ (g : Perm ↥Λᶜ) (y : ↥Λᶜ), φ g y = g y := fun g y => ofSubtype_apply_coe g y
  have hφΛ : ∀ (g : Perm ↥Λᶜ) {x : X}, x ∉ Λᶜ → φ g x = x := fun g x hx =>
    ofSubtype_apply_of_not_mem g hx
  set H₁ : Set X := Subtype.val '' Hᶜ
  have hmem : ∀ y : ↥Λᶜ, (y : X) ∈ H₁ ↔ y ∉ H := fun y =>
    ⟨fun ⟨y', hy', hyy'⟩ => by rwa [← Subtype.ext hyy'], fun hy => ⟨y, hy, rfl⟩⟩
  have hH₁ : H₁ ⊆ Λᶜ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hpres : ∀ g : Perm ↥Λᶜ, (∀ y, g y ∈ H ↔ y ∈ H) → ∀ x, φ g x ∈ H₁ ↔ x ∈ H₁ :=
    fun g hg x => by
      by_cases hx : x ∈ Λᶜ
      · rw [show x = ((⟨x, hx⟩ : ↥Λᶜ) : X) from rfl, hφ, hmem, hmem, hg]
      · rw [hφΛ g hx]
  have hswap : ∀ g : Perm ↥Λᶜ, (∀ y, g y ∈ H ↔ y ∉ H) → ∀ x ∈ Λᶜ, φ g x ∈ H₁ ↔ x ∉ H₁ :=
    fun g hg x hx => by
      rw [show x = ((⟨x, hx⟩ : ↥Λᶜ) : X) from rfl, hφ, hmem, hmem, hg]
  refine ⟨H₁, hH₁, ?_, fun q hq => ?_, ⟨φ s', ⟨s', hs'V, rfl⟩, by rw [← map_pow, hs'2, map_one],
    hswap s' hs'sw, φ r', ⟨r', hr'V, rfl⟩, by rw [← map_pow, hr'2, map_one], hpres r' hr'H,
    fun x hx => ?_, hsr.map φ⟩, fun hn3 => ?_⟩
  · rw [Nat.card_image_of_injective Subtype.val_injective, Nat.card_coe_set_eq]
    have h1 := Set.ncard_add_ncard_compl H
    rw [Nat.card_eq_fintype_card, hcardY, ← Nat.card_coe_set_eq] at h1
    omega
  · obtain ⟨q', rfl⟩ := hQrange q hq
    rcases hperm q' (hQP' hq) with h1 | h1
    · exact Or.inl (hpres q' h1)
    · exact Or.inr (hswap q' h1)
  · rw [show x = ((⟨x, hx⟩ : ↥Λᶜ) : X) from rfl, hφ]
    exact fun h => hr'free _ (Subtype.ext h)
  · ext x
    constructor
    · intro hx
      by_contra hxΛ
      have hxc : x ∈ Λᶜ := fun h => hxΛ (Or.inl h)
      set y : ↥Λᶜ := ⟨x, hxc⟩
      have hyH : y ∈ H := by
        by_contra h
        exact hxΛ (Or.inr ((hmem y).2 h))
      obtain ⟨w', hw'V, hw'H, hw'y⟩ := hiv hn3 y hyH
      rw [hV'P] at hw'V
      have hwfix : φ w' ∈ fixingSubgroup (Perm X) H₁ :=
        (mem_fixingSubgroup_iff _).2 fun x' hx' => by
          obtain ⟨y', hy', rfl⟩ := hx'
          rw [Perm.smul_def, hφ, hw'H y' hy']
      have := hx (φ w') ⟨⟨w', hw'V, rfl⟩, hwfix⟩
      rw [Perm.smul_def, show x = (y : X) from rfl, hφ] at this
      exact hw'y (Subtype.ext this)
    · rintro (hxΛ | hxH) g ⟨hgV, hgH⟩
      · exact (mem_fixingSubgroup_iff _).1 (hVΛ hgV) x hxΛ
      · exact (mem_fixingSubgroup_iff _).1 hgH x hxH

end Half

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_fixSet_notMem_triple (hαβ : α ≠ β) {P' : Subgroup G}
    (h4 : 4 ≤ Nat.card (fixSet Ω P')) :
    ∃ b ∈ fixSet Ω P', b ∉ ({α, β, (C.γ : Ω)} : Set Ω) := by
  by_contra h
  push Not at h
  have h1 := Set.ncard_le_ncard (fun b hb => h b hb) (Set.toFinite ({α, β, (C.γ : Ω)} : Set Ω))
  rw [C.ncard_triple hαβ, ← Nat.card_coe_set_eq] at h1
  omega

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem false_of_mem_fixSet_calP (hαβ : α ≠ β) {b : Ω} (hb : b ∈ fixSet Ω C.calP)
    (hb' : b ∉ ({α, β, (C.γ : Ω)} : Set Ω)) : False := by
  rw [C.fixSet_eq_of_le hαβ le_rfl (C.calP_le_calG.trans inf_le_left)] at hb
  exact hb' hb

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_stabilizer_boxSet {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {Λc : ∀ j, Set (C.D.Ψc j)} (h : ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = g • (δ : Ω) →
      ((∀ j, C.D.coord δ' j ∈ Λc j) ↔ ∀ j, C.D.coord δ j ∈ Λc j)) :
    g ∈ stabilizer G (C.boxSet Λc) := by
  rw [mem_stabilizer_set]
  intro ω
  constructor
  · rintro ⟨δ', hδ', hδ'Λ⟩
    have hω : ω ∈ holtDelta G Ω α β := by
      have h1 := (twoPointElt (inv_mem hg) • δ').2
      change g⁻¹ • (δ' : Ω) ∈ holtDelta G Ω α β at h1
      rwa [hδ', inv_smul_smul] at h1
    exact ⟨⟨ω, hω⟩, rfl, (h ⟨ω, hω⟩ δ' hδ').mp hδ'Λ⟩
  · rintro ⟨δ, rfl, hδ⟩
    exact ⟨twoPointElt hg • δ, rfl, (h δ _ rfl).mpr hδ⟩

theorem four_le_card_fixSet_calP_inf_stabilizer (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (Λc : ∀ i, Set (C.D.Ψc i))
    (hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ i, C.D.coord δ i ∈ Λc i) → ∃ v ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ i, C.D.coord δ' i ∈ Λc i) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ)
    (hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ i, C.D.coord δ i ∈ Λc i)
    (hsize : ∀ i, (Λc i).ncard = 1 ∨ 5 ≤ (Λc i).ncard) (h₁ : 5 ≤ (Λc C.i₁).ncard)
    (hj : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard) :
    4 ≤ Nat.card (fixSet Ω (C.calP ⊓ stabilizer G (C.boxSet Λc))) := by
  have hstabP : ∀ p ∈ C.calP ⊓ stabilizer G (C.boxSet Λc), ∀ δ δ' : holtDelta G Ω α β,
      (δ' : Ω) = p • (δ : Ω) → (∀ i, C.D.coord δ i ∈ Λc i) → ∀ i, C.D.coord δ' i ∈ Λc i := by
    intro p hp δ δ' e hδ
    have h1 := (mem_stabilizer_set.mp (Subgroup.mem_inf.mp hp).2 (δ : Ω)).mpr
      ((C.mem_boxSet_iff δ).mpr hδ)
    rw [← e] at h1
    exact (C.mem_boxSet_iff δ').mp h1
  refine C.four_le_card_fixSet_of_stab_box hS hαβ
    ((C.sylow.2.1.to_le inf_le_left).to_le inf_le_left) (inf_le_left.trans C.calP_le_calG) Λc
    hstabP (fun δ hδ => ?_) hne hsize h₁ hj
  obtain ⟨v, hvP, hvfix, hvδ⟩ := hmove δ hδ
  refine ⟨v, Subgroup.mem_inf.mpr ⟨hvP, ?_⟩, hvfix, hvδ⟩
  refine C.mem_stabilizer_boxSet (C.mem_stabilizer_pair_of_mem_calP hvP) fun δ₁ δ₂ e => ?_
  constructor
  · intro h2
    have h3 := hvfix δ₂ h2
    have h4 : (δ₁ : Ω) = δ₂ := smul_left_cancel v (by rw [← e, h3])
    rw [(Subtype.ext h4 : δ₁ = δ₂)]
    exact h2
  · intro h1
    have := hvfix δ₁ h1
    rw [(Subtype.ext (e.trans this) : δ₂ = δ₁)]
    exact h1

@[expose] def halfStab (i : C.D.ι) (H : Set (C.D.Ψc i)) : Subgroup G where
  carrier := {g | g ∈ C.calP ∧ ∃ h : g ∈ C.kerC i, ∀ x, C.kerCHom i ⟨g, h⟩ x ∈ H ↔ x ∈ H}
  mul_mem' := by
    rintro a b ⟨haP, ha, haH⟩ ⟨hbP, hb, hbH⟩
    refine ⟨C.calP.mul_mem haP hbP, (C.kerC i).mul_mem ha hb, fun x => ?_⟩
    have : C.kerCHom i ⟨a * b, (C.kerC i).mul_mem ha hb⟩ =
        C.kerCHom i ⟨a, ha⟩ * C.kerCHom i ⟨b, hb⟩ := map_mul (C.kerCHom i) ⟨a, ha⟩ ⟨b, hb⟩
    rw [this, Equiv.Perm.mul_apply, haH, hbH]
  one_mem' := ⟨C.calP.one_mem, (C.kerC i).one_mem, fun x => by
    rw [show (⟨1, (C.kerC i).one_mem⟩ : C.kerC i) = 1 from rfl, map_one, Equiv.Perm.one_apply]⟩
  inv_mem' := by
    rintro a ⟨haP, ha, haH⟩
    refine ⟨C.calP.inv_mem haP, (C.kerC i).inv_mem ha, fun x => ?_⟩
    have : C.kerCHom i ⟨a⁻¹, (C.kerC i).inv_mem ha⟩ = (C.kerCHom i ⟨a, ha⟩)⁻¹ :=
      map_inv (C.kerCHom i) ⟨a, ha⟩
    rw [this]
    have h1 := haH ((C.kerCHom i ⟨a, ha⟩)⁻¹ x)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h1
    exact h1.symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem halfStab_le (i : C.D.ι) (H : Set (C.D.Ψc i)) : C.halfStab i H ≤ C.calP ⊓ C.kerC i :=
  fun _ h => Subgroup.mem_inf.mpr ⟨h.1, h.2.1⟩

theorem false_of_half_i₁ (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Fintype.card (C.D.Ψc C.i₁) = 2 ^ n + 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardΛ : Nat.card ↥(({C.D.coord C.γ C.i₁} : Set (C.D.Ψc C.i₁))ᶜ) = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp [hcard]
  have hV := C.fusionIsSylowIn_Qimg_inf hS hP C.i₁
  rw [← fixingSubgroup_singleton_perm] at hV
  set QP : Subgroup (Equiv.Perm (C.D.Ψc C.i₁)) := (C.calP.subgroupOf C.calG).map C.calGHom
    with hQPdef
  have hQP : IsPGroup 2 QP :=
    (((C.sylow.2.1.to_le inf_le_left).comap_of_injective C.calG.subtype
      C.calG.subtype_injective).to_le le_rfl).map _
  have hVQP : C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁) ≤ QP := by
    intro u hu
    obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hu).1
    exact ⟨⟨q, C.kerC_le_calG _ q.2⟩, hqP, (C.kerCHom_eq_calGHom q).symm⟩
  have hγfix : ∀ p : C.calG, C.calGHom p (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ := fun p =>
    (C.coord_smul_eq_calGHom p (δ := C.γ) (δ' := C.γ) (C.calG_le_stabilizer_γ p.2).symm).symm
  have hQPΛ : QP ≤ fixingSubgroup (Equiv.Perm (C.D.Ψc C.i₁)) {C.D.coord C.γ C.i₁} := by
    rintro _ ⟨p, -, rfl⟩
    rw [fixingSubgroup_singleton_perm]
    exact hγfix p
  obtain ⟨H₁, hH₁Λ, hH₁card, hinv, ⟨s, hsV, hs2, hssw, r, hrV, hr2, hrH, hrfree, hsr⟩,
    hsweep⟩ := exists_half_system_strong (by omega) hcardΛ hV hQP hVQP hQPΛ
  have hmemΛ : ∀ x : C.D.Ψc C.i₁, x ∈ ({C.D.coord C.γ C.i₁} : Set (C.D.Ψc C.i₁))ᶜ ↔
      x ≠ C.D.coord C.γ C.i₁ := fun x => by simp
  have hγH : C.D.coord C.γ C.i₁ ∉ H₁ := fun h => (hmemΛ _).mp (hH₁Λ h) rfl
  have hsγ : s (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ := by
    have := hV.1 hsV
    rw [fixingSubgroup_singleton_perm] at this
    exact this.2
  have hrγ : r (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ := by
    have := hV.1 hrV
    rw [fixingSubgroup_singleton_perm] at this
    exact this.2
  obtain ⟨s', hs'P, hs'⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hsV).1
  obtain ⟨r', hr'P, hr'⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hrV).1
  set R := C.halfStab C.i₁ H₁ with hRdef
  have hfQP : ∀ (q : C.kerC C.i₁), (q : G) ∈ C.calP → C.kerCHom C.i₁ q ∈ QP := fun q hq =>
    ⟨⟨q, C.kerC_le_calG _ q.2⟩, hq, (C.kerCHom_eq_calGHom q).symm⟩
  have hfγ : ∀ (q : C.kerC C.i₁), C.kerCHom C.i₁ q (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ :=
    fun q => C.kerCHom_apply_γ q
  have hcompl : ∀ (π : Equiv.Perm (C.D.Ψc C.i₁)), π (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ →
      ∀ x, x ≠ C.D.coord C.γ C.i₁ → π x ≠ C.D.coord C.γ C.i₁ := fun π hπ x hx h =>
    hx (π.injective (h.trans hπ.symm))
  have hH₁ne : H₁.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [← Nat.card_coe_set_eq]
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsR : (s' : G) ∉ R := by
    rintro ⟨-, h, hH⟩
    obtain ⟨x, hx⟩ := hH₁ne
    have h1 := (hH x).mpr hx
    rw [show (⟨(s' : G), h⟩ : C.kerC C.i₁) = s' from rfl, hs'] at h1
    exact ((hssw x (hH₁Λ hx)).mp h1) hx
  have hrR : (r' : G) ∈ R := ⟨hr'P, r'.2, fun x => by
    rw [show (⟨(r' : G), r'.2⟩ : C.kerC C.i₁) = r' from rfl, hr']
    exact hrH x⟩
  have hswapH : ∀ (π : Equiv.Perm (C.D.Ψc C.i₁)), π (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ →
      (∀ x ∈ ({C.D.coord C.γ C.i₁} : Set (C.D.Ψc C.i₁))ᶜ, π x ∈ H₁ ↔ x ∉ H₁) →
        ∀ x, s (π x) ∈ H₁ ↔ x ∈ H₁ := by
    intro π hπγ hπ x
    by_cases hx : x = C.D.coord C.γ C.i₁
    · rw [hx, hπγ, hsγ]
    · have h1 := hssw (π x) ((hmemΛ _).mpr (hcompl π hπγ x hx))
      rw [h1, hπ x ((hmemΛ x).mpr hx), not_not]
  have hQ : ∀ q ∈ C.calP ⊓ C.kerC C.i₁, q ∈ R ∨ (s' : G) * q ∈ R := by
    intro q hq
    obtain ⟨hqP, hqK⟩ := Subgroup.mem_inf.mp hq
    rcases hinv _ (hfQP ⟨q, hqK⟩ hqP) with h | h
    · exact Or.inl ⟨hqP, hqK, h⟩
    · refine Or.inr ⟨C.calP.mul_mem hs'P hqP, (C.kerC C.i₁).mul_mem s'.2 hqK, fun x => ?_⟩
      rw [show (⟨(s' : G) * q, (C.kerC C.i₁).mul_mem s'.2 hqK⟩ : C.kerC C.i₁) =
        s' * ⟨q, hqK⟩ from rfl, map_mul, Equiv.Perm.mul_apply, hs']
      exact hswapH _ (hfγ _) h x
  have hs2' : C.kerCHom C.i₁ s' * C.kerCHom C.i₁ s' = 1 := by rw [hs', ← sq, hs2]
  have hr2' : C.kerCHom C.i₁ r' * C.kerCHom C.i₁ r' = 1 := by rw [hr', ← sq, hr2]
  have hsr' : C.kerCHom C.i₁ s' * C.kerCHom C.i₁ r' = C.kerCHom C.i₁ r' * C.kerCHom C.i₁ s' := by
    rw [hs', hr']
    exact hsr
  have hsfree : ∀ c, c ≠ C.D.coord C.γ C.i₁ → C.kerCHom C.i₁ s' c ≠ c := by
    intro c hc h
    rw [hs'] at h
    have h1 := hssw c ((hmemΛ c).mpr hc)
    rw [h] at h1
    exact (iff_not_self h1).elim
  have hrfree' : ∀ c, c ≠ C.D.coord C.γ C.i₁ → C.kerCHom C.i₁ r' c ≠ c := by
    intro c hc
    rw [hr']
    exact hrfree c ((hmemΛ c).mpr hc)
  have hsrfree : ∀ c, c ≠ C.D.coord C.γ C.i₁ → C.kerCHom C.i₁ (s' * r') c ≠ c := by
    intro c hc h
    rw [map_mul, Equiv.Perm.mul_apply, hs', hr'] at h
    have hrc : r c ≠ C.D.coord C.γ C.i₁ := hcompl r hrγ c hc
    have h1 := hssw (r c) ((hmemΛ _).mpr hrc)
    rw [h, hrH] at h1
    exact (iff_not_self h1).elim
  have h4 : Fintype.card (C.D.Ψc C.i₁) % 4 = 1 := by
    rw [hcard, show n = 2 + (n - 2) by omega, pow_add]
    simp [Nat.add_mod]
  have hfixR := C.smul_eq_of_lemma44 hS hαβ hT hP h4 (C.halfStab_le C.i₁ H₁) hs'P hsR hrR hQ hs2'
    hr2' hsr' hsfree hrfree' hsrfree
  set Λc : ∀ j, Set (C.D.Ψc j) := Function.update (fun _ => Set.univ) C.i₁
    (insert (C.D.coord C.γ C.i₁) H₁) with hΛc
  have hΛ₁ : Λc C.i₁ = insert (C.D.coord C.γ C.i₁) H₁ := Function.update_self _ _ _
  have hΛj : ∀ j, j ≠ C.i₁ → Λc j = Set.univ := fun j hj => Function.update_of_ne hj _ _
  have hbox : ∀ δ : holtDelta G Ω α β, (∀ j, C.D.coord δ j ∈ Λc j) ↔
      C.D.coord δ C.i₁ ∈ insert (C.D.coord C.γ C.i₁) H₁ := by
    intro δ
    refine ⟨fun h => hΛ₁ ▸ h C.i₁, fun h j => ?_⟩
    by_cases hj : j = C.i₁
    · subst hj
      rw [hΛ₁]
      exact h
    · rw [hΛj j hj]
      exact Set.mem_univ _
  have hstabP : ∀ p (hp : p ∈ C.calP), (∀ x, C.calGHom ⟨p, C.calP_le_calG hp⟩ x ∈ H₁ ↔ x ∈ H₁) →
      p ∈ C.calP ⊓ stabilizer G (C.boxSet Λc) := by
    intro p hp hpH
    refine Subgroup.mem_inf.mpr ⟨hp, C.mem_stabilizer_boxSet (C.mem_stabilizer_pair_of_mem_calP hp)
      fun δ δ' e => ?_⟩
    rw [hbox, hbox, C.coord_smul_eq_calGHom ⟨p, C.calP_le_calG hp⟩ e]
    by_cases hc : C.D.coord δ C.i₁ = C.D.coord C.γ C.i₁
    · rw [hc, hγfix]
    · have hpc : C.calGHom ⟨p, C.calP_le_calG hp⟩ (C.D.coord δ C.i₁) ≠ C.D.coord C.γ C.i₁ :=
        hcompl _ (hγfix _) _ hc
      simp only [Set.mem_insert_iff, hc, hpc, false_or, hpH]
  have hsweep' := hsweep hn
  have hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ j, C.D.coord δ j ∈ Λc j) → ∃ v ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ j, C.D.coord δ' j ∈ Λc j) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ := by
    intro δ hδ
    rw [hbox] at hδ
    have hnot : C.D.coord δ C.i₁ ∉ fixSet (C.D.Ψc C.i₁)
        (C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁) ⊓
          fixingSubgroup (Perm (C.D.Ψc C.i₁)) H₁) := by
      rw [hsweep']
      rintro (h | h)
      · exact hδ (Or.inl h)
      · exact hδ (Or.inr h)
    simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨w, hw, hmv⟩ := hnot
    obtain ⟨hwV, hwH⟩ := Subgroup.mem_inf.mp hw
    have hwγ : w (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ := by
      have := hV.1 hwV
      rw [fixingSubgroup_singleton_perm] at this
      exact this.2
    refine C.exists_mem_calP_of_mem_Qimg_fix (Subgroup.mem_inf.mp hwV).1 (Λc := Λc) ?_ hmv
    intro c hc
    rw [hΛ₁] at hc
    rcases hc with rfl | hc
    · exact hwγ
    · exact (mem_fixingSubgroup_iff _).mp hwH c hc
  have hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ j, C.D.coord δ j ∈ Λc j := by
    obtain ⟨c₀, hc₀Λ, hc₀H⟩ : ∃ c₀, c₀ ∈ ({C.D.coord C.γ C.i₁} : Set (C.D.Ψc C.i₁))ᶜ ∧
        c₀ ∉ H₁ := by
      by_contra h
      push Not at h
      have h1 := Set.ncard_le_ncard (fun x hx => h x hx) (Set.toFinite H₁)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardΛ] at h1
      have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine ⟨C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c₀), fun h => ?_⟩
    rw [hbox, C.coord_coordEquiv_symm, Function.update_self] at h
    rcases h with h | h
    · exact (hmemΛ c₀).mp hc₀Λ h
    · exact hc₀H h
  have hsize : ∀ j, (Λc j).ncard = 1 ∨ 5 ≤ (Λc j).ncard := by
    intro j
    right
    by_cases hj : j = C.i₁
    · subst hj
      rw [hΛ₁, Set.ncard_insert_of_notMem hγH (Set.toFinite _), ← Nat.card_coe_set_eq]
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    · rw [hΛj j hj, C.ncard_univ_Ψc]
      exact C.D.five_le_card j
  have h₁ : 5 ≤ (Λc C.i₁).ncard := (hsize C.i₁).resolve_left (by
    rw [hΛ₁, Set.ncard_insert_of_notMem hγH (Set.toFinite _), ← Nat.card_coe_set_eq]
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega)
  have hj' : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard := by
    obtain ⟨j, hj⟩ := hr
    exact ⟨j, hj, by rw [hΛj j hj, C.ncard_univ_Ψc]; exact C.D.five_le_card j⟩
  have h4' := C.four_le_card_fixSet_calP_inf_stabilizer hS hαβ Λc hmove hne hsize h₁ hj'
  obtain ⟨b, hb, hbt⟩ := C.exists_mem_fixSet_notMem_triple hαβ h4'
  have hRP0 : R ≤ C.calP ⊓ stabilizer G (C.boxSet Λc) := by
    rintro g ⟨hgP, hgK, hgH⟩
    refine hstabP g hgP fun x => ?_
    rw [show C.calGHom ⟨g, C.calP_le_calG hgP⟩ = C.kerCHom C.i₁ ⟨g, hgK⟩ from
      (C.kerCHom_eq_calGHom ⟨g, hgK⟩).symm]
    exact hgH x
  have hbR : b ∈ fixSet Ω R := fun g hg => hb g (hRP0 hg)
  have hs'b : (s' : G) • b = b := hfixR b hbR
  have hbP : b ∈ fixSet Ω C.calP := by
    intro p hp
    rcases hinv _ ⟨⟨p, C.calP_le_calG hp⟩, hp, rfl⟩ with h | h
    · exact hb p (hstabP p hp h)
    · have hsp : (s' : G) * p ∈ C.calP := C.calP.mul_mem hs'P hp
      have h1 : (s' : G) * p ∈ C.calP ⊓ stabilizer G (C.boxSet Λc) := by
        refine hstabP _ hsp fun x => ?_
        have h2 : C.calGHom ⟨(s' : G) * p, C.calP_le_calG hsp⟩ =
            C.calGHom ⟨s', C.kerC_le_calG _ s'.2⟩ * C.calGHom ⟨p, C.calP_le_calG hp⟩ :=
          map_mul C.calGHom ⟨s', C.kerC_le_calG _ s'.2⟩ ⟨p, C.calP_le_calG hp⟩
        rw [h2, ← C.kerCHom_eq_calGHom, hs', Equiv.Perm.mul_apply]
        exact hswapH _ (hγfix _) h x
      have h3 := hb _ h1
      rw [mul_smul] at h3
      exact smul_left_cancel _ (h3.trans hs'b.symm)
  exact C.false_of_mem_fixSet_calP hαβ hbP hbt

end AltConfig

end CFSG.Holt.H78
