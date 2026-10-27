module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsClifford
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3)

theorem glGraphAut_eq_tau :
    CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2) = tau :=
  MulEquiv.ext fun g => Units.ext (by
    rw [CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_matrix, tau_apply_val])

theorem aut_S_cases (α : MulAut S) :
    (∃ s : S, α = MulAut.conj s) ∨ ∃ s : S, α = MulAut.conj s * tau := by
  rcases CFSG.QuasithinUnique.Setup.Family.aut_GL32_cases α with ⟨s, h⟩ | ⟨s, h⟩
  · exact Or.inl ⟨s, h⟩
  · exact Or.inr ⟨s, by rw [h, glGraphAut_eq_tau]⟩

theorem tau_ne_conj (s : S) : tau ≠ MulAut.conj s := by
  rw [← glGraphAut_eq_tau]
  exact CFSG.QuasithinUnique.Setup.Family.glGraphAut_ne_conj s

theorem center_S : Subgroup.center S = ⊥ := CFSG.QuasithinUnique.Setup.Family.center_GL32

theorem eq_one_of_forall_conj {s : S} (h : ∀ g : S, s * g * s⁻¹ = g) : s = 1 := by
  have hs : s ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun g => by
    have h1 := h g
    calc g * s = s * g * s⁻¹ * s := by rw [h1]
      _ = s * g := by group
  rw [center_S, Subgroup.mem_bot] at hs
  exact hs

instance nontrivial_S : Nontrivial S :=
  ⟨⟨1, Jmat, fun h => absurd (congrArg (fun u : S => (u : Mat3) 0 0) h) (by decide)⟩⟩

@[expose] def autHom : Efull →* MulAut K :=
  SemidirectProduct.lift MulAut.conj qAct fun q => MonoidHom.ext fun k => MulEquiv.ext fun x => by
    change qAct q k * x * (qAct q k)⁻¹ = qAct q (k * (qAct q).symm x * k⁻¹)
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem autHom_apply (e : Efull) : autHom e = MulAut.conj e.left * qAct e.right :=
  rfl

theorem autHom_apply_apply (e : Efull) (x : K) :
    autHom e x = e.left * qAct e.right x * e.left⁻¹ :=
  rfl

theorem autHom_inl (k : K) : autHom (SemidirectProduct.inl k) = MulAut.conj k := by
  rw [autHom_apply, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]

theorem autHom_inr (q : QFull) : autHom (SemidirectProduct.inr q) = qAct q := by
  rw [autHom_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul]

@[expose] def tauPow (e : ZMod 2) : MulAut S := if e = 0 then 1 else tau

theorem qAct_apply (q : QFull) (x : K) :
    qAct q x = if q.σ = 0 then (tauPow q.e₁ x.1, tauPow q.e₂ x.2)
      else (tauPow q.e₁ x.2, tauPow q.e₂ x.1) := by
  obtain ⟨e₁, e₂, σ⟩ := q
  change QFull.word autA autB autS ⟨e₁, e₂, σ⟩ x = _
  fin_cases e₁ <;> fin_cases e₂ <;> fin_cases σ <;> rfl

theorem tauPow_eq_conj {e : ZMod 2} {s : S} (h : ∀ g, s * tauPow e g * s⁻¹ = g) : e = 0 := by
  fin_cases e
  · rfl
  · exfalso
    apply tau_ne_conj s⁻¹
    refine MulEquiv.ext fun g => ?_
    have h1 := h g
    change s * tau g * s⁻¹ = g at h1
    rw [MulAut.conj_apply, inv_inv]
    have h2 : tau g = s⁻¹ * (s * tau g * s⁻¹) * s := by group
    rw [h2, h1]

theorem autHom_injective : Function.Injective autHom := by
  rw [injective_iff_map_eq_one]
  intro e he
  have h : ∀ x : K, e.left * qAct e.right x * e.left⁻¹ = x := fun x => by
    rw [← autHom_apply_apply, he, MulAut.one_apply]
  obtain ⟨⟨k₁, k₂⟩, ⟨e₁, e₂, σ⟩⟩ := e
  have hσ : σ = 0 := by
    by_contra hσ
    obtain ⟨g, hg⟩ := exists_ne (1 : S)
    have h1 := congrArg Prod.fst (h (g, 1))
    rw [qAct_apply, ite_eq_right hσ] at h1
    change k₁ * tauPow e₁ 1 * k₁⁻¹ = g at h1
    rw [map_one, mul_one, mul_inv_cancel] at h1
    exact hg h1.symm
  subst hσ
  have h₁ : ∀ g, k₁ * tauPow e₁ g * k₁⁻¹ = g := fun g => by
    have h1 := congrArg Prod.fst (h (g, 1))
    rw [qAct_apply] at h1
    exact h1
  have h₂ : ∀ g, k₂ * tauPow e₂ g * k₂⁻¹ = g := fun g => by
    have h1 := congrArg Prod.snd (h (1, g))
    rw [qAct_apply] at h1
    exact h1
  have he₁ := tauPow_eq_conj h₁
  have he₂ := tauPow_eq_conj h₂
  subst he₁ he₂
  have hk₁ : k₁ = 1 := eq_one_of_forall_conj h₁
  have hk₂ : k₂ = 1 := eq_one_of_forall_conj h₂
  subst hk₁ hk₂
  rfl

abbrev L₁ : Subgroup K := (MonoidHom.inl S S).range

abbrev L₂ : Subgroup K := (MonoidHom.inr S S).range

theorem mem_L₁ {x : K} : x ∈ L₁ ↔ x.2 = 1 :=
  ⟨by rintro ⟨g, rfl⟩; rfl, fun h => ⟨x.1, Prod.ext rfl h.symm⟩⟩

theorem mem_L₂ {x : K} : x ∈ L₂ ↔ x.1 = 1 :=
  ⟨by rintro ⟨g, rfl⟩; rfl, fun h => ⟨x.2, Prod.ext h.symm rfl⟩⟩

theorem card_L₁ : Nat.card L₁ = Nat.card S :=
  Nat.card_congr (MonoidHom.ofInjective (f := MonoidHom.inl S S)
    fun _ _ h => congrArg Prod.fst h).toEquiv.symm

theorem card_L₂ : Nat.card L₂ = Nat.card S :=
  Nat.card_congr (MonoidHom.ofInjective (f := MonoidHom.inr S S)
    fun _ _ h => congrArg Prod.snd h).toEquiv.symm

theorem L₁_ne_L₂ : L₁ ≠ L₂ := by
  intro h
  obtain ⟨g, hg⟩ := exists_ne (1 : S)
  have h1 : ((1, g) : K) ∈ L₁ := h ▸ mem_L₂.2 rfl
  exact hg (mem_L₁.1 h1)

theorem map_autS_L₁ : L₁.map autS.toMonoidHom = L₂ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_L₂.2 (mem_L₁.1 hy)
  · intro hx
    exact ⟨autS x, mem_L₁.2 (mem_L₂.1 hx), Prod.ext rfl rfl⟩

theorem map_autS_L₂ : L₂.map autS.toMonoidHom = L₁ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_L₁.2 (mem_L₂.1 hy)
  · intro hx
    exact ⟨autS x, mem_L₂.2 (mem_L₁.1 hx), Prod.ext rfl rfl⟩

theorem map_mul_toMonoidHom (α β : MulAut K) (L : Subgroup K) :
    L.map (α * β).toMonoidHom = (L.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_L₁ (α : MulAut K) : L₁.map α.toMonoidHom = L₁ ∨ L₁.map α.toMonoidHom = L₂ := by
  have : IsSimpleGroup S :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
  set M := L₁.map α.toMonoidHom with hM
  have hL₁n : L₁.Normal := ⟨fun x hx y => mem_L₁.2 (by
    rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, mem_L₁.1 hx, mul_one, mul_inv_cancel])⟩
  have hMn : M.Normal := hL₁n.map α.toMonoidHom α.surjective
  have hcard : Nat.card M = Nat.card S :=
    (Subgroup.card_map_of_injective α.injective).trans card_L₁
  have hfin : Finite S := inferInstance
  have := hMn.comap (MonoidHom.inl S S)
  have := hMn.comap (MonoidHom.inr S S)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.comap (MonoidHom.inl S S)) with h₁ | h₁
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.comap (MonoidHom.inr S S)) with h₂ | h₂
    ·
      exfalso
      have hM1 : M = ⊥ := by
        rw [eq_bot_iff]
        intro m hm
        have hc₁ : ∀ g : S, m.1 * g * m.1⁻¹ = g := fun g => by
          have h1 : MonoidHom.inl S S (m.1 * g * m.1⁻¹ * g⁻¹) ∈ M := by
            have h2 := M.mul_mem hm (hMn.conj_mem m⁻¹ (M.inv_mem hm) (MonoidHom.inl S S g))
            convert h2 using 1
            refine Prod.ext ?_ ?_ <;> simp [mul_assoc]
          rw [← Subgroup.mem_comap, h₁, Subgroup.mem_bot, mul_inv_eq_one] at h1
          exact h1
        have hc₂ : ∀ g : S, m.2 * g * m.2⁻¹ = g := fun g => by
          have h1 : MonoidHom.inr S S (m.2 * g * m.2⁻¹ * g⁻¹) ∈ M := by
            have h2 := M.mul_mem hm (hMn.conj_mem m⁻¹ (M.inv_mem hm) (MonoidHom.inr S S g))
            convert h2 using 1
            refine Prod.ext ?_ ?_ <;> simp [mul_assoc]
          rw [← Subgroup.mem_comap, h₂, Subgroup.mem_bot, mul_inv_eq_one] at h1
          exact h1
        rw [Subgroup.mem_bot]
        exact Prod.ext (eq_one_of_forall_conj hc₁) (eq_one_of_forall_conj hc₂)
      rw [hM1, Subgroup.card_bot] at hcard
      have h168 : 1 < Nat.card S := Finite.one_lt_card_iff_nontrivial.2 inferInstance
      omega
    · right
      have hle : L₂ ≤ M := by
        rintro _ ⟨g, rfl⟩
        have hg : g ∈ M.comap (MonoidHom.inr S S) := h₂ ▸ Subgroup.mem_top g
        exact hg
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_L₂])).symm
  · left
    have hle : L₁ ≤ M := by
      rintro _ ⟨g, rfl⟩
      have hg : g ∈ M.comap (MonoidHom.inl S S) := h₁ ▸ Subgroup.mem_top g
      exact hg
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_L₁])).symm

theorem exists_autHom_of_preserves (α : MulAut K) (h₁ : L₁.map α.toMonoidHom = L₁)
    (h₂ : L₂.map α.toMonoidHom = L₂) : ∃ e : Efull, autHom e = α := by
  have hL₁ : ∀ g : S, (α (g, 1)).2 = 1 := fun g =>
    mem_L₁.1 (h₁ ▸ Subgroup.mem_map_of_mem α.toMonoidHom (mem_L₁.2 rfl))
  have hL₂ : ∀ g : S, (α (1, g)).1 = 1 := fun g =>
    mem_L₂.1 (h₂ ▸ Subgroup.mem_map_of_mem α.toMonoidHom (mem_L₂.2 rfl))
  let f₁ : S →* S := (MonoidHom.fst S S).comp (α.toMonoidHom.comp (MonoidHom.inl S S))
  let f₂ : S →* S := (MonoidHom.snd S S).comp (α.toMonoidHom.comp (MonoidHom.inr S S))
  have hα : ∀ x : K, α x = (f₁ x.1, f₂ x.2) := fun x => by
    have h1 : α x = α (x.1, 1) * α (1, x.2) := by
      rw [← map_mul]
      exact congrArg α (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [h1]
    refine Prod.ext ?_ ?_
    · change (α (x.1, 1)).1 * (α (1, x.2)).1 = (α (x.1, 1)).1
      rw [hL₂, mul_one]
    · change (α (x.1, 1)).2 * (α (1, x.2)).2 = (α (1, x.2)).2
      rw [hL₁, one_mul]
  have hf₁ : Function.Injective f₁ := fun g g' h => by
    have h1 : α (g, 1) = α (g', 1) := Prod.ext h (by rw [hL₁, hL₁])
    exact congrArg Prod.fst (α.injective h1)
  have hf₂ : Function.Injective f₂ := fun g g' h => by
    have h1 : α (1, g) = α (1, g') := Prod.ext (by rw [hL₂, hL₂]) h
    exact congrArg Prod.snd (α.injective h1)
  let α₁ : MulAut S := MulEquiv.ofBijective f₁ (Finite.injective_iff_bijective.1 hf₁)
  let α₂ : MulAut S := MulEquiv.ofBijective f₂ (Finite.injective_iff_bijective.1 hf₂)
  have hcase : ∀ β : MulAut S, ∃ (s : S) (e : ZMod 2), ∀ g, β g = s * tauPow e g * s⁻¹ := by
    intro β
    rcases aut_S_cases β with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact ⟨s, 0, fun g => rfl⟩
    · exact ⟨s, 1, fun g => rfl⟩
  obtain ⟨s₁, e₁, hs₁⟩ := hcase α₁
  obtain ⟨s₂, e₂, hs₂⟩ := hcase α₂
  refine ⟨⟨(s₁, s₂), ⟨e₁, e₂, 0⟩⟩, MulEquiv.ext fun x => ?_⟩
  rw [autHom_apply_apply, hα, qAct_apply]
  refine Prod.ext ?_ ?_
  · exact (hs₁ x.1).symm
  · exact (hs₂ x.2).symm

theorem autHom_surjective : Function.Surjective autHom := by
  intro α
  have hmap₂ : ∀ β : MulAut K, L₂.map β.toMonoidHom = L₁.map (β * autS).toMonoidHom := fun β => by
    rw [map_mul_toMonoidHom, map_autS_L₁]
  have hinj : ∀ (β : MulAut K) {L L' : Subgroup K}, L.map β.toMonoidHom = L'.map β.toMonoidHom →
      L = L' := fun β L L' h => Subgroup.map_injective β.injective h
  rcases map_L₁ α with h₁ | h₁
  · have h₂ : L₂.map α.toMonoidHom = L₂ := by
      rcases map_L₁ (α * autS) with h | h
      · exfalso
        rw [← hmap₂, ← h₁] at h
        exact L₁_ne_L₂ (hinj α h).symm
      · rwa [← hmap₂] at h
    exact exists_autHom_of_preserves α h₁ h₂
  ·
    have h₂ : L₂.map α.toMonoidHom = L₁ := by
      rcases map_L₁ (α * autS) with h | h
      · rwa [← hmap₂] at h
      · exfalso
        rw [← hmap₂] at h
        exact L₁_ne_L₂ (hinj α (h.trans h₁.symm)).symm
    obtain ⟨e, he⟩ := exists_autHom_of_preserves (α * autS)
      (by rw [map_mul_toMonoidHom, map_autS_L₁, h₂])
      (by rw [map_mul_toMonoidHom, map_autS_L₂, h₁])
    refine ⟨e * SemidirectProduct.inr QFull.s, ?_⟩
    rw [map_mul, he, autHom_inr, qAct_s, mul_assoc, show autS * autS = 1 from
      MulEquiv.ext fun _ => rfl, mul_one]

instance finite_MulAut_K : Finite (MulAut K) := Finite.of_surjective autHom autHom_surjective

@[reducible] def decEqQFull : DecidableEq QFull := fun q r =>
  decidable_of_iff (q.e₁ = r.e₁ ∧ q.e₂ = r.e₂ ∧ q.σ = r.σ)
    ⟨fun ⟨h1, h2, h3⟩ => QFull.ext h1 h2 h3, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

attribute [local instance high] decEqQFull

@[expose] def qList : List QFull :=
  [QFull.mk 0 0 0, QFull.mk 1 0 0, QFull.mk 0 1 0, QFull.mk 1 1 0, QFull.mk 0 0 1,
    QFull.mk 1 0 1, QFull.mk 0 1 1, QFull.mk 1 1 1]

theorem mem_qList (q : QFull) : q ∈ qList := by
  obtain ⟨a, b, c⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

@[reducible] def fintypeQFull : Fintype QFull := ⟨⟨qList, by decide⟩, mem_qList⟩

attribute [local instance high] fintypeQFull

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
