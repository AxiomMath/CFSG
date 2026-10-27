module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XBasic
public import Mathlib.GroupTheory.Complement

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

private theorem XHyp.isComplement' (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V₁.IsComplement' V₂ := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    exact h.inf_eq_bot
  · letI : IsMulCommutative V := h.elemAb.toIsMulCommutative
    ext v
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    have hv : v ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; exact Subgroup.mem_top v
    exact (Subgroup.mem_sup_of_normal_right (s := V₁) (t := V₂)).1 hv

private theorem XHyp.bijective_mul (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    Function.Bijective (fun p : ↥V₁ × ↥V₂ => (p.1 : V) * (p.2 : V)) :=
  Subgroup.isComplement'_def.1 h.isComplement'

private noncomputable def XHyp.pairMulEquiv (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    (↥V₁ × ↥V₂) ≃* V := by
  letI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  exact MulEquiv.ofBijective
    ({ toFun := fun p : ↥V₁ × ↥V₂ => (p.1 : V) * (p.2 : V)
       map_one' := by simp
       map_mul' := by
         intro p q
         simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
         ac_rfl } : ↥V₁ × ↥V₂ →* V)
    h.bijective_mul

private noncomputable def XHyp.decEquiv (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    V ≃* (↥V₁ × ↥V₂) :=
  h.pairMulEquiv.symm

private noncomputable def XHyp.proj₁' (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V →* ↥V₁ :=
  (MonoidHom.fst (↥V₁) (↥V₂)).comp h.decEquiv.toMonoidHom

private noncomputable def XHyp.proj₂' (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V →* ↥V₂ :=
  (MonoidHom.snd (↥V₁) (↥V₂)).comp h.decEquiv.toMonoidHom

private theorem XHyp.proj_mul (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) :
    (h.proj₁' v : V) * (h.proj₂' v : V) = v := by
  change ((h.decEquiv v).1 : V) * ((h.decEquiv v).2 : V) = v
  exact h.pairMulEquiv.apply_symm_apply v

private theorem XHyp.dec_eq (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {p : ↥V₁ × ↥V₂} {v : V}
    (hp : (p.1 : V) * (p.2 : V) = v) : h.decEquiv v = p := by
  have h1 : h.pairMulEquiv (h.decEquiv v) = v := h.pairMulEquiv.apply_symm_apply v
  have h2 : h.pairMulEquiv p = v := hp
  exact h.pairMulEquiv.injective (h1.trans h2.symm)

private theorem XHyp.proj₁_comm (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {g : X} (hg : g ∈ Q) (v : V) :
    h.proj₁' (ρ g v) = ⟨ρ g (h.proj₁' v : V), h.apply_mem₁ hg (h.proj₁' v).2⟩ := by
  have ha : ρ g ((h.decEquiv v).1 : V) ∈ V₁ := h.apply_mem₁ hg (h.decEquiv v).1.2
  have hb : ρ g ((h.decEquiv v).2 : V) ∈ V₂ := h.apply_mem₂ hg (h.decEquiv v).2.2
  let p : ↥V₁ × ↥V₂ :=
    (⟨ρ g ((h.decEquiv v).1 : V), ha⟩, ⟨ρ g ((h.decEquiv v).2 : V), hb⟩)
  have hp : (p.1 : V) * (p.2 : V) = ρ g v := by
    have hm : ((h.decEquiv v).1 : V) * ((h.decEquiv v).2 : V) = v := h.proj_mul v
    show ρ g ((h.decEquiv v).1 : V) * ρ g ((h.decEquiv v).2 : V) = ρ g v
    rw [← map_mul (ρ g), hm]
  have hdec := h.dec_eq hp
  ext
  change ((h.decEquiv (ρ g v)).1 : V) = ρ g ((h.decEquiv v).1 : V)
  rw [hdec]

private theorem XHyp.proj₂_comm (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {g : X} (hg : g ∈ Q) (v : V) :
    h.proj₂' (ρ g v) = ⟨ρ g (h.proj₂' v : V), h.apply_mem₂ hg (h.proj₂' v).2⟩ := by
  have ha : ρ g ((h.decEquiv v).1 : V) ∈ V₁ := h.apply_mem₁ hg (h.decEquiv v).1.2
  have hb : ρ g ((h.decEquiv v).2 : V) ∈ V₂ := h.apply_mem₂ hg (h.decEquiv v).2.2
  let p : ↥V₁ × ↥V₂ :=
    (⟨ρ g ((h.decEquiv v).1 : V), ha⟩, ⟨ρ g ((h.decEquiv v).2 : V), hb⟩)
  have hp : (p.1 : V) * (p.2 : V) = ρ g v := by
    have hm : ((h.decEquiv v).1 : V) * ((h.decEquiv v).2 : V) = v := h.proj_mul v
    show ρ g ((h.decEquiv v).1 : V) * ρ g ((h.decEquiv v).2 : V) = ρ g v
    rw [← map_mul (ρ g), hm]
  have hdec := h.dec_eq hp
  ext
  change ((h.decEquiv (ρ g v)).2 : V) = ρ g ((h.decEquiv v).2 : V)
  rw [hdec]


private theorem XHyp.inf₁_cases (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    U ⊓ V₁ = ⊥ ∨ U ⊓ V₁ = V₁ := by
  have hI : ∀ g ∈ ⁅Q₁, Q₁⁆, ∀ u ∈ (U ⊓ V₁).subgroupOf V₁,
      (g : MulAut ↥V₁) u ∈ (U ⊓ V₁).subgroupOf V₁ := by
    intro g hg u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    let g₁ : ↥Q₁ := ⟨g, Subgroup.commutator_le_self Q₁ hg⟩
    let q : ↥Q := h.resEquiv.symm g₁
    have hres : h.resEquiv q = g₁ := MulEquiv.apply_symm_apply h.resEquiv g₁
    have hval : ((h.resEquiv q : MulAut ↥V₁)) = g := congrArg Subtype.val hres
    have hqmem : ((h.resEquiv q : MulAut ↥V₁)) ∈ ⁅Q₁, Q₁⁆ := by
      rw [hval]
      exact hg
    have hq : (q : X) ∈ ⁅Q, Q⁆ := (h.resEquiv_mem_commutator_iff q).1 hqmem
    have hqQ : (q : X) ∈ Q := Subgroup.commutator_le_self Q hq
    have hact : ((g : MulAut ↥V₁) u : V) = ρ q (u : V) := by
      have hres' := h.resEquiv_apply q u
      rw [hval] at hres'
      exact hres'
    rw [hact]
    exact ⟨hU q hq (u : V) hu.1, h.apply_mem₁ hqQ hu.2⟩
  rcases h.module.irreducible_derived ((U ⊓ V₁).subgroupOf V₁) hI with hbot | htop
  · left
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    have hh : (U ⊓ V₁) ⊓ V₁ = ⊥ := disjoint_iff.1 hbot
    simpa only [inf_assoc, inf_idem] using hh
  · right
    have hle : V₁ ≤ U ⊓ V₁ := Subgroup.subgroupOf_eq_top.1 htop
    exact inf_eq_right.2 (hle.trans inf_le_left)

private theorem XHyp.inf₂_cases (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    U ⊓ V₂ = ⊥ ∨ U ⊓ V₂ = V₂ := by
  let W : Subgroup V := (U ⊓ V₂).map (ρ z).toMonoidHom
  have hWV₁ : W ≤ V₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact h.swap₂ hu.2
  have hWinv : ∀ g ∈ ⁅Q, Q⁆, ∀ w ∈ W, ρ g w ∈ W := by
    rintro g hg w ⟨u, hu, rfl⟩
    have hgQ : g ∈ Q := Subgroup.commutator_le_self Q hg
    have hcomm : ρ g * ρ z = ρ z * ρ g := by
      have := congrArg ρ (h.mul_comm_of_mem hgQ)
      simpa using this
    refine ⟨ρ g u, ⟨hU g hg u hu.1, h.apply_mem₂ hgQ hu.2⟩, ?_⟩
    show ρ z (ρ g u) = ρ g (ρ z u)
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm]
  have hWcases := h.inf₁_cases hWinv
  have hW : W = ⊥ ∨ W = V₁ := by
    have hinf : W ⊓ V₁ = W := inf_eq_left.2 hWV₁
    rcases hWcases with hb | ht
    · left; rwa [hinf] at hb
    · right; rwa [hinf] at ht
  rcases hW with hbot | htop
  · left
    rw [eq_bot_iff]
    intro u hu
    have hmem : ρ z u ∈ W := ⟨u, hu, rfl⟩
    rw [hbot] at hmem
    have h1 : ρ z u = 1 := Subgroup.mem_bot.1 hmem
    have := congrArg (fun w => (ρ z)⁻¹ w) h1
    simpa using this
  · right
    apply le_antisymm inf_le_right
    intro u hu
    have hmem : ρ z u ∈ W := by rw [htop]; exact h.swap₂ hu
    obtain ⟨u', hu', hzu'⟩ := Subgroup.mem_map.1 hmem
    have : u' = u := (ρ z).injective hzu'
    exact ⟨this ▸ hu'.1, hu⟩


private theorem XHyp.rho_z_mul_self (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : ρ z * ρ z = 1 := by
  have := congrArg ρ h.mul_self
  simpa using this

private theorem XHyp.rho_comm (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {g : X} (hg : g ∈ Q) :
    ρ g * ρ z = ρ z * ρ g := by
  have := congrArg ρ (h.mul_comm_of_mem hg)
  simpa using this

private theorem XHyp.rho_z_apply_apply (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) :
    ρ z (ρ z v) = v := by
  have := congrArg (fun f : MulAut V => f v) h.rho_z_mul_self
  simpa using this

theorem XHyp.apply_eq_self₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {σ : MulAut V}
    (hσ : ∀ v ∈ V₁, σ v ∈ V₁) (hc : ∀ g ∈ ⁅Q, Q⁆, ∀ v ∈ V₁, σ (ρ g v) = ρ g (σ v)) :
    ∀ v ∈ V₁, σ v = v := by
  let f : ↥V₁ →* ↥V₁ :=
    { toFun := fun v => ⟨σ v, hσ v v.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hf : ∀ g ∈ ⁅Q₁, Q₁⁆, ∀ a, f ((g : MulAut ↥V₁) a) = (g : MulAut ↥V₁) (f a) := by
    intro g hg a
    let g₁ : ↥Q₁ := ⟨g, Subgroup.commutator_le_self Q₁ hg⟩
    let q : ↥Q := h.resEquiv.symm g₁
    have hres : h.resEquiv q = g₁ := MulEquiv.apply_symm_apply h.resEquiv g₁
    have hval : ((h.resEquiv q : MulAut ↥V₁)) = g := congrArg Subtype.val hres
    have hqmem : ((h.resEquiv q : MulAut ↥V₁)) ∈ ⁅Q₁, Q₁⁆ := by rw [hval]; exact hg
    have hq : (q : X) ∈ ⁅Q, Q⁆ := (h.resEquiv_mem_commutator_iff q).1 hqmem
    have hga : (((g : MulAut ↥V₁) a : ↥V₁) : V) = ρ q (a : V) := by
      rw [show (g : MulAut ↥V₁) = (h.resEquiv q : MulAut ↥V₁) from hval.symm]
      exact h.resEquiv_apply q a
    have hgfa : (((g : MulAut ↥V₁) (f a) : ↥V₁) : V) = ρ q (σ (a : V)) := by
      rw [show (g : MulAut ↥V₁) = (h.resEquiv q : MulAut ↥V₁) from hval.symm]
      exact h.resEquiv_apply q (f a)
    apply Subtype.ext
    change σ (((g : MulAut ↥V₁) a : ↥V₁) : V) = (((g : MulAut ↥V₁) (f a) : ↥V₁) : V)
    rw [hga, hgfa]
    exact hc q hq (a : V) a.2
  rcases h.module.endo_derived f hf with hf1 | hfid
  · exfalso
    have hsub : Subsingleton ↥V₁ := by
      refine ⟨fun a b => ?_⟩
      have ha : (a : V) = 1 := by
        have hfa : f a = 1 := by rw [hf1]; rfl
        have hσa : σ (a : V) = 1 := by
          have := congrArg (fun x : ↥V₁ => (x : V)) hfa
          simpa [f] using this
        have hinj : σ (a : V) = σ 1 := by rw [hσa, map_one]
        exact σ.injective hinj
      have hb : (b : V) = 1 := by
        have hfb : f b = 1 := by rw [hf1]; rfl
        have hσb : σ (b : V) = 1 := by
          have := congrArg (fun x : ↥V₁ => (x : V)) hfb
          simpa [f] using this
        have hinj : σ (b : V) = σ 1 := by rw [hσb, map_one]
        exact σ.injective hinj
      have ha1 : a = 1 := Subtype.ext (by simpa using ha)
      have hb1 : b = 1 := Subtype.ext (by simpa using hb)
      rw [ha1, hb1]
    have hcard : Nat.card ↥V₁ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    rw [h.module.card] at hcard
    norm_num at hcard
  · intro v hv
    have hfv : f ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hfid]; rfl
    exact congrArg Subtype.val hfv

theorem XHyp.apply_eq_self₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {σ : MulAut V}
    (hσ : ∀ v ∈ V₂, σ v ∈ V₂) (hc : ∀ g ∈ ⁅Q, Q⁆, ∀ v ∈ V₂, σ (ρ g v) = ρ g (σ v)) :
    ∀ v ∈ V₂, σ v = v := by
  let σ' : MulAut V := ρ z * σ * ρ z
  have hσ' : ∀ v ∈ V₁, σ' v ∈ V₁ := by
    intro v hv
    have hv2 : ρ z v ∈ V₂ := (h.swap v).1 hv
    have h1 : σ (ρ z v) ∈ V₂ := hσ _ hv2
    have h2 : ρ z (σ (ρ z v)) ∈ V₁ := h.swap₂ h1
    simpa [σ'] using h2
  have hc' : ∀ g ∈ ⁅Q, Q⁆, ∀ v ∈ V₁, σ' (ρ g v) = ρ g (σ' v) := by
    intro g hg v hv
    have hgQ : g ∈ Q := Subgroup.commutator_le_self Q hg
    have hcomm : ρ z * ρ g = ρ g * ρ z := (h.rho_comm hgQ).symm
    have hcz : ∀ x : V, ρ z (ρ g x) = ρ g (ρ z x) := by
      intro x
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm]
    have hv2 : ρ z v ∈ V₂ := (h.swap v).1 hv
    show (ρ z * σ * ρ z) (ρ g v) = ρ g ((ρ z * σ * ρ z) v)
    simp only [MulAut.mul_apply]
    rw [hcz]
    rw [hc g hg (ρ z v) hv2]
    rw [hcz]
  have hfix := h.apply_eq_self₁ hσ' hc'
  intro v hv
  have hv1 : ρ z v ∈ V₁ := h.swap₂ hv
  have hτ : σ' (ρ z v) = ρ z v := hfix (ρ z v) hv1
  have hstep : ρ z (σ v) = ρ z v := by
    simpa [σ', h.rho_z_apply_apply v] using hτ
  exact (ρ z).injective hstep


private theorem XHyp.finite (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Finite V :=
  Nat.finite_of_card_ne_zero (by rw [h.card_V]; norm_num)

private theorem XHyp.symm_mem₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {σ : MulAut V}
    (hσ : ∀ v ∈ V₁, σ v ∈ V₁) : ∀ v ∈ V₁, σ.symm v ∈ V₁ := by
  haveI : Finite V := h.finite
  intro v hv
  have hle : V₁.map σ.toMonoidHom ≤ V₁ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hσ w hw
  have hcard : Nat.card (V₁.map σ.toMonoidHom) = Nat.card V₁ :=
    Subgroup.card_map_of_injective σ.injective
  have heq : V₁.map σ.toMonoidHom = V₁ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  have hmem : v ∈ V₁.map σ.toMonoidHom := by rw [heq]; exact hv
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 hmem
  rw [← hwv]
  change σ.symm (σ w) ∈ V₁
  rw [MulEquiv.symm_apply_apply]
  exact hw

private noncomputable def XHyp.restrictAut (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {σ : MulAut V}
    (hσ : ∀ v ∈ V₁, σ v ∈ V₁) : MulAut ↥V₁ where
  toFun v := ⟨σ v, hσ v v.2⟩
  invFun v := ⟨σ.symm v, h.symm_mem₁ hσ v v.2⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  map_mul' a b := by ext; simp

theorem XHyp.exists_mem_Q₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {σ : MulAut V}
    (hσ : ∀ v ∈ V₁, σ v ∈ V₁)
    (hn : ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v ∈ V₁, σ (ρ g v) = ρ g' (σ v)) :
    ∃ q ∈ Q, ∀ v ∈ V₁, σ v = ρ q v := by
  let τ : MulAut ↥V₁ := h.restrictAut hσ
  have hτ : ∀ x : ↥V₁, (τ x : V) = σ (x : V) := fun x => rfl
  have hτinv : ∀ x : ↥V₁, ((τ : MulAut ↥V₁)⁻¹ x : V) = σ.symm (x : V) := fun x => rfl
  have hnorm : ∀ g' ∈ ⁅Q₁, Q₁⁆, τ * g' * τ⁻¹ ∈ ⁅Q₁, Q₁⁆ := by
    intro g' hg'
    let g₁ : ↥Q₁ := ⟨g', Subgroup.commutator_le_self Q₁ hg'⟩
    let q : ↥Q := h.resEquiv.symm g₁
    have hres : h.resEquiv q = g₁ := MulEquiv.apply_symm_apply h.resEquiv g₁
    have hval : ((h.resEquiv q : MulAut ↥V₁)) = g' := congrArg Subtype.val hres
    have hqmem : ((h.resEquiv q : MulAut ↥V₁)) ∈ ⁅Q₁, Q₁⁆ := by rw [hval]; exact hg'
    have hq : (q : X) ∈ ⁅Q, Q⁆ := (h.resEquiv_mem_commutator_iff q).1 hqmem
    obtain ⟨q', hq', hq'eq⟩ := hn q hq
    have hq'Q : q' ∈ Q := Subgroup.commutator_le_self Q hq'
    have hconj : τ * g' * τ⁻¹ = (h.resEquiv ⟨q', hq'Q⟩ : MulAut ↥V₁) := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have hx : σ.symm (x : V) ∈ V₁ := h.symm_mem₁ hσ (x : V) x.2
      have hg'x : ((g' ((τ : MulAut ↥V₁)⁻¹ x) : ↥V₁) : V) = ρ q (σ.symm (x : V)) := by
        have h1 := h.resEquiv_apply q (((τ : MulAut ↥V₁)⁻¹ x))
        rw [hval] at h1
        rwa [hτinv] at h1
      show ((τ * g' * τ⁻¹) x : V) = (((h.resEquiv ⟨q', hq'Q⟩ : MulAut ↥V₁) x : ↥V₁) : V)
      simp only [MulAut.mul_apply]
      rw [hτ]
      rw [hg'x]
      rw [hq'eq (σ.symm (x : V)) hx]
      rw [MulEquiv.apply_symm_apply]
      exact (h.resEquiv_apply ⟨q', hq'Q⟩ x).symm
    rw [hconj]
    exact (h.resEquiv_mem_commutator_iff ⟨q', hq'Q⟩).2 hq'
  have hτQ : τ ∈ Q₁ := h.module.normalizer_derived τ hnorm
  let q : ↥Q := h.resEquiv.symm ⟨τ, hτQ⟩
  refine ⟨q, q.2, fun v hv => ?_⟩
  have hqval : (h.resEquiv q : MulAut ↥V₁) = τ :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply h.resEquiv ⟨τ, hτQ⟩)
  have h1 : (((h.resEquiv q : MulAut ↥V₁) ⟨v, hv⟩ : ↥V₁) : V) = ρ q v :=
    h.resEquiv_apply q ⟨v, hv⟩
  have h2 : (((h.resEquiv q : MulAut ↥V₁) ⟨v, hv⟩ : ↥V₁) : V) = σ v := by
    rw [hqval]
    rfl
  rw [← h1, h2]

theorem XHyp.exists_mem_Q₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {σ : MulAut V}
    (hσ : ∀ v ∈ V₂, σ v ∈ V₂)
    (hn : ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v ∈ V₂, σ (ρ g v) = ρ g' (σ v)) :
    ∃ q ∈ Q, ∀ v ∈ V₂, σ v = ρ q v := by
  let σ' : MulAut V := ρ z * σ * ρ z
  have hσ' : ∀ v ∈ V₁, σ' v ∈ V₁ := by
    intro v hv
    have hv2 : ρ z v ∈ V₂ := (h.swap v).1 hv
    have h1 : σ (ρ z v) ∈ V₂ := hσ _ hv2
    have h2 : ρ z (σ (ρ z v)) ∈ V₁ := h.swap₂ h1
    simpa [σ'] using h2
  have hn' : ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v ∈ V₁, σ' (ρ g v) = ρ g' (σ' v) := by
    intro g hg
    obtain ⟨g', hg', hg'eq⟩ := hn g hg
    refine ⟨g', hg', fun v hv => ?_⟩
    have hgQ : g ∈ Q := Subgroup.commutator_le_self Q hg
    have hg'Q : g' ∈ Q := Subgroup.commutator_le_self Q hg'
    have hcommg : ρ z * ρ g = ρ g * ρ z := (h.rho_comm hgQ).symm
    have hcommg' : ρ z * ρ g' = ρ g' * ρ z := (h.rho_comm hg'Q).symm
    have hcz : ∀ x : V, ρ z (ρ g x) = ρ g (ρ z x) := by
      intro x; rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcommg]
    have hcz' : ∀ x : V, ρ z (ρ g' x) = ρ g' (ρ z x) := by
      intro x; rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcommg']
    have hz2 : ρ z (ρ z v) = v := h.rho_z_apply_apply v
    have hv2 : ρ z v ∈ V₂ := (h.swap v).1 hv
    show (ρ z * σ * ρ z) (ρ g v) = ρ g' ((ρ z * σ * ρ z) v)
    simp only [MulAut.mul_apply]
    rw [hcz]
    rw [hg'eq (ρ z v) hv2]
    rw [hcz']
  obtain ⟨q, hq, hqeq⟩ := h.exists_mem_Q₁ hσ' hn'
  refine ⟨q, hq, fun v hv => ?_⟩
  have hv1 : ρ z v ∈ V₁ := h.swap₂ hv
  have h1 : σ' (ρ z v) = ρ q (ρ z v) := hqeq (ρ z v) hv1
  have h2 : σ' (ρ z v) = ρ z (σ v) := by
    simp only [σ', MulAut.mul_apply]
    rw [h.rho_z_apply_apply v]
  have h3 : ρ q (ρ z v) = ρ z (ρ q v) := by
    have hcomm : ρ q * ρ z = ρ z * ρ q := h.rho_comm hq
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm]
  rw [h2, h3] at h1
  exact (ρ z).injective h1


private noncomputable def XHyp.proj₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V →* V :=
  (Subgroup.subtype V₁).comp h.proj₁'

private noncomputable def XHyp.proj₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V →* V :=
  (Subgroup.subtype V₂).comp h.proj₂'

private theorem XHyp.proj₁_mem (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) : h.proj₁ v ∈ V₁ :=
  (h.proj₁' v).2

private theorem XHyp.proj₂_mem (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) : h.proj₂ v ∈ V₂ :=
  (h.proj₂' v).2

private theorem XHyp.proj_mul' (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) :
    h.proj₁ v * h.proj₂ v = v := h.proj_mul v

private theorem XHyp.proj₁_comm' (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {g : X} (hg : g ∈ Q) (v : V) :
    h.proj₁ (ρ g v) = ρ g (h.proj₁ v) :=
  congrArg Subtype.val (h.proj₁_comm hg v)

private theorem XHyp.proj₂_comm' (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {g : X} (hg : g ∈ Q) (v : V) :
    h.proj₂ (ρ g v) = ρ g (h.proj₂ v) :=
  congrArg Subtype.val (h.proj₂_comm hg v)

private theorem XHyp.proj₁_map_invariant (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    ∀ g ∈ ⁅Q, Q⁆, ∀ w ∈ U.map h.proj₁, ρ g w ∈ U.map h.proj₁ := by
  rintro g hg w ⟨u, hu, rfl⟩
  exact ⟨ρ g u, hU g hg u hu, h.proj₁_comm' (Subgroup.commutator_le_self Q hg) u⟩

private theorem XHyp.proj₂_map_invariant (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    ∀ g ∈ ⁅Q, Q⁆, ∀ w ∈ U.map h.proj₂, ρ g w ∈ U.map h.proj₂ := by
  rintro g hg w ⟨u, hu, rfl⟩
  exact ⟨ρ g u, hU g hg u hu, h.proj₂_comm' (Subgroup.commutator_le_self Q hg) u⟩

private theorem XHyp.proj₁_map_cases (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    U.map h.proj₁ = ⊥ ∨ U.map h.proj₁ = V₁ := by
  have hle : U.map h.proj₁ ≤ V₁ := by
    rintro _ ⟨u, -, rfl⟩
    exact h.proj₁_mem u
  have hcases := h.inf₁_cases (U := U.map h.proj₁) (h.proj₁_map_invariant hU)
  have hinf : U.map h.proj₁ ⊓ V₁ = U.map h.proj₁ := inf_eq_left.2 hle
  rcases hcases with hb | ht
  · left; rwa [hinf] at hb
  · right; rwa [hinf] at ht

private theorem XHyp.proj₂_map_cases (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    U.map h.proj₂ = ⊥ ∨ U.map h.proj₂ = V₂ := by
  have hle : U.map h.proj₂ ≤ V₂ := by
    rintro _ ⟨u, -, rfl⟩
    exact h.proj₂_mem u
  have hcases := h.inf₂_cases (U := U.map h.proj₂) (h.proj₂_map_invariant hU)
  have hinf : U.map h.proj₂ ⊓ V₂ = U.map h.proj₂ := inf_eq_left.2 hle
  rcases hcases with hb | ht
  · left; rwa [hinf] at hb
  · right; rwa [hinf] at ht

private theorem XHyp.eq_bot_of_proj₁_eq_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (h2 : U ⊓ V₂ = ⊥) (h1 : U.map h.proj₁ = ⊥) : U = ⊥ := by
  have hsub : U ≤ V₂ := by
    intro u hu
    have hproj : h.proj₁ u = 1 := by
      have hmem : h.proj₁ u ∈ U.map h.proj₁ := ⟨u, hu, rfl⟩
      rw [h1] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hspec : h.proj₁ u * h.proj₂ u = u := h.proj_mul' u
    rw [hproj, one_mul] at hspec
    rw [← hspec]
    exact h.proj₂_mem u
  have : U ⊓ V₂ = U := inf_eq_left.2 hsub
  rw [← this, h2]

private theorem XHyp.eq_bot_of_proj₂_eq_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (h1 : U ⊓ V₁ = ⊥) (h2 : U.map h.proj₂ = ⊥) : U = ⊥ := by
  have hsub : U ≤ V₁ := by
    intro u hu
    have hproj : h.proj₂ u = 1 := by
      have hmem : h.proj₂ u ∈ U.map h.proj₂ := ⟨u, hu, rfl⟩
      rw [h2] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hspec : h.proj₁ u * h.proj₂ u = u := h.proj_mul' u
    rw [hproj, mul_one] at hspec
    rw [← hspec]
    exact h.proj₁_mem u
  have : U ⊓ V₁ = U := inf_eq_left.2 hsub
  rw [← this, h1]

private theorem XHyp.eq_V₂_of_inf₁_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (h1 : U ⊓ V₁ = ⊥) (h2 : U ⊓ V₂ = V₂) : U = V₂ := by
  have hV₂U : V₂ ≤ U := by
    intro x hx
    have := hx
    rw [← h2] at this
    exact this.1
  apply le_antisymm _ hV₂U
  intro x hx
  letI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  have hxsup : x ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; exact Subgroup.mem_top x
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := V₁) (t := V₂)).1 hxsup
  rw [← hab]
  have hbU : b ∈ U := by
    have := hb
    rw [← h2] at this
    exact this.1
  have haU : a ∈ U := by
    have h := U.mul_mem (hab ▸ hx) (U.inv_mem hbU)
    rwa [mul_inv_cancel_right] at h
  have ha1 : a = 1 := by
    have hmem : a ∈ U ⊓ V₁ := ⟨haU, ha⟩
    rw [h1] at hmem
    exact Subgroup.mem_bot.1 hmem
  simpa [ha1] using hb

private theorem XHyp.eq_V₁_of_inf₂_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (h1 : U ⊓ V₁ = V₁) (h2 : U ⊓ V₂ = ⊥) : U = V₁ := by
  have hV₁U : V₁ ≤ U := by
    intro x hx
    have := hx
    rw [← h1] at this
    exact this.1
  apply le_antisymm _ hV₁U
  intro x hx
  letI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  have hxsup : x ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; exact Subgroup.mem_top x
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := V₁) (t := V₂)).1 hxsup
  rw [← hab]
  have haU : a ∈ U := by
    have := ha
    rw [← h1] at this
    exact this.1
  have hbU : b ∈ U := by
    have h := U.mul_mem (U.inv_mem haU) (hab ▸ hx)
    rwa [inv_mul_cancel_left] at h
  have hb1 : b = 1 := by
    have hmem : b ∈ U ⊓ V₂ := ⟨hbU, hb⟩
    rw [h2] at hmem
    exact Subgroup.mem_bot.1 hmem
  simpa [hb1] using ha

private theorem XHyp.eq_top_of_inf_eq (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (h1 : U ⊓ V₁ = V₁) (h2 : U ⊓ V₂ = V₂) : U = ⊤ := by
  have hV₁U : V₁ ≤ U := by
    intro x hx
    have := hx
    rw [← h1] at this
    exact this.1
  have hV₂U : V₂ ≤ U := by
    intro x hx
    have := hx
    rw [← h2] at this
    exact this.1
  exact top_le_iff.mp (by rw [← h.sup_eq_top]; exact sup_le hV₁U hV₂U)


private theorem XHyp.graph_case (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U)
    (h1 : U ⊓ V₁ = ⊥) (h2 : U ⊓ V₂ = ⊥)
    (hP₁ : U.map h.proj₁ = V₁) (hP₂ : U.map h.proj₂ = V₂) :
    ∀ v : V, v ∈ U ↔ ρ z v = v := by
  letI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  let π : U →* ↥V₁ := h.proj₁'.comp U.subtype
  have hπsurj : Function.Surjective π := by
    intro x
    have hx : (x : V) ∈ U.map h.proj₁ := by rw [hP₁]; exact x.2
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 hx
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    exact hux
  have hπinj : Function.Injective π := by
    intro u v huv
    have h1' : π (u * v⁻¹) = 1 := by
      rw [map_mul, huv]
      simp
    have h2' : h.proj₁ ((u * v⁻¹ : U) : V) = 1 := congrArg Subtype.val h1'
    have hspec : h.proj₁ ((u * v⁻¹ : U) : V) * h.proj₂ ((u * v⁻¹ : U) : V) =
        ((u * v⁻¹ : U) : V) := h.proj_mul' _
    rw [h2', one_mul] at hspec
    have hmem₂ : ((u * v⁻¹ : U) : V) ∈ V₂ := by
      rw [← hspec]
      exact h.proj₂_mem _
    have hmem : ((u * v⁻¹ : U) : V) ∈ U ⊓ V₂ := ⟨(u * v⁻¹).2, hmem₂⟩
    rw [h2] at hmem
    have hone : ((u * v⁻¹ : U) : V) = 1 := Subgroup.mem_bot.1 hmem
    exact mul_inv_eq_one.mp (Subtype.ext hone)
  let eU : U ≃* ↥V₁ := MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  let φ : ↥V₁ →* ↥V₂ := ((h.proj₂').comp U.subtype).comp eU.symm.toMonoidHom
  have hφe : ∀ u : U, φ (eU u) = h.proj₂' (u : V) := by
    intro u
    change ((h.proj₂').comp U.subtype) (eU.symm (eU u)) = h.proj₂' (u : V)
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hφcomm : ∀ (q : X) (hq : q ∈ ⁅Q, Q⁆) (x : ↥V₁),
      φ (⟨ρ q (x : V), h.apply_mem₁ (Subgroup.commutator_le_self Q hq) x.2⟩) =
        (⟨ρ q ((φ x) : V),
          h.apply_mem₂ (Subgroup.commutator_le_self Q hq) (φ x).2⟩ : ↥V₂) := by
    intro q hq x
    obtain ⟨u, rfl⟩ := eU.surjective x
    let u' : U := ⟨ρ q (u : V), hU q hq (u : V) u.2⟩
    have heU' : eU u' = (⟨ρ q ((eU u : V)),
        h.apply_mem₁ (Subgroup.commutator_le_self Q hq) (eU u).2⟩ : ↥V₁) := by
      apply Subtype.ext
      change ((h.proj₁' (ρ q (u : V)) : ↥V₁) : V) = ρ q ((eU u : V))
      rw [h.proj₁_comm (Subgroup.commutator_le_self Q hq) (u : V)]
      rfl
    have h1' : φ (eU u') = h.proj₂' (u' : V) := hφe u'
    have h2' : φ (eU u) = h.proj₂' (u : V) := hφe u
    rw [heU'] at h1'
    rw [h1']
    show h.proj₂' (ρ q (u : V)) = _
    rw [h.proj₂_comm (Subgroup.commutator_le_self Q hq) (u : V)]
    rw [← h2']
  let ψ : ↥V₁ →* ↥V₁ :=
    { toFun := fun x => ⟨ρ z ((φ x) : V), h.swap₂ (φ x).2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hψcomm : ∀ g ∈ ⁅Q₁, Q₁⁆, ∀ a, ψ ((g : MulAut ↥V₁) a) = (g : MulAut ↥V₁) (ψ a) := by
    intro g hg a
    let g₁ : ↥Q₁ := ⟨g, Subgroup.commutator_le_self Q₁ hg⟩
    let q : ↥Q := h.resEquiv.symm g₁
    have hres : h.resEquiv q = g₁ := MulEquiv.apply_symm_apply h.resEquiv g₁
    have hval : ((h.resEquiv q : MulAut ↥V₁)) = g := congrArg Subtype.val hres
    have hqmem : ((h.resEquiv q : MulAut ↥V₁)) ∈ ⁅Q₁, Q₁⁆ := by rw [hval]; exact hg
    have hq : (q : X) ∈ ⁅Q, Q⁆ := (h.resEquiv_mem_commutator_iff q).1 hqmem
    have hqQ : (q : X) ∈ Q := Subgroup.commutator_le_self Q hq
    have hga : (((g : MulAut ↥V₁) a : ↥V₁) : V) = ρ q (a : V) := by
      rw [show (g : MulAut ↥V₁) = (h.resEquiv q : MulAut ↥V₁) from hval.symm]
      exact h.resEquiv_apply q a
    have haeq : (⟨ρ q (a : V), h.apply_mem₁ hqQ a.2⟩ : ↥V₁) = (g : MulAut ↥V₁) a := by
      apply Subtype.ext
      exact hga.symm
    have hcomm := hφcomm q hq a
    apply Subtype.ext
    change ρ z ((φ ((g : MulAut ↥V₁) a)) : V) = ((g : MulAut ↥V₁) (ψ a) : V)
    rw [← haeq, hcomm]
    have hgψ : ((g : MulAut ↥V₁) (ψ a) : V) = ρ q ((ψ a : ↥V₁) : V) := by
      rw [show (g : MulAut ↥V₁) = (h.resEquiv q : MulAut ↥V₁) from hval.symm]
      exact h.resEquiv_apply q (ψ a)
    rw [hgψ]
    show ρ z (ρ q ((φ a) : V)) = ρ q (ρ z ((φ a) : V))
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, h.rho_comm hqQ]
  have hψid : ψ = MonoidHom.id ↥V₁ := by
    rcases h.module.endo_derived ψ hψcomm with hψ1 | hψid
    · exfalso
      have hφ1 : ∀ x : ↥V₁, φ x = 1 := by
        intro x
        have hψx : ψ x = 1 := by rw [hψ1]; rfl
        have hval : ρ z ((φ x) : V) = 1 := congrArg (fun y : ↥V₁ => (y : V)) hψx
        have h2' := congrArg (fun w : V => ρ z w) hval
        simpa [h.rho_z_apply_apply] using h2'
      have hUsub : U ≤ V₁ := by
        intro u hu
        have hspec : h.proj₁ u * h.proj₂ u = u := h.proj_mul' u
        have h2u : h.proj₂ u = 1 := by
          have hφu := hφe ⟨u, hu⟩
          rw [hφ1] at hφu
          exact congrArg Subtype.val hφu.symm
        rw [h2u, mul_one] at hspec
        rw [← hspec]
        exact h.proj₁_mem u
      have hUbot : U = ⊥ := by
        have : U ⊓ V₁ = U := inf_eq_left.2 hUsub
        rw [← this, h1]
      have hV₁bot : V₁ = ⊥ := by
        rw [← hP₁, hUbot]
        simp
      have hcard : Nat.card ↥V₁ = 1 := by rw [hV₁bot]; exact Subgroup.card_bot
      rw [h.module.card] at hcard
      norm_num at hcard
    · exact hψid
  have hφeq : ∀ x : ↥V₁, φ x = ⟨ρ z (x : V), (h.swap (x : V)).1 x.2⟩ := by
    intro x
    have hψx : ψ x = x := by rw [hψid]; rfl
    have hval : ρ z ((φ x) : V) = (x : V) := congrArg (fun y : ↥V₁ => (y : V)) hψx
    have h2' := congrArg (fun w : V => ρ z w) hval
    have h3 : ((φ x) : V) = ρ z (x : V) := by
      simpa [h.rho_z_apply_apply] using h2'
    exact Subtype.ext h3
  intro v
  constructor
  · intro hv
    have hspec : h.proj₁ v * h.proj₂ v = v := h.proj_mul' v
    have hb : h.proj₂ v = ρ z (h.proj₁ v) := by
      have hφv := hφe ⟨v, hv⟩
      have h1' : φ (h.proj₁' v) = h.proj₂' v := hφv
      rw [hφeq (h.proj₁' v)] at h1'
      exact congrArg Subtype.val h1'.symm
    rw [← hspec, hb, map_mul]
    rw [h.rho_z_apply_apply]
    exact mul_comm' _ _
  · intro hv
    have hxsup : v ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; exact Subgroup.mem_top v
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := V₁) (t := V₂)).1 hxsup
    let p : ↥V₁ × ↥V₂ := (⟨a, ha⟩, ⟨b, hb⟩)
    have hp : (p.1 : V) * (p.2 : V) = v := hab
    have hdec : h.decEquiv v = p := h.dec_eq hp
    have ha₂ : ρ z a ∈ V₂ := (h.swap a).1 ha
    have hb₁ : ρ z b ∈ V₁ := h.swap₂ hb
    let qp : ↥V₁ × ↥V₂ := (⟨ρ z b, hb₁⟩, ⟨ρ z a, ha₂⟩)
    have hqp : (qp.1 : V) * (qp.2 : V) = ρ z v := by
      show ρ z b * ρ z a = ρ z v
      rw [← map_mul, mul_comm' b a, hab]
    have hdecq : h.decEquiv (ρ z v) = qp := h.dec_eq hqp
    have hpq : p = qp := by
      rw [← hdec]
      rw [← hdecq, hv]
    have hb_eq : b = ρ z a := congrArg (fun r : ↥V₁ × ↥V₂ => (r.2 : V)) hpq
    have hamap : a ∈ U.map h.proj₁ := by rw [hP₁]; exact ha
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.1 hamap
    have heUu : eU ⟨u, hu⟩ = (⟨a, ha⟩ : ↥V₁) := by
      apply Subtype.ext
      exact hua
    have hφu := hφe ⟨u, hu⟩
    rw [heUu] at hφu
    have hφa := hφeq (⟨a, ha⟩ : ↥V₁)
    rw [hφa] at hφu
    have hproj₂u : h.proj₂ u = ρ z a := congrArg Subtype.val hφu.symm
    rw [← hab, hb_eq, ← hproj₂u, ← hua, h.proj_mul' u]
    exact hu

theorem XHyp.invariant_cases (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {U : Subgroup V}
    (hU : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ U, ρ g u ∈ U) :
    U = ⊥ ∨ U = V₁ ∨ U = V₂ ∨ (∀ v : V, v ∈ U ↔ ρ z v = v) ∨ U = ⊤ := by
  rcases h.inf₁_cases hU with h1 | h1 <;> rcases h.inf₂_cases hU with h2 | h2
  · have hc₁ := h.proj₁_map_cases hU
    have hc₂ := h.proj₂_map_cases hU
    rcases hc₁ with hP₁ | hP₁
    · exact Or.inl (h.eq_bot_of_proj₁_eq_bot h2 hP₁)
    rcases hc₂ with hP₂ | hP₂
    · exact Or.inl (h.eq_bot_of_proj₂_eq_bot h1 hP₂)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h.graph_case hU h1 h2 hP₁ hP₂))))
  · exact Or.inr (Or.inr (Or.inl (h.eq_V₂_of_inf₁_bot h1 h2)))
  · exact Or.inr (Or.inl (h.eq_V₁_of_inf₂_bot h1 h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h.eq_top_of_inf_eq h1 h2))))



end CFSG.EvenSporadicStandard.Co2Std.Exclusion

