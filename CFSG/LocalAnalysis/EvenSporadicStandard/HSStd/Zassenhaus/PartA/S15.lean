module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Abstract

variable {S : Type*} [Group S] {Q : Type*} [Group Q]

theorem exists_conj_lift (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (π : Q →* MulAut S) (hπ : Function.Injective π)
    (hr : π.range = (MulAut.conj : S →* MulAut S).range) (b : MulAut Q) :
    ∃ x : MulAut S, (b * b = 1 → x * x = 1) ∧ ∀ q, x * π q * x⁻¹ = π (b q) := by
  have hex : ∀ s : S, ∃ q : Q, π q = MulAut.conj s := fun s => by
    have : (MulAut.conj s : MulAut S) ∈ π.range := by rw [hr]; exact ⟨s, rfl⟩
    exact this
  choose f hf using hex
  have hmul : ∀ s s' : S, f (s * s') = f s * f s' := by
    intro s s'
    apply hπ
    rw [hf, map_mul, map_mul, hf, hf]
  have hfinj : Function.Injective f := by
    intro s s' h
    apply hinj
    rw [← hf, ← hf, h]
  have hfsurj : Function.Surjective f := by
    intro q
    have : π q ∈ (MulAut.conj : S →* MulAut S).range := by rw [← hr]; exact ⟨q, rfl⟩
    obtain ⟨s, hs⟩ := this
    refine ⟨s, hπ ?_⟩
    rw [hf]
    exact hs
  let F : S ≃* Q := MulEquiv.ofBijective (MonoidHom.mk' f hmul) ⟨hfinj, hfsurj⟩
  have hF : ∀ s, F s = f s := fun s => rfl
  let ψ : MulAut S := F.trans (b.trans F.symm)
  have hψ : ∀ s, ψ s = F.symm (b (F s)) := fun s => rfl
  refine ⟨ψ, fun hbb => ?_, fun q => ?_⟩
  · ext s
    rw [MulAut.mul_apply, hψ, hψ, MulEquiv.apply_symm_apply]
    have : b (b (F s)) = F s := by
      have := congrArg (fun c : MulAut Q => c (F s)) hbb
      simpa using this
    rw [this, MulEquiv.symm_apply_apply]
    rfl
  · obtain ⟨s, rfl⟩ := F.surjective q
    have h1 : π (F s) = MulAut.conj s := hf s
    have h2 : F (ψ s) = b (F s) := by rw [hψ, MulEquiv.apply_symm_apply]
    rw [h1, mul_conj_mul_inv, ← hf, ← hF, h2]

end Abstract

section Diag

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup G}
    (h : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, g = a * b := by
  let T : Subgroup G :=
    { carrier := {g | ∃ a ∈ H, ∃ b ∈ K, g = a * b}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
        have := h a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
        have hc : Commute a b := h a ha b hb
        rw [mul_inv_rev]
        exact hc.inv_inv.eq.symm }
  have hle : H ⊔ K ≤ T := sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩)
    (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem mem_normalizer_of_map_eq {K : Subgroup G} {x : G}
    (h : K.map (MulAut.conj x).toMonoidHom = K) : x ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have : w = y := by
      have h2 : MulAut.conj x w = MulAut.conj x y := by simpa [MulAut.conj_apply] using hwy
      exact (MulAut.conj x).injective h2
    rwa [← this]

end Diag

section Core

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def diagHomOf (K : Subgroup G) (t : G) (hc : ∀ x ∈ K, ∀ y ∈ K, Commute x (t * y * t⁻¹)) :
    ↥K →* G where
  toFun l := (l : G) * (t * l * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h : Commute (b : G) (t * a * t⁻¹) := hc b b.2 a a.2
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h.eq]
      _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group

theorem diagHomOf_apply (K : Subgroup G) (t : G) (hc : ∀ x ∈ K, ∀ y ∈ K, Commute x (t * y * t⁻¹))
    (l : ↥K) : diagHomOf K t hc l = (l : G) * (t * l * t⁻¹) := rfl

theorem PA14.eq_one_of_mem_conj (a : PA14 L t E z) {g : G} (hg : g ∈ a.L₁)
    (hgt : g ∈ conjSub t a.L₁) : g = 1 := by
  obtain ⟨y, hy, hyg⟩ := hgt
  have hyg' : t * y * t⁻¹ = g := by simpa [MulAut.conj_apply] using hyg
  have hmem : (⟨g, hg⟩ : ↥a.L₁) ∈ center ↥a.L₁ := by
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hyg']
    exact (a.L₁_comm k k.2 y hy).eq
  rw [a.Z_triv, mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

theorem diagHomOf_injective (a : PA14 L t E z) :
    Function.Injective (diagHomOf a.L₁ t a.L₁_comm) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hl' : (l : G) * (t * l * t⁻¹) = 1 := hl
  have h1 : (l : G) = (t * l * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hl'
  have h2 : (l : G) ∈ conjSub t a.L₁ := by
    rw [h1]
    exact (conjSub t a.L₁).inv_mem ⟨l, l.2, by simp [MulAut.conj_apply]⟩
  exact Subtype.ext (a.eq_one_of_mem_conj l.2 h2)

open CFSG.QuasithinUnique.Setup.X3Aut in
theorem exists_diag_conj [Finite G] (hb : PAB G L t E W z) (a : PA14 L t E z) (b : MulAut ↥a.L₁)
    (hbb : b * b = 1) :
    ∃ x ∈ a.Abar, x * x = 1 ∧ ∀ l : ↥a.L₁,
      x * diagHomOf a.L₁ t a.L₁_comm l * x⁻¹ = diagHomOf a.L₁ t a.L₁_comm (b l) := by
  have ht2 : t * t = 1 := hb.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set π := diagHomOf a.L₁ t a.L₁_comm with hπdef
  have hπapp : ∀ l : ↥a.L₁, π l = (l : G) * (t * l * t⁻¹) := fun l => rfl
  have hπinj : Function.Injective π := diagHomOf_injective a
  have hL1card : Nat.card ↥a.L₁ = 360 := by
    rw [Nat.card_congr a.eL₁.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hDcard : Nat.card ↥π.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv).symm.trans hL1card
  have hJD : derivedIn a.Abar ≤ π.range := by
    intro g hg
    have hgL : g ∈ L := (a.Abar_le (derivedIn_le a.Abar hg)).1
    have hgt : g * t = t * g := mem_centralizer_iff.1 hb.t_cent g hgL
    obtain ⟨l, hl, k, hk, hgk⟩ := exists_mul_of_mem_sup_of_commute (H := a.L₁)
      (K := conjSub t a.L₁) (fun x hx y hy => by
        obtain ⟨m, hm, rfl⟩ := hy
        exact (a.L₁_comm x hx m hm).eq) (a.J_le hg)
    obtain ⟨k₀, hk₀, hkk⟩ := hk
    have hkk' : k = t * k₀ * t⁻¹ := by rw [← hkk]; simp [MulAut.conj_apply]
    have hg' : t * g * t⁻¹ = g := by rw [mul_inv_eq_iff_eq_mul]; exact hgt.symm
    have e1 : t * g * t⁻¹ = (t * l * t⁻¹) * k₀ := by
      rw [hgk, hkk']
      calc t * (l * (t * k₀ * t⁻¹)) * t⁻¹
          = (t * l * t⁻¹) * ((t * t) * k₀ * (t * t)⁻¹) := by group
        _ = (t * l * t⁻¹) * k₀ := by rw [ht2]; group
    have e2 : l * (t * k₀ * t⁻¹) = (t * l * t⁻¹) * k₀ := by
      rw [← e1, hg', hgk, hkk']
    have hc : k₀ * (t * l * t⁻¹) = (t * l * t⁻¹) * k₀ := (a.L₁_comm k₀ hk₀ l hl).eq
    have e3 : k₀⁻¹ * l = (t * l * t⁻¹) * (t * k₀ * t⁻¹)⁻¹ := by
      calc k₀⁻¹ * l = k₀⁻¹ * (l * (t * k₀ * t⁻¹)) * (t * k₀ * t⁻¹)⁻¹ := by group
        _ = k₀⁻¹ * ((t * l * t⁻¹) * k₀) * (t * k₀ * t⁻¹)⁻¹ := by rw [e2]
        _ = k₀⁻¹ * (k₀ * (t * l * t⁻¹)) * (t * k₀ * t⁻¹)⁻¹ := by rw [hc]
        _ = (t * l * t⁻¹) * (t * k₀ * t⁻¹)⁻¹ := by group
    have h1 : k₀⁻¹ * l ∈ a.L₁ := a.L₁.mul_mem (a.L₁.inv_mem hk₀) hl
    have h2 : k₀⁻¹ * l ∈ conjSub t a.L₁ := by
      rw [e3]
      exact (conjSub t a.L₁).mul_mem ⟨l, hl, by simp [MulAut.conj_apply]⟩
        ((conjSub t a.L₁).inv_mem ⟨k₀, hk₀, by simp [MulAut.conj_apply]⟩)
    have h3 := a.eq_one_of_mem_conj h1 h2
    have hlk : l = k₀ := by
      have := inv_mul_eq_one.1 h3
      exact this.symm
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hπapp, hgk, hkk']
    simp only
    rw [hlk]
  have hperf : _root_.commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hIc : (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤
      _root_.commutator (MulAut (alternatingGroup (Fin 6))) := by
    set I := (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range
      with hI
    have hII : I = ⁅I, I⁆ := by
      have h1 : I = (⊤ : Subgroup (alternatingGroup (Fin 6))).map
          (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) :=
        MonoidHom.range_eq_map _
      have h2 : ⁅I, I⁆ = ((_root_.commutator (alternatingGroup (Fin 6))).map
          (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6)))) := by
        rw [_root_.commutator_def, Subgroup.map_commutator, ← h1]
      rw [h2, hperf, ← h1]
    rw [hII, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hIcard : Nat.card ↥(MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range = 360 := by
    have h1 := Subgroup.card_mul_index (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range
    rw [index_inner_alt6, card_mulAut_alt6] at h1
    omega
  have hMc : (_root_.commutator ↥a.Abar).map a.eAbar.toMonoidHom =
      _root_.commutator (MulAut (alternatingGroup (Fin 6))) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ a.eAbar.surjective]
  have hJcard : Nat.card ↥(derivedIn a.Abar) = Nat.card ↥(_root_.commutator ↥a.Abar) :=
    Subgroup.card_map_of_injective a.Abar.subtype_injective
  have hMccard : Nat.card ↥(_root_.commutator (MulAut (alternatingGroup (Fin 6)))) =
      Nat.card ↥(_root_.commutator ↥a.Abar) := by
    rw [← hMc]
    exact Subgroup.card_map_of_injective a.eAbar.injective
  have hn : Nat.card ↥(derivedIn a.Abar) = 360 := by
    apply le_antisymm
    · rw [← hDcard]; exact Subgroup.card_le_of_le hJD
    · rw [hJcard, ← hMccard, ← hIcard]; exact Subgroup.card_le_of_le hIc
  have hJDeq : derivedIn a.Abar = π.range :=
    Subgroup.eq_of_le_of_card_ge hJD (by rw [hDcard, hn])
  have hMcI : _root_.commutator (MulAut (alternatingGroup (Fin 6))) =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
    refine (Subgroup.eq_of_le_of_card_ge hIc ?_).symm
    rw [hMccard, ← hJcard, hn, hIcard]
  have hπAbar : ∀ l : ↥a.L₁, π l ∈ a.Abar := fun l =>
    derivedIn_le a.Abar (by rw [hJDeq]; exact ⟨l, rfl⟩)
  have hπcomm : ∀ l : ↥a.L₁, (⟨π l, hπAbar l⟩ : ↥a.Abar) ∈ _root_.commutator ↥a.Abar := by
    intro l
    have : π l ∈ derivedIn a.Abar := by rw [hJDeq]; exact ⟨l, rfl⟩
    obtain ⟨c, hc, hcv⟩ := this
    have : c = ⟨π l, hπAbar l⟩ := Subtype.ext hcv
    rwa [← this]
  let πt : ↥a.L₁ →* MulAut (alternatingGroup (Fin 6)) :=
    a.eAbar.toMonoidHom.comp (π.codRestrict a.Abar hπAbar)
  have hπt : ∀ l, πt l = a.eAbar ⟨π l, hπAbar l⟩ := fun l => rfl
  have hπtinj : Function.Injective πt := by
    intro l m h
    have h1 := a.eAbar.injective h
    exact hπinj (congrArg Subtype.val h1)
  have hπtle : πt.range ≤ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range := by
    rw [← hMcI, ← hMc]
    rintro _ ⟨l, rfl⟩
    exact ⟨⟨π l, hπAbar l⟩, hπcomm l, (hπt l).symm⟩
  have hπtcard : Nat.card ↥πt.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hπtinj).toEquiv).symm.trans hL1card
  have hπtr : πt.range = (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range :=
    Subgroup.eq_of_le_of_card_ge hπtle (by rw [hπtcard, hIcard])
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnab : ∃ x y : alternatingGroup (Fin 6), x * y ≠ y * x := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
    intro h
    have := congrArg Subtype.val h
    revert this
    decide
  obtain ⟨xb, hxb2, hxb⟩ := exists_conj_lift (conj_injective_of_simple hnab) πt hπtinj hπtr b
  refine ⟨((a.eAbar.symm xb : ↥a.Abar) : G), (a.eAbar.symm xb).2, ?_, ?_⟩
  · have h1 : a.eAbar.symm xb * a.eAbar.symm xb = 1 := by
      apply a.eAbar.injective
      rw [map_mul, MulEquiv.apply_symm_apply, map_one]
      exact hxb2 hbb
    simpa using congrArg Subtype.val h1
  · intro l
    have h1 : a.eAbar.symm xb * (⟨π l, hπAbar l⟩ : ↥a.Abar) * (a.eAbar.symm xb)⁻¹ =
        ⟨π (b l), hπAbar (b l)⟩ := by
      apply a.eAbar.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact (hxb l).trans (hπt (b l))
    simpa using congrArg Subtype.val h1

theorem s15 : StepS15 := by
  intro G _ _ L t E W z hb a b hbb _
  obtain ⟨x, hxA, hx2, hxπ⟩ := exists_diag_conj hb a b hbb
  have ht2 : t * t = 1 := hb.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hxLu := a.Abar_le hxA
  have hxL : x ∈ L := hxLu.1
  have hxu : x ∈ centralizer ({a.u} : Set G) := hxLu.2
  have hxt : x * t = t * x := mem_centralizer_iff.1 hb.t_cent x hxL
  have hxt' : t * x * t⁻¹ = x := by rw [mul_inv_eq_iff_eq_mul]; exact hxt.symm
  have hπinj := diagHomOf_injective a
  refine ⟨x, hxL, hxu, hx2, ?_⟩
  rcases a.perm x (by rw [a.ub_eq]; exact hxu) with h | h
  · left
    have hx : x ∈ normalizer (a.L₁ : Set G) := mem_normalizer_of_map_eq h
    refine ⟨hx, ?_⟩
    ext l
    have h1 := congrArg Subtype.val (hπinj (a₁ := conjAutOf a.L₁ hx l) (a₂ := b l) (by
      rw [← hxπ l]
      simp only [diagHomOf_apply, conjAutOf_apply]
      calc x * l * x⁻¹ * (t * (x * l * x⁻¹) * t⁻¹)
          = x * l * x⁻¹ * ((t * x * t⁻¹) * (t * l * t⁻¹) * (t * x * t⁻¹)⁻¹) := by group
        _ = x * (l * (t * l * t⁻¹)) * x⁻¹ := by rw [hxt']; group))
    exact h1
  · right
    have hxt2 : (a.L₁.map (MulAut.conj (x * t)).toMonoidHom) = a.L₁ := by
      have e1 : a.L₁.map (MulAut.conj (x * t)).toMonoidHom =
          (a.L₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        exact (map_conj_map_conj a.L₁ x t).symm
      have e2 : (a.L₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          (a.L₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext y
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have : x * (t * y * t⁻¹) * x⁻¹ = t * (x * y * x⁻¹) * t⁻¹ := by
          calc x * (t * y * t⁻¹) * x⁻¹ = (x * t) * y * (x * t)⁻¹ := by group
            _ = (t * x) * y * (t * x)⁻¹ := by rw [hxt]
            _ = t * (x * y * x⁻¹) * t⁻¹ := by group
        exact this
      rw [e1, e2, h]
      have : (a.L₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = a.L₁ := by
        rw [Subgroup.map_map]
        ext y
        simp only [mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨w, hw, rfl⟩
          have : t * (t * w * t⁻¹) * t⁻¹ = w := by
            calc t * (t * w * t⁻¹) * t⁻¹ = (t * t) * w * (t * t)⁻¹ := by group
              _ = w := by rw [ht2]; group
          rw [this]; exact hw
        · intro hy
          refine ⟨y, hy, ?_⟩
          calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
            _ = y := by rw [ht2]; group
      exact this
    have hx' : x * t ∈ normalizer (a.L₁ : Set G) := mem_normalizer_of_map_eq hxt2
    refine ⟨hx', ?_⟩
    ext l
    have h1 := congrArg Subtype.val (hπinj (a₁ := conjAutOf a.L₁ hx' l) (a₂ := b l) (by
      rw [← hxπ l]
      simp only [diagHomOf_apply, conjAutOf_apply]
      calc x * t * l * (x * t)⁻¹ * (t * (x * t * l * (x * t)⁻¹) * t⁻¹)
          = (x * t * l * (x * t)⁻¹) *
            ((t * x * t⁻¹) * (t * t) * l * (t * t)⁻¹ * (t * x * t⁻¹)⁻¹) := by group
        _ = (x * t * l * t⁻¹ * x⁻¹) * (x * l * x⁻¹) := by rw [hxt', ht2]; group
        _ = x * ((t * l * t⁻¹) * l) * x⁻¹ := by group
        _ = x * (l * (t * l * t⁻¹)) * x⁻¹ := by
          rw [← (a.L₁_comm l l.2 l l.2).eq]))
    exact h1

end Core

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
