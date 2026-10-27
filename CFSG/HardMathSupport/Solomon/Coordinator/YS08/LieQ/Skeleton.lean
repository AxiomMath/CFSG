module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Basic
public import CFSG.LieType.ChevTwo.ReductionsTits

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

@[expose] def IsRadical (q : ℕ) {S : Type*} [Group S] (R : Subgroup S) : Prop :=
  R ≠ ⊥ ∧ IsPGroup q R ∧ pCoreOf q (Subgroup.normalizer (R : Set S)) = R ∧
    Subgroup.normalizer (R : Set S) ≠ ⊤

@[expose] def RadRigidInner (q : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ R : Subgroup S, IsRadical q R → ∀ x : S, (∀ r ∈ R, x * r = r * x) →
    Nat.Coprime (orderOf x) q → x = 1

@[expose] def RadRigid (q : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ R : Subgroup S, IsRadical q R → ∀ α : MulAut S, (∀ r ∈ R, α r = r) →
    Nat.Coprime (orderOf α) q → α = 1

variable {q : ℕ} [Fact q.Prime]

theorem IsRadical.map_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    {R : Subgroup S} (hR : IsRadical q R) : IsRadical q (R.map e.toMonoidHom) := by
  obtain ⟨h0, hp, hc, hn⟩ := hR
  refine ⟨?_, hp.map _, ?_, ?_⟩
  · intro hb
    apply h0
    exact (Subgroup.map_eq_bot_iff_of_injective R e.injective).1 hb
  · rw [← Subgroup.map_equiv_normalizer_eq, pCoreOf_map_mulEquiv, hc]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    intro htop
    apply hn
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by ext x; simp
    rw [hid, Subgroup.map_id] at this
    rw [this]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective

theorem RadRigidInner.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : RadRigidInner q S) : RadRigidInner q S' := by
  intro R' hR' x hx hxo
  have hR : IsRadical q (R'.map e.symm.toMonoidHom) := hR'.map_mulEquiv e.symm
  have h1 : e.symm x = 1 := by
    refine h _ hR (e.symm x) ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
      exact hx r hr
    · rwa [MulEquiv.orderOf_eq]
  exact (MulEquiv.map_eq_one_iff e.symm).1 h1

theorem RadRigid.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : RadRigid q S) : RadRigid q S' := by
  intro R' hR' α hα hαo
  have hR : IsRadical q (R'.map e.symm.toMonoidHom) := hR'.map_mulEquiv e.symm
  have hβ : (MulAut.congr e.symm) α = 1 := by
    refine h _ hR _ ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      show e.symm (α (e (e.symm r))) = e.symm r
      rw [MulEquiv.apply_symm_apply, hα r hr]
    · rwa [MulEquiv.orderOf_eq]
  exact (MulEquiv.map_eq_one_iff (MulAut.congr e.symm)).1 hβ

section Core

variable {H : Type} [Group H] [Finite H]

theorem mem_normalizer_of_normal (S : Subgroup H) [S.Normal] (h : H) :
    h ∈ Subgroup.normalizer (S : Set H) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top h

theorem map_normalizerMonoidHom_eq (S : Subgroup H) [S.Normal] {Q : Subgroup H} (hQS : Q ≤ S)
    {h : H} (hh : h ∈ Subgroup.normalizer (Q : Set H)) :
    (Q.subgroupOf S).map
      (S.normalizerMonoidHom ⟨h, mem_normalizer_of_normal S h⟩).toMonoidHom = Q.subgroupOf S := by
  have hconj : ∀ s : ↥S, ((S.normalizerMonoidHom ⟨h, mem_normalizer_of_normal S h⟩ s : ↥S) : H) =
      h * s * h⁻¹ := fun s => rfl
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : (t : H) ∈ Q := ht
    have := (Subgroup.mem_normalizer_iff.1 hh (t : H)).1 ht'
    show ((S.normalizerMonoidHom ⟨h, mem_normalizer_of_normal S h⟩ t : ↥S) : H) ∈ Q
    rw [hconj]
    exact this
  · intro hx
    have hx' : (x : H) ∈ Q := hx
    have hhinv : h⁻¹ ∈ Subgroup.normalizer (Q : Set H) := inv_mem hh
    have h1 : h⁻¹ * (x : H) * h⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hhinv (x : H)).1 hx'
    have h1S : h⁻¹ * (x : H) * h⁻¹⁻¹ ∈ S := hQS h1
    refine ⟨⟨h⁻¹ * (x : H) * h⁻¹⁻¹, h1S⟩, h1, ?_⟩
    apply Subtype.ext
    show h * (h⁻¹ * (x : H) * h⁻¹⁻¹) * h⁻¹ = x
    group

theorem lieQ_core (S : Subgroup H) [S.Normal] (hBT : HoldsTits ↥S q)
    (hcent : ∀ R : Subgroup ↥S, IsRadical q R → ∀ x : H,
      (∀ r ∈ R, x * (r : H) = (r : H) * x) → Nat.Coprime (orderOf x) q → x = 1)
    {Q : Subgroup H} (hQS : Q ≤ S) (hQ : Q ≠ ⊥) (hQp : IsPGroup q ↥Q) :
    ∀ h ∈ Subgroup.normalizer (Q : Set H),
      (∀ r ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)), h * r = r * h) →
      h ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)) := by
  classical
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Subgroup ↥S, Q' = Q.subgroupOf S := ⟨_, rfl⟩
  have hQQ' : Q = Q'.map S.subtype := by
    rw [hQ']
    exact (Subgroup.map_subgroupOf_eq_of_le hQS).symm
  have hQ'p : IsPGroup q ↥Q' := by
    rw [hQ']
    exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQS).symm
  have hQ'ne : Q' ≠ ⊥ := by
    intro hb
    apply hQ
    rw [hQQ', hb, Subgroup.map_bot]
  obtain ⟨hle, hRp, -, hnetop, hcore, -⟩ := canonical_parabolic_tits hBT hQ'ne hQ'p
  obtain ⟨R', hR'⟩ : ∃ R' : Subgroup ↥S, R' = radInf q Q' := ⟨_, rfl⟩
  rw [← hR'] at hle hRp hnetop hcore
  have hR'ne : R' ≠ ⊥ := fun hb => hQ'ne (le_bot_iff.1 (hb ▸ hle))
  have hrad : IsRadical q R' := ⟨hR'ne, hRp, hcore, hnetop⟩
  obtain ⟨RH, hRH⟩ : ∃ RH : Subgroup H, RH = R'.map S.subtype := ⟨_, rfl⟩
  have hRHp : IsPGroup q ↥RH := by
    rw [hRH]
    exact hRp.map _
  have hQRH : Q ≤ RH := by
    rw [hQQ', hRH]
    exact Subgroup.map_mono hle
  have hmemRH : ∀ r ∈ R', (r : H) ∈ RH := fun r hr => by
    rw [hRH]
    exact ⟨r, hr, rfl⟩
  have hconj : ∀ h ∈ Subgroup.normalizer (Q : Set H), ∀ r ∈ RH, h * r * h⁻¹ ∈ RH := by
    intro h hh r hr
    rw [hRH] at hr
    obtain ⟨ρ, hρ, rfl⟩ := hr
    have hQe := map_normalizerMonoidHom_eq S hQS hh
    rw [← hQ'] at hQe
    have hRe := radInf_map_eq (p := q) (S.normalizerMonoidHom ⟨h, mem_normalizer_of_normal S h⟩ :
      MulAut ↥S) hQe
    rw [← hR'] at hRe
    have h1 : (S.normalizerMonoidHom ⟨h, mem_normalizer_of_normal S h⟩ ρ : ↥S) ∈ R' := by
      rw [← hRe]
      exact ⟨ρ, hρ, rfl⟩
    have h2 := hmemRH _ h1
    exact h2
  have hNM : Subgroup.normalizer (Q : Set H) ≤ Subgroup.normalizer (RH : Set H) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hconj h hh y hy
    · intro hy
      have hhinv : h⁻¹ ∈ Subgroup.normalizer (Q : Set H) := inv_mem hh
      have := hconj h⁻¹ hhinv _ hy
      simpa [mul_assoc] using this
  obtain ⟨M, hM⟩ : ∃ M : Subgroup H, M = Subgroup.normalizer (RH : Set H) := ⟨_, rfl⟩
  have hRHM : RH ≤ pCoreOf q M := by
    rw [hM]
    exact le_pCoreOf_of_le_normalizer q Subgroup.le_normalizer le_rfl hRHp
  have hMc : ∀ x ∈ M, (∀ r ∈ pCoreOf q M, x * r = r * x) → x ∈ pCoreOf q M := by
    refine centralizer_pCoreOf_le M ?_
    intro x _ hxc hxo
    exact hcent R' hrad x (fun r hr => hxc _ (hRHM (hmemRH r hr))) hxo
  exact constrained_normalizer_of_le_core M hMc (hQRH.trans hRHM) (hM ▸ hNM)

theorem lieQ_of_radRigid (S : Subgroup H) [S.Normal] (hBT : HoldsTits ↥S q)
    (hRR : RadRigid q ↥S) (hC : Subgroup.centralizer (S : Set H) = ⊥)
    {Q : Subgroup H} (hQS : Q ≤ S) (hQ : Q ≠ ⊥) (hQp : IsPGroup q ↥Q) :
    ∀ h ∈ Subgroup.normalizer (Q : Set H),
      (∀ r ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)), h * r = r * h) →
      h ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)) := by
  refine lieQ_core S hBT ?_ hQS hQ hQp
  intro R hR x hx hxo
  obtain ⟨α, hα⟩ : ∃ α : MulAut ↥S,
      α = S.normalizerMonoidHom ⟨x, mem_normalizer_of_normal S x⟩ := ⟨_, rfl⟩
  have hαc : ∀ s : ↥S, ((α s : ↥S) : H) = x * s * x⁻¹ := fun s => by rw [hα]; rfl
  have hfix : ∀ r ∈ R, α r = r := by
    intro r hr
    apply Subtype.ext
    rw [hαc, hx r hr]
    group
  have hord : Nat.Coprime (orderOf α) q := by
    refine Nat.Coprime.coprime_dvd_left ?_ hxo
    have h1 := orderOf_map_dvd S.normalizerMonoidHom
      (⟨x, mem_normalizer_of_normal S x⟩ : ↥(Subgroup.normalizer (S : Set H)))
    have h2 : orderOf (⟨x, mem_normalizer_of_normal S x⟩ : ↥(Subgroup.normalizer (S : Set H))) =
        orderOf x := (Subgroup.orderOf_coe _).symm
    rw [h2, ← hα] at h1
    exact h1
  have h1 : α = 1 := hRR R hR α hfix hord
  have hxS : x ∈ Subgroup.centralizer (S : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := congrArg (fun β : MulAut ↥S => ((β ⟨s, hs⟩ : ↥S) : H)) h1
    simp only [MulAut.one_apply] at this
    rw [hαc] at this
    have h3 : x * s * x⁻¹ = s := this
    calc s * x = (x * s * x⁻¹) * x := by rw [h3]
      _ = x * s := by group
  rw [hC, Subgroup.mem_bot] at hxS
  exact hxS

end Core

theorem lieQ_inner_of_radRigidInner {S : Type} [Group S] [Finite S] (hBT : HoldsTits S q)
    (hRR : RadRigidInner q S) {Q : Subgroup S} (hQ : Q ≠ ⊥) (hQp : IsPGroup q ↥Q) :
    ∀ h ∈ Subgroup.normalizer (Q : Set S),
      (∀ r ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)), h * r = r * h) →
      h ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)) := by
  obtain ⟨hle, hRp, hnorm, hnetop, hcore, -⟩ := canonical_parabolic_tits hBT hQ hQp
  obtain ⟨R, hR⟩ : ∃ R : Subgroup S, R = radInf q Q := ⟨_, rfl⟩
  rw [← hR] at hle hRp hnorm hnetop hcore
  have hRne : R ≠ ⊥ := fun hb => hQ (le_bot_iff.1 (hb ▸ hle))
  have hrad : IsRadical q R := ⟨hRne, hRp, hcore, hnetop⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup S, M = Subgroup.normalizer (R : Set S) := ⟨_, rfl⟩
  have hRM : R ≤ pCoreOf q M := by
    rw [hM]
    exact le_pCoreOf_of_le_normalizer q Subgroup.le_normalizer le_rfl hRp
  have hMc : ∀ x ∈ M, (∀ r ∈ pCoreOf q M, x * r = r * x) → x ∈ pCoreOf q M := by
    refine centralizer_pCoreOf_le M ?_
    intro x _ hxc hxo
    exact hRR R hrad x (fun r hr => hxc _ (hRM hr)) hxo
  exact constrained_normalizer_of_le_core M hMc (hle.trans hRM) (hM ▸ hnorm)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
