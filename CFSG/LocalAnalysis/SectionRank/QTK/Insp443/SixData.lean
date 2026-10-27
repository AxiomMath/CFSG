module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.A6Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentConfig

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31

structure SixData {G : Type} [Group G] (W : Subgroup G) (D : Fin 6 → Subgroup G) : Prop where
  inj : Function.Injective D
  le : ∀ r, D r ≤ W
  perm : ∀ g ∈ Subgroup.normalizer (W : Set G), ∀ r, ∃ s,
    (D r).map (MulAut.conj g).toMonoidHom = D s
  ker : ∀ g ∈ Subgroup.normalizer (W : Set G),
    (∀ r, (D r).map (MulAut.conj g).toMonoidHom = D r) → g ∈ W
  comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  swap : ∃ g ∈ Subgroup.normalizer (W : Set G), ∀ r,
    (D r).map (MulAut.conj g).toMonoidHom = D (Equiv.swap 0 1 r)
  rot : ∃ g ∈ Subgroup.normalizer (W : Set G), ∀ r,
    (D r).map (MulAut.conj g).toMonoidHom = D (finRotate 6 r)

namespace SixData

variable {G : Type} [Group G] [Finite G] {W : Subgroup G} {D : Fin 6 → Subgroup G}
  (hd : SixData W D)

@[expose] noncomputable def sig (g : ↥(Subgroup.normalizer (W : Set G))) (r : Fin 6) : Fin 6 :=
  Classical.choose (hd.perm g g.2 r)

theorem sig_spec (g : ↥(Subgroup.normalizer (W : Set G))) (r : Fin 6) :
    (D r).map (MulAut.conj (g : G)).toMonoidHom = D (hd.sig g r) :=
  Classical.choose_spec (hd.perm g g.2 r)

theorem sig_eq {g : ↥(Subgroup.normalizer (W : Set G))} {r s : Fin 6}
    (h : (D r).map (MulAut.conj (g : G)).toMonoidHom = D s) : hd.sig g r = s :=
  hd.inj (by rw [← hd.sig_spec, h])

theorem map_conj_mul (a b : G) (K : Subgroup G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem sig_mul (g h : ↥(Subgroup.normalizer (W : Set G))) (r : Fin 6) :
    hd.sig (g * h) r = hd.sig g (hd.sig h r) := by
  apply hd.sig_eq
  rw [Subgroup.coe_mul, map_conj_mul, hd.sig_spec h r, hd.sig_spec g]

theorem sig_one (r : Fin 6) : hd.sig 1 r = r := by
  apply hd.sig_eq
  rw [Subgroup.coe_one]
  convert Subgroup.map_id (D r)
  ext x
  simp

@[expose] noncomputable def psi : ↥(Subgroup.normalizer (W : Set G)) →* Equiv.Perm (Fin 6) where
  toFun g :=
    { toFun := hd.sig g
      invFun := hd.sig g⁻¹
      left_inv := fun r => by rw [← hd.sig_mul, inv_mul_cancel, hd.sig_one]
      right_inv := fun r => by rw [← hd.sig_mul, mul_inv_cancel, hd.sig_one] }
  map_one' := Equiv.ext fun r => hd.sig_one r
  map_mul' g h := Equiv.ext fun r => hd.sig_mul g h r

theorem psi_apply (g : ↥(Subgroup.normalizer (W : Set G))) (r : Fin 6) :
    hd.psi g r = hd.sig g r := rfl

theorem psi_eq_one_iff (g : ↥(Subgroup.normalizer (W : Set G))) :
    hd.psi g = 1 ↔ (g : G) ∈ W := by
  constructor
  · intro h1
    refine hd.ker g g.2 fun r => ?_
    have := hd.sig_spec g r
    rwa [← psi_apply, h1, Equiv.Perm.one_apply] at this
  · intro hg
    refine Equiv.ext fun r => hd.sig_eq ?_
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hc := hd.comm _ hg _ (hd.le r hy)
      simpa [MulAut.conj_apply, hc, mul_assoc] using hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      have hc := hd.comm _ hg _ (hd.le r hx)
      simp [MulAut.conj_apply, hc, mul_assoc]

theorem psi_surjective : Function.Surjective hd.psi := by
  rw [← MonoidHom.range_eq_top]
  obtain ⟨g₁, hg₁, h₁⟩ := hd.swap
  obtain ⟨g₂, hg₂, h₂⟩ := hd.rot
  have e₁ : hd.psi ⟨g₁, hg₁⟩ = Equiv.swap 0 1 :=
    Equiv.ext fun r => hd.sig_eq (h₁ r)
  have e₂ : hd.psi ⟨g₂, hg₂⟩ = finRotate 6 :=
    Equiv.ext fun r => hd.sig_eq (h₂ r)
  have hcl := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 4))
    (support_finRotate (n := 4)) 0
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro σ (rfl | rfl)
  · exact ⟨_, e₂⟩
  · refine ⟨⟨g₁, hg₁⟩, ?_⟩
    rw [e₁]
    rfl

end SixData

theorem KConfig.conclK_of_sixData {G : Type} [Group G] [Finite G] {L V MK : Subgroup G}
    (h : KConfig G L V MK) (hC : Subgroup.centralizer (V : Set G) ≤ V)
    {D : Fin 6 → Subgroup G} (hd : SixData V D)
    {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) (ha2 : a * a = 1)
    (hfix : Nat.card V = 2 * Nat.card {v : V // a * (v : G) * a⁻¹ = v}) :
    ConclK G L V MK :=
  h.conclK_of_a6 hC hd.psi hd.psi_surjective hd.psi_eq_one_iff ha ha2 hfix

theorem eq_bot_of_normal_of_fix {H : Subgroup (Equiv.Perm (Fin 6))} (hH : H.Normal) {r : Fin 6}
    (hr : ∀ σ ∈ H, σ r = r) : H = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  have h1 := hr _ (hH.conj_mem σ hσ (Equiv.swap r i)⁻¹)
  simp only [inv_inv, Equiv.Perm.mul_apply, Equiv.swap_inv] at h1
  have h2 := congrArg (Equiv.swap r i) h1
  simpa [Equiv.swap_apply_left] using h2

theorem KConfig.false_of_sixData {G : Type} [Group G] [Finite G] {L V MK W : Subgroup G}
    (h : KConfig G L V MK) (hCV : Subgroup.centralizer (V : Set G) = W) (hW2 : IsPGroup 2 W)
    {D : Fin 6 → Subgroup G} (hd : SixData W D) {r : Fin 6} (hVr : V = D r) : False := by
  have hLN : L ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hCV]; exact h.le_normalizer_centralizer
  have hNL : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hCV]; exact h.normalizer_centralizer_le (by rw [hCV]; exact hW2)
  let φ : ↥L →* Equiv.Perm (Fin 6) := hd.psi.comp (Subgroup.inclusion hLN)
  have hnorm : φ.range.Normal := by
    refine ⟨fun x hx σ => ?_⟩
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := hd.psi_surjective σ
    have hml : (m : G) * l * (m : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hNL m.2) l).mp l.2
    refine ⟨⟨_, hml⟩, ?_⟩
    change hd.psi (Subgroup.inclusion hLN ⟨_, hml⟩) =
      hd.psi m * hd.psi (Subgroup.inclusion hLN l) * (hd.psi m)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hfix : ∀ σ ∈ φ.range, σ r = r := by
    rintro _ ⟨l, rfl⟩
    change hd.sig (Subgroup.inclusion hLN l) r = r
    apply hd.sig_eq
    rw [← hVr]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.le_normalizer l.2))
  have hbot := eq_bot_of_normal_of_fix hnorm hfix
  have hLW : L ≤ W := fun l hl => by
    have h1 : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (hd.psi_eq_one_iff _).mp h1
  have hL1 : L = ⊥ := eq_bot_of_perfect_of_isPGroup h.perfect (hW2.to_le hLW)
  apply h.ne_bot
  rw [h.eq_commutator, hL1, Subgroup.commutator_bot_right]

end CFSG.SectionRank.QTK.Insp443

end
