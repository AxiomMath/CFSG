module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerDetect

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

theorem finite_linearEquiv [Finite V] : Finite (V ≃ₗ[k] V) :=
  Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective

theorem mem_sup_mul {L A : Subgroup X} (h : A ≤ Subgroup.normalizer (L : Set X)) {g : X}
    (hg : g ∈ L ⊔ A) : ∃ l ∈ L, ∃ a ∈ A, g = l * a := by
  have hg' : g ∈ Subgroup.closure ((L : Set X) ∪ (A : Set X)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]; exact hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, A.one_mem, (mul_one x).symm⟩
    · exact ⟨1, L.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, L.one_mem, 1, A.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, hl₁, a₁, ha₁, rfl⟩ := hx
    obtain ⟨l₂, hl₂, a₂, ha₂, rfl⟩ := hy
    have hc : a₁ * l₂ * a₁⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h ha₁) l₂).1 hl₂
    exact ⟨l₁ * (a₁ * l₂ * a₁⁻¹), L.mul_mem hl₁ hc, a₁ * a₂, A.mul_mem ha₁ ha₂, by group⟩
  | inv x _ hx =>
    obtain ⟨l, hl, a, ha, rfl⟩ := hx
    have hc : a⁻¹ * l⁻¹ * a ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (h (A.inv_mem ha)) l⁻¹).1 (L.inv_mem hl)
      simpa using this
    exact ⟨a⁻¹ * l⁻¹ * a, hc, a⁻¹, A.inv_mem ha, by group⟩

theorem isInvariant_sup_subgroup {ρ : X →* (V ≃ₗ[k] V)} {H K : Subgroup X} {U : Submodule k V}
    (hH : Offender.IsInvariant ρ H U) (hK : Offender.IsInvariant ρ K U) :
    Offender.IsInvariant ρ (H ⊔ K) U := by
  have key : ∀ g ∈ Subgroup.closure ((H : Set X) ∪ (K : Set X)),
      (∀ u ∈ U, ρ g u ∈ U) ∧ (∀ u ∈ U, ρ g⁻¹ u ∈ U) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨hH x hx, hH x⁻¹ (H.inv_mem hx)⟩
      · exact ⟨hK x hx, hK x⁻¹ (K.inv_mem hx)⟩
    | one => exact ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun u hu => ?_, fun u hu => ?_⟩
      · rw [ρ_mul_apply]; exact hx.1 _ (hy.1 u hu)
      · rw [mul_inv_rev, ρ_mul_apply]; exact hy.2 _ (hx.2 u hu)
    | inv x _ hx => exact ⟨hx.2, by simpa using hx.1⟩
  intro g hg u hu
  have hg' : g ∈ Subgroup.closure ((H : Set X) ∪ (K : Set X)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]; exact hg
  exact (key g hg').1 u hu

theorem noPQuotient_two_of_odd {Y : Type*} [Group Y] [Finite Y] (hodd : Odd (Nat.card Y)) :
    NoPQuotient 2 Y := by
  intro N _ hpg
  have h1 : Odd (Nat.card (Y ⧸ N)) := Odd.of_dvd_nat hodd (Subgroup.index_dvd_card N)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
  have hn0 : n = 0 := by
    by_contra hne
    rw [hn] at h1
    exact (Nat.not_even_iff_odd.2 h1) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hn0, pow_zero] at hn
  have : N.index = 1 := hn
  exact Subgroup.index_eq_one.1 this

theorem centralPChief_two_of_odd {Y : Type*} [Group Y] [Finite Y] (hodd : Odd (Nat.card Y)) :
    CentralPChief 2 Y := by
  intro K X hc hpow
  exfalso
  obtain ⟨n, hn⟩ := hpow
  have h1 : Odd (K.relIndex X) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card X))
      (Subgroup.index_dvd_card (K.subgroupOf X))
  have hn0 : n = 0 := by
    by_contra hne
    rw [hn] at h1
    exact (Nat.not_even_iff_odd.2 h1) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hn0, pow_zero] at hn
  have := Subgroup.relIndex_eq_one.1 hn
  exact absurd hc.lt (not_lt_of_ge this)

theorem isElementaryAbelian_range {R S : Type*} [Group R] [Group S] (f : R →* S)
    (h : CFSG.IsElementaryAbelian 2 R) : CFSG.IsElementaryAbelian 2 f.range where
  toIsMulCommutative := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, h.toIsMulCommutative.is_comm.comm a b]⟩⟩
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    show (f a) ^ 2 = 1
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h.exponent_dvd_p a, map_one]

theorem eq_one_of_commutes {W : Type*} [AddCommGroup W] [Module k W] [Finite W]
    (H₀ A₀ : Subgroup (W ≃ₗ[k] W)) (hirr : IsIrrAct H₀) (hP : Nat.card (fixGL A₀) = 2)
    (n : W ≃ₗ[k] W) (hH : ∀ h ∈ H₀, n * h = h * n) (hA : ∀ a ∈ A₀, n * a = a * n) : n = 1 := by
  have hP' : fixGL A₀ ≠ ⊥ := by
    intro h
    rw [h, natCard_bot] at hP
    omega
  obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP'
  have hnp : n p ∈ fixGL A₀ := by
    intro a ha
    have h1 : a (n p) = n (a p) := by
      have := congrArg (fun f : W ≃ₗ[k] W => f p) (hA a ha)
      exact this.symm
    have hp' : a p = p := hpP a ha
    show a (n p) = n p
    rw [h1, hp']
  have hnp0 : n p ≠ 0 := fun h => hp0 (n.injective (by rw [h, map_zero]))
  have hnpp : n p = p := by
    have huniq := (Nat.card_eq_two_iff' (0 : fixGL A₀)).1 hP
    have := huniq.unique (y₁ := ⟨n p, hnp⟩) (y₂ := ⟨p, hpP⟩)
      (fun h => hnp0 (congrArg Subtype.val h)) (fun h => hp0 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  let U : Submodule k W := LinearMap.ker ((n : W →ₗ[k] W) - LinearMap.id)
  have hU : ∀ h ∈ H₀, ∀ u ∈ U, h u ∈ U := by
    intro h hh u hu
    have hnu : n u = u := by
      have := LinearMap.mem_ker.1 hu
      simpa [sub_eq_zero] using this
    have h1 : n (h u) = h (n u) := by
      have := congrArg (fun f : W ≃ₗ[k] W => f u) (hH h hh)
      exact this
    show ((n : W →ₗ[k] W) - (LinearMap.id : W →ₗ[k] W)) (h u) = 0
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [h1, hnu, sub_self]
  rcases hirr U hU with h | h
  · exfalso
    apply hp0
    have : p ∈ U := by
      show ((n : W →ₗ[k] W) - (LinearMap.id : W →ₗ[k] W)) p = 0
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [hnpp, sub_self]
    rw [h] at this
    exact (Submodule.mem_bot k).1 this
  · apply LinearEquiv.ext
    intro w
    have : w ∈ U := by rw [h]; exact Submodule.mem_top
    have := LinearMap.mem_ker.1 this
    simpa [sub_eq_zero] using this

theorem isIrrAct_range_resSub (ρ : X →* (V ≃ₗ[k] V)) (L : Subgroup X) (I : Submodule k V)
    (hI : Offender.IsInvariant ρ L I)
    (hirr : ∀ U : Submodule k V, Offender.IsInvariant ρ L U → U ≤ I → U = ⊥ ∨ U = I) :
    IsIrrAct (resSub ρ L I hI).range := by
  intro U' hU'
  have hU : Offender.IsInvariant ρ L (U'.map I.subtype) := by
    rintro l hl _ ⟨u, hu, rfl⟩
    refine ⟨resSub ρ L I hI ⟨l, hl⟩ u, hU' _ ⟨⟨l, hl⟩, rfl⟩ u hu, ?_⟩
    exact resSub_apply ρ L I hI ⟨l, hl⟩ u
  rcases hirr _ hU (Submodule.map_subtype_le I U') with h | h
  · left
    exact Submodule.map_injective_of_injective I.injective_subtype
      (h.trans (Submodule.map_bot _).symm)
  · right
    exact Submodule.map_injective_of_injective I.injective_subtype
      (h.trans (Submodule.map_subtype_top I).symm)

theorem natCard_le_weight_res [Finite X] [Finite V] (ρ : X →* (V ≃ₗ[k] V)) (B : Subgroup X)
    (W : Submodule k V) (hW : Offender.IsInvariant ρ B W)
    (hmax : ∀ D : Subgroup X, D ≤ B → weight ρ D ≤ weight ρ B) :
    Nat.card ↥W ≤ weight (MonoidHom.id (W ≃ₗ[k] W)) (resSub ρ B W hW).range := by
  have hmaxB : ∀ D : Subgroup ↥B,
      weight (ρ.comp B.subtype) D ≤ weight (ρ.comp B.subtype) ⊤ := by
    intro D
    rw [weight_comp_subtype, weight_comp_subtype, map_subtype_top]
    exact hmax _ (Subgroup.map_subtype_le D)
  have h := restrict_ineq_weak (ρ.comp B.subtype) W hmaxB
    (B := centSub (ρ.comp B.subtype) W) le_rfl
  rw [Subgroup.relIndex_self, one_mul] at h
  have hWC : W ⊓ fixSub (ρ.comp B.subtype) (centSub (ρ.comp B.subtype) W) = W :=
    inf_eq_left.2 fun w hw b hb => hb w hw
  rw [hWC] at h
  have h2 := weightId_range (ρ.comp B.subtype) W (fun a w hw => hW a a.2 w hw)
  unfold resSub
  rw [h2]
  exact h

theorem triv_of_commutator (ρ : X →* (V ≃ₗ[k] V)) (L A : Subgroup X) (I : Submodule k V)
    (hI : Offender.IsInvariant ρ (L ⊔ A) I) (hA : ∀ a ∈ A, ∀ v, ρ a v - v ∈ I) (hLA : ⁅L, A⁆ = L) :
    ∀ g ∈ L ⊔ A, ∀ v, ρ g v - v ∈ I := by
  let Triv : Subgroup X :=
    { carrier := {g | g ∈ L ⊔ A ∧ ∀ v, ρ g v - v ∈ I}
      one_mem' := ⟨(L ⊔ A).one_mem, fun v => by simp⟩
      mul_mem' := fun {g h} hg hh => ⟨(L ⊔ A).mul_mem hg.1 hh.1, fun v => by
        have e : ρ (g * h) v - v = ρ g (ρ h v - v) + (ρ g v - v) := by
          rw [ρ_mul_apply, map_sub]; abel
        rw [e]
        exact I.add_mem (hI g hg.1 _ (hh.2 v)) (hg.2 v)⟩
      inv_mem' := fun {g} hg => ⟨(L ⊔ A).inv_mem hg.1, fun v => by
        have e : ρ g⁻¹ v - v = -ρ g⁻¹ (ρ g v - v) := by
          rw [map_sub, ρ_inv_apply]; abel
        rw [e]
        exact I.neg_mem (hI g⁻¹ ((L ⊔ A).inv_mem hg.1) _ (hg.2 v))⟩ }
  have hnorm : ∀ y ∈ L ⊔ A, ∀ g ∈ Triv, y * g * y⁻¹ ∈ Triv := by
    intro y hy g hg
    refine ⟨(L ⊔ A).mul_mem ((L ⊔ A).mul_mem hy hg.1) ((L ⊔ A).inv_mem hy), fun v => ?_⟩
    have e : ρ (y * g * y⁻¹) v - v = ρ y (ρ g (ρ y⁻¹ v) - ρ y⁻¹ v) := by
      rw [map_sub, ρ_apply_inv ρ y v, ρ_mul_apply, ρ_mul_apply]
    rw [e]
    exact hI y hy _ (hg.2 (ρ y⁻¹ v))
  have hAT : A ≤ Triv := fun a ha => ⟨Subgroup.mem_sup_right ha, hA a ha⟩
  have hLT : L ≤ Triv := by
    rw [← hLA]
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 := hnorm l (Subgroup.mem_sup_left hl) a (hAT ha)
    rw [commutatorElement_def]
    exact Triv.mul_mem h1 (Triv.inv_mem (hAT ha))
  intro g hg v
  exact (sup_le hLT hAT hg).2 v

theorem resSub_mem_normalizer_range {ρ : X →* (V ≃ₗ[k] V)} {H A : Subgroup X} {W : Submodule k V}
    (hWH : Offender.IsInvariant ρ H W) (hWA : Offender.IsInvariant ρ A W)
    (hAn : A ≤ Subgroup.normalizer (H : Set X)) (y : ↥A) :
    resSub ρ A W hWA y ∈
      Subgroup.normalizer (((resSub ρ H W hWH).range : Subgroup (W ≃ₗ[k] W)) :
        Set (W ≃ₗ[k] W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact resSub_conj_mem_range hWH hWA y.2 (hAn y.2) hx
  · intro hx
    have := resSub_conj_mem_range hWH hWA (A.inv_mem y.2) (Subgroup.inv_mem _ (hAn y.2)) hx
    have hinv : resSub ρ A W hWA ⟨(y : X)⁻¹, A.inv_mem y.2⟩ = (resSub ρ A W hWA y)⁻¹ := by
      show resSub ρ A W hWA ((y : ↥A)⁻¹) = _
      rw [map_inv]
    rw [hinv, inv_inv] at this
    have e : (resSub ρ A W hWA y)⁻¹ *
        (resSub ρ A W hWA y * x * (resSub ρ A W hWA y)⁻¹) * resSub ρ A W hWA y = x := by group
    rwa [e] at this

theorem map_mem_commSub_top_of_commute (ρ : X →* (V ≃ₗ[k] V)) (L : Subgroup X) {n : X}
    (hn : ∀ l ∈ L, n * l = l * n) {w : V} (hw : w ∈ commSub ρ L ⊤) :
    ρ n w ∈ commSub ρ L ⊤ := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, u, -, rfl⟩ := hy
    have e : ρ n (ρ l u - u) = ρ l (ρ n u) - ρ n u := by
      rw [map_sub, ← ρ_mul_apply, ← ρ_mul_apply, hn l hl]
    rw [e]
    exact mem_commSub_of hl Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem resSub_mul_comm {ρ : X →* (V ≃ₗ[k] V)} {B C : Subgroup X} {W : Submodule k V}
    (hB : Offender.IsInvariant ρ B W) (hC : Offender.IsInvariant ρ C W) {b : X} (hb : b ∈ B)
    {c : X} (hc : c ∈ C)
    (hbc : b * c = c * b) :
    resSub ρ B W hB ⟨b, hb⟩ * resSub ρ C W hC ⟨c, hc⟩ =
      resSub ρ C W hC ⟨c, hc⟩ * resSub ρ B W hB ⟨b, hb⟩ := by
  apply LinearEquiv.ext
  intro u
  apply Subtype.ext
  show ((resSub ρ B W hB ⟨b, hb⟩ (resSub ρ C W hC ⟨c, hc⟩ u) : W) : V) =
    ((resSub ρ C W hC ⟨c, hc⟩ (resSub ρ B W hB ⟨b, hb⟩ u) : W) : V)
  rw [resSub_apply, resSub_apply, resSub_apply, resSub_apply, ← ρ_mul_apply, ← ρ_mul_apply, hbc]

end CFSG.QuasithinUnique.Setup.Layer
