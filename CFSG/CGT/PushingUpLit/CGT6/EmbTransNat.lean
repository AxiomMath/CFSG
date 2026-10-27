module

public import CFSG.CGT.PushingUpLit.CGT6.EmbTransport
public import CFSG.CGT.PushingUpLit.CGT6.EmbThompson

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUp
open scoped commutatorElement

section CentralFix

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}

theorem eq_one_of_central_fix (hUS : USelf K)
    (hirr : ∀ A : Subgroup V, (∀ x ∈ K, ∀ a ∈ A, x a ∈ A) → A ≤ commV K →
      A = ⊥ ∨ A = commV K) (hne : commV K ≠ ⊥) {r : MulAut V} (hr : r ∈ K)
    (hcent : ∀ k ∈ K, r * k = k * r) (hfix : ∀ u ∈ commV K, r u = u) : r = 1 := by
  let φ : V →* V :=
    { toFun := fun v => r v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hφ : ∀ v, φ v = r v * v⁻¹ := fun _ => rfl
  have hφx : ∀ x ∈ K, ∀ v, φ (x v) = x (φ v) := by
    intro x hx v
    have h1 : r (x v) = x (r v) := by
      have := congrArg (fun e : MulAut V => e v) (hcent x hx)
      simpa [MulAut.mul_apply] using this
    simp only [hφ, map_mul, map_inv, h1]
  have hDU : φ.range ≤ commV K := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨r, hr, v, rfl⟩
  have hDinv : ∀ x ∈ K, ∀ a ∈ φ.range, x a ∈ φ.range := by
    rintro x hx _ ⟨v, rfl⟩
    exact ⟨x v, hφx x hx v⟩
  rcases hirr φ.range hDinv hDU with h0 | h1
  · ext v
    have : φ v ∈ φ.range := ⟨v, rfl⟩
    rw [h0, Subgroup.mem_bot, hφ, mul_inv_eq_one] at this
    simpa using this
  · exfalso
    apply hne
    refine le_bot_iff.mp (hUS ⊥ ?_)
    intro x hx u hu
    rw [Subgroup.mem_bot]
    rw [← h1] at hu
    obtain ⟨v, rfl⟩ := hu
    have hw : x v * v⁻¹ ∈ commV K := Subgroup.subset_closure ⟨x, hx, v, rfl⟩
    have h3 : r (x v * v⁻¹) = x v * v⁻¹ := hfix _ hw
    have h4 : φ (x v * v⁻¹) = 1 := by rw [hφ, h3, mul_inv_cancel]
    rw [map_mul, map_inv, hφx x hx v] at h4
    exact h4

theorem commV_ne_bot_of_not_isPGroup (hK : ¬ IsPGroup 2 ↥K) : commV K ≠ ⊥ := by
  intro h
  apply hK
  have hK1 : ∀ k : ↥K, k = 1 := by
    intro k
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    have : (k : MulAut V) v * v⁻¹ ∈ commV K := Subgroup.subset_closure ⟨k, k.2, v, rfl⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  intro k
  exact ⟨0, by rw [hK1 k]; simp⟩

end CentralFix

section Equiv

theorem IsNatSectionBy.of_equiv {V₁ V₂ : Type*} [CommGroup V₁] [CommGroup V₂] {S M : Type*}
    [Group S] [Group M] {act : S → M → M} {K₁ : Subgroup (MulAut V₁)}
    {K₂ : Subgroup (MulAut V₂)} {P₁ : Subgroup V₁} {P₂ : Subgroup V₂} (eK : ↥K₂ ≃* ↥K₁)
    (eU : ↥P₂ ≃* ↥P₁) (hinv₂ : ∀ x ∈ K₂, ∀ p ∈ P₂, x p ∈ P₂)
    (hcomp : ∀ (x : ↥K₂) (p : ↥P₂) (hp : (x : MulAut V₂) (p : V₂) ∈ P₂),
      ((eU ⟨(x : MulAut V₂) (p : V₂), hp⟩ : ↥P₁) : V₁) =
        ((eK x : ↥K₁) : MulAut V₁) ((eU p : ↥P₁) : V₁))
    (h : IsNatSectionBy act K₁ P₁ ⊥) : IsNatSectionBy act K₂ P₂ ⊥ := by
  obtain ⟨hinv₁, θ, β, hβs, hβk, hβe⟩ := h
  refine ⟨hinv₂, eK.trans θ, β.comp eU.toMonoidHom, hβs.comp eU.surjective, ?_, ?_⟩
  · ext w
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    have h1 : β (eU w) = 1 ↔ eU w ∈ β.ker := (MonoidHom.mem_ker).symm
    rw [h1, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hw
      have : eU w = 1 := Subtype.ext hw
      have h2 : w = 1 := by simpa using this
      rw [h2]
      rfl
    · intro hw
      have : w = 1 := Subtype.ext hw
      rw [this]
      simp
  · intro x p hp
    have hmem : ((eK x : ↥K₁) : MulAut V₁) ((eU p : ↥P₁) : V₁) ∈ P₁ :=
      hinv₁ _ (eK x).2 _ (eU p).2
    have h1 : eU ⟨(x : MulAut V₂) (p : V₂), hp⟩ =
        ⟨((eK x : ↥K₁) : MulAut V₁) ((eU p : ↥P₁) : V₁), hmem⟩ := Subtype.ext (hcomp x p hp)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
    rw [h1]
    exact hβe (eK x) (eU p) hmem

end Equiv

section BarW

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W)
  {K : Subgroup (MulAut V)}

theorem map_commV_barW_eq (hKG : K ≤ G) (hU : commV K ≤ commVW W K) :
    (commV (barW h K)).map W.subtype = commV K :=
  (commV_barW h hKG).trans (le_antisymm commVW_le_commV hU)

@[expose] noncomputable def commBarEquiv (hKG : K ≤ G) (hU : commV K ≤ commVW W K) :
    ↥(commV (barW h K)) ≃* ↥(commV K) :=
  (Subgroup.equivMapOfInjective _ W.subtype W.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_commV_barW_eq h hKG hU))

theorem coe_commBarEquiv (hKG : K ≤ G) (hU : commV K ≤ commVW W K) (w : ↥(commV (barW h K))) :
    ((commBarEquiv h hKG hU w : ↥(commV K)) : V) = (((w : ↥W)) : V) := rfl

theorem coe_commBarEquiv_symm (hKG : K ≤ G) (hU : commV K ≤ commVW W K) (p : ↥(commV K)) :
    ((((commBarEquiv h hKG hU).symm p : ↥(commV (barW h K))) : ↥W) : V) = (p : V) := by
  have := coe_commBarEquiv h hKG hU ((commBarEquiv h hKG hU).symm p)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem isNatSectionBy_barW_iff {S M : Type*} [Group S] [Group M] (act : S → M → M)
    (hKG : K ≤ G) (hU : commV K ≤ commVW W K) (hinj : K ⊓ fixW W = ⊥) :
    IsNatSectionBy act K (commV K) ⊥ ↔
      IsNatSectionBy act (barW h K) (commV (barW h K)) ⊥ := by
  constructor
  · intro hK
    refine IsNatSectionBy.of_equiv (barWEquiv h hKG hinj).symm (commBarEquiv h hKG hU)
      (fun x hx p hp => commV_invariant hx hp) ?_ hK
    intro x p hp
    obtain ⟨k, rfl⟩ := (barWEquiv h hKG hinj).surjective x
    rw [MulEquiv.symm_apply_apply]
    rfl
  · intro hK
    refine IsNatSectionBy.of_equiv (barWEquiv h hKG hinj) (commBarEquiv h hKG hU).symm
      (fun x hx p hp => commV_invariant hx hp) ?_ hK
    intro x p hp
    have h1 := coe_commBarEquiv_symm h hKG hU ⟨(x : MulAut V) (p : V), hp⟩
    have h2 := coe_commBarEquiv_symm h hKG hU p
    apply Subtype.ext
    show ((((commBarEquiv h hKG hU).symm ⟨(x : MulAut V) (p : V), hp⟩ :
        ↥(commV (barW h K))) : ↥W) : V) = (x : MulAut V)
          ((((commBarEquiv h hKG hU).symm p : ↥(commV (barW h K))) : ↥W) : V)
    rw [h1, h2]

theorem irr_of_barW (hKG : K ≤ G) (hKW : commV K ≤ W) (hU : commV K ≤ commVW W K)
    (hirr : ∀ A : Subgroup ↥W, (∀ x ∈ barW h K, ∀ a ∈ A, x a ∈ A) → A ≤ commV (barW h K) →
      A = ⊥ ∨ A = commV (barW h K)) :
    ∀ A : Subgroup V, (∀ x ∈ K, ∀ a ∈ A, x a ∈ A) → A ≤ commV K → A = ⊥ ∨ A = commV K := by
  intro A hA hAU
  have hAW : A ≤ W := hAU.trans hKW
  have hmap : (A.comap W.subtype).map W.subtype = A :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hAW)
  have hA' : ∀ x ∈ barW h K, ∀ a ∈ A.comap W.subtype, x a ∈ A.comap W.subtype := by
    intro x hx a ha
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hx
    exact hA g hg a ha
  have hA'U : A.comap W.subtype ≤ commV (barW h K) := by
    intro a ha
    exact (mem_commV_barW h hKG).mpr (hU (hAU (Subgroup.mem_comap.mp ha)))
  rcases hirr _ hA' hA'U with h0 | h1
  · left
    rw [← hmap, h0, Subgroup.map_bot]
  · right
    rw [← hmap, h1, map_commV_barW_eq h hKG hU]

end BarW

section Descent

variable {V : Type} [CommGroup V] [Finite V] {G Y : Subgroup (MulAut V)} {W : Subgroup V}

omit [Finite V] in
theorem Trans.inf_fixW_of_nat (T : Trans G Y W) {n : ℕ} (hn : 2 ≤ n) (hY : NatOmegaN n Y) :
    Y ⊓ fixW W = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  refine eq_one_of_central_fix T.uy (NatOmegaN.irreducible hn hY)
    (commV_ne_bot_of_not_isPGroup (hY.not_isPGroup hn)) hr.1
    (fun k hk => (Subgroup.mem_centralizer_iff.mp (T.cy ⟨T.yg hr.1, hr.2⟩) k hk).symm)
    (fun u hu => hr.2 u (T.yw hu))

theorem Trans.classX4_bar (hV : ∀ v : V, v ^ 2 = 1) (T : Trans G Y W) (hY : ClassX4 Y) :
    ClassX4 (barW T.inv Y) := by
  rcases classX4_iff.mp hY with hc | ⟨n, hn, hΩ⟩
  · exact classX4_iff.mpr (Or.inl (T.descent hV hc))
  · have hinj := T.inf_fixW_of_nat hn hΩ
    refine classX4_iff.mpr (Or.inr ⟨n, hn, ?_⟩)
    rcases hΩ with h1 | h1
    · exact Or.inl ((isNatSectionBy_barW_iff T.inv _ T.yg T.hU_self hinj).mp h1)
    · exact Or.inr ((isNatSectionBy_barW_iff T.inv _ T.yg T.hU_self hinj).mp h1)

omit [Finite V] in
theorem conjClosure_self {Y : Subgroup (MulAut V)} : conjClosure Y Y = Y :=
  le_antisymm (conjClosure_le le_rfl) le_conjClosure

theorem Trans.ascent_nat (hV : ∀ v : V, v ^ 2 = 1) (T : Trans G Y W) {n : ℕ} (hn : 2 ≤ n)
    {X : Subgroup (MulAut ↥W)} (B : BlockHyp T X) (hX : NatOmegaN n X)
    (hcase : barW T.inv Y = X ∨ (InClassX ↥(yuHol (barW T.inv Y)) ∧
      Nonempty (↥(barW T.inv Y) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
      Nat.card ↥(commV (barW T.inv Y)) = 2 ^ (3 * n))) :
    ∃ K : Subgroup (MulAut V), Y ≤ K ∧ K ≤ G ∧ (K.subgroupOf G).IsSubnormal ∧ NatOmegaN n K ∧
      (Y = K ∨ (InClassX ↥(yuHol Y) ∧
        Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
        Nat.card ↥(commV Y) = 2 ^ (3 * n))) := by
  have hXtG := preW_le T.inv X
  have hYXt := B.yxt
  set K := conjClosure Y (preW T.inv X) with hK
  have hKG : K ≤ G := B.kG
  have hKsub : (K.subgroupOf G).IsSubnormal := B.k_sub
  have hbarK : barW T.inv K = X := B.barK
  have hKW := T.commV_conj_le hXtG
  have hUK := T.hU_conj hXtG
  have hUKself : USelf K := T.uself_conj
  have hirrK : ∀ A : Subgroup V, (∀ x ∈ K, ∀ a ∈ A, x a ∈ A) → A ≤ commV K →
      A = ⊥ ∨ A = commV K := by
    apply irr_of_barW T.inv hKG hKW hUK
    rw [hbarK]
    exact NatOmegaN.irreducible hn hX
  have hneK : commV K ≠ ⊥ := by
    intro hbot
    have h1 : commV X = ⊥ := by
      have h2 := map_commV_barW_eq T.inv hKG hUK
      rw [hbarK, hbot] at h2
      exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp h2
    exact commV_ne_bot_of_not_isPGroup (hX.not_isPGroup hn) h1
  have hinjK : K ⊓ fixW W = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    exact eq_one_of_central_fix hUKself hirrK hneK hr.1 (T.ker_central hXtG hYXt r hr)
      (fun u hu => hr.2 u (hKW hu))
  have hnatK : NatOmegaN n K := by
    have hX' : NatOmegaN n (barW T.inv K) := by rw [hbarK]; exact hX
    rcases hX' with h1 | h1
    · exact Or.inl ((isNatSectionBy_barW_iff T.inv _ hKG hUK hinjK).mpr h1)
    · exact Or.inr ((isNatSectionBy_barW_iff T.inv _ hKG hUK hinjK).mpr h1)
  refine ⟨K, le_conjClosure, hKG, hKsub, hnatK, ?_⟩
  rcases hcase with hb | ⟨hY1, ⟨e⟩, hcard⟩
  · left
    exact le_antisymm le_conjClosure (T.conj_le_of_eq hb)
  · right
    have hinjY : Y ⊓ fixW W = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      have : r ∈ K ⊓ fixW W := ⟨le_conjClosure hr.1, hr.2⟩
      rw [hinjK] at this
      exact this
    have hres : oResidualTwo ↥(yuHol Y) = ⊤ := by
      have := oResidualTwo_yuHol_conjClosure (Y := Y) (Xt := Y) T.no T.uy
      rwa [conjClosure_self] at this
    refine ⟨((T.centralShort_self hV).inClassX_iff hres).mpr hY1,
      ⟨(barWEquiv T.inv T.yg hinjY).trans e⟩, ?_⟩
    have h2 := map_commV_barW_eq T.inv T.yg T.hU_self
    rw [← h2, Subgroup.card_map_of_injective W.subtype_injective]
    exact hcard

end Descent


end CFSG.CGT.PushingUpLit.CGT6
