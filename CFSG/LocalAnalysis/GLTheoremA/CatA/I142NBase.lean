module

public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

theorem isSubnormal_le {A X : Subgroup G} (h : IsSubnormal A X) : A ≤ X := by
  induction h with
  | refl => exact le_rfl
  | step hAM _ _ ih => exact hAM.trans ih

theorem isSubnormal_trans' {A B C : Subgroup G} (h₁ : IsSubnormal A B) (h₂ : IsSubnormal B C) :
    IsSubnormal A C := by
  induction h₁ with
  | refl => exact h₂
  | step hAM hn _ ih => exact IsSubnormal.step hAM hn (ih h₂)

theorem isSubnormal_inf_comap (f : G →* H) {N T : Subgroup H} (h : IsSubnormal N T)
    (X : Subgroup G) : IsSubnormal (X ⊓ N.comap f) (X ⊓ T.comap f) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | @step N' M T' hNM hn _ ih =>
    refine IsSubnormal.step ?_ ?_ ih
    · exact inf_le_inf_left _ (Subgroup.comap_mono hNM)
    · refine ⟨fun n hn' g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn' ⊢
      obtain ⟨hnX, hnN⟩ := Subgroup.mem_inf.1 hn'
      obtain ⟨hgX, hgM⟩ := Subgroup.mem_inf.1 g.2
      have hfn : f (n : G) ∈ N' := hnN
      have hfg : f (g : G) ∈ M := hgM
      have hc := hn.conj_mem (⟨f n, hNM hfn⟩ : M) (Subgroup.mem_subgroupOf.2 hfn) (⟨f g, hfg⟩ : M)
      have hc' : f (g : G) * f (n : G) * (f (g : G))⁻¹ ∈ N' := Subgroup.mem_subgroupOf.1 hc
      rw [Subgroup.mem_inf, Subgroup.mem_comap]
      refine ⟨X.mul_mem (X.mul_mem hgX hnX) (X.inv_mem hgX), ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
      exact hc'

theorem isSubnormal_of_le_of_le {A X M : Subgroup G} (h : IsSubnormal A X) (hAM : A ≤ M)
    (hMX : M ≤ X) : IsSubnormal A M := by
  have := isSubnormal_inf_comap (MonoidHom.id G) h M
  rw [Subgroup.comap_id, Subgroup.comap_id, inf_eq_right.2 hAM, inf_eq_left.2 hMX] at this
  exact this

theorem isSubnormal_map (f : G →* H) {A X : Subgroup G} (h : IsSubnormal A X) :
    IsSubnormal (A.map f) (X.map f) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | @step A' M X' hAM hn _ ih =>
    refine IsSubnormal.step (Subgroup.map_mono hAM) ?_ ih
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.1 hn'
    obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.1 g.2
    have hc : m * x * m⁻¹ ∈ A' := by
      have := hn.conj_mem (⟨x, hAM hx⟩ : M) (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
      exact Subgroup.mem_subgroupOf.1 this
    refine Subgroup.mem_map.2 ⟨m * x * m⁻¹, hc, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hmg, ← hxn, map_mul, map_mul,
      map_inv]

theorem isComponentOf_trans {K N X : Subgroup G} (hK : IsComponentOf K N)
    (hN : IsSubnormal N X) : IsComponentOf K X :=
  ⟨hK.1.trans (isSubnormal_le hN), isSubnormal_trans' hK.2.1 hN, hK.2.2⟩

theorem isComponentOf_of_le {K X M : Subgroup G} (hK : IsComponentOf K X) (hKM : K ≤ M)
    (hMX : M ≤ X) : IsComponentOf K M :=
  ⟨hKM, isSubnormal_of_le_of_le hK.2.1 hKM hMX, hK.2.2⟩

theorem isQuasisimple_of_surjective {Q R : Type*} [Group Q] [Group R] (f : Q →* R)
    (hf : Function.Surjective f) (hk : ∀ g : Q, f g = 1 → g ∈ Subgroup.center Q)
    (hQ : IsQuasisimple Q) : IsQuasisimple R := by
  obtain ⟨hcomm, hsimp⟩ := hQ
  haveI := hsimp.toNontrivial
  have hRc : commutator R = ⊤ := by
    have h1 : Subgroup.map f (commutator Q) = commutator R := by
      show Subgroup.map f ⁅(⊤ : Subgroup Q), ⊤⁆ = ⁅(⊤ : Subgroup R), ⊤⁆
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
    rw [← h1, hcomm, Subgroup.map_top_of_surjective f hf]
  obtain ⟨x, hx⟩ : ∃ x : Q, x ∉ Subgroup.center Q := by
    obtain ⟨a, ha⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨x, fun h => ha (QuotientGroup.eq_one_iff x |>.2 h)⟩
  haveI : Nontrivial R := ⟨⟨f x, 1, fun h => hx (hk x h)⟩⟩
  have hZR : Subgroup.center R ≠ ⊤ := by
    intro htop
    have hbot : commutator R = ⊥ := by
      rw [eq_bot_iff]
      show ⁅(⊤ : Subgroup R), ⊤⁆ ≤ ⊥
      rw [Subgroup.commutator_le]
      intro a _ b _
      have ha : a ∈ Subgroup.center R := htop ▸ Subgroup.mem_top a
      have hab : a * b = b * a := (Subgroup.mem_center_iff.1 ha b).symm
      rw [commutatorElement_def, Subgroup.mem_bot, hab]
      group
    rw [hRc] at hbot
    exact top_ne_bot hbot
  have hcen : Subgroup.center Q ≤ (Subgroup.center R).comap f := by
    intro g hg
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro h
    obtain ⟨y, rfl⟩ := hf h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg y]
  haveI : Nontrivial (R ⧸ Subgroup.center R) := by
    obtain ⟨g, hg⟩ : ∃ g : R, g ∉ Subgroup.center R := by
      by_contra hcon
      push_neg at hcon
      exact hZR (eq_top_iff.2 fun g _ => hcon g)
    exact ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
  refine ⟨hRc, ?_⟩
  exact IsSimpleGroup.isSimpleGroup_of_surjective (QuotientGroup.map (Subgroup.center Q) (Subgroup.center R) f hcen)
    (by
      intro r
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective r
      obtain ⟨y, rfl⟩ := hf r
      exact ⟨QuotientGroup.mk y, rfl⟩)

theorem isComponentOf_map (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    {K X : Subgroup G} (hK : IsComponentOf K X) : IsComponentOf (K.map f) (X.map f) := by
  refine ⟨Subgroup.map_mono hK.1, isSubnormal_map f hK.2.1, ?_⟩
  let g : K →* (K.map f : Subgroup H) :=
    { toFun := fun k => ⟨f k, Subgroup.mem_map_of_mem f k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine isQuasisimple_of_surjective g hg ?_ hK.2.2
  rintro ⟨k, hk⟩ hfk
  have hfk' : f k = 1 := congrArg Subtype.val hfk
  have hc := hf k hfk'
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 hc y)

theorem GLALayer_eq_sSup (X : Subgroup G) : GLALayer X = sSup {K | IsComponentOf K X} := rfl

theorem le_GLALayer {X K : Subgroup G} (h : IsComponentOf K X) : K ≤ GLALayer X :=
  le_sSup (show K ∈ {K | IsComponentOf K X} from h)

theorem GLALayer_le_of {X M : Subgroup G} (h : ∀ K, IsComponentOf K X → K ≤ M) :
    GLALayer X ≤ M :=
  sSup_le fun K hK => h K hK

theorem GLALayer_le (X : Subgroup G) : GLALayer X ≤ X :=
  GLALayer_le_of fun _ hK => hK.1

theorem GLALayer_mono_of_isSubnormal {N X : Subgroup G} (h : IsSubnormal N X) :
    GLALayer N ≤ GLALayer X :=
  GLALayer_le_of fun _ hK => le_GLALayer (isComponentOf_trans hK h)

theorem GLALayer_map_le (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    (X : Subgroup G) : (GLALayer X).map f ≤ GLALayer (X.map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact GLALayer_le_of fun K hK =>
    Subgroup.map_le_iff_le_comap.1 (le_GLALayer (isComponentOf_map f hf hK))

theorem map_GLALayer_le_of_eq (φ : G ≃* G) {X : Subgroup G} (hX : X.map φ.toMonoidHom = X) :
    (GLALayer X).map φ.toMonoidHom ≤ GLALayer X := by
  have hf : ∀ g : G, φ.toMonoidHom g = 1 → g ∈ Subgroup.center G := by
    intro g hg
    have h1 : g = 1 := (MulEquiv.map_eq_one_iff φ).1 hg
    rw [h1]
    exact Subgroup.one_mem _
  have h := GLALayer_map_le φ.toMonoidHom hf X
  rw [hX] at h
  exact h

end CFSG.LocalAnalysis.GLTheoremA.I142N
