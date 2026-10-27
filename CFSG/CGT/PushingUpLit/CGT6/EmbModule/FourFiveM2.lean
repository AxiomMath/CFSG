module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.MinimalMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section SLData

variable {V : Type} [CommGroup V] [Finite V] (Y : Subgroup (MulAut V))

theorem sl_nat_data [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    (φ : (↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (ψ : ↥(shortU ↥(yuHol Y)) →* Multiplicative (Fin 2 → GaloisField 2 n))
    (hsurj : Function.Surjective ψ)
    (hker : ψ.ker = (shortC ↥(yuHol Y)).subgroupOf (shortU ↥(yuHol Y)))
    (hequiv : ∀ (l u : ↥(yuHol Y)) (hu : u ∈ shortU ↥(yuHol Y))
      (hu' : l * u * l⁻¹ ∈ shortU ↥(yuHol Y)), ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd
        ((φ (l : ↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (ψ ⟨u, hu⟩))))
    (hU : shortU ↥(yuHol Y) = (yuInc Y).range) :
    ∃ βV : ↥(commV Y) →* Multiplicative (Fin 2 → GaloisField 2 n), Function.Surjective βV ∧
      βV.ker = (commV Y ⊓ fixV Y).subgroupOf (commV Y) ∧
      ∀ (g : ↥Y) (u : ↥(commV Y)),
        βV ⟨(g : MulAut V) (u : V), apply_mem_commV_self Y g.2 u.2⟩ = Multiplicative.ofAdd
          (((yuTheta Y φ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (βV u))) := by
  classical
  let ι : ↥(commV Y) →* ↥(shortU ↥(yuHol Y)) :=
    (yuInc Y).codRestrict (shortU ↥(yuHol Y)) (yuInc_mem_shortU Y hV)
  refine ⟨ψ.comp ι, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨x, hx⟩ := hsurj w
    obtain ⟨u, hu⟩ : (x : ↥(yuHol Y)) ∈ (yuInc Y).range := hU ▸ x.2
    refine ⟨u, ?_⟩
    have : ι u = x := Subtype.ext hu
    show ψ (ι u) = w
    rw [this, hx]
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h2 : ι u ∈ ψ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at h2
      have h3 : yuInc Y u ∈ Subgroup.center ↥(yuHol Y) := h2.2
      refine ⟨u.2, fun g hg => ?_⟩
      exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) h3
    · rintro ⟨-, hu⟩
      have h2 : ι u ∈ ψ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        refine ⟨yuInc_mem_shortU Y hV u, Subgroup.mem_center_iff.mpr ?_⟩
        intro x
        have h4 := conj_yuInc Y x u
        have h5 : (⟨x.1.right u, apply_mem_commV_self Y x.2.2 u.2⟩ : ↥(commV Y)) = u :=
          Subtype.ext (hu x.1.right x.2.2)
        rw [h5] at h4
        exact mul_inv_eq_iff_eq_mul.mp h4
      exact h2
  · intro g u
    have hu : yuInc Y u ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV u
    have hu' : yuSec Y g * yuInc Y u * (yuSec Y g)⁻¹ ∈ shortU ↥(yuHol Y) :=
      (shortU_normal (L := ↥(yuHol Y))).conj_mem _ hu _
    have h1 := hequiv (yuSec Y g : ↥(yuHol Y)) (yuInc Y u) hu hu'
    have h2 : (⟨yuSec Y g * yuInc Y u * (yuSec Y g)⁻¹, hu'⟩ : ↥(shortU ↥(yuHol Y))) =
        ι ⟨(g : MulAut V) (u : V), apply_mem_commV_self Y g.2 u.2⟩ := by
      apply Subtype.ext
      exact conj_yuInc Y (yuSec Y g) u
    rw [h2] at h1
    exact h1

end SLData

section ResS

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

@[expose] noncomputable def resHomS (S : Subgroup V) (hS : ∀ g ∈ Y, ∀ s ∈ S, g s ∈ S) :
    ↥Y →* MulAut ↥S where
  toFun x := restrictAut x S (fun h hh => hS x x.2 h hh)
    (fun h hh => hS (x : MulAut V)⁻¹ (Y.inv_mem x.2) h hh)
  map_one' := by
    ext h
    rfl
  map_mul' x y := by
    ext h
    rfl

variable {Y}

theorem commV_range_resHomS (S : Subgroup V) (hS : ∀ g ∈ Y, ∀ s ∈ S, g s ∈ S) :
    commV (resHomS Y S hS).range = (commOn Y S).subgroupOf S := by
  apply le_antisymm
  · unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, ⟨g, rfl⟩, v, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨g, g.2, v, v.2, rfl⟩
  · intro w hw
    rw [Subgroup.mem_subgroupOf] at hw
    have key : ∀ x ∈ commOn Y S, ∀ hx : x ∈ S, (⟨x, hx⟩ : ↥S) ∈ commV (resHomS Y S hS).range := by
      intro x hx
      unfold commOn at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g, hg, s, hs, rfl⟩ := hx
        intro hx'
        refine Subgroup.subset_closure ⟨resHomS Y S hS ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, ⟨s, hs⟩, ?_⟩
        apply Subtype.ext
        exact rfl
      | one => intro hx'; exact one_mem _
      | mul a b ha hb iha ihb =>
        intro hab
        have ha' : a ∈ S := commOn_le_self hS ha
        have hb' : b ∈ S := commOn_le_self hS hb
        exact mul_mem (iha ha') (ihb hb')
      | inv a ha iha =>
        intro hab
        have ha' : a ∈ S := commOn_le_self hS ha
        exact inv_mem (iha ha')
    exact key w hw w.2

end ResS

theorem sl2_eq_one_of_mulVec_fix {K : Type*} [Field K] (M : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : ∀ w : Fin 2 → K, (M : Matrix (Fin 2) (Fin 2) K).mulVec w = w) : M = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

section Bound

variable {V : Type} [CommGroup V] [Finite V] (Y : Subgroup (MulAut V))

theorem emb_four_five_bound (hM2 : H1NaturalSL2) [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥(yuHol Y) n) : Nat.card ↥(commV Y ⊓ fixV Y) ≤ 2 ^ n := by
  classical
  obtain ⟨φ, ψ, hsurj, hker, hequiv⟩ := hnat
  have hU := shortU_eq_range Y φ hV hX
  obtain ⟨βV, hβs, hβk, hβe⟩ := sl_nat_data Y hV φ ψ hsurj hker hequiv hU
  have hθs := yuTheta_surjective Y φ hV
  have hRfix := fun {r : ↥Y} (hr : r ∈ (yuTheta Y φ).ker) (u : ↥(commV Y)) =>
    yuTheta_ker_fixes Y φ hV hX hr u
  let R' : Subgroup (MulAut V) := (yuTheta Y φ).ker.map Y.subtype
  let W₀ : Subgroup V := fixV R'
  have hW₀inv : ∀ g ∈ Y, ∀ w ∈ W₀, g w ∈ W₀ := by
    intro g hg w hw r hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have hconj : (⟨g, hg⟩ : ↥Y)⁻¹ * r₀ * ((⟨g, hg⟩ : ↥Y)⁻¹)⁻¹ ∈ (yuTheta Y φ).ker :=
      (MonoidHom.normal_ker (yuTheta Y φ)).conj_mem r₀ hr₀ _
    have h1 : (Y.subtype r₀) (g w) = g ((Y.subtype ((⟨g, hg⟩ : ↥Y)⁻¹ * r₀ *
        ((⟨g, hg⟩ : ↥Y)⁻¹)⁻¹)) w) := by
      simp only [map_mul, map_inv, MulAut.mul_apply, inv_inv]
      exact (MulAut.apply_inv_self (M := V) g _).symm
    rw [h1, hw (Y.subtype ((⟨g, hg⟩ : ↥Y)⁻¹ * r₀ * ((⟨g, hg⟩ : ↥Y)⁻¹)⁻¹)) ⟨_, hconj, rfl⟩]
  have hUW₀ : commV Y ≤ W₀ := by
    intro u hu r hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact hRfix hr₀ ⟨u, hu⟩
  have hUA : commV Y ≠ commV Y ⊓ fixV Y := by
    intro h
    have hfix : ∀ (u : ↥(commV Y)) (g : MulAut V), g ∈ Y → g (u : V) = u := fun u g hg =>
      (h ▸ u.2 : (u : V) ∈ commV Y ⊓ fixV Y).2 g hg
    have hle : shortU ↥(yuHol Y) ≤ shortC ↥(yuHol Y) := by
      intro x hx
      obtain ⟨u, rfl⟩ : x ∈ (yuInc Y).range := hU ▸ hx
      refine ⟨hx, Subgroup.mem_center_iff.mpr fun x' => ?_⟩
      have h4 := conj_yuInc Y x' u
      have h5 : (⟨x'.1.right u, apply_mem_commV_self Y x'.2.2 u.2⟩ : ↥(commV Y)) = u :=
        Subtype.ext (hfix u x'.1.right x'.2.2)
      rw [h5] at h4
      exact mul_inv_eq_iff_eq_mul.mp h4
    exact absurd hX.nonzero (not_lt_of_ge hle)
  have hW₀G : UGen Y W₀ W₀ :=
    ⟨le_rfl, hW₀inv, (commV_le_commOn_commV Y).trans (commOn_mono hUW₀)⟩
  obtain ⟨S, hS, hmin⟩ : ∃ S, UGen Y W₀ S ∧ ∀ S', UGen Y W₀ S' → S' ≤ S → S' = S := by
    obtain ⟨S, hS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup V))
      {S | UGen Y W₀ S} ⟨W₀, hW₀G⟩
    exact ⟨S, hS, fun S' hS' hle => by
      by_contra hne
      exact hmin S' hS' (lt_of_le_of_ne hle hne)⟩
  have hindec := minimal_indecomposable Y hV hX hU hUA hS hmin
  obtain ⟨hSW, hSinv, hUS⟩ := hS
  have hcommS : commOn Y S = commV Y := le_antisymm (commOn_le_commV S) hUS
  have hUsub : commV Y ≤ S := hcommS ▸ commOn_le_self hSinv
  let G_S : Subgroup (MulAut ↥S) := (resHomS Y S hSinv).range
  have hcommGS : commV G_S = (commV Y).subgroupOf S := by
    rw [← hcommS]
    exact commV_range_resHomS S hSinv
  have hVS : ∀ s : ↥S, s ^ 2 = 1 := fun s => Subtype.ext (by simpa using hV (s : V))
  have hind : ∀ A B : Subgroup ↥S, GInv G_S A → GInv G_S B → A ⊓ B = ⊥ → A ⊔ B = ⊤ →
      A = ⊥ ∨ B = ⊥ := by
    intro A B hA hB hinf hsup
    have hAinv : ∀ g ∈ Y, ∀ a ∈ A.map S.subtype, g a ∈ A.map S.subtype := by
      rintro g hg _ ⟨a, ha, rfl⟩
      exact ⟨resHomS Y S hSinv ⟨g, hg⟩ a, hA _ ⟨⟨g, hg⟩, rfl⟩ a ha, rfl⟩
    have hBinv : ∀ g ∈ Y, ∀ b ∈ B.map S.subtype, g b ∈ B.map S.subtype := by
      rintro g hg _ ⟨b, hb, rfl⟩
      exact ⟨resHomS Y S hSinv ⟨g, hg⟩ b, hB _ ⟨⟨g, hg⟩, rfl⟩ b hb, rfl⟩
    have hinf' : A.map S.subtype ⊓ B.map S.subtype = ⊥ := by
      rw [← Subgroup.map_inf_eq A B S.subtype S.subtype_injective, hinf, Subgroup.map_bot]
    have hsup' : A.map S.subtype ⊔ B.map S.subtype = S := by
      rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rcases hindec (A.map S.subtype) (B.map S.subtype) (by
        rintro _ ⟨a, -, rfl⟩; exact a.2) (by rintro _ ⟨b, -, rfl⟩; exact b.2) hAinv hBinv hinf'
        hsup' with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective A S.subtype_injective).mp h)
    · exact Or.inr ((Subgroup.map_eq_bot_iff_of_injective B S.subtype_injective).mp h)
  have hker_le : ∀ g : ↥Y, resHomS Y S hSinv g = 1 → yuTheta Y φ g = 1 := by
    intro g hg
    have hfixU : ∀ u : ↥(commV Y), (g : MulAut V) (u : V) = u := fun u => by
      have := congrArg (fun x : MulAut ↥S => ((x ⟨u, hUsub u.2⟩ : ↥S) : V)) hg
      exact this
    apply sl2_eq_one_of_mulVec_fix
    intro w
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have h1 := hβe g u
    have h2 : (⟨(g : MulAut V) (u : V), apply_mem_commV_self Y g.2 u.2⟩ : ↥(commV Y)) = u :=
      Subtype.ext (hfixU u)
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd, toAdd_ofAdd] at h3
    exact h3.symm
  have hker_ge : ∀ g : ↥Y, yuTheta Y φ g = 1 → resHomS Y S hSinv g = 1 := by
    intro g hg
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    exact hSW s.2 (Y.subtype g) ⟨g, (MonoidHom.mem_ker).mpr hg, rfl⟩
  let f : ↥Y →* ↥G_S := (resHomS Y S hSinv).rangeRestrict
  have hfs : Function.Surjective f := (resHomS Y S hSinv).rangeRestrict_surjective
  have hfker : f.ker ≤ (yuTheta Y φ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    apply hker_le
    have : f g = 1 := hg
    exact congrArg Subtype.val this
  let θS' : ↥G_S →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    MonoidHom.liftOfSurjective f hfs ⟨yuTheta Y φ, hfker⟩
  have hθS' : ∀ g, θS' (f g) = yuTheta Y φ g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply f _ _ ⟨yuTheta Y φ, hfker⟩ g
  have hθSinj : Function.Injective θS' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := hfs x
    rw [hθS'] at hx
    exact Subtype.ext (hker_ge g hx)
  have hθSsurj : Function.Surjective θS' := by
    intro a
    obtain ⟨g, hg⟩ := hθs a
    exact ⟨f g, by rw [hθS', hg]⟩
  let θS : ↥G_S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    MulEquiv.ofBijective θS' ⟨hθSinj, hθSsurj⟩
  have hmemU : ∀ p : ↥(commV G_S), ((p : ↥S) : V) ∈ commV Y := by
    intro p
    have h' : (p : ↥S) ∈ (commV Y).subgroupOf S := by
      rw [← hcommGS]
      exact p.2
    exact Subgroup.mem_subgroupOf.mp h'
  let eS : ↥(commV G_S) →* ↥(commV Y) :=
    { toFun := fun p => ⟨((p : ↥S) : V), hmemU p⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have heS_surj : Function.Surjective eS := by
    intro u
    refine ⟨⟨⟨u, hUsub u.2⟩, ?_⟩, rfl⟩
    rw [hcommGS, Subgroup.mem_subgroupOf]
    exact u.2
  let β : ↥(commV G_S) →* Multiplicative (Fin 2 → GaloisField 2 n) := βV.comp eS
  have hsec : IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (x : Multiplicative (Fin 2 → GaloisField 2 n)) => Multiplicative.ofAdd
        ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd x))) G_S
      (commV G_S) (commV G_S ⊓ fixV G_S) := by
    refine ⟨fun x hx p hp => commV_invariant hx hp, θS, β, hβs.comp heS_surj, ?_, ?_⟩
    · ext p
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h1 : eS p ∈ βV.ker := h
        rw [hβk, Subgroup.mem_subgroupOf] at h1
        refine ⟨p.2, fun x hx => ?_⟩
        obtain ⟨g, rfl⟩ := hx
        apply Subtype.ext
        exact h1.2 g g.2
      · rintro ⟨-, hp⟩
        have : eS p ∈ βV.ker := by
          rw [hβk, Subgroup.mem_subgroupOf]
          refine ⟨hmemU p, fun g hg => ?_⟩
          have := hp (resHomS Y S hSinv ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
          exact congrArg Subtype.val this
        exact this
    · intro x p hp
      obtain ⟨g, rfl⟩ := hfs x
      have h1 := hβe g (eS p)
      show βV (eS ⟨(f g : MulAut ↥S) p, hp⟩) = _
      rw [show θS (f g) = yuTheta Y φ g from hθS' g]
      exact h1
  have hmap : (commV G_S ⊓ fixV G_S).map S.subtype = commV Y ⊓ fixV Y := by
    ext x
    constructor
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      refine ⟨hmemU ⟨s, hs1⟩, fun g hg => ?_⟩
      have := hs2 (resHomS Y S hSinv ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
      exact congrArg Subtype.val this
    · rintro ⟨hx1, hx2⟩
      refine ⟨⟨x, hUsub hx1⟩, ⟨?_, ?_⟩, rfl⟩
      · rw [hcommGS]; exact hx1
      · rintro _ ⟨g, rfl⟩
        exact Subtype.ext (hx2 g g.2)
  have hcard : Nat.card ↥(commV Y ⊓ fixV Y) = Nat.card ↥(commV G_S ⊓ fixV G_S) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective S.subtype_injective
  rw [hcard]
  exact (hM2 n hn ↥S hVS G_S hind hsec).2

end Bound

theorem emb_four_five (hM2 : H1NaturalSL2) (hM4 : SchurMultL2Two) (V : Type) [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (Y : Subgroup (MulAut V)) (hY : ⁅Y, Y⁆ = Y)
    (hX : InClassX ↥(yuHol Y)) :
    Subgroup.center ↥Y = ⊥ ∨
      (Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        Nat.card ↥(Subgroup.center ↥Y) = 2 ∧ IsNaturalSLTwoModule ↥(yuHol Y) 2 ∧
        Nat.card ↥(commV ((Subgroup.center ↥Y).map Y.subtype)) ≤ Nat.card ↥(commV Y ⊓ fixV Y) ∧
        Nat.card ↥(commV Y ⊓ fixV Y) ≤ 4) := by
  rcases emb_four_five_core Y hM4 hV hY hX with h | ⟨hiso, hcard, hsl, hle⟩
  · exact Or.inl h
  · refine Or.inr ⟨hiso, hcard, hsl, hle, ?_⟩
    have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
    have h2 := emb_four_five_bound Y hM2 hV hX.1 (n := 2) le_rfl hsl
    simpa using h2

end CFSG.CGT.PushingUpLit.CGT6
