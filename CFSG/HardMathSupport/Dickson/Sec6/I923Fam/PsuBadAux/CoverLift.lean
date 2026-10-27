module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.RankThree.PerfectCover Subgroup

section Lift

variable {P Y : Type} [Group P] [Group Y]

theorem exists_hopf_endo_lift [Group.IsPerfect P] (θ : MulAut P) :
    ∃ a : HopfCover P →* HopfCover P, ∀ x, hopfCoverMap P (a x) = θ (hopfCoverMap P x) := by
  haveI : Group.IsPerfect (HopfCover P) := hopfCover_isPerfect
  set q : HopfCover P →* P := θ⁻¹.toMonoidHom.comp (hopfCoverMap P) with hqdef
  have hq : Function.Surjective q := θ⁻¹.surjective.comp hopfCoverMap_surjective
  have hker : q.ker ≤ center (HopfCover P) := by
    intro x hx
    apply hopfMultiplier_le_center (S := P)
    have h1 : θ⁻¹ (hopfCoverMap P x) = 1 := hx
    show hopfCoverMap P x = 1
    have := congrArg θ h1
    simpa using this
  refine ⟨hopfLift q hq hker, fun x => ?_⟩
  have h : θ⁻¹ (hopfCoverMap P (hopfLift q hq hker x)) = hopfCoverMap P x :=
    DFunLike.congr_fun (comp_hopfLift q hq hker) x
  have := congrArg θ h
  simpa using this

theorem exists_hopf_aut_lift [Group.IsPerfect P] (θ : MulAut P) :
    ∃ θ' : MulAut (HopfCover P), ∀ x, hopfCoverMap P (θ' x) = θ (hopfCoverMap P x) := by
  haveI : Group.IsPerfect (HopfCover P) := hopfCover_isPerfect
  obtain ⟨a, ha⟩ := exists_hopf_endo_lift θ
  obtain ⟨b, hb⟩ := exists_hopf_endo_lift θ⁻¹
  have hker : (hopfCoverMap P).ker ≤ center (HopfCover P) := hopfMultiplier_le_center
  have hba : b.comp a = MonoidHom.id _ := by
    refine hopfCover_hom_ext (hopfCoverMap P) hker _ _ ?_ rfl
    ext x
    change hopfCoverMap P (b (a x)) = hopfCoverMap P x
    rw [hb, ha]
    simp
  have hab : a.comp b = MonoidHom.id _ := by
    refine hopfCover_hom_ext (hopfCoverMap P) hker _ _ ?_ rfl
    ext x
    change hopfCoverMap P (a (b x)) = hopfCoverMap P x
    rw [ha, hb]
    simp
  exact ⟨MonoidHom.toMulEquiv a b hba hab, ha⟩

theorem map_eq_of_cyclic_of_le {G : Type*} [Group G] [Finite G] {M N : Subgroup G} [IsCyclic M]
    (hNM : N ≤ M) (f : MulAut G) (hfM : ∀ x ∈ M, f x ∈ M) :
    N.map f.toMonoidHom = N := by
  set K := N.map f.toMonoidHom with hK
  have hKM : K ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfM x (hNM hx)
  have hcard : Nat.card K = Nat.card N :=
    Subgroup.card_map_of_injective f.injective
  have h1 : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have h2 : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have heq : K.subgroupOf M = N.subgroupOf M :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [h1, h2, hcard])
  have := (Subgroup.subgroupOf_inj).1 heq
  rwa [inf_eq_left.2 hKM, inf_eq_left.2 hNM] at this

theorem exists_lift_aut_of_cyclic_multiplier [Finite P] [Group.IsPerfect P] [Finite Y]
    [Group.IsPerfect Y] (hM : IsCyclic (hopfMultiplier P)) (π : Y →* P)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center Y) (τ : MulAut P) :
    ∃ τY : MulAut Y, ∀ y, π (τY y) = τ (π y) := by
  classical
  haveI : Finite (HopfCover P) := finite_hopfCover inferInstance
  haveI : Group.IsPerfect (HopfCover P) := hopfCover_isPerfect
  obtain ⟨τh, hτh⟩ := exists_hopf_aut_lift τ
  set ψ := hopfLift π hπ hker with hψdef
  have hψsurj : Function.Surjective ψ := hopfLift_surjective π hπ hker
  have hψ : ∀ x, π (ψ x) = hopfCoverMap P x := fun x =>
    DFunLike.congr_fun (comp_hopfLift π hπ hker) x
  have hNM : ψ.ker ≤ hopfMultiplier P := fun x hx => by
    show hopfCoverMap P x = 1
    rw [← hψ, show ψ x = 1 from hx, map_one]
  have hτM : ∀ x ∈ hopfMultiplier P, τh x ∈ hopfMultiplier P := fun x hx => by
    show hopfCoverMap P (τh x) = 1
    rw [hτh]
    have : hopfCoverMap P x = 1 := hx
    rw [this, map_one]
  haveI : IsCyclic (hopfMultiplier P) := hM
  have hτN : ψ.ker.map τh.toMonoidHom = ψ.ker := map_eq_of_cyclic_of_le hNM τh hτM
  have hkerle : ψ.ker ≤ (ψ.comp τh.toMonoidHom).ker := by
    intro x hx
    have : τh x ∈ ψ.ker.map τh.toMonoidHom := ⟨x, hx, rfl⟩
    rw [hτN] at this
    exact this
  set τY : Y →* Y := MonoidHom.liftOfSurjective ψ hψsurj ⟨ψ.comp τh.toMonoidHom, hkerle⟩ with hτY
  have hτYψ : ∀ x, τY (ψ x) = ψ (τh x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ.comp τh.toMonoidHom, hkerle⟩ x
  have hτYsurj : Function.Surjective τY := by
    intro y
    obtain ⟨x, rfl⟩ := hψsurj y
    obtain ⟨x', rfl⟩ := τh.surjective x
    exact ⟨ψ x', hτYψ x'⟩
  have hτYinj : Function.Injective τY := Finite.injective_iff_surjective.2 hτYsurj
  refine ⟨MulEquiv.ofBijective τY ⟨hτYinj, hτYsurj⟩, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hψsurj y
  change π (τY (ψ x)) = τ (π (ψ x))
  rw [hτYψ, hψ, hψ, hτh]

end Lift

end CFSG.HardMathSupport.Dickson.Sec6.I923
