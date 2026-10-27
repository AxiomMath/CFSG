module

public import CFSG.ClassicalInvolution.Q3.Q3E8BBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair Linked)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_visible_equiv_D8_3 (c : ETCtx3 .E7 0 Ω K z) {w₁ w₂ : G}
    (hw₁ : w₁ ∈ locLayer Ω z) (hw₂ : w₂ ∈ locLayer Ω z) {r₁ r₂ : TypeE8.K7 3 1}
    (hr₁ : c.d.ψ r₁ = locElt Ω z w₁ hw₁) (hr₂ : c.d.ψ r₂ = locElt Ω z w₂ hw₂)
    (hK₁ : K ≤ Subgroup.centralizer ({w₁} : Set G))
    (hK₂ : K ≤ Subgroup.centralizer ({w₂} : Set G)) {T : Subgroup (TypeE8.K7 3 1)}
    (hT : T ∈ TypeE8.F7 3 1)
    (hTvis : T ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)))
    (hLvis : ∀ A ∈ TypeE8.F7 3 1, Commutes A T →
      A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)))
    {Nρ : Subgroup G} (hNρ : Nρ ∈ centralizingMembers Ω {z}) (hNρK : Nρ ≠ K)
    (hNρimg : locImg Ω z Nρ = T.map c.d.ψ)
    (hV1 : ∀ N ∈ centralizingMembers Ω {w₁ * w₂, z}, N ≠ K → N = Nρ ∨ Commutes Nρ N)
    (e : {A : Subgroup (TypeE8.K7 3 1) // A ∈ TypeE8.F7 3 1 ∧ Commutes A T} ≃
      TypeE8.Fund12 3 1)
    (he : ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {w₁ * w₂, z}} ≃ TypeE8.D8Layer 3 1,
      (∀ N N', Commutes N.1 N'.1 ↔ TypeE8.D8Layer.rel 3 1 (φ N) (φ N')) ∧
        ∀ h : K ∈ centralizingMembers Ω {w₁ * w₂, z}, φ ⟨K, h⟩ = none := by
  classical
  have hKmul : K ≤ Subgroup.centralizer ({w₁ * w₂} : Set G) := fun k hk => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.mul_right
      (Subgroup.mem_centralizer_singleton_iff.mp (hK₁ hk) : Commute k w₁)
      (Subgroup.mem_centralizer_singleton_iff.mp (hK₂ hk) : Commute k w₂)).eq
  have hKvis : K ∈ centralizingMembers Ω {w₁ * w₂, z} :=
    mem_centralizingMembers_pair.mpr ⟨⟨c.hK, hKmul⟩, isSubnormal_le c.hz.subnormal⟩
  have hρvis : Nρ ∈ centralizingMembers Ω {w₁ * w₂, z} :=
    mem_centralizingMembers_pair.mpr ⟨⟨hNρ.1,
      (c.le_centralizer_mul_iff hNρ hT hNρimg hw₁ hw₂ hr₁ hr₂).mpr hTvis⟩, hNρ.2⟩
  have hNρself : ¬ Commutes Nρ Nρ := by
    obtain ⟨w, hw⟩ := c.hΩ.classical Nρ hNρ.1
    exact not_commutes_self3 hw
  have hmem : ∀ A : {A : Subgroup (TypeE8.K7 3 1) // A ∈ TypeE8.F7 3 1 ∧ Commutes A T},
      ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = A.1.map c.d.ψ := fun A =>
    c.exists_member_of_fund A.2.1
  choose Lof hLz hLK hLimg using hmem
  have hLv : ∀ A, Lof A ∈ centralizingMembers Ω {w₁ * w₂, z} := fun A =>
    mem_centralizingMembers_pair.mpr ⟨⟨(hLz A).1,
      (c.le_centralizer_mul_iff (hLz A) A.2.1 (hLimg A) hw₁ hw₂ hr₁ hr₂).mpr
        (hLvis A.1 A.2.1 A.2.2)⟩, (hLz A).2⟩
  let ι : TypeE8.D8Layer 3 1 → {N : Subgroup G // N ∈ centralizingMembers Ω {w₁ * w₂, z}} :=
    fun a => match a with
      | none => ⟨K, hKvis⟩
      | some none => ⟨Nρ, hρvis⟩
      | some (some R) => ⟨Lof (e.symm R), hLv _⟩
  have hLρ : ∀ A, Commutes (Lof A) Nρ := fun A =>
    (c.commutes_iff_fund (hLz A) hNρ A.2.1 (hLimg A) hNρimg).mpr A.2.2
  have hinj : Function.Injective ι := by
    intro a b hab
    have h := congrArg Subtype.val hab
    rcases a with _ | _ | R <;> rcases b with _ | _ | R'
    · rfl
    · exact absurd h.symm hNρK
    · exact absurd h.symm (hLK _)
    · exact absurd h hNρK
    · rfl
    · exfalso
      have := hLρ (e.symm R')
      simp only [ι] at h
      rw [← h] at this
      exact hNρself this
    · exact absurd h (hLK _)
    · exfalso
      have := hLρ (e.symm R)
      simp only [ι] at h
      rw [h] at this
      exact hNρself this
    · simp only [ι] at h
      have himg : (e.symm R).1.map c.d.ψ = (e.symm R').1.map c.d.ψ := by
        rw [← hLimg, ← hLimg, h]
      have := eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 _ (e.symm R).2.1)
        (c.hY.pow3 _ (e.symm R').2.1) himg
      have := e.symm.injective (Subtype.ext this)
      rw [this]
  have hsurj : Function.Surjective ι := by
    rintro ⟨N, hN⟩
    by_cases hNK : N = K
    · exact ⟨none, Subtype.ext hNK.symm⟩
    rcases hV1 N hN hNK with hNρ' | hcomm
    · exact ⟨some none, Subtype.ext hNρ'.symm⟩
    · obtain ⟨⟨hNΩ, hNx⟩, hNz'⟩ := mem_centralizingMembers_pair.mp hN
      have hNz : N ∈ centralizingMembers Ω {z} := ⟨hNΩ, hNz'⟩
      obtain ⟨A, hA, hNA⟩ := c.exists_fund_of_ne hNz hNK
      have hAT : Commutes A T :=
        commutes_symm ((c.commutes_iff_fund hNρ hNz hT hNρimg hNA).mp hcomm)
      refine ⟨some (some (e ⟨A, hA, hAT⟩)), Subtype.ext ?_⟩
      show Lof (e.symm (e ⟨A, hA, hAT⟩)) = N
      rw [Equiv.symm_apply_apply]
      exact c.eq_of_locImg_eq (hLz _) hNz ((hLimg _).trans hNA.symm)
  have key : ∀ a b : TypeE8.D8Layer 3 1,
      Commutes (ι a).1 (ι b).1 ↔ TypeE8.D8Layer.rel 3 1 a b := by
    intro a b
    rcases a with _ | _ | R <;> rcases b with _ | _ | R'
    · exact iff_false_intro (not_commutes_self3 c.hz)
    · exact iff_true_intro (c.commutes_K_of_ne hNρ hNρK)
    · exact iff_true_intro (c.commutes_K_of_ne (hLz _) (hLK _))
    · exact iff_true_intro (commutes_symm (c.commutes_K_of_ne hNρ hNρK))
    · exact iff_false_intro hNρself
    · exact iff_true_intro (commutes_symm (hLρ _))
    · exact iff_true_intro (commutes_symm (c.commutes_K_of_ne (hLz _) (hLK _)))
    · exact iff_true_intro (hLρ _)
    · refine (c.commutes_iff_fund (hLz _) (hLz _) (e.symm R).2.1 (hLimg _) (hLimg _)).trans ?_
      have := he (e.symm R) (e.symm R')
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact this
  refine ⟨(Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm, fun N N' => ?_, fun h => ?_⟩
  · have h1 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N) = N :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N
    have h2 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N') = N' :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N'
    have := key ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N)
      ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N')
    rwa [h1, h2] at this
  · exact (Equiv.symm_apply_eq _).mpr (Subtype.ext rfl)

theorem linked_of_visible_D8_3 (c : ETCtx3 .E7 0 Ω K z) {w₁ w₂ : G}
    (hw₁ : w₁ ∈ locLayer Ω z) (hw₂ : w₂ ∈ locLayer Ω z) {r₁ r₂ : TypeE8.K7 3 1}
    (hr₁ : c.d.ψ r₁ = locElt Ω z w₁ hw₁) (hr₂ : c.d.ψ r₂ = locElt Ω z w₂ hw₂)
    (hK₁ : K ≤ Subgroup.centralizer ({w₁} : Set G))
    (hK₂ : K ≤ Subgroup.centralizer ({w₂} : Set G)) {β : Subgroup G}
    (hβx : β ∈ centralizingMembers Ω {w₁ * w₂}) (hnKβ : ¬ Commutes K β)
    {T : Subgroup (TypeE8.K7 3 1)} (hT : T ∈ TypeE8.F7 3 1)
    (hTvis : T ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)))
    (hLvis : ∀ A ∈ TypeE8.F7 3 1, Commutes A T →
      A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)))
    {Nρ : Subgroup G} (hNρ : Nρ ∈ centralizingMembers Ω {z}) (hNρK : Nρ ≠ K)
    (hNρimg : locImg Ω z Nρ = T.map c.d.ψ) (hβρ : ¬ Commutes β Nρ)
    (hV1 : ∀ N ∈ centralizingMembers Ω {w₁ * w₂, z}, N ≠ K → N = Nρ ∨ Commutes Nρ N)
    {A₀ : Subgroup (TypeE8.K7 3 1)} (hA₀ : A₀ ∈ TypeE8.F7 3 1) (hA₀T : Commutes A₀ T)
    {N₀ : Subgroup G} (hN₀ : N₀ ∈ centralizingMembers Ω {z})
    (hN₀img : locImg Ω z N₀ = A₀.map c.d.ψ) (hβ₀ : ¬ Commutes β N₀)
    (hconn : ∀ a b : {A : Subgroup (TypeE8.K7 3 1) // A ∈ TypeE8.F7 3 1 ∧ Commutes A T},
      Relation.ReflTransGen (fun X Y : {A : Subgroup (TypeE8.K7 3 1) //
        A ∈ TypeE8.F7 3 1 ∧ Commutes A T} => ¬ Commutes X.1 Y.1) a b) :
    ∀ R ∈ centralizingMembers Ω {w₁ * w₂, z}, Linked Ω (w₁ * w₂) K R := by
  intro R hR
  have hKmul : K ≤ Subgroup.centralizer ({w₁ * w₂} : Set G) := fun k hk => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.mul_right
      (Subgroup.mem_centralizer_singleton_iff.mp (hK₁ hk) : Commute k w₁)
      (Subgroup.mem_centralizer_singleton_iff.mp (hK₂ hk) : Commute k w₂)).eq
  have hKx : K ∈ centralizingMembers Ω {w₁ * w₂} := ⟨c.hK, hKmul⟩
  have hmemx : ∀ {N : Subgroup G} {B : Subgroup (TypeE8.K7 3 1)},
      N ∈ centralizingMembers Ω {z} → B ∈ TypeE8.F7 3 1 → locImg Ω z N = B.map c.d.ψ →
      B ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)) →
      N ∈ centralizingMembers Ω {w₁ * w₂} := fun hN hB hNB hBc =>
    ⟨hN.1, (c.le_centralizer_mul_iff hN hB hNB hw₁ hw₂ hr₁ hr₂).mpr hBc⟩
  have hKβ : Linked Ω (w₁ * w₂) K β := Relation.ReflTransGen.single ⟨hKx, hβx, hnKβ⟩
  have hKρ : Linked Ω (w₁ * w₂) K Nρ := hKβ.trans (Relation.ReflTransGen.single
    ⟨hβx, hmemx hNρ hT hNρimg hTvis, hβρ⟩)
  have chain : ∀ a b : {A : Subgroup (TypeE8.K7 3 1) // A ∈ TypeE8.F7 3 1 ∧ Commutes A T},
      Relation.ReflTransGen (fun X Y : {A : Subgroup (TypeE8.K7 3 1) //
        A ∈ TypeE8.F7 3 1 ∧ Commutes A T} => ¬ Commutes X.1 Y.1) a b →
      ∀ N N' : Subgroup G, N ∈ centralizingMembers Ω {z} → N' ∈ centralizingMembers Ω {z} →
        locImg Ω z N = a.1.map c.d.ψ → locImg Ω z N' = b.1.map c.d.ψ →
        Linked Ω (w₁ * w₂) N N' := by
    intro a b h
    induction h with
    | refl =>
      intro N N' hN hN' hNB hN'B
      have : N = N' := c.eq_of_locImg_eq hN hN' (hNB.trans hN'B.symm)
      rw [this]
      exact Relation.ReflTransGen.refl
    | @tail b₁ b₂ _ hb ih =>
      intro N N' hN hN' hNB hN'B
      obtain ⟨M, hM, -, hMimg⟩ := c.exists_member_of_fund b₁.2.1
      refine (ih N M hN hM hNB hMimg).trans (Relation.ReflTransGen.single
        ⟨hmemx hM b₁.2.1 hMimg (hLvis _ b₁.2.1 b₁.2.2), hmemx hN' b₂.2.1 hN'B
          (hLvis _ b₂.2.1 b₂.2.2), ?_⟩)
      intro hc
      exact hb ((c.commutes_iff_fund hM hN' b₁.2.1 hMimg hN'B).mp hc)
  obtain ⟨⟨hRΩ, hRx⟩, hRz'⟩ := mem_centralizingMembers_pair.mp hR
  have hRz : R ∈ centralizingMembers Ω {z} := ⟨hRΩ, hRz'⟩
  by_cases hRK : R = K
  · subst hRK
    exact Relation.ReflTransGen.refl
  rcases hV1 R hR hRK with hRρ | hcomm
  · rw [hRρ]
    exact hKρ
  · obtain ⟨B, hB, hRB⟩ := c.exists_fund_of_ne hRz hRK
    have hBT : Commutes B T :=
      commutes_symm ((c.commutes_iff_fund hNρ hRz hT hNρimg hRB).mp hcomm)
    have hRδ : Linked Ω (w₁ * w₂) R N₀ :=
      chain ⟨B, hB, hBT⟩ ⟨A₀, hA₀, hA₀T⟩ (hconn _ _) R N₀ hRz hN₀ hRB hN₀img
    have hKδ : Linked Ω (w₁ * w₂) K N₀ := hKβ.trans (Relation.ReflTransGen.single
      ⟨hβx, hmemx hN₀ hA₀ hN₀img (hLvis _ hA₀ hA₀T), hβ₀⟩)
    exact hKδ.trans hRδ.symm

end Layer

end CFSG.ClassicalInvolution.Q3.Q3W
