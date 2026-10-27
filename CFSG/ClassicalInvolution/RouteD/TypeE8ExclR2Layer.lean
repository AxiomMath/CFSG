module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Vis
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclTwin
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerStmt
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem le_centralizer_iff_single (c : ETCtx p f .E7 0 Ω K z) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {A : Subgroup (TypeE8.K7 p f)} (hA : A ∈ TypeE8.F7 p f)
    (hNA : locImg Ω z N = A.map c.d.ψ) {w : G} (hw : w ∈ locLayer Ω z) {r : TypeE8.K7 p f}
    (hr : c.d.ψ r = locElt Ω z w hw) :
    N ≤ Subgroup.centralizer ({w} : Set G) ↔
      A ≤ Subgroup.centralizer ({r} : Set (TypeE8.K7 p f)) := by
  have h1 := Gaps.le_centralizer_iff_locImg c.hΩ c.hP1 hN ⟨w, hw⟩
  have h2 := Gaps.le_centralizer_iff_map c.d.ψ c.d.ker_le (c.hY.perfR A hA) r
  have hmul : Gaps.locMk Ω z ⟨w, hw⟩ = c.d.ψ r := hr.symm
  rw [hmul, hNA] at h1
  exact h1.trans h2.symm

end ETCtx

end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair Linked NCEdge)
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_visible_equiv_D8 (c : ETCtx p f .E7 0 Ω K z) {w₁ w₂ : G}
    (hw₁ : w₁ ∈ locLayer Ω z) (hw₂ : w₂ ∈ locLayer Ω z) {r₁ r₂ : K7 p f}
    (hr₁ : c.d.ψ r₁ = locElt Ω z w₁ hw₁) (hr₂ : c.d.ψ r₂ = locElt Ω z w₂ hw₂)
    (hK₁ : K ≤ Subgroup.centralizer ({w₁} : Set G))
    (hK₂ : K ≤ Subgroup.centralizer ({w₂} : Set G)) {T : Subgroup (K7 p f)} (hT : T ∈ F7 p f)
    (hTvis : T ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)))
    (hLvis : ∀ A ∈ F7 p f, Commutes A T → A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)))
    {Nρ : Subgroup G} (hNρ : Nρ ∈ centralizingMembers Ω {z}) (hNρK : Nρ ≠ K)
    (hNρimg : locImg Ω z Nρ = T.map c.d.ψ)
    (hV1 : ∀ N ∈ centralizingMembers Ω {w₁ * w₂, z}, N ≠ K → N = Nρ ∨ Commutes Nρ N)
    (e : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} ≃ Fund12 p f)
    (he : ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {w₁ * w₂, z}} ≃ D8Layer p f,
      (∀ N N', Commutes N.1 N'.1 ↔ D8Layer.rel p f (φ N) (φ N')) ∧
        ∀ h : K ∈ centralizingMembers Ω {w₁ * w₂, z}, φ ⟨K, h⟩ = none := by
  classical
  have hKvis : K ∈ centralizingMembers Ω {w₁ * w₂, z} :=
    mem_centralizingMembers_pair.mpr ⟨⟨c.hK, le_centralizer_mul_of_le hK₁ hK₂⟩,
      le_centralizer_of_isClassicalMember c.hz⟩
  have hρvis : Nρ ∈ centralizingMembers Ω {w₁ * w₂, z} :=
    mem_centralizingMembers_pair.mpr ⟨⟨hNρ.1,
      (c.le_centralizer_mul_iff hNρ hT hNρimg hw₁ hw₂ hr₁ hr₂).mpr hTvis⟩, hNρ.2⟩
  have hmem : ∀ A : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T},
      ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = A.1.map c.d.ψ := fun A =>
    c.exists_member_of_fund A.2.1
  choose Lof hLz hLK hLimg using hmem
  have hLv : ∀ A, Lof A ∈ centralizingMembers Ω {w₁ * w₂, z} := fun A =>
    mem_centralizingMembers_pair.mpr ⟨⟨(hLz A).1,
      (c.le_centralizer_mul_iff (hLz A) A.2.1 (hLimg A) hw₁ hw₂ hr₁ hr₂).mpr
        (hLvis A.1 A.2.1 A.2.2)⟩, (hLz A).2⟩
  let ι : D8Layer p f → {N : Subgroup G // N ∈ centralizingMembers Ω {w₁ * w₂, z}} :=
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
      exact not_commutes_self_of_mem c.hΩ hNρ.1 this
    · exact absurd h (hLK _)
    · exfalso
      have := hLρ (e.symm R)
      simp only [ι] at h
      rw [h] at this
      exact not_commutes_self_of_mem c.hΩ hNρ.1 this
    · simp only [ι] at h
      have himg : (e.symm R).1.map c.d.ψ = (e.symm R').1.map c.d.ψ := by
        rw [← hLimg, ← hLimg, h]
      have := Gaps.eq_of_map_eq_of_central c.d.ψ c.d.ker_le (c.hY.perfR _ (e.symm R).2.1)
        (c.hY.perfR _ (e.symm R').2.1) himg
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
  have key : ∀ a b : D8Layer p f, Commutes (ι a).1 (ι b).1 ↔ D8Layer.rel p f a b := by
    intro a b
    rcases a with _ | _ | R <;> rcases b with _ | _ | R'
    · exact iff_false_intro (not_commutes_self_of_isClassicalMember c.hz)
    · exact iff_true_intro (c.commutes_K_of_ne hNρ hNρK)
    · exact iff_true_intro (c.commutes_K_of_ne (hLz _) (hLK _))
    · exact iff_true_intro (commutes_symm (c.commutes_K_of_ne hNρ hNρK))
    · exact iff_false_intro (not_commutes_self_of_mem c.hΩ hNρ.1)
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

theorem connected_of_fund12 (hC : Fund12Connected p f) {T : Subgroup (K7 p f)}
    (e : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} ≃ Fund12 p f)
    (he : ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1)
    (a b : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T}) :
    Relation.ReflTransGen (fun X Y : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} =>
      ¬ Commutes X.1 Y.1) a b := by
  have key : ∀ y : Fund12 p f, Relation.ReflTransGen
      (fun X Y : Fund12 p f => ¬ Commutes X.1 Y.1) (e a) y →
      Relation.ReflTransGen (fun X Y : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} =>
        ¬ Commutes X.1 Y.1) a (e.symm y) := by
    intro y h
    induction h with
    | refl => rw [Equiv.symm_apply_apply]
    | @tail y₁ y₂ _ hy ih =>
      refine ih.tail ?_
      intro hc
      apply hy
      have := (he (e.symm y₁) (e.symm y₂)).mp hc
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  have := key (e b) (hC (e a) (e b))
  rwa [Equiv.symm_apply_apply] at this

theorem linked_of_visible_D8 (c : ETCtx p f .E7 0 Ω K z) {w₁ w₂ : G}
    (hw₁ : w₁ ∈ locLayer Ω z) (hw₂ : w₂ ∈ locLayer Ω z) {r₁ r₂ : K7 p f}
    (hr₁ : c.d.ψ r₁ = locElt Ω z w₁ hw₁) (hr₂ : c.d.ψ r₂ = locElt Ω z w₂ hw₂)
    (hK₁ : K ≤ Subgroup.centralizer ({w₁} : Set G))
    (hK₂ : K ≤ Subgroup.centralizer ({w₂} : Set G)) {β : Subgroup G}
    (hβx : β ∈ centralizingMembers Ω {w₁ * w₂}) (hnKβ : ¬ Commutes K β)
    {T : Subgroup (K7 p f)} (hT : T ∈ F7 p f)
    (hTvis : T ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)))
    (hLvis : ∀ A ∈ F7 p f, Commutes A T → A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)))
    {Nρ : Subgroup G} (hNρ : Nρ ∈ centralizingMembers Ω {z}) (hNρK : Nρ ≠ K)
    (hNρimg : locImg Ω z Nρ = T.map c.d.ψ) (hβρ : ¬ Commutes β Nρ)
    (hV1 : ∀ N ∈ centralizingMembers Ω {w₁ * w₂, z}, N ≠ K → N = Nρ ∨ Commutes Nρ N)
    {A₀ : Subgroup (K7 p f)} (hA₀ : A₀ ∈ F7 p f) (hA₀T : Commutes A₀ T) {N₀ : Subgroup G}
    (hN₀ : N₀ ∈ centralizingMembers Ω {z}) (hN₀img : locImg Ω z N₀ = A₀.map c.d.ψ)
    (hβ₀ : ¬ Commutes β N₀)
    (hconn : ∀ a b : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T},
      Relation.ReflTransGen (fun X Y : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} =>
        ¬ Commutes X.1 Y.1) a b) :
    ∀ R ∈ centralizingMembers Ω {w₁ * w₂, z}, Linked Ω (w₁ * w₂) K R := by
  intro R hR
  have hKx : K ∈ centralizingMembers Ω {w₁ * w₂} :=
    ⟨c.hK, le_centralizer_mul_of_le hK₁ hK₂⟩
  have hmemx : ∀ {N : Subgroup G} {B : Subgroup (K7 p f)}, N ∈ centralizingMembers Ω {z} →
      B ∈ F7 p f → locImg Ω z N = B.map c.d.ψ →
      B ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)) →
      N ∈ centralizingMembers Ω {w₁ * w₂} := fun hN hB hNB hBc =>
    ⟨hN.1, (c.le_centralizer_mul_iff hN hB hNB hw₁ hw₂ hr₁ hr₂).mpr hBc⟩
  have hKβ : Linked Ω (w₁ * w₂) K β := Relation.ReflTransGen.single ⟨hKx, hβx, hnKβ⟩
  have hKρ : Linked Ω (w₁ * w₂) K Nρ := hKβ.trans (Relation.ReflTransGen.single
    ⟨hβx, hmemx hNρ hT hNρimg hTvis, hβρ⟩)
  have chain : ∀ a b : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T},
      Relation.ReflTransGen (fun X Y : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} =>
        ¬ Commutes X.1 Y.1) a b →
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

end CFSG.ClassicalInvolution.RouteD.TypeE8
