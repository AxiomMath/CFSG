module

public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase
public import CFSG.ClassicalInvolution.RouteD.TwinTenNodes
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def D4LinearClique (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (φ : (modelUniv t n p e Fact.out).K →* X), φ.ker ≤ Subgroup.center _ →
    ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        ∀ R₃ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R₁ ≠ R₂ → Commutes R₁ R₂ →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map φ) (R₃.map φ)) →
          ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₂.map φ) (R₃.map φ)

@[expose] def TwinSL4Action (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSL 4 (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ j : Fin 3 → Subgroup G, (∀ a, j a ∈ conjClass K) → (∀ a, Commutes K (j a)) →
          (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) → Commutes (j 1) (j 2) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 1)) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 2)) →
          ∀ x₀ : G, IsClassicalMember p f (j 1) x₀ →
            j 0 ≤ Subgroup.centralizer ({t * x₀} : Set G)

theorem twinSL4Bridge_of_inputs (hP1 : ProductOfTwoP1 p f)
    (hD4 : D4LinearClique p f .POmegaPlus 4 f) (hAct : TwinSL4Action p f) :
    TwinSL4Bridge p f := by
  intro G _ _ _ hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02
  classical
  have hcen := center_eq_bot hnab
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hf : 0 < f := pos_of_five_le S.five
  have hMFZ := Gaps.fundNoncentral p
  obtain ⟨x₀, hx₀⟩ := hΩ.classical (j 1) (hjΩ 1)
  have hj0 : j 0 ≤ Subgroup.centralizer ({t * x₀} : Set G) :=
    hAct G hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02 x₀ hx₀
  obtain ⟨W₀, hW₀⟩ := hKβ
  obtain ⟨g, hg⟩ := hβ
  have htg : t = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd) (hex β ⟨g, hg⟩) ht
      (hg ▸ S.cls.conj g)
  have hP1t : LocalOddCentral (conjClass K) {t} := by
    rw [htg]
    exact Gaps.localOddCentral_conj hΩ.conjInvariant g z S.p1
  have hshape_t : LocalShapeT p f 2 .PSL 4 (conjClass K) t := by
    rw [htg]
    exact hshape.conj hΩ.conjInvariant g
  obtain ⟨Dt, hcard, i₁, htag, hrank, hrest⟩ := hshape_t
  have hbig : ¬ (Dt.tag i₁ = .PSL ∧ Dt.rank i₁ = 2) := by
    rintro ⟨-, h⟩
    rw [hrank] at h
    omega
  have hβΩ : β ∈ conjClass K := ⟨g, hg⟩
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g β := single_class_of_mem hβΩ
  obtain ⟨T, hT, hTβ, hTcomm⟩ := exists_twin_of_layer hMFZ hΩ hex hP1t Dt i₁ (by omega) hrest
    hbig hβΩ ht
  have hnotK : ¬ K ≤ Subgroup.centralizer ({t} : Set G) :=
    S.not_le_centralizer_of_linear hcen (mem_conjClass_self K) hβΩ ht ⟨W₀, hW₀⟩
  have hKx₀ : K ≤ Subgroup.centralizer ({x₀} : Set G) := le_centralizer_of_commutes (hjK 1) hx₀.mem
  have htx : t ≠ x₀ := by
    intro h
    apply hnotK
    rw [h]
    exact hKx₀
  have hj1β : Commutes β (j 1) := hjβ 1 (by decide)
  have hj1t : j 1 ∈ centralizingMembers (conjClass K) {t} :=
    ⟨hjΩ 1, le_centralizer_of_commutes (Commutes.symm hj1β) ht.mem⟩
  have hj1ne : j 1 ≠ β := fun h =>
    not_commutes_of_linearBlockStandardPair hW₀ (h ▸ hjK 1)
  have hj1T : j 1 ≠ T := by
    intro h
    have hTx : IsClassicalMember p f T x₀ := h ▸ hx₀
    have heq := centralizingMembers_eq_of_twin S.odd hf hΩ ht hTx (hsingle T hT.1) hT hTcomm
    have hKmem : K ∈ centralizingMembers (conjClass K) {x₀} := ⟨mem_conjClass_self K, hKx₀⟩
    rw [heq] at hKmem
    exact hnotK hKmem.2
  have hP1x : LocalOddCentral (conjClass K) {t * x₀} := by
    have := hP1 G hnab β t (S.of_mem_conjClass hβΩ ht) (j 1)
      (by rw [conjClass_eq_of_mem hβΩ]; exact hjΩ 1) x₀ hx₀ hj1β htx
    rwa [conjClass_eq_of_mem hβΩ] at this
  have hj0β : j 0 ≠ β := fun h =>
    not_commutes_of_linearBlockStandardPair hW₀ (h ▸ hjK 0)
  have hnc : ¬ Commutes β (j 0) := by
    intro hc
    have h1 : j 0 ≤ Subgroup.centralizer ({t} : Set G) :=
      le_centralizer_of_commutes (Commutes.symm hc) ht.mem
    have h2 : j 0 ≤ Subgroup.centralizer ({x₀} : Set G) := fun n hn =>
      mem_centralizer_right_of_mul (hj0 hn) (h1 hn)
    exact S.not_le_centralizer_of_linear hcen (hjΩ 0) (hjΩ 1) hx₀ hp01 h2
  have hlink : LinkedAtProduct (conjClass K) β t x₀ := ⟨j 0, ⟨hjΩ 0, hj0⟩, hj0β, hnc⟩
  obtain ⟨D, c, htg4, hrk, hexp, -, hβc, hj1c, -, hallc⟩ :=
    exists_d4_component_of_twin_product S.odd S.five hcen hΩ hex S.ih hβΩ hsingle ht hP1t hT hTβ
      hTcomm hj1t hj1ne hj1T hx₀ htx hP1x hlink
  have hj0c := hallc (j 0) ⟨hjΩ 0, hj0⟩ hj0β hnc
  have hperf := fundPerfect_modelUniv S.odd (D.isFundTag c) (D.admissible c)
    (by rw [hexp]; have := S.five; omega)
  obtain ⟨R₁, hR₁⟩ := exists_corr_left hΩ hex D hj1c
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D hβc
  obtain ⟨R₃, hR₃⟩ := exists_corr_left hΩ hex D hj0c
  have hne : R₁ ≠ R₂ := fun h => hj1ne (corr_unique_right hΩ hP1x hR₁ (h ▸ hR₂))
  have hcomm : Commutes R₁ R₂ :=
    (corr_commutes hΩ hP1x hperf hR₁ hR₂).mp (Commutes.symm hj1β)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_locImg_of_members hP1x hj1c.1 hj0c.1
    (linearBlockStandardPair_symm hp01.choose_spec)
  rw [hR₁.2.2, hR₃.2.2] at hW₁
  have hD4' : D4LinearClique p f (D.tag c) (D.rank c) (D.exp c) := by
    rw [htg4, hrk, hexp]
    exact hD4
  obtain ⟨W₂, hW₂⟩ := hD4' _ (D.hom c) (D.ker_le_center c) R₁ hR₁.2.1 R₂ hR₂.2.1 R₃ hR₃.2.1 hne
    hcomm ⟨W₁, hW₁⟩
  rw [← hR₂.2.2, ← hR₃.2.2] at hW₂
  exact linearBlockStandardPair_of_locImg (by have := S.five; omega) (oddCoverSL3 S.five) hΩ hP1x
    hβc.1 hj0c.1 hW₂

theorem pieceTwinSL4_of_inputs (hP1 : ProductOfTwoP1 p f)
    (hD4 : D4LinearClique p f .POmegaPlus 4 f) (hAct : TwinSL4Action p f) :
    PieceTwinSL4 p f :=
  pieceTwinSL4_of_bridge (twinSL4Bridge_of_inputs hP1 hD4 hAct)

@[expose] def TwinSL4ActionU (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSL 4 (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ j : Fin 3 → Subgroup G, (∀ a, j a ∈ conjClass K) → (∀ a, Commutes K (j a)) →
          (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) → Commutes (j 1) (j 2) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 1)) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 2)) →
          ∀ w₁ : G, IsClassicalMember p f (j 0) w₁ → β ≤ Subgroup.centralizer ({z * w₁} : Set G)

theorem twinSL4Bridge_of_inputs_u (hP1 : ProductOfTwoP1 p f)
    (hD4 : D4LinearClique p f .POmegaPlus 4 f) (hAct : TwinSL4ActionU p f) :
    TwinSL4Bridge p f := by
  intro G _ _ _ hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02
  classical
  have hcen := center_eq_bot hnab
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hf : 0 < f := pos_of_five_le S.five
  have hMFZ := Gaps.fundNoncentral p
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  obtain ⟨w₁, hw₁⟩ := hΩ.classical (j 0) (hjΩ 0)
  have hβu : β ≤ Subgroup.centralizer ({z * w₁} : Set G) :=
    hAct G hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02 w₁ hw₁
  obtain ⟨W₀, hW₀⟩ := hKβ
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  have hj1z : j 1 ∈ centralizingMembers (conjClass K) {z} :=
    ⟨hjΩ 1, le_centralizer_of_commutes (Commutes.symm (hjK 1)) S.cls.mem⟩
  have hj0z : j 0 ∈ centralizingMembers (conjClass K) {z} :=
    ⟨hjΩ 0, le_centralizer_of_commutes (Commutes.symm (hjK 0)) S.cls.mem⟩
  obtain ⟨Wj, hWj⟩ := hp01
  have hj01nc : ¬ Commutes (j 0) (j 1) := not_commutes_of_linearBlockStandardPair hWj
  have hj01ne : j 1 ≠ j 0 := fun h => ne_of_linearBlockStandardPair hWj h.symm
  have hzw : z ≠ w₁ := by
    intro h
    have hj1w : j 1 ∈ centralizingMembers (conjClass K) {w₁} := by rw [← h]; exact hj1z
    rcases S.cp_at_member hcen (hjΩ 0) hw₁ hj1w with hc | he
    · exact hj01nc hc
    · exact hj01ne he
  obtain ⟨Dz, hcard, i₁, htag, hrank, hrest⟩ := hshape
  have hbig : ¬ (Dz.tag i₁ = .PSL ∧ Dz.rank i₁ = 2) := by
    rintro ⟨-, h⟩
    rw [hrank] at h
    omega
  obtain ⟨T, hT, hTK, hTcomm⟩ := exists_twin_of_layer hMFZ hΩ hex S.p1 Dz i₁ (by omega) hrest hbig
    hKΩ S.cls
  have hj0K : j 0 ≠ K := fun h => by
    have := hjK 0
    rw [h] at this
    exact not_commutes_self_of_mem hΩ hKΩ this
  have hj0T : j 0 ≠ T := fun h => hj01nc (by rw [h]; exact hTcomm (j 1) hj1z (h ▸ hj01ne))
  have hP1x : LocalOddCentral (conjClass K) {z * w₁} :=
    hP1 G hnab K z S (j 0) (hjΩ 0) w₁ hw₁ (hjK 0) hzw
  have hβK : β ≠ K := fun h => ne_of_linearBlockStandardPair hW₀ h.symm
  have hnc : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hlink : LinkedAtProduct (conjClass K) K z w₁ := ⟨β, ⟨hβ, hβu⟩, hβK, hnc⟩
  obtain ⟨D, c, htg4, hrk, hexp, -, hKc, hj0c, -, hallc⟩ :=
    exists_d4_component_of_twin_product S.odd S.five hcen hΩ hex S.ih hKΩ (single_class K) S.cls
      S.p1 hT hTK hTcomm hj0z hj0K hj0T hw₁ hzw hP1x hlink
  have hβc := hallc β ⟨hβ, hβu⟩ hβK hnc
  have hperf := fundPerfect_modelUniv S.odd (D.isFundTag c) (D.admissible c)
    (by rw [hexp]; have := S.five; omega)
  obtain ⟨R₁, hR₁⟩ := exists_corr_left hΩ hex D hKc
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D hj0c
  obtain ⟨R₃, hR₃⟩ := exists_corr_left hΩ hex D hβc
  have hne : R₁ ≠ R₂ := fun h => hj0K (corr_unique_right hΩ hP1x hR₂ (h ▸ hR₁))
  have hcomm : Commutes R₁ R₂ :=
    (corr_commutes hΩ hP1x hperf hR₁ hR₂).mp (hjK 0)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_locImg_of_members hP1x hKc.1 hβc.1 hW₀
  rw [hR₁.2.2, hR₃.2.2] at hW₁
  have hD4' : D4LinearClique p f (D.tag c) (D.rank c) (D.exp c) := by
    rw [htg4, hrk, hexp]
    exact hD4
  obtain ⟨W₂, hW₂⟩ := hD4' _ (D.hom c) (D.ker_le_center c) R₁ hR₁.2.1 R₂ hR₂.2.1 R₃ hR₃.2.1 hne
    hcomm ⟨W₁, hW₁⟩
  rw [← hR₂.2.2, ← hR₃.2.2] at hW₂
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_of_locImg (by have := S.five; omega)
    (oddCoverSL3 S.five) hΩ hP1x hj0c.1 hβc.1 hW₂
  exact ⟨W', linearBlockStandardPair_symm hW'⟩

theorem pieceTwinSL4_of_inputs_u (hP1 : ProductOfTwoP1 p f)
    (hD4 : D4LinearClique p f .POmegaPlus 4 f) (hAct : TwinSL4ActionU p f) :
    PieceTwinSL4 p f :=
  pieceTwinSL4_of_bridge (twinSL4Bridge_of_inputs_u hP1 hD4 hAct)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
