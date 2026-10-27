module

public import CFSG.ClassicalInvolution.Q3.Q3TCD4
public import CFSG.ClassicalInvolution.Q3.Q3TCP1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.ClassicalInvolution.RouteD.NonClassical (le_centralizer_of_commutes)

theorem statedLieAdmissible_sl4_three : StatedLieAdmissible .PSL 4 3 1 :=
  ⟨Nat.prime_three, Nat.one_pos, by show 2 ≤ 4; omega,
    fun h => by have := congrArg Prod.fst h; simp at this,
    fun h => by have := congrArg Prod.fst h; simp at this⟩

theorem statedLieAdmissible_plus4_three : StatedLieAdmissible .POmegaPlus 4 3 1 :=
  ⟨Nat.prime_three, Nat.one_pos, le_rfl⟩

section Statements


@[expose] def TwinSL4Action3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z →
      ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        ∀ j : Fin 3 → Subgroup G, (∀ a, j a ∈ conjClass3 K) → (∀ a, Commutes K (j a)) →
          (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) → Commutes (j 1) (j 2) →
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j 0) (j 1)) →
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j 0) (j 2)) →
          ∀ x₀ : G, IsClassicalMember3 (j 1) x₀ → j 0 ≤ Subgroup.centralizer ({t * x₀} : Set G)

@[expose] def D4LinearClique3 : Prop :=
  ∀ R₁ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
    ∀ R₂ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
      ∀ R₃ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
        Commutes R₁ R₂ → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₃) →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃

@[expose] def TwinSL4Bridge3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z →
      ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        ∀ j : Fin 3 → Subgroup G, (∀ a, j a ∈ conjClass3 K) → (∀ a, Commutes K (j a)) →
          (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) → Commutes (j 1) (j 2) →
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j 0) (j 1)) →
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j 0) (j 2)) →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (j 0)

end Statements

section Lift

theorem not_three_dvd_card_center_of_cop {K : Type} [Group K] [Finite K]
    (h : ∀ w ∈ Subgroup.center K, ¬ 3 ∣ orderOf w) : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 3 h3
  exact h (x : K) x.2 (by rw [Subgroup.orderOf_coe, hx])


theorem exists_lin_of_map_pow3 {KY X : Type} [Group KY] [Group X] [Finite KY]
    (hC : ¬ 3 ∣ Nat.card (Subgroup.center KY)) (ψ : KY →* X)
    (hker : ψ.ker ≤ Subgroup.center KY) {R₁ R₂ : Subgroup KY} (hR₁ : Pow3 R₁) (hR₂ : Pow3 R₂)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := WeakCT.pair_normalize hW
  have hWsup := Gaps.linear_eq_sup hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : SL(3, GaloisField 3 1) →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπC : ¬ 3 ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hπker))
  obtain ⟨α, hα, -⟩ := ModelFacts.LinearAut.sl_existsUnique_lift (n := 3) (K := GaloisField 3 1)
    (p := 3) (by norm_num) hπ hπker hπC θ'
  have hαψ : ∀ s, ψ (α s) = θ s := fun s => congrArg Subtype.val (DFunLike.congr_fun hα s)
  have hψα : ψ.comp α = θ := MonoidHom.ext hαψ
  have hcop : ∀ z ∈ ψ.ker, ¬ 3 ∣ orderOf z := fun z hz h3 =>
    hC (h3.trans (Subgroup.orderOf_dvd_natCard _ (hker hz)))
  have hp₁ : Pow3 ((B12 (GaloisField 3 1)).map α) := (pow3_range_sl2 card_gf3 _).map α
  have hp₂ : Pow3 ((B23 (GaloisField 3 1)).map α) := (pow3_range_sl2 card_gf3 _).map α
  have hR₁' : (B12 (GaloisField 3 1)).map α = R₁ :=
    eq_of_map_eq_of_pow3 ψ hker hcop hp₁ hR₁ (by rw [Subgroup.map_map, hψα, hU])
  have hR₂' : (B23 (GaloisField 3 1)).map α = R₂ :=
    eq_of_map_eq_of_pow3 ψ hker hcop hp₂ hR₂ (by rw [Subgroup.map_map, hψα, hV])
  have hid : (MulAut.conj (1 : SL(3, GaloisField 3 1))⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  refine ⟨α.range, α, 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hαψ, hs, map_one]
  · rw [hid, Subgroup.map_id, hR₁']
  · rw [hid, Subgroup.map_id, hR₂']

end Lift

section Bridge


theorem twinSL4Bridge3_of_inputs (hTw : MFTwin3) (h3 : OddThreeFreeInput)
    (hP : ProductP1Input3) (hD4 : D4LinearClique3) (hAct : TwinSL4Action3) :
    TwinSL4Bridge3 := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02
  classical
  have hΩ := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := fun L hL => by
    obtain ⟨g, hg⟩ := hL
    exact ⟨g, hg.symm⟩
  obtain ⟨x₀, hx₀⟩ := hΩ.classical (j 1) (hjΩ 1)
  have hj0 : j 0 ≤ Subgroup.centralizer ({t * x₀} : Set G) :=
    hAct G hnab K z hR hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02 x₀ hx₀
  obtain ⟨W₀, hW₀⟩ := hKβ
  have hRβ : RouteD3Setup β t := RouteD3Setup.of_mem_conjClass3 hR hβ ht
  have hcl : conjClass3 β = conjClass3 K := conjClass3_eq_of_mem hβ
  obtain ⟨cK⟩ := nonempty_tctx3 (yData3_sl4 statedLieAdmissible_sl4_three) h3 hR hshape
  obtain ⟨cβ⟩ := cK.exists_ctx_member hsingle hβ ht
  obtain ⟨T, hT, hTQ⟩ := cβ.exists_twin
  have hTβ : T ≠ β := cβ.twin_ne hT hTQ.le
  have hTcomm : ∀ N ∈ centralizingMembers (conjClass3 K) {t}, N ≠ T → Commutes T N :=
    fun N hN hNT => cβ.commutes_T_of_ne hT hTQ.le hN hNT
  have hnotK : ¬ K ≤ Subgroup.centralizer ({t} : Set G) := by
    intro hle
    rcases cp_at_member3 h3 hnab hR hβ ht (L := K) ⟨hKΩ, hle⟩ with hc | he
    · exact not_commutes_of_linearBlockStandardPair hW₀ hc.symm
    · exact ne_of_linearBlockStandardPair hW₀ he
  have hKx₀ : K ≤ Subgroup.centralizer ({x₀} : Set G) :=
    le_centralizer_of_commutes (hjK 1) hx₀.mem
  have htx : t ≠ x₀ := fun h => hnotK (h ▸ hKx₀)
  have hj1β : Commutes β (j 1) := hjβ 1 (by decide)
  have hj1t : j 1 ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hjΩ 1, le_centralizer_of_commutes (Commutes.symm hj1β) ht.mem⟩
  have hj1ne : j 1 ≠ β := fun h => not_commutes_of_linearBlockStandardPair hW₀ (h ▸ hjK 1)
  have hsingleβ : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g β := fun L hL => by
    rw [← hcl] at hL
    obtain ⟨g, hg⟩ := hL
    exact ⟨g, hg.symm⟩
  have hj1T : j 1 ≠ T := by
    intro h
    have hTx : IsClassicalMember3 T x₀ := h ▸ hx₀
    have heq := centralizingMembers_eq_of_twin3 hΩ ht hTx (hsingleβ T hT.1) hT hTcomm
    have hKmem : K ∈ centralizingMembers (conjClass3 K) {x₀} := ⟨hKΩ, hKx₀⟩
    rw [heq] at hKmem
    exact hnotK hKmem.2
  obtain ⟨hP1x, hO3x⟩ := hP G β t hRβ (j 1) (hcl ▸ hjΩ 1) x₀ hx₀ hj1β htx
  have hj0β : j 0 ≠ β := fun h => not_commutes_of_linearBlockStandardPair hW₀ (h ▸ hjK 0)
  obtain ⟨Wj, hWj⟩ := hp01
  have hnc : ¬ Commutes β (j 0) := by
    intro hc
    have h1 : j 0 ≤ Subgroup.centralizer ({t} : Set G) :=
      le_centralizer_of_commutes (Commutes.symm hc) ht.mem
    have h2 : j 0 ≤ Subgroup.centralizer ({x₀} : Set G) := fun n hn =>
      mem_centralizer_right_of_mul (hj0 hn) (h1 hn)
    rcases cp_at_member3 h3 hnab hR (hjΩ 1) hx₀ (L := j 0) ⟨hjΩ 0, h2⟩ with hc' | he
    · exact not_commutes_of_linearBlockStandardPair hWj hc'.symm
    · exact ne_of_linearBlockStandardPair hWj he
  have hj0Ωβ : j 0 ∈ conjClass3 β := hcl ▸ hjΩ 0
  have hlink : LinkedAtProduct (conjClass3 β) β t x₀ := ⟨j 0, ⟨hj0Ωβ, hj0⟩, hj0β, hnc⟩
  obtain ⟨ι, hι, D, c, hk, -, hβc, hj1c, -, hallc⟩ :=
    exists_d4_component_of_twin_product3 hTw h3 hnab hRβ (T₁ := T) (hcl ▸ hT) hTβ
      (fun N hN hNT => hTcomm N (hcl ▸ hN) hNT) (K₂ := j 1) (hcl ▸ hj1t) hj1ne hj1T hx₀ htx
      hP1x hO3x hlink
  have hj0c := hallc (j 0) ⟨hj0Ωβ, hj0⟩ hj0β hnc
  have hpc : PowCop3 (D.kind c) :=
    hk ▸ powCop3_model (by trivial) statedLieAdmissible_plus4_three (by decide) (by decide)
  have hexβ := hRβ.setup.1
  have hΩβ := hRβ.inClass
  obtain ⟨R₁, hR₁⟩ := exists_corr_left3 hΩβ hexβ hP1x hO3x D hj1c
  obtain ⟨R₂, hR₂⟩ := exists_corr_left3 hΩβ hexβ hP1x hO3x D hβc
  obtain ⟨R₃, hR₃⟩ := exists_corr_left3 hΩβ hexβ hP1x hO3x D hj0c
  have hcomm : Commutes R₁ R₂ :=
    (corr_commutes3 hΩβ hexβ hP1x hO3x hpc hR₁ hR₂).mp (Commutes.symm hj1β)
  obtain ⟨W₁, hW₁⟩ := Gaps.linearBlockStandardPair_locImg_of_members (p := 3) (f := 1) hP1x
    hj1c.1 hj0c.1 (linearBlockStandardPair_symm hWj)
  rw [hR₁.2.2, hR₃.2.2] at hW₁
  have key : ∀ c' : CompData, c' = CompData.model .POmegaPlus 4 → PowCop3 c' →
      ∀ φ : c'.G →* locQuot (conjClass3 β) (t * x₀), φ.ker ≤ Subgroup.center c'.G →
      ∀ R₁ ∈ c'.fund, ∀ R₂ ∈ c'.fund, ∀ R₃ ∈ c'.fund, Commutes R₁ R₂ →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map φ) (R₃.map φ)) →
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₂.map φ) (R₃.map φ) := by
    rintro c' rfl hpc' φ hker R₁ h₁ R₂ h₂ R₃ h₃ hcomm hlin
    have : Finite (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K :=
      ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial
        statedLieAdmissible_plus4_three
    obtain ⟨W₁', hW₁'⟩ := exists_lin_of_map_pow3 (not_three_dvd_card_center_of_cop hpc'.cop) φ hker
      (hpc'.pow3 R₁ h₁) (hpc'.pow3 R₃ h₃) hlin
    obtain ⟨W₂', hW₂'⟩ := hD4 R₁ h₁ R₂ h₂ R₃ h₃ hcomm ⟨W₁', hW₁'⟩
    exact ⟨_, Gaps.linearBlockStandardPair_map φ hker hW₂'⟩
  obtain ⟨W₂, hW₂⟩ := key _ hk hpc (D.hom c) (D.ker_le_center c) R₁ hR₁.2.1 R₂ hR₂.2.1 R₃ hR₃.2.1
    hcomm ⟨W₁, hW₁⟩
  rw [← hR₂.2.2, ← hR₃.2.2] at hW₂
  exact linearBlockStandardPair_of_locImg3' hΩβ hexβ hP1x hO3x hβc.1 hj0c.1 hW₂

end Bridge

end CFSG.ClassicalInvolution.Q3.Q3TC
