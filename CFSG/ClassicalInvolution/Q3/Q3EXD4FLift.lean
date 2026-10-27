module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped MatrixGroups commutatorElement


section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {ι : Type}

theorem locMk_inj_of_member3 (hex : ExactMembers3 Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {a b : ↥(locLayer Ω x)} (ha : (a : G) ∈ L)
    (hb : (b : G) ∈ L) (h : locMk Ω x a = locMk Ω x b) : a = b := by
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L := CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := Generic.inf_oddCore_eq_bot hO
  have hmem : a⁻¹ * b ∈ (L.subgroupOf (locLayer Ω x)) ⊓
      classicalInvolutionOddCore ↥(locLayer Ω x) :=
    ⟨(L.subgroupOf (locLayer Ω x)).mul_mem ((L.subgroupOf (locLayer Ω x)).inv_mem
      (Subgroup.mem_subgroupOf.mpr ha)) (Subgroup.mem_subgroupOf.mpr hb), QuotientGroup.eq.mp h⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

omit [Finite G] in
theorem exists_lift_of_corr3 {w : G} {D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)}
    {i : ι} {T : Subgroup G} {R : Subgroup (D.kind i).G} (hR : Corr3 Ω w D i T R)
    {u : (D.kind i).G} (hu : u ∈ R) :
    ∃ (y : G) (hy : y ∈ locLayer Ω w), y ∈ T ∧ locMk Ω w ⟨y, hy⟩ = D.hom i u := by
  have hmem : D.hom i u ∈ locImg Ω w T := hR.2.2 ▸ ⟨u, hu, rfl⟩
  obtain ⟨y', hy', hyu⟩ := hmem
  exact ⟨y', y'.2, Subgroup.mem_subgroupOf.mp hy', hyu⟩

theorem elem_central_of_lift3 {w : G} {D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)}
    {i : ι} (hgen : ∀ R ∈ (D.kind i).fund, ModelFacts.Gen3 R)
    (hk3 : ∀ x ∈ (D.hom i).ker, x ^ 3 = 1 → x = 1) {T : Subgroup G} {R : Subgroup (D.kind i).G}
    (hR : Corr3 Ω w D i T R) {y : G} (hy : y ∈ locLayer Ω w) {u : (D.kind i).G}
    (hu : D.hom i u = locMk Ω w ⟨y, hy⟩) (hc : ∀ g ∈ T, y * g = g * y) :
    ∀ r ∈ R, u * r = r * u := by
  have hcent : ∀ r ∈ R, r * u = u * r :=
    ModelFacts.commute_of_map_commute_of_gen3 (D.hom i) (D.ker_le_center i) hk3
      (hgen R hR.2.1) (b := u) (by
        intro r hr
        have hx : D.hom i r ∈ locImg Ω w T := hR.2.2 ▸ ⟨r, hr, rfl⟩
        obtain ⟨g, hg, hrg⟩ := hx
        rw [hu, ← hrg]
        show locMk Ω w g * locMk Ω w ⟨y, hy⟩ = locMk Ω w ⟨y, hy⟩ * locMk Ω w g
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (hc g (Subgroup.mem_subgroupOf.mp hg)).symm)
  intro r hr
  exact (hcent r hr).symm

end Lift

section Generate

variable {Y : Type} [Group Y]

theorem le_of_gen3_of_le_sup_center {A B Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y)
    (hZ3 : ¬ 3 ∣ Nat.card Z) (hA : ModelFacts.Gen3 A) (h : A ≤ B ⊔ Z) : A ≤ B := by
  obtain ⟨S, hSA, hS3, hAS⟩ := hA
  have hZc : ∀ z ∈ Z, ∀ h ∈ (⊤ : Subgroup Y), z * h = h * z := fun z hz h _ =>
    (Subgroup.mem_center_iff.mp (hZ hz) h).symm
  have hS : ∀ s ∈ S, s ∈ B := by
    intro s hs
    obtain ⟨b, hb, z, hz, hsbz⟩ :=
      exists_mul_of_mem_sup_central (H := ⊤) (A := B) le_top hZc (h (hSA hs))
    have hbz : Commute b z := Subgroup.mem_center_iff.mp (hZ hz) b
    have h3 : (b * z) ^ 3 = 1 := by rw [← hsbz]; exact hS3 s hs
    rw [hbz.mul_pow] at h3
    have hz3 : z ^ 3 ∈ B := by
      have : z ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h3
      rw [this]
      exact B.inv_mem (B.pow_mem hb 3)
    have hord : ¬ 3 ∣ orderOf z := fun h3' => hZ3 (h3'.trans (Subgroup.orderOf_dvd_natCard Z hz))
    have hcop : Nat.Coprime 3 (orderOf z) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hord
    have hzB : z ∈ B := (Subgroup.zpowers_le.mpr hz3) (mem_zpowers_pow_iff.mpr hcop)
    rw [hsbz]
    exact B.mul_mem hb hzB
  exact hAS.trans ((Subgroup.closure_le B).mpr hS)

end Generate

section Generate2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {ι : Type}

theorem le_iSup_of_model_generates3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {w : G}
    (hP1 : LocalOddCentral Ω {w}) (hO3 : LocalOddThreeFree3 Ω w)
    {D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)} {i : ι} {ι' : Type}
    (T : ι' → Subgroup G) (R : ι' → Subgroup (D.kind i).G)
    (hT : ∀ a, Corr3 Ω w D i (T a) (R a)) (hgen : (⨆ a, R a) = ⊤) {L : Subgroup G}
    (hL : L ∈ compMembers3 Ω w D i) : L ≤ ⨆ a, T a := by
  classical
  set Y := locLayer Ω w with hY
  set B : Subgroup ↥Y := ⨆ a, (T a).subgroupOf Y with hB
  have hmapB : B.map (locMk Ω w) = ⨆ a, locImg Ω w (T a) := by
    rw [hB, Subgroup.map_iSup]
    rfl
  have hrange : (D.hom i).range = ⨆ a, locImg Ω w (T a) := by
    have : ∀ a, locImg Ω w (T a) = (R a).map (D.hom i) := fun a => (hT a).2.2
    simp only [this]
    rw [← Subgroup.map_iSup, hgen, MonoidHom.range_eq_map]
  have hLB : L.subgroupOf Y ≤ B ⊔ classicalInvolutionOddCore ↥Y := by
    intro a ha
    have h1 : locMk Ω w a ∈ (D.hom i).range := hL.2 ⟨a, ha, rfl⟩
    rw [hrange, ← hmapB] at h1
    have h2 := Subgroup.comap_map_eq (locMk Ω w) B ▸ (show a ∈ Subgroup.comap (locMk Ω w)
      (B.map (locMk Ω w)) from h1)
    rw [QuotientGroup.ker_mk'] at h2
    exact h2
  obtain ⟨z₀, hz⟩ := hΩ.classical L hL.1.1
  have hLY := le_centralizingLayer hL.1
  obtain ⟨e'⟩ := hz.nonempty_equiv_sl2 (hex L hL.1.1)
  obtain ⟨e₁⟩ : Nonempty (↥(L.subgroupOf (locLayer Ω w)) ≃* SL(2, ZMod 3)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e'⟩
  have hBle := le_of_gen3_of_le_sup_center hP1 hO3 (ModelFacts.gen3_of_equiv_sl2 e₁) hLB
  intro l hl
  have hlY : l ∈ Y := le_centralizingLayer hL.1 hl
  have h3 : (⟨l, hlY⟩ : ↥Y) ∈ B := hBle (Subgroup.mem_subgroupOf.mpr hl)
  have h4 : l ∈ B.map Y.subtype := ⟨⟨l, hlY⟩, h3, rfl⟩
  rw [hB, Subgroup.map_iSup] at h4
  have hle : (⨆ a, ((T a).subgroupOf Y).map Y.subtype) ≤ ⨆ a, T a := iSup_mono fun a => by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy
  exact hle h4

end Generate2

section Members

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem exists_node_members3 (S : D4Ctx3 G K z 4) {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) :
    ∃ (Mk : Fin 4 → Subgroup G) (zk : Fin 4 → G),
      (∀ k, Mk k ∈ outerSet (conjClass3 K) N₀) ∧ (∀ k, IsClassicalMember3 (Mk k) (zk k)) ∧
      (∀ j k, zk j * zk k = zk k * zk j) ∧
      ∀ L ∈ outerSet (conjClass3 K) N₀, L ≤ ⨆ k, Mk k := by
  classical
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨w, hw, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hN₀
  have hout := outerSet_eq_compMembers3 hΩ hex hw hN₀ hP1 hO3 (single_class_of_mem3 hN₀) D hk
    hrest
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hpc := powCop3_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hgen3 := gen3_of_kind hk
  have hk3 := ker_k3_of_powCop3 hpc (D.hom i₁) (D.ker_le_center i₁)
  have hsc := singleClass_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  obtain ⟨R, c, hRf, hcR, hcz, hc1, huniq, hcomm, hgen⟩ := exists_nodes_of_kind hk
  choose M hM using fun k => exists_corr_right3 hΩ D hsc (hRf k)
  have hMout : ∀ k, M k ∈ outerSet Ω N₀ := fun k => by
    rw [hout]
    exact ⟨(hM k).1, (hM k).2.2 ▸ Subgroup.map_le_range _ _⟩
  choose z' hz' using fun k => hΩ.classical (M k) (hM k).1.1
  have hzY : ∀ k, z' k ∈ locLayer Ω w := fun k => le_centralizingLayer (hM k).1 (hz' k).mem
  have hzc : ∀ k, D.hom i₁ (c k) = locMk Ω w ⟨z' k, hzY k⟩ := by
    intro k
    obtain ⟨c', hc'R, hc'z, hc'img, hc'1⟩ :=
      exists_central_preimage3 hgen3 hk3 (hM k) (hz' k) (hzY k)
    rw [← hc'img, huniq k c' hc'R hc'z hc'1]
  refine ⟨M, z', hMout, hz', ?_, ?_⟩
  · intro j k
    have hsq : ∀ m, z' m * z' m = 1 := fun m => mul_self_of_isClassicalMember3 (hz' m)
    set Zj : ↥(locLayer Ω w) := ⟨z' j, hzY j⟩
    set Zk : ↥(locLayer Ω w) := ⟨z' k, hzY k⟩
    have hmk : locMk Ω w (Zj * Zk * Zj⁻¹ * Zk⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      show locMk Ω w ⟨z' j, hzY j⟩ * locMk Ω w ⟨z' k, hzY k⟩ * (locMk Ω w ⟨z' j, hzY j⟩)⁻¹ *
        (locMk Ω w ⟨z' k, hzY k⟩)⁻¹ = 1
      rw [← hzc j, ← hzc k, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
        hcomm j k]
      group
      exact map_one _
    have hO : Zj * Zk * Zj⁻¹ * Zk⁻¹ ∈ classicalInvolutionOddCore ↥(locLayer Ω w) :=
      (QuotientGroup.eq_one_iff _).mp hmk
    have hcent := hP1 hO
    have hZj : Zj * Zj = 1 := Subtype.ext (hsq j)
    have hZk : Zk * Zk = 1 := Subtype.ext (hsq k)
    have hZji : Zj⁻¹ = Zj := inv_eq_of_mul_eq_one_right hZj
    have hZki : Zk⁻¹ = Zk := inv_eq_of_mul_eq_one_right hZk
    set A : ↥(locLayer Ω w) := Zj * Zk * Zj⁻¹ * Zk⁻¹ with hA
    have hAA : A * A = 1 := by
      have h1 : Zj * A * Zj⁻¹ = A⁻¹ := by
        rw [hA, hZji, hZki]
        calc Zj * (Zj * Zk * Zj * Zk) * Zj = (Zj * Zj) * Zk * Zj * Zk * Zj := by group
          _ = Zk * Zj * Zk * Zj := by rw [hZj, one_mul]
          _ = (Zj * Zk * Zj * Zk)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hZji, hZki]
            group
      have h2 : Zj * A * Zj⁻¹ = A := by
        rw [Subgroup.mem_center_iff.mp hcent Zj]
        group
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.mpr h1
    have hA1 := eq_one_of_mem_oddCore_of_sq hO hAA
    have hcomm' : Zj * Zk = Zk * Zj := by
      have h3 : (Zj * Zk) * (Zj * Zk) = 1 := by
        have h4 := hA1
        rw [hA, hZji, hZki] at h4
        simpa [mul_assoc] using h4
      calc Zj * Zk = (Zj * Zk)⁻¹ := eq_inv_of_mul_eq_one_left h3
        _ = Zk * Zj := by rw [mul_inv_rev, hZki, hZji]
    exact congrArg Subtype.val hcomm'
  · intro L hL
    exact le_iSup_of_model_generates3 hΩ hex hP1 hO3 M R hM hgen (hout ▸ hL)

theorem exists_noncommuting_outer3 (S : D4Ctx3 G K z 4) {N M : Subgroup G}
    (hN : N ∈ conjClass3 K) (hM : M ∈ outerSet (conjClass3 K) N) :
    ∃ L ∈ outerSet (conjClass3 K) N, L ≠ M ∧ ¬ Commutes M L := by
  classical
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨w, hw, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hN
  have hout := outerSet_eq_compMembers3 hΩ hex hw hN hP1 hO3 (single_class_of_mem3 hN) D hk hrest
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hpc := powCop3_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hsc := singleClass_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hMc : M ∈ compMembers3 Ω w D i₁ := hout ▸ hM
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hMc
  obtain ⟨S', hS, hSne, hSnc⟩ := exists_fund_not_commuting_of_kind hk
    (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm (by decide) hR.2.1
  obtain ⟨L', hL'⟩ := exists_corr_right3 hΩ D hsc hS
  refine ⟨L', hout ▸ ⟨hL'.1, hL'.2.2 ▸ Subgroup.map_le_range _ _⟩,
    fun h => hSne (corr_unique_left3 hpc hL' (h ▸ hR)), fun h => hSnc ?_⟩
  exact (corr_commutes3 hΩ hex hP1 hO3 hpc hL' hR).mp h.symm

theorem exists_lift_data3 (hnab : ∃ x y : G, x * y ≠ y * x) (S : D4Ctx3 G K z 4)
    {N₀ M : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) (hM : M ∈ outerSet (conjClass3 K) N₀) {z₀ : G}
    (hz₀ : IsClassicalMember3 N₀ z₀) :
    ∃ (Ta Tb : Subgroup G) (ya yb : G) (P : Subgroup G) (x : G),
      Ta ∈ conjClass3 K ∧ Tb ∈ conjClass3 K ∧
      cnbhd (conjClass3 K) Ta = cnbhd (conjClass3 K) N₀ ∧
      cnbhd (conjClass3 K) Tb = cnbhd (conjClass3 K) N₀ ∧ Ta ≠ N₀ ∧ Tb ≠ N₀ ∧ Ta ≠ Tb ∧
      ya ∈ Ta ∧ yb ∈ Tb ∧ ya * ya = z₀ ∧ yb * yb = z₀ ∧
      (¬ ∀ g ∈ Ta, ya * g = g * ya) ∧ (¬ ∀ g ∈ Tb, yb * g = g * yb) ∧ ya * yb ≠ 1 ∧
      P ∈ conjClass3 K ∧ x ∈ P ∧ (∀ g ∈ P, g * (ya * yb) = (ya * yb) * g) ∧
      (x * z₀ * x⁻¹ * z₀⁻¹) ^ 4 = 1 ∧ x * z₀ * x⁻¹ * z₀⁻¹ ≠ 1 := by
  classical
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hMΩ : M ∈ Ω := hM.1.1
  obtain ⟨w, hw, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hMΩ
  have hout := outerSet_eq_compMembers3 hΩ hex hw hMΩ hP1 hO3 (single_class_of_mem3 hMΩ) D hk
    hrest
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hpc := powCop3_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hgen3 := gen3_of_kind hk
  have hk3 := ker_k3_of_powCop3 hpc (D.hom i₁) (D.ker_le_center i₁)
  let 𝒯 : Set (Subgroup G) := {T | T ∈ Ω ∧ cnbhd Ω T = cnbhd Ω N₀}
  have h𝒯 : 𝒯.ncard = 4 := ncard_twins_of_shape3 S hN₀
  have hN₀𝒯 : N₀ ∈ 𝒯 := ⟨hN₀, rfl⟩
  have h3 : (𝒯 \ {N₀}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem hN₀𝒯, h𝒯]
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, hset⟩ := Set.ncard_eq_three.mp h3
  have hT : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ 𝒯 ∧ T ≠ N₀ := by
    intro T hT
    have : T ∈ 𝒯 \ {N₀} := by
      rw [hset]
      rcases hT with rfl | rfl | rfl <;> simp
    exact ⟨this.1, this.2⟩
  have hcomm𝒯 : ∀ {T T' : Subgroup G}, T ∈ 𝒯 → T' ∈ 𝒯 → T ≠ T' → Commutes T T' := by
    intro T T' hT hT' hne
    have : T ∈ cnbhd Ω T' := by
      rw [hT'.2, ← hT.2]
      exact self_mem_cnbhd hT.1
    exact this.2.resolve_left hne
  have hout' : ∀ T ∈ 𝒯, T ∈ compMembers3 Ω w D i₁ := by
    intro T hT
    rw [← hout]
    have hMT : M ∈ outerSet Ω T := by
      rw [outerSet_eq_of_cnbhd_eq hT.2]
      exact hM
    exact mem_outerSet_symm hT.1 hMT
  have hT₂ := hT T₂ (Or.inl rfl)
  have hT₃ := hT T₃ (Or.inr (Or.inl rfl))
  have hT₄ := hT T₄ (Or.inr (Or.inr rfl))
  obtain ⟨R₁, hR₁⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hout' N₀ hN₀𝒯)
  obtain ⟨R₂, hR₂⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hout' T₂ hT₂.1)
  obtain ⟨R₃, hR₃⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hout' T₃ hT₃.1)
  obtain ⟨R₄, hR₄⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hout' T₄ hT₄.1)
  have hR12 : R₁ ≠ R₂ := fun h => hT₂.2 (corr_unique_right3 hΩ hex hP1 hO3 hR₂ (h ▸ hR₁))
  have hR13 : R₁ ≠ R₃ := fun h => hT₃.2 (corr_unique_right3 hΩ hex hP1 hO3 hR₃ (h ▸ hR₁))
  have hR14 : R₁ ≠ R₄ := fun h => hT₄.2 (corr_unique_right3 hΩ hex hP1 hO3 hR₄ (h ▸ hR₁))
  have hR23 : R₂ ≠ R₃ := fun h => h23 (corr_unique_right3 hΩ hex hP1 hO3 hR₂ (h ▸ hR₃))
  have hR24 : R₂ ≠ R₄ := fun h => h24 (corr_unique_right3 hΩ hex hP1 hO3 hR₂ (h ▸ hR₄))
  have hR34 : R₃ ≠ R₄ := fun h => h34 (corr_unique_right3 hΩ hex hP1 hO3 hR₃ (h ▸ hR₄))
  have c12 : Commutes R₁ R₂ :=
    (corr_commutes3 hΩ hex hP1 hO3 hpc hR₁ hR₂).mp (hcomm𝒯 hN₀𝒯 hT₂.1 hT₂.2.symm)
  have c13 : Commutes R₁ R₃ :=
    (corr_commutes3 hΩ hex hP1 hO3 hpc hR₁ hR₃).mp (hcomm𝒯 hN₀𝒯 hT₃.1 hT₃.2.symm)
  have c14 : Commutes R₁ R₄ :=
    (corr_commutes3 hΩ hex hP1 hO3 hpc hR₁ hR₄).mp (hcomm𝒯 hN₀𝒯 hT₄.1 hT₄.2.symm)
  have hz₀Y : z₀ ∈ locLayer Ω w := le_centralizingLayer hR₁.1 hz₀.mem
  obtain ⟨c, hcR, hcz, hcimg, hc1⟩ := exists_central_preimage3 hgen3 hk3 hR₁ hz₀ hz₀Y
  have hcp := exists_clique_partner_of_kind hk hR₁.2.1 hR₂.2.1 hR₃.2.1 hR₄.2.1 hR12 hR13 hR14
    hR23 hR24 hR34 c12 c13 c14 hcR hcz hc1
  unfold CliquePartnerS at hcp
  obtain ⟨Ra, Rb, hRa, hRb, hab, ua, hua, ub, hub, Pm, hPm, xm, hxm, hcom, hsqa, hsqb, hnca,
    hncb, hnc, ht4, htnc⟩ := hcp
  have hsel : ∀ {R : Subgroup (D.kind i₁).G},
      (R = R₂ ∨ R = R₃ ∨ R = R₄) → ∃ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) ∧ Corr3 Ω w D i₁ T R := by
    rintro R (rfl | rfl | rfl)
    · exact ⟨T₂, Or.inl rfl, hR₂⟩
    · exact ⟨T₃, Or.inr (Or.inl rfl), hR₃⟩
    · exact ⟨T₄, Or.inr (Or.inr rfl), hR₄⟩
  obtain ⟨Ta, hTa, hRaTa⟩ := hsel hRa
  obtain ⟨Tb, hTb, hRbTb⟩ := hsel hRb
  have hTab : Ta ≠ Tb := fun h => hab (corr_unique_left3 hpc hRaTa (h ▸ hRbTb))
  obtain ⟨hTa𝒯, hTaN⟩ := hT Ta hTa
  obtain ⟨hTb𝒯, hTbN⟩ := hT Tb hTb
  obtain ⟨ya, hyaY, hyaT, hya⟩ := exists_lift_of_corr3 hRaTa hua
  obtain ⟨yb, hybY, hybT, hyb⟩ := exists_lift_of_corr3 hRbTb hub
  have hz₀a : IsClassicalMember3 Ta z₀ :=
    isClassicalMember_of_twin3 hnab S hN₀ hTa𝒯.1 hTa𝒯.2 hz₀
  have hz₀b : IsClassicalMember3 Tb z₀ :=
    isClassicalMember_of_twin3 hnab S hN₀ hTb𝒯.1 hTb𝒯.2 hz₀
  obtain ⟨ca, hcaR, hcaz, hcaimg, hca1⟩ := exists_central_preimage3 hgen3 hk3 hRaTa hz₀a hz₀Y
  obtain ⟨cb, hcbR, hcbz, hcbimg, hcb1⟩ := exists_central_preimage3 hgen3 hk3 hRbTb hz₀b hz₀Y
  have hsqya : ya * ya = z₀ := by
    have h1 : locMk Ω w (⟨ya, hyaY⟩ * ⟨ya, hyaY⟩) = locMk Ω w ⟨z₀, hz₀Y⟩ := by
      rw [map_mul, hya, ← map_mul, hsqa ca hcaR hcaz hca1, hcaimg]
    have := locMk_inj_of_member3 hex hRaTa.1 (a := ⟨ya, hyaY⟩ * ⟨ya, hyaY⟩) (b := ⟨z₀, hz₀Y⟩)
      (Subgroup.mul_mem _ hyaT hyaT) hz₀a.mem h1
    exact congrArg Subtype.val this
  have hsqyb : yb * yb = z₀ := by
    have h1 : locMk Ω w (⟨yb, hybY⟩ * ⟨yb, hybY⟩) = locMk Ω w ⟨z₀, hz₀Y⟩ := by
      rw [map_mul, hyb, ← map_mul, hsqb cb hcbR hcbz hcb1, hcbimg]
    have := locMk_inj_of_member3 hex hRbTb.1 (a := ⟨yb, hybY⟩ * ⟨yb, hybY⟩) (b := ⟨z₀, hz₀Y⟩)
      (Subgroup.mul_mem _ hybT hybT) hz₀b.mem h1
    exact congrArg Subtype.val this
  have hyaYb : ya * yb ∈ locLayer Ω w := (locLayer Ω w).mul_mem hyaY hybY
  have himg : locMk Ω w ⟨ya * yb, hyaYb⟩ = D.hom i₁ (ua * ub) := by
    rw [map_mul, ← hya, ← hyb]
    exact map_mul (locMk Ω w) ⟨ya, hyaY⟩ ⟨yb, hybY⟩
  have hne1 : ya * yb ≠ 1 := by
    intro h1
    apply hnc
    apply D.ker_le_center i₁
    rw [MonoidHom.mem_ker, ← himg]
    have : (⟨ya * yb, hyaYb⟩ : ↥(locLayer Ω w)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hsc := singleClass_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  obtain ⟨P, hPcorr⟩ := exists_corr_right3 hΩ D hsc hPm
  obtain ⟨x', hx'Y, hx'P, hx'⟩ := exists_lift_of_corr3 hPcorr hxm
  have hPcomm : ∀ g ∈ P, g * (ya * yb) = (ya * yb) * g := by
    refine commutes_elem_of_commutes_locImg3 hΩ hex hP1 hO3 hPcorr.1 hyaYb ?_
    intro w' hw'
    rw [hPcorr.2.2] at hw'
    obtain ⟨r, hr, rfl⟩ := hw'
    rw [himg, ← map_mul, ← map_mul, hcom r hr]
  set X : ↥(locLayer Ω w) := ⟨x', hx'Y⟩ with hX
  set Z₀ : ↥(locLayer Ω w) := ⟨z₀, hz₀Y⟩ with hZ₀
  have hlocT : locMk Ω w (X * Z₀ * X⁻¹ * Z₀⁻¹) = D.hom i₁ (xm * c * xm⁻¹ * c⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
      hcimg]
    rw [hX, hx']
  have hTne : x' * z₀ * x'⁻¹ * z₀⁻¹ ≠ 1 := by
    intro h1
    apply htnc
    apply D.ker_le_center i₁
    rw [MonoidHom.mem_ker, ← hlocT]
    have : X * Z₀ * X⁻¹ * Z₀⁻¹ = 1 := Subtype.ext h1
    rw [this, map_one]
  have hT4 : (x' * z₀ * x'⁻¹ * z₀⁻¹) ^ 4 = 1 := by
    set T' : ↥(locLayer Ω w) := X * Z₀ * X⁻¹ * Z₀⁻¹ with hT'
    have hmk : locMk Ω w (T' ^ 4) = 1 := by
      rw [map_pow, hT', hlocT, ← map_pow, ht4, map_one]
    have hO : T' ^ 4 ∈ classicalInvolutionOddCore ↥(locLayer Ω w) :=
      (QuotientGroup.eq_one_iff _).mp hmk
    have hcent : T' ^ 4 ∈ Subgroup.center ↥(locLayer Ω w) := hP1 hO
    have hZ2 : Z₀ * Z₀ = 1 := Subtype.ext (mul_self_of_isClassicalMember3 hz₀)
    have hZi : Z₀⁻¹ = Z₀ := inv_eq_of_mul_eq_one_right hZ2
    have hinv : Z₀ * T' * Z₀⁻¹ = T'⁻¹ := by
      rw [hT']
      simp only [mul_inv_rev, inv_inv, hZi, mul_assoc, hZ2, mul_one]
    have hsq : T' ^ 4 * T' ^ 4 = 1 := by
      have h1 : Z₀ * T' ^ 4 * Z₀⁻¹ = (T' ^ 4)⁻¹ := by
        rw [← conj_pow, hinv, inv_pow]
      have h2 : Z₀ * T' ^ 4 * Z₀⁻¹ = T' ^ 4 := by
        rw [Subgroup.mem_center_iff.mp hcent Z₀]
        group
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.mpr h1
    have := eq_one_of_mem_oddCore_of_sq hO hsq
    exact congrArg Subtype.val this
  refine ⟨Ta, Tb, ya, yb, P, x', hTa𝒯.1, hTb𝒯.1, hTa𝒯.2, hTb𝒯.2, hTaN, hTbN, hTab, hyaT,
    hybT, hsqya, hsqyb, ?_, ?_, hne1, hPcorr.1.1, hx'P, hPcomm, hT4, hTne⟩
  · exact fun hc => hnca (elem_central_of_lift3 hgen3 hk3 hRaTa hyaY hya.symm hc)
  · exact fun hc => hncb (elem_central_of_lift3 hgen3 hk3 hRbTb hybY hyb.symm hc)


end Members

end CFSG.ClassicalInvolution.Q3.Q3W.EX
