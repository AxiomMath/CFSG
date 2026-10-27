module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecBCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix IsMulCommutative

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X6 CFSG.ComponentClassification

section Helpers

theorem exists_unique_coatom_of_uniqueMax {X : Type*} [Group X] {S P D : Subgroup X}
    (h : CFSG.QuasithinUnique.Setup.X35.IsUniqueMaxOver S P D) :
    ∃! M' : Subgroup ↥D, IsCoatom M' ∧ S.subgroupOf D ≤ M' := by
  obtain ⟨hSP, hPD, hY⟩ := h
  have hPle : P ≤ D := hPD.le
  have hmapP : (P.subgroupOf D).map D.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPle
  have hmapS : (S.subgroupOf D).map D.subtype = S :=
    Subgroup.map_subgroupOf_eq_of_le (hSP.trans hPle)
  have htop : ∀ b : Subgroup ↥D, b.map D.subtype = D → b = ⊤ := by
    intro b hb
    apply Subgroup.map_injective D.subtype_injective
    rw [hb]
    exact (map_subtype_top D).symm
  have hcoatom : IsCoatom (P.subgroupOf D) := by
    refine ⟨fun htop' => hPD.not_ge (Subgroup.subgroupOf_eq_top.1 htop'), fun b hb => ?_⟩
    by_contra hne
    have hPY : P ≤ b.map D.subtype := by
      rw [← hmapP]
      exact Subgroup.map_mono hb.le
    have hYD : b.map D.subtype < D := lt_of_le_of_ne (Subgroup.map_subtype_le b)
      fun h' => hne (htop b h')
    have hYP := hY _ (hSP.trans hPY) hYD
    apply hb.ne
    apply Subgroup.map_injective D.subtype_injective
    rw [hmapP]
    exact le_antisymm hYP hPY |>.symm
  refine ⟨P.subgroupOf D, ⟨hcoatom, fun x hx => hSP hx⟩, ?_⟩
  rintro M'' ⟨hM'', hSM''⟩
  have hSY : S ≤ M''.map D.subtype := by
    rw [← hmapS]
    exact Subgroup.map_mono hSM''
  have hYD : M''.map D.subtype < D := lt_of_le_of_ne (Subgroup.map_subtype_le M'')
    fun h' => hM''.1 (htop M'' h')
  have hYP := hY _ hSY hYD
  have hle : M'' ≤ P.subgroupOf D := fun x hx => hYP ⟨x, hx, rfl⟩
  by_contra hne
  exact hcoatom.1 (hM''.2 _ (lt_of_le_of_ne hle hne))

theorem simpleSummandsStable_comp {P P' M : Type} [Group P] [Group P'] [AddCommGroup M]
    [Module (ZMod 2) M] {π : P →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}
    (h : X7b.SimpleSummandsStable π A) (ψ : P' →* P) (hψ : Function.Surjective ψ) :
    X7b.SimpleSummandsStable (π.comp ψ) A := by
  obtain ⟨ι, U, hind, hsup, hU⟩ := h
  refine ⟨ι, U, hind, hsup, fun i => ?_⟩
  obtain ⟨h1, ⟨x, hx, g, hg⟩, h3, h4, h5⟩ := hU i
  refine ⟨h1, ⟨x, hx, ?_⟩, ?_, ?_, h5⟩
  · obtain ⟨g', rfl⟩ := hψ g
    exact ⟨g', hg⟩
  · intro g' y hy
    exact h3 (ψ g') y hy
  · intro W' hW hinv
    refine h4 W' hW fun g y hy => ?_
    obtain ⟨g', rfl⟩ := hψ g
    exact hinv g' y hy

end Helpers

section Linear

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem data_linear {H T M E : Subgroup (W ≃ₗ[ZMod 2] W)} (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (W ≃ₗ[ZMod 2] W), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E)
    {L : Subgroup (W ≃ₗ[ZMod 2] W)} (hL : IsComponentIn L H) {G : Type} [Group G]
    (θ : ↥L ≃* G) (hZ : Subgroup.center ↥L = ⊥) :
    ∃ (HD SD : Subgroup (MulAut G)) (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U)
      (_ : Finite U) (π : G →* (U ≃ₗ[ZMod 2] U)) (A' : Subgroup (U ≃ₗ[ZMod 2] U)),
      OuterAutomorphisms.inner G ≤ HD ∧ SD ≤ HD ∧ OuterAutomorphisms.inner G ⊔ SD = HD ∧
      IsSylowTwoOf SD HD ∧ (∃! M' : Subgroup ↥HD, IsCoatom M' ∧ SD.subgroupOf HD ≤ M') ∧
      Function.Injective π ∧ (∀ a ∈ A', ∀ x, ∃ y, a * π x * a⁻¹ = π y) ∧
      CFSG.IsElementaryAbelian 2 ↥A' ∧ A' ≠ ⊥ ∧ X7b.SimpleSummandsStable π A' ∧
      Nat.card U ≤ Nat.card A' * Nat.card {w : U // ∀ a ∈ A', a w = w} ∧
      ∀ s ∈ SD, ∃ b : U ≃ₗ[ZMod 2] U, ∀ x, b * π x * b⁻¹ = π (s x) := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) := finite_linearEquiv
  have hLH : L ≤ H := hL.1
  have hLc : CFSG.IsComponent (L.subgroupOf H) := hL.2
  have hqL : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComponentIn hL
  have hAct := Final.actual_component_minimal_parabolic hns hO2 hT hTn hTM hMH hmax hEH hEne hEel
    hEoff
  let c : Comp ↥H := ⟨L.subgroupOf H, hLc⟩
  have hcpt := hAct.transfer c
  obtain ⟨A₀, hA₀le, hA₀min, hA₀comm⟩ := hAct.offender c
  obtain ⟨hA₀H, hA₀ne, hA₀el, hA₀off, hA₀strict⟩ := hA₀min
  have hmapL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hA₀L : ⁅L, A₀⁆ = L := by
    have h1 : ⁅(L.subgroupOf H).map H.subtype, A₀⁆ = (L.subgroupOf H).map H.subtype := hA₀comm
    rwa [hmapL] at h1
  set N' : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.normalizer (L : Set (W ≃ₗ[ZMod 2] W)) with hN'
  have hLN : L ≤ N' := Subgroup.le_normalizer
  have hA₀N : A₀ ≤ N' := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := hA₀le ha
    have hnN : n ∈ normL (L.subgroupOf H) := hn.2
    have := map_subtype_mem_normalizer (H := H) (L := L.subgroupOf H) hnN
    rwa [hmapL] at this
  let L₁ : Subgroup ↥N' := L.subgroupOf N'
  have hL₁N : L₁.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 g.2 x).1 hx⟩
  let e : ↥L ≃* ↥L₁ := (Subgroup.subgroupOfEquivOfLe hLN).symm
  have hq₁ : CFSG.IsQuasisimple ↥L₁ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqL
  have hZ₁ : Subgroup.center ↥L₁ = ⊥ := by
    have := Subgroup.map_center_eq e
    rw [hZ, Subgroup.map_bot] at this
    exact this.symm
  let A : Subgroup ↥N' := A₀.subgroupOf N'
  have hmapA : A.map N'.subtype = A₀ := Subgroup.map_subgroupOf_eq_of_le hA₀N
  have hmapL₁ : L₁.map N'.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLN
  have hAne : A ≠ ⊥ := by
    intro hbot
    apply hA₀ne
    rw [← hmapA, hbot, Subgroup.map_bot]
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := IsElementaryAbelian.subgroupOf hA₀N
  have hLA : ⁅L₁, A⁆ = L₁ := by
    apply Subgroup.map_injective N'.subtype_injective
    rw [Subgroup.map_commutator, hmapL₁, hmapA]
    exact hA₀L
  have hw : ∀ B : Subgroup ↥N', weight N'.subtype B =
      weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (B.map N'.subtype) := fun B =>
    weight_comp_subtype (MonoidHom.id (W ≃ₗ[ZMod 2] W)) N' B
  have hoff : Nat.card W ≤ weight N'.subtype A := by
    rw [hw, hmapA]
    exact hA₀off
  have hstrict : ∀ D : Subgroup ↥N', ⊥ < D → D < A → weight N'.subtype D < weight N'.subtype A := by
    intro B hB0 hBA
    rw [hw B, hw A, hmapA]
    refine hA₀strict (B.map N'.subtype) ?_ ?_
    · refine bot_lt_iff_ne_bot.mpr fun h => (bot_lt_iff_ne_bot.mp hB0) ?_
      exact (Subgroup.map_eq_bot_iff_of_injective B N'.subtype_injective).mp h
    · rw [← hmapA]
      exact (Subgroup.map_lt_map_iff_of_injective N'.subtype_injective).mpr hBA
  obtain ⟨U, iU1, iU2, iU3, ρL₁, A', hinj, hconj, hel, hne, hsss, hoffU, hlift⟩ :=
    data_core N'.subtype N'.subtype_injective L₁ hq₁ hZ₁ hAne hAel hLA hoff hstrict
  let φ' : G →* ↥L₁ := (e.toMonoidHom).comp θ.symm.toMonoidHom
  have hφ'surj : Function.Surjective φ' := e.surjective.comp θ.symm.surjective
  let π : G →* (U ≃ₗ[ZMod 2] U) := ρL₁.comp φ'
  let θ₀ : ↥(L.subgroupOf H) ≃* G := (Subgroup.subgroupOfEquivOfLe hLH).trans θ
  let Θ : MulAut ↥(L.subgroupOf H) ≃* MulAut G := MulAut.congr θ₀
  have hinn : (OuterAutomorphisms.inner ↥(L.subgroupOf H)).map Θ.toMonoidHom =
      OuterAutomorphisms.inner G := OuterAutomorphisms.inner_map_congr θ₀
  have hSyl : IsSylowTwoOf (actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H)))
      (actImg (L.subgroupOf H) (normL (L.subgroupOf H))) :=
    isSylowTwoOf_iff_isSylowOf.2 hcpt.sylow_S
  have hUM : CFSG.QuasithinUnique.Setup.X35.IsUniqueMaxOver
      (actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H)))
      (actImg (L.subgroupOf H) (maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H)))
      (actImg (L.subgroupOf H) (normL (L.subgroupOf H))) := by
    obtain ⟨hSP, hPA, hY⟩ := hcpt.P_max
    exact ⟨hSP, hPA, fun Y hSY hYA => hY Y hYA.le hSY hYA⟩
  refine ⟨(actImg (L.subgroupOf H) (normL (L.subgroupOf H))).map Θ.toMonoidHom,
    (actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H))).map Θ.toMonoidHom,
    U, iU1, iU2, iU3, π, A', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hel, hne, ?_, hoffU, ?_⟩
  · rw [← hinn]
    exact Subgroup.map_mono hcpt.inn_le
  · exact Subgroup.map_mono (actImg_mono inf_le_right)
  · have hrange : actImg (L.subgroupOf H) (normL (L.subgroupOf H)) =
        OuterAutomorphisms.inner ↥(L.subgroupOf H) ⊔
          actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H)) :=
      hcpt.range_eq_inn_mul
    rw [← hinn, ← Subgroup.map_sup, ← hrange]
  · exact (isSylowTwoOf_map_mulEquiv Θ).2 hSyl
  · exact exists_unique_coatom_of_uniqueMax (hUM.map Θ.injective)
  · exact (hinj.comp e.injective).comp θ.symm.injective
  · intro a ha x
    obtain ⟨l', hl'⟩ := hconj a ha (φ' x)
    refine ⟨θ (e.symm l'), ?_⟩
    show a * ρL₁ (φ' x) * a⁻¹ = ρL₁ (φ' (θ (e.symm l')))
    rw [hl']
    congr 1
    simp [φ']
  · exact simpleSummandsStable_comp hsss φ' hφ'surj
  ·
    rintro _ ⟨α, hα, rfl⟩ 
    obtain ⟨n, hnT, hnN, rfl⟩ := mem_actImg.1 hα
    have hgN : (n : W ≃ₗ[ZMod 2] W) ∈ N' := by
      have := map_subtype_mem_normalizer (H := H) (L := L.subgroupOf H) hnN
      rwa [hmapL] at this
    obtain ⟨b, hb⟩ := hlift ⟨(n : W ≃ₗ[ZMod 2] W), hgN⟩
    refine ⟨b, fun x => ?_⟩
    show b * ρL₁ (φ' x) * b⁻¹ = ρL₁ (φ' (Θ.toMonoidHom (actOf (L.subgroupOf H) n) x))
    rw [hb (φ' x)]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    have key : ∀ l : ↥(L.subgroupOf H),
        (((actOf (L.subgroupOf H) n l : ↥(L.subgroupOf H)) : ↥H) : W ≃ₗ[ZMod 2] W) =
          (n : W ≃ₗ[ZMod 2] W) * ((l : ↥H) : W ≃ₗ[ZMod 2] W) * (n : W ≃ₗ[ZMod 2] W)⁻¹ := fun l => by
      have := congrArg (fun y : ↥H => (y : W ≃ₗ[ZMod 2] W)) (actOf_coe hnN l)
      simpa using this
    have h1 : φ' (Θ.toMonoidHom (actOf (L.subgroupOf H) n) x) =
        e (Subgroup.subgroupOfEquivOfLe hLH (actOf (L.subgroupOf H) n
          ((Subgroup.subgroupOfEquivOfLe hLH).symm (θ.symm x)))) := by
      show e.toMonoidHom (θ.symm (θ₀ (actOf (L.subgroupOf H) n (θ₀.symm x)))) = _
      simp [θ₀]
    rw [h1]
    exact (key ((Subgroup.subgroupOfEquivOfLe hLH).symm (θ.symm x))).symm

end Linear

end CFSG.QuasithinUnique.Setup.X7Sec
