module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Quasithin

section Transport

variable {G Mg Mn H : Type*} [Group G] [Group Mg] [Group Mn] [Group H] {ι : Type*}

@[expose] def PEAligned (ext : ι → Mn →* Mg) (Φ : ι → Mn →* G) : Prop :=
  ∀ k l g h, ext k g = ext l h → Φ k g = Φ l h

@[expose] def PENormal (ext : ι → Mn →* Mg) (Φ : ι → Mn →* G) (iota : H →* Mg) (ε : H →* G) :
    Prop :=
  ∀ k g y, ext k g = iota y → Φ k g = ε y

variable (ext : ι → Mn →* Mg) (Φ : ι → Mn →* G) (iota : H →* Mg) (ε : H →* G)

@[expose] noncomputable def peTrans {P : Type*} [Group P] (i : ι) (hi : Function.Injective (ext i))
    (y : H) (p : P →* Mg) (hp : ∀ x, (iota y)⁻¹ * p x * iota y ∈ (ext i).range) : P →* G :=
  (MulAut.conj (ε y)).toMonoidHom.comp ((Φ i).comp
    ((MonoidHom.ofInjective hi).symm.toMonoidHom.comp
      (((MulAut.conj (iota y)⁻¹).toMonoidHom.comp p).codRestrict _ fun x => by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          inv_inv] using hp x)))

variable {ext Φ iota ε}

theorem peTrans_apply {P : Type*} [Group P] {i : ι} (hi : Function.Injective (ext i)) {y : H}
    {p : P →* Mg} (hp : ∀ x, (iota y)⁻¹ * p x * iota y ∈ (ext i).range) (x : P) {g : Mn}
    (hg : ext i g = (iota y)⁻¹ * p x * iota y) :
    peTrans ext Φ iota ε i hi y p hp x = ε y * Φ i g * (ε y)⁻¹ := by
  have h1 : (MonoidHom.ofInjective hi).symm
      ((((MulAut.conj (iota y)⁻¹).toMonoidHom.comp p).codRestrict _ fun x => by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          inv_inv] using hp x) x) = g := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, hg]
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  simp only [peTrans, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h1]

theorem peTrans_value_eq (hA : PEAligned ext Φ) (hN : PENormal ext Φ iota ε) {i i' : ι}
    {y y' : H} (hm : iota (y⁻¹ * y') ∈ (ext i).range) {x : Mg} {g g' : Mn}
    (hg : ext i g = (iota y)⁻¹ * x * iota y) (hg' : ext i' g' = (iota y')⁻¹ * x * iota y') :
    ε y * Φ i g * (ε y)⁻¹ = ε y' * Φ i' g' * (ε y')⁻¹ := by
  obtain ⟨m, hm⟩ := hm
  have hm1 : Φ i m = ε (y⁻¹ * y') := hN i m _ hm
  have hext : ext i' g' = ext i (m⁻¹ * g * m) := by
    rw [hg', map_mul, map_mul, map_inv, hm, hg, map_mul, map_inv]
    group
  have h2 : Φ i' g' = Φ i (m⁻¹ * g * m) := hA i' i g' _ hext
  rw [h2, map_mul, map_mul, map_inv, hm1, map_mul, map_inv]
  group

theorem peTrans_value_iota (hN : PENormal ext Φ iota ε) {i : ι} {y z : H} {g : Mn}
    (hg : ext i g = (iota y)⁻¹ * iota z * iota y) : ε y * Φ i g * (ε y)⁻¹ = ε z := by
  have h : ext i g = iota (y⁻¹ * z * y) := by rw [hg, map_mul, map_mul, map_inv]
  rw [hN i g _ h, map_mul, map_mul, map_inv]
  group

end Transport

section Placement

variable {G Mg Mn H : Type*} [Group G] [Group Mg] [Group Mn] [Group H] {ι : Type*}
  {S : Type*} [Group S] (D : CFSG.LieType.Universal.UniversalRootDatum S)
  (ext : ι → Mn →* Mg) (Φ : ι → Mn →* G) (iota : H →* Mg) (ε : H →* G) (ρ : S →* Mg)

@[expose] noncomputable def peFamily (idx : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι)
    (tr : {J : Finset (Fin D.rank) // J.card ≤ 2} → H) (hinj : ∀ i, Function.Injective (ext i))
    (hmem : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
      (iota (tr J))⁻¹ * ρ x * iota (tr J) ∈ (ext (idx J)).range) :
    ∀ J, D.leviAmalgam J →* G := fun J =>
  peTrans ext Φ iota ε (idx J) (hinj (idx J)) (tr J) (ρ.comp (D.leviAmalgam J).subtype) (hmem J)

variable {D ext Φ iota ε ρ}

theorem peFamily_apply {idx : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι}
    {tr : {J : Finset (Fin D.rank) // J.card ≤ 2} → H} {hinj : ∀ i, Function.Injective (ext i)}
    {hmem : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
      (iota (tr J))⁻¹ * ρ x * iota (tr J) ∈ (ext (idx J)).range}
    (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J) {g : Mn}
    (hg : ext (idx J) g = (iota (tr J))⁻¹ * ρ x * iota (tr J)) :
    peFamily D ext Φ iota ε ρ idx tr hinj hmem J x = ε (tr J) * Φ (idx J) g * (ε (tr J))⁻¹ :=
  peTrans_apply _ _ x hg

theorem pe_levi_empty_eq_bot :
    CFSG.LieType.CurtisTits.levi D.rootGroup (∅ : Finset (Fin D.rank)) = ⊥ := by
  simp [CFSG.LieType.CurtisTits.levi]

theorem isCompatible_peFamily (hA : PEAligned ext Φ) (hN : PENormal ext Φ iota ε)
    {idx : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι}
    {tr : {J : Finset (Fin D.rank) // J.card ≤ 2} → H} {hinj : ∀ i, Function.Injective (ext i)}
    {hmem : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
      (iota (tr J))⁻¹ * ρ x * iota (tr J) ∈ (ext (idx J)).range}
    (hcomp : ∀ I J : {J : Finset (Fin D.rank) // J.card ≤ 2}, I ≤ J → I.1.Nonempty →
      iota ((tr I)⁻¹ * tr J) ∈ (ext (idx I)).range) :
    CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam
      (peFamily D ext Φ iota ε ρ idx tr hinj hmem) := by
  intro I J hIJ x y hxy
  rcases I.1.eq_empty_or_nonempty with hI | hI
  · have hx : (x : S) = 1 := by
      have h := x.2
      change (x : S) ∈ CFSG.LieType.CurtisTits.levi D.rootGroup I.1 at h
      rw [hI, pe_levi_empty_eq_bot, Subgroup.mem_bot] at h
      exact h
    have hx1 : x = 1 := Subtype.ext hx
    have hy1 : y = 1 := Subtype.ext (hxy.symm.trans hx)
    rw [hx1, hy1, map_one, map_one]
  · obtain ⟨g, hg⟩ := hmem I x
    obtain ⟨g', hg'⟩ := hmem J y
    rw [peFamily_apply I x hg, peFamily_apply J y hg']
    refine peTrans_value_eq hA hN (hcomp I J hIJ hI) hg ?_
    rw [hg', hxy]

theorem range_peFamily_le {idx : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι}
    {tr : {J : Finset (Fin D.rank) // J.card ≤ 2} → H} {hinj : ∀ i, Function.Injective (ext i)}
    {hmem : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
      (iota (tr J))⁻¹ * ρ x * iota (tr J) ∈ (ext (idx J)).range}
    {T : Subgroup G} (hΦ : ∀ i, (Φ i).range ≤ T) (hε : ε.range ≤ T)
    (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) :
    (peFamily D ext Φ iota ε ρ idx tr hinj hmem J).range ≤ T := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, hg⟩ := hmem J x
  rw [peFamily_apply J x hg]
  exact mul_mem (mul_mem (hε ⟨_, rfl⟩) (hΦ _ ⟨g, rfl⟩)) (inv_mem (hε ⟨_, rfl⟩))

end Placement

section Completion

variable {G S : Type} [Group G] [Group S]

theorem exists_ct_of_compatible {D : CFSG.LieType.Universal.UniversalRootDatum S}
    {τ : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hCT : CFSG.LieType.CurtisTits.CurtisTitsConclusion.{0} D τ n p f) (hZ : center S = ⊥)
    (φ : ∀ J, D.leviAmalgam J →* G) (hφ : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : S →* G, Function.Injective ψ ∧ ψ.range = ⨆ J, (φ J).range ∧
      ∀ J (x : D.leviAmalgam J), ψ x = φ J x := by
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, D.leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hφ I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt' : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨J, x, hx⟩ := hnt
    exact ⟨J, x, fun h => hx (congrArg Subtype.val h)⟩
  obtain ⟨-, -, hrec, -⟩ := hCT
  obtain ⟨ψ₀, hψ₀, hsurj, hker, -, -, -, -⟩ := hrec G₀ φ' hcomp' hgen' hnt'
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have h1 := hker hz
    rw [hZ] at h1
    exact h1
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, fun J x =>
    congrArg Subtype.val (hψ₀ J x)⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem range_le_range_of_perfect_centralizer [Finite G] {Mn : Type*} [Group Mn] [Finite Mn]
    {ψ : S →* G} (hψ : Function.Injective ψ) {A : Subgroup S} (hA : ⁅A, A⁆ = A) {z : G}
    (hAz : A.map ψ ≤ centralizer ({z} : Set G)) {Φ : Mn →* G}
    (hΦ : Φ.range = perfectCore (centralizer ({z} : Set G))) (hcard : Nat.card Mn ≤ Nat.card A) :
    Φ.range ≤ ψ.range := by
  have hperf : ⁅A.map ψ, A.map ψ⁆ = A.map ψ := by rw [← Subgroup.map_commutator, hA]
  have hle : A.map ψ ≤ Φ.range := hΦ ▸ le_perfectCore_of_perfect hAz hperf
  have hcardA : Nat.card (A.map ψ) = Nat.card A := Subgroup.card_map_of_injective (K := A) hψ
  have hcardΦ : Nat.card Φ.range ≤ Nat.card Mn :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective Φ)
  have heq : A.map ψ = Φ.range :=
    Subgroup.eq_of_le_of_card_ge hle (hcardΦ.trans (hcard.trans hcardA.ge))
  rw [← heq]
  exact Subgroup.map_le_range ψ A

end Completion

end CFSG.SeitzReduction.SymplecticPilot
