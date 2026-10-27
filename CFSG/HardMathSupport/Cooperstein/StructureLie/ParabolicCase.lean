module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
public import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup
public import CFSG.Quasithin.Background.SmithC27RDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Quasithin.SmithC27
open CFSG.HardMathSupport.Cooperstein.Proving

section Normalizer

variable {Q : Type} [Group Q]

theorem mem_normalizer_of_conj_mem {H : Subgroup Q} {x : Q}
    (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) (h' : ∀ y ∈ H, x⁻¹ * y * x ∈ H) :
    x ∈ Subgroup.normalizer (H : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have := h' _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem mem_normalizer_pCoreOf {p : ℕ} {H : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.normalizer (H : Set Q)) :
    g ∈ Subgroup.normalizer (pCoreOf p H : Set Q) :=
  mem_normalizer_of_conj_mem (fun _ hx => conj_mem_pCoreOf hg hx) fun _ hx => by
    simpa using conj_mem_pCoreOf ((Subgroup.normalizer (H : Set Q)).inv_mem hg) hx

end Normalizer

section GammaLevel

variable {Γ : Type} [Group Γ]

theorem exists_isSylowTwoOf [Finite Γ] (L : Subgroup Γ) : ∃ T : Subgroup Γ, IsSylowTwoOf T L := by
  have : Finite ↥L := Finite.of_injective _ Subtype.val_injective
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥L)
  refine ⟨(P : Subgroup ↥L).map L.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  have e : ((P : Subgroup ↥L).map L.subtype).subgroupOf L = P :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [e]
  exact P.not_dvd_index

theorem pCoreOf_normalizer_inf_eq {Sb Lb : Subgroup Γ} (hSb : IsPGroup 2 Sb)
    (h82 : ∀ U : Subgroup Γ, U ≤ Lb → IsPGroup 2 U →
      Subgroup.normalizer (Sb : Set Γ) ⊓ Subgroup.normalizer (Lb : Set Γ) ≤
        Subgroup.normalizer (U : Set Γ) → U ≤ Sb) :
    pCoreOf 2 (Subgroup.normalizer (Sb : Set Γ) ⊓ Lb) = Sb ⊓ Lb := by
  apply le_antisymm
  · set U := pCoreOf 2 (Subgroup.normalizer (Sb : Set Γ) ⊓ Lb) with hU
    have hUL : U ≤ Lb :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right
    refine le_inf (h82 U hUL (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) ?_) hUL
    intro g hg
    refine mem_normalizer_pCoreOf (Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, hg.2⟩)
    exact Subgroup.le_normalizer hg.1
  · have hle : Sb ⊓ Lb ≤ Subgroup.normalizer (Sb : Set Γ) ⊓ Lb :=
      inf_le_inf_right Lb Subgroup.le_normalizer
    refine le_pCoreOf_of_normal_in hle (fun h hh a ha => ⟨?_, ?_⟩) (hSb.to_le inf_le_left)
    · exact (Subgroup.mem_normalizer_iff.mp hh.1 a).mp ha.1
    · exact Lb.mul_mem (Lb.mul_mem hh.2 ha.2) (Lb.inv_mem hh.2)

theorem isParabolicTwo_and_eq_pCoreOf_of_isRadicalParabolic [Finite Γ] {Sb Lb : Subgroup Γ}
    (hSb : IsPGroup 2 Sb) (hrad : IsRadicalParabolic Lb)
    (h82 : ∀ U : Subgroup Γ, U ≤ Lb → IsPGroup 2 U →
      Subgroup.normalizer (Sb : Set Γ) ⊓ Subgroup.normalizer (Lb : Set Γ) ≤
        Subgroup.normalizer (U : Set Γ) → U ≤ Sb)
    (hY : Subgroup.normalizer ((Sb ⊓ Lb : Subgroup Γ) : Set Γ) ⊓ Lb ≤
      Subgroup.normalizer (Sb : Set Γ)) :
    IsParabolicTwo Lb (Subgroup.normalizer (Sb : Set Γ) ⊓ Lb) ∧
      Sb ⊓ Lb = pCoreOf 2 (Subgroup.normalizer (Sb : Set Γ) ⊓ Lb) := by
  refine ⟨?_, (pCoreOf_normalizer_inf_eq hSb h82).symm⟩
  set R : Subgroup Γ := Sb ⊓ Lb with hR
  by_cases hR0 : R = ⊥
  · have hLN : Lb ≤ Subgroup.normalizer (Sb : Set Γ) := fun x hx =>
      hY ⟨by
        rw [hR0]
        exact Subgroup.mem_normalizer_iff.mpr fun y => by
          simp [Subgroup.mem_bot, mul_eq_one_iff_eq_inv, eq_comm], hx⟩
    rw [inf_eq_right.mpr hLN]
    obtain ⟨T, hT⟩ := exists_isSylowTwoOf Lb
    exact ⟨le_rfl, T, hT, inf_le_left⟩
  · have hRL : R ≤ Lb := inf_le_right
    have hRp : IsPGroup 2 R := hSb.to_le inf_le_left
    have hW : pCoreOf 2 (Lb ⊓ Subgroup.normalizer (R : Set Γ)) = R := by
      apply le_antisymm
      · set W := pCoreOf 2 (Lb ⊓ Subgroup.normalizer (R : Set Γ)) with hWdef
        have hWL : W ≤ Lb :=
          (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_left
        have hWS : W ≤ Sb := by
          refine h82 W hWL (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) ?_
          intro g hg
          have hgR : g ∈ Subgroup.normalizer (R : Set Γ) :=
            Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.1, hg.2⟩
          exact mem_normalizer_pCoreOf (Subgroup.inf_normalizer_le_normalizer_inf
            ⟨hg.2, Subgroup.le_normalizer hgR⟩)
        exact le_inf hWS hWL
      · have hle : R ≤ Lb ⊓ Subgroup.normalizer (R : Set Γ) := le_inf hRL Subgroup.le_normalizer
        exact le_pCoreOf_of_normal_in hle
          (fun h hh a ha => (Subgroup.mem_normalizer_iff.mp hh.2 a).mp ha) hRp
    have hP := hrad R hRL hR0 hRp hW
    have heq : Lb ⊓ Subgroup.normalizer (R : Set Γ) = Subgroup.normalizer (Sb : Set Γ) ⊓ Lb := by
      apply le_antisymm
      · intro x hx
        exact ⟨hY ⟨hx.2, hx.1⟩, hx.1⟩
      · intro x hx
        exact ⟨hx.2, Subgroup.inf_normalizer_le_normalizer_inf ⟨hx.1, Subgroup.le_normalizer hx.2⟩⟩
    rw [heq] at hP
    exact hP

end GammaLevel

section XLevel

variable {G : Type} [Group G] {X S L : Subgroup G}

abbrev barHom (X : Subgroup G) : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥X)

theorem mem_barM_iff {Y : Subgroup G} {γ : ↥X ⧸ CFSG.pCore 2 ↥X} :
    γ ∈ barM X Y ↔ ∃ x : ↥X, (x : G) ∈ Y ∧ barHom X x = γ := by
  simp [barM, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem barHom_mem_barM {Y : Subgroup G} {x : ↥X} (hx : (x : G) ∈ Y) :
    barHom X x ∈ barM X Y :=
  mem_barM_iff.mpr ⟨x, hx, rfl⟩

theorem mem_of_barHom_mem (hQ : pCoreOf 2 X ≤ S) {x : ↥X} (hx : barHom X x ∈ barM X S) :
    (x : G) ∈ S := by
  obtain ⟨y, hy, hxy⟩ := mem_barM_iff.mp hx
  have h1 : y⁻¹ * x ∈ CFSG.pCore 2 ↥X := QuotientGroup.eq.mp hxy
  have h2 : ((y⁻¹ * x : ↥X) : G) ∈ S := hQ (mem_pCoreOf_iff.mpr ⟨_, h1, rfl⟩)
  have h3 : (x : G) = (y : G) * ((y⁻¹ * x : ↥X) : G) := by simp
  rw [h3]
  exact S.mul_mem hy h2

theorem isPGroup_barM {p : ℕ} {Y : Subgroup G} (hY : IsPGroup p Y) : IsPGroup p (barM X Y) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
  obtain ⟨k, hk⟩ := hY ⟨(x : G), hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : ((x : G)) ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have h2 : x ^ (p ^ k) = 1 := Subtype.ext (by simpa using h1)
  change (barHom X x) ^ (p ^ k) = 1
  rw [← map_pow, h2, map_one]

theorem isPGroup_of_map_barHom {A : Subgroup ↥X} (hA : IsPGroup 2 (A.map (barHom X))) :
    IsPGroup 2 A := by
  rintro ⟨a, ha⟩
  obtain ⟨k, hk⟩ := hA ⟨barHom X a, Subgroup.mem_map_of_mem _ ha⟩
  have h1 : (barHom X a) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : a ^ (2 ^ k) ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using h1
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, h2⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h3 : (a ^ (2 ^ k)) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  simpa [pow_add, pow_mul] using h3

theorem barHom_conj_mem_barM {Y : Subgroup G} {x : ↥X}
    (hx : (x : G) ∈ Subgroup.normalizer (Y : Set G)) {γ : ↥X ⧸ CFSG.pCore 2 ↥X}
    (hγ : γ ∈ barM X Y) : barHom X x * γ * (barHom X x)⁻¹ ∈ barM X Y := by
  obtain ⟨y, hy, rfl⟩ := mem_barM_iff.mp hγ
  have : barHom X x * barHom X y * (barHom X x)⁻¹ = barHom X (x * y * x⁻¹) := by simp
  rw [this]
  exact barHom_mem_barM ((Subgroup.mem_normalizer_iff.mp hx _).mp hy)

theorem barHom_mem_normalizer_of_mem {Y : Subgroup G} {x : ↥X}
    (hx : (x : G) ∈ Subgroup.normalizer (Y : Set G)) :
    barHom X x ∈ Subgroup.normalizer (barM X Y : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  refine mem_normalizer_of_conj_mem (fun γ hγ => barHom_conj_mem_barM hx hγ) fun γ hγ => ?_
  have hx' : ((x⁻¹ : ↥X) : G) ∈ Subgroup.normalizer (Y : Set G) := by
    simpa using (Subgroup.normalizer (Y : Set G)).inv_mem hx
  simpa using barHom_conj_mem_barM hx' hγ

theorem mem_normalizer_of_barHom_mem_normalizer (hQ : pCoreOf 2 X ≤ S) (hSX : S ≤ X) {x : ↥X}
    (hx : barHom X x ∈ Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X))) :
    (x : G) ∈ Subgroup.normalizer (S : Set G) := by
  have key : ∀ z : ↥X, barHom X z ∈ Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X)) →
      ∀ s ∈ S, (z : G) * s * (z : G)⁻¹ ∈ S := by
    intro z hz s hs
    have h1 := (Subgroup.mem_normalizer_iff.mp hz (barHom X ⟨s, hSX hs⟩)).mp
      (barHom_mem_barM (X := X) (Y := S) (x := ⟨s, hSX hs⟩) hs)
    have h2 : barHom X z * barHom X ⟨s, hSX hs⟩ * (barHom X z)⁻¹ =
        barHom X (z * ⟨s, hSX hs⟩ * z⁻¹) := by simp
    rw [h2] at h1
    exact mem_of_barHom_mem hQ h1
  refine mem_normalizer_of_conj_mem (key x hx) fun s hs => ?_
  have hx' : barHom X x⁻¹ ∈ Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  simpa using key x⁻¹ hx' s hs

theorem barM_inf (hQ : pCoreOf 2 X ≤ S) :
    barM X (S ⊓ L) = barM X S ⊓ barM X L := by
  apply le_antisymm
  · intro γ hγ
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
    exact ⟨barHom_mem_barM hx.1, barHom_mem_barM hx.2⟩
  · rintro γ ⟨hγS, hγL⟩
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγL
    exact barHom_mem_barM ⟨mem_of_barHom_mem hQ hγS, hx⟩

theorem barM_normalizer_inf (hQ : pCoreOf 2 X ≤ S) (hSX : S ≤ X) :
    barM X (Subgroup.normalizer (S : Set G) ⊓ L) =
      Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X)) ⊓ barM X L := by
  apply le_antisymm
  · intro γ hγ
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
    exact ⟨barHom_mem_normalizer_of_mem hx.1, barHom_mem_barM hx.2⟩
  · rintro γ ⟨hγS, hγL⟩
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγL
    exact barHom_mem_barM ⟨mem_normalizer_of_barHom_mem_normalizer hQ hSX hγS, hx⟩

variable [Finite G]

theorem le_barM_of_normalizer_le (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    {U : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hUL : U ≤ barM X L) (hU : IsPGroup 2 U)
    (hN : Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X)) ⊓
      Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) ≤
        Subgroup.normalizer (U : Set (↥X ⧸ CFSG.pCore 2 ↥X))) : U ≤ barM X S := by
  set A : Subgroup ↥X := U.comap (barHom X) with hAdef
  set U' : Subgroup G := A.map X.subtype ⊓ L with hU'
  have hU'L : U' ≤ L := inf_le_right
  have hmemU' : ∀ {l : G}, l ∈ U' ↔ ∃ x : ↥X, barHom X x ∈ U ∧ (x : G) = l ∧ l ∈ L := by
    intro l
    simp only [hU', Subgroup.mem_inf, Subgroup.mem_map, hAdef, Subgroup.mem_comap,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hl⟩
      exact ⟨x, hx, rfl, hl⟩
    · rintro ⟨x, hx, rfl, hl⟩
      exact ⟨⟨x, hx, rfl⟩, hl⟩
  have hU'p : IsPGroup 2 U' := by
    have hAp : IsPGroup 2 A :=
      isPGroup_of_map_barHom (hU.to_le (Subgroup.map_comap_le _ _))
    exact (hAp.map X.subtype).to_le inf_le_left
  have hN' : X ⊓ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (U' : Set G) := by
    have key : ∀ g : G, g ∈ X ⊓ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G) →
        ∀ u ∈ U', g * u * g⁻¹ ∈ U' := by
      intro g hg u hu
      obtain ⟨x, hxU, rfl, huL⟩ := hmemU'.mp hu
      have hgN : barHom X ⟨g, hg.1.1⟩ ∈ Subgroup.normalizer (U : Set _) :=
        hN ⟨barHom_mem_normalizer_of_mem (Y := S) hg.1.2, barHom_mem_normalizer_of_mem (Y := L) hg.2⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hgN (barHom X x)).mp hxU
      refine hmemU'.mpr ⟨⟨g, hg.1.1⟩ * x * ⟨g, hg.1.1⟩⁻¹, ?_, rfl, ?_⟩
      · simpa using h1
      · exact (Subgroup.mem_normalizer_iff.mp hg.2 _).mp huL
    intro g hg
    refine mem_normalizer_of_conj_mem (key g hg) fun u hu => ?_
    simpa using key g⁻¹ ((X ⊓ Subgroup.normalizer (S : Set G) ⊓
      Subgroup.normalizer (L : Set G)).inv_mem hg) u hu
  have hU'S : U' ≤ S :=
    Coordinator.le_of_le_twoPrimeComponent hA hL hU'L hU'p hN'
  intro γ hγ
  obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp (hUL hγ)
  exact barHom_mem_barM (hU'S (hmemU'.mpr ⟨x, hγ, rfl, hx⟩))

theorem barM_inf_eq_pCoreOf (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    barM X (S ⊓ L) = pCoreOf 2 (barM X (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  have hQ : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hSX : S ≤ X := hA.twoRadical.1
  rw [barM_inf hQ, barM_normalizer_inf hQ hSX]
  exact (pCoreOf_normalizer_inf_eq (isPGroup_barM hA.twoRadical.isPGroup)
    fun U hUL hU hN => le_barM_of_normalizer_le hA hL hUL hU hN).symm

theorem nineThreeTwo_of_isRadicalParabolic (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hcl : IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)))
    (hrad : IsRadicalParabolic (barM X L))
    (hY : Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) ⊓ barM X L ≤
      Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X))) :
    NineThreeTwo X S L := by
  have hQ : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hSX : S ≤ X := hA.twoRadical.1
  rw [barM_inf hQ] at hY
  obtain ⟨hpar, -⟩ := isParabolicTwo_and_eq_pCoreOf_of_isRadicalParabolic
    (isPGroup_barM hA.twoRadical.isPGroup) hrad
    (fun U hUL hU hN => le_barM_of_normalizer_le hA hL hUL hU hN) hY
  refine ⟨hcl, ?_, barM_inf_eq_pCoreOf hA hL⟩
  rw [barM_normalizer_inf hQ hSX]
  exact hpar

end XLevel

end CFSG.HardMathSupport.Cooperstein.StructureLie
