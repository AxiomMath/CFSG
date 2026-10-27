module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusStepSplit
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer {B : Subgroup G} {g : G} (hg : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer (centralizer (B : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (B : Set G), ∀ x ∈ centralizer (B : Set G),
      g * x * g⁻¹ ∈ centralizer (B : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : g⁻¹ * b * g ∈ B := by
      have := (mem_normalizer_iff.mp ((normalizer (B : Set G)).inv_mem hg) b).mp hb
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx _ hb'
    calc b * (g * x * g⁻¹) = g * ((g⁻¹ * b * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * b := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ ((normalizer (B : Set G)).inv_mem hg) _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem mem_normalizer_map_subtype (Y : Subgroup G) (P : Subgroup ↥Y) {g : G}
    (hg : g ∈ normalizer (Y : Set G))
    (hP : ∀ y : ↥Y, (Y.normalizerMonoidHom ⟨g, hg⟩ y ∈ P ↔ y ∈ P)) :
    g ∈ normalizer ((P.map Y.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (hP y).mpr hy, rfl⟩
  · rintro ⟨y', hy', hy'z⟩
    have hzY : z ∈ Y := (mem_normalizer_iff.mp hg z).mpr (hy'z ▸ y'.2)
    refine ⟨⟨z, hzY⟩, (hP ⟨z, hzY⟩).mp ?_, rfl⟩
    have : Y.normalizerMonoidHom ⟨g, hg⟩ ⟨z, hzY⟩ = y' := Subtype.ext hy'z.symm
    rw [this]
    exact hy'

theorem mem_iff_of_map_eq {A : Type} [Group A] (P : Subgroup A) (α : MulAut A)
    (h : P.map α.toMonoidHom = P) (x : A) : α x ∈ P ↔ x ∈ P := by
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := α.injective hzx
    rwa [← this]
  · intro hx
    have : α x ∈ P.map α.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this

theorem caseB [Finite G] (M : Subgroup G) [M.Normal] (B T : Subgroup G) (hT : IsPGroup 2 T)
    (hBT : B ≤ T) (hTn : T ≤ normalizer (B : Set G)) (hTM : T ≤ M ⊔ B)
    (IH : ∀ d ∈ NPlusIn (centralizer (T : Set G)), TwoElt d → d ∈ M) :
    ∀ u ∈ NPlusIn (centralizer (B : Set G)), TwoElt u → u ∈ M := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := centralizer (B : Set G) with hY
  have hNY : ∀ g ∈ normalizer (B : Set G), g ∈ normalizer (Y : Set G) :=
    fun g hg => mem_normalizer_centralizer hg
  let c : ∀ g : G, g ∈ normalizer (B : Set G) → MulAut ↥Y :=
    fun g hg => Y.normalizerMonoidHom ⟨g, hNY g hg⟩
  have hc : ∀ (g : G) (hg : g ∈ normalizer (B : Set G)) (y : ↥Y),
      ((c g hg y : ↥Y) : G) = g * (y : G) * g⁻¹ := fun _ _ _ => rfl
  let 𝒢' : Set (MulAut ↥Y) := {α | ∃ (g : G) (hg : g ∈ normalizer (B : Set G)), α = c g hg}
  let 𝒢 : Set (MulAut ↥Y) := {α | ∃ (g : G) (hg : g ∈ T), α = c g (hTn hg)}
  have hsub : 𝒢 ⊆ 𝒢' := by
    rintro α ⟨g, hg, rfl⟩
    exact ⟨g, hTn hg, rfl⟩
  set M' : Subgroup ↥Y := M.comap Y.subtype with hM'
  have hM'n : M'.Normal := Subgroup.Normal.comap inferInstance _
  set XY : Subgroup ↥Y := NPlus ↥Y ⊓ M' with hXY
  have hXYn : XY.Normal := inferInstance
  have hXM : XY ≤ M' := inf_le_right
  have hX : ∀ α ∈ 𝒢', XY.map α.toMonoidHom = XY := by
    rintro _ ⟨g, hg, rfl⟩
    apply map_eq_of_map_le
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have : c g hg x ∈ (NPlus ↥Y).map (c g hg).toMonoidHom := ⟨x, hx.1, rfl⟩
      rwa [NPlus_map_aut] at this
    · show ((c g hg x : ↥Y) : G) ∈ M
      rw [hc g hg]
      exact (inferInstance : M.Normal).conj_mem _ hx.2 g
  have hcomm : ∀ α ∈ 𝒢, ∀ z ∈ NPlus ↥Y, z⁻¹ * α z ∈ XY := by
    rintro _ ⟨g, hg, rfl⟩ z hz
    refine ⟨?_, ?_⟩
    · have h1 : c g (hTn hg) z ∈ NPlus ↥Y := by
        have : c g (hTn hg) z ∈ (NPlus ↥Y).map (c g (hTn hg)).toMonoidHom := ⟨z, hz, rfl⟩
        rwa [NPlus_map_aut] at this
      exact (NPlus ↥Y).mul_mem ((NPlus ↥Y).inv_mem hz) h1
    · show (((z⁻¹ * c g (hTn hg) z : ↥Y)) : G) ∈ M
      obtain ⟨m, hm, b, hb, hmb⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing M B
        Subgroup.le_normalizer_of_normal g).mp (hTM hg)
      have hbz : b * (z : G) = (z : G) * b := Subgroup.mem_centralizer_iff.mp z.2 b hb
      have e1 : (((z⁻¹ * c g (hTn hg) z : ↥Y)) : G) = (z : G)⁻¹ * (g * (z : G) * g⁻¹) := rfl
      rw [e1, ← hmb]
      have e2 : (z : G)⁻¹ * (m * b * (z : G) * (m * b)⁻¹) =
          ((z : G)⁻¹ * m * (z : G)) * m⁻¹ := by
        calc (z : G)⁻¹ * (m * b * (z : G) * (m * b)⁻¹)
            = (z : G)⁻¹ * (m * (b * (z : G)) * b⁻¹ * m⁻¹) := by group
          _ = (z : G)⁻¹ * (m * ((z : G) * b) * b⁻¹ * m⁻¹) := by rw [hbz]
          _ = ((z : G)⁻¹ * m * (z : G)) * m⁻¹ := by group
      rw [e2]
      refine M.mul_mem ?_ (M.inv_mem hm)
      have := (inferInstance : M.Normal).conj_mem m hm (z : G)⁻¹
      simpa using this
  obtain ⟨Z0, Z1, hZsup, hZ0n, hZ1n, hOZ1, hZ1inv, hZ0two, hZ1fix, hD⟩ :=
    step_split XY M' hXM 𝒢' 𝒢 hsub hX hcomm
  have hOY : ∀ φ : MulAut ↥Y, (pPrimeCore 2 ↥Y).map φ.toMonoidHom = pPrimeCore 2 ↥Y :=
    fun φ => pPrimeCore_map_iso 2 φ
  have hZ1M : ∀ z ∈ Z1, TwoElt z → (z : G) ∈ M := by
    intro z hz h2z
    set K : Subgroup G := Z1.map Y.subtype with hK
    set Oo : Subgroup G := (pPrimeCore 2 ↥Y).map Y.subtype with hOo
    have hOoodd : Odd (Nat.card Oo) := by
      rw [hOo, Subgroup.card_map_of_injective Y.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hOoK : Oo ≤ K := Subgroup.map_mono hOZ1
    have hKY : K ≤ Y := Subgroup.map_subtype_le _
    have hYOo : Y ≤ normalizer (Oo : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_map_subtype Y _ hOY)
    have hTY : T ≤ normalizer (Y : Set G) := fun g hg => hNY g (hTn hg)
    have hTOo : T ≤ normalizer (Oo : Set G) :=
      hTY.trans (normalizer_le_normalizer_map_subtype Y _ hOY)
    have hOoKn : (Oo.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOoK).mpr (hKY.trans hYOo)
    have hcommTO : ⁅K, T⁆ ≤ Oo := by
      rw [Subgroup.commutator_le]
      rintro k ⟨w, hw, rfl⟩ t ht
      have h1 := hZ1fix (c t (hTn ht)) ⟨t, ht, rfl⟩ w⁻¹ (Z1.inv_mem hw)
      exact ⟨_, h1, by simp [commutatorElement_def, hc, mul_assoc]⟩
    have hfac := ClassicalInvolution.LBalanceProof.exists_centralizer_mul_of_commutator_le K T Oo
      hT hOoK hOoKn hOoodd hTOo hcommTO
    set D : Subgroup G := K ⊓ centralizer (T : Set G) with hDdef
    have hDY : D ≤ Y := inf_le_left.trans hKY
    have hCY : centralizer (T : Set G) ≤ Y :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBT)
    have hDZ : D.subgroupOf Y ≤ Z1 := by
      intro y hy
      have hyD : (y : G) ∈ D := hy
      obtain ⟨w, hw, hwy⟩ := hyD.1
      have : w = y := Subtype.ext hwy
      rwa [← this]
    have hZD : Z1 ≤ D.subgroupOf Y ⊔ pPrimeCore 2 ↥Y := by
      intro y hy
      obtain ⟨cc, hcc, m, hm, hcm⟩ := hfac (y : G) ⟨y, hy, rfl⟩
      obtain ⟨o, ho, hom⟩ := hm
      have hcY : cc ∈ Y := hDY hcc
      have : y = ⟨cc, hcY⟩ * o := Subtype.ext (by
        show (y : G) = cc * (o : G)
        rw [hcm, ← hom]
        rfl)
      rw [this]
      exact Subgroup.mul_mem_sup (show (⟨cc, hcY⟩ : ↥Y) ∈ D.subgroupOf Y from hcc) ho
    have hNPtop : NPlus ↥(D.subgroupOf Y) = ⊤ := hD _ hDZ hZD
    have hDNP : NPlus ↥D = ⊤ := by
      let e := Subgroup.subgroupOfEquivOfLe hDY
      have h1 := NPlus_map_equiv e
      rw [hNPtop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective] at h1
      exact h1.symm
    have hDD : D ≤ NPlusIn D := by
      intro d hd
      exact ⟨⟨d, hd⟩, by rw [hDNP]; trivial, rfl⟩
    have hCn : centralizer (T : Set G) ≤ normalizer (D : Set G) := by
      intro g hg
      have hgB : g ∈ normalizer (B : Set G) :=
        Subgroup.centralizer_le_normalizer (B : Set G) (hCY hg)
      have hgY : g ∈ normalizer (Y : Set G) := hNY g hgB
      have hgK : g ∈ normalizer (K : Set G) := by
        refine mem_normalizer_map_subtype Y Z1 hgY ?_
        exact mem_iff_of_map_eq Z1 (c g hgB) (hZ1inv (c g hgB) ⟨g, hgB, rfl⟩)
      have hgC : g ∈ normalizer (centralizer (T : Set G) : Set G) := Subgroup.le_normalizer hg
      rw [mem_normalizer_iff]
      intro x
      have h1' := mem_normalizer_iff.mp hgK x
      have h2' := mem_normalizer_iff.mp hgC x
      show x ∈ K ⊓ centralizer (T : Set G) ↔ g * x * g⁻¹ ∈ K ⊓ centralizer (T : Set G)
      simp only [Subgroup.mem_inf]
      exact and_congr h1' h2'
    have hDNPin : NPlusIn D ≤ NPlusIn (centralizer (T : Set G)) :=
      NPlusIn_le_of_normal inf_le_right hCn
    have hDtwo : ∀ d ∈ D, TwoElt d → d ∈ M := fun d hd h2d => IH d (hDNPin (hDD hd)) h2d
    have hyz : (z : G) ∈ Oo ⊔ D := by
      obtain ⟨cc, hcc, m, hm, hcm⟩ := hfac (z : G) ⟨z, hz, rfl⟩
      rw [hcm, sup_comm]
      exact Subgroup.mul_mem_sup hcc hm
    exact twoElt_mem_sup_odd (D := D) (O := Oo) (M := M) (hDY.trans hYOo) hOoodd hDtwo hyz
      (h2z.map Y.subtype)
  intro u hu h2u
  obtain ⟨z, hz, rfl⟩ := hu
  have hz2 : TwoElt z := TwoElt.of_injective (f := Y.subtype) Y.subtype_injective h2u
  rw [hZsup] at hz
  have hmem := twoElt_mem_sup_of_normalizes (Subgroup.le_normalizer_of_normal)
    (Subgroup.le_normalizer_of_normal) hz hz2
  have hle : oTwoPrimeOf Z0 ⊔ oTwoPrimeOf Z1 ≤ M' :=
    sup_le (oTwoPrimeOf_le_iff.mpr hZ0two) (oTwoPrimeOf_le_iff.mpr fun x hx h2 => hZ1M x hx h2)
  exact hle hmem

end CFSG.OddStandard.Solomon75
