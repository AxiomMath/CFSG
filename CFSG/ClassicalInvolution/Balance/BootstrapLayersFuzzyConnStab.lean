module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnLink

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices LinkMove mem_fuzzyVertices_map)
open scoped commutatorElement

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

abbrev frameLink (p f : ℕ) [Fact p.Prime] (𝒞 : Set (Subgroup G)) (a : G) :
    Subgroup G → Subgroup G → Prop :=
  LinkMove (fuzzyFrames p f 𝒞) (fuzzyVertices p f 𝒞) a

omit [Finite G] in
theorem map_conj_comm_conj (X : Subgroup G) (g y : G) :
    (X.map (MulAut.conj y).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * y * g⁻¹)).toMonoidHom := by
  have h1 : (X.map (MulAut.conj y).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g * y)).toMonoidHom := by
    exact (conjSub_mul g y X).symm
  have h2 : (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * y * g⁻¹)).toMonoidHom =
      X.map (MulAut.conj (g * y * g⁻¹ * g)).toMonoidHom := by
    exact (conjSub_mul (g * y * g⁻¹) g X).symm
  rw [h1, h2]
  have : g * y * g⁻¹ * g = g * y := by group
  rw [this]

omit [Finite G] in
theorem map_conj_inv_map_conj (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  show conjSub g⁻¹ (conjSub g X) = X
  rw [← conjSub_mul]
  simp

variable {𝒞 : Set (Subgroup G)} {a : G}

theorem frameLink_symm {X Y : Subgroup G} (h : frameLink p f 𝒞 a X Y) : frameLink p f 𝒞 a Y X := by
  obtain ⟨hX, hY, hXa, hYa, hmove⟩ := h
  refine ⟨hY, hX, hYa, hXa, ?_⟩
  rcases hmove with h | ⟨y, hy, rfl⟩
  · exact Or.inl (ShareFour.symm h)
  · refine Or.inr ⟨y⁻¹, inv_mem hy, ?_⟩
    rw [map_conj_inv_map_conj]

theorem frameLink_conj (hinv : ConjInvariant 𝒞) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) {X Y : Subgroup G}
    (h : frameLink p f 𝒞 a X Y) :
    frameLink p f 𝒞 a (X.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hX, hY, hXa, hYa, hmove⟩ := h
  have hcl : ∀ {Z : Subgroup G}, a ∈ fuzzyVertices p f 𝒞 Z →
      a ∈ fuzzyVertices p f 𝒞 (Z.map (MulAut.conj g).toMonoidHom) := fun hZ => by
    have := mem_fuzzyVertices_map hinv hZ g
    rwa [conj_eq_of_mem_centralizer_singleton hg] at this
  refine ⟨FuzzyFrameOn.map hinv hX g, FuzzyFrameOn.map hinv hY g, hcl hXa, hcl hYa, ?_⟩
  rcases hmove with ⟨F, ⟨hFX, hF4⟩, ⟨hFY, -⟩⟩ | ⟨y, hy, rfl⟩
  · left
    have hF : Nat.card (F.map (MulAut.conj g).toMonoidHom) = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hF4
    exact ⟨F.map (MulAut.conj g).toMonoidHom, ⟨Subgroup.map_mono hFX, hF⟩,
      ⟨Subgroup.map_mono hFY, hF⟩⟩
  · right
    exact ⟨g * y * g⁻¹, conj_mem_oddCoreIn hg hy, map_conj_comm_conj X g y⟩

theorem reflTransGen_frameLink_symm {X Y : Subgroup G}
    (h : Relation.ReflTransGen (frameLink p f 𝒞 a) X Y) :
    Relation.ReflTransGen (frameLink p f 𝒞 a) Y X := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (frameLink_symm hbc)).trans ih

theorem reflTransGen_frameLink_conj (hinv : ConjInvariant 𝒞) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) {X Y : Subgroup G}
    (h : Relation.ReflTransGen (frameLink p f 𝒞 a) X Y) :
    Relation.ReflTransGen (frameLink p f 𝒞 a) (X.map (MulAut.conj g).toMonoidHom)
      (Y.map (MulAut.conj g).toMonoidHom) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (frameLink_conj hinv hg hbc)

theorem reflTransGen_frameLink_conj_of_coset (hinv : ConjInvariant 𝒞) {B : Subgroup G}
    (hB : FuzzyFrameOn p f 𝒞 B) (haB : a ∈ fuzzyVertices p f 𝒞 B) {g x : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (hxB : x ∈ B) (hx1 : x ≠ 1) (hxa : x ≠ a)
    (hcoset : x⁻¹ * (g * x * g⁻¹) ∈ involutionOddCore a) :
    Relation.ReflTransGen (frameLink p f 𝒞 a) B (B.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hBa, J, hJ𝒞, hJa, hBJ⟩ := haB
  have ca := isCentralInvolution_of_isClassicalMember hJa
  obtain ⟨J₀, z₀, hJz, hAdef, hel, hcard, htriv⟩ := hB
  have hBc : ∀ {u v : G}, u ∈ B → v ∈ B → u * v = v * u := fun hu hv =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hu⟩ : B) ⟨_, hv⟩)
  have hB2 : ∀ {u : G}, u ∈ B → u * u = 1 := fun hu => by
    rw [← pow_two]
    exact hel.2 _ hu
  have hx2 := hB2 hxB
  have hx'2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨y, hy, hyx⟩ := exists_mem_oddCoreIn_conj_eq (X := Subgroup.centralizer ({a} : Set G)) hx2
    hx'2 (by rw [← involutionOddCore_eq_oddCoreIn]; exact hcoset)
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hy
  have hB' : FuzzyFrameOn p f 𝒞 B := ⟨J₀, z₀, hJz, hAdef, hel, hcard, htriv⟩
  set B₂ : Subgroup G := B.map (MulAut.conj g).toMonoidHom with hB₂
  set B₁ : Subgroup G := B₂.map (MulAut.conj y⁻¹).toMonoidHom with hB₁
  have hB₂𝒯 : FuzzyFrameOn p f 𝒞 B₂ := FuzzyFrameOn.map hinv hB' g
  have hB₁𝒯 : FuzzyFrameOn p f 𝒞 B₁ := FuzzyFrameOn.map hinv hB₂𝒯 y⁻¹
  have hcl : ∀ (h : G), h ∈ Subgroup.centralizer ({a} : Set G) → ∀ {Z : Subgroup G},
      a ∈ fuzzyVertices p f 𝒞 Z → a ∈ fuzzyVertices p f 𝒞 (Z.map (MulAut.conj h).toMonoidHom) :=
    fun h hh Z hZ => by
      have := mem_fuzzyVertices_map hinv hZ h
      rwa [conj_eq_of_mem_centralizer_singleton hh] at this
  have haB' : a ∈ fuzzyVertices p f 𝒞 B := ⟨hBa, J, hJ𝒞, hJa, hBJ⟩
  have haB₂ := hcl g hg haB'
  have haB₁ := hcl y⁻¹ (inv_mem hyC) haB₂
  have h21 : frameLink p f 𝒞 a B₂ B₁ := by
    refine ⟨hB₂𝒯, hB₁𝒯, haB₂, haB₁, Or.inr ⟨y⁻¹, ?_, rfl⟩⟩
    exact inv_mem hy
  have haB₁mem : a ∈ B₁ := by
    have h1 : g * a * g⁻¹ ∈ B₂ := conj_mem_conjSub hBa
    have h2 : y⁻¹ * (g * a * g⁻¹) * y⁻¹⁻¹ ∈ B₁ := conj_mem_conjSub h1
    rwa [conj_eq_of_mem_centralizer_singleton hg, inv_inv,
      show y⁻¹ * a * y = a by
        have := conj_eq_of_mem_centralizer_singleton (inv_mem hyC)
        simpa using this] at h2
  have hxB₁mem : x ∈ B₁ := by
    have h1 : g * x * g⁻¹ ∈ B₂ := conj_mem_conjSub hxB
    have h2 : y⁻¹ * (g * x * g⁻¹) * y⁻¹⁻¹ ∈ B₁ := conj_mem_conjSub h1
    rwa [← hyx, inv_inv, show y⁻¹ * (y * x * y⁻¹) * y = x by group] at h2
  have hF4 : Nat.card (Subgroup.closure ({a, x} : Set G)) = 2 ^ 2 := by
    have h := card_closure_pair_eq_four ca.sq hx2 ca.ne_one hx1 (Ne.symm hxa)
      (hBc hBa hxB)
    rw [h]
    norm_num
  have hFB : Subgroup.closure ({a, x} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hBa
    · exact hxB
  have hFB₁ : Subgroup.closure ({a, x} : Set G) ≤ B₁ := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact haB₁mem
    · exact hxB₁mem
  have h1B : frameLink p f 𝒞 a B B₁ :=
    ⟨hB', hB₁𝒯, haB', haB₁, Or.inl ⟨_, ⟨hFB, hF4⟩, ⟨hFB₁, hF4⟩⟩⟩
  exact (Relation.ReflTransGen.single h1B).tail (frameLink_symm h21)

end Basic

section Stabilizer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

def linkStab (hinv : ConjInvariant 𝒞) (a : G) (B : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.centralizer ({a} : Set G) ∧
    Relation.ReflTransGen (frameLink p f 𝒞 a) B (B.map (MulAut.conj g).toMonoidHom)}
  one_mem' := ⟨one_mem _, by
    show Relation.ReflTransGen (frameLink p f 𝒞 a) B (conjSub 1 B)
    rw [conjSub_one]⟩
  mul_mem' := by
    rintro g h ⟨hg, hBg⟩ ⟨hh, hBh⟩
    refine ⟨mul_mem hg hh, hBg.trans ?_⟩
    have h1 := reflTransGen_frameLink_conj hinv hg hBh
    have h2 : (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        B.map (MulAut.conj (g * h)).toMonoidHom := (conjSub_mul g h B).symm
    rwa [h2] at h1
  inv_mem' := by
    rintro g ⟨hg, hBg⟩
    refine ⟨inv_mem hg, ?_⟩
    have h1 := reflTransGen_frameLink_conj hinv (inv_mem hg) hBg
    rw [map_conj_inv_map_conj] at h1
    exact reflTransGen_frameLink_symm h1

theorem mem_linkStab_iff (hinv : ConjInvariant 𝒞) {B : Subgroup G} {g : G} :
    g ∈ linkStab (p := p) (f := f) hinv a B ↔ g ∈ Subgroup.centralizer ({a} : Set G) ∧
      Relation.ReflTransGen (frameLink p f 𝒞 a) B (B.map (MulAut.conj g).toMonoidHom) :=
  Iff.rfl

theorem oddCoreIn_le_linkStab (hinv : ConjInvariant 𝒞) {B : Subgroup G}
    (hB : FuzzyFrameOn p f 𝒞 B) (haB : a ∈ fuzzyVertices p f 𝒞 B) :
    involutionOddCore a ≤ linkStab (p := p) (f := f) hinv a B := by
  intro y hy
  have hy' : y ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hy'
  refine ⟨hyC, Relation.ReflTransGen.single ⟨hB, FuzzyFrameOn.map hinv hB y, haB, ?_,
    Or.inr ⟨y, hy', rfl⟩⟩⟩
  have := mem_fuzzyVertices_map hinv haB y
  rwa [conj_eq_of_mem_centralizer_singleton hyC] at this

theorem mem_linkStab_of_coset (hinv : ConjInvariant 𝒞) {B : Subgroup G}
    (hB : FuzzyFrameOn p f 𝒞 B) (haB : a ∈ fuzzyVertices p f 𝒞 B) {g x : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (hxB : x ∈ B) (hx1 : x ≠ 1) (hxa : x ≠ a)
    (hcoset : x⁻¹ * (g * x * g⁻¹) ∈ involutionOddCore a) :
    g ∈ linkStab (p := p) (f := f) hinv a B :=
  ⟨hg, reflTransGen_frameLink_conj_of_coset hinv hB haB hg hxB hx1 hxa hcoset⟩

end Stabilizer

end CFSG.ClassicalInvolution.Balance.Bootstrap
