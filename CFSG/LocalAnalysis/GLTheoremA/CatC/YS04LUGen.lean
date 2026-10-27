module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

abbrev LUGood {T : Type} [Group T] (p : ℕ) (D : Subgroup (MulAut T)) : Prop :=
  ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup T, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
    (∃ a b : ↥L, a * b ≠ b * a) ∧ p ∣ Nat.card L ∧
    ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

abbrev LUCore {T : Type} [Group T] (p : ℕ) (f : MulAut T) (L : Subgroup T) : Prop :=
  L ≤ fixSub f ∧ IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧ p ∣ Nat.card L ∧
    ∀ g ∈ fixSub f, ∀ x ∈ L, g * x * g⁻¹ ∈ L

theorem mem_fixSub_iff {T : Type} [Group T] (y : MulAut T) (g : T) :
    g ∈ fixSub y ↔ y g = g := Iff.rfl

theorem isSimpleGroup_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    [IsSimpleGroup G] : IsSimpleGroup H :=
  e.symm.isSimpleGroup

theorem nonabelian_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ∃ a b : G, a * b ≠ b * a) : ∃ a b : H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab ?_⟩
  apply e.injective
  rw [map_mul, map_mul]
  exact h'

theorem LUGood_of_conj {T : Type} [Group T] {p : ℕ} {D : Subgroup (MulAut T)} {f β x : MulAut T}
    {L : Subgroup T} (hL : LUCore p f L) (hxD : x ∈ D) (hx1 : x ≠ 1) (hx : x = β * f * β⁻¹) :
    LUGood p D := by
  obtain ⟨hLf, hs, hna, hp, hnorm⟩ := hL
  haveI := hs
  have hxg : ∀ g : T, x g = β (f (β.symm g)) := fun g => by rw [hx]; rfl
  have hfix : ∀ g : T, x g = g ↔ f (β.symm g) = β.symm g := fun g => by
    rw [hxg]
    constructor
    · intro h
      have h' := congrArg β.symm h
      simpa using h'
    · intro h
      rw [h]
      simp
  have hβi : Function.Injective β.toMonoidHom := β.injective
  let e : ↥L ≃* ↥(L.map β.toMonoidHom) := L.equivMapOfInjective β.toMonoidHom hβi
  refine ⟨x, hxD, hx1, L.map β.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨ℓ, hℓ, rfl⟩
    show x (β ℓ) = β ℓ
    rw [hfix, MulEquiv.symm_apply_apply]
    exact (mem_fixSub_iff f ℓ).1 (hLf hℓ)
  · exact e.symm.isSimpleGroup
  · exact nonabelian_of_mulEquiv e hna
  · rw [Subgroup.card_map_of_injective hβi]
    exact hp
  · intro g hg u hu
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.1 hu
    have hgf : f (β.symm g) = β.symm g := (hfix g).1 ((mem_fixSub_iff x g).1 hg)
    have hc := hnorm (β.symm g) ((mem_fixSub_iff f _).2 hgf) ℓ hℓ
    refine Subgroup.mem_map.2 ⟨_, hc, ?_⟩
    simp [map_mul, map_inv]

theorem LUGood_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) {p : ℕ}
    {D : Subgroup (MulAut S)} (h : LUGood p (D.map (MulAut.congr e).toMonoidHom)) :
    LUGood p D := by
  obtain ⟨y', hy', hy'1, L', hL'f, hL's, hL'na, hL'p, hL'n⟩ := h
  haveI := hL's
  obtain ⟨y, hyD, rfl⟩ := Subgroup.mem_map.1 hy'
  have hcg : ∀ (α : MulAut S) (g : S), (MulAut.congr e α) (e g) = e (α g) := fun α g => by
    simp [MulAut.congr_apply]
  have hcg' : ∀ (α : MulAut S) (t : T), (MulAut.congr e α) t = e (α (e.symm t)) :=
    fun α t => by simp [MulAut.congr_apply]
  have hei : Function.Injective (e.symm.toMonoidHom) := e.symm.injective
  let e' : ↥L' ≃* ↥(L'.map e.symm.toMonoidHom) := L'.equivMapOfInjective e.symm.toMonoidHom hei
  refine ⟨y, hyD, fun h1 => hy'1 (by rw [h1, map_one]), L'.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨ℓ, hℓ, rfl⟩
    have h1 : e (y (e.symm ℓ)) = ℓ := by
      have h0 : (MulAut.congr e y) ℓ = ℓ := (mem_fixSub_iff _ _).1 (hL'f hℓ)
      rw [hcg'] at h0
      exact h0
    show y (e.symm ℓ) = e.symm ℓ
    apply e.injective
    rw [h1, e.apply_symm_apply]
  · exact e'.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hL'na
    refine ⟨e' a, e' b, fun h' => hab ?_⟩
    apply e'.injective
    rw [map_mul, map_mul]
    exact h'
  · rw [← Nat.card_congr e'.toEquiv]
    exact hL'p
  · intro g hg u hu
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.1 hu
    have hgy : MulAut.congr e y (e g) = e g := by
      rw [hcg, (mem_fixSub_iff y g).1 hg]
    have hc := hL'n (e g) ((mem_fixSub_iff _ _).2 hgy) ℓ hℓ
    refine Subgroup.mem_map.2 ⟨_, hc, ?_⟩
    simp [map_mul, map_inv]

theorem map_congr_inf_inner {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (D : Subgroup (MulAut S)) (hD : D ⊓ inner S = ⊥) :
    D.map (MulAut.congr e).toMonoidHom ⊓ inner T = ⊥ := by
  rw [eq_bot_iff]
  rintro x' hx'
  obtain ⟨hmap, hin⟩ := Subgroup.mem_inf.1 hx'
  obtain ⟨x, hxD, rfl⟩ := Subgroup.mem_map.1 hmap
  obtain ⟨t, ht⟩ := (MonoidHom.mem_range).1 hin
  have hx : x ∈ inner S := by
    refine (MonoidHom.mem_range).2 ⟨e.symm t, ?_⟩
    apply (MulAut.congr e).injective
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.congr_conj, e.apply_symm_apply, ht]
    rfl
  have hx1 : x = 1 := Subgroup.mem_bot.1 (hD ▸ Subgroup.mem_inf.2 ⟨hxD, hx⟩)
  rw [hx1, map_one, Subgroup.mem_bot]

end CFSG.LocalAnalysis.GLTheoremA
