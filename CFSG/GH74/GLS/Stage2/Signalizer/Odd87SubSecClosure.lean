module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSecG

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {G : Type} [Group G] {z : G}

theorem subsec_exists_hom {B : Type} [Group B] {b : B} (h : SecOfG G z B b) :
    ∃ (H₀ : Subgroup G) (hz : z ∈ H₀) (φ : ↥H₀ →* B),
      H₀ ≠ ⊤ ∧ Function.Surjective φ ∧ Odd (Nat.card φ.ker) ∧ φ ⟨z, hz⟩ = b := by
  obtain ⟨H₀, H₁, hn, hz, hne, hodd, e, he⟩ := h
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' H₁)).ker = H₁ := by
    ext x
    simp
  refine ⟨H₀, hz, e.toMonoidHom.comp (QuotientGroup.mk' H₁), hne, ?_, ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective H₁)
  · rw [hker]
    exact hodd
  · exact he

theorem subsec_of_hom {B : Type} [Group B] {b : B} {H₀ : Subgroup G} (hz : z ∈ H₀) (hne : H₀ ≠ ⊤)
    (φ : ↥H₀ →* B) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (hb : φ ⟨z, hz⟩ = b) : SecOfG G z B b :=
  ⟨H₀, φ.ker, MonoidHom.normal_ker φ, hz, hne, hodd,
    QuotientGroup.quotientKerEquivOfSurjective φ hφ, hb⟩

theorem subsec_card_ker_comp {A A' C : Type} [Group A] [Group A'] [Group C] (e : A ≃* A')
    (f : A →* C) : Nat.card (f.comp e.symm.toMonoidHom).ker = Nat.card f.ker :=
  Nat.card_congr (e.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl)

theorem subsec_subgroupComap_eq_one {A C : Type} [Group A] [Group C] (f : A →* C) (Y : Subgroup C)
    (x : ↥(Y.comap f)) : (f.subgroupComap Y) x = 1 ↔ f x.1 = 1 := by
  rw [← Subtype.coe_inj]
  exact Iff.rfl

theorem subsec_card_ker_subgroupComap {A C : Type} [Group A] [Group C] (f : A →* C)
    (Y : Subgroup C) : Nat.card (f.subgroupComap Y).ker = Nat.card f.ker :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, (subsec_subgroupComap_eq_one f Y x.1).1 x.2⟩
      invFun := fun y => ⟨⟨y.1, by simp [Subgroup.mem_comap, MonoidHom.mem_ker.1 y.2]⟩,
        (subsec_subgroupComap_eq_one f Y _).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem SecOfG.sub {B : Type} [Group B] {b : B} (h : SecOfG G z B b) (Y : Subgroup B) (hb : b ∈ Y) :
    SecOfG G z ↥Y ⟨b, hb⟩ := by
  obtain ⟨H₀, hz, φ, hne, hφ, hodd, hzb⟩ := subsec_exists_hom h
  have hzY : (⟨z, hz⟩ : ↥H₀) ∈ Y.comap φ := by
    rw [Subgroup.mem_comap, hzb]
    exact hb
  have hz' : z ∈ (Y.comap φ).map H₀.subtype := ⟨⟨z, hz⟩, hzY, rfl⟩
  have hne' : (Y.comap φ).map H₀.subtype ≠ ⊤ := by
    intro htop
    apply hne
    have hle : (Y.comap φ).map H₀.subtype ≤ H₀ := Subgroup.map_subtype_le _
    rw [htop] at hle
    exact top_le_iff.mp hle
  let ι : ↥(Y.comap φ) ≃* ↥((Y.comap φ).map H₀.subtype) :=
    Subgroup.equivMapOfInjective _ H₀.subtype H₀.subtype_injective
  refine subsec_of_hom (H₀ := (Y.comap φ).map H₀.subtype) hz' hne'
    ((φ.subgroupComap Y).comp ι.symm.toMonoidHom) ?_ ?_ ?_
  · exact (φ.subgroupComap_surjective Y hφ).comp ι.symm.surjective
  · rw [subsec_card_ker_comp ι (φ.subgroupComap Y), subsec_card_ker_subgroupComap]
    exact hodd
  · have hι : ι.symm ⟨z, hz'⟩ = ⟨⟨z, hz⟩, hzY⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    show (φ.subgroupComap Y) (ι.symm ⟨z, hz'⟩) = ⟨b, hb⟩
    rw [hι]
    exact Subtype.ext hzb

theorem SecOfG.quot {B : Type} [Group B] {b : B} (h : SecOfG G z B b) (N : Subgroup B) [N.Normal]
    (hN : Odd (Nat.card ↥N)) : SecOfG G z (B ⧸ N) (QuotientGroup.mk b) := by
  obtain ⟨H₀, hz, φ, hne, hφ, hodd, hzb⟩ := subsec_exists_hom h
  have hker : ((QuotientGroup.mk' N).comp φ).ker = N.comap φ := by
    ext x
    simp [QuotientGroup.eq_one_iff]
  refine subsec_of_hom hz hne ((QuotientGroup.mk' N).comp φ)
    ((QuotientGroup.mk'_surjective N).comp hφ) ?_ ?_
  · rw [hker, ← Subgroup.card_ker_mul_card_of_surjective (φ.subgroupComap_surjective N hφ),
      subsec_card_ker_subgroupComap]
    exact Nat.odd_mul.mpr ⟨hodd, hN⟩
  · show QuotientGroup.mk' N (φ ⟨z, hz⟩) = QuotientGroup.mk b
    rw [hzb]
    rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
