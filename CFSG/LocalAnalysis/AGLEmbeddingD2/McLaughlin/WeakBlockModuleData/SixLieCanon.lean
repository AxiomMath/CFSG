module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNode

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {Q : Type*} [Group Q]

theorem exists_line_of_threePrimeSub [Finite Q] {Lb P E N : Subgroup Q} (hPL : P ≤ Lb)
    (hEP : E ≤ P) (hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥Lb))) (hE3 : IsPGroup 3 E)
    (hNLb : N ≤ Subgroup.normalizer (Lb : Set Q)) (hNE : N ≤ Subgroup.normalizer (E : Set Q))
    (hNP : N ≤ Subgroup.normalizer (P : Set Q))
    (hcard : Nat.card
      (((E.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))) ⊓
        threePrimeSub ((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))) :
        Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) = 3) :
    ∃ W : Subgroup Q, W ≤ E ∧ Nat.card W = 3 ∧ N ≤ Subgroup.normalizer (W : Set Q) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  set E' : Subgroup ↥Lb := E.subgroupOf Lb with hE'
  set P' : Subgroup ↥Lb := P.subgroupOf Lb with hP'
  set J : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb) := P'.map ρ with hJ
  set E₁ : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb) := E'.map ρ ⊓ threePrimeSub J with hE₁
  have hEL : E ≤ Lb := hEP.trans hPL
  have hE'3 : IsPGroup 3 E' := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEL).symm
  have hinj : ∀ x ∈ E', ρ x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center ↥Lb := (QuotientGroup.eq_one_iff x).mp hx1
    obtain ⟨k, hk⟩ := hE'3 ⟨x, hx⟩
    have h3 : orderOf x ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (Subgroup.center ↥Lb) := Subgroup.orderOf_dvd_natCard _ hxc
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hZ3) h3 h2)
  set W' : Subgroup ↥Lb := E' ⊓ E₁.comap ρ with hW'
  have hWmap : W'.map ρ = E₁ := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_inf.mp hw).2
    · intro y hy
      obtain ⟨e, he, rfl⟩ := (Subgroup.mem_inf.mp hy).1
      exact ⟨e, ⟨he, hy⟩, rfl⟩
  have hcardW' : Nat.card W' = 3 := by
    rw [← hcard, ← hWmap]
    exact (card_map_eq_of_inj_on ρ fun x hx => hinj x (Subgroup.mem_inf.mp hx).1).symm
  have hE'map : E'.map Lb.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEL
  refine ⟨W'.map Lb.subtype, (Subgroup.map_mono inf_le_left).trans hE'map.le, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Lb.subtype_injective, hcardW']
  · intro n hn
    set ψ0 : Lb ≃* Lb := conjOnNormalizer Lb n (hNLb hn) with hψ0
    have hcen : (Subgroup.center Lb).map ψ0.toMonoidHom = Subgroup.center Lb := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' := Subgroup.mem_center_iff.mp hw
        refine Subgroup.mem_center_iff.mpr fun a => ?_
        have := hw' (ψ0.symm a)
        have h2 := congrArg ψ0 this
        simpa using h2
      · intro hz
        have hz' := Subgroup.mem_center_iff.mp hz
        refine ⟨ψ0.symm z, Subgroup.mem_center_iff.mpr fun a => ?_, by simp⟩
        have := hz' (ψ0 a)
        have h2 := congrArg ψ0.symm this
        simpa using h2
    set ψ1 : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* (↥Lb ⧸ Subgroup.center ↥Lb) :=
      QuotientGroup.congr (Subgroup.center Lb) (Subgroup.center Lb) ψ0 hcen with hψ1
    have hψ1ρ : ∀ a : ↥Lb, ψ1 (ρ a) = ρ (ψ0 a) := fun a => rfl
    have hψP : ∀ p ∈ P', ψ0 p ∈ P' := fun p hp =>
      Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hNP hn) p).mp (Subgroup.mem_subgroupOf.mp hp))
    have hψEm : ∀ p ∈ E', ψ0 p ∈ E' := fun p hp =>
      Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hNE hn) p).mp (Subgroup.mem_subgroupOf.mp hp))
    have hψJ : ∀ g ∈ J, ψ1 g ∈ J := by
      rintro _ ⟨p, hp, rfl⟩
      rw [hψ1ρ]
      exact ⟨ψ0 p, hψP p hp, rfl⟩
    have hψE : ∀ g ∈ E'.map ρ, ψ1 g ∈ E'.map ρ := by
      rintro _ ⟨p, hp, rfl⟩
      rw [hψ1ρ]
      exact ⟨ψ0 p, hψEm p hp, rfl⟩
    have hψO : ∀ g ∈ threePrimeSub J, ψ1 g ∈ threePrimeSub J := fun g hg =>
      map_threePrimeSub_le ψ1 hψJ ⟨g, hg, rfl⟩
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨w, hw, rfl⟩
    change n * (w : Q) * n⁻¹ ∈ ((W'.map Lb.subtype : Subgroup Q) : Set Q)
    have hw1 := (Subgroup.mem_inf.mp hw).1
    have hw2 : ρ w ∈ E₁ := (Subgroup.mem_inf.mp hw).2
    refine ⟨ψ0 w, Subgroup.mem_inf.mpr ⟨hψEm w hw1, ?_⟩, rfl⟩
    rw [Subgroup.mem_comap, ← hψ1ρ]
    exact ⟨hψE _ hw2.1, hψO _ hw2.2⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
