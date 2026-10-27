module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Transport
public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin

theorem exists_mem_normalizer_not_mem {X : Type*} [Group X] [Finite X] {F P : Subgroup X}
    (hP : IsPGroup 2 P) (hFP : F ≤ P) (hne : F ≠ P) :
    ∃ x ∈ P, x ∈ Subgroup.normalizer (F : Set X) ∧ x ∉ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : F.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    apply le_antisymm hFP
    intro y hy
    have : (⟨y, hy⟩ : P) ∈ F.subgroupOf P := by rw [h]; exact Subgroup.mem_top _
    exact this
  have hlt2 := Group.normalizerCondition_of_isNilpotent (G := P) (F.subgroupOf P) hlt
  obtain ⟨x, hx, hx2⟩ := IsConcreteLE.exists_of_lt hlt2
  refine ⟨x, x.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · intro hy
      have hyP : y ∈ P := hFP hy
      exact (hx ⟨y, hyP⟩).mp (show (⟨y, hyP⟩ : P) ∈ F.subgroupOf P from hy)
    · intro hy
      have hyP : (x : X) * y * (x : X)⁻¹ ∈ P := hFP hy
      have hyP' : y ∈ P := by
        have := P.mul_mem (P.mul_mem (P.inv_mem x.2) hyP) x.2
        simpa [mul_assoc] using this
      exact (hx ⟨y, hyP'⟩).mpr
        (show (⟨(x : X) * y * (x : X)⁻¹, hyP⟩ : P) ∈ F.subgroupOf P from hy)
  · intro hxF
    exact hx2 hxF

variable {X : Type} [Group X] [Finite X]

theorem eight_dvd_normalizer_of_sylow
    (hP8 : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → 8 ≤ Nat.card P) {F : Subgroup X}
    (hF : IsFourSubgroup F) : 8 ∣ Nat.card (Subgroup.normalizer (F : Set X)) := by
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF.2]; norm_num)
  obtain ⟨P, hFP, hP⟩ := exists_isSylowTwoOf_of_le (le_top : F ≤ ⊤) hF2
  have hP8' := hP8 P hP
  have hFne : F ≠ P := by
    intro h
    have h4 : Nat.card F = 4 := hF.2
    have : Nat.card F = Nat.card P := by rw [h]
    omega
  obtain ⟨x, hxP, hxN, hxF⟩ := exists_mem_normalizer_not_mem hP.isPGroup hFP hFne
  have hQ2 : IsPGroup 2 ↥(P ⊓ Subgroup.normalizer (F : Set X)) :=
    hP.isPGroup.to_le inf_le_left
  have hFQ : F ≤ P ⊓ Subgroup.normalizer (F : Set X) := le_inf hFP Subgroup.le_normalizer
  have hQne : F ≠ P ⊓ Subgroup.normalizer (F : Set X) := by
    intro h
    apply hxF
    rw [h]
    exact ⟨hxP, hxN⟩
  have hlt : Nat.card F < Nat.card ↥(P ⊓ Subgroup.normalizer (F : Set X)) :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hFQ) fun h =>
      hQne (Subgroup.eq_of_le_of_card_ge hFQ (le_of_eq h.symm))
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  rw [hF.2, hk] at hlt
  have hk3 : 3 ≤ k := by
    by_contra hlt'
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 8 ∣ Nat.card ↥(P ⊓ Subgroup.normalizer (F : Set X)) := by
    rw [hk]
    exact (pow_dvd_pow 2 hk3 : 2 ^ 3 ∣ 2 ^ k)
  exact h8.trans (Subgroup.card_dvd_of_le inf_le_right)

theorem four_normalizer_of_centralizer {F : Subgroup X} (hF : IsFourSubgroup F)
    (hcent : Subgroup.centralizer (F : Set X) = F)
    (h3 : 3 ∣ Nat.card (Subgroup.normalizer (F : Set X)))
    (h8 : 8 ∣ Nat.card (Subgroup.normalizer (F : Set X))) :
    Nonempty (↥(Subgroup.normalizer (F : Set X)) ≃* Equiv.Perm (Fin 4)) := by
  have hFN : F ≤ Subgroup.normalizer (F : Set X) := Subgroup.le_normalizer
  have hFnormal : (F.subgroupOf (Subgroup.normalizer (F : Set X))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).mpr le_rfl
  have hcard : Nat.card (F.subgroupOf (Subgroup.normalizer (F : Set X))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv]
    exact hF.2
  have hexp : ∀ x ∈ F.subgroupOf (Subgroup.normalizer (F : Set X)), x * x = 1 := by
    intro x hx
    apply Subtype.ext
    have := hF.1.2 (x : X) (Subgroup.mem_subgroupOf.mp hx)
    rw [pow_two] at this
    exact this
  have hC : ∀ g : ↥(Subgroup.normalizer (F : Set X)),
      (∀ f ∈ F.subgroupOf (Subgroup.normalizer (F : Set X)), g * f = f * g) →
        g ∈ F.subgroupOf (Subgroup.normalizer (F : Set X)) := by
    intro g hg
    have hgC : (g : X) ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := hg ⟨h, hFN hh⟩ (Subgroup.mem_subgroupOf.mpr hh)
      have h2 := congrArg Subtype.val this
      exact h2.symm
    rw [hcent] at hgC
    exact Subgroup.mem_subgroupOf.mpr hgC
  have h24 : 24 ∣ Nat.card ↥(Subgroup.normalizer (F : Set X)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 8) h3 h8
  exact perm_four_of_klein _ hcard hexp hC h24

structure SylowFourData (P₀ : Subgroup X) : Prop where
  sylow : IsSylowTwoOf P₀ ⊤
  shape : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P₀ ≃* DihedralGroup n)) ∨
    Nonempty (↥P₀ ≃* SemidihedralGroup 4)
  normalizer_le : Subgroup.normalizer (P₀ : Set X) ≤ P₀
  four : ∀ F : Subgroup X, F ≤ P₀ → IsFourSubgroup F →
    Subgroup.centralizer (F : Set X) = F ∧ ∃ w ∈ Subgroup.normalizer (F : Set X), orderOf w = 3

namespace SylowFourData

variable {P₀ : Subgroup X} (D : SylowFourData P₀)

include D

theorem exists_conj_eq {P : Subgroup X} (hP : IsSylowTwoOf P ⊤) :
    ∃ h : X, P = P₀.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨h, -, hh⟩ := D.sylow.exists_conj hP
  exact ⟨h, hh⟩

theorem sylow_shape : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ →
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup n)) ∨
      Nonempty (↥P ≃* SemidihedralGroup 4) := by
  intro P hP
  obtain ⟨h, rfl⟩ := D.exists_conj_eq hP
  let e : ↥P₀ ≃* ↥(P₀.map (MulAut.conj h).toMonoidHom) :=
    Subgroup.equivMapOfInjective P₀ _ (MulAut.conj h).injective
  rcases D.shape with ⟨n, hn, ⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨e.symm.trans e'⟩

theorem sylow_normalizer : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ →
    Subgroup.normalizer (P : Set X) ≤ P := by
  intro P hP n hn
  obtain ⟨h, rfl⟩ := D.exists_conj_eq hP
  have hn' : n ∈ (Subgroup.normalizer (P₀ : Set X)).map (MulAut.conj h).toMonoidHom := by
    rw [normalizer_map]
    exact hn
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn'
  exact Subgroup.mem_map_of_mem _ (D.normalizer_le hm)

theorem card_ge_eight : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → 8 ≤ Nat.card P := by
  intro P hP
  rcases D.sylow_shape P hP with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  · have h16 := CFSG.Semidihedral.card 4 (by norm_num)
    rw [Nat.card_congr e.toEquiv, h16]
    norm_num

theorem exists_conj_four {F : Subgroup X} (hF : IsFourSubgroup F) :
    ∃ h : X, F.map (MulAut.conj h⁻¹).toMonoidHom ≤ P₀ := by
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF.2]; norm_num)
  obtain ⟨P, hFP, hP⟩ := exists_isSylowTwoOf_of_le (le_top : F ≤ ⊤) hF2
  obtain ⟨h, rfl⟩ := D.exists_conj_eq hP
  refine ⟨h, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp (hFP hx)
  have : (MulAut.conj h⁻¹) x = p := by
    rw [← hpx]
    show h⁻¹ * (h * p * h⁻¹) * h⁻¹⁻¹ = p
    group
  rw [show (MulAut.conj h⁻¹).toMonoidHom x = p from this]
  exact hp

theorem centralizer_four {F : Subgroup X} (hF : IsFourSubgroup F) :
    Subgroup.centralizer (F : Set X) = F := by
  obtain ⟨h, hh⟩ := D.exists_conj_four hF
  have hF₀ : IsFourSubgroup (F.map (MulAut.conj h⁻¹).toMonoidHom) :=
    isFourSubgroup_map (MulAut.conj h⁻¹) hF
  obtain ⟨hc, -⟩ := D.four _ hh hF₀
  apply le_antisymm
  · intro g hg
    have hg' : (MulAut.conj h⁻¹) g ∈
        Subgroup.centralizer ((F.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨f, hf, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hg f hf
      show (MulAut.conj h⁻¹) f * (MulAut.conj h⁻¹) g = (MulAut.conj h⁻¹) g * (MulAut.conj h⁻¹) f
      rw [← map_mul, ← map_mul, this]
    rw [hc] at hg'
    obtain ⟨f, hf, hfg⟩ := Subgroup.mem_map.mp hg'
    have : f = g := (MulAut.conj h⁻¹).injective hfg
    rw [← this]
    exact hf
  · intro f hf
    have := hF.1.1
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact setLike_mul_comm hg hf

theorem four_normalizer {F : Subgroup X} (hF : IsFourSubgroup F) :
    Nonempty (↥(Subgroup.normalizer (F : Set X)) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨h, hh⟩ := D.exists_conj_four hF
  have hF₀ : IsFourSubgroup (F.map (MulAut.conj h⁻¹).toMonoidHom) :=
    isFourSubgroup_map (MulAut.conj h⁻¹) hF
  obtain ⟨-, w, hwN, hw3⟩ := D.four _ hh hF₀
  have hwN' : (MulAut.conj h) w ∈ Subgroup.normalizer (F : Set X) := by
    have hmap : (Subgroup.normalizer (F : Set X)).map (MulAut.conj h⁻¹).toMonoidHom =
        Subgroup.normalizer ((F.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup X) : Set X) :=
      normalizer_map (MulAut.conj h⁻¹) F
    rw [← hmap] at hwN
    obtain ⟨m, hm, hmw⟩ := Subgroup.mem_map.mp hwN
    have : m = (MulAut.conj h) w := by
      have h1 : h⁻¹ * m * h = w := by simpa [MulAut.conj_apply] using hmw
      rw [MulAut.conj_apply]
      calc m = h * (h⁻¹ * m * h) * h⁻¹ := by group
        _ = h * w * h⁻¹ := by rw [h1]
    rw [← this]
    exact hm
  have h3 : 3 ∣ Nat.card (Subgroup.normalizer (F : Set X)) := by
    have hord : orderOf (MulAut.conj h w) = 3 := by rw [MulEquiv.orderOf_eq]; exact hw3
    have := orderOf_dvd_natCard (⟨(MulAut.conj h) w, hwN'⟩ : Subgroup.normalizer (F : Set X))
    rw [Subgroup.orderOf_mk, hord] at this
    exact this
  exact four_normalizer_of_centralizer hF (D.centralizer_four hF) h3
    (eight_dvd_normalizer_of_sylow D.card_ge_eight hF)

end SylowFourData

end CFSG.QuasithinUnique.Unc25Small
