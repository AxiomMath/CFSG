module

public import CFSG.CharacterTheory.Wreathed.BrauerWongModel

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u v

theorem pPrimeCore_isComplement'_of_le_center {X : Type v} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (P : Sylow p X) (hP : (P : Subgroup X) ≤ Subgroup.center X) :
    (CFSG.pPrimeCore p X).IsComplement' (P : Subgroup X) := by
  have hN : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_center_iff.mp (hP hh) g).symm
  have hK := MonoidHom.ker_transferSylow_isComplement' P hN
  set K := (MonoidHom.transferSylow P hN).ker
  have hKcop : Nat.Coprime p (Nat.card K) :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (MonoidHom.not_dvd_card_ker_transferSylow P hN)
  have hKle : K ≤ CFSG.pPrimeCore p X := le_sSup ⟨MonoidHom.normal_ker _, hKcop⟩
  have hdisj : CFSG.pPrimeCore p X ⊓ (P : Subgroup X) = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.symm CFSG.pPrimeCore_coprime_card)
  have heq : CFSG.pPrimeCore p X = K := by
    refine le_antisymm ?_ hKle
    intro x hx
    obtain ⟨⟨k, q⟩, hkq⟩ := hK.2 x
    change (k : X) * q = x at hkq
    have hq : (q : X) ∈ CFSG.pPrimeCore p X ⊓ (P : Subgroup X) := by
      refine ⟨?_, q.property⟩
      have : (q : X) = (k : X)⁻¹ * x := by rw [← hkq]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKle k.property)) hx
    rw [hdisj, Subgroup.mem_bot] at hq
    rw [← hkq, hq, mul_one]
    exact k.property
  rw [heq]
  exact hK

variable {G : Type u} [Group G]

theorem center_map_eq_modelCenter (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype = modelCenter S e := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  rw [← Subgroup.map_center_eq e.symm, Subgroup.map_map, hstr.center]
  rfl

theorem sylow_inf_centralizer (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) = modelCenter S e := by
  rw [← center_map_eq_modelCenter n hn S e]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hxS, hxC⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.property)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    change (y : G) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)

theorem modelCenter_le_centralizer (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    modelCenter S e ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  rw [← sylow_inf_centralizer n hn S e]
  exact inf_le_right

theorem exists_sylow_centralizer_eq_center [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    ∃ P : Sylow 2 (Subgroup.centralizer ((S : Subgroup G) : Set G)),
      (P : Subgroup _) = (modelCenter S e).subgroupOf
        (Subgroup.centralizer ((S : Subgroup G) : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ((S : Subgroup G) : Set G)
  have hZp : IsPGroup 2 ((modelCenter S e).subgroupOf C) := by
    have h : IsPGroup 2 (modelCenter S e) := S.isPGroup'.to_le (modelCenter_le_sylow S e)
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe (modelCenter_le_centralizer n hn S e)).symm
  obtain ⟨P, hP⟩ := hZp.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  let Q : Subgroup G := (P : Subgroup C).map C.subtype
  have hQp : IsPGroup 2 Q := P.isPGroup'.map C.subtype
  have hQC : Q ≤ C := Subgroup.map_subtype_le _
  have hQN : Q ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    hQC.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 2 ↥(Q ⊔ (S : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' hQp S.isPGroup' hQN
  have hQS : Q ≤ (S : Subgroup G) := by
    have := S.is_maximal' hsup le_sup_right
    rw [← this]
    exact le_sup_left
  intro x hx
  change (x : G) ∈ modelCenter S e
  rw [← sylow_inf_centralizer n hn S e]
  exact ⟨hQS ⟨x, hx, rfl⟩, x.property⟩

@[expose] def sylowCentralizerCore (S : Sylow 2 G) : Subgroup G :=
  (CFSG.pPrimeCore 2 (Subgroup.centralizer ((S : Subgroup G) : Set G))).map
    (Subgroup.centralizer ((S : Subgroup G) : Set G)).subtype

theorem sylowCentralizerCore_le (S : Sylow 2 G) :
    sylowCentralizerCore S ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
  Subgroup.map_subtype_le _

theorem sylowCentralizerCore_coprime [Finite G] (S : Sylow 2 G) :
    Nat.Coprime 2 (Nat.card (sylowCentralizerCore S)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sylowCentralizerCore, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.pPrimeCore_coprime_card

theorem sylow_inf_sylowCentralizerCore [Finite G] (S : Sylow 2 G) :
    (S : Subgroup G) ⊓ sylowCentralizerCore S = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_left _ (sylowCentralizerCore_coprime S)

theorem centralizer_eq_center_prod_core [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    ∃ φ : ↥(modelCenter S e) × ↥(sylowCentralizerCore S) ≃*
      ↥(Subgroup.centralizer ((S : Subgroup G) : Set G)),
      ∀ x y, (φ (x, y) : G) = x * y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ((S : Subgroup G) : Set G)
  obtain ⟨P, hP⟩ := exists_sylow_centralizer_eq_center n hn S e
  have hPc : (P : Subgroup C) ≤ Subgroup.center C := by
    intro x hx
    rw [hP] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxS : (x : G) ∈ (S : Subgroup G) := modelCenter_le_sylow S e hx
    exact (Subgroup.mem_centralizer_iff.mp y.property _ hxS).symm
  have hcomp := (pPrimeCore_isComplement'_of_le_center P hPc).symm
  let f : ↥(modelCenter S e) →* C :=
    { toFun := fun z => ⟨z, modelCenter_le_centralizer n hn S e z.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g : ↥(sylowCentralizerCore S) →* C :=
    { toFun := fun x => ⟨x, sylowCentralizerCore_le S x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcomm : ∀ z x, Commute (f z) (g x) := by
    intro z x
    apply Subtype.ext
    have hzS : (z : G) ∈ (S : Subgroup G) := modelCenter_le_sylow S e z.property
    exact Subgroup.mem_centralizer_iff.mp (sylowCentralizerCore_le S x.property) _ hzS
  let F := f.noncommCoprod g hcomm
  have hbij : Function.Bijective F := by
    have hfP : ∀ z, f z ∈ (P : Subgroup C) := fun z => by
      rw [hP]; exact z.property
    have hgE : ∀ x, g x ∈ CFSG.pPrimeCore 2 C := fun x => by
      obtain ⟨y, hy, hyx⟩ := x.property
      have : g x = y := Subtype.ext hyx.symm
      rw [this]; exact hy
    constructor
    · rintro ⟨z₁, x₁⟩ ⟨z₂, x₂⟩ h
      have h' := hcomp.1 (a₁ := (⟨f z₁, hfP z₁⟩, ⟨g x₁, hgE x₁⟩))
        (a₂ := (⟨f z₂, hfP z₂⟩, ⟨g x₂, hgE x₂⟩)) h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
      obtain ⟨h1, h2⟩ := h'
      have h1' : (z₁ : G) = z₂ := congrArg (fun c : C => (c : G)) h1
      have h2' : (x₁ : G) = x₂ := congrArg (fun c : C => (c : G)) h2
      exact Prod.ext (Subtype.ext h1') (Subtype.ext h2')
    · intro c
      obtain ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, hpq⟩ := hcomp.2 c
      change p * q = c at hpq
      rw [hP] at hp
      refine ⟨(⟨p, hp⟩, ⟨q, q, hq, rfl⟩), ?_⟩
      rw [← hpq]
      rfl
  refine ⟨MulEquiv.ofBijective F hbij, ?_⟩
  intro x y
  rfl

theorem exists_sylow_mul_mem_centralizer [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (g : G) (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ∃ s ∈ (S : Subgroup G), s⁻¹ * g ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  have haut : IsPGroup 2 (MulAut (S : Subgroup G)) :=
    (wreath_automorphism_isPGroup n hn).of_equiv (MulAut.congr e).symm
  obtain ⟨q, hq, hqg⟩ := CFSG.GorensteinWalter.hom_to_pGroup_image_on_sylow haut
    (S : Subgroup G).normalizerMonoidHom (S.subtype (Subgroup.le_normalizer)) ⟨g, hg⟩
  rw [Sylow.coe_subtype] at hq
  refine ⟨q, hq, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := DFunLike.congr_fun hqg ⟨x, hx⟩
  have h' := congrArg Subtype.val h
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
  change (q : G) * x * (q : G)⁻¹ = g * x * g⁻¹ at h'
  calc
    x * ((q : G)⁻¹ * g) = (q : G)⁻¹ * ((q : G) * x * (q : G)⁻¹) * g := by group
    _ = (q : G)⁻¹ * (g * x * g⁻¹) * g := by rw [h']
    _ = (q : G)⁻¹ * g * x := by group

theorem normalizer_eq_sylow_prod_core [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    ∃ ψ : ↥(S : Subgroup G) × ↥(sylowCentralizerCore S) ≃*
      ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)),
      ∀ x y, (ψ (x, y) : G) = x * y := by
  set C := Subgroup.centralizer ((S : Subgroup G) : Set G)
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let f : ↥(S : Subgroup G) →* N :=
    { toFun := fun s => ⟨s, Subgroup.le_normalizer s.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g : ↥(sylowCentralizerCore S) →* N :=
    { toFun := fun x => ⟨x, Subgroup.centralizer_le_normalizer _
        (sylowCentralizerCore_le S x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcomm : ∀ s x, Commute (f s) (g x) := by
    intro s x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (sylowCentralizerCore_le S x.property) _
      s.property
  let F := f.noncommCoprod g hcomm
  obtain ⟨φ, hφ⟩ := centralizer_eq_center_prod_core n hn S e
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨s₁, x₁⟩ ⟨s₂, x₂⟩ h
      have h' : (s₁ : G) * x₁ = s₂ * x₂ := congrArg Subtype.val h
      have hmem : (s₂ : G)⁻¹ * s₁ ∈ (S : Subgroup G) ⊓ sylowCentralizerCore S := by
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ s₂.property) s₁.property, ?_⟩
        have : (s₂ : G)⁻¹ * s₁ = x₂ * (x₁ : G)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h']
          group
        rw [this]
        exact Subgroup.mul_mem _ x₂.property (Subgroup.inv_mem _ x₁.property)
      rw [sylow_inf_sylowCentralizerCore, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hs : s₁ = s₂ := Subtype.ext hmem.symm
      subst hs
      have hx : x₁ = x₂ := Subtype.ext (mul_left_cancel h')
      rw [hx]
    · intro c
      obtain ⟨s, hs, hsc⟩ := exists_sylow_mul_mem_centralizer n hn S e c c.property
      obtain ⟨⟨z, x⟩, hzx⟩ := φ.surjective ⟨_, hsc⟩
      have hzx' : (z : G) * x = s⁻¹ * c := by
        rw [← hφ]
        exact congrArg Subtype.val hzx
      have hsz : s * z ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ hs (modelCenter_le_sylow S e z.property)
      refine ⟨(⟨s * z, hsz⟩, x), Subtype.ext ?_⟩
      change s * z * x = c
      rw [mul_assoc, hzx']
      group
  refine ⟨MulEquiv.ofBijective F hbij, ?_⟩
  intro x y
  rfl

end CFSG.Wreathed.BrauerWong
