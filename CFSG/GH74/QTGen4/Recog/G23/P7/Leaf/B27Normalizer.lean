module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27NormalizerA
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.B27N

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

section Part2

variable {a b t z : G} {H H₁ H₂ M₁ M₂ Pb : Subgroup G}

theorem card_cent_Pb_conj (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {g x : G}
    (hg : g ∈ Subgroup.normalizer (Pb : Set G)) :
    Nat.card ↥(Pb ⊓ Subgroup.centralizer {g * x * g⁻¹}) =
      Nat.card ↥(Pb ⊓ Subgroup.centralizer {x}) := by
  have hgi : g⁻¹ ∈ Subgroup.normalizer (Pb : Set G) := Subgroup.inv_mem _ hg
  have hmap : (Pb ⊓ Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom =
      Pb ⊓ Subgroup.centralizer {g * x * g⁻¹} := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨huPb, huc⟩ := Subgroup.mem_inf.mp hu
      have hux : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp huc
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hg u).mp huPb
      · rw [Subgroup.mem_centralizer_singleton_iff]
        show g * u * g⁻¹ * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * u * g⁻¹)
        calc g * u * g⁻¹ * (g * x * g⁻¹) = g * (u * x) * g⁻¹ := by group
          _ = g * (x * u) * g⁻¹ := by rw [hux]
          _ = (g * x * g⁻¹) * (g * u * g⁻¹) := by group
    · intro hy
      obtain ⟨hyPb, hyc⟩ := Subgroup.mem_inf.mp hy
      have hyc' : y * (g * x * g⁻¹) = (g * x * g⁻¹) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyc
      refine ⟨g⁻¹ * y * g⁻¹⁻¹, ?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp hgi y).mp hyPb
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc g⁻¹ * y * g⁻¹⁻¹ * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyc']
            _ = x * (g⁻¹ * y * g⁻¹⁻¹) := by group
      · show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
        group
  rw [← hmap, Subgroup.card_map_of_injective]
  exact (MulAut.conj g).injective

theorem Core.E_elem (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {x : G} (hx : x ∈ Subgroup.closure ({t, z} : Set G)) :
    x = 1 ∨ x = z ∨ x = t' ∨ x = t' * z := by
  have hz2 : z * z = 1 := C.z_mul
  have ht'2 : t' * t' = 1 := C.t'_mul ht'
  have hcomm : z * t' = t' * z := (C.t'_z ht').symm
  have e_z_tz : z * (t' * z) = t' := by
    calc z * (t' * z) = (z * t') * z := by group
      _ = (t' * z) * z := by rw [hcomm]
      _ = t' := by rw [mul_assoc, hz2, mul_one]
  have e_t_tz : t' * (t' * z) = z := by
    calc t' * (t' * z) = (t' * t') * z := by group
      _ = z := by rw [ht'2, one_mul]
  have e_tz_z : t' * z * z = t' := by rw [mul_assoc, hz2, mul_one]
  have e_tz_t : t' * z * t' = z := by
    calc t' * z * t' = t' * (z * t') := by group
      _ = t' * (t' * z) := by rw [hcomm]
      _ = z := e_t_tz
  have e_tz_tz : t' * z * (t' * z) = 1 := by
    calc t' * z * (t' * z) = (t' * z * t') * z := by group
      _ = z * z := by rw [e_tz_t]
      _ = 1 := hz2
  have hmul : ∀ x ∈ ({1, z, t', t' * z} : Set G), ∀ y ∈ ({1, z, t', t' * z} : Set G),
      x * y ∈ ({1, z, t', t' * z} : Set G) := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inl (one_mul z))
    · exact Or.inr (Or.inr (Or.inl (one_mul t')))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one z))
    · exact Or.inl hz2
    · exact Or.inr (Or.inr (Or.inr hcomm))
    · exact Or.inr (Or.inr (Or.inl e_z_tz))
    · exact Or.inr (Or.inr (Or.inl (mul_one t')))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl ht'2
    · exact Or.inr (Or.inl e_t_tz)
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl e_tz_z))
    · exact Or.inr (Or.inl e_tz_t)
    · exact Or.inl e_tz_tz
  have hgen : t ∈ ({1, z, t', t' * z} : Set G) := by
    rcases ht' with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inl h.symm))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inr (by rw [h, mul_assoc, C.z_mul, mul_one])))
  have hzS : z ∈ ({1, z, t', t' * z} : Set G) := by
    simp
  have hS : x ∈ ({1, z, t', t' * z} : Set G) := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact hgen
      · rw [hx]; exact hzS
    | one => simp
    | mul x y _ _ ihx ihy => exact hmul x ihx y ihy
    | inv x _ ih =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
      rcases ih with h | h | h | h
      · rw [h]; simp
      · rw [h]; exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hz2))
      · rw [h]; exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ht'2)))
      · rw [h]; exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right e_tz_tz)))
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hS

theorem card_cent_Pb_z (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Nat.card ↥(Pb ⊓ Subgroup.centralizer {z}) = 9 := by
  rw [C.Pb_inf_z, C.card_P]

theorem card_cent_Pb_t' [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) :
    Nat.card ↥(Pb ⊓ Subgroup.centralizer {t'}) = 3 := by
  rw [C.Pb_inf_cent_t' ht' hW, C.card_wOne]

theorem card_cent_Pb_t'z [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) :
    Nat.card ↥(Pb ⊓ Subgroup.centralizer {t' * z}) = 1 := by
  rw [C.Pb_inf_cent_t'z ht' hW, Subgroup.card_bot]

theorem Core.rigid_z [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {g : G}
    (hg : g ∈ Subgroup.normalizer (Pb : Set G)) (hy : g * z * g⁻¹ = z ∨ g * z * g⁻¹ = t' ∨
      g * z * g⁻¹ = t' * z) : g * z * g⁻¹ = z := by
  have hc := card_cent_Pb_conj C (x := z) hg
  rw [card_cent_Pb_z C] at hc
  rcases hy with h | h | h
  · exact h
  · rw [h, card_cent_Pb_t' C ht' hW] at hc; omega
  · rw [h, card_cent_Pb_t'z C ht' hW] at hc; omega

theorem Core.rigid_t' [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {g : G}
    (hg : g ∈ Subgroup.normalizer (Pb : Set G)) (hy : g * t' * g⁻¹ = z ∨ g * t' * g⁻¹ = t' ∨
      g * t' * g⁻¹ = t' * z) : g * t' * g⁻¹ = t' := by
  have hc := card_cent_Pb_conj C (x := t') hg
  rw [card_cent_Pb_t' C ht' hW] at hc
  rcases hy with h | h | h
  · rw [h, card_cent_Pb_z C] at hc; omega
  · exact h
  · rw [h, card_cent_Pb_t'z C ht' hW] at hc; omega

theorem Core.cent_of_normE [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {g : G}
    (hg : g ∈ Subgroup.normalizer (Pb : Set G))
    (hgz : g * z * g⁻¹ ∈ Subgroup.closure ({t, z} : Set G))
    (hgt : g * t' * g⁻¹ ∈ Subgroup.closure ({t, z} : Set G)) :
    g * z = z * g ∧ g * t' = t' * g := by
  have hz1 : z ≠ 1 := C.z_ne
  have ht1 : t' ≠ 1 := C.t'_ne ht'
  constructor
  · have hzz : g * z * g⁻¹ = z := by
      rcases C.E_elem ht' hgz with h | h | h | h
      · exfalso
        apply hz1
        have : z = g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ := by group
        rw [this, h]; group
      · exact C.rigid_z ht' hW hg (Or.inl h)
      · exact C.rigid_z ht' hW hg (Or.inr (Or.inl h))
      · exact C.rigid_z ht' hW hg (Or.inr (Or.inr h))
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hzz]
  · have htt : g * t' * g⁻¹ = t' := by
      rcases C.E_elem ht' hgt with h | h | h | h
      · exfalso
        apply ht1
        have : t' = g⁻¹ * (g * t' * g⁻¹) * g⁻¹⁻¹ := by group
        rw [this, h]; group
      · exact C.rigid_t' ht' hW hg (Or.inl h)
      · exact C.rigid_t' ht' hW hg (Or.inr (Or.inl h))
      · exact C.rigid_t' ht' hW hg (Or.inr (Or.inr h))
    calc g * t' = (g * t' * g⁻¹) * g := by group
      _ = t' * g := by rw [htt]

theorem Core.E_isPGroup (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) :
    IsPGroup 2 ↥(Subgroup.closure ({t, z} : Set G)) := by
  intro x
  refine ⟨1, ?_⟩
  have hx2 : (x : G) ^ 2 = 1 := by
    have hz2 : z * z = 1 := C.z_mul
    have ht'2 : t' * t' = 1 := C.t'_mul ht'
    rcases C.E_elem ht' x.2 with h | h | h | h
    · rw [h]; simp
    · rw [h, sq, hz2]
    · rw [h, sq, ht'2]
    · rw [h, sq]
      have hcomm : z * t' = t' * z := (C.t'_z ht').symm
      calc t' * z * (t' * z) = (t' * z * t') * z := by group
        _ = (t' * z * t') * z := rfl
        _ = (t' * (z * t')) * z := by group
        _ = (t' * (t' * z)) * z := by rw [hcomm]
        _ = (t' * t') * (z * z) := by group
        _ = 1 := by rw [C.t'_mul ht', C.z_mul, one_mul]
  rw [pow_one]
  exact Subtype.ext (by simpa using hx2)

theorem Core.E_norm_P (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {e' : G}
    (he' : e' ∈ Subgroup.closure ({t, z} : Set G)) {p : G}
    (hp : p ∈ Subgroup.closure ({a, b} : Set G)) :
    e' * p * e'⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
  have hN : e' ∈ Subgroup.normalizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
    rw [C.norm_P]; exact Subgroup.mem_sup_right he'
  exact (Subgroup.mem_normalizer_iff.mp hN p).mp hp

theorem pow_coprime_eq_one {x : G} {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1)
    (hmn : Nat.Coprime m n) : x = 1 := by
  have h : x ^ (Nat.gcd m n) = 1 := pow_gcd_eq_one.mpr ⟨hm, hn⟩
  rw [Nat.Coprime.gcd_eq_one hmn, pow_one] at h
  exact h

theorem Core.E_maximal [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w)
    {R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (Pb : Set G))
    (hR2 : IsPGroup 2 ↥R) (hER : Subgroup.closure ({t, z} : Set G) ≤ R) :
    R = Subgroup.closure ({t, z} : Set G) := by
  by_contra hne
  have hneTop : (Subgroup.closure ({t, z} : Set G)).subgroupOf R ≠ ⊤ := by
    intro h
    apply hne
    have hRE : R ≤ Subgroup.closure ({t, z} : Set G) := by
      intro x hx
      have hm : (⟨x, hx⟩ : ↥R) ∈ (Subgroup.closure ({t, z} : Set G)).subgroupOf R := by
        rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hm
    exact le_antisymm hRE hER
  have hlt : (Subgroup.closure ({t, z} : Set G)).subgroupOf R < ⊤ := lt_top_iff_ne_top.mpr hneTop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  have hNC := normalizerCondition_of_isNilpotent (G := ↥R)
  have hlt' := hNC _ hlt
  obtain ⟨x, hxN, hxE⟩ := SetLike.exists_of_lt hlt'
  have hxR : (x : G) ∈ R := x.2
  have hxNorm : (x : G) ∈ Subgroup.normalizer (Pb : Set G) := hRN hxR
  have hgE : ∀ e ∈ Subgroup.closure ({t, z} : Set G),
      (x : G) * e * (x : G)⁻¹ ∈ Subgroup.closure ({t, z} : Set G) := by
    intro e he
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN (⟨e, hER he⟩ : ↥R)).mp
      (Subgroup.mem_subgroupOf.mpr he)
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa using h2
  have hzE : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htE : t' ∈ Subgroup.closure ({t, z} : Set G) := by
    rcases ht' with h | h
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]; exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hzE
  have hcent := C.cent_of_normE ht' hW hxNorm (hgE z hzE) (hgE t' htE)
  have hgH : (x : G) ∈ H := (C.cent_z _).mp hcent.1
  have hPE := C.norm_inter_H hxNorm hgH
  obtain ⟨p, hp, e', he', hpe⟩ := (mem_sup_of_normalizes (fun e' he' p hp => C.E_norm_P he' hp)).mp hPE
  have hpR : p ∈ R := by
    have : p = (x : G) * e'⁻¹ := by rw [← hpe]; group
    rw [this]
    exact R.mul_mem hxR (R.inv_mem (hER he'))
  have hp3 : p ^ 3 = 1 := C.P_cube hp
  obtain ⟨k, hk⟩ := hR2 ⟨p, hpR⟩
  have hpk : p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hp1 : p = 1 := pow_coprime_eq_one hpk hp3 (Nat.Coprime.pow_left k (by norm_num))
  apply hxE
  rw [Subgroup.mem_subgroupOf]
  have : (x : G) = e' := by rw [← hpe, hp1, one_mul]
  rw [this]
  exact he'

theorem Core.cent_E [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {g : G}
    (hg : g ∈ Subgroup.normalizer (Pb : Set G))
    (hgE : ∀ e ∈ Subgroup.closure ({t, z} : Set G),
      g * e * g⁻¹ ∈ Subgroup.closure ({t, z} : Set G)) :
    ∀ e ∈ Subgroup.closure ({t, z} : Set G), g * e = e * g := by
  have hzE : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htE : t' ∈ Subgroup.closure ({t, z} : Set G) := by
    rcases ht' with h | h
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]; exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hzE
  have hcent := C.cent_of_normE ht' hW hg (hgE z hzE) (hgE t' htE)
  intro e he
  have hz := hcent.1
  have ht := hcent.2
  rcases C.E_elem ht' he with h | h | h | h
  · rw [h]; group
  · rw [h]; exact hz
  · rw [h]; exact ht
  · rw [h]
    calc g * (t' * z) = (g * t') * z := by group
      _ = (t' * g) * z := by rw [ht]
      _ = t' * (g * z) := by group
      _ = t' * (z * g) := by rw [hz]
      _ = (t' * z) * g := by group

theorem Core.exists_sylow_E [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) :
    ∃ P : Sylow 2 ↥(Subgroup.normalizer (Pb : Set G)),
      (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))) =
        (Subgroup.closure ({t, z} : Set G)).subgroupOf (Subgroup.normalizer (Pb : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.normalizer (Pb : Set G) :=
    C.E_le_norm_Pb
  have hPN2 : IsPGroup 2 ↥((Subgroup.closure ({t, z} : Set G)).subgroupOf
      (Subgroup.normalizer (Pb : Set G))) :=
    (C.E_isPGroup ht').of_injective (Subgroup.subgroupOfEquivOfLe hEN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEN).injective
  refine ⟨Sylow.mk _ hPN2 ?_, rfl⟩
  intro Q hQ hle
  have hRN : Q.map (Subgroup.normalizer (Pb : Set G)).subtype ≤ Subgroup.normalizer (Pb : Set G) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hR2 : IsPGroup 2 ↥(Q.map (Subgroup.normalizer (Pb : Set G)).subtype) :=
    hQ.of_injective (Subgroup.equivMapOfInjective Q (Subgroup.normalizer (Pb : Set G)).subtype
      (Subgroup.subtype_injective _)).symm.toMonoidHom
      (Subgroup.equivMapOfInjective Q (Subgroup.normalizer (Pb : Set G)).subtype
        (Subgroup.subtype_injective _)).symm.injective
  have hER : Subgroup.closure ({t, z} : Set G) ≤
      Q.map (Subgroup.normalizer (Pb : Set G)).subtype := by
    intro x hx
    have hmem : (⟨x, hEN hx⟩ : ↥(Subgroup.normalizer (Pb : Set G))) ∈ Q :=
      hle (Subgroup.mem_subgroupOf.mpr hx)
    exact ⟨⟨x, hEN hx⟩, hmem, rfl⟩
  have hRE := C.E_maximal ht' hW hRN hR2 hER
  ext x
  constructor
  · intro hx
    have hxR : (x : G) ∈ Q.map (Subgroup.normalizer (Pb : Set G)).subtype := ⟨x, hx, rfl⟩
    rw [hRE] at hxR
    exact Subgroup.mem_subgroupOf.mpr hxR
  · intro hx
    have hxE : (x : G) ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mem_subgroupOf.mp hx
    rw [← hRE] at hxE
    obtain ⟨y, hy, hyx⟩ := hxE
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy

theorem Core.exists_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) :
    ∃ Mf : Subgroup G, Mf ≤ Subgroup.normalizer (Pb : Set G) ∧ Odd (Nat.card ↥Mf) ∧
      (∀ g ∈ Subgroup.normalizer (Pb : Set G), ∀ x ∈ Mf, g * x * g⁻¹ ∈ Mf) ∧
      Mf ⊓ Subgroup.closure ({t, z} : Set G) = ⊥ ∧
      Mf ⊔ Subgroup.closure ({t, z} : Set G) = Subgroup.normalizer (Pb : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.normalizer (Pb : Set G) :=
    C.E_le_norm_Pb
  obtain ⟨P, hPE⟩ := C.exists_sylow_E ht' hW
  have hP : Subgroup.normalizer (P : Set ↥(Subgroup.normalizer (Pb : Set G))) ≤
      Subgroup.centralizer (P : Set ↥(Subgroup.normalizer (Pb : Set G))) := by
    intro x' hx'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hgE : ∀ e ∈ Subgroup.closure ({t, z} : Set G),
        (x' : G) * e * (x' : G)⁻¹ ∈ Subgroup.closure ({t, z} : Set G) := by
      intro e he
      have hemem : (⟨e, hEN he⟩ : ↥(Subgroup.normalizer (Pb : Set G))) ∈
          (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))) := by
        rw [hPE]; exact Subgroup.mem_subgroupOf.mpr he
      have h1 := (Subgroup.mem_normalizer_iff.mp hx' ⟨e, hEN he⟩).mp hemem
      rw [hPE] at h1
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa using h2
    have hhE : (h : G) ∈ Subgroup.closure ({t, z} : Set G) := by
      have hh' : h ∈ (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))) := SetLike.mem_coe.mp hh
      rw [hPE] at hh'; exact Subgroup.mem_subgroupOf.mp hh'
    have hcomm := C.cent_E ht' hW x'.2 hgE (h : G) hhE
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcomm.symm
  obtain ⟨K, hKn, hK2, -, -, -, -, hsup, hinf, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hP
  have hB : ∀ b ∈ (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))), ∀ a' ∈ K,
      b * a' * b⁻¹ ∈ K := fun b _ a' ha' => Subgroup.Normal.conj_mem hKn a' ha' b
  refine ⟨K.map (Subgroup.normalizer (Pb : Set G)).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective]
    rcases Nat.even_or_odd (Nat.card ↥K) with h | h
    · exact absurd (even_iff_two_dvd.mp h) hK2
    · exact h
  · intro g hg x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hconj := Subgroup.Normal.conj_mem hKn k hk ⟨g, hg⟩
    exact ⟨_, hconj, rfl⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxM, hxE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxM
    have hkP : k ∈ (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))) := by
      rw [hPE]; exact Subgroup.mem_subgroupOf.mpr hxE
    have hk1 : k ∈ K ⊓ (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))) := Subgroup.mem_inf.mpr ⟨hk, hkP⟩
    rw [hinf, Subgroup.mem_bot] at hk1
    simp [hk1]
  · apply le_antisymm
    · exact sup_le (by rintro _ ⟨x, _, rfl⟩; exact x.2) hEN
    · intro g hg
      have hgtop : (⟨g, hg⟩ : ↥(Subgroup.normalizer (Pb : Set G))) ∈
          K ⊔ (P : Subgroup ↥(Subgroup.normalizer (Pb : Set G))) := by
        rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨k, hk, p, hp, hkp⟩ := (mem_sup_of_normalizes hB).mp hgtop
      have hg' : g = (k : G) * (p : G) := by
        have := congrArg Subtype.val hkp
        simpa using this.symm
      have hpE : (p : G) ∈ Subgroup.closure ({t, z} : Set G) := by
        rw [hPE] at hp; exact Subgroup.mem_subgroupOf.mp hp
      rw [hg']
      exact mul_mem (Subgroup.mem_sup_left ⟨k, hk, rfl⟩) (Subgroup.mem_sup_right hpE)

def conjPb (Pb : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Pb : Set G)) : ↥Pb →* ↥Pb where
  toFun x := ⟨g * x.1 * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x.1).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem Core.gl_rep [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∃ coords : ↥Pb → (Fin 3 → ZMod 3), (∀ x y : ↥Pb, coords (x * y) = coords x + coords y) ∧
      Function.Injective coords ∧
      ∃ ρ : G → Matrix (Fin 3) (Fin 3) (ZMod 3),
        (∀ g ∈ Subgroup.normalizer (Pb : Set G), ∀ h ∈ Subgroup.normalizer (Pb : Set G),
          ρ (g * h) = ρ g * ρ h) ∧ ρ 1 = 1 ∧
        (∀ g (hg : g ∈ Subgroup.normalizer (Pb : Set G)) (x : G) (hx : x ∈ Pb),
          (ρ g).mulVec (coords ⟨x, hx⟩) = coords ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx⟩) := by
  classical
  letI cg : CommGroup ↥Pb :=
    { (inferInstance : Group ↥Pb) with
      mul_comm := fun x y => Subtype.ext (C.Pb_comm x.1 x.2 y.1 y.2) }
  have hexp : ∀ x : Additive ↥Pb, (3 : ℕ) • x = 0 := by
    intro x
    have h3 : (Additive.toMul x) ^ 3 = 1 := Subtype.ext (by simpa using C.Pb_cube (Additive.toMul x).2)
    show Additive.ofMul ((Additive.toMul x) ^ 3) = Additive.ofMul 1
    rw [h3]
  letI : Module (ZMod 3) (Additive ↥Pb) := AddCommGroup.zmodModule hexp
  have hcard : Nat.card (Additive ↥Pb) = 27 := by
    rw [Nat.card_congr Additive.ofMul.symm]
    exact C.Pb_card
  haveI : Fintype (Additive ↥Pb) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 3) (Additive ↥Pb) = 3 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := Additive ↥Pb)
    have h27 : Fintype.card (Additive ↥Pb) = 27 := by
      rw [← Nat.card_eq_fintype_card]; exact hcard
    have h3 : Fintype.card (ZMod 3) = 3 := ZMod.card 3
    rw [h27, h3] at h
    have h' : (3 : ℕ) ^ 3 = 3 ^ Module.finrank (ZMod 3) (Additive ↥Pb) := by
      rw [← h]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h').symm
  let β : Module.Basis (Fin 3) (ZMod 3) (Additive ↥Pb) :=
    Module.finBasisOfFinrankEq (ZMod 3) (Additive ↥Pb) hfin
  let f : ∀ g ∈ Subgroup.normalizer (Pb : Set G), Additive ↥Pb →ₗ[ZMod 3] Additive ↥Pb :=
    fun g hg => AddMonoidHom.toZModLinearMap 3 (MonoidHom.toAdditive (conjPb Pb g hg))
  let ρ : G → Matrix (Fin 3) (Fin 3) (ZMod 3) := fun g =>
    if hg : g ∈ Subgroup.normalizer (Pb : Set G) then LinearMap.toMatrix β β (f g hg) else 0
  refine ⟨fun x => β.equivFun (Additive.ofMul x), ?_, ?_, ρ, ?_, ?_, ?_⟩
  · intro x y
    simp only [ofMul_mul, map_add]
  · intro x y hxy
    exact Additive.ofMul.injective (β.equivFun.injective hxy)
  · intro g hg h hh
    have hgh : g * h ∈ Subgroup.normalizer (Pb : Set G) := mul_mem hg hh
    simp only [ρ, dif_pos hg, dif_pos hh, dif_pos hgh]
    rw [← LinearMap.toMatrix_comp β β β]
    congr 1
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [f, conjPb, mul_assoc]
  · simp only [ρ]
    rw [dif_pos (Subgroup.one_mem _)]
    have hf : f 1 (Subgroup.one_mem _) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [f, conjPb]
    rw [hf, LinearMap.toMatrix_id]
  · intro g hg x hx
    simp only [ρ, dif_pos hg]
    have := LinearMap.toMatrix_mulVec_repr β β (f g hg) (Additive.ofMul ⟨x, hx⟩)
    simpa [f, conjPb] using this

abbrev GL3Trans : Prop :=
  ∀ g : GL (Fin 3) (ZMod 3), orderOf g = 13 → ∀ u v : Fin 3 → ZMod 3, u ≠ 0 → v ≠ 0 →
    ∃ k : ℕ, ∃ c : ZMod 3, c ≠ 0 ∧
      ((g ^ k : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)).mulVec u = c • v

theorem Core.ord13_false [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (hGL : GL3Trans) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Pb : Set G)) (hord : orderOf g = 13) : False := by
  obtain ⟨coords, hadd, hinj, ρ, hmul, hone, hrel⟩ := C.gl_rep
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ k : ℕ, g ^ k ∈ Subgroup.normalizer (Pb : Set G) := fun k =>
    (Subgroup.normalizer (Pb : Set G)).pow_mem hgN k
  have hρpow : ∀ k : ℕ, ρ (g ^ k) = (ρ g) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ k ih =>
      rw [pow_succ, hmul (g ^ k) (hpow k) g hgN, ih, pow_succ]
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Pb : Set G) := Subgroup.inv_mem _ hgN
  have hρ1 : ρ g * ρ g⁻¹ = 1 := by
    rw [← hmul g hgN g⁻¹ hginv, mul_inv_cancel, hone]
  have hρ2 : ρ g⁻¹ * ρ g = 1 := by
    rw [← hmul g⁻¹ hginv g hgN, inv_mul_cancel, hone]
  let Ug : GL (Fin 3) (ZMod 3) := Units.mk (ρ g) (ρ g⁻¹) hρ1 hρ2
  have hUg : ∀ k : ℕ, ((Ug ^ k : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      ρ (g ^ k) := by
    intro k
    rw [Units.val_pow_eq_pow_val, hρpow]
  have hgpow13 : g ^ 13 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hUg1 : Ug ≠ 1 := by
    intro h1
    have hρg : ρ g = 1 := by
      have := congrArg (fun U : GL (Fin 3) (ZMod 3) => (U : Matrix (Fin 3) (Fin 3) (ZMod 3))) h1
      simpa [Ug] using this
    have hcent : g ∈ Subgroup.centralizer (Pb : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hrx := hrel g hgN x hx
      rw [hρg, Matrix.one_mulVec] at hrx
      have hxg : g * x * g⁻¹ = x := congrArg Subtype.val (hinj hrx.symm)
      exact (mul_inv_eq_iff_eq_mul.mp hxg).symm
    rw [C.cent_Pb_eq] at hcent
    have hg3 : g ^ 3 = 1 := C.Pb_cube hcent
    have hg1 : g = 1 := pow_coprime_eq_one hgpow13 hg3 (by norm_num)
    rw [hg1, orderOf_one] at hord
    norm_num at hord
  have hUg13 : orderOf Ug = 13 := by
    apply orderOf_eq_prime
    · apply Units.ext
      have h := hUg 13
      rw [hgpow13, hone] at h
      simpa using h
    · exact hUg1
  have hcoord1 : coords (1 : ↥Pb) = 0 := by
    have h11 := hadd (1 : ↥Pb) (1 : ↥Pb)
    rw [mul_one] at h11
    simpa using h11
  have hcp : ∀ (x : ↥Pb) (n : ℕ), coords (x ^ n) = n • coords x := by
    intro x n
    induction n with
    | zero => rw [pow_zero, hcoord1, zero_smul]
    | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]
  let bP : ↥Pb := ⟨b, C.b_Pb⟩
  let aP : ↥Pb := ⟨a, C.a_Pb⟩
  have hu : coords aP ≠ 0 := by
    intro h
    apply C.a_ne
    have := hinj (h.trans hcoord1.symm)
    exact congrArg Subtype.val this
  have hv : coords bP ≠ 0 := by
    intro h
    apply C.b_ne
    have := hinj (h.trans hcoord1.symm)
    exact congrArg Subtype.val this
  obtain ⟨k, c, hc0, hk⟩ := hGL Ug hUg13 (coords aP) (coords bP) hu hv
  rw [hUg k] at hk
  have hrel' := hrel (g ^ k) (hpow k) a C.a_Pb
  rw [hk] at hrel'
  have hcv : c • coords bP = coords (bP ^ c.val) := by
    rw [hcp, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  have hconj_eq : coords ⟨g ^ k * a * (g ^ k)⁻¹, (Subgroup.mem_normalizer_iff.mp (hpow k) a).mp C.a_Pb⟩
      = coords (bP ^ c.val) := hrel'.symm.trans hcv
  have hxeq := congrArg Subtype.val (hinj hconj_eq)
  rw [Subgroup.coe_pow] at hxeq
  have h_conj : g ^ k * a * (g ^ k)⁻¹ = b ^ c.val := hxeq
  have hcv3 : c.val = 1 ∨ c.val = 2 := by
    have h1 : c.val ≠ 0 := fun h => hc0 ((ZMod.val_eq_zero c).mp h)
    have h2 : c.val < 3 := ZMod.val_lt c
    omega
  have hb3' : b * (b * b) = 1 := by rw [← pow_three]; exact C.b_cube
  have hb2 : b ^ 2 = b⁻¹ := by
    rw [sq]; exact eq_inv_of_mul_eq_one_right hb3'
  have hbb : IsConj b b⁻¹ := isConj_iff.mpr ⟨t, C.t_b⟩
  rcases hcv3 with h1 | h2
  · apply C.not_conj_ab
    rw [isConj_iff]
    exact ⟨g ^ k, by rw [h_conj, h1, pow_one]⟩
  · have hab' : IsConj a b⁻¹ := by
      rw [isConj_iff]
      exact ⟨g ^ k, by rw [h_conj, h2, hb2]⟩
    apply C.not_conj_ab
    exact IsConj.trans hab' hbb.symm

theorem Core.gl_hom [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∃ coords : ↥Pb → (Fin 3 → ZMod 3), (∀ x y : ↥Pb, coords (x * y) = coords x + coords y) ∧
      Function.Injective coords ∧
      ∃ ψ : ↥(Subgroup.normalizer (Pb : Set G)) →* GL (Fin 3) (ZMod 3),
        ∀ (g : ↥(Subgroup.normalizer (Pb : Set G))) (x : G) (hx : x ∈ Pb),
          ((ψ g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)).mulVec (coords ⟨x, hx⟩) =
            coords ⟨(g : G) * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp hx⟩ := by
  obtain ⟨coords, hadd, hinj, ρ, hmul, hone, hrel⟩ := C.gl_rep
  have hginv : ∀ g : ↥(Subgroup.normalizer (Pb : Set G)), (g : G)⁻¹ ∈ Subgroup.normalizer (Pb : Set G) :=
    fun g => Subgroup.inv_mem _ g.2
  have hρ1 : ∀ g : ↥(Subgroup.normalizer (Pb : Set G)), ρ g * ρ (g : G)⁻¹ = 1 := by
    intro g
    rw [← hmul (g : G) g.2 (g : G)⁻¹ (hginv g), mul_inv_cancel, hone]
  have hρ2 : ∀ g : ↥(Subgroup.normalizer (Pb : Set G)), ρ (g : G)⁻¹ * ρ g = 1 := by
    intro g
    rw [← hmul (g : G)⁻¹ (hginv g) (g : G) g.2, inv_mul_cancel, hone]
  refine ⟨coords, hadd, hinj, {
    toFun := fun g => Units.mk (ρ g) (ρ (g : G)⁻¹) (hρ1 g) (hρ2 g)
    map_one' := ?_
    map_mul' := ?_ }, ?_⟩
  · apply Units.ext
    simp only [Units.val_mk, Units.val_one]
    have : ((1 : ↥(Subgroup.normalizer (Pb : Set G))) : G) = 1 := rfl
    rw [this, hone]
  · intro g h
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk, Subgroup.coe_mul]
    rw [hmul (g : G) g.2 (h : G) h.2]
  · intro g x hx
    exact hrel (g : G) g.2 x hx

theorem Core.prime_dvd_N [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (hGL : GL3Trans) {p : ℕ}
    (hp : p.Prime) (hpN : p ∣ Nat.card ↥(Subgroup.normalizer (Pb : Set G))) : p = 2 ∨ p = 3 := by
  obtain ⟨coords, -, hinj, ψ, hψ⟩ := C.gl_hom
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥(Subgroup.normalizer (Pb : Set G)) := Fintype.ofFinite _
  have hpN' : p ∣ Fintype.card ↥(Subgroup.normalizer (Pb : Set G)) := by
    rw [← Nat.card_eq_fintype_card]; exact hpN
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hpN'
  have hgord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  by_cases hgP : (x : G) ∈ Pb
  · have h3 : (x : G) ^ 3 = 1 := C.Pb_cube hgP
    have hd : p ∣ 3 := by
      rw [← hgord]; exact orderOf_dvd_of_pow_eq_one h3
    right
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
  · have hψ1 : ψ x ≠ 1 := by
      intro h1
      apply hgP
      have hcent : (x : G) ∈ Subgroup.centralizer (Pb : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hry := hψ x y hy
        rw [h1, Units.val_one, Matrix.one_mulVec] at hry
        have hxy : (x : G) * y * (x : G)⁻¹ = y := congrArg Subtype.val (hinj hry.symm)
        exact (mul_inv_eq_iff_eq_mul.mp hxy).symm
      rw [C.cent_Pb_eq] at hcent
      exact hcent
    have hψp : ψ x ^ p = 1 := by
      rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
    have hord : orderOf (ψ x) = p := orderOf_eq_prime hψp hψ1
    have hdvd : p ∣ Nat.card (GL (Fin 3) (ZMod 3)) := by
      rw [← hord]; exact orderOf_dvd_natCard _
    rw [Matrix.card_GL_field, ZMod.card 3, Fin.prod_univ_three] at hdvd
    norm_num at hdvd
    by_cases hp13 : p = 13
    · exfalso
      exact C.ord13_false hGL x.2 (by rw [hgord, hp13])
    · have h11232 : p ∣ 2 ^ 5 * 3 ^ 3 * 13 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).mp h11232 with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h')
        · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h')
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h) hp13

theorem Core.isPGroup_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (hGL : GL3Trans)
    {Mf : Subgroup G} (hMN : Mf ≤ Subgroup.normalizer (Pb : Set G)) (hodd : Odd (Nat.card ↥Mf)) :
    IsPGroup 3 ↥Mf := by
  have hdvd : Nat.card ↥Mf ∣ Nat.card ↥(Subgroup.normalizer (Pb : Set G)) :=
    Subgroup.card_dvd_of_le hMN
  have hpos : Nat.card ↥Mf ≠ 0 := (Nat.card_pos).ne'
  have h2 : ¬ 2 ∣ Nat.card ↥Mf := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  have key := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hpos (fun {d} hd hdM => by
    have hdN : d ∣ Nat.card ↥(Subgroup.normalizer (Pb : Set G)) := dvd_trans hdM hdvd
    rcases C.prime_dvd_N hGL hd hdN with h | h
    · exfalso
      apply h2
      rw [← h]; exact hdM
    · exact h)
  exact IsPGroup.of_card key

structure MfData (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (Mf : Subgroup G) : Prop where
  le : Mf ≤ Subgroup.normalizer (Pb : Set G)
  odd : Odd (Nat.card ↥Mf)
  conj : ∀ g ∈ Subgroup.normalizer (Pb : Set G), ∀ x ∈ Mf, g * x * g⁻¹ ∈ Mf
  inf : Mf ⊓ Subgroup.closure ({t, z} : Set G) = ⊥
  sup : Mf ⊔ Subgroup.closure ({t, z} : Set G) = Subgroup.normalizer (Pb : Set G)

theorem Core.three_mem_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf) {g : G}
    (hg : g ∈ Subgroup.normalizer (Pb : Set G)) {n : ℕ} (hn : g ^ 3 ^ n = 1) : g ∈ Mf := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (Pb : Set G) with hNdef
  set E := Subgroup.closure ({t, z} : Set G) with hEdef
  have hEN : E ≤ N := C.E_le_norm_Pb
  let K : Subgroup ↥N := Mf.subgroupOf N
  haveI hK : K.Normal := ⟨fun k hk x => by
    have hk' : (k : G) ∈ Mf := Subgroup.mem_subgroupOf.mp hk
    exact Subgroup.mem_subgroupOf.mpr (hM.conj x x.2 k hk')⟩
  have hKcard : Nat.card ↥K = Nat.card ↥Mf :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM.le).toEquiv
  have hB : ∀ e ∈ E, ∀ m ∈ Mf, e * m * e⁻¹ ∈ Mf := fun e he m hm => hM.conj e (hEN he) m hm
  have hsupcard : Nat.card ↥(Mf ⊔ E) = Nat.card ↥Mf * Nat.card ↥E :=
    card_sup_of_normalizes hB hM.inf
  rw [hM.sup] at hsupcard
  have hidx := Subgroup.card_mul_index K
  rw [hKcard, hsupcard] at hidx
  have hMpos : Nat.card ↥Mf ≠ 0 := (Nat.card_pos).ne'
  have hidxE : K.index = Nat.card ↥E := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hMpos) hidx
  obtain ⟨m, hm⟩ := (C.E_isPGroup ht').exists_card_eq
  let x : ↥N := ⟨g, hg⟩
  have hx : x ^ 3 ^ n = 1 := Subtype.ext (by simpa using hn)
  have hd1 : orderOf (QuotientGroup.mk' K x) ∣ 3 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hx, map_one]
  have hd2 : orderOf (QuotientGroup.mk' K x) ∣ 2 ^ m := by
    have h := orderOf_dvd_natCard (QuotientGroup.mk' K x)
    rw [← Subgroup.index_eq_card, hidxE, hm] at h
    exact h
  have hcop : Nat.Coprime (3 ^ n) (2 ^ m) := Nat.Coprime.pow n m (by norm_num)
  have hone : orderOf (QuotientGroup.mk' K x) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  have hπ : QuotientGroup.mk' K x = 1 := orderOf_eq_one_iff.mp hone
  have hxK : x ∈ K := (QuotientGroup.eq_one_iff x).mp hπ
  exact Subgroup.mem_subgroupOf.mp hxK

theorem inv_conj_involution {g x : G} (hg : g * g = 1) : g * (g * x * g⁻¹) * g⁻¹ = x := by
  have hgg : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hg, inv_one]
  calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g⁻¹ * g⁻¹) := by group
    _ = x := by rw [hg, hgg, one_mul, mul_one]

theorem mem_normalizer_of_involution {S : Subgroup G} {g : G} (hg : g * g = 1)
    (hf : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hf h, fun hh => ?_⟩
  have h2 := hf _ hh
  rwa [inv_conj_involution hg] at h2

theorem conj_mem_of_norm {S : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (S : Set G))
    {p : G} (hp : p ∈ S) : x * p * x⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hx p).mp hp

theorem eq_one_of_sq_cube {g : G} (h2 : g * g = 1) (h3 : g ^ 3 = 1) : g = 1 := by
  calc g = g ^ 3 * (g * g)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem comm_of_conj_eq {c p : G} (h : c * p * c⁻¹ = p) : p * c = c * p := by
  calc p * c = (c * p * c⁻¹) * c := by rw [h]
    _ = c * p := by group

theorem Core.t_conj_zpow_b (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (k : ℤ) :
    t * b ^ k * t⁻¹ = b ^ (-k) := by
  rw [← conj_zpow, C.t_b, inv_zpow, zpow_neg]

theorem Core.z_conj_zpow_b (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (k : ℤ) :
    z * b ^ k * z⁻¹ = b ^ k := by
  have h : z * b * z⁻¹ = b := by rw [C.comm_zb, mul_inv_cancel_right]
  rw [← conj_zpow, h]

theorem Core.t_norm_MM (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Subgroup.closure ({t, z} : Set G) ≤
      Subgroup.normalizer ((M₁ ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hfwd : ∀ v : G, (∀ x ∈ M₁, v * x * v⁻¹ ∈ M₁) →
      (∀ k : ℤ, v * b ^ k * v⁻¹ ∈ Subgroup.zpowers b) →
      ∀ x ∈ M₁ ⊔ Subgroup.zpowers b, v * x * v⁻¹ ∈ M₁ ⊔ Subgroup.zpowers b := by
    intro v hv1 hv2 x hx
    obtain ⟨m, hm, c, hc, rfl⟩ := (mem_sup_of_normalizes C.zpow_b_norm_M₁).mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have e : v * (m * b ^ k) * v⁻¹ = (v * m * v⁻¹) * (v * b ^ k * v⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hv1 m hm)) (Subgroup.mem_sup_right (hv2 k))
  have hT : t ∈ Subgroup.normalizer ((M₁ ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
    mem_normalizer_of_involution C.t_mul
      (hfwd t (fun x hx => C.M₁_t x hx) (fun k => by
        rw [C.t_conj_zpow_b k]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _))
  have hZ : z ∈ Subgroup.normalizer ((M₁ ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
    mem_normalizer_of_involution C.z_mul
      (hfwd z (fun x hx => C.z_conj_M₁ hx) (fun k => by
        rw [C.z_conj_zpow_b k]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _))
  exact (Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨hT, Set.singleton_subset_iff.mpr hZ⟩)

theorem Core.Enorm_MM (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {e m : G}
    (he : e ∈ Subgroup.closure ({t, z} : Set G)) (hm : m ∈ M₁ ⊔ Subgroup.zpowers b) :
    e * m * e⁻¹ ∈ M₁ ⊔ Subgroup.zpowers b :=
  (Subgroup.mem_normalizer_iff.mp (C.t_norm_MM he) m).mp hm

theorem Core.Enorm_P (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {e p : G}
    (he : e ∈ Subgroup.closure ({t, z} : Set G)) (hp : p ∈ Subgroup.closure ({a, b} : Set G)) :
    e * p * e⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
  have hN : e ∈ Subgroup.normalizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
    rw [C.norm_P]; exact Subgroup.mem_sup_right he
  exact (Subgroup.mem_normalizer_iff.mp hN p).mp hp

theorem Core.MM_le_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf) :
    M₁ ⊔ Subgroup.zpowers b ≤ Mf := by
  intro x hx
  have hP : IsPGroup 3 ↥(M₁ ⊔ Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 4) (by rw [C.card_MM]; norm_num)
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact C.three_mem_Mf ht' hM (C.MM_le_norm_Pb hx) hk'

theorem Core.P_le_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf) :
    Subgroup.closure ({a, b} : Set G) ≤ Mf :=
  le_trans C.P_le_Pb (le_trans C.Pb_le_MM (C.MM_le_Mf ht' hM))

theorem Core.Pb_le_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf) : Pb ≤ Mf :=
  le_trans C.Pb_le_MM (C.MM_le_Mf ht' hM)

theorem Core.norm_a_MM (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    M₁ ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  have hb : b ∈ Subgroup.centralizer {a} :=
    Subgroup.mem_centralizer_singleton_iff.mpr C.ab_comm.symm
  have hsub : M₁ ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer {a} :=
    sup_le (by rw [← C.M₁_sup]; exact le_sup_left) (Subgroup.zpowers_le.mpr hb)
  rw [C.norm_a]
  exact le_trans hsub le_sup_left

theorem Core.Mf_inf_norm_a [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf) :
    Mf ⊓ Subgroup.normalizer (Subgroup.zpowers a : Set G) = M₁ ⊔ Subgroup.zpowers b := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨m, hm, e, he, hme⟩ := (mem_sup_of_normalizes
      (fun e he m hm => C.Enorm_MM he hm)).mp (C.norm_inter_norm_a (hM.le hxM) hxN)
    have hmMf : m ∈ Mf := C.MM_le_Mf ht' hM hm
    have heMf : e ∈ Mf := by
      have h1 : e = m⁻¹ * x := by rw [← hme]; group
      rw [h1]; exact Mf.mul_mem (Mf.inv_mem hmMf) hxM
    have he1 : e = 1 := by
      have hmem : e ∈ Mf ⊓ Subgroup.closure ({t, z} : Set G) := Subgroup.mem_inf.mpr ⟨heMf, he⟩
      rw [hM.inf] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [he1, mul_one] at hme
    rw [← hme]; exact hm
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨C.MM_le_Mf ht' hM hx, C.norm_a_MM hx⟩

theorem Core.t_inv_P (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {q : G} (hq : q ∈ Subgroup.closure ({a, b} : Set G)) :
    t' * q * t'⁻¹ = q⁻¹ := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact C.t'_a ht'
    · exact C.t'_b ht'
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := C.P_comm x y hx hy
    calc t' * (x * y) * t'⁻¹ = (t' * x * t'⁻¹) * (t' * y * t'⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
      _ = (y * x)⁻¹ := by group
      _ = (x * y)⁻¹ := by rw [hxy]
  | inv x hx ihx =>
    calc t' * x⁻¹ * t'⁻¹ = (t' * x * t'⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [ihx]

theorem Core.u_sq (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) : t' * z * (t' * z) = 1 := by
  have hcomm : t' * z = z * t' := C.t'_z ht'
  calc t' * z * (t' * z) = t' * (z * t') * z := by group
    _ = t' * (t' * z) * z := by rw [← hcomm]
    _ = (t' * t') * (z * z) := by group
    _ = 1 := by rw [C.t'_mul ht', C.z_mul, one_mul]

theorem Core.u_ne_one (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) : t' * z ≠ 1 := by
  intro h
  have htz : t' = z := by
    calc t' = t' * z * z := by rw [mul_assoc, C.z_mul, mul_one]
      _ = z := by rw [h, one_mul]
  have h1 := C.t'_a ht'
  rw [htz] at h1
  have ha : z * a * z⁻¹ = a := by rw [C.comm_za, mul_inv_cancel_right]
  rw [ha] at h1
  apply C.a_ne
  apply eq_one_of_sq_cube _ C.a_cube
  calc a * a = a * a⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel a

theorem Core.u_inv_Pb (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {p : G}
    (hp : p ∈ Pb) : t' * z * p * (t' * z)⁻¹ = p⁻¹ := by
  obtain ⟨w, hw, q, hq, rfl⟩ := C.Pb_decomp hp
  have hzw : z * w * z⁻¹ = w⁻¹ := ((mem_wOne C).mp hw).1.2
  have hw' : t' * w * t'⁻¹ = w := hW w hw
  have hqz : z * q * z⁻¹ = q := C.z_fix_P hq
  have hq' : t' * q * t'⁻¹ = q⁻¹ := C.t_inv_P ht' hq
  have hwPb : w ∈ Pb := C.wOne_le_Pb hw
  have hqPb : q ∈ Pb := C.P_le_Pb hq
  have hcomm : q * w = w * q := C.Pb_comm q hqPb w hwPb
  have huw : t' * z * w * (t' * z)⁻¹ = w⁻¹ := by
    calc t' * z * w * (t' * z)⁻¹ = t' * (z * w * z⁻¹) * t'⁻¹ := by group
      _ = t' * w⁻¹ * t'⁻¹ := by rw [hzw]
      _ = (t' * w * t'⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [hw']
  have huq : t' * z * q * (t' * z)⁻¹ = q⁻¹ := by
    calc t' * z * q * (t' * z)⁻¹ = t' * (z * q * z⁻¹) * t'⁻¹ := by group
      _ = t' * q * t'⁻¹ := by rw [hqz]
      _ = q⁻¹ := hq'
  calc t' * z * (w * q) * (t' * z)⁻¹ = (t' * z * w * (t' * z)⁻¹) * (t' * z * q * (t' * z)⁻¹) := by
        group
    _ = w⁻¹ * q⁻¹ := by rw [huw, huq]
    _ = (q * w)⁻¹ := (mul_inv_rev q w).symm
    _ = (w * q)⁻¹ := by rw [hcomm]

theorem Core.u_comm_Pb [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {x : G}
    (hx : x ∈ Subgroup.normalizer (Pb : Set G)) :
    t' * z * x * (t' * z)⁻¹ * x⁻¹ ∈ Pb := by
  have huu : (t' * z)⁻¹ = t' * z := inv_eq_of_mul_eq_one_right (C.u_sq ht')
  rw [← C.cent_Pb_eq, Subgroup.mem_centralizer_iff]
  intro p hp
  have hq : x⁻¹ * p * x ∈ Pb := by
    have h := conj_mem_of_norm (Subgroup.inv_mem _ hx) hp
    rwa [inv_inv] at h
  have hinvq : (t' * z)⁻¹ * (x⁻¹ * p * x) * (t' * z) = (x⁻¹ * p * x)⁻¹ := by
    have h := C.u_inv_Pb ht' hW hq
    rw [huu] at h ⊢
    exact h
  apply comm_of_conj_eq
  calc t' * z * x * (t' * z)⁻¹ * x⁻¹ * p * (t' * z * x * (t' * z)⁻¹ * x⁻¹)⁻¹
      = t' * z * (x * ((t' * z)⁻¹ * (x⁻¹ * p * x) * (t' * z)) * x⁻¹) * (t' * z)⁻¹ := by group
    _ = t' * z * (x * (x⁻¹ * p * x)⁻¹ * x⁻¹) * (t' * z)⁻¹ := by rw [hinvq]
    _ = (t' * z * p⁻¹ * (t' * z)⁻¹) := by group
    _ = ((t' * z) * p * (t' * z)⁻¹)⁻¹ := by group
    _ = p := by rw [C.u_inv_Pb ht' hW hp, inv_inv]

theorem Core.lift_z [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x p : G} (hp : p ∈ Pb)
    (h : z * x * z⁻¹ = x * p) : z * (x * p ^ 2) * z⁻¹ = x * p ^ 2 := by
  have hp3 : p ^ 3 = 1 := C.Pb_cube hp
  have hpinv : p⁻¹ = p ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hp3]
  have hzp : z * p * z⁻¹ = p⁻¹ := by
    have h1 : z * (x * p) * z⁻¹ = x := by
      rw [← h]; exact inv_conj_involution C.z_mul
    have h3 : (z * x * z⁻¹) * (z * p * z⁻¹) = x := by
      rw [← (show z * (x * p) * z⁻¹ = (z * x * z⁻¹) * (z * p * z⁻¹) by group)]
      exact h1
    rw [h] at h3
    calc z * p * z⁻¹ = (x * p)⁻¹ * (x * p * (z * p * z⁻¹)) := by group
      _ = (x * p)⁻¹ * x := by rw [h3]
      _ = p⁻¹ := by group
  calc z * (x * p ^ 2) * z⁻¹ = (z * x * z⁻¹) * (z * p * z⁻¹) ^ 2 := by
        rw [conj_pow]; group
    _ = x * p * p⁻¹ ^ 2 := by rw [h, hzp]
    _ = x * p⁻¹ := by group
    _ = x * p ^ 2 := by rw [hpinv]

theorem Core.fix_z_mem_Pb [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf) {x : G} (hx : x ∈ Mf)
    (hzx : z * x * z⁻¹ = x) : x ∈ Pb := by
  have hc : z * x = x * z := by
    calc z * x = (z * x * z⁻¹) * z := by group
      _ = x * z := by rw [hzx]
  have hxH : x ∈ H := (C.cent_z x).mp hc.symm
  have hEP : ∀ e ∈ Subgroup.closure ({t, z} : Set G), ∀ p ∈ Subgroup.closure ({a, b} : Set G),
      e * p * e⁻¹ ∈ Subgroup.closure ({a, b} : Set G) :=
    fun e he p hp => C.Enorm_P he hp
  obtain ⟨p, hp, e, he, hpe⟩ :=
    (mem_sup_of_normalizes hEP).mp (C.norm_inter_H (hM.le hx) hxH)
  have hpM : p ∈ Mf := C.P_le_Mf ht' hM hp
  have heM : e ∈ Mf := by
    have h1 : e = p⁻¹ * x := by rw [← hpe]; group
    rw [h1]; exact Mf.mul_mem (Mf.inv_mem hpM) hx
  have he1 : e = 1 := by
    have hmem : e ∈ Mf ⊓ Subgroup.closure ({t, z} : Set G) := Subgroup.mem_inf.mpr ⟨heM, he⟩
    rw [hM.inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [he1, mul_one] at hpe
  rw [← hpe]
  exact C.P_le_Pb hp

theorem Core.u_lift_fix [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {x c : G}
    (hc : c ∈ Pb) (h : t' * z * x * (t' * z)⁻¹ = c * x) :
    t' * z * (c ^ 2 * x) * (t' * z)⁻¹ = c ^ 2 * x := by
  have hc3 : c ^ 3 = 1 := C.Pb_cube hc
  have hcinv : c⁻¹ = c ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hc3]
  have hu : t' * z * c * (t' * z)⁻¹ = c⁻¹ := C.u_inv_Pb ht' hW hc
  calc t' * z * (c ^ 2 * x) * (t' * z)⁻¹
      = (t' * z * c * (t' * z)⁻¹) ^ 2 * (t' * z * x * (t' * z)⁻¹) := by
        rw [conj_pow]; group
    _ = (c⁻¹) ^ 2 * (c * x) := by rw [hu, h]
    _ = c⁻¹ * x := by group
    _ = c ^ 2 * x := by rw [hcinv]

theorem Core.Mf_inf_cent_t' [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) :
    Mf ⊓ Subgroup.centralizer {t'} = wOne C := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxc' := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hxt : t' * x * t'⁻¹ = x := by
      calc t' * x * t'⁻¹ = (x * t') * t'⁻¹ := by rw [hxc']
        _ = x := by group
    have hu : t' * z * x * (t' * z)⁻¹ = z * x * z⁻¹ := by
      calc t' * z * x * (t' * z)⁻¹ = z * t' * x * (z * t')⁻¹ := by rw [C.t'_z ht']
        _ = z * (t' * x * t'⁻¹) * z⁻¹ := by group
        _ = z * x * z⁻¹ := by rw [hxt]
    have hcx := C.u_comm_Pb ht' hW (hM.le hxM)
    have hp : x⁻¹ * (t' * z * x * (t' * z)⁻¹ * x⁻¹) * x ∈ Pb := by
      have h := conj_mem_of_norm (Subgroup.inv_mem _ (hM.le hxM)) hcx
      rwa [inv_inv] at h
    have hzx : z * x * z⁻¹ = x * (x⁻¹ * (t' * z * x * (t' * z)⁻¹ * x⁻¹) * x) := by
      rw [hu]; group
    obtain ⟨p, hpPb, hzxp⟩ : ∃ p ∈ Pb, z * x * z⁻¹ = x * p := ⟨_, hp, hzx⟩
    have hy := C.lift_z hpPb hzxp
    have hpM : p ^ 2 ∈ Mf := Mf.pow_mem (C.Pb_le_Mf ht' hM hpPb) 2
    have hyM : x * p ^ 2 ∈ Mf := Mf.mul_mem hxM hpM
    have hyPb := C.fix_z_mem_Pb ht' hM hyM hy
    have hxPb : x ∈ Pb := by
      have h := Pb.mul_mem hyPb (Pb.inv_mem (Pb.pow_mem hpPb 2))
      rwa [mul_inv_cancel_right] at h
    rw [← C.Pb_inf_cent_t' ht' hW]
    exact Subgroup.mem_inf.mpr ⟨hxPb, hxc⟩
  · intro x hx
    have hxPb : x ∈ Pb := by
      rw [C.Pb_eq_sup]; exact Subgroup.mem_sup_right hx
    have hxt : x * t' = t' * x := by
      have := hW x hx
      calc x * t' = (t' * x * t'⁻¹) * t' := by rw [this]
        _ = t' * x := by group
    exact Subgroup.mem_inf.mpr ⟨C.Pb_le_Mf ht' hM hxPb,
      Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩

theorem Core.Mf_eq_sup [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) :
    Mf = Pb ⊔ (Mf ⊓ Subgroup.centralizer {t' * z}) := by
  apply le_antisymm
  · intro x hx
    have hcx := C.u_comm_Pb ht' hW (hM.le hx)
    obtain ⟨c, hc, hcdef⟩ : ∃ c ∈ Pb, t' * z * x * (t' * z)⁻¹ = c * x :=
      ⟨_, hcx, by group⟩
    have hfix := C.u_lift_fix ht' hW hc hcdef
    have hyS : c ^ 2 * x ∈ Mf ⊓ Subgroup.centralizer {t' * z} := by
      refine Subgroup.mem_inf.mpr ⟨Mf.mul_mem (Mf.pow_mem (C.Pb_le_Mf ht' hM hc) 2) hx, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc c ^ 2 * x * (t' * z) = (t' * z * (c ^ 2 * x) * (t' * z)⁻¹) * (t' * z) := by rw [hfix]
        _ = (t' * z) * (c ^ 2 * x) := by group
    have hxeq : x = (c ^ 2)⁻¹ * (c ^ 2 * x) := by group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Pb.inv_mem (Pb.pow_mem hc 2)))
      (Subgroup.mem_sup_right hyS)
  · exact sup_le (C.Pb_le_Mf ht' hM) inf_le_left

theorem Core.card_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) :
    Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) = 9 ∧ Nat.card ↥Mf = 243 := by
  have hsup := C.Mf_eq_sup ht' hW hM
  have hdisj : Pb ⊓ (Mf ⊓ Subgroup.centralizer {t' * z}) = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨hpPb, hpS⟩ := Subgroup.mem_inf.mp hp
    have hcomm : p * (t' * z) = (t' * z) * p :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hpS).2
    have hup : t' * z * p * (t' * z)⁻¹ = p := by
      calc t' * z * p * (t' * z)⁻¹ = p * (t' * z) * (t' * z)⁻¹ := by rw [hcomm]
        _ = p := by group
    have heq : p = p⁻¹ := by
      have h := C.u_inv_Pb ht' hW hpPb
      rw [hup] at h
      exact h
    have hpp : p * p = 1 := mul_eq_one_iff_eq_inv.mpr heq
    exact Subgroup.mem_bot.mpr (eq_one_of_sq_cube hpp (C.Pb_cube hpPb))
  have hnorm : ∀ s ∈ Mf ⊓ Subgroup.centralizer {t' * z}, ∀ p ∈ Pb, s * p * s⁻¹ ∈ Pb :=
    fun s hs p hp => conj_mem_of_norm (hM.le (Subgroup.mem_inf.mp hs).1) hp
  have hcard : Nat.card ↥Mf = 27 * Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) := by
    have h1 : Nat.card ↥Mf = Nat.card ↥(Pb ⊔ (Mf ⊓ Subgroup.centralizer {t' * z})) :=
      congrArg (fun K : Subgroup G => Nat.card ↥K) hsup
    rw [h1, card_sup_of_normalizes hnorm hdisj, C.Pb_card]
  have hodd : Odd (Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z})) := by
    have h := hM.odd
    rw [hcard] at h
    exact (Nat.odd_mul.mp h).2
  obtain ⟨g, hg⟩ := isConj_iff.mp (C.inv_conj (t' * z) (C.u_sq ht') (C.u_ne_one ht'))
  have hz' : g⁻¹ * (t' * z) * g = z := by rw [← hg]; group
  have hS'le : (Mf ⊓ Subgroup.centralizer {t' * z}).map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have hsu : s * (t' * z) = (t' * z) * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs).2
    have hy' : (MulAut.conj g⁻¹).toMonoidHom s = g⁻¹ * s * g := by
      simp [MulAut.conj_apply]
    rw [hy']
    apply (C.cent_z _).mp
    calc g⁻¹ * s * g * z = g⁻¹ * s * g * (g⁻¹ * (t' * z) * g) := by rw [hz']
      _ = g⁻¹ * (s * (t' * z)) * g := by group
      _ = g⁻¹ * ((t' * z) * s) * g := by rw [hsu]
      _ = (g⁻¹ * (t' * z) * g) * (g⁻¹ * s * g) := by group
      _ = z * (g⁻¹ * s * g) := by rw [hz']
  have hcardS' : Nat.card ↥((Mf ⊓ Subgroup.centralizer {t' * z}).map
      (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hdvd576 : Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) ∣ 576 := by
    rw [← C.card_H, ← hcardS']
    exact Subgroup.card_dvd_of_le hS'le
  have h2 : ¬ 2 ∣ Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) := by
    rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.mp hodd
  have hcop : Nat.Coprime (Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z})) (2 ^ 6) :=
    Nat.Coprime.pow_right 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
  have hd9 : Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) ∣ 9 :=
    hcop.dvd_of_dvd_mul_right (by norm_num; exact hdvd576)
  have hle9 : Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) ≤ 9 := Nat.le_of_dvd (by norm_num) hd9
  have h81 : 81 ∣ Nat.card ↥Mf := by
    rw [← C.card_MM]; exact Subgroup.card_dvd_of_le (C.MM_le_Mf ht' hM)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * z}) = k := ⟨_, rfl⟩
  rw [hk] at hcard hd9 hle9
  have hk3 : 3 ∣ k := by
    rw [hcard] at h81
    omega
  have hk9 : k = 9 ∨ k = 3 := by
    interval_cases k <;> first | omega | (norm_num at hd9)
  rcases hk9 with rfl | rfl
  · refine ⟨hk, ?_⟩
    rw [hcard]
  · exfalso
    have hcardMf : Nat.card ↥Mf = 81 := by rw [hcard]
    have hMM : M₁ ⊔ Subgroup.zpowers b = Mf :=
      Subgroup.eq_of_le_of_card_ge (C.MM_le_Mf ht' hM) (by rw [C.card_MM, hcardMf])
    apply C.not_le_norm_a
    rw [← hM.sup, ← hMM]
    refine sup_le C.norm_a_MM ?_
    apply Subgroup.closure_le _ |>.mpr
    intro e he
    rcases he with rfl | rfl
    · rw [C.norm_a]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [C.norm_a]; exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr C.comm_za)

theorem Core.t'_M₁ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {x : G} (hx : x ∈ M₁) : t' * x * t'⁻¹ ∈ M₁ := by
  rcases ht' with rfl | rfl
  · exact C.M₁_t x hx
  · have e : t * z * x * (t * z)⁻¹ = t * (z * x * z⁻¹) * t⁻¹ := by group
    rw [e]; exact C.M₁_t _ (C.z_conj_M₁ hx)

theorem Core.t'_inv_b (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) : t' * b⁻¹ * t'⁻¹ = b := by
  have h := C.t'_b ht'
  calc t' * b⁻¹ * t'⁻¹ = (t' * b * t'⁻¹)⁻¹ := by group
    _ = b := by rw [h, inv_inv]

theorem Core.bM₁ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} (hx : x ∈ M₁) :
    b * x * b⁻¹ ∈ M₁ :=
  (Subgroup.mem_normalizer_iff.mp C.b_mem_norm_M₁ x).mp hx

theorem Core.bM₁' (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} (hx : x ∈ M₁) :
    b⁻¹ * x * b ∈ M₁ := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ C.b_mem_norm_M₁) x).mp hx
  rwa [inv_inv] at h

theorem Core.t'_mod_M₁ [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) {x : G} (hx : x ∈ M₁) : t' * x * t'⁻¹ * x ∈ wOne C := by
  have hn : t' * x * t'⁻¹ ∈ M₁ := C.t'_M₁ ht' hx
  have hy : t' * (t' * x * t'⁻¹ * x) * t'⁻¹ = t' * x * t'⁻¹ * x := by
    calc t' * (t' * x * t'⁻¹ * x) * t'⁻¹
        = (t' * (t' * x * t'⁻¹) * t'⁻¹) * (t' * x * t'⁻¹) := by group
      _ = x * (t' * x * t'⁻¹) := by rw [inv_conj_involution (C.t'_mul ht')]
      _ = (t' * x * t'⁻¹) * x := C.M₁_comm x hx _ hn
  have hyM : t' * x * t'⁻¹ * x ∈ M₁ := M₁.mul_mem hn hx
  have hyc : t' * x * t'⁻¹ * x ∈ Subgroup.centralizer {t'} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (t' * x * t'⁻¹ * x) * t' = (t' * (t' * x * t'⁻¹ * x) * t'⁻¹) * t' := by rw [hy]
      _ = t' * (t' * x * t'⁻¹ * x) := by group
  have hM1 : M₁ ≤ Mf := le_trans le_sup_left (C.MM_le_Mf ht' hM)
  rw [← C.Mf_inf_cent_t' ht' hW hM]
  exact Subgroup.mem_inf.mpr ⟨hM1 hyM, hyc⟩

theorem Core.comm_M₁_b [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) {m : G} (hm : m ∈ M₁) :
    b * m * b⁻¹ * m⁻¹ ∈ wOne C := by
  have hpM : b * m * b⁻¹ ∈ M₁ := C.bM₁ hm
  have hcM : b * m * b⁻¹ * m⁻¹ ∈ M₁ := M₁.mul_mem hpM (M₁.inv_mem hm)
  obtain ⟨w₁, hw₁W, hw₁⟩ : ∃ w ∈ wOne C, w = t' * m * t'⁻¹ * m :=
    ⟨_, C.t'_mod_M₁ ht' hW hM hm, rfl⟩
  obtain ⟨w₂, hw₂W, hw₂⟩ : ∃ w ∈ wOne C,
      w = t' * (b * m * b⁻¹ * m⁻¹) * t'⁻¹ * (b * m * b⁻¹ * m⁻¹) :=
    ⟨_, C.t'_mod_M₁ ht' hW hM hcM, rfl⟩
  have hw₁M : w₁ ∈ M₁ := ((mem_wOne C).mp hw₁W).1.1
  have hw₁b : w₁ * b = b * w₁ := ((mem_wOne C).mp hw₁W).2
  have hw₂M : w₂ ∈ M₁ := ((mem_wOne C).mp hw₂W).1.1
  have hw₂b : w₂ * b = b * w₂ := ((mem_wOne C).mp hw₂W).2
  have hE1 : t' * m * t'⁻¹ = w₁ * m⁻¹ := by rw [hw₁]; group
  have hE1' : t' * m⁻¹ * t'⁻¹ = m * w₁⁻¹ := by
    calc t' * m⁻¹ * t'⁻¹ = (t' * m * t'⁻¹)⁻¹ := by group
      _ = (w₁ * m⁻¹)⁻¹ := by rw [hE1]
      _ = m * w₁⁻¹ := by group
  have hbinv' : t' * b⁻¹ * t'⁻¹ = b := C.t'_inv_b ht'
  have hbm1M : b⁻¹ * m⁻¹ * b * m ∈ M₁ :=
    M₁.mul_mem (C.bM₁' (M₁.inv_mem hm)) hm
  have hE7 : t' * (b * m * b⁻¹ * m⁻¹) * t'⁻¹ = b⁻¹ * m⁻¹ * b * m := by
    calc t' * (b * m * b⁻¹ * m⁻¹) * t'⁻¹
        = (t' * b * t'⁻¹) * (t' * m * t'⁻¹) * (t' * b⁻¹ * t'⁻¹) * (t' * m⁻¹ * t'⁻¹) := by group
      _ = b⁻¹ * (w₁ * m⁻¹) * b * (m * w₁⁻¹) := by
          rw [C.t'_b ht', hE1, hbinv', hE1']
      _ = b⁻¹ * m⁻¹ * b * m := by
          have hcomm1 : w₁ * (b⁻¹ * m⁻¹ * b * m) = (b⁻¹ * m⁻¹ * b * m) * w₁ :=
            C.M₁_comm w₁ hw₁M _ hbm1M
          have hbw : b⁻¹ * w₁ * b = w₁ := by
            calc b⁻¹ * w₁ * b = b⁻¹ * (w₁ * b) := by group
              _ = b⁻¹ * (b * w₁) := by rw [hw₁b]
              _ = w₁ := by group
          calc b⁻¹ * (w₁ * m⁻¹) * b * (m * w₁⁻¹)
              = (b⁻¹ * w₁ * b) * (b⁻¹ * m⁻¹ * b * m) * w₁⁻¹ := by group
            _ = w₁ * (b⁻¹ * m⁻¹ * b * m) * w₁⁻¹ := by rw [hbw]
            _ = (b⁻¹ * m⁻¹ * b * m) * w₁ * w₁⁻¹ := by rw [hcomm1]
            _ = b⁻¹ * m⁻¹ * b * m := by group
  have hpM' : (b * m * b⁻¹)⁻¹ ∈ M₁ := M₁.inv_mem hpM
  have hcomm2 : m * (b * m * b⁻¹)⁻¹ = (b * m * b⁻¹)⁻¹ * m := C.M₁_comm m hm _ hpM'
  have hcinv : (b * m * b⁻¹ * m⁻¹)⁻¹ = m * (b * m * b⁻¹)⁻¹ := by group
  have hstar0 : w₂ * (b * m * b⁻¹)⁻¹ * m = b⁻¹ * m⁻¹ * b * m := by
    calc w₂ * (b * m * b⁻¹)⁻¹ * m = w₂ * ((b * m * b⁻¹)⁻¹ * m) := by group
      _ = w₂ * (m * (b * m * b⁻¹)⁻¹) := by rw [hcomm2]
      _ = w₂ * (b * m * b⁻¹ * m⁻¹)⁻¹ := by rw [hcinv]
      _ = t' * (b * m * b⁻¹ * m⁻¹) * t'⁻¹ := by
          rw [hw₂]; group
      _ = b⁻¹ * m⁻¹ * b * m := hE7
  have hstar1 : w₂ * (b * m * b⁻¹)⁻¹ = b⁻¹ * m⁻¹ * b := mul_right_cancel hstar0
  have hstar : b⁻¹ * m * b = b * m * b⁻¹ * w₂⁻¹ := by
    calc b⁻¹ * m * b = (b⁻¹ * m⁻¹ * b)⁻¹ := by group
      _ = (w₂ * (b * m * b⁻¹)⁻¹)⁻¹ := by rw [hstar1]
      _ = b * m * b⁻¹ * w₂⁻¹ := by group
  have hkey : b * b * m * b⁻¹ * b⁻¹ = b⁻¹ * m * b := by
    have hb3 : b ^ 3 = 1 := C.b_cube
    have hb3' : b * b * b = 1 := by
      have h := hb3
      rw [pow_succ, pow_succ, pow_one] at h
      exact h
    have hbi : b⁻¹ = b * b := (eq_inv_iff_mul_eq_one.mpr hb3').symm
    rw [hbi]
    calc b * b * m * (b * b) * (b * b) = b * b * m * (b * b * b) * b := by group
      _ = b * b * m * b := by rw [hb3']; group
  have hbw2 : b * w₂⁻¹ * b⁻¹ = w₂⁻¹ := by
    calc b * w₂⁻¹ * b⁻¹ = (b * w₂ * b⁻¹)⁻¹ := by group
      _ = (w₂ * b * b⁻¹)⁻¹ := by rw [hw₂b]
      _ = w₂⁻¹ := by group
  have hE10 : b⁻¹ * m * b = m * w₂ := by
    have h1 : m = b * (b⁻¹ * m * b) * b⁻¹ := by group
    have h2 : b * (b * m * b⁻¹ * w₂⁻¹) * b⁻¹ = (b⁻¹ * m * b) * w₂⁻¹ := by
      calc b * (b * m * b⁻¹ * w₂⁻¹) * b⁻¹
          = (b * b * m * b⁻¹ * b⁻¹) * (b * w₂⁻¹ * b⁻¹) := by group
        _ = (b⁻¹ * m * b) * w₂⁻¹ := by rw [hkey, hbw2]
    have h3 : m = (b⁻¹ * m * b) * w₂⁻¹ := by
      calc m = b * (b⁻¹ * m * b) * b⁻¹ := h1
        _ = b * (b * m * b⁻¹ * w₂⁻¹) * b⁻¹ := by rw [hstar]
        _ = (b⁻¹ * m * b) * w₂⁻¹ := h2
    calc b⁻¹ * m * b = ((b⁻¹ * m * b) * w₂⁻¹) * w₂ := by group
      _ = m * w₂ := by rw [← h3]
  have hbm : b * m * b⁻¹ = m * w₂ * w₂ := by
    calc b * m * b⁻¹ = (b * m * b⁻¹ * w₂⁻¹) * w₂ := by group
      _ = (b⁻¹ * m * b) * w₂ := by rw [hstar]
      _ = m * w₂ * w₂ := by rw [hE10]
  have hmw : m * w₂ = w₂ * m := C.M₁_comm m hm w₂ hw₂M
  have hc2 : b * m * b⁻¹ * m⁻¹ = w₂ * w₂ := by
    rw [hbm]
    calc m * w₂ * w₂ * m⁻¹ = (m * w₂) * (w₂ * m⁻¹) := by group
      _ = (w₂ * m) * (w₂ * m⁻¹) := by rw [hmw]
      _ = w₂ * (m * w₂ * m⁻¹) := by group
      _ = w₂ * (w₂ * m * m⁻¹) := by rw [hmw]
      _ = w₂ * w₂ := by group
  rw [hc2]
  exact (wOne C).mul_mem hw₂W hw₂W

theorem comm_mod_of_closure {K Z : Subgroup G} {S : Set G} (hK : Subgroup.closure S = K)
    (hZ : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z) (hS : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ Z) :
    ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have step1 : ∀ s ∈ S, ∀ x ∈ K, x * s * x⁻¹ * s⁻¹ ∈ Z := by
    intro s hs x hx
    rw [← hK] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hS y hy s hs
    | one => simp
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      have hy₁K : y₁ ∈ K := hK ▸ hy₁
      have e : y₁ * y₂ * s * (y₁ * y₂)⁻¹ * s⁻¹
          = (y₁ * (y₂ * s * y₂⁻¹ * s⁻¹) * y₁⁻¹) * (y₁ * s * y₁⁻¹ * s⁻¹) := by group
      rw [e]
      exact Z.mul_mem (hZ y₁ hy₁K _ ih₂) ih₁
    | inv y hy ih =>
      have hyK : y ∈ K := hK ▸ hy
      have e : y⁻¹ * s * y⁻¹⁻¹ * s⁻¹ = y⁻¹ * (y * s * y⁻¹ * s⁻¹)⁻¹ * y⁻¹⁻¹ := by group
      rw [e]
      exact hZ y⁻¹ (K.inv_mem hyK) _ (Z.inv_mem ih)
  intro x hx y hy
  rw [← hK] at hy
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact step1 s hs x hx
  | one => simp
  | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
    have hy₁K : y₁ ∈ K := hK ▸ hy₁
    have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹
        = (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e]
    exact Z.mul_mem ih₁ (hZ y₁ hy₁K _ ih₂)
  | inv y hy ih =>
    have hyK : y ∈ K := hK ▸ hy
    have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact hZ y⁻¹ (K.inv_mem hyK) _ (Z.inv_mem ih)

theorem Core.MM_comm_mod [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) :
    ∀ x ∈ M₁ ⊔ Subgroup.zpowers b, ∀ y ∈ M₁ ⊔ Subgroup.zpowers b,
      x * y * x⁻¹ * y⁻¹ ∈ wOne C := by
  set S : Set G := (M₁ : Set G) ∪ {b} with hSdef
  have hK : Subgroup.closure S = M₁ ⊔ Subgroup.zpowers b := by
    rw [hSdef, Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  have hcentW : M₁ ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer ((wOne C : Subgroup G) : Set G) := by
    apply sup_le
    · intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact C.M₁_comm w (wOne_le_M₁ C hw) m hm
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact ((mem_wOne C).mp hw).2
  have hZ : ∀ k ∈ M₁ ⊔ Subgroup.zpowers b, ∀ w ∈ wOne C, k * w * k⁻¹ ∈ wOne C := by
    intro k hk w hw
    have hkc := hcentW hk
    rw [Subgroup.mem_centralizer_iff] at hkc
    have hwk := hkc w hw
    have e : k * w * k⁻¹ = w := by
      calc k * w * k⁻¹ = (w * k) * k⁻¹ := by rw [hwk]
        _ = w := by group
    rw [e]; exact hw
  have hS : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ wOne C := by
    intro s hs s' hs'
    rcases hs with hs | hs <;> rcases hs' with hs' | hs'
    · have hc : s * s' = s' * s := C.M₁_comm s hs s' hs'
      have e : s * s' * s⁻¹ * s'⁻¹ = 1 := by
        calc s * s' * s⁻¹ * s'⁻¹ = (s * s') * s⁻¹ * s'⁻¹ := rfl
          _ = (s' * s) * s⁻¹ * s'⁻¹ := by rw [hc]
          _ = 1 := by group
      rw [e]; exact (wOne C).one_mem
    · rw [Set.mem_singleton_iff.mp hs']
      have h := C.comm_M₁_b ht' hW hM hs
      have e : s * b * s⁻¹ * b⁻¹ = (b * s * b⁻¹ * s⁻¹)⁻¹ := by group
      rw [e]; exact (wOne C).inv_mem h
    · rw [Set.mem_singleton_iff.mp hs]
      exact C.comm_M₁_b ht' hW hM hs'
    · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp hs']
      have e : b * b * b⁻¹ * b⁻¹ = 1 := by group
      rw [e]; exact (wOne C).one_mem
  exact comm_mod_of_closure hK hZ hS

theorem Core.noncomm_b [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∃ m ∈ M₁, b * m * b⁻¹ * m⁻¹ ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hle : M₁ ≤ Subgroup.centralizer {b} := by
    intro m hm
    have h := hcon m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : b * m = (b * m * b⁻¹ * m⁻¹) * m * b := by group
    rw [h, one_mul] at e
    exact e.symm
  have hinf : M₁ ⊓ Subgroup.centralizer {b} = M₁ := inf_eq_left.mpr hle
  have h9 := C.card_M₁_cent_b
  rw [hinf, C.M₁_card] at h9
  omega

theorem Core.wOne_gen [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) :
    ∃ m ∈ M₁, wOne C = Subgroup.zpowers (b * m * b⁻¹ * m⁻¹) := by
  obtain ⟨m, hm, hne⟩ := C.noncomm_b
  refine ⟨m, hm, ?_⟩
  have hc0W : b * m * b⁻¹ * m⁻¹ ∈ wOne C := C.comm_M₁_b ht' hW hM hm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : (b * m * b⁻¹ * m⁻¹) ^ 3 = 1 := C.M₁_cube _ (wOne_le_M₁ C hc0W)
  have hord : orderOf (b * m * b⁻¹ * m⁻¹) = 3 := orderOf_eq_prime hcube hne
  have h1 : Subgroup.zpowers (b * m * b⁻¹ * m⁻¹) ≤ wOne C := Subgroup.zpowers_le.mpr hc0W
  have h2 : Nat.card ↥(wOne C) ≤ Nat.card ↥(Subgroup.zpowers (b * m * b⁻¹ * m⁻¹)) := by
    rw [Nat.card_zpowers, hord, C.card_wOne]
  exact (Subgroup.eq_of_le_of_card_ge h1 h2).symm

theorem Core.MM_commutator [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) :
    ⁅M₁ ⊔ Subgroup.zpowers b, M₁ ⊔ Subgroup.zpowers b⁆ = wOne C := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact C.MM_comm_mod ht' hW hM x hx y hy
  · obtain ⟨m, hm, hW₁⟩ := C.wOne_gen ht' hW hM
    rw [hW₁, Subgroup.zpowers_le]
    have hb : b ∈ M₁ ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hmM : m ∈ M₁ ⊔ Subgroup.zpowers b := Subgroup.mem_sup_left hm
    have := Subgroup.commutator_mem_commutator hb hmM
    rw [commutatorElement_def] at this
    exact this

theorem normal_of_index_three_243 [Finite G] {K H : Subgroup G} (hHK : H ≤ K)
    (hK : Nat.card ↥K = 243) (hH : Nat.card ↥H = 81) :
    ∀ g ∈ K, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
  have hidx : (H.subgroupOf K).index = (Nat.card ↥K).minFac := by
    have h1 := Subgroup.index_mul_card (H.subgroupOf K)
    have h2 : Nat.card ↥(H.subgroupOf K) = 81 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hH]
    rw [h2, hK] at h1
    have h4 : (H.subgroupOf K).index = 3 := by
      have h5 : 81 * (H.subgroupOf K).index = 81 * 3 := by linarith [h1]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h5
    rw [h4, hK]
    norm_num
  have hN : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_minFac_card hidx
  intro g hg h hh
  have hmem := Subgroup.Normal.conj_mem hN (⟨h, hHK hh⟩ : ↥K) (Subgroup.mem_subgroupOf.mpr hh)
    (⟨g, hg⟩ : ↥K)
  have h' := Subgroup.mem_subgroupOf.mp hmem
  simpa using h'

theorem Core.MM_normal_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {Mf : Subgroup G} (hM : MfData C Mf)
    (hMf : Nat.card ↥Mf = 243) :
    ∀ g ∈ Mf, ∀ u ∈ M₁ ⊔ Subgroup.zpowers b, g * u * g⁻¹ ∈ M₁ ⊔ Subgroup.zpowers b :=
  normal_of_index_three_243 (C.MM_le_Mf ht' hM) hMf C.card_MM

theorem fpf_inv_comm {Y : Type*} [Group Y] [Finite Y] (α : Y →* Y) (hinv : ∀ y, α (α y) = y)
    (hfix : ∀ y, α y = y → y = 1) : (∀ y, α y = y⁻¹) ∧ ∀ g h : Y, g * h = h * g := by
  have hinj : Function.Injective (fun y : Y => y⁻¹ * α y) := by
    intro y y' hyy'
    simp only at hyy'
    have hk : α (y' * y⁻¹) = y' * y⁻¹ := by
      rw [map_mul, map_inv]
      have h1 : α y' = y' * (y'⁻¹ * α y') := by group
      have h2 : α y = y * (y⁻¹ * α y) := by group
      rw [h1, h2, hyy']
      group
    have h3 := hfix _ hk
    exact (mul_inv_eq_one.mp h3).symm
  have hsurj : Function.Surjective (fun y : Y => y⁻¹ * α y) :=
    Finite.injective_iff_surjective.mp hinj
  have hα : ∀ y, α y = y⁻¹ := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    simp only at hx
    subst hx
    rw [map_mul, map_inv, hinv]
    group
  refine ⟨hα, fun g h => ?_⟩
  have hgh : α (g * h) = (g * h)⁻¹ := hα _
  rw [map_mul, hα, hα] at hgh
  have h3 : g⁻¹ * h⁻¹ = h⁻¹ * g⁻¹ := by rw [hgh, mul_inv_rev]
  calc g * h = (h⁻¹ * g⁻¹)⁻¹ := by group
    _ = (g⁻¹ * h⁻¹)⁻¹ := by rw [h3]
    _ = h * g := by group

theorem Core.Mf_fix_wOne [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) {x w : G} (hx : x ∈ Mf) (hw : w ∈ wOne C)
    (h : t' * x * t'⁻¹ = x * w) : x ∈ wOne C := by
  have hzw : z * w * z⁻¹ = w⁻¹ := ((mem_wOne C).mp hw).1.2
  have hu : t' * z * x * (t' * z)⁻¹ = z * x * z⁻¹ * w⁻¹ := by
    calc t' * z * x * (t' * z)⁻¹ = z * (t' * x * t'⁻¹) * z⁻¹ := by rw [C.t'_z ht']; group
      _ = z * (x * w) * z⁻¹ := by rw [h]
      _ = z * x * z⁻¹ * (z * w * z⁻¹) := by group
      _ = z * x * z⁻¹ * w⁻¹ := by rw [hzw]
  have hcx := C.u_comm_Pb ht' hW (hM.le hx)
  have hzx : z * x * z⁻¹ = (t' * z * x * (t' * z)⁻¹ * x⁻¹) * x * w := by
    rw [hu]; group
  have hp : x⁻¹ * (t' * z * x * (t' * z)⁻¹ * x⁻¹) * x * w ∈ Pb := by
    have h1 := conj_mem_of_norm (Subgroup.inv_mem _ (hM.le hx)) hcx
    rw [inv_inv] at h1
    exact Pb.mul_mem h1 (C.wOne_le_Pb hw)
  obtain ⟨p, hpPb, hzxp⟩ : ∃ p ∈ Pb, z * x * z⁻¹ = x * p :=
    ⟨_, hp, by rw [hzx]; group⟩
  have hy := C.lift_z hpPb hzxp
  have hyM : x * p ^ 2 ∈ Mf := Mf.mul_mem hx (Mf.pow_mem (C.Pb_le_Mf ht' hM hpPb) 2)
  have hyPb := C.fix_z_mem_Pb ht' hM hyM hy
  have hxPb : x ∈ Pb := by
    have h2 := Pb.mul_mem hyPb (Pb.inv_mem (Pb.pow_mem hpPb 2))
    rwa [mul_inv_cancel_right] at h2
  obtain ⟨w₀, hw₀, q, hq, hxq⟩ := C.Pb_decomp hxPb
  have hq' : t' * q * t'⁻¹ = q⁻¹ := C.t_inv_P ht' hq
  have hw₀' : t' * w₀ * t'⁻¹ = w₀ := hW w₀ hw₀
  have hcalc : t' * x * t'⁻¹ = w₀ * q⁻¹ := by
    rw [← hxq]
    calc t' * (w₀ * q) * t'⁻¹ = (t' * w₀ * t'⁻¹) * (t' * q * t'⁻¹) := by group
      _ = w₀ * q⁻¹ := by rw [hw₀', hq']
  have hqw : q⁻¹ = q * w := by
    have h1 : w₀ * q⁻¹ = w₀ * (q * w) := by
      calc w₀ * q⁻¹ = t' * x * t'⁻¹ := hcalc.symm
        _ = x * w := h
        _ = w₀ * q * w := by rw [← hxq]
        _ = w₀ * (q * w) := by group
    exact mul_left_cancel h1
  have hq3 : q ^ 3 = 1 := C.P_cube hq
  have h4 : q⁻¹ * q⁻¹ = q := by
    have h5 : q⁻¹ * q⁻¹ * q⁻¹ = 1 := by
      calc q⁻¹ * q⁻¹ * q⁻¹ = (q ^ 3)⁻¹ := by group
        _ = 1 := by rw [hq3, inv_one]
    calc q⁻¹ * q⁻¹ = (q⁻¹ * q⁻¹ * q⁻¹) * q := by group
      _ = q := by rw [h5, one_mul]
  have hw' : q⁻¹ * q⁻¹ = w := by
    calc q⁻¹ * q⁻¹ = q⁻¹ * (q * w) := by rw [← hqw]
      _ = w := by group
  have hwq : w = q := by rw [← hw', h4]
  have hqW : q ∈ wOne C := hwq ▸ hw
  have hzq : z * q * z⁻¹ = q := C.z_fix_P hq
  have hzq' : z * q * z⁻¹ = q⁻¹ := ((mem_wOne C).mp hqW).1.2
  have hqq : q * q = 1 := mul_eq_one_iff_eq_inv.mpr (hzq.symm.trans hzq')
  have hq1 : q = 1 := eq_one_of_sq_cube hqq hq3
  rw [← hxq, hq1, mul_one]
  exact hw₀

theorem Core.wOne_conj_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) (hMf : Nat.card ↥Mf = 243) :
    ∀ x ∈ Mf, ∀ w ∈ wOne C, x * w * x⁻¹ ∈ wOne C := by
  intro x hx w hw
  obtain ⟨m, hm, hW₁⟩ := C.wOne_gen ht' hW hM
  have hc0 : x * (b * m * b⁻¹ * m⁻¹) * x⁻¹ ∈ wOne C := by
    have hbM := C.MM_normal_Mf ht' hM hMf x hx b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    have hmM := C.MM_normal_Mf ht' hM hMf x hx m (Subgroup.mem_sup_left hm)
    have e : x * (b * m * b⁻¹ * m⁻¹) * x⁻¹
        = (x * b * x⁻¹) * (x * m * x⁻¹) * (x * b * x⁻¹)⁻¹ * (x * m * x⁻¹)⁻¹ := by
      group
    rw [e, ← C.MM_commutator ht' hW hM]
    exact Subgroup.commutator_mem_commutator hbM hmM
  rw [hW₁] at hw hc0 ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hc0 k

theorem Core.Mf_commutator_le [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) (hMf : Nat.card ↥Mf = 243) :
    ∀ x ∈ Mf, ∀ y ∈ Mf, x * y * x⁻¹ * y⁻¹ ∈ wOne C := by
  have hWn := C.wOne_conj_Mf ht' hW hM hMf
  haveI hN : ((wOne C).subgroupOf Mf).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hWn (g : G) g.2 (n : G) hn
    simpa using this⟩
  have hE : t' ∈ Subgroup.closure ({t, z} : Set G) := by
    rcases ht' with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have htN : t' ∈ Subgroup.normalizer (Pb : Set G) := C.E_le_norm_Pb hE
  have hMconj : ∀ x : ↥Mf, t' * (x : G) * t'⁻¹ ∈ Mf := fun x => hM.conj t' htN x x.2
  let φ : ↥Mf →* ↥Mf :=
    { toFun := fun x => ⟨t' * (x : G) * t'⁻¹, hMconj x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφN : (wOne C).subgroupOf Mf ≤ ((wOne C).subgroupOf Mf).comap φ := by
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    show t' * (n : G) * t'⁻¹ ∈ wOne C
    rw [hW _ (Subgroup.mem_subgroupOf.mp hn)]
    exact Subgroup.mem_subgroupOf.mp hn
  obtain ⟨α, hα_mk⟩ : ∃ α : (↥Mf ⧸ (wOne C).subgroupOf Mf) →* (↥Mf ⧸ (wOne C).subgroupOf Mf),
      ∀ x : ↥Mf, α (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
    ⟨QuotientGroup.map _ _ φ hφN, fun x => QuotientGroup.map_mk _ _ _ _ _⟩
  have hαα : ∀ y, α (α y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hα_mk, hα_mk]
    congr 1
    apply Subtype.ext
    show t' * (t' * (x : G) * t'⁻¹) * t'⁻¹ = x
    exact inv_conj_involution (C.t'_mul ht')
  have hfix : ∀ y, α y = y → y = 1 := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hα_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hy
    have hy' : (x : G)⁻¹ * (t' * (x : G) * t'⁻¹) ∈ wOne C := by
      have h0 := (wOne C).inv_mem hy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h0
      exact h0
    have hxW : (x : G) ∈ wOne C :=
      C.Mf_fix_wOne ht' hW hM x.2 hy' (by group)
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hxW
  obtain ⟨-, hcomm⟩ := fpf_inv_comm α hαα hfix
  intro x hx y hy
  have hc := hcomm (QuotientGroup.mk (⟨x⁻¹, Mf.inv_mem hx⟩ : ↥Mf))
    (QuotientGroup.mk (⟨y⁻¹, Mf.inv_mem hy⟩ : ↥Mf))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hc
  have hyx : y * x * y⁻¹ * x⁻¹ ∈ wOne C := by
    have e : y * x * y⁻¹ * x⁻¹ = (x⁻¹ * y⁻¹)⁻¹ * (y⁻¹ * x⁻¹) := by group
    rw [e]
    simpa using hc
  have e2 : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [e2]
  exact (wOne C).inv_mem hyx

theorem Core.Mf_derived [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) (hMf : Nat.card ↥Mf = 243) :
    ⁅Mf, Mf⁆ = wOne C := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact C.Mf_commutator_le ht' hW hM hMf x hx y hy
  · rw [← C.MM_commutator ht' hW hM]
    exact Subgroup.commutator_mono (C.MM_le_Mf ht' hM) (C.MM_le_Mf ht' hM)

theorem Core.M₁_normal_Mf [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) {Mf : Subgroup G}
    (hM : MfData C Mf) (hMf : Nat.card ↥Mf = 243) :
    ∀ g ∈ Mf, ∀ m ∈ M₁, g * m * g⁻¹ ∈ M₁ := by
  intro g hg m hm
  have hc : g * m * g⁻¹ * m⁻¹ ∈ wOne C :=
    C.Mf_commutator_le ht' hW hM hMf g hg m (le_trans le_sup_left (C.MM_le_Mf ht' hM) hm)
  have e : g * m * g⁻¹ = (g * m * g⁻¹ * m⁻¹) * m := by group
  rw [e]
  exact M₁.mul_mem (wOne_le_M₁ C hc) hm

end Part2

end CFSG.GH74.QTGen4.Recog.G23.P7.B27N

namespace CFSG.GH74.QTGen4.Recog.G23.P7

theorem leafB27Normalizer [G23Leaf LeafGL3Facts] : LeafB27Normalizer := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm hS hF hO hL hPb hM₁ hM₂
  have hGL : B27N.GL3Trans := (G23Leaf.out (L := LeafGL3Facts)).1
  have C := B27N.core_of_leaf hS hF hO hL hPb hM₁ hM₂
  obtain ⟨t', ht', hW⟩ := C.exists_t'
  obtain ⟨Mf, h1, h2, h3, h4, h5⟩ := C.exists_Mf ht' hW
  have hM : B27N.MfData C Mf := ⟨h1, h2, h3, h4, h5⟩
  have hthree : IsPGroup 3 ↥Mf := C.isPGroup_Mf hGL hM.le hM.odd
  have hcard := C.card_Mf ht' hW hM
  have hMf := hcard.2
  refine ⟨B27N.wOne C, Mf, t', ?_⟩
  exact
    { t'_mem := ht'
      card_W₁ := C.card_wOne
      W₁_le := fun x hx => Subgroup.mem_inf.mpr
        ⟨B27N.wOne_le_M₁ C hx, Subgroup.mem_centralizer_singleton_iff.mpr
          ((B27N.mem_wOne C).mp hx).2⟩
      W₁_inv := fun w hw => ((B27N.mem_wOne C).mp hw).1.2
      W₁_cent := hW
      Pb_eq := C.Pb_eq_sup
      cent_Pb := C.cent_Pb_eq
      compl := ⟨hM.le, C.E_le_norm_Pb, hM.conj, hM.odd, hM.inf, hM.sup⟩
      three := hthree
      card_Mf := hMf
      M₁_normal := C.M₁_normal_Mf ht' hW hM hMf
      M₁_le := le_trans le_sup_left (C.MM_le_Mf ht' hM)
      s₂_mem := C.MM_le_Mf ht' hM (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      inf_norm := C.Mf_inf_norm_a ht' hM
      not_le_norm := C.not_le_norm_a
      cent_t' := C.Mf_inf_cent_t' ht' hW hM
      derived := C.Mf_derived ht' hW hM hMf
      card_cent_t'z := hcard.1 }

end CFSG.GH74.QTGen4.Recog.G23.P7

end
