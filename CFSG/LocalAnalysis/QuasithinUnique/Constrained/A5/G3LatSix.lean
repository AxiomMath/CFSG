module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5Six
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Direct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLatAlt

public section

namespace CFSG.QuasithinUnique.A5.G3

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def NoDelta5Norm (X : Type) [Group X] : Prop :=
  ∀ T B : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Subgroup.normalizer (B : Set X) →
    ¬ IsDelta5Group ↥B

section Transport

variable {A C : Type} [Group A] [Group C]

theorem mem_map_iff_symm (f : A ≃* C) (B : Subgroup A) (c : C) :
    c ∈ B.map f.toMonoidHom ↔ f.symm c ∈ B := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨f.symm c, h, by simp⟩

theorem delta5_pullback (e : C ≃* A) {T B : Subgroup A}
    (hTB : T ≤ Subgroup.normalizer (B : Set A)) (hD : IsDelta5Group ↥B) :
    T.map e.symm.toMonoidHom ≤ Subgroup.normalizer ((B.map e.symm.toMonoidHom : Subgroup C) :
      Set C) ∧ IsDelta5Group ↥(B.map e.symm.toMonoidHom) := by
  refine ⟨?_, hD.of_equiv (B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have h1 := Subgroup.mem_normalizer_iff.mp (hTB ht) (e b)
  have hm : ∀ z : C, z ∈ B.map e.symm.toMonoidHom ↔ e z ∈ B := by
    intro z
    rw [mem_map_iff_symm]
    simp
  rw [hm, hm]
  have : e (e.symm.toMonoidHom t * b * (e.symm.toMonoidHom t)⁻¹) = t * e b * t⁻¹ := by
    simp
  rw [this]
  exact h1

theorem NoDelta5Norm.of_mulEquiv (e : C ≃* A) (h : NoDelta5Norm C) : NoDelta5Norm A := by
  intro T B hT hTB hD
  obtain ⟨h1, h2⟩ := delta5_pullback e hTB hD
  refine h (T.map e.symm.toMonoidHom) (B.map e.symm.toMonoidHom) ?_ h1 h2
  have := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T)
    (Y := ⊤)).mpr hT
  rwa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at this

end Transport

theorem exists_conj_eq_of_isSylowTwoOf {M : Type*} [Group M] [Finite M] {U T : Subgroup M}
    (hU : IsSylowTwoOf U ⊤) (hT : IsSylowTwoOf T ⊤) :
    ∃ g : M, U.map (MulAut.conj g).toMonoidHom = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUi : ¬ 2 ∣ U.index := by
    have h1 : (U.subgroupOf (⊤ : Subgroup M)).index = U.index := Subgroup.relIndex_top_right U
    rw [← h1]
    exact hU.2.2
  have hTi : ¬ 2 ∣ T.index := by
    have h1 : (T.subgroupOf (⊤ : Subgroup M)).index = T.index := Subgroup.relIndex_top_right T
    rw [← h1]
    exact hT.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (hU.2.1.toSylow hUi) (hT.2.1.toSylow hTi)
  refine ⟨g, ?_⟩
  have hg' := congrArg (fun P : Sylow 2 M => (P : Subgroup M)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at hg'
  exact hg'

theorem noDelta5Norm_of_sylow {M : Type} [Group M] [Finite M] {U : Subgroup M}
    (hU : IsSylowTwoOf U ⊤)
    (h : ∀ B : Subgroup M, U ≤ Subgroup.normalizer (B : Set M) → ¬ IsDelta5Group ↥B) :
    NoDelta5Norm M := by
  intro T B hT hTB hD
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isSylowTwoOf hU hT
  obtain ⟨h1, h2⟩ := delta5_pullback (MulAut.conj g) hTB hD
  have hU' : T.map (MulAut.conj g).symm.toMonoidHom = U := by
    rw [← hg, Subgroup.map_map]
    have : ((MulAut.conj g).symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id M := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rw [hU'] at h1
  exact h _ h1 h2

theorem not_isDelta5_of_latCert {n : ℕ} (c : LatCert (Perm (Fin n))) (hck : c.check RN.enc = true)
    (htle : c.tleOK RN.enc = true) (hk : c.sizes.headD 0 = 2 ^ 7) {m : ℕ}
    (hm : c.msize = 2 ^ 7 * m) (hodd : ¬ 2 ∣ m)
    (hA : ∀ (j : ℕ) (hj : j < (c.tGens :: c.lat).length), c.sizes.getD j 0 = 1920 →
      ∃ A : Subgroup (Perm (Fin n)), A ≤ Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ∧
        Nat.card A = 960 ∧ ⁅A, A⁆ = A ∧ ∀ g ∈ A, orderOf g ≠ 6)
    (B : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens})) (hD : IsDelta5Group ↥B)
    (hUB : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}) ≤
      Subgroup.normalizer (B : Set ↥(Subgroup.closure {g | g ∈ c.mGens}))) : False := by
  classical
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hTM : Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.closure {g | g ∈ c.mGens} :=
    c.t_le_m (rawIsEnc n) hcl htle
  have hUsyl := c.isSylowTwoOf_top (rawIsEnc n) hck (k := 7) hk hm hodd
  have hUcard : Nat.card ↥((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv,
      c.card_t (rawIsEnc n) hcl hsz, hk]
  obtain ⟨j, hj1, hj2, -, -⟩ := delta5_sup_data hUsyl hD hUB
  have hj : j = 1 := by
    have h2 : 2 ^ (6 + j) = 2 ^ 7 := by rw [← hj1, hUcard]
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hj
  have hYcard : Nat.card ↥(B ⊔ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})) = 1920 := by rw [hj2]; norm_num
  obtain ⟨i, hi, hLM, hYL, hcardi⟩ := c.overgroup_cases_idx (rawIsEnc n) hck
    (B ⊔ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}))
    le_sup_right
  have hLcard : Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}) = 1920 := by
    rw [hYL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv] at hYcard
    exact hYcard
  have hsizes : c.sizes.getD i 0 = 1920 := by rw [← hcardi]; exact hLcard
  obtain ⟨A, hAL', hAcard, hAperf, hAsix⟩ := hA i hi hsizes
  have hY₀ : (B ⊔ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})).map (Subgroup.closure {g | g ∈ c.mGens}).subtype =
        Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]} := by
    rw [hYL]
    exact Subgroup.map_subgroupOf_eq_of_le hLM
  have hB₀Y₀ : B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype ≤
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]} := by
    rw [← hY₀]
    exact Subgroup.map_mono le_sup_left
  have hB₀card : Nat.card (B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype) = 960 := by
    rw [Subgroup.card_map_of_injective (Subgroup.closure {g | g ∈ c.mGens}).subtype_injective]
    exact hD.card
  have hY₀card : Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}) =
      2 * Nat.card (B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype) := by
    rw [hLcard, hB₀card]
  have hcomm := commutator_le_of_card_eq_two_mul hB₀Y₀ hY₀card
  have hAB : A ≤ B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype := by
    calc A = ⁅A, A⁆ := hAperf.symm
      _ ≤ ⁅Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]},
            Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}⁆ :=
          Subgroup.commutator_mono hAL' hAL'
      _ ≤ _ := hcomm
  have hAB' : A = B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype :=
    Subgroup.eq_of_le_of_card_ge hAB (by rw [hB₀card, hAcard])
  obtain ⟨g, hg⟩ := hD.exists_orderOf_six
  have hg' : ((Subgroup.closure {g | g ∈ c.mGens}).subtype (g : ↥(Subgroup.closure {g | g ∈
      c.mGens}))) ∈ B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype := ⟨g, g.2, rfl⟩
  apply hAsix _ (hAB' ▸ hg')
  show orderOf (((g : ↥B) : ↥(Subgroup.closure {g | g ∈ c.mGens})) : Perm (Fin n)) = 6
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact hg

theorem not_isDelta5_of_latCert_amb {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hck : c.check RN.enc = true) (htle : c.tleOK RN.enc = true) (hk : c.sizes.headD 0 = 2 ^ 7)
    {m : ℕ}
    (hm : c.msize = 2 ^ 7 * m) (hodd : ¬ 2 ∣ m)
    (hA : ∀ (j : ℕ) (hj : j < (c.tGens :: c.lat).length), c.sizes.getD j 0 = 1920 →
      ∃ A : Subgroup (Perm (Fin n)), A ≤ Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ∧
        Nat.card A = 960 ∧ ⁅A, A⁆ = A ∧ ∀ g ∈ A, orderOf g ≠ 6)
    (B : Subgroup (Perm (Fin n))) (hBM : B ≤ Subgroup.closure {g | g ∈ c.mGens})
    (hD : IsDelta5Group ↥B)
    (hTB : Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.normalizer (B : Set (Perm (Fin n)))) :
    False :=
  not_isDelta5_of_latCert c hck htle hk hm hodd hA (B.subgroupOf (Subgroup.closure {g | g ∈ c.mGens}))
    (hD.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm) (subgroupOf_le_normalizer hTB)

theorem card_mem_sizes_of_latCert {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hck : c.check RN.enc = true) (Z : Subgroup (Perm (Fin n)))
    (hTZ : Subgroup.closure {g | g ∈ c.tGens} ≤ Z)
    (hZM : Z ≤ Subgroup.closure {g | g ∈ c.mGens}) : Nat.card Z ∈ c.sizes := by
  obtain ⟨L, -, hLM, hZL, hLcard⟩ := c.overgroup_cases (rawIsEnc n) hck
    (Z.subgroupOf (Subgroup.closure {g | g ∈ c.mGens})) (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hTZ hx)
  have h1 : Nat.card Z = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv, hZL,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
  rw [h1]
  exact hLcard

theorem noDelta5Norm_of_latSix {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hck : c.check RN.enc = true) (htle : c.tleOK RN.enc = true) (hk : c.sizes.headD 0 = 2 ^ 7)
    {m : ℕ}
    (hm : c.msize = 2 ^ 7 * m) (hodd : ¬ 2 ∣ m) (ds : List (AData n))
    (hs : latSixCheck c ds = true) :
    NoDelta5Norm ↥(Subgroup.closure {g | g ∈ c.mGens}) := by
  have hUsyl := c.isSylowTwoOf_top (rawIsEnc n) hck (k := 7) hk hm hodd
  exact noDelta5Norm_of_sylow hUsyl fun B hUB hD =>
    not_isDelta5_of_latCert c hck htle hk hm hodd (hA_of_latSixCheck c
      (LatCert.closedOK_of_check hck) ds hs) B hD hUB

end CFSG.QuasithinUnique.A5.G3
