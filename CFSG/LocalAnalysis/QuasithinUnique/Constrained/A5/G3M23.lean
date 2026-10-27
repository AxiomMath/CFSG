module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Orbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Cert1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Cert2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Mathieu

public section

namespace CFSG.QuasithinUnique.A5.G3.M23

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.Quasithin
open scoped Pointwise

abbrev Mg : Subgroup (Perm (Fin 23)) := CFSG.Blueprint.NativeSporadic.M23

theorem card_Mg
    : Nat.card ↥Mg = 10200960 := by
  have h := CFSG.M23.M23Group.card_M23
  rw [← Nat.card_eq_fintype_card] at h
  change Nat.card ↥CFSG.Blueprint.NativeSporadic.M23 = 10200960
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact h

theorem four_pretrans
    : MulAction.IsMultiplyPretransitive ↥Mg (Fin 23) 4 :=
  (congrArg (fun H : Subgroup (Perm (Fin 23)) => MulAction.IsMultiplyPretransitive ↥H (Fin 23) 4)
    CFSG.Sporadic.Mathieu.nativeM23_eq).mpr CFSG.M23.M23Group.four_pretransitive

theorem two_pretrans
    : MulAction.IsMultiplyPretransitive ↥Mg (Fin 23) 2 := by
  have := four_pretrans
  exact MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 4) (by norm_num) (by simp)

theorem one_pretrans
    : MulAction.IsPretransitive ↥Mg (Fin 23) := by
  have := four_pretrans
  have h1 : MulAction.IsMultiplyPretransitive ↥Mg (Fin 23) 1 :=
    MulAction.isMultiplyPretransitive_of_le (m := 1) (n := 4) (by norm_num) (by simp)
  exact MulAction.is_one_pretransitive_iff.mp h1

@[expose] def pair : Set.powersetCard (Fin 23) 2 :=
  Set.powersetCard.ofCard (s := ({19, 20} : Finset (Fin 23))) (by decide)

theorem card_stab2
    : Nat.card (MulAction.stabilizer ↥Mg pair) = 40320 := by
  have h2 := two_pretrans
  have hpt : MulAction.IsPretransitive ↥Mg (Set.powersetCard (Fin 23) 2) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive ↥Mg h2
  have hnc : Nat.card (MulAction.orbit ↥Mg pair) = 253 := by
    rw [MulAction.orbit_eq_univ, Nat.card_univ, Set.powersetCard.card]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥Mg pair)
  have h3 : (MulAction.stabilizer ↥Mg pair).index = Nat.card (MulAction.orbit ↥Mg pair) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [h3, hnc, card_Mg] at h1
  omega

theorem mGens2_stab : ∀ g ∈ mGens2,
    ({19, 20} : Finset (Fin 23)).image (fun x => g x) = {19, 20} := by
  intro g hg
  simp only [mGens2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> decide +kernel

theorem smul_pair_val (y : ↥Mg) :
    (y • pair).val = ({19, 20} : Finset (Fin 23)).image (fun x => (y : Perm (Fin 23)) x) := by
  show y • ({19, 20} : Finset (Fin 23)) = _
  rw [Finset.smul_finset_def]
  rfl

theorem mem_stab2_iff (y : ↥Mg) :
    y ∈ MulAction.stabilizer ↥Mg pair ↔ ((y : Perm (Fin 23)) 19 ∈ ({19, 20} : Finset (Fin 23)) ∧
      (y : Perm (Fin 23)) 20 ∈ ({19, 20} : Finset (Fin 23))) := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, smul_pair_val]
  have hp : pair.val = ({19, 20} : Finset (Fin 23)) := rfl
  rw [hp]
  constructor
  · intro h
    constructor
    · have : (y : Perm (Fin 23)) 19 ∈ ({19, 20} : Finset (Fin 23)).image
        (fun x => (y : Perm (Fin 23)) x) := Finset.mem_image_of_mem _ (by simp)
      rwa [h] at this
    · have : (y : Perm (Fin 23)) 20 ∈ ({19, 20} : Finset (Fin 23)).image
        (fun x => (y : Perm (Fin 23)) x) := Finset.mem_image_of_mem _ (by simp)
      rwa [h] at this
  · rintro ⟨h19, h20⟩
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [Finset.card_image_of_injective _ (y : Perm (Fin 23)).injective]

theorem stab2_le_closure
    : ∀ y ∈ Mg, y 19 ∈ ({19, 20} : Finset (Fin 23)) →
    y 20 ∈ ({19, 20} : Finset (Fin 23)) → y ∈ Subgroup.closure {g | g ∈ mGens2} := by
  intro y hy h19 h20
  have hcl : C2.cert.closedOK RN.enc = true := LatCert.closedOK_of_check C2.cert_check
  have hsz : C2.cert.sizesOK RN.enc = true := LatCert.sizesOK_of_check C2.cert_check
  have hcard : Nat.card (Subgroup.closure {g | g ∈ mGens2}) = 40320 :=
    C2.cert.card_m (rawIsEnc 23) hcl hsz
  have hW : Nat.card ((MulAction.stabilizer ↥Mg pair).map Mg.subtype) = 40320 := by
    rw [Subgroup.card_map_of_injective Mg.subtype_injective]
    exact card_stab2
  have hle : Subgroup.closure {g | g ∈ mGens2} ≤ (MulAction.stabilizer ↥Mg pair).map Mg.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    refine ⟨⟨g, mGens2_mem g hg⟩, (mem_stab2_iff _).mpr ?_, rfl⟩
    have h := mGens2_stab g hg
    constructor
    · have : g 19 ∈ ({19, 20} : Finset (Fin 23)).image (fun x => g x) :=
        Finset.mem_image_of_mem _ (by simp)
      rwa [h] at this
    · have : g 20 ∈ ({19, 20} : Finset (Fin 23)).image (fun x => g x) :=
        Finset.mem_image_of_mem _ (by simp)
      rwa [h] at this
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hcard])
  rw [heq]
  exact ⟨⟨y, hy⟩, (mem_stab2_iff _).mpr ⟨h19, h20⟩, rfl⟩

theorem mGens1_fix : ∀ g ∈ mGens1, g 0 = 0 := by
  intro g hg
  simp only [mGens1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> decide +kernel

theorem fix_le_closure1
    : ∀ y ∈ Mg, y 0 = 0 → y ∈ Subgroup.closure {g | g ∈ mGens1} := by
  intro y hy h0
  have := one_pretrans
  have hcl : C1.cert.closedOK RN.enc = true := LatCert.closedOK_of_check C1.cert_check
  have hsz : C1.cert.sizesOK RN.enc = true := LatCert.sizesOK_of_check C1.cert_check
  have hcard : Nat.card (Subgroup.closure {g | g ∈ mGens1}) = 443520 :=
    C1.cert.card_m (rawIsEnc 23) hcl hsz
  have hSt : Nat.card (MulAction.stabilizer ↥Mg (0 : Fin 23)) = 443520 := by
    have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥Mg (0 : Fin 23))
    have h3 : (MulAction.stabilizer ↥Mg (0 : Fin 23)).index = 23 := by
      rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]
      simp [Nat.card_eq_fintype_card]
    rw [h3, card_Mg] at h1
    omega
  have hW : Nat.card ((MulAction.stabilizer ↥Mg (0 : Fin 23)).map Mg.subtype) = 443520 := by
    rw [Subgroup.card_map_of_injective Mg.subtype_injective]
    exact hSt
  have hle : Subgroup.closure {g | g ∈ mGens1} ≤
      (MulAction.stabilizer ↥Mg (0 : Fin 23)).map Mg.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, mGens1_mem g hg⟩, MulAction.mem_stabilizer_iff.mpr (mGens1_fix g hg), rfl⟩
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hcard])
  rw [heq]
  exact ⟨⟨y, hy⟩, MulAction.mem_stabilizer_iff.mpr h0, rfl⟩

abbrev Tg : Subgroup (Perm (Fin 23)) := Subgroup.closure {g | g ∈ tGens}

theorem Tg_le
    : Tg ≤ Mg := (Subgroup.closure_le _).mpr fun g hg => tGens_mem g hg

theorem card_Tg : Nat.card ↥Tg = 128 := by
  have hcl := LatCert.closedOK_of_check C1.cert_check
  have hsz := LatCert.sizesOK_of_check C1.cert_check
  exact C1.cert.card_t (rawIsEnc 23) hcl hsz

theorem tSylow
    : IsSylowTwoOf (Tg.subgroupOf Mg) ⊤ := by
  have hU : Nat.card ↥(Tg.subgroupOf Mg) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tg_le).toEquiv, card_Tg]
    norm_num
  refine ⟨le_top, IsPGroup.of_card hU, ?_⟩
  have hidx := Subgroup.card_mul_index (Tg.subgroupOf Mg)
  rw [hU, card_Mg] at hidx
  have h79 : (Tg.subgroupOf Mg).index = 79695 := by omega
  have h1 : ((Tg.subgroupOf Mg).subgroupOf (⊤ : Subgroup ↥Mg)).index =
      (Tg.subgroupOf Mg).index := Subgroup.relIndex_top_right _
  rw [h1, h79]
  decide

theorem normalizer_map_subtype {P : Type} [Group P] {M : Subgroup P} {U B : Subgroup ↥M}
    (h : U ≤ Subgroup.normalizer (B : Set ↥M)) :
    U.map M.subtype ≤ Subgroup.normalizer ((B.map M.subtype : Subgroup P) : Set P) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hu' := Subgroup.mem_normalizer_iff.mp (h hu)
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨u * b * u⁻¹, (hu' b).mp hb, by simp⟩
  · rintro ⟨b', hb', hb'x⟩
    have hxe : x = (u : P)⁻¹ * (b' : P) * (u : P) := by
      have : (b' : P) = (u : P) * x * (u : P)⁻¹ := hb'x
      rw [this]
      group
    have hxM : x ∈ M := by
      rw [hxe]
      exact M.mul_mem (M.mul_mem (M.inv_mem u.2) b'.2) u.2
    have hxB : (⟨x, hxM⟩ : ↥M) ∈ B := by
      rw [hu' ⟨x, hxM⟩]
      have : u * ⟨x, hxM⟩ * u⁻¹ = b' := by
        apply Subtype.ext
        have : (b' : P) = (u : P) * x * (u : P)⁻¹ := hb'x
        simpa using this.symm
      rw [this]
      exact hb'
    exact ⟨⟨x, hxM⟩, hxB, rfl⟩

theorem core
    (B : Subgroup ↥Mg) (hD : IsDelta5Group ↥B)
    (hUB : Tg.subgroupOf Mg ≤ Subgroup.normalizer (B : Set ↥Mg)) : False := by
  classical
  obtain ⟨j, hj1, hj2, -, -⟩ := delta5_sup_data tSylow hD hUB
  have hUcard : Nat.card ↥(Tg.subgroupOf Mg) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tg_le).toEquiv, card_Tg]
    norm_num
  have hj : j = 1 := by
    have h2 : 2 ^ (6 + j) = 2 ^ 7 := by rw [← hj1, hUcard]
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hj
  have hYcard : Nat.card ↥(B ⊔ Tg.subgroupOf Mg) = 1920 := by rw [hj2]; norm_num
  have hY₀card : Nat.card ↥((B ⊔ Tg.subgroupOf Mg).map Mg.subtype) = 1920 := by
    rw [Subgroup.card_map_of_injective Mg.subtype_injective]
    exact hYcard
  have hY₀M : (B ⊔ Tg.subgroupOf Mg).map Mg.subtype ≤ Mg := Subgroup.map_subtype_le _
  have hTU : (Tg.subgroupOf Mg).map Mg.subtype = Tg := Subgroup.map_subgroupOf_eq_of_le Tg_le
  have hTY : Tg ≤ (B ⊔ Tg.subgroupOf Mg).map Mg.subtype :=
    hTU.symm.le.trans (Subgroup.map_mono le_sup_right)
  have hBY : B.map Mg.subtype ≤ (B ⊔ Tg.subgroupOf Mg).map Mg.subtype :=
    Subgroup.map_mono le_sup_left
  have hB₀M : B.map Mg.subtype ≤ Mg := Subgroup.map_subtype_le _
  have hD₀ : IsDelta5Group ↥(B.map Mg.subtype) :=
    hD.of_equiv (B.equivMapOfInjective Mg.subtype Mg.subtype_injective)
  have hTB₀ : Tg ≤ Subgroup.normalizer ((B.map Mg.subtype : Subgroup (Perm (Fin 23))) :
      Set (Perm (Fin 23))) :=
    hTU.symm.le.trans (normalizer_map_subtype hUB)
  generalize (B ⊔ Tg.subgroupOf Mg).map Mg.subtype = Y₀ at hY₀card hY₀M hTY hBY
  generalize B.map Mg.subtype = B₀ at hBY hB₀M hD₀ hTB₀
  have hcl1 : C1.cert.closedOK RN.enc = true := LatCert.closedOK_of_check C1.cert_check
  have hcl2 : C2.cert.closedOK RN.enc = true := LatCert.closedOK_of_check C2.cert_check
  rcases orbit_zero_cases hTY hY₀card with hA | hB | hC
  ·
    have hfix : ∀ y ∈ Y₀, y 0 = 0 := by
      intro y hy
      have hmem : y 0 ∈ MulAction.orbit ↥Y₀ (0 : Fin 23) := ⟨⟨y, hy⟩, rfl⟩
      have key : ∀ z : Fin 23, tau z = 0 → z = 0 := by decide
      exact key _ ((hA _).mp hmem)
    have hB₀le : B₀ ≤ Subgroup.closure {g | g ∈ mGens1} := fun y hy =>
      fix_le_closure1 y (hB₀M hy) (hfix y (hBY hy))
    exact not_isDelta5_of_latCert_amb C1.cert C1.cert_check C1.cert_tle (by decide)
      (m := 3465) (by decide) (by decide)
      (hA_of_latSixCheck C1.cert hcl1 [C1.aData1] C1.cert_latSix) B₀ hB₀le hD₀ hTB₀
  ·
    have hstab : Nat.card (MulAction.stabilizer ↥Y₀ (0 : Fin 23)) = 640 := by
      have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥Y₀ (0 : Fin 23))
      have h3 : (MulAction.stabilizer ↥Y₀ (0 : Fin 23)).index = 3 := by
        rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hB]
      rw [h3, hY₀card] at h1
      omega
    have hZcard : Nat.card ↥((MulAction.stabilizer ↥Y₀ (0 : Fin 23)).map Y₀.subtype) = 640 := by
      rw [Subgroup.card_map_of_injective Y₀.subtype_injective]
      exact hstab
    have hTZ : Tg ≤ (MulAction.stabilizer ↥Y₀ (0 : Fin 23)).map Y₀.subtype := fun t ht =>
      ⟨⟨t, hTY ht⟩, MulAction.mem_stabilizer_iff.mpr (closure_tGens_fix_zero t ht), rfl⟩
    have hZM : (MulAction.stabilizer ↥Y₀ (0 : Fin 23)).map Y₀.subtype ≤
        Subgroup.closure {g | g ∈ mGens1} := by
      rintro _ ⟨⟨z, hz⟩, hzs, rfl⟩
      exact fix_le_closure1 z (hY₀M hz) (MulAction.mem_stabilizer_iff.mp hzs)
    have hmem := card_mem_sizes_of_latCert C1.cert C1.cert_check _ hTZ hZM
    rw [hZcard] at hmem
    revert hmem
    decide
  ·
    have h19 := orbit_nineteen hTY hY₀card hC
    have hfix : ∀ y ∈ Y₀, y 19 ∈ ({19, 20} : Finset (Fin 23)) ∧
        y 20 ∈ ({19, 20} : Finset (Fin 23)) := by
      intro y hy
      have m19 : y 19 ∈ MulAction.orbit ↥Y₀ (19 : Fin 23) := ⟨⟨y, hy⟩, rfl⟩
      have m20 : (20 : Fin 23) ∈ MulAction.orbit ↥Y₀ (19 : Fin 23) := (h19 20).mpr (by decide)
      have e : MulAction.orbit ↥Y₀ (20 : Fin 23) = MulAction.orbit ↥Y₀ (19 : Fin 23) :=
        MulAction.orbit_eq_iff.mpr m20
      have m20' : y 20 ∈ MulAction.orbit ↥Y₀ (20 : Fin 23) := ⟨⟨y, hy⟩, rfl⟩
      rw [e] at m20'
      have key : ∀ z : Fin 23, tau z = 1 → z ∈ ({19, 20} : Finset (Fin 23)) := by decide
      exact ⟨key _ ((h19 _).mp m19), key _ ((h19 _).mp m20')⟩
    have hB₀le : B₀ ≤ Subgroup.closure {g | g ∈ mGens2} := fun y hy =>
      stab2_le_closure y (hB₀M hy) (hfix y (hBY hy)).1 (hfix y (hBY hy)).2
    exact not_isDelta5_of_latCert_amb C2.cert C2.cert_check C2.cert_tle (by decide)
      (m := 315) (by decide) (by decide)
      (hA_of_latSixCheck C2.cert hcl2 [C2.aData1, C2.aData2] C2.cert_latSix) B₀ hB₀le hD₀ hTB₀

theorem noDelta5Norm_m23_closure
    : NoDelta5Norm ↥Mg :=
  noDelta5Norm_of_sylow tSylow fun B hUB hD => core B hD hUB

end CFSG.QuasithinUnique.A5.G3.M23

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Quasithin

theorem noDelta5Norm_m23
    {X : Type} [Group X] (h : IsSporadic .M23 X) : NoDelta5Norm X := by
  obtain ⟨e⟩ := h
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := e
  exact NoDelta5Norm.of_mulEquiv e'.symm M23.noDelta5Norm_m23_closure

theorem mathieuNoDelta5
    : MathieuNoDelta5 :=
  mathieuNoDelta5_of fun _ _ _ h => noDelta5Norm_m23 h

end CFSG.QuasithinUnique.A5.G3
