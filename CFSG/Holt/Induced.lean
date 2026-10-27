module

public import CFSG.Holt.Witt
public import CFSG.Holt.Centralizer

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section Induced

@[expose] def inducedHom (K : Subgroup G) (Ψ : Set Ω) (h : K ≤ stabilizer G Ψ) :
    K →* Equiv.Perm Ψ :=
  (MulAction.toPermHom (stabilizer G Ψ) Ψ).comp (Subgroup.inclusion h)

@[expose] def inducedPerm (K : Subgroup G) (Ψ : Set Ω) (h : K ≤ stabilizer G Ψ) :
    Subgroup (Equiv.Perm Ψ) :=
  (inducedHom K Ψ h).range

variable {K : Subgroup G} {Ψ : Set Ω} {h : K ≤ stabilizer G Ψ}

@[simp] theorem coe_inducedHom_apply (k : K) (ω : Ψ) :
    ((inducedHom K Ψ h k ω : Ψ) : Ω) = (k : G) • (ω : Ω) := rfl

theorem mem_inducedPerm {π : Equiv.Perm Ψ} :
    π ∈ inducedPerm K Ψ h ↔ ∃ k ∈ K, ∀ ω : Ψ, (π ω : Ω) = k • (ω : Ω) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, fun ω => rfl⟩
  · rintro ⟨k, hk, hπ⟩
    exact ⟨⟨k, hk⟩, Equiv.ext fun ω => Subtype.ext (hπ ω).symm⟩

theorem inducedHom_eq_one_iff {k : K} :
    inducedHom K Ψ h k = 1 ↔ (k : G) ∈ fixingSubgroup G Ψ := by
  rw [mem_fixingSubgroup_iff, Equiv.ext_iff]
  constructor
  · intro hk ω hω
    exact congrArg Subtype.val (hk ⟨ω, hω⟩)
  · intro hk ω
    exact Subtype.ext (hk ω ω.2)

theorem ker_inducedHom : (inducedHom K Ψ h).ker = (fixingSubgroup G Ψ).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, inducedHom_eq_one_iff, Subgroup.mem_subgroupOf]

theorem inducedPerm_mono {K' : Subgroup G} {h' : K' ≤ stabilizer G Ψ} (hKK' : K ≤ K') :
    inducedPerm K Ψ h ≤ inducedPerm K' Ψ h' := fun _ hπ =>
  let ⟨k, hk, hπ⟩ := mem_inducedPerm.mp hπ
  mem_inducedPerm.mpr ⟨k, hKK' hk, hπ⟩

theorem card_inducedPerm_mul_card_ker [Finite G] :
    Nat.card (inducedPerm K Ψ h) * Nat.card ((fixingSubgroup G Ψ).subgroupOf K) =
      Nat.card K := by
  rw [← ker_inducedHom, inducedPerm,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (inducedHom K Ψ h)).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem card_inducedPerm_le [Finite G] : Nat.card (inducedPerm K Ψ h) ≤ Nat.card K :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)

theorem card_inducedPerm_lt [Finite G] {k : G} (hk : k ∈ K) (hk1 : k ≠ 1)
    (hkΨ : k ∈ fixingSubgroup G Ψ) : Nat.card (inducedPerm K Ψ h) < Nat.card K := by
  have hker : 1 < Nat.card ((fixingSubgroup G Ψ).subgroupOf K) := by
    rw [Subgroup.one_lt_card_iff_ne_bot, Ne, Subgroup.eq_bot_iff_forall]
    intro hbot
    exact hk1 (congrArg Subtype.val (hbot ⟨k, hk⟩ (Subgroup.mem_subgroupOf.mpr hkΨ)))
  have := card_inducedPerm_mul_card_ker (K := K) (Ψ := Ψ) (h := h)
  have hK : 0 < Nat.card K := Nat.card_pos
  have hpos : 0 < Nat.card (inducedPerm K Ψ h) := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at this
    omega
  nlinarith

end Induced

section CentralizerImage

theorem normalizer_le_stabilizer_fixSet (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ stabilizer G (fixSet Ω T) := by
  intro n hn
  rw [mem_stabilizer_set]
  intro ω
  refine ⟨fun hω => ?_, smul_mem_fixSet_of_mem_normalizer hn⟩
  simpa only [inv_smul_smul] using smul_mem_fixSet_of_mem_normalizer (inv_mem hn) hω

theorem centralizer_le_stabilizer_fixSet (T : Subgroup G) :
    Subgroup.centralizer (T : Set G) ≤ stabilizer G (fixSet Ω T) :=
  (Subgroup.centralizer_le_normalizer _).trans (normalizer_le_stabilizer_fixSet T)

theorem le_fixingSubgroup_fixSet (T : Subgroup G) : T ≤ fixingSubgroup G (fixSet Ω T) :=
  fun t ht => (mem_fixingSubgroup_iff G).mpr fun _ hω => hω t ht

variable (Ω) in
@[expose] def centralizerImage (T : Subgroup G) : Subgroup (Equiv.Perm (fixSet Ω T)) :=
  (MulAction.toPermHom (Subgroup.centralizer (T : Set G)) (fixSet Ω T)).range

theorem centralizerImage_eq_inducedPerm (T : Subgroup G) :
    centralizerImage Ω T =
      inducedPerm (Subgroup.centralizer (T : Set G)) (fixSet Ω T)
        (centralizer_le_stabilizer_fixSet T) := rfl

theorem mem_centralizerImage {T : Subgroup G} {π : Equiv.Perm (fixSet Ω T)} :
    π ∈ centralizerImage Ω T ↔
      ∃ c ∈ Subgroup.centralizer (T : Set G), ∀ ω : fixSet Ω T, (π ω : Ω) = c • (ω : Ω) := by
  rw [centralizerImage_eq_inducedPerm, mem_inducedPerm]

theorem card_centralizerImage_lt [Finite G] {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hT : IsPGroup p T) (hT1 : T ≠ ⊥) :
    Nat.card (centralizerImage Ω T) < Nat.card (Subgroup.centralizer (T : Set G)) := by
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have := hT.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center T)
  have hzC : ((z : T) : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩)
  rw [centralizerImage_eq_inducedPerm]
  refine card_inducedPerm_lt hzC (fun h1 => hz ?_) (le_fixingSubgroup_fixSet T (z : T).2)
  exact Subtype.ext (Subtype.ext h1)

theorem card_centralizerImage_lt_card [Finite G] {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hT : IsPGroup p T) (hT1 : T ≠ ⊥) : Nat.card (centralizerImage Ω T) < Nat.card G :=
  (card_centralizerImage_lt hT hT1).trans_le (Subgroup.card_le_card_group _)

end CentralizerImage

section Lift

variable {K : Subgroup G} {Ψ : Set Ω} {h : K ≤ stabilizer G Ψ} {p : ℕ}

theorem isPGroup_inducedPerm {R : Subgroup G} (hR : IsPGroup p R) (hRΨ : R ≤ stabilizer G Ψ) :
    IsPGroup p (inducedPerm R Ψ hRΨ) :=
  hR.of_surjective _ (inducedHom R Ψ hRΨ).rangeRestrict_surjective

theorem inducedPerm_eq_map {R : Subgroup G} (hRK : R ≤ K) :
    inducedPerm R Ψ (hRK.trans h) = (R.subgroupOf K).map (inducedHom K Ψ h) := by
  ext π
  rw [mem_inducedPerm, Subgroup.mem_map]
  constructor
  · rintro ⟨r, hr, hπ⟩
    exact ⟨⟨r, hRK hr⟩, hr, Equiv.ext fun ω => Subtype.ext (hπ ω).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, fun ω => rfl⟩

variable [Fact p.Prime]

theorem exists_isPGroup_map_eq_of_map_le {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    {H : Subgroup A} {Q : Subgroup B} (hQ : IsPGroup p Q) (hQH : Q ≤ H.map φ)
    {E : Subgroup A} (hE : IsPGroup p E) (hEH : E ≤ H) (hEQ : E.map φ ≤ Q) :
    ∃ P : Subgroup A, E ≤ P ∧ P ≤ H ∧ IsPGroup p P ∧ P.map φ = Q := by
  set W := H ⊓ Q.comap φ
  let ψ : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := hQH hq
    exact ⟨⟨a, ha, hq⟩, rfl⟩
  have hEW : E ≤ W := le_inf hEH fun e he => hEQ ⟨e, he, rfl⟩
  obtain ⟨T, hT⟩ := (hE.comap_of_injective W.subtype W.subtype_injective).exists_le_sylow
  have htop : ((T.mapSurjective hψ : Sylow p Q) : Subgroup Q) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, fun e he => ⟨⟨e, hEW he⟩,
    hT (Subgroup.mem_comap.mpr he : (⟨e, hEW he⟩ : W) ∈ E.comap W.subtype), rfl⟩,
    (Subgroup.map_subtype_le _).trans inf_le_left, T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2.2
  · intro q hq
    obtain ⟨w, hw, hwq⟩ : (⟨q, hq⟩ : Q) ∈ (T : Subgroup W).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwq⟩

theorem fusionIsSylowIn_map {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    {P H : Subgroup A} (hP : fusionIsSylowIn p P H) :
    fusionIsSylowIn p (P.map φ) (H.map φ) := by
  refine ⟨Subgroup.map_mono hP.1, hP.2.1.map φ, fun Q hQH hQ hPQ => ?_⟩
  obtain ⟨P', hPP', hP'H, hP', rfl⟩ := exists_isPGroup_map_eq_of_map_le φ hQ hQH hP.2.1 hP.1 hPQ
  rw [hP.2.2 P' hP'H hP' hPP']

theorem exists_fusionIsSylowIn_map_eq {A B : Type*} [Group A] [Group B] [Finite A]
    (φ : A →* B) {H : Subgroup A} {Q : Subgroup B} (hQ : fusionIsSylowIn p Q (H.map φ)) :
    ∃ P : Subgroup A, fusionIsSylowIn p P H ∧ P.map φ = Q := by
  obtain ⟨R, -, hRH, hR, hRQ⟩ := exists_isPGroup_map_eq_of_map_le φ hQ.2.1 hQ.1 IsPGroup.of_bot
    bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  obtain ⟨P, hRP, hP⟩ := exists_fusionIsSylowIn_ge hR hRH
  exact ⟨P, hP, hQ.2.2 _ (Subgroup.map_mono hP.1) (hP.2.1.map φ) (hRQ ▸ Subgroup.map_mono hRP)⟩

theorem exists_le_inducedPerm_eq [Finite G] {Q : Subgroup (Equiv.Perm Ψ)} (hQ : IsPGroup p Q)
    (hQK : Q ≤ inducedPerm K Ψ h) {E : Subgroup G} (hE : IsPGroup p E) (hEK : E ≤ K)
    (hEQ : inducedPerm E Ψ (hEK.trans h) ≤ Q) :
    ∃ R : Subgroup G, ∃ hRK : R ≤ K,
      E ≤ R ∧ IsPGroup p R ∧ inducedPerm R Ψ (hRK.trans h) = Q := by
  have hQ' : Q ≤ (⊤ : Subgroup K).map (inducedHom K Ψ h) := by
    rwa [← MonoidHom.range_eq_map]
  obtain ⟨P, hEP, -, hP, hPQ⟩ := exists_isPGroup_map_eq_of_map_le (inducedHom K Ψ h) hQ hQ'
    (E := E.subgroupOf K) (hE.comap_of_injective K.subtype K.subtype_injective) le_top
    (by rwa [← inducedPerm_eq_map hEK])
  refine ⟨P.map K.subtype, Subgroup.map_subtype_le P, fun e he => ⟨⟨e, hEK he⟩,
    hEP (Subgroup.mem_subgroupOf.mpr he : (⟨e, hEK he⟩ : K) ∈ E.subgroupOf K), rfl⟩,
    hP.map _, ?_⟩
  rw [inducedPerm_eq_map (h := h) (Subgroup.map_subtype_le P)]
  convert hPQ
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective P

theorem exists_inducedPerm_eq_of_isPGroup [Finite G] {Q : Subgroup (Equiv.Perm Ψ)}
    (hQ : IsPGroup p Q) (hQK : Q ≤ inducedPerm K Ψ h) :
    ∃ R : Subgroup G, ∃ hRK : R ≤ K, IsPGroup p R ∧ inducedPerm R Ψ (hRK.trans h) = Q := by
  refine (exists_le_inducedPerm_eq hQ hQK IsPGroup.of_bot bot_le fun π hπ => ?_).imp
    fun R ⟨hRK, _, hR, hRQ⟩ => ⟨hRK, hR, hRQ⟩
  obtain ⟨k, hk, hπ⟩ := mem_inducedPerm.mp hπ
  rw [Subgroup.mem_bot] at hk
  subst hk
  have : π = 1 := Equiv.ext fun ω => Subtype.ext ((hπ ω).trans (one_smul G _))
  rw [this]
  exact Q.one_mem

theorem fusionIsSylowIn_inducedPerm [Finite G] {S : Subgroup G} (hS : fusionIsSylowIn p S K) :
    fusionIsSylowIn p (inducedPerm S Ψ (hS.1.trans h)) (inducedPerm K Ψ h) := by
  refine ⟨inducedPerm_mono hS.1, isPGroup_inducedPerm hS.2.1 _, fun Q hQK hQ hSQ => ?_⟩
  obtain ⟨R, hRK, hSR, hR, rfl⟩ := exists_le_inducedPerm_eq hQ hQK hS.2.1 hS.1 hSQ
  obtain rfl := hS.2.2 R hRK hR hSR
  rfl

end Lift

section FixedSets

variable {p : ℕ} [Fact p.Prime]

theorem card_modEq_card_fixSet_inter_of_le_stabilizer {P : Subgroup G} (hP : IsPGroup p P)
    {Λ : Set Ω} [Finite Λ] (hPΛ : P ≤ stabilizer G Λ) :
    Nat.card Λ ≡ Nat.card ↥(fixSet Ω P ∩ Λ) [MOD p] := by
  have e : Nat.card (fixedPoints (inducedPerm P Λ hPΛ) Λ) = Nat.card ↥(fixSet Ω P ∩ Λ) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, fun y hy =>
          congrArg Subtype.val (x.2 ⟨inducedHom P Λ hPΛ ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩), x.1.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.2⟩, fun π => by
          obtain ⟨y, hy, hπ⟩ := mem_inducedPerm.mp π.2
          exact Subtype.ext ((hπ _).trans (x.2.1 y hy))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← e]
  exact (isPGroup_inducedPerm hP hPΛ).card_modEq_card_fixedPoints Λ

theorem exists_smul_fixSet_eq_of_fusionIsSylowIn [Finite G] {S S' H : Subgroup G}
    (hS : fusionIsSylowIn p S H) (hS' : fusionIsSylowIn p S' H) :
    ∃ k ∈ H, fixSet Ω S' = k • fixSet Ω S := by
  obtain ⟨k, hk, hkS⟩ := exists_mem_conj_of_fusionIsSylowIn hS hS'
  refine ⟨k, hk, Set.ext fun ω => ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixSet, mem_fixSet]
  constructor
  · intro hω s hs
    have hx : k * s * k⁻¹ ∈ S' :=
      (hkS _).mpr (by rw [show k⁻¹ * (k * s * k⁻¹) * k = s by group]; exact hs)
    have h1 := hω _ hx
    rw [mul_smul, mul_smul] at h1
    exact eq_inv_smul_iff.mpr h1
  · intro hω x hx
    have h1 := hω _ ((hkS x).mp hx)
    rw [mul_smul, mul_smul, smul_inv_smul] at h1
    exact smul_left_cancel _ h1

theorem fixSet_eq_of_fusionIsSylowIn [Finite G] {Ψ : Set Ω} {S S' H : Subgroup G}
    (hH : H ≤ stabilizer G Ψ) (hS : fusionIsSylowIn p S H) (hS' : fusionIsSylowIn p S' H)
    (hF : fixSet Ω S = Ψ) : fixSet Ω S' = Ψ := by
  obtain ⟨k, hk, hkF⟩ := exists_smul_fixSet_eq_of_fusionIsSylowIn (Ω := Ω) hS hS'
  rw [hkF, hF]
  exact hH hk

theorem not_dvd_card_orbit_of_fusionIsSylowIn [Finite G] {S H : Subgroup G}
    (hS : fusionIsSylowIn p S H) {ω : Ω} (hω : ω ∈ fixSet Ω S) :
    ¬ p ∣ Nat.card (orbit H ω) := by
  obtain ⟨T, hT⟩ := exists_sylow_eq_subgroupOf_of_fusionIsSylowIn hS
  have hle : (T : Subgroup H) ≤ stabilizer H ω := by
    intro t ht
    rw [hT, Subgroup.mem_subgroupOf] at ht
    exact hω _ ht
  intro hdvd
  rw [Nat.card_coe_set_eq, ← index_stabilizer] at hdvd
  exact T.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hle))

end FixedSets

section Lemma17

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem inf_eq_bot_of_isPGroup_of_not_dvd {N P : Subgroup G} (hN : ¬ p ∣ Nat.card N)
    (hP : IsPGroup p P) : N ⊓ P = ⊥ := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN).symm

theorem eq_of_isPGroup_of_le_sup {N R P : Subgroup G} (hN : ¬ p ∣ Nat.card N)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hP : IsPGroup p P) (hRP : R ≤ P)
    (hPNR : P ≤ N ⊔ R) : P = R := by
  refine le_antisymm (fun x hx => ?_) hRP
  have hx' : x ∈ ((N ⊔ R : Subgroup G) : Set G) := hPNR hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N R hRN, Set.mem_mul] at hx'
  obtain ⟨n, hn, r, hr, rfl⟩ := hx'
  have hnP : n ∈ P := by simpa using P.mul_mem hx (P.inv_mem (hRP hr))
  have hnNP : n ∈ N ⊓ P := ⟨hn, hnP⟩
  rw [inf_eq_bot_of_isPGroup_of_not_dvd hN hP, Subgroup.mem_bot] at hnNP
  rw [hnNP, one_mul]
  exact hr

theorem exists_mem_centralizer_smul_eq {N S : Subgroup G} (hN : ¬ p ∣ Nat.card N)
    (hS : IsPGroup p S) (hSN : S ≤ Subgroup.normalizer (N : Set G)) {α β : Ω}
    (hα : α ∈ fixSet Ω S) (hβ : β ∈ fixSet Ω S) {g : G} (hg : g ∈ N) (hgα : g • α = β) :
    ∃ m ∈ N ⊓ Subgroup.centralizer (S : Set G), m • α = β := by
  have hgN : g ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hg
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'def
  have hmemS' : ∀ y, y ∈ S' ↔ g⁻¹ * y * g ∈ S := fun y => by
    rw [hS'def, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hconj : ∀ s ∈ S, g * s * g⁻¹ ∈ S' := fun s hs =>
    (hmemS' _).mpr (by rwa [show g⁻¹ * (g * s * g⁻¹) * g = s by group])
  have hS'N : S' ≤ Subgroup.normalizer (N : Set G) := fun y hy => by
    have hs := (hmemS' y).mp hy
    rw [show y = g * (g⁻¹ * y * g) * g⁻¹ by group]
    exact mul_mem (mul_mem hgN (hSN hs)) (inv_mem hgN)
  have hsup : N ⊔ S ≤ N ⊔ S' := sup_le le_sup_left fun s hs => by
    rw [show s = g⁻¹ * (g * s * g⁻¹) * g by group]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hg))
      (Subgroup.mem_sup_right (hconj s hs))) (Subgroup.mem_sup_left hg)
  have hgα' : g⁻¹ • β = α := by rw [← hgα, inv_smul_smul]
  have hSY : fusionIsSylowIn p S ((N ⊔ S) ⊓ stabilizer G β) :=
    ⟨le_inf le_sup_right (mem_fixSet_iff_le_stabilizer.mp hβ), hS, fun P hPY hP hSP =>
      eq_of_isPGroup_of_le_sup hN hSN hP hSP (hPY.trans inf_le_left)⟩
  have hS'Y : fusionIsSylowIn p S' ((N ⊔ S) ⊓ stabilizer G β) := by
    refine ⟨fun y hy => ⟨?_, ?_⟩, hS.map _, fun P hPY hP hSP =>
      eq_of_isPGroup_of_le_sup hN hS'N hP hSP ((hPY.trans inf_le_left).trans hsup)⟩
    · rw [show y = g * (g⁻¹ * y * g) * g⁻¹ by group]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hg)
        (Subgroup.mem_sup_right ((hmemS' y).mp hy))) (Subgroup.mem_sup_left (inv_mem hg))
    · show y • β = β
      rw [show y = g * (g⁻¹ * y * g) * g⁻¹ by group, mul_smul, mul_smul, hgα',
        hα _ ((hmemS' y).mp hy), hgα]
  obtain ⟨k, hkY, hk⟩ := exists_mem_conj_of_fusionIsSylowIn hS'Y hSY
  have hk' : k ∈ ((S ⊔ N : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hkY.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S N hSN, Set.mem_mul] at hk'
  obtain ⟨s₀, hs₀, n₀, hn₀, rfl⟩ := hk'
  have hm : n₀ * g ∈ N := N.mul_mem hn₀ hg
  refine ⟨n₀ * g, ⟨hm, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, ?_⟩
  · have h1 : (n₀ * g)⁻¹ * y * (n₀ * g) ∈ S := by
      have h := (hmemS' _).mp ((hk (s₀ * y * s₀⁻¹)).mp
        (S.mul_mem (S.mul_mem hs₀ hy) (S.inv_mem hs₀)))
      rwa [show g⁻¹ * ((s₀ * n₀)⁻¹ * (s₀ * y * s₀⁻¹) * (s₀ * n₀)) * g =
        (n₀ * g)⁻¹ * y * (n₀ * g) by group] at h
    have h2 : (n₀ * g)⁻¹ * y * (n₀ * g) * y⁻¹ ∈ N ⊓ S := by
      refine ⟨?_, S.mul_mem h1 (S.inv_mem hy)⟩
      rw [show (n₀ * g)⁻¹ * y * (n₀ * g) * y⁻¹ = (n₀ * g)⁻¹ * (y * (n₀ * g) * y⁻¹) by group]
      exact N.mul_mem (N.inv_mem hm)
        ((Subgroup.mem_normalizer_iff.mp (hSN hy) (n₀ * g)).mp hm)
    rw [inf_eq_bot_of_isPGroup_of_not_dvd hN hS, Subgroup.mem_bot] at h2
    have h3 := mul_inv_eq_one.mp h2
    calc y * (n₀ * g) = n₀ * g * ((n₀ * g)⁻¹ * y * (n₀ * g)) := by group
      _ = n₀ * g * y := by rw [h3]
  · have hkβ : s₀ • n₀ • β = β := by
      rw [← mul_smul]
      exact hkY.2
    have hn₀β : n₀ • β = β := by
      rw [smul_eq_iff_eq_inv_smul] at hkβ
      rw [hkβ]
      exact hβ _ (S.inv_mem hs₀)
    rw [mul_smul, hgα, hn₀β]

end Lemma17

end CFSG.Holt
