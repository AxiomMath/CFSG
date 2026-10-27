module

public import CFSG.Holt.H78.Sec4Prop43B
import CFSG.Holt.H78.AltModelSylow
public import CFSG.Holt.H78.Sec4AltSylow

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_of_mem_Qimg {i : C.D.ι} {u : Equiv.Perm (C.D.Ψc i)} (hu : u ∈ C.Qimg i) :
    ∃ q : C.kerC i, (q : G) ∈ C.calP ∧ C.kerCHom i q = u := by
  obtain ⟨q, hq, rfl⟩ := hu
  exact ⟨q, (Subgroup.mem_inf.mp hq).1, rfl⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_of_kerCHom_fix {i : C.D.ι} (q : C.kerC i) {Λc : ∀ j, Set (C.D.Ψc j)}
    (hq : ∀ c ∈ Λc i, C.kerCHom i q c = c) (δ : holtDelta G Ω α β)
    (hδ : ∀ j, C.D.coord δ j ∈ Λc j) : (q : G) • (δ : Ω) = δ := by
  have hmem : (q : G) • (δ : Ω) ∈ holtDelta G Ω α β :=
    (twoPointElt (C.kerC_le_stabilizer_pair i q.2) • δ).2
  have : (⟨_, hmem⟩ : holtDelta G Ω α β) = δ := by
    refine C.eq_of_coord_eq (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rw [C.coord_smul_eq_kerCHom q rfl, hq _ (hδ j)]
    · exact C.coord_smul_of_mem_kerC q.2 rfl hj
  exact congrArg Subtype.val this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_ne_of_kerCHom_ne {i : C.D.ι} (q : C.kerC i) {δ : holtDelta G Ω α β}
    (hq : C.kerCHom i q (C.D.coord δ i) ≠ C.D.coord δ i) : (q : G) • (δ : Ω) ≠ δ := by
  intro h
  apply hq
  rw [← C.coord_smul_eq_kerCHom q h.symm]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_stabilizer_pair_of_mem_calP {p : G} (hp : p ∈ C.calP) :
    p ∈ stabilizer G ({α, β} : Set Ω) :=
  C.calG_le_stabilizer_pair (C.calP_le_calG hp)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_γ_of_mem_calP {p : G} (hp : p ∈ C.calP) : p • (C.γ : Ω) = C.γ :=
  C.calG_le_stabilizer_γ (C.calP_le_calG hp)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ncard_univ_Ψc (i : C.D.ι) :
    (Set.univ : Set (C.D.Ψc i)).ncard = Fintype.card (C.D.Ψc i) := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem twoPointElt_mem_normalizer_of_mem_calG {g : G} (hg : g ∈ C.calG) :
    twoPointElt (C.calG_le_stabilizer_pair hg) ∈
      Subgroup.normalizer (C.D.L C.i₁ : Set (twoPointSection G Ω α β)) :=
  (mem_twoPointNormalizer_iff_of_mem _).mp (Subgroup.mem_inf.mp hg).2

@[expose] noncomputable def calGElt :
    C.calG →* Subgroup.normalizer (C.D.L C.i₁ : Set (twoPointSection G Ω α β)) :=
  (((twoPointHom G Ω α β).comp (Subgroup.inclusion C.calG_le_stabilizer_pair)).codRestrict
    (twoPointSection G Ω α β) fun _ => twoPointHom_mem_twoPointSection _).codRestrict _
      fun g => C.twoPointElt_mem_normalizer_of_mem_calG g.2

@[expose] noncomputable def calGHom : C.calG →* Equiv.Perm (C.D.Ψc C.i₁) :=
  (C.D.nRho C.i₁).comp C.calGElt

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_smul_eq_calGHom (g : C.calG) {δ δ' : holtDelta G Ω α β}
    (h : (δ' : Ω) = (g : G) • (δ : Ω)) :
    C.D.coord δ' C.i₁ = C.calGHom g (C.D.coord δ C.i₁) := by
  have hδ' : δ' = (C.calGElt g : twoPointSection G Ω α β) • δ := Subtype.ext h
  rw [calGHom, MonoidHom.comp_apply, C.D.nRho_coord, hδ']

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem kerCHom_eq_calGHom (q : C.kerC C.i₁) :
    C.kerCHom C.i₁ q = C.calGHom ⟨q, C.kerC_le_calG C.i₁ q.2⟩ := by
  refine Equiv.ext fun c => ?_
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c)
  have hδ : C.D.coord δ C.i₁ = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  set δ' := twoPointElt (C.kerC_le_stabilizer_pair C.i₁ q.2) • δ
  rw [← hδ, ← C.coord_smul_eq_kerCHom q (δ' := δ') rfl,
    ← C.coord_smul_eq_calGHom ⟨q, C.kerC_le_calG C.i₁ q.2⟩ (δ' := δ') rfl]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_kerC_i₁ {h n : G} (hh : h ∈ C.calG) (hn : n ∈ C.kerC C.i₁) :
    h * n * h⁻¹ ∈ C.kerC C.i₁ := by
  have hinv : h⁻¹ ∈ C.calG := C.calG.inv_mem hh
  change h * n * h⁻¹ ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G (C.hyper C.i₁)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (stabilizer G α ⊓ stabilizer G β).mul_mem
      ((stabilizer G α ⊓ stabilizer G β).mul_mem (C.calG_le_inf hh) (C.kerC_le_inf _ hn))
      ((stabilizer G α ⊓ stabilizer G β).inv_mem (C.calG_le_inf hh))
  · rw [mem_fixingSubgroup_iff]
    rintro _ ⟨δ, rfl, hδ⟩
    set π := twoPointElt (C.calG_le_stabilizer_pair hinv)
    have hπγ : π • C.γ = C.γ := Subtype.ext (C.calG_le_stabilizer_γ hinv)
    have h1 := ((C.D.normalizer_L_preserves_fibres (C.twoPointElt_mem_normalizer_of_mem_calG hinv)
      δ C.γ).1).mpr hδ
    rw [hπγ] at h1
    have h2 : n • ((π • δ : holtDelta G Ω α β) : Ω) = (π • δ : holtDelta G Ω α β) :=
      C.smul_eq_of_mem_kerC hn h1
    change n • (h⁻¹ • (δ : Ω)) = h⁻¹ • (δ : Ω) at h2
    rw [mul_smul, mul_smul, h2, smul_inv_smul]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem calGHom_conj_mem_Qimg {p : G} (hp : p ∈ C.calP) {u : Equiv.Perm (C.D.Ψc C.i₁)}
    (hu : u ∈ C.Qimg C.i₁) :
    C.calGHom ⟨p, C.calP_le_calG hp⟩ * u * (C.calGHom ⟨p, C.calP_le_calG hp⟩)⁻¹ ∈
      C.Qimg C.i₁ := by
  obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg hu
  have hpG := C.calP_le_calG hp
  have hmem : p * (q : G) * p⁻¹ ∈ C.kerC C.i₁ := C.conj_mem_kerC_i₁ hpG q.2
  have hmemP : p * (q : G) * p⁻¹ ∈ C.calP := C.calP.mul_mem (C.calP.mul_mem hp hqP)
    (C.calP.inv_mem hp)
  refine ⟨⟨_, hmem⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hmemP, hmem⟩), ?_⟩
  rw [C.kerCHom_eq_calGHom, C.kerCHom_eq_calGHom, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem false_of_not_mapsDir (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hP : fusionIsSylowIn 2 C.calP C.calG) {j k : C.D.ι} (hj : j ≠ C.i₁) (hk : k ≠ C.i₁)
    (hjk : ∀ p ∈ C.calP, ¬ C.MapsDir p j k) : False := by
  classical
  set I : Set C.D.ι := {l | ∃ p ∈ C.calP, C.MapsDir p j l} with hI
  have hjI : j ∈ I := ⟨1, C.calP.one_mem, C.mapsDir_one j⟩
  have hi₁I : C.i₁ ∉ I := by
    rintro ⟨p, hp, hpj⟩
    exact hj (MapsDir.eq C (inv_mem (C.mem_stabilizer_pair_of_mem_calP hp)) hpj.inv
      (C.mapsDir_i₁ (Subgroup.mem_inf.mp hp).2).inv)
  have hkI : k ∉ I := fun ⟨p, hp, hpk⟩ => hjk p hp hpk
  set Λc : ∀ l, Set (C.D.Ψc l) := fun l => if l ∈ I then {C.D.coord C.γ l} else Set.univ
    with hΛc
  have hΛI : ∀ l ∈ I, Λc l = {C.D.coord C.γ l} := fun l hl => by simp [hΛc, hl]
  have hΛnI : ∀ l ∉ I, Λc l = Set.univ := fun l hl => by simp [hΛc, hl]
  have hstab : ∀ p ∈ C.calP, ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
      (∀ l, C.D.coord δ l ∈ Λc l) → ∀ l, C.D.coord δ' l ∈ Λc l := by
    intro p hp δ δ' e hδ l
    by_cases hl : l ∈ I
    · rw [hΛI l hl, Set.mem_singleton_iff]
      obtain ⟨σ, hσ⟩ := C.exists_mapsDir (C.mem_stabilizer_pair_of_mem_calP hp)
      have hml : C.MapsDir p (σ.symm l) l := by
        have := hσ (σ.symm l)
        rwa [Equiv.apply_symm_apply] at this
      have hmI : σ.symm l ∈ I := by
        obtain ⟨q, hq, hqj⟩ := hl
        exact ⟨p⁻¹ * q, C.calP.mul_mem (C.calP.inv_mem hp) hq,
          MapsDir.mul C (C.mem_stabilizer_pair_of_mem_calP hq) hqj hml.inv⟩
      have hδm := hδ (σ.symm l)
      rw [hΛI _ hmI, Set.mem_singleton_iff] at hδm
      exact (hml δ C.γ δ' C.γ e (C.smul_γ_of_mem_calP hp).symm).mpr hδm
    · rw [hΛnI l hl]
      exact Set.mem_univ _
  have hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ l, C.D.coord δ l ∈ Λc l) → ∃ v ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ l, C.D.coord δ' l ∈ Λc l) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ := by
    intro δ hδ
    push Not at hδ
    obtain ⟨l, hl⟩ := hδ
    have hlI : l ∈ I := by
      by_contra hlI
      rw [hΛnI l hlI] at hl
      exact hl (Set.mem_univ _)
    rw [hΛI l hlI, Set.mem_singleton_iff] at hl
    have hU := C.fusionIsSylowIn_Qimg_inf hS hP l
    have hfix := fixSet_eq_singleton_of_fusionIsSylowIn_alternatingGroup (C.D.odd_card_Ψc l)
      (C.D.five_le_card l) hU
    have hnot : C.D.coord δ l ∉ fixSet (C.D.Ψc l) (C.Qimg l ⊓ alternatingGroup (C.D.Ψc l)) := by
      rw [hfix, Set.mem_singleton_iff]
      exact hl
    simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨u, hu, hmv⟩ := hnot
    obtain ⟨q, hqP, hqu⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hu).1
    refine ⟨q, hqP, fun δ' hδ' => C.smul_eq_of_kerCHom_fix q (Λc := Λc) ?_ δ' hδ', ?_⟩
    · intro c hc
      rw [hΛI l hlI, Set.mem_singleton_iff] at hc
      rw [hc]
      exact C.kerCHom_apply_γ q
    · exact C.smul_ne_of_kerCHom_ne q (by rw [hqu]; exact hmv)
  have hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ l, C.D.coord δ l ∈ Λc l := by
    have := C.nontrivial_Ψc j
    obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ j)
    refine ⟨C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c), fun h => hc ?_⟩
    have := h j
    rw [C.coord_coordEquiv_symm, Function.update_self, hΛI j hjI, Set.mem_singleton_iff] at this
    exact this
  have hsize : ∀ l, (Λc l).ncard = 1 ∨ 5 ≤ (Λc l).ncard := by
    intro l
    by_cases hl : l ∈ I
    · left
      rw [hΛI l hl, Set.ncard_singleton]
    · right
      rw [hΛnI l hl, C.ncard_univ_Ψc]
      exact C.D.five_le_card l
  have h₁ : 5 ≤ (Λc C.i₁).ncard := by
    rw [hΛnI _ hi₁I, C.ncard_univ_Ψc]
    exact C.D.five_le_card _
  have hj' : ∃ j', j' ≠ C.i₁ ∧ 5 ≤ (Λc j').ncard := ⟨k, hk, by
    rw [hΛnI _ hkI, C.ncard_univ_Ψc]
    exact C.D.five_le_card _⟩
  have h4 := C.four_le_card_fixSet_of_stab_box hS hαβ (C.sylow.2.1.to_le inf_le_left)
    C.calP_le_calG Λc hstab hmove hne hsize h₁ hj'
  rw [C.fix_three] at h4
  omega

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem calGHom_image_orbit {p : G} (hp : p ∈ C.calP) (c : C.D.Ψc C.i₁) :
    (C.calGHom ⟨p, C.calP_le_calG hp⟩) '' orbit (C.Qimg C.i₁) c =
      orbit (C.Qimg C.i₁) (C.calGHom ⟨p, C.calP_le_calG hp⟩ c) := by
  set φ := C.calGHom ⟨p, C.calP_le_calG hp⟩
  have hφinv : φ⁻¹ = C.calGHom ⟨p⁻¹, C.calP_le_calG (C.calP.inv_mem hp)⟩ := by
    rw [← map_inv]
    rfl
  ext y
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨⟨φ * u * φ⁻¹, C.calGHom_conj_mem_Qimg hp u.2⟩, ?_⟩
    change (φ * u * φ⁻¹) (φ c) = φ ((u : Equiv.Perm (C.D.Ψc C.i₁)) c)
    simp [Equiv.Perm.mul_apply]
  · rintro ⟨v, rfl⟩
    have hv : φ⁻¹ * v * φ ∈ C.Qimg C.i₁ := by
      have := C.calGHom_conj_mem_Qimg (C.calP.inv_mem hp) v.2
      rwa [← hφinv, inv_inv] at this
    refine ⟨(φ⁻¹ * (v : Equiv.Perm (C.D.Ψc C.i₁)) * φ) c, ⟨⟨_, hv⟩, rfl⟩, ?_⟩
    change φ ((φ⁻¹ * v * φ) c) = (v : Equiv.Perm (C.D.Ψc C.i₁)) (φ c)
    simp [Equiv.Perm.mul_apply]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fusionIsSylowIn_Qimg_inf_alternatingGroup [Finite G] [Fintype Ω] [DecidableEq Ω]
    (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG) (i : C.D.ι) :
    fusionIsSylowIn 2 (C.Qimg i ⊓ alternatingGroup (C.D.Ψc i)) (alternatingGroup (C.D.Ψc i)) :=
  fusionIsSylowIn_alternatingGroup_of_stabilizer (C.D.odd_card_Ψc i)
    (by have := C.D.five_le_card i; omega) (C.fusionIsSylowIn_Qimg_inf hS hP i)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem calGHom_mem_orbit [Finite G] [Fintype Ω] [DecidableEq Ω] (hS : Sec4Setting G Ω)
    (hP : fusionIsSylowIn 2 C.calP C.calG) {p : G} (hp : p ∈ C.calP) {c x : C.D.Ψc C.i₁}
    (hc : c ∈ orbit ↥(C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁)) x) :
    C.calGHom ⟨p, C.calP_le_calG hp⟩ c ∈
      orbit ↥(C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁)) x := by
  have hU := C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP C.i₁
  have h4 : 4 ≤ Fintype.card (C.D.Ψc C.i₁) := by have := C.D.five_le_card C.i₁; omega
  set U := C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁) with hUdef
  have horb : ∀ y, orbit (C.Qimg C.i₁) y = orbit U y :=
    orbit_eq_of_fusionIsSylowIn_alternatingGroup_of_le h4 hU (C.isPGroup_Qimg C.i₁) inf_le_left
  set φ := C.calGHom ⟨p, C.calP_le_calG hp⟩
  have hcx : orbit U c = orbit U x := orbit_eq_iff.mpr hc
  have hcard : Nat.card (orbit U (φ c)) = Nat.card (orbit U x) := by
    rw [← horb, ← C.calGHom_image_orbit hp, Nat.card_image_of_injective φ.injective, horb, hcx]
  rw [← orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup h4 hU hcard]
  exact mem_orbit_self _

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_calP_of_mem_Qimg_fix {i : C.D.ι} {u : Equiv.Perm (C.D.Ψc i)}
    (hu : u ∈ C.Qimg i) {Λc : ∀ j, Set (C.D.Ψc j)} (hfix : ∀ c ∈ Λc i, u c = c)
    {δ : holtDelta G Ω α β} (hmv : u (C.D.coord δ i) ≠ C.D.coord δ i) :
    ∃ v ∈ C.calP, (∀ δ' : holtDelta G Ω α β, (∀ j, C.D.coord δ' j ∈ Λc j) →
      v • (δ' : Ω) = δ') ∧ v • (δ : Ω) ≠ δ := by
  obtain ⟨q, hqP, hqu⟩ := C.exists_of_mem_Qimg hu
  exact ⟨q, hqP, fun δ' hδ' => C.smul_eq_of_kerCHom_fix q (fun c hc => by rw [hqu]; exact hfix c hc)
    δ' hδ', C.smul_ne_of_kerCHom_ne q (by rw [hqu]; exact hmv)⟩

theorem false_of_two_bits_i₁ (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hP : fusionIsSylowIn 2 C.calP C.calG) (hr : ∃ j, j ≠ C.i₁) {a a' : ℕ} (ha : 2 ≤ a)
    (ha' : 2 ≤ a') (haa' : a ≠ a') (hba : (Fintype.card (C.D.Ψc C.i₁)).testBit a)
    (hba' : (Fintype.card (C.D.Ψc C.i₁)).testBit a') : False := by
  classical
  have hU := C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP C.i₁
  set U := C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁) with hUdef
  have h4 : 4 ≤ Fintype.card (C.D.Ψc C.i₁) := by have := C.D.five_le_card C.i₁; omega
  obtain ⟨x₀, hx₀⟩ := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup h4 hU a).mp hba
  obtain ⟨x₁, hx₁⟩ := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup h4 hU a').mp hba'
  set O : Set (C.D.Ψc C.i₁) := orbit U x₀ with hOdef
  set Λc : ∀ j, Set (C.D.Ψc j) := Function.update (fun _ => Set.univ) C.i₁ Oᶜ with hΛc
  have hΛ₁ : Λc C.i₁ = Oᶜ := Function.update_self _ _ _
  have hΛj : ∀ j, j ≠ C.i₁ → Λc j = Set.univ := fun j hj => Function.update_of_ne hj _ _
  have hγ : C.D.coord C.γ C.i₁ ∉ O := by
    intro h
    have h1 : orbit U (C.D.coord C.γ C.i₁) = O := orbit_eq_iff.mpr h
    have h2 : orbit U (C.D.coord C.γ C.i₁) = {C.D.coord C.γ C.i₁} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_orbit_self _, ?_⟩
      rintro _ ⟨u, rfl⟩
      exact C.Qimg_le_stabilizer C.i₁ (Subgroup.mem_inf.mp u.2).1
    rw [h1] at h2
    rw [h2, Nat.card_unique] at hx₀
    have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hO' : orbit U x₁ ⊆ Oᶜ := by
    intro y hy hyO
    have h1 : orbit U x₁ = O := (orbit_eq_iff.mpr hy).symm.trans (orbit_eq_iff.mpr hyO)
    rw [h1] at hx₁
    rw [hx₁] at hx₀
    exact haa' (Nat.pow_right_injective le_rfl hx₀).symm
  have hγ₁ : C.D.coord C.γ C.i₁ ∉ orbit U x₁ := by
    intro h
    have h1 : orbit U x₁ = {C.D.coord C.γ C.i₁} := by
      rw [← orbit_eq_iff.mpr h]
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_orbit_self _, ?_⟩
      rintro _ ⟨u, rfl⟩
      exact C.Qimg_le_stabilizer C.i₁ (Subgroup.mem_inf.mp u.2).1
    rw [h1, Nat.card_unique] at hx₁
    have : 2 ^ 2 ≤ 2 ^ a' := Nat.pow_le_pow_right (by norm_num) ha'
    omega
  have h₁ : 5 ≤ (Λc C.i₁).ncard := by
    rw [hΛ₁]
    have hsub : insert (C.D.coord C.γ C.i₁) (orbit U x₁) ⊆ Oᶜ := Set.insert_subset hγ hO'
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem hγ₁ (Set.toFinite _), ← Nat.card_coe_set_eq, hx₁] at h1
    have : 2 ^ 2 ≤ 2 ^ a' := Nat.pow_le_pow_right (by norm_num) ha'
    omega
  have hsize : ∀ j, (Λc j).ncard = 1 ∨ 5 ≤ (Λc j).ncard := by
    intro j
    right
    by_cases hj : j = C.i₁
    · subst hj
      exact h₁
    · rw [hΛj j hj, C.ncard_univ_Ψc]
      exact C.D.five_le_card j
  have hj' : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard := by
    obtain ⟨j, hj⟩ := hr
    exact ⟨j, hj, by rw [hΛj j hj, C.ncard_univ_Ψc]; exact C.D.five_le_card j⟩
  have hstab : ∀ p ∈ C.calP, ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
      (∀ j, C.D.coord δ j ∈ Λc j) → ∀ j, C.D.coord δ' j ∈ Λc j := by
    intro p hp δ δ' e hδ j
    by_cases hj : j = C.i₁
    · subst hj
      have hδ₁ := hδ C.i₁
      rw [hΛ₁] at hδ₁ ⊢
      rw [C.coord_smul_eq_calGHom ⟨p, C.calP_le_calG hp⟩ e]
      intro hO
      have h1 := C.calGHom_mem_orbit hS hP (C.calP.inv_mem hp) hO
      rw [← Equiv.Perm.mul_apply, ← map_mul] at h1
      have h2 : (⟨p⁻¹, C.calP_le_calG (C.calP.inv_mem hp)⟩ * ⟨p, C.calP_le_calG hp⟩ : C.calG) =
          1 := Subtype.ext (inv_mul_cancel p)
      rw [h2, map_one, Equiv.Perm.one_apply] at h1
      exact hδ₁ h1
    · rw [hΛj j hj]
      exact Set.mem_univ _
  have hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ j, C.D.coord δ j ∈ Λc j) → ∃ v ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ j, C.D.coord δ' j ∈ Λc j) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ := by
    intro δ hδ
    have hδO : C.D.coord δ C.i₁ ∈ O := by
      by_contra hδO
      refine hδ fun j => ?_
      by_cases hj : j = C.i₁
      · subst hj
        rw [hΛ₁]
        exact hδO
      · rw [hΛj j hj]
        exact Set.mem_univ _
    have hinv : ∀ u ∈ U, ∀ x ∈ Oᶜ, u x ∈ Oᶜ := by
      intro u hu x hx hux
      apply hx
      have hux' : (⟨u, hu⟩ : U) • x ∈ O := hux
      have h1 : orbit U x = O := by
        rw [← MulAction.orbit_smul (⟨u, hu⟩ : U) x]
        exact orbit_eq_iff.mpr hux'
      rw [← h1]
      exact mem_orbit_self x
    have hcard : Nat.card ↥(Oᶜᶜ) = 2 ^ a := by rw [compl_compl]; exact hx₀
    have hfixO := fixSet_inf_fixingSubgroup_eq hU hinv
      (by rw [hcard]; exact (Nat.even_pow' (by omega)).mpr even_two)
      (by rw [hcard]; intro h; have := Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm);
          omega)
    have hnot : C.D.coord δ C.i₁ ∉ fixSet (C.D.Ψc C.i₁) (U ⊓ fixingSubgroup _ Oᶜ) := by
      rw [hfixO]
      exact fun h => h hδO
    simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨w, hw, hmv⟩ := hnot
    obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.mp hw
    refine C.exists_mem_calP_of_mem_Qimg_fix (Subgroup.mem_inf.mp hwU).1 (Λc := Λc) ?_ hmv
    intro c hc
    rw [hΛ₁] at hc
    exact (mem_fixingSubgroup_iff _).mp hwfix c hc
  have hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ j, C.D.coord δ j ∈ Λc j := by
    refine ⟨C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ x₀), fun h => ?_⟩
    have := h C.i₁
    rw [C.coord_coordEquiv_symm, Function.update_self, hΛ₁] at this
    exact this (mem_orbit_self x₀)
  have h5 := C.four_le_card_fixSet_of_stab_box hS hαβ (C.sylow.2.1.to_le inf_le_left)
    C.calP_le_calG Λc hstab hmove hne hsize h₁ hj'
  rw [C.fix_three] at h5
  omega

@[expose] noncomputable def transportFun {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (j k : C.D.ι) (c : C.D.Ψc j) : C.D.Ψc k :=
  C.D.coord (twoPointElt hg • C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)) k

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_smul_eq_transportFun {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {j k : C.D.ι} (hjk : C.MapsDir g j k) {δ δ' : holtDelta G Ω α β}
    (e : (δ' : Ω) = g • (δ : Ω)) : C.D.coord δ' k = C.transportFun hg j k (C.D.coord δ j) :=
  (hjk δ _ δ' _ e rfl).mpr (by rw [C.coord_coordEquiv_symm, Function.update_self])

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transportFun_left_inv {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {j k : C.D.ι}
    (hjk : C.MapsDir g j k) (c : C.D.Ψc j) :
    C.transportFun (inv_mem hg) k j (C.transportFun hg j k c) = c := by
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : C.D.coord δ j = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  have h1 := C.coord_smul_eq_transportFun hg hjk (δ := δ) (δ' := twoPointElt hg • δ) rfl
  have h2 := C.coord_smul_eq_transportFun (inv_mem hg) hjk.inv (δ := twoPointElt hg • δ)
    (δ' := δ) (by change (δ : Ω) = g⁻¹ • g • (δ : Ω); rw [inv_smul_smul])
  rw [← hδ, ← h1, ← h2]

@[expose] noncomputable def transport {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {j k : C.D.ι} (hjk : C.MapsDir g j k) : C.D.Ψc j ≃ C.D.Ψc k where
  toFun := C.transportFun hg j k
  invFun := C.transportFun (inv_mem hg) k j
  left_inv := C.transportFun_left_inv hg hjk
  right_inv c := by
    have := C.transportFun_left_inv (inv_mem hg) hjk.inv c
    simp only [inv_inv] at this
    exact this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_smul_eq_transport {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {j k : C.D.ι} (hjk : C.MapsDir g j k) {δ δ' : holtDelta G Ω α β}
    (e : (δ' : Ω) = g • (δ : Ω)) : C.D.coord δ' k = C.transport hg hjk (C.D.coord δ j) :=
  C.coord_smul_eq_transportFun hg hjk e

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_γ {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {j k : C.D.ι}
    (hjk : C.MapsDir g j k) (hgγ : g • (C.γ : Ω) = C.γ) :
    C.transport hg hjk (C.D.coord C.γ j) = C.D.coord C.γ k :=
  (C.coord_smul_eq_transport hg hjk hgγ.symm).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem permCongr_mem_Qimg {p : G} (hp : p ∈ C.calP) {j k : C.D.ι}
    (hjk : C.MapsDir p j k) {u : Equiv.Perm (C.D.Ψc j)} (hu : u ∈ C.Qimg j) :
    (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hjk).permCongr u ∈ C.Qimg k := by
  have hpS := C.mem_stabilizer_pair_of_mem_calP hp
  set φ := C.transport hpS hjk
  obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg hu
  have hpγ := C.smul_γ_of_mem_calP hp
  have hpinvγ : p⁻¹ • (C.γ : Ω) = C.γ := by rw [inv_smul_eq_iff, hpγ]
  have hmem : p * (q : G) * p⁻¹ ∈ C.kerC k := by
    change p * (q : G) * p⁻¹ ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G (C.hyper k)
    have hpG := C.calG_le_inf (C.calP_le_calG hp)
    refine Subgroup.mem_inf.mpr ⟨(stabilizer G α ⊓ stabilizer G β).mul_mem
      ((stabilizer G α ⊓ stabilizer G β).mul_mem hpG (C.kerC_le_inf j q.2))
      ((stabilizer G α ⊓ stabilizer G β).inv_mem hpG), ?_⟩
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨δ, rfl, hδ⟩
    set δ'' := twoPointElt (inv_mem hpS) • δ
    have h1 : C.D.coord δ'' j = C.D.coord C.γ j := by
      rw [C.coord_smul_eq_transport (inv_mem hpS) hjk.inv (δ := δ) rfl, hδ]
      exact C.transport_γ (inv_mem hpS) hjk.inv hpinvγ
    have h2 : (q : G) • ((δ'' : holtDelta G Ω α β) : Ω) = δ'' := C.smul_eq_of_mem_kerC q.2 h1
    change (q : G) • (p⁻¹ • (δ : Ω)) = p⁻¹ • (δ : Ω) at h2
    rw [mul_smul, mul_smul, h2, smul_inv_smul]
  refine ⟨⟨_, hmem⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨C.calP.mul_mem
    (C.calP.mul_mem hp hqP) (C.calP.inv_mem hp), hmem⟩), Equiv.ext fun c => ?_⟩
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) k c)
  have hδ : C.D.coord δ k = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  set δ₁ := twoPointElt (inv_mem hpS) • δ
  set δ₂ := twoPointElt (C.kerC_le_stabilizer_pair j q.2) • δ₁
  set δ₃ := twoPointElt hpS • δ₂
  have e₃ : (δ₃ : Ω) = (p * (q : G) * p⁻¹) • (δ : Ω) := by
    change p • (q : G) • p⁻¹ • (δ : Ω) = _
    rw [mul_smul, mul_smul]
  rw [← hδ, ← C.coord_smul_eq_kerCHom ⟨_, hmem⟩ e₃,
    C.coord_smul_eq_transport hpS hjk (δ := δ₂) rfl, C.coord_smul_eq_kerCHom q rfl,
    C.coord_smul_eq_transport (inv_mem hpS) hjk.inv (δ := δ) rfl]
  rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_image_orbit_subset {p : G} (hp : p ∈ C.calP) {j k : C.D.ι}
    (hjk : C.MapsDir p j k) (c : C.D.Ψc j) :
    (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hjk) '' orbit (C.Qimg j) c ⊆
      orbit (C.Qimg k) (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hjk c) := by
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  refine ⟨⟨_, C.permCongr_mem_Qimg hp hjk u.2⟩, ?_⟩
  change (C.transport _ hjk).permCongr (u : Equiv.Perm (C.D.Ψc j)) (C.transport _ hjk c) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_orbit_transport {p : G} (hp : p ∈ C.calP) {j k : C.D.ι}
    (hjk : C.MapsDir p j k) (c : C.D.Ψc j) :
    Nat.card (orbit (C.Qimg k) (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hjk c)) =
      Nat.card (orbit (C.Qimg j) c) := by
  set φ := C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hjk
  set ψ := C.transport (C.mem_stabilizer_pair_of_mem_calP (C.calP.inv_mem hp)) hjk.inv
  have hψφ : ψ (φ c) = c := φ.left_inv c
  have h1 := Set.ncard_le_ncard (C.transport_image_orbit_subset hp hjk c) (Set.toFinite _)
  have h2 := Set.ncard_le_ncard (C.transport_image_orbit_subset (C.calP.inv_mem hp) hjk.inv
    (φ c)) (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ φ.injective] at h1
  rw [Set.ncard_image_of_injective _ ψ.injective] at h2
  change _ ≤ (orbit (C.Qimg j) (ψ (φ c))).ncard at h2
  rw [hψφ] at h2
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact le_antisymm h2 h1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_Ψc_eq_of_mapsDir {p : G} (hp : p ∈ C.calP) {j k : C.D.ι}
    (hjk : C.MapsDir p j k) : Fintype.card (C.D.Ψc j) = Fintype.card (C.D.Ψc k) :=
  Fintype.card_congr (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hjk)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem orbit_Qimg_γ (j : C.D.ι) : orbit (C.Qimg j) (C.D.coord C.γ j) = {C.D.coord C.γ j} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_orbit_self _, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact C.Qimg_le_stabilizer j u.2


section DropOrbit

variable (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG)

include hS hP

omit [FaithfulSMul G Ω] in
theorem orbit_Qimg_eq (j : C.D.ι) (x : C.D.Ψc j) :
    orbit (C.Qimg j) x = orbit ↥(C.Qimg j ⊓ alternatingGroup (C.D.Ψc j)) x :=
  orbit_eq_of_fusionIsSylowIn_alternatingGroup_of_le (by have := C.D.five_le_card j; omega)
    (C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP j) (C.isPGroup_Qimg j) inf_le_left x

omit [FaithfulSMul G Ω] in
theorem orbit_Qimg_eq_of_card_eq {j : C.D.ι} {x y : C.D.Ψc j}
    (h : Nat.card (orbit (C.Qimg j) x) = Nat.card (orbit (C.Qimg j) y)) :
    orbit (C.Qimg j) x = orbit (C.Qimg j) y := by
  rw [C.orbit_Qimg_eq hS hP] at h ⊢
  rw [C.orbit_Qimg_eq hS hP j y] at h ⊢
  exact orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup
    (by have := C.D.five_le_card j; omega) (C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP j) h

omit [FaithfulSMul G Ω] in
theorem setOf_card_orbit_ne_eq {j : C.D.ι} {a : ℕ} {c : C.D.Ψc j}
    (hc : Nat.card (orbit (C.Qimg j) c) = 2 ^ a) :
    {x : C.D.Ψc j | Nat.card (orbit (C.Qimg j) x) ≠ 2 ^ a} = (orbit (C.Qimg j) c)ᶜ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  constructor
  · intro hx hxc
    exact hx (by rw [orbit_eq_iff.mpr hxc]; exact hc)
  · intro hx hxa
    exact hx (by
      rw [← C.orbit_Qimg_eq_of_card_eq hS hP (hxa.trans hc.symm)]
      exact mem_orbit_self x)

omit [FaithfulSMul G Ω] in
theorem five_le_ncard_setOf_card_orbit_ne {j : C.D.ι} {a a' : ℕ} (ha : 2 ≤ a) (ha' : 2 ≤ a')
    (haa' : a ≠ a') (hba' : (Fintype.card (C.D.Ψc j)).testBit a') :
    5 ≤ {x : C.D.Ψc j | Nat.card (orbit (C.Qimg j) x) ≠ 2 ^ a}.ncard := by
  obtain ⟨x₁, hx₁⟩ := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup
    (by have := C.D.five_le_card j; omega) (C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP j)
      a').mp hba'
  rw [← C.orbit_Qimg_eq hS hP] at hx₁
  have hpow : ∀ b, 2 ≤ b → 4 ≤ 2 ^ b := fun b hb => by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hγ₁ : C.D.coord C.γ j ∉ orbit (C.Qimg j) x₁ := by
    intro h
    rw [← orbit_eq_iff.mpr h, C.orbit_Qimg_γ, Nat.card_unique] at hx₁
    have := hpow a' ha'
    omega
  have hsub : insert (C.D.coord C.γ j) (orbit (C.Qimg j) x₁) ⊆
      {x : C.D.Ψc j | Nat.card (orbit (C.Qimg j) x) ≠ 2 ^ a} := by
    refine Set.insert_subset ?_ fun y hy => ?_
    · change Nat.card (orbit (C.Qimg j) (C.D.coord C.γ j)) ≠ 2 ^ a
      rw [C.orbit_Qimg_γ, Nat.card_unique]
      have := hpow a ha
      omega
    · change Nat.card (orbit (C.Qimg j) y) ≠ 2 ^ a
      rw [orbit_eq_iff.mpr hy, hx₁]
      exact fun h => haa' (Nat.pow_right_injective le_rfl h).symm
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hγ₁ (Set.toFinite _), ← Nat.card_coe_set_eq, hx₁] at h1
  have := hpow a' ha'
  omega

omit [FaithfulSMul G Ω] in
theorem exists_sweep_of_card_orbit {j : C.D.ι} {a : ℕ} (ha : 2 ≤ a) {δ : holtDelta G Ω α β}
    (hδ : Nat.card (orbit (C.Qimg j) (C.D.coord δ j)) = 2 ^ a) {Λc : ∀ l, Set (C.D.Ψc l)}
    (hΛ : Λc j = {x : C.D.Ψc j | Nat.card (orbit (C.Qimg j) x) ≠ 2 ^ a}) :
    ∃ v ∈ C.calP, (∀ δ' : holtDelta G Ω α β, (∀ l, C.D.coord δ' l ∈ Λc l) →
      v • (δ' : Ω) = δ') ∧ v • (δ : Ω) ≠ δ := by
  have hU := C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP j
  set U := C.Qimg j ⊓ alternatingGroup (C.D.Ψc j)
  set O := orbit U (C.D.coord δ j)
  have hOQ : orbit (C.Qimg j) (C.D.coord δ j) = O := C.orbit_Qimg_eq hS hP j _
  rw [C.setOf_card_orbit_ne_eq hS hP hδ, hOQ] at hΛ
  have hinv : ∀ u ∈ U, ∀ x ∈ Oᶜ, u x ∈ Oᶜ := by
    intro u hu x hx hux
    apply hx
    have hux' : (⟨u, hu⟩ : U) • x ∈ O := hux
    have h1 : orbit U x = O := by
      rw [← MulAction.orbit_smul (⟨u, hu⟩ : U) x]
      exact orbit_eq_iff.mpr hux'
    rw [← h1]
    exact mem_orbit_self x
  have hcard : Nat.card ↥(Oᶜᶜ) = 2 ^ a := by rw [compl_compl, ← hOQ]; exact hδ
  have hfixO := fixSet_inf_fixingSubgroup_eq hU hinv
    (by rw [hcard]; exact (Nat.even_pow' (by omega)).mpr even_two)
    (by rw [hcard]; intro h; have := Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm);
        omega)
  have hnot : C.D.coord δ j ∉ fixSet (C.D.Ψc j) (U ⊓ fixingSubgroup _ Oᶜ) := by
    rw [hfixO]
    exact fun h => h (mem_orbit_self _)
  simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hnot
  obtain ⟨w, hw, hmv⟩ := hnot
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.mp hw
  refine C.exists_mem_calP_of_mem_Qimg_fix (Subgroup.mem_inf.mp hwU).1 (Λc := Λc) ?_ hmv
  intro c hc
  rw [hΛ] at hc
  exact (mem_fixingSubgroup_iff _).mp hwfix c hc

end DropOrbit

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_i₁_iff_of_mapsDir {p : G} (hp : p ∈ C.calP) {m l : C.D.ι} (h : C.MapsDir p m l) :
    m = C.i₁ ↔ l = C.i₁ := by
  have hpS := C.mem_stabilizer_pair_of_mem_calP hp
  have hi₁ := C.mapsDir_i₁ (Subgroup.mem_inf.mp hp).2
  constructor
  · rintro rfl
    exact MapsDir.eq C hpS h hi₁
  · rintro rfl
    exact MapsDir.eq C (inv_mem hpS) h.inv hi₁.inv

theorem false_of_two_bits_ne (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hP : fusionIsSylowIn 2 C.calP C.calG)
    (htrans : ∀ j k, j ≠ C.i₁ → k ≠ C.i₁ → ∃ p ∈ C.calP, C.MapsDir p j k) {j₀ : C.D.ι}
    (hj₀ : j₀ ≠ C.i₁) {a a' : ℕ} (ha : 2 ≤ a) (ha' : 2 ≤ a') (haa' : a ≠ a')
    (hba : (Fintype.card (C.D.Ψc j₀)).testBit a)
    (hba' : (Fintype.card (C.D.Ψc j₀)).testBit a') : False := by
  classical
  set Λc : ∀ l, Set (C.D.Ψc l) := Function.update
    (fun l => {x : C.D.Ψc l | Nat.card (orbit (C.Qimg l) x) ≠ 2 ^ a}) C.i₁ Set.univ with hΛc
  have hΛ₁ : Λc C.i₁ = Set.univ := Function.update_self _ _ _
  have hΛl : ∀ l, l ≠ C.i₁ → Λc l = {x : C.D.Ψc l | Nat.card (orbit (C.Qimg l) x) ≠ 2 ^ a} :=
    fun l hl => Function.update_of_ne hl _ _
  have hcard : ∀ l, l ≠ C.i₁ → Fintype.card (C.D.Ψc l) = Fintype.card (C.D.Ψc j₀) := by
    intro l hl
    obtain ⟨p, hp, hpl⟩ := htrans j₀ l hj₀ hl
    exact (C.card_Ψc_eq_of_mapsDir hp hpl).symm
  have hstab : ∀ p ∈ C.calP, ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
      (∀ l, C.D.coord δ l ∈ Λc l) → ∀ l, C.D.coord δ' l ∈ Λc l := by
    intro p hp δ δ' e hδ l
    by_cases hl : l = C.i₁
    · subst hl
      rw [hΛ₁]
      exact Set.mem_univ _
    · obtain ⟨σ, hσ⟩ := C.exists_mapsDir (C.mem_stabilizer_pair_of_mem_calP hp)
      have hml : C.MapsDir p (σ.symm l) l := by
        have := hσ (σ.symm l)
        rwa [Equiv.apply_symm_apply] at this
      have hm : σ.symm l ≠ C.i₁ := fun h => hl ((C.eq_i₁_iff_of_mapsDir hp hml).mp h)
      have hδm := hδ (σ.symm l)
      rw [hΛl _ hm] at hδm
      rw [hΛl l hl, C.coord_smul_eq_transport (C.mem_stabilizer_pair_of_mem_calP hp) hml e]
      change Nat.card (orbit (C.Qimg l) _) ≠ 2 ^ a
      rw [C.card_orbit_transport hp hml]
      exact hδm
  have hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ l, C.D.coord δ l ∈ Λc l) → ∃ v ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ l, C.D.coord δ' l ∈ Λc l) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ := by
    intro δ hδ
    push Not at hδ
    obtain ⟨l, hl⟩ := hδ
    have hl₁ : l ≠ C.i₁ := by
      rintro rfl
      rw [hΛ₁] at hl
      exact hl (Set.mem_univ _)
    rw [hΛl l hl₁, Set.mem_ofPred_eq, not_not] at hl
    exact C.exists_sweep_of_card_orbit hS hP ha hl (hΛl l hl₁)
  have hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ l, C.D.coord δ l ∈ Λc l := by
    obtain ⟨x₀, hx₀⟩ := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup
      (by have := C.D.five_le_card j₀; omega)
      (C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP j₀) a).mp hba
    rw [← C.orbit_Qimg_eq hS hP] at hx₀
    refine ⟨C.coordEquiv.symm (Function.update (C.D.coord C.γ) j₀ x₀), fun h => ?_⟩
    have := h j₀
    rw [hΛl j₀ hj₀, C.coord_coordEquiv_symm, Function.update_self] at this
    exact this hx₀
  have hsize : ∀ l, (Λc l).ncard = 1 ∨ 5 ≤ (Λc l).ncard := by
    intro l
    right
    by_cases hl : l = C.i₁
    · subst hl
      rw [hΛ₁, C.ncard_univ_Ψc]
      exact C.D.five_le_card _
    · rw [hΛl l hl]
      exact C.five_le_ncard_setOf_card_orbit_ne hS hP ha ha' haa' (by rw [hcard l hl]; exact hba')
  have h₁ : 5 ≤ (Λc C.i₁).ncard := by
    rw [hΛ₁, C.ncard_univ_Ψc]
    exact C.D.five_le_card _
  have hj' : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard := ⟨j₀, hj₀, by
    rw [hΛl j₀ hj₀]
    exact C.five_le_ncard_setOf_card_orbit_ne hS hP ha ha' haa' hba'⟩
  have h5 := C.four_le_card_fixSet_of_stab_box hS hαβ (C.sylow.2.1.to_le inf_le_left)
    C.calP_le_calG Λc hstab hmove hne hsize h₁ hj'
  rw [C.fix_three] at h5
  omega

end AltConfig

end CFSG.Holt.H78
