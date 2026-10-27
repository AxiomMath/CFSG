module

public import CFSG.ClassicalInvolution.Asc77.AscS24BMu
public import CFSG.ClassicalInvolution.AschTight.Hall196Syl
public import CFSG.ClassicalInvolution.Asc77.AscS24BNorm

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped Pointwise

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_normalizer_MGrp (hΩ : HypOmegaMod p f Ω) {W : Subgroup G} :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (MGrp Ω W : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (W : Set G), conjSub n (MGrp Ω W) ≤ MGrp Ω W := by
    intro n hn
    rw [conjSub_le_iff]
    refine iSup₂_le fun R hR => ?_
    rw [← conjSub_le_iff]
    exact Thompson.le_MGrp_of_mem_D (Thompson.conjSub_mem_D hΩ hR hn)
  intro n hn
  refine mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (key n hn) ?_)
  have h := conjSub_mono (n := n) (key n⁻¹ (Subgroup.inv_mem _ hn))
  rwa [conjSub_conjSub_inv] at h

@[expose] noncomputable def piM (Ω : Set (Subgroup G)) (W : Subgroup G) :
    ↥(MGrp Ω W) →* ↥(muGroup Ω W) :=
  MonoidHom.mk' (fun x => ⟨Thompson.piG W x, Thompson.piG_mem_muGroup (Subgroup.mem_sup_left x.2)⟩)
    (fun x y => Subtype.ext (Thompson.piG_mul (Thompson.MGrp_le_normalizer Ω W x.2)
      (Thompson.MGrp_le_normalizer Ω W y.2)))

omit [Finite G] in
theorem piM_apply {W : Subgroup G} (x : ↥(MGrp Ω W)) :
    (piM Ω W x : NQuot (W ⊔ OCW W)) = Thompson.piG W x := rfl

omit [Finite G] in
theorem piM_surjective (W : Subgroup G) : Function.Surjective (piM Ω W) := by
  rintro ⟨q, hq⟩
  obtain ⟨m, hm, rfl⟩ := Thompson.mem_muGroup_iff.mp hq
  have hle : MGrp Ω W ≤ Subgroup.normalizer (OCW W : Set G) :=
    (Thompson.MGrp_le_normalizer Ω W).trans (Thompson.normalizer_le_normalizer_OCW W)
  have hm' : m ∈ ((MGrp Ω W : Set G) * (OCW W : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]; exact hm
  obtain ⟨m₁, hm₁, o, ho, rfl⟩ := hm'
  refine ⟨⟨m₁, hm₁⟩, Subtype.ext ?_⟩
  change Thompson.piG W m₁ = Thompson.piG W (m₁ * o)
  rw [Thompson.piG_mul (Thompson.MGrp_le_normalizer Ω W hm₁)
    (Thompson.OCW_le_normalizer W ho), Thompson.piG_of_mem_sup (Subgroup.mem_sup_right ho),
    mul_one]

open Equiv in
theorem perm4_conj_swap : ∀ g : Perm (Fin 4), ∀ σ ∈ S4.swaps4, g * σ * g⁻¹ ∈ S4.swaps4 := by
  decide +kernel

omit [Finite G] in
theorem eq_one_of_pow_three {Q : Type*} [Group Q] {H : Subgroup Q} (hH : IsPGroup 2 H) {y : Q}
    (hy : y ∈ H) (h3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨y, hy⟩
  have hk' : y ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem isSylow2In_P : IsSylow2In ((S : Subgroup G) ⊓ MGrp Ω W) (MGrp Ω W) :=
  AschTight.Hall196.isSylow2In_inf_of_le_normalizer S
    (C.le_normalizer_W.trans (le_normalizer_MGrp C.hs.stand.hyp))

include C in
theorem exists_swap : ∃ x ∈ (S : Subgroup G) ⊓ MGrp Ω W, conjSub x K = K' := by
  have hP := C.isSylow2In_P
  let PS : Sylow 2 ↥(MGrp Ω W) := AscQuot.sylowOfIsSylow2In' hP
  let PB : Sylow 2 ↥(muGroup Ω W) := PS.mapSurjective (piM_surjective W)
  have hmemPB : ∀ q, q ∈ (PB : Subgroup ↥(muGroup Ω W)) ↔
      ∃ x : ↥(MGrp Ω W), (x : G) ∈ (S : Subgroup G) ∧ piM Ω W x = q := by
    intro q
    change q ∈ (PS : Subgroup ↥(MGrp Ω W)).map (piM Ω W) ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (Subgroup.mem_subgroupOf.mp hx).1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩, rfl⟩
  have hcardμ : Nat.card ↥(muGroup Ω W) = 24 := by
    rw [Nat.card_congr C.D.φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have h8 : 2 ^ 3 ∣ Nat.card ↥(PB : Subgroup ↥(muGroup Ω W)) :=
    Sylow.pow_dvd_card_of_pow_dvd_card PB (by rw [hcardμ]; norm_num)
  set ra := T7D.imgQ C.D.F.ρ with hra
  set ta := T7D.imgQ C.D.F.ρ' with hta
  have hrM : C.D.F.ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr
  have hraP : ra ∈ (PB : Subgroup ↥(muGroup Ω W)) :=
    (hmemPB ra).mpr ⟨⟨_, hrM⟩, C.hd.hR.2.2 C.r_mem_R, rfl⟩
  have hab : C.D.φ ra ≠ C.D.φ ta := fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : C.D.φ ra * C.D.φ ta = C.D.φ ta * C.D.φ ra := by
    rw [← map_mul, ← map_mul, C.D.hcomm]
  have hsw_r := C.φ_imgQ_mem C.D.F.ρ
  have hsw_t := C.φ_imgQ_mem C.D.F.ρ'
  obtain ⟨h, hhP, hh⟩ : ∃ h ∈ (PB : Subgroup ↥(muGroup Ω W)),
      ¬ (h = 1 ∨ h = ra ∨ h = ta ∨ h = ra * ta) := by
    by_contra hcon
    push Not at hcon
    have hsub : ((PB : Subgroup ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
        {1, ra, ta, ra * ta} := by
      intro x hx
      rcases hcon x hx with h | h | h | h <;> simp [h]
    have hle : Nat.card ↥(PB : Subgroup ↥(muGroup Ω W)) ≤ 4 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
      refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
      rw [Set.ncard_singleton]
    have hpos : 0 < Nat.card ↥(PB : Subgroup ↥(muGroup Ω W)) := Nat.card_pos
    obtain ⟨k, hk⟩ := h8
    omega
  have hnc : h * ra ≠ ra * h := by
    intro hc
    have hc' : C.D.φ h * C.D.φ ra = C.D.φ ra * C.D.φ h := by rw [← map_mul, ← map_mul, hc]
    rcases perm4_cent_swap (C.D.φ h) _ hsw_r _ hsw_t hab hcomm hc' with e | e | e | e
    · exact hh (Or.inl (C.D.φ.injective (e.trans (map_one C.D.φ).symm)))
    · exact hh (Or.inr (Or.inl (C.D.φ.injective e)))
    · exact hh (Or.inr (Or.inr (Or.inl (C.D.φ.injective e))))
    · exact hh (Or.inr (Or.inr (Or.inr (C.D.φ.injective (e.trans (map_mul C.D.φ ra ta).symm)))))
  have hcP : h * ra * h⁻¹ ∈ (PB : Subgroup ↥(muGroup Ω W)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhP hraP) (Subgroup.inv_mem _ hhP)
  have hcsw : C.D.φ (h * ra * h⁻¹) ∈ S4.swaps4 := by
    rw [map_mul, map_mul, map_inv]
    exact perm4_conj_swap _ _ hsw_r
  have hcab : h * ra * h⁻¹ = ta := by
    by_contra hne
    have hne' : C.D.φ (h * ra * h⁻¹) ≠ C.D.φ ta := fun e => hne (C.D.φ.injective e)
    have hne'' : C.D.φ (h * ra * h⁻¹) ≠ C.D.φ ra := by
      intro e
      apply hnc
      have e' := C.D.φ.injective e
      calc h * ra = h * ra * h⁻¹ * h := by group
        _ = ra * h := by rw [e']
    obtain ⟨h3, h1⟩ := perm4_mul_swap_cube _ hsw_r _ hsw_t hab hcomm _ hcsw hne'' hne'
    have hy : ra * (h * ra * h⁻¹) ∈ (PB : Subgroup ↥(muGroup Ω W)) := Subgroup.mul_mem _ hraP hcP
    have hy3 : (ra * (h * ra * h⁻¹)) ^ 3 = 1 := by
      apply C.D.φ.injective
      rw [map_pow, map_mul, h3, map_one]
    apply h1
    rw [← map_mul, eq_one_of_pow_three PB.isPGroup' hy hy3, map_one]
  obtain ⟨x, hxS, hx⟩ := (hmemPB h).mp hhP
  have hxN : (x : G) ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W x.2
  refine ⟨x, ⟨hxS, x.2⟩, ?_⟩
  have himg : (T7D.conjRep C.D.c.hΩ hxN C.D.F.ρ).img = C.D.F.ρ'.img := by
    rw [T7D.conjRep_img]
    have e := congrArg Subtype.val hcab
    have hxv : Thompson.piG W (x : G) = (h : NQuot (W ⊔ OCW W)) := by
      rw [← hx]; rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [hxv]
    exact e
  have hKK := C.D.c.K_eq_of_img_eq _ _ himg
  change conjSub (x : G) C.D.F.ρ.K = C.D.F.ρ'.K at hKK
  exact (congrArg (conjSub (x : G)) C.hK).symm.trans (hKK.trans C.hK')

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
