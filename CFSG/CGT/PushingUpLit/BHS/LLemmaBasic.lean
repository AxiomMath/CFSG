module

public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin.A1b CFSG.RankThree.PartOne

variable {Γ : Type} [Group Γ]

@[expose] def starIn (X A U : Subgroup Γ) : Subgroup Γ :=
  ⨆ (g : Γ) (_ : g ∈ X) (_ : conjSub g A ≤ U), conjSub g A

theorem starIn_le {X A U : Subgroup Γ} : starIn X A U ≤ U :=
  iSup₂_le fun _ _ => iSup_le fun h => h

theorem le_starIn {X A U : Subgroup Γ} {g : Γ} (hg : g ∈ X) (h : conjSub g A ≤ U) :
    conjSub g A ≤ starIn X A U :=
  le_iSup₂_of_le g hg (le_iSup_of_le h le_rfl)

theorem starIn_mono {X A U V : Subgroup Γ} (h : U ≤ V) : starIn X A U ≤ starIn X A V :=
  iSup₂_le fun _ hg => iSup_le fun hgU => le_starIn hg (hgU.trans h)

theorem starIn_conjSub_le {X A U : Subgroup Γ} {h : Γ} (hh : h ∈ X) :
    starIn X A (conjSub h U) ≤ conjSub h (starIn X A U) := by
  refine iSup₂_le fun g hg => iSup_le fun hgU => ?_
  have h1 : conjSub (h⁻¹ * g) A ≤ U := by
    have := conjSub_mono h⁻¹ hgU
    rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  have h2 := conjSub_mono h (le_starIn (X.mul_mem (X.inv_mem hh) hg) h1)
  rwa [← conjSub_mul, mul_inv_cancel_left] at h2

theorem starIn_conjSub {X A U : Subgroup Γ} {h : Γ} (hh : h ∈ X) :
    starIn X A (conjSub h U) = conjSub h (starIn X A U) := by
  refine le_antisymm (starIn_conjSub_le hh) ?_
  have h1 := starIn_conjSub_le (A := A) (U := conjSub h U) (X.inv_mem hh)
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h1
  have h2 := conjSub_mono h h1
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h2

theorem mem_normalizer_starIn {X A U : Subgroup Γ} {x : Γ} (hx : x ∈ X)
    (hxU : x ∈ Subgroup.normalizer (U : Set Γ)) :
    x ∈ Subgroup.normalizer (starIn X A U : Set Γ) := by
  have h1 : conjSub x U = U := by
    unfold conjSub
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxU
  have h2 : conjSub x (starIn X A U) = starIn X A U := by
    rw [← starIn_conjSub hx, h1]
  unfold conjSub at h2
  rw [MulEquiv.toMonoidHom_eq_coe] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem card_conjSub (g : Γ) (H : Subgroup Γ) : Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_starIn_conjSub {X A U : Subgroup Γ} {h : Γ} (hh : h ∈ X) :
    Nat.card (starIn X A (conjSub h U)) = Nat.card (starIn X A U) := by
  rw [starIn_conjSub hh, card_conjSub]

theorem conjSub_self_of_mem {H : Subgroup Γ} {a : Γ} (ha : a ∈ H) : conjSub a H = H := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem ha h) (H.inv_mem ha)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) hx) ha

theorem conjSub_sup (g : Γ) (H K : Subgroup Γ) :
    conjSub g (H ⊔ K) = conjSub g H ⊔ conjSub g K :=
  Subgroup.map_sup _ _ _

theorem mem_sup_iff_of_le_normalizer {K R : Subgroup Γ}
    (h : K ≤ Subgroup.normalizer (R : Set Γ)) {x : Γ} :
    x ∈ K ⊔ R ↔ ∃ k ∈ K, ∃ r ∈ R, x = k * r := by
  constructor
  · intro hx
    let P : Subgroup Γ :=
      { carrier := {x | ∃ k ∈ K, ∃ r ∈ R, x = k * r}
        one_mem' := ⟨1, K.one_mem, 1, R.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨k₁, hk₁, r₁, hr₁, rfl⟩ ⟨k₂, hk₂, r₂, hr₂, rfl⟩
          refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₂⁻¹ * r₁ * k₂ * r₂, ?_, by group⟩
          refine R.mul_mem ?_ hr₂
          have := (Subgroup.mem_normalizer_iff.mp (h (K.inv_mem hk₂)) r₁).mp hr₁
          simpa [mul_assoc] using this
        inv_mem' := by
          rintro _ ⟨k, hk, r, hr, rfl⟩
          refine ⟨k⁻¹, K.inv_mem hk, k * r⁻¹ * k⁻¹, ?_, by group⟩
          have := (Subgroup.mem_normalizer_iff.mp (h hk) r⁻¹).mp (R.inv_mem hr)
          simpa [mul_assoc] using this }
    have hKP : K ≤ P := fun k hk => ⟨k, hk, 1, R.one_mem, by simp⟩
    have hRP : R ≤ P := fun r hr => ⟨1, K.one_mem, r, hr, by simp⟩
    exact sup_le hKP hRP hx
  · rintro ⟨k, hk, r, hr, rfl⟩
    exact (K ⊔ R).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hr)

theorem conjSub_inf (g : Γ) (H K : Subgroup Γ) :
    conjSub g (H ⊓ K) = conjSub g H ⊓ conjSub g K :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem isPGroup_conjSub {p : ℕ} {H : Subgroup Γ} (hH : IsPGroup p H) (g : Γ) :
    IsPGroup p (conjSub g H) :=
  hH.map _

theorem conjSub_eq_of_conjSub_le [Finite Γ] {x : Γ} {H : Subgroup Γ} (h : conjSub x H ≤ H) :
    conjSub x H = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSub])

theorem conjSub_lt_of_lt [Finite Γ] {X M : Subgroup Γ} (hMX : M < X) {x : Γ} (hx : x ∈ X) :
    conjSub x M < X := by
  have h1 : conjSub x M ≤ X := by
    have := conjSub_mono x hMX.le
    rwa [conjSub_self_of_mem hx] at this
  refine lt_of_le_of_ne h1 fun h => ?_
  have h2 := Nine.card_lt_of_lt hMX
  have h3 : Nat.card (conjSub x M) = Nat.card X := by rw [h]
  rw [card_conjSub] at h3
  omega

theorem isSylowOf_of_le_of_le {X Y T : Subgroup Γ} (hT : IsSylowOf 2 T X) (hTY : T ≤ Y)
    (hYX : Y ≤ X) : IsSylowOf 2 T Y := by
  refine ⟨hTY, hT.2.1, fun hd => hT.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T Y X hTY hYX]
  exact dvd_mul_of_dvd_left hd _

theorem isSylowOf_conjSub {X T : Subgroup Γ} (hT : IsSylowOf 2 T X) (g : Γ) :
    IsSylowOf 2 (conjSub g T) (conjSub g X) := by
  refine ⟨conjSub_mono g hT.1, hT.2.1.map _, ?_⟩
  unfold conjSub
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hT.2.2

theorem exists_conj_le_of_isSylowOf [Finite Γ] {K T R : Subgroup Γ} (hT : IsSylowOf 2 T K)
    (hR : IsPGroup 2 R) (hRK : R ≤ K) : ∃ k ∈ K, conjSub k R ≤ T := by
  have hTp : IsPGroup 2 (T.subgroupOf K) := hT.2.1.comap_subtype (K := K)
  have hRp : IsPGroup 2 (R.subgroupOf K) := hR.comap_subtype (K := K)
  obtain ⟨S, hS⟩ := hRp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥K (hTp.toSylow hT.2.2) S
  refine ⟨(h : Γ)⁻¹, (h⁻¹).2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (⟨x, hRK hx⟩ : K) ∈ (S : Subgroup K) := hS hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  have hxS2 : ((MulAut.conj h)⁻¹ • (⟨x, hRK hx⟩ : K)) ∈ T.subgroupOf K := hxS
  have hmem : (h⁻¹ * ⟨x, hRK hx⟩ * h : K) ∈ T.subgroupOf K := by
    simpa [MulAut.inv_def, MulAut.conj_symm_apply] using hxS2
  have hmem' := Subgroup.mem_subgroupOf.mp hmem
  simpa [MulAut.conj_apply] using hmem'

end CFSG.CGT.PushingUpLit.BHS
