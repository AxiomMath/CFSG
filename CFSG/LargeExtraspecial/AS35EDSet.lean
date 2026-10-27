module

public import CFSG.LargeExtraspecial.AS35DFourEight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

omit S in
theorem map_conj_map_conj (g h : G) (K : Subgroup G) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit S in
theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

omit S in
theorem conj_injective (g : G) : Function.Injective fun x : G => g * x * g⁻¹ :=
  fun _ _ h => mul_left_cancel (mul_right_cancel h)

theorem inv_mul_mem_M_of_conj_eq {g k : G} (h : g * S.z * g⁻¹ = k * S.z * k⁻¹) :
    k⁻¹ * g ∈ S.M := by
  rw [S.mem_M_iff]
  calc k⁻¹ * g * S.z = k⁻¹ * (g * S.z * g⁻¹) * g := by group
    _ = k⁻¹ * (k * S.z * k⁻¹) * g := by rw [h]
    _ = S.z * (k⁻¹ * g) := by group

theorem isHSet_map_conj {m : G} (hm : m ∈ S.M) {H : Subgroup G} (hH : S.IsHSet H) :
    S.IsHSet (H.map (MulAut.conj m).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQH, hO, hHM⟩ := hH
  set O := (CFSG.pCore 2 H).map H.subtype with hOdef
  have hOn : ∀ n ∈ H, ∀ x ∈ O, n * x * n⁻¹ ∈ O := by
    rintro n hn _ ⟨x, hx, rfl⟩
    exact ⟨⟨n, hn⟩ * x * ⟨n, hn⟩⁻¹, CFSG.pCore_normal.conj_mem x hx _, rfl⟩
  have hO1 : O ≠ ⊥ := fun h => hO ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
  refine ⟨?_, ?_, ?_⟩
  · rw [← S.QG_map_conj hm]
    exact map_mono hQH
  · refine pCore_ne_bot_of (X := O.map (MulAut.conj m).toMonoidHom)
      (map_mono (map_subtype_le _)) ?_ ((CFSG.pCore_isPGroup.map _).map _) ?_
    · rintro _ ⟨n, hn, rfl⟩ _ ⟨x, hx, rfl⟩
      refine ⟨n * x * n⁻¹, hOn n hn x hx, ?_⟩
      simp [mul_assoc]
    · intro h0
      exact hO1 ((map_eq_bot_iff_of_injective _ (MulAut.conj m).injective).mp h0)
  · intro hle
    apply hHM
    intro x hx
    have h1 : m * x * m⁻¹ ∈ S.M := hle ⟨x, hx, by simp⟩
    have h2 := S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hm) h1) hm
    simpa [mul_assoc] using h2

theorem isHStar_map_conj {m : G} (hm : m ∈ S.M) {H : Subgroup G} (hH : S.IsHStar H) :
    S.IsHStar (H.map (MulAut.conj m).toMonoidHom) := by
  refine ⟨S.isHSet_map_conj hm hH.1, fun H' hH' hle => ?_⟩
  have h1 := S.isHSet_map_conj (S.M.inv_mem hm) hH'
  have h2 : H'.map (MulAut.conj m⁻¹).toMonoidHom ≤ H := by
    have := map_mono (f := (MulAut.conj m⁻¹).toMonoidHom) hle
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at this
  have h3 := hH.2 _ h1 h2
  rw [← h3, map_conj_map_conj, mul_inv_cancel, map_conj_one]

theorem zConj_map_conj {m : G} (hm : m ∈ S.M) (H : Subgroup G) :
    S.zConj (H.map (MulAut.conj m).toMonoidHom) = (fun x => m * x * m⁻¹) '' S.zConj H := by
  have hmz := S.conj_z_of_mem_M hm
  have hmz' : m⁻¹ * S.z * m = S.z := by
    calc m⁻¹ * S.z * m = m⁻¹ * (m * S.z * m⁻¹) * m := by rw [hmz]
      _ = S.z := by group
  ext x
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨k * S.z * k⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * (k * S.z * k⁻¹) * m⁻¹ = m * k * (m⁻¹ * S.z * m) * k⁻¹ * m⁻¹ := by rw [hmz']; group
      _ = m * k * m⁻¹ * S.z * (m * k * m⁻¹)⁻¹ := by group
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨m * k * m⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    calc m * k * m⁻¹ * S.z * (m * k * m⁻¹)⁻¹ = m * k * (m⁻¹ * S.z * m) * k⁻¹ * m⁻¹ := by group
      _ = m * (k * S.z * k⁻¹) * m⁻¹ := by rw [hmz']; group

theorem conj_mem_ESet {m : G} (hm : m ∈ S.M) {t : G} (ht : t ∈ S.ESet) :
    m * t * m⁻¹ ∈ S.ESet := by
  obtain ⟨h, rfl, hH, h5⟩ := ht
  have heq : S.QG ⊔ S.Qa (m * h) = (S.QG ⊔ S.Qa h).map (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.map_sup, S.QG_map_conj hm, S.Qa_mul h m]
  refine ⟨m * h, by group, ?_, ?_⟩
  · rw [heq]
    exact S.isHStar_map_conj hm hH
  · rw [heq, S.zConj_map_conj hm, Set.ncard_image_of_injective _ (conj_injective m)]
    exact h5

theorem conj_mem_DSet {m : G} (hm : m ∈ S.M) {t : G} (ht : t ∈ S.DSet) :
    m * t * m⁻¹ ∈ S.DSet := by
  refine ⟨S.conj_mem_ESet hm ht.1, fun hc => ht.2 ?_⟩
  have h1 : S.z * (m * t * m⁻¹) = m * (S.z * t) * m⁻¹ := by
    calc S.z * (m * t * m⁻¹) = (m * S.z * m⁻¹) * (m * t * m⁻¹) := by rw [S.conj_z_of_mem_M hm]
      _ = m * (S.z * t) * m⁻¹ := by group
  rw [h1] at hc
  exact hc.trans (isConj_iff.mpr ⟨m, rfl⟩).symm

@[expose] def DAt (g : G) : Set G := (fun x => g * x * g⁻¹) '' S.DSet

theorem mem_DAt {g x : G} : x ∈ S.DAt g ↔ g⁻¹ * x * g ∈ S.DSet := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [mul_assoc] using hd
  · intro h
    exact ⟨g⁻¹ * x * g, h, by group⟩

theorem conj_mem_DAt {g d : G} (hd : d ∈ S.DSet) : g * d * g⁻¹ ∈ S.DAt g := ⟨d, hd, rfl⟩

theorem DAt_one : S.DAt 1 = S.DSet := by
  ext x
  rw [mem_DAt]
  simp

theorem DAt_eq_of_conj_eq {g k : G} (h : g * S.z * g⁻¹ = k * S.z * k⁻¹) :
    S.DAt g = S.DAt k := by
  have hm := S.inv_mul_mem_M_of_conj_eq h
  ext x
  rw [mem_DAt, mem_DAt]
  constructor
  · intro hx
    have := S.conj_mem_DSet hm hx
    rwa [show k⁻¹ * g * (g⁻¹ * x * g) * (k⁻¹ * g)⁻¹ = k⁻¹ * x * k by group] at this
  · intro hx
    have := S.conj_mem_DSet (S.M.inv_mem hm) hx
    rwa [show (k⁻¹ * g)⁻¹ * (k⁻¹ * x * k) * (k⁻¹ * g)⁻¹⁻¹ = g⁻¹ * x * g by group] at this

theorem conj_mem_DAt_mul {g c x : G} (hx : x ∈ S.DAt g) : c * x * c⁻¹ ∈ S.DAt (c * g) := by
  rw [mem_DAt] at hx ⊢
  rwa [show (c * g)⁻¹ * (c * x * c⁻¹) * (c * g) = g⁻¹ * x * g by group]

noncomputable abbrev HAt (h : G) : Subgroup G := S.QG ⊔ S.Qa h

theorem mem_zConj_of_ncard_eq_five {h : G} (h5 : (S.zConj (S.HAt h)).ncard = 5) :
    h * S.z * h⁻¹ ∈ S.zConj (S.HAt h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ω := S.zConj (S.HAt h) with hΩ
  have hPH : S.Qa h ≤ S.HAt h := le_sup_right
  let act : MulAction (S.Qa h) Ω :=
    { smul := fun y x => ⟨y * x * (y : G)⁻¹, conj_mem_conjIn_of_mem (hPH y.2) x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (1 : G) * x * 1⁻¹ = x
        group)
      mul_smul := fun a b x => Subtype.ext (by
        change (a * b : G) * x * (a * b : G)⁻¹ = a * (b * x * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  have hP2 : IsPGroup 2 (S.Qa h) := (S.conjBy h).isPGroup_QG
  have hcard : ¬ 2 ∣ Nat.card Ω := by
    rw [Nat.card_coe_set_eq, h5]
    decide
  obtain ⟨p, hp⟩ := hP2.nonempty_fixed_point_of_prime_not_dvd_card Ω hcard
  have hpc : ∀ q ∈ (S.conjBy h).QG, q * (p : G) = p * q := by
    intro q hq
    have h1 := congrArg Subtype.val (hp ⟨q, hq⟩)
    change q * (p : G) * q⁻¹ = p at h1
    calc q * (p : G) = q * p * q⁻¹ * q := by group
      _ = p * q := by rw [h1]
  have hp1 : (p : G) ≠ 1 := by
    obtain ⟨k, -, hk⟩ := p.2
    intro h1
    apply S.z_ne_one
    calc S.z = k⁻¹ * (k * S.z * k⁻¹) * k := by group
      _ = 1 := by rw [hk, h1]; group
  have h2 := (S.conjBy h).eq_z_of_commute_QG hpc hp1
  rw [conjBy_z] at h2
  exact h2 ▸ p.2

variable [Finite G]

theorem isHStar_of_mem_ESet {t h : G} (ht : t ∈ S.ESet) (hh : h * S.z * h⁻¹ = t) :
    S.IsHStar (S.HAt h) ∧ (S.zConj (S.HAt h)).ncard = 5 := by
  obtain ⟨h', hh', hH, h5⟩ := ht
  rw [HAt, S.Qa_eq_of_conj_eq (hh.trans hh'.symm)]
  exact ⟨hH, h5⟩

theorem ne_z_of_mem_ESet {t : G} (ht : t ∈ S.ESet) : t ≠ S.z := by
  obtain ⟨h, rfl, hH, -⟩ := ht
  intro htz
  have hQa : S.Qa h = S.QG := by
    rw [S.Qa_eq_of_conj_eq (g := h) (h := 1) (by rw [htz]; group), S.Qa_one]
  apply hH.1.2.2
  rw [hQa, sup_idem]
  exact S.QG_le_M

omit [Finite G] in
theorem mem_M_of_conj_eq_z {m : G} (hm : m * S.z * m⁻¹ = S.z) : m ∈ S.M := by
  rw [S.mem_M_iff]
  calc m * S.z = m * S.z * m⁻¹ * m := by group
    _ = S.z * m := by rw [hm]

@[expose] def SixFourConcl : Prop :=
  ∀ H : Subgroup G, S.IsHStar H → S.IsAFive H ∧
    ∀ g ∈ H, g ∉ S.M → H = S.QG ⊔ S.Qa g ∧ ¬ IsConj S.z (S.z * (g * S.z * g⁻¹))

end Setting

namespace Asc77

theorem IsAFiveAt.exists_conj {G : Type} [Group G] {z : G} {H : Subgroup G}
    (hA : IsAFiveAt z H) {p p' : G} (hp : p ∈ conjIn z H) (hp' : p' ∈ conjIn z H) (hpz : p ≠ z)
    (hp'z : p' ≠ z) : ∃ m ∈ H, m * z * m⁻¹ = z ∧ m * p * m⁻¹ = p' := by
  by_cases hpp : p = p'
  · exact ⟨1, H.one_mem, by group, by rw [← hpp]; group⟩
  obtain ⟨_, _, h5, -, -, -, hsurj⟩ := hA
  have hzΩ : z ∈ conjIn z H := self_mem_conjIn z H
  have hsub : ({z, p, p'} : Set G) ⊆ conjIn z H := by
    rintro x (rfl | rfl | rfl)
    · exact hzΩ
    · exact hp
    · exact hp'
  have h3 : ({z, p, p'} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hpz.symm, hp'z.symm⟩), Set.ncard_pair hpp]
  have hdiff : (conjIn z H \ {z, p, p'}).ncard = 2 := by
    rw [Set.ncard_sdiff hsub, h5, h3]
  obtain ⟨a, ha⟩ : (conjIn z H \ {z, p, p'}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha
  obtain ⟨haΩ, haz, hap, hap'⟩ := ha
  set Z : conjIn z H := ⟨z, hzΩ⟩
  set P : conjIn z H := ⟨p, hp⟩
  set P' : conjIn z H := ⟨p', hp'⟩
  set A : conjIn z H := ⟨a, haΩ⟩
  have hne : ∀ {x y : conjIn z H}, (x : G) ≠ y → x ≠ y :=
    fun h h' => h (congrArg Subtype.val h')
  have hPA : P ≠ A := hne (Ne.symm hap)
  have hPP' : P ≠ P' := hne hpp
  have hZP : Z ≠ P := hne (Ne.symm hpz)
  have hZP' : Z ≠ P' := hne (Ne.symm hp'z)
  have hZA : Z ≠ A := hne (Ne.symm haz)
  have hP'P : P' ≠ P := hne (Ne.symm hpp)
  have hP'A : P' ≠ A := hne (Ne.symm hap')
  have hσ : Equiv.Perm.sign (Equiv.swap P A * Equiv.swap P P') = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hPA, Equiv.Perm.sign_swap hPP']
    decide
  obtain ⟨k, hk⟩ := hsurj _ hσ
  refine ⟨k, k.2, ?_, ?_⟩
  · have e := congrArg Subtype.val (DFunLike.congr_fun hk Z)
    rw [conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZP hZP',
      Equiv.swap_apply_of_ne_of_ne hZP hZA] at e
    exact e
  · have e := congrArg Subtype.val (DFunLike.congr_fun hk P)
    rw [conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hP'P hP'A] at e
    exact e

end Asc77

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem zConj_diff_subset_DSet (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {p : G} (hp : p ∈ S.zConj (S.HAt h)) (hpz : p ≠ S.z) :
    p ∈ S.DSet := by
  obtain ⟨hH, h5⟩ := S.isHStar_of_mem_ESet ht.1 hh
  have htH : t ∈ S.zConj (S.HAt h) := hh ▸ S.mem_zConj_of_ncard_eq_five h5
  obtain ⟨m, -, hmz, hmp⟩ :=
    (hS _ hH).1.1.exists_conj htH hp (S.ne_z_of_mem_ESet ht.1) hpz
  rw [← hmp]
  exact S.conj_mem_DSet (S.mem_M_of_conj_eq_z hmz) ht

theorem z_mem_DAt (hS : S.SixFourConcl) {t g : G} (ht : t ∈ S.DSet) (hg : g * S.z * g⁻¹ = t) :
    S.z ∈ S.DAt g := by
  obtain ⟨-, h5⟩ := S.isHStar_of_mem_ESet ht.1 hg
  obtain ⟨x, hxH, hx⟩ := S.mem_zConj_of_ncard_eq_five h5
  rw [S.DAt_eq_of_conj_eq hx.symm, mem_DAt]
  refine S.zConj_diff_subset_DSet hS ht hg ⟨x⁻¹, (S.HAt g).inv_mem hxH, by rw [inv_inv]⟩ ?_
  intro h1
  apply S.ne_z_of_mem_ESet ht.1
  rw [← hg, ← hx]
  calc x * S.z * x⁻¹ = x * (x⁻¹ * S.z * x) * x⁻¹ := by rw [h1]
    _ = S.z := by group

theorem mem_DAt_symm (hS : S.SixFourConcl) {g k : G} (hk : k * S.z * k⁻¹ ∈ S.DAt g) :
    g * S.z * g⁻¹ ∈ S.DAt k := by
  rw [mem_DAt] at hk ⊢
  have h1 := S.z_mem_DAt hS hk (g := g⁻¹ * k) (by group)
  rw [mem_DAt] at h1
  rwa [show (g⁻¹ * k)⁻¹ * S.z * (g⁻¹ * k) = k⁻¹ * (g * S.z * g⁻¹) * k by group] at h1

theorem DSet_nonempty (hS : S.SixFourConcl) (hH : ∃ H : Subgroup G, S.IsHSet H) :
    S.DSet.Nonempty := by
  obtain ⟨H, hH⟩ := hH
  obtain ⟨H₀, -, hmin⟩ := (Set.toFinite {H : Subgroup G | S.IsHSet H}).exists_le_minimal hH
  have hH₀ : S.IsHStar H₀ := ⟨hmin.prop, fun H' hH' hle => le_antisymm hle (hmin.2 hH' hle)⟩
  obtain ⟨g, hgH, hgM⟩ := Set.not_subset.mp hH₀.1.2.2
  obtain ⟨hA, hrest⟩ := hS H₀ hH₀
  obtain ⟨hHeq, hD⟩ := hrest g hgH hgM
  obtain ⟨_, _, h5, -⟩ := hA.1
  refine ⟨g * S.z * g⁻¹, ⟨g, rfl, hHeq ▸ hH₀, ?_⟩, hD⟩
  rw [← hHeq]
  exact h5

end Setting

end CFSG.LargeExtraspecial
