module

public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarAbstract
public import CFSG.Goldschmidt.Steps.GoldType

public section

namespace CFSG.ComponentClassification.AS81.Qbar

open Subgroup CFSG.Open CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  normalizer_transitive_center benderBorel_sylowCenter)
open CFSG.ComponentClassification.AschbacherToolkit.BenderExt (benderData_of_isBenderGroup)
open scoped Pointwise

section Restrict

variable {L : Type*} [Group L] {H : Type*} [Group H]

@[expose] def restrictAut (ρ : H →* MulAut L) (W : Subgroup L)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) : H →* MulAut W where
  toFun h :=
    { toFun := fun w => ⟨ρ h w, hW h w w.2⟩
      invFun := fun w => ⟨ρ h⁻¹ w, hW h⁻¹ w w.2⟩
      left_inv := fun w => Subtype.ext (by
        change ρ h⁻¹ (ρ h w) = w
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun w => Subtype.ext (by
        change ρ h (ρ h⁻¹ w) = w
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun a b => Subtype.ext (map_mul (ρ h) (a : L) (b : L)) }
  map_one' := MulEquiv.ext fun w => Subtype.ext (by
    change ρ 1 w = w
    rw [map_one, MulAut.one_apply])
  map_mul' := fun a b => MulEquiv.ext fun w => Subtype.ext (by
    change ρ (a * b) w = ρ a (ρ b w)
    rw [map_mul, MulAut.mul_apply])

theorem apply_eq_of_mem_ker {ρ : H →* MulAut L} {W : Subgroup L}
    {hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W} {h : H} (hh : h ∈ (restrictAut ρ W hW).ker) {w : L}
    (hw : w ∈ W) : ρ h w = w := by
  rw [MonoidHom.mem_ker] at hh
  have := congrArg (fun e : MulAut W => (e ⟨w, hw⟩ : L)) hh
  exact this

@[expose] def conjAutOn (W S : Subgroup L) (hS : S ≤ normalizer (W : Set L)) : S →* MulAut W :=
  restrictAut (MulAut.conj.comp S.subtype) W fun s w hw =>
    (mem_normalizer_iff.mp (hS s.2) w).mp hw

theorem conjAutOn_apply (W S : Subgroup L) (hS : S ≤ normalizer (W : Set L)) (s : S) (w : W) :
    (conjAutOn W S hS s w : L) = s * w * (s : L)⁻¹ :=
  rfl

theorem restrictAut_mul_conjAutOn (ρ : H →* MulAut L) {W S : Subgroup L}
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (hS : S ≤ normalizer (W : Set L)) (h : H) (s : S)
    (hs : ρ h s ∈ S) :
    restrictAut ρ W hW h * conjAutOn W S hS s * (restrictAut ρ W hW h)⁻¹ =
      conjAutOn W S hS ⟨ρ h s, hs⟩ := by
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [← map_inv]
  change ρ h (s * ρ h⁻¹ w * (s : L)⁻¹) = ρ h s * w * (ρ h s)⁻¹
  have e1 : ρ h (ρ h⁻¹ (w : L)) = w := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [map_mul, map_mul, e1, map_inv]

theorem restrictAut_mem_normalizer_range (ρ : H →* MulAut L) {W S : Subgroup L}
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (hS : S ≤ normalizer (W : Set L))
    (hρS : ∀ h, ∀ s ∈ S, ρ h s ∈ S) (h : H) :
    restrictAut ρ W hW h ∈ normalizer ((conjAutOn W S hS).range : Set (MulAut W)) := by
  have key : ∀ k : H, ∀ c ∈ (conjAutOn W S hS).range,
      restrictAut ρ W hW k * c * (restrictAut ρ W hW k)⁻¹ ∈ (conjAutOn W S hS).range := by
    rintro k _ ⟨s, rfl⟩
    rw [restrictAut_mul_conjAutOn ρ hW hS k s (hρS k s s.2)]
    exact ⟨_, rfl⟩
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key h c, fun hc => ?_⟩
  have := key h⁻¹ _ hc
  rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at this

end Restrict

section Normalizer

variable {L : Type*} [Group L] [Finite L]

theorem exists_apply_eq_of_maps_to (α : MulAut L) {W : Subgroup L} (hα : ∀ w ∈ W, α w ∈ W)
    {w : L} (hw : w ∈ W) : ∃ w' ∈ W, α w' = w := by
  let f : W → W := fun v => ⟨α v, hα v v.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (α.injective (congrArg Subtype.val hab))
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem apply_mem_normalizer (α : MulAut L) {T : Subgroup L} (hα : ∀ t ∈ T, α t ∈ T) {n : L}
    (hn : n ∈ normalizer (T : Set L)) : α n ∈ normalizer (T : Set L) := by
  have hα' : ∀ t ∈ T, α⁻¹ t ∈ T := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := exists_apply_eq_of_maps_to α hα ht
    rw [MulAut.inv_apply_self]
    exact ht'
  rw [mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h1 := (mem_normalizer_iff.mp hn (α⁻¹ t)).mp (hα' t ht)
    have h2 := hα _ h1
    rwa [map_mul, map_mul, map_inv, MulAut.apply_inv_self] at h2
  · intro ht
    have h1 := hα' _ ht
    rw [map_mul, map_mul, map_inv, MulAut.inv_apply_self] at h1
    have h2 := (mem_normalizer_iff.mp hn (α⁻¹ t)).mpr h1
    have h3 := hα _ h2
    rwa [MulAut.apply_inv_self] at h3

end Normalizer

section Kinds

variable {L : Type} [Group L] [Finite L] {H : Type*} [Group H]

theorem four_fix {W : Subgroup L} (hW4 : Nat.card W = 4) (ρ : H →* MulAut L)
    (hρ : ∀ h, ∀ w ∈ W, ρ h w ∈ W) :
    ∃ m : ℕ, ∀ h ∈ derivedSeries H m, ∀ w ∈ W, ρ h w = w := by
  have : Group.IsSolvable (MulAut W) := isSolvable_mulAut_of_card_le_four hW4.le
  obtain ⟨m, hm⟩ := Group.IsSolvable.solvable (G := MulAut W)
  refine ⟨m, fun h hh w hw => apply_eq_of_mem_ker (hW := hρ) ?_ hw⟩
  have h1 := map_derivedSeries_le_derivedSeries (restrictAut ρ W hρ) m ⟨h, hh, rfl⟩
  rw [hm, mem_bot] at h1
  exact h1

theorem eight_fix (T : Sylow 2 L) (hT8 : Nat.card (T : Subgroup L) = 8)
    (hTc : IsMulCommutative (T : Subgroup L))
    (htrans : ∀ x ∈ (T : Subgroup L), ∀ y ∈ (T : Subgroup L), x ≠ 1 → y ≠ 1 →
      ∃ n ∈ normalizer ((T : Subgroup L) : Set L), n⁻¹ * x * n = y)
    (ρ : H →* MulAut L) (hρ : ∀ h, ∀ w ∈ (T : Subgroup L), ρ h w ∈ (T : Subgroup L)) :
    ∀ h ∈ derivedSeries H 2, ∀ w ∈ (T : Subgroup L), ρ h w = w := by
  set N := normalizer ((T : Subgroup L) : Set L) with hN
  have hNW : N ≤ normalizer ((T : Subgroup L) : Set L) := le_rfl
  set κ := conjAutOn (T : Subgroup L) N hNW with hκ
  have hodd : Odd (Nat.card κ.range) := by
    rw [← Subgroup.index_ker]
    have hTk : (T : Subgroup L).subgroupOf N ≤ κ.ker := by
      intro t ht
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [conjAutOn_apply]
      have := hTc.is_comm.comm ⟨t, mem_subgroupOf.mp ht⟩ w
      have h1 : (t : L) * w = w * t := congrArg Subtype.val this
      rw [h1, mul_inv_cancel_right]
      rfl
    have h1 : κ.ker.index ∣ ((T : Subgroup L).subgroupOf N).index := index_dvd_of_le hTk
    have h2 : (T : Subgroup L).relIndex N ∣ (T : Subgroup L).index :=
      relIndex_dvd_index_of_le le_normalizer
    have h3 : ¬ 2 ∣ (T : Subgroup L).index := T.not_dvd_index
    have h4 : ¬ 2 ∣ κ.ker.index := fun h => h3 ((h.trans h1).trans h2)
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h4)
  have htr : ∀ x y : (T : Subgroup L), x ≠ 1 → y ≠ 1 → ∃ g ∈ κ.range, g x = y := by
    intro x y hx hy
    obtain ⟨n, hn, hxy⟩ := htrans x x.2 y y.2 (fun h => hx (Subtype.ext h))
      (fun h => hy (Subtype.ext h))
    refine ⟨κ ⟨n, hn⟩⁻¹, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [conjAutOn_apply]
    change n⁻¹ * x * n⁻¹⁻¹ = y
    rw [inv_inv, hxy]
  obtain ⟨P, hPc, -, hPtr, hPn⟩ := exists_cyclic_transitive_of_card_eight hT8 hodd htr
  have hρN : ∀ h, ∀ s ∈ N, ρ h s ∈ N := fun h s hs => apply_mem_normalizer (ρ h) (hρ h) hs
  have hnorm : ∀ h, restrictAut ρ (T : Subgroup L) hρ h ∈ normalizer (P : Set (MulAut _)) :=
    fun h => hPn _ (restrictAut_mem_normalizer_range ρ hρ hNW hρN h)
  intro h hh w hw
  exact apply_eq_of_mem_ker (derivedSeries_two_le_ker hPc hPtr _ hnorm hh) hw

theorem smul_sylow_eq_of_bender (hX : fusionIsBenderGroup L)
    (T : Sylow 2 L) (α : MulAut L)
    (hα : ∀ w ∈ Omega1 (T : Subgroup L), α w ∈ Omega1 (T : Subgroup L)) : α • T = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hq4, hB⟩ := (benderData_of_isBenderGroup hX).borel
  obtain ⟨hSE, -, hZcard, -⟩ := benderBorel_sylowCenter hB T
  have hΩ := GoldType.omega1_eq_sylowCenter_of_bender hX T
  set W := Omega1 (T : Subgroup L) with hW
  set N := normalizer ((T : Subgroup L) : Set L) with hN
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L T (α • T)
  by_contra hne
  have hgN : g ∉ N := by
    intro hgN
    apply hne
    rw [← hg]
    exact Sylow.smul_eq_iff_mem_normalizer.mpr hgN
  have hgN' : g⁻¹ ∉ N := fun h => hgN (by simpa using N.inv_mem h)
  have hodd := hSE.2.2 g⁻¹ hgN'
  rw [inv_inv] at hodd
  have hWle : W ≤ N ⊓ N.map (MulAut.conj g).toMonoidHom := by
    intro w hw
    have hwT : w ∈ (T : Subgroup L) := GoldType.omega1_le _ hw
    refine ⟨le_normalizer hwT, ?_⟩
    obtain ⟨w', hw', rfl⟩ := exists_apply_eq_of_maps_to α hα hw
    have h1 : α w' ∈ ((α • T : Sylow 2 L) : Subgroup L) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul w' α _ (GoldType.omega1_le _ hw')
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    refine ⟨(MulAut.conj g)⁻¹ • α w', le_normalizer h1, ?_⟩
    change MulAut.conj g ((MulAut.conj g)⁻¹ • α w') = α w'
    exact MulAut.apply_inv_self L _ _
  have hWeven : 2 ∣ Nat.card W := by
    rw [hΩ, hZcard]
    have hpow : IsPGroup 2 (sylowCenter (T : Subgroup L)) :=
      T.isPGroup'.to_le (fun z hz => hz.1)
    obtain ⟨j, hj⟩ := hpow.exists_card_eq
    rw [← hZcard, hj]
    rcases j with _ | j
    · rw [← hZcard, hj] at hq4
      norm_num at hq4
    · exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  have h2 : 2 ∣ Nat.card ↥(N ⊓ N.map (MulAut.conj g).toMonoidHom) :=
    hWeven.trans (Subgroup.card_dvd_of_le hWle)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem bender_fix (hX : fusionIsBenderGroup L) (T : Sylow 2 L)
    (ρ : H →* MulAut L)
    (hρ : ∀ h, ∀ w ∈ Omega1 (T : Subgroup L), ρ h w ∈ Omega1 (T : Subgroup L)) :
    ∀ h ∈ derivedSeries H 2, ∀ w ∈ Omega1 (T : Subgroup L), ρ h w = w := by
  obtain ⟨q, k, hq4, hB⟩ := (benderData_of_isBenderGroup hX).borel
  obtain ⟨-, ⟨D, hDc, -, -, hTD⟩, -, -, -⟩ := hB T
  obtain ⟨hSE, hZ2, -, -⟩ := benderBorel_sylowCenter hB T
  have hΩ := GoldType.omega1_eq_sylowCenter_of_bender hX T
  set W := Omega1 (T : Subgroup L) with hW
  set N := normalizer ((T : Subgroup L) : Set L) with hN
  have hNW : N ≤ normalizer (W : Set L) := GoldType.normalizer_le_normalizer_omega1 _
  set κ := conjAutOn W N hNW with hκ
  have hDN : D ≤ N := hTD ▸ le_sup_right
  have hTk : ∀ t ∈ (T : Subgroup L), ∀ ht : t ∈ N, κ ⟨t, ht⟩ = 1 := by
    intro t ht htN
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [conjAutOn_apply]
    have hw : (w : L) ∈ sylowCenter (T : Subgroup L) := hΩ ▸ w.2
    rw [((mem_sylowCenter.mp hw).2 t ht), mul_inv_cancel_right]
    rfl
  have hrange : κ.range = (κ.comp (inclusion hDN)).range := by
    refine le_antisymm ?_ (fun c ⟨d, hd⟩ => ⟨inclusion hDN d, hd⟩)
    rintro _ ⟨n, rfl⟩
    have hn : (n : L) ∈ ((D ⊔ (T : Subgroup L) : Subgroup L) : Set L) := by
      rw [sup_comm, hTD]
      exact n.2
    rw [coe_mul_of_left_le_normalizer_right D (T : Subgroup L) hDN, Set.mem_mul] at hn
    obtain ⟨d, hd, t, ht, hdt⟩ := hn
    refine ⟨⟨d, hd⟩, ?_⟩
    have htN : t ∈ N := le_normalizer ht
    have hn' : n = inclusion hDN ⟨d, hd⟩ * ⟨t, htN⟩ := Subtype.ext hdt.symm
    rw [MonoidHom.comp_apply, hn', map_mul, hTk t ht htN, mul_one]
  have hCc : IsCyclic κ.range := by
    rw [hrange]
    exact isCyclic_of_surjective (κ.comp (inclusion hDN)).rangeRestrict
      (κ.comp (inclusion hDN)).rangeRestrict_surjective
  have htr : ∀ x y : W, x ≠ 1 → y ≠ 1 → ∃ c ∈ κ.range, c x = y := by
    intro x y hx hy
    have hx' : (x : L) ∈ sylowCenter (T : Subgroup L) := hΩ ▸ x.2
    have hy' : (y : L) ∈ sylowCenter (T : Subgroup L) := hΩ ▸ y.2
    obtain ⟨n, hn, hxy⟩ := normalizer_transitive_center hSE hZ2 hx' hy'
      (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
    refine ⟨κ ⟨n, hn⟩⁻¹, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [conjAutOn_apply]
    change n⁻¹ * x * n⁻¹⁻¹ = y
    rw [inv_inv, hxy]
  have hρN : ∀ h, ∀ s ∈ N, ρ h s ∈ N := by
    intro h s hs
    have hT : ρ h • T = T := smul_sylow_eq_of_bender hX T (ρ h) (hρ h)
    have hρT : ∀ t ∈ (T : Subgroup L), ρ h t ∈ (T : Subgroup L) := by
      intro t ht
      have h1 : ρ h t ∈ ((ρ h • T : Sylow 2 L) : Subgroup L) := by
        rw [Sylow.pointwise_smul_def]
        exact Subgroup.smul_mem_pointwise_smul t (ρ h) _ ht
      rwa [hT] at h1
    exact apply_mem_normalizer (ρ h) hρT hs
  have hnorm : ∀ h, restrictAut ρ W hρ h ∈ normalizer (κ.range : Set (MulAut W)) :=
    fun h => restrictAut_mem_normalizer_range ρ hρ hNW hρN h
  intro h hh w hw
  exact apply_eq_of_mem_ker (derivedSeries_two_le_ker hCc htr _ hnorm hh) hw

end Kinds

theorem exists_derivedSeries_fix
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (hL : goldschmidtSimpleType L)
    (T : Sylow 2 L) {H : Type*} [Group H] (ρ : H →* MulAut L)
    (hρ : ∀ h, ∀ w ∈ Omega1 (T : Subgroup L), ρ h w ∈ Omega1 (T : Subgroup L)) :
    ∃ m : ℕ, ∀ h ∈ derivedSeries H m, ∀ w ∈ Omega1 (T : Subgroup L), ρ h w = w := by
  rcases hL with ⟨f, hf, he⟩ | ⟨n, hn, he⟩ | ⟨f, hf, he⟩ | hrest
  · exact ⟨2, bender_fix (Or.inl ⟨f, by omega, he⟩) T ρ hρ⟩
  · exact ⟨2, bender_fix (Or.inr (Or.inr ⟨n, hn, he⟩)) T ρ hρ⟩
  · exact ⟨2, bender_fix (Or.inr (Or.inl ⟨f, hf, he⟩)) T ρ hρ⟩
  · obtain ⟨-, hsq, -, htrans⟩ := GoldType.elementary_of_clauses hrest T
    have hΩ : Omega1 (T : Subgroup L) = T := GoldType.omega1_eq_self hsq
    rw [hΩ] at hρ ⊢
    rcases hrest with ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ | hRJ
    · obtain ⟨hT4, -, -⟩ := GoldType.sylow_of_psl2_odd hpo hf h8 e T
      exact four_fix hT4 ρ hρ
    · obtain ⟨-, hT8, hTc, -⟩ := GoldType.sylow_of_ree_or_j1 hRJ T
      exact ⟨2, eight_fix T hT8 hTc htrans ρ hρ⟩

end CFSG.ComponentClassification.AS81.Qbar
