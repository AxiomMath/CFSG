module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Cover

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]

@[expose] def twoLift (N : Subgroup H) [N.Normal] (W : Subgroup (H ⧸ N)) : Subgroup H :=
  ⨆ (S : Subgroup H) (_ : IsPGroup 2 S) (_ : S.map (QuotientGroup.mk' N) ≤ W), S

omit [Finite H] in
theorem le_twoLift {W : Subgroup (H ⧸ N)} {S : Subgroup H} (hS : IsPGroup 2 S)
    (hSW : S.map (QuotientGroup.mk' N) ≤ W) : S ≤ twoLift N W :=
  le_iSup₂_of_le S hS (le_iSup_of_le hSW le_rfl)

variable (hNc : N ≤ center H) (hNo : Odd (Nat.card N))
include hNc hNo

theorem le_of_isSylowOf_comap {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) {S : Subgroup H}
    (hS : ABGLocalTools.IsSylowOf 2 S (W.comap (QuotientGroup.mk' N))) {S' : Subgroup H}
    (hS' : IsPGroup 2 S') (hS'W : S'.map (QuotientGroup.mk' N) ≤ W) : S' ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hmap : S.map π = W := by
    have h1 := AschbacherTheorem3.IsSylowOf.map hS π
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h1
    exact (h1.eq_of_le h1.le le_rfl hW).symm
  intro s' hs'
  obtain ⟨s, hs, hss'⟩ : π s' ∈ S.map π := hmap ▸ hS'W ⟨s', hs', rfl⟩
  set n := s⁻¹ * s' with hn
  have hnN : n ∈ N := by
    rw [hn, ← QuotientGroup.eq]
    exact hss'
  have hnc : ∀ h : H, h * n = n * h := fun h => (mem_center_iff.mp (hNc hnN) h)
  obtain ⟨a, ha⟩ := hS.isPGroup ⟨s, hs⟩
  obtain ⟨b, hb⟩ := hS' ⟨s', hs'⟩
  have ha' : s ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : s' ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hs'eq : s' = s * n := by rw [hn, mul_inv_cancel_left]
  have hpow : n ^ 2 ^ (a + b) = 1 := by
    have h1 : s' ^ 2 ^ (a + b) = s ^ 2 ^ (a + b) * n ^ 2 ^ (a + b) := by
      rw [hs'eq]
      exact Commute.mul_pow (hnc s) _
    have h2 : s' ^ 2 ^ (a + b) = 1 := by
      rw [pow_add, mul_comm, pow_mul, hb', one_pow]
    have h3 : s ^ 2 ^ (a + b) = 1 := by
      rw [pow_add, pow_mul, ha', one_pow]
    rw [h2, h3, one_mul] at h1
    exact h1.symm
  have hodd : Odd (orderOf n) := by
    have hd : orderOf (⟨n, hnN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact hNo.of_dvd_nat hd
  have h1 : orderOf n ∣ 2 ^ (a + b) := orderOf_dvd_of_pow_eq_one hpow
  have hn1 : orderOf n = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp h1 with ⟨k, -, hk⟩
    rcases k with _ | k
    · simpa using hk
    · rw [hk, pow_succ] at hodd
      exact absurd (Nat.even_iff.mpr (by omega)) (Nat.not_even_iff_odd.mpr hodd)
  rw [hs'eq, orderOf_eq_one_iff.mp hn1, mul_one]
  exact hs

theorem twoLift_eq {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) {S : Subgroup H}
    (hS : ABGLocalTools.IsSylowOf 2 S (W.comap (QuotientGroup.mk' N))) : twoLift N W = S := by
  refine le_antisymm (iSup₂_le fun S' hS' => iSup_le fun hS'W =>
    le_of_isSylowOf_comap hNc hNo hW hS hS' hS'W) (le_twoLift hS.isPGroup ?_)
  exact map_le_iff_le_comap.mpr hS.le

theorem isSylowOf_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    ABGLocalTools.IsSylowOf 2 (twoLift N W) (W.comap (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := ABGLocalTools.exists_isSylowOf 2 (W.comap (QuotientGroup.mk' N))
  rw [twoLift_eq hNc hNo hW hS]
  exact hS

theorem isPGroup_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    IsPGroup 2 (twoLift N W) :=
  (isSylowOf_twoLift hNc hNo hW).isPGroup

theorem map_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    (twoLift N W).map (QuotientGroup.mk' N) = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := AschbacherTheorem3.IsSylowOf.map (isSylowOf_twoLift hNc hNo hW)
    (QuotientGroup.mk' N)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h1
  exact (h1.eq_of_le h1.le le_rfl hW).symm

theorem mk_mem_of_mem_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) {a : H}
    (ha : a ∈ twoLift N W) : QuotientGroup.mk' N a ∈ W :=
  (map_twoLift hNc hNo hW).le ⟨a, ha, rfl⟩

theorem twoLift_map {S : Subgroup H} (hS : IsPGroup 2 S) :
    twoLift N (S.map (QuotientGroup.mk' N)) = S := by
  have hW : IsPGroup 2 (S.map (QuotientGroup.mk' N)) := hS.map _
  refine AS81.eq_of_map_eq (isPGroup_twoLift hNc hNo hW) hNo le_rfl ?_ ?_
  · exact le_twoLift hS le_rfl
  · rw [map_twoLift hNc hNo hW]

theorem twoLift_mono {W₁ W₂ : Subgroup (H ⧸ N)} (hW₁ : IsPGroup 2 W₁) (h : W₁ ≤ W₂) :
    twoLift N W₁ ≤ twoLift N W₂ :=
  le_twoLift (isPGroup_twoLift hNc hNo hW₁) ((map_twoLift hNc hNo hW₁).le.trans h)

theorem injOn_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) {a b : H}
    (ha : a ∈ twoLift N W) (hb : b ∈ twoLift N W)
    (h : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b :=
  AS81.mk'_injOn (isPGroup_twoLift hNc hNo hW) hNo ha hb h

@[expose] noncomputable def twoLiftEquiv {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    ↥(twoLift N W) ≃* ↥W :=
  (MulEquiv.ofBijective (((QuotientGroup.mk' N).comp (twoLift N W).subtype).rangeRestrict)
    ⟨fun a b h => Subtype.ext (injOn_twoLift hNc hNo hW a.2 b.2
        (congrArg Subtype.val h)),
      MonoidHom.rangeRestrict_surjective _⟩).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_eq_map, ← map_map, ← MonoidHom.range_eq_map, range_subtype,
        map_twoLift hNc hNo hW]))

theorem card_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    Nat.card (twoLift N W) = Nat.card W :=
  Nat.card_congr (twoLiftEquiv hNc hNo hW).toEquiv

theorem mem_normalizer_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) {h : H}
    (hh : QuotientGroup.mk' N h ∈ normalizer (W : Set (H ⧸ N))) :
    h ∈ normalizer (twoLift N W : Set H) := by
  have key : ∀ k : H, QuotientGroup.mk' N k ∈ normalizer (W : Set (H ⧸ N)) →
      ∀ a ∈ twoLift N W, k * a * k⁻¹ ∈ twoLift N W := by
    intro k hk a ha
    have hle : (twoLift N W).map (MulAut.conj k).toMonoidHom ≤ twoLift N W := by
      refine le_twoLift ((isPGroup_twoLift hNc hNo hW).map _) ?_
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have hbW : QuotientGroup.mk' N b ∈ W := (map_twoLift hNc hNo hW) ▸ ⟨b, hb, rfl⟩
      have h1 := (mem_normalizer_iff.mp hk _).mp hbW
      simpa [MulAut.conj_apply] using h1
    exact hle ⟨a, ha, rfl⟩
  rw [mem_normalizer_iff]
  intro a
  refine ⟨key h hh a, fun ha => ?_⟩
  have := key h⁻¹ (by rw [map_inv]; exact inv_mem hh) _ ha
  simpa [mul_assoc] using this

theorem twoLift_inf {W W₁ W₂ : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) (h₁ : W₁ ≤ W)
    (h₂ : W₂ ≤ W) : twoLift N (W₁ ⊓ W₂) = twoLift N W₁ ⊓ twoLift N W₂ := by
  have hW₁ := hW.to_le h₁
  have hW₂ := hW.to_le h₂
  refine le_antisymm (le_inf (twoLift_mono hNc hNo (hW₁.to_le inf_le_left) inf_le_left)
    (twoLift_mono hNc hNo (hW₂.to_le inf_le_right) inf_le_right)) (le_twoLift
      ((isPGroup_twoLift hNc hNo hW₁).to_le inf_le_left) ?_)
  exact (map_inf_le _ _ _).trans (inf_le_inf (map_twoLift hNc hNo hW₁).le
    (map_twoLift hNc hNo hW₂).le)

theorem twoLift_sup {W₁ W₂ : Subgroup (H ⧸ N)} (hW : IsPGroup 2 ↥(W₁ ⊔ W₂)) :
    twoLift N (W₁ ⊔ W₂) = twoLift N W₁ ⊔ twoLift N W₂ := by
  have h₁ := twoLift_mono hNc hNo (hW.to_le le_sup_left) (le_sup_left : W₁ ≤ W₁ ⊔ W₂)
  have h₂ := twoLift_mono hNc hNo (hW.to_le le_sup_right) (le_sup_right : W₂ ≤ W₁ ⊔ W₂)
  refine (AS81.eq_of_map_eq (isPGroup_twoLift hNc hNo hW) hNo le_rfl (sup_le h₁ h₂) ?_).symm.symm
  rw [Subgroup.map_sup, map_twoLift hNc hNo hW, map_twoLift hNc hNo (hW.to_le le_sup_left),
    map_twoLift hNc hNo (hW.to_le le_sup_right)]

theorem exists_mem_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) {w : H ⧸ N}
    (hw : w ∈ W) : ∃ a ∈ twoLift N W, QuotientGroup.mk' N a = w := by
  rw [← map_twoLift hNc hNo hW] at hw
  exact hw

theorem map_centerIn_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    (centerIn (twoLift N W)).map (QuotientGroup.mk' N) = centerIn W := by
  apply le_antisymm
  · rintro _ ⟨a, ⟨ha, hac⟩, rfl⟩
    refine ⟨mk_mem_of_mem_twoLift hNc hNo hW ha, mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨b, hb, rfl⟩ := exists_mem_twoLift hNc hNo hW hw
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hac b hb]
  · rintro w ⟨hw, hwc⟩
    obtain ⟨a, ha, rfl⟩ := exists_mem_twoLift hNc hNo hW hw
    refine ⟨a, ⟨ha, mem_centralizer_iff.mpr fun b hb => ?_⟩, rfl⟩
    apply injOn_twoLift hNc hNo hW (mul_mem hb ha) (mul_mem ha hb)
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hwc _ (mk_mem_of_mem_twoLift hNc hNo hW hb)

theorem centerIn_twoLift {W : Subgroup (H ⧸ N)} (hW : IsPGroup 2 W) :
    centerIn (twoLift N W) = twoLift N (centerIn W) := by
  have hZ : IsPGroup 2 (centerIn W) := hW.to_le inf_le_left
  have hle : centerIn (twoLift N W) ≤ twoLift N (centerIn W) :=
    le_twoLift ((isPGroup_twoLift hNc hNo hW).to_le inf_le_left)
      (map_centerIn_twoLift hNc hNo hW).le
  refine AS81.eq_of_map_eq (isPGroup_twoLift hNc hNo hW) hNo inf_le_left
    ((twoLift_mono hNc hNo hZ inf_le_left)) ?_
  rw [map_centerIn_twoLift hNc hNo hW, map_twoLift hNc hNo hZ]

theorem isElemAbelian_twoLift {W : Subgroup (H ⧸ N)} (hW : CFSG.Open.IsElemAbelian 2 W) :
    CFSG.Open.IsElemAbelian 2 (twoLift N W) := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa using hW.2 _ w.2)⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · apply injOn_twoLift hNc hNo hW2 (mul_mem a.2 b.2) (mul_mem b.2 a.2)
    have ha := mk_mem_of_mem_twoLift hNc hNo hW2 a.2
    have hb := mk_mem_of_mem_twoLift hNc hNo hW2 b.2
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hW.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  · apply injOn_twoLift hNc hNo hW2 (pow_mem ha 2) (one_mem _)
    have ha' := mk_mem_of_mem_twoLift hNc hNo hW2 ha
    rw [map_pow, map_one, hW.2 _ ha']

end CFSG.ComponentClassification.AS81
