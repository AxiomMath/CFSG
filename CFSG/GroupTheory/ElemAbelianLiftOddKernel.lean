module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {H : Type*} [Group H] [Finite H]

private theorem exists_isPGroup_two_map_mk_eq_of_odd_card {N : Subgroup H} [N.Normal]
    (hNodd : Odd (Nat.card N)) {T : Subgroup (H ⧸ N)} (hT : IsPGroup 2 T) :
    ∃ S' : Subgroup H, IsPGroup 2 S' ∧ S' ⊓ N = ⊥ ∧
      S'.map (QuotientGroup.mk' N) = T := by
  classical
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let P : Subgroup H := T.comap π
  let φ : P →* T :=
    { toFun := fun p => ⟨π (p : H), Subgroup.mem_comap.mp p.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφsurj : Function.Surjective φ := by
    intro t
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective N t
    refine ⟨⟨h, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hh]
      exact t.2
    · ext
      exact hh
  let S : Sylow 2 P := Sylow.nonempty.some
  have hTtop : IsPGroup 2 (⊤ : Subgroup T) :=
    hT.of_equiv (Subgroup.topEquiv (G := T)).symm
  have hQtop : (S.mapSurjective (f := φ) hφsurj : Subgroup T) = ⊤ :=
    ((S.mapSurjective (f := φ) hφsurj).is_maximal' (Q := ⊤) hTtop le_top).symm
  have hSmap : S.map φ = ⊤ := by
    rw [← Sylow.coe_mapSurjective (P := S) (f := φ) hφsurj]
    exact hQtop
  let S' : Subgroup H := S.map P.subtype
  have hS'P : S' ≤ P := Subgroup.map_subtype_le S.1
  have hS'2 : IsPGroup 2 S' := S.2.map P.subtype
  have hS'disj : Disjoint S' N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS'2
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hNodd)
  have hT_le : T ≤ S'.map π := by
    intro t ht
    have htS : (⟨t, ht⟩ : T) ∈ S.map φ := by
      rw [hSmap]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hst⟩ := htS
    exact ⟨(s : H), ⟨s, hs, rfl⟩, congrArg Subtype.val hst⟩
  have hle_T : S'.map π ≤ T := by
    rintro _ ⟨h, hh, rfl⟩
    exact Subgroup.mem_comap.mp (hS'P hh)
  exact ⟨S', hS'2, hS'disj.eq_bot, le_antisymm hle_T hT_le⟩

private theorem isElemAbelian_of_map_mk_eq_of_disjoint {N : Subgroup H} [N.Normal]
    {S' : Subgroup H} (hdisj : S' ⊓ N = ⊥) {T : Subgroup (H ⧸ N)}
    (hT : IsElemAbelian 2 T) (hmap : S'.map (QuotientGroup.mk' N) = T) :
    IsElemAbelian 2 S' := by
  classical
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  have hinj : ∀ {a b : H}, a ∈ S' → b ∈ S' → π a = π b → a = b := by
    intro a b ha hb hab
    have hmem : a⁻¹ * b ∈ S' := S'.mul_mem (S'.inv_mem ha) hb
    have hker : a⁻¹ * b ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change π (a⁻¹ * b) = 1
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hbot : a⁻¹ * b ∈ S' ⊓ N := ⟨hmem, hker⟩
    rw [hdisj] at hbot
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · have haT : π (a : H) ∈ T := hmap ▸ Subgroup.mem_map_of_mem π a.2
    have hbT : π (b : H) ∈ T := hmap ▸ Subgroup.mem_map_of_mem π b.2
    have hcomm : π (a : H) * π (b : H) = π (b : H) * π (a : H) :=
      congrArg Subtype.val (hT.1.is_comm.comm ⟨π (a : H), haT⟩ ⟨π (b : H), hbT⟩)
    apply Subtype.ext
    exact hinj (S'.mul_mem a.2 b.2) (S'.mul_mem b.2 a.2)
      (by simpa only [Subgroup.coe_mul, map_mul] using hcomm)
  · have haT : π a ∈ T := hmap ▸ Subgroup.mem_map_of_mem π ha
    have hsq : π (a ^ 2) = 1 := by
      rw [map_pow]
      exact hT.2 (π a) haT
    have ha2S : a ^ 2 ∈ S' := S'.pow_mem ha 2
    have ha2N : a ^ 2 ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (a ^ 2) = 1
      exact hsq
    have hbot : a ^ 2 ∈ S' ⊓ N := ⟨ha2S, ha2N⟩
    rw [hdisj] at hbot
    exact Subgroup.mem_bot.mp hbot

theorem exists_isElemAbelian_two_map_mk_eq_of_odd_card {N : Subgroup H} [N.Normal]
    (hNodd : Odd (Nat.card N)) {T : Subgroup (H ⧸ N)} (hT : IsElemAbelian 2 T) :
    ∃ T' : Subgroup H, IsElemAbelian 2 T' ∧ T'.map (QuotientGroup.mk' N) = T := by
  obtain ⟨S', -, hdisj, hmap⟩ :=
    exists_isPGroup_two_map_mk_eq_of_odd_card hNodd hT.isPGroup
  exact ⟨S', isElemAbelian_of_map_mk_eq_of_disjoint hdisj hT hmap, hmap⟩

end CFSG.GroupTheory

end
