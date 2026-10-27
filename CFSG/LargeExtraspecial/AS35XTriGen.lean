module

public import CFSG.LargeExtraspecial.AS35XGen

public section

namespace CFSG.LargeExtraspecial.AS35X

open Subgroup

section Image

variable {L : Type*} [Group L]

theorem fischerQ_image_mk (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {D : Set L}
    (hinv : ∀ e ∈ D, e * e = 1) :
    fischerQ (QuotientGroup.mk' (center L) '' D) =
      (fischerQ D).map (QuotientGroup.mk' (center L)) := by
  rw [fischerQ, fischerQ, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, _, ⟨e, he, rfl⟩, hne, hc, rfl⟩
    refine ⟨d * e, ⟨d, hd, e, he, fun h => hne (h ▸ rfl), ?_, rfl⟩, map_mul _ _ _⟩
    exact commute_of_mk hZ (hinv e he) hc
  · rintro ⟨_, ⟨d, hd, e, he, hne, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨d, hd, rfl⟩, _, ⟨e, he, rfl⟩,
      fun h => hne (eq_of_mk_eq hZ (hinv d hd) (hinv e he) h), ?_, (map_mul _ _ _).symm⟩
    rw [← map_mul, ← map_mul, hc]

theorem map_mk_fischerQ_inf_centralizer (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) {D : Set L}
    (hinv : ∀ e ∈ D, e * e = 1) {t : L} (ht : t * t = 1) :
    (fischerQ D ⊓ centralizer {t}).map (QuotientGroup.mk' (center L)) =
      fischerQ (QuotientGroup.mk' (center L) '' D) ⊓
        centralizer {QuotientGroup.mk' (center L) t} := by
  rw [fischerQ_image_mk hZ hinv]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxt⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨⟨x, hxQ, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hxt]
  · intro hy
    obtain ⟨⟨x, hxQ, rfl⟩, hyt⟩ := mem_inf.mp hy
    refine ⟨x, mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    exact commute_of_mk hZ ht (mem_centralizer_singleton_iff.mp hyt)

end Image

theorem false_of_triality {O : Type*} [Group O] [Finite O] {Mb L P : Subgroup O} {D : Set O}
    {t : O} (hDL : D ⊆ L) (hLM : L ≤ Mb) (hPM : P ≤ Mb) (ht : t ∈ D)
    (hconjD : ∀ m ∈ Mb, ∀ d ∈ D, m * d * m⁻¹ ∈ D) (hinv : ∀ d ∈ D, d * d = 1)
    (hZ : ∀ c ∈ center L, c * c = 1 → c = 1) (hP2 : IsPGroup 2 P)
    (hPt : ∀ p ∈ P, p * t = t * p)
    (hPn : ∀ c ∈ Mb, c * t = t * c → ∀ x ∈ P, c * x * c⁻¹ ∈ P)
    (h58 : ∀ X : Subgroup O, X ≤ Mb → (∀ x ∈ X, x * t = t * x) →
      (∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) → Odd (Nat.card X) → Nat.card X ≤ 3)
    (hns : ¬ Group.IsSolvable (fischerQ (QuotientGroup.mk' (center L) '' (Subtype.val ⁻¹' D)) ⊓
      centralizer {QuotientGroup.mk' (center L) ⟨t, hDL ht⟩} : Subgroup (L ⧸ center L)))
    (hno2 : S12NoNormalTwo (fischerQ (QuotientGroup.mk' (center L) '' (Subtype.val ⁻¹' D)) ⊓
      centralizer {QuotientGroup.mk' (center L) ⟨t, hDL ht⟩})) : False := by
  classical
  set π := QuotientGroup.mk' (center L) with hπ
  set t' : L := ⟨t, hDL ht⟩ with ht'
  have hinv' : ∀ e ∈ (Subtype.val ⁻¹' D : Set L), e * e = 1 :=
    fun e he => Subtype.ext (hinv _ he)
  set C₁ : Subgroup L := fischerQ (Subtype.val ⁻¹' D) ⊓ centralizer {t'} with hC₁
  set C₀ : Subgroup O := fischerQ D ⊓ centralizer {t} with hC₀
  have hmapC : C₁.map π = fischerQ (π '' (Subtype.val ⁻¹' D)) ⊓ centralizer {π t'} :=
    map_mk_fischerQ_inf_centralizer hZ hinv' (Subtype.ext (hinv t ht))
  have hC10 : C₁.map L.subtype = C₀ := map_subtype_fischerQ_inf_centralizer hDL t'
  have hmem : ∀ c : L, c ∈ C₁ ↔ (c : O) ∈ C₀ := fun c => by
    rw [← hC10]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hC0L : ∀ {c : O}, c ∈ C₀ → c ∈ L := fun hc =>
    (closure_le L).mpr hDL (fischerQ_le_closure hc.1)
  have hC0t : ∀ {c : O}, c ∈ C₀ → c * t = t * c := fun hc =>
    mem_centralizer_singleton_iff.mp hc.2
  have hPC : ∀ p ∈ P, ∀ c ∈ C₀, p * c * p⁻¹ ∈ C₀ := by
    intro p hp c hc
    refine mem_inf.mpr ⟨conj_mem_fischerQ (fun e he => hconjD p (hPM hp) e he) hc.1,
      mem_centralizer_singleton_iff.mpr ?_⟩
    have hpt := hPt p hp
    have hct := hC0t hc
    have hpt' : p⁻¹ * t = t * p⁻¹ := by
      calc p⁻¹ * t = p⁻¹ * (t * p) * p⁻¹ := by group
        _ = p⁻¹ * (p * t) * p⁻¹ := by rw [hpt]
        _ = t * p⁻¹ := by group
    calc p * c * p⁻¹ * t = p * c * (p⁻¹ * t) := by group
      _ = p * c * (t * p⁻¹) := by rw [hpt']
      _ = p * (c * t) * p⁻¹ := by group
      _ = p * (t * c) * p⁻¹ := by rw [hct]
      _ = p * t * c * p⁻¹ := by group
      _ = t * p * c * p⁻¹ := by rw [hpt]
      _ = t * (p * c * p⁻¹) := by group
  have hCP : ∀ c ∈ C₀, ∀ x ∈ P, c * x * c⁻¹ ∈ P := fun c hc =>
    hPn c (hLM (hC0L hc)) (hC0t hc)
  have hK : ∀ k ∈ P, k ∈ C₀ → k = 1 := by
    set K₁ : Subgroup L := (P ⊓ C₀).comap L.subtype with hK₁
    have hK₁2 : IsPGroup 2 K₁ := (hP2.to_le inf_le_left).comap_subtype
    have hK₁C : K₁ ≤ C₁ := fun k hk => (hmem k).mpr hk.2
    have hbot : K₁.map π = ⊥ := by
      refine hno2 _ (hmapC ▸ map_mono hK₁C) (hK₁2.map π) ?_
      intro y hy
      rw [← hmapC] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      have hc0 := (hmem c).mp hc
      refine mem_normalizer_of_conj_mem fun k hk => ?_
      obtain ⟨k₀, hk₀, rfl⟩ := hk
      refine ⟨c * k₀ * c⁻¹, ⟨?_, ?_⟩, by rw [map_mul, map_mul, map_inv]⟩
      · exact hCP c hc0 k₀ hk₀.1
      · exact C₀.mul_mem (C₀.mul_mem hc0 hk₀.2) (C₀.inv_mem hc0)
    intro k hkP hkC
    have hkK : (⟨k, hC0L hkC⟩ : L) ∈ K₁ := ⟨hkP, hkC⟩
    have h1 : π ⟨k, hC0L hkC⟩ = 1 := by
      have : π ⟨k, hC0L hkC⟩ ∈ K₁.map π := ⟨_, hkK, rfl⟩
      rwa [hbot, mem_bot] at this
    obtain ⟨n, hn⟩ := hK₁2 ⟨_, hkK⟩
    have h2 : (⟨k, hC0L hkC⟩ : L) = 1 :=
      eq_one_of_mem_center_of_pow hZ (mk'_eq_one_iff.mp h1) n (congrArg Subtype.val hn)
    exact congrArg Subtype.val h2
  have hcomm : ∀ p ∈ P, ∀ c ∈ C₀, p * c = c * p := by
    intro p hp c hc
    have hw : p * c * p⁻¹ * c⁻¹ = 1 := by
      refine hK _ ?_ (C₀.mul_mem (hPC p hp c hc) (C₀.inv_mem hc))
      rw [show p * c * p⁻¹ * c⁻¹ = p * (c * p⁻¹ * c⁻¹) by group]
      exact P.mul_mem hp (hCP c hc _ (P.inv_mem hp))
    calc p * c = p * c * p⁻¹ * c⁻¹ * (c * p) := by group
      _ = c * p := by rw [hw, one_mul]
  have hsol0 : Group.IsSolvable C₀ := by
    by_contra hns0
    obtain ⟨r, hr, h5, hdvd⟩ := exists_prime_five_le_of_not_isSolvable hns0
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hxC := x.2
    have hcard : Nat.card (zpowers (x : O)) = r := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    have hodd : Odd (Nat.card (zpowers (x : O))) := by
      rw [hcard]
      rcases hr.eq_two_or_odd' with h | h
      · omega
      · exact h
    have h3 := h58 (zpowers (x : O)) (zpowers_le.mpr (hLM (hC0L hxC)))
      (fun y hy => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left (hC0t hxC) k) : _))
      (fun p hp y hy => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        have hpx : Commute p (x : O) := hcomm p hp _ hxC
        rw [(hpx.zpow_right k).eq, mul_inv_cancel_right]
        exact mem_zpowers_iff.mpr ⟨k, rfl⟩) hodd
    omega
  apply hns
  let e : C₁ ≃* C₀ := (C₁.equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr hC10)
  have hsol1 : Group.IsSolvable C₁ :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hsol2 : Group.IsSolvable (C₁.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective C₁)
  rw [hmapC] at hsol2
  exact hsol2

end CFSG.LargeExtraspecial.AS35X
