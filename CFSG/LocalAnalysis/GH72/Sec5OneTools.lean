module

public import CFSG.LocalAnalysis.GH72.Sec5DBasic
public import CFSG.LocalAnalysis.GH72.DDAut
public import TauCeti.GroupTheory.OrderOfElement.PPart
public import CFSG.LocalAnalysis.GH72.Sec4CStruct

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

namespace G5one

section Elements

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_isSylowOf_of_le_normalizer {T N : Subgroup G} (hT : IsSylowOf 2 T N)
    (hNT : N ≤ normalizer (T : Set G)) {x : G} (hxN : x ∈ N) (hx : IsPGroup 2 (zpowers x)) :
    x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcN, hc⟩ := exists_mem_conj_mem_of_isSylowOf hT hxN hx
  have hc' := (mem_normalizer_iff.mp (hNT (N.inv_mem hcN)) (c * x * c⁻¹)).mp hc
  simpa [mul_assoc] using hc'

theorem isPGroup_zpowers_pPart (x : G) : IsPGroup 2 (zpowers (TauCeti.pPart 2 x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := (orderOf x).factorization 2) ?_
  rw [Nat.card_zpowers, TauCeti.orderOf_pPart Nat.prime_two (orderOf_pos x).ne']

theorem odd_orderOf_pFreePart (x : G) : Odd (orderOf (TauCeti.pFreePart 2 x)) := by
  have h := TauCeti.not_dvd_orderOf_pFreePart (x := x) Nat.prime_two (orderOf_pos x).ne'
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)

omit [Finite G] in
theorem mem_centralizer_of_odd_of_mem_normalizer {T : Subgroup G} {k : ℕ}
    (e : T ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) {x : G} (hx : x ∈ normalizer (T : Set G))
    (hodd : Odd (orderOf x)) : x ∈ centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := T.normalizerMonoidHom ⟨x, hx⟩ with hσ
  have h1 : orderOf σ ∣ orderOf x := by
    have h := orderOf_map_dvd T.normalizerMonoidHom ⟨x, hx⟩
    rwa [Subgroup.orderOf_mk] at h
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (dih_isPGroup_mulAut e hk)) σ
  have hm0 : m = 0 := by
    by_contra h
    have h2 : 2 ∣ orderOf σ := hm ▸ dvd_pow_self 2 h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans h1))
  rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
  rw [mem_centralizer_iff]
  intro t ht
  have h3 : σ ⟨t, ht⟩ = ⟨t, ht⟩ := by rw [hm]; rfl
  have h4 : x * t * x⁻¹ = t := congrArg Subtype.val h3
  calc t * x = x * t * x⁻¹ * x := by rw [h4]
    _ = x * t := by group

end Elements

section Bar

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}

theorem centralizer_bar_le {V : Subgroup G} (hVH : V ≤ H) (hV : IsPGroup 2 V) :
    centralizer (bar H V : Set (Bar H)) ≤ bar H (H ⊓ centralizer (V : Set G)) := by
  intro u hu
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) u
  have hn : ∀ v ∈ V, v * (h : G) * v⁻¹ * (h : G)⁻¹ ∈ O H := by
    intro v hv
    set v' : H := ⟨v, hVH hv⟩ with hv'def
    have hv' : QuotientGroup.mk' (CFSG.oddCore H) v' ∈ bar H V := ⟨v', hv, rfl⟩
    have hc := mem_centralizer_iff.mp hu _ hv'
    have hk : v' * h * v'⁻¹ * h⁻¹ ∈ CFSG.oddCore H := by
      rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker, map_mul, map_mul, map_mul,
        map_inv, map_inv, hc]
      group
    exact ⟨_, hk, rfl⟩
  obtain ⟨d, hd, hdV⟩ :=
    G5d.exists_fixed_mem_coset_of_isPGroup hV (G4c.odd_card_O H)
      (hVH.trans (G4c.le_normalizer_O H)) hn
  obtain ⟨d', hd', rfl⟩ := hd
  refine ⟨d' * h, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_subgroupOf, mem_inf]
    refine ⟨(d' * h).2, ?_⟩
    rw [mem_centralizer_iff]
    intro v hv
    have e : v * ((d' : G) * h) * v⁻¹ = (d' : G) * h := hdV v hv
    change v * ((d' : G) * h) = ((d' : G) * h) * v
    calc v * ((d' : G) * h) = v * ((d' : G) * h) * v⁻¹ * v := by group
      _ = (d' : G) * h * v := by rw [e]
  · rw [← QuotientGroup.ker_mk' (CFSG.oddCore H)] at hd'
    change QuotientGroup.mk' (CFSG.oddCore H) (d' * h) = QuotientGroup.mk' (CFSG.oddCore H) h
    rw [map_mul, MonoidHom.mem_ker.mp hd', one_mul]

omit [Finite G] in
theorem bar_map_cj (K : Subgroup G) {h : G} (hh : h ∈ H) :
    bar H (K.map (G4c.cj h)) =
      (bar H K).map (G4c.cj (QuotientGroup.mk' (CFSG.oddCore H) ⟨h, hh⟩)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := hx
    have hkx' : h * k * h⁻¹ = (x : G) := hkx
    have hkH : k ∈ H := by
      have : k = h⁻¹ * (x : G) * h := by
        rw [← hkx']
        group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) x.2) hh
    refine ⟨QuotientGroup.mk' _ ⟨k, hkH⟩, ⟨⟨k, hkH⟩, hk, rfl⟩, ?_⟩
    rw [G4c.cj_apply, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [← hkx']
    rfl
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    rw [G4c.cj_apply, map_mul, map_mul, map_inv]

omit [Finite G] in
theorem bar_le_iff {K : Subgroup G} (hKH : K ≤ H) {L : Subgroup (Bar H)} :
    bar H K ≤ L ↔ K ≤ (L.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype := by
  constructor
  · intro h k hk
    exact ⟨⟨k, hKH hk⟩, h ⟨⟨k, hKH hk⟩, hk, rfl⟩, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy

end Bar

section GenW

variable {G : Type*} [Group G] [Finite G] {H K₀ T V : Subgroup G}

abbrev genW (H K₀ T : Subgroup G) : Subgroup G :=
  ⨆ (k : G) (_ : k ∈ H ⊓ K₀), T.map (G4c.cj k)

omit [Finite G] in
theorem genW_le (hTK : T ≤ H ⊓ K₀) : genW H K₀ T ≤ H ⊓ K₀ := by
  refine iSup₂_le fun k hk => ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [G4c.cj_apply]
  exact mul_mem (mul_mem hk (hTK ht)) (inv_mem hk)

omit [Finite G] in
theorem le_genW : T ≤ genW H K₀ T := by
  have h := le_iSup₂_of_le (f := fun (k : G) (_ : k ∈ H ⊓ K₀) => T.map (G4c.cj k)) 1 (one_mem _)
    le_rfl
  intro t ht
  refine h ⟨t, ht, ?_⟩
  rw [G4c.cj_apply]
  group

theorem le_genW_of_isPGroup (hT : IsSylowOf 2 T (H ⊓ K₀)) {Q : Subgroup G} (hQ : Q ≤ H ⊓ K₀)
    (hQ2 : IsPGroup 2 Q) : Q ≤ genW H K₀ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hcQ⟩ := exists_mem_map_conj_le_of_isSylowOf hT hQ hQ2
  have h1 : Q ≤ T.map (G4c.cj c⁻¹) := G4c.map_cj_le_iff.mp hcQ
  exact h1.trans (le_iSup₂_of_le (f := fun (k : G) (_ : k ∈ H ⊓ K₀) => T.map (G4c.cj k)) c⁻¹
    (inv_mem hc) le_rfl)

omit [Finite G] in
theorem le_normalizer_genW : H ⊓ K₀ ≤ normalizer (genW H K₀ T : Set G) := by
  intro g hg
  refine G4c.mem_normalizer_of_map_cj_eq (le_antisymm ?_ ?_)
  · rw [Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hk => ?_
    rw [G4b.map_conj_map_conj]
    exact le_iSup₂_of_le (f := fun (k : G) (_ : k ∈ H ⊓ K₀) => T.map (G4c.cj k)) (g * k)
      (mul_mem hg hk) le_rfl
  · refine iSup₂_le fun k hk => ?_
    have h := le_iSup₂_of_le (f := fun (k : G) (_ : k ∈ H ⊓ K₀) => T.map (G4c.cj k)) (g⁻¹ * k)
      (mul_mem (inv_mem hg) hk) le_rfl
    have h2 := map_mono (f := G4c.cj g) h
    rw [G4b.map_conj_map_conj, mul_inv_cancel_left] at h2
    exact h2

variable (hTK : T ≤ H ⊓ K₀) (hT : IsSylowOf 2 T (H ⊓ K₀)) (hVH : V ≤ H) (hV : IsPGroup 2 V)
  (hK₀ : centralizer (V : Set G) ≤ normalizer (K₀ : Set G)) {L : Subgroup (Bar H)}
  (hLn : L.Normal) (hTL : IsSylowOf 2 (bar H T) L) (hLV : L ≤ centralizer (bar H V : Set (Bar H)))

include hTK hT hVH hV hK₀ hLn hTL hLV in
theorem map_bar_le_bar_genW (u : Bar H) :
    (bar H T).map (G4c.cj u) ≤ bar H (genW H K₀ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (bar H T).map (G4c.cj u) with hP
  have hPL : P ≤ L := by
    rintro _ ⟨t, ht, rfl⟩
    rw [G4c.cj_apply]
    exact hLn.conj_mem _ (hTL.le ht) u
  have hP2 : IsPGroup 2 P := (hTL.isPGroup).map _
  obtain ⟨c, hcL, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hTL hPL hP2
  have hceq : P.map (G4c.cj c) = bar H T :=
    eq_of_le_of_card_ge hc (by rw [G4c.card_map_cj, hP, G4c.card_map_cj])
  have hPeq : P = (bar H T).map (G4c.cj c⁻¹) := by
    rw [← hceq, G4c.map_cj_cj_inv]
  obtain ⟨ℓ, hℓ, hℓc⟩ := centralizer_bar_le hVH hV (hLV (L.inv_mem hcL))
  rw [SetLike.mem_coe, mem_subgroupOf] at hℓ
  have hTℓ : T.map (G4c.cj (ℓ : G)) ≤ genW H K₀ T := by
    refine le_genW_of_isPGroup hT ?_ ((hT.isPGroup).map _)
    rintro _ ⟨t, ht, rfl⟩
    rw [G4c.cj_apply]
    refine mem_inf.mpr ⟨mul_mem (mul_mem ℓ.2 (mem_inf.mp (hTK ht)).1) (inv_mem ℓ.2), ?_⟩
    exact (mem_normalizer_iff.mp (hK₀ (mem_inf.mp hℓ).2) t).mp (mem_inf.mp (hTK ht)).2
  have hbar := bar_map_cj (H := H) T ℓ.2
  have hℓ' : QuotientGroup.mk' (CFSG.oddCore H) ⟨(ℓ : G), ℓ.2⟩ = c⁻¹ := hℓc
  rw [hℓ'] at hbar
  rw [hPeq, ← hbar]
  exact G4c.bar_mono hTℓ

omit [Finite G] in
include hTK hLn hTL in
theorem bar_genW_le : bar H (genW H K₀ T) ≤ L := by
  rw [bar_le_iff ((genW_le hTK).trans inf_le_left)]
  refine iSup₂_le fun k hk => ?_
  rw [← bar_le_iff (fun x hx => ?_)]
  · rw [bar_map_cj T (mem_inf.mp hk).1]
    rintro _ ⟨t, ht, rfl⟩
    rw [G4c.cj_apply]
    exact hLn.conj_mem _ (hTL.le ht) _
  · obtain ⟨t, ht, rfl⟩ := hx
    rw [G4c.cj_apply]
    exact mul_mem (mul_mem (mem_inf.mp hk).1 (mem_inf.mp (hTK ht)).1)
      (inv_mem (mem_inf.mp hk).1)

include hTK hT hVH hV hK₀ hLn hTL hLV in
theorem bar_genW_normal : (bar H (genW H K₀ T)).Normal := by
  refine G4c.normal_of_top_le_normalizer fun u _ => G4c.mem_normalizer_of_map_cj_eq ?_
  have key : ∀ u : Bar H, (bar H (genW H K₀ T)).map (G4c.cj u) ≤ bar H (genW H K₀ T) := by
    intro u
    rw [G4c.map_cj_le_iff, bar_le_iff ((genW_le hTK).trans inf_le_left)]
    refine iSup₂_le fun k hk => ?_
    rw [← bar_le_iff (fun x hx => ?_), bar_map_cj T (mem_inf.mp hk).1, ← G4c.map_cj_le_iff,
      G4b.map_conj_map_conj]
    · exact map_bar_le_bar_genW hTK hT hVH hV hK₀ hLn hTL hLV _
    · obtain ⟨t, ht, rfl⟩ := hx
      rw [G4c.cj_apply]
      exact mul_mem (mul_mem (mem_inf.mp hk).1 (mem_inf.mp (hTK ht)).1)
        (inv_mem (mem_inf.mp hk).1)
  refine le_antisymm (key u) ?_
  have h := map_mono (f := G4c.cj u) (key u⁻¹)
  rwa [G4c.map_cj_inv_cj] at h

end GenW

end G5one

end CFSG.GH72
