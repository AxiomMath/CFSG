module

public import CFSG.CGT.L5R.WrapGL
public import CFSG.CGT.M24S.Balance
public import CFSG.CGT.M24S.NSHolt
public import CFSG.CGT.M24S.Type4

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Holt.General CFSG.GroupTheory.GL52

variable {G : Type} [Group G]

theorem card_inf_centralizer_eq_four [Finite G] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (hcard : Nat.card T = 16) {y : G} (hyN : y ∈ Subgroup.normalizer (T : Set G))
    (hy2 : y ^ 2 = 1) {a b : G} (ha : a ∈ T) (hb : b ∈ T) (hya : a * y ≠ y * a)
    (hyb : b * y ≠ y * b) (hyab : a * b * y ≠ y * (a * b)) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) = 4 := by
  set F := T ⊓ Subgroup.centralizer ({y} : Set G) with hF
  have hle4 : 4 ≤ Nat.card F := four_le_card_inf_centralizer_of_sq_eq_one hT hcard hyN hy2
  have hdvd : Nat.card F ∣ 16 := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have hnot : ∀ {c : G}, c * y ≠ y * c → c ∉ F := fun hcy hcF =>
    hcy (Subgroup.mem_centralizer_singleton_iff.mp hcF.2)
  have h16 : Nat.card F ≠ 16 := by
    intro h16
    have heq : F = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, h16])
    exact hnot hya (heq ▸ ha)
  have h8 : Nat.card F ≠ 8 := by
    intro h8
    have hidx : (F.subgroupOf T).index = 2 := by
      have h1 := Subgroup.card_mul_index (F.subgroupOf T)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : F ≤ T)).toEquiv, h8,
        hcard] at h1
      omega
    have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : T)) (b := ⟨b, hb⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
    exact hnot hyab (key.mpr (iff_of_false (hnot hya) (hnot hyb)))
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 4 from hdvd)
  rw [hm'] at hle4 h16 h8 ⊢
  interval_cases m <;> simp_all

theorem conj_coe_eq_of_mulEquiv {X : Subgroup G} (φ : ↥X ≃* G52) {u v w : ↥X}
    (h : φ u * φ v * (φ u)⁻¹ = φ w) : (u : G) * v * (u : G)⁻¹ = w := by
  have : u * v * u⁻¹ = w := φ.injective (by rw [map_mul, map_mul, map_inv, h])
  exact congrArg Subtype.val this

theorem mulEquiv_comm_of_coe_comm {X : Subgroup G} (φ : ↥X ≃* G52) {u v : ↥X}
    (h : (u : G) * v = v * u) : φ u * φ v = φ v * φ u := by
  rw [← map_mul, ← map_mul, show u * v = v * u from Subtype.ext h]

theorem mem_of_conj_mem_of_mulEquiv_l52 [Finite G] {T H : Subgroup G} (h : Hyp T H)
    (hL : LocalFacts T H) (h4 : ¬ HasType4 T) {X : Subgroup G}
    (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* G52) (t : Fin 4 → G)
    (htX : ∀ j, t j ∈ X) (hT : T = Subgroup.closure (Set.range t))
    (hφt : ∀ j, ((φ ⟨t j, htX j⟩ : G52) : M5) = tLM j) {z : G} (hzT : z ∈ T) (hz1 : z ≠ 1)
    {g : G} (hg : g⁻¹ * z * g ∈ X) : g ∈ X := by
  have htT : ∀ j, t j ∈ T := fun j => hT ▸ Subgroup.subset_closure ⟨j, rfl⟩
  have hzz : z * z = 1 := by rw [← sq]; exact h.wc.1.2 z hzT
  have hb2 : (⟨g⁻¹ * z * g, hg⟩ : ↥X) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, sq, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hzz,
      mul_one, inv_mul_cancel, Subgroup.coe_one])
  have hb1 : (⟨g⁻¹ * z * g, hg⟩ : ↥X) ≠ 1 := fun h1 => hz1 (by
    have h2 : g⁻¹ * z * g = 1 := congrArg Subtype.val h1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group)
  have hβ2 : φ ⟨g⁻¹ * z * g, hg⟩ ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have hβ1 : φ ⟨g⁻¹ * z * g, hg⟩ ≠ 1 := fun h1 => hb1 (φ.injective (h1.trans (map_one φ).symm))
  rcases exists_conj_tL_or_upsL hβ2 hβ1 (hφt 0) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    have hbx : ((φ.symm c : ↥X) : G) * t 0 * ((φ.symm c : ↥X) : G)⁻¹ = g⁻¹ * z * g :=
      conj_coe_eq_of_mulEquiv φ (u := φ.symm c) (v := ⟨t 0, htX 0⟩)
        (w := ⟨g⁻¹ * z * g, hg⟩) (by rw [φ.apply_symm_apply]; exact hc)
    have ht01 : t 0 ≠ 1 := by
      intro h1
      apply tLM_zero_ne_one
      rw [← hφt 0, show (⟨t 0, htX 0⟩ : ↥X) = 1 from Subtype.ext h1, map_one, Units.val_one]
    obtain ⟨k, hkH, hkz⟩ := hL.transitive z hzT hz1 (t 0) (htT 0) ht01
    set x : G := ((φ.symm c : ↥X) : G) with hxdef
    have hgxk : g * x * k ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * x * k * z = g * (x * (k * z * k⁻¹) * x⁻¹) * x * k := by group
        _ = g * (g⁻¹ * z * g) * x * k := by rw [hkz, hbx]
        _ = z * (g * x * k) := by group
    have hkX : k ∈ X := hX (hL.le_normalizer hkH)
    have h1 : g * x * k ∈ X := hX (hL.centralizer_le z hzT hz1 hgxk)
    have h2 := X.mul_mem h1 (X.mul_mem (X.inv_mem hkX) (X.inv_mem (φ.symm c).2))
    rwa [show g * x * k * (k⁻¹ * x⁻¹) = g by group] at h2
  ·
    exfalso
    obtain ⟨y, hφy⟩ : ∃ y : ↥X, φ y = upsL := ⟨φ.symm upsL, φ.apply_symm_apply upsL⟩
    have hbx : ((φ.symm c : ↥X) : G) * y * ((φ.symm c : ↥X) : G)⁻¹ = g⁻¹ * z * g :=
      conj_coe_eq_of_mulEquiv φ (u := φ.symm c) (v := y) (w := ⟨g⁻¹ * z * g, hg⟩)
        (by rw [φ.apply_symm_apply, hφy]; exact hc)
    obtain ⟨e0, e1, e2, e3⟩ := upsL_conj_tL (τ := fun j => φ ⟨t j, htX j⟩) hφt
    obtain ⟨n0, n1, n01⟩ := tL_mul_upsL_ne (τ := fun j => φ ⟨t j, htX j⟩) hφt
    have hy0 : (y : G) * t 0 * (y : G)⁻¹ = t 0 * t 2 :=
      conj_coe_eq_of_mulEquiv φ (u := y) (v := ⟨t 0, htX 0⟩)
        (w := ⟨t 0, htX 0⟩ * ⟨t 2, htX 2⟩)
        (by rw [map_mul φ ⟨t 0, htX 0⟩ ⟨t 2, htX 2⟩, hφy]; exact e0)
    have hy1 : (y : G) * t 1 * (y : G)⁻¹ = t 1 * t 3 :=
      conj_coe_eq_of_mulEquiv φ (u := y) (v := ⟨t 1, htX 1⟩)
        (w := ⟨t 1, htX 1⟩ * ⟨t 3, htX 3⟩)
        (by rw [map_mul φ ⟨t 1, htX 1⟩ ⟨t 3, htX 3⟩, hφy]; exact e1)
    have hy2 : (y : G) * t 2 * (y : G)⁻¹ = t 2 :=
      conj_coe_eq_of_mulEquiv φ (u := y) (v := ⟨t 2, htX 2⟩) (w := ⟨t 2, htX 2⟩)
        (by rw [hφy]; exact e2)
    have hy3 : (y : G) * t 3 * (y : G)⁻¹ = t 3 :=
      conj_coe_eq_of_mulEquiv φ (u := y) (v := ⟨t 3, htX 3⟩) (w := ⟨t 3, htX 3⟩)
        (by rw [hφy]; exact e3)
    have hyT : ∀ j, (y : G) * t j * (y : G)⁻¹ ∈ T := by
      intro j
      fin_cases j
      · simpa [hy0] using T.mul_mem (htT 0) (htT 2)
      · simpa [hy1] using T.mul_mem (htT 1) (htT 3)
      · simpa [hy2] using htT 2
      · simpa [hy3] using htT 3
    have hle : conjSubgroup (y : G) T ≤ T := by
      refine Subgroup.map_le_iff_le_comap.mpr ?_
      have hcl : Subgroup.closure (Set.range t) ≤
          T.comap (MulAut.conj (y : G)).toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        simpa [MulAut.conj_apply] using hyT j
      rwa [← hT] at hcl
    have heq : conjSubgroup (y : G) T = T := Subgroup.eq_of_le_of_card_ge hle (by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj (y : G)).injective])
    have hyN : (y : G) ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_of_conjSubgroup_eq heq
    have hysq : (y : G) ^ 2 = 1 := by
      have : y ^ 2 = 1 := φ.injective (by rw [map_pow, hφy, upsL_sq, map_one])
      have h2 := congrArg Subtype.val this
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have hn0 : t 0 * y ≠ y * t 0 := fun hc0 => by
      have := mulEquiv_comm_of_coe_comm φ (u := ⟨t 0, htX 0⟩) (v := y) hc0
      rw [hφy] at this
      exact n0 this
    have hn1 : t 1 * y ≠ y * t 1 := fun hc1 => by
      have := mulEquiv_comm_of_coe_comm φ (u := ⟨t 1, htX 1⟩) (v := y) hc1
      rw [hφy] at this
      exact n1 this
    have hn01 : t 0 * t 1 * y ≠ y * (t 0 * t 1) := fun hc01 => by
      have := mulEquiv_comm_of_coe_comm φ (u := ⟨t 0, htX 0⟩ * ⟨t 1, htX 1⟩) (v := y) hc01
      rw [map_mul φ ⟨t 0, htX 0⟩ ⟨t 1, htX 1⟩, hφy] at this
      exact n01 this
    have hyT' : (y : G) ∉ T := fun hy =>
      hn0 (congrArg Subtype.val (h.wc.1.1.is_comm.comm (⟨t 0, htT 0⟩ : T) ⟨y, hy⟩))
    have hcard4 := card_inf_centralizer_eq_four h.wc.1 hL.card_T hyN hysq (htT 0) (htT 1) hn0 hn1
      hn01
    have hyc : (y : G) ∈ conjSubgroup (((φ.symm c : ↥X) : G)⁻¹ * g⁻¹) T := by
      rw [mem_conjSubgroup]
      have hz' : (((φ.symm c : ↥X) : G)⁻¹ * g⁻¹)⁻¹ * y * (((φ.symm c : ↥X) : G)⁻¹ * g⁻¹) =
          z := by
        calc _ = g * (((φ.symm c : ↥X) : G) * y * ((φ.symm c : ↥X) : G)⁻¹) * g⁻¹ := by group
          _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hbx]
          _ = z := by group
      rw [hz']
      exact hzT
    exact h4 ⟨y, _, hyN, hyT', hyc, hcard4⟩

theorem eq_top_of_mulEquiv_l52 [Finite G] [IsSimpleGroup G] (hHolt : CFSG.Holt.H78.HoltTheorem1)
    {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H) (h4 : ¬ HasType4 T)
    {X : Subgroup G} (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* G52)
    (t : Fin 4 → G) (htX : ∀ j, t j ∈ X) (hT : T = Subgroup.closure (Set.range t))
    (hφt : ∀ j, ((φ ⟨t j, htX j⟩ : G52) : M5) = tLM j) : X = ⊤ := by
  by_contra hXtop
  obtain ⟨S, hTS, -, z, hzT, hz1, hZ⟩ := hL.sylow
  have hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    ((hZ z (hTS hzT)).mpr (Or.inr rfl) s hs).symm
  have hz2 : z ^ 2 = 1 := h.wc.1.2 z hzT
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hzT)
  have hTrip : IsHoltTriple G (G ⧸ X) z ((1 : G) : G ⧸ X) := by
    refine ⟨inferInstance, orderOf_eq_prime hz2 hz1, fun ω => ?_,
      ⟨S, hTS hzT, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq, mul_one,
      show (z * g)⁻¹ * g = g⁻¹ * z * g by rw [mul_inv_rev, hzinv], Subgroup.inv_mem_iff]
    exact ⟨fun hg => mem_of_conj_mem_of_mulEquiv_l52 h hL h4 hX φ t htX hT hφt hzT hz1 hg,
      fun hg => X.mul_mem (X.mul_mem (X.inv_mem hg) hzX) hg⟩
  exact false_of_isHoltTriple hHolt hXtop (hL.card_sylow S) hZ hTrip

end CFSG.CGT.L5R
