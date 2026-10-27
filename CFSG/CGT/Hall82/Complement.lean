module

public import CFSG.CGT.Hall82.Dichotomy
public import CFSG.CGT.Hall82.ModelFacts

public section

namespace CFSG.CGT.Hall82

theorem index_ne_two_of_dihedral {X : Type} [Group X] [Finite X] {y t : X}
    (ht : t * t = 1) (hy : y ^ 4 = 1) (hty : (t * y) * (t * y) = 1)
    (hcl : Nat.card (Subgroup.closure ({y, t} : Set X)) = 8)
    (hodd : Odd (Nat.card X / 8)) (h8 : 8 ∣ Nat.card X)
    (hconj : ∀ x : X, x * x = 1 → x ≠ 1 → ∃ a : X, a * t * a⁻¹ = x)
    (N : Subgroup X) : N.index ≠ 2 := by
  classical
  intro hNidx
  have hconj_yt : t * y * t⁻¹ = y⁻¹ := by
    have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have h1 : t * y * t = y⁻¹ := by
      calc t * y * t = (t * y) * (t * y) * y⁻¹ := by group
        _ = y⁻¹ := by rw [hty, one_mul]
    rw [ht_inv]
    exact h1
  have hy2_ne : y ^ 2 ≠ 1 := by
    intro hy2
    have hle := card_closure_pair_le_two_mul_card_zpowers (a := y) (b := t) ht hconj_yt
    rw [hcl] at hle
    have hle2 : Nat.card (Subgroup.zpowers y) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hy2)
    omega
  have hty_ne : t * y ≠ 1 := by
    intro h
    have ht_eq : t = y⁻¹ := by
      have := congrArg (· * y⁻¹) h
      simpa [mul_assoc] using this
    have hEq : Subgroup.closure ({y, t} : Set X) = Subgroup.zpowers y := by
      rw [ht_eq]
      exact closure_pair_eq_zpowers_of_mem_zpowers
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
    rw [hEq] at hcl
    have hle := card_zpowers_le_four_of_pow_four_eq_one hy
    omega
  haveI hNnormal : N.Normal := Subgroup.normal_of_index_eq_two hNidx
  have hy2N : y ^ 2 ∈ N := Subgroup.sq_mem_of_index_two hNidx y
  have hy2_sq : y ^ 2 * y ^ 2 = 1 := by
    calc y ^ 2 * y ^ 2 = y ^ 4 := by group
      _ = 1 := hy
  obtain ⟨a, ha⟩ := hconj (y ^ 2) hy2_sq hy2_ne
  have htN : t ∈ N := by
    have hconjmem : a⁻¹ * y ^ 2 * a ∈ N := by
      simpa only [inv_inv] using hNnormal.conj_mem (y ^ 2) hy2N a⁻¹
    have heq : a⁻¹ * y ^ 2 * a = t := by
      rw [← ha]
      group
    rwa [heq] at hconjmem
  have htyN : t * y ∈ N := by
    obtain ⟨b, hb⟩ := hconj (t * y) hty hty_ne
    have hconjmem : b * t * b⁻¹ ∈ N := hNnormal.conj_mem t htN b
    rwa [hb] at hconjmem
  have hyN : y ∈ N := by
    have h : t⁻¹ * (t * y) ∈ N := N.mul_mem (N.inv_mem htN) htyN
    simpa [mul_assoc] using h
  have hclosure_le : Subgroup.closure ({y, t} : Set X) ≤ N := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hyN
    · exact htN
  have h8dvdN : 8 ∣ Nat.card N := by
    have h := Subgroup.card_dvd_of_le hclosure_le
    rwa [hcl] at h
  have hcardN : Nat.card N * 2 = Nat.card X := by
    simpa [hNidx] using Subgroup.card_mul_index N
  have hX : Nat.card X = 8 * (Nat.card X / 8) := (Nat.mul_div_cancel' h8).symm
  obtain ⟨m, hm⟩ := h8dvdN
  have hk2 : Nat.card X / 8 = 2 * m := by
    rw [hm, hX] at hcardN
    omega
  exact hodd.not_two_dvd_nat ⟨m, hk2⟩

theorem exists_compl_or_forall_mem_mod {G X : Type} [Group G] [Group X] [Finite G]
    {H J V : Subgroup G} (hVJ : V ≤ J) (hJH : J ≤ H)
    (hVn : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    (hJc : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ * j⁻¹ ∈ V)
    (hJV : Nat.card J = 2 * Nat.card V)
    (π : ↥H →* X) (hπ : Function.Surjective π) (hker : π.ker = J.subgroupOf H)
    {y t : X} (ht : t * t = 1) (hy : y ^ 4 = 1) (hty : (t * y) * (t * y) = 1)
    (hcl : Nat.card (Subgroup.closure ({y, t} : Set X)) = 8)
    (hodd : Odd (Nat.card X / 8)) (h8 : 8 ∣ Nat.card X)
    (hconj : ∀ x : X, x * x = 1 → x ≠ 1 → ∃ a : X, a * t * a⁻¹ = x) :
    (∃ K : Subgroup G, V ≤ K ∧ K ≤ H ∧ K ⊓ J = V ∧ K ⊔ J = H) ∨
      ∀ h ∈ H, h * h ∈ V → h ∈ J := by
  classical
  haveI : Finite X := Finite.of_surjective π hπ
  have hVH : V ≤ H := hVJ.trans hJH
  haveI hVHnormal : (V.subgroupOf H).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr
      (hVn (g : G) g.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))⟩
  have hVleKer : V.subgroupOf H ≤ π.ker := by
    intro v hv
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr (hVJ (Subgroup.mem_subgroupOf.mp hv))
  let Q := ↥H ⧸ V.subgroupOf H
  let mk : ↥H →* Q := QuotientGroup.mk' (V.subgroupOf H)
  let W : Subgroup Q := (J.subgroupOf H).map mk
  let πQ : Q →* X := QuotientGroup.lift (V.subgroupOf H) π hVleKer
  have hπQ : Function.Surjective πQ :=
    QuotientGroup.lift_surjective_of_surjective (V.subgroupOf H) π hπ hVleKer
  have hkerQ : πQ.ker = W := by
    rw [QuotientGroup.ker_lift, hker]
  have hJHcard : Nat.card (J.subgroupOf H) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv
  have hVHcard : Nat.card (V.subgroupOf H) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
  have hW2 : Nat.card W = 2 := by
    have hrel : (V.subgroupOf H).relIndex (J.subgroupOf H) = Nat.card W := by
      have h := Subgroup.relIndex_ker (f := mk) (K := J.subgroupOf H)
      rw [QuotientGroup.ker_mk'] at h
      exact h
    have hmul : (V.subgroupOf H).relIndex (J.subgroupOf H) * Nat.card (V.subgroupOf H) =
        Nat.card (J.subgroupOf H) := by
      have h := Subgroup.relIndex_mul_card (V.subgroupOf H) (J.subgroupOf H)
      rwa [inf_eq_left.mpr (Subgroup.subgroupOf_mono H hVJ)] at h
    rw [hrel, hVHcard, hJHcard, hJV] at hmul
    exact Nat.mul_right_cancel Nat.card_pos hmul
  have hWZ : W ≤ Subgroup.center Q := by
    rintro w ⟨j, hj, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have hcomm : mk j * mk h = mk h * mk j := by
      rw [← map_mul, ← map_mul]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      have hVmem := hJc ((h : G)⁻¹) (H.inv_mem h.2) ((j : G)⁻¹) (J.inv_mem hjJ)
      simpa [mul_assoc] using hVmem
    exact hcomm.symm
  rcases exists_compl_or_forall_mem (H := Q) (X := X) (π := πQ) (W := W)
      hπQ hkerQ hW2 hWZ ht hy hty hcl hodd h8 hconj with hsplit | hall
  · left
    obtain ⟨Kbar, hKbarInf, hKbarSup⟩ := hsplit
    let K' : Subgroup ↥H := Kbar.comap mk
    let K : Subgroup G := K'.map H.subtype
    have hK'inf : K' ⊓ J.subgroupOf H = V.subgroupOf H := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxK, hxJ⟩ := Subgroup.mem_inf.mp hx
        have hxW : mk x ∈ W := Subgroup.mem_map_of_mem mk hxJ
        have hxbot : mk x ∈ (⊥ : Subgroup Q) := by
          rw [← hKbarInf]
          change mk x ∈ Kbar at hxK
          exact Subgroup.mem_inf.mpr ⟨hxW, hxK⟩
        rw [Subgroup.mem_bot] at hxbot
        exact (QuotientGroup.eq_one_iff x).mp hxbot
      · intro hx
        have hxker : mk x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
        exact Subgroup.mem_inf.mpr ⟨by
          rw [Subgroup.mem_comap, hxker]
          exact Kbar.one_mem, Subgroup.mem_subgroupOf.mpr
            (hVJ (Subgroup.mem_subgroupOf.mp hx))⟩
    have hK'sup : K' ⊔ J.subgroupOf H = ⊤ := by
      have h := congrArg (Subgroup.comap mk) hKbarSup
      rw [← Subgroup.comap_sup_eq (f := mk) W Kbar (QuotientGroup.mk'_surjective (V.subgroupOf H)),
        QuotientGroup.comap_map_mk', sup_eq_right.mpr (Subgroup.subgroupOf_mono H hVJ),
        Subgroup.comap_top] at h
      simpa [sup_comm] using h
    have hVHleK' : V.subgroupOf H ≤ K' := by
      rw [← hK'inf]
      exact inf_le_left
    have hVK : V ≤ K := by
      intro v hv
      have hvH : v ∈ H := hVH hv
      have hvVH : (⟨v, hvH⟩ : ↥H) ∈ V.subgroupOf H := Subgroup.mem_subgroupOf.mpr hv
      exact Subgroup.mem_map.mpr ⟨⟨v, hvH⟩, hVHleK' hvVH, rfl⟩
    have hKH : K ≤ H := Subgroup.map_subtype_le K'
    have hKJ : K ⊓ J = V := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxK, hxJ⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨k', hk'K, hk'x⟩ := Subgroup.mem_map.mp hxK
        have hk'JH : k' ∈ J.subgroupOf H := by
          rw [Subgroup.mem_subgroupOf]
          rw [show (k' : G) = x from hk'x]
          exact hxJ
        have hk'V : k' ∈ V.subgroupOf H := by
          rw [← hK'inf]
          exact Subgroup.mem_inf.mpr ⟨hk'K, hk'JH⟩
        rw [← hk'x]
        exact Subgroup.mem_subgroupOf.mp hk'V
      · intro hx
        exact Subgroup.mem_inf.mpr ⟨hVK hx, hVJ hx⟩
    have hKJ' : K ⊔ J = H := by
      have h := congrArg (Subgroup.map H.subtype) hK'sup
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJH,
        Subgroup.map_top, Subgroup.range_subtype] at h
      exact h
    exact ⟨K, hVK, hKH, hKJ, hKJ'⟩
  · right
    intro h hh hsq
    have hq2 : mk ⟨h, hh⟩ * mk ⟨h, hh⟩ = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hsq)
    have hmem : mk ⟨h, hh⟩ ∈ W := hall (mk ⟨h, hh⟩) hq2
    have hcomap : (⟨h, hh⟩ : ↥H) ∈ Subgroup.comap mk W := by
      rw [Subgroup.mem_comap]
      exact hmem
    have hJH : (⟨h, hh⟩ : ↥H) ∈ J.subgroupOf H := by
      change (⟨h, hh⟩ : ↥H) ∈ Subgroup.comap mk (Subgroup.map mk (J.subgroupOf H)) at hcomap
      rw [QuotientGroup.comap_map_mk' (V.subgroupOf H) (J.subgroupOf H),
        sup_eq_right.mpr (Subgroup.subgroupOf_mono H hVJ)] at hcomap
      exact hcomap
    exact Subgroup.mem_subgroupOf.mp hJH

theorem eq_of_inf_eq_of_sup_eq {G X : Type} [Group G] [Group X] [Finite G]
    {H J V K K' : Subgroup G} (hVJ : V ≤ J) (hJH : J ≤ H)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (π : ↥H →* X) (hπ : Function.Surjective π) (hker : π.ker = J.subgroupOf H)
    (hX : ∀ N : Subgroup X, N.index ≠ 2) (hJV : Nat.card J = 2 * Nat.card V)
    (hVK : V ≤ K) (hKH : K ≤ H) (hKJ : K ⊓ J = V) (hKJ' : K ⊔ J = H)
    (hVK' : V ≤ K') (hK'H : K' ≤ H) (hK'J : K' ⊓ J = V) (hK'J' : K' ⊔ J = H) :
    K = K' := by
  classical
  haveI : Finite X := Finite.of_surjective π hπ
  have hVH : V ≤ H := hVJ.trans hJH
  have hJcard : Nat.card (J.subgroupOf H) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv
  have hHcard : Nat.card ↥H = Nat.card J * Nat.card X := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := π) hπ
    rw [hker, hJcard] at h
    exact h.symm
  haveI hJHnormal : (J.subgroupOf H).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr
      (hJn (g : G) g.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))⟩
  let πK : ↥K →* X := π.comp (Subgroup.inclusion hKH)
  have hπK : Function.Surjective πK := by
    intro x
    obtain ⟨h, hh⟩ := hπ x
    have hmemH : (⟨h, h.2⟩ : ↥H) ∈ (K.subgroupOf H) ⊔ (J.subgroupOf H) := by
      rw [← Subgroup.subgroupOf_sup hKH hJH, hKJ']
      exact Subgroup.mem_subgroupOf.mpr h.2
    obtain ⟨k, hkK, j, hjJ, hkj⟩ := Subgroup.mem_sup_of_normal_right.mp hmemH
    have hkKG : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
    have hjker : π j = 1 := by
      have hmemker : j ∈ π.ker := by
        rw [hker]
        exact hjJ
      exact MonoidHom.mem_ker.mp hmemker
    refine ⟨⟨(k : G), hkKG⟩, ?_⟩
    have hsub : (⟨h, h.2⟩ : ↥H) = k * j := hkj.symm
    calc πK ⟨(k : G), hkKG⟩ = π k := rfl
      _ = π k * π j := by rw [hjker, mul_one]
      _ = π (k * j) := (map_mul π _ _).symm
      _ = π ⟨h, h.2⟩ := by rw [← hsub]
      _ = x := hh
  have hkerK : πK.ker = V.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hmem : (⟨k, hKH k.2⟩ : ↥H) ∈ π.ker := hk
      rw [hker] at hmem
      have hkJ : (k : G) ∈ J := Subgroup.mem_subgroupOf.mp hmem
      have hkKJ : (k : G) ∈ K ⊓ J := Subgroup.mem_inf.mpr ⟨k.2, hkJ⟩
      rw [hKJ] at hkKJ
      exact Subgroup.mem_subgroupOf.mpr hkKJ
    · intro hk
      have hkV : (k : G) ∈ V := Subgroup.mem_subgroupOf.mp hk
      have hkJ : (k : G) ∈ J := hVJ hkV
      have hmemker : (⟨k, hKH k.2⟩ : ↥H) ∈ π.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr hkJ
      exact MonoidHom.mem_ker.mp hmemker
  have hcardK : Nat.card K = Nat.card V * Nat.card X := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := πK) hπK
    rw [hkerK] at h
    have hVcard : Nat.card (V.subgroupOf K) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
    rw [hVcard] at h
    exact h.symm
  let πK' : ↥K' →* X := π.comp (Subgroup.inclusion hK'H)
  have hπK' : Function.Surjective πK' := by
    intro x
    obtain ⟨h, hh⟩ := hπ x
    have hmemH : (⟨h, h.2⟩ : ↥H) ∈ (K'.subgroupOf H) ⊔ (J.subgroupOf H) := by
      rw [← Subgroup.subgroupOf_sup hK'H hJH, hK'J']
      exact Subgroup.mem_subgroupOf.mpr h.2
    obtain ⟨k, hkK, j, hjJ, hkj⟩ := Subgroup.mem_sup_of_normal_right.mp hmemH
    have hkKG : (k : G) ∈ K' := Subgroup.mem_subgroupOf.mp hkK
    have hjker : π j = 1 := by
      have hmemker : j ∈ π.ker := by
        rw [hker]
        exact hjJ
      exact MonoidHom.mem_ker.mp hmemker
    refine ⟨⟨(k : G), hkKG⟩, ?_⟩
    have hsub : (⟨h, h.2⟩ : ↥H) = k * j := hkj.symm
    calc πK' ⟨(k : G), hkKG⟩ = π k := rfl
      _ = π k * π j := by rw [hjker, mul_one]
      _ = π (k * j) := (map_mul π _ _).symm
      _ = π ⟨h, h.2⟩ := by rw [← hsub]
      _ = x := hh
  have hkerK' : πK'.ker = V.subgroupOf K' := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hmem : (⟨k, hK'H k.2⟩ : ↥H) ∈ π.ker := hk
      rw [hker] at hmem
      have hkJ : (k : G) ∈ J := Subgroup.mem_subgroupOf.mp hmem
      have hkKJ : (k : G) ∈ K' ⊓ J := Subgroup.mem_inf.mpr ⟨k.2, hkJ⟩
      rw [hK'J] at hkKJ
      exact Subgroup.mem_subgroupOf.mpr hkKJ
    · intro hk
      have hkV : (k : G) ∈ V := Subgroup.mem_subgroupOf.mp hk
      have hkJ : (k : G) ∈ J := hVJ hkV
      have hmemker : (⟨k, hK'H k.2⟩ : ↥H) ∈ π.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr hkJ
      exact MonoidHom.mem_ker.mp hmemker
  have hcardK' : Nat.card K' = Nat.card V * Nat.card X := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := πK') hπK'
    rw [hkerK'] at h
    have hVcard : Nat.card (V.subgroupOf K') = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK').toEquiv
    rw [hVcard] at h
    exact h.symm
  have hcard_eq : Nat.card K = Nat.card K' := by rw [hcardK, hcardK']
  have hcardH : Nat.card ↥H = 2 * Nat.card K' := by
    calc Nat.card ↥H = Nat.card J * Nat.card X := hHcard
      _ = (2 * Nat.card V) * Nat.card X := by rw [hJV]
      _ = 2 * (Nat.card V * Nat.card X) := by ring
      _ = 2 * Nat.card K' := by rw [hcardK']
  have hK'index : (K'.subgroupOf H).index = 2 := by
    have h := Subgroup.card_mul_index (K'.subgroupOf H)
    have hcard_sub : Nat.card (K'.subgroupOf H) = Nat.card K' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'H).toEquiv
    rw [hcard_sub, hcardH] at h
    rw [mul_comm 2 (Nat.card K')] at h
    exact Nat.mul_left_cancel Nat.card_pos h
  have hK'relH : K'.relIndex H = 2 := hK'index
  have hrel_le : (K ⊓ K').relIndex K ≤ 2 := by
    have h1 : (K ⊓ K').relIndex K = K'.relIndex K := by
      simpa [inf_comm] using Subgroup.inf_relIndex_right K' K
    have h2 : K'.relIndex K ≤ K'.relIndex H :=
      Subgroup.relIndex_le_of_le_right (H := K') hKH (by rw [hK'relH]; norm_num)
    exact h1.trans_le (h2.trans (le_of_eq hK'relH))
  have hVL : V ≤ K ⊓ K' := le_inf hVK hVK'
  have hkernel_le : πK.ker ≤ (K ⊓ K').subgroupOf K := by
    rw [hkerK]
    exact Subgroup.subgroupOf_mono K hVL
  have hindex_eq : (((K ⊓ K').subgroupOf K).map πK).index =
      (K ⊓ K').relIndex K := by
    rw [Subgroup.index_map_eq (H := (K ⊓ K').subgroupOf K) hπK hkernel_le]
    rfl
  have himg_le : (((K ⊓ K').subgroupOf K).map πK).index ≤ 2 := by
    rw [hindex_eq]
    exact hrel_le
  have himg_ne : (((K ⊓ K').subgroupOf K).map πK).index ≠ 2 := hX _
  have himg_pos : (((K ⊓ K').subgroupOf K).map πK).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have himg_one : (((K ⊓ K').subgroupOf K).map πK).index = 1 := by omega
  have hrel_one : (K ⊓ K').relIndex K = 1 := by
    rw [← hindex_eq, himg_one]
  have hKle : K ≤ K ⊓ K' := Subgroup.relIndex_eq_one.mp hrel_one
  have hKleK' : K ≤ K' := fun x hx => (hKle hx).2
  exact Subgroup.eq_of_le_of_card_ge hKleK' (le_of_eq hcard_eq.symm)

theorem conj_eq_of_inf_eq_of_sup_eq {G X : Type} [Group G] [Group X] [Finite G]
    {H J V K : Subgroup G} (hVJ : V ≤ J) (hJH : J ≤ H)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (π : ↥H →* X) (hπ : Function.Surjective π) (hker : π.ker = J.subgroupOf H)
    (hX : ∀ N : Subgroup X, N.index ≠ 2) (hJV : Nat.card J = 2 * Nat.card V)
    (hVK : V ≤ K) (hKH : K ≤ H) (hKJ : K ⊓ J = V) (hKJ' : K ⊔ J = H)
    {g : G} (hHg : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ H)
    (hJg : ∀ x, x ∈ J ↔ g * x * g⁻¹ ∈ J)
    (hVg : ∀ x, x ∈ V ↔ g * x * g⁻¹ ∈ V) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  classical
  let c : G →* G := (MulAut.conj g).toMonoidHom
  let K' : Subgroup G := K.map c
  have hHmap : H.map c = H := by
    simpa [c] using (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      ((Subgroup.mem_normalizer_iff).mpr hHg)
  have hJmap : J.map c = J := by
    simpa [c] using (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      ((Subgroup.mem_normalizer_iff).mpr hJg)
  have hVmap : V.map c = V := by
    simpa [c] using (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      ((Subgroup.mem_normalizer_iff).mpr hVg)
  have hK'J : K' ⊓ J = V := by
    have h := Subgroup.map_inf K J c (by simpa [c] using (MulAut.conj g).injective)
    rw [hKJ, hJmap, hVmap] at h
    exact h.symm
  have hVK' : V ≤ K' := hK'J ▸ inf_le_left
  have hK'H : K' ≤ H := by
    intro x hx
    have hx' : x ∈ H.map c := Subgroup.map_mono hKH hx
    rwa [hHmap] at hx'
  have hK'J' : K' ⊔ J = H := by
    have h := congrArg (Subgroup.map c) hKJ'
    rw [Subgroup.map_sup, hJmap, hHmap] at h
    change K.map c ⊔ J = H
    exact h
  have hEq := eq_of_inf_eq_of_sup_eq hVJ hJH hJn π hπ hker hX hJV
    hVK hKH hKJ hKJ' hVK' hK'H hK'J hK'J'
  change K.map c = K
  exact hEq.symm

noncomputable def yL (hF : ModelFacts) : ↥hexaL := ⟨hallYP, hF.y_mem⟩

noncomputable def tL (hF : ModelFacts) : ↥hexaL := ⟨hallTP, hF.t_mem⟩

theorem hexaL_t_mul_t (hF : ModelFacts) : tL hF * tL hF = 1 := by
  apply Subtype.ext
  simpa [tL] using hF.t_mul_t

theorem hexaL_y_pow_four (hF : ModelFacts) : yL hF ^ 4 = 1 := by
  apply Subtype.ext
  simpa [yL] using hF.y_pow_four

theorem hexaL_ty_mul_ty (hF : ModelFacts) : (tL hF * yL hF) * (tL hF * yL hF) = 1 := by
  apply Subtype.ext
  simpa [tL, yL] using hF.ty_mul_ty

theorem hexaL_card_closure (hF : ModelFacts) :
    Nat.card (Subgroup.closure ({yL hF, tL hF} : Set ↥hexaL)) = 8 := by
  have himg : hexaL.subtype '' ({yL hF, tL hF} : Set ↥hexaL) =
      ({hallYP, hallTP} : Set (Equiv.Perm (Fin 64))) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨yL hF, Or.inl rfl, rfl⟩
      · exact ⟨tL hF, Or.inr rfl, rfl⟩
  have hmap : (Subgroup.closure ({yL hF, tL hF} : Set ↥hexaL)).map hexaL.subtype =
      Subgroup.closure ({hallYP, hallTP} : Set (Equiv.Perm (Fin 64))) := by
    rw [MonoidHom.map_closure, himg]
  have hcard := Subgroup.card_map_of_injective
    (K := Subgroup.closure ({yL hF, tL hF} : Set ↥hexaL)) hexaL.subtype_injective
  rw [hmap, hF.card_closure] at hcard
  exact hcard.symm

theorem hexaL_odd (hF : ModelFacts) : Odd (Nat.card ↥hexaL / 8) := by
  rw [hF.card]
  norm_num

theorem hexaL_dvd (hF : ModelFacts) : 8 ∣ Nat.card ↥hexaL := by
  rw [hF.card]
  norm_num

theorem hexaL_conj (hF : ModelFacts) :
    ∀ x : ↥hexaL, x * x = 1 → x ≠ 1 → ∃ a : ↥hexaL, a * tL hF * a⁻¹ = x := by
  intro x hx2 hx1
  obtain ⟨a, ha_mem, ha⟩ := hF.conj_t (x : Equiv.Perm (Fin 64)) x.2
    (congrArg Subtype.val hx2) (fun h => hx1 (Subtype.ext h))
  refine ⟨⟨a, ha_mem⟩, ?_⟩
  apply Subtype.ext
  simpa [tL] using ha

theorem index_ne_two_hexaL (hF : ModelFacts) (N : Subgroup ↥hexaL) : N.index ≠ 2 :=
  index_ne_two_of_dihedral (y := yL hF) (t := tL hF)
    (hexaL_t_mul_t hF) (hexaL_y_pow_four hF) (hexaL_ty_mul_ty hF)
    (hexaL_card_closure hF) (hexaL_odd hF) (hexaL_dvd hF) (hexaL_conj hF) N

end CFSG.CGT.Hall82
