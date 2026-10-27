module

public import CFSG.LargeExtraspecial.SMod20UaOrbit
public import CFSG.LargeExtraspecial.SMod20CollCert

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

attribute [local irreducible] uaPts uPts uPos collS2

@[expose] noncomputable def uaRank (i c : ℕ) :
    Set (Equiv.Perm (Fin 693)) :=
  {u | ∃ a < 512, 0 < a ∧ uaCls collS2 a = c ∧ uaPsi i a = u}

theorem collCo_parts :
    (∀ k < 21, 0 < uaCo[k]! ∧ uaCo[k]! < 512) ∧
      (∀ k < 21, ∀ l < 21, uaCo[k]! = uaCo[l]! → k = l) ∧
      (∀ k < 21, ∀ l < 21, k < l → ∀ m < 21, uaCo[m]! ≠ uaCo[k]! ^^^ uaCo[l]!) ∧
      ∀ k < 21, ∀ l < 21, k < l → ∀ k' < 21, ∀ l' < 21, k' < l' →
        uaCo[k]! ^^^ uaCo[l]! = uaCo[k']! ^^^ uaCo[l']! → k = k' ∧ l = l' := by
  have h := collFacts.co
  unfold collCoOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun k hk => h1 k (Nat.zero_le _) hk, fun k hk l hl he => ?_, fun k hk l hl hkl => ?_,
    fun k hk l hl hkl k' hk' l' hl' hkl' he => ?_⟩
  · rcases h2 k (Nat.zero_le _) hk l (Nat.zero_le _) hl with h | h
    · exact h
    · exact absurd he h
  · rcases h3 k (Nat.zero_le _) hk l (Nat.zero_le _) hl with h | h
    · omega
    · exact fun m hm => h.1 m (Nat.zero_le _) hm
  · rcases h3 k (Nat.zero_le _) hk l (Nat.zero_le _) hl with h | h
    · omega
    · rcases h.2 k' (Nat.zero_le _) hk' l' (Nat.zero_le _) hl' with (h' | h') | h'
      · omega
      · exact h'
      · exact absurd he h'

theorem uaMem_uaCo {a : ℕ} : uaMem uaCo a = true ↔ ∃ k < 21, uaCo[k]! = a := by
  unfold uaMem
  rw [anyIn_eq_true]
  simp only [beq_iff_eq]

theorem uaCls_def (a : ℕ) : uaCls collS2 a =
    if a == 0 then 0 else if uaMem uaCo a then 1 else if collS2[a]! then 2 else 3 := rfl

theorem uaCls_eq_one {a : ℕ} :
    uaCls collS2 a = 1 ↔ ∃ k < 21, uaCo[k]! = a := by
  rw [uaCls_def]
  by_cases h0 : a = 0
  · subst h0
    simp only [beq_self_eq_true, ite_true]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro ⟨k, hk, he⟩
      exact absurd he (Nat.pos_iff_ne_zero.1 (collCo_parts.1 k hk).1)
  · have h0' : (a == 0) = false := beq_eq_false_iff_ne.2 h0
    rw [h0', ite_eq_right_of_eq_false _ _ (by decide)]
    by_cases hm : uaMem uaCo a = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
      exact ⟨fun _ => uaMem_uaCo.1 hm, fun _ => rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
      constructor
      · intro h
        split at h <;> exact absurd h (by decide)
      · intro h
        exact absurd (uaMem_uaCo.2 h) hm

theorem xor_pair_symm {k l : ℕ} : uaCo[k]! ^^^ uaCo[l]! = uaCo[l]! ^^^ uaCo[k]! := Nat.xor_comm _ _

theorem uaCls_eq_two {a : ℕ} (ha : a < 512) :
    uaCls collS2 a = 2 ↔ ∃ k < 21, ∃ l < 21, k ≠ l ∧ uaCo[k]! ^^^ uaCo[l]! = a := by
  obtain ⟨-, hinj, hnot, -⟩ := collCo_parts
  have hnot' : ∀ k < 21, ∀ l < 21, k ≠ l → ∀ m < 21, uaCo[m]! ≠ uaCo[k]! ^^^ uaCo[l]! := by
    intro k hk l hl hkl m hm
    rcases lt_or_gt_of_ne hkl with h | h
    · exact hnot k hk l hl h m hm
    · rw [xor_pair_symm]
      exact hnot l hl k hk h m hm
  have hpos : ∀ k < 21, ∀ l < 21, k ≠ l → uaCo[k]! ^^^ uaCo[l]! ≠ 0 := fun k hk l hl hkl h =>
    hkl (hinj k hk l hl (xor_eq_zero_iff.1 h))
  rw [uaCls_def]
  constructor
  · intro h
    by_cases h0 : a = 0
    · rw [h0] at h
      exact absurd h (by decide)
    · rw [beq_eq_false_iff_ne.2 h0, ite_eq_right_of_eq_false _ _ (by decide)] at h
      by_cases hm : uaMem uaCo a = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)] at h
        exact absurd h (by decide)
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)] at h
        by_cases hs : collS2[a]! = true
        · exact (collS2_get ha).1 hs
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
          exact absurd h (by decide)
  · rintro ⟨k, hk, l, hl, hkl, rfl⟩
    have hm : uaMem uaCo (uaCo[k]! ^^^ uaCo[l]!) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨m, hm, he⟩ := uaMem_uaCo.1 h
      exact hnot' k hk l hl hkl m hm he
    rw [beq_eq_false_iff_ne.2 (hpos k hk l hl hkl), ite_eq_right_of_eq_false _ _ (by decide), hm,
      ite_eq_right_of_eq_false _ _ (by decide),
      ite_eq_left_of_eq_true _ _ (eq_true ((collS2_get ha).2 ⟨k, hk, l, hl, hkl, rfl⟩))]

theorem uaCls_cases {a : ℕ} (ha : 0 < a) :
    uaCls collS2 a = 1 ∨ uaCls collS2 a = 2 ∨ uaCls collS2 a = 3 := by
  rw [uaCls_def, beq_eq_false_iff_ne.2 (Nat.pos_iff_ne_zero.1 ha),
    ite_eq_right_of_eq_false _ _ (by decide)]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem uaCls_zero : uaCls collS2 0 = 0 := by
  rw [uaCls_def]
  rfl

section Rank

variable
  {i : ℕ}

theorem uaRank_one (hi : i < 891) : uaRank i 1 = tvP '' wPlane i := by
  ext u
  constructor
  · rintro ⟨a, -, -, hc, rfl⟩
    obtain ⟨k, hk, rfl⟩ := uaCls_eq_one.1 hc
    exact ⟨wPt i k, wPt_mem i hk, by rw [uaPsi_co hi hk]; rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨uaCo[k]!, uaCo_lt hk, (collCo_parts.1 k hk).1, uaCls_eq_one.2 ⟨k, hk, rfl⟩,
      uaPsi_co hi hk⟩

theorem uaRank_two (hi : i < 891) :
    uaRank i 2 = {u | ∃ p ∈ wPlane i, ∃ q ∈ wPlane i, p ≠ q ∧ tvP p * tvP q = u} := by
  ext u
  constructor
  · rintro ⟨a, ha, -, hc, rfl⟩
    obtain ⟨k, hk, l, hl, hkl, rfl⟩ := (uaCls_eq_two ha).1 hc
    exact ⟨wPt i k, wPt_mem i hk, wPt i l, wPt_mem i hl, fun h => hkl (wPt_inj hi hk hl h),
      by rw [uaPsi_xor hi, uaPsi_co hi hk, uaPsi_co hi hl]; rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, _, ⟨l, hl, rfl⟩, hpq, rfl⟩
    have hkl : k ≠ l := fun h => hpq (by rw [h])
    have hlt := Nat.xor_lt_two_pow (n := 9) (uaCo_lt hk) (uaCo_lt hl)
    refine ⟨_, hlt, Nat.pos_of_ne_zero fun h =>
      hkl (collCo_parts.2.1 k hk l hl (xor_eq_zero_iff.1 h)),
      (uaCls_eq_two hlt).2 ⟨k, hk, l, hl, hkl, rfl⟩, ?_⟩
    rw [uaPsi_xor hi, uaPsi_co hi hk, uaPsi_co hi hl]
    rfl

theorem uaRank_eq_of_mem (hi : i < 891) {c c' : ℕ} {u : Equiv.Perm (Fin 693)}
    (hu : u ∈ uaRank i c) (hu' : u ∈ uaRank i c') : c = c' := by
  obtain ⟨a, ha, -, rfl, rfl⟩ := hu
  obtain ⟨b, hb, -, rfl, he⟩ := hu'
  rw [uaPsi_inj hi hb ha he]

theorem mem_uaRank_cases (hi : i < 891) {u : Equiv.Perm (Fin 693)} (hu : u ∈ UA i)
    (h1 : u ≠ 1) : u ∈ uaRank i 1 ∨ u ∈ uaRank i 2 ∨ u ∈ uaRank i 3 := by
  obtain ⟨a, ha, rfl⟩ := (mem_UA hi).1 hu
  have ha0 : 0 < a := Nat.pos_of_ne_zero fun h => h1 (by rw [h, uaPsi_zero])
  rcases uaCls_cases ha0 with h | h | h
  · exact Or.inl ⟨a, ha, ha0, h, rfl⟩
  · exact Or.inr (Or.inl ⟨a, ha, ha0, h, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ha0, h, rfl⟩)

theorem uaRank_subset (hi : i < 891) (c : ℕ) : uaRank i c ⊆ UA i \ {1} := by
  rintro _ ⟨a, ha, ha0, -, rfl⟩
  exact ⟨uaPsi_mem_UA a, uaPsi_ne_one hi ha0 ha⟩

theorem uaRank_three (hi : i < 891) :
    uaRank i 3 = (UA i : Set (Equiv.Perm (Fin 693))) \ ({1} ∪ uaRank i 1 ∪ uaRank i 2) := by
  ext u
  constructor
  · intro hu
    obtain ⟨hU, h1⟩ := uaRank_subset hi 3 hu
    refine ⟨hU, ?_⟩
    rintro ((h | h) | h)
    · exact h1 h
    · exact absurd (uaRank_eq_of_mem hi hu h) (by decide)
    · exact absurd (uaRank_eq_of_mem hi hu h) (by decide)
  · rintro ⟨hU, hnot⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hnot
    obtain ⟨⟨h1, hr1⟩, hr2⟩ := hnot
    rcases mem_uaRank_cases hi hU h1 with h | h | h
    · exact absurd h hr1
    · exact absurd h hr2
    · exact h

theorem uaRank_eq_image {c : ℕ} (hc : 0 < c) :
    uaRank i c = uaPsi i '' ↑((Finset.range 512).filter fun a => uaCls collS2 a = c) := by
  ext u
  simp only [uaRank, Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, -, hc', rfl⟩
    exact ⟨a, ⟨ha, hc'⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hc'⟩, rfl⟩
    refine ⟨a, ha, Nat.pos_of_ne_zero fun h => ?_, hc', rfl⟩
    rw [h, uaCls_zero] at hc'
    omega

theorem ncard_uaRank (hi : i < 891) {c : ℕ} (hc : 0 < c) :
    (uaRank i c).ncard = (List.range 512).countP fun a => uaCls collS2 a == c := by
  rw [uaRank_eq_image hc, Set.InjOn.ncard_image fun a ha b hb h => uaPsi_inj hi
    (Finset.mem_range.1 (Finset.mem_filter.1 ha).1) (Finset.mem_range.1 (Finset.mem_filter.1 hb).1)
    h, Set.ncard_coe_finset, countP_range_eq_card]
  simp only [beq_iff_eq]

theorem ncard_uaRank_eq (hi : i < 891) :
    (uaRank i 1).ncard = 21 ∧ (uaRank i 2).ncard = 210 ∧ (uaRank i 3).ncard = 280 := by
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate21262.2.2.1
  rw [ncard_uaRank hi (by norm_num), ncard_uaRank hi (by norm_num), ncard_uaRank hi (by norm_num)]
  exact ⟨h1, h2, h3⟩

end Rank

section Orbit

variable
  {i : ℕ}

theorem conj_mem_uaRank_one_two {j : ℕ} (hi : i < 891) (hj : j < 891) {g : Equiv.Perm (Fin 693)}
    (hg : IsPolarAut g) (hW : ⇑g '' wPlane i = wPlane j) {c : ℕ} (hc : c = 1 ∨ c = 2)
    {u : Equiv.Perm (Fin 693)} (hu : u ∈ uaRank i c) : g * u * g⁻¹ ∈ uaRank j c := by
  rcases hc with rfl | rfl
  · rw [uaRank_one hi] at hu
    rw [uaRank_one hj]
    obtain ⟨p, hp, rfl⟩ := hu
    exact ⟨g p, hW ▸ ⟨p, hp, rfl⟩, (hg.mul_tvP_mul_inv p).symm⟩
  · rw [uaRank_two hi] at hu
    rw [uaRank_two hj]
    obtain ⟨p, hp, q, hq, hpq, rfl⟩ := hu
    refine ⟨g p, hW ▸ ⟨p, hp, rfl⟩, g q, hW ▸ ⟨q, hq, rfl⟩, g.injective.ne hpq, ?_⟩
    rw [← hg.mul_tvP_mul_inv p, ← hg.mul_tvP_mul_inv q]
    group

theorem conj_mem_uaRank {j : ℕ} (hi : i < 891) (hj : j < 891) {g : Equiv.Perm (Fin 693)}
    (hg : IsPolarAut g) (hW : ⇑g '' wPlane i = wPlane j) (c : ℕ)
    {u : Equiv.Perm (Fin 693)} (hu : u ∈ uaRank i c) : g * u * g⁻¹ ∈ uaRank j c := by
  have hc : c = 1 ∨ c = 2 ∨ c = 3 := by
    obtain ⟨a, -, ha0, rfl, -⟩ := hu
    exact uaCls_cases ha0
  rcases hc with hc | hc | hc
  · exact conj_mem_uaRank_one_two hi hj hg hW (Or.inl hc) hu
  · exact conj_mem_uaRank_one_two hi hj hg hW (Or.inr hc) hu
  · subst hc
    rw [uaRank_three hi] at hu
    rw [uaRank_three hj]
    obtain ⟨hU, hnot⟩ := hu
    refine ⟨conj_mem_UA hg hW hU, fun h => hnot ?_⟩
    have hback : ∀ c, c = 1 ∨ c = 2 → g * u * g⁻¹ ∈ uaRank j c → u ∈ uaRank i c := by
      intro c hc h'
      have := conj_mem_uaRank_one_two hj hi hg.inv (image_wPlane_inv hW) hc h'
      rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group] at this
    rcases h with (h | h) | h
    · left; left
      rw [Set.mem_singleton_iff] at h ⊢
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact Or.inl (Or.inr (hback 1 (Or.inl rfl) h))
    · exact Or.inr (hback 2 (Or.inr rfl) h)

theorem conj_mem_PA {j : ℕ} {h : Equiv.Perm (Fin 693)} (hh : h ∈ T46)
    (hW : ⇑h '' wPlane j = wPlane i) {g : Equiv.Perm (Fin 693)} (hg : g ∈ PA j) :
    h * g * h⁻¹ ∈ PA i := by
  refine ⟨T46.mul_mem (T46.mul_mem hh hg.1) (T46.inv_mem hh), mem_stabilizer_wPlane.2 ?_⟩
  rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp,
    image_wPlane_inv hW, mem_stabilizer_wPlane.1 hg.2, hW]

theorem exists_PA_conj_zero {c : ℕ} {u v : Equiv.Perm (Fin 693)} (hu : u ∈ uaRank 0 c)
    (hv : v ∈ uaRank 0 c) : ∃ g ∈ PA 0, g * u * g⁻¹ = v := by
  obtain ⟨a, ha, -, hca, rfl⟩ := hu
  obtain ⟨b, hb, -, hcb, rfl⟩ := hv
  obtain ⟨x, hx, hxa⟩ := exists_conj_uaRoot ha
  obtain ⟨y, hy, hyb⟩ := exists_conj_uaRoot hb
  refine ⟨y * x⁻¹, (PA 0).mul_mem hy ((PA 0).inv_mem hx), ?_⟩
  rw [hxa, hyb, hca, hcb]
  group

theorem exists_PA_conj (hi : i < 891) {c : ℕ} {u v : Equiv.Perm (Fin 693)}
    (hu : u ∈ uaRank i c) (hv : v ∈ uaRank i c) : ∃ g ∈ PA i, g * u * g⁻¹ = v := by
  obtain ⟨h, hh, hhW⟩ := exists_image_wPlane_zero hi
  have hpa := isPolarAut_of_mem hh
  have hinv := image_wPlane_inv hhW
  have hu' := conj_mem_uaRank hi (by norm_num) hpa.inv hinv c hu
  have hv' := conj_mem_uaRank hi (by norm_num) hpa.inv hinv c hv
  obtain ⟨g, hg, hgu⟩ := exists_PA_conj_zero hu' hv'
  refine ⟨h * g * h⁻¹, conj_mem_PA hh hhW hg, ?_⟩
  calc h * g * h⁻¹ * u * (h * g * h⁻¹)⁻¹ = h * (g * (h⁻¹ * u * h⁻¹⁻¹) * g⁻¹) * h⁻¹ := by group
    _ = v := by rw [hgu]; group

theorem orbit_rank_one (hi : i < 891) {O : Set (Equiv.Perm (Fin 693))} (hO : O ⊆ UA i)
    (h1 : (1 : Equiv.Perm (Fin 693)) ∉ O) (hne : O.Nonempty)
    (hinv : ∀ g ∈ PA i, ∀ u ∈ O, g * u * g⁻¹ ∈ O) (hdvd : O.ncard ∣ 336) :
    O = tvP '' wPlane i := by
  have hfull : ∀ c, ∀ u ∈ O, u ∈ uaRank i c → uaRank i c ⊆ O := fun c u hu huc v hv => by
    obtain ⟨g, hg, rfl⟩ := exists_PA_conj hi huc hv
    exact hinv g hg u hu
  have hx : ∀ c, (O ∩ uaRank i c).ncard = 0 ∨ (O ∩ uaRank i c).ncard = (uaRank i c).ncard := by
    intro c
    by_cases h : ∃ u ∈ O, u ∈ uaRank i c
    · obtain ⟨u, hu, huc⟩ := h
      right
      rw [Set.inter_eq_right.2 (hfull c u hu huc)]
    · left
      rw [Set.ncard_eq_zero (Set.toFinite _)]
      exact Set.eq_empty_iff_forall_notMem.2 fun u hu => h ⟨u, hu.1, hu.2⟩
  have hdisj : ∀ c c', c ≠ c' → Disjoint (O ∩ uaRank i c) (O ∩ uaRank i c') := fun c c' hcc' =>
    Set.disjoint_left.2 fun u hu hu' => hcc' (uaRank_eq_of_mem hi hu.2 hu'.2)
  have hcover : O = (O ∩ uaRank i 1) ∪ (O ∩ uaRank i 2) ∪ (O ∩ uaRank i 3) := by
    ext u
    constructor
    · intro hu
      rcases mem_uaRank_cases hi (hO hu) fun h => h1 (h ▸ hu) with h | h | h
      · exact Or.inl (Or.inl ⟨hu, h⟩)
      · exact Or.inl (Or.inr ⟨hu, h⟩)
      · exact Or.inr ⟨hu, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  have hsplit : O.ncard = (O ∩ uaRank i 1).ncard + (O ∩ uaRank i 2).ncard +
      (O ∩ uaRank i 3).ncard := by
    conv_lhs => rw [hcover]
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hdisj 1 3 (by decide),
      hdisj 2 3 (by decide)⟩) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq (hdisj 1 2 (by decide)) (Set.toFinite _) (Set.toFinite _)]
  have hpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  obtain ⟨n1, n2, n3⟩ := ncard_uaRank_eq hi
  have hx1 : (O ∩ uaRank i 1).ncard = 0 ∨ (O ∩ uaRank i 1).ncard = 21 := n1 ▸ hx 1
  have hx2 : (O ∩ uaRank i 2).ncard = 0 ∨ (O ∩ uaRank i 2).ncard = 210 := n2 ▸ hx 2
  have hx3 : (O ∩ uaRank i 3).ncard = 0 ∨ (O ∩ uaRank i 3).ncard = 280 := n3 ▸ hx 3
  have key : (O ∩ uaRank i 1).ncard = 21 ∧ (O ∩ uaRank i 2).ncard = 0 ∧
      (O ∩ uaRank i 3).ncard = 0 := by
    rw [hsplit] at hdvd hpos
    rcases hx1 with e1 | e1 <;> rcases hx2 with e2 | e2 <;> rcases hx3 with e3 | e3 <;>
      rw [e1, e2, e3] at hdvd hpos <;> rw [e1, e2, e3] <;>
      first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; omega)
  have hR1 : O ∩ uaRank i 1 = uaRank i 1 := Set.eq_of_subset_of_ncard_le Set.inter_subset_right
    (by rw [key.1, n1]) (Set.toFinite _)
  rw [hcover, (Set.ncard_eq_zero (Set.toFinite _)).1 key.2.1,
    (Set.ncard_eq_zero (Set.toFinite _)).1 key.2.2, hR1, Set.union_empty, Set.union_empty,
    uaRank_one hi]

end Orbit

section Dist

variable
  {i : ℕ}

theorem exists_PA_image_zero {j j' : ℕ} (hj : j < 891) (hj' : j' < 891)
    (h : (wPlane 0 ∩ wPlane j).ncard = (wPlane 0 ∩ wPlane j').ncard) :
    ∃ g ∈ PA 0, ⇑g '' wPlane j = wPlane j' := by
  obtain ⟨x, hx, hxj⟩ := exists_PA_zero_image hj
  obtain ⟨y, hy, hyj⟩ := exists_PA_zero_image hj'
  rw [uaMeet_eq hj, h, ← uaMeet_eq hj'] at hxj
  refine ⟨y * x⁻¹, (PA 0).mul_mem hy ((PA 0).inv_mem hx), ?_⟩
  rw [Equiv.Perm.coe_mul, Set.image_comp, image_wPlane_inv hxj, hyj]

theorem exists_PA_image (hi : i < 891) {j j' : ℕ} (hj : j < 891) (hj' : j' < 891)
    (h : (wPlane i ∩ wPlane j).ncard = (wPlane i ∩ wPlane j').ncard) :
    ∃ g ∈ PA i, ⇑g '' wPlane j = wPlane j' := by
  obtain ⟨x, hx, hxW⟩ := exists_image_wPlane_zero hi
  obtain ⟨k, hk, hkj⟩ := exists_image_wPlane (T46.inv_mem hx) hj
  obtain ⟨k', hk', hkj'⟩ := exists_image_wPlane (T46.inv_mem hx) hj'
  have hinv := image_wPlane_inv hxW
  have hmeet : (wPlane 0 ∩ wPlane k).ncard = (wPlane 0 ∩ wPlane k').ncard := by
    rw [← hinv, ← hkj, ← hkj', ← Set.image_inter x⁻¹.injective,
      ← Set.image_inter x⁻¹.injective, Set.ncard_image_of_injective _ x⁻¹.injective,
      Set.ncard_image_of_injective _ x⁻¹.injective, h]
  obtain ⟨g, hg, hgk⟩ := exists_PA_image_zero hk hk' hmeet
  refine ⟨x * g * x⁻¹, conj_mem_PA hx hxW hg, ?_⟩
  rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hkj, hgk,
    ← image_wPlane_inv hkj', inv_inv]

end Dist

end CFSG.LargeExtraspecial.SMod20
