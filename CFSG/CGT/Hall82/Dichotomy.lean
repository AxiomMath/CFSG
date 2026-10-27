module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.CGT.Hall82

theorem closure_pair_eq_zpowers_of_mem_zpowers {G : Type*} [Group G] {a b : G}
    (hb : b ∈ Subgroup.zpowers a) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxa | hxb
    · rw [hxa]; exact Subgroup.mem_zpowers a
    · rw [hxb]; exact hb
  · rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (Set.mem_insert a {b}))

theorem card_zpowers_le_four_of_pow_four_eq_one {G : Type*} [Group G] {a : G}
    (ha : a ^ 4 = 1) : Nat.card (Subgroup.zpowers a) ≤ 4 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr ha)

theorem card_closure_pair_le_two_mul_card_zpowers {G : Type*} [Group G]
    {a b : G} (hb : b * b = 1) (hconj : b * a * b⁻¹ = a⁻¹) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 2 * Nat.card (Subgroup.zpowers a) := by
  classical
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hmap : (Subgroup.zpowers a).map (MulAut.conj b).toMonoidHom = Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (b * a * b⁻¹) = Subgroup.zpowers a
    rw [hconj, Subgroup.zpowers_inv]
  have hmemP : ∀ p ∈ Subgroup.zpowers a, b * p * b⁻¹ ∈ Subgroup.zpowers a := by
    intro p hp
    have h := Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hp
    rw [hmap] at h
    simpa using h
  have hcover : ∀ x ∈ Subgroup.closure ({a, b} : Set G),
      x ∈ (Subgroup.zpowers a : Set G) ∨
        ∃ p ∈ Subgroup.zpowers a, x = p * b := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ (Subgroup.zpowers a : Set G) ∨
      ∃ p ∈ Subgroup.zpowers a, x = p * b) ?_ ?_ ?_ ?_ hx
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hza | hzb
      · rw [hza]; exact Or.inl (Subgroup.mem_zpowers a)
      · rw [hzb]; exact Or.inr ⟨1, Subgroup.one_mem _, by rw [one_mul]⟩
    · exact Or.inl (Subgroup.one_mem _)
    · intro x y hx hy hx' hy'
      rcases hx' with hxP | ⟨p, hpP, rfl⟩
      · rcases hy' with hyP | ⟨q, hqP, rfl⟩
        · exact Or.inl (Subgroup.mul_mem _ hxP hyP)
        · exact Or.inr ⟨x * q, Subgroup.mul_mem _ hxP hqP, by rw [mul_assoc]⟩
      · rcases hy' with hyP | ⟨q, hqP, rfl⟩
        · refine Or.inr ⟨p * (b * y * b⁻¹), Subgroup.mul_mem _ hpP (hmemP y hyP), ?_⟩
          calc p * b * y = p * (b * y) := by group
            _ = p * (b * y * b⁻¹ * b) := by
                rw [mul_assoc (b * y) b⁻¹ b, inv_mul_cancel, mul_one]
            _ = p * (b * y * b⁻¹) * b := by group
        · have hmem := Subgroup.mul_mem _ hpP (hmemP q hqP)
          refine Or.inl ?_
          have heq : p * b * (q * b) = p * (b * q * b⁻¹) := by
            calc p * b * (q * b) = p * (b * q * b⁻¹) * (b * b) := by group
              _ = p * (b * q * b⁻¹) := by rw [hb, mul_one]
          rw [heq]
          exact hmem
    · intro x hx hx'
      rcases hx' with hxP | ⟨p, hpP, rfl⟩
      · exact Or.inl (Subgroup.inv_mem _ hxP)
      · refine Or.inr ⟨b * p⁻¹ * b⁻¹, hmemP p⁻¹ (Subgroup.inv_mem _ hpP), ?_⟩
        calc (p * b)⁻¹ = b⁻¹ * p⁻¹ := mul_inv_rev p b
          _ = b * p⁻¹ := by rw [hb']
          _ = b * p⁻¹ * b⁻¹ * b := by
              rw [mul_assoc (b * p⁻¹) b⁻¹ b, inv_mul_cancel, mul_one]
          _ = (b * p⁻¹ * b⁻¹) * b := by rw [mul_assoc]
  set P : Subgroup G := Subgroup.zpowers a with hP
  set K : Subgroup G := Subgroup.closure ({a, b} : Set G) with hK
  let S : Set G := (P : Set G) ∪ (fun p : G => p * b) '' (P : Set G)
  have hsub : (K : Set G) ⊆ S := by
    intro x hx
    rcases hcover x hx with hxP | ⟨p, hp, rfl⟩
    · exact Or.inl hxP
    · exact Or.inr ⟨p, hp, rfl⟩
  have himage : Nat.card ((fun p : G => p * b) '' (P : Set G)) = Nat.card P := by
    rw [Nat.card_image_of_injective (f := fun p : G => p * b) (fun x y h => mul_right_cancel h)]
    rfl
  by_cases hPfin : Finite P
  · have hPset : (P : Set G).Finite := Set.finite_coe_iff.mpr hPfin
    have hSfin : S.Finite := hPset.union (hPset.image _)
    have hle : Nat.card K ≤ Nat.card S := Set.ncard_le_ncard hsub hSfin
    have hunion : Nat.card S ≤
        Nat.card (P : Set G) + Nat.card ((fun p : G => p * b) '' (P : Set G)) :=
      Set.card_union_le (P : Set G) ((fun p : G => p * b) '' (P : Set G))
    calc Nat.card K
        ≤ Nat.card S := hle
      _ ≤ Nat.card (P : Set G) + Nat.card ((fun p : G => p * b) '' (P : Set G)) := hunion
      _ = Nat.card P + Nat.card P := by rw [himage]; rfl
      _ = 2 * Nat.card P := by ring
  · have hPinf : Infinite P := not_finite_iff_infinite.mp hPfin
    have hPK : P ≤ K := by
      rw [hP, hK, Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (Set.mem_insert a {b}))
    have hKinf : Infinite K :=
      Infinite.of_injective (fun p : P => (⟨p.1, hPK p.2⟩ : K)) (by
        intro x y h
        exact Subtype.ext (congrArg (fun z : K => (z : G)) h))
    haveI := hPinf
    haveI := hKinf
    simp [Nat.card_eq_zero_of_infinite]

theorem card_closure_pair_le_eight {G : Type*} [Group G] {a b : G}
    (ha : a ^ 4 = 1) (hb : b * b = 1) (hconj : b * a * b⁻¹ = a⁻¹) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 8 := by
  have h1 := card_closure_pair_le_two_mul_card_zpowers hb hconj
  have h2 := card_zpowers_le_four_of_pow_four_eq_one ha
  omega

theorem exists_compl_or_forall_mem {H X : Type} [Group H] [Group X] [Finite H]
    (π : H →* X) (hπ : Function.Surjective π) {W : Subgroup H} (hW : π.ker = W)
    (hW2 : Nat.card W = 2) (hWZ : W ≤ Subgroup.center H)
    {y t : X} (ht : t * t = 1) (hy : y ^ 4 = 1) (hty : (t * y) * (t * y) = 1)
    (hcl : Nat.card (Subgroup.closure ({y, t} : Set X)) = 8)
    (hodd : Odd (Nat.card X / 8)) (h8 : 8 ∣ Nat.card X)
    (hconj : ∀ x : X, x * x = 1 → x ≠ 1 → ∃ a : X, a * t * a⁻¹ = x) :
    (∃ K : Subgroup H, W ⊓ K = ⊥ ∧ W ⊔ K = ⊤) ∨ ∀ h : H, h * h = 1 → h ∈ W := by
  classical
  haveI : Finite X := Finite.of_surjective π hπ
  have hconj_yt : t * y * t⁻¹ = y⁻¹ := by
    have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have h1 : t * y * t = y⁻¹ := by
      calc t * y * t = (t * y) * (t * y) * y⁻¹ := by group
        _ = y⁻¹ := by rw [hty, one_mul]
    rw [ht_inv]
    exact h1
  have ht_ne : t ≠ 1 := by
    intro ht1
    have hEq : Subgroup.closure ({y, t} : Set X) = Subgroup.zpowers y := by
      rw [ht1]
      exact closure_pair_eq_zpowers_of_mem_zpowers (Subgroup.one_mem _)
    rw [hEq] at hcl
    have hle := card_zpowers_le_four_of_pow_four_eq_one hy
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
  have hy2_ne : y ^ 2 ≠ 1 := by
    intro hy2
    have hle := card_closure_pair_le_two_mul_card_zpowers (a := y) (b := t) ht hconj_yt
    rw [hcl] at hle
    have hle2 : Nat.card (Subgroup.zpowers y) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hy2)
    omega
  obtain ⟨w0, hw0ne, hw0uniq⟩ := (Nat.card_eq_two_iff' (1 : W)).1 hW2
  let w : H := (w0 : H)
  have hwW : w ∈ W := w0.2
  have hw1 : w ≠ 1 := fun h => hw0ne (Subtype.ext h)
  have hwuniq : ∀ z ∈ W, z ≠ 1 → z = w := by
    intro z hzW hz1
    have h := hw0uniq ⟨z, hzW⟩ (by simpa using hz1)
    exact congrArg Subtype.val h
  have hw2 : w * w = 1 := by
    haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW2]; norm_num)
    have h := pow_card_eq_one' (x := w0)
    rw [hW2] at h
    have h' := congrArg Subtype.val h
    simpa [pow_two, w] using h'
  have hwcenter : ∀ z : H, w * z = z * w := by
    intro z
    exact (Subgroup.mem_center_iff.mp (hWZ hwW) z).symm
  by_cases hex : ∃ s : H, s * s = 1 ∧ s ∉ W
  · left
    obtain ⟨s, hs2, hsW⟩ := hex
    have hsX : π s * π s = 1 := by rw [← map_mul, hs2, map_one]
    have hsne : π s ≠ 1 := by
      intro h
      apply hsW
      rw [← hW, MonoidHom.mem_ker]
      exact h
    obtain ⟨c, hc⟩ := hconj (π s) hsX hsne
    obtain ⟨c', hc'⟩ := hπ c⁻¹
    have hs1_sq : (c' * s * c'⁻¹) * (c' * s * c'⁻¹) = 1 := by
      calc (c' * s * c'⁻¹) * (c' * s * c'⁻¹) = c' * (s * s) * c'⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have hpi_s1 : π (c' * s * c'⁻¹) = t := by
      calc π (c' * s * c'⁻¹) = π c' * π s * (π c')⁻¹ := by
              rw [map_mul, map_mul, map_inv]
        _ = c⁻¹ * π s * (c⁻¹)⁻¹ := by rw [hc']
        _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hc, inv_inv]
        _ = t := by group
    have hinv_pre : ∀ x : X, x * x = 1 → ∃ s' : H, s' * s' = 1 ∧ π s' = x := by
      intro x hx
      by_cases hx1 : x = 1
      · exact ⟨1, by simp, by simp [hx1]⟩
      · obtain ⟨a, ha⟩ := hconj x hx hx1
        obtain ⟨a', ha'⟩ := hπ a
        refine ⟨a' * (c' * s * c'⁻¹) * a'⁻¹, ?_, ?_⟩
        · calc (a' * (c' * s * c'⁻¹) * a'⁻¹) * (a' * (c' * s * c'⁻¹) * a'⁻¹)
              = a' * ((c' * s * c'⁻¹) * (c' * s * c'⁻¹)) * a'⁻¹ := by group
            _ = 1 := by rw [hs1_sq]; group
        · calc π (a' * (c' * s * c'⁻¹) * a'⁻¹)
              = π a' * π (c' * s * c'⁻¹) * (π a')⁻¹ := by rw [map_mul, map_mul, map_inv]
            _ = a * t * a⁻¹ := by rw [ha', hpi_s1]
            _ = x := ha
    obtain ⟨t', ht'2, ht'pi⟩ := hinv_pre t ht
    obtain ⟨su, hsu2, hsupi⟩ := hinv_pre (t * y) hty
    let y' : H := t' * su
    have hpi_y' : π y' = y := by
      calc π y' = π t' * π su := map_mul π t' su
        _ = t * (t * y) := by rw [ht'pi, hsupi]
        _ = y := by rw [← mul_assoc, ht, one_mul]
    have hy'4W : y' ^ 4 ∈ W := by
      rw [← hW, MonoidHom.mem_ker, map_pow, hpi_y']
      exact hy
    have hy'4 : y' ^ 4 = 1 := by
      by_contra hne
      have hy'4eq : y' ^ 4 = w := hwuniq _ hy'4W hne
      have hpi_y'2 : π (y' ^ 2) = y ^ 2 := by rw [map_pow, hpi_y']
      have hsq1 : (y' ^ 2) * (y' ^ 2) = w := by
        calc (y' ^ 2) * (y' ^ 2) = y' ^ 4 := by group
          _ = w := hy'4eq
      have hcomm : w * y' ^ 2 = y' ^ 2 * w := hwcenter (y' ^ 2)
      have hsq2 : (y' ^ 2 * w) * (y' ^ 2 * w) = w := by
        calc (y' ^ 2 * w) * (y' ^ 2 * w) = y' ^ 2 * (w * y' ^ 2) * w := by group
          _ = y' ^ 2 * (y' ^ 2 * w) * w := by rw [hcomm]
          _ = (y' ^ 2 * y' ^ 2) * (w * w) := by group
          _ = w := by rw [hsq1, hw2, mul_one]
      have hfib : ∀ h : H, π h = y ^ 2 → h = y' ^ 2 ∨ h = y' ^ 2 * w := by
        intro h hh
        have hzW : (y' ^ 2)⁻¹ * h ∈ W := by
          rw [← hW, MonoidHom.mem_ker, map_mul, map_inv, hpi_y'2, hh]
          group
        by_cases hz1 : (y' ^ 2)⁻¹ * h = 1
        · left
          calc h = y' ^ 2 * ((y' ^ 2)⁻¹ * h) := by group
            _ = y' ^ 2 := by rw [hz1, mul_one]
        · right
          have hzw : (y' ^ 2)⁻¹ * h = w := hwuniq _ hzW hz1
          calc h = y' ^ 2 * ((y' ^ 2)⁻¹ * h) := by group
            _ = y' ^ 2 * w := by rw [hzw]
      have hy2_sq : y ^ 2 * y ^ 2 = 1 := by
        calc y ^ 2 * y ^ 2 = y ^ 4 := by group
          _ = 1 := hy
      obtain ⟨r, hr2, hrpi⟩ := hinv_pre (y ^ 2) hy2_sq
      rcases hfib r hrpi with hr | hr
      · rw [hr] at hr2
        apply hne
        calc y' ^ 4 = (y' ^ 2) * (y' ^ 2) := by group
          _ = 1 := hr2
      · rw [hr] at hr2
        rw [hsq2] at hr2
        exact hw1 hr2
    have ht'_inv : (t')⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
    have hsu_inv : su⁻¹ = su := inv_eq_of_mul_eq_one_right hsu2
    have hconj_y't' : t' * y' * t'⁻¹ = y'⁻¹ := by
      change t' * (t' * su) * t'⁻¹ = (t' * su)⁻¹
      calc t' * (t' * su) * t'⁻¹ = (t' * t') * (su * t'⁻¹) := by group
        _ = su * t'⁻¹ := by rw [ht'2, one_mul]
        _ = su * t' := by rw [ht'_inv]
        _ = (t' * su)⁻¹ := by rw [mul_inv_rev, hsu_inv, ht'_inv]
        _ = y'⁻¹ := rfl
    let K₀ : Subgroup H := Subgroup.closure ({y', t'} : Set H)
    have hK₀le8 : Nat.card K₀ ≤ 8 :=
      card_closure_pair_le_eight hy'4 ht'2 hconj_y't'
    have hK₀map : K₀.map π = Subgroup.closure ({y, t} : Set X) := by
      rw [MonoidHom.map_closure]
      have himg : π '' ({y', t'} : Set H) = ({y, t} : Set X) := by
        ext z
        simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rcases hx with hxy | hxt
          · left
            rw [hxy]
            exact hpi_y'
          · right
            rw [hxt]
            exact ht'pi
        · intro hz
          rcases hz with hzy | hzt
          · exact ⟨y', Or.inl rfl, by rw [hzy]; exact hpi_y'⟩
          · exact ⟨t', Or.inr rfl, by rw [hzt]; exact ht'pi⟩
      rw [himg]
    have hrange_card : Nat.card (K₀.map π) = 8 := by rw [hK₀map, hcl]
    let hf : K₀ →* X := π.comp K₀.subtype
    have hfrange : hf.range = K₀.map π := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hmul := Subgroup.card_ker_mul_card_range hf
    rw [hfrange, hrange_card] at hmul
    have hker_pos : 1 ≤ Nat.card hf.ker := Nat.card_pos
    have hker_le : Nat.card hf.ker ≤ 1 := by
      have hle8 : Nat.card hf.ker * 8 ≤ 1 * 8 := by
        rw [hmul]
        simpa using hK₀le8
      exact Nat.le_of_mul_le_mul_right hle8 (by norm_num)
    have hker1 : Nat.card hf.ker = 1 := le_antisymm hker_le hker_pos
    have hkerbot : hf.ker = ⊥ := Subgroup.card_eq_one.mp hker1
    have hinj : Function.Injective hf := (MonoidHom.ker_eq_bot_iff hf).mp hkerbot
    have hK₀card : Nat.card K₀ = 8 := by
      rw [← hmul, hker1, one_mul]
    have hK₀inf : K₀ ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨hxK, hxW⟩ := Subgroup.mem_inf.mp hx
      have hxpi : π x = 1 := by
        have hxker : x ∈ π.ker := by rwa [hW]
        exact MonoidHom.mem_ker.mp hxker
      have heq : (⟨x, hxK⟩ : K₀) = 1 := by
        apply hinj
        calc hf ⟨x, hxK⟩ = π x := rfl
          _ = 1 := hxpi
          _ = π 1 := by rw [map_one]
          _ = hf 1 := rfl
      simpa using congrArg Subtype.val heq
    haveI hWnormal : W.Normal := Subgroup.normal_of_le_center hWZ
    haveI hWcomm : IsMulCommutative W :=
      Subgroup.le_centralizer_iff_isMulCommutative.mp
        (hWZ.trans (Subgroup.center_le_centralizer _))
    have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 1) (by rw [hW2]; norm_num)
    have hWK : W ⊓ K₀ = ⊥ := by rw [inf_comm]; exact hK₀inf
    have hdisj : Disjoint W K₀ := by
      rw [disjoint_iff, inf_comm]
      exact hK₀inf
    have hnormal : K₀ ≤ Subgroup.normalizer (W : Set H) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hPcard : Nat.card (W ⊔ K₀ : Subgroup H) = 16 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W K₀ hnormal
        hdisj, hW2, hK₀card]
    have hPp : IsPGroup 2 (W ⊔ K₀ : Subgroup H) :=
      IsPGroup.of_card (n := 4) (by rw [hPcard]; norm_num)
    have hcardH : Nat.card H = 2 * Nat.card X := by
      have h := Subgroup.card_ker_mul_card_of_surjective (f := π) hπ
      rw [hW, hW2] at h
      exact h.symm
    have hcardX : Nat.card X = 8 * (Nat.card X / 8) :=
      (Nat.mul_div_cancel' h8).symm
    have hcardH16 : Nat.card H = 16 * (Nat.card X / 8) := by
      calc Nat.card H = 2 * Nat.card X := hcardH
        _ = 2 * (8 * (Nat.card X / 8)) := by conv_lhs => rw [hcardX]
        _ = 16 * (Nat.card X / 8) := by ring
    have hPindex : (W ⊔ K₀ : Subgroup H).index = Nat.card X / 8 := by
      have h := Subgroup.card_mul_index (W ⊔ K₀ : Subgroup H)
      rw [hPcard, hcardH16] at h
      exact Nat.mul_left_cancel (by norm_num : 0 < 16) h
    have hPindex_odd : Odd (W ⊔ K₀ : Subgroup H).index := by
      rw [hPindex]
      exact hodd
    have hPnotdvd : ¬ 2 ∣ (W ⊔ K₀ : Subgroup H).index := hPindex_odd.not_two_dvd_nat
    have hgas := CFSG.Quasithin.gaschutz (G := H) (p := 2) (V := W) hWp
      (hPp.toSylow hPnotdvd)
    refine hgas.mpr ⟨K₀, ?_, hWK, (IsPGroup.toSylow_coe hPp hPnotdvd).symm⟩
    rw [IsPGroup.toSylow_coe hPp hPnotdvd]
    exact le_sup_right
  · right
    intro h hh
    by_contra hnot
    exact hex ⟨h, hh, hnot⟩

end CFSG.CGT.Hall82
