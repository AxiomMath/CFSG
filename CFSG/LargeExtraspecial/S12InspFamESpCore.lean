module

public import CFSG.LargeExtraspecial.S12InspFamESpLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12InspSp

open CFSG.Open LinearMap.BilinForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}
  (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (h4 : 4 < Fintype.card ι)
  {T : SpG b} {v : ι → ZMod 2} (hv : v ≠ 0) (hT : ∀ x, act T x = x + b x v • v)

include halt hnd h4 hv hT in
theorem tr_mul_tr_mem {N : Subgroup (SpG b)}
    (hN : ∀ c ∈ Subgroup.centralizer {T}, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hP : ∀ c ∈ Subgroup.centralizer {T}, ∀ d ∈ Subgroup.centralizer {T}, c * c = 1 →
      d * d = 1 → c * d = d * c → c ∉ N → d ∉ N → c * d ∈ N)
    {a z : ι → ZMod 2} (ha : b a v = 0) (ha0 : a ≠ 0) (hav : a ≠ v) (hz : b z v = 0)
    (hz0 : z ≠ 0) (hzv : z ≠ v) : tr halt a * tr halt z ∈ N := by
  have hC : ∀ {w}, b w v = 0 → tr halt w ∈ Subgroup.centralizer {T} := fun hw =>
    tr_mem_centralizer halt hT hw
  have step1 : ∀ {a z : ι → ZMod 2}, b a v = 0 → b z v = 0 → b a z = 1 → tr halt a ∈ N →
      tr halt z ∈ N := by
    intro a z ha hz haz hN'
    have hmem := hN _ (Subgroup.mul_mem _ (hC ha) (hC hz)) _ hN'
    rwa [conj_tr halt, act_tr_mul_tr_self halt haz] at hmem
  have step2 : ∀ {a z : ι → ZMod 2}, b a v = 0 → a ≠ 0 → a ≠ v → b z v = 0 → z ≠ 0 → z ≠ v →
      tr halt a ∈ N → tr halt z ∈ N := by
    intro a z ha ha0 hav hz hz0 hzv hN'
    obtain ⟨c, hcv, hac, hzc⟩ := exists_perp_b_eq_one_two halt hnd hv ha0 hav hz0 hzv
    have hcz : b c z = 1 := by rw [b_symm halt, hzc]
    exact step1 hcv hz hcz (step1 ha hcv hac hN')
  have hcomm : ∀ {a z : ι → ZMod 2}, b a v = 0 → b z v = 0 → b a z = 0 → tr halt a ∉ N →
      tr halt z ∉ N → tr halt a * tr halt z ∈ N := fun ha hz haz hna hnz =>
    hP _ (hC ha) _ (hC hz) (tr_mul_self halt _) (tr_mul_self halt _) (tr_comm halt haz) hna hnz
  by_cases hA : tr halt a ∈ N
  · exact Subgroup.mul_mem _ hA (step2 ha ha0 hav hz hz0 hzv hA)
  have hZ : tr halt z ∉ N := fun h => hA (step2 hz hz0 hzv ha ha0 hav h)
  rcases zmod_two_cases (b a z) with haz | haz
  · exact hcomm ha hz haz hA hZ
  · obtain ⟨y', hy'⟩ := exists_b_eq_one halt hnd hv
    obtain ⟨c, hc0, hcv, hca, hcz, hcy⟩ := exists_ne_zero_perp4 (b := b) h4 v a z y'
    have hcv' : c ≠ v := by
      rintro rfl
      rw [b_symm halt, hy'] at hcy
      exact one_ne_zero hcy
    have hC' : tr halt c ∉ N := fun h => hA (step2 hcv hc0 hcv' ha ha0 hav h)
    have h1 := hcomm ha hcv (by rw [b_symm halt, hca]) hA hC'
    have h2 := hcomm hcv hz hcz hC' hZ
    have h3 := Subgroup.mul_mem _ h1 h2
    rwa [show tr halt a * tr halt c * (tr halt c * tr halt z) = tr halt a * tr halt z by
      rw [mul_assoc, ← mul_assoc (tr halt c), tr_mul_self halt c, one_mul]] at h3

omit hv hT in
include halt hnd h4 in
theorem forall_of_invariant {y : ι → ZMod 2} (hyv : b y v = 1)
    {P : (ι → ZMod 2) → Prop} (hadd : ∀ x z, P x → P z → P (x + z))
    (hinv : ∀ a z w, b a v = 0 → b a y = 0 → a ≠ 0 → b z v = 0 → b z y = 0 → z ≠ 0 →
      b w v = 0 → b w y = 0 → P w → P (res b v y (tr halt a * tr halt z) w))
    {x : ι → ZMod 2} (hxv : b x v = 0) (hxy : b x y = 0) (hx0 : x ≠ 0) (hPx : P x) :
    ∀ w, b w v = 0 → b w y = 0 → P w := by
  have stepA : ∀ z, b z v = 0 → b z y = 0 → b x z = 1 → P z := by
    intro z hzv hzy hxz
    obtain ⟨a, ha0, hav, hay, hax, haz⟩ := exists_ne_zero_perp4 (b := b) h4 v y x z
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxz
      exact zero_ne_one hxz
    have hres : res b v y (tr halt a * tr halt z) x = x + z := by
      have hxa : b (x + z) a = 0 := by
        rw [add_left, b_symm halt x a, b_symm halt z a, hax, haz, add_zero]
      rw [res, act_mul, act_tr halt z x, hxz, one_smul, act_tr halt a (x + z), hxa, zero_smul,
        add_zero,
        pr_of_perp (by rw [add_left, hxv, hzv, add_zero]) (by rw [add_left, hxy, hzy, add_zero])]
    have h1 := hinv a z x hav hay ha0 hzv hzy hz0 hxv hxy hPx
    rw [hres] at h1
    have h2 := hadd _ _ h1 hPx
    rwa [add_add_self_left] at h2
  obtain ⟨y'', hy''⟩ := exists_b_eq_one halt hnd hx0
  have hz₀v : b (pr b v y y'') v = 0 := b_pr_v halt hyv y''
  have hz₀y : b (pr b v y y'') y = 0 := b_pr_y halt hyv y''
  have hxz₀ : b x (pr b v y y'') = 1 := by rw [b_pr_right hxv hxy, b_symm halt, hy'']
  have hPz₀ := stepA _ hz₀v hz₀y hxz₀
  intro w hwv hwy
  rcases zmod_two_cases (b x w) with h | h
  · have h1 := stepA (w + pr b v y y'') (by rw [add_left, hwv, hz₀v, add_zero])
      (by rw [add_left, hwy, hz₀y, add_zero]) (by rw [add_right, h, hxz₀, zero_add])
    have h2 := hadd _ _ h1 hPz₀
    rwa [add_assoc, add_self_vec, add_zero] at h2
  · exact stepA w hwv hwy h

include halt hnd h4 hv hT in
theorem le_rad {L : Subgroup (SpG b)} (hLC : L ≤ Subgroup.centralizer {T}) (hL2 : IsPGroup 2 L)
    (hpair : ∀ a z, b a v = 0 → a ≠ 0 → a ≠ v → b z v = 0 → z ≠ 0 → z ≠ v →
      tr halt a * tr halt z ∈ Subgroup.normalizer (L : Set (SpG b))) :
    L ≤ rad b v := by
  classical
  obtain ⟨y, hyv⟩ := exists_b_eq_one halt hnd hv
  have hLv : ∀ ℓ ∈ L, act ℓ v = v := fun ℓ hℓ =>
    act_eq_of_mem_centralizer halt hnd hv hT (hLC hℓ)
  have hne : ∀ {a}, b a y = 0 → a ≠ v := fun {a} hay h => by
    rw [h, b_symm halt, hyv] at hay
    exact one_ne_zero hay
  let W : Submodule (ZMod 2) (ι → ZMod 2) :=
    { carrier := {w | b w v = 0 ∧ b w y = 0}
      add_mem' := fun {x z} hx hz => ⟨by rw [add_left, hx.1, hz.1, add_zero],
        by rw [add_left, hx.2, hz.2, add_zero]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c x hx => ⟨by rw [smul_left, hx.1, mul_zero],
        by rw [smul_left, hx.2, mul_zero]⟩ }
  let A : MulAction L W :=
    { smul := fun ℓ w => ⟨res b v y ℓ w, b_res_v halt hyv _ _, b_res_y halt hyv _ _⟩
      one_smul := fun w => Subtype.ext (res_one w.2.1 w.2.2)
      mul_smul := fun ℓ ℓ' w => Subtype.ext (res_mul halt hyv (hLv _ ℓ.2) (hLv _ ℓ'.2) w.2.1) }
  obtain ⟨c₀, hc₀, hc₀v, hc₀y, -, -⟩ := exists_ne_zero_perp4 (b := b) h4 v y v y
  have hW2 : 2 ∣ Nat.card W := by
    have : Nontrivial W := ⟨⟨⟨c₀, hc₀v, hc₀y⟩, 0, fun h => hc₀ (congrArg Subtype.val h)⟩⟩
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (Module.finrank_pos (R := ZMod 2) (M := W)).ne'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hL2.card_modEq_card_fixedPoints W
  have h0fix : (0 : W) ∈ MulAction.fixedPoints L W := fun ℓ =>
    Subtype.ext (show res b v y ℓ 0 = 0 by rw [res, act_zero, pr_zero])
  obtain ⟨w₀, hw₀fix, hw₀0⟩ : ∃ w₀ ∈ MulAction.fixedPoints L W, w₀ ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : Nat.card (MulAction.fixedPoints L W) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr
        ⟨fun p q => Subtype.ext ((h p p.2).trans (h q q.2).symm)⟩
    have h2 : 0 < Nat.card (MulAction.fixedPoints L W) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, h0fix⟩⟩, inferInstance⟩
    have h3 : Nat.card W % 2 = 0 := Nat.mod_eq_zero_of_dvd hW2
    unfold Nat.ModEq at hmod
    omega
  have hfixall := forall_of_invariant halt hnd h4 hyv
    (P := fun w => ∀ ℓ ∈ L, res b v y ℓ w = w)
    (fun x z hx hz ℓ hℓ => by rw [res_add, hx ℓ hℓ, hz ℓ hℓ])
    (fun a z w hav hay ha0 hzv hzy hz0 hwv hwy hPw ℓ hℓ => by
      have hcv : act (tr halt a * tr halt z) v = v := act_tr_mul_tr_v halt hav hzv
      have hcN := hpair a z hav ha0 (hne hay) hzv hz0 (hne hzy)
      have hℓ' : (tr halt a * tr halt z)⁻¹ * ℓ * (tr halt a * tr halt z) ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcN) ℓ).1 hℓ
        simpa using this
      calc res b v y ℓ (res b v y (tr halt a * tr halt z) w) =
          res b v y (ℓ * (tr halt a * tr halt z)) w :=
            (res_mul halt hyv (hLv _ hℓ) hcv hwv).symm
        _ = res b v y ((tr halt a * tr halt z) *
            ((tr halt a * tr halt z)⁻¹ * ℓ * (tr halt a * tr halt z))) w := by
          congr 1
          group
        _ = res b v y (tr halt a * tr halt z)
            (res b v y ((tr halt a * tr halt z)⁻¹ * ℓ * (tr halt a * tr halt z)) w) :=
          res_mul halt hyv hcv (hLv _ hℓ') hwv
        _ = res b v y (tr halt a * tr halt z) w := by rw [hPw _ hℓ'])
    w₀.2.1 w₀.2.2 (fun h => hw₀0 (Subtype.ext h))
    (fun ℓ hℓ => congrArg Subtype.val (hw₀fix ⟨ℓ, hℓ⟩))
  intro ℓ hℓ
  exact mem_rad_of_res halt hyv (hLv ℓ hℓ) fun w hwv hwy => hfixall w hwv hwy ℓ hℓ

include halt hnd h4 hv hT in
theorem rad_le {L : Subgroup (SpG b)} (hLr : L ≤ rad b v) (hTL : T ∈ L)
    (hpair : ∀ a z, b a v = 0 → a ≠ 0 → a ≠ v → b z v = 0 → z ≠ 0 → z ≠ v →
      tr halt a * tr halt z ∈ Subgroup.normalizer (L : Set (SpG b)))
    (hbig : ∃ ℓ ∈ L, ℓ ≠ 1 ∧ ℓ ≠ T) : rad b v ≤ L := by
  obtain ⟨y, hyv⟩ := exists_b_eq_one halt hnd hv
  have hne : ∀ {a}, b a y = 0 → a ≠ v := fun {a} hay h => by
    rw [h, b_symm halt, hyv] at hay
    exact one_ne_zero hay
  obtain ⟨ℓ₀, hℓ₀, hℓ₀1, hℓ₀T⟩ := hbig
  have h0 : piv b v y ℓ₀ ≠ 0 := fun h =>
    (eq_one_or_eq_of_piv halt hyv hT (hLr hℓ₀) h).elim hℓ₀1 hℓ₀T
  have hall := forall_of_invariant halt hnd h4 hyv
    (P := fun w => ∃ ℓ ∈ L, piv b v y ℓ = w)
    (fun x z ⟨ℓ, hℓ, hx⟩ ⟨ℓ', hℓ', hz⟩ => ⟨ℓ * ℓ', L.mul_mem hℓ hℓ', by
      rw [piv_mul halt hyv (hLr hℓ) (hLr hℓ'), hx, hz]⟩)
    (fun a z w hav hay ha0 hzv hzy hz0 _ _ ⟨ℓ, hℓ, hw⟩ => by
      have hcv : act (tr halt a * tr halt z) v = v := act_tr_mul_tr_v halt hav hzv
      have hcN := hpair a z hav ha0 (hne hay) hzv hz0 (hne hzy)
      refine ⟨(tr halt a * tr halt z) * ℓ * (tr halt a * tr halt z)⁻¹,
        (Subgroup.mem_normalizer_iff.1 hcN ℓ).1 hℓ, ?_⟩
      rw [piv_conj halt hyv hcv (hLr hℓ), hw])
    (b_piv_v halt hyv ℓ₀) (b_piv_y halt hyv ℓ₀) h0 ⟨ℓ₀, hℓ₀, rfl⟩
  intro k hk
  obtain ⟨ℓ, hℓ, hkl⟩ := hall (piv b v y k) (b_piv_v halt hyv k) (b_piv_y halt hyv k)
  have hinv : piv b v y ℓ⁻¹ = piv b v y ℓ := by
    have := piv_mul halt hyv (Subgroup.inv_mem _ (hLr hℓ)) (hLr hℓ)
    rw [inv_mul_cancel, piv_one] at this
    exact eq_of_add_eq_zero_vec this.symm
  have hz : piv b v y (ℓ⁻¹ * k) = 0 := by
    rw [piv_mul halt hyv (Subgroup.inv_mem _ (hLr hℓ)) hk, hinv, hkl, add_self_vec]
  rcases eq_one_or_eq_of_piv halt hyv hT
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLr hℓ)) hk) hz with h | h
  · have hk' : k = ℓ := by rw [← mul_inv_cancel_left ℓ k, h, mul_one]
    rw [hk']
    exact hℓ
  · have hk' : k = ℓ * T := by rw [← h, mul_inv_cancel_left]
    rw [hk']
    exact L.mul_mem hℓ hTL

include halt hnd h4 hv hT in
theorem centralizer_le_normalizer_of {N L : Subgroup (SpG b)}
    (hN : ∀ c ∈ Subgroup.centralizer {T}, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hP : ∀ c ∈ Subgroup.centralizer {T}, ∀ d ∈ Subgroup.centralizer {T}, c * c = 1 →
      d * d = 1 → c * d = d * c → c ∉ N → d ∉ N → c * d ∈ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set (SpG b))) (hLC : L ≤ Subgroup.centralizer {T})
    (hL2 : IsPGroup 2 L) (hTL : T ∈ L) (hbig : ∃ ℓ ∈ L, ℓ ≠ 1 ∧ ℓ ≠ T) :
    Subgroup.centralizer {T} ≤ Subgroup.normalizer (L : Set (SpG b)) := by
  have hpair : ∀ a z, b a v = 0 → a ≠ 0 → a ≠ v → b z v = 0 → z ≠ 0 → z ≠ v →
      tr halt a * tr halt z ∈ Subgroup.normalizer (L : Set (SpG b)) :=
    fun a z ha ha0 hav hz hz0 hzv =>
      hNL (tr_mul_tr_mem halt hnd h4 hv hT hN hP ha ha0 hav hz hz0 hzv)
  have hLr := le_rad halt hnd h4 hv hT hLC hL2 hpair
  have hL : L = rad b v := le_antisymm hLr (rad_le halt hnd h4 hv hT hLr hTL hpair hbig)
  rw [hL]
  exact centralizer_le_normalizer_rad halt hnd hv hT

end CFSG.LargeExtraspecial.S12InspSp
