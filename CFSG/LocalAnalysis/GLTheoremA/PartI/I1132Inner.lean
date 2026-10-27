module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Tri

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA.I113

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_noncentral {M : Subgroup Q}
    (hSyl : ∀ R : Sylow 3 ↥M, Nat.card (R : Subgroup ↥M) = 27 ∧
      (∃ r ∈ (R : Subgroup ↥M), ∃ s ∈ (R : Subgroup ↥M), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup ↥M), r ^ 3 = 1) :
    ∃ y ∈ M, orderOf y = 3 ∧ ∃ m ∈ M, y * m ≠ m * y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥M))
  obtain ⟨-, ⟨r, hr, s, -, hrs⟩, hexp⟩ := hSyl R
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hrs (by rw [one_mul, mul_one])
  have hro : orderOf r = 3 := orderOf_eq_prime (hexp r hr) hr1
  refine ⟨(r : Q), r.2, by rw [Subgroup.orderOf_coe]; exact hro, (s : Q), s.2, fun h => hrs ?_⟩
  exact Subtype.ext (by simpa using h)

theorem exists_w {M : Subgroup Q}
    (hSyl : ∀ R : Sylow 3 ↥M, Nat.card (R : Subgroup ↥M) = 27 ∧
      (∃ r ∈ (R : Subgroup ↥M), ∃ s ∈ (R : Subgroup ↥M), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup ↥M), r ^ 3 = 1) {y : Q} (hy : y ∈ M) (hyo : orderOf y = 3) :
    ∃ w ∈ M, w ^ 3 = 1 ∧ y * w = w * y ∧ w ∉ Subgroup.zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set y' : ↥M := ⟨y, hy⟩ with hy'
  have hyo' : orderOf y' = 3 := by rw [hy', Subgroup.orderOf_mk]; exact hyo
  have hZp : IsPGroup 3 (Subgroup.zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo', pow_one])
  obtain ⟨R, hR⟩ := hZp.exists_le_sylow
  obtain ⟨hR27, -, hRexp⟩ := hSyl R
  have key : ∃ w' ∈ (R : Subgroup ↥M), y' * w' = w' * y' ∧ w' ∉ Subgroup.zpowers y' := by
    haveI : Nontrivial ↥(R : Subgroup ↥M) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hR27]; norm_num
    haveI := R.isPGroup'.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥(R : Subgroup ↥M))
    set z₀ : ↥M := ((z : ↥(R : Subgroup ↥M)) : ↥M) with hz₀
    have hz₀R : z₀ ∈ (R : Subgroup ↥M) := (z : ↥(R : Subgroup ↥M)).2
    have hz₀c : ∀ x ∈ (R : Subgroup ↥M), x * z₀ = z₀ * x := by
      intro x hx
      have := Subgroup.mem_center_iff.1 z.2 ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hz₀1 : z₀ ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    by_cases hzy : z₀ ∈ Subgroup.zpowers y'
    · have hzo : orderOf z₀ = 3 := orderOf_eq_prime (hRexp z₀ hz₀R) hz₀1
      have heq : Subgroup.zpowers z₀ = Subgroup.zpowers y' := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact Subgroup.zpowers_le.2 hzy
        · rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hyo']
      have hyz : y' ∈ Subgroup.zpowers z₀ := heq ▸ Subgroup.mem_zpowers y'
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyz
      have hyc : ∀ x ∈ (R : Subgroup ↥M), y' * x = x * y' := by
        intro x hx
        rw [← hk]
        exact ((Commute.zpow_right (hz₀c x hx) k).eq).symm
      have hnle : ¬ (R : Subgroup ↥M) ≤ Subgroup.zpowers y' := by
        intro hle
        have := Subgroup.card_le_of_le hle
        rw [hR27, Nat.card_zpowers, hyo'] at this
        norm_num at this
      obtain ⟨w', hw'R, hw'⟩ := SetLike.not_le_iff_exists.1 hnle
      exact ⟨w', hw'R, hyc w' hw'R, hw'⟩
    · exact ⟨z₀, hz₀R, hz₀c y' (hR (Subgroup.mem_zpowers y')), hzy⟩
  obtain ⟨w', hw'R, hcomm, hnot⟩ := key
  refine ⟨(w' : Q), w'.2, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val (hRexp w' hw'R)
    simpa using this
  · have := congrArg Subtype.val hcomm
    simpa [hy'] using this
  · intro hmem
    apply hnot
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [hy'] using hk)⟩

theorem exists_inner {B M : Subgroup Q} {c : Q} (Tr : Triple3 B M c)
    (hH9 : ∀ E : Subgroup (MulAut ↥M), IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hSyl : ∀ R : Sylow 3 ↥M, Nat.card (R : Subgroup ↥M) = 27 ∧
      (∃ r ∈ (R : Subgroup ↥M), ∃ s ∈ (R : Subgroup ↥M), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup ↥M), r ^ 3 = 1)
    (hH : 3 < Nat.card (t113H B M)) :
    ∃ y ∈ M, orderOf y = 3 ∧ (∃ m ∈ M, y * m ≠ m * y) ∧
      ∃ a ∈ t113A B M, ∀ l ∈ M, a * l * a⁻¹ = y * l * y⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := t113H B M with hHdef
  have hHp : IsPGroup 3 H := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (Tr.H_elem.2 g g.2)⟩
  obtain ⟨S, hS⟩ := hHp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 ↥M)
    (not_dvd_card_sylow 3 ↥M)
  have hSinv : ∀ φ ∈ H, ∀ s ∈ (S : Subgroup ↥M), φ s ∈ (S : Subgroup ↥M) := by
    intro φ hφ s hs
    have h1 : (⟨φ, hφ⟩ : H) • S = S := hS ⟨φ, hφ⟩
    have h2 : (⟨φ, hφ⟩ : H) • s ∈ (((⟨φ, hφ⟩ : H) • S : Sylow 3 ↥M) : Subgroup ↥M) :=
      Subgroup.smul_mem_pointwise_smul s (⟨φ, hφ⟩ : H) (S : Subgroup ↥M) hs
    rw [h1] at h2
    exact h2
  obtain ⟨-, ⟨r, hr, t, -, hrt⟩, hSexp⟩ := hSyl S
  set Sh : Subgroup (MulAut ↥M) := (S : Subgroup ↥M).map (MulAut.conj : ↥M →* MulAut ↥M)
    with hShdef
  have hShp : IsPGroup 3 Sh := S.isPGroup'.map _
  have hconj : ∀ (φ : MulAut ↥M) (s : ↥M), φ * MulAut.conj s * φ⁻¹ = MulAut.conj (φ s) := by
    intro φ s
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  have hShn : ∀ φ ∈ H, ∀ n ∈ Sh, φ * n * φ⁻¹ ∈ Sh := by
    intro φ hφ n hn
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hn
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ (hSinv φ hφ s hs)
  have hle : H ≤ Subgroup.normalizer (Sh : Set (MulAut ↥M)) := by
    intro φ hφ
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hShn φ hφ n, fun h => ?_⟩
    have := hShn φ⁻¹ (H.inv_mem hφ) _ h
    simpa [mul_assoc] using this
  have hPp : IsPGroup 3 ↥(H ⊔ Sh) := IsPGroup.to_sup_of_normal_right' hHp hShp hle
  have hShP : Sh ≤ H ⊔ Sh := le_sup_right
  have hHP : H ≤ H ⊔ Sh := le_sup_left
  haveI : (Sh.subgroupOf (H ⊔ Sh)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hShP).2 (sup_le hle Subgroup.le_normalizer)
  haveI : Group.IsNilpotent ↥(H ⊔ Sh) := hPp.isNilpotent
  have hconj_ne : MulAut.conj r ≠ 1 := by
    intro h
    apply hrt
    have := congrArg (fun f : MulAut ↥M => f t) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc r * t = r * t * r⁻¹ * r := by group
      _ = t * r := by rw [this]
  have hne : Sh.subgroupOf (H ⊔ Sh) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨MulAut.conj r, hShP (Subgroup.mem_map_of_mem _ hr)⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem _ hr
    · intro h
      exact hconj_ne
        (congrArg (fun x : ↥(Sh.subgroupOf (H ⊔ Sh)) => ((x : ↥(H ⊔ Sh)) : MulAut ↥M)) h)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hcen
  obtain ⟨⟨x, hx⟩, hx1⟩ := hcen
  obtain ⟨hxS, hxZ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxS)
  have hzc : ∀ φ ∈ H, φ * (x : MulAut ↥M) = (x : MulAut ↥M) * φ := by
    intro φ hφ
    have := Subgroup.mem_center_iff.1 hxZ ⟨φ, hHP hφ⟩
    exact congrArg Subtype.val this
  have hx1' : (x : MulAut ↥M) ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
  have hs3 : s ^ 3 = 1 := hSexp s hs
  have hx3 : (x : MulAut ↥M) ^ 3 = 1 := by rw [← hsx, ← map_pow, hs3, map_one]
  have hxo : orderOf (x : MulAut ↥M) = 3 := orderOf_eq_prime hx3 hx1'
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hx1' (by rw [← hsx, map_one])
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hm : ∃ m : ↥M, s * m ≠ m * s := by
    by_contra! hcon
    apply hx1'
    rw [← hsx]
    refine MulEquiv.ext fun m => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, hcon m, mul_inv_cancel_right]
  have hxH : (x : MulAut ↥M) ∈ H := by
    by_contra hxH
    have hzp := t113_zpowers_elem hxo
    have hi : H ⊓ Subgroup.zpowers (x : MulAut ↥M) = ⊥ := by
      have hd := Subgroup.card_dvd_of_le
        (inf_le_right : H ⊓ Subgroup.zpowers (x : MulAut ↥M) ≤ _)
      rw [hzp.2] at hd
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq := Subgroup.eq_of_le_of_card_ge
          (inf_le_right : H ⊓ Subgroup.zpowers (x : MulAut ↥M) ≤ _) (by rw [h3, hzp.2])
        have hmem : (x : MulAut ↥M) ∈ H ⊓ Subgroup.zpowers (x : MulAut ↥M) := by
          rw [heq]; exact Subgroup.mem_zpowers _
        exact hxH (Subgroup.mem_inf.1 hmem).1
    have hcomm : ∀ p ∈ H, ∀ q ∈ Subgroup.zpowers (x : MulAut ↥M), p * q = q * p := by
      intro p hp q hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      exact (Commute.zpow_right (hzc p hp) k).eq
    have hHe : IsElemAbelian 3 H := Tr.H_elem
    have hE := t113_sup_elemAbelian hHe hzp.1 hcomm hi
    have h9 := hH9 _ hE.1
    rw [hE.2, hzp.2] at h9
    omega
  have hxH' : (x : MulAut ↥M) ∈ (t113Rho B M).range := hxH
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hxH'
  obtain ⟨m, hm⟩ := hm
  refine ⟨(s : Q), s.2, by rw [Subgroup.orderOf_coe]; exact hso,
    ⟨(m : Q), m.2, fun h => hm (Subtype.ext (by simpa using h))⟩, (a : Q), a.2, ?_⟩
  intro l hl
  have h1 : ((t113Rho B M a ⟨l, hl⟩ : ↥M) : Q) = (a : Q) * l * (a : Q)⁻¹ := Tr.rho_apply a ⟨l, hl⟩
  rw [ha, ← hsx, MulAut.conj_apply] at h1
  rw [← h1]
  simp

end CFSG.LocalAnalysis.GLTheoremA.I1132
