module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L225
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L225Core

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped MatrixGroups

namespace F3A75

theorem sl23_mem_of_normal {N : Subgroup SL23} (hN : N.Normal) {x : SL23} (hxN : x ∈ N)
    (hx1 : x ≠ 1) (hx2 : x ≠ -1) {q : SL23} (hq : q ^ 4 = 1) : q ∈ N := by
  rcases F3L221.sl23_cases x with h | h | h | h | h
  · exact absurd h hx1
  · exact absurd h hx2
  · rcases T1.sl23_sq_of_pow_four q (Or.inl hq) with hq2 | hq2
    · rcases eq_one_or_neg_one_of_mul_self_SL23 q (by rw [← sq]; exact hq2) with h1 | h1
      · rw [h1]
        exact one_mem N
      · rw [h1, ← h, sq]
        exact mul_mem hxN hxN
    · obtain ⟨g, hg⟩ := F3L225.sl23_conj_of_sq_eq_neg_one x q h hq2
      have h1 : q = g * x * g⁻¹ := by rw [hg, mul_inv_cancel_right]
      rw [h1]
      exact hN.conj_mem x hxN g
  · have h3 : (x ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, h]
      exact neg_one_sq
    have h1 : x ^ 2 ≠ 1 := by
      intro h2
      rcases eq_one_or_neg_one_of_mul_self_SL23 x (by rw [← sq]; exact h2) with h4 | h4
      · exact hx1 h4
      · exact hx2 h4
    rw [normal_eq_top_of_mem_sl23 (MulEquiv.refl SL23) hN (pow_mem hxN 2) h3 h1]
    exact mem_top q
  · rw [normal_eq_top_of_mem_sl23 (MulEquiv.refl SL23) hN hxN h hx1]
    exact mem_top q

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem e_mk_pow_four {M : Subgroup Q} (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3)) {s : Q}
    (hs : s ∈ M) {n : ℕ} (hsn : s ^ 2 ^ n = 1) : e (QuotientGroup.mk ⟨s, hs⟩) ^ 4 = 1 := by
  set y := e (QuotientGroup.mk ⟨s, hs⟩) with hy
  have h1 : y ^ 2 ^ n = 1 := by
    rw [hy, ← map_pow, ← QuotientGroup.mk_pow]
    rw [show (⟨s, hs⟩ : ↥M) ^ 2 ^ n = 1 from Subtype.ext (by simpa using hsn),
      QuotientGroup.mk_one, map_one]
  have h2 : orderOf y ∣ 8 := by
    have h3 : orderOf y ∣ 8 * 3 := by
      have h4 := orderOf_dvd_natCard y
      rw [card_SL23] at h4
      exact h4
    have hcop : Nat.Coprime (orderOf y) 3 :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
        (Nat.Coprime.pow_left n (by norm_num))
    exact hcop.dvd_of_dvd_mul_right h3
  exact F3L221.sl23_pow_four_of_pow_eight y (orderOf_dvd_iff_pow_eq_one.mp h2)

theorem e_mk_eq_neg_one {M : Subgroup Q} (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3)) {z : Q}
    (hzM : z ∈ M) (hz : orderOf z = 2) : e (QuotientGroup.mk ⟨z, hzM⟩) = -1 := by
  have hzz : (⟨z, hzM⟩ : ↥M) * ⟨z, hzM⟩ = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq, ← hz, pow_orderOf_eq_one])
  have h1 : e (QuotientGroup.mk ⟨z, hzM⟩) * e (QuotientGroup.mk ⟨z, hzM⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, hzz, QuotientGroup.mk_one, map_one]
  rcases eq_one_or_neg_one_of_mul_self_SL23 _ h1 with h | h
  · exfalso
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff] at h
    exact F3L221.not_mem_pPrimeCore_of_orderOf hzM hz h
  · exact h

omit [Finite Q] in
theorem map_pPrimeCore_le_normalizer {M H : Subgroup Q}
    (hH : ∀ k ∈ M, ∀ h ∈ H, k * h * k⁻¹ ∈ H) :
    (pPrimeCore 2 ↥M).map M.subtype ≤ normalizer (H : Set Q) := by
  intro o' ho'
  obtain ⟨o, -, rfl⟩ := ho'
  show (o : Q) ∈ normalizer (H : Set Q)
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact hH o o.2 y
  · intro hy
    have h3 := hH _ (inv_mem o.2) _ hy
    rwa [show (o : Q)⁻¹ * ((o : Q) * y * (o : Q)⁻¹) * (o : Q)⁻¹⁻¹ = y by group] at h3

theorem mem_of_not_central {M N : Subgroup Q} (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    (hNM : N ≤ M) (hNn : ∀ k ∈ M, ∀ n ∈ N, k * n * k⁻¹ ∈ N) {x : Q} (hxN : x ∈ N)
    (hx1 : e (QuotientGroup.mk ⟨x, hNM hxN⟩) ≠ 1) (hx2 : e (QuotientGroup.mk ⟨x, hNM hxN⟩) ≠ -1)
    {s : Q} (hs : s ∈ M) {n : ℕ} (hsn : s ^ 2 ^ n = 1) : s ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pPrimeCore 2 ↥M with hR
  have hNMn : (N.subgroupOf M).Normal := ⟨fun y hy g => by
    rw [mem_subgroupOf] at hy ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hNn g g.2 y hy⟩
  set Nb : Subgroup SL23 := ((N.subgroupOf M).map (QuotientGroup.mk' R)).map e.toMonoidHom
    with hNb
  have hNbn : Nb.Normal :=
    (hNMn.map _ (QuotientGroup.mk'_surjective R)).map _ e.surjective
  have hxb : e (QuotientGroup.mk ⟨x, hNM hxN⟩) ∈ Nb :=
    ⟨QuotientGroup.mk ⟨x, hNM hxN⟩, ⟨⟨x, hNM hxN⟩, hxN, rfl⟩, rfl⟩
  obtain ⟨_, ⟨n', hn', rfl⟩, hn'e⟩ := sl23_mem_of_normal hNbn hxb hx1 hx2 (e_mk_pow_four e hs hsn)
  have hn'e' : e (QuotientGroup.mk n') = e (QuotientGroup.mk ⟨s, hs⟩) := hn'e
  have h1 : n'⁻¹ * ⟨s, hs⟩ ∈ R := QuotientGroup.eq.mp (e.injective hn'e')
  have hmem : s ∈ N ⊔ R.map M.subtype := by
    have h2 : s = (n' : Q) * ((n'⁻¹ * ⟨s, hs⟩ : ↥M) : Q) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h2]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hn')) (mem_sup_right ⟨_, h1, rfl⟩)
  have hOodd : Odd (Nat.card ↥(R.map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact odd_card_pPrimeCore_two ↥M
  exact F3L221.mem_of_mem_sup_of_odd (map_pPrimeCore_le_normalizer hNn) hOodd hmem hsn

omit [Finite Q] in
theorem conj_mem_centralizer {L : Subgroup Q} {k : Q} (hk : k ∈ normalizer (L : Set Q)) {c : Q}
    (hc : c ∈ centralizer (L : Set Q)) : k * c * k⁻¹ ∈ centralizer (L : Set Q) := by
  rw [mem_centralizer_iff]
  intro m hm
  have hm' : k⁻¹ * m * k ∈ L := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hk) m).mp hm
    rwa [inv_inv] at h1
  have h2 : (k⁻¹ * m * k) * c = c * (k⁻¹ * m * k) := (mem_centralizer_iff.mp hc) _ hm'
  calc m * (k * c * k⁻¹) = k * ((k⁻¹ * m * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * m * k)) * k⁻¹ := by rw [h2]
    _ = k * c * k⁻¹ * m := by group

theorem mem_sup_centralizer_of_outQuat {L M : Subgroup Q}
    (hOut : ∀ (R : Subgroup (MulAut ↥L)) (φ : ↥R →* PSL(2, ZMod 3)), Function.Surjective φ →
      ∃ r : ↥R, (r : MulAut ↥L) ∈ (MulAut.conj : ↥L →* MulAut ↥L).range ∧ φ r ≠ 1)
    (hMN : M ≤ normalizer (L : Set Q)) (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    {s : Q} (hs : s ∈ M) {n : ℕ} (hsn : s ^ 2 ^ n = 1) : s ∈ L ⊔ centralizer (L : Set Q) := by
  by_contra hsN
  set Z := centralizer (L : Set Q) with hZ
  set N := M ⊓ (L ⊔ Z) with hN
  have hNn : ∀ k ∈ M, ∀ y ∈ N, k * y * k⁻¹ ∈ N := by
    intro k hk y hy
    obtain ⟨hyM, hyLZ⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hk hyM) (inv_mem hk), ?_⟩
    have hle : L ⊔ Z ≤ (L ⊔ Z).comap (MulAut.conj k).toMonoidHom :=
      sup_le (fun l hl => mem_sup_left ((mem_normalizer_iff.mp (hMN hk) l).mp hl))
        (fun c hc => mem_sup_right (conj_mem_centralizer (hMN hk) hc))
    exact hle hyLZ
  have hc : ∀ y (hy : y ∈ N), e (QuotientGroup.mk ⟨y, (mem_inf.mp hy).1⟩) = 1 ∨
      e (QuotientGroup.mk ⟨y, (mem_inf.mp hy).1⟩) = -1 := by
    intro y hy
    by_contra hne
    push Not at hne
    exact hsN (mem_inf.mp (mem_of_not_central e inf_le_left hNn hy hne.1 hne.2 hs hsn)).2
  let ρ : ↥M →* MulAut ↥L := L.normalizerMonoidHom.comp (inclusion hMN)
  let ψ : ↥M →* PSL(2, ZMod 3) :=
    ((QuotientGroup.mk' (center SL23)).comp e.toMonoidHom).comp
      (QuotientGroup.mk' (pPrimeCore 2 ↥M))
  have hψ : ∀ m : ↥M, (m : Q) ∈ L ⊔ Z → ψ m = 1 := by
    intro m hm
    have h3 := hc (m : Q) (mem_inf.mpr ⟨m.2, hm⟩)
    show QuotientGroup.mk (e (QuotientGroup.mk m)) = (1 : PSL(2, ZMod 3))
    rw [QuotientGroup.eq_one_iff, mem_center_SL23_iff]
    exact h3
  have hker : ρ.ker ≤ ψ.ker := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm ⊢
    refine hψ m (mem_sup_right ?_)
    rw [hZ, mem_centralizer_iff]
    intro l hl
    have h1 : (m : Q) * l * (m : Q)⁻¹ = l := by
      have h2 := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : Q)) hm
      exact h2
    calc l * m = ((m : Q) * l * (m : Q)⁻¹) * m := by rw [h1]
      _ = m * l := by group
  let φ : ↥ρ.range →* PSL(2, ZMod 3) :=
    (QuotientGroup.lift ρ.ker ψ hker).comp
      (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
  have hφ : ∀ m : ↥M, φ (ρ.rangeRestrict m) = ψ m := by
    intro m
    have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm (ρ.rangeRestrict m) =
        QuotientGroup.mk m := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift ρ.ker ψ hker
      ((QuotientGroup.quotientKerEquivRange ρ).symm (ρ.rangeRestrict m)) = ψ m
    rw [h1, QuotientGroup.lift_mk]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e.symm Y)
    refine ⟨ρ.rangeRestrict m, ?_⟩
    rw [hφ]
    show QuotientGroup.mk (e (QuotientGroup.mk m)) = (QuotientGroup.mk Y : PSL(2, ZMod 3))
    rw [hm, MulEquiv.apply_symm_apply]
  obtain ⟨r, ⟨l, hl⟩, hr⟩ := hOut ρ.range φ hφs
  obtain ⟨m, hm⟩ := r.2
  have hr' : r = ρ.rangeRestrict m := Subtype.ext hm.symm
  rw [hr', hφ] at hr
  apply hr
  apply hψ
  have hcZ : (l : Q)⁻¹ * m ∈ Z := by
    rw [hZ, mem_centralizer_iff]
    intro y hy
    have h2 : (m : Q) * y * (m : Q)⁻¹ = l * y * (l : Q)⁻¹ := by
      have h1 := congrArg (fun f : MulAut ↥L => ((f ⟨y, hy⟩ : ↥L) : Q)) (hl.trans hm.symm)
      exact h1.symm
    calc y * ((l : Q)⁻¹ * m) = (l : Q)⁻¹ * ((l : Q) * y * (l : Q)⁻¹) * m := by group
      _ = (l : Q)⁻¹ * ((m : Q) * y * (m : Q)⁻¹) * m := by rw [h2]
      _ = (l : Q)⁻¹ * m * y := by group
  have h3 : (m : Q) = l * ((l : Q)⁻¹ * m) := by group
  rw [h3]
  exact mul_mem (mem_sup_left l.2) (mem_sup_right hcZ)

theorem mem_or_centralizes {L M : Subgroup Q} {t z : Q} (htL : t ∈ L)
    (hM : IsSolvableTwoComponentIn M (centralizer {t})) (hMN : M ≤ normalizer (L : Set Q))
    (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3)) (hzM : z ∈ M) (hz : orderOf z = 2)
    (hzc : ∀ k ∈ M, k * z = z * k)
    (hinner : ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ L ⊔ centralizer (L : Set Q)) :
    (∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ L) ∨
      ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → ∀ l ∈ L, s * l = l * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set Q) with hC
  set Z := centralizer (L : Set Q) with hZ
  set A := L ⊓ C with hA
  set OM := (pPrimeCore 2 ↥M).map M.subtype with hOM
  set W := normalizer (L : Set Q) ⊓ C with hW
  have hMC : M ≤ C := hM.1
  have hZN : Z ≤ normalizer (L : Set Q) := centralizer_le_normalizer _
  have hZC : Z ≤ C := fun c hc =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hc) t htL).symm
  have hAn : ∀ k ∈ W, ∀ a ∈ A, k * a * k⁻¹ ∈ A := by
    intro k hk a ha
    obtain ⟨hkN, hkC⟩ := mem_inf.mp hk
    obtain ⟨haL, haC⟩ := mem_inf.mp ha
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hkN a).mp haL,
      mul_mem (mul_mem hkC haC) (inv_mem hkC)⟩
  have hOMn : ∀ k ∈ C, ∀ o ∈ OM, k * o * k⁻¹ ∈ OM := by
    intro k hk o ho
    rw [hOM, hM.2.2.1] at ho ⊢
    obtain ⟨o', ho', hoo⟩ := ho
    refine ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹,
      (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem o' ho' _, ?_⟩
    rw [← hoo]
    rfl
  have hMW : M ≤ W := le_inf hMN hMC
  have hZW : Z ≤ W := le_inf hZN hZC
  have hAW : A ≤ W := le_inf (inf_le_left.trans le_normalizer) inf_le_right
  have hMs : (M.subgroupOf W).IsSubnormal :=
    F3L226.isSubnormal_subgroupOf_mono inf_le_right hM.2.1
  have hMA : ∀ k ∈ M, ∀ a ∈ A, k * a * k⁻¹ ∈ A := fun k hk => hAn k (hMW hk)
  have hMZ : ∀ k ∈ M, ∀ c ∈ Z, k * c * k⁻¹ ∈ Z := fun k hk c hc =>
    conj_mem_centralizer (hMN hk) hc
  have hOModd : Odd (Nat.card OM) := by
    rw [hOM, Subgroup.card_map_of_injective M.subtype_injective]
    exact odd_card_pPrimeCore_two ↥M
  have hAZ : ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ A ⊔ Z := by
    intro s hs hs2
    have hss : s ∈ ((L ⊔ Z : Subgroup Q) : Set Q) := hinner s hs hs2
    rw [coe_mul_of_right_le_normalizer_left L Z hZN] at hss
    obtain ⟨l, hl, c, hc, hlc⟩ := hss
    have hlC : l ∈ C := by
      have h1 : l = s * c⁻¹ := by rw [← hlc]; group
      rw [h1]
      exact mul_mem (hMC hs) (inv_mem (hZC hc))
    rw [← hlc]
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hl, hlC⟩)) (mem_sup_right hc)
  set D : Set Q := {q | ∃ hq : q ∈ M, e (QuotientGroup.mk ⟨q, hq⟩) ^ 4 = 1} with hD
  have hxD : ∀ s ∈ M, ∀ {n : ℕ}, s ^ 2 ^ n = 1 → s ∈ D := fun s hs n hsn =>
    ⟨hs, e_mk_pow_four e hs hsn⟩
  have hDso : ∀ q ∈ D, ∃ s ∈ A ⊔ Z, ∃ o ∈ OM, q = s * o := by
    rintro q ⟨hq, hq4⟩
    have h4 : (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨q, hq⟩) ^ 2 ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one, show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact hq4
    obtain ⟨k, ⟨m, hm⟩, hk⟩ := F3L225.exists_pow_two_pow _ _ h4
    set s : ↥M := ⟨q, hq⟩ ^ k with hs
    have hsn : (s : Q) ^ 2 ^ m = 1 := by
      have h5 := congrArg Subtype.val hm
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h5
    have hk' : (QuotientGroup.mk s : ↥M ⧸ pPrimeCore 2 ↥M) = QuotientGroup.mk ⟨q, hq⟩ := hk
    have ho : s⁻¹ * ⟨q, hq⟩ ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.mp hk'
    refine ⟨(s : Q), hAZ _ s.2 ⟨m, hsn⟩, ((s⁻¹ * ⟨q, hq⟩ : ↥M) : Q), ⟨_, ho, rfl⟩, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have hDc : ∀ q ∈ D, ∃ a ∈ D, ∃ g ∈ M, q * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ OM := by
    rintro q ⟨hq, hq4⟩
    obtain ⟨a₀, g₀, ha₀, hqa⟩ := F3L221.sl23_commutator hq4
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm a₀)
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm g₀)
    have hea : e (QuotientGroup.mk a) = a₀ := by rw [ha, MulEquiv.apply_symm_apply]
    have heg : e (QuotientGroup.mk g) = g₀ := by rw [hg, MulEquiv.apply_symm_apply]
    refine ⟨(a : Q), ⟨a.2, ?_⟩, (g : Q), g.2, ?_⟩
    · show e (QuotientGroup.mk a) ^ 4 = 1
      rw [hea]
      exact ha₀
    · have h1 : (⟨q, hq⟩ : ↥M) * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ pPrimeCore 2 ↥M := by
        rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hea, heg]
        rw [← hqa, mul_inv_cancel]
      exact ⟨_, h1, rfl⟩
  have hAOn : ∀ k ∈ W, ∀ a ∈ A ⊔ OM, k * a * k⁻¹ ∈ A ⊔ OM := by
    intro k hk a ha
    have hle : A ⊔ OM ≤ (A ⊔ OM).comap (MulAut.conj k).toMonoidHom :=
      sup_le (fun a' ha' => mem_sup_left (hAn k hk a' ha'))
        (fun o ho => mem_sup_right (hOMn k (mem_inf.mp hk).2 o ho))
    exact hle ha
  have hZOn : ∀ k ∈ W, ∀ a ∈ Z ⊔ OM, k * a * k⁻¹ ∈ Z ⊔ OM := by
    intro k hk a ha
    have hle : Z ⊔ OM ≤ (Z ⊔ OM).comap (MulAut.conj k).toMonoidHom :=
      sup_le (fun c hc => mem_sup_left (conj_mem_centralizer (mem_inf.mp hk).1 hc))
        (fun o ho => mem_sup_right (hOMn k (mem_inf.mp hk).2 o ho))
    exact hle ha
  have key₁ := F3L221.mem_sup_inf_of_isSubnormal (M := W) (A := A ⊔ OM) (B := Z) (K := M)
    hZW hMW hAOn hMZ (D := D) (fun q hq => by
      obtain ⟨s, hs, o, ho, rfl⟩ := hDso q hq
      exact mul_mem ((sup_le_sup_right le_sup_left Z) hs) (mem_sup_left (mem_sup_right ho)))
    (fun q hq => by
      obtain ⟨a, ha, g, hg, h⟩ := hDc q hq
      exact ⟨a, ha, g, hg, mem_sup_right h⟩) hMs
  have key₂ := F3L221.mem_sup_inf_of_isSubnormal (M := W) (A := Z ⊔ OM) (B := A) (K := M)
    hAW hMW hZOn hMA (D := D) (fun q hq => by
      obtain ⟨s, hs, o, ho, rfl⟩ := hDso q hq
      have hle : A ⊔ Z ≤ (Z ⊔ OM) ⊔ A := sup_le le_sup_right (le_sup_left.trans le_sup_left)
      exact mul_mem (hle hs) (mem_sup_left (mem_sup_right ho)))
    (fun q hq => by
      obtain ⟨a, ha, g, hg, h⟩ := hDc q hq
      exact ⟨a, ha, g, hg, mem_sup_right h⟩) hMs
  by_cases hzL : z ∈ L
  · have hzA : z ∈ A := mem_inf.mpr ⟨hzL, hMC hzM⟩
    by_cases hpm : ∀ y (hy : y ∈ M ⊓ Z), e (QuotientGroup.mk ⟨y, (mem_inf.mp hy).1⟩) = 1 ∨
        e (QuotientGroup.mk ⟨y, (mem_inf.mp hy).1⟩) = -1
    ·
      left
      have hMZ' : M ⊓ Z ≤ A ⊔ OM := by
        intro y hy
        have hyM := (mem_inf.mp hy).1
        rcases hpm y hy with h | h
        · have h1 : (⟨y, hyM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
            rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
            exact h
          exact mem_sup_right ⟨_, h1, rfl⟩
        · have h1 : (⟨z, hzM⟩ : ↥M)⁻¹ * ⟨y, hyM⟩ ∈ pPrimeCore 2 ↥M :=
            QuotientGroup.eq.mp (e.injective ((e_mk_eq_neg_one e hzM hz).trans h.symm))
          have h2 : y = z * (((⟨z, hzM⟩ : ↥M)⁻¹ * ⟨y, hyM⟩ : ↥M) : Q) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
          rw [h2]
          exact mul_mem (mem_sup_left hzA) (mem_sup_right ⟨_, h1, rfl⟩)
      rintro s hs ⟨n, hsn⟩
      have h2 : s ∈ A ⊔ OM := (sup_le le_rfl hMZ') (key₁ s (hxD s hs hsn))
      exact (mem_inf.mp (F3L221.mem_of_mem_sup_of_odd (map_pPrimeCore_le_normalizer hMA)
        hOModd h2 hsn)).1
    ·
      right
      push Not at hpm
      obtain ⟨y, hy, hy1, hy2⟩ := hpm
      rintro s hs ⟨n, hsn⟩ l hl
      have hMZn : ∀ k ∈ M, ∀ y ∈ M ⊓ Z, k * y * k⁻¹ ∈ M ⊓ Z := fun k hk y hy =>
        mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp hy).1) (inv_mem hk),
          hMZ k hk y (mem_inf.mp hy).2⟩
      have h1 := mem_of_not_central e inf_le_left hMZn hy hy1 hy2 hs hsn
      exact ((mem_centralizer_iff.mp (mem_inf.mp h1).2) l hl).symm
  ·
    right
    have hMAn : ∀ k ∈ M, ∀ y ∈ M ⊓ A, k * y * k⁻¹ ∈ M ⊓ A := fun k hk y hy =>
      mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp hy).1) (inv_mem hk),
        hMA k hk y (mem_inf.mp hy).2⟩
    have hMAO : M ⊓ A ≤ OM := F3L221.le_pPrimeCore_of_not_mem e hzM hz hzc inf_le_left hMAn
      (fun h => hzL (mem_inf.mp (mem_inf.mp h).2).1)
    rintro s hs ⟨n, hsn⟩ l hl
    have hle : (Z ⊔ OM) ⊔ (M ⊓ A) ≤ Z ⊔ OM := sup_le le_rfl (hMAO.trans le_sup_right)
    have h2 : s ∈ Z ⊔ OM := hle (key₂ s (hxD s hs hsn))
    have h3 := F3L221.mem_of_mem_sup_of_odd (map_pPrimeCore_le_normalizer hMZ) hOModd h2 hsn
    exact ((mem_centralizer_iff.mp h3) l hl).symm

end F3A75

end CFSG.ComponentClassification.HarrisLit.T1
