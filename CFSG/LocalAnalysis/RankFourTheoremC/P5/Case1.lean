module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Automizer
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Lift
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Semilinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

namespace BorelDataP

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G} {n : ℕ}
  {f : GaloisField p n → G} {W : Subgroup G}

private def commQKP (hB : BorelDataP p P M x f W) (O Y : Subgroup G)
    (hQO : hB.QK ≤ normalizer (O : Set G)) : Subgroup G where
  carrier := {g | g ∈ hB.QK ∧ ∀ i ∈ Y, i ^ 2 = 1 → g * i * g⁻¹ * i⁻¹ ∈ O}
  mul_mem' := by
    rintro g g' ⟨hg, hgi⟩ ⟨hg', hg'i⟩
    refine ⟨hB.QK.mul_mem hg hg', fun i hi hi2 => ?_⟩
    have e : g * g' * i * (g * g')⁻¹ * i⁻¹ =
        (g * (g' * i * g'⁻¹ * i⁻¹) * g⁻¹) * (g * i * g⁻¹ * i⁻¹) := by group
    rw [e]
    exact O.mul_mem ((mem_normalizer_iff.mp (hQO hg) _).mp (hg'i i hi hi2)) (hgi i hi hi2)
  one_mem' := ⟨hB.QK.one_mem, fun i _ _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hgi⟩
    refine ⟨hB.QK.inv_mem hg, fun i hi hi2 => ?_⟩
    have e : g⁻¹ * i * (g⁻¹)⁻¹ * i⁻¹ = g⁻¹ * (g * i * g⁻¹ * i⁻¹)⁻¹ * g := by group
    rw [e]
    have := (mem_normalizer_iff.mp (hQO (hB.QK.inv_mem hg)) _).mp (O.inv_mem (hgi i hi hi2))
    simpa [mul_assoc] using this

private theorem x_mem_plane' (t₀ : GaloisField p n) : x ∈ plane x f t₀ :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

private theorem f_mem_plane' (t₀ : GaloisField p n) : f t₀ ∈ plane x f t₀ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers (f t₀))

private theorem mem_zpowers_nat_of_pow_p {y z : G} (hy : y ^ p = 1) (hy1 : y ≠ 1)
    (hz : z ∈ zpowers y) : ∃ m : ℕ, z = y ^ m := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hord : orderOf y = p := orderOf_eq_prime hy hy1
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  refine ⟨(k % (p : ℤ)).toNat, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne'), ← hord, zpow_mod_orderOf]

private theorem eq_t0_of_conj_mem (hB : BorelDataP p P M x f W) (hp2 : p ≠ 2) {O Y : Subgroup G}
    (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G)) (hY2 : IsPGroup 2 Y)
    {t₀ s : GaloisField p n} (hUY : plane x f t₀ ≤ normalizer (Y : Set G))
    {i : G} (hiY : i ∈ Y) {o : G} (ho : o ∈ O) (hio : i * f t₀ * i⁻¹ = f s * o) : s = t₀ := by
  have hp2c : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
  have hu : f t₀ ∈ normalizer (Y : Set G) := hUY (f_mem_plane' t₀)
  set c : G := f t₀ * i * (f t₀)⁻¹ * i⁻¹ with hc
  have hcY : c ∈ Y := Y.mul_mem ((mem_normalizer_iff.mp hu i).mp hiY) (Y.inv_mem hiY)
  have hcR : c ∈ hB.QK ⊔ O := by
    have e : c = f t₀ * (f s * o)⁻¹ := by rw [← hio, hc]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hB.f_mem_QK t₀))
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hB.f_mem_QK s))
        (Subgroup.mem_sup_right ho)))
  have hcO : c ∈ O := by
    obtain ⟨k, hk⟩ := hY2 ⟨c, hcY⟩
    have hord : orderOf c ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hcop : Nat.Coprime p (orderOf c) :=
      Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right _ hp2c)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact O.pow_mem (hB.pow_p_mem_QK_sup hQO hcR) m
  have hcf : i * f t₀ * i⁻¹ = c⁻¹ * f t₀ := by rw [hc]; group
  have ho' : (f t₀)⁻¹ * c⁻¹ * f t₀ ∈ O := by
    have := (mem_normalizer_iff.mp (hQO (hB.QK.inv_mem (hB.f_mem_QK t₀))) c⁻¹).mp (O.inv_mem hcO)
    simpa using this
  have hfs : f s * o = f t₀ * ((f t₀)⁻¹ * c⁻¹ * f t₀) := by
    rw [← hio, hcf]; group
  exact hB.eq_of_f_mul_mem hO ho ho' hQO hfs

private theorem f_mem_commQKP (hB : BorelDataP p P M x f W) {O Y : Subgroup G}
    (hQO : hB.QK ≤ normalizer (O : Set G)) {s : GaloisField p n}
    (hs : ∀ i ∈ Y, i ^ 2 = 1 → ∃ o ∈ O, i * f s * i⁻¹ = f s * o) :
    f s ∈ commQKP hB O Y hQO := by
  refine ⟨hB.f_mem_QK s, fun i hiY hi2 => ?_⟩
  obtain ⟨o, ho, h⟩ := hs i hiY hi2
  have e : f s * i * (f s)⁻¹ * i⁻¹ = f s * o⁻¹ * (f s)⁻¹ := by
    calc f s * i * (f s)⁻¹ * i⁻¹ = f s * (i * f s * i⁻¹)⁻¹ := by group
      _ = f s * (f s * o)⁻¹ := by rw [h]
      _ = f s * o⁻¹ * (f s)⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp (hQO (hB.f_mem_QK s)) _).mp (O.inv_mem ho)

private theorem mem_commQKP_iff (hB : BorelDataP p P M x f W) {O Y : Subgroup G}
    (hQO : hB.QK ≤ normalizer (O : Set G)) {g : G} :
    g ∈ commQKP hB O Y hQO ↔ g ∈ hB.QK ∧ ∀ i ∈ Y, i ^ 2 = 1 → g * i * g⁻¹ * i⁻¹ ∈ O :=
  Iff.rfl

private theorem x_not_mem_QK_sup (hB : BorelDataP p P M x f W) {O : Subgroup G}
    (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G)) :
    x ∉ (hB.QK ⊔ O : Subgroup G) := by
  intro hxr
  obtain ⟨t, o, ho, hxo⟩ := (hB.mem_QK_sup_iff hQO).mp hxr
  have hco : Commute ((f t)⁻¹) x := (show Commute (f t) x from hB.f_comm t).inv_left
  have ho' : o = (f t)⁻¹ * x := by rw [hxo]; group
  have hop : o ^ p = 1 := by
    rw [ho', hco.mul_pow, inv_pow, hB.f_pow_p, hB.x_pow, inv_one, one_mul]
  have ho1 : o = 1 := by
    have hd : orderOf o ∣ p := orderOf_dvd_of_pow_eq_one hop
    have hd2 : orderOf o ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime hp.out).mp hd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ hd2) hO
  rw [ho1, mul_one] at hxo
  exact hB.f_ne t hxo.symm

private theorem x_comm_QK_sup (hB : BorelDataP p P M x f W) {O : Subgroup G}
    (hQO : hB.QK ≤ normalizer (O : Set G)) (hxO : x ∈ normalizer (O : Set G)) {r : G}
    (hr : r ∈ hB.QK ⊔ O) : x * r * x⁻¹ * r⁻¹ ∈ O := by
  obtain ⟨t, o, ho, rfl⟩ := (hB.mem_QK_sup_iff hQO).mp hr
  have hxf : x * f t * x⁻¹ = f t := by
    have := hB.f_comm t
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have e : x * (f t * o) * x⁻¹ * (f t * o)⁻¹ = f t * (x * o * x⁻¹ * o⁻¹) * (f t)⁻¹ := by
    calc x * (f t * o) * x⁻¹ * (f t * o)⁻¹ = (x * f t * x⁻¹) * (x * o * x⁻¹) * o⁻¹ * (f t)⁻¹ := by
          group
      _ = f t * (x * o * x⁻¹ * o⁻¹) * (f t)⁻¹ := by rw [hxf]; group
  rw [e]
  exact (mem_normalizer_iff.mp (hQO (hB.f_mem_QK t)) _).mp
    (O.mul_mem ((mem_normalizer_iff.mp hxO o).mp ho) (O.inv_mem ho))

private theorem f_not_mem_zpowers_t0 (hB : BorelDataP p P M x f W) {t₀ w : GaloisField p n}
    (ht₀ : t₀ ≠ 0) (hwv : ∀ m : ℕ, w ≠ (m : GaloisField p n) * t₀) :
    f w ∉ zpowers (f t₀) := by
  intro hmem
  have hft1 : f t₀ ≠ 1 := fun h => ht₀ (hB.f_inj (h.trans hB.f_zero.symm))
  obtain ⟨m, hm⟩ := mem_zpowers_nat_of_pow_p (hB.f_pow_p t₀) hft1 hmem
  exact hwv m (hB.f_inj (by rw [hB.f_nat_mul]; exact hm))

private theorem card_sup_zpowers_t0 (hB : BorelDataP p P M x f W) {t₀ w : GaloisField p n}
    (ht₀ : t₀ ≠ 0) (hnot : f w ∉ zpowers (f t₀))
    (hcommB : ∀ e ∈ zpowers (f t₀), e * f w = f w * e) :
    Nat.card (zpowers (f t₀) ⊔ zpowers (f w) : Subgroup G) = p ^ 2 := by
  have hft1 : f t₀ ≠ 1 := fun h => ht₀ (hB.f_inj (h.trans hB.f_zero.symm))
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp.out (zpowers (f t₀)) (hB.f_pow_p w) hnot
    hcommB, Nat.card_zpowers, orderOf_eq_prime (hB.f_pow_p t₀) hft1, pow_two]

private theorem normalizer_le_of_E {Y E : Subgroup G}
    (hD1 : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hY₁ne : involClosure Y ≠ ⊥) (hY2 : IsPGroup 2 Y)
    (hEN : E ≤ normalizer (involClosure Y : Set G)) (hEM : E ≤ M) (hEel : IsElemAbelian p E)
    (hE27 : p ^ 3 ≤ Nat.card E) : normalizer (Y : Set G) ≤ M := by
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEel.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have h1 : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2 : p ^ 3 ≤ p ^ k := by rw [← hk]; exact hE27
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    have h4 : p ^ 2 * 2 ≤ p ^ 2 * p := Nat.mul_le_mul le_rfl hp.out.two_le
    have h5 : 0 < p ^ 2 := pow_pos hp.out.pos 2
    linarith
  have hrank : 3 ≤ CFSG.Open.pRank p (normalizer (involClosure Y : Set G) ⊓ M) :=
    hk3.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp.out _)
      ⟨E, le_inf hEN hEM, hEel, hk⟩)
  have hTL : IsTwoLocal (normalizer (involClosure Y : Set G)) :=
    ⟨involClosure Y, hY₁ne, hY2.to_le (involClosure_le Y), rfl⟩
  intro g hg
  exact (hD1 _ hTL hrank) (mem_normalizer_involClosure hg)

theorem normalizer_le_of_normal (hB : BorelDataP p P M x f W) (hS : PtShape p P x)
    {O : Subgroup G} (hO : ¬ p ∣ Nat.card O) (hO2 : 2 ∣ Nat.card O)
    (hOM : M ≤ normalizer (O : Set G)) (hOle : O ≤ M)
    (hQM : hB.QK ≤ M) (hRM : M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G))
    (hCM : centralizer (hB.QK : Set G) ≤ M) (hxM : x ∈ M)
    (hD1 : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    {t₀ : GaloisField p n} (ht₀ : t₀ ≠ 0) {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hUY : plane x f t₀ ≤ normalizer (Y : Set G)) (hYO : IsSylowOf 2 (Y ⊓ O) O) :
    normalizer (Y : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by have := hB.five_le; omega
  have hQO : hB.QK ≤ normalizer (O : Set G) := hQM.trans hOM
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    have h1 := hYO.card_eq
    rw [hbot, bot_inf_eq, Subgroup.card_bot] at h1
    have h2 : (Nat.card O).factorization 2 ≠ 0 := by
      have hpos : Nat.card O ≠ 0 := Nat.card_pos.ne'
      have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos).mp hO2
      omega
    have : 2 ^ (Nat.card O).factorization 2 = 1 := h1.symm
    have h3 : (Nat.card O).factorization 2 = 0 := by
      by_contra hne
      have := Nat.one_lt_two_pow hne
      omega
    exact h2 h3
  have hY₁ne : involClosure Y ≠ ⊥ := involClosure_ne_bot hY2 hY1
  choose ψ hψ using fun i : Y => exists_acts (hB := hB) hRM hQO (hYM i.2)
  have hψadd : ∀ i : Y, ∀ s t, ψ i (s + t) = ψ i s + ψ i t := fun i s t =>
    Acts.map_add hB hO hQO (hψ i) s t
  have hψinj : ∀ i : Y, Function.Injective (ψ i) := fun i =>
    Acts.injective hB hO hQO (hOM (hYM i.2)) (hψ i)
  let ψe : Y → (GaloisField p n ≃+ GaloisField p n) := fun i =>
    AddEquiv.ofBijective (AddMonoidHom.mk' (ψ i) (hψadd i))
      ⟨hψinj i, Finite.surjective_of_injective (hψinj i)⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Set (GaloisField p n ≃+ GaloisField p n),
      Ψ = {φ | ∃ i : Y, (i : G) ^ 2 = 1 ∧ φ = ψe i} := ⟨_, rfl⟩
  have hmemΨ : ∀ φ, φ ∈ Ψ ↔ ∃ i : Y, (i : G) ^ 2 = 1 ∧ φ = ψe i := by
    subst hΨ
    exact fun φ => Iff.rfl
  have hFcard : Nat.card (GaloisField p n) = p ^ n :=
    GaloisField.card p n (by have := hB.three_le; omega)
  have hfix : ∀ i : Y, (i : G) ^ 2 = 1 → ψ i t₀ = t₀ := by
    intro i _
    obtain ⟨o, ho, hio⟩ := hψ i t₀
    exact eq_t0_of_conj_mem hB hp2 hO hQO hY2 hUY i.2 ho hio
  have hinv : ∀ φ ∈ Ψ, ∀ t, φ (φ t) = t := by
    intro φ hφ t
    obtain ⟨i, hi2, rfl⟩ := (hmemΨ φ).mp hφ
    exact Acts.involutive hB hO hQO (hOM (hYM i.2)) ((pow_two (i : G)).symm.trans hi2) (hψ i) t
  have hnorm : ∀ φ ∈ Ψ, ∀ a : (GaloisField p n)ˣ, ∃ b : (GaloisField p n)ˣ,
      ∀ t, φ ((a : GaloisField p n) ^ 2 * t) = (b : GaloisField p n) ^ 2 * φ t := by
    intro φ hφ a
    obtain ⟨i, -, rfl⟩ := (hmemΨ φ).mp hφ
    exact Acts.squares hB hS hO hOM hOle hQM hRM hCM (hYM i.2) (hψ i) a
  have hfixΨ : ∀ φ ∈ Ψ, φ t₀ = t₀ := by
    intro φ hφ
    obtain ⟨i, hi2, rfl⟩ := (hmemΨ φ).mp hφ
    exact hfix i hi2
  obtain ⟨w, hwfix, hwm⟩ :=
    exists_fixed_not_mem_line_p hp2 hFcard hB.three_le Ψ hinv hnorm ht₀ hfixΨ
  have hwY : ∀ i : Y, (i : G) ^ 2 = 1 → ψ i w = w := fun i hi2 =>
    hwfix (ψe i) ((hmemΨ _).mpr ⟨i, hi2, rfl⟩)
  have hcomm_f : ∀ s, Commute (f t₀) (f s) := fun s => by
    show f t₀ * f s = f s * f t₀
    rw [← hB.f_add, ← hB.f_add, add_comm]
  have hnotw : f w ∉ zpowers (f t₀) := f_not_mem_zpowers_t0 hB ht₀ hwm
  have hcommB : ∀ e ∈ zpowers (f t₀), e * f w = f w * e := by
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact ((hcomm_f w).zpow_left k).eq
  have hcardA : Nat.card (zpowers (f t₀) ⊔ zpowers (f w) : Subgroup G) = p ^ 2 :=
    card_sup_zpowers_t0 hB ht₀ hnotw hcommB
  have hct : ∀ s, (∀ i : Y, (i : G) ^ 2 = 1 → ψ i s = s) →
      zpowers (f s) ≤ commQKP hB O Y hQO := by
    intro s hs
    rw [zpowers_le]
    refine f_mem_commQKP hB hQO (fun i hi hi2 => ?_)
    obtain ⟨o, ho, h⟩ := hψ ⟨i, hi⟩ s
    rw [hs ⟨i, hi⟩ hi2] at h
    exact ⟨o, ho, h⟩
  have hAc : zpowers (f t₀) ⊔ zpowers (f w) ≤ commQKP hB O Y hQO :=
    sup_le (hct t₀ hfix) (hct w hwY)
  have hAQ : zpowers (f t₀) ⊔ zpowers (f w) ≤ hB.QK :=
    sup_le (zpowers_le.mpr (hB.f_mem_QK t₀)) (zpowers_le.mpr (hB.f_mem_QK w))
  have hAR : zpowers (f t₀) ⊔ zpowers (f w) ≤ hB.QK ⊔ O := hAQ.trans le_sup_left
  have hAO : (zpowers (f t₀) ⊔ zpowers (f w)) ⊓ O = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right O hAQ).trans (hB.QK_inf_eq_bot hO hQO).le)
  have hAfix : ∀ a ∈ zpowers (f t₀) ⊔ zpowers (f w), ∀ i ∈ Y, i ^ 2 = 1 →
      a * i * a⁻¹ * i⁻¹ ∈ O := fun a ha i hi hi2 =>
    ((mem_commQKP_iff hB hQO).mp (hAc ha)).2 i hi hi2
  have hA : p ^ 2 ≤ Nat.card (zpowers (f t₀) ⊔ zpowers (f w) : Subgroup G) := hcardA.ge
  have hRO : hB.QK ⊔ O ≤ normalizer (O : Set G) := sup_le hQO Subgroup.le_normalizer
  have hYR : Y ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G) := hYM.trans hRM
  have hYNO : Y ≤ normalizer (O : Set G) := hYM.trans hOM
  obtain ⟨E, hEN, hER, hEel, hE27⟩ := exists_elemAbelian_normalizing_involClosure_p (O := O)
    (R := hB.QK ⊔ O) (Y := Y) (A := zpowers (f t₀) ⊔ zpowers (f w)) (x := x) hp2
    le_sup_right hRO hYR hYNO hO (fun r hr => hB.pow_p_mem_QK_sup hQO hr)
    (fun r hr r' hr' => hB.comm_mem_QK_sup hQO hr hr') hY2 hYO hB.x_pow
    (x_not_mem_QK_sup hB hO hQO) (hRM hxM) (fun r hr => x_comm_QK_sup hB hQO (hOM hxM) hr)
    (hUY (x_mem_plane' t₀)) hAR hAO hA hAfix
  have hEM : E ≤ M := hER.trans (sup_le (sup_le hQM hOle) (zpowers_le.mpr hxM))
  exact normalizer_le_of_E hD1 hY₁ne hY2 hEN hEM hEel hE27

end BorelDataP

end CFSG.LocalAnalysis.RankFourTheoremC.P5
