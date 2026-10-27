module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Local
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.ClassicalInvolution.Balance Subgroup

namespace S3T5

theorem eq_of_add_self_eq_zero {k : ℕ} [NeZero k] {x y : ZMod k} (hx : x + x = 0) (hx0 : x ≠ 0)
    (hy : y + y = 0) (hy0 : y ≠ 0) : x = y := by
  have hxv : (x.val + x.val) % k = 0 := by
    rw [← ZMod.val_add, hx, ZMod.val_zero]
  have hyv : (y.val + y.val) % k = 0 := by
    rw [← ZMod.val_add, hy, ZMod.val_zero]
  have hxl : x.val < k := ZMod.val_lt x
  have hyl : y.val < k := ZMod.val_lt y
  have hx1 : x.val ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).1 h)
  have hy1 : y.val ≠ 0 := fun h => hy0 ((ZMod.val_eq_zero y).1 h)
  have hxk : x.val + x.val = k := by
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hxv
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    rw [hc, hc1, mul_one]
  have hyk : y.val + y.val = k := by
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hyv
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    rw [hc, hc1, mul_one]
  exact ZMod.val_injective k (by omega)

theorem eq_one_of_odd_comm {k : ℕ} [NeZero k] {z t w : DihedralGroup k} (hz : ∀ y, y * z = z * y)
    (hz1 : z ≠ 1) (hzz : z * z = 1) (htt : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z)
    (hw : Odd (orderOf w)) (hwt : w * t = t * w) : w = 1 := by
  rcases w with i | i
  swap
  · rw [DihedralGroup.orderOf_sr] at hw
    exact absurd hw (by decide)
  suffices hii : i + i = 0 by
    have h2 : DihedralGroup.r i ^ 2 = 1 := by
      rw [pow_two, DihedralGroup.r_mul_r, hii, DihedralGroup.one_def]
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    have h1 : orderOf (DihedralGroup.r i) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hw; exact absurd hw (by decide)
    exact orderOf_eq_one_iff.1 h1
  rcases t with j | j
  ·
    rcases z with i₀ | i₀
    · exfalso
      apply htz
      have h0 : i₀ + i₀ = 0 := by
        have := hz (DihedralGroup.sr 0)
        simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, zero_add, zero_sub] at this
        have h' : i₀ = -i₀ := DihedralGroup.sr.inj this
        calc i₀ + i₀ = -i₀ + i₀ := by rw [← h']
          _ = 0 := by ring
      have hj : j + j = 0 := by
        rw [DihedralGroup.r_mul_r, DihedralGroup.one_def] at htt
        exact DihedralGroup.r.inj htt
      have hj0 : j ≠ 0 := fun h => ht1 (by rw [h, DihedralGroup.one_def])
      have hi0 : i₀ ≠ 0 := fun h => hz1 (by rw [h, DihedralGroup.one_def])
      rw [eq_of_add_self_eq_zero hj hj0 h0 hi0]
    ·
      have := hz (DihedralGroup.r 1)
      simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at this
      have h' : i₀ - 1 = i₀ + 1 := DihedralGroup.sr.inj this
      have h2 : (1 : ZMod k) + 1 = 0 := by
        calc (1 : ZMod k) + 1 = (i₀ + 1) - (i₀ - 1) := by ring
          _ = 0 := by rw [h', sub_self]
      calc i + i = i * (1 + 1) := by ring
        _ = 0 := by rw [h2, mul_zero]
  ·
    simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hwt
    have h' : j - i = j + i := DihedralGroup.sr.inj hwt
    calc i + i = (j + i) - (j - i) := by ring
      _ = 0 := by rw [h', sub_self]

theorem exists_fieldAut_of_involution {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* L2 F) {y : MulAut K} (hy2 : orderOf y = 2) (hproj : fieldProj e y ≠ 1) :
    ∃ (e' : K ≃* L2 F) (σ : F ≃+* F), y = fieldAutHom e' σ ∧ orderOf σ = 2 := by
  have hord : orderOf (thetaAut e y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy2
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord
    (by rw [← fieldProj_apply]; exact hproj)
  have hΘφ := thetaAut_fieldAutHom e (thetaAut e y).right
  have hΘa : thetaAut e (innDiagHom e C) = SemidirectProduct.inl C := thetaAut_innDiagHom e C
  have hconj : (innDiagHom e C)⁻¹ * y * innDiagHom e C = fieldAutHom e (thetaAut e y).right := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, hΘa, hΘφ]
    exact hC
  refine ⟨twistEquiv e (innDiagHom e C)⁻¹, (thetaAut e y).right, ?_, ?_⟩
  · rw [fieldAutHom_twist, inv_inv, ← hconj]
    group
  · have h1 : orderOf (fieldProj e y) ∣ 2 := hy2 ▸ orderOf_map_dvd (fieldProj e) y
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hproj
    · exact h

theorem isLocallyKBalanced_two_of_pow_two
    {F : Type} [Field F] [Finite F]
    {K : Type} [Group K] [Finite K] (hF : L2Field F) (e : K ≃* L2 F) {p j : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2 ^ j) : Th2.Bal.IsLocallyKBalanced 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro H hH F' hF4 hF2
  by_contra hne
  have hF3 : 3 ≤ Nat.card ↥F' := by
    have : (2 : ℕ) ^ 2 = 4 := by norm_num
    omega
  have hcore : ∀ f : H, f ∈ F' → f ≠ 1 → CFSG.Assembly.Dichotomy.involutionOddCore f ≠ ⊥ :=
    fun f hfF hf1 hbot =>
      hne (le_bot_iff.mp ((deltaCore_le_involutionOddCore hfF hf1).trans hbot.le))
  have hord2 : ∀ f : H, f ∈ F' → f ≠ 1 → orderOf (f : MulAut K) = 2 := by
    intro f hfF hf1
    have h1 : (f : MulAut K) ^ 2 = 1 := by
      rw [pow_two]
      exact congrArg Subtype.val (hF2 f hfF)
    exact orderOf_eq_prime h1 (fun h => hf1 (Subtype.ext h))
  have hinD : ∀ f : H, f ∈ F' → f ≠ 1 → (f : MulAut K) ∈ innDiagSub e := by
    intro f hfF hf1
    by_contra hfD
    have hproj : fieldProj e (f : MulAut K) ≠ 1 := fun h => hfD ((mem_innDiagSub_iff e _).2 h)
    obtain ⟨e', σ, hσ, hσ2⟩ := exists_fieldAut_of_involution e (hord2 f hfF hf1) hproj
    apply hcore f hfF hf1
    apply Th2.Bal.involutionOddCore_eq_bot_of_pPrimeCoreOf H f
    rw [hσ]
    exact Th2.Bal.pPrimeCoreOf_fieldInvolution_eq_bot hF e' H hH σ hσ2
  obtain ⟨⟨w, hwΔ⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨a, b, ha, hb, hab⟩ := Th2.Bal.exists_two_ne_one (G := ↥F') hF3
  have ha' : (a : H) ≠ 1 := fun h => ha (Subtype.ext h)
  have hb' : (b : H) ≠ 1 := fun h => hb (Subtype.ext h)
  have hwa := deltaCore_le_involutionOddCore a.2 ha' hwΔ
  have hwb := deltaCore_le_involutionOddCore b.2 hb' hwΔ
  have hwac : w * a = a * w :=
    Subgroup.mem_centralizer_singleton_iff.1 (Prop27.involutionOddCore_le_centralizer _ hwa)
  have hwbc : w * b = b * w :=
    Subgroup.mem_centralizer_singleton_iff.1 (Prop27.involutionOddCore_le_centralizer _ hwb)
  have hbac : (b : H) * a = a * b := by
    have haa : (a : H) * a = 1 := hF2 _ a.2
    have hbb : (b : H) * b = 1 := hF2 _ b.2
    have hab2 : ((a : H) * b) * ((a : H) * b) = 1 := hF2 _ (F'.mul_mem a.2 b.2)
    calc (b : H) * a = (b : H) * a * ((a : H) * b * ((a : H) * b)) := by rw [hab2, mul_one]
      _ = (b : H) * (a * a) * b * (a * b) := by group
      _ = (a : H) * b := by rw [haa, mul_one, hbb, one_mul]
  have hwodd : Odd (orderOf (w : MulAut K)) := by
    rw [Subgroup.orderOf_coe]
    exact (CFSG.Assembly.Dichotomy.odd_card_involutionOddCore (a : H)).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hwa)
  have hwD : (w : MulAut K) ∈ innDiagSub e := by
    rw [mem_innDiagSub_iff]
    have hGal : Nat.card (F ≃+* F) = 2 ^ j := by
      obtain ⟨-, ⟨φ⟩, hn⟩ := ivk_1_2e F hF K e
      rw [← Nat.card_congr φ.toEquiv]
      exact hn p (2 ^ j) hp hcard
    have h1 := orderOf_map_dvd (fieldProj e) (w : MulAut K)
    have h2 : orderOf (fieldProj e (w : MulAut K)) ∣ 2 ^ j := hGal ▸ orderOf_dvd_natCard _
    have h3 : Odd (orderOf (fieldProj e (w : MulAut K))) := hwodd.of_dvd_nat h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases i with _ | i
    · exact orderOf_eq_one_iff.1 (by rw [hi, pow_zero])
    · rw [hi, pow_succ] at h3
      exact absurd (Nat.even_mul.2 (Or.inr even_two)) (Nat.not_even_iff_odd.2 h3)
  set C := centralizer ({((a : H) : MulAut K)} : Set (MulAut K)) ⊓ innDiagSub e with hC
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨⟨t, ht⟩, h3⟩ := hF
    omega
  obtain ⟨ε, hε, hcongr⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      show (Nat.card F : ℤ) % 4 = 1 % 4
      omega
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show (Nat.card F : ℤ) % 4 = (-1) % 4
      omega
  have hdih : ∃ m, IsDihedralOrder ↥C m := by
    by_cases haI : ((a : H) : MulAut K) ∈ innAut K
    · obtain ⟨u, hu⟩ := haI
      have hu2 : orderOf u = 2 := by
        rw [← orderOf_injective _ (conj_injective_of_L2 e) u, hu]
        exact hord2 _ a.2 ha'
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
        ⟨(Nat.card F - ε).toNat, by rcases hε with rfl | rfl <;> omega⟩
      obtain ⟨hD, -⟩ := ivk_1_3a F hF K e ε hε hcongr d hd u hu2
      refine ⟨2 * d, ?_⟩
      rw [hC, ← hu]
      exact hD
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
        ⟨(Nat.card F + ε).toNat, by rcases hε with rfl | rfl <;> omega⟩
      obtain ⟨hD, -⟩ :=
        ivk_1_3b F hF K e ε hε hcongr d hd _ (hinD _ a.2 ha') haI (hord2 _ a.2 ha')
      exact ⟨2 * d, hD⟩
  obtain ⟨m, k, -, hk2, ⟨φ⟩⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  have haC : ((a : H) : MulAut K) ∈ C :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hinD _ a.2 ha'⟩
  have hbC : ((b : H) : MulAut K) ∈ C :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hbac), hinD _ b.2 hb'⟩
  have hwC : (w : MulAut K) ∈ C :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hwac), hwD⟩
  have hsq : ∀ f : H, f ∈ F' → ∀ hfC : (f : MulAut K) ∈ C, (⟨_, hfC⟩ : ↥C) * ⟨_, hfC⟩ = 1 :=
    fun f hf hfC => Subtype.ext (congrArg (fun x : ↥H => (x : MulAut K)) (hF2 f hf))
  have hne1 : ∀ f : H, f ≠ 1 → ∀ hfC : (f : MulAut K) ∈ C, φ ⟨_, hfC⟩ ≠ 1 := by
    intro f hf1 hfC h1
    apply hf1
    have h2 : (⟨_, hfC⟩ : ↥C) = 1 := φ.injective (h1.trans (map_one φ).symm)
    exact Subtype.ext (congrArg (fun x : ↥C => (x : MulAut K)) h2)
  have hzc : ∀ y, y * φ ⟨_, haC⟩ = φ ⟨_, haC⟩ * y := by
    intro y
    obtain ⟨c, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2.1)
  have htz : φ ⟨_, hbC⟩ ≠ φ ⟨_, haC⟩ := by
    intro h1
    apply hab
    have h2 : (⟨_, hbC⟩ : ↥C) = ⟨_, haC⟩ := φ.injective h1
    have h3 : ((b : H) : MulAut K) = ((a : H) : MulAut K) :=
      congrArg (fun x : ↥C => (x : MulAut K)) h2
    have h4 : (b : H) = (a : H) := Subtype.ext h3
    exact (Subtype.ext h4).symm
  have hwo : Odd (orderOf (φ ⟨_, hwC⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hwodd
  have hwt : φ ⟨_, hwC⟩ * φ ⟨_, hbC⟩ = φ ⟨_, hbC⟩ * φ ⟨_, hwC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg (fun x : ↥H => (x : MulAut K)) hwbc)
  have h1 := eq_one_of_odd_comm hzc (hne1 _ ha' haC)
    (by rw [← map_mul, hsq _ a.2 haC, map_one]) (by rw [← map_mul, hsq _ b.2 hbC, map_one])
    (hne1 _ hb' hbC) htz hwo hwt
  apply hw1'
  have h2 : (⟨_, hwC⟩ : ↥C) = 1 := φ.injective (h1.trans (map_one φ).symm)
  exact Subtype.ext (congrArg (fun x : ↥C => (x : MulAut K)) h2)

theorem not_pow_two_of_not_locallyBalanced
    {L : Type} [Group L] [Finite L]
    {p m : ℕ} (hp : p.Prime) (hodd : Odd (p ^ m)) (hLie : Blueprint.LieModel L .PSL 2 p m)
    (hnot : ¬ Th2.Bal.IsLocallyKBalanced 2 (L ⧸ center L)) : ¬ ∃ k : ℕ, m = 2 ^ k := by
  rintro ⟨k, rfl⟩
  obtain ⟨F, _, _, e0, hF, hcard⟩ := Th2.Bal.exists_l2Field_of_lieModel hodd hLie
  have hc : center L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply conj_injective_of_L2 e0
    ext g
    simp only [MulAut.conj_apply, map_one, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hz g).symm
  let eKL : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact hnot (isLocallyKBalanced_two_of_pow_two hF (eKL.trans e0) hp hcard)

end S3T5

end CFSG.GH74.Generic.BProg.B3
