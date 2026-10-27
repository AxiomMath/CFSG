module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256b
public import Certificates.Certificate256301
public import Certificates.Certificate256302
public import CFSG.Sporadic.Recognition.HSMultiplierCert

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Generic

variable {K : Type} [Group K]

theorem fixedSub_conj (g : K) :
    Prop1310a5.fixedSub (MulAut.conj g) = Subgroup.centralizer ({g} : Set K) := by
  ext k
  change (MulAut.conj g) k = k ↔ k ∈ Subgroup.centralizer {g}
  rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc k * g = g * k * g⁻¹ * g := by rw [h]
      _ = g * k := by group
  · intro h
    rw [← h]
    group

theorem centralizer_sq_eq {e : K} (he : e ^ 3 = 1) :
    Subgroup.centralizer ({e ^ 2} : Set K) = Subgroup.centralizer ({e} : Set K) := by
  have h4 : (e ^ 2) ^ 2 = e := by
    calc (e ^ 2) ^ 2 = e ^ 3 * e := by group
      _ = e := by rw [he, one_mul]
  ext k
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 := Commute.pow_right (show Commute k (e ^ 2) from h) 2
    rw [h4] at h2
    exact h2.eq
  · intro h
    exact (Commute.pow_right (show Commute k e from h) 2).eq

theorem centralizer_conj_eq (c e : K) :
    Subgroup.centralizer ({c * e * c⁻¹} : Set K) =
      GLBConj c⁻¹ (Subgroup.centralizer ({e} : Set K)) := by
  have h := centralizer_singleton_gLBConj c⁻¹ e
  rwa [inv_inv] at h

noncomputable def barConj (g : K) (J : Subgroup K) : barOf 3 (GLBConj g J) ≃* barOf 3 J :=
  (QuotientGroup.congr (GLAPPrimeCore 3 ↥J) (GLAPPrimeCore 3 ↥(GLBConj g J)) (conjEquiv g J)
    (glaPPrimeCore_map_iso 3 (conjEquiv g J))).symm

theorem isAltType_barOf_gLBConj (g : K) {J : Subgroup K} (h : IsAltType 5 (barOf 3 J)) :
    IsAltType 5 (barOf 3 (GLBConj g J)) := by
  obtain ⟨e⟩ := h
  exact ⟨(barConj g J).trans e⟩

theorem conj_injective (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← hZ, Subgroup.mem_center_iff]
  intro k
  have h := congrArg (fun φ : MulAut K => φ k) (MonoidHom.mem_ker.1 hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc k * g = g * k * g⁻¹ * g := by rw [h]
    _ = g * k := by group

theorem le_kstar {A : Subgroup (MulAut K)} {S : MulAut K → Set (Subgroup K)} {a : MulAut K} (ha : a ∈ A)
    (ha1 : a ≠ 1) {J : Subgroup K} (hJ : J ∈ S a) : J ≤ Prop1310a5b.Kstar A S :=
  le_iSup₂_of_le (f := fun (a : MulAut K) (_ : a ∈ A ∧ a ≠ 1) => ⨆ (J : Subgroup K) (_ : J ∈ S a), J) a
    ⟨ha, ha1⟩ (le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ S a) => J) J hJ le_rfl)

theorem factorization_five_eq_one {m : ℕ} (hm : m ∣ 360) (h5 : 5 ∣ m) : m.factorization 5 = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  have h1 := (Nat.factorization_le_iff_dvd hm0 (by norm_num)).2 hm 5
  have h2 : (360 : ℕ).factorization 5 = 1 := by
    rw [show (360 : ℕ) = 5 ^ 1 * 72 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_five hm0 h5
  omega

variable [Finite K]

theorem not_mem_zpowers_of_mem_comp {g y : K} {L : Subgroup K}
    (hLg : L ≤ Subgroup.centralizer ({g} : Set K)) (hL5 : IsAltType 5 (barOf 3 L)) (hyL : y ∈ L)
    (hy : orderOf y = 3) : y ∉ Subgroup.zpowers g := by
  intro hyg
  obtain ⟨eL⟩ := hL5
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyg
  set t : ↥L := ⟨g ^ k, hyL⟩ with ht
  have hcent : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) t) ∈ Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) u
    rw [← map_mul, ← map_mul]
    congr 1
    have hu : Commute (u0 : K) g := Subgroup.mem_centralizer_singleton_iff.1 (hLg u0.2)
    exact Subtype.ext (Commute.zpow_right hu k).eq
  have hone : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) t) = 1 := by
    have hc : eL (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) t) ∈
        Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff] at hcent ⊢
      intro v
      obtain ⟨v', rfl⟩ := eL.surjective v
      rw [← map_mul, ← map_mul, hcent v']
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact eL.injective (hc.trans (map_one eL).symm)
  have hmem : t ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff t).1 hone
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  have ho : orderOf (⟨t, hmem⟩ : GLAPPrimeCore 3 ↥L) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hy
  have h3 := orderOf_dvd_natCard (⟨t, hmem⟩ : GLAPPrimeCore 3 ↥L)
  rw [ho] at h3
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

theorem exists_conj_of_orderOf_three {e₁ e₂ : K}
    (hE : Nat.card (Subgroup.closure ({e₁, e₂} : Set K)) = 3 ^ (Nat.card K).factorization 3)
    (hcls : ∀ ε ∈ Subgroup.closure ({e₁, e₂} : Set K), ε ≠ 1 →
      ∃ c : K, ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ c * e₁ ^ s * c⁻¹ = ε)
    {z : K} (hz : orderOf z = 3) : ∃ c : K, ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ c * e₁ ^ s * c⁻¹ = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hE hzp
  obtain ⟨ε, hε, hεz⟩ := hk (Subgroup.mem_zpowers z)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hεz
  have hε1 : ε ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel] at hεz
    rw [← hεz, orderOf_one] at hz
    omega
  obtain ⟨c, s, hs, hc⟩ := hcls ε hε hε1
  refine ⟨k * c, s, hs, ?_⟩
  rw [← hεz, ← hc]
  group

theorem exists_comp_of_orderOf_three {e₁ : K} (he₁ : e₁ ^ 3 = 1)
    (hcl : ∀ z : K, orderOf z = 3 → ∃ c : K, ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ c * e₁ ^ s * c⁻¹ = z)
    {g : K} (hg : orderOf g = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({g} : Set K)) L) (hL5 : IsAltType 5 (barOf 3 L))
    {z : K} (hz : orderOf z = 3) :
    ∃ J : Subgroup K, GLAPComponent 3 (Subgroup.centralizer ({z} : Set K)) J ∧ IsAltType 5 (barOf 3 J) := by
  obtain ⟨c₁, s₁, hs₁, hc₁⟩ := hcl g hg
  obtain ⟨c₂, s₂, hs₂, hc₂⟩ := hcl z hz
  have hC : ∀ s : ℕ, (s = 1 ∨ s = 2) →
      Subgroup.centralizer ({e₁ ^ s} : Set K) = Subgroup.centralizer ({e₁} : Set K) := by
    rintro s (rfl | rfl)
    · rw [pow_one]
    · exact centralizer_sq_eq he₁
  have hCg : Subgroup.centralizer ({g} : Set K) =
      GLBConj c₁⁻¹ (Subgroup.centralizer ({e₁} : Set K)) := by
    rw [← hc₁, centralizer_conj_eq, hC s₁ hs₁]
  have hCz : Subgroup.centralizer ({z} : Set K) =
      GLBConj c₂⁻¹ (Subgroup.centralizer ({e₁} : Set K)) := by
    rw [← hc₂, centralizer_conj_eq, hC s₂ hs₂]
  refine ⟨GLBConj (c₁ * c₂⁻¹) L, ?_, isAltType_barOf_gLBConj _ hL5⟩
  have h := glaPComponent_gLBConj hL (c₁ * c₂⁻¹)
  have e : GLBConj (c₁ * c₂⁻¹) (Subgroup.centralizer ({g} : Set K)) =
      Subgroup.centralizer ({z} : Set K) := by
    rw [hCg, hCz, gLBConj_gLBConj, inv_mul_cancel_left]
  rwa [e] at h

theorem exists_comp_mem_of_pow_five {z : K}
    (h360 : Nat.card (Subgroup.centralizer ({z} : Set K)) ∣ 360) {J : Subgroup K}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({z} : Set K)) J) (hJ5 : IsAltType 5 (barOf 3 J))
    {w : K} (hw : w ^ 5 = 1) (hwz : Commute w z) :
    ∃ J' : Subgroup K, GLAPComponent 3 (Subgroup.centralizer ({z} : Set K)) J' ∧
      IsAltType 5 (barOf 3 J') ∧ w ∈ J' := by
  by_cases hw1 : w = 1
  · exact ⟨J, hJ, hJ5, hw1 ▸ J.one_mem⟩
  have hwo : orderOf w = 5 := orderOf_eq_prime hw hw1
  set C := Subgroup.centralizer ({z} : Set K) with hC
  have hwC : w ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hwz.eq
  have hJC : J ≤ C := hJ.1
  have h60 : 60 ∣ Nat.card J := by
    obtain ⟨eJ⟩ := hJ5
    have h1 : Nat.card (barOf 3 J) ∣ Nat.card J := Subgroup.index_dvd_card (H := GLAPPrimeCore 3 ↥J)
    rwa [Nat.card_congr eJ.toEquiv, Inputs256b.card_alt5] at h1
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 5 (dvd_trans (by norm_num) h60)
  set w' : ↥C := ⟨w, hwC⟩ with hw'
  set q' : ↥C := ⟨q, hJC q.2⟩ with hq'
  have hw'o : orderOf w' = 5 := by rw [hw', Subgroup.orderOf_mk]; exact hwo
  have hq'o : orderOf q' = 5 := by
    rw [hq', Subgroup.orderOf_mk, ← hq, Subgroup.orderOf_coe]
  have hfac : (Nat.card ↥C).factorization 5 = 1 :=
    factorization_five_eq_one h360 (hw'o ▸ orderOf_dvd_natCard w')
  have hQ : Nat.card (Subgroup.zpowers q') = 5 ^ (Nat.card ↥C).factorization 5 := by
    rw [Nat.card_zpowers, hq'o, hfac, pow_one]
  have hWp : IsPGroup 5 (Subgroup.zpowers w') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw'o, pow_one])
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hQ hWp
  obtain ⟨u, hu, huw⟩ := hc (Subgroup.mem_zpowers w')
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at huw
  have hwK : w = (c : K) * q ^ m * (c : K)⁻¹ := by
    have := congrArg Subtype.val huw
    simpa [hw', hq'] using this.symm
  refine ⟨GLBConj (c : K)⁻¹ J, ?_, isAltType_barOf_gLBConj _ hJ5, ?_⟩
  · have h := glaPComponent_gLBConj hJ (c : K)⁻¹
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (C.inv_mem c.2))] at h
  · rw [mem_gLBConj, inv_inv, hwK]
    have : (c : K)⁻¹ * ((c : K) * (q : K) ^ m * (c : K)⁻¹) * (c : K) = ((q ^ m : ↥J) : K) := by
      rw [Subgroup.coe_zpow]
      group
    rw [this]
    exact (q ^ m).2

end Generic

section Abstract

@[expose] def Gen5Model (K : Type*) [Group K] : Prop :=
  ∃ e₁ e₂ : K, e₁ ^ 3 = 1 ∧ e₂ ^ 3 = 1 ∧ Commute e₁ e₂ ∧
    Nat.card (Subgroup.closure ({e₁, e₂} : Set K)) = 9 ∧
    (∀ ε ∈ Subgroup.closure ({e₁, e₂} : Set K), ε ≠ 1 →
      ∃ c : K, ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ c * e₁ ^ s * c⁻¹ = ε) ∧
    Subgroup.closure {w : K | w ^ 5 = 1 ∧
      ∃ ε ∈ Subgroup.closure ({e₁, e₂} : Set K), ε ≠ 1 ∧ Commute w ε} = ⊤

theorem Gen5Model.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (f : K ≃* K') (h : Gen5Model K) :
    Gen5Model K' := by
  obtain ⟨e₁, e₂, he₁, he₂, he, hE9, hcls, hW⟩ := h
  have hmapE : (Subgroup.closure ({e₁, e₂} : Set K)).map f.toMonoidHom =
      Subgroup.closure ({f e₁, f e₂} : Set K') := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  refine ⟨f e₁, f e₂, by rw [← map_pow, he₁, map_one], by rw [← map_pow, he₂, map_one], he.map f, ?_, ?_, ?_⟩
  · rw [← hmapE, Subgroup.card_map_of_injective f.injective, hE9]
  · intro ε' hε' hε'1
    rw [← hmapE] at hε'
    obtain ⟨ε, hε, rfl⟩ := hε'
    have hε1 : ε ≠ 1 := fun h1 => hε'1 (by rw [h1]; exact map_one _)
    obtain ⟨c, s, hs, hc⟩ := hcls ε hε hε1
    refine ⟨f c, s, hs, ?_⟩
    rw [← hc]
    simp only [map_mul, map_pow, map_inv, MulEquiv.coe_toMonoidHom]
  · rw [eq_top_iff]
    have h1 : (Subgroup.closure {w : K | w ^ 5 = 1 ∧
        ∃ ε ∈ Subgroup.closure ({e₁, e₂} : Set K), ε ≠ 1 ∧ Commute w ε}).map f.toMonoidHom ≤
        Subgroup.closure {w : K' | w ^ 5 = 1 ∧
          ∃ ε ∈ Subgroup.closure ({f e₁, f e₂} : Set K'), ε ≠ 1 ∧ Commute w ε} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨w, ⟨hw5, ε, hε, hε1, hwε⟩, rfl⟩
      refine ⟨by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hw5, map_one], f ε,
        hmapE ▸ Subgroup.mem_map_of_mem _ hε, fun h1 => hε1 (f.injective (h1.trans (map_one f).symm)),
        hwε.map f⟩
    rw [hW, Subgroup.map_top_of_surjective _ f.surjective] at h1
    exact h1

variable {K : Type} [Group K] [Finite K]

theorem kstar_a5Comps_eq_top (hZ : Subgroup.center K = ⊥)
    (hinn : ∀ α : MulAut K, α ^ 3 = 1 → ∃ g : K, MulAut.conj g = α)
    (h360 : ∀ z : K, orderOf z = 3 → Nat.card (Subgroup.centralizer ({z} : Set K)) ∣ 360)
    (h9 : (Nat.card K).factorization 3 = 2) (hM : Gen5Model K)
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L))
    {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) :
    Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) Inputs256b.a5Comps = ⊤ := by
  obtain ⟨e₁, e₂, he₁, he₂, he, hE9, hcls, hW⟩ := hM
  have hinj := conj_injective hZ
  obtain ⟨g, rfl⟩ := hinn x (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hg : orderOf g = 3 := by rw [← orderOf_injective _ hinj g]; exact hx
  rw [fixedSub_conj] at hL
  have hLg : L ≤ Subgroup.centralizer ({g} : Set K) := hL.1
  have hyg : Commute y g := Subgroup.mem_centralizer_singleton_iff.1 (hLg hyL)
  have hyz := not_mem_zpowers_of_mem_comp hLg hL5 hyL hy
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    omega
  set P := Subgroup.closure ({g, y} : Set K) with hP
  have hP9 : Nat.card P = 9 := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine
    (by rw [← hg]; exact pow_orderOf_eq_one g) (by rw [← hy]; exact pow_orderOf_eq_one y) hyg.symm hg1 hyz
  set E := Subgroup.closure ({e₁, e₂} : Set K) with hE
  have hEsyl : Nat.card E = 3 ^ (Nat.card K).factorization 3 := by
    rw [hE9, h9]
    norm_num
  have hcl := fun (z : K) (hz : orderOf z = 3) => exists_conj_of_orderOf_three hEsyl hcls hz
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  obtain ⟨h, hh⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hEsyl hPp
  have hPeq : P = E.map (MulAut.conj h).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hh
      (le_of_eq (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hE9, hP9]))
  have hA : Prop1310a5b.Agrp (MulAut.conj g) y = P.map (MulAut.conj : K →* MulAut K) := by
    rw [Prop1310a5b.Agrp, hP, MonoidHom.map_closure, Set.image_pair]
  have hcube : ∀ ε ∈ E, ε ^ 3 = 1 := by
    intro ε hε
    obtain ⟨i, j, -, -, rfl⟩ :=
      CFSG.RankThree.Asc83Table.E9Basis.exists_pow_mul_pow ⟨e₁, e₂, he₁, he₂, he, hE9⟩ hε
    have h1 : (e₁ ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, he₁, one_pow]
    have h2 : (e₂ ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, he₂, one_pow]
    rw [(he.pow_pow i j).mul_pow, h1, h2, one_mul]
  have key : ∀ w ∈ {w : K | w ^ 5 = 1 ∧ ∃ ε ∈ E, ε ≠ 1 ∧ Commute w ε},
      (MulAut.conj h).toMonoidHom w ∈ Prop1310a5b.Kstar (Prop1310a5b.Agrp (MulAut.conj g) y)
        Inputs256b.a5Comps := by
    rintro w ⟨hw5, ε, hεE, hε1, hwε⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hzP : h * ε * h⁻¹ ∈ P := by
      rw [hPeq]
      exact ⟨ε, hεE, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hz1 : h * ε * h⁻¹ ≠ 1 := by
      intro h1
      apply hε1
      calc ε = h⁻¹ * (h * ε * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    have hz3 : orderOf (h * ε * h⁻¹) = 3 := by
      refine orderOf_eq_prime ?_ hz1
      rw [show (h * ε * h⁻¹) ^ 3 = (MulAut.conj h) (ε ^ 3) by simp [MulAut.conj_apply, conj_pow],
        hcube ε hεE, map_one]
    obtain ⟨J, hJ, hJ5⟩ := exists_comp_of_orderOf_three he₁ hcl hg hL hL5 hz3
    have hw5' : (h * w * h⁻¹) ^ 5 = 1 := by
      rw [show (h * w * h⁻¹) ^ 5 = (MulAut.conj h) (w ^ 5) by simp [MulAut.conj_apply, conj_pow], hw5,
        map_one]
    have hcomm : Commute (h * w * h⁻¹) (h * ε * h⁻¹) := by
      have := hwε.map (MulAut.conj h)
      simpa only [MulAut.conj_apply] using this
    obtain ⟨J', hJ', hJ'5, hwJ'⟩ := exists_comp_mem_of_pow_five (h360 _ hz3) hJ hJ5 hw5' hcomm
    have haA : MulAut.conj (h * ε * h⁻¹) ∈ Prop1310a5b.Agrp (MulAut.conj g) y := by
      rw [hA]
      exact Subgroup.mem_map_of_mem _ hzP
    have ha1 : MulAut.conj (h * ε * h⁻¹) ≠ 1 := fun h1 => hz1 (hinj (h1.trans (map_one _).symm))
    have hJ'' : J' ∈ Inputs256b.a5Comps (MulAut.conj (h * ε * h⁻¹)) :=
      ⟨by rw [fixedSub_conj]; exact hJ', hJ'5⟩
    exact le_kstar haA ha1 hJ'' hwJ'
  rw [eq_top_iff]
  have hle : (Subgroup.closure {w : K | w ^ 5 = 1 ∧ ∃ ε ∈ E, ε ≠ 1 ∧ Commute w ε}).map
      (MulAut.conj h).toMonoidHom ≤
      Prop1310a5b.Kstar (Prop1310a5b.Agrp (MulAut.conj g) y) Inputs256b.a5Comps := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro w hw
    exact key w hw
  rw [hW, Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective] at hle
  exact hle

end Abstract

section Check

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen

variable {n : ℕ}

theorem rep_prodN {gs : Array (Array ℕ)} {G : ℕ → Equiv.Perm (Fin n)} {m : ℕ}
    (hG : ∀ j < m, Rep n gs[j]! (G j)) :
    ∀ w : List ℕ, (w.all fun j => decide (j < m)) = true → Rep n (prodN n gs w) (w.map G).prod
  | [], _ => by simpa [prodN] using (rep_idA (n := n))
  | j :: w, hw => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [prodN, List.map_cons, List.prod_cons]
    exact rep_compA (hG j hw.1) (rep_prodN hG w hw.2)

theorem gen5Model_of_check {tA tB : Array ℕ} {A B : Equiv.Perm (Fin n)} (hA : Rep n tA A) (hB : Rep n tB B)
    {X : Subgroup (Equiv.Perm (Fin n))} (hX : Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin n))) = X)
    {e1W e2W : List ℕ} {cls : List (ℕ × ℕ × ℕ × List ℕ)} {wW : List (List ℕ)} {wP : List (ℕ × ℕ)}
    {aW bW : List ℕ} (h : gen5Check n tA tB e1W e2W cls wW wP aW bW = true) : Gen5Model ↥X := by
  simp only [gen5Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hlet⟩, he9⟩, hpairs⟩, hcls⟩, hwlet⟩, hwlen⟩, hsig⟩, hablet⟩, haeq⟩, hbeq⟩ := h
  set G : ℕ → Equiv.Perm (Fin n) := fun j => if j = 0 then A else B with hGdef
  have hG : ∀ j < 2, Rep n (#[tA, tB] : Array (Array ℕ))[j]! (G j) := by
    intro j hj
    interval_cases j
    · simpa [hGdef] using hA
    · simpa [hGdef] using hB
  have hGX : ∀ j, G j ∈ X := by
    intro j
    rw [← hX]
    by_cases hj : j = 0
    · simp only [hGdef, hj, if_true]
      exact Subgroup.subset_closure (by simp)
    · simp only [hGdef, hj, if_false]
      exact Subgroup.subset_closure (by simp)
  have hwordX : ∀ w : List ℕ, (w.map G).prod ∈ X := fun w =>
    list_prod_mem fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact hGX j
  rw [List.all_append, Bool.and_eq_true] at hlet
  have hr1 := rep_prodN hG e1W hlet.1
  have hr2 := rep_prodN hG e2W hlet.2
  set E1 : ↥X := ⟨(e1W.map G).prod, hwordX e1W⟩ with hE1def
  set E2 : ↥X := ⟨(e2W.map G).prod, hwordX e2W⟩ with hE2def
  have hcard : Nat.card (Subgroup.closure ({E1, E2} : Set ↥X)) = 9 :=
    card_closure_of_e9Check (g₁ := E1) (g₂ := E2) hr1 hr2 he9
  simp only [e9Check, Bool.and_eq_true, Bool.not_eq_true'] at he9
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h13⟩, h23⟩, hc12⟩, -⟩, -⟩, -⟩, -⟩ := he9
  have hE1 : E1 ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN hr1 3) rep_idA h13)
  have hE2 : E2 ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN hr2 3) rep_idA h23)
  have hE12 : Commute E1 E2 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_comm_of_commN hr1 hr2 hc12)
  have hpEX : ∀ ab : ℕ × ℕ, E1 ^ ab.1 * E2 ^ ab.2 ∈ Subgroup.closure ({E1, E2} : Set ↥X) := fun ab =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  refine ⟨E1, E2, hE1, hE2, hE12, hcard, ?_, ?_⟩
  ·
    intro ε hε hε1
    obtain ⟨i, j, hi, hj, rfl⟩ :=
      CFSG.RankThree.Asc83Table.E9Basis.exists_pow_mul_pow ⟨E1, E2, hE1, hE2, hE12, hcard⟩ hε
    have hij : (i, j) ∈ e9Pairs := by
      have h00 : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨rfl, rfl⟩
        exact hε1 (by simp)
      interval_cases i <;> interval_cases j <;> first | exact absurd ⟨rfl, rfl⟩ h00 | decide
    rw [← beq_iff_eq.1 hpairs] at hij
    obtain ⟨t, ht, hteq⟩ := List.mem_map.1 hij
    have hct := List.all_eq_true.1 hcls t ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hct
    obtain ⟨⟨hclet, hs⟩, hceq⟩ := hct
    have hrc := rep_prodN hG t.2.2.2 hclet
    obtain ⟨hti, htj⟩ := Prod.mk.inj hteq
    subst hti htj
    refine ⟨⟨(t.2.2.2.map G).prod, hwordX _⟩, t.2.2.1, hs, Subtype.ext ?_⟩
    have hperm := eq_of_eqA (rep_compA hrc (rep_powN hr1 _)) (rep_compA (rep_pN hr1 hr2 _) hrc) hceq
    dsimp only at hperm
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_mk, hE1def, hE2def]
    rw [hperm]
    group
  ·
    have hlen : wP.length = wW.length := beq_iff_eq.1 hwlen
    have hwsz : ((wW.map (prodN n #[tA, tB])).toArray).size = wW.length := by simp
    set Wp : ℕ → Equiv.Perm (Fin n) := fun i => ((wW[i]!).map G).prod with hWp
    have hrW : ∀ i < wW.length, Rep n ((wW.map (prodN n #[tA, tB])).toArray)[i]! (Wp i) := by
      intro i hi
      have hmem : wW[i]! ∈ wW := by
        rw [getElem!_pos wW i hi]
        exact List.getElem_mem hi
      have hr := rep_prodN hG (wW[i]!) (List.all_eq_true.1 hwlet _ hmem)
      have e : ((wW.map (prodN n #[tA, tB])).toArray)[i]! = prodN n #[tA, tB] (wW[i]!) := by
        simp [getElem!_pos, hi]
      rw [e]
      exact hr
    have hWS : ∀ i < wW.length, (⟨Wp i, hwordX _⟩ : ↥X) ∈ {w : ↥X | w ^ 5 = 1 ∧
        ∃ ε ∈ Subgroup.closure ({E1, E2} : Set ↥X), ε ≠ 1 ∧ Commute w ε} := by
      intro i hi
      have hi' : i < ((wW.map (prodN n #[tA, tB])).toArray).size := by rw [hwsz]; exact hi
      have hsi := allLt_spec hsig hi'
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hsi
      obtain ⟨⟨⟨hpow, -⟩, hcomm⟩, hp1⟩ := hsi
      have h5 : (wW.map fun _ => (5 : ℕ)).getD i 0 = 5 := by simp [hi]
      rw [h5] at hpow
      have hrp := rep_pN hr1 hr2 (wP.getD i (0, 0))
      refine ⟨Subtype.ext ?_, E1 ^ (wP.getD i (0, 0)).1 * E2 ^ (wP.getD i (0, 0)).2, hpEX _, ?_, ?_⟩
      · rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact eq_of_eqA (rep_powN (hrW i hi) 5) rep_idA hpow
      · intro h1
        have h1' : (e1W.map G).prod ^ (wP.getD i (0, 0)).1 * (e2W.map G).prod ^ (wP.getD i (0, 0)).2 = 1 := by
          have := congrArg Subtype.val h1
          simpa [hE1def, hE2def, Subgroup.coe_mk] using this
        rw [(eqA_iff hrp rep_idA).2 h1'] at hp1
        exact Bool.noConfusion hp1
      · exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_mk, hE1def, hE2def]
          exact mul_comm_of_commN (hrW i hi) hrp hcomm)
    rw [List.all_append, Bool.and_eq_true] at hablet
    have hAeq : (aW.map Wp).prod = A := eq_of_eqA (rep_prodN hrW aW hablet.1) hA haeq
    have hBeq : (bW.map Wp).prod = B := eq_of_eqA (rep_prodN hrW bW hablet.2) hB hbeq
    set S := {w : ↥X | w ^ 5 = 1 ∧ ∃ ε ∈ Subgroup.closure ({E1, E2} : Set ↥X), ε ≠ 1 ∧ Commute w ε}
      with hS
    have hwmap : ∀ v : List ℕ, (v.all fun j => decide (j < wW.length)) = true →
        (v.map Wp).prod ∈ (Subgroup.closure S).map X.subtype := by
      intro v hv
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, hiv, rfl⟩ := List.mem_map.1 hx
      have hi : i < wW.length := of_decide_eq_true (List.all_eq_true.1 hv i hiv)
      exact ⟨⟨Wp i, hwordX _⟩, Subgroup.subset_closure (hWS i hi), rfl⟩
    have hT : Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin n))) ≤ (Subgroup.closure S).map X.subtype := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · rw [← hAeq]
        exact hwmap aW hablet.1
      · rw [← hBeq]
        exact hwmap bW hablet.2
    rw [hX] at hT
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, hy, hyx⟩ := hT x.2
    rwa [show x = y from Subtype.ext hyx.symm]

theorem isInvA_of_gen5Check {tA tB : Array ℕ} {e1W e2W : List ℕ} {cls : List (ℕ × ℕ × ℕ × List ℕ)}
    {wW : List (List ℕ)} {wP : List (ℕ × ℕ)} {aW bW : List ℕ}
    (h : gen5Check n tA tB e1W e2W cls wW wP aW bW = true) :
    isInvA n tA (invCand n tA) = true ∧ isInvA n tB (invCand n tB) = true := by
  simp only [gen5Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hA, hB⟩

end Check

section Models

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem gen5Model_m23 : Gen5Model ↥CFSG.Blueprint.NativeSporadic.M23 :=
  gen5Model_of_check rep_m23A rep_m23B rfl Certificates.certificate256301

theorem gen5Model_hs : Gen5Model ↥CFSG.RankThree.Native.hs100P := by
  have h : hsGen5Check = true := Certificates.certificate256302
  obtain ⟨hA, hB⟩ := isInvA_of_gen5Check h
  exact gen5Model_of_check (rep_permOfArr hA).1 (rep_permOfArr hB).1 rfl h

theorem card_centralizer_dvd_of_check (D : B3S3.Data) (hD : B3S3.check D = true) {A B : Equiv.Perm (Fin D.n)}
    (hA : Rep D.n D.A A) (hB : Rep D.n D.B B) {m : ℕ} (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ m)
    {Q : Type} [Group Q] (φ : Q ≃* ↥(Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin D.n))))) {z : Q}
    (hz : orderOf z = 3) : Nat.card (Subgroup.centralizer ({z} : Set Q)) ∣ m := by
  obtain ⟨-, hcls⟩ := B3S3.check_card_order_sound D hA hB hD
  have hx3 : orderOf ((φ z : ↥(Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin D.n))))) :
      Equiv.Perm (Fin D.n)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hz
  obtain ⟨c, hc, hcc⟩ := hcls _ (φ z).2 hx3
  have h1 : Nat.card (Subgroup.centralizer ({z} : Set Q)) =
      Nat.card (Subgroup.centralizer ({φ z} : Set ↥(Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin D.n)))))) := by
    rw [← map_centralizer_mulEquiv φ z, Subgroup.card_map_of_injective φ.injective]
  have h2 : Nat.card (Subgroup.centralizer
      ({φ z} : Set ↥(Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin D.n)))))) =
      Nat.card ↥(Subgroup.centralizer ({((φ z : ↥(Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin D.n))))) :
        Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
          Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin D.n)))) := by
    rw [← map_centralizer_subtype, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [h1, h2, hcc]
  exact hsmall c hc

noncomputable def quotCenterEquiv {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    K ≃* K ⧸ Subgroup.center K :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem exists_conj_of_outer_le_two {K : Type} [Group K] [Finite K] (hZ : Subgroup.center K = ⊥)
    (hout : Nat.card (Outer K) ≤ 2) (α : MulAut K) (hα : α ^ 3 = 1) : ∃ g : K, MulAut.conj g = α := by
  obtain ⟨s, hs, -⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hZ hout α hα
  exact ⟨s, hs⟩

variable {K : Type} [Group K] [Finite K]

theorem kstar_a5Comps_eq_top_m23
    (hq : CFSG.Open.IsQuasisimple K) (hs : IsSporType .M23 (K ⧸ Subgroup.center K))
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L))
    {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) :
    Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) Inputs256b.a5Comps = ⊤ := by
  obtain ⟨f⟩ := hs
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have e : K ⧸ Subgroup.center K ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := f.trans b.symm
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  have hZ : Subgroup.center K = ⊥ := Subgroup.card_eq_one.1
    (CFSG.Sporadic.Recognition.M23Multiplier.card_center_eq_one_of_certificate inferInstance e)
  have φ : K ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := (quotCenterEquiv hZ).trans e
  have hout : Nat.card (Outer K) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.at_m23_schreier.1 φ
  have h360 : ∀ z : K, orderOf z = 3 → Nat.card (Subgroup.centralizer ({z} : Set K)) ∣ 360 :=
    fun z hz => card_centralizer_dvd_of_check B3S3.m23S3Data Certificates.certificate13511.2.2.2
      rep_m23A rep_m23B (by decide +kernel) φ hz
  have h9 : (Nat.card K).factorization 3 = 2 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.m23_card,
      show (10200960 : ℕ) = 3 ^ 2 * 1133440 by norm_num,
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
  exact kstar_a5Comps_eq_top hZ (exists_conj_of_outer_le_two hZ hout) h360 h9
    (gen5Model_m23.of_mulEquiv φ.symm) hx hL hL5 hyL hy

theorem kstar_a5Comps_eq_top_hs
    (hq : CFSG.Open.IsQuasisimple K) (hcore : GLAPPrimeCore 3 K = ⊥)
    (hs : IsSporType .HS (K ⧸ Subgroup.center K))
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L))
    {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) :
    Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) Inputs256b.a5Comps = ⊤ := by
  obtain ⟨f⟩ := hs
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.HS := f.trans b.symm
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  have hZ : Subgroup.center K = ⊥ := by
    have h2 := CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate inferInstance e
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_three hcore).exists_card_eq
    rw [hk] at h2
    have hk0 : k = 0 := by
      by_contra hk0
      have := Nat.le_self_pow hk0 3
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  have φ₀ : K ≃* CFSG.Blueprint.NativeSporadic.HS := (quotCenterEquiv hZ).trans e
  have hout : Nat.card (Outer K) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      (φ₀.trans CFSG.Sporadic.Schreier.hsPermEquiv)
  have hD := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := B3S3.check_valid hD
  have h360 : ∀ z : K, orderOf z = 3 → Nat.card (Subgroup.centralizer ({z} : Set K)) ∣ 360 :=
    fun z hz => card_centralizer_dvd_of_check B3S3.hsS3Data hD (CFSG.RankThree.Native.rep_of_validA hvA)
      (CFSG.RankThree.Native.rep_of_validA hvB) (by decide +kernel)
      (φ₀.trans CFSG.Sporadic.Schreier.hsPermEquiv) hz
  have φ : K ≃* ↥CFSG.RankThree.Native.hs100P := φ₀.trans CFSG.RankThree.Native.hs100Equiv
  have h9 : (Nat.card K).factorization 3 = 2 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.RankThree.Native.card_hs100P,
      show (44352000 : ℕ) = 3 ^ 2 * 4928000 by norm_num,
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
  exact kstar_a5Comps_eq_top hZ (exists_conj_of_outer_le_two hZ hout) h360 h9
    (gen5Model_hs.of_mulEquiv φ.symm) hx hL hL5 hyL hy

end Models

theorem inputGen2324c_holds :
    Inputs256b.InputGen2324c := by
  intro K _ _ hq hcore hs x hx L hL hL5 y hyL hy
  rcases hs with hs | hs
  · exact kstar_a5Comps_eq_top_hs hq hcore hs hx hL hL5 hyL hy
  · exact kstar_a5Comps_eq_top_m23 hq hs hx hL hL5 hyL hy

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

end
