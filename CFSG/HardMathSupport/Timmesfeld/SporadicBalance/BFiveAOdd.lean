module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAFix
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiveOddKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMBaby

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic

section Generic

variable {G : Type*} [Group G]

theorem eq_four_of_two_pow {m : ℕ} (hm : m ≠ 0) (h7 : 2 ^ m ≤ 2 ^ 7) (h5 : 5 ∣ 2 ^ m - 1) :
    m = 4 := by
  have hm7 : m ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h7
  interval_cases m <;> simp_all

theorem twenty_le_of_two_pow {m : ℕ} (hm : m ≠ 0) (h25 : 25 ∣ 2 ^ m - 1) : 20 ≤ m := by
  by_contra hlt
  push Not at hlt
  interval_cases m <;> simp_all

theorem odd_card_gLAPPrimeCoreOf_of_five_local [Finite G] {y : G} {P : Subgroup G}
    (hP : IsPGroup 5 P) (hPc : 5 ^ 4 ≤ Nat.card P)
    (hPy : P ≤ Subgroup.centralizer ({y} : Set G)) (hyP : y ∈ P) (Q2 : G → Prop)
    (hinv : ∀ w : G, w * w = 1 → w ≠ 1 → ∀ R : Subgroup G, IsPGroup 5 R →
      R ≤ Subgroup.centralizer ({w} : Set G) → Nat.card R ≤ 5 ^ 3)
    (hnot : ∀ w : G, w * w = 1 → w ≠ 1 → ¬ Q2 w → ∀ R : Subgroup G, IsPGroup 5 R →
      R ≤ Subgroup.centralizer ({w} : Set G) → Nat.card R ≤ 5 ^ 2)
    (hb7 : ∀ w : G, Q2 w → w ∈ Subgroup.centralizer ({y} : Set G) →
      Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set G)) ⊓
        Subgroup.centralizer ({w} : Set G)) ≤ 2 ^ 7)
    (hb3 : ∀ w : G, Q2 w → w ∈ Subgroup.centralizer ({y} : Set G) → ∀ R : Subgroup G,
      IsPGroup 5 R → 125 ≤ Nat.card R → R ≤ Subgroup.centralizer ({w} : Set G) →
      R ≤ Subgroup.centralizer ({y} : Set G) → y ∈ R →
      Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set G)) ⊓
        Subgroup.centralizer ({w} : Set G)) ≤ 2 ^ 3)
    (hconj : ∀ w g : G, Q2 w → Q2 (g * w * g⁻¹)) {t : G} (htQ : Q2 t) (ht : t * t = 1)
    (hty : t ∈ Subgroup.centralizer ({y} : Set G)) :
    Odd (Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set G)))) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({y} : Set G) with hC
  set O := GLAPPrimeCoreOf 5 C with hO
  have hOC : O ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime 5 (Nat.card O) := coprime_card_GLAPPrimeCoreOf Nat.prime_five C
  have hPO : ∀ g ∈ P, ∀ x ∈ O, g * x * g⁻¹ ∈ O := fun g hg x hx =>
    GLAPPrimeCoreOf_conj_mem g (hPy hg) x hx
  obtain ⟨T, hT⟩ := exists_sylow_invariant Nat.prime_five Nat.prime_two hP hPO hcop
  set TG : Subgroup G := (T : Subgroup ↥O).map O.subtype with hTG
  have hTGcard : Nat.card TG = Nat.card (T : Subgroup ↥O) :=
    Subgroup.card_map_of_injective O.subtype_injective
  have hTGO : TG ≤ O := Subgroup.map_subtype_le _
  have hTGp : IsPGroup 2 TG := T.isPGroup'.map _
  have hTGn : ∀ g ∈ P, ∀ x ∈ TG, g * x * g⁻¹ ∈ TG := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨_, hT g hg x hx, rfl⟩
  by_cases hT1 : TG = ⊥
  · have hTc : Nat.card (T : Subgroup ↥O) = 1 := by
      rw [← hTGcard, hT1, Subgroup.card_bot]
    have hfac : (Nat.card ↥O).factorization 2 = 0 := by
      have h := Sylow.card_eq_multiplicity T
      rw [hTc] at h
      have h' : 2 ^ (Nat.card ↥O).factorization 2 = 2 ^ 0 := by rw [← h, pow_zero]
      exact Nat.pow_right_injective le_rfl h'
    have hQ0 : Nat.card ↥O ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_eq_zero_iff] at hfac
    rcases hfac with h | h | h
    · exact absurd Nat.prime_two h
    · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
    · exact absurd h hQ0
  exfalso
  have hTb : ∀ x ∈ TG, x ≠ 1 →
      Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) * 5 ^ 1 ≤ Nat.card P := by
    intro x hx hx1
    obtain ⟨m, hm⟩ := hTGp ⟨x, hx⟩
    have hxm : x ^ (2 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    obtain ⟨j, hj2, hj1⟩ := exists_involution_pow hxm hx1
    have hle : P ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({x ^ j} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
      exact (Commute.pow_right (show Commute g x from h) j).eq
    have h3 := hinv _ hj2 hj1 _ (hP.to_le inf_le_left) hle
    calc Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) * 5 ^ 1 ≤ 5 ^ 3 * 5 :=
          Nat.mul_le_mul_right _ (by simpa using h3)
      _ = 5 ^ 4 := by norm_num
      _ ≤ Nat.card P := hPc
  have hT5 := pow_dvd_card_sub_one_of_orbit Nat.prime_five hP hTGn hTb
  set Z := omegaCenter TG with hZ
  have hZT : Z ≤ TG := omegaCenter_le TG
  obtain ⟨w0, hw0Z, hw01⟩ := exists_mem_omegaCenter hTGp hT1
  have hZn : ∀ g ∈ P, ∀ x ∈ Z, g * x * g⁻¹ ∈ Z := fun g hg x hx =>
    conj_mem_omegaCenter (hTGn g hg) (fun z hz => by
      have := hTGn g⁻¹ (P.inv_mem hg) z hz
      simpa using this) hx
  have hwC : ∀ w ∈ Z, w ∈ C := fun w hw => hOC (hTGO (hZT hw))
  by_cases hcase : ∃ w ∈ Z, w ≠ 1 ∧ Q2 w
  ·
    obtain ⟨w, hwZ, hw1, hwQ⟩ := hcase
    have hTw : TG ≤ O ⊓ Subgroup.centralizer ({w} : Set G) := by
      intro x hx
      refine Subgroup.mem_inf.2 ⟨hTGO hx, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hwZ.2.1 x hx)
    have h7 := (Subgroup.card_le_of_le hTw).trans (hb7 w hwQ (hwC w hwZ))
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hTGp
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hT1
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero])
    rw [hm] at h7 hT5
    have hm4 := eq_four_of_two_pow hm0 h7 (by simpa using hT5)
    have horb := card_le_card_sub_one_mul hTGn (hZT hwZ) hw1
    rw [hm, hm4] at horb
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 (hP.to_le (inf_le_left :
      P ⊓ Subgroup.centralizer ({w} : Set G) ≤ P))
    have hR3 : 125 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set G)) := by
      rw [ha, hb] at horb
      rw [ha] at hPc
      rw [hb]
      have h4 : 4 ≤ a := (Nat.pow_le_pow_iff_right (by norm_num)).1 hPc
      have hab : a ≤ b + 1 := by
        by_contra hlt
        push Not at hlt
        have : 5 ^ (b + 2) ≤ 5 ^ a := Nat.pow_le_pow_right (by norm_num) hlt
        have : 5 ^ (b + 2) = 25 * 5 ^ b := by ring
        omega
      have : 3 ≤ b := by omega
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ 5 ^ b := Nat.pow_le_pow_right (by norm_num) this
    have hyw : y ∈ Subgroup.centralizer ({w} : Set G) := by
      have := hwC w hwZ
      rw [hC, Subgroup.mem_centralizer_singleton_iff] at this
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact this.symm
    have h3 := hb3 w hwQ (hwC w hwZ) _ (hP.to_le inf_le_left) hR3 inf_le_right
      (inf_le_left.trans hPy) ⟨hyP, hyw⟩
    have h3' := (Subgroup.card_le_of_le hTw).trans h3
    rw [hm, hm4] at h3'
    norm_num at h3'
  ·
    push Not at hcase
    have hZb : ∀ x ∈ Z, x ≠ 1 →
        Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) * 5 ^ 2 ≤ Nat.card P := by
      intro x hx hx1
      have h2 := hnot x hx.2.2 hx1 (hcase x hx hx1) _ (hP.to_le inf_le_left) inf_le_right
      calc Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) * 5 ^ 2 ≤ 5 ^ 2 * 5 ^ 2 :=
            Nat.mul_le_mul_right _ h2
        _ = 5 ^ 4 := by norm_num
        _ ≤ Nat.card P := hPc
    have hZ25 := pow_dvd_card_sub_one_of_orbit Nat.prime_five hP hZn hZb
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (hTGp.to_le hZT)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      have hZbot := Subgroup.eq_bot_of_card_eq Z hm
      have hw0 : w0 ∈ (⊥ : Subgroup G) := hZbot ▸ hw0Z
      exact hw01 (Subgroup.mem_bot.1 hw0)
    rw [hm] at hZ25
    have hm20 := twenty_le_of_two_pow hm0 (by simpa using hZ25)
    have htO : ∀ x ∈ O, t * x * t⁻¹ ∈ O := fun x hx => GLAPPrimeCoreOf_conj_mem t hty x hx
    obtain ⟨T2, hT2⟩ := exists_sylow_normalized_of_involution ht htO
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥O T T2
    have hmemT2 : ∀ x : ↥O, x ∈ (T2 : Subgroup ↥O) ↔ g⁻¹ * x * g ∈ (T : Subgroup ↥O) := by
      intro x
      have e : ((T2 : Sylow 2 ↥O) : Subgroup ↥O) = ((g • T : Sylow 2 ↥O) : Subgroup ↥O) := by
        rw [hg]
      rw [e, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    set t' : G := (g : G)⁻¹ * t * g with ht'
    have ht'2 : t' * t' = 1 := by
      calc t' * t' = (g : G)⁻¹ * (t * t) * g := by rw [ht']; group
        _ = 1 := by rw [ht]; group
    have ht'Q : Q2 t' := by
      have := hconj t (g : G)⁻¹ htQ
      simpa [ht'] using this
    have ht'y : t' ∈ C := by
      have hgC : (g : G) ∈ C := hOC g.2
      exact C.mul_mem (C.mul_mem (C.inv_mem hgC) hty) hgC
    have ht'T : ∀ x ∈ TG, t' * x * t'⁻¹ ∈ TG := by
      rintro _ ⟨x, hx, rfl⟩
      have hx2 : g * x * g⁻¹ ∈ (T2 : Subgroup ↥O) := by
        rw [hmemT2]
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e]
        exact hx
      have hx3 := hT2 _ hx2
      rw [hmemT2] at hx3
      refine ⟨_, hx3, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ht']
      group
    have ht'i : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
    have ht'Z : ∀ x ∈ Z, t' * x * t'⁻¹ ∈ Z := fun x hx =>
      conj_mem_omegaCenter ht'T (fun z hz => by
        have := ht'T z hz
        rw [ht'i] at this ⊢
        exact this) hx
    have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => (hb.2.1 a (hZT ha))
    have hZ2 : ∀ a ∈ Z, a * a = 1 := fun a ha => ha.2.2
    have hsq := card_le_sq_of_involution hZab hZ2 ht'2 ht'Z
    have hZC : Z ⊓ Subgroup.centralizer ({t'} : Set G) ≤
        O ⊓ Subgroup.centralizer ({t'} : Set G) :=
      inf_le_inf_right _ (hZT.trans hTGO)
    have h7 := (Subgroup.card_le_of_le hZC).trans (hb7 t' ht'Q ht'y)
    have h14 : Nat.card Z ≤ (2 ^ 7) ^ 2 := hsq.trans (Nat.pow_le_pow_left h7 2)
    rw [hm] at h14
    have : 2 ^ 20 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm20
    norm_num at h14
    omega

end Generic

section Classes

theorem card_isPGroup_five_le_of_babyInv_ne_one {k : Fin 4} (hk : k ≠ 1) {t : B}
    (ht : BabyInv k t) {Q : Subgroup B} (hQ : IsPGroup 5 Q)
    (hle : Q ≤ Subgroup.centralizer ({t} : Set B)) : Nat.card Q ≤ 5 ^ 2 := by
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [ht.2] at hdvd
  refine card_le_of_isPGroup_of_dvd (by norm_num) hQ ?_ hdvd
  fin_cases k <;> simp_all [babyCentOrder]

theorem babyInv_one_conj {w : B} (hw : BabyInv 1 w) (g : B) : BabyInv 1 (g * w * g⁻¹) :=
  ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hw.1,
    (CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩)).symm.trans
      hw.2⟩

end Classes

section B


theorem odd_card_gLAPPrimeCoreOf_B_five {y : B} (hy : orderOf y = 5) {P : Subgroup B}
    (hP : IsPGroup 5 P) (hPc : 5 ^ 4 ≤ Nat.card P) (hPy : P ≤ Subgroup.centralizer ({y} : Set B))
    (hyP : y ∈ P) {t : B} (ht : BabyInv 1 t) (hty : t ∈ Subgroup.centralizer ({y} : Set B)) :
    Odd (Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)))) := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hinv2 : ∀ w : B, w * w = 1 → w ≠ 1 → orderOf w = 2 := fun w hw hw1 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hw) hw1
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.1, sq] at this
  refine odd_card_gLAPPrimeCoreOf_of_five_local hP hPc hPy hyP (BabyInv 1) ?_ ?_
    (fun w hw hwy => card_gLAPPrimeCoreOf_inf_centralizer_le hw hy hwy)
    (fun w hw hwy R hR hRc hRw hRy hyR =>
      card_gLAPPrimeCoreOf_inf_centralizer_le_of_central hw hy hwy hR hRc hRw hRy hyR)
    (fun w g hw => babyInv_one_conj hw g) ht htt hty
  · intro w hw hw1 R hR hle
    obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 w (hinv2 w hw hw1)
    exact card_isPGroup_five_le_of_babyInv hk hR hle
  · intro w hw hw1 hnot R hR hle
    obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 w (hinv2 w hw hw1)
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hnot hk
    exact card_isPGroup_five_le_of_babyInv_ne_one hk1 hk hR hle

end B

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
