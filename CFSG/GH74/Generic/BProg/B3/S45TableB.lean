module

public import CFSG.GH74.Generic.BProg.B3.S45TableA
public import CFSG.GH74.Generic.BProg.B3.L2CompQuasi
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.BProg.B3.L2CompOrders
public import CFSG.GH74.Generic.S45.LPsl2Cover
public import CFSG.GH74.Generic.S45.LSporMathA

public section

namespace CFSG.GH74.Generic.BProg.B3.S45TableB

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GH74.Generic.BProg.B3.S45TableA
open scoped MatrixGroups

theorem datum_quotient {X : Type} [Group X] [Finite X] (hKp : Group.IsPerfect X) {y : MulAut X}
    (hy : orderOf y = 2) (hd : Datum X y) :
    ∃ yb : MulAut (X ⧸ center X), yb ≠ 1 ∧ yb * yb = 1 ∧ Datum (X ⧸ center X) yb := by
  obtain ⟨yb, hyb, hyb1, hyb2⟩ := S45.LAlt.exists_induced_quotient hKp y hy
  obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨hQs, hQn, -, -⟩ := S45.LAlt.hasL2Model_data hQ
  refine ⟨yb, hyb1, hyb2, V, Q, inferInstance, inferInstance, (QuotientGroup.mk' (center X)).comp π, ψ,
    ?_, ?_, hψ, hodd, hQ⟩
  · intro v
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hyb, hfix]
  · intro v hv
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hv
    exact MonoidHom.mem_ker.2 (psi_eq_one_of_mem_center hker hψ hQs hQn hv)

section Orders

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem range_le_fixedIn {V : Type} [Group V] {yb : MulAut S} {π : V →* S} (hfix : ∀ v, yb (π v) = π v) :
    π.range ≤ B2.fixedIn S (zpowers yb) := by
  rintro _ ⟨v, rfl⟩
  exact L2CompBasic.mem_fixedIn_zpowers_iff.2 (hfix v)

theorem false_of_m11_datum
    (hm : NativeSporadic.IsSporadic S .M11) {yb : MulAut S} (hy2 : yb * yb = 1) (hy1 : yb ≠ 1)
    (hd : Datum S yb) : False := by
  obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨-, -, -, q, hq5, -, hcard, -⟩ := S45.LAlt.hasL2Model_data hQ
  obtain ⟨e⟩ := hm
  have e' : S ≃* NativeSporadic.M11 := e
  have hα2 : MulAut.congr e' yb * MulAut.congr e' yb = 1 := by
    rw [← map_mul, hy2, map_one]
  have hα1 : MulAut.congr e' yb ≠ 1 := fun h => hy1 ((MulAut.congr e').injective (by rw [h, map_one]))
  have hC : Nat.card ↥(B2.fixedIn S (zpowers yb)) = 48 := by
    rw [← L2CompOrders.card_fixedIn_congr e' yb]
    exact S45.LAlt.m11_fixed_card _ hα2 hα1
  have h1 : Nat.card Q ∣ Nat.card π.range := card_dvd_range hker hψ
  have h2 : Nat.card π.range ∣ 48 := hC ▸ Subgroup.card_dvd_of_le (range_le_fixedIn hfix)
  have h3 : Nat.card Q ≤ 48 := Nat.le_of_dvd (by norm_num) (h1.trans h2)
  have h4 := L2CompOrders.sixty_le_card hq5 hcard
  omega

theorem false_of_sz8_datum (hm : LieModel S .twistedB2 0 2 3) {yb : MulAut S}
    (hd : Datum S yb) : False := by
  obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨-, -, -, q, hq5, -, hcard, -⟩ := S45.LAlt.hasL2Model_data hQ
  have hX : Nat.card S = 29120 := by
    rw [card_of_lieModel_twistedB2 hm]
    decide
  have h1 : Nat.card Q ∣ Nat.card π.range := card_dvd_range hker hψ
  have h2 : Nat.card π.range ∣ Nat.card S := Subgroup.card_subgroup_dvd_card π.range
  have h3 : 3 ∣ 29120 := hX ▸ (L2CompOrders.three_dvd_of_card hcard).trans (h1.trans h2)
  omega

theorem no_subgroup_168 {X : Type} [Group X] [Finite X] (hX : Nat.card X = 504) (hXs : IsSimpleGroup X)
    (P : Subgroup X) (hN : Nat.card P = 168) : False := by
  have hidx : P.index = 3 := by
    have := P.index_mul_card
    rw [hN, hX] at this
    omega
  have hfi : P.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    omega
  have hdvd := P.index_normalCore_dvd_factorial_index
  rw [hidx] at hdvd
  rcases hXs.eq_bot_or_eq_top_of_normal P.normalCore with hb | ht
  · rw [hb, Subgroup.index_bot] at hdvd
    rw [hX] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    norm_num [Nat.factorial] at this
  · have hL : P = ⊤ := top_le_iff.1 (ht ▸ P.normalCore_le)
    rw [hL, Subgroup.index_top] at hidx
    omega

theorem false_of_l28_datum (hm : LieModel S .PSL 2 2 3) (hXs : IsSimpleGroup S) {yb : MulAut S}
    (hy1 : yb ≠ 1) (hd : Datum S yb) : False := by
  obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨-, -, -, q, hq5, hqodd, hcard, -⟩ := S45.LAlt.hasL2Model_data hQ
  have hX : Nat.card S = 504 := by
    have := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hm
    rw [this]
    decide
  have h1 : Nat.card Q ∣ Nat.card π.range := card_dvd_range hker hψ
  have h2 : Nat.card π.range ∣ 504 := hX ▸ Subgroup.card_subgroup_dvd_card π.range
  have h3 : Nat.card Q ∣ 504 := h1.trans h2
  have hle : Nat.card Q ≤ 504 := Nat.le_of_dvd (by norm_num) h3
  have hq10 : q ≤ 10 := by
    by_contra hgt
    push Not at hgt
    have h4 : 120 ≤ q ^ 2 - 1 := by
      have : 121 ≤ q ^ 2 := by nlinarith
      omega
    have : 11 * 120 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hgt h4
    omega
  have hN : Nat.card Q = 168 := by
    obtain ⟨k, hk⟩ := hqodd
    have hk' : q = 5 ∨ q = 7 ∨ q = 9 := by omega
    rcases hk' with rfl | rfl | rfl
    · exfalso
      have : Nat.card Q = 60 := by norm_num at hcard; omega
      rw [this] at h3
      omega
    · norm_num at hcard
      omega
    · exfalso
      have : Nat.card Q = 360 := by norm_num at hcard; omega
      rw [this] at h3
      omega
  rw [hN] at h1
  obtain ⟨m, hm'⟩ := h1
  have hmle : Nat.card π.range ∣ 504 := h2
  have hm3 : m = 1 ∨ m = 3 := by
    have h504 : 168 * m ∣ 504 := hm' ▸ hmle
    have h168 : 168 * m ∣ 168 * 3 := by norm_num; exact h504
    have hmd : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h168
    exact (Nat.dvd_prime Nat.prime_three).1 hmd
  rcases hm3 with rfl | rfl
  · exact no_subgroup_168 hX hXs π.range (by omega)
  · apply hy1
    have hcardtop : Nat.card π.range = Nat.card S := by omega
    have htop : π.range = ⊤ := Subgroup.eq_top_of_card_eq _ hcardtop
    ext s
    have hs : s ∈ π.range := htop ▸ Subgroup.mem_top s
    obtain ⟨v, rfl⟩ := hs
    rw [hfix v]
    simp

end Orders

section Covers

theorem false_of_center_ne_bot_psl2_w {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 r f) {y : MulAut K}
    (hd : Datum K y) : False := by
  obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨hQs, hQn, -, -⟩ := S45.LAlt.hasL2Model_data hQ
  have : Finite V := finite_V ψ hψ hodd hQ
  obtain ⟨w, hw2, hψw⟩ := exists_invol_lift ψ hψ hodd hQ
  obtain ⟨F, _, _, hk, ⟨a⟩⟩ := exists_mulEquiv_sl_two_of_center_ne_bot hKp hZ2 hZ hr2 hmodel
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hvv : π w * π w = 1 := by rw [← map_mul, hww, map_one]
  have hc : a (π w) ∈ Subgroup.center SL(2, F) :=
    sl2_sq_eq_one_mem_center (Ring.two_ne_zero hk) (by rw [← map_mul, hvv, map_one])
  have hvc : π w ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply a.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc (a g)
  exact hψw (psi_eq_one_of_mem_center hker hψ hQs hQn hvc)

theorem a7_cover_involution_comm {K : Type} [Group K] [Finite K]
    (hKp : Group.IsPerfect K) (hZ2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) :
    ∀ v : K, v * v = 1 → ∀ k : K, (k * v)⁻¹ * (v * k) ∈ center K := by
  classical
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hZ (Subgroup.card_eq_one.1 (by simpa using hk))
  have hdvd : 2 ^ (k - 1) ∣ Nat.card ↥(center K) := by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(center K)) 2 (n := k - 1) hdvd
  have hWi : W.index = 2 := by
    have h1 := W.index_mul_card
    rw [hW, hk] at h1
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  let Z'' : Subgroup K := W.map (center K).subtype
  have hZ''Z : ∀ n ∈ Z'', n ∈ center K := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hZ''n : Z''.Normal := ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.1 (hZ''Z n hn) g
    have : g * n * g⁻¹ = n := by
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hc]
        _ = n := by group
    rw [this]
    exact hn⟩
  have hZ''le : Z'' ≤ center K := hZ''Z
  have hWcomm : W.Normal := inferInstance
  obtain ⟨g', hg'⟩ : ∃ g' : ↥(center K), g' ∉ W := by
    by_contra hcon
    push Not at hcon
    have : W = ⊤ := Subgroup.eq_top_iff' W |>.2 hcon
    rw [this, Subgroup.index_top] at hWi
    omega
  have hgZ'' : ((g' : ↥(center K)) : K) ∉ Z'' := by
    intro hmem
    obtain ⟨w, hw, hwg⟩ := hmem
    have hwe : w = g' := Subtype.ext hwg
    subst hwe
    exact hg' hw
  have hg2 : g' * g' ∈ W := by
    have h1 : (QuotientGroup.mk g' : ↥(center K) ⧸ W) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(center K) ⧸ W) (x := QuotientGroup.mk g')
      have hc : Nat.card (↥(center K) ⧸ W) = 2 := hWi
      rwa [hc] at this
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h1
    exact h1
  let π : K →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hπZ : Z'' ≤ π.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1
    rw [(QuotientGroup.eq_one_iff x).2 (hZ''le hx), map_one]
  let π' : K ⧸ Z'' →* alternatingGroup (Fin 7) := QuotientGroup.lift Z'' π hπZ
  have hπ'mk : ∀ x : K, π' (QuotientGroup.mk x) = e (QuotientGroup.mk x) := fun x => rfl
  let z : K ⧸ Z'' := QuotientGroup.mk (g' : K)
  have hQ2 : ∃! q : ↥(center K) ⧸ W, q ≠ 1 := (Nat.card_eq_two_iff' (1 : ↥(center K) ⧸ W)).1 hWi
  have hcov : CFSG.ClassicalInvolution.Hat2A7.IsDoubleCoverA7 π' z := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      obtain ⟨b, rfl⟩ := e.surjective a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨QuotientGroup.mk x, rfl⟩
    · have := hKp
      infer_instance
    · intro h
      exact hgZ'' ((QuotientGroup.eq_one_iff _).1 h)
    · show (QuotientGroup.mk (g' : K) : K ⧸ Z'') * QuotientGroup.mk (g' : K) = 1
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact ⟨g' * g', hg2, rfl⟩
    · intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        show (QuotientGroup.mk x : K ⧸ Z'') * QuotientGroup.mk (g' : K) =
          QuotientGroup.mk (g' : K) * QuotientGroup.mk x
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.1 g'.2 x
    · intro w
      induction w using QuotientGroup.induction_on with
      | H x =>
        rw [hπ'mk]
        have h1 : e (QuotientGroup.mk x) = 1 ↔ x ∈ center K :=
          (MulEquiv.map_eq_one_iff e).trans (QuotientGroup.eq_one_iff x)
        rw [h1]
        constructor
        · intro hx
          by_cases hxW : (⟨x, hx⟩ : ↥(center K)) ∈ W
          · left
            rw [QuotientGroup.eq_one_iff]
            exact ⟨⟨x, hx⟩, hxW, rfl⟩
          · right
            have hne1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥(center K)) : ↥(center K) ⧸ W) ≠ 1 := by
              rw [Ne, QuotientGroup.eq_one_iff]
              exact hxW
            have hne2 : (QuotientGroup.mk g' : ↥(center K) ⧸ W) ≠ 1 := by
              rw [Ne, QuotientGroup.eq_one_iff]
              exact hg'
            obtain ⟨q, -, hq⟩ := hQ2
            have heq : (QuotientGroup.mk (⟨x, hx⟩ : ↥(center K)) : ↥(center K) ⧸ W) =
                QuotientGroup.mk g' := (hq _ hne1).trans (hq _ hne2).symm
            rw [QuotientGroup.eq] at heq
            rw [show (QuotientGroup.mk x : K ⧸ Z'') = z from ?_]
            rw [QuotientGroup.eq]
            exact ⟨_, heq, rfl⟩
        · rintro (h | h)
          · exact hZ''le ((QuotientGroup.eq_one_iff x).1 h)
          · have h' := (QuotientGroup.eq).1 h
            have hxg : x = (g' : K) * (x⁻¹ * (g' : K))⁻¹ := by group
            rw [hxg]
            exact Subgroup.mul_mem _ g'.2 (Subgroup.inv_mem _ (hZ''le h'))
  intro v hv2 k
  have hmk2 : (QuotientGroup.mk v : K ⧸ Z'') * QuotientGroup.mk v = 1 := by
    rw [← QuotientGroup.mk_mul, hv2, QuotientGroup.mk_one]
  rcases hcov.eq_one_or_eq_z_of_sq_eq_one hmk2 with h | h
  · have hvZ : v ∈ center K := hZ''le ((QuotientGroup.eq_one_iff _).1 h)
    have hkv : k * v = v * k := Subgroup.mem_center_iff.1 hvZ k
    rw [hkv, inv_mul_cancel]
    exact one_mem _
  · have hc := hcov.central (QuotientGroup.mk k)
    rw [← h, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    exact hZ''le hc

theorem false_of_center_ne_bot_a7_w {K : Type} [Group K] [Finite K]
    (hKp : Group.IsPerfect K) (hZ2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) {y : MulAut K} (hd : Datum K y) : False := by
  obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨hQs, hQn, -, -⟩ := S45.LAlt.hasL2Model_data hQ
  have : Finite V := finite_V ψ hψ hodd hQ
  obtain ⟨w, hw2, hψw⟩ := exists_invol_lift ψ hψ hodd hQ
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hvv : π w * π w = 1 := by rw [← map_mul, hww, map_one]
  have hcomm := a7_cover_involution_comm hKp hZ2 hZ e (π w) hvv
  have hzc : ψ w ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨u, rfl⟩ := hψ q
    have h1 : π ((u * w)⁻¹ * (w * u)) ∈ Subgroup.center K := by
      have := hcomm (π u)
      simpa only [map_mul, map_inv] using this
    have h3 := psi_eq_one_of_mem_center hker hψ hQs hQn h1
    rw [map_mul, map_inv, map_mul, map_mul] at h3
    exact inv_mul_eq_one.1 h3
  rw [center_eq_bot_of_simple_nonab hQs hQn, Subgroup.mem_bot] at hzc
  exact hψw hzc

end Covers

theorem s45Table_proved :
    FalseCtxS45.S45Table := by
  intro X _ _ hX3 hq hZ hGH y hy hdat hab
  have hKp : Group.IsPerfect X := hq.1
  have hXb : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hXn : ∃ a b : X ⧸ center X, a * b ≠ b * a := hq.2.2
  have hrank : ∀ _ : RankCertified (X ⧸ center X) 3, False := fun h => h.not_sectionalTwoRankLE hX3
  have h5 : Hyp5w X y := ⟨hy, hab, hdat⟩
  obtain ⟨yb, hyb1, hyb2, hdb⟩ := datum_quotient hKp hy hdat
  have hTriv : center X = ⊥ → (X ⧸ center X ≃* X) := fun hZ1 =>
    (QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot
  have hTrivData : center X = ⊥ → IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := fun hZ1 => by
    have e := hTriv hZ1
    refine ⟨?_, ?_⟩
    · have := hXb
      exact e.symm.isSimpleGroup
    · obtain ⟨a, b, hab'⟩ := hXn
      exact ⟨e a, e b, fun h => hab' (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  rcases hGH with ⟨n, h7, h11, ⟨e⟩⟩ | hspor | ⟨p, f, hp, hf, hrow⟩
  · by_cases hn : n = 7
    · subst hn
      by_cases hZ1 : center X = ⊥
      · exact (false_of_alt7 ((hTriv hZ1).symm.trans e) h5).elim
      · exact (false_of_center_ne_bot_a7_w hKp hZ hZ1 e hdat).elim
    · exact (hrank ((rankCertified_alternating (by omega)).of_mulEquiv e.symm)).elim
  · rcases hspor with h | h | h | h | h | h | h | h | h
    · exact (false_of_m11_datum h hyb2 hyb1 hdb).elim
    · exact (hrank (E2.rank3_M12 h)).elim
    · exact (hrank (E2.rank3_M22 h)).elim
    · exact (hrank (E2.rank3_M23 h)).elim
    · exact Or.inr h
    · exact (hrank (E2.rank3_J2 h)).elim
    · exact (hrank (E2.rank3_J3 h)).elim
    · exact (hrank (rankCertified_of_isSporadic_McL h)).elim
    · exact (hrank (rankCertified_of_isSporadic_Ly h)).elim
  · rcases hrow with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · by_cases hZ1 : center X = ⊥
      · exact (false_of_l2 hp hp2 hf (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (hTriv hZ1) hm)
          h5).elim
      · exact (false_of_center_ne_bot_psl2_w hKp hZ hZ1 hp2 (stated_of_lieModel_PSL hm) hdat).elim
    · by_cases hZ1 : center X = ⊥
      · obtain ⟨hXs, hXn'⟩ := hTrivData hZ1
        exact (false_of_l3 hXs hXn' hp2
          (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (hTriv hZ1) hm) h5).elim
      · exact (hZ1 (L2CompQuasi.center_eq_bot_of_psl3 hKp hZ hp2 (stated_of_lieModel_PSL hm))).elim
    · by_cases hZ1 : center X = ⊥
      · exact (false_of_u3 hp2 (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (hTriv hZ1) hm) h5).elim
      · exact (hZ1 (L2CompQuasi.center_eq_bot_of_psu3 hKp hZ hp2 (stated_of_lieModel_PSU hm))).elim
    · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psp_data hm
      exact (hrank ((rankCertified_PSp4 (ringChar_ne_two_of_card_eq hp hp2 hF)).of_mulEquiv
        e.symm)).elim
    · exact (hrank (rankCertified_of_lieModel_G2 hp hp2 hm)).elim
    · exact (rank_3D4_of_lieModel hp hp2 hm hX3).elim
    · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hm
      exact (hrank ((rankCertified_PSL4 (ringChar_ne_two_of_card_eq hp hp2 hF)).of_mulEquiv
        e.symm)).elim
    · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data hm
      have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
      exact (hrank ((rankCertified_PSU4 hF hodd).of_mulEquiv e.symm)).elim
    · have hp2 : p ≠ 2 := B2.PumpupTableAux.ne_two_of_pow_mod_four hf (Or.inl hmod)
      obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hm
      exact (hrank ((rankCertified_PSL5 (ringChar_ne_two_of_card_eq hp hp2 hF)).of_mulEquiv
        e.symm)).elim
    · have hp2 : p ≠ 2 := B2.PumpupTableAux.ne_two_of_pow_mod_four hf (Or.inr hmod)
      obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data hm
      have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
      exact (hrank ((rankCertified_PSU5 hF hodd).of_mulEquiv e.symm)).elim
    · exact Or.inl ⟨f, hm⟩
    · exact (false_of_l28_datum hm hXb hyb1 hdb).elim
    · exact (hrank (E2.rank3_L2_16 hm)).elim
    · exact (hrank (E2.rank3_L3_4 hm)).elim
    · exact (hrank (E2.rank3_U3_4 hm)).elim
    · exact (false_of_sz8_datum hm hdb).elim

end CFSG.GH74.Generic.BProg.B3.S45TableB
