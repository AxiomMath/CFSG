module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.Sporadic.ON
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant
  isoInvariant_card_quotient_center)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_fixed_of_central_two_kernel {L S : Type*} [Group L] [Finite L] [Group S]
    (π : L →* S) (hπ : Function.Surjective π) (hc : π.ker ≤ center L) (h2 : IsPGroup 2 π.ker)
    (γ : MulAut L) (γbar : S →* S) (hcompat : ∀ x, π (γ x) = γbar (π x)) {y : S}
    (hy : γbar y = y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : orderOf y = r) :
    ∃ x : L, γ x = x ∧ orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, rfl⟩ := hπ y
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h2
  have hker : x₀ ^ r ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, ← hyr, pow_orderOf_eq_one]
  have hxr : (x₀ ^ Nat.card π.ker) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x₀ ^ r, hker⟩ : π.ker)))
  have hyk : π x₀ ^ Nat.card π.ker ≠ 1 := by
    intro h1
    have h := orderOf_dvd_of_pow_eq_one h1
    rw [hyr, hj] at h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  set x := x₀ ^ Nat.card π.ker with hxdef
  have hx1 : x ≠ 1 := fun h => hyk (by rw [← map_pow, ← hxdef, h, map_one])
  refine ⟨x, ?_, orderOf_eq_prime hxr hx1⟩
  set q := γ x * x⁻¹ with hqdef
  have hq : q ∈ π.ker := by
    rw [MonoidHom.mem_ker, hqdef, map_mul, map_inv, hcompat, hxdef, map_pow, map_pow, hy,
      mul_inv_cancel]
  have hγx : γ x = q * x := by rw [hqdef, inv_mul_cancel_right]
  have hqr : q ^ r = 1 := by
    have h1 : (γ x) ^ r = 1 := by rw [← map_pow, hxr, map_one]
    have hcomm : Commute q x := (mem_center_iff.1 (hc hq) x).symm
    rw [hγx, hcomm.mul_pow, hxr, mul_one] at h1
    exact h1
  have hq1 : q = 1 := by
    obtain ⟨i, hi⟩ := h2 ⟨q, hq⟩
    have hd1 : orderOf q ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hi)
    have hd2 : orderOf q ∣ r := orderOf_dvd_of_pow_eq_one hqr
    have hcop : Nat.Coprime (2 ^ i) r :=
      Nat.Coprime.pow_left i ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rw [hγx, hq1, one_mul]

section OuterRoot

variable {D : Type} [Group D] {n : ℕ} {α : MulAut D} {S : Subgroup D}

theorem IsRankOneFixedRoot.sq_eq_one_of_mem_centralizer (h : IsRankOneFixedRoot n α S) {t : D}
    (htS : t ∈ S) (ht : orderOf t = 2) {x : D} (hxS : x ∈ S)
    (hxt : x ∈ centralizer ({t} : Set D)) : x ^ 2 = 1 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h.exists_field
  have : CharP K 2 := charP_two_of_card (by have := h.1; omega) hK
  set ψ := (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm
  set e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K := φ.trans ψ
  have ht' : orderOf (e ⟨t, htS⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht]
  have hx' : e ⟨x, hxS⟩ ∈ centralizer ({e ⟨t, htS⟩} : Set _) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hxt)
  have h2 := CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht' hx'
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h2
  exact congrArg Subtype.val h2

theorem IsRankOneFixedRoot.prime_dvd_of_outer [Finite D] (h : IsRankOneFixedRoot n α S)
    (hout : α ∉ inner D) {t : D} (htS : t ∈ S) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore ↥(α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D)) =
      ⊥)
    {x : D} (hx : x ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hxr : orderOf x = r) : r ∣ n := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D) with hCdef
  set N := S.subgroupOf C
  have : N.Normal := h.2.2.2.1
  have hSC : S ≤ C := h.2.2.1
  have hnorm : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    intro c hc s hs
    have := (h.2.2.2.1).conj_mem ⟨s, hSC hs⟩ (by rw [mem_subgroupOf]; exact hs) ⟨c, hc⟩
    rwa [mem_subgroupOf] at this
  set Z := C ⊓ centralizer (S : Set D) with hZdef
  have hZodd : Odd (Nat.card Z) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 hev
    have hP : zpowers (z : D) ≤ C ⊓ centralizer (S : Set D) := zpowers_le.2 z.2
    have hPp : IsPGroup 2 (zpowers (z : D)) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hbot := (h.2.2.2.2.2 _ hP hPp).2 hout
    have hz1 : (z : D) = 1 := by
      have : (z : D) ∈ zpowers (z : D) := mem_zpowers _
      rwa [hbot, mem_bot] at this
    rw [show z = 1 from Subtype.ext hz1, orderOf_one] at hz
    omega
  have hZle : Z ≤ C ⊓ centralizer ({t} : Set D) := by
    intro z hz
    refine mem_inf.2 ⟨(mem_inf.1 hz).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.1 (mem_inf.1 hz).2) t htS).symm
  have hZn : (Z.subgroupOf (C ⊓ centralizer ({t} : Set D))).Normal := by
    refine ⟨fun z hz c => ?_⟩
    rw [mem_subgroupOf] at hz ⊢
    obtain ⟨hzC, hzS⟩ := mem_inf.1 hz
    have hcC : (c : D) ∈ C := (mem_inf.1 c.2).1
    refine mem_inf.2 ⟨?_, ?_⟩
    · simp only [coe_mul, coe_inv]
      exact C.mul_mem (C.mul_mem hcC hzC) (C.inv_mem hcC)
    · rw [mem_centralizer_iff]
      intro s hs
      have hs' : (c : D)⁻¹ * s * (c : D) ∈ S := by
        have := hnorm _ (C.inv_mem hcC) s hs
        rwa [inv_inv] at this
      have h1 := (mem_centralizer_iff.1 hzS) _ hs'
      simp only [coe_mul, coe_inv]
      calc s * ((c : D) * z * (c : D)⁻¹)
          = (c : D) * ((c : D)⁻¹ * s * (c : D) * z) * (c : D)⁻¹ := by group
        _ = (c : D) * (z * ((c : D)⁻¹ * s * (c : D))) * (c : D)⁻¹ := by rw [h1]
        _ = (c : D) * z * (c : D)⁻¹ * s := by group
  have hZbot : Z = ⊥ := by
    have hle : Z.subgroupOf (C ⊓ centralizer ({t} : Set D)) ≤
        CFSG.oddCore ↥(C ⊓ centralizer ({t} : Set D)) :=
      le_sSup ⟨hZn, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]; exact hZodd⟩
    rw [hcore, le_bot_iff, subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hZle] at hle
    exact hle
  set f : C →* MulAut N := MulAut.conjNormal
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcZ : (c : D) ∈ Z := by
      refine mem_inf.2 ⟨c.2, mem_centralizer_iff.2 fun s hs => ?_⟩
      have h1 := congrArg (fun φ : MulAut N => ((φ ⟨⟨s, hSC hs⟩, by
        rw [mem_subgroupOf]; exact hs⟩ : N) : C)) hc
      simp only [f, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      have h2 := congrArg Subtype.val h1
      simp only [coe_mul, coe_inv] at h2
      calc s * (c : D) = (c : D) * s * (c : D)⁻¹ * c := by rw [h2]
        _ = c * s := by group
    rw [hZbot, mem_bot] at hcZ
    exact (mem_bot).2 (Subtype.ext hcZ)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h.exists_field
  have hCdvd : Nat.card C ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) * n := by
    rw [← card_mulAut_sl2 (by have := h.1; omega) hK,
      ← Nat.card_congr (MulAut.congr ((Subgroup.subgroupOfEquivOfLe hSC).trans φ)).toEquiv]
    exact Subgroup.card_dvd_of_injective f hfinj
  have hNcard : Nat.card N = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, h.card]
  have hQdvd : Nat.card (C ⧸ N) ∣ n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, hNcard, mul_comm (2 ^ n * ((2 ^ n) ^ 2 - 1))] at hCdvd
    have hpos : 0 < 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      have := h.1
      have h2 : 2 ≤ 2 ^ n :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 1 < (2 ^ n) ^ 2 := by nlinarith
      exact Nat.mul_pos (by positivity) (by omega)
    exact Nat.dvd_of_mul_dvd_mul_right hpos hCdvd
  set xC : C := ⟨x, (mem_inf.1 hx).1⟩
  have hxCr : orderOf xC = r := by rw [Subgroup.orderOf_mk, hxr]
  have hne : (xC : C ⧸ N) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    have h2 := h.sq_eq_one_of_mem_centralizer htS ht h1 (mem_inf.1 hx).2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hxr] at h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h3)
  have hpow : (xC : C ⧸ N) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow, ← hxCr, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hord := orderOf_eq_prime hpow hne
  exact (hord ▸ orderOf_dvd_natCard (xC : C ⧸ N)).trans hQdvd

end OuterRoot

section PSL3Four

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.PSL3Four (F4 frob)

@[expose] def matPermThree : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def matOrthFive : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; ⟨2⟩, ⟨3⟩, 0; ⟨3⟩, ⟨2⟩, 0]

@[expose] def matCompSeven : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def sl3PermThree : SpecialLinearGroup (Fin 3) F4 :=
  ⟨matPermThree, by rw [det_fin_three]; decide⟩

@[expose] def sl3OrthFive : SpecialLinearGroup (Fin 3) F4 :=
  ⟨matOrthFive, by rw [det_fin_three]; decide⟩

@[expose] def sl3CompSeven : SpecialLinearGroup (Fin 3) F4 :=
  ⟨matCompSeven, by rw [det_fin_three]; decide⟩

theorem proj_ne_one_of_entry {g : SpecialLinearGroup (Fin 3) F4}
    (h00 : (g : Matrix (Fin 3) (Fin 3) F4) 0 0 = 0) : proj 3 F4 g ≠ 1 := by
  rw [Ne, proj_eq_one_iff, mem_scalars]
  rintro ⟨c, -, hc⟩
  have h := congrFun (congrFun hc 0) 0
  rw [h00, scalar_apply, diagonal_apply_eq] at h
  exact c.ne_zero h.symm

theorem orderOf_proj_of_entry {g : SpecialLinearGroup (Fin 3) F4} {r : ℕ} (hr : r.Prime)
    (hg : g ^ r = 1) (h00 : (g : Matrix (Fin 3) (Fin 3) F4) 0 0 = 0) :
    orderOf (proj 3 F4 g) = r := by
  have : Fact r.Prime := ⟨hr⟩
  exact orderOf_eq_prime (by rw [← map_pow, hg, map_one]) (proj_ne_one_of_entry h00)

theorem dualAut_proj_of_orthogonal {g : SpecialLinearGroup (Fin 3) F4}
    (hg : (g : Matrix (Fin 3) (Fin 3) F4) * (g : Matrix (Fin 3) (Fin 3) F4)ᵀ = 1) :
    dualAut 3 F4 (proj 3 F4 g) = proj 3 F4 g := by
  rw [dualAut_proj]
  congr 1
  have hinv : g⁻¹ = g.transpose := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    change (g : Matrix (Fin 3) (Fin 3) F4) * (g.transpose : Matrix (Fin 3) (Fin 3) F4) = 1
    rw [SpecialLinearGroup.coe_transpose, hg]
  rw [hinv]
  refine Subtype.ext ?_
  change ((g.transpose.transpose : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = g
  rw [SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_transpose, transpose_transpose]

theorem fieldAut_proj_of_frob {g : SpecialLinearGroup (Fin 3) F4}
    (hg : SpecialLinearGroup.map frob.toRingHom g = g) :
    fieldAut 3 F4 frob (proj 3 F4 g) = proj 3 F4 g := by
  rw [fieldAut_proj, hg]

theorem conj_fixed {G : Type*} [Group G] {γ β φ : MulAut G} (hγ : γ = φ * β * φ⁻¹) {y : G}
    (hy : β y = y) : γ (φ y) = φ y := by
  rw [hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hy]

theorem exists_fixed_three_five_of_graph (A : GL (Fin 3) F4)
    (hA : (conjAut 3 F4 A * dualAut 3 F4) ^ 2 = 1) :
    ∃ y z : projectiveSL 3 F4, (conjAut 3 F4 A * dualAut 3 F4) y = y ∧ orderOf y = 3 ∧
      (conjAut 3 F4 A * dualAut 3 F4) z = z ∧ orderOf z = 5 := by
  obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms (K := F4) (f := 2)
      (by norm_num) CFSG.Sporadic.ONOddCore.card_F4 (le_refl 3) A hA
  have hC1 : C = 1 := by
    rcases hC with ⟨h, -⟩ | ⟨r, hr, -⟩
    · exact Units.ext h
    · omega
  rw [hC1, map_one, one_mul] at hHC
  have h3 : sl3PermThree ^ 3 = 1 := Subtype.ext (by decide)
  have h5 : sl3OrthFive ^ 5 = 1 := Subtype.ext (by decide)
  refine ⟨conjAut 3 F4 H (proj 3 F4 sl3PermThree), conjAut 3 F4 H (proj 3 F4 sl3OrthFive),
    conj_fixed hHC (dualAut_proj_of_orthogonal (by decide)), ?_,
    conj_fixed hHC (dualAut_proj_of_orthogonal (by decide)), ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_proj_of_entry Nat.prime_three h3 (by decide)
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_proj_of_entry (by norm_num) h5 (by decide)

theorem frob_ne_one : frob ≠ 1 := by
  intro h
  have := DFunLike.congr_fun h ⟨2⟩
  revert this
  decide

theorem exists_fixed_three_seven_of_field (A : GL (Fin 3) F4)
    (hA : (conjAut 3 F4 A * fieldAut 3 F4 frob) ^ 2 = 1) :
    ∃ y z : projectiveSL 3 F4, (conjAut 3 F4 A * fieldAut 3 F4 frob) y = y ∧ orderOf y = 3 ∧
      (conjAut 3 F4 A * fieldAut 3 F4 frob) z = z ∧ orderOf z = 7 := by
  obtain ⟨-, -, H, hH⟩ := linear_field_involution_descent (K := F4) Nat.prime_two (f := 2)
    (by norm_num) CFSG.Sporadic.ONOddCore.card_F4 (le_refl 3) A frob frob_ne_one hA
  have h3 : sl3PermThree ^ 3 = 1 := Subtype.ext (by decide)
  have h7 : sl3CompSeven ^ 7 = 1 := Subtype.ext (by decide)
  refine ⟨conjAut 3 F4 H (proj 3 F4 sl3PermThree), conjAut 3 F4 H (proj 3 F4 sl3CompSeven),
    conj_fixed hH (fieldAut_proj_of_frob (Subtype.ext (by decide))), ?_,
    conj_fixed hH (fieldAut_proj_of_frob (Subtype.ext (by decide))), ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_proj_of_entry Nat.prime_three h3 (by decide)
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_proj_of_entry (by norm_num) h7 (by decide)

end PSL3Four

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore in
theorem on_outer_exists_fixed_of_quotient
    {D : Type} [Group D] {α : MulAut D} {t : D} (Θ : D ≃* Pv) (hΘt : Θ t = zP)
    (hz : MulAut.congr Θ α zP = zP) {γbar : MulAut S3}
    (hc : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((MulAut.congr Θ α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = γbar (lToS a))
    {y : S3} (hy : γbar y = y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : orderOf y = r) :
    ∃ x ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D), orderOf x = r := by
  set γ := MulAut.congr Θ α
  set γM := resM γ hz
  obtain ⟨l, hl, hlr⟩ := exists_fixed_of_central_two_kernel lToS lToS_surjective
    (by rw [ker_lToS]; exact QL_le_center) (by rw [ker_lToS]; exact QL_isPGroup) (resL γM)
    γbar.toMonoidHom (fun a => hc a (resL γM a) ((resL_val γM a).trans (resM_val γ hz _))) hy hr
    hr2 hyr
  have eC : ↥(CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α ⊓
      centralizer ({t} : Set D)) ≃*
      ↥(CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup γ ⊓
        centralizer ({zP} : Set Pv)) := by
    have e := fixedCentCongr Θ α t
    rw [hΘt] at e
    exact e
  set lF : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (resL γM) := ⟨l, hl⟩
  set m := fixedLEquiv γM lF
  set m' : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup γM :=
    ⟨m, (mem_inf.1 m.2).1⟩
  set x := eC.symm (fixedMEquiv hz m')
  refine ⟨x, x.2, ?_⟩
  have h1 : orderOf m' = r := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_mk l hl).trans hlr
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, h1]

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore in
theorem on_outer_fixed_no_normal_even_SL2
    {D : Type} [Group D] [Finite D] (hON : NativeSporadic.IsSporadic D .ONan) {n : ℕ} (hn : 2 ≤ n)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D)
    (hα : orderOf α = 2) (hout : α ∉ inner D) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) (hr : FixedRootRankOne α S) :
    False := by
  have h : IsRankOneFixedRoot n α S := ⟨hn, hα, hSα, hSn, ⟨K, inferInstance, inferInstance, hK,
    hSK⟩, hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hON
  obtain ⟨s, hs2⟩ : ∃ s : S, orderOf s = 2 := exists_prime_orderOf_dvd_card' 2
    (by rw [h.card]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _)
  have htS : (s : D) ∈ S := s.2
  have ht : orderOf (s : D) = 2 := by rw [Subgroup.orderOf_coe, hs2]
  have hαt : α s = s := hSα htS
  set θ : D ≃* Pv := e.trans onEquivPv
  have ha : orderOf ((θ s : Pv) : Equiv.Perm (Fin N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate _ (θ s).2 ha
  set gP : Pv := ⟨g, hg⟩
  set Θ : D ≃* Pv := θ.trans (MulAut.conj gP⁻¹)
  have hΘt : Θ s = zP := by
    apply Subtype.ext
    change g⁻¹ * ((θ s : Pv) : Equiv.Perm (Fin N)) * g⁻¹⁻¹ = onz
    rw [hga]
    group
  set γ := MulAut.congr Θ α
  have hγ2 : orderOf γ = 2 := (orderOf_congr Θ α).trans hα
  have hγout : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range :=
    fun hb => hout ((congr_mem_inner_iff Θ α).1 hb)
  have hγγ : γ * γ = 1 := mul_self_eq_one_of_orderOf_eq_two hγ2
  have hz : γ zP = zP := by
    rw [← hΘt]
    change Θ (α (Θ.symm (Θ s))) = Θ s
    rw [MulEquiv.symm_apply_apply, hαt]
  have hcore : CFSG.oddCore ↥(α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer ({(s : D)} : Set D)) = ⊥ := by
    have h1 := oddCore_fixed_centralizer hγout hγγ (a := zP)
      (by rw [← hΘt, MulEquiv.orderOf_eq, ht]) hz
    have e1 := fixedCentCongr Θ α s
    rw [hΘt] at e1
    exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      e1.symm h1
  obtain ⟨-, hLm, -, A, hA⟩ := ctuc_on_outer_local_quotient_is_graph_or_field.2.2 γ hγout hz
  have hcard : Nat.card D = 460815505920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON
  have hS : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 460815505920 := by
    rw [← hcard]
    exact h.sl2Order_dvd_card
  have hlt := lt_of_sl2Order_dvd (by norm_num) (show 460815505920 < 2 ^ 39 by norm_num) hS
  rcases hA with hc | hc
  · obtain ⟨y, w, hy, hy3, hw, hw5⟩ := exists_fixed_three_five_of_graph A
      (by rw [sq]; exact induced_sq hγγ hLm hc)
    obtain ⟨x3, hx3, hx3r⟩ := on_outer_exists_fixed_of_quotient Θ hΘt hz hc hy
      Nat.prime_three (by norm_num) hy3
    obtain ⟨x5, hx5, hx5r⟩ := on_outer_exists_fixed_of_quotient Θ hΘt hz hc hw
      (by norm_num) (by norm_num) hw5
    have h3 := h.prime_dvd_of_outer hout htS ht hcore hx3 Nat.prime_three (by norm_num) hx3r
    have h5 := h.prime_dvd_of_outer hout htS ht hcore hx5 (by norm_num) (by norm_num) hx5r
    interval_cases n <;> omega
  · obtain ⟨y, w, hy, hy3, hw, hw7⟩ := exists_fixed_three_seven_of_field A
      (by rw [sq]; exact induced_sq hγγ hLm hc)
    obtain ⟨x3, hx3, hx3r⟩ := on_outer_exists_fixed_of_quotient Θ hΘt hz hc hy
      Nat.prime_three (by norm_num) hy3
    obtain ⟨x7, hx7, hx7r⟩ := on_outer_exists_fixed_of_quotient Θ hΘt hz hc hw
      (by norm_num) (by norm_num) hw7
    have h3 := h.prime_dvd_of_outer hout htS ht hcore hx3 Nat.prime_three (by norm_num) hx3r
    have h7 := h.prime_dvd_of_outer hout htS ht hcore hx7 (by norm_num) (by norm_num) hx7r
    interval_cases n <;> omega

open CFSG.Sporadic.ONOddCore
  (cti_on_involution_local_components_projective_linear_quotient_order) in
theorem on_fixedRootFree :
    SporadicFixedRootFree .ONan := by
  intro D _ _ hD hs n α S h
  by_cases hα : α ∈ inner D
  · refine h.false_of_inner_comps hD hα (isoInvariant_card_quotient_center {20160})
      (sl2_fails_card_quotient_center_mem (N := {20160}) (fun m hm h' =>
        sl2Order_ne_of_check (B := 15) (by norm_num) (by decide) m hm
          (Set.mem_singleton_iff.1 h')) n h.1) (fun t ht B hB => Set.mem_singleton_iff.2
        (cti_on_involution_local_components_projective_linear_quotient_order hs t ht B hB))
  · obtain ⟨K, _, _, hK, hSK⟩ := h.exists_field
    exact on_outer_fixed_no_normal_even_SL2 hs h.1 K hK α h.2.1 hα S h.2.2.1 h.2.2.2.1 hSK
      h.2.2.2.2.2

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
