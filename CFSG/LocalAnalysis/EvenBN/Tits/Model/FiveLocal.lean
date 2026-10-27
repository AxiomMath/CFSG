module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32OrbitsTwo
public import CFSG.RankThree.PartOne.KE.TitsFiveCentralizer
public import Certificates.Certificate27585

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32
  Certificates.TitsAschbacherFive
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.RankThree.PartOne.KE

theorem mul_pow_mul_inv {M : Type*} [Group M] (g a : M) (n : ℕ) :
    g * a ^ n * g⁻¹ = (g * a * g⁻¹) ^ n :=
  conj_pow.symm

theorem fiveCheck_eq_true : fiveCheck () = true :=
  Certificates.certificate27585

theorem fiveCheck_parts :
    hLetters u2Word = true ∧ hLetters deltaHWord = true ∧
      eqA 1755 (compA 1755 (u2Arr ()) xArr) (compA 1755 (powA xArr 3) (u2Arr ())) = true ∧
      eqA 1755 (compA 1755 (u2Arr ()) (u2Arr ())) (compA 1755 titsZArr (vA 2)) = true ∧
      eqA 1755 (compA 1755 (deltaArr ())
        (Certificates.MaxD2Perm.wT Certificates.MaxD2Perm.titsDData
          Certificates.MaxD2Perm.titsDData.uW))
        (compA 1755 xArr (deltaArr ())) = true ∧
      transCheck () = true := by
  have h := fiveCheck_eq_true
  unfold fiveCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

@[expose] noncomputable def fiveU₂ : Equiv.Perm (Fin 1755) := hElt u2Word

theorem fiveU₂_facts
    : fiveU₂ ∈ titsH ∧ fiveU₂ * hatX * fiveU₂⁻¹ = hatX ^ 3 ∧
      fiveU₂ * fiveU₂ = titsZ * parrottV 2 := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := fiveCheck_parts
  obtain ⟨hr, hmem⟩ := rep_hElt h1
  refine ⟨hmem, ?_, ?_⟩
  · have e := eq_of_eqA (rep_compA hr rep_xArr) (rep_compA (rep_powA rep_xArr 3) hr) h3
    change hElt u2Word * hatX * (hElt u2Word)⁻¹ = hatX ^ 3
    rw [e, mul_inv_cancel_right]
  · exact eq_of_eqA (rep_compA hr hr) (rep_compA titsZ_rep (rep_vA (by norm_num))) h4

theorem parrottV_two_facts
    : IsLong (parrottV 2) ∧ IsShort (titsZ * parrottV 2) ∧
      parrottV 2 * hatX * (parrottV 2)⁻¹ = hatX⁻¹ ∧ parrottV 2 * titsZ = titsZ * parrottV 2 ∧
      parrottV 2 ∈ titsH ∧ parrottV 2 * parrottV 2 = 1 := by
  obtain ⟨-, c2, -, -, -⟩ := ree_conj_two
  obtain ⟨c12, -, -, -, -⟩ := ree_conj_two
  obtain ⟨-, hw2, -, -, -⟩ := reeW_orders
  have hw2A : reeW₂ ∈ titsA := titsD_le_titsA (titsN_le_titsD hw2)
  obtain ⟨-, hX5, hX1, -, -⟩ := hatX_facts
  obtain ⟨s1, -, -, -, s⟩ := parrott_squares
  have hz : titsZ = parrottV 12 := parrottV_twelve.symm
  have e2 : parrottV 2 = reeW₂ * parrottV 8 * reeW₂⁻¹ := by
    rw [← c2]
    group
  have e8 : eElt 1 = parrottV 8 := by
    rw [eElt, show u8Bits 1 = [8] by decide]
    simp
  have e9 : eElt 9 = parrottV 8 * parrottV 11 := by
    rw [eElt, show u8Bits 9 = [8, 11] by decide]
    simp
  have h811 : parrottV 11 * parrottV 8 = parrottV 8 * parrottV 11 :=
    parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)
  have ezv : titsZ * parrottV 2 = reeW₂ * (parrottV 8 * parrottV 11) * reeW₂⁻¹ := by
    rw [← h811, hz, ← c12, ← c2]
    group
  have hL8 : IsLong (parrottV 8) := by
    rw [← e8]
    exact (eElt_long_short (m := 1) (by norm_num) le_rfl).1 (by decide)
  have hS9 : IsShort (parrottV 8 * parrottV 11) := by
    rw [← e9]
    exact (eElt_long_short (m := 9) (by norm_num) (by norm_num)).2 (by decide)
  have hv2D : parrottV 2 ∈ titsD := (parrottV_mem_titsD_iff (by norm_num)).2 (by decide)
  have hcomm : parrottV 2 * titsZ = titsZ * parrottV 2 := by
    rw [hz]
    exact (parrottV_twelve_comm (by norm_num) (by norm_num)).symm
  have hinv : parrottV 2 * hatX * (parrottV 2)⁻¹ = hatX⁻¹ := by
    have h5 : hatX ^ 5 = 1 := by rw [← hX5, pow_orderOf_eq_one]
    rw [← s1, mul_inv_rev]
    calc parrottV 1 * parrottV 1 * hatX * ((parrottV 1)⁻¹ * (parrottV 1)⁻¹) =
        parrottV 1 * (parrottV 1 * hatX * (parrottV 1)⁻¹) * (parrottV 1)⁻¹ := by group
      _ = parrottV 1 * hatX ^ 3 * (parrottV 1)⁻¹ := by rw [hX1]
      _ = (hatX ^ 3) ^ 3 := by rw [mul_pow_mul_inv, hX1]
      _ = hatX⁻¹ := by
        rw [← pow_mul]
        rw [show hatX ^ (3 * 3) = hatX ^ 5 * hatX ^ 4 by rw [← pow_add]]
        rw [h5, one_mul, eq_inv_iff_mul_eq_one, ← pow_succ, h5]
  refine ⟨?_, ?_, hinv, hcomm, ?_, s 2 (by norm_num) (by norm_num) (by decide)⟩
  · rw [e2]
    exact hL8.conj hw2A
  · rw [ezv]
    exact hS9.conj hw2A
  · rw [← titsD_centralizer_z]
    exact mem_inf.2 ⟨hv2D, mem_centralizer_singleton_iff.2 hcomm⟩

theorem titsZ_hatX
    : titsZ * hatX = hatX * titsZ ∧ titsZ * titsZ = 1 := by
  obtain ⟨hXH, -, -, -, -⟩ := hatX_facts
  have hXz : hatX ∈ titsD ⊓ centralizer {titsZ} := by
    rw [titsD_centralizer_z]
    exact hXH
  obtain ⟨-, -, -, -, s⟩ := parrott_squares
  refine ⟨(mem_centralizer_singleton_iff.1 (mem_inf.1 hXz).2).symm, ?_⟩
  rw [← parrottV_twelve]
  exact s 12 (by norm_num) le_rfl (by decide)

theorem titsH_centralizer_hatX
    {c : Equiv.Perm (Fin 1755)} (hc : c ∈ titsH) (hcx : c * hatX = hatX * c) :
    ∃ a b : ℕ, c = hatX ^ a * titsZ ^ b := by
  obtain ⟨hXH, hX5, -, -, -⟩ := hatX_facts
  obtain ⟨hzx, hzz⟩ := titsZ_hatX
  have hzH : titsZ ∈ titsH := by
    rw [← titsD_centralizer_z]
    exact mem_inf.2 ⟨titsZ_mem_titsD, mem_centralizer_singleton_iff.2 rfl⟩
  set x : titsH := ⟨hatX, hXH⟩ with hxdef
  set w : titsH := ⟨hatX * titsZ, mul_mem hXH hzH⟩ with hwdef
  have hx5 : orderOf x = 5 := by rw [← Subgroup.orderOf_coe]; exact hX5
  have hz2 : orderOf (⟨titsZ, hzH⟩ : titsH) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hzz) titsZ_ne_one
  have hw : orderOf w = 10 := by
    have hcomm : Commute x ⟨titsZ, hzH⟩ := Subtype.ext hzx.symm
    have e : w = x * ⟨titsZ, hzH⟩ := rfl
    rw [e, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx5, hz2]; norm_num), hx5, hz2]
  have hC := card_centralizer_titsH_of_orderOf_five hx5
  have hle : zpowers w ≤ centralizer ({x} : Set titsH) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]
    apply Subtype.ext
    change hatX * titsZ * hatX = hatX * (hatX * titsZ)
    rw [mul_assoc, hzx]
  have heq : zpowers w = centralizer ({x} : Set titsH) :=
    eq_of_le_of_card_ge hle (by rw [hC, Nat.card_zpowers, hw])
  have hcC : (⟨c, hc⟩ : titsH) ∈ centralizer ({x} : Set titsH) :=
    mem_centralizer_singleton_iff.2 (Subtype.ext hcx)
  rw [← heq, mem_zpowers_iff] at hcC
  obtain ⟨k, hk⟩ := hcC
  have hw10n : w ^ 10 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw10 : w ^ (10 : ℤ) = 1 := by exact_mod_cast hw10n
  refine ⟨(k % 10).toNat, (k % 10).toNat, ?_⟩
  have e1 : w ^ k = w ^ (k % 10).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    conv_lhs => rw [← Int.emod_add_mul_ediv k 10, zpow_add, zpow_mul, hw10, one_zpow, mul_one]
  have e2 : c = (w : Equiv.Perm (Fin 1755)) ^ (k % 10).toNat := by
    have := congrArg Subtype.val (hk.symm.trans e1)
    rwa [Subgroup.coe_pow] at this
  rw [e2, show (w : Equiv.Perm (Fin 1755)) = hatX * titsZ from rfl,
    (Commute.mul_pow (show Commute hatX titsZ from hzx.symm))]

theorem exists_titsH_conj_hatX
    {y : Equiv.Perm (Fin 1755)} (hy : y ∈ titsH) (hy5 : orderOf y = 5) :
    ∃ η ∈ titsH, η * y * η⁻¹ = hatX := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hXH, hX5, -, -, -⟩ := hatX_facts
  obtain ⟨hU, hUx, -⟩ := fiveU₂_facts
  set x : titsH := ⟨hatX, hXH⟩
  have hx5 : orderOf x = 5 := by rw [← Subgroup.orderOf_coe]; exact hX5
  have hP : IsPGroup 5 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx5, pow_one])
  have hindex : ¬ 5 ∣ (zpowers x).index := by
    have h := card_mul_index (zpowers x)
    rw [Nat.card_zpowers, hx5, titsQH_facts.2.2.2] at h
    have h' : (zpowers x).index = 2048 := by omega
    rw [h']
    norm_num
  set y' : titsH := ⟨y, hy⟩
  have hy'5 : orderOf y' = 5 := by rw [← Subgroup.orderOf_coe]; exact hy5
  have hQ : IsPGroup 5 (zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'5, pow_one])
  obtain ⟨T, hT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsH (hP.toSylow hindex) T
  have hyT : y' ∈ (T : Subgroup titsH) := hT (mem_zpowers y')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe] at hyT
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hyT
  have hconj : (g⁻¹ : titsH) * y' * g = x ^ j := by
    rw [hj]
    simp [MulAut.smul_def]
  have hx5n' : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
  have hx5z : x ^ (5 : ℤ) = 1 := by exact_mod_cast hx5n'
  obtain ⟨r, hr5, hjm⟩ : ∃ r : ℕ, r < 5 ∧ x ^ j = x ^ r := by
    refine ⟨(j % 5).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))]
    conv_lhs => rw [← Int.emod_add_mul_ediv j 5, zpow_add, zpow_mul, hx5z, one_zpow, mul_one]
  have hr0 : r ≠ 0 := by
    intro h0
    have h1 : (g⁻¹ : titsH) * y' * g = 1 := by rw [hconj, hjm, h0, pow_zero]
    have : y' = 1 := by
      have := congrArg (fun a => g * a * g⁻¹) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hy'5
    exact absurd hy'5 (by norm_num)
  set u : titsH := ⟨fiveU₂, hU⟩
  have hux : u * x * u⁻¹ = x ^ 3 := Subtype.ext (by simpa using hUx)
  have hupow : ∀ m s : ℕ, u ^ m * x ^ s * (u ^ m)⁻¹ = x ^ (s * 3 ^ m) := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      calc u ^ (m + 1) * x ^ s * (u ^ (m + 1))⁻¹ = u * (u ^ m * x ^ s * (u ^ m)⁻¹) * u⁻¹ := by
            rw [pow_succ']; group
        _ = u * x ^ (s * 3 ^ m) * u⁻¹ := by rw [ih]
        _ = (u * x * u⁻¹) ^ (s * 3 ^ m) := by rw [mul_pow_mul_inv]
        _ = x ^ (s * 3 ^ (m + 1)) := by rw [hux, ← pow_mul]; congr 1; ring
  have hx5n : ∀ s : ℕ, x ^ s = x ^ (s % 5) := fun s => by
    conv_lhs => rw [← Nat.mod_add_div s 5, pow_add, pow_mul, show x ^ 5 = 1 by
      rw [← hx5, pow_orderOf_eq_one], one_pow, mul_one]
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (r * 3 ^ m) % 5 = 1 := by
    interval_cases r
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  refine ⟨u ^ m * g⁻¹, mul_mem (pow_mem hU m) (inv_mem g.2), ?_⟩
  have key : (u ^ m * g⁻¹ : titsH) * y' * (u ^ m * g⁻¹)⁻¹ = x := by
    calc (u ^ m * g⁻¹ : titsH) * y' * (u ^ m * g⁻¹)⁻¹ =
        u ^ m * ((g⁻¹ : titsH) * y' * g) * (u ^ m)⁻¹ := by group
      _ = x := by rw [hconj, hjm, hupow, hx5n, hm, pow_one]
  exact congrArg Subtype.val key

theorem isLong_hatX_pow_mul_parrottV_two
    (e : ℕ) : IsLong (hatX ^ e * parrottV 2) := by
  obtain ⟨hL, -, hinv, -, -, -⟩ := parrottV_two_facts
  obtain ⟨hXH, hX5, -, -, -⟩ := hatX_facts
  have h5 : hatX ^ 5 = 1 := by rw [← hX5, pow_orderOf_eq_one]
  have hXA : hatX ^ (3 * e) ∈ titsA :=
    titsD_le_titsA (titsH_le_titsD (pow_mem hXH _))
  have hinvp : ∀ n : ℕ, parrottV 2 * hatX ^ n * (parrottV 2)⁻¹ = (hatX ^ n)⁻¹ := by
    intro n
    rw [mul_pow_mul_inv, hinv, inv_pow]
  have key : hatX ^ (3 * e) * parrottV 2 * (hatX ^ (3 * e))⁻¹ = hatX ^ e * parrottV 2 := by
    have e1 : parrottV 2 * (hatX ^ (3 * e))⁻¹ = hatX ^ (3 * e) * parrottV 2 := by
      have := hinvp (3 * e)
      calc parrottV 2 * (hatX ^ (3 * e))⁻¹ =
          (parrottV 2 * (hatX ^ (3 * e))⁻¹ * (parrottV 2)⁻¹) * parrottV 2 := by group
        _ = hatX ^ (3 * e) * parrottV 2 := by
          rw [show parrottV 2 * (hatX ^ (3 * e))⁻¹ * (parrottV 2)⁻¹ =
            (parrottV 2 * hatX ^ (3 * e) * (parrottV 2)⁻¹)⁻¹ by group, this, inv_inv]
    calc hatX ^ (3 * e) * parrottV 2 * (hatX ^ (3 * e))⁻¹ =
        hatX ^ (3 * e) * (parrottV 2 * (hatX ^ (3 * e))⁻¹) := by group
      _ = hatX ^ (3 * e) * hatX ^ (3 * e) * parrottV 2 := by rw [e1]; group
      _ = hatX ^ e * parrottV 2 := by
        rw [← pow_add, show 3 * e + 3 * e = 5 * e + e by ring, pow_add, pow_mul, h5, one_pow,
          one_mul]
  rw [← key]
  exact hL.conj hXA

theorem isLong_titsZ_mul_sq
    {l : Equiv.Perm (Fin 1755)} (hl : l ∈ titsH) (hlX : l * hatX * l⁻¹ ∈ zpowers hatX)
    (hinv : l * l * hatX * (l * l)⁻¹ = hatX⁻¹) : IsLong (titsZ * (l * l)) := by
  obtain ⟨hXH, hX5, -, -, -⟩ := hatX_facts
  obtain ⟨hU, hUx, hUU⟩ := fiveU₂_facts
  obtain ⟨-, -, hv2x, hv2z, -, hv22⟩ := parrottV_two_facts
  obtain ⟨hzx, hzz⟩ := titsZ_hatX
  have h5 : hatX ^ 5 = 1 := by rw [← hX5, pow_orderOf_eq_one]
  have hzH : titsZ ∈ titsH := by
    rw [← titsD_centralizer_z]
    exact mem_inf.2 ⟨titsZ_mem_titsD, mem_centralizer_singleton_iff.2 rfl⟩
  have hHz : ∀ h ∈ titsH, h * titsZ = titsZ * h := fun h hh => by
    rw [← titsD_centralizer_z] at hh
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hh).2
  obtain ⟨k0, hk0⟩ := mem_zpowers_iff.1 hlX
  have hx5z : hatX ^ (5 : ℤ) = 1 := by exact_mod_cast h5
  have hpow5 : ∀ s : ℕ, hatX ^ s = hatX ^ (s % 5) := fun s => by
    conv_lhs => rw [← Nat.mod_add_div s 5, pow_add, pow_mul, h5, one_pow, mul_one]
  obtain ⟨k, hk5, hlk⟩ : ∃ k : ℕ, k < 5 ∧ l * hatX * l⁻¹ = hatX ^ k := by
    refine ⟨(k0 % 5).toNat, by omega, ?_⟩
    rw [← hk0, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k0 (by norm_num))]
    conv_lhs => rw [← Int.emod_add_mul_ediv k0 5, zpow_add, zpow_mul, hx5z, one_zpow, mul_one]
  have hl2 : l * l * hatX * (l * l)⁻¹ = hatX ^ (k * k) := by
    calc l * l * hatX * (l * l)⁻¹ = l * (l * hatX * l⁻¹) * l⁻¹ := by group
      _ = l * hatX ^ k * l⁻¹ := by rw [hlk]
      _ = (hatX ^ k) ^ k := by rw [mul_pow_mul_inv, hlk]
      _ = hatX ^ (k * k) := by rw [← pow_mul]
  have hx4 : hatX⁻¹ = hatX ^ 4 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, h5]
  rw [hl2, hx4, hpow5 (k * k)] at hinv
  have hinj : ∀ a b : ℕ, a < 5 → b < 5 → hatX ^ a = hatX ^ b → a = b := by
    intro a b ha hb hab
    have := pow_inj_mod.1 hab
    rw [hX5, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this
  have hkk : (k * k) % 5 = 4 := hinj _ _ (Nat.mod_lt _ (by norm_num)) (by norm_num) hinv
  have hUinv : fiveU₂⁻¹ * hatX * fiveU₂ = hatX ^ 2 := by
    have : fiveU₂ * hatX ^ 2 * fiveU₂⁻¹ = hatX := by
      rw [mul_pow_mul_inv, hUx, ← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_add, h5, one_mul,
        pow_one]
    calc fiveU₂⁻¹ * hatX * fiveU₂ = fiveU₂⁻¹ * (fiveU₂ * hatX ^ 2 * fiveU₂⁻¹) * fiveU₂ := by
          rw [this]
      _ = hatX ^ 2 := by group
  have finish : ∀ e : ℕ, titsZ * (l * l) = hatX ^ e * parrottV 2 → IsLong (titsZ * (l * l)) :=
    fun e he => by rw [he]; exact isLong_hatX_pow_mul_parrottV_two e
  have hU2inv : (fiveU₂ * fiveU₂)⁻¹ = titsZ * parrottV 2 := by
    rw [hUU, mul_inv_rev, show (parrottV 2)⁻¹ = parrottV 2 from
      inv_eq_of_mul_eq_one_right hv22, show titsZ⁻¹ = titsZ from inv_eq_of_mul_eq_one_right hzz,
      hv2z]
  have hk23 : k = 2 ∨ k = 3 := by interval_cases k <;> simp at hkk ⊢
  rcases hk23 with hk2 | hk3
  ·
    obtain ⟨a, b, hc⟩ := titsH_centralizer_hatX (c := l * fiveU₂) (mul_mem hl hU) (by
      have : l * fiveU₂ * hatX * (l * fiveU₂)⁻¹ = hatX := by
        calc l * fiveU₂ * hatX * (l * fiveU₂)⁻¹ = l * (fiveU₂ * hatX * fiveU₂⁻¹) * l⁻¹ := by
              group
          _ = l * hatX ^ 3 * l⁻¹ := by rw [hUx]
          _ = (l * hatX * l⁻¹) ^ 3 := by rw [mul_pow_mul_inv]
          _ = hatX := by
            rw [hlk, hk2, ← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_add, h5, one_mul,
              pow_one]
      calc l * fiveU₂ * hatX = l * fiveU₂ * hatX * (l * fiveU₂)⁻¹ * (l * fiveU₂) := by group
        _ = hatX * (l * fiveU₂) := by rw [this])
    have hl' : l = hatX ^ a * titsZ ^ b * fiveU₂⁻¹ := by rw [← hc]; group
    refine finish (3 * a) ?_
    have hconjU : fiveU₂⁻¹ * (hatX ^ a * titsZ ^ b) * fiveU₂ = hatX ^ (2 * a) * titsZ ^ b := by
      have h1 : fiveU₂⁻¹ * hatX ^ a * fiveU₂ = hatX ^ (2 * a) := by
        have := mul_pow_mul_inv fiveU₂⁻¹ hatX a
        rw [inv_inv] at this
        rw [this, hUinv, ← pow_mul, mul_comm]
      have h2 : fiveU₂⁻¹ * titsZ ^ b * fiveU₂ = titsZ ^ b := by
        have hc : Commute fiveU₂ (titsZ ^ b) :=
          Commute.pow_right (show Commute fiveU₂ titsZ from hHz _ hU) b
        rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
      calc fiveU₂⁻¹ * (hatX ^ a * titsZ ^ b) * fiveU₂ =
          (fiveU₂⁻¹ * hatX ^ a * fiveU₂) * (fiveU₂⁻¹ * titsZ ^ b * fiveU₂) := by group
        _ = hatX ^ (2 * a) * titsZ ^ b := by rw [h1, h2]
    have hzb : titsZ ^ b * hatX ^ (2 * a) = hatX ^ (2 * a) * titsZ ^ b :=
      ((Commute.pow_pow (show Commute titsZ hatX from hzx) b (2 * a))).eq
    have hzbb : titsZ ^ b * titsZ ^ b = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, sq, hzz, one_pow]
    calc titsZ * (l * l) = titsZ * (hatX ^ a * titsZ ^ b * fiveU₂⁻¹ *
          (hatX ^ a * titsZ ^ b * fiveU₂⁻¹)) := by rw [← hl']
      _ = titsZ * (hatX ^ a * titsZ ^ b * (fiveU₂⁻¹ * (hatX ^ a * titsZ ^ b) * fiveU₂) *
          (fiveU₂ * fiveU₂)⁻¹) := by group
      _ = titsZ * (hatX ^ a * (titsZ ^ b * hatX ^ (2 * a)) * titsZ ^ b * (titsZ * parrottV 2)) := by
          rw [hconjU, hU2inv]; group
      _ = titsZ * (hatX ^ a * hatX ^ (2 * a) * (titsZ ^ b * titsZ ^ b) * titsZ) * parrottV 2 := by
          rw [hzb]; group
      _ = (titsZ * hatX ^ (3 * a)) * titsZ * parrottV 2 := by
          rw [hzbb, mul_one, ← pow_add, show a + 2 * a = 3 * a by ring]; group
      _ = hatX ^ (3 * a) * parrottV 2 := by
          rw [(Commute.pow_right (show Commute titsZ hatX from hzx) (3 * a)).eq,
            mul_assoc (hatX ^ (3 * a)) titsZ titsZ, hzz, mul_one]
  ·
    obtain ⟨a, b, hc⟩ := titsH_centralizer_hatX (c := l * fiveU₂⁻¹) (mul_mem hl (inv_mem hU)) (by
      have : l * fiveU₂⁻¹ * hatX * (l * fiveU₂⁻¹)⁻¹ = hatX := by
        calc l * fiveU₂⁻¹ * hatX * (l * fiveU₂⁻¹)⁻¹ = l * (fiveU₂⁻¹ * hatX * fiveU₂) * l⁻¹ := by
              group
          _ = l * hatX ^ 2 * l⁻¹ := by rw [hUinv]
          _ = (l * hatX * l⁻¹) ^ 2 := by rw [mul_pow_mul_inv]
          _ = hatX := by
            rw [hlk, hk3, ← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_add, h5, one_mul,
              pow_one]
      calc l * fiveU₂⁻¹ * hatX = l * fiveU₂⁻¹ * hatX * (l * fiveU₂⁻¹)⁻¹ * (l * fiveU₂⁻¹) := by
            group
        _ = hatX * (l * fiveU₂⁻¹) := by rw [this])
    have hl' : l = hatX ^ a * titsZ ^ b * fiveU₂ := by rw [← hc]; group
    refine finish (4 * a) ?_
    have hconjU : fiveU₂ * (hatX ^ a * titsZ ^ b) * fiveU₂⁻¹ = hatX ^ (3 * a) * titsZ ^ b := by
      have h1 : fiveU₂ * hatX ^ a * fiveU₂⁻¹ = hatX ^ (3 * a) := by
        rw [mul_pow_mul_inv, hUx, ← pow_mul]
      have h2 : fiveU₂ * titsZ ^ b * fiveU₂⁻¹ = titsZ ^ b := by
        have hc : Commute fiveU₂ (titsZ ^ b) :=
          Commute.pow_right (show Commute fiveU₂ titsZ from hHz _ hU) b
        rw [hc.eq, mul_inv_cancel_right]
      calc fiveU₂ * (hatX ^ a * titsZ ^ b) * fiveU₂⁻¹ =
          (fiveU₂ * hatX ^ a * fiveU₂⁻¹) * (fiveU₂ * titsZ ^ b * fiveU₂⁻¹) := by group
        _ = hatX ^ (3 * a) * titsZ ^ b := by rw [h1, h2]
    have hzb : titsZ ^ b * hatX ^ (3 * a) = hatX ^ (3 * a) * titsZ ^ b :=
      ((Commute.pow_pow (show Commute titsZ hatX from hzx) b (3 * a))).eq
    have hzbb : titsZ ^ b * titsZ ^ b = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, sq, hzz, one_pow]
    calc titsZ * (l * l) = titsZ * (hatX ^ a * titsZ ^ b * fiveU₂ *
          (hatX ^ a * titsZ ^ b * fiveU₂)) := by rw [← hl']
      _ = titsZ * (hatX ^ a * titsZ ^ b * (fiveU₂ * (hatX ^ a * titsZ ^ b) * fiveU₂⁻¹) *
          (fiveU₂ * fiveU₂)) := by group
      _ = titsZ * (hatX ^ a * (titsZ ^ b * hatX ^ (3 * a)) * titsZ ^ b * (titsZ * parrottV 2)) := by
          rw [hconjU, hUU]; group
      _ = titsZ * (hatX ^ a * hatX ^ (3 * a) * (titsZ ^ b * titsZ ^ b) * titsZ) * parrottV 2 := by
          rw [hzb]; group
      _ = (titsZ * hatX ^ (4 * a)) * titsZ * parrottV 2 := by
          rw [hzbb, mul_one, ← pow_add, show a + 3 * a = 4 * a by ring]; group
      _ = hatX ^ (4 * a) * parrottV 2 := by
          rw [(Commute.pow_right (show Commute titsZ hatX from hzx) (4 * a)).eq,
            mul_assoc (hatX ^ (4 * a)) titsZ titsZ, hzz, mul_one]

noncomputable abbrev fiveGensL : List (Equiv.Perm (Fin 1755)) := [titsDGen 0, titsDGen 1]

@[expose] noncomputable def fiveR : Subgroup (Equiv.Perm (Fin 1755)) :=
  CFSG.AGLEmbedding.MaxD2.Rsub Certificates.MaxD2Perm.titsDData fiveGensL

@[expose] noncomputable def fiveN : Subgroup (Equiv.Perm (Fin 1755)) :=
  CFSG.AGLEmbedding.MaxD2.Nsub Certificates.MaxD2Perm.titsDData fiveGensL

@[expose] noncomputable def fiveU : Equiv.Perm (Fin 1755) :=
  CFSG.AGLEmbedding.FusD2.wordVal fiveGensL Certificates.MaxD2Perm.titsDData.uW

@[expose] noncomputable def fiveDelta : Equiv.Perm (Fin 1755) :=
  hElt deltaHWord *
      (CFSG.AGLEmbedding.FusD2.wordVal fiveGensL deltaAWord * titsZ) ^ deltaExp *
    CFSG.AGLEmbedding.FusD2.wordVal fiveGensL deltaBWord

theorem tabRep_wT_D (w : List ℤ) :
    TabRep (Certificates.MaxD2Perm.wT Certificates.MaxD2Perm.titsDData w)
      (CFSG.AGLEmbedding.FusD2.wordVal fiveGensL w) := by
  have h := CFSG.AGLEmbeddingD2.tits_five_local_check_d
  simp only [Certificates.MaxD2Perm.check, Bool.and_eq_true] at h
  exact CFSG.AGLEmbedding.MaxD2.wT_rep CFSG.AGLEmbeddingD2.titsD_hS
    (CFSG.AGLEmbedding.MaxD2.giT_rep CFSG.AGLEmbeddingD2.titsD_hS h.1.1.1.1.1.1.1) w

theorem wordVal_mem_titsD (w : List ℤ) : CFSG.AGLEmbedding.FusD2.wordVal fiveGensL w ∈ titsD := by
  have h := CFSG.AGLEmbedding.MaxD2.wordVal_mem_Gsub (D := Certificates.MaxD2Perm.titsDData)
    (S := fiveGensL) w
  rwa [show (CFSG.AGLEmbedding.MaxD2.Gsub (D := Certificates.MaxD2Perm.titsDData) fiveGensL :
    Subgroup (Equiv.Perm (Fin 1755))) = titsD from
    CFSG.AGLEmbeddingD2.titsD_eq_closure_list.symm] at h

theorem fiveDelta_facts
    : fiveDelta ∈ titsD ∧ fiveDelta * fiveU * fiveDelta⁻¹ = hatX := by
  obtain ⟨-, h2, -, -, h5, -⟩ := fiveCheck_parts
  obtain ⟨hr, hmem⟩ := rep_hElt h2
  have rw' : ∀ w, Rep 1755 (Certificates.MaxD2Perm.wT Certificates.MaxD2Perm.titsDData w)
      (CFSG.AGLEmbedding.FusD2.wordVal fiveGensL w) := fun w x => (tabRep_wT_D w).2 x
  have hδ : Rep 1755 (deltaArr ()) fiveDelta :=
    rep_compA (rep_compA hr (rep_powA (rep_compA (rw' _) titsZ_rep) _)) (rw' _)
  refine ⟨mul_mem (mul_mem (titsH_le_titsD hmem)
    (pow_mem (mul_mem (wordVal_mem_titsD _) titsZ_mem_titsD) _)) (wordVal_mem_titsD _), ?_⟩
  have e := eq_of_eqA (rep_compA hδ (rw' _)) (rep_compA rep_xArr hδ) h5
  change fiveDelta * fiveU * fiveDelta⁻¹ = hatX
  rw [show fiveU = CFSG.AGLEmbedding.FusD2.wordVal fiveGensL
    Certificates.MaxD2Perm.titsDData.uW from rfl, e, mul_inv_cancel_right]

theorem exists_conj_fiveU
    {y : Equiv.Perm (Fin 1755)} (hy : y ∈ fiveR) (hy1 : y ≠ 1) :
    ∃ n ∈ fiveN, n * fiveU * n⁻¹ = y := by
  obtain ⟨-, -, -, -, -, h6⟩ := fiveCheck_parts
  have h := CFSG.AGLEmbeddingD2.tits_five_local_check_d
  simp only [Certificates.MaxD2Perm.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep CFSG.AGLEmbeddingD2.titsD_hS hInv
  have hRe := CFSG.AGLEmbedding.MaxD2.enum_R CFSG.AGLEmbeddingD2.titsD_hS hgi hR
  have hNe := CFSG.AGLEmbedding.MaxD2.enum_N CFSG.AGLEmbeddingD2.titsD_hS hgi hN
  obtain ⟨k, hk, hky⟩ := hRe.exists_pos hy
  have hu : TabRep (Certificates.MaxD2Perm.wT Certificates.MaxD2Perm.titsDData
      Certificates.MaxD2Perm.titsDData.uW) fiveU := tabRep_wT_D _
  unfold transCheck at h6
  simp only [allBelow_eq_true, Bool.or_eq_true, beq_iff_eq, anyBelow_eq_true] at h6
  rcases h6 k hk with h1 | ⟨j, hj, hj'⟩
  · exact absurd ((hky.eq_iff TabRep.idTab).1 h1) hy1
  · obtain ⟨n, hn, hnr⟩ := hNe.exists_elt hj
    refine ⟨n, hn, ?_⟩
    have e := eq_of_eqA (rep_compA (fun x => hnr.2 x) (fun x => hu.2 x))
      (rep_compA (fun x => hky.2 x) (fun x => hnr.2 x)) hj'
    exact mul_inv_eq_iff_eq_mul.2 e

theorem exists_sylow_fiveR :
    ∃ P : Sylow 5 titsD, (P : Subgroup titsD) = fiveR.subgroupOf titsD := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := CFSG.AGLEmbeddingD2.tits_five_local_check_d
  simp only [Certificates.MaxD2Perm.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep CFSG.AGLEmbeddingD2.titsD_hS hInv
  have h25 : Nat.card fiveR = 25 :=
    CFSG.AGLEmbedding.MaxD2.card_R CFSG.AGLEmbeddingD2.titsD_hS hgi hR
  have hYD : fiveR ≤ titsD := by
    have hle := CFSG.AGLEmbedding.MaxD2.Rsub_le_Gsub (D := Certificates.MaxD2Perm.titsDData)
      (S := fiveGensL)
    rwa [show (CFSG.AGLEmbedding.MaxD2.Gsub (D := Certificates.MaxD2Perm.titsDData) fiveGensL :
      Subgroup (Equiv.Perm (Fin 1755))) = titsD from
      CFSG.AGLEmbeddingD2.titsD_eq_closure_list.symm] at hle
  have hcard : Nat.card (fiveR.subgroupOf titsD) = 25 := by
    rw [← h25]
    exact Nat.card_congr (subgroupOfEquivOfLe hYD).toEquiv
  have hp : IsPGroup 5 (fiveR.subgroupOf titsD) :=
    IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hidx : ¬ 5 ∣ (fiveR.subgroupOf titsD).index := by
    have h := card_mul_index (fiveR.subgroupOf titsD)
    rw [hcard, card_titsD] at h
    have : (fiveR.subgroupOf titsD).index = 718848 := by omega
    rw [this]
    decide
  exact ⟨hp.toSylow hidx, rfl⟩

theorem exists_conj_hatX_of_orderOf_five
    {y : Equiv.Perm (Fin 1755)} (hy : y ∈ titsD) (hy5 : orderOf y = 5) :
    ∃ c ∈ titsD, c * hatX * c⁻¹ = y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P, hP⟩ := exists_sylow_fiveR
  obtain ⟨hδD, hδ⟩ := fiveDelta_facts
  set y' : titsD := ⟨y, hy⟩
  have hy'5 : orderOf y' = 5 := by rw [← Subgroup.orderOf_coe]; exact hy5
  have hQ : IsPGroup 5 (zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'5, pow_one])
  obtain ⟨T, hT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsD P T
  have hyT : y' ∈ (T : Subgroup titsD) := hT (mem_zpowers y')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP] at hyT
  have hmem : (g : Equiv.Perm (Fin 1755))⁻¹ * y * g ∈ fiveR := by
    have := mem_subgroupOf.1 hyT
    simpa [MulAut.smul_def] using this
  have hne : (g : Equiv.Perm (Fin 1755))⁻¹ * y * g ≠ 1 := by
    intro h1
    have hy1 : y = 1 := by
      have := congrArg (fun a => (g : Equiv.Perm (Fin 1755)) * a * (g : Equiv.Perm (Fin 1755))⁻¹)
        h1
      simpa [mul_assoc] using this
    rw [hy1, orderOf_one] at hy5
    exact absurd hy5 (by norm_num)
  obtain ⟨n, hn, hny⟩ := exists_conj_fiveU hmem hne
  have hnD : n ∈ titsD := by
    have h1 := CFSG.AGLEmbedding.MaxD2.Nsub_le_Gsub (D := Certificates.MaxD2Perm.titsDData)
      (S := fiveGensL) hn
    rwa [show (CFSG.AGLEmbedding.MaxD2.Gsub (D := Certificates.MaxD2Perm.titsDData) fiveGensL :
    Subgroup (Equiv.Perm (Fin 1755))) = titsD from
    CFSG.AGLEmbeddingD2.titsD_eq_closure_list.symm] at h1
  refine ⟨(g : Equiv.Perm (Fin 1755)) * n * fiveDelta⁻¹, mul_mem (mul_mem g.2 hnD) (inv_mem hδD),
    ?_⟩
  have hu : fiveU = fiveDelta⁻¹ * hatX * fiveDelta := by rw [← hδ]; group
  calc (g : Equiv.Perm (Fin 1755)) * n * fiveDelta⁻¹ * hatX *
        ((g : Equiv.Perm (Fin 1755)) * n * fiveDelta⁻¹)⁻¹ =
      (g : Equiv.Perm (Fin 1755)) * (n * (fiveDelta⁻¹ * hatX * fiveDelta) * n⁻¹) *
        (g : Equiv.Perm (Fin 1755))⁻¹ := by group
    _ = y := by rw [← hu, hny]; group

theorem card_le_four_of_le_centralizer_hatX
    {P : Subgroup (Equiv.Perm (Fin 1755))} (hPA : P ≤ titsA)
    (hPC : P ≤ centralizer {hatX}) (hP2 : IsPGroup 2 P) : Nat.card P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hXH, hX5, -, -, -⟩ := hatX_facts
  have hXD : hatX ∈ titsD := titsH_le_titsD hXH
  set x : titsD := ⟨hatX, hXD⟩
  have hx5 : orderOf x = 5 := by rw [← Subgroup.orderOf_coe]; exact hX5
  set C := centralizer ({x} : Set titsD)
  set φ : C →* Equiv.Perm (Fin 1755) := titsD.subtype.comp C.subtype
  have hφ : Function.Injective φ :=
    (Subtype.coe_injective).comp Subtype.coe_injective
  set Q : Subgroup C := P.comap φ
  have hQ2 : IsPGroup 2 Q := hP2.comap_of_injective φ hφ
  obtain ⟨R, hQR⟩ := hQ2.exists_le_sylow
  have hR := tits_card_sylow_two_centralizer_le_two hx5 R
  have hDP : Nat.card (titsD ⊓ P : Subgroup _) ≤ 2 := by
    have hinj : Function.Injective (fun p : (titsD ⊓ P : Subgroup _) =>
        (⟨⟨⟨p.1, (mem_inf.1 p.2).1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
          (mem_centralizer_singleton_iff.1 (hPC (mem_inf.1 p.2).2)))⟩,
          (mem_inf.1 p.2).2⟩ : Q)) := by
      intro p q h
      apply Subtype.ext
      have := congrArg (fun r : Q => ((r : C) : titsD).1) h
      simpa using this
    calc Nat.card (titsD ⊓ P : Subgroup _) ≤ Nat.card Q := Nat.card_le_card_of_injective _ hinj
      _ ≤ Nat.card R := Subgroup.card_le_of_le hQR
      _ ≤ 2 := hR
  have hidx : titsD.relIndex P ≤ 2 := by
    have h2 : titsD.relIndex titsA = 2 := titsD_index
    calc titsD.relIndex P ≤ titsD.relIndex titsA :=
          relIndex_le_of_le_right hPA (by rw [h2]; norm_num)
      _ = 2 := h2
  have hmul := relIndex_mul_card titsD P
  calc Nat.card P = titsD.relIndex P * Nat.card (titsD ⊓ P : Subgroup _) := hmul.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hidx hDP
    _ = 4 := by norm_num

end CFSG.LocalAnalysis.EvenBN.Tits.Model
