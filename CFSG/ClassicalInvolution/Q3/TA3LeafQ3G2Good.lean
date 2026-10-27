module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Core
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot
public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement MatrixGroups

theorem conj_mul_comm {Y : Type} [Group Y] {g a q : Y} (hg : g * q = q * g)
    (ha : a * q = q * a) : g * a * g⁻¹ * q = q * (g * a * g⁻¹) := by
  have hg' : g⁻¹ * q = q * g⁻¹ := (Commute.inv_left (hg : Commute g q)).eq
  calc g * a * g⁻¹ * q = g * a * (g⁻¹ * q) := by group
    _ = g * (a * q) * g⁻¹ := by rw [hg']; group
    _ = g * q * a * g⁻¹ := by rw [ha]; group
    _ = q * (g * a * g⁻¹) := by rw [hg]; group

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem TightDatum.mem_oddCoreImg_of_odd_order (hD : TightDatum R S t) {w : Y} (hw : w ∈ R)
    (hodd : Odd (orderOf w)) : w ∈ oddCoreImg R := by
  set π : R →* R ⧸ classicalInvolutionOddCore R := QuotientGroup.mk' _
  have h1 : orderOf (π ⟨w, hw⟩) ∣ orderOf w := by
    have := orderOf_map_dvd π ⟨w, hw⟩
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨m, hm⟩ := hD.twoGroup (π ⟨w, hw⟩)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hm)
  have hj0 : j = 0 := by
    by_contra hj0
    have h3 : Odd (2 ^ j) := hj ▸ hodd.of_dvd_nat h1
    exact (Nat.not_even_iff_odd.mpr h3) ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero] at hj
  exact ⟨⟨w, hw⟩, (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hj), rfl⟩

theorem TightDatum.pow_four_of_mem_B (hD : TightDatum R S t) {C : Subgroup Y} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = 3) {h3 : (3 : F₂) = 0}
    (P : CentShape Y C t F₁ F₂ h3) (hC : C ≤ Subgroup.centralizer ({t} : Set Y)) {m : Y}
    (hm : m ∈ R) (hmB : m ∈ P.B) : m ^ 4 = 1 := by
  by_contra h4
  have hh3 := P.B_pow_four hF₂ hmB h4
  have hhO : m ^ 4 ∈ oddCoreImg R := TightDatum.mem_oddCoreImg_of_odd_order hD (pow_mem hm 4)
    (by rw [orderOf_eq_prime hh3 h4]; decide)
  obtain ⟨g, hgB, hg4, hg1⟩ := P.B_exists_commutator hF₂ (pow_mem hmB 4) hh3 h4
  refine hg1 (eq_one_of_mem_oddCoreImg (R := R) ?_
    ((orderOf_dvd_of_pow_eq_one hg4).trans (by norm_num)))
  rw [show m ^ 4 * g * (m ^ 4)⁻¹ * g⁻¹ = m ^ 4 * (g * (m ^ 4)⁻¹ * g⁻¹) by group]
  exact mul_mem hhO (datum_conj_mem_oddCoreImg hD (hC (P.le_B hgB)) (inv_mem hhO))

theorem TightDatum.good_of_centShape (hD : TightDatum R S t) {N : Subgroup Y} [hN : N.Normal]
    {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = 3) {h3 : (3 : F₂) = 0}
    (P : CentShape Y (N ⊓ Subgroup.centralizer ({t} : Set Y)) t F₁ F₂ h3)
    (hMA : ∀ m ∈ R, m ∈ N → ∀ a ∈ P.A, m * a = a * m) : GoodThreeElement R t := by
  have hBC : ∀ b ∈ P.B, b ∈ Subgroup.centralizer ({t} : Set Y) := fun b hb =>
    (Subgroup.mem_inf.mp (P.le_B hb)).2
  have hconjC : ∀ g ∈ Subgroup.centralizer ({t} : Set Y),
      ∀ c ∈ N ⊓ Subgroup.centralizer ({t} : Set Y),
        g * c * g⁻¹ ∈ N ⊓ Subgroup.centralizer ({t} : Set Y) := fun g hg c hc =>
    Subgroup.mem_inf.mpr ⟨hN.conj_mem c (Subgroup.mem_inf.mp hc).1 g,
      mul_mem (mul_mem hg (Subgroup.mem_inf.mp hc).2) (inv_mem hg)⟩
  have hnorm : ∀ g ∈ Subgroup.centralizer ({t} : Set Y), ∀ m, m ∈ R → m ∈ N →
      g * m * g⁻¹ ∈ R ∧ g * m * g⁻¹ ∈ N := fun g hg m hm hmN =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hg) m).mp hm, hN.conj_mem m hmN g⟩
  have hcomm : ∀ g ∈ Subgroup.centralizer ({t} : Set Y), ∀ m, m ∈ R → m ∈ N →
      ⁅g, m⁆ ∈ R ∧ ⁅g, m⁆ ∈ N := fun g hg m hm hmN => by
    rw [commutatorElement_def]
    exact ⟨mul_mem (hnorm g hg m hm hmN).1 (inv_mem hm),
      mul_mem (hnorm g hg m hm hmN).2 (inv_mem hmN)⟩
  have h8 : ∀ {c : Y}, c ^ 4 = 1 → orderOf c ∣ 8 := fun hc =>
    (orderOf_dvd_of_pow_eq_one hc).trans (by norm_num)
  have hMB : ∀ m ∈ R, m ∈ N → m ∈ P.B := fun m hm hmN =>
    P.cent_A m (Subgroup.mem_inf.mpr ⟨hmN, hD.cent hm⟩) (hMA m hm hmN)
  have hpow4 : ∀ m ∈ R, m ∈ N → m ^ 4 = 1 := fun m hm hmN =>
    TightDatum.pow_four_of_mem_B hD hF₂ P inf_le_right hm (hMB m hm hmN)
  have hsB := hMB s hsR hsN
  have hs4' : s ^ 4 = 1 := by rw [← hs4]; exact pow_orderOf_eq_one s
  have hs2 : s ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hs4] at this
    norm_num at this
  have hQM : ∀ q ∈ P.B, q ^ 4 = 1 → q ^ 2 ≠ 1 → q ∈ R ∧ q ∈ N := by
    intro q hq q4 q2
    obtain ⟨g, hgB, hg⟩ := P.B_exists_conj hF₂ hsB hq hs4' hs2 q4 q2
    have hq' : q = g * s * g⁻¹ := by
      calc q = q * g * g⁻¹ := by group
        _ = g * s * g⁻¹ := by rw [hg]
    rw [hq']
    exact hnorm g (hBC g hgB) s hsR hsN
  have hiM := hQM P.i (P.eB.symm _).2 (P.pow_four_symm SL3.i₀_sq) (P.pow_two_symm_ne SL3.i₀_sq)
  have hjM := hQM P.j (P.eB.symm _).2 (P.pow_four_symm (SL3.j₀_sq h3))
    (P.pow_two_symm_ne (SL3.j₀_sq h3))
  have hxB : P.x ∈ P.B := (P.eB.symm _).2
  refine ⟨P.x, 1, hBC _ hxB, by rw [pow_one]; exact P.x_pow_three, ⟨s, hsR, fun hO => ?_⟩, ?_⟩
  · obtain ⟨hcR, hcN⟩ := hcomm P.x (hBC _ hxB) s hsR hsN
    exact P.B_mul_ne_mul hF₂ hxB hsB P.x_pow_three P.x_ne_one hs4' hs2
      (commutatorElement_eq_one_iff_mul_comm.mp
        (eq_one_of_mem_oddCoreImg hO (h8 (hpow4 _ hcR hcN))))
  intro y hy hyR
  have hyM : ∀ m ∈ R, m ∈ N → y * m = m * y := fun m hm hmN => by
    obtain ⟨hcR, hcN⟩ := hcomm y hy m hm hmN
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (eq_one_of_mem_oddCoreImg (hyR m hm) (h8 (hpow4 _ hcR hcN)))
  have hgA : ∀ g ∈ Subgroup.centralizer ({t} : Set Y), g * P.i = P.i * g →
      g * P.j = P.j * g → ∀ a ∈ P.A, g * a * g⁻¹ ∈ P.A := fun g hg hgi hgj a ha =>
    P.cent_ij _ (hconjC g hg a (P.le_A ha)) (conj_mul_comm hgi (P.comm a ha _ (P.eB.symm _).2))
      (conj_mul_comm hgj (P.comm a ha _ (P.eB.symm _).2))
  have hyi := hyM _ hiM.1 hiM.2
  have hyj := hyM _ hjM.1 hjM.2
  have hxy : y * P.x * y⁻¹ ∈ P.B := by
    refine P.cent_A _ (hconjC y hy _ (P.le_B hxB)) fun a ha => ?_
    have ha' := hgA y⁻¹ (inv_mem hy) (Commute.inv_left (hyi : Commute y P.i)).eq
      (Commute.inv_left (hyj : Commute y P.j)).eq a ha
    rw [inv_inv] at ha'
    have hxa := P.comm _ ha' P.x hxB
    calc y * P.x * y⁻¹ * a = y * (P.x * (y⁻¹ * a * y)) * y⁻¹ := by group
      _ = y * (y⁻¹ * a * y * P.x) * y⁻¹ := by rw [hxa]
      _ = a * (y * P.x * y⁻¹) := by group
  have hu : ∀ q, q ∈ R → q ∈ N →
      P.x⁻¹ * (y * P.x * y⁻¹) * q = q * (P.x⁻¹ * (y * P.x * y⁻¹)) := by
    intro q hq hqN
    have h1 := hnorm P.x (hBC _ hxB) q hq hqN
    have hyq' : y⁻¹ * q * y = q := by rw [mul_assoc, ← hyM q hq hqN, inv_mul_cancel_left]
    have key : y * P.x * y⁻¹ * q * (y * P.x * y⁻¹)⁻¹ = P.x * q * P.x⁻¹ := by
      calc y * P.x * y⁻¹ * q * (y * P.x * y⁻¹)⁻¹ =
          y * (P.x * (y⁻¹ * q * y) * P.x⁻¹) * y⁻¹ := by group
        _ = P.x * q * P.x⁻¹ := by rw [hyq', hyM _ h1.1 h1.2, mul_inv_cancel_right]
    calc P.x⁻¹ * (y * P.x * y⁻¹) * q =
        P.x⁻¹ * (y * P.x * y⁻¹ * q * (y * P.x * y⁻¹)⁻¹) * (y * P.x * y⁻¹) := by group
      _ = q * (P.x⁻¹ * (y * P.x * y⁻¹)) := by rw [key]; group
  have hxu : y * P.x * y⁻¹ = P.x * (P.x⁻¹ * (y * P.x * y⁻¹)) := by group
  rcases P.eq_one_or_eq_t (mul_mem (inv_mem hxB) hxy) (hu _ hiM.1 hiM.2) (hu _ hjM.1 hjM.2)
    with h | h
  · rw [h, mul_one] at hxu
    have hxy' : P.x * y = y * P.x := by
      calc P.x * y = y * P.x * y⁻¹ * y := by rw [hxu]
        _ = y * P.x := by group
    rw [commutatorElement_def, hxy', mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · exfalso
    rw [h] at hxu
    have hxt : P.x * t = t * P.x := Subgroup.mem_centralizer_singleton_iff.mp (hBC _ hxB)
    have h1 : (y * P.x * y⁻¹) ^ 3 = 1 := by rw [conj_pow, P.x_pow_three, mul_one, mul_inv_cancel]
    rw [hxu, Commute.mul_pow hxt 3, P.x_pow_three, one_mul] at h1
    have ht2 : t ^ 2 = 1 := by rw [← hD.order]; exact pow_orderOf_eq_one t
    have ht1 : t = 1 := by
      calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
        _ = 1 := by rw [h1, ht2]; group
    have := hD.order
    rw [ht1, orderOf_one] at this
    exact absurd this (by norm_num)

end CFSG.ClassicalInvolution.Q3.TA3
