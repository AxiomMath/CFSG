module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSCentral
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.J4.QT2LocGenLem
public import CFSG.Sporadic.Schreier.J4SOutGen

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem plane_centralizer_trivial {G : Type*} [Group G] [Finite G] {Q E : Subgroup G} {z : G}
    (hQc : Nat.card Q = 11 ^ 3) (hzQ : z ∈ Q) (hzord : orderOf z = 11)
    (hzc : ∀ q ∈ Q, q * z = z * q)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Subgroup.zpowers z)
    (hcentral : ∀ q ∈ Q, (∀ a ∈ Q, q * a = a * q) → q ∈ Subgroup.zpowers z)
    (hCzN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : Subgroup.centralizer (Q : Set G) ≤ Q) (hexp : ∀ q ∈ Q, q ^ 11 = 1)
    (hEQ : E ≤ Q) (hEel : IsElemAbelian 11 E) (hE : Nat.card E = 11 ^ 2) {u : G}
    (hu : ∀ e ∈ E, u * e = e * u) (hcop : Nat.Coprime (orderOf u) 11) : u = 1 := by
  have h11 : Nat.Prime 11 := by norm_num
  obtain ⟨x, hxE, hxz⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers z) :=
      Subgroup.card_le_of_le (fun e he => hcon e he)
    rw [Nat.card_zpowers, hzord, hE] at h1
    norm_num at h1
  have hxQ : x ∈ Q := hEQ hxE
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = Q ⊓ Subgroup.centralizer ({x} : Set G) := ⟨_, rfl⟩
  have hmemC : ∀ g, g ∈ C ↔ g ∈ Q ∧ g * x = x * g := by
    intro g
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hEC : E ≤ C := by
    intro e he
    refine (hmemC e).2 ⟨hEQ he, ?_⟩
    exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨e, he⟩ ⟨x, hxE⟩)
  have hCQ' : C ≤ Q := fun g hg => ((hmemC g).1 hg).1
  have hdvd1 : Nat.card C ∣ 11 ^ 3 := by
    have := Subgroup.card_dvd_of_le hCQ'
    rwa [hQc] at this
  have hdvd2 : 11 ^ 2 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hEC
    rwa [hE] at this
  have hCE : C = E := by
    have hne : Nat.card C ≠ 11 ^ 3 := by
      intro hc
      have hCeq : C = Q := Subgroup.eq_of_le_of_card_ge hCQ' (by rw [hc, hQc])
      apply hxz
      refine hcentral x hxQ (fun a ha => ?_)
      have : a ∈ C := hCeq ▸ ha
      exact ((hmemC a).1 this).2.symm
    obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow h11).1 hdvd1
    have h2i : 2 ≤ i := by
      have : 11 ^ 2 ∣ 11 ^ i := hCi ▸ hdvd2
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    have hi2 : i = 2 := by
      have : i ≠ 3 := fun h3 => hne (by rw [hCi, h3])
      omega
    exact (Subgroup.eq_of_le_of_card_ge hEC (by rw [hCi, hi2, hE])).symm
  have hqzE : z ∈ E := by
    rw [← hCE]
    exact (hmemC z).2 ⟨hzQ, (hzc x hxQ).symm⟩
  have huqz : u ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hu z hqzE)
  have huN : u ∈ Subgroup.normalizer (Q : Set G) := hCzN huqz
  have hconjQ : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.1 huN q).1 hq
  obtain ⟨y, hyQ, hyE⟩ : ∃ y ∈ Q, y ∉ E := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card Q ≤ Nat.card E := Subgroup.card_le_of_le (fun q hq => hcon q hq)
    rw [hQc, hE] at h1
    norm_num at h1
  have hz'' : ⁅x, y⁆ ∈ Subgroup.zpowers z := hcomm x hxQ y hyQ
  have huz'' : u * ⁅x, y⁆ = ⁅x, y⁆ * u := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz''
    rw [← hn]
    exact (Commute.zpow_right (show Commute u z from hu z hqzE) n).eq
  have hux : u * x * u⁻¹ = x := by
    rw [hu x hxE]; group
  have hcomm_eq : ⁅x, u * y * u⁻¹⁆ = ⁅x, y⁆ := by
    have h1 : u * ⁅x, y⁆ * u⁻¹ = ⁅x, y⁆ := by rw [huz'']; group
    calc ⁅x, u * y * u⁻¹⁆ = ⁅u * x * u⁻¹, u * y * u⁻¹⁆ := by rw [hux]
      _ = u * ⁅x, y⁆ * u⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅x, y⁆ := h1
  obtain ⟨d, hd⟩ : ∃ d : G, d = y⁻¹ * (u * y * u⁻¹) := ⟨_, rfl⟩
  have hdQ : d ∈ Q := by
    rw [hd]; exact Q.mul_mem (Q.inv_mem hyQ) (hconjQ y hyQ)
  have hyd : u * y * u⁻¹ = y * d := by rw [hd]; group
  have hdx : d * x = x * d := by
    have h3 : d * x⁻¹ * d⁻¹ = x⁻¹ := by
      have e1 : x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
        have e0 : x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ = x * (y * d) * x⁻¹ * (y * d)⁻¹ := by group
        rw [e0, ← hyd]
        simpa only [commutatorElement_def] using hcomm_eq
      calc d * x⁻¹ * d⁻¹ = (x * y)⁻¹ * (x * y * (d * x⁻¹ * d⁻¹) * y⁻¹) * y := by group
        _ = (x * y)⁻¹ * (x * y * x⁻¹ * y⁻¹) * y := by rw [e1]
        _ = x⁻¹ := by group
    have h4 : d * x⁻¹ = x⁻¹ * d := by
      calc d * x⁻¹ = (d * x⁻¹ * d⁻¹) * d := by group
        _ = x⁻¹ * d := by rw [h3]
    calc d * x = x * (x⁻¹ * d) * x := by group
      _ = x * (d * x⁻¹) * x := by rw [h4]
      _ = x * d := by group
  have hdE : d ∈ E := by
    rw [← hCE]
    exact (hmemC d).2 ⟨hdQ, hdx⟩
  have hud : u * d = d * u := hu d hdE
  have hpow : ∀ n : ℕ, u ^ n * y * (u ^ n)⁻¹ = y * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hudn : u * d ^ n * u⁻¹ = d ^ n := by
        rw [(Commute.pow_right (show Commute u d from hud) n).eq]; group
      calc u ^ (n + 1) * y * (u ^ (n + 1))⁻¹ = u * (u ^ n * y * (u ^ n)⁻¹) * u⁻¹ := by group
        _ = u * (y * d ^ n) * u⁻¹ := by rw [ih]
        _ = (u * y * u⁻¹) * (u * d ^ n * u⁻¹) := by group
        _ = y * d ^ (n + 1) := by rw [hyd, hudn]; group
  have hdm : d ^ orderOf u = 1 := by
    have h1 := hpow (orderOf u)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    exact mul_left_cancel (a := y) (by rw [mul_one]; exact h1.symm)
  have hd11 : d ^ 11 = 1 := hEel.2 d hdE
  have hd1 : d = 1 := by
    have := pow_gcd_eq_one.2 ⟨hdm, hd11⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  have hyu : u * y = y * u := by
    calc u * y = (u * y * u⁻¹) * u := by group
      _ = y * u := by rw [hyd, hd1, mul_one]
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = Subgroup.closure ((E : Set G) ∪ {y}) := ⟨_, rfl⟩
  have hEH : E ≤ H := fun e he => hH ▸ Subgroup.subset_closure (Or.inl he)
  have hyH : y ∈ H := hH ▸ Subgroup.subset_closure (Or.inr rfl)
  have hHQ : H ≤ Q := by
    rw [hH, Subgroup.closure_le]
    rintro a (ha | rfl)
    · exact hEQ ha
    · exact hyQ
  have hHQ' : H = Q := by
    have hd1' : Nat.card H ∣ 11 ^ 3 := by
      have := Subgroup.card_dvd_of_le hHQ
      rwa [hQc] at this
    have hd2' : 11 ^ 2 ∣ Nat.card H := by
      have := Subgroup.card_dvd_of_le hEH
      rwa [hE] at this
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow h11).1 hd1'
    have h2i : 2 ≤ i := by
      have : 11 ^ 2 ∣ 11 ^ i := hHi ▸ hd2'
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    have hi3 : i = 3 := by
      by_contra hne
      have hi2 : i = 2 := by omega
      have hEeq : E = H := Subgroup.eq_of_le_of_card_ge hEH (by rw [hHi, hi2, hE])
      exact hyE (hEeq ▸ hyH)
    exact Subgroup.eq_of_le_of_card_ge hHQ (by rw [hHi, hi3, hQc])
  have huC : u ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [← hHQ'] at hq
    have hHle : H ≤ Subgroup.centralizer ({u} : Set G) := by
      rw [hH, Subgroup.closure_le]
      rintro a (ha | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hu a ha).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 hyu.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hHle hq)
  have huQ : u ∈ Q := hCQ huC
  have hu11 : u ^ 11 = 1 := hexp u huQ
  exact orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hu11))

end CFSG.HardMathSupport.Dickson.I271
