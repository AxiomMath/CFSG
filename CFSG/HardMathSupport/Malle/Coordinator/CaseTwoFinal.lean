module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSetup
public import CFSG.HardMathSupport.Malle.Coordinator.InvertingInvolution
public import CFSG.HardMathSupport.Malle.Coordinator.NoOddNormal
public import CFSG.HardMathSupport.Malle.Proving.LeNormalizerOfIsolated
import all CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

open CFSG.AGLEmbedding CFSG.Quasithin
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem agree_mul {Z : Subgroup Y} {a a' b b' : Y}
    (hb : b' ∈ Subgroup.normalizer (Z : Set Y)) (hab : ∀ z ∈ Z, a * z * a⁻¹ = b * z * b⁻¹)
    (hab' : ∀ z ∈ Z, a' * z * a'⁻¹ = b' * z * b'⁻¹) :
    ∀ z ∈ Z, (a * a') * z * (a * a')⁻¹ = (b * b') * z * (b * b')⁻¹ := by
  intro z hz
  have hz' : b' * z * b'⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hb z).mp hz
  calc (a * a') * z * (a * a')⁻¹ = a * (a' * z * a'⁻¹) * a⁻¹ := by group
    _ = a * (b' * z * b'⁻¹) * a⁻¹ := by rw [hab' z hz]
    _ = b * (b' * z * b'⁻¹) * b⁻¹ := hab _ hz'
    _ = (b * b') * z * (b * b')⁻¹ := by group

theorem agree_inv {Z : Subgroup Y} {a b : Y} (ha : a ∈ Subgroup.normalizer (Z : Set Y))
    (hab : ∀ z ∈ Z, a * z * a⁻¹ = b * z * b⁻¹) :
    ∀ z ∈ Z, a⁻¹ * z * a⁻¹⁻¹ = b⁻¹ * z * b⁻¹⁻¹ := by
  intro z hz
  have hz' : a⁻¹ * z * a ∈ Z := (Subgroup.mem_normalizer_iff''.mp ha z).mp hz
  have h1 := hab _ hz'
  have h2 : a * (a⁻¹ * z * a) * a⁻¹ = z := by group
  rw [h2] at h1
  calc a⁻¹ * z * a⁻¹⁻¹ = b⁻¹ * (b * (a⁻¹ * z * a) * b⁻¹) * b := by group
    _ = b⁻¹ * z * b⁻¹⁻¹ := by rw [← h1]; group

theorem reeF4CaseTwoInvariant_of
    (hTor : ReeF4CyclicToralCentralizers) (hInv : ReeF4InvolutionCentralizerCoprime)
    (hNc : ReeF4SylowNormalizerCard) (hSig : ReeF4OuterSigmaFixedOrder)
    (hSieve : ReeF4IndexSieve) : ReeF4CaseTwoInvariant := by
  intro Y _ _ K d hd hKn e hCK T h3 M hMK hTM hNM hMne hCase
  have := hKn
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hKcard, hKidx, hPcard, hP5, hZcard, hCZ, -, φ, hφT, D, hφfix⟩ :=
    exists_caseTwo_data hSig K d hd e hCK T h3
  obtain ⟨-, hZe, -, hCZT, i, j, h, t, hGL⟩ := LocalAction.reeF4_core_of_certs K d hd e hCK T h3
  set P := (T : Subgroup Y) ⊓ K with hP
  set Z := centerOf (T : Subgroup Y) with hZ
  set N := K ⊓ Subgroup.normalizer (P : Set Y) with hN
  have hPK : P ≤ K := inf_le_right
  have hNcard : Nat.card N = 60000 := by
    have hPidx : ¬ 5 ∣ P.relIndex K := OvergroupTransport.not_dvd_relIndex_inf_sylow K T
    let P' : Sylow 5 K := (hP5.comap_subtype (K := K)).toSylow hPidx
    have h := hNc K d hd e P'
    have hPset : ((P' : Subgroup K) : Set K) = ((P.subgroupOf K : Subgroup K) : Set K) := rfl
    rw [hPset, ← Subgroup.subgroupOf_normalizer_eq hPK] at h
    have : (Subgroup.normalizer (P : Set Y)).subgroupOf K = N.subgroupOf K := by
      ext x
      simp [Subgroup.mem_subgroupOf, hN]
    rw [this, card_subgroupOf_of_le inf_le_left] at h
    exact h
  have hTor' : ∀ p ∈ ({13, 61, 331, 1321} : Finset ℕ), ∀ w ∈ K, orderOf w = p →
      Nat.card (K ⊓ Subgroup.centralizer ({w} : Set Y) : Subgroup Y) ∣
        cyclicCentralizerBound p := by
    intro p hp w hwK hw
    obtain ⟨h1, h2, h3'⟩ := hTor K d hd e ⟨w, hwK⟩
    have hwo : orderOf (⟨w, hwK⟩ : K) = p := by rw [← Subgroup.orderOf_coe]; exact hw
    have hexp : ∀ E : ℕ, (∀ g ∈ Subgroup.centralizer ({(⟨w, hwK⟩ : K)} : Set K), g ^ E = 1) →
        ∀ g ∈ (K ⊓ Subgroup.centralizer ({w} : Set Y) : Subgroup Y), g ^ E = 1 := by
      intro E hE g hg
      have hg' : (⟨g, hg.1⟩ : K) ∈ Subgroup.centralizer ({(⟨w, hwK⟩ : K)} : Set K) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
      simpa using congrArg Subtype.val (hE _ hg')
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [show cyclicCentralizerBound 13 = 793 by simp [cyclicCentralizerBound]]
      exact card_dvd_of_pow_eq_one (E := 793) (X := 793) (Q := reeF4Order / 793) inf_le_left
        (by rw [hKcard]; norm_num [reeF4Order]) (by norm_num [reeF4Order])
        (hexp 793 (h1 (Or.inl hwo)))
    · rw [show cyclicCentralizerBound 61 = 793 by simp [cyclicCentralizerBound]]
      exact card_dvd_of_pow_eq_one (E := 793) (X := 793) (Q := reeF4Order / 793) inf_le_left
        (by rw [hKcard]; norm_num [reeF4Order]) (by norm_num [reeF4Order])
        (hexp 793 (h1 (Or.inr hwo)))
    · rw [show cyclicCentralizerBound 331 = 8937 by simp [cyclicCentralizerBound]]
      exact card_dvd_of_pow_eq_one (E := 993) (X := 8937) (Q := reeF4Order / 8937) inf_le_left
        (by rw [hKcard]; norm_num [reeF4Order]) (by norm_num [reeF4Order])
        (hexp 993 (h2 hwo))
    · rw [show cyclicCentralizerBound 1321 = 1321 by simp [cyclicCentralizerBound]]
      exact card_dvd_of_pow_eq_one (E := 1321) (X := 1321) (Q := reeF4Order / 1321) inf_le_left
        (by rw [hKcard]; norm_num [reeF4Order]) (by norm_num [reeF4Order])
        (hexp 1321 (h3' hwo))
  have hInv' : ∀ s ∈ K, s ≠ 1 → s * s = 1 →
      ¬ 15 ∣ Nat.card (K ⊓ Subgroup.centralizer ({s} : Set Y) : Subgroup Y) := by
    intro s hsK hs1 hs2
    have h := hInv K d hd e ⟨s, hsK⟩ (fun h => hs1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hs2))
    rwa [card_centralizer_subtype] at h
  have hφKn : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K := fun k hk => by
    simpa using hKn.conj_mem k hk φ⁻¹
  have hφM : φ ∈ Subgroup.normalizer (M : Set Y) := hTM hφT
  have hC : ∀ x ∈ Z, x ≠ 1 →
      M ⊓ Subgroup.centralizer ({x} : Set Y) ≤ Subgroup.normalizer (P : Set Y) :=
    fun x hx hx1 => hCase x (D.le hx) (D.pow_five x hx) hx1
  have hMN : M ⊓ Subgroup.normalizer (P : Set Y) = N :=
    le_antisymm (inf_le_inf_right _ hMK) (le_inf hNM inf_le_right)
  have hEnd : ¬ 2 ∣ N.relIndex M → M ≤ Subgroup.normalizer (P : Set Y) := by
    intro hodd
    have hq := hGL.toIsQ8Data
    have hNZT : Subgroup.normalizer (Z : Set Y) ≤ Subgroup.normalizer (P : Set Y) := by
      intro g hg
      have hgT : g ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
        LocalAction.normalizer_le_normalizer_of_centralizer_eq hCZT hg
      rw [Subgroup.mem_normalizer_iff] at hgT ⊢
      intro x
      rw [hP, Subgroup.mem_inf, Subgroup.mem_inf, hgT x]
      exact and_congr_right fun _ => ⟨fun hx => hKn.conj_mem x hx g, fun hx => by
        simpa [mul_assoc] using hKn.conj_mem _ hx g⁻¹⟩
    have hiP := hNZT hq.mem_i
    have hjP := hNZT hq.mem_j
    have hZne : ∃ z ∈ Z, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
      rw [this, Subgroup.card_bot] at hZcard
      norm_num at hZcard
    obtain ⟨u, huN, hu1, hu2, hinv⟩ := exists_inverting_involution hKidx hPK D.comm hP5 D.le
      D.pow_five D.omega hZne hCZ hiP hq.inv_ii
    have hiso := isolated_of_inverting_involution hPK D.comm hP5 hPcard D.le D.omega hCZ
      hNcard hInv' hMK hNM hodd huN hu1 hu2 hinv
    have hi4 : ∀ z ∈ Z, i ^ 4 * z * (i ^ 4)⁻¹ = z := by
      intro z hz
      have h1 := hq.inv_ii z hz
      have h2 := hq.inv_ii z⁻¹ (Z.inv_mem hz)
      have e : i ^ 4 = (i * i) * (i * i) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      calc i ^ 4 * z * (i ^ 4)⁻¹ = (i * i) * ((i * i) * z * (i * i)⁻¹) * (i * i)⁻¹ := by
            rw [e]; group
        _ = z := by rw [h1]; rw [h2]; group
    have hj4 : ∀ z ∈ Z, j ^ 4 * z * (j ^ 4)⁻¹ = z := by
      intro z hz
      have h1 := hq.inv_jj z hz
      have h2 := hq.inv_jj z⁻¹ (Z.inv_mem hz)
      have e : j ^ 4 = (j * j) * (j * j) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      calc j ^ 4 * z * (j ^ 4)⁻¹ = (j * j) * ((j * j) * z * (j * j)⁻¹) * (j * j)⁻¹ := by
            rw [e]; group
        _ = z := by rw [h1]; rw [h2]; group
    obtain ⟨i₀, hi₀z, hi₀K, hi₀⟩ := exists_pow_mem_conj_eq hKidx hi4
    obtain ⟨j₀, hj₀z, hj₀K, hj₀⟩ := exists_pow_mem_conj_eq hKidx hj4
    have hi₀N : i₀ ∈ N := ⟨hi₀K, (Subgroup.zpowers_le.mpr hiP) hi₀z⟩
    have hj₀N : j₀ ∈ N := ⟨hj₀K, (Subgroup.zpowers_le.mpr hjP) hj₀z⟩
    have hi₀Z : i₀ ∈ Subgroup.normalizer (Z : Set Y) :=
      (Subgroup.zpowers_le.mpr hq.mem_i) hi₀z
    have hj₀Z : j₀ ∈ Subgroup.normalizer (Z : Set Y) :=
      (Subgroup.zpowers_le.mpr hq.mem_j) hj₀z
    have hii : ∀ z ∈ Z, (i₀ * i₀) * z * (i₀ * i₀)⁻¹ = z⁻¹ := by
      intro z hz
      rw [agree_mul hq.mem_i hi₀ hi₀ z hz]
      exact hq.inv_ii z hz
    have hjj : ∀ z ∈ Z, (j₀ * j₀) * z * (j₀ * j₀)⁻¹ = z⁻¹ := by
      intro z hz
      rw [agree_mul hq.mem_j hj₀ hj₀ z hz]
      exact hq.inv_jj z hz
    have hij : ∀ z ∈ Z, ⁅i₀, j₀⁆ * z * ⁅i₀, j₀⁆⁻¹ = z⁻¹ := by
      intro z hz
      have h1 := agree_mul (Subgroup.inv_mem _ hq.mem_j)
        (agree_mul (Subgroup.inv_mem _ hq.mem_i) (agree_mul hq.mem_j hi₀ hj₀)
          (agree_inv hi₀Z hi₀)) (agree_inv hj₀Z hj₀) z hz
      rw [commutatorElement_def, h1]
      have := hq.inv_comm z hz
      rw [commutatorElement_def] at this
      exact this
    have hZN : N ≤ Subgroup.normalizer (Z : Set Y) := fun x hx => D.normalizer_le_normalizer hx.2
    have hidx96 : P.relIndex N = 96 := by
      have h1 := Subgroup.relIndex_mul_card (H := P) (K := N)
      rw [inf_eq_left.mpr (le_inf hPK Subgroup.le_normalizer), hPcard, hNcard] at h1
      omega
    have hW : ∀ W : Subgroup Y, Odd (Nat.card W) → P ≤ W →
        W ≤ M ⊓ Subgroup.normalizer (P : Set Y) →
        (∀ g ∈ M ⊓ Subgroup.normalizer (P : Set Y), ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = P := by
      intro W hWodd hPW hWN hWn
      rw [hMN] at hWN hWn
      exact eq_of_odd_normal (le_inf hPK Subgroup.le_normalizer) inf_le_right D.comm hP5 D.le
        D.pow_five (by rw [hZcard]) hZN (fun x hx => hCZ ⟨hx.1.1, hx.2⟩) hidx96 hi₀N hj₀N hii hjj
        hij hPW hWN hWn hWodd
    have hPidxM : ¬ 5 ∣ P.relIndex M := by
      intro h5
      have hPidx : ¬ 5 ∣ P.relIndex K := OvergroupTransport.not_dvd_relIndex_inf_sylow K T
      apply hPidx
      rw [← Subgroup.relIndex_mul_relIndex P M K ((le_inf hPK Subgroup.le_normalizer).trans hNM)
        hMK]
      exact Dvd.dvd.mul_right h5 _
    have hinv' : ∀ x ∈ P, u * x * u⁻¹ = x⁻¹ := by
      intro x hx
      have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
      rw [hu]; exact hinv x hx
    exact CFSG.HardMathSupport.Malle.Proving.le_normalizer_of_isolated Nat.prime_five
      (by decide) ((le_inf hPK Subgroup.le_normalizer).trans hNM) hP5 hPidxM D.comm D.le hZe
      (by rw [hZcard]; norm_num) hC hW (hNM huN) hu1 hu2 hinv' hiso
  exact caseTwo_core D hKcard hPcard hZcard hPK hP5 hCZ hφKn hφfix hNcard hTor' hSieve hMK hφM
    hNM hC hEnd

end CFSG.HardMathSupport.Malle.Coordinator
