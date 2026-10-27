module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_pow_mul_eq {L : Subgroup X} {l w : X} (hl : l ∈ L)
    (hw : w ∈ normalizer (L : Set X)) (m : ℕ) : ∃ l' ∈ L, (l * w) ^ m = l' * w ^ m := by
  induction m with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, one_mul]⟩
  | succ m ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hwm : w ^ m ∈ normalizer (L : Set X) := pow_mem hw m
    refine ⟨l' * (w ^ m * l * (w ^ m)⁻¹), mul_mem hl' ((mem_normalizer_iff.mp hwm l).mp hl), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem exists_mul_of_mem_oddGen [Finite X] {G L K : Subgroup X}
    (hKL : K ≤ normalizer (L : Set X))
    (hlift : ∀ z ∈ G, Odd (orderOf z) → ∃ l ∈ L, l⁻¹ * z ∈ K) {z : X} (hz : z ∈ oddGen G) :
    ∃ l ∈ L, ∃ u ∈ oddGen K, z = l * u := by
  change z ∈ Subgroup.closure _ at hz
  induction hz using closure_induction with
  | mem z hz =>
    obtain ⟨hzG, hodd⟩ := hz
    obtain ⟨l, hl, hw⟩ := hlift z hzG hodd
    have hzlw : z = l * (l⁻¹ * z) := by rw [mul_inv_cancel_left]
    obtain ⟨b, c, hc, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (l⁻¹ * z)).ne'
    have hv : (l⁻¹ * z) ^ 2 ^ b ∈ oddGen K := by
      refine mem_oddGen (pow_mem hw _) ?_
      have h1 : ((l⁻¹ * z) ^ 2 ^ b) ^ c = 1 := by rw [← pow_mul, ← hord, pow_orderOf_eq_one]
      exact hc.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
    obtain ⟨l₁, hl₁, h1⟩ := exists_pow_mul_eq hl (hKL hw) (2 ^ b)
    have hcop : Nat.Coprime (2 ^ b) (orderOf z) :=
      Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hodd)
    obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime hcop
    obtain ⟨l₂, hl₂, h2⟩ := exists_pow_mul_eq hl₁ (hKL (oddGen_le K hv)) d
    refine ⟨l₂, hl₂, ((l⁻¹ * z) ^ 2 ^ b) ^ d, pow_mem hv d, ?_⟩
    rw [← h2, ← h1, ← hzlw, hd]
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨l₁, hl₁, u₁, hu₁, rfl⟩ := h₁
    obtain ⟨l₂, hl₂, u₂, hu₂, rfl⟩ := h₂
    have hu₁N := hKL (oddGen_le K hu₁)
    exact ⟨l₁ * (u₁ * l₂ * u₁⁻¹), mul_mem hl₁ ((mem_normalizer_iff.mp hu₁N l₂).mp hl₂),
      u₁ * u₂, mul_mem hu₁ hu₂, by group⟩
  | inv z _ h =>
    obtain ⟨l, hl, u, hu, rfl⟩ := h
    have huN := inv_mem (hKL (oddGen_le K hu))
    exact ⟨u⁻¹ * l⁻¹ * u⁻¹⁻¹, (mem_normalizer_iff.mp huN l⁻¹).mp (inv_mem hl), u⁻¹,
      inv_mem hu, by group⟩

variable {M : Subgroup X} {n : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem IsPermAction.apply_eq_of_le (hρ : IsPermAction θ ρ) (hn : 4 ≤ n) {L : Subgroup X}
    (hLM : L ≤ M) {θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n)}
    {ρL : ↥(normalizer (L : Set X)) →* Perm (Fin n)} (hρL : IsPermAction θL ρL)
    (hθL : ∀ (x : X) (hxL : x ∈ L) (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M))
    {z : X} (hzL : z ∈ normalizer (L : Set X)) (hzM : z ∈ normalizer (M : Set X)) :
    ρL ⟨z, hzL⟩ = ρ ⟨z, hzM⟩ := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := θL.surjective b
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  change ρL _ * _ * (ρL _)⁻¹ = ρ _ * _ * (ρ _)⁻¹
  rw [← hρL, hθL (w : X) w.2 (hLM w.2), ← hρ]
  have h1 : ((L.normalizerMonoidHom ⟨z, hzL⟩ w : ↥L) : X) = z * w * z⁻¹ := by simp
  have h2 : ((M.normalizerMonoidHom ⟨z, hzM⟩ ⟨w, hLM w.2⟩ : ↥M) : X) = z * w * z⁻¹ := by simp
  have h3 := hθL _ (L.normalizerMonoidHom ⟨z, hzL⟩ w).2 (hLM (L.normalizerMonoidHom ⟨z, hzL⟩ w).2)
  have h4 : (⟨_, hLM (L.normalizerMonoidHom ⟨z, hzL⟩ w).2⟩ : ↥M) =
      M.normalizerMonoidHom ⟨z, hzM⟩ ⟨w, hLM w.2⟩ := Subtype.ext (h1.trans h2.symm)
  rw [h4] at h3
  exact congrArg Subtype.val h3

theorem IsPermAction.exists_mem_layer_apply_eq (hρ : IsPermAction θ ρ) (hn : 4 ≤ n)
    {L : Subgroup X} (hLM : L ≤ M) (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n))
    (hθL : ∀ (x : X) (hxL : x ∈ L) (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M))
    {z : X} (hzN : z ∈ normalizer (M : Set X)) (hzA : ρ ⟨z, hzN⟩ ∈ alternatingGroup (Fin n)) :
    ∃ (l : X) (hl : l ∈ L), ρ ⟨l, le_normalizer (hLM hl)⟩ = ρ ⟨z, hzN⟩ := by
  obtain ⟨q, hq⟩ := θL.surjective ⟨ρ ⟨z, hzN⟩, hzA⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨l, l.2, ?_⟩
  rw [hρ.apply_of_mem hn ⟨l, hLM l.2⟩, ← hθL l l.2 (hLM l.2)]
  exact congrArg Subtype.val hq

theorem IsPermAction.exists_mul_of_mem_oddGen_centralizer (hρ : IsPermAction θ ρ) [Finite X]
    (hn : 4 ≤ n) {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X)) {a : X}
    (hCa : centralizer ({a} : Set X) ≤ H) {L : Subgroup X} (hLM : L ≤ M)
    (hLC : L ≤ centralizer ({a} : Set X)) (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n))
    (hθL : ∀ (x : X) (hxL : x ∈ L) (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M))
    (hLN : ∀ g ∈ normalizer (M : Set X), g * a = a * g → g ∈ normalizer (L : Set X))
    {z : X} (hz : z ∈ oddGen (centralizer ({a} : Set X))) :
    ∃ l ∈ L, ∃ u ∈ oddGen (centralizer ({a} : Set X) ⊓
      (H ⊓ UnbalancedLayer.coreActionKernel M)), z = l * u := by
  refine exists_mul_of_mem_oddGen (fun w hw => ?_) (fun w hw hodd => ?_) hz
  · exact hLN w (hHN (hCa (mem_inf.mp hw).1)) (mem_centralizer_singleton_iff.mp (mem_inf.mp hw).1)
  · have hwN : w ∈ normalizer (M : Set X) := hHN (hCa hw)
    have hwA : ρ ⟨w, hwN⟩ ∈ alternatingGroup (Fin n) := by
      rw [Perm.mem_alternatingGroup]
      refine sign_eq_one_of_odd_orderOf ?_
      have h1 : Odd (orderOf (⟨w, hwN⟩ : ↥(normalizer (M : Set X)))) := by
        rw [Subgroup.orderOf_mk]
        exact hodd
      exact h1.of_dvd_nat (orderOf_map_dvd ρ _)
    obtain ⟨l, hl, hρl⟩ := hρ.exists_mem_layer_apply_eq hn hLM θL hθL hwN hwA
    refine ⟨l, hl, mem_inf.mpr ⟨mul_mem (inv_mem (hLC hl)) hw,
      mem_inf.mpr ⟨hCa (mul_mem (inv_mem (hLC hl)) hw), ?_⟩⟩⟩
    have hlwN : l⁻¹ * w ∈ normalizer (M : Set X) := mul_mem (inv_mem (le_normalizer (hLM hl))) hwN
    refine hρ.mem_coreActionKernel hlwN ?_
    have h1 : (⟨l⁻¹ * w, hlwN⟩ : ↥(normalizer (M : Set X))) =
        (⟨l, le_normalizer (hLM hl)⟩ : ↥(normalizer (M : Set X)))⁻¹ * ⟨w, hwN⟩ := rfl
    rw [h1, map_mul, map_inv, hρl, inv_mul_cancel]

theorem IsPermAction.mem_oddGen_kernel_of_mem_oddGen (hρ : IsPermAction θ ρ) [Finite X]
    (hn : 4 ≤ n) {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X)) {a : X}
    (hCa : centralizer ({a} : Set X) ≤ H) {L : Subgroup X} (hLM : L ≤ M)
    (hLC : L ≤ centralizer ({a} : Set X)) (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n))
    (hθL : ∀ (x : X) (hxL : x ∈ L) (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M))
    (hLN : ∀ g ∈ normalizer (M : Set X), g * a = a * g → g ∈ normalizer (L : Set X))
    {z : X} (hz : z ∈ oddGen (centralizer ({a} : Set X)))
    (hzK : z ∈ H ⊓ UnbalancedLayer.coreActionKernel M) :
    z ∈ oddGen (centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M)) := by
  obtain ⟨l, hl, u, hu, rfl⟩ :=
    hρ.exists_mul_of_mem_oddGen_centralizer hn hHN hCa hLM hLC θL hθL hLN hz
  have huK := (mem_inf.mp (oddGen_le _ hu)).2
  have hlK : l ∈ H ⊓ UnbalancedLayer.coreActionKernel M := by
    have h := mul_mem hzK (inv_mem huK)
    rwa [mul_inv_cancel_right] at h
  refine mul_mem (mem_oddGen (mem_inf.mpr ⟨hLC hl, hlK⟩) ?_) hu
  exact odd_orderOf_of_mem_oddCoreIn
    (mem_core_of_mem_coreActionKernel hρ hn (hLM hl) (mem_inf.mp hlK).2)

variable {L : Subgroup X} {θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n)}
  {ρL : ↥(normalizer (L : Set X)) →* Perm (Fin n)}

theorem IsPermAction.exists_lift_oddCentGen_inf (hρL : IsPermAction θL ρL) [Finite X]
    (hn : 4 ≤ n) {c : X} (hc : c ∈ normalizer (L : Set X)) (hc2 : c * c = 1)
    {π : Perm (Fin n)} (hπ : π ∈ oddCentGen (ρL ⟨c, hc⟩)) :
    ∃ (q : X) (hq : q ∈ L), q ∈ oddGen (L ⊓ centralizer ({c} : Set X)) ∧
      ρL ⟨q, le_normalizer hq⟩ = π := by
  change π ∈ Subgroup.closure _ at hπ
  induction hπ using closure_induction with
  | mem π hπ' =>
    obtain ⟨hπA, hπσ, hodd⟩ := hπ'
    obtain ⟨x, hxc, hx⟩ := hρL.exists_lift hc hc2 (b := ⟨π, hπA⟩) hπσ
    have hρx : ρL ⟨x, le_normalizer x.2⟩ = π := by
      rw [hρL.apply_of_mem hn x, hx]
    let f : ↥L →* Perm (Fin n) := ρL.comp (Subgroup.inclusion le_normalizer)
    have hfx : f x = π := hρx
    obtain ⟨k, hk, hfk⟩ := exists_pow_odd_of_odd_map f x (by rw [hfx]; exact hodd)
    refine ⟨((x ^ k : ↥L) : X), (x ^ k).2, mem_oddGen ⟨(x ^ k).2, ?_⟩ ?_, ?_⟩
    · rw [Subgroup.coe_pow]
      exact pow_mem hxc k
    · rw [Subgroup.orderOf_coe]
      exact hk
    · rw [← hfx, ← hfk]
      rfl
  | one => exact ⟨1, one_mem _, one_mem _, map_one ρL⟩
  | mul π₁ π₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, hq₁, hq₁o, hρ₁⟩ := h₁
    obtain ⟨q₂, hq₂, hq₂o, hρ₂⟩ := h₂
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, mul_mem hq₁o hq₂o, ?_⟩
    rw [← hρ₁, ← hρ₂, ← map_mul]
    rfl
  | inv π _ h =>
    obtain ⟨q, hq, hqo, hρq⟩ := h
    refine ⟨q⁻¹, inv_mem hq, inv_mem hqo, ?_⟩
    rw [← hρq, ← map_inv]
    rfl

theorem IsPermAction.exists_involution_mem_oddGen_inf (hρL : IsPermAction θL ρL) [Finite X]
    (hn : 4 ≤ n) {c : X} (hc : c ∈ normalizer (L : Set X)) (hc2 : c * c = 1)
    (hcA : ρL ⟨c, hc⟩ ∈ alternatingGroup (Fin n)) (h8 : 8 ≤ (ρL ⟨c, hc⟩).support.card) :
    ∃ (y : X) (hy : y ∈ L), y ∈ oddGen (L ⊓ centralizer ({c} : Set X)) ∧ y * y = 1 ∧
      ρL ⟨y, le_normalizer hy⟩ = ρL ⟨c, hc⟩ := by
  classical
  have hσ2 : ρL ⟨c, hc⟩ * ρL ⟨c, hc⟩ = 1 := by
    rw [← map_mul, show (⟨c, hc⟩ : ↥(normalizer (L : Set X))) * ⟨c, hc⟩ = 1 from
      Subtype.ext hc2, map_one]
  obtain ⟨q, hq, hqo, hρq⟩ :=
    hρL.exists_lift_oddCentGen_inf hn hc hc2 (mem_oddCentGen_self hσ2 hcA h8)
  obtain ⟨b, d, hd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
  have hyL : q ^ d ∈ L := pow_mem hq d
  have hρy : ρL ⟨q ^ d, le_normalizer hyL⟩ = ρL ⟨c, hc⟩ := by
    have h1 : (⟨q ^ d, le_normalizer hyL⟩ : ↥(normalizer (L : Set X))) =
        ⟨q, le_normalizer hq⟩ ^ d := rfl
    rw [h1, map_pow, hρq]
    obtain ⟨j, rfl⟩ := hd
    rw [pow_succ, pow_mul, sq, hσ2, one_pow, one_mul]
  refine ⟨q ^ d, hyL, pow_mem hqo d, ?_, hρy⟩
  have hyy : ρL ⟨q ^ d * q ^ d, le_normalizer (mul_mem hyL hyL)⟩ = 1 := by
    have h1 : (⟨q ^ d * q ^ d, le_normalizer (mul_mem hyL hyL)⟩ : ↥(normalizer (L : Set X))) =
        ⟨q ^ d, le_normalizer hyL⟩ * ⟨q ^ d, le_normalizer hyL⟩ := rfl
    rw [h1, map_mul, hρy, hσ2]
  have hcore : q ^ d * q ^ d ∈ (pPrimeCore 2 ↥L).map L.subtype :=
    mem_core_of_mem_coreActionKernel hρL hn (mul_mem hyL hyL)
      (hρL.mem_coreActionKernel _ hyy)
  have hodd := odd_orderOf_of_mem_oddCoreIn hcore
  have h2pow : orderOf (q ^ d * q ^ d) ∣ 2 ^ b := by
    have h1 : (q ^ d) ^ 2 ^ b = 1 := by
      rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    rw [← sq]
    exact (orderOf_pow_dvd 2).trans (orderOf_dvd_of_pow_eq_one h1)
  have h1 : orderOf (q ^ d * q ^ d) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hodd)) h2pow
  exact orderOf_eq_one_iff.mp h1

theorem exists_kernel_involution [Finite X] {H : Subgroup X} (hMH : M ≤ H)
    (hMpc : IsPComponent 2 (M.subgroupOf H)) (hHN : H ≤ normalizer (M : Set X)) (hn : 9 ≤ n)
    (hρ : IsPermAction θ ρ) {Q : Subgroup X} (hQK : Q ≤ H ⊓ UnbalancedLayer.coreActionKernel M)
    (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2)
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ → normalizer (T : Set X) ≤ H) {a g : X}
    (ha : a ∈ Q) (ha1 : a ≠ 1) {x : X} (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X)))
    (hx2 : x * x = 1) (hx' : g * x * g⁻¹ ∈ H) (hx'M : g * x * g⁻¹ ∉ M)
    (h8 : 8 ≤ (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card) :
    ∃ (y : X) (hy : y ∈ M), y * y = 1 ∧ y * (g * x * g⁻¹) = g * x * g⁻¹ * y ∧
      ρ ⟨y, le_normalizer hy⟩ = ρ ⟨g * x * g⁻¹, hHN hx'⟩ ∧
      y ∈ oddGen (centralizer ({g * x * g⁻¹} : Set X) ⊓ centralizer ({a} : Set X)) ∧
      y * (g * x * g⁻¹) ∈ oddGen (centralizer ({a} : Set X) ⊓
        (H ⊓ UnbalancedLayer.coreActionKernel M)) ∧
      centralizer ({y * (g * x * g⁻¹)} : Set X) ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  have ha2 : IsPGroup 2 (zpowers a) := hQ2.to_le (zpowers_le.mpr ha)
  have hCa : centralizer ({a} : Set X) ≤ H := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  obtain ⟨La, hLaM, hLaC, -, -, ⟨θLa, hθLa⟩, hLaN⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  have hx'N : g * x * g⁻¹ ∈ normalizer (M : Set X) := hHN hx'
  have hx'o : g * x * g⁻¹ ∈ oddGen (centralizer ({a} : Set X)) := by
    have h1 := conj_mem_oddGen_centralizer (g := g) hxo
    rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at h1
  have hx'A : ρ ⟨g * x * g⁻¹, hx'N⟩ ∈ alternatingGroup (Fin n) :=
    mem_alternatingGroup_of_mem_oddGen (ρ := ρ) (hCa.trans hHN) hx'o hx'N
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'a : g * x * g⁻¹ * a = a * (g * x * g⁻¹) :=
    mem_centralizer_singleton_iff.mp (oddGen_le _ hx'o)
  have hx'La : g * x * g⁻¹ ∈ normalizer (La : Set X) := hLaN _ hx'N hx'a
  obtain ⟨ρa, hρa⟩ := exists_isPermAction (M := La) (by omega) (by omega) θLa
  have hρax' : ρa ⟨g * x * g⁻¹, hx'La⟩ = ρ ⟨g * x * g⁻¹, hx'N⟩ :=
    hρ.apply_eq_of_le (by omega) hLaM hρa hθLa hx'La hx'N
  obtain ⟨y, hyLa, hyo, hy2, hρay⟩ := hρa.exists_involution_mem_oddGen_inf (by omega) hx'La hx'2
    (by rw [hρax']; exact hx'A) (by rw [hρax']; omega)
  have hyM : y ∈ M := hLaM hyLa
  have hρy : ρ ⟨y, le_normalizer hyM⟩ = ρ ⟨g * x * g⁻¹, hx'N⟩ := by
    rw [hρ.apply_of_mem (by omega) ⟨y, hyM⟩, ← hθLa y hyLa hyM,
      ← hρa.apply_of_mem (by omega) ⟨y, hyLa⟩, hρay, hρax']
  have hyx' : y * (g * x * g⁻¹) = g * x * g⁻¹ * y :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp (oddGen_le _ hyo)).2
  have hle : La ⊓ centralizer ({g * x * g⁻¹} : Set X) ≤
      centralizer ({g * x * g⁻¹} : Set X) ⊓ centralizer ({a} : Set X) := fun z hz =>
    mem_inf.mpr ⟨(mem_inf.mp hz).2, hLaC (mem_inf.mp hz).1⟩
  have hyo' : y ∈ oddGen (centralizer ({g * x * g⁻¹} : Set X) ⊓ centralizer ({a} : Set X)) :=
    oddGen_mono hle hyo
  have hkH : y * (g * x * g⁻¹) ∈ H := mul_mem (hMH hyM) hx'
  have hkK : y * (g * x * g⁻¹) ∈ UnbalancedLayer.coreActionKernel M := by
    refine hρ.mem_coreActionKernel (hHN hkH) ?_
    have h1 : (⟨y * (g * x * g⁻¹), hHN hkH⟩ : ↥(normalizer (M : Set X))) =
        ⟨y, le_normalizer hyM⟩ * ⟨g * x * g⁻¹, hx'N⟩ := rfl
    have h2 : (⟨g * x * g⁻¹, hx'N⟩ : ↥(normalizer (M : Set X))) * ⟨g * x * g⁻¹, hx'N⟩ = 1 :=
      Subtype.ext hx'2
    rw [h1, map_mul, hρy, ← map_mul, h2, map_one]
  have hk2 : y * (g * x * g⁻¹) * (y * (g * x * g⁻¹)) = 1 := by
    calc y * (g * x * g⁻¹) * (y * (g * x * g⁻¹)) = y * (g * x * g⁻¹ * y) * (g * x * g⁻¹) := by
          group
      _ = y * (y * (g * x * g⁻¹)) * (g * x * g⁻¹) := by rw [hyx']
      _ = (y * y) * (g * x * g⁻¹ * (g * x * g⁻¹)) := by group
      _ = 1 := by rw [hy2, hx'2, one_mul]
  have hk1 : y * (g * x * g⁻¹) ≠ 1 := by
    intro h
    apply hx'M
    have h1 : g * x * g⁻¹ = y⁻¹ := by
      calc g * x * g⁻¹ = y⁻¹ * (y * (g * x * g⁻¹)) := by group
        _ = y⁻¹ := by rw [h, mul_one]
    rw [h1]
    exact inv_mem hyM
  have hCk : centralizer ({y * (g * x * g⁻¹)} : Set X) ≤ H := by
    obtain ⟨c, hc⟩ := exists_conj_mem_of_card_eq
      (G := ↥(H ⊓ UnbalancedLayer.coreActionKernel M))
      (H := Q.subgroupOf (H ⊓ UnbalancedLayer.coreActionKernel M))
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv]; exact hQcard)
      (x := ⟨y * (g * x * g⁻¹), mem_inf.mpr ⟨hkH, hkK⟩⟩)
      (isPGroup_zpowers_of_mul_self (Subtype.ext hk2))
    rw [mem_subgroupOf] at hc
    have hcQ : (c : X) * (y * (g * x * g⁻¹)) * (c : X)⁻¹ ∈ Q := by simpa using hc
    have hc1 : (c : X) * (y * (g * x * g⁻¹)) * (c : X)⁻¹ ≠ 1 := by
      intro h
      apply hk1
      calc y * (g * x * g⁻¹) = (c : X)⁻¹ * ((c : X) * (y * (g * x * g⁻¹)) * (c : X)⁻¹) * c := by
            group
        _ = 1 := by rw [h]; group
    have hN := hNT _ (zpowers_le.mpr hcQ) (fun h => hc1 (zpowers_eq_bot.mp h))
    have hcH : (c : X) ∈ H := (mem_inf.mp c.2).1
    intro z hz
    have h1 : (c : X) * z * (c : X)⁻¹ ∈ H := by
      apply hN
      apply Subgroup.centralizer_le_normalizer
      rw [centralizer_zpowers_eq']
      exact (mem_centralizer_conj_iff (c := (c : X))).mp hz
    have h2 := mul_mem (mul_mem (inv_mem hcH) h1) hcH
    rwa [show (c : X)⁻¹ * ((c : X) * z * (c : X)⁻¹) * c = z by group] at h2
  have hko : y * (g * x * g⁻¹) ∈ oddGen (centralizer ({a} : Set X)) :=
    mul_mem (oddGen_mono (hle.trans inf_le_right) hyo) hx'o
  exact ⟨y, hyM, hy2, hyx', hρy, hyo',
    hρ.mem_oddGen_kernel_of_mem_oddGen (by omega) hHN hCa hLaM hLaC θLa hθLa hLaN hko
      (mem_inf.mpr ⟨hkH, hkK⟩),
    hCk⟩

end CFSG.ComponentClassification.SolMax
