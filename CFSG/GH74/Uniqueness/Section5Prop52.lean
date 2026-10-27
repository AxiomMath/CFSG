module

public import CFSG.GH74.Uniqueness.Section5Lemma51
public import CFSG.GH74.Uniqueness.Section5Stmt
public import CFSG.GH74.Uniqueness.Section5Omega
public import CFSG.GH74.Uniqueness.Section5ZStar
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Prelim

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X}

omit [Group X] in
theorem odd_pow_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) : Odd (p ^ n) :=
  (hp.odd_of_ne_two hp2).pow

theorem odd_card_of_isPGroup [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P) : Odd (Nat.card P) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  exact odd_pow_of_ne_two hp hp2 n

theorem isPGroup_conjugate {p : ℕ} {P : Subgroup X} (hP : IsPGroup p P) (g : X) :
    IsPGroup p (conjugate P g) :=
  hP.map _

theorem conjugate_mono {A B : Subgroup X} (h : A ≤ B) (g : X) : conjugate A g ≤ conjugate B g := by
  intro x hx
  rw [mem_conjugate_iff] at hx ⊢
  exact h hx

theorem conjugate_conjugate_inv (A : Subgroup X) (g : X) : conjugate (conjugate A g) g⁻¹ = A := by
  rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem conjugate_inv_conjugate (A : Subgroup X) (g : X) : conjugate (conjugate A g⁻¹) g = A := by
  rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]

theorem Prop52Cond.map_conjugate [Finite X] (hZ : IsInvariantInvolutionSet Z) {p : ℕ} {P : Subgroup X}
    (hP : Prop52Cond Z M p P) (g : X) : Prop52Cond Z M p (conjugate P g) := by
  refine ⟨isPGroup_conjugate hP.pgroup g, by rw [ncard_omegaFix_conjugate]; exact hP.three_le, ?_⟩
  obtain ⟨u, hu, huN, hcard⟩ := hP.exists_u
  refine ⟨g⁻¹ * u * g, hZ.2 u hu g, ?_, by rw [zCosetNum_conjugate hZ]; exact hcard⟩
  rw [normalizer_conjugate, mem_conjugate_iff]
  have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
  rw [e]
  exact huN

theorem Prop52Cond.maximal_map_conjugate [Finite X] (hZ : IsInvariantInvolutionSet Z) {p : ℕ}
    {P : Subgroup X} (hP : Maximal (Prop52Cond Z M p) P) (g : X) :
    Maximal (Prop52Cond Z M p) (conjugate P g) := by
  refine ⟨hP.1.map_conjugate hZ g, fun Q hQ hle => ?_⟩
  have hQ' := hQ.map_conjugate hZ g⁻¹
  have hle' : P ≤ conjugate Q g⁻¹ := by
    have := conjugate_mono hle g⁻¹
    rwa [conjugate_conjugate_inv] at this
  have := conjugate_mono (hP.2 hQ' hle') g
  rwa [conjugate_inv_conjugate] at this

theorem zCosetNum_conj_of_mem_normalizer (hZ : IsInvariantInvolutionSet Z) {P : Subgroup X}
    {c u : X} (hc : c ∈ normalizer (P : Set X)) :
    zCosetNum Z P (c⁻¹ * u * c) = zCosetNum Z P u := by
  have := zCosetNum_conjugate hZ P u c
  rwa [conjugate_eq_iff_mem_normalizer.mpr hc] at this


theorem zCosetNum_eq_ncard (Z : Set X) (P : Subgroup X) (u : X) :
    zCosetNum Z P u = {y : X | y ∈ Z ∧ y * u⁻¹ ∈ P}.ncard :=
  Nat.card_coe_set_eq _

end Prelim

section Lemma54

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.lemma54 (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {P : Subgroup X}
    (hP3 : 3 ≤ (omegaFix M (P : Set X)).ncard) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    (hzN : z ∈ normalizer (P : Set X)) (hPM : ¬ P ≤ M)
    (hrank : Open.pRank 2 (zHull Z (normalizer (P : Set X))) ≤ 1) :
    ∃ β ∈ omegaFix M (P : Set X), ∃ δ ∈ omegaFix M (P : Set X), β ≠ δ ∧
      ∀ s ∈ Z, s ∈ normalizer (P : Set X) → conjugate β s ≠ δ := by
  set N := normalizer (P : Set X) with hN
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hiso : ∀ y ∈ Z, y ∈ N → y * z = z * y → y = z := fun y hy hyN hyz =>
    eq_of_commute_of_pRank_zHull_le_one hZ hrank hy hyN hz hzN hyz
  obtain ⟨K, hKN, hKn, hKodd, hKcomm, hKcl⟩ := exists_odd_normal_of_isolated hZ hz hzN hiso
  have hKnorm : N ≤ normalizer (K : Set X) := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn
  have hF1 : ∀ s ∈ Z, s ∈ N → ∀ β ∈ omegaFix M (P : Set X), conjugate β s ≠ β := by
    intro s hs hsN β hβ hfix
    obtain ⟨a, haN, has⟩ := (hKcl s hs hsN).1
    have hβ' := conjugate_mem_omegaFix_of_mem_normalizer (N.inv_mem haN) hβ
    have hzβ' : conjugate (conjugate β a⁻¹) z = conjugate β a⁻¹ := by
      rw [conjugate_conjugate]
      have e : a⁻¹ * z = s * a⁻¹ := by rw [← has]; group
      rw [e, ← conjugate_conjugate, hfix]
    obtain ⟨γ, -, huniq⟩ := h.existsUnique_fixed_point hZ hz
    have h1 := huniq _ ⟨hβ'.1, hzβ'⟩
    have h2 := huniq M ⟨self_mem_omega M, (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM⟩
    have hMβ : conjugate β a⁻¹ = M := h1.trans h2.symm
    apply hPM
    have hMP : M ∈ omegaFix M (P : Set X) := by
      have := hβ'
      rwa [hMβ] at this
    exact h.self_mem_omegaFix_iff.mp hMP
  by_contra hno
  push Not at hno
  have hclaim : ∀ k ∈ K, ∀ β ∈ omegaFix M (P : Set X), conjugate β k = β := by
    intro k hk β hβ
    by_contra hne
    have hkN : k ∈ N := hKN hk
    have hβk := conjugate_mem_omegaFix_of_mem_normalizer hkN hβ
    obtain ⟨s, hs, hsN, hsβ⟩ := hno β hβ _ hβk (fun heq => hne heq.symm)
    set w := s * k⁻¹ with hw
    have hwβ : conjugate β w = β := by
      rw [hw, ← conjugate_conjugate, hsβ, conjugate_conjugate, mul_inv_cancel, conjugate_one]
    have hsK : s * z⁻¹ ∈ K := (hKcl s hs hsN).2
    have hz' : z * k⁻¹ * z⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKnorm hzN) k⁻¹).mp (K.inv_mem hk)
    have hwK : w * z⁻¹ ∈ K := by
      have e : w * z⁻¹ = (s * z⁻¹) * (z * k⁻¹ * z⁻¹) := by rw [hw]; group
      rw [e]
      exact K.mul_mem hsK hz'
    have hww : w * w ∈ K := by
      have e : w * w = (w * z⁻¹) * (z * (w * z⁻¹) * z⁻¹) * (z * z) := by group
      rw [e, hz2, mul_one]
      exact K.mul_mem hwK ((Subgroup.mem_normalizer_iff.mp (hKnorm hzN) _).mp hwK)
    have hodd : Odd (orderOf (w * w)) := by
      have hd : orderOf (w * w) ∣ Nat.card K := by
        have := orderOf_dvd_natCard (⟨w * w, hww⟩ : K)
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hKodd hd
    set o := orderOf (w * w) with ho
    obtain ⟨j, hj⟩ := hodd
    set y := w ^ o with hy
    have hyy : y * y = 1 := by
      rw [hy, ← pow_add, ← two_mul, pow_mul, sq, ho, pow_orderOf_eq_one]
    have hyK : y * z⁻¹ ∈ K := by
      have e : y = (w * w) ^ j * w := by rw [hy, hj, pow_succ, pow_mul, sq]
      have e2 : y * z⁻¹ = (w * w) ^ j * (w * z⁻¹) := by rw [e]; group
      rw [e2]
      exact K.mul_mem (K.pow_mem hww j) hwK
    have hzK : z ∉ K := CFSG.OddInversion.notMem_of_odd_card hKodd (hZ.1 z hz)
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1, one_mul] at hyK
      exact hzK (by simpa using K.inv_mem hyK)
    have hy2 : orderOf y = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    have hyZ : y ∈ Z := by
      have hcos := (CFSG.OddInversion.odd_inversion_coset_count hKodd (hKnorm hzN) hzK
        (hZ.1 z hz)).1
      have hmem : y ∈ {v : X | v * z⁻¹ ∈ K ∧ orderOf v = 2} := ⟨hyK, hy2⟩
      rw [hcos] at hmem
      obtain ⟨d, -, hd⟩ := hmem
      rw [hd]
      exact hZ.2 z hz d
    have hyN : y ∈ N := N.pow_mem (N.mul_mem hsN (N.inv_mem hkN)) o
    have hpow : ∀ n : ℕ, conjugate β (w ^ n) = β := by
      intro n
      induction n with
      | zero => simp [conjugate_one]
      | succ n ih => rw [pow_succ, ← conjugate_conjugate, ih, hwβ]
    exact hF1 y hyZ hyN β hβ (hpow o)
  obtain ⟨β₀, hβ₀⟩ : (omegaFix M (P : Set X)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  have hsub : omegaFix M (P : Set X) ⊆ {β₀, conjugate β₀ z} := by
    intro δ hδ
    by_cases hδβ : δ = β₀
    · exact Or.inl hδβ
    · obtain ⟨s, hs, hsN, hsβ⟩ := hno β₀ hβ₀ δ hδ (fun h' => hδβ h'.symm)
      right
      have hk : s * z⁻¹ ∈ K := (hKcl s hs hsN).2
      have e : conjugate β₀ s = conjugate (conjugate β₀ (s * z⁻¹)) z := by
        rw [conjugate_conjugate]
        congr 1
        group
      rw [← hsβ, e, hclaim _ hk β₀ hβ₀]
      exact Set.mem_singleton _
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({β₀, conjugate β₀ z} : Set (Subgroup X)).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  omega

end Lemma54

section Lemma56

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.lemma55 (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : Maximal (Prop52Cond Z M p) P) {β δ : Subgroup X}
    (hβ : β ∈ omegaFix M (P : Set X)) (hδ : δ ∈ omegaFix M (P : Set X)) (hβδ : β ≠ δ)
    (hno : ∀ s ∈ Z, s ∈ normalizer (P : Set X) → conjugate β s ≠ δ) {R : Subgroup X}
    (hR : ABGLocalTools.IsSylowOf p R (β ⊓ δ)) (hPR : P ≤ R) :
    omegaFix M (R : Set X) = {β, δ} ∧ P < R := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hβΩ, -⟩ := h.mem_omegaFix_iff.mp hβ
  obtain ⟨hδΩ, -⟩ := h.mem_omegaFix_iff.mp hδ
  have hβR : β ∈ omegaFix M (R : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hβΩ, hR.le.trans inf_le_left⟩
  have hδR : δ ∈ omegaFix M (R : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hδΩ, hR.le.trans inf_le_right⟩
  obtain ⟨s, hs, hsR, hs1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 hβΩ hδΩ hβδ hR
  have hΩR : omegaFix M (R : Set X) = {β, δ} := by
    by_contra hne
    have h3 : 3 ≤ (omegaFix M (R : Set X)).ncard := by
      by_contra hlt
      apply hne
      symm
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · rintro x (rfl | rfl)
        · exact hβR
        · exact hδR
      · rw [Set.ncard_pair hβδ]
        omega
    have hcond : Prop52Cond Z M p R :=
      ⟨hR.isPGroup, h3, s, hs, hsR, h.lemma39_card hZ hβΩ hβδ hp hp2 hs hs1 hR hsR⟩
    have hRP : R = P := le_antisymm (hP.2 hcond hPR) hPR
    rw [hRP] at hsR
    exact hno s hs hsR hs1
  refine ⟨hΩR, lt_of_le_of_ne hPR fun heq => ?_⟩
  have h3 := hP.1.three_le
  rw [heq, hΩR, Set.ncard_pair hβδ] at h3
  omega

theorem two_le_of_modEq_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≡ n [MOD p]) : 2 ≤ n := by
  by_contra hlt
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h2 : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
  have hn' : n % p = n := Nat.mod_eq_of_lt (by omega)
  unfold Nat.ModEq at hn
  rw [h2, hn'] at hn
  omega

theorem IsProductDisconnected.prop52_key (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : Maximal (Prop52Cond Z M p) P) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    (hzN : z ∈ normalizer (P : Set X)) : P ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hPM
  have hPp := hP.1.pgroup
  have hPodd := odd_card_of_isPGroup hp hp2 hPp
  set N := normalizer (P : Set X) with hN
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hrank : Open.pRank 2 (zHull Z N) ≤ 1 := by
    by_contra hge
    push Not at hge
    exact hPM (h.le_of_odd_normalizer hZ hPodd hge hz hzM hzN)
  have hiso : ∀ y ∈ Z, y ∈ N → y * z = z * y → y = z := fun y hy hyN hyz =>
    eq_of_commute_of_pRank_zHull_le_one hZ hrank hy hyN hz hzN hyz
  have hZstar : IsZStarIn (N ⊔ zpowers z) z := by
    rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hzN)]
    exact isZStarIn_of_isolated hZ hz hzN hiso
  have hconj : ∀ s ∈ Z, s ∈ N → ∃ a ∈ N, a⁻¹ * z * a = s := fun s hs hsN =>
    exists_mem_conj_of_isolated hZ hz hzN hiso hs hsN
  have h5A : ∀ s ∈ Z, s ∈ N → zCosetNum Z P s = zNumShare Z M p := by
    intro s hs hsN
    obtain ⟨u, hu, huN, hcard⟩ := hP.1.exists_u
    obtain ⟨a, haN, rfl⟩ := hconj u hu huN
    obtain ⟨b, hbN, rfl⟩ := hconj s hs hsN
    have hc : a⁻¹ * b ∈ N := N.mul_mem (N.inv_mem haN) hbN
    have e : b⁻¹ * z * b = (a⁻¹ * b)⁻¹ * (a⁻¹ * z * a) * (a⁻¹ * b) := by group
    rw [e, zCosetNum_conj_of_mem_normalizer hZ hc]
    exact hcard
  obtain ⟨β, hβ, δ, hδ, hβδ, hno⟩ := h.lemma54 hZ hP.1.three_le hz hzM hzN hPM hrank
  have hPβδ : P ≤ β ⊓ δ :=
    le_inf (h.mem_omegaFix_iff.mp hβ).2 (h.mem_omegaFix_iff.mp hδ).2
  obtain ⟨Q, hQ⟩ := (hPp.comap_subtype (K := β ⊓ δ)).exists_le_sylow
  set R : Subgroup X := (Q : Subgroup ↥(β ⊓ δ)).map (β ⊓ δ).subtype with hR
  have hRsyl : ABGLocalTools.IsSylowOf p R (β ⊓ δ) := ⟨Q, rfl⟩
  have hPR : P ≤ R := fun x hx =>
    ⟨⟨x, hPβδ hx⟩, hQ (show (⟨x, hPβδ hx⟩ : ↥(β ⊓ δ)) ∈ P.subgroupOf (β ⊓ δ) from hx), rfl⟩
  obtain ⟨hΩR, hPRlt⟩ := h.lemma55 hZ hp hp2 hP hβ hδ hβδ hno hRsyl hPR
  have hRp := hRsyl.isPGroup
  have hmodΩ : (omega M).ncard ≡ 2 [MOD p] := by
    have := ncard_omega_modEq_ncard_omegaFix (M := M) hp hRp
    rwa [hΩR, Set.ncard_pair hβδ] at this
  obtain ⟨A, hAp, hPA, hAR, hAN⟩ :=
    CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hRp hPRlt
  obtain ⟨Q', hQ'⟩ := (hAp.comap_subtype (K := N)).exists_le_sylow
  set B : Subgroup X := (Q' : Subgroup ↥N).map N.subtype with hB
  have hBsyl : ABGLocalTools.IsSylowOf p B N := ⟨Q', rfl⟩
  have hAB : A ≤ B := fun x hx =>
    ⟨⟨x, hAN hx⟩, hQ' (show (⟨x, hAN hx⟩ : ↥N) ∈ A.subgroupOf N from hx), rfl⟩
  have hBp := hBsyl.isPGroup
  have hBodd := odd_card_of_isPGroup hp hp2 hBp
  have hbot : z ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨Q₀, hQ₀, -, hzQ₀⟩ := exists_invariant_sylow hp hp2 (hZ.1 z hz)
    (Subgroup.le_normalizer hzN) hZstar bot_le IsPGroup.of_bot hbot
  obtain ⟨w, hwN, hwB⟩ := exists_conj_of_isSylowOf hQ₀ hBsyl
  set v := w⁻¹ * z * w with hv
  have hvZ : v ∈ Z := hZ.2 z hz w
  have hvN : v ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hwN) hzN) hwN
  have hv2 : v * v = 1 := hZ.mul_self_eq_one hvZ
  have hvB : v ∈ normalizer (B : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer, ← hwB, conjugate_conjugate]
    have e : w * v = z * w := by rw [hv]; group
    rw [e, ← conjugate_conjugate, conjugate_eq_iff_mem_normalizer.mpr hzQ₀]
  have hmodB : (omega M).ncard ≡ (omegaFix M (B : Set X)).ncard [MOD p] :=
    ncard_omega_modEq_ncard_omegaFix hp hBp
  have hB2 : 2 ≤ (omegaFix M (B : Set X)).ncard :=
    two_le_of_modEq_two hp hp2 (hmodΩ.symm.trans hmodB)
  obtain ⟨l₁, l₂, hl₁, hl₂, hl12⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mp (by omega : 1 < (omegaFix M (B : Set X)).ncard)
  have hex : ∃ l ∈ omegaFix M (B : Set X), conjugate l v ≠ l := by
    by_contra hall
    push Not at hall
    obtain ⟨γ, -, huniq⟩ := h.existsUnique_fixed_point hZ hvZ
    exact hl12 ((huniq l₁ ⟨hl₁.1, hall l₁ hl₁⟩).trans (huniq l₂ ⟨hl₂.1, hall l₂ hl₂⟩).symm)
  obtain ⟨l, hl, hlv⟩ := hex
  have hμ : conjugate l v ∈ omegaFix M (B : Set X) :=
    conjugate_mem_omegaFix_of_mem_normalizer hvB hl
  have hA3 : 3 ≤ (omegaFix M (A : Set X)).ncard := by
    by_contra hlt
    have hRA : omegaFix M (R : Set X) ⊆ omegaFix M (A : Set X) :=
      omegaFix_anti (fun x hx => hAR hx)
    have hBA : omegaFix M (B : Set X) ⊆ omegaFix M (A : Set X) :=
      omegaFix_anti (fun x hx => hAB hx)
    have hAcard : (omegaFix M (A : Set X)).ncard = 2 := by
      have h1 := Set.ncard_le_ncard hRA (Set.toFinite _)
      rw [hΩR, Set.ncard_pair hβδ] at h1
      omega
    have hAeq : omegaFix M (A : Set X) = {β, δ} := by
      rw [← hΩR]
      exact (Set.eq_of_subset_of_ncard_le hRA (by rw [hΩR, Set.ncard_pair hβδ]; omega)
        (Set.toFinite _)).symm
    have hBeq : omegaFix M (B : Set X) = {β, δ} := by
      rw [← hAeq]
      exact Set.eq_of_subset_of_ncard_le hBA (by omega) (Set.toFinite _)
    rw [hBeq] at hl hμ
    rcases hl with rfl | rfl <;> rcases hμ with hμ | hμ
    · exact hlv hμ
    · exact hno v hvZ hvN hμ
    · have : conjugate β v = l := by
        rw [← hμ, conjugate_conjugate, hv2, conjugate_one]
      exact hno v hvZ hvN this
    · exact hlv hμ
  have hPB : P ≤ B := hPA.le.trans hAB
  have hBle : B ≤ l ⊓ conjugate l v :=
    le_inf (h.mem_omegaFix_iff.mp hl).2 (h.mem_omegaFix_iff.mp hμ).2
  have hvW : v ∈ normalizer ((l ⊓ conjugate l v : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate (M := l) hv2
  have hcardB := (h.prop37c_omega hZ hvZ hl.1 hlv hp hp2 le_rfl hvW hBle hBp hvB).2
  have hZB : zCosetNum Z B v ≤ zNumShare Z M p := by
    rw [zCosetNum_eq_card_invertedSet hZ hvZ hBodd hvB]
    exact hcardB
  have hZPv : zCosetNum Z P v = zNumShare Z M p := h5A v hvZ hvN
  have hZPB : zCosetNum Z P v ≤ zCosetNum Z B v := zCosetNum_mono hPB v
  have hZBeq : zCosetNum Z B v = zNumShare Z M p := le_antisymm hZB (hZPv ▸ hZPB)
  have hset : ∀ y, y ∈ Z → y * v⁻¹ ∈ B → y * v⁻¹ ∈ P := by
    have hsubset : {y : X | y ∈ Z ∧ y * v⁻¹ ∈ P} ⊆ {y : X | y ∈ Z ∧ y * v⁻¹ ∈ B} :=
      fun y hy => ⟨hy.1, hPB hy.2⟩
    have hle : ({y : X | y ∈ Z ∧ y * v⁻¹ ∈ B}).ncard ≤ ({y : X | y ∈ Z ∧ y * v⁻¹ ∈ P}).ncard := by
      rw [← zCosetNum_eq_ncard, ← zCosetNum_eq_ncard, hZBeq, hZPv]
    have heq := Set.eq_of_subset_of_ncard_le hsubset hle (Set.toFinite _)
    intro y hy hyB
    have : y ∈ {y : X | y ∈ Z ∧ y * v⁻¹ ∈ B} := ⟨hy, hyB⟩
    rw [← heq] at this
    exact this.2
  have hcomm : ∀ a ∈ B, a⁻¹ * v * a * v⁻¹ ∈ P := by
    intro a ha
    apply hset (a⁻¹ * v * a) (hZ.2 v hvZ a)
    have h1 : v * a * v⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hvB a).mp ha
    have e : a⁻¹ * v * a * v⁻¹ = a⁻¹ * (v * a * v⁻¹) := by group
    rw [e]
    exact B.mul_mem (B.inv_mem ha) h1
  have hvA : v ∈ normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ a ∈ A, v * a * v⁻¹ ∈ A := by
      intro a ha
      have h1 := hcomm a (hAB ha)
      have e : v * a * v⁻¹ = a * (a⁻¹ * v * a * v⁻¹) := by group
      rw [e]
      exact A.mul_mem ha (hPA.le h1)
    intro a
    refine ⟨key a, fun hva => ?_⟩
    have := key _ hva
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have e : v * (v * a * v⁻¹) * v⁻¹ = a := by
      rw [hvi]
      calc v * (v * a * v) * v = (v * v) * a * (v * v) := by group
        _ = a := by rw [hv2]; group
    rwa [e] at this
  have hZA : zCosetNum Z A v = zNumShare Z M p :=
    le_antisymm (hZBeq ▸ zCosetNum_mono hAB v) (hZPv ▸ zCosetNum_mono hPA.le v)
  have hcondA : Prop52Cond Z M p A := ⟨hAp, hA3, v, hvZ, hvA, hZA⟩
  exact absurd hPA (not_lt_of_ge (hP.2 hcondA hPA.le))

end Lemma56

section Prop52

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.prop52a (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : Maximal (Prop52Cond Z M p) P) {s : X} (hs : s ∈ Z) (hsN : s ∈ normalizer (P : Set X))
    {β : Subgroup X} (hβ : β ∈ omega M) (hβs : conjugate β s = β) : P ≤ β := by
  obtain ⟨g, hg⟩ := exists_conjugate_eq_base hβ
  have hmax' := Prop52Cond.maximal_map_conjugate hZ hP g
  have hsβ : s ∈ β := (h.conjugate_eq_iff_mem hβ).mp hβs
  have hzM : g⁻¹ * s * g ∈ M := by
    have : g⁻¹ * s * g ∈ conjugate β g := by
      rw [mem_conjugate_iff]
      have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
      rw [e]
      exact hsβ
    rwa [hg] at this
  have hzN : g⁻¹ * s * g ∈ normalizer (conjugate P g : Set X) := by
    rw [normalizer_conjugate, mem_conjugate_iff]
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rw [e]
    exact hsN
  have hle := h.prop52_key hZ hp hp2 hmax' (hZ.2 s hs g) hzM hzN
  intro x hx
  have hx' : g⁻¹ * x * g ∈ conjugate P g := by
    rw [mem_conjugate_iff]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  have hβeq : β = conjugate M g⁻¹ := by
    rw [← hg, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  rw [hβeq, mem_conjugate_iff]
  have e : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by rw [inv_inv]
  rw [e]
  exact hle hx'

theorem ZDSetup.prop52 (S : ZDSetup X Z M) : Prop52Stmt Z M := by
  intro p hp hp2 P hP
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact p.Prime := ⟨hp⟩
  have hPp := hP.1.pgroup
  have hPodd := odd_card_of_isPGroup hp hp2 hPp
  obtain ⟨u, hu, huN, hcard⟩ := hP.1.exists_u
  have ha : ∀ s ∈ Z, s ∈ normalizer (P : Set X) → ∀ β ∈ omega M, conjugate β s = β → P ≤ β :=
    fun s hs hsN β hβ hβs => h.prop52a hZ hp hp2 hP hs hsN hβ hβs
  refine ⟨⟨⟨u, hu, huN⟩, ha⟩, fun hD γ hγ => ?_⟩
  obtain ⟨δ, ⟨hδΩ, huδ⟩, -⟩ := h.existsUnique_fixed_point hZ hu
  have hδP : P ≤ δ := ha u hu huN δ hδΩ huδ
  have h3 := hP.1.three_le
  obtain ⟨β, hβ, hβδ⟩ : ∃ β ∈ omegaFix M (P : Set X), β ≠ δ := by
    by_contra hall
    push Not at hall
    have hsub : omegaFix M (P : Set X) ⊆ {δ} := fun x hx => hall x hx
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp only [Set.ncard_singleton] at this
    omega
  have hβΩ : β ∈ omega M := hβ.1
  have hPβ : P ≤ β := (h.mem_omegaFix_iff.mp hβ).2
  have hPDβ : P ≤ δ ⊓ β := le_inf hδP hPβ
  have hcnt : Nat.card (CFSG.OddInversion.invertedSet P u) = zNumShare Z M p := by
    rw [← zCosetNum_eq_card_invertedSet hZ hu hPodd huN]
    exact hcard
  obtain ⟨Q, hQ, hQle, huQ⟩ :=
    h.prop38c_omega hZ hu hδΩ huδ hβΩ hβδ hp hp2 hPDβ hPp huN hcnt
  have hβu : conjugate β u ≠ β := by
    intro hfix
    obtain ⟨γ', -, huniq⟩ := h.existsUnique_fixed_point hZ hu
    exact hβδ ((huniq β ⟨hβΩ, hfix⟩).trans (huniq δ ⟨hδΩ, huδ⟩).symm)
  have hu2 : u * u = 1 := hZ.mul_self_eq_one hu
  have hδβu : δ ≠ conjugate β u := by
    intro heq
    apply hβδ
    have : conjugate δ u = β := by
      rw [heq, conjugate_conjugate, hu2, conjugate_one]
    rw [← this, huδ]
  have hQδ : δ ∈ omegaFix M (Q : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hδΩ, (hQle.trans (inf_le_left.trans inf_le_left))⟩
  have hQβ : β ∈ omegaFix M (Q : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hβΩ, (hQle.trans (inf_le_left.trans inf_le_right))⟩
  have hQβu : conjugate β u ∈ omegaFix M (Q : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨conjugate_mem_omega hβΩ u, hQle.trans inf_le_right⟩
  have hQ3 : 3 ≤ (omegaFix M (Q : Set X)).ncard := by
    have : 2 < (omegaFix M (Q : Set X)).ncard :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨δ, β, conjugate β u, hQδ, hQβ, hQβu,
        hβδ.symm, hδβu, hβu.symm⟩
    omega
  have hQodd := odd_card_of_isPGroup hp hp2 hQ.isPGroup
  have hQcnt := (h.prop38b_omega hZ hu hδΩ huδ hβΩ hβδ hp hp2 hQ.le hQ.isPGroup huQ).2 hQ
  have hQcond : Prop52Cond Z M p Q :=
    ⟨hQ.isPGroup, hQ3, u, hu, huQ, by
      rw [zCosetNum_eq_card_invertedSet hZ hu hQodd huQ]; exact hQcnt⟩
  obtain ⟨Q₁, hQ₁⟩ := (hPp.comap_subtype (K := δ ⊓ β)).exists_le_sylow
  set R₁ : Subgroup X := (Q₁ : Subgroup ↥(δ ⊓ β)).map (δ ⊓ β).subtype with hR₁
  have hR₁syl : ABGLocalTools.IsSylowOf p R₁ (δ ⊓ β) := ⟨Q₁, rfl⟩
  have hPR₁ : P ≤ R₁ := fun x hx =>
    ⟨⟨x, hPDβ hx⟩, hQ₁ (show (⟨x, hPDβ hx⟩ : ↥(δ ⊓ β)) ∈ P.subgroupOf (δ ⊓ β) from hx), rfl⟩
  obtain ⟨w, hw, hwQ⟩ := exists_conj_of_isSylowOf hQ hR₁syl
  have hR₁cond : Prop52Cond Z M p R₁ := by
    rw [← hwQ]
    exact hQcond.map_conjugate hZ w
  have hR₁P : R₁ ≤ P := hP.2 hR₁cond hPR₁
  have hPsyl : ABGLocalTools.IsSylowOf p P (δ ⊓ β) := by
    have : R₁ = P := le_antisymm hR₁P hPR₁
    rw [← this]
    exact hR₁syl
  have hγP : P ≤ γ := (h.mem_omegaFix_iff.mp hγ).2
  have htrans : ∃ n ∈ normalizer (P : Set X), conjugate δ n = γ := by
    obtain ⟨γ₂, hγ₂, hγγ₂⟩ : ∃ γ₂ ∈ omegaFix M (P : Set X), γ₂ ≠ γ := by
      by_contra hall
      push Not at hall
      have hsub : omegaFix M (P : Set X) ⊆ {γ} := fun x hx => hall x hx
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      simp only [Set.ncard_singleton] at this
      omega
    obtain ⟨g, hg1, hg2⟩ := hD δ hδΩ β hβΩ hβδ.symm γ hγ.1 γ₂ hγ₂.1 hγγ₂.symm
    have hPg : P ≤ conjugate (δ ⊓ β) g := by
      rw [conjugate_inf, hg1, hg2]
      exact le_inf hγP (h.mem_omegaFix_iff.mp hγ₂).2
    obtain ⟨e, he, hen⟩ := exists_mul_mem_normalizer_of_isSylowOf hp hPsyl hPg
    refine ⟨e * g, hen, ?_⟩
    rw [← conjugate_conjugate, (h.conjugate_eq_iff_mem hδΩ).mpr (Subgroup.mem_inf.mp he).1, hg1]
  obtain ⟨n, hnN, hnδ⟩ := htrans
  refine ⟨n⁻¹ * u * n, hZ.2 u hu n, ?_, ?_⟩
  · exact (normalizer (P : Set X)).mul_mem
      ((normalizer (P : Set X)).mul_mem ((normalizer (P : Set X)).inv_mem hnN) huN) hnN
  · rw [← hnδ, conjugate_conjugate]
    have e : n * (n⁻¹ * u * n) = u * n := by group
    rw [e, ← conjugate_conjugate, huδ]

end Prop52

end CFSG.GH74.Uniqueness
