module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2414a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2414b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_16
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Easy

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem swapData_of_cfg (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D) {t : G} (htT : t ∈ T)
    (htS : t ∉ S) (htt : t * t = 1) :
    SwapData (thompsonJ S) (blockU L) (conjR (blockU L) t) (centerOf (thompsonJ S)) t := by
  obtain ⟨⟨-, -, hTnR⟩, ⟨hOL, -⟩, ⟨-, hRsyl, h3⟩, -, -, -, h7, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨hRU, hZR, -, -⟩ := h3 t htT htS
  obtain ⟨hUab, hVab, hmax⟩ := h7 t htT htS
  have hLU : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [← hOL]; exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hRL : thompsonJ S ≤ L := hRsyl.1
  have htR : t ∈ Subgroup.normalizer (thompsonJ S : Set G) := hTnR htT
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine ⟨htt, hRU, fun x hx => hLU (hRL hx), ?_, hZR, fun a ha b hb => IsElemAbelian.comm hUab ha hb,
    fun a ha b hb => IsElemAbelian.comm hVab ha hb, fun a ha => ?_, fun a ha => ?_, fun u hu => ?_,
    fun v hv => mem_conjR.1 hv, fun n hn r hr => (Subgroup.mem_centralizer_iff.1 hn.2 r hr).symm,
    fun x hx hx2 => ?_⟩
  · intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjR, mem_conjR]
    have hm : t * r * t⁻¹ ∈ thompsonJ S := (Subgroup.mem_normalizer_iff.1 htR r).1 hr
    have hmL : t * r * t⁻¹ ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
      hLU (hRL hm)
    have e : t * (r * y * r⁻¹) * t⁻¹ = (t * r * t⁻¹) * (t * y * t⁻¹) * (t * r * t⁻¹)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 hmL (t * y * t⁻¹)
  · rw [← sq]; exact hUab.2 a ha
  · rw [← sq]; exact hVab.2 a ha
  · rw [mem_conjR]
    have : t * (t * u * t⁻¹) * t⁻¹ = u := by
      rw [hti]
      calc t * (t * u * t) * t = (t * t) * u * (t * t) := by group
        _ = u := by rw [htt]; group
    rw [this]
    exact hu
  · have hE : IsElemAbelian 2 (Subgroup.zpowers x) :=
      isElemAbelian_zpowers_of_sq_eq_one (by rw [sq]; exact hx2)
    rcases hmax _ (Subgroup.zpowers_le.2 hx) hE with h | h
    · exact Or.inl (h (Subgroup.mem_zpowers x))
    · exact Or.inr (h (Subgroup.mem_zpowers x))

omit [Finite G] in
theorem exists_normalizing_involution {R B : Subgroup G}
    (hRT : R ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T)
    (hRTbot : R ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥)
    (hTnR : T ≤ Subgroup.normalizer (R : Set G)) (hRS : R ≤ S) {t : G} (htT : t ∈ T)
    (htS : t ∉ S) (ht2 : t ^ 2 ∈ R) :
    ∃ t₁ ∈ T ⊓ Subgroup.normalizer (B : Set G), t₁ * t₁ = 1 ∧ t₁ ∉ S ∧ ∃ r ∈ R, t = r * t₁ := by
  have htmem : t ∈ R ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) := hRT.ge htT
  obtain ⟨r, hr, t₁, ht₁, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := R)
    (H := T ⊓ Subgroup.normalizer (B : Set G)) (fun x hx => hTnR hx.1)).1 htmem
  refine ⟨t₁, ht₁, ?_, fun h => htS (S.mul_mem (hRS hr) h), r, hr, rfl⟩
  have h1 : t₁ * t₁ ∈ R := by
    have ht2' : (r * t₁) * (r * t₁) ∈ R := by rw [← sq]; exact ht2
    have e : t₁ * t₁ = r⁻¹ * ((r * t₁) * r⁻¹ * (r * t₁)⁻¹) * ((r * t₁) * (r * t₁)) := by group
    rw [e]
    have hc : (r * t₁) * r⁻¹ * (r * t₁)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (hTnR htT) r⁻¹).1 (R.inv_mem hr)
    exact R.mul_mem (R.mul_mem (R.inv_mem hr) hc) ht2'
  have h2 : t₁ * t₁ ∈ R ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) :=
    ⟨h1, (T ⊓ Subgroup.normalizer (B : Set G)).mul_mem ht₁ ht₁⟩
  rw [hRTbot, Subgroup.mem_bot] at h2
  exact h2

omit [Finite G] in
theorem conj_center_eq {R : Subgroup G} {t₁ r z : G} (hr : r ∈ R)
    (ht₁ : t₁ ∈ Subgroup.normalizer (R : Set G)) (hz : z ∈ centerOf R) :
    (r * t₁) * z * (r * t₁)⁻¹ = t₁ * z * t₁⁻¹ := by
  have hz' : t₁ * z * t₁⁻¹ ∈ centerOf R := by
    have : z ∈ conjR (centerOf R) t₁ := by rw [centerOf_normalized ht₁]; exact hz
    exact mem_conjR.1 this
  have hc : r * (t₁ * z * t₁⁻¹) = (t₁ * z * t₁⁻¹) * r := Subgroup.mem_centralizer_iff.1 hz'.2 r hr
  calc (r * t₁) * z * (r * t₁)⁻¹ = r * (t₁ * z * t₁⁻¹) * r⁻¹ := by group
    _ = (t₁ * z * t₁⁻¹) * r * r⁻¹ := by rw [hc]
    _ = t₁ * z * t₁⁻¹ := by group

theorem center_dichotomy (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D)
    (hc : centerOf L = ⊥) {t : G} (htT : t ∈ T) (htS : t ∉ S) (htt : t * t = 1) :
    (∀ z ∈ centerOf (thompsonJ S), t * z = z * t) ∨
      Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ^ 2 =
        Nat.card (centerOf (thompsonJ S)) := by
  obtain ⟨⟨-, -, hTnR⟩, -, -, -, ⟨B, hB⟩, h6, -, ⟨hDcyc, hDcard⟩, -⟩ := h8 G T M H S L D n hcfg
  have hB0 := hB
  obtain ⟨hDB, -, -, -, -, -, -, -, hRT, hRTbot, -⟩ := hB
  obtain ⟨hBle, hDreg⟩ := (h6 B hB0).2 hc
  obtain ⟨t₁, ht₁mem, ht₁t₁, -, r, hr, htr⟩ := exists_normalizing_involution hRT hRTbot hTnR
    (thompsonJ_le_self S) htT htS (by rw [sq, htt]; exact Subgroup.one_mem _)
  have ht₁T : t₁ ∈ T := ht₁mem.1
  have ht₁B : t₁ ∈ Subgroup.normalizer (B : Set G) := ht₁mem.2
  have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) := by simp [lin2Z, hc]
  obtain ⟨⟨hZel, hZcard, -⟩, -, -⟩ :=
    h16 G T M H S L D n hcfg (centerOf (thompsonJ S)) hZR.symm
  have hZN : ∀ z ∈ centerOf (thompsonJ S), t₁ * z * t₁⁻¹ ∈ centerOf (thompsonJ S) := by
    intro z hz
    have : z ∈ conjR (centerOf (thompsonJ S)) t₁ := by
      rw [centerOf_normalized (hTnR ht₁T)]; exact hz
    exact mem_conjR.1 this
  have hconj : ∀ b ∈ D, ∀ z ∈ centerOf (thompsonJ S), b⁻¹ * z * b ∈ centerOf (thompsonJ S) := by
    intro b hb z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      have : b⁻¹ * 1 * b = 1 := by group
      rw [this]
      exact Subgroup.one_mem _
    · exact (hDreg.1 b hb z ⟨hz, hz1⟩).1
  have hDN : D ≤ Subgroup.normalizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      simpa using hconj b⁻¹ (D.inv_mem hb) z hz
    · intro hz
      simpa [mul_assoc] using hconj b hb _ hz
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := D)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDC : ∀ b ∈ D, ∀ x ∈ Subgroup.centralizer ((centerOf (thompsonJ S) : Subgroup G) : Set G),
      b * x * b⁻¹ ∈ Subgroup.centralizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) := by
    intro b hb x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : b⁻¹ * z * b ∈ centerOf (thompsonJ S) := hconj b hb z hz
    have h2 := Subgroup.mem_centralizer_iff.1 hx _ h1
    calc z * (b * x * b⁻¹) = b * ((b⁻¹ * z * b) * x) * b⁻¹ := by group
      _ = b * (x * (b⁻¹ * z * b)) * b⁻¹ := by rw [h2]
      _ = (b * x * b⁻¹) * z := by group
  have hDnC : D ≤ Subgroup.normalizer
      ((Subgroup.centralizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) : Subgroup G) :
        Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hDC b hb x
    · intro hx
      simpa [mul_assoc] using hDC b⁻¹ (D.inv_mem hb) _ hx
  have htD : ∀ d ∈ D, ∃ d' ∈ D, ∀ z ∈ centerOf (thompsonJ S),
      (t₁ * d * t₁⁻¹) * z * (t₁ * d * t₁⁻¹)⁻¹ = d' * z * d'⁻¹ := by
    intro d hd
    have hm : t₁ * d * t₁⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 ht₁B d).1 (hDB hd)
    have hm' : t₁ * d * t₁⁻¹ ∈
        Subgroup.centralizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) ⊔ D := by
      rw [sup_comm]; exact hBle hm
    obtain ⟨c, hcC, d', hd', e⟩ := (mem_sup_iff_of_le_normalizer hDnC).1 hm'
    refine ⟨d', hd', fun z hz => ?_⟩
    have hy : d' * z * d'⁻¹ ∈ centerOf (thompsonJ S) :=
      (Subgroup.mem_normalizer_iff.1 (hDN hd') z).1 hz
    have hcy := Subgroup.mem_centralizer_iff.1 hcC _ hy
    rw [e]
    calc (c * d') * z * (c * d')⁻¹ = c * (d' * z * d'⁻¹) * c⁻¹ := by group
      _ = (d' * z * d'⁻¹) * c * c⁻¹ := by rw [← hcy]
      _ = d' * z * d'⁻¹ := by group
  have hS := singer_involution (Z := centerOf (thompsonJ S)) (D := D) (e := n)
    (by have := hcfg.one_lt; omega) hZel hZcard hDN hDcomm hDreg hDcard ht₁t₁ hZN htD
  have hact : ∀ z ∈ centerOf (thompsonJ S), t * z * t⁻¹ = t₁ * z * t₁⁻¹ := fun z hz => by
    rw [htr]; exact conj_center_eq hr (hTnR ht₁T) hz
  have hiff : ∀ z ∈ centerOf (thompsonJ S), (z * t = t * z ↔ z * t₁ = t₁ * z) := by
    intro z hz
    have e1 : z * t = t * z ↔ t * z * t⁻¹ = z := by
      rw [mul_inv_eq_iff_eq_mul]; exact eq_comm
    have e2 : z * t₁ = t₁ * z ↔ t₁ * z * t₁⁻¹ = z := by
      rw [mul_inv_eq_iff_eq_mul]; exact eq_comm
    rw [e1, e2, hact z hz]
  have heq : (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) =
      centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({t₁} : Set G) := by
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      exact ⟨hz, Subgroup.mem_centralizer_singleton_iff.2
        ((hiff z hz).1 (Subgroup.mem_centralizer_singleton_iff.1 hzc))⟩
    · rintro ⟨hz, hzc⟩
      exact ⟨hz, Subgroup.mem_centralizer_singleton_iff.2
        ((hiff z hz).2 (Subgroup.mem_centralizer_singleton_iff.1 hzc))⟩
  rcases hS with hfix | hcard
  · left
    intro z hz
    have h1 : t₁ * z = z * t₁ := hfix z hz
    have h2 : t * z * t⁻¹ = z := by
      rw [hact z hz, mul_inv_eq_iff_eq_mul]; exact h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  · right
    rw [heq]
    exact hcard

theorem lemma2_4_14_inv (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D)
    {t : G} (htT : t ∈ T) (htS : t ∉ S) (htt : t * t = 1) :
    (∀ i : G, t⁻¹ * i ∈ thompsonJ S → i * i = 1 → ∃ s ∈ thompsonJ S, i = s * t * s⁻¹) ∧
      ((centerOf L = ⊥ ∧
          centerOf (thompsonJ S) = thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) ∧
          ¬ ⁅thompsonJ S, Subgroup.zpowers t⁆ ≤ centerOf (thompsonJ S)) ∨
        (centerOf L = ⊥ ∧ Even n ∧
          Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) =
            2 ^ (3 * n / 2) ∧
          Nat.card (omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) :
            Subgroup G)) = 2 ^ (n / 2)) ∨
        (centerOf L ≠ ⊥ ∧
          Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) =
            2 ^ (2 * n) ∧
          Nat.card (omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) :
            Subgroup G)) = 2 ^ n)) := by
  have hs := swapData_of_cfg h8 hcfg htT htS htt
  obtain ⟨-, ⟨hOL, -⟩, -, -, -, -, -, -, -⟩ := h8 G T M H S L D n hcfg
  have hcardU : Nat.card (blockU L) = 2 ^ (2 * n) * Nat.card (centerOf L) := by
    rw [lin2_card_U hcfg.lin2, blockZ_eq_centerOf hcfg.charTwo_L hOL]
  have hNab : ∀ a ∈ centerOf (thompsonJ S), ∀ b ∈ centerOf (thompsonJ S), a * b = b * a :=
    fun a ha b hb => hs.U_ab a (hs.N_le_U ha) b (hs.N_le_U hb)
  have hNsq : ∀ a ∈ centerOf (thompsonJ S), a * a = 1 :=
    fun a ha => hs.U_sq a (hs.N_le_U ha)
  have hq : (2 : ℕ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  have h2n : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := hcfg.one_lt; omega)
  by_cases hc : centerOf L = ⊥
  · have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) := by simp [lin2Z, hc]
    obtain ⟨⟨hZel, hZcard, -⟩, -, -⟩ :=
      h16 G T M H S L D n hcfg (centerOf (thompsonJ S)) hZR.symm
    have hcardU' : Nat.card (blockU L) = 2 ^ (2 * n) := by
      rw [hcardU, hc, Subgroup.card_bot, mul_one]
    rcases center_dichotomy h8 h16 hcfg hc htT htS htt with hfix | hcard
    ·
      have hCN := hs.C_eq_N hfix
      refine ⟨fun i hi hi2 => hs.transitive_of_centralizes hfix
        (by rw [hcardU', hZcard, hq]) hi hi2, Or.inl ⟨hc, hCN.symm, ?_⟩⟩
      obtain ⟨u, hu, hun⟩ : ∃ u ∈ blockU L, u ∉ centerOf (thompsonJ S) := by
        by_contra hcon
        have hle : blockU L ≤ centerOf (thompsonJ S) := fun u hu => by
          by_contra hu'
          exact hcon ⟨u, hu, hu'⟩
        have := Subgroup.card_le_of_le hle
        rw [hcardU', hZcard, hq] at this
        nlinarith
      exact hs.not_commutator_le hu hun
    ·
      have hcc : Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({t} : Set G) :
          Subgroup G) * Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({t} : Set G) :
          Subgroup G) = Nat.card (centerOf (thompsonJ S)) := by rw [← sq]; exact hcard
      have H3 := H3_of_card hs.tt (fun x hx => hs.tau_N hx) hNab hNsq hcc
      obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card (centerOf (thompsonJ S) ⊓
          Subgroup.centralizer ({t} : Set G) : Subgroup G) = 2 ^ a := by
        have hdvd : Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({t} : Set G) :
            Subgroup G) ∣ 2 ^ n := Dvd.intro _ (hcc.trans hZcard)
        obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        exact ⟨a, ha⟩
      have han : a + a = n := by
        have : 2 ^ (a + a) = 2 ^ n := by rw [pow_add, ← ha, hcc, hZcard]
        exact Nat.pow_right_injective (le_refl 2) this
      have hcardC := hs.card_C H3
      rw [ha, hZcard, hcardU'] at hcardC
      have hx : Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) =
          2 ^ (3 * a) := by
        have hA : (2 : ℕ) ^ n = 2 ^ a * 2 ^ a := by rw [← pow_add, han]
        have hC : (2 : ℕ) ^ (3 * a) = 2 ^ a * 2 ^ a * 2 ^ a := by
          rw [show 3 * a = a + a + a by ring, pow_add, pow_add]
        rw [hq, hA] at hcardC
        rw [hC]
        apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ a * 2 ^ a by positivity)
        rw [hcardC]; ring
      refine ⟨fun i hi hi2 => hs.transitive_of_H3 H3 hi hi2,
        Or.inr (Or.inl ⟨hc, ⟨a, han.symm⟩, ?_, ?_⟩)⟩
      · rw [hx]; congr 1; omega
      · rw [hs.omegaOneOf_C, ha]; congr 1; omega
  ·
    have hZe : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
    obtain ⟨⟨hZel, hZcard, -⟩, h2, -⟩ := h16 G T M H S L D n hcfg (centerOf L) hZe.symm
    rcases h2 t htT htS with ⟨hc', -⟩ | ⟨-, hNsup, hinf⟩
    · exact absurd hc' hc
    have hAN : centerOf L ≤ centerOf (thompsonJ S) := by rw [hNsup]; exact le_sup_left
    have hA'N : conjR (centerOf L) t ≤ centerOf (thompsonJ S) := by
      rw [hNsup]; exact le_sup_right
    have hAA' : ∀ a ∈ centerOf L, t * a * t⁻¹ ∈ conjR (centerOf L) t := fun a ha => by
      rw [mem_conjR, hs.tau_tau]; exact ha
    have hA'A : ∀ a ∈ conjR (centerOf L) t, t * a * t⁻¹ ∈ centerOf L :=
      fun a ha => mem_conjR.1 ha
    have hfixc := card_fixed_of_diag hs.tt hNab hAN hA'N hAA' hA'A hNsup hinf
    have hNcard : Nat.card (centerOf (thompsonJ S)) = 2 ^ n * 2 ^ n := by
      have hnorm : centerOf L ≤
          Subgroup.normalizer ((conjR (centerOf L) t : Subgroup G) : Set G) :=
        le_normalizer_of_commute fun a ha b hb => hNab a (hA'N ha) b (hAN hb)
      have := card_sup_mul_card_inf hnorm
      rw [← hNsup, hinf, Subgroup.card_bot, mul_one, card_conjR, hZcard] at this
      exact this
    have hH3 := H3_of_card hs.tt (fun x hx => hs.tau_N hx) hNab hNsq
      (by rw [hfixc, hZcard, hNcard])
    have hcardC := hs.card_C hH3
    rw [hfixc, hZcard, hNcard, hcardU, hZcard] at hcardC
    have hx : Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) =
        2 ^ (2 * n) := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ n * 2 ^ n by positivity)
      rw [hcardC, hq]; ring
    refine ⟨fun i hi hi2 => hs.transitive_of_H3 hH3 hi hi2, Or.inr (Or.inr ⟨hc, hx, ?_⟩)⟩
    rw [hs.omegaOneOf_C, hfixc, hZcard]

end Config

theorem lemma2_4_14 (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) : Lemma2_4_14 := by
  intro G _ _ T M H S L D n hcfg t htT htS ht2
  have h16 := lemma2_4_16 h8 h11 lemma244
  obtain ⟨⟨-, -, hTnR⟩, -, -, -, ⟨B, hB⟩, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨-, -, -, -, -, -, -, -, hRT, hRTbot, -⟩ := hB
  obtain ⟨t₁, ht₁mem, ht₁t₁, ht₁S, r, hr, htr⟩ := exists_normalizing_involution hRT hRTbot hTnR
    (thompsonJ_le_self S) htT htS ht2
  have ht₁T : t₁ ∈ T := ht₁mem.1
  have hcore := lemma2_4_14_inv h8 h16 hcfg ht₁T ht₁S ht₁t₁
  have h0 : t⁻¹ * t₁ ∈ thompsonJ S := by
    have e : t⁻¹ * t₁ = t₁⁻¹ * r⁻¹ * (t₁⁻¹)⁻¹ := by rw [htr]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hTnR (T.inv_mem ht₁T)) r⁻¹).1 ((thompsonJ S).inv_mem hr)
  have hcoset : ∀ i : G, t⁻¹ * i ∈ thompsonJ S → t₁⁻¹ * i ∈ thompsonJ S := by
    intro i hi
    have e : t₁⁻¹ * i = (t⁻¹ * t₁)⁻¹ * (t⁻¹ * i) := by group
    rw [e]
    exact (thompsonJ S).mul_mem ((thompsonJ S).inv_mem h0) hi
  refine ⟨⟨t₁, h0, by rw [sq]; exact ht₁t₁⟩, ?_, ?_⟩
  · intro i j hi hj hi2 hj2
    obtain ⟨s₁, hs₁, e₁⟩ := hcore.1 i (hcoset i hi) (by rw [← sq]; exact hi2)
    obtain ⟨s₂, hs₂, e₂⟩ := hcore.1 j (hcoset j hj) (by rw [← sq]; exact hj2)
    refine ⟨s₁ * s₂⁻¹, (thompsonJ S).mul_mem hs₁ ((thompsonJ S).inv_mem hs₂), ?_⟩
    rw [e₁, e₂]
    group
  · intro ht
    exact (lemma2_4_14_inv h8 h16 hcfg htT htS (by rw [← sq]; exact ht)).2


end CFSG.QuasithinUnique.Lin2
