module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GorensteinWalter
open scoped Pointwise

@[expose] def PGL2CartanStmt : Prop :=
  ∀ {F : Type} [Field F] [Finite F], Odd (Nat.card F) → 5 ≤ Nat.card F →
    ∀ {M : Type} [Group M] (_ : M ≃* PGL2 F) (I : Subgroup M), I.index = 2 →
      ∀ (Y H : Subgroup M), Nat.card ↥Y = Nat.card F → H ≤ I → IsCyclic ↥H →
        Nat.card ↥H = (Nat.card F - 1) / 2 → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
        ∀ w : M, w * w = 1 → w ∉ H → (∀ h ∈ H, w * h * w⁻¹ = h⁻¹) →
          ∃ T : Subgroup M, IsCyclic ↥T ∧ Nat.card ↥T = Nat.card F - 1 ∧ H ≤ T ∧
            (∀ s ∈ T, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧ (∀ s ∈ T, w * s * w⁻¹ = s⁻¹) ∧ T ⊓ I = H

section Quotient

variable {G : Type} [Group G]

theorem conj_inv_mem_of_finite [Finite G] (g : G) (Y : Subgroup G) (h : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    ∀ y ∈ Y, g⁻¹ * y * g ∈ Y := by
  have hinj : Function.Injective (fun y : ↥Y => (⟨g * y * g⁻¹, h y y.2⟩ : ↥Y)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨y', hy'⟩ := hsurj ⟨y, hy⟩
  have := congrArg Subtype.val hy'
  simp only at this
  have e : g⁻¹ * y * g = y' := by rw [← this]; group
  rw [e]; exact y'.2

theorem conj_pow_closed (g : G) (Y : Subgroup G) (h : ∀ y ∈ Y, g⁻¹ * y * g ∈ Y) :
    ∀ k : ℕ, ∀ y ∈ Y, (g ^ k)⁻¹ * y * g ^ k ∈ Y := by
  intro k
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    have := ih _ (h y hy)
    have e : (g ^ (k + 1))⁻¹ * y * g ^ (k + 1) = (g ^ k)⁻¹ * (g⁻¹ * y * g) * g ^ k := by
      rw [pow_succ', mul_inv_rev]; group
    rw [e]; exact this

end Quotient

section Core

variable {G : Type} [Group G] [Finite G]

theorem cartan_core (hP : PGL2CartanStmt) (I Y H M Z : Subgroup G) (x w : G) (n q : ℕ)
    (hM : M = I ⊔ zpowers x) (hZ : Z = zpowers (x ^ 2))
    (hq5 : 5 ≤ q) (hqodd : Odd q) (hn : 3 ≤ n) (hqn : (q - 1).factorization 2 ≤ n - 1)
    (hIn : ∀ i ∈ I, x * i * x⁻¹ ∈ I) (hx2 : ∀ i ∈ I, x ^ 2 * i = i * x ^ 2)
    (hZI : I ⊓ Z = ⊥) [hN : (Z.subgroupOf M).Normal]
    (hcardI : Nat.card ↥I = q * (q ^ 2 - 1) / 2)
    (hquot : IVK.IsPGL2 (↥M ⧸ Z.subgroupOf M) (fun r => r = q))
    (hYI : Y ≤ I) (hYc : Nat.card ↥Y = q) (hHI : H ≤ I) (hHcyc : IsCyclic ↥H)
    (hHc : Nat.card ↥H = (q - 1) / 2) (hHY : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hwI : w ∈ I) (hw2 : w * w = 1) (hwH : w ∉ H) (hwinv : ∀ h ∈ H, w * h * w⁻¹ = h⁻¹) :
    ∃ b ∈ I, ∃ u ∈ H, u * u = 1 ∧
      ((b * x) ^ (2 ^ (n - 3))) * ((b * x) ^ (2 ^ (n - 3))) = u * x ^ (2 ^ (n - 2)) ∧
      ((b * x) ^ (2 ^ (n - 3)))⁻¹ * w * (b * x) ^ (2 ^ (n - 3)) = u * w ∧
      (∀ h ∈ H, ((b * x) ^ (2 ^ (n - 3)))⁻¹ * h * (b * x) ^ (2 ^ (n - 3)) = h) ∧
      (∀ y ∈ Y, ((b * x) ^ (2 ^ (n - 3)))⁻¹ * y * (b * x) ^ (2 ^ (n - 3)) ∈ Y) ∧
      (b * x) ^ (2 ^ (n - 3)) ∈ M := by
  classical
  have hIM : I ≤ M := hM ▸ le_sup_left
  have hxM : x ∈ M := hM ▸ Subgroup.mem_sup_right (mem_zpowers x)
  have hZM : Z ≤ M := by rw [hZ, zpowers_le]; exact M.pow_mem hxM 2
  obtain ⟨F, hFfield, hFfin, hFq, ⟨θ⟩⟩ := hquot
  let π : ↥M →* (↥M ⧸ Z.subgroupOf M) := QuotientGroup.mk' (Z.subgroupOf M)
  let ι : ↥I →* (↥M ⧸ Z.subgroupOf M) := π.comp (Subgroup.inclusion hIM)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : (Subgroup.inclusion hIM g : ↥M) ∈ Z.subgroupOf M := by
      have := (QuotientGroup.eq_one_iff (N := Z.subgroupOf M) (Subgroup.inclusion hIM g)).mp hg
      exact this
    have h2 : (g : G) ∈ Z := h1
    have h3 : (g : G) ∈ I ⊓ Z := ⟨g.2, h2⟩
    rw [hZI] at h3
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  have hq : Nat.card F = q := hFq
  have hmem : ∀ (A : Subgroup G) (g : ↥I), ι g ∈ (A.subgroupOf I).map ι ↔ (g : G) ∈ A := by
    intro A g
    rw [Subgroup.mem_map_iff_mem hιinj]
    rfl
  have hcardmap : ∀ A : Subgroup G, A ≤ I → Nat.card ↥((A.subgroupOf I).map ι) = Nat.card ↥A := by
    intro A hA
    rw [Subgroup.card_map_of_injective hιinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hIbcard : Nat.card ↥ι.range = Nat.card ↥I := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hιinj, Subgroup.card_top]
  have hMb : Nat.card (↥M ⧸ Z.subgroupOf M) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr θ.toEquiv, pgl2_card_formula, hq]
  have hq24 : 24 ≤ q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have hdiv2 : 2 ∣ q * (q ^ 2 - 1) := by
    have : Even (q ^ 2 - 1) := Nat.Odd.sub_odd (hqodd.pow) odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp this) q
  have hidx : ι.range.index = 2 := by
    have h1 := Subgroup.card_mul_index ι.range
    rw [hIbcard, hcardI, hMb] at h1
    have h2 : 0 < q * (q ^ 2 - 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    have h3 : q * (q ^ 2 - 1) / 2 * 2 = q * (q ^ 2 - 1) / 2 * ι.range.index := by
      rw [h1, Nat.div_mul_cancel hdiv2]
    exact (Nat.eq_of_mul_eq_mul_left h2 h3).symm
  have hHcyc' : IsCyclic ↥((H.subgroupOf I).map ι) := by
    have : IsCyclic ↥H := hHcyc
    have : IsCyclic ↥(H.subgroupOf I) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hHI).symm.toMonoidHom
        (MulEquiv.surjective _)
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective _ ι hιinj).toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨T, hTcyc, hTcard, hHT, hTY, hTw, hTI⟩ := hP (F := F) (by rw [hq]; exact hqodd)
    (by rw [hq]; exact hq5) θ ι.range hidx ((Y.subgroupOf I).map ι) ((H.subgroupOf I).map ι)
    (by rw [hcardmap Y hYI, hYc, hq])
    (by rw [MonoidHom.range_eq_map]; exact Subgroup.map_mono le_top) hHcyc'
    (by rw [hcardmap H hHI, hHc, hq])
    (by
      rintro _ ⟨h₀, hh₀, rfl⟩ _ ⟨y₀, hy₀, rfl⟩
      refine ⟨h₀ * y₀ * h₀⁻¹, ?_, by simp⟩
      exact hHY _ hh₀ _ hy₀)
    (ι ⟨w, hwI⟩)
    (by rw [← map_mul]; convert map_one ι; exact Subtype.ext hw2)
    (by rw [hmem H]; exact hwH)
    (by
      rintro _ ⟨h₀, hh₀, rfl⟩
      have hh : (⟨w, hwI⟩ : ↥I) * h₀ * (⟨w, hwI⟩ : ↥I)⁻¹ = h₀⁻¹ := Subtype.ext (hwinv _ hh₀)
      calc ι ⟨w, hwI⟩ * ι h₀ * (ι ⟨w, hwI⟩)⁻¹ = ι ((⟨w, hwI⟩ : ↥I) * h₀ * (⟨w, hwI⟩ : ↥I)⁻¹) := by
            simp
        _ = ι h₀⁻¹ := by rw [hh]
        _ = (ι h₀)⁻¹ := map_inv ι h₀)
  let bar : G → ↥M ⧸ Z.subgroupOf M := fun g => if hg : g ∈ M then π ⟨g, hg⟩ else 1
  have bar_of_mem : ∀ {g : G} (hg : g ∈ M), bar g = π ⟨g, hg⟩ := fun {g} hg => by simp [bar, hg]
  have bar_mul : ∀ {g g' : G}, g ∈ M → g' ∈ M → bar (g * g') = bar g * bar g' := by
    intro g g' hg hg'
    rw [bar_of_mem (M.mul_mem hg hg'), bar_of_mem hg, bar_of_mem hg']
    exact map_mul π ⟨g, hg⟩ ⟨g', hg'⟩
  have bar_one : bar 1 = 1 := by
    rw [bar_of_mem M.one_mem]; exact map_one π
  have bar_inv : ∀ {g : G}, g ∈ M → bar g⁻¹ = (bar g)⁻¹ := by
    intro g hg
    rw [bar_of_mem (M.inv_mem hg), bar_of_mem hg]
    exact map_inv π ⟨g, hg⟩
  have bar_pow : ∀ {g : G}, g ∈ M → ∀ k : ℕ, bar (g ^ k) = bar g ^ k := by
    intro g hg k
    rw [bar_of_mem (M.pow_mem hg k), bar_of_mem hg]
    exact map_pow π ⟨g, hg⟩ k
  have bar_eq_one : ∀ {g : G}, g ∈ M → (bar g = 1 ↔ g ∈ Z) := by
    intro g hg
    rw [bar_of_mem hg]
    exact QuotientGroup.eq_one_iff (N := Z.subgroupOf M) ⟨g, hg⟩
  have bar_Z : ∀ {g : G}, g ∈ Z → bar g = 1 := fun {g} hg => (bar_eq_one (hZM hg)).mpr hg
  have bar_I : ∀ {i : G} (hi : i ∈ I), bar i = ι ⟨i, hi⟩ := fun {i} hi => by
    rw [bar_of_mem (hIM hi)]; rfl
  have bar_inj : ∀ {i j : G}, i ∈ I → j ∈ I → bar i = bar j → i = j := by
    intro i j hi hj h
    rw [bar_I hi, bar_I hj] at h
    exact congrArg Subtype.val (hιinj h)
  have bar_mem_map : ∀ (A : Subgroup G) {g : G} (hg : g ∈ I), bar g ∈ (A.subgroupOf I).map ι ↔ g ∈ A := by
    intro A g hg
    rw [bar_I hg]; exact hmem A ⟨g, hg⟩
  have hIn' : ∀ i ∈ I, x⁻¹ * i * x ∈ I := conj_inv_mem_of_finite x I hIn
  have hxnorm : x ∈ normalizer (I : Set G) := by
    rw [mem_normalizer_iff]
    intro i
    constructor
    · exact hIn i
    · intro h
      have := hIn' _ h
      simpa [mul_assoc] using this
  have hprod : (M : Set G) = (I : Set G) * (zpowers x : Set G) := by
    rw [hM]
    exact Subgroup.coe_mul_of_right_le_normalizer_left I (zpowers x) (by rw [zpowers_le]; exact hxnorm)
  have hZc : ∀ z' ∈ Z, ∀ m ∈ M, z' * m = m * z' := by
    intro z' hz' m hm
    rw [hZ] at hz'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz'
    have hmM : (m : G) ∈ (I : Set G) * (zpowers x : Set G) := by rw [← hprod]; exact hm
    obtain ⟨i, hi, c, hc, rfl⟩ := hmM
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have h1 : Commute ((x ^ 2) ^ j) i := (show Commute (x ^ 2) i from hx2 i hi).zpow_left j
    have h2 : Commute ((x ^ 2) ^ j) (x ^ k) := by
      rw [← zpow_natCast, ← zpow_mul]
      exact Commute.zpow_zpow_self x _ _
    exact (h1.mul_right h2)
  have hqpos : q - 1 ≠ 0 := by omega
  obtain ⟨g₀, hg₀⟩ := hTcyc.exists_generator
  have hog : orderOf g₀ = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, hTcard, hq]
  have hvdvd : 2 ^ ((q - 1).factorization 2) ∣ q - 1 := Nat.ordProj_dvd (q - 1) 2
  let σT : ↥T := g₀ ^ ((q - 1) / 2 ^ ((q - 1).factorization 2))
  have hσord : orderOf σT = 2 ^ ((q - 1).factorization 2) := by
    have := orderOf_pow_orderOf_div (x := g₀) (n := 2 ^ ((q - 1).factorization 2))
      (by rw [hog]; exact hqpos) (by rw [hog]; exact hvdvd)
    rw [hog] at this
    exact this
  let σ : ↥M ⧸ Z.subgroupOf M := (σT : ↥M ⧸ Z.subgroupOf M)
  have hσT : σ ∈ T := σT.2
  have hσord' : orderOf σ = 2 ^ ((q - 1).factorization 2) := by
    rw [← hσord]; exact Subgroup.orderOf_coe σT
  have hσIb : σ ∉ ι.range := by
    intro h
    have h1 : σ ∈ T ⊓ ι.range := ⟨hσT, h⟩
    rw [hTI] at h1
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    rw [hσord', hcardmap H hHI, hHc] at h2
    have hq2 : q - 1 = 2 * ((q - 1) / 2) := by obtain ⟨k, hk⟩ := hqodd; omega
    have h3 : 2 ^ ((q - 1).factorization 2 + 1) ∣ q - 1 := by
      have : 2 * 2 ^ ((q - 1).factorization 2) ∣ 2 * ((q - 1) / 2) := Nat.mul_dvd_mul_left 2 h2
      rw [← hq2, ← pow_succ'] at this
      exact this
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hqpos).mp h3
    omega
  have hxZ : ∀ j : ℤ, x ^ (2 * j) ∈ Z := by
    intro j
    rw [hZ]
    exact mem_zpowers_iff.mpr ⟨j, by rw [zpow_mul]; norm_cast⟩
  have hlift : ∃ (b : G) (hb : b ∈ I), bar (b * x) = σ := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective σ
    have hgM : (g : G) ∈ (I : Set G) * (zpowers x : Set G) := by rw [← hprod]; exact g.2
    obtain ⟨i, hi, c, hc, hgic⟩ := hgM
    have hgic' : i * c = (g : G) := hgic
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have hbarg : bar (g : G) = σ := by rw [bar_of_mem g.2]; exact hg
    rw [← hgic'] at hbarg
    have hiM : i ∈ M := hIM hi
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exfalso
      apply hσIb
      rw [← hbarg, bar_mul hiM (M.zpow_mem hxM _), bar_Z (hxZ j), mul_one, bar_I hi]
      exact ⟨⟨i, hi⟩, rfl⟩
    · refine ⟨i, hi, ?_⟩
      rw [← hbarg, zpow_add_one, ← mul_assoc, bar_mul (M.mul_mem hiM (M.zpow_mem hxM _)) hxM,
        bar_mul hiM (M.zpow_mem hxM _), bar_Z (hxZ j), mul_one, bar_mul hiM hxM]
  obtain ⟨b, hb, hbσ⟩ := hlift
  refine ⟨b, hb, ?_⟩
  have hτM : b * x ∈ M := M.mul_mem (hIM hb) hxM
  have hτI : ∀ i ∈ I, (b * x) * i * (b * x)⁻¹ ∈ I := by
    intro i hi
    have e : (b * x) * i * (b * x)⁻¹ = b * (x * i * x⁻¹) * b⁻¹ := by group
    rw [e]
    exact I.mul_mem (I.mul_mem hb (hIn i hi)) (I.inv_mem hb)
  have hτY : ∀ y ∈ Y, (b * x) * y * (b * x)⁻¹ ∈ Y := by
    intro y hy
    have hyI := hYI hy
    have hI' : (b * x) * y * (b * x)⁻¹ ∈ I := hτI y hyI
    have hbar : bar ((b * x) * y * (b * x)⁻¹) = σ * bar y * σ⁻¹ := by
      rw [bar_mul (M.mul_mem hτM (hIM hyI)) (M.inv_mem hτM), bar_mul hτM (hIM hyI), bar_inv hτM, hbσ]
    have hyb : bar y ∈ (Y.subgroupOf I).map ι := (bar_mem_map Y hyI).mpr hy
    have := hTY σ hσT _ hyb
    rw [← hbar] at this
    exact (bar_mem_map Y hI').mp this
  have hTcomm : ∀ s ∈ T, ∀ s' ∈ T, s * s' = s' * s := by
    intro s hs s' hs'
    obtain ⟨g, hg⟩ := hTcyc.exists_generator
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hg ⟨s, hs⟩)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hg ⟨s', hs'⟩)
    have : (⟨s, hs⟩ : ↥T) * ⟨s', hs'⟩ = ⟨s', hs'⟩ * ⟨s, hs⟩ := by
      rw [← hi, ← hj]; exact Commute.zpow_zpow_self g i j
    exact congrArg Subtype.val this
  have hτH : ∀ h ∈ H, (b * x) * h * (b * x)⁻¹ = h := by
    intro h hh
    have hhI := hHI hh
    have hbar : bar ((b * x) * h * (b * x)⁻¹) = σ * bar h * σ⁻¹ := by
      rw [bar_mul (M.mul_mem hτM (hIM hhI)) (M.inv_mem hτM), bar_mul hτM (hIM hhI), bar_inv hτM, hbσ]
    have hhb : bar h ∈ (H.subgroupOf I).map ι := (bar_mem_map H hhI).mpr hh
    have hcomm := hTcomm σ hσT _ (hHT hhb)
    apply bar_inj (hτI h hhI) hhI
    rw [hbar, hcomm]; group
  have hτν : (b * x) * (w * (b * x) * w⁻¹) ∈ Z := by
    have hwM : w ∈ M := hIM hwI
    have hbar : bar ((b * x) * (w * (b * x) * w⁻¹)) = 1 := by
      rw [bar_mul hτM (M.mul_mem (M.mul_mem hwM hτM) (M.inv_mem hwM)),
        bar_mul (M.mul_mem hwM hτM) (M.inv_mem hwM), bar_mul hwM hτM, bar_inv hwM, hbσ,
        bar_I hwI]
      have := hTw σ hσT
      rw [this]; group
    exact (bar_eq_one (M.mul_mem hτM (M.mul_mem (M.mul_mem (hIM hwI) hτM) (M.inv_mem (hIM hwI))))).mp hbar
  have hc : b * (x * b * x⁻¹) ∈ I := I.mul_mem hb (hIn b hb)
  have hcτ : (b * x) * (b * x) = (b * (x * b * x⁻¹)) * x ^ 2 := by group
  have hx2Z : x ^ 2 ∈ Z := by rw [hZ]; exact mem_zpowers _
  have hbarx2 : bar (x ^ 2) = 1 := bar_Z hx2Z
  have hbarc : bar (b * (x * b * x⁻¹)) = σ ^ 2 := by
    have h1 : bar ((b * x) * (b * x)) = σ ^ 2 := by rw [bar_mul hτM hτM, hbσ, pow_two]
    rw [hcτ, bar_mul (hIM hc) (M.pow_mem hxM 2), hbarx2, mul_one] at h1
    exact h1
  have hsq : σ ^ 2 ∈ ι.range := by
    have : ι.range.Normal := Subgroup.normal_of_index_eq_two hidx
    have := Subgroup.pow_index_mem ι.range σ
    rwa [hidx] at this
  have huI : (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) ∈ I := I.pow_mem hc _
  have hbaru : bar ((b * (x * b * x⁻¹)) ^ (2 ^ (n - 3))) = (σ ^ 2) ^ (2 ^ (n - 3)) := by
    rw [bar_pow (hIM hc), hbarc]
  have huH : (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) ∈ H := by
    refine (bar_mem_map H huI).mp ?_
    rw [hbaru, ← hTI]
    exact ⟨T.pow_mem (T.pow_mem hσT 2) _, ι.range.pow_mem hsq _⟩
  have hm4 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    have : n - 1 = (n - 3) + 2 := by omega
    rw [this, pow_add]; ring
  have h2m : 2 * 2 ^ (n - 3) = 2 ^ (n - 2) := by
    have : n - 2 = (n - 3) + 1 := by omega
    rw [this, pow_succ]; ring
  have hσpow : σ ^ (2 ^ (n - 1)) = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hσord']
    exact pow_dvd_pow 2 hqn
  have huu : (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) * (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) = 1 := by
    have h1 : bar ((b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) * (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3))) = 1 := by
      rw [bar_mul (hIM huI) (hIM huI), hbaru, ← pow_mul, ← pow_add]
      have : 2 * 2 ^ (n - 3) + 2 * 2 ^ (n - 3) = 2 ^ (n - 1) := by rw [hm4]; ring
      rw [this, hσpow]
    exact bar_inj (I.mul_mem huI huI) I.one_mem (by rw [h1, bar_one])
  have haa : (b * x) ^ (2 ^ (n - 3)) * (b * x) ^ (2 ^ (n - 3)) =
      (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) * x ^ (2 ^ (n - 2)) := by
    have e1 : (b * x) ^ (2 ^ (n - 3)) * (b * x) ^ (2 ^ (n - 3)) = ((b * x) * (b * x)) ^ (2 ^ (n - 3)) :=
      ((Commute.refl (b * x)).mul_pow _).symm
    rw [e1, hcτ]
    have hcom : Commute (b * (x * b * x⁻¹)) (x ^ 2) := (hx2 _ hc).symm
    rw [hcom.mul_pow, ← pow_mul, h2m]
  have hτinvI : ∀ i ∈ I, (b * x)⁻¹ * i * (b * x) ∈ I := conj_inv_mem_of_finite _ I hτI
  have haI : ∀ i ∈ I, ((b * x) ^ (2 ^ (n - 3)))⁻¹ * i * (b * x) ^ (2 ^ (n - 3)) ∈ I :=
    conj_pow_closed _ I hτinvI _
  have hτinvY : ∀ y ∈ Y, (b * x)⁻¹ * y * (b * x) ∈ Y := conj_inv_mem_of_finite _ Y hτY
  refine ⟨_, huH, huu, haa, ?_, ?_, ?_, M.pow_mem hτM _⟩
  ·
    set u : G := (b * (x * b * x⁻¹)) ^ (2 ^ (n - 3)) with hu
    set ν : G := (b * x) * (w * (b * x) * w⁻¹) with hνdef
    set t : G := x ^ (2 ^ (n - 2)) with ht
    have htZ : t ∈ Z := by
      rw [hZ]
      exact mem_zpowers_iff.mpr ⟨((2 ^ (n - 3) : ℕ) : ℤ), by rw [zpow_natCast, ← pow_mul, h2m]⟩
    have hwτ : w * (b * x) * w⁻¹ = (b * x)⁻¹ * ν := by rw [hνdef]; group
    have hcomν : Commute (b * x)⁻¹ ν := (hZc ν hτν _ (M.inv_mem hτM)).symm
    have hwa : w * (b * x) ^ (2 ^ (n - 3)) * w⁻¹ = ((b * x) ^ (2 ^ (n - 3)))⁻¹ * ν ^ (2 ^ (n - 3)) := by
      have e1 : w * (b * x) ^ (2 ^ (n - 3)) * w⁻¹ = (w * (b * x) * w⁻¹) ^ (2 ^ (n - 3)) := by
        rw [conj_pow]
      rw [e1, hwτ, hcomν.mul_pow, inv_pow]
    have e2 : ((b * x) ^ (2 ^ (n - 3)))⁻¹ * w * (b * x) ^ (2 ^ (n - 3)) =
        ((b * x) ^ (2 ^ (n - 3)))⁻¹ * (w * (b * x) ^ (2 ^ (n - 3)) * w⁻¹) * w := by group
    have haa' : ((b * x) ^ (2 ^ (n - 3)))⁻¹ * ((b * x) ^ (2 ^ (n - 3)))⁻¹ = (u * t)⁻¹ := by
      rw [← haa, mul_inv_rev]
    have hform : ((b * x) ^ (2 ^ (n - 3)))⁻¹ * w * (b * x) ^ (2 ^ (n - 3)) =
        u⁻¹ * (t⁻¹ * ν ^ (2 ^ (n - 3))) * w := by
      rw [e2, hwa]
      have h4 : (u * t)⁻¹ = u⁻¹ * t⁻¹ := by
        rw [mul_inv_rev]
        exact (show Commute t u from hZc t htZ u (hIM huI)).inv_inv.eq
      calc ((b * x) ^ (2 ^ (n - 3)))⁻¹ * (((b * x) ^ (2 ^ (n - 3)))⁻¹ * ν ^ (2 ^ (n - 3))) * w
          = (((b * x) ^ (2 ^ (n - 3)))⁻¹ * ((b * x) ^ (2 ^ (n - 3)))⁻¹) * ν ^ (2 ^ (n - 3)) * w := by
            group
        _ = _ := by rw [haa', h4]; group
    have hAI := haI w hwI
    have htν : t⁻¹ * ν ^ (2 ^ (n - 3)) = u * (((b * x) ^ (2 ^ (n - 3)))⁻¹ * w * (b * x) ^ (2 ^ (n - 3))) * w⁻¹ := by
      rw [hform]; group
    have htνI : t⁻¹ * ν ^ (2 ^ (n - 3)) ∈ I := by
      rw [htν]
      exact I.mul_mem (I.mul_mem huI hAI) (I.inv_mem hwI)
    have htνZ : t⁻¹ * ν ^ (2 ^ (n - 3)) ∈ Z := Z.mul_mem (Z.inv_mem htZ) (Z.pow_mem hτν _)
    have h5 : t⁻¹ * ν ^ (2 ^ (n - 3)) ∈ I ⊓ Z := ⟨htνI, htνZ⟩
    rw [hZI] at h5
    have h6 : t⁻¹ * ν ^ (2 ^ (n - 3)) = 1 := Subgroup.mem_bot.mp h5
    rw [hform, h6, mul_one, inv_eq_of_mul_eq_one_right huu]
  · intro h hh
    have hc1 : (b * x) * h = h * (b * x) := by
      have := hτH h hh
      calc (b * x) * h = ((b * x) * h * (b * x)⁻¹) * (b * x) := by group
        _ = h * (b * x) := by rw [this]
    have hc2 : (b * x) ^ (2 ^ (n - 3)) * h = h * (b * x) ^ (2 ^ (n - 3)) :=
      Commute.pow_left (show Commute (b * x) h from hc1) _
    calc ((b * x) ^ (2 ^ (n - 3)))⁻¹ * h * (b * x) ^ (2 ^ (n - 3))
        = ((b * x) ^ (2 ^ (n - 3)))⁻¹ * (h * (b * x) ^ (2 ^ (n - 3))) := by group
      _ = ((b * x) ^ (2 ^ (n - 3)))⁻¹ * ((b * x) ^ (2 ^ (n - 3)) * h) := by rw [hc2]
      _ = h := by group
  · exact conj_pow_closed (b * x) Y hτinvY _

end Core


end CFSG.GH74.GLS.SP.Local
