module

public import CFSG.GH74.GLS.SP.Local.SPLCtOut
public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

theorem xnorm_core (hP : PGL2CartanStmt) (I Y H M Z : Subgroup G) (x w : G) (q : ℕ)
    (hM : M = I ⊔ zpowers x) (hZ : Z = zpowers (x ^ 2))
    (hq5 : 5 ≤ q) (hqodd : Odd q)
    (hIn : ∀ i ∈ I, x * i * x⁻¹ ∈ I)
    (hZI : I ⊓ Z = ⊥) [hN : (Z.subgroupOf M).Normal]
    (hcardI : Nat.card ↥I = q * (q ^ 2 - 1) / 2)
    (hquot : IVK.IsPGL2 (↥M ⧸ Z.subgroupOf M) (fun r => r = q))
    (hYI : Y ≤ I) (hYc : Nat.card ↥Y = q) (hHI : H ≤ I) (hHcyc : IsCyclic ↥H)
    (hHc : Nat.card ↥H = (q - 1) / 2) (hHY : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hwI : w ∈ I) (hw2 : w * w = 1) (hwH : w ∉ H) (hwinv : ∀ h ∈ H, w * h * w⁻¹ = h⁻¹) :
    ∃ b ∈ I, b * x * b⁻¹ ∈ normalizer ((H ⊔ zpowers w : Subgroup G) : Set G) := by
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
  obtain ⟨wb, hwb⟩ : ∃ wb : ↥M ⧸ Z.subgroupOf M, ι ⟨w, hwI⟩ = wb := ⟨_, rfl⟩
  have hwbL : wb ∈ ι.range := ⟨⟨w, hwI⟩, hwb⟩
  have hwbsq : wb * wb = 1 := by
    rw [← hwb, ← map_mul]; convert map_one ι; exact Subtype.ext hw2
  have hwbH : wb ∉ (H.subgroupOf I).map ι := by rw [← hwb, hmem H]; exact hwH
  have hwbinvH : ∀ h ∈ (H.subgroupOf I).map ι, wb * h * wb⁻¹ = h⁻¹ := by
    rintro _ ⟨h₀, hh₀, rfl⟩
    have hh : (⟨w, hwI⟩ : ↥I) * h₀ * (⟨w, hwI⟩ : ↥I)⁻¹ = h₀⁻¹ := Subtype.ext (hwinv _ hh₀)
    calc wb * ι h₀ * wb⁻¹ = ι ⟨w, hwI⟩ * ι h₀ * (ι ⟨w, hwI⟩)⁻¹ := by rw [hwb]
      _ = ι ((⟨w, hwI⟩ : ↥I) * h₀ * (⟨w, hwI⟩ : ↥I)⁻¹) := by simp
      _ = ι h₀⁻¹ := by rw [hh]
      _ = (ι h₀)⁻¹ := map_inv ι h₀
  obtain ⟨T, hTcyc, hTcard, hHT, -, hTw, hTI⟩ := hP (F := F) (by rw [hq]; exact hqodd)
    (by rw [hq]; exact hq5) θ ι.range hidx ((Y.subgroupOf I).map ι) ((H.subgroupOf I).map ι)
    (by rw [hcardmap Y hYI, hYc, hq])
    (by rw [MonoidHom.range_eq_map]; exact Subgroup.map_mono le_top) hHcyc'
    (by rw [hcardmap H hHI, hHc, hq])
    (by
      rintro _ ⟨h₀, hh₀, rfl⟩ _ ⟨y₀, hy₀, rfl⟩
      refine ⟨h₀ * y₀ * h₀⁻¹, ?_, by simp⟩
      exact hHY _ hh₀ _ hy₀)
    wb hwbsq hwbH hwbinvH
  let bar : G → ↥M ⧸ Z.subgroupOf M := fun g => if hg : g ∈ M then π ⟨g, hg⟩ else 1
  have bar_of_mem : ∀ {g : G} (hg : g ∈ M), bar g = π ⟨g, hg⟩ := fun {g} hg => by simp [bar, hg]
  have bar_mul : ∀ {g g' : G}, g ∈ M → g' ∈ M → bar (g * g') = bar g * bar g' := by
    intro g g' hg hg'
    rw [bar_of_mem (M.mul_mem hg hg'), bar_of_mem hg, bar_of_mem hg']
    exact map_mul π ⟨g, hg⟩ ⟨g', hg'⟩
  have bar_inv : ∀ {g : G}, g ∈ M → bar g⁻¹ = (bar g)⁻¹ := by
    intro g hg
    rw [bar_of_mem (M.inv_mem hg), bar_of_mem hg]
    exact map_inv π ⟨g, hg⟩
  have bar_zpow : ∀ {g : G}, g ∈ M → ∀ k : ℤ, bar (g ^ k) = bar g ^ k := by
    intro g hg k
    rw [bar_of_mem (M.zpow_mem hg k), bar_of_mem hg]
    exact map_zpow π ⟨g, hg⟩ k
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
  have hbw : bar w = wb := by rw [bar_I hwI]; exact hwb
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
  have hTcomm : ∀ s ∈ T, ∀ s' ∈ T, s * s' = s' * s := by
    intro s hs s' hs'
    obtain ⟨g, hg⟩ := hTcyc.exists_generator
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hg ⟨s, hs⟩)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hg ⟨s', hs'⟩)
    have : (⟨s, hs⟩ : ↥T) * ⟨s', hs'⟩ = ⟨s', hs'⟩ * ⟨s, hs⟩ := by
      rw [← hi, ← hj]; exact Commute.zpow_zpow_self g i j
    exact congrArg Subtype.val this
  have hx2Z : x ^ 2 ∈ Z := by rw [hZ]; exact mem_zpowers _
  have hxbsq : bar x * bar x = 1 := by
    rw [← bar_mul hxM hxM, ← pow_two]; exact bar_Z hx2Z
  have hxbL : bar x ∉ ι.range := by
    intro hxL
    have htop : ι.range = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
      have hmM : ((m : ↥M) : G) ∈ (I : Set G) * (zpowers x : Set G) := by rw [← hprod]; exact m.2
      obtain ⟨i, hi, c, hc, hic⟩ := hmM
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      have hic' : i * x ^ k = (m : G) := hic
      have hbm : bar (m : G) = (m : ↥M ⧸ Z.subgroupOf M) := by rw [bar_of_mem m.2]; rfl
      rw [← hbm, ← hic', bar_mul (hIM hi) (M.zpow_mem hxM k), bar_zpow hxM, bar_I hi]
      exact ι.range.mul_mem ⟨⟨i, hi⟩, rfl⟩ (ι.range.zpow_mem hxL k)
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  have hTL : ¬ T ≤ ι.range := by
    intro hle
    have h1 : T ⊓ ι.range = T := inf_eq_left.mpr hle
    have h2 : Nat.card ↥(T ⊓ ι.range) = Nat.card ↥T := by rw [h1]
    rw [hTI, hcardmap H hHI, hHc, hTcard, hq] at h2
    omega
  obtain ⟨σ, hσT, hσL⟩ : ∃ σ ∈ T, σ ∉ ι.range := by
    by_contra hcon
    exact hTL (fun σ hσ => by_contra (fun h => hcon ⟨σ, hσ, h⟩))
  have hsq : σ ^ 2 ∈ ι.range := by
    have : ι.range.Normal := Subgroup.normal_of_index_eq_two hidx
    have := Subgroup.pow_index_mem ι.range σ
    rwa [hidx] at this
  have hσ2H : σ ^ 2 ∈ (H.subgroupOf I).map ι := by
    rw [← hTI]
    exact ⟨T.pow_mem hσT 2, hsq⟩
  have hwbTall : ∀ s ∈ T, wb * s * wb⁻¹ = s⁻¹ := hTw
  have hwbinv : wb⁻¹ = wb := inv_eq_of_mul_eq_one_right hwbsq
  have hβsq : (σ * wb) * (σ * wb) = 1 := by
    have hwbT : wb * σ * wb = σ⁻¹ := by
      have := hwbTall σ hσT
      rwa [hwbinv] at this
    calc σ * wb * (σ * wb) = σ * (wb * σ * wb) := by group
      _ = σ * σ⁻¹ := by rw [hwbT]
      _ = 1 := mul_inv_cancel σ
  have hβL : σ * wb ∉ ι.range := by
    intro h
    apply hσL
    have := ι.range.mul_mem h (ι.range.inv_mem hwbL)
    simpa using this
  obtain ⟨l, hl, hlx⟩ := pgl2_outer_involutions_conj (F := F) (by rw [hq]; exact hqodd)
    (by rw [hq]; exact hq5) θ ι.range hidx (bar x) (σ * wb) hxbsq hβsq hxbL hβL
  obtain ⟨b', rfl⟩ := hl
  have hb : (b' : G) ∈ I := b'.2
  refine ⟨(b' : G), hb, ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g = (b' : G) * x * (b' : G)⁻¹ := ⟨_, rfl⟩
  rw [← hg]
  have hbM : (b' : G) ∈ M := hIM hb
  have hbb : bar (b' : G) = ι b' := bar_I hb
  have hgM : g ∈ M := by
    rw [hg]; exact M.mul_mem (M.mul_mem hbM hxM) (M.inv_mem hbM)
  have hbarg : bar g = σ * wb := by
    rw [hg, bar_mul (M.mul_mem hbM hxM) (M.inv_mem hbM), bar_mul hbM hxM, bar_inv hbM, hbb]
    exact hlx
  have hgI : ∀ i ∈ I, g * i * g⁻¹ ∈ I := by
    intro i hi
    have e : g * i * g⁻¹ = (b' : G) * (x * ((b' : G)⁻¹ * i * (b' : G)) * x⁻¹) * (b' : G)⁻¹ := by
      rw [hg]; group
    rw [e]
    have hi' : (b' : G)⁻¹ * i * (b' : G) ∈ I := I.mul_mem (I.mul_mem (I.inv_mem hb) hi) hb
    exact I.mul_mem (I.mul_mem hb (hIn _ hi')) (I.inv_mem hb)
  have hgH : ∀ h ∈ H, g * h * g⁻¹ = h⁻¹ := by
    intro h hh
    have hhI := hHI hh
    have hhb : bar h ∈ (H.subgroupOf I).map ι := (bar_mem_map H hhI).mpr hh
    have hbar : bar (g * h * g⁻¹) = (σ * wb) * bar h * (σ * wb)⁻¹ := by
      rw [bar_mul (M.mul_mem hgM (hIM hhI)) (M.inv_mem hgM), bar_mul hgM (hIM hhI), bar_inv hgM, hbarg]
    have hcomm : σ * (bar h)⁻¹ = (bar h)⁻¹ * σ := hTcomm σ hσT _ (T.inv_mem (hHT hhb))
    apply bar_inj (hgI h hhI) (hHI (H.inv_mem hh))
    calc bar (g * h * g⁻¹) = (σ * wb) * bar h * (σ * wb)⁻¹ := hbar
      _ = σ * (wb * bar h * wb⁻¹) * σ⁻¹ := by group
      _ = σ * (bar h)⁻¹ * σ⁻¹ := by rw [hwbinvH _ hhb]
      _ = (bar h)⁻¹ * σ * σ⁻¹ := by rw [hcomm]
      _ = (bar h)⁻¹ := by group
      _ = bar h⁻¹ := (bar_inv (hIM hhI)).symm
  have hgw : ∃ h' ∈ H, g * w * g⁻¹ = h' * w := by
    obtain ⟨h', hh', hh'e⟩ := hσ2H
    have hh'I : (h' : G) ∈ I := h'.2
    have hbh' : bar (h' : G) = σ ^ 2 := by rw [bar_I hh'I]; exact hh'e
    have hwb' : wb * σ⁻¹ = σ * wb := by
      have h2 := hwbTall σ⁻¹ (T.inv_mem hσT)
      rw [inv_inv] at h2
      calc wb * σ⁻¹ = (wb * σ⁻¹ * wb⁻¹) * wb := by group
        _ = σ * wb := by rw [h2]
    refine ⟨(h' : G), hh', ?_⟩
    apply bar_inj (hgI w hwI) (I.mul_mem hh'I hwI)
    have hL : bar (g * w * g⁻¹) = σ ^ 2 * wb := by
      rw [bar_mul (M.mul_mem hgM (hIM hwI)) (M.inv_mem hgM), bar_mul hgM (hIM hwI), bar_inv hgM, hbarg, hbw]
      calc σ * wb * wb * (σ * wb)⁻¹ = σ * (wb * wb) * (wb⁻¹ * σ⁻¹) := by group
        _ = σ * (wb⁻¹ * σ⁻¹) := by rw [hwbsq, mul_one]
        _ = σ * (wb * σ⁻¹) := by rw [hwbinv]
        _ = σ * (σ * wb) := by rw [hwb']
        _ = σ ^ 2 * wb := by rw [pow_two, mul_assoc]
    have hR : bar ((h' : G) * w) = σ ^ 2 * wb := by
      rw [bar_mul (hIM hh'I) (hIM hwI), hbh', hbw]
    rw [hL, hR]
  obtain ⟨h', hh', hgwe⟩ := hgw
  have hgP : ∀ p ∈ H ⊔ zpowers w, g * p * g⁻¹ ∈ H ⊔ zpowers w := by
    have hle : H ⊔ zpowers w ≤ (H ⊔ zpowers w).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun h hh => ?_) (zpowers_le.mpr ?_)
      · show g * h * g⁻¹ ∈ H ⊔ zpowers w
        rw [hgH h hh]
        exact Subgroup.mem_sup_left (H.inv_mem hh)
      · show g * w * g⁻¹ ∈ H ⊔ zpowers w
        rw [hgwe]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right (mem_zpowers w))
    intro p hp
    exact hle hp
  rw [mem_normalizer_iff]
  intro p
  constructor
  · exact hgP p
  · intro hp
    have h2 := conj_inv_mem_of_finite g _ hgP _ hp
    have e : g⁻¹ * (g * p * g⁻¹) * g = p := by group
    rwa [e] at h2

end Core

section Ict

variable {G : Type} [Group G] [Finite G]

theorem ict_diag_mem (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) {k : G} (hk : k ∈ D.K₁) :
    k * (D.t * k * D.t⁻¹) ∈ D.Ict := by
  rw [Ict_eq D hs]
  exact ⟨⟨k, hk⟩, rfl⟩

theorem ict_center_trivial (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) :
    ∀ g : ↥D.Ict, (∀ i : ↥D.Ict, g * i = i * g) → g = 1 := by
  obtain ⟨F, hF1, hF2, hFq, ⟨e⟩⟩ := Ict_isL2 D hs
  intro g hg
  let e' := e.trans (IVK.L2.equivPSL F)
  have hcen : e' g ∈ Subgroup.center (CFSG.GorensteinWalter.PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨i, rfl⟩ := e'.surjective y
    rw [← map_mul, ← map_mul, hg i]
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot F] at hcen
  exact e'.map_eq_one_iff.mp (Subgroup.mem_bot.mp hcen)

theorem ict_inf_sq (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) {x : G}
    (hx2 : ∀ i ∈ D.Ict, x ^ 2 * i = i * x ^ 2) : D.Ict ⊓ zpowers (x ^ 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgI, hgZ⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hgZ
  have hcomm : ∀ i : ↥D.Ict, (⟨(x ^ 2) ^ j, hgI⟩ : ↥D.Ict) * i = i * ⟨(x ^ 2) ^ j, hgI⟩ := by
    intro i
    apply Subtype.ext
    exact ((show Commute (x ^ 2) i from hx2 i i.2).zpow_left j)
  have := ict_center_trivial D hs _ hcomm
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem ict_card (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) :
    Nat.card ↥D.Ict = D.q * (D.q ^ 2 - 1) / 2 := by
  obtain ⟨F, hF1, hF2, hFq, ⟨e⟩⟩ := Ict_isL2 D hs
  have hq : Nat.card F = D.q := hFq
  let e' := e.trans (IVK.L2.equivPSL F)
  obtain ⟨k, hk1, hkq⟩ := hs.q_pow
  rw [Nat.card_congr e'.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F
    ⟨D.p, k, hs.prime, hs.prime.odd_of_ne_two hs.p_ne_two, hk1, by rw [hq, hkq]⟩, hq]

theorem Y₀_le_Ict (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    D.Y₀ ≤ D.toSPLNot1.Ict := fun y hy => by
  obtain ⟨a, ha, rfl⟩ := Y₀_decomp D hs h3 hy
  exact ict_diag_mem D.toSPLNot1 hs (h3.X₁_le ha)

theorem H₀_le_Ict (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D) : D.H₀ ≤ D.Ict := by
  show zpowers (D.h₁ * D.h₂) ≤ D.Ict
  rw [zpowers_le]
  exact ict_diag_mem D hs h1.h₁_mem

theorem w_mem_Ict (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D) : D.w ∈ D.Ict :=
  ict_diag_mem D hs h1.w₁_mem

end Ict

section Main

theorem ct_xnorm {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D) (hA : SPLCtA D) {x : G} (hxCt : x ∈ D.Ct)
    (hx2 : ∀ i ∈ D.Ict, x ^ 2 * i = i * x ^ 2)
    (hN : ((zpowers (x ^ 2)).subgroupOf (D.Ict ⊔ zpowers x)).Normal)
    (hquot : IVK.IsPGL2 (↥(D.Ict ⊔ zpowers x) ⧸ (zpowers (x ^ 2)).subgroupOf (D.Ict ⊔ zpowers x))
        (fun r => r = D.q)) :
    ∃ b ∈ D.Ict, b * x * b⁻¹ ∈ normalizer ((D.H₀ ⊔ zpowers D.w : Subgroup G) : Set G) := by
  obtain ⟨X₁, X₁', Y₁, hX⟩ := exists_X ⟨D, D.Act, D.Ict, x⟩ hs h1
  let D₃ : SPLNot3 G := ⟨⟨D, D.Act, D.Ict, x⟩, X₁, X₁', Y₁, 1⟩
  have h3 : SPL3X D₃ := hX 1
  exact xnorm_core pgl2CartanStmt D.Ict D₃.Y₀ D.H₀ (D.Ict ⊔ zpowers x) (zpowers (x ^ 2)) x D.w D.q
    rfl rfl hs.q_ge hs.odd_q (hA.I_normal x hxCt) (ict_inf_sq D hs hx2) (ict_card D hs) hquot
    (Y₀_le_Ict D₃ hs h3) (Y₀_card D₃ hs h3) (H₀_le_Ict D hs h1) (isCyclic_zpowers _)
    (H₀_card' D₃ hs h1) (H₀_norm_Y₀ D₃ hs h1 h3) (w_mem_Ict D hs h1) (w_mul_w D₃ hs h1)
    (w_not_mem_H₀ D₃ hs h1) (w_inv_H₀ D₃ hs h1)

end Main

end CFSG.GH74.GLS.SP.Local
