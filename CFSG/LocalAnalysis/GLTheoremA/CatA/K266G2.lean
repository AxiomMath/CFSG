module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K266Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

private theorem inner_rep_unique {K : Subgroup G} (hZ : Subgroup.center ↥K = ⊥) {k k' : G}
    (hk : k ∈ K) (hk' : k' ∈ K) (h : ∀ x ∈ K, k * x * k⁻¹ = k' * x * k'⁻¹) : k = k' := by
  have hz : k'⁻¹ * k ∈ K := K.mul_mem (K.inv_mem hk') hk
  have hcen : (⟨k'⁻¹ * k, hz⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have h1 : k * x = (k' * x * k'⁻¹) * k := by rw [← h x hx]; group
    show x * (k'⁻¹ * k) = k'⁻¹ * k * x
    calc x * (k'⁻¹ * k) = k'⁻¹ * ((k' * x * k'⁻¹) * k) := by group
      _ = k'⁻¹ * (k * x) := by rw [h1]
      _ = k'⁻¹ * k * x := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  have h2 : k'⁻¹ * k = 1 := congrArg Subtype.val hcen
  exact (inv_mul_eq_one.mp h2).symm

private theorem conj_comm_iff {a c x : G} (h : a * x * a⁻¹ = c * x * c⁻¹) :
    a * x = x * a ↔ c * x = x * c := by
  have e1 : a * x = x * a ↔ a * x * a⁻¹ = x := (mul_inv_eq_iff_eq_mul).symm
  have e2 : c * x = x * c ↔ c * x * c⁻¹ = x := (mul_inv_eq_iff_eq_mul).symm
  rw [e1, e2, h]

private theorem isElemAbelian_range_of {B : Subgroup G} (hB : IsElemAbelian 3 B) (ρ : B →* G) :
    IsElemAbelian 3 ρ.range := by
  refine ⟨⟨⟨fun a c => ?_⟩⟩, ?_⟩
  · rcases a with ⟨_, ⟨b, rfl⟩⟩
    rcases c with ⟨_, ⟨c, rfl⟩⟩
    apply Subtype.ext
    show ρ b * ρ c = ρ c * ρ b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hB b.2 c.2)
  · rintro _ ⟨b, rfl⟩
    have hb3 : b ^ 3 = (1 : B) := Subtype.ext (hB.2 b b.2)
    rw [← map_pow, hb3, map_one]

private theorem mem_normalizer_of_conj {K T : Subgroup G} (hTK : T ≤ K) {b d : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hd : d ∈ Subgroup.normalizer (T : Set G))
    (h : ∀ x ∈ K, b * x * b⁻¹ = d * x * d⁻¹) : b ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hbK hd ⊢
  intro y
  constructor
  · intro hy
    have hyK : y ∈ K := hTK hy
    rw [h y hyK]
    exact (hd y).mp hy
  · intro hby
    have hyK : y ∈ K := (hbK y).mpr (hTK hby)
    have h2 : d * y * d⁻¹ ∈ T := by
      rw [← h y hyK]
      exact hby
    exact (hd y).mpr h2

end Helpers

theorem i266G2_of_facts (G : Type) [Group G] [Finite G] (n : ℕ)
    (hInn : K266InnG2 n) (hOdd : K266OddG2 n) (hLayer : K266LayerG2 n) (hKey : K266KeyG2 n)
    (hDisj : K266G2NotU6) (X K B : Subgroup G) (hK : GLAPComponent 3 X K)
    (hG2 : catalogIs (PSimple 3 K) (S10.isG2n n))
    (hZ : Subgroup.center (PQuot 3 K) = ⊥) (hO : GLAPPrimeCoreOf 3 K = ⊥)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hBc : 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ Nat.card B)
    (hInnB : InnDiagOn 3 B K)
    (hT : ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K) :
    ∃ (E : Subgroup G) (y : G) (J : Subgroup G), S10.IsE0 B K E ∧ y ∈ E ∧ ¬ CentMod 3 K y ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      ((catalogIs (PSimple 3 K) (S10.isG2n n) → Even n ∧ catalogIs (PSimple 3 J) (S10.isL2n n)) ∧
        (catalogIs (PSimple 3 K) (S10.isU6n n) → catalogIs (PSimple 3 J) (S10.isUrn n))) ∧
      ∃ T : Subgroup G, T ≤ K ⊓ Subgroup.centralizer ({y} : Set G) ∧ IsPGroup 2 T ∧
        B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧
        IsEmpty (T ≃* QuaternionGroup 2) := by
  classical
  have hO' : GLAPPrimeCore 3 ↥K = ⊥ := by
    have h : (GLAPPrimeCore 3 ↥K).map K.subtype = ⊥ := hO
    exact (Subgroup.map_eq_bot_iff_of_injective (GLAPPrimeCore 3 ↥K) (Subgroup.subtype_injective K)).mp h
  have hPQ : PQuot 3 K ≃* ↥K := (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
  have hPS : PSimple 3 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans hPQ)
  have hKcat : catalogIs ↥K (S10.isG2n n) := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hG2
    exact ⟨i, hi, ⟨hPS.symm.trans e⟩⟩
  have hZK : Subgroup.center ↥K = ⊥ := by
    have h := Subgroup.map_center_eq hPQ
    rw [hZ, Subgroup.map_bot] at h
    exact h.symm
  have hinn : ∀ a ∈ B, ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹ :=
    hInn G X K B hK hG2 hZ hO hInnB
  choose! kf hkfK hkf using hinn
  have kf_mul : ∀ b ∈ B, ∀ c ∈ B, kf (b * c) = kf b * kf c := by
    intro b hb c hc
    apply inner_rep_unique hZK (hkfK _ (B.mul_mem hb hc)) (K.mul_mem (hkfK b hb) (hkfK c hc))
    intro x hx
    have hcx : c * x * c⁻¹ ∈ K := by
      rw [hkf c hc x hx]
      exact K.mul_mem (K.mul_mem (hkfK c hc) hx) (K.inv_mem (hkfK c hc))
    calc kf (b * c) * x * (kf (b * c))⁻¹ = (b * c) * x * (b * c)⁻¹ := (hkf (b * c) (B.mul_mem hb hc) x hx).symm
      _ = b * (c * x * c⁻¹) * b⁻¹ := by group
      _ = kf b * (c * x * c⁻¹) * (kf b)⁻¹ := hkf b hb _ hcx
      _ = kf b * (kf c * x * (kf c)⁻¹) * (kf b)⁻¹ := by rw [hkf c hc x hx]
      _ = kf b * kf c * x * (kf b * kf c)⁻¹ := by group
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →* G, ∀ b : B, ρ b = kf (b : G) :=
    ⟨MonoidHom.mk' (fun b : B => kf (b : G)) (fun b c => kf_mul _ b.2 _ c.2), fun b => rfl⟩
  have hρK : ∀ b : B, ρ b ∈ K := fun b => by rw [hρ]; exact hkfK _ b.2
  have hρconj : ∀ b : B, ∀ x ∈ K, (b : G) * x * (b : G)⁻¹ = ρ b * x * (ρ b)⁻¹ := fun b x hx => by
    rw [hρ]; exact hkf _ b.2 x hx
  have hρcomm : ∀ b : B, ∀ x ∈ K, (b : G) * x = x * (b : G) ↔ ρ b * x = x * ρ b := fun b x hx =>
    conj_comm_iff (hρconj b x hx)
  have hρone : ∀ b : B, ρ b = 1 ↔ ∀ x ∈ K, (b : G) * x = x * (b : G) := by
    intro b
    constructor
    · intro h x hx
      exact (hρcomm b x hx).mpr (by rw [h, one_mul, mul_one])
    · intro h
      refine inner_rep_unique hZK (hρK b) (K.one_mem) (fun x hx => ?_)
      have h2 : ρ b * x = x * ρ b := (hρcomm b x hx).mp (h x hx)
      rw [one_mul, inv_one, mul_one, mul_inv_eq_iff_eq_mul]
      exact h2
  have hDK : ρ.range ≤ K := by
    rintro _ ⟨b, rfl⟩
    exact hρK b
  have hDEA : IsElemAbelian 3 ρ.range := isElemAbelian_range_of hB ρ
  have hkerCz : ∀ b : B, ρ b = 1 → (b : G) ∈ B ⊓ centModSubgroup 3 K := fun b hb => by
    have hc := (hρone b).mp hb
    have hmem : (b : G) ∈ centModSubgroup 3 K := by
      show (b : G) ∈ Subgroup.normalizer (K : Set G) ∧ ∀ l ∈ K, ⁅l, (b : G)⁆ ∈ GLAPPrimeCoreOf 3 K
      refine ⟨hBN b.2, fun l hl => ?_⟩
      rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hc l hl).symm
    exact Subgroup.mem_inf.mpr ⟨b.2, hmem⟩
  have hD9 : 9 ≤ Nat.card ρ.range := by
    have hinj : Nat.card ρ.ker ≤ Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
      refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : G), hkerCz x.1 (MonoidHom.mem_ker.mp x.2)⟩) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg Subtype.val hxy
      exact h
    have hmul := Subgroup.card_ker_mul_card_range ρ
    have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
    have h9 : Nat.card ρ.ker * 9 ≤ Nat.card ρ.ker * Nat.card ρ.range := by
      calc Nat.card ρ.ker * 9 = 3 ^ 2 * Nat.card ρ.ker := by ring
        _ ≤ 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) := Nat.mul_le_mul_left _ hinj
        _ ≤ Nat.card B := hBc
        _ = Nat.card ρ.ker * Nat.card ρ.range := hmul.symm
    exact Nat.le_of_mul_le_mul_left h9 hpos
  obtain ⟨T₀, hT₀K, hT₀2, hT₀N, hT₀O⟩ := hT
  have hT₀ne : T₀ ≠ ⊥ := by
    intro h
    apply hT₀O
    rw [h, hO]
  have hDN₀ : ρ.range ≤ Subgroup.normalizer (T₀ : Set G) := by
    rintro _ ⟨b, rfl⟩
    exact mem_normalizer_of_conj hT₀K (Subgroup.le_normalizer (hρK b)) (hT₀N b.2)
      (fun x hx => (hρconj b x hx).symm)
  have hEven : Even n := by
    rcases Nat.even_or_odd n with h | h
    · exact h
    · exact absurd hDN₀ (hOdd G K ρ.range T₀ hKcat h hDEA hD9 hDK hT₀K hT₀2 hT₀ne)
  obtain ⟨y', hy'D, hy'1, ⟨J, hJ1, hJc, hJcat⟩, ⟨T₁, hT₁C, hT₁2, hT₁N, hT₁comm, hT₁Q⟩⟩ :=
    hKey G K ρ.range hKcat hEven hDEA hD9 hDK
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy'D
  have hbne : (b : G) ≠ 1 := by
    intro h
    apply hy'1
    rw [← hb]
    have hb1 : b = 1 := Subtype.ext h
    rw [hb1, map_one]
  have hb3 : (b : G) ^ 3 = 1 := hB.2 _ b.2
  have hbpow : b ^ 3 = (1 : B) := Subtype.ext hb3
  have hy3 : y' ^ 3 = 1 := by rw [← hb, ← map_pow, hbpow, map_one]
  have hordy : orderOf y' = 3 := orderOf_eq_prime hy3 hy'1
  have hcentX : ∀ c ∈ B ⊓ centModSubgroup 3 K, ∀ x ∈ K, x * c = c * x := by
    intro c hc x hx
    have hcm : ∀ l ∈ K, ⁅l, c⁆ ∈ GLAPPrimeCoreOf 3 K :=
      (show c ∈ Subgroup.normalizer (K : Set G) ∧ ∀ l ∈ K, ⁅l, c⁆ ∈ GLAPPrimeCoreOf 3 K from
        (Subgroup.mem_inf.mp hc).2).2
    have h1 : ⁅x, c⁆ = 1 := by
      have := hcm x hx
      rw [hO, Subgroup.mem_bot] at this
      exact this
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hCzB : B ⊓ centModSubgroup 3 K ≤ B := inf_le_left
  have hEB : Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr b.2) hCzB
  have hbE : (b : G) ∈ Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hKCE : K ⊓ Subgroup.centralizer ((Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) :
      Subgroup G) : Set G) = K ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact Subgroup.mem_centralizer_iff.mp hx (b : G) (by simpa using hbE)
    · rintro ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      have hbx : (b : G) * x = x * (b : G) := Subgroup.mem_centralizer_iff.mp hx _ (Set.mem_singleton _)
      have hEx : Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff.mp hh]
          exact hbx.symm
        · intro c hc
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff.mp hh]
          exact hcentX c hc x hxK
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.mp (hEx hh) x (Set.mem_singleton x)).symm
  have hKCb : K ⊓ Subgroup.centralizer ({(b : G)} : Set G) = K ⊓ Subgroup.centralizer ({y'} : Set G) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      have h1 : (b : G) * x = x * (b : G) := Subgroup.mem_centralizer_iff.mp hx _ (Set.mem_singleton _)
      have h2 : y' * x = x * y' := by rw [← hb]; exact (hρcomm b x hxK).mp h1
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact h2
    · rintro ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      have h2 : y' * x = x * y' := Subgroup.mem_centralizer_iff.mp hx _ (Set.mem_singleton _)
      have h1 : (b : G) * x = x * (b : G) := (hρcomm b x hxK).mpr (by rw [hb]; exact h2)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact h1
  have hJb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({(b : G)} : Set G)) J := by
    rw [hKCb]; exact hJc
  have hlayE : GLAPLayer 3 (K ⊓ Subgroup.centralizer ((Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) :
      Subgroup G) : Set G)) ≠ ⊥ := by
    intro h
    have hJle : J ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer ((Subgroup.zpowers (b : G) ⊔
        (B ⊓ centModSubgroup 3 K) : Subgroup G) : Set G)) := by
      rw [hKCE]
      exact le_sSup (show J ∈ {L | GLAPComponent 3 (K ⊓ Subgroup.centralizer ({(b : G)} : Set G)) L} from hJb)
    rw [h, le_bot_iff] at hJle
    exact hJ1 hJle
  have hordb : orderOf (b : G) = 3 := orderOf_eq_prime hb3 hbne
  have hEcard : Nat.card (Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) : Subgroup G) =
      3 * Nat.card (B ⊓ centModSubgroup 3 K : Subgroup G) := by
    have hnorm : (B ⊓ centModSubgroup 3 K) ≤ Subgroup.normalizer (Subgroup.zpowers (b : G) : Set G) := by
      intro c hc
      have hcB : c ∈ B := (Subgroup.mem_inf.mp hc).1
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hzB : Subgroup.zpowers (b : G) ≤ B := Subgroup.zpowers_le.mpr b.2
      have hhB : h ∈ B := hzB hh
      exact isElemAbelian_commute hB hhB hcB
    have hinf : Subgroup.zpowers (b : G) ⊓ (B ⊓ centModSubgroup 3 K) = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hg1, hg2⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg1
      have hBk : (b : G) ^ k ∈ B := (Subgroup.mem_inf.mp hg2).1
      have hk1 : ρ ⟨(b : G) ^ k, hBk⟩ = 1 :=
        (hρone _).mpr (fun x hx => (hcentX _ hg2 x hx).symm)
      have hbk_eq : (⟨(b : G) ^ k, hBk⟩ : B) = b ^ k := Subtype.ext (by simp)
      rw [hbk_eq, map_zpow, hb] at hk1
      have hdvd : ((orderOf y' : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hk1
      rw [hordy] at hdvd
      obtain ⟨m, hm⟩ : (3 : ℤ) ∣ k := by exact_mod_cast hdvd
      rw [Subgroup.mem_bot, hm, zpow_mul, zpow_ofNat, hb3, one_zpow]
    have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hordb] at hcard
    exact hcard
  have hmax : ∀ E' : Subgroup G, E' ≤ B → GLAPLayer 3 (K ⊓ Subgroup.centralizer (E' : Set G)) ≠ ⊥ →
      Nat.card E' ≤ Nat.card (Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) : Subgroup G) := by
    intro E' hE'B hlay
    obtain ⟨ρF, hρF⟩ : ∃ ρF : (E'.subgroupOf B) →* G, ∀ f, ρF f = ρ (f : B) :=
      ⟨ρ.comp (E'.subgroupOf B).subtype, fun f => rfl⟩
    have hρFrange : ρF.range ≤ ρ.range := by
      rintro _ ⟨f, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨(f : B), (hρF f).symm⟩
    have hρFK : ρF.range ≤ K := hρFrange.trans hDK
    have hρFEA : IsElemAbelian 3 ρF.range := isElemAbelian_mono hDEA hρFrange
    have hKCD : K ⊓ Subgroup.centralizer (E' : Set G) = K ⊓ Subgroup.centralizer (ρF.range : Set G) := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxK, hx⟩
        refine ⟨hxK, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hd
        rw [← hf, hρF]
        have hfE : ((f : B) : G) ∈ E' := Subgroup.mem_subgroupOf.mp f.2
        have h1 : ((f : B) : G) * x = x * ((f : B) : G) := Subgroup.mem_centralizer_iff.mp hx _ hfE
        exact (hρcomm (f : B) x hxK).mp h1
      · rintro ⟨hxK, hx⟩
        refine ⟨hxK, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have heB : e ∈ B := hE'B he
        have hfmem : (⟨e, heB⟩ : B) ∈ E'.subgroupOf B := Subgroup.mem_subgroupOf.mpr he
        have hρmem : ρ ⟨e, heB⟩ ∈ ρF.range :=
          MonoidHom.mem_range.mpr ⟨⟨⟨e, heB⟩, hfmem⟩, hρF _⟩
        have h1 : ρ ⟨e, heB⟩ * x = x * ρ ⟨e, heB⟩ := Subgroup.mem_centralizer_iff.mp hx _ hρmem
        exact (hρcomm ⟨e, heB⟩ x hxK).mpr h1
    have hlay' : GLAPLayer 3 (K ⊓ Subgroup.centralizer (ρF.range : Set G)) ≠ ⊥ := by
      rw [← hKCD]; exact hlay
    have hD'9 : Nat.card ρF.range < 9 := by
      by_contra hc
      push_neg at hc
      exact hlay' (hLayer G K ρF.range hKcat hEven hρFEA hc hρFK)
    have hD'card : Nat.card ρF.range ≤ 3 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (isPGroup_of_isElemAbelian hρFEA)
      rw [hk] at hD'9 ⊢
      rcases k with _ | _ | k
      · norm_num
      · norm_num
      · have h3 : 0 < 3 ^ k := by positivity
        have h9 : 3 ^ (k + 1 + 1) = 3 ^ k * 3 * 3 := by ring
        omega
    have hFE : Nat.card (E'.subgroupOf B) = Nat.card E' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'B).toEquiv
    have hkerF : Nat.card ρF.ker ≤ Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨((x.1 : B) : G), hkerCz (x.1 : B) ((hρF x.1).symm.trans (MonoidHom.mem_ker.mp x.2))⟩) ?_
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext hxy))
    have hmulF := Subgroup.card_ker_mul_card_range ρF
    calc Nat.card E' = Nat.card (E'.subgroupOf B) := hFE.symm
      _ = Nat.card ρF.ker * Nat.card ρF.range := hmulF.symm
      _ ≤ Nat.card ↥(B ⊓ centModSubgroup 3 K) * 3 := Nat.mul_le_mul hkerF hD'card
      _ = 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K) := mul_comm _ _
      _ = Nat.card (Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K) : Subgroup G) := hEcard.symm
  refine ⟨Subgroup.zpowers (b : G) ⊔ (B ⊓ centModSubgroup 3 K), (b : G), J, ?_, hbE, ?_, hJb, ?_, ?_⟩
  · unfold S10.IsE0
    exact ⟨hEB, hlayE, hmax⟩
  · intro hcm
    obtain ⟨_, hle⟩ := hcm
    rw [hO] at hle
    apply hy'1
    rw [← hb]
    apply (hρone b).mpr
    intro x hx
    have h1 : ⁅x, (b : G)⁆ ∈ ⁅K, Subgroup.zpowers (b : G)⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers _)
    have h2 := hle h1
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  · exact ⟨fun _ => ⟨hEven, hJcat⟩, fun hU => (hDisj _ n n hG2 hU).elim⟩
  · have hT₁K : T₁ ≤ K := fun x hx => (Subgroup.mem_inf.mp (hT₁C hx)).1
    have hT₁C' : T₁ ≤ K ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
      rw [hKCb]; exact hT₁C
    refine ⟨T₁, hT₁C', hT₁2, ?_, ?_, hT₁Q⟩
    · intro b' hb'
      exact mem_normalizer_of_conj hT₁K (hBN hb') (hT₁N (MonoidHom.mem_range.mpr ⟨⟨b', hb'⟩, rfl⟩))
        (fun x hx => hρconj ⟨b', hb'⟩ x hx)
    · intro hbot
      apply hT₁comm
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro t ht d hd
      obtain ⟨b', rfl⟩ := MonoidHom.mem_range.mp hd
      have hc : ⁅t, (b' : G)⁆ ∈ ⁅T₁, B⁆ := Subgroup.commutator_mem_commutator ht b'.2
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      have hc2 : ρ b' * t = t * ρ b' := (hρcomm b' t (hT₁K ht)).mp hc.symm
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc2.symm

end CFSG.LocalAnalysis.GLTheoremA.K266
