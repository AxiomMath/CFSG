module

public import CFSG.CGT.Foote82.T66.CaseIINorm

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem eq_one_of_isPGroup_of_odd {Γ : Type*} [Group Γ] {Y C : Subgroup Γ} [Finite C]
    (hY : IsPGroup 2 Y) (hC : Odd (Nat.card C)) {y : Γ} (hyY : y ∈ Y) (hyC : y ∈ C) : y = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hY) ⟨y, hyY⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf (⟨y, hyC⟩ : ↥C) ∣ Nat.card C := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hk] at h1
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  · exfalso
    have h2 : 2 ∣ Nat.card C := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1
    exact (Nat.not_even_iff_odd.2 hC) (even_iff_two_dvd.2 h2)

theorem le_normalizer_of_commute {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set Γ) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h x hx b hb, mul_inv_cancel_right]
    exact hx
  · intro hx
    have e : x = b * x * b⁻¹ := by
      have := h _ hx b hb
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [mul_assoc, ← this, ← mul_assoc]
        _ = b * x * b⁻¹ := by group
    rw [e]
    exact hx

theorem mem_normalizer_of_mem_centralizer {Γ : Type*} [Group Γ] {A : Subgroup Γ} {k : Γ}
    (hk : k ∈ Subgroup.centralizer (A : Set Γ)) : k ∈ Subgroup.normalizer (A : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← Subgroup.mem_centralizer_iff.1 hk x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := Subgroup.mem_centralizer_iff.1 hk _ hx
    have h2 : k * x = k * (k * x * k⁻¹) := by
      calc k * x = (k * x * k⁻¹) * k := by group
        _ = k * (k * x * k⁻¹) := h1
    rw [mul_left_cancel h2]
    exact hx

theorem le_two_pow_factorization {n m : ℕ} (hm : m ≠ 0) (h : 2 ^ n ∣ m) :
    2 ^ n ≤ 2 ^ m.factorization 2 :=
  Nat.pow_le_pow_right (by norm_num) ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).1 h)

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem H₁_le_normalizer : H₁ ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)) := by
  intro h hh
  refine ⟨c.H₁_le_G hh, Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => c.conj_mem_H hh hy,
    fun hy => ?_⟩⟩
  have := c.conj_mem_H (H₁.inv_mem hh) hy
  simpa [mul_assoc] using this

theorem card_dvd_of_le_normalizer (haut : CaseIIAut) (hG1 : CaseIIG1) {Y : Subgroup (GLV V)}
    (hY : IsPGroup 2 Y) (hYG : Y ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))) :
    Nat.card ↥Y ∣ Nat.card ↥H₁ := by
  set M := G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)) with hM
  set CH := G ⊓ Subgroup.centralizer (HH G L v : Set (GLV V)) with hCH
  have hCHM : CH ≤ M := fun k hk => ⟨hk.1, mem_normalizer_of_mem_centralizer hk.2⟩
  have hH₁M : H₁ ≤ M := d.H₁_le_normalizer
  have hodd : Odd (Nat.card ↥CH) := d.odd_card_CH hG1
  haveI hN : (CH.subgroupOf M).Normal := by
    refine ⟨fun k hk m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hm := m.2
    refine ⟨G.mul_mem (G.mul_mem hm.1 hk.1) (G.inv_mem hm.1), ?_⟩
    apply Subgroup.mem_centralizer_iff.2
    intro y hy
    have hy' : (m : GLV V)⁻¹ * y * m ∈ HH G L v := by
      have := (Subgroup.mem_normalizer_iff.1 hm.2 ((m : GLV V)⁻¹ * y * m)).1
      have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm.2) y).1 hy
      simpa [mul_assoc] using h2
    have hc := Subgroup.mem_centralizer_iff.1 hk.2 _ hy'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (↑m * ↑k * (↑m)⁻¹) = ↑m * ((↑m)⁻¹ * y * ↑m * ↑k) * (↑m)⁻¹ := by group
      _ = ↑m * (↑k * ((↑m)⁻¹ * y * ↑m)) * (↑m)⁻¹ := by rw [hc]
      _ = ↑m * ↑k * (↑m)⁻¹ * y := by group
  have htop : H₁.subgroupOf M ⊔ CH.subgroupOf M = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨h₁, hh₁, hconj⟩ := c.exists_H₁_of_normalizer haut m.2.2
    have hcm : h₁⁻¹ * (m : GLV V) ∈ CH := by
      refine ⟨G.mul_mem (G.inv_mem (c.H₁_le_G hh₁)) m.2.1, ?_⟩
      apply Subgroup.mem_centralizer_iff.2
      intro y hy
      have h1 := hconj y hy
      calc y * (h₁⁻¹ * ↑m) = h₁⁻¹ * (h₁ * y * h₁⁻¹) * ↑m := by group
        _ = h₁⁻¹ * (↑m * y * (↑m)⁻¹) * ↑m := by rw [h1]
        _ = h₁⁻¹ * ↑m * y := by group
    have e : m = ⟨h₁, hH₁M hh₁⟩ * ⟨h₁⁻¹ * m, hCHM hcm⟩ := Subtype.ext (by simp)
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.2 hh₁) (Subgroup.mem_subgroupOf.2 hcm)
  have hYM : Y ≤ M := hYG
  let f : ↥(Y.subgroupOf M) →* ↥M ⧸ CH.subgroupOf M :=
    (QuotientGroup.mk' (CH.subgroupOf M)).comp (Y.subgroupOf M).subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hy2 : ((y : ↥M) : GLV V) ∈ CH := by
      have := (QuotientGroup.eq_one_iff (y : ↥M)).1 hy
      exact Subgroup.mem_subgroupOf.1 this
    have := eq_one_of_isPGroup_of_odd hY hodd (Subgroup.mem_subgroupOf.1 y.2) hy2
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext this)
  have h1 := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at h1
  have h2 : Nat.card (↥M ⧸ CH.subgroupOf M) = (CH.subgroupOf M).relIndex (H₁.subgroupOf M) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex_top_right, ← htop,
      Subgroup.relIndex_sup_right]
  have h3 := Subgroup.relIndex_mul_card (H := CH.subgroupOf M) (K := H₁.subgroupOf M)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₁M).toEquiv] at h3
  rw [h2] at h1
  exact h1.trans (Dvd.intro _ h3)

theorem exists_T : ∃ T : Subgroup (GLV V), T ≤ H₁ ∧ IsPGroup 2 T ∧
    Nat.card ↥T = 2 ^ (Nat.card ↥H₁).factorization 2 ∧ z ∈ T ∧ g * z * g⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set zz : ↥H₁ := ⟨z, c.z_mem⟩
  set uu : ↥H₁ := ⟨g * z * g⁻¹, d.u_mem_H₁⟩
  have hzz : orderOf zz = 2 := by rw [Subgroup.orderOf_mk, c.orderOf_z]
  have huu : uu * uu = 1 := Subtype.ext d.u_mul_u
  have hp : ∀ x : ↥H₁, x * x = 1 → IsPGroup 2 (Subgroup.zpowers x) := by
    intro x hx
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h2 : x ^ 2 = 1 := by rw [sq, hx]
    have hd := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hzz2 : zz * zz = 1 := Subtype.ext c.z_mul_z
  have hcomm : uu * zz = zz * uu := Subtype.ext d.comm
  have hnorm : Subgroup.zpowers uu ≤ Subgroup.normalizer (Subgroup.zpowers zz : Set ↥H₁) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow (hcomm.symm : Commute zz uu) m n)).eq
  have hE := IsPGroup.to_sup_of_normal_left' (hp zz hzz2) (hp uu huu) hnorm
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  refine ⟨(S : Subgroup ↥H₁).map H₁.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · exact (S.isPGroup').map _
  · rw [Subgroup.card_map_of_injective H₁.subtype_injective, Sylow.card_eq_multiplicity]
  · exact ⟨zz, hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers zz)), rfl⟩
  · exact ⟨uu, hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers uu)), rfl⟩

end GD

theorem commSpace_conj (y a : GLV V) (ha : a * a = 1) :
    commSpace (Subgroup.zpowers (y * a * y⁻¹)) ⊤ =
      (commSpace (Subgroup.zpowers a) ⊤).map (y : V →ₗ[ZMod 2] V) := by
  have hya : (y * a * y⁻¹) * (y * a * y⁻¹) = 1 := by
    calc (y * a * y⁻¹) * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [ha, mul_one, mul_inv_cancel]
  rw [commSpace_zpowers_eq_map hya, commSpace_zpowers_eq_map ha, ← map_subOne_conj]
  congr 1
  rw [Submodule.map_top]
  exact (LinearMap.range_eq_top.2 y.surjective).symm

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem lemma57 (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1) {T : Subgroup (GLV V)}
    (hTH₁ : T ≤ H₁) (hTc : Nat.card ↥T = 2 ^ (Nat.card ↥H₁).factorization 2)
    (hzT : z ∈ T) (huT : g * z * g⁻¹ ∈ T)
    (hfus : ∀ a ∈ T, (∃ x ∈ G, a = x * z * x⁻¹) → ∃ h ∈ HH G L v, a = h * z * h⁻¹) :
    ∀ P : Subgroup (GLV V), P ≤ G → IsPGroup 2 P → T ≤ P → P = T := by
  intro P hPG hP2 hTP
  by_contra hne
  have hlt : T < P := lt_of_le_of_ne hTP (Ne.symm hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hT' : T.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm _ hTP
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ T.subgroupOf P := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨y', hy'N, hy'T⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hT')
  have hyP : (y' : GLV V) ∈ P := y'.2
  have hyG : (y' : GLV V) ∈ G := hPG hyP
  have hyT : (y' : GLV V) ∉ T := fun h => hy'T (Subgroup.mem_subgroupOf.2 h)
  have hconj : ∀ t ∈ T, (y' : GLV V) * t * (y' : GLV V)⁻¹ ∈ T ∧
      (y' : GLV V)⁻¹ * t * (y' : GLV V) ∈ T := by
    intro t ht
    have hN := Subgroup.mem_normalizer_iff.1 hy'N
    constructor
    · have := (hN ⟨t, hTP ht⟩).1 (Subgroup.mem_subgroupOf.2 ht)
      exact Subgroup.mem_subgroupOf.1 this
    · have := (hN (y'⁻¹ * ⟨t, hTP ht⟩ * y')).2 (by
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using ht)
      exact Subgroup.mem_subgroupOf.1 this
  set S : Set (GLV V) := {a | a ∈ T ∧ ∃ h ∈ HH G L v, a = h * z * h⁻¹} with hS
  have hzS : z ∈ S := ⟨hzT, 1, (HH G L v).one_mem, by simp⟩
  have huS : g * z * g⁻¹ ∈ S := ⟨huT, g, d.mem, rfl⟩
  have hU : UU z (g * z * g⁻¹) = ⨅ a ∈ S, commSpace (Subgroup.zpowers a) ⊤ := by
    apply le_antisymm
    · refine le_iInf₂ fun a ha => ?_
      obtain ⟨-, h, hh, rfl⟩ := ha
      exact d.U_le hs hh
    · exact le_inf (iInf₂_le z hzS) (iInf₂_le _ huS)
  have hSy : ∀ a ∈ S, (y' : GLV V) * a * (y' : GLV V)⁻¹ ∈ S ∧
      (y' : GLV V)⁻¹ * a * (y' : GLV V) ∈ S := by
    intro a ha
    obtain ⟨haT, h, hh, rfl⟩ := ha
    have hhG : h ∈ G := c.H_le_G hh
    constructor
    · refine ⟨(hconj _ haT).1, hfus _ (hconj _ haT).1 ⟨(y' : GLV V) * h,
        G.mul_mem hyG hhG, by group⟩⟩
    · refine ⟨(hconj _ haT).2, hfus _ (hconj _ haT).2 ⟨(y' : GLV V)⁻¹ * h,
        G.mul_mem (G.inv_mem hyG) hhG, by group⟩⟩
  have hinvol : ∀ a ∈ S, a * a = 1 := by
    rintro a ⟨-, h, -, rfl⟩
    calc (h * z * h⁻¹) * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
      _ = 1 := by rw [c.z_mul_z, mul_one, mul_inv_cancel]
  have hxU : ∀ w, w ∈ UU z (g * z * g⁻¹) ↔ (y' : GLV V) w ∈ UU z (g * z * g⁻¹) := by
    intro w
    rw [hU]
    simp only [Submodule.mem_iInf]
    constructor
    · intro hw a ha
      have hb := (hSy a ha).2
      have h1 := hw _ hb
      have e : a = (y' : GLV V) * ((y' : GLV V)⁻¹ * a * (y' : GLV V)) * (y' : GLV V)⁻¹ := by
        group
      rw [e, commSpace_conj _ _ (hinvol _ hb)]
      exact Submodule.mem_map_of_mem h1
    · intro hw a ha
      have hb := (hSy a ha).1
      have h1 := hw _ hb
      rw [commSpace_conj _ _ (hinvol _ ha)] at h1
      obtain ⟨w', hw', hww'⟩ := h1
      have : w' = w := (y' : GLV V).injective hww'
      rwa [← this]
  have hyN := d.mem_normalizer_H hs hyG hxU
  set Y := T ⊔ Subgroup.zpowers (y' : GLV V) with hY
  have hYP : Y ≤ P := sup_le hTP (Subgroup.zpowers_le.2 hyP)
  have hY2 : IsPGroup 2 ↥Y := hP2.to_le hYP
  have hYN : Y ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)) :=
    sup_le (hTH₁.trans d.H₁_le_normalizer) (Subgroup.zpowers_le.2 ⟨hyG, hyN⟩)
  have hdvd := d.card_dvd_of_le_normalizer haut hG1 hY2 hYN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hY2)
  rw [hk] at hdvd
  have hle := le_two_pow_factorization Nat.card_pos.ne' hdvd
  rw [← hTc, ← hk] at hle
  have hTY : T < Y := lt_of_le_of_ne le_sup_left fun h =>
    hyT (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  exact absurd hle (not_le.2 (Subgroup.card_lt_of_lt hTY))

end GD

end CaseII

end CFSG.CGT.Foote82
