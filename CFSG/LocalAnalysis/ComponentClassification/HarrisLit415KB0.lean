module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415JX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415KA

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem mem_sup_of_commute {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  obtain ⟨-, hset⟩ := GroupTheory.card_sup_mul_card_inf_of_commute A B hc
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_B₀_of {X : Type} [Group X] [Finite X] {β t z₁ z : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X)) (ht2 : t * t = 1)
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W) (hz₁W : z₁ ∈ W)
    (hz₁2 : z₁ ^ 2 = 1) (hz₁ne : z₁ ≠ t * z₁ * t⁻¹) (hzz : z = z₁ * (t * z₁ * t⁻¹))
    (hmk : ∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
      (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁)
    (hcomm : ∀ y ∈ W, ∀ hy : y ∈ centralizer ({β} : Set X), y * z₁ = z₁ * y ↔
      Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨y, hy⟩ : MBar β)).toMonoidHom = Kb₁)
    (hmul : ∀ y ∈ W, y * z₁ ≠ z₁ * y → y * t * z₁ = z₁ * (y * t))
    (hW₀z₂ : ∀ y ∈ W, y * z₁ = z₁ * y → y * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * y)
    {Ds : Subgroup X} (hDsW : Ds ≤ W)
    (hDsyl : IsSylowOf 2 (barOf (centralizer {β}) Ds)
      (layer (MBar β) ⊓ centralizer {(QuotientGroup.mk ⟨t, htM⟩ : MBar β)}))
    {m : ℕ} (hm : 2 ≤ m) (eDs : ↥Ds ≃* DihedralGroup (2 ^ m)) (hzDs : z ∈ Ds)
    (hzc : ∀ d ∈ Ds, z * d = d * z) :
    (∃ a ∈ barOf (centralizer {β}) W ⊓ Kb₁, ∃ b ∈ barOf (centralizer {β}) W ⊓ Kb₁,
      a * b ≠ b * a) ∧
    (∀ c ∈ barOf (centralizer {β}) W ⊓ Kb₁,
      (∀ d ∈ barOf (centralizer {β}) W ⊓ Kb₁, c * d = d * c) →
        c = 1 ∨ c = QuotientGroup.mk ⟨z₁, hW.le hz₁W⟩) ∧
    ∃ B₀ : Subgroup X, B₀ ≤ W ∧ (∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) ∧
      (∀ y ∈ W, ∀ x ∈ B₀, y * x * y⁻¹ ∈ B₀) ∧
      zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ≤ B₀ ∧
      (∀ x ∈ B₀, x ^ 2 = 1 ↔ x ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹)) ∧
      (∀ x ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹), ∃ y ∈ B₀, y ^ 2 = x) ∧
      Nat.card ↥(zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹)) = 4 ∧
      ∀ x ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹), x = 1 ∨ x = z₁ ∨ x = t * z₁ * t⁻¹ ∨ x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  have hWM : W ≤ M := hW.le
  have hWp := hW.isPGroup
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  set s : MBar β := QuotientGroup.mk ⟨t, htM⟩ with hsdef
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 : s * s = 1 := by
    rw [hsdef, ← QuotientGroup.mk_mul]
    have : (⟨t, htM⟩ : ↥M) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
    rw [this, QuotientGroup.mk_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  set P := barOf M W with hPdef
  have hP : IsSylowOf 2 P ⊤ := isSylowOf_barOf hW
  have hsP : s ∈ P := mk_mem_barOf htM htW
  have hDsM : Ds ≤ M := hDsW.trans hWM
  have hDsp : IsPGroup 2 Ds := hWp.to_le hDsW
  set D := barOf M Ds with hDdef
  have hDP : D ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hDsW hy, rfl⟩
  set eD : ↥D ≃* DihedralGroup (2 ^ m) := (barEquiv hDsM hDsp).symm.trans eDs with heD
  have hz₁M : z₁ ∈ M := hWM hz₁W
  set zb₁ : MBar β := QuotientGroup.mk ⟨z₁, hz₁M⟩ with hzb₁
  have hzb₁P : zb₁ ∈ P ⊓ Kb₁ := mem_inf.mpr ⟨mk_mem_barOf hz₁M hz₁W, hmk hz₁M⟩
  have hzM : z ∈ M := hDsM hzDs
  have hzb : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) = zb₁ * (s⁻¹ * zb₁ * s) := by
    rw [hsi]
    have : (⟨z, hzM⟩ : ↥M) = ⟨z₁, hz₁M⟩ * (⟨t, htM⟩ * ⟨z₁, hz₁M⟩ * ⟨t, htM⟩) :=
      Subtype.ext (by show z = z₁ * (t * z₁ * t); rw [hzz, hti])
    rw [this]
    simp only [QuotientGroup.mk_mul]
    rfl
  have hzbD : ∀ d ∈ D, zb₁ * (s⁻¹ * zb₁ * s) * d = d * (zb₁ * (s⁻¹ * zb₁ * s)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hzb]
    show (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk ⟨z, hzM⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hzc y hy)
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem htW hz₁W) (inv_mem htW)
  have hz₂2' : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ ^ 2) * t⁻¹ by rw [sq]; group, hz₁2]
    group
  have hz₁2' : z₁ * z₁ = 1 := by rw [← sq]; exact hz₁2
  have hz₁1 : z₁ ≠ 1 := fun h1 => hz₁ne (by rw [h1]; group)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hzz] at h1
    apply hz₁ne
    calc z₁ = (t * z₁ * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = t * z₁ * t⁻¹ := inv_eq_of_mul_eq_one_right hz₂2'
  have hzb1 : zb₁ * (s⁻¹ * zb₁ * s) ≠ 1 := by
    rw [← hzb]
    intro h1
    exact hz1 (mk_injOn hWM hWp (hDsW hzDs) (one_mem W) (by rw [h1]; rfl))
  obtain ⟨hnab, hcen, v, hv, hvo, hv2, hv4⟩ :=
    hprod.dihedral_facts hE hP hs2 hsP hDsyl hDP hm eD hzb₁P hzbD hzb1
  obtain ⟨v₁', hv₁W', hv₁eq⟩ := mem_barOf.mp (mem_inf.mp hv).1
  set v₁ : X := (v₁' : X) with hv₁def
  have hv₁W : v₁ ∈ W := hv₁W'
  have hv₁b : (QuotientGroup.mk ⟨v₁, hWM hv₁W⟩ : MBar β) = v := hv₁eq
  obtain ⟨v₂, hv₂def⟩ : ∃ v₂ : X, v₂ = t * v₁ * t⁻¹ := ⟨_, rfl⟩
  have hv₂W : v₂ ∈ W := by rw [hv₂def]; exact mul_mem (mul_mem htW hv₁W) (inv_mem htW)
  have hv₂b : (QuotientGroup.mk ⟨v₂, hWM hv₂W⟩ : MBar β) = s⁻¹ * v * s := by
    rw [hsi, ← hv₁b]
    have : (⟨v₂, hWM hv₂W⟩ : ↥M) = ⟨t, htM⟩ * ⟨v₁, hWM hv₁W⟩ * ⟨t, htM⟩ :=
      Subtype.ext (by show v₂ = t * v₁ * t; rw [hv₂def, hti])
    rw [this]
    simp only [QuotientGroup.mk_mul]
    rfl
  have hvK : v ∈ Kb₁ := (mem_inf.mp hv).2
  have hv₂K : s⁻¹ * v * s ∈ Kb₂ := hprod.conj_mem_K₂ hvK
  have hpow₁ : ∀ a : ℤ, (QuotientGroup.mk ⟨v₁ ^ a, hWM (zpow_mem hv₁W a)⟩ : MBar β) = v ^ a := by
    intro a
    rw [← hv₁b, ← QuotientGroup.mk_zpow]
    rfl
  have hpow₂ : ∀ b : ℤ, (QuotientGroup.mk ⟨v₂ ^ b, hWM (zpow_mem hv₂W b)⟩ : MBar β) =
      (s⁻¹ * v * s) ^ b := by
    intro b
    rw [← hv₂b, ← QuotientGroup.mk_zpow]
    rfl
  have hcomm₁₂ : ∀ a b : ℤ, v₁ ^ a * v₂ ^ b = v₂ ^ b * v₁ ^ a := by
    intro a b
    refine mk_injOn hWM hWp (mul_mem (zpow_mem hv₁W a) (zpow_mem hv₂W b))
      (mul_mem (zpow_mem hv₂W b) (zpow_mem hv₁W a)) ?_
    have h1 : (⟨v₁ ^ a * v₂ ^ b, hWM (mul_mem (zpow_mem hv₁W a) (zpow_mem hv₂W b))⟩ : ↥M) =
        ⟨v₁ ^ a, hWM (zpow_mem hv₁W a)⟩ * ⟨v₂ ^ b, hWM (zpow_mem hv₂W b)⟩ := rfl
    have h2 : (⟨v₂ ^ b * v₁ ^ a, hWM (mul_mem (zpow_mem hv₂W b) (zpow_mem hv₁W a))⟩ : ↥M) =
        ⟨v₂ ^ b, hWM (zpow_mem hv₂W b)⟩ * ⟨v₁ ^ a, hWM (zpow_mem hv₁W a)⟩ := rfl
    rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hpow₁, hpow₂]
    exact hprod.comm (zpow_mem hvK a) (zpow_mem hv₂K b)
  have hcap' : ∀ a b : ℤ, v₁ ^ a * v₂ ^ b = 1 → v₁ ^ a = 1 ∧ v₂ ^ b = 1 := by
    intro a b hab
    have h1 : v ^ a * (s⁻¹ * v * s) ^ b = 1 := by
      rw [← hpow₁, ← hpow₂, ← QuotientGroup.mk_mul]
      have : (⟨v₁ ^ a, hWM (zpow_mem hv₁W a)⟩ : ↥M) * ⟨v₂ ^ b, hWM (zpow_mem hv₂W b)⟩ = 1 :=
        Subtype.ext hab
      rw [this, QuotientGroup.mk_one]
    have h2 : v ^ a = ((s⁻¹ * v * s) ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : v ^ a ∈ Kb₁ ⊓ Kb₂ := mem_inf.mpr ⟨zpow_mem hvK a, h2 ▸ inv_mem (zpow_mem hv₂K b)⟩
    rw [hprod.inf_eq, mem_bot] at h3
    have h4 : v₁ ^ a = 1 := mk_injOn hWM hWp (zpow_mem hv₁W a) (one_mem W) (by
      rw [hpow₁, h3]; rfl)
    refine ⟨h4, ?_⟩
    rw [h4, one_mul] at hab
    exact hab
  have hcap : ∀ x₁ ∈ zpowers v₁, ∀ x₂ ∈ zpowers v₂, x₁ * x₂ = 1 → x₁ = 1 ∧ x₂ = 1 := by
    intro x₁ hx₁ x₂ hx₂ h12
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hx₁
    obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hx₂
    exact hcap' a b h12
  have hv₁o : orderOf v₁ = 4 := by
    have h1 := orderOf_injective (barHom hWM) (barHom_injective hWM hWp) ⟨v₁, hv₁W⟩
    rw [Subgroup.orderOf_mk] at h1
    rw [← h1]
    show orderOf (QuotientGroup.mk ⟨v₁, hWM hv₁W⟩ : MBar β) = 4
    rw [hv₁b, hvo]
  have hv₁2 : v₁ ^ 2 = z₁ := by
    refine mk_injOn hWM hWp (pow_mem hv₁W 2) hz₁W ?_
    have h1 : (⟨v₁ ^ 2, hWM (pow_mem hv₁W 2)⟩ : ↥M) = ⟨v₁, hWM hv₁W⟩ ^ 2 := rfl
    rw [h1, QuotientGroup.mk_pow, hv₁b, hv2]
  have hv₂2 : v₂ ^ 2 = t * z₁ * t⁻¹ := by rw [hv₂def, conj_pow, hv₁2]
  have hc₀ : ∀ a ∈ zpowers v₁, ∀ b ∈ zpowers v₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact hcomm₁₂ i j
  set B₀ := zpowers v₁ ⊔ zpowers v₂ with hB₀
  have hmemB₀ : ∀ x ∈ B₀, ∃ a b : ℤ, x = v₁ ^ a * v₂ ^ b := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc₀ hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact ⟨i, j, rfl⟩
  have hB₀W : B₀ ≤ W := sup_le (zpowers_le.mpr hv₁W) (zpowers_le.mpr hv₂W)
  have hB₀c : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, b, rfl⟩ := hmemB₀ x hx
    obtain ⟨c, d, rfl⟩ := hmemB₀ y hy
    calc v₁ ^ a * v₂ ^ b * (v₁ ^ c * v₂ ^ d) = v₁ ^ a * (v₂ ^ b * v₁ ^ c) * v₂ ^ d := by group
      _ = v₁ ^ a * (v₁ ^ c * v₂ ^ b) * v₂ ^ d := by rw [hcomm₁₂]
      _ = v₁ ^ c * v₁ ^ a * (v₂ ^ b * v₂ ^ d) := by group
      _ = v₁ ^ c * v₁ ^ a * (v₂ ^ d * v₂ ^ b) := by group
      _ = v₁ ^ c * (v₁ ^ a * v₂ ^ d) * v₂ ^ b := by group
      _ = v₁ ^ c * (v₂ ^ d * v₁ ^ a) * v₂ ^ b := by rw [hcomm₁₂]
      _ = v₁ ^ c * v₂ ^ d * (v₁ ^ a * v₂ ^ b) := by group
  have hW₀v₁ : ∀ y ∈ W, y * z₁ = z₁ * y → y * v₁ * y⁻¹ ∈ zpowers v₁ := by
    intro y hyW hyz
    have hyM := hWM hyW
    have hyK := (hcomm y hyW hyM).mp hyz
    set yb : MBar β := QuotientGroup.mk ⟨y, hyM⟩ with hyb
    have h1 : yb * v * yb⁻¹ ∈ P ⊓ Kb₁ := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem (mk_mem_barOf hyM hyW) (mem_inf.mp hv).1)
        (inv_mem (mk_mem_barOf hyM hyW)), ?_⟩
      rw [← hyK]
      exact ⟨v, hvK, rfl⟩
    have h2 : orderOf (yb * v * yb⁻¹) = 4 := by
      have := MulEquiv.orderOf_eq (MulAut.conj yb) v
      simp only [MulAut.conj_apply] at this
      rw [this, hvo]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hv4 _ h1 h2)
    rw [mem_zpowers_iff]
    refine ⟨k, mk_injOn hWM hWp (zpow_mem hv₁W k)
      (mul_mem (mul_mem hyW hv₁W) (inv_mem hyW)) ?_⟩
    rw [show (⟨v₁ ^ k, hWM (zpow_mem hv₁W k)⟩ : ↥M) = ⟨v₁ ^ k, hWM (zpow_mem hv₁W k)⟩ from rfl,
      hpow₁, hk]
    have : (⟨y * v₁ * y⁻¹, hWM (mul_mem (mul_mem hyW hv₁W) (inv_mem hyW))⟩ : ↥M) =
        ⟨y, hyM⟩ * ⟨v₁, hWM hv₁W⟩ * (⟨y, hyM⟩)⁻¹ := rfl
    rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hv₁b]
  have hW₀v₂ : ∀ y ∈ W, y * z₁ = z₁ * y → y * v₂ * y⁻¹ ∈ zpowers v₂ := by
    intro y hyW hyz
    have hy' : t⁻¹ * y * t ∈ W := mul_mem (mul_mem (inv_mem htW) hyW) htW
    have hy'z : t⁻¹ * y * t * z₁ = z₁ * (t⁻¹ * y * t) := by
      have h1 := hW₀z₂ y hyW hyz
      calc t⁻¹ * y * t * z₁ = t⁻¹ * (y * (t * z₁ * t⁻¹)) * t := by group
        _ = t⁻¹ * ((t * z₁ * t⁻¹) * y) * t := by rw [h1]
        _ = z₁ * (t⁻¹ * y * t) := by group
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hW₀v₁ _ hy' hy'z)
    rw [mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [hv₂def, conj_zpow, hk]
    group
  have hB₀n : ∀ y ∈ W, ∀ x ∈ B₀, y * x * y⁻¹ ∈ B₀ := by
    have hgen : ∀ y ∈ W, y * v₁ * y⁻¹ ∈ B₀ ∧ y * v₂ * y⁻¹ ∈ B₀ := by
      intro y hyW
      by_cases hyz : y * z₁ = z₁ * y
      · exact ⟨mem_sup_left (hW₀v₁ y hyW hyz), mem_sup_right (hW₀v₂ y hyW hyz)⟩
      · have hyt := hmul y hyW hyz
        have hytW : y * t ∈ W := mul_mem hyW htW
        have h1 : y * v₁ * y⁻¹ = (y * t) * v₂ * (y * t)⁻¹ := by
          rw [hv₂def, mul_inv_rev, hti]
          calc y * v₁ * y⁻¹ = y * (t * t) * v₁ * (t * t) * y⁻¹ := by rw [ht2]; group
            _ = y * t * (t * v₁ * t) * (t * y⁻¹) := by group
        have h2 : y * v₂ * y⁻¹ = (y * t) * v₁ * (y * t)⁻¹ := by
          rw [hv₂def, mul_inv_rev, hti]
          group
        exact ⟨h1 ▸ mem_sup_right (hW₀v₂ _ hytW hyt), h2 ▸ mem_sup_left (hW₀v₁ _ hytW hyt)⟩
    intro y hyW x hx
    obtain ⟨a, b, rfl⟩ := hmemB₀ x hx
    have h1 : y * (v₁ ^ a * v₂ ^ b) * y⁻¹ = (y * v₁ * y⁻¹) ^ a * (y * v₂ * y⁻¹) ^ b := by
      rw [conj_zpow (a := y) (b := v₁), conj_zpow (a := y) (b := v₂)]
      group
    rw [h1]
    exact mul_mem (zpow_mem (hgen y hyW).1 a) (zpow_mem (hgen y hyW).2 b)
  have hsq : ∀ (u : X) (hu : u ∈ zpowers v₁), u ^ 2 = 1 → u = 1 ∨ u = z₁ := by
    intro u hu hu2
    rcases eq_of_mem_zpowers_sq (m := 2) (by norm_num) hv₁o hu hu2 with h1 | h1
    · exact Or.inl h1
    · right
      rw [h1, ← hv₁2]
      norm_num
  have hsq₂ : ∀ (u : X) (hu : u ∈ zpowers v₂), u ^ 2 = 1 → u = 1 ∨ u = t * z₁ * t⁻¹ := by
    intro u hu hu2
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have h1 : v₂ ^ k = t * v₁ ^ k * t⁻¹ := by rw [hv₂def, conj_zpow]
    have h2 : (v₁ ^ k) ^ 2 = 1 := by
      calc (v₁ ^ k) ^ 2 = t⁻¹ * (t * v₁ ^ k * t⁻¹) ^ 2 * t := by rw [sq, sq]; group
        _ = 1 := by rw [← h1, hu2]; group
    rcases hsq _ (zpow_mem (mem_zpowers v₁) k) h2 with h3 | h3
    · left
      rw [h1, h3]
      group
    · right
      rw [h1, h3]
  set Z := zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) with hZdef
  have hcZ : ∀ a ∈ zpowers z₁, ∀ b ∈ zpowers (t * z₁ * t⁻¹), a * b = b * a := by
    intro a ha b hb
    have hz₁₂ : z₁ * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * z₁ := by
      have := hcomm₁₂ 2 2
      simp only [zpow_ofNat] at this
      rw [← hv₂2, ← hv₁2]
      exact this
    rcases mem_zpowers_two hz₁2' ha with rfl | rfl <;>
      rcases mem_zpowers_two hz₂2' hb with rfl | rfl <;> simp [hz₁₂]
  have hmemZ : ∀ x ∈ Z, x = 1 ∨ x = z₁ ∨ x = t * z₁ * t⁻¹ ∨ x = z := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcZ hx
    rcases mem_zpowers_two hz₁2' ha with rfl | rfl <;>
      rcases mem_zpowers_two hz₂2' hb with rfl | rfl <;> simp [hzz]
  have hZB₀ : Z ≤ B₀ := sup_le
    (zpowers_le.mpr (hv₁2 ▸ pow_mem (mem_sup_left (mem_zpowers v₁)) 2))
    (zpowers_le.mpr (hv₂2 ▸ pow_mem (mem_sup_right (mem_zpowers v₂)) 2))
  have hZ4 : Nat.card Z = 4 := by
    obtain ⟨hB₁c, hB₁2⟩ := elem_zpowers hz₁2'
    have hz₂B₁ : t * z₁ * t⁻¹ ∉ zpowers z₁ := fun h1 => by
      rcases mem_zpowers_two hz₁2' h1 with h2 | h2
      · have h3 : z₁ = 1 := by
          calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
            _ = 1 := by rw [h2]; group
        exact hz₁1 h3
      · exact hz₁ne h2.symm
    obtain ⟨-, -, hcard⟩ := elem_sup hB₁c hB₁2 hz₂2' hz₂B₁ (fun a ha =>
      hcZ a ha _ (mem_zpowers _))
    rw [hcard, card_zpowers_two hz₁2' hz₁1]
  have hZ2 : ∀ x ∈ Z, x ^ 2 = 1 := by
    intro x hx
    rcases hmemZ x hx with h | h | h | h <;> rw [h]
    · simp
    · exact hz₁2
    · rw [sq]; exact hz₂2'
    · rw [sq]
      have := hcZ z₁ (mem_zpowers _) _ (mem_zpowers _)
      rw [hzz]
      calc z₁ * (t * z₁ * t⁻¹) * (z₁ * (t * z₁ * t⁻¹)) =
          z₁ * ((t * z₁ * t⁻¹) * z₁) * (t * z₁ * t⁻¹) := by group
        _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) * (t * z₁ * t⁻¹) := by rw [this]
        _ = (z₁ * z₁) * ((t * z₁ * t⁻¹) * (t * z₁ * t⁻¹)) := by group
        _ = 1 := by rw [hz₁2', hz₂2', one_mul]
  have hB₀2 : ∀ x ∈ B₀, x ^ 2 = 1 ↔ x ∈ Z := by
    intro x hx
    refine ⟨fun hx2 => ?_, fun hxZ => hZ2 x hxZ⟩
    obtain ⟨a, b, rfl⟩ := hmemB₀ x hx
    have h1 : (v₁ ^ a) ^ 2 * (v₂ ^ b) ^ 2 = 1 := by
      rw [← hx2, sq, sq, sq]
      calc v₁ ^ a * v₁ ^ a * (v₂ ^ b * v₂ ^ b) = v₁ ^ a * (v₁ ^ a * v₂ ^ b) * v₂ ^ b := by group
        _ = v₁ ^ a * (v₂ ^ b * v₁ ^ a) * v₂ ^ b := by rw [hcomm₁₂]
        _ = v₁ ^ a * v₂ ^ b * (v₁ ^ a * v₂ ^ b) := by group
    obtain ⟨h3, h4⟩ := hcap _ (pow_mem (zpow_mem (mem_zpowers v₁) a) 2) _
      (pow_mem (zpow_mem (mem_zpowers v₂) b) 2) h1
    have h5 := hsq _ (zpow_mem (mem_zpowers v₁) a) h3
    have h6 := hsq₂ _ (zpow_mem (mem_zpowers v₂) b) h4
    exact mul_mem (h5.elim (fun h => h ▸ one_mem _) (fun h => h ▸ mem_sup_left (mem_zpowers _)))
      (h6.elim (fun h => h ▸ one_mem _) (fun h => h ▸ mem_sup_right (mem_zpowers _)))
  have hZsq : ∀ x ∈ Z, ∃ y ∈ B₀, y ^ 2 = x := by
    intro x hx
    rcases hmemZ x hx with h | h | h | h <;> rw [h]
    · exact ⟨1, one_mem _, one_pow 2⟩
    · exact ⟨v₁, mem_sup_left (mem_zpowers _), hv₁2⟩
    · exact ⟨v₂, mem_sup_right (mem_zpowers _), hv₂2⟩
    · refine ⟨v₁ * v₂, mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)), ?_⟩
      have h1 := hcomm₁₂ 1 1
      simp only [zpow_one] at h1
      calc (v₁ * v₂) ^ 2 = v₁ * (v₂ * v₁) * v₂ := by rw [sq]; group
        _ = v₁ * (v₁ * v₂) * v₂ := by rw [h1]
        _ = v₁ ^ 2 * v₂ ^ 2 := by rw [sq, sq]; group
        _ = z := by rw [hv₁2, hv₂2, hzz]
  exact ⟨hnab, hcen, B₀, hB₀W, hB₀c, hB₀n, hZB₀, hB₀2, hZsq, hZ4, hmemZ⟩

end L415

end CFSG.ComponentClassification.HarrisLit
