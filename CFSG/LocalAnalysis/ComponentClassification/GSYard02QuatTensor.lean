module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigFourConn
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

structure QuatData (Q : Type) [Group Q] (z : Q) : Prop where
  sq : z * z = 1
  ne_one : z ≠ 1
  unique : ∀ a : Q, a * a = 1 → a = 1 ∨ a = z
  exists_sq : ∃ a : Q, a * a = z
  common : ∀ a b : Q, a * a = z → b * b = z →
    ∃ c : Q, c * c = z ∧ c * a = z * (a * c) ∧ c * b = z * (b * c)

section Quaternion

open QuaternionGroup

private theorem two_mul_natCast (m : ℕ) : (2 : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
  have h : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact h

private theorem quat_common_aa {m : ℕ} (half : ZMod (2 * m))
    (h2m : 2 * (m : ZMod (2 * m)) = 0)
    (i j : ZMod (2 * m)) (hi : i + i = (m : ZMod (2 * m))) (hj : j + j = (m : ZMod (2 * m))) :
    ∃ c : QuaternionGroup m, c * c = a (m : ZMod (2 * m)) ∧
      c * a i = a (m : ZMod (2 * m)) * (a i * c) ∧
      c * a j = a (m : ZMod (2 * m)) * (a j * c) := by
  refine ⟨xa 0, ?_, ?_, ?_⟩
  · simp [xa_mul_xa]
  · simp only [xa_mul_a, a_mul_xa, xa.injEq]
    linear_combination hi + h2m
  · simp only [xa_mul_a, a_mul_xa, xa.injEq]
    linear_combination hj + h2m

private theorem quat_common_ax {m : ℕ} (half : ZMod (2 * m))
    (hm : (m : ZMod (2 * m)) = 2 * half) (h2m : 2 * (m : ZMod (2 * m)) = 0)
    (i j : ZMod (2 * m)) (hi : i + i = (m : ZMod (2 * m))) :
    ∃ c : QuaternionGroup m, c * c = a (m : ZMod (2 * m)) ∧
      c * a i = a (m : ZMod (2 * m)) * (a i * c) ∧
      c * xa j = a (m : ZMod (2 * m)) * (xa j * c) := by
  refine ⟨xa (j + half), ?_, ?_, ?_⟩
  · simp [xa_mul_xa]
  · simp only [xa_mul_a, a_mul_xa, xa.injEq]
    linear_combination hi + h2m
  · simp only [xa_mul_xa, a_mul_a, a.injEq]
    linear_combination hm - h2m

private theorem quat_common_xx {m : ℕ} (half : ZMod (2 * m))
    (hm : (m : ZMod (2 * m)) = 2 * half) (i j : ZMod (2 * m)) :
    ∃ c : QuaternionGroup m, c * c = a (m : ZMod (2 * m)) ∧
      c * xa i = a (m : ZMod (2 * m)) * (xa i * c) ∧
      c * xa j = a (m : ZMod (2 * m)) * (xa j * c) := by
  refine ⟨a half, ?_, ?_, ?_⟩
  · simp only [a_mul_a, a.injEq]
    linear_combination -hm
  · simp only [a_mul_xa, xa_mul_a, xa.injEq]
    linear_combination hm
  · simp only [a_mul_xa, xa_mul_a, xa.injEq]
    linear_combination hm

private theorem quat_common {m : ℕ} (half : ZMod (2 * m))
    (hm : (m : ZMod (2 * m)) = 2 * half) (h2m : 2 * (m : ZMod (2 * m)) = 0)
    (g g' : QuaternionGroup m) (hg : g * g = a (m : ZMod (2 * m)))
    (hg' : g' * g' = a (m : ZMod (2 * m))) :
    ∃ c : QuaternionGroup m, c * c = a (m : ZMod (2 * m)) ∧
      c * g = a (m : ZMod (2 * m)) * (g * c) ∧ c * g' = a (m : ZMod (2 * m)) * (g' * c) := by
  cases g with
  | a i =>
    cases g' with
    | a j =>
      simp only [a_mul_a, a.injEq] at hg hg'
      exact quat_common_aa half h2m i j hg hg'
    | xa j =>
      simp only [a_mul_a, a.injEq] at hg
      exact quat_common_ax half hm h2m i j hg
  | xa i =>
    cases g' with
    | a j =>
      simp only [a_mul_a, a.injEq] at hg'
      obtain ⟨c, h1, h2, h3⟩ := quat_common_ax half hm h2m j i hg'
      exact ⟨c, h1, h3, h2⟩
    | xa j => exact quat_common_xx half hm i j

private theorem quat_unique {m : ℕ} (hm0 : 0 < m) (g : QuaternionGroup m) (hg : g * g = 1) :
    g = 1 ∨ g = a (m : ZMod (2 * m)) := by
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (2 * m) := ⟨by omega⟩
  cases g with
  | a i =>
    simp only [a_mul_a, one_def, a.injEq] at hg
    have hk : ((2 * i.val : ℕ) : ZMod (2 * m)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination hg
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hk
    have hdvd' : m ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
    have hlt := ZMod.val_lt i
    obtain ⟨c, hc⟩ := hdvd'
    have hc2 : c < 2 := by
      by_contra hcon
      push Not at hcon
      have : m * 2 ≤ m * c := Nat.mul_le_mul_left m hcon
      omega
    interval_cases c
    · left
      rw [one_def]
      congr 1
      rw [← ZMod.natCast_zmod_val i, hc]
      simp
    · right
      congr 1
      rw [← ZMod.natCast_zmod_val i, hc]
      simp
  | xa i =>
    exfalso
    simp only [xa_mul_xa, one_def, a.injEq] at hg
    have h0 : (m : ZMod (2 * m)) = 0 := by linear_combination hg
    have := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have := Nat.le_of_dvd hm0 this
    omega

theorem quatData_quaternion {m : ℕ} (hm : ∃ h, m = 2 * h) (hm0 : 0 < m) :
    QuatData (QuaternionGroup m) (a (m : ZMod (2 * m))) := by
  have h2m := two_mul_natCast m
  obtain ⟨h, hh⟩ := hm
  have hhalf : (m : ZMod (2 * m)) = 2 * ((h : ℕ) : ZMod (2 * m)) := by
    have : (m : ZMod (2 * m)) = ((2 * h : ℕ) : ZMod (2 * m)) := by rw [← hh]
    rw [this]
    push_cast
    ring
  refine ⟨?_, ?_, quat_unique hm0, ?_, fun g g' hg hg' => quat_common _ hhalf h2m g g' hg hg'⟩
  · rw [a_mul_a, one_def]
    congr 1
    linear_combination h2m
  · rw [one_def]
    intro h0
    simp only [a.injEq] at h0
    have := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have := Nat.le_of_dvd hm0 this
    omega
  · exact ⟨xa 0, by simp [xa_mul_xa]⟩

end Quaternion

theorem QuatData.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {z : Q}
    (hQ : QuatData Q z) : QuatData Q' (e z) where
  sq := by rw [← map_mul, hQ.sq, map_one]
  ne_one := fun h => hQ.ne_one (e.injective (by rw [h, map_one]))
  unique := fun a ha => by
    obtain ⟨b, rfl⟩ := e.surjective a
    rw [← map_mul, ← map_one e] at ha
    rcases hQ.unique b (e.injective ha) with h | h
    · left; rw [h, map_one]
    · right; rw [h]
  exists_sq := by
    obtain ⟨a, ha⟩ := hQ.exists_sq
    exact ⟨e a, by rw [← map_mul, ha]⟩
  common := fun a b ha hb => by
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [← map_mul] at ha hb
    obtain ⟨c, hc1, hc2, hc3⟩ := hQ.common a b (e.injective ha) (e.injective hb)
    refine ⟨e c, by rw [← map_mul, hc1], ?_, ?_⟩
    · rw [← map_mul, hc2, map_mul, map_mul]
    · rw [← map_mul, hc3, map_mul, map_mul]

theorem QuatData.of_equiv_quaternion {Q : Type} [Group Q] {m : ℕ} (hm : ∃ h, m = 2 * h)
    (hm0 : 0 < m) (e : Q ≃* QuaternionGroup m) {z : Q} (hz : z * z = 1) (hz1 : z ≠ 1) :
    QuatData Q z := by
  have h0 := quatData_quaternion hm hm0
  have hez : e z = QuaternionGroup.a (m : ZMod (2 * m)) := by
    rcases h0.unique (e z) (by rw [← map_mul, hz, map_one]) with h1 | h1
    · exact absurd (e.injective (h1.trans (map_one e).symm)) hz1
    · exact h1
  have := QuatData.of_mulEquiv e.symm h0
  rwa [← hez, MulEquiv.symm_apply_apply] at this

section Graph

variable {K : Type} [Group K]

@[expose] def vz (z x : K) : Subgroup K := zpowers x ⊔ zpowers z

structure Inv2 (z x : K) : Prop where
  sq : x * x = 1
  ne_one : x ≠ 1
  ne_z : x ≠ z
  comm : x * z = z * x

private theorem zpowers_le_centralizer_zpowers' {x y : K} (hxy : x * y = y * x) :
    zpowers x ≤ centralizer (zpowers y : Set K) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact ((Commute.zpow_left (Commute.symm hxy) k)).eq

private theorem exists_mem_ne_ne [Finite K] {H : Subgroup K} (h : 2 < Nat.card H)
    (x y : K) : ∃ z ∈ H, z ≠ x ∧ z ≠ y := by
  by_contra hc
  have hsub : (H : Set K) ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · exact Or.inl hzx
    · by_cases hzy : z = y
      · exact Or.inr hzy
      · exact (hc ⟨z, hz, hzx, hzy⟩).elim
  have hle : Nat.card H ≤ 2 := by
    have e : Nat.card H = (H : Set K).ncard := Nat.card_coe_set_eq (H : Set K)
    rw [e]
    calc (H : Set K).ncard ≤ ({x, y} : Set K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({y} : Set K).ncard + 1 := Set.ncard_insert_le x {y}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem isKleinFour_vz [Finite K] {z x : K} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hx : Inv2 z x) :
    IsKleinFour (vz z x) :=
  FooteLit.isKleinFour_sup_zpowers (by rw [sq]; exact hx.sq) (by rw [sq]; exact hz2) hx.ne_one hz1
    (Ne.symm hx.ne_z) hx.comm

theorem commFourAdj_vz [Finite K] {z x y : K} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hx : Inv2 z x) (hy : Inv2 z y) (hxy : x * y = y * x) :
    Sig.CommFourAdj K (vz z x) (vz z y) := by
  refine ⟨isKleinFour_vz hz2 hz1 hx, isKleinFour_vz hz2 hz1 hy, ?_⟩
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    exact sup_le (zpowers_le_centralizer_zpowers' hxy.symm)
      (zpowers_le_centralizer_zpowers' hx.comm.symm)
  · rw [le_centralizer_iff]
    exact sup_le (zpowers_le_centralizer_zpowers' hy.comm) (zpowers_le_centralizer_zpowers' rfl)

theorem commFourAdj_vz_of_le [Finite K] {z : K} {P F : Subgroup K} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ g ∈ P, g * z = z * g) (hF : IsKleinFour F) (hFP : F ≤ P) :
    ∃ f ∈ F, Inv2 z f ∧ Sig.CommFourAdj K F (vz z f) := by
  have hF2 : ∀ x ∈ F, x ^ 2 = 1 := fun x hx => FooteLit.sq_eq_one_of_isKleinFour hF hx
  obtain ⟨f, hfF, hf1, hfz⟩ := exists_mem_ne_ne (H := F) (by rw [hF.card_four]; norm_num) 1 z
  have hf : Inv2 z f := ⟨by rw [← sq]; exact hF2 f hfF, hf1, hfz, hzc f (hFP hfF)⟩
  refine ⟨f, hfF, hf, hF, isKleinFour_vz hz2 hz1 hf, ?_⟩
  rw [le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    exact FooteLit.commute_of_sq_eq_one hF2 hh hfF
  · rw [Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    exact hzc h (hFP hh)

end Graph

section Tensor

variable {K : Type} [Group K]

structure QuatIn (z : K) (Q : Subgroup K) : Prop where
  mem : z ∈ Q
  sq : z * z = 1
  ne_one : z ≠ 1
  unique : ∀ a ∈ Q, a * a = 1 → a = 1 ∨ a = z
  exists_sq : ∃ a ∈ Q, a * a = z
  common : ∀ a ∈ Q, a * a = z → ∀ b ∈ Q, b * b = z →
    ∃ c ∈ Q, c * c = z ∧ c * a = z * (a * c) ∧ c * b = z * (b * c)

theorem QuatIn.of_quatData {z : K} {Q : Subgroup K} (hz : z ∈ Q) (h : QuatData ↥Q ⟨z, hz⟩) :
    QuatIn z Q where
  mem := hz
  sq := congrArg Subtype.val h.sq
  ne_one := fun h1 => h.ne_one (Subtype.ext h1)
  unique := fun a ha haa => by
    rcases h.unique ⟨a, ha⟩ (Subtype.ext haa) with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1
  exists_sq := by
    obtain ⟨⟨a, ha⟩, h1⟩ := h.exists_sq
    exact ⟨a, ha, congrArg Subtype.val h1⟩
  common := fun a ha haz b hb hbz => by
    obtain ⟨⟨c, hc⟩, h1, h2, h3⟩ := h.common ⟨a, ha⟩ ⟨b, hb⟩ (Subtype.ext haz) (Subtype.ext hbz)
    exact ⟨c, hc, congrArg Subtype.val h1, congrArg Subtype.val h2, congrArg Subtype.val h3⟩

theorem QuatIn.map_mulEquiv {z : K} {Q : Subgroup K} (h : QuatIn z Q) (f : K ≃* K)
    (hfz : f z = z) : QuatIn z (Q.map f.toMonoidHom) where
  mem := ⟨z, h.mem, hfz⟩
  sq := h.sq
  ne_one := h.ne_one
  unique := fun b hb hbb => by
    obtain ⟨a, ha, hab⟩ := hb
    have hab' : b = f a := hab.symm
    subst hab'
    have haa : a * a = 1 := f.injective (by rw [map_mul, map_one]; exact hbb)
    rcases h.unique a ha haa with h1 | h1
    · left; rw [h1, map_one]
    · right; rw [h1, hfz]
  exists_sq := by
    obtain ⟨a, ha, haz⟩ := h.exists_sq
    exact ⟨f a, ⟨a, ha, rfl⟩, by rw [← map_mul, haz, hfz]⟩
  common := fun b₁ hb₁ hb₁z b₂ hb₂ hb₂z => by
    obtain ⟨a₁, ha₁, hab₁⟩ := hb₁
    obtain ⟨a₂, ha₂, hab₂⟩ := hb₂
    have hab₁' : b₁ = f a₁ := hab₁.symm
    have hab₂' : b₂ = f a₂ := hab₂.symm
    subst hab₁' hab₂'
    have h1 : a₁ * a₁ = z := f.injective (by rw [map_mul, hfz]; exact hb₁z)
    have h2 : a₂ * a₂ = z := f.injective (by rw [map_mul, hfz]; exact hb₂z)
    obtain ⟨c, hc, hcz, hc1, hc2⟩ := h.common a₁ ha₁ h1 a₂ ha₂ h2
    refine ⟨f c, ⟨c, hc, rfl⟩, ?_, ?_, ?_⟩
    · rw [← map_mul, hcz, hfz]
    · rw [← map_mul, hc1, map_mul, map_mul, hfz]
    · rw [← map_mul, hc2, map_mul, map_mul, hfz]

private theorem le_normalizer_of_comm {A B : Subgroup K}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ≤ normalizer (B : Set K) := fun x hx =>
  mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      rw [show x * y * x⁻¹ = y by rw [hc x hx y hy]; group]
      exact hy
    · intro hy
      have h := hc x hx _ hy
      have e : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹ * x) := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h]
          _ = x * y * x⁻¹ := by group
      rw [e]
      exact hy

theorem mem_sup_of_commute {A B : Subgroup K} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : K}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_comm hc)] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨a, ha, b, hb, rfl⟩

structure QuatPair (z : K) (P Q₁ Q₂ : Subgroup K) : Prop where
  zc : ∀ g ∈ P, g * z = z * g
  le₁ : Q₁ ≤ P
  le₂ : Q₂ ≤ P
  comm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a
  inter : ∀ g ∈ Q₁, g ∈ Q₂ → g = 1 ∨ g = z
  q₁ : QuatIn z Q₁
  q₂ : QuatIn z Q₂

variable {z : K} {P Q₁ Q₂ : Subgroup K}

theorem QuatPair.not_sq_mem (h : QuatPair z P Q₁ Q₂) {g : K} (hg₁ : g ∈ Q₁) (hg₂ : g ∈ Q₂)
    (hgz : g * g = z) : False := by
  rcases h.inter g hg₁ hg₂ with h1 | h1
  · apply h.q₁.ne_one
    rw [← hgz, h1, one_mul]
  · apply h.q₁.ne_one
    calc z = g * g := hgz.symm
      _ = z * z := by rw [h1]
      _ = 1 := h.q₁.sq

theorem QuatPair.inv2_mul (h : QuatPair z P Q₁ Q₂) {c₁ c₂ : K} (hc₁ : c₁ ∈ Q₁) (hc₂ : c₂ ∈ Q₂)
    (h1 : c₁ * c₁ = z) (h2 : c₂ * c₂ = z) : Inv2 z (c₁ * c₂) where
  sq := by
    calc c₁ * c₂ * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ := by simp only [mul_assoc]
      _ = c₁ * (c₁ * c₂) * c₂ := by rw [(h.comm c₁ hc₁ c₂ hc₂).symm]
      _ = (c₁ * c₁) * (c₂ * c₂) := by simp only [mul_assoc]
      _ = 1 := by rw [h1, h2, h.q₁.sq]
  ne_one := fun h0 => by
    have hc : c₁ = c₂⁻¹ := eq_inv_of_mul_eq_one_left h0
    exact h.not_sq_mem hc₁ (by rw [hc]; exact Q₂.inv_mem hc₂) h1
  ne_z := fun h0 => by
    have hc : c₁ = z * c₂⁻¹ := eq_mul_inv_of_mul_eq h0
    exact h.not_sq_mem hc₁ (by rw [hc]; exact Q₂.mul_mem h.q₂.mem (Q₂.inv_mem hc₂)) h1
  comm := h.zc _ (mul_mem (h.le₁ hc₁) (h.le₂ hc₂))

theorem QuatPair.sq_of_decomp (h : QuatPair z P Q₁ Q₂) {a₁ a₂ : K} (ha₁ : a₁ ∈ Q₁)
    (ha₂ : a₂ ∈ Q₂) (hi : Inv2 z (a₁ * a₂)) : a₁ * a₁ = z ∧ a₂ * a₂ = z := by
  have hsq : a₁ * a₁ * (a₂ * a₂) = 1 := by
    calc a₁ * a₁ * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by simp only [mul_assoc]
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [h.comm a₁ ha₁ a₂ ha₂]
      _ = a₁ * a₂ * (a₁ * a₂) := by simp only [mul_assoc]
      _ = 1 := hi.sq
  have hmem : a₁ * a₁ ∈ Q₂ := by
    have : a₁ * a₁ = (a₂ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact Q₂.inv_mem (Q₂.mul_mem ha₂ ha₂)
  rcases h.inter _ (Q₁.mul_mem ha₁ ha₁) hmem with h1 | h1
  · have h2 : a₂ * a₂ = 1 := by rw [h1, one_mul] at hsq; exact hsq
    exfalso
    rcases h.q₁.unique a₁ ha₁ h1 with e1 | e1 <;> rcases h.q₂.unique a₂ ha₂ h2 with e2 | e2
    · exact hi.ne_one (by rw [e1, e2, one_mul])
    · exact hi.ne_z (by rw [e1, e2, one_mul])
    · exact hi.ne_z (by rw [e1, e2, mul_one])
    · exact hi.ne_one (by rw [e1, e2, h.q₁.sq])
  · refine ⟨h1, ?_⟩
    rw [h1] at hsq
    have : a₂ * a₂ = z⁻¹ := eq_inv_of_mul_eq_one_right hsq
    rw [this]
    exact inv_eq_of_mul_eq_one_right h.q₁.sq

theorem QuatPair.comm_of_anti (h : QuatPair z P Q₁ Q₂) {a₁ a₂ c₁ c₂ : K} (ha₁ : a₁ ∈ Q₁)
    (ha₂ : a₂ ∈ Q₂) (hc₁ : c₁ ∈ Q₁) (hc₂ : c₂ ∈ Q₂) (h1 : c₁ * a₁ = z * (a₁ * c₁))
    (h2 : c₂ * a₂ = z * (a₂ * c₂)) : (c₁ * c₂) * (a₁ * a₂) = (a₁ * a₂) * (c₁ * c₂) := by
  have hzac : a₁ * c₁ * z = z * (a₁ * c₁) := h.zc _ (mul_mem (h.le₁ ha₁) (h.le₁ hc₁))
  calc c₁ * c₂ * (a₁ * a₂) = c₁ * (c₂ * a₁) * a₂ := by simp only [mul_assoc]
    _ = c₁ * (a₁ * c₂) * a₂ := by rw [(h.comm a₁ ha₁ c₂ hc₂).symm]
    _ = (c₁ * a₁) * (c₂ * a₂) := by simp only [mul_assoc]
    _ = (z * (a₁ * c₁)) * (z * (a₂ * c₂)) := by rw [h1, h2]
    _ = z * ((a₁ * c₁) * z) * (a₂ * c₂) := by simp only [mul_assoc]
    _ = z * (z * (a₁ * c₁)) * (a₂ * c₂) := by rw [hzac]
    _ = (z * z) * ((a₁ * c₁) * (a₂ * c₂)) := by simp only [mul_assoc]
    _ = (a₁ * c₁) * (a₂ * c₂) := by rw [h.q₁.sq, one_mul]
    _ = a₁ * (c₁ * a₂) * c₂ := by simp only [mul_assoc]
    _ = a₁ * (a₂ * c₁) * c₂ := by rw [h.comm c₁ hc₁ a₂ ha₂]
    _ = (a₁ * a₂) * (c₁ * c₂) := by simp only [mul_assoc]

theorem QuatPair.reflTransGen_vz [Finite K] (h : QuatPair z P Q₁ Q₂) {x y : K}
    (hx : x ∈ Q₁ ⊔ Q₂) (hy : y ∈ Q₁ ⊔ Q₂) (hxi : Inv2 z x) (hyi : Inv2 z y) :
    Relation.ReflTransGen (Sig.CommFourAdj K) (vz z x) (vz z y) := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute h.comm hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_sup_of_commute h.comm hy
  obtain ⟨ha₁z, ha₂z⟩ := h.sq_of_decomp ha₁ ha₂ hxi
  obtain ⟨hb₁z, hb₂z⟩ := h.sq_of_decomp hb₁ hb₂ hyi
  obtain ⟨c₁, hc₁, hc₁z, hc₁a, hc₁b⟩ := h.q₁.common a₁ ha₁ ha₁z b₁ hb₁ hb₁z
  obtain ⟨c₂, hc₂, hc₂z, hc₂a, hc₂b⟩ := h.q₂.common a₂ ha₂ ha₂z b₂ hb₂ hb₂z
  have hwi : Inv2 z (c₁ * c₂) := h.inv2_mul hc₁ hc₂ hc₁z hc₂z
  have hxw : (a₁ * a₂) * (c₁ * c₂) = (c₁ * c₂) * (a₁ * a₂) :=
    (h.comm_of_anti ha₁ ha₂ hc₁ hc₂ hc₁a hc₂a).symm
  have hyw : (c₁ * c₂) * (b₁ * b₂) = (b₁ * b₂) * (c₁ * c₂) :=
    h.comm_of_anti hb₁ hb₂ hc₁ hc₂ hc₁b hc₂b
  exact (Relation.ReflTransGen.single (commFourAdj_vz h.q₁.sq h.q₁.ne_one hxi hwi hxw)).trans
    (Relation.ReflTransGen.single (commFourAdj_vz h.q₁.sq h.q₁.ne_one hwi hyi hyw))

theorem QuatPair.exists_inv2_comm (h : QuatPair z P Q₁ Q₂) {t x e : K} (ht2 : t * t = 1)
    (hQt : ∀ a ∈ Q₁, t * a * t ∈ Q₂) (he : e ∈ Q₁ ⊔ Q₂) (hx : x = e * t) (hxi : Inv2 z x) :
    ∃ y ∈ Q₁ ⊔ Q₂, Inv2 z y ∧ x * y = y * x := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_sup_of_commute h.comm he
  obtain ⟨a₁, ha₁, ha₁z⟩ := h.q₁.exists_sq
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxi.sq
  obtain ⟨a₂, ha₂def⟩ : ∃ a₂, a₂ = x * a₁ * x⁻¹ := ⟨_, rfl⟩
  have ha₂ : a₂ ∈ Q₂ := by
    have hb : t * a₁ * t⁻¹ ∈ Q₂ := by rw [ht_inv]; exact hQt a₁ ha₁
    have hb' : u₂ * (t * a₁ * t⁻¹) * u₂⁻¹ ∈ Q₂ :=
      Q₂.mul_mem (Q₂.mul_mem hu₂ hb) (Q₂.inv_mem hu₂)
    have e1 : a₂ = u₁ * (u₂ * (t * a₁ * t⁻¹) * u₂⁻¹) * u₁⁻¹ := by
      rw [ha₂def, hx]; group
    have e2 : u₁ * (u₂ * (t * a₁ * t⁻¹) * u₂⁻¹) * u₁⁻¹ = u₂ * (t * a₁ * t⁻¹) * u₂⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h.comm u₁ hu₁ _ hb'
    rw [e1, e2]
    exact hb'
  have hxa₁ : x * a₁ = a₂ * x := by rw [ha₂def]; group
  have hxa₂ : x * a₂ = a₁ * x := by
    calc x * a₂ = x * (x * a₁ * x⁻¹) := by rw [ha₂def]
      _ = (x * x) * a₁ * x⁻¹ := by group
      _ = a₁ * x⁻¹ := by rw [hxi.sq, one_mul]
      _ = a₁ * x := by rw [hxinv]
  have ha₂z : a₂ * a₂ = z := by
    calc a₂ * a₂ = x * (a₁ * a₁) * x⁻¹ := by rw [ha₂def]; group
      _ = x * z * x⁻¹ := by rw [ha₁z]
      _ = z := by rw [hxi.comm]; group
  refine ⟨a₁ * a₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂),
    h.inv2_mul ha₁ ha₂ ha₁z ha₂z, ?_⟩
  calc x * (a₁ * a₂) = (x * a₁) * a₂ := (mul_assoc _ _ _).symm
    _ = a₂ * x * a₂ := by rw [hxa₁]
    _ = a₂ * (x * a₂) := mul_assoc _ _ _
    _ = a₂ * (a₁ * x) := by rw [hxa₂]
    _ = (a₂ * a₁) * x := (mul_assoc _ _ _).symm
    _ = (a₁ * a₂) * x := by rw [(h.comm a₁ ha₁ a₂ ha₂).symm]

theorem reflTransGen_commFourAdj_of_quatPair [Finite K] {t : K} (h : QuatPair z P Q₁ Q₂)
    (ht2 : t * t = 1) (hQt : ∀ a ∈ Q₁, t * a * t ∈ Q₂)
    (hP : ∀ g ∈ P, ∃ e ∈ Q₁ ⊔ Q₂, g = e ∨ g = e * t) {F G : Subgroup K} (hF : IsKleinFour F)
    (hFP : F ≤ P) (hG : IsKleinFour G) (hGP : G ≤ P) :
    Relation.ReflTransGen (Sig.CommFourAdj K) F G := by
  obtain ⟨a₁, ha₁, ha₁z⟩ := h.q₁.exists_sq
  obtain ⟨a₂, ha₂, ha₂z⟩ := h.q₂.exists_sq
  have hx₀ : Inv2 z (a₁ * a₂) := h.inv2_mul ha₁ ha₂ ha₁z ha₂z
  have hx₀m : a₁ * a₂ ∈ Q₁ ⊔ Q₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)
  have key : ∀ F : Subgroup K, IsKleinFour F → F ≤ P →
      Relation.ReflTransGen (Sig.CommFourAdj K) F (vz z (a₁ * a₂)) := by
    intro F hF hFP
    obtain ⟨f, hfF, hfi, hadj⟩ := commFourAdj_vz_of_le h.q₁.sq h.q₁.ne_one h.zc hF hFP
    refine Relation.ReflTransGen.head hadj ?_
    obtain ⟨e, he, hfe | hfe⟩ := hP f (hFP hfF)
    · exact h.reflTransGen_vz (by rw [hfe]; exact he) hx₀m hfi hx₀
    · obtain ⟨y, hy, hyi, hfy⟩ := h.exists_inv2_comm ht2 hQt he hfe hfi
      exact (Relation.ReflTransGen.single
        (commFourAdj_vz h.q₁.sq h.q₁.ne_one hfi hyi hfy)).trans
          (h.reflTransGen_vz hy hx₀m hyi hx₀)
  exact (key F hF hFP).trans (reflTransGen_commFourAdj_symm (key G hG hGP))

end Tensor

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
