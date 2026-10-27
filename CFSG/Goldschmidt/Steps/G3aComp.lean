module

public import CFSG.Goldschmidt.Steps.G3aAut
public import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups Pointwise

namespace G3a

open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)

section Acts

variable {Q : Type*} [Group Q]

def actsBy (L M : Subgroup Q) (hML : M ≤ L) : Subgroup Q where
  carrier := {q | ∃ ℓ ∈ M, ∀ x ∈ L, q⁻¹ * x * q = ℓ⁻¹ * x * ℓ}
  one_mem' := ⟨1, M.one_mem, fun x _ => by group⟩
  mul_mem' := by
    rintro q₁ q₂ ⟨ℓ₁, hℓ₁, h₁⟩ ⟨ℓ₂, hℓ₂, h₂⟩
    refine ⟨ℓ₁ * ℓ₂, M.mul_mem hℓ₁ hℓ₂, fun x hx => ?_⟩
    have hy : ℓ₁⁻¹ * x * ℓ₁ ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem (hML hℓ₁)) hx) (hML hℓ₁)
    calc (q₁ * q₂)⁻¹ * x * (q₁ * q₂) = q₂⁻¹ * (q₁⁻¹ * x * q₁) * q₂ := by group
      _ = q₂⁻¹ * (ℓ₁⁻¹ * x * ℓ₁) * q₂ := by rw [h₁ x hx]
      _ = ℓ₂⁻¹ * (ℓ₁⁻¹ * x * ℓ₁) * ℓ₂ := h₂ _ hy
      _ = (ℓ₁ * ℓ₂)⁻¹ * x * (ℓ₁ * ℓ₂) := by group
  inv_mem' := by
    rintro q ⟨ℓ, hℓ, h⟩
    refine ⟨ℓ⁻¹, M.inv_mem hℓ, fun x hx => ?_⟩
    have hy : ℓ * x * ℓ⁻¹ ∈ L := L.mul_mem (L.mul_mem (hML hℓ) hx) (L.inv_mem (hML hℓ))
    have h1 := h _ hy
    have e1 : ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ = x := by group
    rw [e1] at h1
    calc q⁻¹⁻¹ * x * q⁻¹ = q * (q⁻¹ * (ℓ * x * ℓ⁻¹) * q) * q⁻¹ := by rw [h1, inv_inv]
      _ = ℓ⁻¹⁻¹ * x * ℓ⁻¹ := by group

theorem mem_actsBy {L M : Subgroup Q} {hML : M ≤ L} {q : Q} :
    q ∈ actsBy L M hML ↔ ∃ ℓ ∈ M, ∀ x ∈ L, q⁻¹ * x * q = ℓ⁻¹ * x * ℓ := Iff.rfl

theorem act_pow {L : Subgroup Q} {a ℓ : Q} (hℓ : ℓ ∈ L)
    (hact : ∀ x ∈ L, a⁻¹ * x * a = ℓ⁻¹ * x * ℓ) (n : ℕ) :
    ∀ x ∈ L, (a ^ n)⁻¹ * x * a ^ n = (ℓ ^ n)⁻¹ * x * ℓ ^ n := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have hy : (ℓ ^ n)⁻¹ * x * ℓ ^ n ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem (L.pow_mem hℓ n)) hx) (L.pow_mem hℓ n)
    calc (a ^ (n + 1))⁻¹ * x * a ^ (n + 1) = a⁻¹ * ((a ^ n)⁻¹ * x * a ^ n) * a := by
          rw [pow_succ]; group
      _ = a⁻¹ * ((ℓ ^ n)⁻¹ * x * ℓ ^ n) * a := by rw [ih x hx]
      _ = ℓ⁻¹ * ((ℓ ^ n)⁻¹ * x * ℓ ^ n) * ℓ := hact _ hy
      _ = (ℓ ^ (n + 1))⁻¹ * x * ℓ ^ (n + 1) := by rw [pow_succ]; group

end Acts

section PGroup

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem le_sylow_of_le_normalizer (P : Sylow 2 Q) {N : Subgroup Q} (hN : IsPGroup 2 N)
    (hNP : N ≤ Subgroup.normalizer ((P : Subgroup Q) : Set Q)) : N ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hN.to_sup_of_normal_right' P.isPGroup' hNP
  have := P.is_maximal' hp le_sup_right
  rw [← this]
  exact le_sup_left

omit [Finite Q] in
theorem le_sylow_of_normal (P : Sylow 2 Q) {N : Subgroup Q} [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hN.to_sup_of_normal_left P.isPGroup'
  have := P.is_maximal' hp le_sup_right
  rw [← this]
  exact le_sup_left

omit [Finite Q] in
theorem pCore_le_sylow (P : Sylow 2 Q) : CFSG.Open.pCore 2 Q ≤ P := by
  have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := Q) 2
  exact le_sylow_of_normal P (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2)

end PGroup

section TypeI

variable {K : Type} [Group K] [Finite K]

theorem mem_center_of_fixed
    (hI : IsGoldTypeI K) (P : Sylow 2 K) {ℓ : K}
    (hℓ : ℓ ∈ (P : Subgroup K))
    (h1 : ∀ t ∈ (P : Subgroup K), ℓ⁻¹ * t * ℓ * t⁻¹ ∈ Subgroup.center K)
    (h2 : ∀ n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
      ℓ⁻¹ * (n⁻¹ * ℓ * n) ∈ Subgroup.center K) : ℓ ∈ Subgroup.center K := by
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hQ : fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  set P' : Sylow 2 (K ⧸ Subgroup.center K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup (K ⧸ Subgroup.center K)) = (P : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D, h⟩ := exists_borelSetup hQ P'
  have hker : ∀ {y : K}, y ∈ Subgroup.center K ↔ π y = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']
  have hℓP : π ℓ ∈ (P' : Subgroup (K ⧸ Subgroup.center K)) := by rw [hP']; exact ⟨ℓ, hℓ, rfl⟩
  have hℓC : π ℓ ∈ Subgroup.centralizer
      ((P' : Subgroup (K ⧸ Subgroup.center K)) : Set (K ⧸ Subgroup.center K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [hP'] at ht
    obtain ⟨t, ht, rfl⟩ := ht
    have := hker.mp (h1 t ht)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
    calc π t * π ℓ = π ℓ * ((π ℓ)⁻¹ * π t * π ℓ * (π t)⁻¹) * π t := by group
      _ = π ℓ * π t := by rw [this]; group
  have hℓZ : π ℓ ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)) := ⟨hℓP, hℓC⟩
  rw [hker]
  by_contra hne
  obtain ⟨w, hw, hw1, hwℓ⟩ := h.exists_ne (π ℓ)
  obtain ⟨d, hd, hdw⟩ := h.trans hℓZ hw hne hw1
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ d
  have hn := mem_normalizer_of_map P (by rw [← hP']; exact h.le hd)
  have := hker.mp (h2 n hn)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
  apply hwℓ
  rw [← hdw]
  calc (QuotientGroup.mk' (Subgroup.center K) n)⁻¹ * π ℓ * QuotientGroup.mk' (Subgroup.center K) n
      = π ℓ * ((π ℓ)⁻¹ * ((π n)⁻¹ * π ℓ * π n)) := by rw [hπ]; group
    _ = π ℓ := by rw [this, mul_one]

theorem exists_sq_eq
    (hI : IsGoldTypeI K) (P : Sylow 2 K) {B : Subgroup K}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hmap : B.map (QuotientGroup.mk' (Subgroup.center K)) =
      sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K)) :
        Sylow 2 (K ⧸ Subgroup.center K)) : Subgroup (K ⧸ Subgroup.center K)))
    {x : K} (hx : x ∈ B) : ∃ z ∈ Subgroup.center K, x ^ 2 = z ^ 2 := by
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hQ : fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  set P' : Sylow 2 (K ⧸ Subgroup.center K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup (K ⧸ Subgroup.center K)) = (P : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D, h⟩ := exists_borelSetup hQ P'
  have hker : ∀ {y : K}, y ∈ Subgroup.center K ↔ π y = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']
  have hcen : ∀ {z y : K}, z ∈ Subgroup.center K → z * y = y * z := fun hz =>
    Subgroup.mem_center_iff.mp hz _ |>.symm
  have hsq : ∀ y ∈ B, y ^ 2 ∈ Subgroup.center K := by
    intro y hy
    have hyZ : π y ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    rw [hker, map_pow]
    exact h.sq _ hyZ
  have htr : ∀ y ∈ B, ∀ y' ∈ B, π y ≠ 1 → π y' ≠ 1 →
      ∃ z ∈ Subgroup.center K, y ^ 2 = y' ^ 2 * z ^ 2 := by
    intro y hy y' hy' h1 h2
    have hyZ : π y ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    have hy'Z : π y' ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [← hmap]
      exact ⟨y', hy', rfl⟩
    obtain ⟨d, hd, hdy⟩ := h.trans hyZ hy'Z h1 h2
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ d
    have hn := mem_normalizer_of_map P (by rw [← hP']; exact h.le hd)
    set z := y'⁻¹ * (n⁻¹ * y * n) with hz
    have hzZ : z ∈ Subgroup.center K := by
      rw [hker, hz, map_mul, map_mul, map_mul, map_inv, map_inv]
      change (π y')⁻¹ * ((π n)⁻¹ * π y * π n) = 1
      rw [show (π n)⁻¹ * π y * π n = π y' from hdy]
      group
    refine ⟨z, hzZ, ?_⟩
    have hyc : y ^ 2 * n = n * y ^ 2 := hcen (hsq y hy)
    have e1 : (n⁻¹ * y * n) ^ 2 = y ^ 2 := by
      rw [sq, sq]
      calc n⁻¹ * y * n * (n⁻¹ * y * n) = n⁻¹ * (y * y) * n := by group
        _ = n⁻¹ * (y * y * n) := by group
        _ = n⁻¹ * (n * (y * y)) := by rw [← sq, hyc, sq]
        _ = y * y := by group
    have e2 : n⁻¹ * y * n = y' * z := by rw [hz]; group
    rw [← e1, e2, sq, sq y', sq z]
    calc y' * z * (y' * z) = y' * (z * y') * z := by group
      _ = y' * (y' * z) * z := by rw [hcen hzZ]
      _ = y' * y' * (z * z) := by group
  by_cases hx1 : π x = 1
  · exact ⟨x, hker.mpr hx1, rfl⟩
  have hxZ : π x ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)) := by
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  obtain ⟨w, hw, hw1, hwx⟩ := h.exists_ne (π x)
  rw [← hmap] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hxy1 : π (x * y) ≠ 1 := by
    rw [map_mul]
    intro h'
    apply hwx
    have hx2 : π x * π x = 1 := by rw [← sq]; exact h.sq _ hxZ
    calc (QuotientGroup.mk' (Subgroup.center K)) y = (π x)⁻¹ * (π x * π y) := by
          rw [hπ]; group
      _ = π x := by rw [h', mul_one, inv_eq_of_mul_eq_one_right hx2]
  obtain ⟨z₁, hz₁, e₁⟩ := htr x hx (x * y) (B.mul_mem hx hy) hx1 hxy1
  obtain ⟨z₂, hz₂, e₂⟩ := htr x hx y hy hx1 hw1
  have hxy : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
    rw [sq, sq, sq]
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hBc y hy x hx]
      _ = x * x * (y * y) := by group
  have hy2 : y ^ 2 = z₁⁻¹ ^ 2 := by
    have h3 : x ^ 2 = x ^ 2 * (y ^ 2 * z₁ ^ 2) := by
      calc x ^ 2 = (x * y) ^ 2 * z₁ ^ 2 := e₁
        _ = x ^ 2 * (y ^ 2 * z₁ ^ 2) := by rw [hxy, mul_assoc]
    have h4 : y ^ 2 * z₁ ^ 2 = 1 := mul_eq_left.mp h3.symm
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left h4
  refine ⟨z₁⁻¹ * z₂, Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₁) hz₂, ?_⟩
  rw [e₂, hy2, sq, sq, sq]
  have hc : z₁⁻¹ * z₂ = z₂ * z₁⁻¹ := hcen (Subgroup.inv_mem _ hz₁)
  calc z₁⁻¹ * z₁⁻¹ * (z₂ * z₂) = z₁⁻¹ * (z₁⁻¹ * z₂) * z₂ := by group
    _ = z₁⁻¹ * (z₂ * z₁⁻¹) * z₂ := by rw [hc]
    _ = z₁⁻¹ * z₂ * (z₁⁻¹ * z₂) := by group

end TypeI

section Conf

variable {Q : Type} [Group Q] [Finite Q]

structure SConf (P : Sylow 2 Q) (B : Subgroup Q) : Prop where
  le : B ≤ P
  comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  closed : fusionStronglyClosed (B : Set Q) (P : Subgroup Q)
  top : Subgroup.normalClosure (B : Set Q) = ⊤
  odd : goldschmidtOddCore Q = ⊥
  gen : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤
  central : CFSG.Open.pCore 2 Q ≤ Subgroup.center Q
  bar : B = CFSG.Open.pCore 2 Q ⊔ Omega1 ((P : Subgroup Q) ⊓ goldschmidtLayer Q)
  types : ∀ L : Subgroup Q, IsComponentOf L ⊤ → IsGoldTypeI L ∨ IsGoldTypeII L

namespace SConf

variable {P : Sylow 2 Q} {B : Subgroup Q} (hc : SConf P B) {L : Subgroup Q}
  (hL : IsComponentOf L ⊤)
include hc hL

theorem exists_act (q : Q) : ∃ ℓ ∈ L, ∀ x ∈ L, q⁻¹ * x * q = ℓ⁻¹ * x * ℓ := by
  have h2 : CFSG.Open.pCore 2 Q ≤ actsBy L L le_rfl := fun q hq =>
    ⟨1, L.one_mem, fun x _ => by
      have := Subgroup.mem_center_iff.1 (hc.central hq) x
      calc q⁻¹ * x * q = q⁻¹ * (x * q) := by group
        _ = q⁻¹ * (q * x) := by rw [this]
        _ = 1⁻¹ * x * 1 := by group⟩
  have hE : goldschmidtLayer Q ≤ actsBy L L le_rfl := by
    refine sSup_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · intro y hy
      rw [hLL] at hy
      exact ⟨y, hy, fun x _ => rfl⟩
    · intro y hy
      refine ⟨1, L.one_mem, fun x hx => ?_⟩
      have hcm := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b Q L' L hL' hL hLL) hy
      have := Subgroup.mem_centralizer_iff.1 hcm x hx
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [this]
        _ = 1⁻¹ * x * 1 := by group
  have h := sup_le h2 hE
  rw [hc.gen] at h
  exact h (Subgroup.mem_top q)

theorem normal : L.Normal := ⟨fun x hx g => by
  obtain ⟨ℓ, hℓ, hact⟩ := hc.exists_act hL g⁻¹
  have := hact x hx
  rw [inv_inv] at this
  rw [this]
  exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) hx) hℓ⟩

theorem center_le_pCore : (Subgroup.center L).map L.subtype ≤ CFSG.Open.pCore 2 Q := by
  have := hc.normal hL
  have hp : IsPGroup 2 ((Subgroup.center L).map L.subtype) := ((N8d Q hc.odd).1 L hL).map _
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 _ inferInstance hp

theorem center_le : (Subgroup.center L).map L.subtype ≤ B := by
  rw [hc.bar]
  exact le_sup_of_le_left (hc.center_le_pCore hL)

omit [Finite Q] in
theorem omega1_le : Omega1 ((P : Subgroup Q) ⊓ L) ≤ B := by
  rw [hc.bar]
  refine le_sup_of_le_right (Subgroup.closure_mono ?_)
  rintro t ⟨⟨htP, htL⟩, ht2⟩
  exact ⟨⟨htP, CFSG.ComponentClassification.Layer.component_le hL htL⟩, ht2⟩

theorem not_le_centralizer : ¬ B ≤ Subgroup.centralizer (L : Set Q) := by
  intro hB
  have := hc.normal hL
  have htop : Subgroup.centralizer (L : Set Q) = ⊤ := by
    rw [eq_top_iff, ← hc.top]
    exact Subgroup.normalClosure_le_normal hB
  have hZ : Subgroup.center L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    have hx : (x : Q) ∈ Subgroup.centralizer (L : Set Q) := by rw [htop]; exact Subgroup.mem_top _
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hZ]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ hsub

theorem exists_sylow : ∃ PL : Sylow 2 L,
    ∀ x : L, x ∈ (PL : Subgroup L) ↔ (x : Q) ∈ (P : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hc.normal hL
  obtain ⟨PL, hPL⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P
    (Subgroup.Normal.isSubnormal ‹L.Normal›)
  refine ⟨PL, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have : (x : Q) ∈ (PL : Subgroup L).map L.subtype := ⟨x, hx, rfl⟩
    rw [hPL] at this
    exact this.1
  · have : (x : Q) ∈ (P : Subgroup Q) ⊓ L := ⟨hx, x.2⟩
    rw [← hPL] at this
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from Subtype.ext hyx] at hy

theorem mem_sylow_of_act {a ℓ : Q} (ha : a ∈ (P : Subgroup Q)) (hℓ : ℓ ∈ L)
    (hact : ∀ x ∈ L, a⁻¹ * x * a = ℓ⁻¹ * x * ℓ) : ℓ ∈ (P : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := hc.normal hL
  obtain ⟨PL, hmemPL⟩ := hc.exists_sylow hL
  have hact' : ∀ x ∈ L, ℓ * x * ℓ⁻¹ = a * x * a⁻¹ := by
    intro x hx
    have hy : a * x * a⁻¹ ∈ L := hLn.conj_mem x hx a
    have h1 := hact _ hy
    calc ℓ * x * ℓ⁻¹ = ℓ * (a⁻¹ * (a * x * a⁻¹) * a) * ℓ⁻¹ := by group
      _ = ℓ * (ℓ⁻¹ * (a * x * a⁻¹) * ℓ) * ℓ⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ := by group
  set ℓ' : L := ⟨ℓ, hℓ⟩ with hℓ'
  have hmaps : ∀ s ∈ (PL : Subgroup L), MulAut.conj ℓ' s ∈ (PL : Subgroup L) := by
    intro s hs
    rw [hmemPL] at hs ⊢
    rw [MulAut.conj_apply]
    change ℓ * (s : Q) * ℓ⁻¹ ∈ (P : Subgroup Q)
    rw [hact' s s.2]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ha) _).mp hs
  have hS := CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.smul_eq_of_mapsTo
    (α := MulAut.conj ℓ') (S := PL) hmaps
  rw [← Sylow.smul_def] at hS
  have hN := Sylow.smul_eq_iff_mem_normalizer.mp hS
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨a, ha⟩
  have hak : a ^ (2 ^ k) = 1 := by
    have h1 := pow_orderOf_eq_one (⟨a, ha⟩ : (P : Subgroup Q))
    rw [hk] at h1
    simpa using congrArg Subtype.val h1
  have hℓZ : ℓ' ^ (2 ^ k) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := act_pow hℓ hact (2 ^ k) y y.2
    rw [hak, inv_one, one_mul, mul_one] at h1
    change (y : Q) * ℓ ^ (2 ^ k) = ℓ ^ (2 ^ k) * y
    calc (y : Q) * ℓ ^ (2 ^ k) = ℓ ^ (2 ^ k) * ((ℓ ^ (2 ^ k))⁻¹ * y * ℓ ^ (2 ^ k)) := by group
      _ = ℓ ^ (2 ^ k) * y := by rw [← h1]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp ((N8d Q hc.odd).1 L hL)) ⟨_, hℓZ⟩
  have hℓ2 : ℓ' ^ (2 ^ (k + j)) = 1 := by
    have h1 := pow_orderOf_eq_one (⟨_, hℓZ⟩ : Subgroup.center L)
    rw [hj] at h1
    have h2 : (ℓ' ^ (2 ^ k)) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val h1
    rwa [← pow_mul, ← pow_add] at h2
  have hp : IsPGroup 2 (Subgroup.zpowers ℓ') := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hℓ2)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hmem : ℓ' ∈ Subgroup.zpowers ℓ' ⊓ (PL : Subgroup L) := by
    rw [← hp.inf_normalizer_sylow PL]
    exact ⟨Subgroup.mem_zpowers ℓ', hN⟩
  exact (hmemPL ℓ').mp hmem.2

omit [Finite Q] hc in
theorem exists_mul_ne : ∃ a b : L, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hZ : Subgroup.center L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hab y x
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hZ]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ hsub

theorem typeII_facts (hII : IsGoldTypeII L) : Subgroup.center L = ⊥ ∧
    (∀ t ∈ (P : Subgroup Q) ⊓ L, t ^ 2 = 1) ∧ ∃ t ∈ (P : Subgroup Q) ⊓ L, t ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.center L) := (N8d Q hc.odd).1 L hL
  have hZ : Subgroup.center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have hodd := hII.1
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  obtain ⟨PL, hmemPL⟩ := hc.exists_sylow hL
  obtain ⟨hexp, hcard⟩ : (∀ t ∈ (PL : Subgroup L), t ^ 2 = 1) ∧ 2 ≤ Nat.card (PL : Subgroup L) := by
    rcases hII.2 with hL2 | hJR
    · obtain ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ := hL2
      have e' := CFSG.QuasithinUnique.RankOneRecog.mulEquivOfCenterEqBot hZ e
      obtain ⟨hcard, hexp, -⟩ := GoldType.sylow_of_psl2_odd hpo hf h8 e' PL
      exact ⟨hexp, by omega⟩
    · have hJR' : CFSG.Walter.IsTypeJR L := CFSG.Walter.IsTypeJR.of_mulEquiv
        (CFSG.QuasithinUnique.RankOneRecog.mulEquivOfCenterEqBot hZ (MulEquiv.refl _)).symm hJR
      obtain ⟨hel, hcard⟩ := hJR'.sylow_two_of_nonabelian (exists_mul_ne hL) PL
      refine ⟨fun t ht => ?_, by omega⟩
      have h1 : (⟨t, ht⟩ : (PL : Subgroup L)) ^ 2 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        exact (Monoid.order_dvd_exponent _).trans hel.exponent_dvd_p
      simpa using congrArg Subtype.val h1
  refine ⟨hZ, fun t ht => ?_, ?_⟩
  · have := hexp ⟨t, ht.2⟩ ((hmemPL _).mpr ht.1)
    simpa using congrArg Subtype.val this
  · have hne : (PL : Subgroup L) ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hcard
      omega
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    refine ⟨((u : L) : Q), ⟨(hmemPL u).mp u.2, (u : L).2⟩, fun h' => hu1 ?_⟩
    exact Subtype.ext (Subtype.ext h')

theorem typeII (hII : IsGoldTypeII L) :
    (∃ x ∈ B ⊓ L, ∃ y ∈ L, x * y ≠ y * x) ∧
    B ⊓ L ≤ (Subgroup.center L).map L.subtype ⊔ Omega1 ((P : Subgroup Q) ⊓ L) ∧
    ∀ a ∈ B, ∃ x ∈ B ⊓ L, ∀ y ∈ L, a⁻¹ * y * a = x⁻¹ * y * x := by
  obtain ⟨hZ, hexp, t, ht, ht1⟩ := hc.typeII_facts hL hII
  have hΩ : Omega1 ((P : Subgroup Q) ⊓ L) = (P : Subgroup Q) ⊓ L := GoldType.omega1_eq_self hexp
  refine ⟨⟨t, ⟨hc.omega1_le hL (by rw [hΩ]; exact ht), ht.2⟩, ?_⟩, fun x hx => ?_,
    fun a ha => ?_⟩
  · by_contra hcomm
    push Not at hcomm
    have hcen : (⟨t, ht.2⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact ht1 (congrArg Subtype.val hcen)
  · refine le_sup_of_le_right (le_of_eq hΩ.symm) ⟨hc.le hx.1, hx.2⟩
  · obtain ⟨ℓ, hℓ, hact⟩ := hc.exists_act hL a
    have hℓP := hc.mem_sylow_of_act hL (hc.le ha) hℓ hact
    exact ⟨ℓ, ⟨hc.omega1_le hL (by rw [hΩ]; exact ⟨hℓP, hℓ⟩), hℓ⟩, hact⟩

omit [Finite Q] hc hL in
theorem commute_of_act {a ℓ : Q} (hact : ∀ x ∈ L, a⁻¹ * x * a = ℓ⁻¹ * x * ℓ) {x : Q}
    (hx : x ∈ L) : (a * ℓ⁻¹) * x = x * (a * ℓ⁻¹) := by
  calc (a * ℓ⁻¹) * x = a * (ℓ⁻¹ * x * ℓ) * ℓ⁻¹ := by group
    _ = a * (a⁻¹ * x * a) * ℓ⁻¹ := by rw [hact x hx]
    _ = x * (a * ℓ⁻¹) := by group

theorem typeI (hI : IsGoldTypeI L) :
    (∃ x ∈ B ⊓ L, ∃ y ∈ L, x * y ≠ y * x) ∧
    B ⊓ L ≤ (Subgroup.center L).map L.subtype ⊔ Omega1 ((P : Subgroup Q) ⊓ L) ∧
    ∀ a ∈ B, ∃ x ∈ B ⊓ L, ∀ y ∈ L, a⁻¹ * y * a = x⁻¹ * y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PL, hmemPL⟩ := hc.exists_sylow hL
  set BL : Subgroup L := B.subgroupOf L with hBL
  have hBLP : BL ≤ PL := fun x hx => (hmemPL x).mpr (hc.le hx)
  have hBLc : ∀ a ∈ BL, ∀ b ∈ BL, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hc.comm _ ha _ hb)
  have hBLcl : fusionStronglyClosed (BL : Set L) PL := by
    intro a ha g hg
    have hg' : ((g⁻¹ * a * g : L) : Q) ∈ (P : Subgroup Q) := (hmemPL _).mp hg
    exact hc.closed a ha g hg'
  have hnot : ¬ BL ≤ Subgroup.center L := by
    intro hle
    apply hc.not_le_centralizer hL
    intro a ha
    obtain ⟨ℓ, hℓ, hact⟩ := hc.exists_act hL a
    have hℓP := hc.mem_sylow_of_act hL (hc.le ha) hℓ hact
    set ℓ' : L := ⟨ℓ, hℓ⟩ with hℓ'
    have hℓ'P : ℓ' ∈ (PL : Subgroup L) := (hmemPL _).mpr hℓP
    have h1 : ∀ t ∈ (PL : Subgroup L), ℓ'⁻¹ * t * ℓ' * t⁻¹ ∈ Subgroup.center L := by
      intro t ht
      apply hle
      show ((ℓ'⁻¹ * t * ℓ' * t⁻¹ : L) : Q) ∈ B
      have htP : (t : Q) ∈ (P : Subgroup Q) := (hmemPL t).mp ht
      have e : ((ℓ'⁻¹ * t * ℓ' * t⁻¹ : L) : Q) = a⁻¹ * ((t : Q) * a * (t : Q)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hℓ']
        rw [← hact t t.2]
        group
      rw [e]
      refine B.mul_mem (B.inv_mem ha) ?_
      have := conj_mem_of_stronglyClosed hc.le hc.closed ((P : Subgroup Q).inv_mem htP) ha
      rwa [inv_inv] at this
    have h2 : ∀ n ∈ Subgroup.normalizer ((PL : Subgroup L) : Set L),
        ℓ'⁻¹ * (n⁻¹ * ℓ' * n) ∈ Subgroup.center L := by
      intro n hn
      apply hle
      show ((ℓ'⁻¹ * (n⁻¹ * ℓ' * n) : L) : Q) ∈ B
      have e : ((ℓ'⁻¹ * (n⁻¹ * ℓ' * n) : L) : Q) = a⁻¹ * ((n : Q)⁻¹ * a * n) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hℓ']
        have h3 := hact (n : Q)⁻¹ (L.inv_mem n.2)
        calc ℓ⁻¹ * ((n : Q)⁻¹ * ℓ * n) = (ℓ⁻¹ * (n : Q)⁻¹ * ℓ) * n := by group
          _ = (a⁻¹ * (n : Q)⁻¹ * a) * n := by rw [h3]
          _ = a⁻¹ * ((n : Q)⁻¹ * a * n) := by group
      rw [e]
      have hnaP : (n : Q)⁻¹ * a * n ∈ (P : Subgroup Q) := by
        have hc' := commute_of_act hact (L.inv_mem n.2)
        have e2 : (n : Q)⁻¹ * a * n = (a * ℓ⁻¹) * ((n : Q)⁻¹ * ℓ * n) := by
          calc (n : Q)⁻¹ * a * n = ((n : Q)⁻¹ * (a * ℓ⁻¹)) * ℓ * n := by group
            _ = ((a * ℓ⁻¹) * (n : Q)⁻¹) * ℓ * n := by rw [hc']
            _ = (a * ℓ⁻¹) * ((n : Q)⁻¹ * ℓ * n) := by group
        rw [e2]
        refine (P : Subgroup Q).mul_mem ((P : Subgroup Q).mul_mem (hc.le ha)
          ((P : Subgroup Q).inv_mem hℓP)) ?_
        have h4 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) ℓ').mp hℓ'P
        rw [inv_inv] at h4
        exact (hmemPL _).mp h4
      exact B.mul_mem (B.inv_mem ha) (hc.closed a ha n hnaP)
    have hcen := mem_center_of_fixed hI PL hℓ'P h1 h2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have e := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨x, hx⟩)
    simp only [Subgroup.coe_mul, hℓ'] at e
    have h5 : ℓ⁻¹ * x * ℓ = x := by
      calc ℓ⁻¹ * x * ℓ = ℓ⁻¹ * (x * ℓ) := by group
        _ = ℓ⁻¹ * (ℓ * x) := by rw [e]
        _ = x := by group
    calc x * a = a * (a⁻¹ * x * a) := by group
      _ = a * x := by rw [hact x hx, h5]
  have hQb : fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  set P' : Sylow 2 (L ⧸ Subgroup.center L) := PL.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup (L ⧸ Subgroup.center L)) = (PL : Subgroup L).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D, h⟩ := exists_borelSetup hQb P'
  have hmap := map_eq_sylowCenter hI PL hBLP hBLc hBLcl hnot h
  have hker : ∀ {y : L}, y ∈ Subgroup.center L ↔ π y = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']
  have hZ2 : IsPGroup 2 (Subgroup.center L) := (N8d Q hc.odd).1 L hL
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp hnot
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hxZ
    push Not at hxZ
    obtain ⟨y, hy⟩ := hxZ
    exact ⟨x, ⟨hx, x.2⟩, y, y.2, fun h' => hy (Subtype.ext h'.symm)⟩
  · intro x hx
    set x' : L := ⟨x, hx.2⟩ with hx'
    obtain ⟨z, hz, hxz⟩ := exists_sq_eq hI PL hBLc hmap (x := x') hx.1
    have hzc : ∀ y : L, z⁻¹ * y = y * z⁻¹ := fun y =>
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) y).symm
    set u : L := x' * z⁻¹ with hu
    have hu2 : u ^ 2 = 1 := by
      rw [hu, sq]
      calc x' * z⁻¹ * (x' * z⁻¹) = x' * (z⁻¹ * x') * z⁻¹ := by group
        _ = x' * (x' * z⁻¹) * z⁻¹ := by rw [hzc]
        _ = x' ^ 2 * (z ^ 2)⁻¹ := by rw [sq x', sq z]; group
        _ = 1 := by rw [hxz, mul_inv_cancel]
    have huP : u ∈ (PL : Subgroup L) :=
      (PL : Subgroup L).mul_mem (hBLP hx.1) ((PL : Subgroup L).inv_mem
        (le_sylow_of_normal PL hZ2 hz))
    have e : x = (u : Q) * (z : Q) := by
      rw [hu]
      simp [hx']
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure
      ⟨⟨(hmemPL u).mp huP, u.2⟩, by simpa using congrArg Subtype.val hu2⟩))
      (Subgroup.mem_sup_left ⟨z, hz, rfl⟩)
  · intro a ha
    set Zhat : Subgroup Q :=
      ((sylowCenter (P' : Subgroup (L ⧸ Subgroup.center L))).comap π).map L.subtype with hZhat
    have hZhatL : Zhat ≤ L := Subgroup.map_subtype_le _
    have hBM : B ≤ actsBy L Zhat hZhatL := by
      rw [hc.bar]
      refine sup_le (fun q hq => ⟨1, Zhat.one_mem, fun x _ => ?_⟩) ?_
      · have := Subgroup.mem_center_iff.1 (hc.central hq) x
        calc q⁻¹ * x * q = q⁻¹ * (x * q) := by group
          _ = q⁻¹ * (q * x) := by rw [this]
          _ = 1⁻¹ * x * 1 := by group
      · refine (Subgroup.closure_le _).mpr ?_
        rintro u ⟨⟨huP, -⟩, hu2⟩
        obtain ⟨ℓ, hℓ, hact⟩ := hc.exists_act hL u
        have hℓP := hc.mem_sylow_of_act hL huP hℓ hact
        have hℓ2 : (⟨ℓ, hℓ⟩ : L) ^ 2 ∈ Subgroup.center L := by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          have h1 := act_pow hℓ hact 2 y y.2
          rw [hu2, inv_one, one_mul, mul_one] at h1
          change (y : Q) * ℓ ^ 2 = ℓ ^ 2 * y
          calc (y : Q) * ℓ ^ 2 = ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * y * ℓ ^ 2) := by group
            _ = ℓ ^ 2 * y := by rw [← h1]
        refine ⟨ℓ, ⟨⟨ℓ, hℓ⟩, ?_, rfl⟩, hact⟩
        show π ⟨ℓ, hℓ⟩ ∈ sylowCenter (P' : Subgroup (L ⧸ Subgroup.center L))
        refine h.inv _ ?_ ?_
        · rw [hP']
          exact ⟨_, (hmemPL _).mpr hℓP, rfl⟩
        · rw [← map_pow, ← hker]
          exact hℓ2
    obtain ⟨ℓ, ⟨ℓ', hℓ'Z, rfl⟩, hact⟩ := hBM ha
    have hℓ'Z' : π ℓ' ∈ sylowCenter (P' : Subgroup (L ⧸ Subgroup.center L)) := hℓ'Z
    rw [← hmap] at hℓ'Z'
    obtain ⟨x', hx', hxℓ⟩ := hℓ'Z'
    refine ⟨x', ⟨hx', x'.2⟩, fun y hy => ?_⟩
    rw [hact y hy]
    have hzc : x'⁻¹ * ℓ' ∈ Subgroup.center L := hker.mpr (by
      rw [map_mul, map_inv, hxℓ, inv_mul_cancel])
    have key : ℓ'⁻¹ * ⟨y, hy⟩ * ℓ' = x'⁻¹ * ⟨y, hy⟩ * x' := by
      have hzy := Subgroup.mem_center_iff.mp hzc (x'⁻¹ * ⟨y, hy⟩ * x')
      calc ℓ'⁻¹ * ⟨y, hy⟩ * ℓ' = (x'⁻¹ * ℓ')⁻¹ * ((x'⁻¹ * ⟨y, hy⟩ * x') * (x'⁻¹ * ℓ')) := by
            group
        _ = (x'⁻¹ * ℓ')⁻¹ * ((x'⁻¹ * ℓ') * (x'⁻¹ * ⟨y, hy⟩ * x')) := by rw [hzy]
        _ = x'⁻¹ * ⟨y, hy⟩ * x' := by group
    have := congrArg Subtype.val key
    simpa using this

theorem analysis :
    (∃ x ∈ B ⊓ L, ∃ y ∈ L, x * y ≠ y * x) ∧
    B ⊓ L ≤ (Subgroup.center L).map L.subtype ⊔ Omega1 ((P : Subgroup Q) ⊓ L) ∧
    ∀ a ∈ B, ∃ x ∈ B ⊓ L, ∀ y ∈ L, a⁻¹ * y * a = x⁻¹ * y * x := by
  rcases hc.types L hL with hI | hII
  · exact hc.typeI hL hI
  · exact hc.typeII hL hII

end SConf

end Conf

end G3a

end CFSG.Goldschmidt
