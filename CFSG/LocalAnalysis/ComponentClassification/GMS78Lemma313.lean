module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Facts

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Lemma313 (L T : Subgroup G) (q : ℕ) : Prop where
  cover : ∀ v ∈ gmsV L T, v ∉ gmsA L T ↔ ∃ Q ∈ gmsDelta L T, v ∈ Q ∧ v ≠ 1
  inf_eq_bot : ∀ Q₁ ∈ gmsDelta L T, ∀ Q₂ ∈ gmsDelta L T, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥
  card_eq : Nat.card (gmsDelta L T) = q
  stronglyClosed : ∀ a ∈ gmsA L T, ∀ g : G, g * a * g⁻¹ ∈ gmsV L T → g * a * g⁻¹ ∈ gmsA L T
  twoTransitive : ∀ Q₁ ∈ gmsDelta L T, ∀ Q₂ ∈ gmsDelta L T, ∀ Q₁' ∈ gmsDelta L T,
    ∀ Q₂' ∈ gmsDelta L T, Q₁ ≠ Q₂ → Q₁' ≠ Q₂' → ∃ n ∈ normalizer (gmsV L T : Set G),
      rightConjugate Q₁ n = Q₁' ∧ rightConjugate Q₂ n = Q₂'

@[expose] def DeltaPair (L T : Subgroup G) : Prop :=
  (∃ x, rightConjugate (T ⊓ centralizer (L : Set G)) x = gmsA L T) ∧
    ∀ x, rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ gmsV L T →
      rightConjugate (T ⊓ centralizer (L : Set G)) x = T ⊓ centralizer (L : Set G) ∨
        rightConjugate (T ⊓ centralizer (L : Set G)) x = gmsA L T

theorem exists_mem_normalizer_of_not_isSylowOf {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPG : ¬ IsSylowOf 2 P ⊤) :
    ∃ S : Sylow 2 G, P ≤ S ∧ ∃ z ∈ (S : Subgroup G), z ∈ normalizer (P : Set G) ∧ z ∉ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hne : P ≠ (S : Subgroup G) := by
    intro hPS'
    apply hPG
    rw [isSylowOf_iff]
    refine ⟨le_top, hP, ?_⟩
    rw [hPS', relIndex_top_right]
    exact Sylow.not_dvd_index S
  set I := P.subgroupOf (S : Subgroup G) with hI
  have hIlt : I < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hPS fun x hx => ?_)
    have : (⟨x, hx⟩ : (S : Subgroup G)) ∈ I := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup G)) I hIlt
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : G) ∈ normalizer (P : Set G) := by
    have : x ∈ (normalizer (P : Set G)).subgroupOf (S : Subgroup G) := by
      rw [subgroupOf_normalizer_eq hPS]
      exact hxN
    exact mem_subgroupOf.mp this
  exact ⟨S, hPS, x, x.2, hxN', fun hx => hxI (mem_subgroupOf.mpr hx)⟩

namespace Sec3

variable {L T : Subgroup G}

theorem commutator_le_inf (h : Sec3 G L T) :
    ⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ ≤ gmsV L T ⊓ L := by
  rw [commutator_le]
  intro g hg v hv
  obtain ⟨hgL, hgN⟩ := mem_inf.mp hg
  have hVT : gmsV L T ≤ T := sup_le (inf_le_left.trans inf_le_left) inf_le_left
  have hvM : v ∈ normalizer (L : Set G) := h.sylow.le (hVT hv)
  rw [commutatorElement_def]
  refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hgN v).mp hv) (inv_mem hv), ?_⟩
  have h1 : v * g⁻¹ * v⁻¹ ∈ L := (mem_normalizer_iff.mp hvM g⁻¹).mp (inv_mem hgL)
  rw [show g * v * g⁻¹ * v⁻¹ = g * (v * g⁻¹ * v⁻¹) by group]
  exact mul_mem hgL h1

theorem mem_of_mem_normalizer (h : Sec3 G L T) {S : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    {y : G} (hyS : y ∈ S) (hyM : y ∈ normalizer (L : Set G)) : y ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (T ⊔ zpowers y : Subgroup G) := hS.to_le (sup_le hTS (zpowers_le.mpr hyS))
  have heq := h.sylow.eq_of_le le_sup_left (sup_le h.sylow.le (zpowers_le.mpr hyM)) hP
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

theorem exists_mem_normalizer_not_mem (h : Sec3 G L T) (hTG : ¬ IsSylowOf 2 T ⊤) :
    ∃ y ∈ normalizer (T : Set G), y ∉ normalizer (L : Set G) := by
  obtain ⟨S, hTS, z, hzS, hzN, hzT⟩ :=
    exists_mem_normalizer_of_not_isSylowOf h.sylow.isPGroup hTG
  exact ⟨z, hzN, fun hzM => hzT (h.mem_of_mem_normalizer S.isPGroup' hTS hzS hzM)⟩

theorem exists_mem_normalizer_sq_mem (h : Sec3 G L T) (hTG : ¬ IsSylowOf 2 T ⊤) :
    ∃ S : Sylow 2 G, T ≤ S ∧ ∃ y ∈ (S : Subgroup G), y ∈ normalizer (T : Set G) ∧
      y ∉ normalizer (L : Set G) ∧ y ^ 2 ∈ T := by
  classical
  obtain ⟨S, hTS, z, hzS, hzN, hzT⟩ :=
    exists_mem_normalizer_of_not_isSylowOf h.sylow.isPGroup hTG
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨z, hzS⟩
  have hn' : z ^ 2 ^ n ∈ T := by
    have := congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [this]
    exact one_mem _
  have hex : ∃ j, z ^ 2 ^ j ∈ T := ⟨n, hn'⟩
  set j := Nat.find hex with hj
  have hjT : z ^ 2 ^ j ∈ T := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hjT
    exact hzT hjT
  set y := z ^ 2 ^ (j - 1) with hy
  have hyT : y ∉ T := Nat.find_min hex (by omega)
  have hy2 : y ^ 2 ∈ T := by
    rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
    exact hjT
  have hyS : y ∈ (S : Subgroup G) := pow_mem hzS _
  refine ⟨S, hTS, y, hyS, pow_mem hzN _, fun hyM => hyT ?_, hy2⟩
  exact h.mem_of_mem_normalizer S.isPGroup' hTS hyS hyM

namespace Facts

variable {q : ℕ}

theorem commutator_eq_gmsA (hX : Facts L T q) (h : Sec3 G L T) :
    ⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ = gmsA L T := by
  have hle := h.commutator_le_inf.trans (h.gmsV_inf_eq hX.oddCenter).le
  refine le_antisymm hle ?_
  have hZ := hX.oddCenter
  obtain ⟨k, hB⟩ := hX.borel
  have hT₁syl : IsSylowOf 2 (T ⊓ L) L := h.isSylowOf_T₁
  obtain ⟨hA₁card, hA₁sq, -⟩ := hX.sylow h
  obtain ⟨y, hy, -, htrans, -⟩ := exists_torus hZ hT₁syl hB
  have hyV : y ∈ L ⊓ normalizer (gmsV L T : Set G) :=
    mem_inf.mpr ⟨(mem_inf.mp hy).1, inf_normalizer_le_normalizer hy⟩
  have hq4 := hX.four_le
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ gmsA L T, a ≠ 1 := by
    have h1 : 1 < Nat.card (gmsA L T) := by rw [hA₁card]; omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨a, ha, fun h1 => ha1 (Subtype.ext h1)⟩
  obtain ⟨b, hb, hbz⟩ : ∃ b ∈ gmsA L T, b ∉ zpowers a := by
    by_contra hall
    push Not at hall
    have hle : gmsA L T ≤ zpowers a := hall
    have h1 := card_le_of_le hle
    rw [Nat.card_zpowers, hA₁card, orderOf_eq_prime (hA₁sq a ha) ha1] at h1
    omega
  have hb1 : b ≠ 1 := fun h1 => hbz (h1 ▸ one_mem _)
  have hba : b ≠ a := fun h1 => hbz (h1 ▸ mem_zpowers a)
  obtain ⟨c, hc, hyc⟩ : ∃ c ∈ gmsA L T, y * c ≠ c * y := by
    by_contra hall
    push Not at hall
    obtain ⟨m, hm⟩ := htrans a ha b hb ha1 hb1
    have hc : y ^ m * a = a * y ^ m := Commute.pow_left (hall a ha) m
    apply hba
    rw [← hm, mul_assoc, ← hc, inv_mul_cancel_left]
  set V₀ := ⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ with hV₀def
  have hc0 : ⁅y, c⁆ ∈ V₀ := commutator_mem_commutator hyV (mem_sup_left hc)
  have hc1 : ⁅y, c⁆ ≠ 1 := fun h1 => hyc (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hV₀n : ∀ n ∈ L ⊓ normalizer (gmsV L T : Set G), rightConjugate V₀ n = V₀ := by
    intro n hn
    change V₀.map (MulAut.conj n⁻¹).toMonoidHom = V₀
    rw [hV₀def, map_commutator]
    have h1 : (L ⊓ normalizer (gmsV L T : Set G)).map (MulAut.conj n⁻¹).toMonoidHom =
        L ⊓ normalizer (gmsV L T : Set G) := (rightConjugate_eq_self_iff _ n).mpr (le_normalizer hn)
    have h2 : (gmsV L T).map (MulAut.conj n⁻¹).toMonoidHom = gmsV L T :=
      (rightConjugate_eq_self_iff _ n).mpr (mem_inf.mp hn).2
    rw [h1, h2]
  intro b' hb'
  by_cases hb'1 : b' = 1
  · rw [hb'1]
    exact one_mem _
  obtain ⟨m, hm⟩ := htrans _ (hle hc0) b' hb' hc1 hb'1
  rw [← hV₀n _ (pow_mem hyV m), mem_rightConjugate_iff, ← hm]
  simpa [mul_assoc] using hc0

theorem exists_le_of_mem
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {a : G} (ha : a ∈ gmsA L T)
    (ha1 : a ≠ 1) {z : G} (haz : a ∈ rightConjugate (T ⊓ centralizer (L : Set G)) z) :
    ∃ x, rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ gmsV L T ∧
      a ∈ rightConjugate (T ⊓ centralizer (L : Set G)) x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVel, -, hVC, -⟩ := hX.vFacts h hF
  have hNK := AS76b.normalizer_centralizer_eq h.hyp.standard
  have hKz := AS76b.tightlyEmbedded_rightConjugate
    (AS76b.tightlyEmbedded_centralizer h.hyp.standard) z
  have haV : a ∈ gmsV L T := mem_sup_left ha
  have haK : a ∈ rightConjugate (centralizer (L : Set G)) z :=
    (map_mono inf_le_right : rightConjugate (T ⊓ centralizer (L : Set G)) z ≤
      rightConjugate (centralizer (L : Set G)) z) haz
  have hord : orderOf a = 2 := orderOf_eq_prime (hVel.2 a haV) ha1
  have hZ2 : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hZ1 : zpowers a ≠ ⊥ := fun hb => ha1 (by
    have h1 : a ∈ zpowers a := mem_zpowers a
    rwa [hb, mem_bot] at h1)
  have hNZ := normalizer_two_subgroup_le _ _ hKz hZ2 (zpowers_le.mpr haK) hZ1
  have hWN : gmsW L T ≤ normalizer (rightConjugate (centralizer (L : Set G)) z : Set G) :=
    (le_centralizer_iff.mpr (zpowers_le.mpr (hVC haV))).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNZ)
  have hTz : IsSylowOf 2 (rightConjugate T z)
      (normalizer (rightConjugate (centralizer (L : Set G)) z : Set G)) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate h.sylow z
    have h2 : rightConjugate (normalizer (L : Set G)) z =
        normalizer (rightConjugate (centralizer (L : Set G)) z : Set G) := by
      ext x
      rw [mem_rightConjugate_iff, AS76b.mem_normalizer_rightConjugate_iff, hNK]
    rwa [h2] at h1
  have hW2 : IsPGroup 2 (gmsW L T) := h.sylow.isPGroup.to_le (sup_le inf_le_left inf_le_left)
  obtain ⟨P, hP, hWP⟩ := AS76b.exists_isSylowOf_le hWN hW2
  obtain ⟨c, hc, hPc⟩ := IsSylowOf.exists_map_conj hTz hP
  rw [Sec3.map_conj_rightConjugate] at hPc
  set u := z * c⁻¹ with hu
  have hWu : rightConjugate (gmsW L T) u⁻¹ ≤ T := by
    intro w hw
    rw [mem_rightConjugate_iff] at hw
    have h1 := hWP hw
    rw [hPc, mem_rightConjugate_iff] at h1
    simpa [mul_assoc] using h1
  have hVu : rightConjugate (gmsV L T) u = gmsV L T :=
    (rightConjugate_eq_self_iff _ _).mpr (by
      simpa using inv_mem ((rightConjugate_eq_self_iff _ _).mp (hX.weakClosure u⁻¹ hWu)))
  have haP : a ∈ rightConjugate T u := by
    rw [← hPc]
    exact hWP (mem_sup_left (mem_inf.mp ha).1)
  have hKu : rightConjugate (centralizer (L : Set G)) u =
      rightConjugate (centralizer (L : Set G)) z := by
    rw [hu, ← rightConjugate_mul]
    exact (rightConjugate_eq_self_iff _ _).mpr (inv_mem hc)
  have haT₀ : a ∈ rightConjugate (T ⊓ centralizer (L : Set G)) u := by
    rw [AschbacherTheorem3.rightConjugate_inf, hKu]
    exact mem_inf.mpr ⟨haP, haK⟩
  have hT₀u : rightConjugate (T ⊓ centralizer (L : Set G)) u ≤ gmsV L T := by
    calc rightConjugate (T ⊓ centralizer (L : Set G)) u ≤ rightConjugate (gmsV L T) u :=
          map_mono le_sup_right
      _ = gmsV L T := hVu
  exact ⟨u, hT₀u, haT₀⟩

theorem not_deltaPair_of_lt
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation)
    (hlt : Nat.card (gmsA L T) < Nat.card (T ⊓ L : Subgroup G)) : ¬ DeltaPair L T := by
  rintro ⟨-, h3⟩
  obtain ⟨-, -, hinvA⟩ := hX.sylow h
  obtain ⟨y, hyT, hyM⟩ := h.exists_mem_normalizer_not_mem (hX.not_isSylowOf_top h hF)
  have hyW : y ∈ normalizer (gmsW L T : Set G) := h.normalizer_le hF hyT
  have hWy : rightConjugate (gmsW L T) y ≤ T := by
    rw [(rightConjugate_eq_self_iff _ y).mpr hyW]
    exact sup_le inf_le_left inf_le_left
  have hVy := hX.weakClosure y hWy
  have hT₀y : rightConjugate (T ⊓ centralizer (L : Set G)) y ≤ gmsV L T := by
    calc rightConjugate (T ⊓ centralizer (L : Set G)) y ≤ rightConjugate (gmsV L T) y :=
          map_mono le_sup_right
      _ = gmsV L T := hVy
  rcases h3 y hT₀y with h4 | h4
  · apply hyM
    have hNT₀ : normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ≤
        normalizer (L : Set G) := by
      have h1 := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
      rwa [rightConjugate_one, rightConjugate_one] at h1
    exact hNT₀ ((rightConjugate_eq_self_iff _ y).mp h4)
  ·
    obtain ⟨a, ha, haA⟩ : ∃ a ∈ T ⊓ L, a ∉ gmsA L T := by
      by_contra hall
      push Not at hall
      have h1 := card_le_of_le (show T ⊓ L ≤ gmsA L T from hall)
      omega
    have ha2 : a ^ 2 ≠ 1 := fun h1 => haA (hinvA a ha h1)
    have ha2A : a ^ 2 ∈ gmsA L T := hX.sq_mem a ha
    rw [← h4, mem_rightConjugate_iff] at ha2A
    have hya : y * a * y⁻¹ ∈ gmsW L T := (mem_normalizer_iff.mp hyW a).mp (mem_sup_left ha)
    have hT₁N : T ⊓ L ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
      fun x hx => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
        (mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2).symm)
    obtain ⟨a', ha', t', ht', heq⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hT₁N hya
    have hc : a' * t' = t' * a' := mem_centralizer_iff.mp (mem_inf.mp ht').2 a' (mem_inf.mp ha').2
    have hT₀el := h.isElemAbelian_T₀ hF
    have hsq : (y * a * y⁻¹) ^ 2 = a' ^ 2 := by
      rw [← heq, Commute.mul_pow hc 2, hT₀el.2 t' ht', mul_one]
    have hya2 : y * a ^ 2 * y⁻¹ = (y * a * y⁻¹) ^ 2 := by
      simp only [sq]
      group
    have hmem : y * a ^ 2 * y⁻¹ ∈ (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) := by
      refine mem_inf.mpr ⟨?_, ha2A⟩
      rw [hya2, hsq]
      exact (mem_inf.mp (hX.sq_mem a' ha')).1
    rw [h.inf_eq_bot_of_odd hX.oddCenter, mem_bot] at hmem
    apply ha2
    calc a ^ 2 = y⁻¹ * (y * a ^ 2 * y⁻¹) * y := by group
      _ = 1 := by rw [hmem]; group

theorem lemma313_of_not_pair
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) (hne : ¬ DeltaPair L T) :
    Lemma313 L T q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₀, hh₀M, hD, hDK⟩ := h.exists_conj hF
  obtain ⟨hVcard, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨hA₁card, -, -⟩ := hX.sylow h
  have h36 := hX.lemma36 h hF hh₀M hD hDK
  rw [hX.commutator_eq_gmsA h] at h36
  have hV2 : IsPGroup 2 (gmsV L T) := fun v => ⟨1, Subtype.ext (by simpa using hVel.2 v v.2)⟩
  rcases h36 with ⟨hDA, -, h3⟩ | ⟨-, hcov, h2tr⟩
  · refine (hne ⟨⟨h₀, hDA.symm⟩, fun x hx => ?_⟩).elim
    rw [hDA]
    exact h3 x hx
  ·
    have hcov' : ∀ v ∈ gmsV L T, v ∉ gmsA L T ↔ ∃ Q ∈ gmsDelta L T, v ∈ Q ∧ v ≠ 1 := by
      intro v hv
      rw [hcov v hv]
      constructor
      · rintro ⟨x, hxV, hvx, hv1⟩
        exact ⟨_, ⟨⟨x, rfl⟩, hxV⟩, hvx, hv1⟩
      · rintro ⟨Q, ⟨⟨x, rfl⟩, hQV⟩, hvQ, hv1⟩
        exact ⟨x, hQV, hvQ, hv1⟩
    have hinf : ∀ Q₁ ∈ gmsDelta L T, ∀ Q₂ ∈ gmsDelta L T, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥ := by
      rintro Q₁ ⟨⟨x₁, rfl⟩, h₁⟩ Q₂ ⟨⟨x₂, rfl⟩, h₂⟩ hne
      exact h.inf_eq_bot_of_conj hV2 h₁ h₂ hne
    refine ⟨hcov', hinf, ?_, ?_, ?_⟩
    ·
      have : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
        SetLike.coe_injective
      have : Fintype (gmsDelta L T) := Fintype.ofFinite _
      have hcount := card_mul_eq_of_cover (ι := gmsDelta L T) (W := gmsA L T) le_sup_left
        (fun Q => Q.1) (fun i j hij => hinf i.1 i.2 j.1 j.2 fun h1 => hij (Subtype.ext h1))
        (fun i => i.2.2) (c := Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
        (fun i => by
          obtain ⟨⟨x, hx⟩, -⟩ := i.2
          show Nat.card i.1 = _
          rw [← hx, rightConjugate_card])
        (fun v hv => by
          rw [hcov' v hv]
          constructor
          · rintro ⟨Q, hQ, hvQ, hv1⟩
            exact ⟨⟨Q, hQ⟩, hvQ, hv1⟩
          · rintro ⟨⟨Q, hQ⟩, hvQ, hv1⟩
            exact ⟨Q, hQ, hvQ, hv1⟩)
      have ht1 : 1 < Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr h.T₀_ne_bot
      rw [hVcard, hA₁card, ← Nat.mul_sub_one] at hcount
      rw [Nat.card_eq_fintype_card]
      exact Nat.eq_of_mul_eq_mul_right (by omega) hcount
    ·
      intro a ha g hga
      by_contra hgaA
      have ha1 : a ≠ 1 := fun h1 => hgaA (by rw [h1, mul_one, mul_inv_cancel]; exact one_mem _)
      obtain ⟨Q, ⟨⟨x, rfl⟩, -⟩, hgx, -⟩ := (hcov' _ hga).mp hgaA
      have hax : a ∈ rightConjugate (T ⊓ centralizer (L : Set G)) (x * g) := by
        rw [mem_rightConjugate_iff]
        rw [mem_rightConjugate_iff] at hgx
        simpa [mul_assoc] using hgx
      obtain ⟨x', hx'V, hax'⟩ := hX.exists_le_of_mem h hF ha ha1 hax
      exact ((hcov' a (mem_sup_left ha)).mpr ⟨_, ⟨⟨x', rfl⟩, hx'V⟩, hax', ha1⟩) ha
    ·
      rintro Q₁ ⟨⟨x₁, rfl⟩, h₁⟩ Q₂ ⟨⟨x₂, rfl⟩, h₂⟩ Q₁' ⟨⟨x₁', rfl⟩, h₁'⟩ Q₂' ⟨⟨x₂', rfl⟩, h₂'⟩
        hne hne'
      exact h2tr x₁ x₂ x₁' x₂' h₁ h₂ h₁' h₂' hne hne'

theorem lemma313
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation)
    (hlt : Nat.card (gmsA L T) < Nat.card (T ⊓ L : Subgroup G)) : Lemma313 L T q :=
  hX.lemma313_of_not_pair h hF (hX.not_deltaPair_of_lt h hF hlt)

end Facts

end Sec3

end CFSG.ComponentClassification.GMS78
