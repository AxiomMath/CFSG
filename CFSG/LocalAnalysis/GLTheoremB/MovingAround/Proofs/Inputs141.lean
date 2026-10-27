module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs183eqv

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped commutatorElement

@[expose] def Input14_1Core : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ →
    ∀ B : Subgroup Y, B ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 B →
      B ⊓ Subgroup.centralizer (K : Set Y) = ⊥ → B ≠ ⊥ →
      (Nat.card ↥B = 3 → IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)) →
    ∀ J : Subgroup Y, GLAPComponent 3 (K ⊓ Subgroup.centralizer (B : Set Y)) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∀ k : Y, k ∈ K → k ∈ Subgroup.centralizer (B : Set Y) → IsPGroup 2 ↥(Subgroup.zpowers k) →
      InducesInner 3 J k

section Elementary

theorem isPGroup_center_of_core_bot {X : Type} [Group X] [Finite X] (h : GLAPPrimeCore 3 X = ⊥) :
    IsPGroup 3 ↥(Subgroup.center X) := by
  rintro ⟨z, hz⟩
  have hn : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨a, m, hm3, hzm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  set w := z ^ (3 ^ a) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (hzm ▸ Dvd.intro m rfl), hzm,
      Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hwc : w ∈ Subgroup.center X := Subgroup.pow_mem _ hz _
  have hnorm : (Subgroup.zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc := Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hwc j) g
    have e : g * w ^ j * g⁻¹ = w ^ j := by rw [hc]; group
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) j
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers w)) := by
    rw [Nat.card_zpowers, hwo]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3
  have hle : Subgroup.zpowers w ≤ CFSG.pPrimeCore 3 X := le_sSup ⟨hnorm, hcop⟩
  have hle' : Subgroup.zpowers w ≤ ⊥ := by
    have h' : CFSG.pPrimeCore 3 X = ⊥ := h
    rw [← h']
    exact hle
  rw [le_bot_iff, Subgroup.zpowers_eq_bot] at hle'
  exact ⟨a, Subtype.ext (by simpa [hw] using hle')⟩

theorem glaPPrimeCore_eq_bot_of_center {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 3 ↥(Subgroup.center ↥K))
    (h3 : 3 ∣ Nat.card ↥K) : GLAPPrimeCore 3 ↥K = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  by_cases htop : GLAPPrimeCore 3 ↥K = ⊤
  · exfalso
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3
  · have hle : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K := l119_normal_le_center hKq htop
    have hP : IsPGroup 3 ↥(GLAPPrimeCore 3 ↥K) := hZ.to_le hle
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
    have hn0 : n = 0 := by
      by_contra hne
      rw [hn] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (dvd_pow_self 3 hne)
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn

theorem three_dvd_card_of_isLThreeFour {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : 3 ∣ Nat.card ↥J := by
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hJt
  have h2 : Nat.card (barOf 3 J) = Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) *
      Nat.card (Subgroup.center (barOf 3 J)) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ↥J = Nat.card (barOf 3 J) * Nat.card (GLAPPrimeCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h3, h2, h1]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by norm_num) _) _

theorem le_of_perfect_of_le_sup {G : Type} [Group G] {A Z P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPA : P ≤ A ⊔ Z) (hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a)
    (hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) : P ≤ A := by
  have hcomm : ⁅A ⊔ Z, A ⊔ Z⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := Input183.mem_sup_of_commute hAZ hg₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := Input183.mem_sup_of_commute hAZ hg₂
    have e1 : a₁ * z₁ * (a₂ * z₂) = a₁ * a₂ * (z₁ * z₂) := by
      calc a₁ * z₁ * (a₂ * z₂) = a₁ * (z₁ * a₂) * z₂ := by group
        _ = a₁ * (a₂ * z₁) * z₂ := by rw [hAZ a₂ ha₂ z₁ hz₁]
        _ = a₁ * a₂ * (z₁ * z₂) := by group
    have e2 : a₂ * z₂ * (a₁ * z₁) = a₂ * a₁ * (z₁ * z₂) := by
      calc a₂ * z₂ * (a₁ * z₁) = a₂ * (z₂ * a₁) * z₁ := by group
        _ = a₂ * (a₁ * z₂) * z₁ := by rw [hAZ a₁ ha₁ z₂ hz₂]
        _ = a₂ * a₁ * (z₂ * z₁) := by group
        _ = a₂ * a₁ * (z₁ * z₂) := by rw [hZZ z₂ hz₂ z₁ hz₁]
    have e3 : ⁅a₁ * z₁, a₂ * z₂⁆ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by
      rw [commutatorElement_def]
      calc a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹
          = (a₁ * z₁ * (a₂ * z₂)) * (a₂ * z₂ * (a₁ * z₁))⁻¹ := by group
        _ = (a₁ * a₂ * (z₁ * z₂)) * (a₂ * a₁ * (z₁ * z₂))⁻¹ := by rw [e1, e2]
        _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by group
    rw [e3]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅A ⊔ Z, A ⊔ Z⁆ := Subgroup.commutator_mono hPA hPA
    _ ≤ A := hcomm

theorem mem_center_of_commutator_mem_center {Q : Type} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) {x : Q}
    (h : ∀ y : Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Q) : x ∈ Subgroup.center Q := by
  let φ : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, h y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y₁ y₂ => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (h y₂) y₁⁻¹
        show x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ = x * y₁ * x⁻¹ * y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹)
        calc x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹
            = x * y₁ * x⁻¹ * ((x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
          _ = x * y₁ * x⁻¹ * (y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹)) := by rw [hc]
          _ = x * y₁ * x⁻¹ * y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹) := by group }
  have hker : commutator Q ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hq.1] at hker
  refine Subgroup.mem_center_iff.2 fun y => ?_
  have h1 : φ y = 1 := hker (Subgroup.mem_top y)
  have h2 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : x * y = y * x := by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h2, one_mul]
  exact h3.symm

end Elementary

section Family

variable {G : Type} [Group G] [Finite G]

theorem pairwise_comm_of {𝒞 : Set (Subgroup G)}
    (hcomm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x) :
    Pairwise fun (i j : ↥𝒞) => ∀ x y : G, x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y :=
  fun i j hij x y hx hy => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx y hy

theorem noncommPiCoprod_conj {ι : Type} [Fintype ι] {H : ι → Subgroup G}
    (hc : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (f : ∀ i, H i) (i : ι)
    {y : G} (hy : y ∈ H i) :
    Subgroup.noncommPiCoprod hc f * y * (Subgroup.noncommPiCoprod hc f)⁻¹ = (f i : G) * y * (f i : G)⁻¹ := by
  classical
  have h1 : f * Pi.mulSingle i ⟨y, hy⟩ * f⁻¹ = Pi.mulSingle i (f i * ⟨y, hy⟩ * (f i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  have h2 := congrArg (Subgroup.noncommPiCoprod hc) h1
  rw [map_mul, map_mul, map_inv, Subgroup.noncommPiCoprod_mulSingle,
    Subgroup.noncommPiCoprod_mulSingle] at h2
  simpa using h2

theorem noncommPiCoprod_range_eq {𝒞 : Set (Subgroup G)} [Fintype ↥𝒞]
    (hc : Pairwise fun (i j : ↥𝒞) => ∀ x y : G, x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y) :
    (Subgroup.noncommPiCoprod (H := fun i : ↥𝒞 => (i : Subgroup G)) hc).range = sSup 𝒞 := by
  rw [Subgroup.noncommPiCoprod_range, sSup_eq_iSup']

theorem exists_pow_three_eq_one_of_mem_center {𝒞 : Set (Subgroup G)}
    (hcomm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (hZ : ∀ X ∈ 𝒞, IsPGroup 3 ↥(Subgroup.center ↥X)) {w : G}
    (hw : w ∈ sSup 𝒞 ⊓ Subgroup.centralizer ((sSup 𝒞 : Subgroup G) : Set G)) :
    ∃ a : ℕ, w ^ (3 ^ a) = 1 := by
  classical
  letI : Fintype ↥𝒞 := Fintype.ofFinite _
  have hc := pairwise_comm_of hcomm
  have hwr : w ∈ (Subgroup.noncommPiCoprod (H := fun i : ↥𝒞 => (i : Subgroup G)) hc).range := by
    rw [noncommPiCoprod_range_eq hc]
    exact hw.1
  obtain ⟨f, rfl⟩ := hwr
  have hfc : ∀ i : ↥𝒞, ∃ a : ℕ, (f i : G) ^ (3 ^ a) = 1 := by
    intro i
    have hcen : f i ∈ Subgroup.center ↥(i : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := noncommPiCoprod_conj hc f i y.2
      have h2 := Subgroup.mem_centralizer_iff.1 hw.2 (y : G)
        ((le_sSup i.2 : (i : Subgroup G) ≤ sSup 𝒞) y.2)
      have h3 : (f i : G) * y * (f i : G)⁻¹ = y := by
        rw [← h1, ← h2]
        group
      apply Subtype.ext
      show (y : G) * (f i : G) = (f i : G) * y
      calc (y : G) * (f i : G) = ((f i : G) * y * (f i : G)⁻¹) * (f i : G) := by rw [h3]
        _ = (f i : G) * y := by group
    obtain ⟨a, ha⟩ := hZ i.1 i.2 ⟨f i, hcen⟩
    refine ⟨a, ?_⟩
    have h1 := congrArg (fun z : ↥(Subgroup.center ↥(i : Subgroup G)) => ((z : ↥(i : Subgroup G)) : G)) ha
    simpa using h1
  choose a ha using hfc
  refine ⟨∑ i, a i, ?_⟩
  have hf : f ^ (3 ^ ∑ i, a i) = 1 := by
    funext i
    apply Subtype.ext
    have hdvd : 3 ^ a i ∣ 3 ^ ∑ j, a j :=
      pow_dvd_pow 3 (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    have h1 : orderOf (f i : G) ∣ 3 ^ ∑ j, a j := (orderOf_dvd_of_pow_eq_one (ha i)).trans hdvd
    simpa using orderOf_dvd_iff_pow_eq_one.1 h1
  rw [← map_pow, hf, map_one]

theorem sSup_le_normalizer_of_comm {𝒞 : Set (Subgroup G)}
    (hcomm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {X : Subgroup G} (hX : X ∈ 𝒞) : sSup 𝒞 ≤ Subgroup.normalizer (X : Set G) := by
  refine sSup_le fun X' hX' => ?_
  by_cases h : X' = X
  · subst h
    exact Subgroup.le_normalizer
  · intro y hy
    exact Input183.normalizer_of_commute fun x hx => hcomm X' hX' X hX h y hy x hx

theorem isComponentOf_sSup_of_comm {𝒞 : Set (Subgroup G)} (hq : ∀ X ∈ 𝒞, CFSG.Open.IsQuasisimple ↥X)
    (hcomm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {X : Subgroup G} (hX : X ∈ 𝒞) : IsComponentOf X (sSup 𝒞) := by
  have hle : X ≤ sSup 𝒞 := le_sSup hX
  exact ⟨hle, IsSubnormal.step hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
    (sSup_le_normalizer_of_comm hcomm hX)) (IsSubnormal.refl _), hq X hX⟩

theorem mem_normalizer_sSup {𝒞 : Set (Subgroup G)} {b : G} (hb : ∀ X ∈ 𝒞, GLBConj b X ∈ 𝒞)
    (hb' : ∀ X ∈ 𝒞, GLBConj b⁻¹ X ∈ 𝒞) :
    b ∈ Subgroup.normalizer ((sSup 𝒞 : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm ?_ ?_
  · unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hb X hX)
  · refine sSup_le fun X hX => ?_
    have e : GLBConj b (GLBConj b⁻¹ X) = X := by
      rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]
    rw [← e]
    exact gLBConj_mono b (le_sSup (hb' X hX))

theorem commutator_eq_self_of_isQuasisimple {H : Subgroup G} (h : CFSG.Open.IsQuasisimple ↥H) :
    ⁅H, H⁆ = H := by
  have h1 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1, h.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_centBar_of_mem_centralizer {J : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (J : Set G)) : c ∈ centBar 3 ⊤ J := by
  rw [Claims1245b.mem_centBar_forall_iff]
  refine ⟨Subgroup.mem_top _, Subgroup.centralizer_le_normalizer _ hc, fun l hl => ?_⟩
  have e : c * l * c⁻¹ * l⁻¹ = 1 := by
    rw [← Subgroup.mem_centralizer_iff.1 hc l hl]
    group
  rw [e]
  exact Subgroup.one_mem _

theorem conj_mem_centralizer_of_normalizer {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) y).1 hy
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hy'
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * y := by group

end Family

section Diag

variable {G : Type} [Group G] [Finite G]

theorem oprod_three {H : Type} [Group H] (f : ℕ → H) : Input183.oprod 3 f = f 0 * f 1 * f 2 := by
  have h3 : Input183.oprod 3 f = Input183.oprod 2 f * f 2 := Input183.oprod_succ 2 f
  have h2 : Input183.oprod 2 f = Input183.oprod 1 f * f 1 := Input183.oprod_succ 1 f
  have h1 : Input183.oprod 1 f = Input183.oprod 0 f * f 0 := Input183.oprod_succ 0 f
  rw [h3, h2, h1, Input183.oprod_zero, one_mul]

theorem diagSub_ker_le_center {X : Subgroup G} {s : G}
    (hc : ∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j, ∀ y ∈ Input183.orbA s X k,
      x * y = y * x) :
    (Inputs183eqv.diagSub s 3 X hc).ker ≤ Subgroup.center ↥X := by
  intro x hx
  rw [MonoidHom.mem_ker, Inputs183eqv.diagSub_apply, oprod_three] at hx
  set u := s ^ 1 * (x : G) * (s ^ 1)⁻¹ with hu
  set v := s ^ 2 * (x : G) * (s ^ 2)⁻¹ with hv
  have hx' : (x : G) * (u * v) = 1 := by
    rw [← mul_assoc]
    simpa using hx
  have hxe : (x : G) = (u * v)⁻¹ := eq_inv_of_mul_eq_one_left hx'
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  show (y : G) * x = x * y
  have hy0 : (y : G) ∈ Input183.orbA s X 0 := by
    rw [Input183.orbA_zero]
    exact y.2
  have c1 : Commute (y : G) u :=
    hc 0 1 (by norm_num) (by norm_num) (by norm_num) _ hy0 _ (Input183.mem_orbA x.2)
  have c2 : Commute (y : G) v :=
    hc 0 2 (by norm_num) (by norm_num) (by norm_num) _ hy0 _ (Input183.mem_orbA x.2)
  rw [hxe]
  exact ((c1.mul_right c2).inv_right).eq

theorem isQuasisimple_diagSub_range {X : Subgroup G} (hXq : CFSG.Open.IsQuasisimple ↥X) {s : G}
    (hc : ∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j, ∀ y ∈ Input183.orbA s X k,
      x * y = y * x) :
    CFSG.Open.IsQuasisimple ↥(Inputs183eqv.diagSub s 3 X hc).range :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientKerEquivRange _)
    (CFSG.ComponentClassification.Quasisimple.central_quotient hXq _ (diagSub_ker_le_center hc))

theorem isKGroup_diagSub_range {X : Subgroup G} (hXK : CFSG.Open.IsKGroup ↥X) {s : G}
    (hc : ∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j, ∀ y ∈ Input183.orbA s X k,
      x * y = y * x) :
    CFSG.Open.IsKGroup ↥(Inputs183eqv.diagSub s 3 X hc).range :=
  CFSG.KCore.KGroupNonab.of_mulEquiv isoInvariant_isCatalogGroup
    (CFSG.KCore.KGroupNonab.quotient isoInvariant_isCatalogGroup hXK _)
    (QuotientGroup.quotientKerEquivRange _).symm

theorem isPGroup_center_diagSub_range {X : Subgroup G} (hXq : CFSG.Open.IsQuasisimple ↥X)
    (hZ : IsPGroup 3 ↥(Subgroup.center ↥X)) {s : G}
    (hc : ∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j, ∀ y ∈ Input183.orbA s X k,
      x * y = y * x) :
    IsPGroup 3 ↥(Subgroup.center ↥(Inputs183eqv.diagSub s 3 X hc).range) := by
  rintro ⟨⟨z, hzr⟩, hzc⟩
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hzr
  have hxc : x ∈ Subgroup.center ↥X := by
    refine mem_center_of_commutator_mem_center hXq fun y => diagSub_ker_le_center hc ?_
    rw [MonoidHom.mem_ker]
    have h1 := Subgroup.mem_center_iff.1 hzc
      ⟨Inputs183eqv.diagSub s 3 X hc y, MonoidHom.mem_range.2 ⟨y, rfl⟩⟩
    have h2 : Inputs183eqv.diagSub s 3 X hc y * Inputs183eqv.diagSub s 3 X hc x =
        Inputs183eqv.diagSub s 3 X hc x * Inputs183eqv.diagSub s 3 X hc y := congrArg Subtype.val h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
    group
  obtain ⟨a, ha⟩ := hZ ⟨x, hxc⟩
  refine ⟨a, ?_⟩
  have hx1 : x ^ (3 ^ a) = 1 := congrArg Subtype.val ha
  apply Subtype.ext
  apply Subtype.ext
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← map_pow, hx1, map_one]

theorem gLBConj_diagSub_range {X : Subgroup G} {s b : G} (hbs : b * s = s * b)
    (hc : ∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j, ∀ y ∈ Input183.orbA s X k,
      x * y = y * x)
    (hc' : ∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s (GLBConj b X) j,
      ∀ y ∈ Input183.orbA s (GLBConj b X) k, x * y = y * x) :
    GLBConj b (Inputs183eqv.diagSub s 3 X hc).range =
      (Inputs183eqv.diagSub s 3 (GLBConj b X) hc').range := by
  have hbs' : Commute b s := hbs
  have hcomm : ∀ j : ℕ, b⁻¹ * s ^ j = s ^ j * b⁻¹ := fun j => ((hbs'.inv_left).pow_right j).eq
  have key : ∀ x : G, Input183.oprod 3 (fun j => s ^ j * (b⁻¹ * x * b) * (s ^ j)⁻¹) =
      b⁻¹ * Input183.oprod 3 (fun j => s ^ j * x * (s ^ j)⁻¹) * b := by
    intro x
    have h1 := Input183.conj_oprod b⁻¹ 3 (fun j => s ^ j * x * (s ^ j)⁻¹)
    rw [inv_inv] at h1
    rw [h1]
    refine Input183.oprod_congr fun j _ => ?_
    have h2 : (s ^ j)⁻¹ * b = b * (s ^ j)⁻¹ := ((hbs'.pow_right j).inv_right).eq.symm
    calc s ^ j * (b⁻¹ * x * b) * (s ^ j)⁻¹ = (s ^ j * b⁻¹) * x * (b * (s ^ j)⁻¹) := by group
      _ = (b⁻¹ * s ^ j) * x * ((s ^ j)⁻¹ * b) := by rw [hcomm j, h2]
      _ = b⁻¹ * (s ^ j * x * (s ^ j)⁻¹) * b := by group
  ext y
  rw [mem_gLBConj]
  constructor
  · rintro ⟨x, hx⟩
    have hx' : b⁻¹ * (x : G) * b ∈ GLBConj b X := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using x.2
    refine ⟨⟨b⁻¹ * x * b, hx'⟩, ?_⟩
    rw [Inputs183eqv.diagSub_apply]
    show Input183.oprod 3 (fun j => s ^ j * (b⁻¹ * (x : G) * b) * (s ^ j)⁻¹) = y
    rw [key, ← Inputs183eqv.diagSub_apply s 3 X hc x, hx]
    group
  · rintro ⟨x', hx'⟩
    have hx : b * (x' : G) * b⁻¹ ∈ X := (mem_gLBConj).1 x'.2
    refine ⟨⟨b * x' * b⁻¹, hx⟩, ?_⟩
    rw [Inputs183eqv.diagSub_apply]
    have e := key (b * (x' : G) * b⁻¹)
    have e2 : b⁻¹ * (b * (x' : G) * b⁻¹) * b = x' := by group
    rw [e2, ← Inputs183eqv.diagSub_apply s 3 (GLBConj b X) hc' x', hx'] at e
    show Input183.oprod 3 (fun j => s ^ j * (b * (x' : G) * b⁻¹) * (s ^ j)⁻¹) = b * y * b⁻¹
    rw [show Input183.oprod 3 (fun j => s ^ j * (b * (x' : G) * b⁻¹) * (s ^ j)⁻¹) =
      b * (b⁻¹ * Input183.oprod 3 (fun j => s ^ j * (b * (x' : G) * b⁻¹) * (s ^ j)⁻¹) * b) * b⁻¹ by group,
      ← e]

theorem diag_data {𝒞 : Set (Subgroup G)} {s : G} (hs : orderOf s = 3)
    (hsN : s ∈ Subgroup.normalizer ((sSup 𝒞 : Subgroup G) : Set G))
    (hq : ∀ X ∈ 𝒞, CFSG.Open.IsQuasisimple ↥X)
    (hcomm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (hnot : ∀ X ∈ 𝒞, s ∉ Subgroup.normalizer (X : Set G)) :
    ∃ D : Subgroup G → Subgroup G,
      (∀ X ∈ 𝒞, ∀ j : ℕ, Input183.orbA s X j ∈ 𝒞) ∧
      (∀ X ∈ 𝒞, ∃ hc : (∀ j k, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j,
          ∀ y ∈ Input183.orbA s X k, x * y = y * x), D X = (Inputs183eqv.diagSub s 3 X hc).range) ∧
      (∀ X ∈ 𝒞, D X ≤ sSup 𝒞 ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      (∀ X ∈ 𝒞, D X ≤ Input183.OJ s X) ∧
      (∀ m ∈ sSup 𝒞 ⊓ Subgroup.centralizer ({s} : Set G), ∃ d ∈ ⨆ X ∈ 𝒞, D X,
        ∃ w ∈ sSup 𝒞 ⊓ Subgroup.centralizer ((sSup 𝒞 : Subgroup G) : Set G), m = d * w) ∧
      (∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, Input183.OJ s X = Input183.OJ s X' →
        D X' ≤ D X ⊔ (sSup 𝒞 ⊓ Subgroup.centralizer ((sSup 𝒞 : Subgroup G) : Set G))) := by
  classical
  set L : Subgroup G := sSup 𝒞 with hL
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp0 : 0 < 3 := by norm_num
  have hbp : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hcompL : ∀ X ∈ 𝒞, IsComponentOf X L := fun X hX => isComponentOf_sSup_of_comm hq hcomm hX
  have hmem : ∀ X ∈ 𝒞, ∀ j : ℕ, Input183.orbA s X j ∈ 𝒞 := fun X hX j =>
    Input183.orbA_mem_family hL hcompL hcomm hsN hX j
  have hAcomm_of : ∀ X ∈ 𝒞, ∀ j k : ℕ, j < 3 → k < 3 → j ≠ k → ∀ x ∈ Input183.orbA s X j,
      ∀ y ∈ Input183.orbA s X k, x * y = y * x := fun X hX j k hj hk hjk x hx y hy =>
    hcomm _ (hmem X hX j) _ (hmem X hX k)
      (Input183.orbA_ne_of_not_normalizer hp hs (hnot X hX) hj hk hjk) x hx y hy
  have hAL : ∀ X ∈ 𝒞, ∀ j < 3, Input183.orbA s X j ≤ L := fun X hX j _ => le_sSup (hmem X hX j)
  let Dg : Subgroup G → Subgroup G := fun X =>
    if h : X ∈ 𝒞 then (Inputs183eqv.diagSub s 3 X (hAcomm_of X h)).range else ⊥
  have hDg : ∀ X (hX : X ∈ 𝒞), Dg X = (Inputs183eqv.diagSub s 3 X (hAcomm_of X hX)).range :=
    fun X hX => dif_pos hX
  have hdiag_fixed : ∀ X (hX : X ∈ 𝒞) (x : ↥X),
      s * Inputs183eqv.diagSub s 3 X (hAcomm_of X hX) x * s⁻¹ =
        Inputs183eqv.diagSub s 3 X (hAcomm_of X hX) x :=
    fun X hX x => by
      rw [Inputs183eqv.diagSub_apply]
      exact Input183.diag_shift hs hp0 (hAcomm_of X hX) (x : G) x.2
  have hDM : ∀ X ∈ 𝒞, Dg X ≤ L ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro X hX d hd
    rw [hDg X hX] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [Inputs183eqv.diagSub_apply]
      exact Input183.oprod_mem fun j hj => hAL X hX j hj (Input183.mem_orbA x.2)
    · exact (mul_inv_eq_iff_eq_mul.1 (hdiag_fixed X hX x)).symm
  have hDOJ : ∀ X ∈ 𝒞, Dg X ≤ Input183.OJ s X := by
    intro X hX d hd
    rw [hDg X hX] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    rw [Inputs183eqv.diagSub_apply]
    exact Input183.oprod_mem fun j _ => Input183.orbA_le_OJ s X j (Input183.mem_orbA x.2)
  have hSO : ∀ X ∈ 𝒞, ∀ o ∈ Input183.OJ s X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set G),
      s * o * s⁻¹ = o * z → o ∈ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
    intro X hX o ho z hz h
    rw [Input183.OJ_eq_fin hs hp0] at ho
    obtain ⟨x, hxX, w, hw, rfl⟩ := Input183.orbit_fixed hp0 hs hL hcomm
      (fun j _ => hmem X hX j) (fun j hj => hAL X hX j hj) (hAcomm_of X hX) hsN ho hz h
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hw)
    rw [hDg X hX]
    refine MonoidHom.mem_range.2 ⟨⟨x, hxX⟩, ?_⟩
    rw [Inputs183eqv.diagSub_apply]
  have hDeq : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, Input183.OJ s X = Input183.OJ s X' →
      Dg X' ≤ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
    intro X hX X' hX' h d hd
    have hdOJ := hDOJ X' hX' hd
    rw [← h] at hdOJ
    rw [hDg X' hX'] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    have hfix : s * Inputs183eqv.diagSub s 3 X' (hAcomm_of X' hX') x * s⁻¹ =
        Inputs183eqv.diagSub s 3 X' (hAcomm_of X' hX') x * 1 := by
      rw [mul_one]
      exact hdiag_fixed X' hX' x
    exact hSO X hX _ hdOJ 1 (L ⊓ Subgroup.centralizer (L : Set G)).one_mem hfix
  obtain ⟨hC1, -⟩ := Input183.core_gen_normal hbp hp0 hL hmem hcomm Dg hDM hDOJ hSO hDeq
  exact ⟨Dg, hmem, fun X hX => ⟨hAcomm_of X hX, hDg X hX⟩, hDM, hDOJ, hC1, hDeq⟩

end Diag

section Config

variable {G : Type} [Group G] [Finite G]

structure IsConfig (𝒞 : Set (Subgroup G)) (B : Subgroup G) : Prop where
  quasisimple : ∀ X ∈ 𝒞, CFSG.Open.IsQuasisimple ↥X
  kgroup : ∀ X ∈ 𝒞, CFSG.Open.IsKGroup ↥X
  center : ∀ X ∈ 𝒞, IsPGroup 3 ↥(Subgroup.center ↥X)
  comm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x
  elem : IsElemAbelian 3 B
  stab : ∀ X ∈ 𝒞, ∀ b ∈ B, GLBConj b X ∈ 𝒞
  trans : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, ∃ b ∈ B, GLBConj b X = X'

theorem IsConfig.mem_normalizer {𝒞 : Set (Subgroup G)} {B : Subgroup G} (hC : IsConfig 𝒞 B) {b : G}
    (hb : b ∈ B) : b ∈ Subgroup.normalizer ((sSup 𝒞 : Subgroup G) : Set G) :=
  mem_normalizer_sSup (fun X hX => hC.stab X hX b hb) (fun X hX => hC.stab X hX b⁻¹ (B.inv_mem hb))

theorem IsConfig.eq_singleton {𝒞 : Set (Subgroup G)} {B J : Subgroup G} (hC : IsConfig 𝒞 B)
    (hJ : GLAPComponent 3 (sSup 𝒞 ⊓ Subgroup.centralizer (B : Set G)) J)
    (hfix : ∀ s ∈ B, ∀ X ∈ 𝒞, s ∈ Subgroup.normalizer (X : Set G)) : ∃ K ∈ 𝒞, sSup 𝒞 = K := by
  obtain ⟨K, hK⟩ : 𝒞.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 : J ≤ ⊥ := by
      have h2 := hJ.1
      rw [hne, sSup_empty] at h2
      exact h2.trans inf_le_left
    exact Input183.glaPComponent_ne_bot' hJ (le_bot_iff.1 h1)
  have h𝒞 : 𝒞 = {K} := by
    ext X
    constructor
    · intro hX
      obtain ⟨b, hb, rfl⟩ := hC.trans K hK X hX
      exact gLBConj_eq_of_mem_normalizer (hfix b hb K hK)
    · rintro rfl
      exact hK
  exact ⟨K, hK, by rw [h𝒞, sSup_singleton]⟩

theorem inducesInner_of_le_centralizer {K B J : Subgroup G} {k : G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hBK : B ≤ Subgroup.centralizer (K : Set G))
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer (B : Set G)) J) (hk : k ∈ K) : InducesInner 3 J k := by
  have hKB : K ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (Subgroup.mem_centralizer_iff.1 (hBK hb) x hx).symm
  rw [inf_eq_left.2 hKB] at hJ
  have hJK : J = K := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.i183v_eq_or_le_center hJ.2.1 hKq with h | h
    · exact h
    · exfalso
      have hab : ⁅J, J⁆ ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro j₁ hj₁ j₂ hj₂
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 (h hj₁)
        have hc := Subgroup.mem_center_iff.1 hz ⟨j₂, hJ.1 hj₂⟩
        have hc' : j₂ * (z : G) = (z : G) * j₂ := congrArg Subtype.val hc
        rw [Subgroup.mem_bot, commutatorElement_def]
        show (z : G) * j₂ * (z : G)⁻¹ * j₂⁻¹ = 1
        rw [← hc']
        group
      rw [glaPComponent_perfect hJ, le_bot_iff] at hab
      exact Input183.glaPComponent_ne_bot' hJ hab
  refine ⟨k, hJK ▸ hk, ?_⟩
  rw [inv_mul_cancel]
  exact Subgroup.one_mem _

theorem isChevSimple_of_input14_17 (hI1417 : Claims1245c.Input14_17) {K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hKK : CFSG.Open.IsKGroup ↥K) (hKO : GLAPPrimeCore 3 ↥K = ⊥) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb3 : b ^ 3 = 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K) := by
  have h1 := hI1417 K K hKK (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hKq hKO) b hbN hb3 J
    hJ hJt
  have e : barOf 3 K ≃* ↥K := (QuotientGroup.quotientMulEquivOfEq hKO).trans QuotientGroup.quotientBot
  have eZ : (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) ≃* (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center (barOf 3 K)) (Subgroup.center ↥K) e (Subgroup.map_center_eq e)
  rcases h1 with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨eZ.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨eZ.symm.trans f⟩⟩

theorem config_step {𝒞 : Set (Subgroup G)} {B J : Subgroup G} {k : G} (hC : IsConfig 𝒞 B)
    (hJ : GLAPComponent 3 (sSup 𝒞 ⊓ Subgroup.centralizer (B : Set G)) J)
    (hk : k ∈ sSup 𝒞) (hkB : k ∈ Subgroup.centralizer (B : Set G))
    (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k))
    {s : G} (hsB : s ∈ B) {X₀ : Subgroup G} (hX₀ : X₀ ∈ 𝒞)
    (hsX₀ : s ∉ Subgroup.normalizer (X₀ : Set G)) :
    ∃ 𝒞' : Set (Subgroup G), Nat.card ↥(sSup 𝒞') < Nat.card ↥(sSup 𝒞) ∧ sSup 𝒞' ≤ sSup 𝒞 ∧
      IsConfig 𝒞' B ∧ GLAPComponent 3 (sSup 𝒞' ⊓ Subgroup.centralizer (B : Set G)) J ∧ k ∈ sSup 𝒞' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  set L : Subgroup G := sSup 𝒞 with hL
  set ZL : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G) with hZL
  have hnot : ∀ X ∈ 𝒞, s ∉ Subgroup.normalizer (X : Set G) := by
    intro X hX hsX
    obtain ⟨b, hb, rfl⟩ := hC.trans X₀ hX₀ X hX
    apply hsX₀
    rw [mem_normalizer_iff_gLBConj_eq] at hsX ⊢
    have hbs : b * s = s * b := hC.elem.comm hb hsB
    have e : GLBConj b (GLBConj s X₀) = GLBConj b X₀ := by
      rw [gLBConj_gLBConj, ← hbs, ← gLBConj_gLBConj]
      exact hsX
    have e2 := congrArg (GLBConj b⁻¹) e
    simp only [gLBConj_gLBConj, mul_inv_cancel_right, mul_inv_cancel, gLBConj_one] at e2
    exact e2
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hsX₀ (Subgroup.one_mem _)
  have hs3 : s ^ 3 = 1 := hC.elem.2 s hsB
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hC.mem_normalizer hsB
  obtain ⟨D, hmem, hDdef, hDM, hDOJ, hC1, hDeq⟩ := diag_data hso hsN hC.quasisimple hC.comm hnot
  set 𝒞' : Set (Subgroup G) := D '' 𝒞 with h𝒞'
  have hL' : sSup 𝒞' = ⨆ X ∈ 𝒞, D X := sSup_image
  have hL'le : sSup 𝒞' ≤ L ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [hL']
    exact iSup₂_le hDM
  have hZLc : ∀ g ∈ L, ∀ z ∈ ZL, g * z = z * g := fun g hg z hz =>
    Subgroup.mem_centralizer_iff.1 hz.2 g hg
  have hZLZL : ∀ z ∈ ZL, ∀ z' ∈ ZL, z * z' = z' * z := fun z hz z' hz' =>
    Subgroup.mem_centralizer_iff.1 hz'.2 z hz.1
  have hDq : ∀ X ∈ 𝒞, CFSG.Open.IsQuasisimple ↥(D X) := fun X hX => by
    obtain ⟨hc, hD⟩ := hDdef X hX
    rw [hD]
    exact isQuasisimple_diagSub_range (hC.quasisimple X hX) hc
  have hDL : ∀ X ∈ 𝒞, D X ≤ L := fun X hX => (hDM X hX).trans inf_le_left
  have hDeq' : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, Input183.OJ s X = Input183.OJ s X' → D X' ≤ D X :=
    fun X hX X' hX' h => le_of_perfect_of_le_sup (commutator_eq_self_of_isQuasisimple (hDq X' hX'))
      (hDeq X hX X' hX' h) (fun a ha z hz => hZLc a (hDL X hX ha) z hz) hZLZL
  have hconj : ∀ X ∈ 𝒞, ∀ b ∈ B, GLBConj b (D X) = D (GLBConj b X) := by
    intro X hX b hb
    obtain ⟨hc, hD⟩ := hDdef X hX
    obtain ⟨hc', hD'⟩ := hDdef (GLBConj b X) (hC.stab X hX b hb)
    rw [hD, hD']
    exact gLBConj_diagSub_range (hC.elem.comm hb hsB) hc hc'
  have hC' : IsConfig 𝒞' B := by
    refine ⟨?_, ?_, ?_, ?_, hC.elem, ?_, ?_⟩
    · rintro _ ⟨X, hX, rfl⟩
      exact hDq X hX
    · rintro _ ⟨X, hX, rfl⟩
      obtain ⟨hc, hD⟩ := hDdef X hX
      rw [hD]
      exact isKGroup_diagSub_range (hC.kgroup X hX) hc
    · rintro _ ⟨X, hX, rfl⟩
      obtain ⟨hc, hD⟩ := hDdef X hX
      rw [hD]
      exact isPGroup_center_diagSub_range (hC.quasisimple X hX) (hC.center X hX) hc
    · rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩ hne x hx y hy
      by_cases hOJ : Input183.OJ s X = Input183.OJ s X'
      · exact absurd (le_antisymm (hDeq' X' hX' X hX hOJ.symm) (hDeq' X hX X' hX' hOJ)) hne
      · exact Input183.OJ_comm_of_ne hs3 (by norm_num) hmem hC.comm hX hX' hOJ x (hDOJ X hX hx) y
          (hDOJ X' hX' hy)
    · rintro _ ⟨X, hX, rfl⟩ b hb
      rw [hconj X hX b hb]
      exact ⟨GLBConj b X, hC.stab X hX b hb, rfl⟩
    · rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩
      obtain ⟨b, hb, hbX⟩ := hC.trans X hX X' hX'
      exact ⟨b, hb, by rw [hconj X hX b hb, hbX]⟩
  have hlt : L ⊓ Subgroup.centralizer ({s} : Set G) < L := by
    refine lt_of_le_of_ne inf_le_left fun heq => hsX₀ ?_
    refine Input183.normalizer_of_commute fun x hx => ?_
    have hxL : x ∈ L := (le_sSup hX₀ : X₀ ≤ L) hx
    rw [← heq] at hxL
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxL.2).symm
  have hcard : Nat.card ↥(sSup 𝒞') < Nat.card ↥L := by
    have h1 : Nat.card ↥(sSup 𝒞') ≤ Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) :=
      Subgroup.card_le_of_le hL'le
    have h2 : Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) < Nat.card ↥L :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) fun h =>
        hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.ge)
    omega
  have hJL : J ≤ L ⊓ Subgroup.centralizer (B : Set G) := hJ.1
  have hCBs : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hsB)
  have hsup : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ sSup 𝒞' ⊔ ZL := by
    intro m hm
    obtain ⟨d, hd, w, hw, rfl⟩ := hC1 m hm
    rw [← hL'] at hd
    exact Subgroup.mul_mem_sup hd hw
  have hJ' : J ≤ sSup 𝒞' := le_of_perfect_of_le_sup (glaPComponent_perfect hJ)
    (fun j hj => hsup ⟨(hJL hj).1, hCBs (hJL hj).2⟩)
    (fun a ha z hz => hZLc a (hL'le ha).1 z hz) hZLZL
  have hJc : GLAPComponent 3 (sSup 𝒞' ⊓ Subgroup.centralizer (B : Set G)) J :=
    glaPComponent_of_le hp3 hJ (le_inf hJ' (hJL.trans inf_le_right))
      (inf_le_inf_right _ (hL'le.trans inf_le_left))
  have hks : k ∈ L ⊓ Subgroup.centralizer ({s} : Set G) := ⟨hk, hCBs hkB⟩
  obtain ⟨d, hd, w, hw, hkdw⟩ := hC1 k hks
  obtain ⟨a, ha⟩ := exists_pow_three_eq_one_of_mem_center hC.comm hC.center hw
  have hkw : Commute k w := hZLc k hk w hw
  have hdk : d = k * w⁻¹ := by
    rw [hkdw]
    group
  have hdpow : d ^ (3 ^ a) = k ^ (3 ^ a) := by
    rw [hdk, (hkw.inv_right).mul_pow, inv_pow, ha, inv_one, mul_one]
  obtain ⟨n2, hn2⟩ := hk2 ⟨k, Subgroup.mem_zpowers k⟩
  have hkn : k ^ (2 ^ n2) = 1 := by
    have h := congrArg Subtype.val hn2
    simpa using h
  have hcop : Nat.Coprime (3 ^ a) (orderOf k) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hkn) (Nat.Coprime.pow _ _ (by norm_num))
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
  have hkmem : k ∈ sSup 𝒞' := by
    rw [← hr, ← hdpow]
    rw [← hL'] at hd
    exact Subgroup.pow_mem _ (Subgroup.pow_mem _ hd _) _
  exact ⟨𝒞', hcard, hL'le.trans inf_le_left, hC', hJc, hkmem⟩

end Config

section Main

theorem isComponentOf_of_glaPComponent_of_core_bot {G : Type} [Group G] {p : ℕ} {X L : Subgroup G}
    (hcore : GLAPPrimeCore p ↥X = ⊥) (hL : GLAPComponent p X L) : IsComponentOf L X := by
  refine ⟨hL.1, hL.2.1, ?_⟩
  have hq := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (L.subgroupOf X) _ hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hL.1)) hq

theorem exists_config (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {Y : Type} [Group Y] [Finite Y] (hYK : CFSG.Open.IsKGroup Y) (hYO : GLAPPrimeCore 3 Y = ⊥)
    {B : Subgroup Y} (hB : IsElemAbelian 3 B) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (Subgroup.centralizer (B : Set Y)) J) {v : Y}
    (hv2 : IsPGroup 2 ↥(Subgroup.zpowers v)) (hvB : v ∈ Subgroup.centralizer (B : Set Y))
    (hv : ∀ L : Subgroup Y, IsComponentOf L ⊤ → v ∈ Subgroup.normalizer (L : Set Y) ∧
      ∃ l ∈ L, l⁻¹ * v ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ (𝒞 : Set (Subgroup Y)) (k : Y), IsConfig 𝒞 B ∧
      GLAPComponent 3 (sSup 𝒞 ⊓ Subgroup.centralizer (B : Set Y)) J ∧ J ≤ sSup 𝒞 ∧
      k ∈ sSup 𝒞 ∧ k ∈ Subgroup.centralizer (B : Set Y) ∧ IsPGroup 2 ↥(Subgroup.zpowers k) ∧
      k⁻¹ * v ∈ Subgroup.centralizer ((sSup 𝒞 : Subgroup Y) : Set Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hTK : CFSG.Open.IsKGroup ↥(⊤ : Subgroup Y) :=
    CFSG.KCore.KGroupNonab.of_mulEquiv isoInvariant_isCatalogGroup hYK Subgroup.topEquiv
  have hTO : GLAPPrimeCore 3 ↥(⊤ : Subgroup Y) = ⊥ := by
    rw [← glaPPrimeCore_map_iso 3 (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).symm, hYO,
      Subgroup.map_bot]
  have hTO' : GLAPPrimeCoreOf 3 (⊤ : Subgroup Y) = ⊥ := by
    show (GLAPPrimeCore 3 ↥(⊤ : Subgroup Y)).map (⊤ : Subgroup Y).subtype = ⊥
    rw [hTO, Subgroup.map_bot]
  have hJ' : GLAPComponent 3 ((⊤ : Subgroup Y) ⊓ Subgroup.centralizer (B : Set Y)) J := by
    rwa [top_inf_eq]
  obtain ⟨𝒞, hcomp3, heq, hstab, htr⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hSch Y ⊤ hTK 3 hp3 B le_top hB J hJ'
  have hcompT : ∀ L ∈ 𝒞, IsComponentOf L ⊤ := fun L hL =>
    isComponentOf_of_glaPComponent_of_core_bot hTO (hcomp3 L hL)
  have hcomm : ∀ X ∈ 𝒞, ∀ X' ∈ 𝒞, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x :=
    fun X hX X' hX' hne x hx y hy =>
      Prop95Parts.Input18.comp_comm (hcompT X hX) (hcompT X' hX') hne hx hy
  have hLO : ∀ L ∈ 𝒞, GLAPPrimeCore 3 ↥L = ⊥ := fun L hL => by
    have h1 : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 ⊤ :=
      glaPPrimeCoreOf_le_of_isSubnormal hp3 (hcompT L hL).2.1
    rw [hTO', le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h1
  have hC : IsConfig 𝒞 B :=
    ⟨fun L hL => (hcompT L hL).2.2,
      fun L _ => CFSG.KCore.KGroupNonab.of_injective isoInvariant_isCatalogGroup hYK L.subtype
        L.subtype_injective,
      fun L hL => isPGroup_center_of_core_bot (hLO L hL), hcomm, hB, hstab, htr⟩
  set M : Subgroup Y := sSup 𝒞 with hM
  have hJM : J ≤ M := by
    have h1 : J ≤ ⨆ g ∈ GLAPLayer 3 (⊤ : Subgroup Y), GLBConj g J :=
      le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 (⊤ : Subgroup Y)) => GLBConj g J) 1
        (Subgroup.one_mem _) (by rw [gLBConj_one])
    rw [← heq, ← sSup_eq_iSup] at h1
    exact h1
  have hJc : GLAPComponent 3 (M ⊓ Subgroup.centralizer (B : Set Y)) J :=
    glaPComponent_of_le hp3 hJ (le_inf hJM hJ.1) inf_le_right
  letI : Fintype ↥𝒞 := Fintype.ofFinite _
  have hcP := pairwise_comm_of hcomm
  have hl : ∀ i : ↥𝒞, ∃ l ∈ (i : Subgroup Y),
      l⁻¹ * v ∈ Subgroup.centralizer ((i : Subgroup Y) : Set Y) :=
    fun i => (hv i.1 (hcompT i.1 i.2)).2
  choose l hlmem hlc using hl
  set m : Y := Subgroup.noncommPiCoprod (H := fun i : ↥𝒞 => (i : Subgroup Y)) hcP
    (fun i => ⟨l i, hlmem i⟩) with hm
  have hmM : m ∈ M := by
    rw [hM, ← noncommPiCoprod_range_eq hcP]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  have hc : m⁻¹ * v ∈ Subgroup.centralizer (M : Set Y) := by
    have hle : M ≤ Subgroup.centralizer ({m⁻¹ * v} : Set Y) := by
      refine sSup_le fun X hX y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : m * y * m⁻¹ = l ⟨X, hX⟩ * y * (l ⟨X, hX⟩)⁻¹ :=
        noncommPiCoprod_conj hcP (fun i => ⟨l i, hlmem i⟩) ⟨X, hX⟩ hy
      have h2 : y * ((l ⟨X, hX⟩)⁻¹ * v) = (l ⟨X, hX⟩)⁻¹ * v * y :=
        Subgroup.mem_centralizer_iff.1 (hlc ⟨X, hX⟩) y hy
      calc y * (m⁻¹ * v) = m⁻¹ * (m * y * m⁻¹) * v := by group
        _ = m⁻¹ * (l ⟨X, hX⟩ * y * (l ⟨X, hX⟩)⁻¹) * v := by rw [h1]
        _ = m⁻¹ * l ⟨X, hX⟩ * (y * ((l ⟨X, hX⟩)⁻¹ * v)) := by group
        _ = m⁻¹ * l ⟨X, hX⟩ * ((l ⟨X, hX⟩)⁻¹ * v * y) := by rw [h2]
        _ = m⁻¹ * v * y := by group
    exact Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  obtain ⟨n2, hn2⟩ := hv2 ⟨v, Subgroup.mem_zpowers v⟩
  have hvn : v ^ (2 ^ n2) = 1 := by
    have h := congrArg Subtype.val hn2
    simpa using h
  set c : Y := m⁻¹ * v with hcdef
  have hmc : Commute m c := Subgroup.mem_centralizer_iff.1 hc m hmM
  have hvmc : v = m * c := by
    rw [hcdef]
    group
  have hmpow : m ^ (2 ^ n2) ∈ M ⊓ Subgroup.centralizer (M : Set Y) := by
    refine ⟨Subgroup.pow_mem _ hmM _, ?_⟩
    have h1 : m ^ (2 ^ n2) * c ^ (2 ^ n2) = 1 := by rw [← hmc.mul_pow, ← hvmc, hvn]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc _)
  obtain ⟨a3, ha3⟩ := exists_pow_three_eq_one_of_mem_center hcomm hC.center hmpow
  have hcop : Nat.Coprime (2 ^ n2) (3 ^ a3) := Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨u, t, hut⟩ := Nat.isCoprime_iff_coprime.2 hcop
  set k : Y := m ^ (t * ((3 ^ a3 : ℕ) : ℤ)) with hkdef
  set z : Y := m ^ (u * ((2 ^ n2 : ℕ) : ℤ)) with hzdef
  have hmzk : m = z * k := by rw [hzdef, hkdef, ← zpow_add, hut, zpow_one]
  have hzM : z ∈ M ⊓ Subgroup.centralizer (M : Set Y) := by
    rw [hzdef, mul_comm, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hmpow _
  have hkM : k ∈ M := Subgroup.zpow_mem _ hmM _
  have hkn : k ^ (2 ^ n2) = 1 := by
    rw [hkdef, ← zpow_natCast, ← zpow_mul]
    have e : t * ((3 ^ a3 : ℕ) : ℤ) * ((2 ^ n2 : ℕ) : ℤ) = ((2 ^ n2 * 3 ^ a3 : ℕ) : ℤ) * t := by
      push_cast
      ring
    rw [e, zpow_mul, zpow_natCast, pow_mul, ha3, one_zpow]
  have hkv : k⁻¹ * v ∈ Subgroup.centralizer (M : Set Y) := by
    have hzm : Commute z m := (Subgroup.mem_centralizer_iff.1 hzM.2 m hmM).symm
    have hk' : k = z⁻¹ * m := by
      rw [hmzk]
      group
    have e : k⁻¹ * v = z * c := by
      rw [hk', hcdef]
      calc (z⁻¹ * m)⁻¹ * v = m⁻¹ * z * v := by group
        _ = z * m⁻¹ * v := by rw [(hzm.inv_right).eq]
        _ = z * (m⁻¹ * v) := by group
    rw [e]
    exact Subgroup.mul_mem _ hzM.2 hc
  have hk2 : IsPGroup 2 ↥(Subgroup.zpowers k) := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨n2, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkn, one_zpow]
  have hkB : k ∈ Subgroup.centralizer (B : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (M : Set Y) := hC.mem_normalizer hb
    have hbv : b * v = v * b := Subgroup.mem_centralizer_iff.1 hvB b hb
    set k' : Y := b * k * b⁻¹ with hk'def
    have hk'M : k' ∈ M := (Subgroup.mem_normalizer_iff.1 hbN k).1 hkM
    have hc' : k'⁻¹ * v ∈ Subgroup.centralizer (M : Set Y) := by
      have h1 := conj_mem_centralizer_of_normalizer hbN hkv
      have e : b * (k⁻¹ * v) * b⁻¹ = k'⁻¹ * v := by
        rw [hk'def]
        calc b * (k⁻¹ * v) * b⁻¹ = (b * k * b⁻¹)⁻¹ * (b * v * b⁻¹) := by group
          _ = (b * k * b⁻¹)⁻¹ * (v * b * b⁻¹) := by rw [hbv]
          _ = (b * k * b⁻¹)⁻¹ * v := by group
      rw [← e]
      exact h1
    set z' : Y := k⁻¹ * k' with hz'def
    have hz'Z : z' ∈ M ⊓ Subgroup.centralizer (M : Set Y) := by
      refine ⟨M.mul_mem (M.inv_mem hkM) hk'M, ?_⟩
      have e : z' = (k⁻¹ * v) * (k'⁻¹ * v)⁻¹ := by
        rw [hz'def]
        group
      rw [e]
      exact Subgroup.mul_mem _ hkv (Subgroup.inv_mem _ hc')
    obtain ⟨a', ha'⟩ := exists_pow_three_eq_one_of_mem_center hcomm hC.center hz'Z
    have hkz : Commute k z' := Subgroup.mem_centralizer_iff.1 hz'Z.2 k hkM
    have hkk' : k' = k * z' := by
      rw [hz'def]
      group
    have hk'n : k' ^ (2 ^ n2) = 1 := by
      rw [hk'def, conj_pow, hkn]
      group
    have hz'n : z' ^ (2 ^ n2) = 1 := by
      rw [hkk', hkz.mul_pow, hkn, one_mul] at hk'n
      exact hk'n
    have hz'1 : z' = 1 := by
      have h3 : orderOf z' ∣ Nat.gcd (2 ^ n2) (3 ^ a') :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz'n) (orderOf_dvd_of_pow_eq_one ha')
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow _ _ (by norm_num)), Nat.dvd_one,
        orderOf_eq_one_iff] at h3
      exact h3
    have e : k' = k := by rw [hkk', hz'1, mul_one]
    calc b * k = (b * k * b⁻¹) * b := by group
      _ = k * b := by rw [← hk'def, e]
  exact ⟨𝒞, k, hC, hJc, hJM, hkM, hkB, hk2, hkv⟩

theorem inducesInner_of_mul_centralizer {Y : Type} [Group Y] [Finite Y] {J M : Subgroup Y} {k v : Y} (hJM : J ≤ M)
    (hkv : k⁻¹ * v ∈ Subgroup.centralizer (M : Set Y)) (hk : InducesInner 3 J k) : InducesInner 3 J v := by
  obtain ⟨j, hj, hjk⟩ := hk
  refine ⟨j, hj, ?_⟩
  have e : j⁻¹ * v = (j⁻¹ * k) * (k⁻¹ * v) := by group
  rw [e]
  exact (centBar 3 ⊤ J).mul_mem hjk (mem_centBar_of_mem_centralizer (Subgroup.centralizer_le hJM hkv))

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141

end
