module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalance
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Open CFSG.SignalizerFunctorTheorem
open CFSG.ClassicalInvolution.Balance (deltaCore TwoBalancedWrt)

section Basic

variable {G : Type*} [Group G]

theorem involutionOddCore_eq (a : G) :
    CFSG.Assembly.Dichotomy.involutionOddCore a =
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  simp only [CFSG.Assembly.Dichotomy.involutionOddCore,
    CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]

theorem wGroup_eq_iSup_deltaCore (A : Subgroup G) :
    wGroup A = ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : 4 ≤ Nat.card B) (_ : ∀ b ∈ B, b * b = 1),
      deltaCore B := by
  simp only [wGroup, deltaCore_eq_iInf_pPrimeCore]

theorem wGroup_mono {A A' : Subgroup G} (h : A ≤ A') : wGroup A ≤ wGroup A' := by
  rw [wGroup_eq_iSup_deltaCore, wGroup_eq_iSup_deltaCore]
  exact iSup_le fun B => iSup_le fun hB => iSup_le fun h4 => iSup_le fun h2 =>
    le_iSup_of_le B (le_iSup_of_le (hB.trans h) (le_iSup_of_le h4 (le_iSup_of_le h2 le_rfl)))

theorem deltaCore_anti {D D' : Subgroup G} (h : D ≤ D') : deltaCore D' ≤ deltaCore D :=
  CFSG.ClassicalInvolution.Balance.le_deltaCore fun _ hd hd1 =>
    CFSG.ClassicalInvolution.Balance.deltaCore_le_involutionOddCore (h hd) hd1

theorem wGroup_map_conj (g : G) (A : Subgroup G) :
    wGroup (A.map (MulAut.conj g).toMonoidHom) = (wGroup A).map (MulAut.conj g).toMonoidHom := by
  set φ := (MulAut.conj g).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.conj g).injective
  have hcard : ∀ B : Subgroup G, Nat.card (B.map φ) = Nat.card B := fun B =>
    card_map_of_injective hinj
  have hsq : ∀ B : Subgroup G, (∀ b ∈ B, b * b = 1) → ∀ b ∈ B.map φ, b * b = 1 := by
    rintro B hB _ ⟨b, hb, rfl⟩
    rw [← map_mul, hB b hb, map_one]
  apply le_antisymm
  · rw [wGroup_eq_iSup_deltaCore]
    refine iSup_le fun B => iSup_le fun hB => iSup_le fun h4 => iSup_le fun h2 => ?_
    set B₀ : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB₀
    have hBB : B = B₀.map φ := by
      rw [hB₀, map_map]
      ext x
      simp only [hφ, mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      constructor
      · intro hx
        exact ⟨x, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        convert hy using 1
        group
    have hB₀A : B₀ ≤ A := by
      rw [hB₀]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hB hy
      simpa [hφ, MulAut.conj_apply, mul_assoc] using hz
    have h2' : ∀ b ∈ B₀, b * b = 1 := by
      rw [hB₀]
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, h2 b hb, map_one]
    rw [hBB, ← CFSG.ClassicalInvolution.Balance.deltaCore_map]
    refine map_mono ?_
    rw [wGroup_eq_iSup_deltaCore]
    refine le_iSup_of_le B₀ (le_iSup_of_le hB₀A (le_iSup_of_le ?_ (le_iSup_of_le h2' le_rfl)))
    rw [hBB, hcard] at h4
    exact h4
  · rw [map_le_iff_le_comap, wGroup_eq_iSup_deltaCore]
    refine iSup_le fun B => iSup_le fun hB => iSup_le fun h4 => iSup_le fun h2 => ?_
    rw [← map_le_iff_le_comap, CFSG.ClassicalInvolution.Balance.deltaCore_map,
      wGroup_eq_iSup_deltaCore]
    exact le_iSup_of_le (B.map φ) (le_iSup_of_le (map_mono hB)
      (le_iSup_of_le (by rw [hcard]; exact h4) (le_iSup_of_le (hsq B h2) le_rfl)))

theorem wGroup_conjugate (A : Subgroup G) (g : G) :
    wGroup (conjugate A g) = conjugate (wGroup A) g :=
  wGroup_map_conj g⁻¹ A

end Basic

theorem GrS4.mem_normalizer_wGroup {G : Type} [Group G] {E : Subgroup G} {g : G}
    (hg : g ∈ normalizer (E : Set G)) :
    g ∈ normalizer (wGroup E : Set G) := by
  have hg' : E.map (MulAut.conj g).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.mp hg
  have h1 : wGroup (E.map (MulAut.conj g).toMonoidHom) = wGroup E := by rw [hg']
  rw [wGroup_map_conj] at h1
  exact mem_normalizer_iff_map_conj_eq.mpr h1

section Completion

variable {G : Type} [Group G] [Finite G]

theorem exists_le_card_four {B : Subgroup G} (hB : IsPGroup 2 B) (h4 : 4 ≤ Nat.card B) :
    ∃ F : Subgroup G, F ≤ B ∧ Nat.card F = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥B)).mp hB
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp_all
  have hdvd : 2 ^ 2 ∣ Nat.card B := by
    rw [hk]
    exact pow_dvd_pow 2 hk2
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨H.map B.subtype, map_subtype_le H, ?_⟩
  rw [card_map_of_injective B.subtype_injective, hH]
  norm_num

theorem exists_le_card_eight {G : Type*} [Group G] [Finite G]
    {B : Subgroup G} (hB : IsPGroup 2 B) (h8 : 8 ≤ Nat.card B) :
    ∃ F : Subgroup G, F ≤ B ∧ Nat.card F = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥B)).mp hB
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp_all
  have hdvd : 2 ^ 3 ∣ Nat.card B := by
    rw [hk]
    exact pow_dvd_pow 2 hk3
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨H.map B.subtype, map_subtype_le H, ?_⟩
  rw [card_map_of_injective B.subtype_injective, hH]
  norm_num

theorem wGroup_eq_completion {A : Subgroup G} (hA : IsElemTwo A) :
    wGroup A = completion 2 2 A deltaCore := by
  apply le_antisymm
  · rw [wGroup_eq_iSup_deltaCore]
    refine iSup_le fun B => iSup_le fun hB => iSup_le fun h4 => iSup_le fun _ => ?_
    obtain ⟨F, hFB, hF4⟩ := exists_le_card_four ((hA.mono hB).isPGroup) h4
    exact (deltaCore_anti hFB).trans (le_completion ⟨hFB.trans hB, by rw [hF4]; norm_num⟩)
  · refine iSup₂_le fun F hF => ?_
    rw [wGroup_eq_iSup_deltaCore]
    exact le_iSup_of_le F (le_iSup_of_le hF.1 (le_iSup_of_le (by rw [hF.2]; norm_num)
      (le_iSup_of_le (fun b hb => hA.2 b (hF.1 hb)) le_rfl)))

omit [Finite G] in
theorem twoBalancedWrt_of_gwTwoBalanced (hB : GWTwoBalanced G) {A : Subgroup G}
    (hA : IsElemTwo A) : TwoBalancedWrt A := by
  intro F hF a haA ha1
  have h4 : Nat.card F = 4 := hF.2
  have h2 : ∀ x ∈ F, x * x = 1 := fun x hx => hA.2 x (hF.1 hx)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hA.2 a haA) ha1
  have h := hB F (nonempty_mulEquiv_four h4 h2) a ha2 fun e he => hA.1 e (hF.1 he) a haA
  rw [deltaCore_eq_iInf_pPrimeCore, involutionOddCore_eq]
  exact h

omit [Finite G] in
theorem IsElemTwo.isElemAbelian {A : Subgroup G} (hA : IsElemTwo A) : IsElemAbelian 2 A :=
  ⟨⟨⟨fun x y => Subtype.ext (hA.1 _ x.2 _ y.2)⟩⟩, fun x hx => by rw [pow_two]; exact hA.2 x hx⟩

theorem wGroup_eq_of_le_eight_of_twoBalancedWrt {A A₀ : Subgroup G} (hB : TwoBalancedWrt A)
    (hA : IsElemTwo A) (hA₀ : A₀ ≤ A) (h8 : Nat.card A₀ = 8) : wGroup A = wGroup A₀ := by
  by_cases h16 : 16 ≤ Nat.card A
  · rw [wGroup_eq_completion hA, wGroup_eq_completion (hA.mono hA₀),
      CFSG.ClassicalInvolution.Balance.completion_eq_iSup_of_mem_E3 hA.isElemAbelian h16
        hB ⟨hA₀, by rw [h8]; norm_num⟩]
    rfl
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp hA.isPGroup
    have h8le : 8 ≤ Nat.card A := h8 ▸ card_le_of_le hA₀
    have hk3 : k = 3 := by
      rw [hk] at h16 h8le
      have h1 : k < 4 := by
        by_contra h
        push Not at h
        exact h16 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h))
      have h2 : 3 ≤ k := by
        by_contra h
        push Not at h
        interval_cases k <;> norm_num at h8le
      omega
    have hAA : A₀ = A := eq_of_le_of_card_ge hA₀ (by rw [hk, hk3, h8]; norm_num)
    rw [hAA]

theorem wGroup_eq_of_le_eight (hB : GWTwoBalanced G) {A A₀ : Subgroup G} (hA : IsElemTwo A)
    (hA₀ : A₀ ≤ A) (h8 : Nat.card A₀ = 8) : wGroup A = wGroup A₀ :=
  wGroup_eq_of_le_eight_of_twoBalancedWrt (twoBalancedWrt_of_gwTwoBalanced hB hA) hA hA₀ h8

theorem exists_isElemTwo_eight {A : Subgroup G} (hA : IsAbelianTwoOfRank 3 A) :
    ∃ F : Subgroup G, F ≤ A ∧ IsElemTwo F ∧ Nat.card F = 8 := by
  obtain ⟨F, hFA, hF, h8⟩ := exists_isElemTwo_of_isAbelianTwoOfRank hA
  obtain ⟨F', hF'F, hF'8⟩ := exists_le_card_eight hF.isPGroup h8
  exact ⟨F', hF'F.trans hFA, hF.mono hF'F, hF'8⟩

theorem wGroup_eq_of_abelian_in {S A A₀ : Subgroup G}
    (hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    (hAS : A ≤ S) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA₀A : A₀ ≤ A)
    (hA₀ : IsElemTwo A₀) (h8 : Nat.card A₀ = 8) : wGroup A = wGroup A₀ := by
  refine le_antisymm ?_ (wGroup_mono hA₀A)
  rw [wGroup_eq_iSup_deltaCore A]
  refine iSup_le fun D => iSup_le fun hDA => iSup_le fun h4 => iSup_le fun h2 => ?_
  have hD : IsElemTwo D := ⟨fun x hx y hy => hAc x (hDA hx) y (hDA hy), h2⟩
  have hDA₀ : IsElemTwo (D ⊔ A₀) := hD.sup hA₀ fun x hx y hy => hAc x (hDA hx) y (hA₀A hy)
  have hDS : D ⊔ A₀ ≤ S := sup_le (hDA.trans hAS) (hA₀A.trans hAS)
  have h1 : deltaCore D ≤ wGroup (D ⊔ A₀) := by
    rw [wGroup_eq_iSup_deltaCore]
    exact le_iSup_of_le D (le_iSup_of_le le_sup_left (le_iSup_of_le h4 (le_iSup_of_le h2 le_rfl)))
  rwa [wGroup_eq_of_le_eight_of_twoBalancedWrt (hB (D ⊔ A₀) hDS hDA₀) hDA₀ le_sup_right h8]
    at h1

theorem wGroup_eq_of_commute_in {S A A' : Subgroup G}
    (hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    (hAS : A ≤ S) (hA'S : A' ≤ S)
    (hA : IsAbelianTwoOfRank 3 A) (hA' : IsAbelianTwoOfRank 3 A')
    (hc : ∀ x ∈ A, ∀ y ∈ A', x * y = y * x) : wGroup A = wGroup A' := by
  obtain ⟨F, hFA, hF, hF8⟩ := exists_isElemTwo_eight hA
  obtain ⟨F', hF'A, hF', hF'8⟩ := exists_isElemTwo_eight hA'
  have hFF : IsElemTwo (F ⊔ F') := hF.sup hF' fun x hx y hy => hc x (hFA hx) y (hF'A hy)
  have hFFS : F ⊔ F' ≤ S := sup_le (hFA.trans hAS) (hF'A.trans hA'S)
  rw [wGroup_eq_of_abelian_in hB hAS hA.2.1 hFA hF hF8,
    wGroup_eq_of_abelian_in hB hA'S hA'.2.1 hF'A hF' hF'8,
    ← wGroup_eq_of_le_eight_of_twoBalancedWrt (hB (F ⊔ F') hFFS hFF) hFF le_sup_left hF8,
    wGroup_eq_of_le_eight_of_twoBalancedWrt (hB (F ⊔ F') hFFS hFF) hFF le_sup_right hF'8]

theorem wGroup_eq_of_commute (hB : GWTwoBalanced G) {A A' : Subgroup G}
    (hA : IsAbelianTwoOfRank 3 A) (hA' : IsAbelianTwoOfRank 3 A')
    (hc : ∀ x ∈ A, ∀ y ∈ A', x * y = y * x) : wGroup A = wGroup A' :=
  wGroup_eq_of_commute_in (S := ⊤) (fun _ _ hE => twoBalancedWrt_of_gwTwoBalanced hB hE)
    le_top le_top hA hA' hc

theorem wGroup_eq_of_abelianConnected (hB : GWTwoBalanced G) {E A : Subgroup G}
    (h : AbelianConnected 3 E A) : wGroup E = wGroup A := by
  obtain ⟨hE, hchain⟩ := h
  suffices ∀ B : Subgroup G, Relation.ReflTransGen (fun A' B' : Subgroup G =>
      IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) E B →
      IsAbelianTwoOfRank 3 B ∧ wGroup E = wGroup B from (this A hchain).2
  intro B hEB
  induction hEB with
  | refl => exact ⟨hE, rfl⟩
  | tail _ hBC ih =>
    obtain ⟨hB3, hW⟩ := ih
    exact ⟨hBC.1, hW.trans (wGroup_eq_of_commute hB hB3 hBC.1 hBC.2)⟩

theorem AbelianConnectedIn.abelianConnected {S A B : Subgroup G}
    (h : AbelianConnectedIn S 3 A B) : AbelianConnected 3 A B := by
  obtain ⟨-, hA, hchain⟩ := h
  refine ⟨hA, ?_⟩
  induction hchain with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hBC ih => exact ih.tail ⟨hBC.2.1, hBC.2.2⟩

theorem wGroup_eq_of_abelianConnectedIn {S E A : Subgroup G}
    (hB : ∀ B : Subgroup G, B ≤ S → IsElemTwo B → TwoBalancedWrt B)
    (h : AbelianConnectedIn S 3 E A) : wGroup E = wGroup A := by
  obtain ⟨hES, hE, hchain⟩ := h
  suffices ∀ B : Subgroup G, Relation.ReflTransGen (fun A' B' : Subgroup G =>
      B' ≤ S ∧ IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) E B →
      B ≤ S ∧ IsAbelianTwoOfRank 3 B ∧ wGroup E = wGroup B from (this A hchain).2.2
  intro B hEB
  induction hEB with
  | refl => exact ⟨hES, hE, rfl⟩
  | tail _ hBC ih =>
    obtain ⟨hBS, hB3, hW⟩ := ih
    exact ⟨hBC.1, hBC.2.1,
      hW.trans (wGroup_eq_of_commute_in hB hBS hBC.1 hB3 hBC.2.1 hBC.2.2)⟩

end Completion

section Sylow

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowTwoIn_mem {H : Subgroup G} {a : G} (ha : a ∈ H) (ha2 : orderOf a = 2) :
    ∃ S : Subgroup G, IsSylowTwoIn S H ∧ a ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ((zpowers a).subgroupOf H) := by
    refine IsPGroup.of_equiv ?_ (subgroupOfEquivOfLe (zpowers_le.mpr ha)).symm
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨map_subtype_le _, Q, ?_⟩, ?_⟩
  · exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  · exact ⟨⟨a, ha⟩, hQ (mem_subgroupOf.mpr (mem_zpowers a)), rfl⟩

omit [Finite G] in
theorem IsSylowTwoIn.isPGroup {S H : Subgroup G} (h : IsSylowTwoIn S H) : IsPGroup 2 S := by
  obtain ⟨hSH, P, hP⟩ := h
  have hp := P.isPGroup'
  rw [hP] at hp
  exact hp.of_equiv (subgroupOfEquivOfLe hSH)

theorem IsSylowTwoIn.exists_conj_le {S H Q : Subgroup G} (h : IsSylowTwoIn S H) (hQH : Q ≤ H)
    (hQ : IsPGroup 2 Q) : ∃ c ∈ H, ∀ q ∈ Q, c * q * c⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P, hP⟩ := h
  have hp : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H T P
  refine ⟨c, c.2, fun q hq => ?_⟩
  have hqT : (⟨q, hQH hq⟩ : H) ∈ (T : Subgroup H) := hT (mem_subgroupOf.mpr hq)
  have hmem : MulAut.conj c (⟨q, hQH hq⟩ : H) ∈ ((c • T : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul _ _ _ hqT
  rw [hc, hP, mem_subgroupOf] at hmem
  simpa using hmem

omit [Finite G] in
theorem IsSylowTwoIn.eq_of_le {S H Q : Subgroup G} (h : IsSylowTwoIn S H) (hSQ : S ≤ Q)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) : Q = S := by
  obtain ⟨-, P, hP⟩ := h
  have hp : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  have hle : (P : Subgroup H) ≤ Q.subgroupOf H := by
    rw [hP]
    exact fun x hx => mem_subgroupOf.mpr (hSQ (mem_subgroupOf.mp hx))
  have heq := P.is_maximal' hp hle
  refine le_antisymm (fun q hq => ?_) hSQ
  have hq' : (⟨q, hQH hq⟩ : H) ∈ (P : Subgroup H) := by
    rw [← heq]
    exact mem_subgroupOf.mpr hq
  rw [hP] at hq'
  exact mem_subgroupOf.mp hq'

theorem exists_isElemTwo_of_three_le_pRank {H : Subgroup G} (h : 3 ≤ pRank 2 ↥H) :
    ∃ F : Subgroup G, F ≤ H ∧ IsElemTwo F ∧ 8 ≤ Nat.card F := by
  set s := {r : ℕ | ∃ B : Subgroup ↥H, IsElementaryAbelian 2 ↥B ∧ Nat.card B = 2 ^ r} with hs
  have h3 : 3 ≤ sSup s := h
  have hne : s.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn, csSup_empty] at h3
    exact absurd h3 (by decide)
  have hbdd : BddAbove s := by
    refine ⟨Nat.card H, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := card_le_card_group B
  obtain ⟨B, hBe, hBc⟩ := Nat.sSup_mem hne hbdd
  refine ⟨B.map H.subtype, map_subtype_le _, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hc := hBe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
    exact congrArg (fun w : B => ((w : ↥H) : G)) hc
  · rintro _ ⟨x, hx, rfl⟩
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x hx
    have h2' := congrArg Subtype.val h2
    rw [← pow_two]
    exact h2'
  · rw [card_map_of_injective H.subtype_injective, hBc]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ sSup s := Nat.pow_le_pow_right (by norm_num) h3

omit [Finite G] in
theorem IsElemTwo.map_conj {E : Subgroup G} (hE : IsElemTwo E) (h : G) :
    IsElemTwo (E.map (MulAut.conj h).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hE.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE.2 x hx, map_one]

end Sylow

section Corollary226

variable {G : Type} [Group G] [Finite G]

private theorem sylow_and_fusion_of_threeConnected_within {S : Subgroup G}
    (hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    {A : Subgroup G} (hAS : A ≤ S) (hA : IsElemTwo A) (h16 : 16 ≤ Nat.card A)
    (hSyl : IsSylowTwoIn S (normalizer (wGroup A : Set G))) (h3 : IsThreeConnected S) :
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) ∧
      ∀ a b : G, b ∈ S → IsExtremalIn S a → (∃ g : G, a = g⁻¹ * b * g) →
        3 ≤ pRank 2 ↥(S ⊓ centralizer ({b} : Set G)) →
        ∃ m ∈ normalizer (wGroup A : Set G), b = m⁻¹ * a * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := normalizer (wGroup A : Set G)
  have hSM : S ≤ M := hSyl.1
  have hA8 : 8 ≤ Nat.card A := by omega
  have hA3 : IsAbelianTwoOfRank 3 A := hA.isAbelianTwoOfRank hA8
  have key : ∀ E : Subgroup G, E ≤ S → IsAbelianTwoOfRank 3 E → wGroup E = wGroup A := by
    intro E hES hE
    exact wGroup_eq_of_abelianConnectedIn hB (h3 E A hES hAS hE hA3)
  have key2 : ∀ E : Subgroup G, IsElemTwo E → 8 ≤ Nat.card E → E ≤ S → ∀ h : G,
      E.map (MulAut.conj h).toMonoidHom ≤ S → h ∈ M := by
    intro E hE hE8 hES h hEh
    have hEh8 : 8 ≤ Nat.card ↥(E.map (MulAut.conj h).toMonoidHom) := by
      rw [card_map_of_injective (MulAut.conj h).injective]
      exact hE8
    have h1 := key _ hEh ((hE.map_conj h).isAbelianTwoOfRank hEh8)
    rw [wGroup_map_conj, key E hES (hE.isAbelianTwoOfRank hE8)] at h1
    exact mem_normalizer_iff_map_conj_eq.mpr h1
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨Q, hSQ⟩ := hSyl.isPGroup.exists_le_sylow
    refine ⟨Q, le_antisymm ?_ hSQ⟩
    by_contra hQS
    have hlt : S.subgroupOf Q < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hQS fun q hq => ?_
      have : (⟨q, hq⟩ : Q) ∈ S.subgroupOf Q := by rw [htop]; exact mem_top _
      exact mem_subgroupOf.mp this
    have hnil : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
    obtain ⟨y, hyN, hyS⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hyM : (y : G) ∈ M := by
      refine key2 A hA hA8 hAS y ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxQ : x ∈ Q := hSQ (hAS hx)
      have hx' : (⟨x, hxQ⟩ : Q) ∈ S.subgroupOf Q := mem_subgroupOf.mpr (hAS hx)
      have := (mem_normalizer_iff.mp hyN _).mp hx'
      exact mem_subgroupOf.mp this
    have hQ' : IsPGroup 2 ↥(S ⊔ zpowers (y : G)) :=
      Q.isPGroup'.to_le (sup_le hSQ (zpowers_le.mpr y.2))
    have heq := hSyl.eq_of_le le_sup_left (sup_le hSM (zpowers_le.mpr hyM)) hQ'
    have hyS' : (y : G) ∈ S ⊔ zpowers (y : G) :=
      (le_sup_right : zpowers (y : G) ≤ S ⊔ zpowers (y : G)) (mem_zpowers (y : G))
    rw [heq] at hyS'
    exact hyS (mem_subgroupOf.mpr hyS')
  ·
    rintro a b hbS ⟨haS, P, hP⟩ ⟨g, rfl⟩ hrank
    obtain ⟨E, hEC, hE, hE8⟩ := exists_isElemTwo_of_three_le_pRank hrank
    have hEgC : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({g⁻¹ * b * g} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxb := mem_centralizer_singleton_iff.mp (mem_inf.mp (hEC hx)).2
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * x * g * (g⁻¹ * b * g) = g⁻¹ * (x * b) * g := by group
        _ = g⁻¹ * (b * x) * g := by rw [hxb]
        _ = g⁻¹ * b * g * (g⁻¹ * x * g) := by group
    have hSylC : IsSylowTwoIn (S ⊓ centralizer ({g⁻¹ * b * g} : Set G))
        (centralizer ({g⁻¹ * b * g} : Set G)) := ⟨inf_le_right, P, hP⟩
    obtain ⟨c, hcC, hcE⟩ := hSylC.exists_conj_le hEgC (hE.map_conj g⁻¹).isPGroup
    have hhM : c * g⁻¹ ∈ M := by
      refine key2 E hE hE8 (hEC.trans inf_le_left) (c * g⁻¹) ?_
      rintro _ ⟨x, hx, rfl⟩
      have := hcE (g⁻¹ * x * g) ⟨x, hx, by simp⟩
      have h' := (mem_inf.mp this).1
      simpa [MulAut.conj_apply, mul_assoc] using h'
    refine ⟨c * g⁻¹, hhM, ?_⟩
    have hc := mem_centralizer_singleton_iff.mp hcC
    calc b = (c * g⁻¹)⁻¹ * (c * (g⁻¹ * b * g) * c⁻¹) * (c * g⁻¹) := by group
      _ = (c * g⁻¹)⁻¹ * (g⁻¹ * b * g) * (c * g⁻¹) := by
        rw [show c * (g⁻¹ * b * g) * c⁻¹ = g⁻¹ * b * g by
          rw [hc]; group]

theorem sylow_and_fusion_of_threeConnected_in {S : Subgroup G}
    (hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    {A : Subgroup G} (hA : IsElemTwo A) (h16 : 16 ≤ Nat.card A)
    (hSyl : IsSylowTwoIn S (normalizer (wGroup A : Set G))) (h3 : IsThreeConnected S) :
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) ∧
      ∀ a b : G, b ∈ S → IsExtremalIn S a → (∃ g : G, a = g⁻¹ * b * g) →
        3 ≤ pRank 2 ↥(S ⊓ centralizer ({b} : Set G)) →
        ∃ m ∈ normalizer (wGroup A : Set G), b = m⁻¹ * a * m := by
  let M := normalizer (wGroup A : Set G)
  have hAM : A ≤ M := fun a ha => GrS4.mem_normalizer_wGroup (le_normalizer ha)
  obtain ⟨c, hcM, hcA⟩ := hSyl.exists_conj_le hAM hA.isPGroup
  set A' := A.map (MulAut.conj c).toMonoidHom with hA'
  have hA'S : A' ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcA x hx
  have hA'e : IsElemTwo A' := hA.map_conj c
  have hA'16 : 16 ≤ Nat.card A' := by
    rw [hA', card_map_of_injective (MulAut.conj c).injective]
    exact h16
  have hWA' : wGroup A' = wGroup A := by
    rw [hA', wGroup_map_conj]
    exact (mem_normalizer_iff_map_conj_eq.mp hcM)
  have hmain := sylow_and_fusion_of_threeConnected_within (S := S) (A := A') hB
    hA'S hA'e hA'16 (by simpa [hWA'] using hSyl) h3
  refine ⟨hmain.1, ?_⟩
  rintro a b hbS ha hconj hrank
  obtain ⟨m, hm, hbm⟩ := hmain.2 a b hbS ha hconj hrank
  exact ⟨m, by simpa [hWA'] using hm, hbm⟩

theorem sylow_and_fusion_of_threeConnected (hB : GWTwoBalanced G) {A : Subgroup G}
    (hA : IsElemTwo A) (h16 : 16 ≤ Nat.card A) {S : Subgroup G}
    (hSyl : IsSylowTwoIn S (normalizer (wGroup A : Set G))) (h3 : IsThreeConnected S) :
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) ∧
      ∀ a b : G, b ∈ S → IsExtremalIn S a → (∃ g : G, a = g⁻¹ * b * g) →
        3 ≤ pRank 2 ↥(S ⊓ centralizer ({b} : Set G)) →
        ∃ m ∈ normalizer (wGroup A : Set G), b = m⁻¹ * a * m :=
  sylow_and_fusion_of_threeConnected_in
    (fun _ _ hE => twoBalancedWrt_of_gwTwoBalanced hB hE) hA h16 hSyl h3

theorem gorensteinWalterConnectedInput : GorensteinWalterConnectedInput := by
  intro G _ _ hB A hAc hA2 h16
  have hA : IsElemTwo A := ⟨hAc, hA2⟩
  refine ⟨fun E E₁ hE hE₁ => ?_, fun S hSM hSyl h3 => ?_⟩
  · have hWE := wGroup_eq_of_abelianConnected hB hE
    have hWE₁ := wGroup_eq_of_abelianConnected hB hE₁
    refine ⟨hWE, hWE₁, fun g hg => ?_⟩
    rw [hg, wGroup_conjugate, hWE, conjugate] at hWE₁
    exact inv_inv g ▸ inv_mem (mem_normalizer_iff_map_conj_eq.mpr hWE₁)
  · exact sylow_and_fusion_of_threeConnected hB hA h16 ⟨hSM, hSyl⟩ h3

end Corollary226

end CFSG.ComponentClassification.GrSLit
