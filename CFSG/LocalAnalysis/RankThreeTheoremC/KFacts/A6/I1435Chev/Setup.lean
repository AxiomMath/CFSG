module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Common

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

@[expose] def FourLines {K : Type} [Group K] (E : Subgroup K) (x : K) : Prop :=
  ∃ k : Fin 4 → K, (∀ i, k i * x * (k i)⁻¹ ∈ E) ∧
    ∀ i j, zpowers (k i * x * (k i)⁻¹) = zpowers (k j * x * (k j)⁻¹) → i = j

structure Shape (K : Type) [Group K] [Finite K] : Prop where
  dvd27 : 27 ∣ Nat.card K
  not_dvd243 : ¬ 3 ^ 5 ∣ Nat.card K
  exists_E : ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 27
  abelian_exp : ∀ A : Subgroup K, IsPGroup 3 A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    27 ≤ Nat.card A → ∀ a ∈ A, a ^ 3 = 1
  pow_nine : ∀ g : K, IsPGroup 3 (zpowers g) → g ^ 9 = 1
  sylow81 : ∀ S : Subgroup K, IsPGroup 3 S → Nat.card S = 81 → Nonempty (↥S ≃* W3)
  point : ∀ E : Subgroup K, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E = 27 →
    ∃ x ∈ E, x ≠ 1 ∧ CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set K)) ∧
      ¬ FourLines E x

@[expose] def AutShape (K : Type) [Group K] : Prop :=
  ∃ A : Subgroup (MulAut K), (∀ a ∈ A, a ^ 3 = 1) ∧ Nat.card A = 27

@[expose] def Witness (K : Type) [Group K] : Prop :=
  ∃ E : Subgroup K, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ Nat.card E = 27 ∧
    ∀ x ∈ E, x ≠ 1 →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set K)) ∨ FourLines E x

theorem Shape.not_witness {K : Type} [Group K] [Finite K] (h : Shape K) : ¬ Witness K := by
  rintro ⟨E, hEc, hE27, hE⟩
  obtain ⟨x, hxE, hx1, hsolv, hfour⟩ := h.point E hEc hE27
  rcases hE x hxE hx1 with h' | h'
  · exact h' hsolv
  · exact hfour h'

theorem pow_three_of_mem_wBase {w : W3} (hw : w ∈ wBase) : w ^ 3 = 1 := by
  have hw' : w = baseHom w.left := RegularWreathProduct.ext rfl (mem_wBase.mp hw)
  rw [hw', ← map_pow, fun_cube, map_one]

theorem pow_nine_W3 (w : W3) : w ^ 9 = 1 := by
  have h3 : w ^ 3 ∈ wBase := by
    show RegularWreathProduct.rightHom (w ^ 3) = 1
    rw [map_pow]
    exact m3_cube _
  rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, pow_three_of_mem_wBase h3]

theorem W3_not_comm : ∃ a b : W3, a * b ≠ b * a := by
  refine ⟨baseHom (fun q => q), RegularWreathProduct.inl q1, fun h => ?_⟩
  have := congrArg (fun w : W3 => w.left 1) h
  revert this
  decide

theorem not_comm_of_mulEquiv_W3 {S : Type*} [Group S] (e : S ≃* W3) :
    ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := W3_not_comm
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

section Transport

variable {K L : Type} [Group K] [Group L]

theorem FourLines.map {E : Subgroup K} {x : K} (φ : K →* L) (hφ : Function.Injective φ)
    (h : FourLines E x) : FourLines (E.map φ) (φ x) := by
  obtain ⟨k, hk, hinj⟩ := h
  refine ⟨fun i => φ (k i), fun i => ?_, fun i j hij => hinj i j ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_map_of_mem φ (hk i)
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      ← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers] at hij
    exact map_injective hφ hij

theorem not_isPSolvable_map [Finite K] [Finite L] {φ : K →* L} (hφ : Function.Injective φ)
    {H : Subgroup K} (hH : ¬ CFSG.HallHigman.IsPSolvable 3 ↥H) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(H.map φ) := fun h =>
  hH (isPSolvable_of_equiv (equivMapOfInjective H φ hφ).symm h)

theorem not_isPSolvable_centralizer_map [Finite K] [Finite L] {φ : K →* L}
    (hφ : Function.Injective φ) {x : K}
    (h : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set K))) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({φ x} : Set L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hs
  have hle : (centralizer ({x} : Set K)).map φ ≤ centralizer ({φ x} : Set L) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  exact not_isPSolvable_map hφ h
    (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hs hle)

theorem Witness.map [Finite K] [Finite L] {φ : K →* L} (hφ : Function.Injective φ)
    (h : Witness K) : Witness L := by
  obtain ⟨E, hEc, hE27, hE⟩ := h
  refine ⟨E.map φ, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  · rw [card_map_of_injective hφ, hE27]
  · rintro _ ⟨y, hy, rfl⟩ hy1
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
    rcases hE y hy hy1' with h' | h'
    · exact Or.inl (not_isPSolvable_centralizer_map hφ h')
    · exact Or.inr (h'.map φ hφ)

theorem Witness.of_mulEquiv [Finite K] [Finite L] (e : K ≃* L) (h : Witness K) : Witness L :=
  h.map (φ := e.toMonoidHom) e.injective

end Transport

section Conj

variable {L : Type} [Group L] [Finite L]

theorem exists_conj_of_card27 (h243 : ¬ 3 ^ 5 ∣ Nat.card L)
    (h81 : ∀ S : Subgroup L, IsPGroup 3 S → Nat.card S = 81 → Nonempty (↥S ≃* W3))
    {A B : Subgroup L} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hcA : Nat.card A = 27) (hcB : Nat.card B = 27) :
    ∃ g : L, A = B.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have h27 : 3 ^ 3 ∣ Nat.card L := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hcA]
    exact card_subgroup_dvd_card A
  have hle3 : 3 ≤ (Nat.card L).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hL0).1 h27
  have hle4 : (Nat.card L).factorization 3 ≤ 4 := by
    by_contra h
    exact h243 ((Nat.prime_three.pow_dvd_iff_le_factorization hL0).2 (by omega))
  by_cases h81d : (Nat.card L).factorization 3 = 4
  · refine exists_conj_eq (fun Q => h81 Q Q.isPGroup' ?_) hA hB hcA hcB
    rw [Sylow.card_eq_multiplicity, h81d]
    norm_num
  · have h3 : (Nat.card L).factorization 3 = 3 := by omega
    have hcA' : Nat.card A = 3 ^ (Nat.card L).factorization 3 := by rw [h3, hcA]; norm_num
    have hcB' : Nat.card B = 3 ^ (Nat.card L).factorization 3 := by rw [h3, hcB]; norm_num
    let SA : Sylow 3 L := Sylow.ofCard A hcA'
    let SB : Sylow 3 L := Sylow.ofCard B hcB'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L SB SA
    refine ⟨g, ?_⟩
    have h1 : ((g • SB : Sylow 3 L) : Subgroup L) = (SA : Subgroup L) := congrArg _ hg
    rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Sylow.coe_ofCard,
      pointwise_smul_def] at h1
    exact h1.symm

end Conj

section Point

variable {K : Type} [Group K]

@[expose] def centralizerConjEquiv (g x : K) :
    ↥(centralizer ({x} : Set K)) ≃* ↥(centralizer ({g * x * g⁻¹} : Set K)) :=
  ((MulAut.conj g).subgroupMap (centralizer ({x} : Set K))).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
          _ = g * (x * z) * g⁻¹ := by rw [hz]
          _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
      · intro hy
        refine ⟨g⁻¹ * y * g, ?_, ?_⟩
        swap
        · show g * (g⁻¹ * y * g) * g⁻¹ = y
          group
        calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
          _ = x * (g⁻¹ * y * g) := by group))

theorem FourLines.conj {E : Subgroup K} {x : K} (g : K) (h : FourLines E x) :
    FourLines (E.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) := by
  have := h.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

end Point

section Ambient

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X}

@[expose] noncomputable def sylowEquivW3 (e : ↥(P : Subgroup X) ≃* W3) (Q : Sylow 3 X) :
    ↥(Q : Subgroup X) ≃* W3 :=
  (Sylow.equiv Q P).trans e

theorem pow_nine_of_isPGroup (e : ↥(P : Subgroup X) ≃* W3) {g : X}
    (hg : IsPGroup 3 (zpowers g)) : g ^ 9 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  have hgQ : g ∈ (Q : Subgroup X) := hQ (mem_zpowers g)
  have h := pow_nine_W3 (sylowEquivW3 e Q ⟨g, hgQ⟩)
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h
  exact congrArg Subtype.val h

theorem pow_three_of_abelian (e : ↥(P : Subgroup X) ≃* W3) {A : Subgroup X}
    (hA : IsPGroup 3 A) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h27 : 27 ≤ Nat.card A) :
    ∀ a ∈ A, a ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  have hAB := eq_baseIn_of_comm (sylowEquivW3 e Q) hQ hc h27
  intro a ha
  rw [hAB] at ha
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := ha
  simp only [MulEquiv.coe_toMonoidHom, subtype_apply]
  rw [← Subgroup.coe_pow, ← map_pow, pow_three_of_mem_wBase hw, map_one, Subgroup.coe_one]

variable {K : Subgroup X}

theorem autShape_of_hyp (hKn : K.Normal) (hCK : centralizer (K : Set X) = ⊥)
    (e : ↥(P : Subgroup X) ≃* W3) : AutShape ↥K := by
  set E := Open.thompsonSubgroup (P : Subgroup X)
  have hEB : E = baseIn e := thompsonSubgroup_eq_baseIn e
  let φ : X →* MulAut ↥K := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    change MulAut.conjNormal g = 1 at hg
    have hg' : g ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro k hk
      have := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : X)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc k * g = g * k * g⁻¹ * g := by rw [this]
        _ = g * k := by group
    rw [hCK, mem_bot] at hg'
    exact hg'
  refine ⟨E.map φ, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, pow_three_of_abelian e (P := P) (A := E) ?_ ?_ ?_ a ha, map_one]
    · exact IsPGroup.of_card (n := 3) (by rw [hEB, card_baseIn]; norm_num)
    · intro a ha b hb
      rw [hEB] at ha hb
      exact baseIn_comm e ha hb
    · rw [hEB, card_baseIn]
  · rw [card_map_of_injective hφ, hEB, card_baseIn]

theorem shape_of_hyp (e : ↥(P : Subgroup X) ≃* W3)
    (hEK : Open.thompsonSubgroup (P : Subgroup X) ≤ K) {x : X}
    (hxJ : x ∈ Open.thompsonSubgroup (P : Subgroup X)) (hx1 : x ≠ 1)
    (hlines : conjLinesIn (Open.thompsonSubgroup (P : Subgroup X)) x = 3)
    (hsolv : CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set X))) : Shape ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Open.thompsonSubgroup (P : Subgroup X) with hE
  have hEB : E = baseIn e := thompsonSubgroup_eq_baseIn e
  have hxK : x ∈ K := hEK hxJ
  have hpmap : ∀ {A : Subgroup ↥K}, IsPGroup 3 A → IsPGroup 3 (A.map K.subtype) := fun hA =>
    hA.map K.subtype
  have hcmap : ∀ A : Subgroup ↥K, Nat.card (A.map K.subtype) = Nat.card A := fun A =>
    card_map_of_injective K.subtype_injective
  set E' : Subgroup ↥K := E.subgroupOf K with hE'
  have hE'c : Nat.card E' = 27 := by
    rw [hE', Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv, hEB, card_baseIn]
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    rw [mem_subgroupOf, hEB] at ha hb
    exact Subtype.ext (baseIn_comm e ha hb)
  have h243 : ¬ 3 ^ 5 ∣ Nat.card ↥K := by
    intro h
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 h
    have hc : Nat.card (H.map K.subtype) = 3 ^ 5 := by rw [hcmap, hH]
    have := card_dvd_of_isPGroup e (IsPGroup.of_card hc)
    rw [hc] at this
    norm_num at this
  have h81 : ∀ S : Subgroup ↥K, IsPGroup 3 S → Nat.card S = 81 → Nonempty (↥S ≃* W3) := by
    intro S hS hS81
    obtain ⟨eS⟩ := nonempty_mulEquiv_W3 e (hpmap hS) (by rw [hcmap, hS81])
    exact ⟨(equivMapOfInjective S K.subtype K.subtype_injective).trans eS⟩
  refine ⟨?_, h243, ⟨E', ⟨⟨⟨fun a b => Subtype.ext (hE'comm a a.2 b b.2)⟩⟩, ?_⟩, hE'c⟩, ?_, ?_,
    h81, ?_⟩
  · rw [← hE'c]
    exact card_subgroup_dvd_card E'
  · intro a ha
    have h3 := pow_three_of_abelian e (A := E) (IsPGroup.of_card (n := 3)
      (by rw [hEB, card_baseIn]; norm_num)) (fun a ha b hb => by
        rw [hEB] at ha hb
        exact baseIn_comm e ha hb) (by rw [hEB, card_baseIn]) (a : X) ha
    exact Subtype.ext h3
  · intro A hA hAc hA27 a ha
    have h3 := pow_three_of_abelian e (hpmap hA) (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [subtype_apply]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hAc u hu v hv]) (by rw [hcmap]; exact hA27)
      (a : X) (mem_map_of_mem _ ha)
    exact Subtype.ext h3
  · intro g hg
    have h9 := pow_nine_of_isPGroup e (g := (g : X)) (by
      have := hg.map K.subtype
      rwa [MonoidHom.map_zpowers] at this)
    exact Subtype.ext h9
  ·
    intro E₁ hE₁c hE₁27
    obtain ⟨g, hg⟩ := exists_conj_of_card27 h243 h81 hE₁c hE'comm hE₁27 hE'c
    refine ⟨g * ⟨x, hxK⟩ * g⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [hg]
      exact ⟨⟨x, hxK⟩, (show (⟨x, hxK⟩ : ↥K) ∈ E.subgroupOf K from hxJ), rfl⟩
    · intro h
      apply hx1
      have : (⟨x, hxK⟩ : ↥K) = 1 := by
        calc (⟨x, hxK⟩ : ↥K) = g⁻¹ * (g * ⟨x, hxK⟩ * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      exact congrArg Subtype.val this
    ·
      have hsK : CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({(⟨x, hxK⟩ : ↥K)} : Set ↥K)) := by
        by_contra hns
        exact not_isPSolvable_centralizer hxK _ le_rfl hns hsolv
      exact isPSolvable_of_equiv (centralizerConjEquiv g _) hsK
    · intro hfour
      have h1 := hfour.conj g⁻¹
      have h2 : E₁.map (MulAut.conj g⁻¹).toMonoidHom = E' := by
        rw [hg, map_map]
        have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
            MonoidHom.id ↥K := by
          ext y
          simp [mul_assoc]
        rw [this, map_id]
      rw [h2, show g⁻¹ * (g * ⟨x, hxK⟩ * g⁻¹) * g⁻¹⁻¹ = ⟨x, hxK⟩ by group] at h1
      obtain ⟨k, hk, hinj⟩ := h1
      refine conjLinesIn_ne_three hEK (MonoidHom.id ↥K) Function.injective_id hxK k
        (fun i => ?_) (fun i j hij => hinj i j hij) hlines
      rw [map_id]
      exact hk i

end Ambient

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
