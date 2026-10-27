module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinTors
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.SectionRank.ClassicalEven
open scoped MatrixGroups

private theorem largeEvenProj_equiv_statedProj_lin {d : ℕ} {F : Type} [Field F] :
    Nonempty (LargeEvenProj (LargeEvenSLGroup (Fin d) F) ≃*
      StatedProj (StatedSL d F)) :=
  ⟨by rw [largeEvenSLGroup_eq_statedSL]⟩

private theorem diagonal_mem_normalizer_rootSubgroupGL {k : ℕ} {F : Type} [Field F] [Fintype F]
    (a : GL (Fin (k + 2)) F)
    (hadiag : ∀ i j : Fin (k + 2), i ≠ j →
      (a : Matrix (Fin (k + 2)) (Fin (k + 2)) F) i j = 0) :
    a ∈ Subgroup.normalizer
      (rootSubgroupGL (F := F) (k + 2) : Set (GL (Fin (k + 2)) F)) := by
  classical
  have hne : ∀ i : Fin (k + 2), (a : Matrix (Fin (k + 2)) (Fin (k + 2)) F) i i ≠ 0 := by
    intro i hzero
    have h1 : ((a * a⁻¹ : GL (Fin (k + 2)) F) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) F) i i = 1 := by
      rw [mul_inv_cancel]
      simp
    rw [Units.val_mul, Matrix.mul_apply] at h1
    have hsum : (∑ j : Fin (k + 2),
        (a : Matrix (Fin (k + 2)) (Fin (k + 2)) F) i j *
          ((a⁻¹ : GL (Fin (k + 2)) F) :
            Matrix (Fin (k + 2)) (Fin (k + 2)) F) j i) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hji : j = i
      · subst hji
        rw [hzero, zero_mul]
      · rw [hadiag i j (fun h => hji h.symm), zero_mul]
    rw [hsum] at h1
    exact zero_ne_one h1
  let v : Fin (k + 2) → Fˣ :=
    fun i => Units.mk0 ((a : Matrix (Fin (k + 2)) (Fin (k + 2)) F) i i) (hne i)
  have hva : a = torusDiag v := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [coe_torusDiag, Matrix.diagonal_apply_eq]
      rfl
    · rw [hadiag i j hij, coe_torusDiag, Matrix.diagonal_apply_ne _ hij]
  have hconj : ∀ x ∈ rootSubgroupGL (F := F) (k + 2),
      a * x * a⁻¹ ∈ rootSubgroupGL (F := F) (k + 2) := by
    intro x hx
    rw [mem_rootSubgroupGL] at hx ⊢
    obtain ⟨s, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd (fun _ =>
      (v 0 : F) * s.toAdd ⟨0, 0⟩ * (((v 1)⁻¹ : Fˣ) : F)), ?_⟩
    rw [hva, ← map_inv (torusDiag (K := F))]
    exact (torusDiag_mul_linHom_mul_inv k v s).symm
  have hconj' : ∀ x ∈ rootSubgroupGL (F := F) (k + 2),
      a⁻¹ * x * a ∈ rootSubgroupGL (F := F) (k + 2) := by
    intro x hx
    rw [mem_rootSubgroupGL] at hx ⊢
    obtain ⟨s, rfl⟩ := hx
    let w : Fin (k + 2) → Fˣ := fun i => (v i)⁻¹
    have ha_inv : a⁻¹ = torusDiag w := by
      rw [hva, ← map_inv]
      rfl
    refine ⟨Multiplicative.ofAdd (fun _ =>
      (w 0 : F) * s.toAdd ⟨0, 0⟩ * (((w 1)⁻¹ : Fˣ) : F)), ?_⟩
    have h := torusDiag_mul_linHom_mul_inv k w s
    have hw : (fun i => (w i)⁻¹) = v := funext fun i => inv_inv (v i)
    rw [hw] at h
    rw [ha_inv, hva]
    exact h.symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change a * x * a⁻¹ ∈ rootSubgroupGL (F := F) (k + 2)
    exact hconj x hx
  · intro x hx
    refine ⟨a⁻¹ * x * a, hconj' x hx, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group

theorem lin_torsion_data {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F) :
    ∃ E X : Subgroup (LinPSL d F), X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ (d - 1) ∧ E ≤ Subgroup.normalizer (X : Set (LinPSL d F)) := by
  classical
  have hd2 : 2 ≤ d := h.2.2.2.2.2.2
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
  have hp : p.Prime := h.1
  have hp2 : p ≠ 2 := h.2.1
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := n)
    rw [← Nat.card_eq_fintype_card]
    exact h.2.2.2.2.1
  obtain ⟨hD_SL0, hDab, hDcard0, hDscal0⟩ := lin_diagTorsion_data h
  have hD_SL : LinDiagTorsion p (j + 2) F ≤ StatedSL (j + 2) F := by
    have h := hD_SL0
    change LinDiagTorsion p (j + 2) F ≤ LargeEvenSLGroup (Fin (j + 2)) F at h
    rw [largeEvenSLGroup_eq_statedSL] at h
    exact h
  have hDcard : Nat.card (LinDiagTorsion p (j + 2) F) = p ^ (j + 1) := by
    simpa using hDcard0
  have hDnorm : LinDiagTorsion p (j + 2) F ≤ Subgroup.normalizer
      (rootSubgroupGL (F := F) (j + 2) : Set (GL (Fin (j + 2)) F)) := by
    rw [LinDiagTorsion, Subgroup.closure_le]
    rintro a ⟨-, -, hadiag⟩
    exact diagonal_mem_normalizer_rootSubgroupGL (k := j) a hadiag
  have hDscal : ∀ z : ↥(StatedSL (j + 2) F),
      (z : GL (Fin (j + 2)) F) ∈ LinDiagTorsion p (j + 2) F →
      (z : GL (Fin (j + 2)) F) ∈ StatedScalars (Fin (j + 2)) F →
      (z : GL (Fin (j + 2)) F) = 1 := by
    intro z hzD hzK
    exact hDscal0 (z : GL (Fin (j + 2)) F) hzD hzK
  obtain ⟨E', X', hX'ne, hX'2, hE'el, hE'card, hE'norm⟩ :=
    exists_elemAbelian_le_normalizer_statedProj_of (j + 2) p (j + 1) (by omega) hp hp2
      (LinDiagTorsion p (j + 2) F) hD_SL hDscal hDcard hDab hDnorm
  obtain ⟨e⟩ := largeEvenProj_equiv_statedProj_lin (d := j + 2) (F := F)
  refine ⟨E'.map e.symm.toMonoidHom, X'.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hX'ne ((Subgroup.map_eq_bot_iff_of_injective X' (f := e.symm.toMonoidHom)
      e.symm.injective).mp hbot)
  · exact hX'2.map e.symm.toMonoidHom
  · exact hE'el.map e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE'card]
    congr 1
  · calc E'.map e.symm.toMonoidHom
        ≤ (Subgroup.normalizer (X' : Set (StatedProj (StatedSL (j + 2) F)))).map
            e.symm.toMonoidHom := Subgroup.map_mono hE'norm
      _ = Subgroup.normalizer (X'.map e.symm.toMonoidHom) :=
          Subgroup.map_equiv_normalizer_eq X' e.symm

private theorem exists_isElemAbelian_le_comap {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {r : ℕ} (hr : r.Prime) (hrN : ¬ r ∣ Nat.card N)
    {E : Subgroup (G ⧸ N)} (hE : IsElemAbelian r E) :
    ∃ B : Subgroup G, B ≤ E.comap (QuotientGroup.mk' N) ∧ IsElemAbelian r B ∧
      Nat.card B = Nat.card E := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  let ψ : ↥(E.comap π) →* G ⧸ N := π.comp (E.comap π).subtype
  have hψ : ∀ x : ↥(E.comap π), ψ x ∈ E := fun x => x.2
  let α : ↥(E.comap π) →* ↥E := ψ.codRestrict E hψ
  have hα : Function.Surjective α := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (e : G ⧸ N)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [Subgroup.mem_comap]
    rw [show π g = (e : G ⧸ N) from hg]
    exact e.2
  have hcardker : Nat.card α.ker = Nat.card N := by
    have h1 : Nat.card α.ker * Nat.card E = Nat.card ↥(E.comap π) := by
      have h := Subgroup.card_ker_mul_card_range α
      rw [MonoidHom.range_eq_top.2 hα, Subgroup.card_top] at h
      exact h
    have h2 : Nat.card ↥(E.comap π) = Nat.card E * Nat.card N :=
      CFSG.ClassicalInvolution.Sp62Rec.natCard_comap_mk N E
    have hEpos : 0 < Nat.card E :=
      Nat.card_pos_iff.2 ⟨⟨1, E.one_mem⟩, inferInstance⟩
    rw [h2, mul_comm (Nat.card α.ker) (Nat.card E)] at h1
    exact Nat.eq_of_mul_eq_mul_left hEpos h1
  have hker : ¬ r ∣ Nat.card α.ker := by
    rw [hcardker]
    exact hrN
  have htop : IsElemAbelian r (⊤ : Subgroup ↥E) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact isElemAbelian_commute hE (a : ↥E).2 (b : ↥E).2
    · apply Subtype.ext
      simpa using hE.2 (x : ↥E).1 (x : ↥E).2
  obtain ⟨B, hBelem, hBcard⟩ := rk2_lift_elemAbelian hr α hα hker htop
  refine ⟨B.map (E.comap π).subtype, Subgroup.map_subtype_le B,
    hBelem.map (E.comap π).subtype, ?_⟩
  rw [Subgroup.card_map_of_injective (E.comap π).subtype_injective, hBcard,
    Subgroup.card_top]

theorem rank_lift_center_quotient {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hxC : x ∈ Subgroup.centralizer (S : Set Ω))
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    {R : Type} [Group R] (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) {X E : Subgroup R} (hX : X ≠ ⊥)
    (hX2 : IsPGroup 2 X) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set R)) : k + 1 ≤ GLATwoLocalRank p Ω := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite R := Finite.of_surjective θ.toMonoidHom θ.surjective
  let π : ↥S →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥S))
  have hπker : π.ker = Subgroup.center ↥S := by
    have h : π = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S)) := rfl
    rw [h, MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hxS : x ∉ S := by
    intro hxSin
    have hxZ : (⟨x, hxSin⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : Ω) * x = x * (g : Ω)
      exact Subgroup.mem_centralizer_iff.mp hxC (g : Ω) g.2
    have hord : orderOf (⟨x, hxSin⟩ : ↥S) = p := by
      rw [Subgroup.orderOf_mk, orderOf_eq_prime hxp hx1]
    have hdvd : p ∣ Nat.card (Subgroup.center ↥S) := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard (Subgroup.center ↥S) hxZ
    exact hZ hdvd
  let H : Subgroup ↥S := X.comap π
  have hH_eq : H = (X.comap θ.toMonoidHom).comap
      (QuotientGroup.mk' (Subgroup.center ↥S)) := by
    change X.comap (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))) =
      (X.comap θ.toMonoidHom).comap (QuotientGroup.mk' (Subgroup.center ↥S))
    rw [Subgroup.comap_comap]
  have hcardXcomap : Nat.card (X.comap θ.toMonoidHom) = Nat.card X := by
    rw [← Subgroup.card_map_of_injective (K := X.comap θ.toMonoidHom)
        (f := θ.toMonoidHom) θ.injective,
      Subgroup.map_comap_eq_self_of_surjective θ.surjective X]
  have hcardH : Nat.card H = Nat.card X * Nat.card (Subgroup.center ↥S) := by
    rw [hH_eq, CFSG.ClassicalInvolution.Sp62Rec.natCard_comap_mk
        (Subgroup.center ↥S) (X.comap θ.toMonoidHom), hcardXcomap]
  let E' : Subgroup (↥S ⧸ Subgroup.center ↥S) := E.comap θ.toMonoidHom
  have hE' : IsElemAbelian p E' := hE.comap θ.injective
  obtain ⟨B, hBle, hBelem, hBcard⟩ := exists_isElemAbelian_le_comap hp hZ hE'
  have hE'card : Nat.card E' = Nat.card E := by
    rw [← Subgroup.card_map_of_injective (K := E') (f := θ.toMonoidHom) θ.injective,
      Subgroup.map_comap_eq_self_of_surjective θ.surjective E]
  have hBcard' : Nat.card B = p ^ k := by
    rw [hBcard, hE'card, hEcard]
  have hBnle : B ≤ Subgroup.normalizer (H : Set ↥S) := by
    intro b hb
    have hb' : π b ∈ E := by
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥S)) b ∈ E' := hBle hb
      exact Subgroup.mem_comap.1 h1
    change b ∈ Subgroup.normalizer ((X.comap π : Subgroup ↥S) : Set ↥S)
    rw [← Subgroup.comap_normalizer_eq_of_surjective X hπsurj, Subgroup.mem_comap]
    exact hXE hb'
  have hcoprime : Nat.Coprime p (Nat.card H) := by
    rw [hcardH]
    refine Nat.Coprime.mul_right ?_ ?_
    · obtain ⟨n, hn⟩ := hX2.exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right n
    · exact (hp.coprime_iff_not_dvd).2 hZ
  obtain ⟨P, -, hPnorm⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_pgroup_actor_sylow_containing p 2 hp Nat.prime_two
      B H ⊥ (isPGroup_of_isElemAbelian hBelem) hBnle hcoprime bot_le
      (IsPGroup.of_bot (p := 2)) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  let P₀ : Subgroup ↥S := (P : Subgroup H).map H.subtype
  let PΩ : Subgroup Ω := P₀.map S.subtype
  have h2H : 2 ∣ Nat.card H := by
    rw [hcardH]
    refine dvd_mul_of_dvd_left ?_ _
    have h1 : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot X).mpr hX
    exact (hX2.card_eq_or_dvd).resolve_left h1.ne'
  have hP₀ne : P₀ ≠ ⊥ := by
    change (P : Subgroup H).map H.subtype ≠ ⊥
    intro hbot
    exact P.ne_bot_of_dvd_card h2H
      ((Subgroup.map_eq_bot_iff_of_injective (P : Subgroup H) (f := H.subtype)
        H.subtype_injective).mp hbot)
  have hPΩne : PΩ ≠ ⊥ := by
    change P₀.map S.subtype ≠ ⊥
    intro hbot
    exact hP₀ne ((Subgroup.map_eq_bot_iff_of_injective P₀ (f := S.subtype)
      S.subtype_injective).mp hbot)
  have hPΩ2 : IsPGroup 2 PΩ := by
    simpa only [PΩ, P₀] using (P.isPGroup'.map H.subtype).map S.subtype
  have hBΩnorm : B.map S.subtype ≤ Subgroup.normalizer (PΩ : Set Ω) := by
    have h1 : B.map S.subtype ≤ Subgroup.normalizer (P₀.map S.subtype : Set Ω) :=
      (Subgroup.map_mono hPnorm).trans (Subgroup.le_normalizer_map S.subtype)
    simpa only [PΩ] using h1
  have hcomm : ∀ a ∈ B.map S.subtype, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    rintro a ⟨a', ha', rfl⟩ b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hax : Commute (a' : Ω) x :=
      Subgroup.mem_centralizer_iff.mp hxC (a' : Ω) a'.2
    exact (hax.zpow_right n).eq
  have hBΩel : IsElemAbelian p (B.map S.subtype) := hBelem.map S.subtype
  have hE1el : IsElemAbelian p (B.map S.subtype ⊔ Subgroup.zpowers x) :=
    IsElemAbelian.sup_of_commute hBΩel (isElemAbelian_zpowers hxp) hcomm
  have hzxcent : Subgroup.zpowers x ≤
      Subgroup.centralizer (B.map S.subtype : Set Ω) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha x (Subgroup.mem_zpowers x)
  have hzxnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (B.map S.subtype : Set Ω) :=
    hzxcent.trans (Subgroup.centralizer_le_normalizer _)
  have hBΩcard : Nat.card (B.map S.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective (K := B) (f := S.subtype) S.subtype_injective, hBcard']
  have hzpcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hdisj : Disjoint (B.map S.subtype) (Subgroup.zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro y hyB hyzx
    have hyS : y ∈ S := Subgroup.map_subtype_le B hyB
    haveI : Fact (Nat.card (Subgroup.zpowers x)).Prime := ⟨by rw [hzpcard]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        (S.subgroupOf (Subgroup.zpowers x)) with h | h
    · have hy : (⟨y, hyzx⟩ : Subgroup.zpowers x) ∈
          S.subgroupOf (Subgroup.zpowers x) := hyS
      rw [h] at hy
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hy)
    · exfalso
      have hxmem : (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) ∈
          S.subgroupOf (Subgroup.zpowers x) := by rw [h]; trivial
      exact hxS hxmem
  have hE1card :
      Nat.card (B.map S.subtype ⊔ Subgroup.zpowers x : Subgroup Ω) = p ^ (k + 1) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (B.map S.subtype) (Subgroup.zpowers x) hzxnorm hdisj, hBΩcard, hzpcard,
      ← pow_succ]
  have hE1norm : B.map S.subtype ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (PΩ : Set Ω) := by
    refine sup_le hBΩnorm ?_
    have hxcentPΩ : x ∈ Subgroup.centralizer (PΩ : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyS : y ∈ S := by
        change y ∈ P₀.map S.subtype at hy
        exact Subgroup.map_subtype_le P₀ hy
      exact Subgroup.mem_centralizer_iff.mp hxC y hyS
    exact (Subgroup.zpowers_le.mpr hxcentPΩ).trans (Subgroup.centralizer_le_normalizer _)
  have hbound := card_le_pow_glaTwoLocalRank hp hE1el hPΩne hPΩ2 hE1norm
  rw [hE1card] at hbound
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hbound

theorem lin_rank_lower {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (θ : ↥S ⧸ Subgroup.center ↥S ≃* LinPSL d F)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) : p ^ d ≤ Nat.card B := by
  obtain ⟨E, X, hX, hX2, hE, hEc, hXE⟩ := lin_torsion_data h
  have hxC : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hrank := rank_lift_center_quotient hcfg.prime hcfg.odd hxC hcfg.ne_one
    (hcfg.elem.2 x hcfg.mem) hZ θ hX hX2 hE hEc hXE
  have hd2 : 2 ≤ d := h.2.2.2.2.2.2
  have hcard : Nat.card B = p ^ GLATwoLocalRank p Ω := hcfg.bmax.2.1
  rw [hcard]
  exact Nat.pow_le_pow_right hcfg.prime.pos (by omega)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
