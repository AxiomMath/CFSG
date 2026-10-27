module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fusion
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def NoL3Comp {G : Type} [Group G] (C : Subgroup G) : Prop :=
  ∀ J : Subgroup G, GLAPComponent 3 C J → ∀ p : ℕ, ¬ IsL3Kind p (barOf 3 J)

theorem isL3Kind_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsL3Kind p X) : IsL3Kind p Y := by
  rcases h with h | ⟨W, hW, hWSL, ⟨f⟩⟩
  · exact Or.inl (SL3EpsOfChar.of_mulEquiv' e h)
  · exact Or.inr ⟨W, hW, hWSL, ⟨e.symm.trans f⟩⟩

theorem noL3Comp_of_injective {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (φ : G →* G') (hφ : Function.Injective φ) {C : Subgroup G} (h : NoL3Comp (C.map φ)) :
    NoL3Comp C := by
  intro J hJ p hL
  have hc : ∀ y ∈ C ⊓ φ.ker, ∀ x ∈ C, x * y = y * x := fun y hy x _ => by
    have : y = 1 := hφ ((MonoidHom.mem_ker.1 hy.2).trans (map_one φ).symm)
    rw [this, mul_one, one_mul]
  have hJ' := glaPComponent_map_central Nat.prime_three φ hc hJ
  obtain ⟨e⟩ := barEquiv_of_mulEquiv (J.equivMapOfInjective φ hφ)
  exact h _ hJ' p (isL3Kind_of_mulEquiv e hL)

theorem noL3Comp_map_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') {C : Subgroup G} (h : NoL3Comp C) : NoL3Comp (C.map e.toMonoidHom) := by
  refine noL3Comp_of_injective e.symm.toMonoidHom e.symm.injective ?_
  have : (C.map e.toMonoidHom).map e.symm.toMonoidHom = C := by
    rw [Subgroup.map_map]
    have h1 : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [h1, Subgroup.map_id]
  rw [this]
  exact h

theorem noL3Comp_conj_class {G : Type} [Group G] [Finite G] {P : Subgroup G} {X k : G}
    (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2)
    (h : NoL3Comp (Subgroup.centralizer ({X} : Set G) ⊓ P)) :
    NoL3Comp (Subgroup.centralizer ({k * X ^ e * k⁻¹} : Set G) ⊓ P) := by
  rw [← map_centralizer_conj_class' hX3 hk he]
  exact noL3Comp_map_mulEquiv (MulAut.conj k) h

theorem noL3Comp_centralizer_of_isConj {M : Type} [Group M] [Finite M] {x y : M} (hxy : IsConj x y)
    (h : NoL3Comp (Subgroup.centralizer ({x} : Set M))) :
    NoL3Comp (Subgroup.centralizer ({y} : Set M)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  have := noL3Comp_map_mulEquiv (MulAut.conj c) h
  rwa [map_centralizer_mulEquiv, MulAut.conj_apply, hc] at this

@[expose] def NoL3Dvd (N : ℕ) : Prop :=
  ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → ¬ L3Ord r ε ∣ N * e

@[expose] def L3DvdCheck (N B : ℕ) : Bool :=
  (List.range B).all fun i => [true, false].all fun ε => [1, 3].all fun e =>
    decide (¬ L3Ord (i + 4) ε ∣ N * e)

theorem noL3Dvd_of_check {N B : ℕ} (hN : 0 < N) (hB : 12 * N < (B + 4) ^ 8)
    (h : L3DvdCheck N B = true) : NoL3Dvd N := by
  intro r ε e he hc hdvd
  have hr4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (hc.2 rfl).1
    · exact (hc.1 rfl).1
  have hle : L3Ord r ε ≤ N * e := Nat.le_of_dvd (by rcases he with rfl | rfl <;> omega) hdvd
  have hrB : r < B + 4 := by
    by_contra hge
    push Not at hge
    have h1 : (B + 4) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hge 8
    have h2 := L3Ord_pow_le hc
    have h3 : 4 * (N * e) ≤ 12 * N := by rcases he with rfl | rfl <;> omega
    omega
  have hall := List.all_eq_true.1 h (r - 4) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 hall ε (by cases ε <;> simp)
  have h3 := List.all_eq_true.1 h2 e (by rcases he with rfl | rfl <;> simp)
  have hr : r - 4 + 4 = r := by omega
  rw [hr] at h3
  exact of_decide_eq_true h3 hdvd

@[expose] def NoL3DvdPrime (N q : ℕ) : Prop :=
  ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → L3Ord r ε ∣ N * e → q ∣ L3Ord r ε

@[expose] def L3PrimeCheck (N q B : ℕ) : Bool :=
  (List.range B).all fun i => [true, false].all fun ε => [1, 3].all fun e =>
    decide (L3Ord (i + 4) ε ∣ N * e → q ∣ L3Ord (i + 4) ε)

theorem noL3DvdPrime_of_check {N q B : ℕ} (hN : 0 < N) (hB : 12 * N < (B + 4) ^ 8)
    (h : L3PrimeCheck N q B = true) : NoL3DvdPrime N q := by
  intro r ε e he hc hdvd
  have hr4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (hc.2 rfl).1
    · exact (hc.1 rfl).1
  have hle : L3Ord r ε ≤ N * e := Nat.le_of_dvd (by rcases he with rfl | rfl <;> omega) hdvd
  have hrB : r < B + 4 := by
    by_contra hge
    push Not at hge
    have h1 : (B + 4) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hge 8
    have h2 := L3Ord_pow_le hc
    have h3 : 4 * (N * e) ≤ 12 * N := by rcases he with rfl | rfl <;> omega
    omega
  have hall := List.all_eq_true.1 h (r - 4) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 hall ε (by cases ε <;> simp)
  have h3 := List.all_eq_true.1 h2 e (by rcases he with rfl | rfl <;> simp)
  have hr : r - 4 + 4 = r := by omega
  rw [hr] at h3
  exact of_decide_eq_true h3 hdvd

theorem noL3Comp_of_not_dvd {M : Type} [Group M] [Finite M] {C : Subgroup M} {q : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) (hN : NoL3DvdPrime (Nat.card M) q) (hqC : ¬ q ∣ Nat.card ↥C) : NoL3Comp C := by
  intro J hJ p hL
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  have hdvdC : Nat.card (barOf 3 J) ∣ Nat.card ↥C :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJ.1)
  have hdvdM : Nat.card (barOf 3 J) ∣ Nat.card M := hdvdC.trans (Subgroup.card_subgroup_dvd_card C)
  have hL3 : L3Ord r ε ∣ Nat.card M * e := by
    rw [← hcard]
    exact Nat.mul_dvd_mul_right hdvdM e
  have hq' := hN r ε e he hc hL3
  rw [← hcard] at hq'
  have hqJ : q ∣ Nat.card (barOf 3 J) := by
    rcases (Nat.Prime.dvd_mul hq).1 hq' with h | h
    · exact h
    · exfalso
      rcases he with rfl | rfl
      · exact hq.one_lt.ne' (Nat.dvd_one.1 h)
      · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)
  exact hqC (hqJ.trans hdvdC)

theorem not_dvd_card_centralizer_of_free {M : Type} [Group M] [Finite M] {q : ℕ} (hq : q.Prime)
    (hfree : ∀ y : M, orderOf y = q → ¬ 3 ∣ Nat.card (Subgroup.centralizer ({y} : Set M)))
    {x : M} (hx : orderOf x = 3) : ¬ q ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set M)) := by
  intro hdvd
  haveI := Fact.mk hq
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hy' : orderOf (y : M) = q := by rw [Subgroup.orderOf_coe]; exact hy
  refine hfree (y : M) hy' ?_
  have hxy : x ∈ Subgroup.centralizer ({(y : M)} : Set M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 y.2).symm
  have h3 := orderOf_dvd_natCard (⟨x, hxy⟩ : ↥(Subgroup.centralizer ({(y : M)} : Set M)))
  rw [Subgroup.orderOf_mk, hx] at h3
  exact h3

theorem noL3Comp_of_noDvd {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hN : NoL3Dvd (Nat.card ↥C)) : NoL3Comp C := by
  intro J hJ p hL
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  have hdvd : Nat.card (barOf 3 J) ∣ Nat.card ↥C :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJ.1)
  exact hN r ε e he hc (by rw [← hcard]; exact Nat.mul_dvd_mul_right hdvd e)

theorem noL3Comp_of_solvable {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hC : Group.IsSolvable ↥C) : NoL3Comp C := by
  intro J hJ p hL
  have hone := hom_eq_one_of_solvable Nat.prime_three hJ (MonoidHom.id ↥C)
  have hJ0 : J = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g = 1 := congrArg Subtype.val (hone g hg)
    exact Subgroup.mem_bot.2 h1
  have hq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  have hnt := nontrivial_of_isQuasisimple hq
  subst hJ0
  have hsub : Subsingleton (barOf 3 (⊥ : Subgroup G)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  exact (not_nontrivial_iff_subsingleton.2 hsub) hnt

theorem glaPPrimeCore_eq_bot_of_glaPComponent {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hC : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J) : GLAPPrimeCore 3 ↥J = ⊥ := by
  have h1 : GLAPPrimeCoreOf 3 J ≤ GLAPPrimeCoreOf 3 C :=
    LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hJ.2.1
  rw [hC] at h1
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : G) ∈ GLAPPrimeCoreOf 3 J := (Lemma512Ns.mem_gLAPPrimeCoreOf_iff 3 J _).2 ⟨x.2, hx⟩
  have h2 := h1 hx'
  rw [Subgroup.mem_bot] at h2 ⊢
  exact Subtype.ext h2

theorem isComponentOf_of_glaPComponent' {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hC : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J) : IsComponentOf J C := by
  have hcore := glaPPrimeCore_eq_bot_of_glaPComponent hC hJ
  have e : barOf 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact ⟨hJ.1, hJ.2.1, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e
    (isQuasisimple_quotient_of_glaPComponent hJ)⟩

theorem card_barOf_of_glaPComponent {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hC : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J) :
    Nat.card (barOf 3 J) = Nat.card ↥J := by
  have hcore := glaPPrimeCore_eq_bot_of_glaPComponent hC hJ
  have e : barOf 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact Nat.card_congr e.toEquiv

theorem noL3Comp_of_no_component {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hO : GLAPPrimeCoreOf 3 C = ⊥) (h : ∀ K : Subgroup G, IsComponentOf K C → False) :
    NoL3Comp C := fun J hJ _ _ => h J (isComponentOf_of_glaPComponent' hO hJ)

private theorem subgroupOf_commutator_self' {G : Type*} [Group G] (C : Subgroup G) :
    ⁅C, C⁆.subgroupOf C = commutator ↥C := by
  rw [← Subgroup.map_subtype_commutator C]
  exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _

private theorem commutator_self_le' {G : Type*} [Group G] (C : Subgroup G) : ⁅C, C⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)

private theorem le_commutator_of_perfect' {G : Type*} [Group G] {C H : Subgroup G} (hH : H ≤ C)
    (hperf : commutator ↥H = ⊤) : H ≤ ⁅C, C⁆ := by
  have h1 : ⁅H, H⁆ = H := by
    rw [← Subgroup.map_subtype_commutator H, hperf, Subgroup.map_top, Subgroup.range_subtype]
  calc H = ⁅H, H⁆ := h1.symm
    _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hH hH

theorem noL3Comp_of_derived_simple {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hO : GLAPPrimeCoreOf 3 C = ⊥) (hs : IsSimpleGroup ↥⁅C, C⁆)
    (hNo : NoL3Eq (Nat.card ↥⁅C, C⁆)) : NoL3Comp C := by
  intro J hJ p hL
  have hK : IsComponentOf J C := isComponentOf_of_glaPComponent' hO hJ
  have hN : (⁅C, C⁆.subgroupOf C).Normal := by
    rw [subgroupOf_commutator_self']; infer_instance
  have hJN : J = ⁅C, C⁆ := component_eq_of_normal_simple hK (commutator_self_le' C) hN hs
    (fun H hH hperf => le_commutator_of_perfect' hH hperf)
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  rw [card_barOf_of_glaPComponent hO hJ, hJN] at hcard
  exact hNo r ε e he hc hcard

theorem noL3Comp_of_quasisimple {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥C) (hO : GLAPPrimeCoreOf 3 C = ⊥)
    (hNo : NoL3Eq (Nat.card ↥C)) : NoL3Comp C := by
  intro J hJ p hL
  have hK : IsComponentOf J C := isComponentOf_of_glaPComponent' hO hJ
  have hCC : IsComponentOf C C := ⟨le_rfl, CFSG.Open.IsSubnormal.refl C, hq⟩
  have hJC : J = C := by
    rcases b3Lie_comp_le_or_comm hCC hK.1 hK.2.1 with h | h
    · exact le_antisymm hK.1 h
    · exfalso
      obtain ⟨a, b, hab⟩ := b3Lie_exists_noncomm_of_isQuasisimple hK.2.2
      have h1 := Subgroup.commutator_mem_commutator (hK.1 a.2) b.2
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab (Subtype.ext h1)
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  rw [card_barOf_of_glaPComponent hO hJ, hJC] at hcard
  exact hNo r ε e he hc hcard

theorem isQuasisimple_native_of_open {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem isQuasisimple_open_of_native {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨hQ.1.commutator_eq_top, hQ.2.1⟩

theorem not_nontrivial_barOf_bot {G : Type} [Group G] :
    ¬ Nontrivial (barOf 3 (⊥ : Subgroup G)) := by
  intro hnt
  have hsub : Subsingleton (barOf 3 (⊥ : Subgroup G)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  exact (not_nontrivial_iff_subsingleton.2 hsub) hnt

theorem noL3Comp_of_normal_quasisimple {G : Type} [Group G] [Finite G] {C L : Subgroup G}
    (hLC : L ≤ C) (hLn : (L.subgroupOf C).Normal) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hperf : ∀ H : Subgroup G, H ≤ C → commutator ↥H = ⊤ → H ≤ L)
    (hNo : ∀ d : ℕ, d ∣ Nat.card ↥(Subgroup.center ↥L) → Nat.Coprime d 3 →
      NoL3Eq (Nat.card ↥L / d)) : NoL3Comp C := by
  intro J hJ p hL3
  have hCL : IsComponentOf L C :=
    ⟨hLC, CFSG.Open.IsSubnormal.step hLC hLn (CFSG.Open.IsSubnormal.refl C), hq⟩
  have hperfJ : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJL : J ≤ L := hperf J hJ.1 (Subgroup.isPerfect_iff.2 hperfJ).commutator_eq_top
  have hqJ : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  have hnt := nontrivial_of_isQuasisimple hqJ
  have hJeq : J = L := by
    rcases b3Lie_comp_le_or_comm hCL hJ.1 hJ.2.1 with h | h
    · exact le_antisymm hJL h
    · exfalso
      have h1 : ⁅J, J⁆ ≤ ⁅L, J⁆ := Subgroup.commutator_mono hJL le_rfl
      rw [h] at h1
      have h2 : J = ⊥ := by
        rw [← hperfJ]
        exact le_bot_iff.1 h1
      subst h2
      exact not_nontrivial_barOf_bot hnt
  have hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_native_of_open hq)
      (GLAPPrimeCore.normal 3 ↥L) with htop | hle
    · exfalso
      have hsub : Subsingleton (barOf 3 L) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        exact QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _)
      rw [hJeq] at hnt
      exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
    · exact hle
  have hdvd : Nat.card (GLAPPrimeCore 3 ↥L) ∣ Nat.card ↥(Subgroup.center ↥L) :=
    Subgroup.card_dvd_of_le hO
  have hcop : Nat.Coprime (Nat.card (GLAPPrimeCore 3 ↥L)) 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
      Nat.prime_three ↥L).symm
  have hdpos : 0 < Nat.card (GLAPPrimeCore 3 ↥L) := Nat.card_pos
  have hmul : Nat.card ↥L = Nat.card (barOf 3 L) * Nat.card (GLAPPrimeCore 3 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)
  have hbar : Nat.card (barOf 3 L) = Nat.card ↥L / Nat.card (GLAPPrimeCore 3 ↥L) := by
    rw [hmul]
    exact (Nat.mul_div_cancel _ hdpos).symm
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL3
  rw [hJeq, hbar] at hcard
  exact hNo _ hdvd hcop r ε e he hc hcard

theorem noL3Comp_of_quasisimple_central {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥C)
    (hNo : ∀ d : ℕ, d ∣ Nat.card ↥(Subgroup.center ↥C) → Nat.Coprime d 3 →
      NoL3Eq (Nat.card ↥C / d)) : NoL3Comp C :=
  noL3Comp_of_normal_quasisimple le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hq
    (fun _ hH _ => hH) hNo

@[expose] def L3Excl (N q k : ℕ) : Prop :=
  ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → L3Ord r ε ∣ N * e →
    q ∣ L3Ord r ε ∧ ¬ 3 ^ k ∣ L3Ord r ε

@[expose] def l3CondB (r : ℕ) (ε : Bool) : Bool :=
  if ε then decide (4 ≤ r) && decide (r % 3 = 1) else decide (5 ≤ r) && decide (r % 3 = 2)

theorem l3CondB_of_cond {r : ℕ} {ε : Bool} (h : L3Cond r ε) : l3CondB r ε = true := by
  cases ε
  · obtain ⟨h5, h3⟩ := h.2 rfl
    simp [l3CondB, h5, h3]
  · obtain ⟨h4, h3⟩ := h.1 rfl
    simp [l3CondB, h4, h3]

@[expose] def L3ExclCheck (N q k B : ℕ) : Bool :=
  (List.range B).all fun i => [true, false].all fun ε => [1, 3].all fun e =>
    decide (l3CondB (i + 4) ε = true → L3Ord (i + 4) ε ∣ N * e →
      q ∣ L3Ord (i + 4) ε ∧ ¬ 3 ^ k ∣ L3Ord (i + 4) ε)

theorem l3Excl_of_check {N q k B : ℕ} (hN : 0 < N) (hB : 12 * N < (B + 4) ^ 8)
    (h : L3ExclCheck N q k B = true) : L3Excl N q k := by
  intro r ε e he hc hdvd
  have hr4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (hc.2 rfl).1
    · exact (hc.1 rfl).1
  have hle : L3Ord r ε ≤ N * e := Nat.le_of_dvd (by rcases he with rfl | rfl <;> omega) hdvd
  have hrB : r < B + 4 := by
    by_contra hge
    push Not at hge
    have h1 : (B + 4) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hge 8
    have h2 := L3Ord_pow_le hc
    have h3 : 4 * (N * e) ≤ 12 * N := by rcases he with rfl | rfl <;> omega
    omega
  have hall := List.all_eq_true.1 h (r - 4) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 hall ε (by cases ε <;> simp)
  have h3 := List.all_eq_true.1 h2 e (by rcases he with rfl | rfl <;> simp)
  have hr : r - 4 + 4 = r := by omega
  rw [hr] at h3
  exact of_decide_eq_true h3 (l3CondB_of_cond hc) hdvd

theorem noL3Comp_of_prime_pair {G : Type} [Group G] [Finite G] {P C : Subgroup G} {q k : ℕ}
    (hCP : C ≤ P) (hq : q.Prime) (hq3 : q ≠ 3) (hN : L3Excl (Nat.card ↥P) q k)
    (hqq : ¬ q ^ 2 ∣ Nat.card ↥C)
    (hpair : ∃ a ∈ C, ∃ b ∈ C, orderOf a = q ∧ orderOf b = q ∧
      3 ^ k ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set G))) :
    NoL3Comp C := by
  intro J hJ p hL
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  have hdvdC : Nat.card (barOf 3 J) ∣ Nat.card ↥C :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJ.1)
  have hdvdM : Nat.card (barOf 3 J) ∣ Nat.card ↥P := hdvdC.trans (Subgroup.card_dvd_of_le hCP)
  have hL3 : L3Ord r ε ∣ Nat.card ↥P * e := by
    rw [← hcard]
    exact Nat.mul_dvd_mul_right hdvdM e
  obtain ⟨hqL, hk⟩ := hN r ε e he hc hL3
  rw [← hcard] at hqL hk
  have hqJbar : q ∣ Nat.card (barOf 3 J) := by
    rcases (Nat.Prime.dvd_mul hq).1 hqL with h | h
    · exact h
    · exfalso
      rcases he with rfl | rfl
      · exact hq.one_lt.ne' (Nat.dvd_one.1 h)
      · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)
  have hmulJ : Nat.card ↥J = Nat.card (barOf 3 J) * Nat.card (GLAPPrimeCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hqJ : q ∣ Nat.card ↥J := hmulJ ▸ Dvd.dvd.mul_right hqJbar _
  have hmulC : Nat.card ↥J * J.relIndex C = Nat.card ↥C := by
    have h1 := Subgroup.card_mul_index (J.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ.1).toEquiv] at h1
    exact h1
  have hrel : ¬ q ∣ J.relIndex C := by
    intro hr
    apply hqq
    rw [← hmulC, pow_two]
    exact Nat.mul_dvd_mul hqJ hr
  obtain ⟨a, haC, b, hbC, hao, hbo, h3⟩ := hpair
  have hcopq : Nat.Coprime q (J.relIndex C) := (Nat.Prime.coprime_iff_not_dvd hq).2 hrel
  have haJ : a ∈ J := mem_of_isSubnormal_of_coprime hJ.2.1 haC (by rw [hao]; exact hcopq)
  have hbJ : b ∈ J := mem_of_isSubnormal_of_coprime hJ.2.1 hbC (by rw [hbo]; exact hcopq)
  have hHJ : Subgroup.closure ({a, b} : Set G) ≤ J := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact haJ
    · exact hbJ
  have h3J : 3 ^ k ∣ Nat.card ↥J := h3.trans (Subgroup.card_dvd_of_le hHJ)
  have hcop3 : Nat.Coprime (3 ^ k) (Nat.card (GLAPPrimeCore 3 ↥J)) :=
    Nat.Coprime.pow_left k
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
        Nat.prime_three ↥J)
  exact hk ((hcop3.dvd_of_dvd_mul_right (hmulJ ▸ h3J)).mul_right e)

theorem noL3Comp_of_not_dvd_sub {G : Type} [Group G] [Finite G] {P C : Subgroup G} {q k : ℕ}
    (hCP : C ≤ P) (hq : q.Prime) (hq3 : q ≠ 3) (hN : L3Excl (Nat.card ↥P) q k)
    (hqC : ¬ q ∣ Nat.card ↥C) : NoL3Comp C := by
  intro J hJ p hL
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  have hdvdC : Nat.card (barOf 3 J) ∣ Nat.card ↥C :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJ.1)
  have hdvdM : Nat.card (barOf 3 J) ∣ Nat.card ↥P := hdvdC.trans (Subgroup.card_dvd_of_le hCP)
  have hL3 : L3Ord r ε ∣ Nat.card ↥P * e := by
    rw [← hcard]
    exact Nat.mul_dvd_mul_right hdvdM e
  obtain ⟨hqL, -⟩ := hN r ε e he hc hL3
  rw [← hcard] at hqL
  have hqJbar : q ∣ Nat.card (barOf 3 J) := by
    rcases (Nat.Prime.dvd_mul hq).1 hqL with h | h
    · exact h
    · exfalso
      rcases he with rfl | rfl
      · exact hq.one_lt.ne' (Nat.dvd_one.1 h)
      · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)
  exact hqC (hqJbar.trans hdvdC)

theorem sporL3DownInner_of_comp {s : TauCeti.SporadicName} (M : Type) [Group M] [Finite M]
    (hM : Nonempty (M ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (hcard : NoL3Eq (Nat.card M))
    (hC : ∀ x : M, orderOf x = 3 → NoL3Comp (Subgroup.centralizer ({x} : Set M))) :
    SporL3DownInner s := by
  intro S _ _ hS hnab hSs x hx J hJ p hL
  have e : S ≃* M := hSs.some.trans hM.some.symm
  by_cases hx1 : x = 1
  · subst hx1
    have hCtop : Subgroup.centralizer ({1} : Set S) = ⊤ := by simp
    have hsn : CFSG.Open.IsSubnormal J ⊤ := hCtop ▸ hJ.2.1
    haveI := hS
    have hq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
    have hnt := nontrivial_of_isQuasisimple hq
    rcases eq_bot_or_eq_top_of_isSubnormal hsn rfl with hJ0 | hJ1
    · exfalso
      subst hJ0
      have hsub : Subsingleton (barOf 3 (⊥ : Subgroup S)) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim a b]
      exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
    · subst hJ1
      have hbar := card_barOf_top_of_simple hnt
      obtain ⟨r, ε, e', he', hc, hcd⟩ := isL3Kind_card_forms hL
      rw [hbar, Nat.card_congr e.toEquiv] at hcd
      exact hcard r ε e' he' hc hcd
  · have hx3 : orderOf x = 3 := orderOf_eq_prime hx hx1
    have hcomp := hC (e x) (by rw [MulEquiv.orderOf_eq]; exact hx3)
    have hS' : NoL3Comp (Subgroup.centralizer ({x} : Set S)) := by
      refine noL3Comp_of_injective e.toMonoidHom e.injective ?_
      rw [map_centralizer_mulEquiv e x]
      exact hcomp
    exact hS' J hJ p hL

theorem sporL3DownInner_of_perm_comp {s : TauCeti.SporadicName} {G : Type} [Group G] [Finite G]
    (P : Subgroup G) (hM : Nonempty (↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hord : NoL3Eq (Nat.card ↥P))
    (hC : ∀ x ∈ P, orderOf x = 3 → NoL3Comp (Subgroup.centralizer ({x} : Set G) ⊓ P)) :
    SporL3DownInner s := by
  refine sporL3DownInner_of_comp ↥P hM hord ?_
  intro x hx
  have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  refine noL3Comp_of_injective P.subtype P.subtype_injective ?_
  rw [map_centralizer_subtype P x]
  exact hC x x.2 hx3

theorem sporL3DownInner_of_fusion_comp {s : TauCeti.SporadicName} {G : Type} [Group G] [Finite G]
    (P : Subgroup G) (hM : Nonempty (↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hord : NoL3Eq (Nat.card ↥P)) (cs : G → Prop)
    (hcs : ∀ c, cs c → c ^ 3 = 1 ∧ NoL3Comp (Subgroup.centralizer ({c} : Set G) ⊓ P))
    (hfus : ∀ x ∈ P, orderOf x = 3 →
      ∃ k ∈ P, ∃ c, cs c ∧ ∃ e, (e = 1 ∨ e = 2) ∧ x = k * c ^ e * k⁻¹) :
    SporL3DownInner s := by
  refine sporL3DownInner_of_comp ↥P hM hord ?_
  intro x hx
  have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨k, hk, c, hc, e, he, hxe⟩ := hfus x x.2 hx3
  obtain ⟨hc3, hNo⟩ := hcs c hc
  refine noL3Comp_of_injective P.subtype P.subtype_injective ?_
  rw [map_centralizer_subtype P x, hxe]
  exact noL3Comp_conj_class hc3 hk he hNo

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
