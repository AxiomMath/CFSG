module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212Layer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

noncomputable instance compMulAction (K : Type*) [Group K] [Finite K] :
    MulAction K (ComponentIndex K) where
  smul g C := cjComp g C
  one_smul C := cjComp_one C
  mul_smul g h C := cjComp_mul g h C

section Setting

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem center_comp_le_pCore [Fact p.Prime] (hcore : primeComplementCore (G := K) p = ⊥)
    (C : ComponentIndex K) {c : K} (hcK : c ∈ C.1) (hcc : ∀ g ∈ C.1, g * c = c * g) :
    c ∈ CFSG.pCore p K := by
  have hc : c ∈ (center C.1).map C.1.subtype :=
    (CFSG.LocalCores.mem_map_center_iff C.1).2 ⟨hcK, mem_centralizer_iff.2 hcc⟩
  exact CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot p hcore
    (CFSG.LocalCores.center_component_le_center_layer C.2 hc)

theorem center_comp_eq_bot [Fact p.Prime] (hcore : primeComplementCore (G := K) p = ⊥)
    (hpc : CFSG.pCore p K = ⊥) (C : ComponentIndex K) : center C.1 = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have h1 : (c : K) ∈ CFSG.pCore p K :=
    center_comp_le_pCore hcore C c.2 fun g hg =>
      congrArg Subtype.val (mem_center_iff.1 hc ⟨g, hg⟩)
  rw [hpc, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem exists_comp [Fact p.Prime] (hcore : primeComplementCore (G := K) p = ⊥)
    (hnc : ¬ ∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q) :
    Nonempty (ComponentIndex K) := by
  obtain ⟨C, hC⟩ := exists_isComponentOf_of_layer_ne_bot
    (layer_ne_bot_of_not_exists_selfCentralizing hcore hnc)
  exact ⟨⟨C, (CFSG.isComponent_iff_open C).2 hC⟩⟩

theorem dvd_card_comp [Fact p.Prime] (hcore : primeComplementCore (G := K) p = ⊥)
    (C : ComponentIndex K) : p ∣ Nat.card C.1 :=
  ((exists_pElement_not_central Fact.out hcore ((CFSG.isComponent_iff_open C.1).1 C.2)).1.trans
    (Subgroup.card_quotient_dvd_card _))

end Setting

section Config

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem mem_of_normalizes_of_dvd [Fact p.Prime]
    (h : Lemma212ConfigGe n p P z D) {N : Subgroup K}
    (hPN : (P : Subgroup K) ≤ normalizer (N : Set K)) (hN : p ∣ Nat.card N) : z ∈ N := by
  have hp : p.Prime := Fact.out
  have hPS : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup K) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2
      ⟨le_top, P.isPGroup', by simpa [Subgroup.relIndex_top_right] using P.not_dvd_index⟩
  have hPM : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup K) (N ⊔ P) :=
    hPS.of_le le_sup_right le_top
  have hMN : N ⊔ P ≤ normalizer (N : Set K) := sup_le le_normalizer hPN
  have hS := hPM.inf_of_le_normalizer le_sup_left hMN
  have hPNne : (P : Subgroup K) ⊓ N ≠ ⊥ := by
    intro hbot
    have hcard := hS.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hfac : 1 ≤ (Nat.card N).factorization p :=
      (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').1 hN
    have h1 : 1 < p ^ (Nat.card N).factorization p := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  haveI : (N.subgroupOf (P : Subgroup K)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hHne : N.subgroupOf (P : Subgroup K) ≠ ⊥ := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPNne
    intro hbot
    apply ht1
    have hmem : (⟨t, t.2.1⟩ : ↥(P : Subgroup K)) ∈ N.subgroupOf (P : Subgroup K) := t.2.2
    rw [hbot, mem_bot] at hmem
    have h2 : ((⟨t, t.2.1⟩ : ↥(P : Subgroup K)) : K) = ((1 : ↥(P : Subgroup K)) : K) :=
      congrArg Subtype.val hmem
    exact Subtype.ext h2
  haveI : Group.IsNilpotent (↥(P : Subgroup K)) := P.isPGroup'.isNilpotent
  have hW : N.subgroupOf (P : Subgroup K) ⊓ center (↥(P : Subgroup K)) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set W : Subgroup (↥(P : Subgroup K)) :=
    N.subgroupOf (P : Subgroup K) ⊓ center (↥(P : Subgroup K))
  have hWp : IsPGroup p W := P.isPGroup'.to_subgroup W
  haveI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW
  obtain ⟨m, hm, hmcard⟩ := hWp.nontrivial_iff_card.mp inferInstance
  have hdvdW : p ∣ Nat.card W := hmcard ▸ dvd_pow_self p hm.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) p hdvdW
  set u : K := ((w : ↥(P : Subgroup K)) : K)
  have hu_ord : orderOf u = p :=
    (Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans hw)
  have hup : u ^ p = 1 := by
    rw [← hu_ord]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu_ord
    exact hp.one_lt.ne hu_ord
  have huC : u ∈ centralizer ((P : Subgroup K) : Set K) := by
    refine mem_centralizer_iff.mpr fun g hg => ?_
    exact congrArg Subtype.val (mem_center_iff.mp w.2.2 ⟨g, hg⟩)
  have hmem : u ∈ zpowers z := h.unique u (w : ↥(P : Subgroup K)).2 huC hup
  have heq : zpowers u = zpowers z :=
    zpowers_eq_of_mem_zpowers hup h.z_pow_eq_one hu1 (h.ne_one hp) hmem
  have hzu : z ∈ zpowers u := by
    rw [heq]
    exact mem_zpowers z
  have huN : u ∈ N := w.2.1
  exact zpowers_le.mpr huN hzu

end Config

section Orbits

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem π_congr {hZ : ∀ C : ComponentIndex K, center C.1 = ⊥} (C : ComponentIndex K) {x y : K}
    (hxy : x = y) (hx : x ∈ layer K) (hy : y ∈ layer K) : π hZ C x hx = π hZ C y hy := by
  subst hxy
  rfl

@[expose] def compJoin (S : Set (ComponentIndex K)) : Subgroup K := ⨆ C ∈ S, C.1

theorem le_compJoin {S : Set (ComponentIndex K)} {C : ComponentIndex K} (hC : C ∈ S) :
    C.1 ≤ compJoin S :=
  le_iSup₂ (f := fun (C : ComponentIndex K) (_ : C ∈ S) => C.1) C hC

theorem compJoin_le_centralizer {S : Set (ComponentIndex K)} {C : ComponentIndex K}
    (hC : ∀ C' ∈ S, C' ≠ C) : compJoin S ≤ centralizer (C.1 : Set K) :=
  iSup₂_le fun C' hC' => commutator_eq_bot_iff_le_centralizer.1
    ((distinct_components_commute C'.2 C.2).resolve_left fun h => hC C' hC' (Subtype.ext h))

theorem conj_mem_compJoin {S : Set (ComponentIndex K)} (g : K) (hS : ∀ C ∈ S, g • C ∈ S) {x : K}
    (hx : x ∈ compJoin S) : g * x * g⁻¹ ∈ compJoin S := by
  have h : (compJoin S).map (MulAut.conj g).toMonoidHom ≤ compJoin S := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun C hC c hc => ?_
    exact le_compJoin (hS C hC) (mem_cjComp_of_mem g C hc)
  exact h ⟨x, hx, rfl⟩

theorem le_normalizer_compJoin {S : Set (ComponentIndex K)} {H : Subgroup K}
    (hS : ∀ g ∈ H, ∀ C ∈ S, g • C ∈ S) : H ≤ normalizer (compJoin S : Set K) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_compJoin g (hS g hg) hx, fun hx => ?_⟩
  have := conj_mem_compJoin g⁻¹ (hS g⁻¹ (H.inv_mem hg)) hx
  simpa [mul_assoc] using this

variable [Fact p.Prime]

theorem layer_normalizes (K : Type) [Group K] [Finite K] (H : Subgroup K) :
    H ≤ normalizer (layer K : Set K) := by
  haveI := layer_normal K
  exact le_normalizer_of_normal

theorem z_mem_layer_of_conf (hcore : primeComplementCore (G := K) p = ⊥)
    (hnc : ¬ ∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q)
    (h : Lemma212ConfigGe n p P z D) : z ∈ layer K := by
  obtain ⟨C⟩ := exists_comp hcore hnc
  exact mem_of_normalizes_of_dvd h (layer_normalizes K _)
    ((dvd_card_comp hcore C).trans (Subgroup.card_dvd_of_le (component_le_layer C.2)))

theorem z_mem_compJoin_of_conf (hcore : primeComplementCore (G := K) p = ⊥)
    (h : Lemma212ConfigGe n p P z D) {S : Set (ComponentIndex K)}
    (hS : ∀ g ∈ (P : Subgroup K), ∀ C ∈ S, g • C ∈ S) (hne : S.Nonempty) : z ∈ compJoin S := by
  obtain ⟨C, hC⟩ := hne
  exact mem_of_normalizes_of_dvd h (le_normalizer_compJoin hS)
    ((dvd_card_comp hcore C).trans (Subgroup.card_dvd_of_le (le_compJoin hC)))

end Orbits

section Transitive

structure Red (n p : ℕ) (K : Type) [Group K] [Finite K] (P : Sylow p K) (z : K)
    (D : Subgroup K) : Prop where
  prime : p.Prime
  core : primeComplementCore (G := K) p = ⊥
  nc : ¬ ∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q
  pc : CFSG.pCore p K = ⊥
  conf : Lemma212ConfigGe n p P z D

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

namespace Red

theorem fact (R : Red n p K P z D) : Fact p.Prime := ⟨R.prime⟩

theorem hZ (R : Red n p K P z D) (C : ComponentIndex K) : center C.1 = ⊥ :=
  haveI := R.fact
  center_comp_eq_bot R.core R.pc C

theorem hzL (R : Red n p K P z D) : z ∈ layer K :=
  haveI := R.fact
  z_mem_layer_of_conf R.core R.nc R.conf

theorem z_ne_one (R : Red n p K P z D) : z ≠ 1 := R.conf.ne_one R.prime

theorem z_pow (R : Red n p K P z D) : z ^ p = 1 := R.conf.z_pow_eq_one

theorem g_z (R : Red n p K P z D) {g : K} (hg : g ∈ (P : Subgroup K)) : g * z * g⁻¹ = z := by
  have := mem_centralizer_iff.1 R.conf.central g hg
  rw [this]
  group

@[expose] noncomputable def zc (R : Red n p K P z D) (C : ComponentIndex K) : K :=
  π (R.hZ) C z R.hzL

theorem isPretransitive (R : Red n p K P z D) :
    MulAction.IsPretransitive (P : Subgroup K) (ComponentIndex K) := by
  haveI := R.fact
  refine ⟨fun C₁ C₂ => ?_⟩
  by_contra hno
  push Not at hno
  set S₁ : Set (ComponentIndex K) := MulAction.orbit (P : Subgroup K) C₁ with hS₁def
  set S₂ : Set (ComponentIndex K) := S₁ᶜ with hS₂def
  have hS₁ : ∀ g ∈ (P : Subgroup K), ∀ C ∈ S₁, g • C ∈ S₁ := by
    rintro g hg C ⟨a, rfl⟩
    exact ⟨⟨g, hg⟩ * a, mul_smul (⟨g, hg⟩ : ↥(P : Subgroup K)) a C₁⟩
  have hS₂ : ∀ g ∈ (P : Subgroup K), ∀ C ∈ S₂, g • C ∈ S₂ := by
    intro g hg C hC hgC
    apply hC
    have := hS₁ g⁻¹ ((P : Subgroup K).inv_mem hg) _ hgC
    simpa using this
  have hz₁ := z_mem_compJoin_of_conf R.core R.conf hS₁ ⟨C₁, MulAction.mem_orbit_self C₁⟩
  have hz₂ := z_mem_compJoin_of_conf R.core R.conf hS₂ ⟨C₂, fun ⟨a, ha⟩ => hno a ha⟩
  have hz1 : z = 1 := by
    refine eq_one_of_π_eq_one (hZ := R.hZ) R.hzL fun C => ?_
    rw [π_eq_one_iff (hZ := R.hZ)]
    by_cases hC : C ∈ S₁
    · exact compJoin_le_centralizer (S := S₂)
        (fun C' hC' hCC' => hC' (by rw [hCC']; exact hC)) hz₂
    · exact compJoin_le_centralizer (S := S₁)
        (fun C' hC' hCC' => hC (by rw [← hCC']; exact hC')) hz₁
  exact R.z_ne_one hz1

theorem zc_ne_one (R : Red n p K P z D) (C : ComponentIndex K) : R.zc C ≠ 1 := by
  haveI := R.fact
  intro h1
  haveI := R.isPretransitive
  have hall : ∀ C' : ComponentIndex K, R.zc C' = 1 := by
    intro C'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (P : Subgroup K) C C'
    subst hg
    have h2 := π_conj (hZ := R.hZ) (g : K) C R.hzL
    have h3 : π R.hZ (cjComp (g : K) C) ((g : K) * z * (g : K)⁻¹)
        (conj_mem_layer (g : K) R.hzL) = π R.hZ (cjComp (g : K) C) z R.hzL :=
      π_congr _ (R.g_z g.2) _ _
    rw [h3] at h2
    unfold zc at h1 ⊢
    show π R.hZ (cjComp (g : K) C) z R.hzL = 1
    rw [h2, h1]
    simp
  have hz1 : z = 1 := eq_one_of_π_eq_one (hZ := R.hZ) R.hzL hall
  exact R.z_ne_one hz1

theorem zc_pow (R : Red n p K P z D) (C : ComponentIndex K) : R.zc C ^ p = 1 := by
  have h1 := π_pow (hZ := R.hZ) C R.hzL p
  have h2 : π R.hZ C (z ^ p) (pow_mem R.hzL p) = π R.hZ C 1 (one_mem _) :=
    π_congr C R.z_pow _ _
  rw [π_one] at h2
  unfold zc
  rw [← h1]
  exact h2

theorem zc_mem (R : Red n p K P z D) (C : ComponentIndex K) : R.zc C ∈ C.1 := π_mem C z R.hzL

theorem z_conj_eq (R : Red n p K P z D) (C : ComponentIndex K) {x : K} (hx : x ∈ C.1) :
    z * x * z⁻¹ = R.zc C * x * (R.zc C)⁻¹ := by
  obtain ⟨u, hu, hCu, hzu⟩ := exists_eq_π_mul (hZ := R.hZ) C R.hzL
  have hxu : u * x = x * u := (mem_centralizer_iff.1 hCu x hx).symm
  conv_lhs => rw [hzu]
  show R.zc C * u * x * (R.zc C * u)⁻¹ = _
  calc R.zc C * u * x * (R.zc C * u)⁻¹ = R.zc C * (u * x) * u⁻¹ * (R.zc C)⁻¹ := by group
    _ = R.zc C * (x * u) * u⁻¹ * (R.zc C)⁻¹ := by rw [hxu]
    _ = R.zc C * x * (R.zc C)⁻¹ := by group

end Red

end Transitive

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
