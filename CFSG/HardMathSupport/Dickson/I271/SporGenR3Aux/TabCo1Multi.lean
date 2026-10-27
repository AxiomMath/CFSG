module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeMulti

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Conj

variable {G : Type*} [Group G]

theorem conj_mem_of_gen {S : Set G} {R : Subgroup G} {g : G} (h : ∀ s ∈ S, g * s * g⁻¹ ∈ R) :
    ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ R := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simpa using R.one_mem
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact R.mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact R.inv_mem hx

theorem normalizes_closure {S : Set G} {R : Subgroup G}
    (h : ∀ s ∈ S, (∀ x ∈ R, s * x * s⁻¹ ∈ R) ∧ (∀ x ∈ R, s⁻¹ * x * s ∈ R)) :
    ∀ g ∈ Subgroup.closure S, (∀ x ∈ R, g * x * g⁻¹ ∈ R) ∧ (∀ x ∈ R, g⁻¹ * x * g ∈ R) := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
  | mul a b _ _ ha hb =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      rw [this]
      exact ha.1 _ (hb.1 x hx)
    · have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
      rw [this]
      exact hb.2 _ (ha.2 x hx)
  | inv a _ ha =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simpa using ha.2 x hx
    · simpa using ha.1 x hx

theorem normalizes_of_gen {T : Set G} {s : G} {R : Subgroup G} (hR : R = Subgroup.closure T)
    (h1 : ∀ t ∈ T, s * t * s⁻¹ ∈ R) (h2 : ∀ t ∈ T, s⁻¹ * t * s ∈ R) :
    (∀ x ∈ R, s * x * s⁻¹ ∈ R) ∧ (∀ x ∈ R, s⁻¹ * x * s ∈ R) := by
  subst hR
  refine ⟨conj_mem_of_gen h1, fun x hx => ?_⟩
  have := conj_mem_of_gen (g := s⁻¹) (R := Subgroup.closure T) (S := T)
    (fun t ht => by simpa using h2 t ht) x hx
  simpa using this

theorem normalSubgroupOf_of_conj_aux {C L : Subgroup G}
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) : (L.subgroupOf C).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hLn g.1 g.2 x hx⟩

end Conj

section Constrained

variable {G : Type} [Group G]

theorem pConstrainedShape_of_data {p n : ℕ} (P : Subgroup G) [Finite P] (z t₁ t₂ s₁ s₂ : G)
    (ht₁ : t₁ ∈ P) (ht₂ : t₂ ∈ P) (hs₁ : s₁ ∈ P) (hs₂ : s₂ ∈ P)
    (hzt₁ : t₁ * z = z * t₁) (hzt₂ : t₂ * z = z * t₂) (hzs₁ : s₁ * z = z * s₁)
    (hzs₂ : s₂ * z = z * s₂)
    (hR : Nat.card ↥(Subgroup.closure ({t₁, t₂} : Set G)) = p ^ n)
    (hnorm : ∀ s ∈ ({s₁, s₂} : Set G), ∀ t ∈ ({t₁, t₂} : Set G),
      s * t * s⁻¹ ∈ Subgroup.closure ({t₁, t₂} : Set G) ∧
        s⁻¹ * t * s ∈ Subgroup.closure ({t₁, t₂} : Set G))
    {m : ℕ} (hbd : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ P) ≤ m)
    (hC : m ≤ Nat.card ↥(Subgroup.closure ({s₁, s₂} : Set G)))
    (hcent : ∀ g ∈ P, g * t₁ = t₁ * g → g * t₂ = t₂ * g →
      g ∈ Subgroup.closure ({t₁, t₂} : Set G)) :
    PConstrainedShape p (Subgroup.centralizer ({z} : Set G) ⊓ P) := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ P with hCdef
  set R : Subgroup G := Subgroup.closure ({t₁, t₂} : Set G) with hRdef
  have hCP : C ≤ P := inf_le_right
  haveI : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion hCP) (Subgroup.inclusion_injective hCP)
  have hmemC : ∀ g, g ∈ P → g * z = z * g → g ∈ C := fun g hg hgz =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hgz, hg⟩
  have hSC : Subgroup.closure ({s₁, s₂} : Set G) ≤ C := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with rfl | hy
    · exact hmemC _ hs₁ hzs₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hmemC _ hs₂ hzs₂
  have hCeq : Subgroup.closure ({s₁, s₂} : Set G) = C :=
    Subgroup.eq_of_le_of_card_ge hSC (hbd.trans hC)
  have hRC : R ≤ C := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with rfl | hy
    · exact hmemC _ ht₁ hzt₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hmemC _ ht₂ hzt₂
  have hnorm' := normalizes_closure (R := R) (S := ({s₁, s₂} : Set G)) fun s hs => by
    obtain ⟨h1, h2⟩ : (∀ t ∈ ({t₁, t₂} : Set G), s * t * s⁻¹ ∈ R) ∧
        (∀ t ∈ ({t₁, t₂} : Set G), s⁻¹ * t * s ∈ R) :=
      ⟨fun t ht => (hnorm s hs t ht).1, fun t ht => (hnorm s hs t ht).2⟩
    exact normalizes_of_gen rfl h1 h2
  have hconj : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    rw [← hCeq] at hg
    exact (hnorm' g hg).1 r hr
  haveI : Finite ↥R := Finite.of_injective (Subgroup.inclusion (hRC.trans hCP))
    (Subgroup.inclusion_injective _)
  refine pConstrainedShape_of_normal_pgroup hRC (normalSubgroupOf_of_conj_aux hconj)
    (IsPGroup.of_card hR) ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine hcent x (hCP hx2) ?_ ?_
    · exact ((Subgroup.mem_centralizer_iff.1 hx1) t₁ (Subgroup.subset_closure (by simp))).symm
    · exact ((Subgroup.mem_centralizer_iff.1 hx1) t₂ (Subgroup.subset_closure (by simp))).symm

end Constrained

section TwoComp

variable {Q : Type} [Group Q] [Finite Q]

theorem glaPComponent_of_subnormal_quasisimple {p : ℕ} {C L : Subgroup Q}
    (hsub : IsSubnormal L C) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hcore : GLAPPrimeCore p ↥C = ⊥) : GLAPComponent p C L := by
  have hLC : L ≤ C := hsub.le
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) :=
    mk'_injective_of_eq_bot _ hcore
  refine ⟨hLC, hsub, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := C) p hsub
    rwa [barX_self] at this
  · have e1 : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
    have e2 : ↥(L.subgroupOf C) ≃*
        ↥((L.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))) :=
      Subgroup.equivMapOfInjective _ _ hinj
    exact isQuasisimple_of_mulEquiv' (e1.symm.trans e2) hLq
  · intro J hJ _ heq
    have h1 : J.subgroupOf C = L.subgroupOf C := Subgroup.map_injective hinj heq
    have h2 : J ⊓ C = L ⊓ C := Subgroup.subgroupOf_inj.1 h1
    rw [inf_of_le_left (hJ.le.trans hLC), inf_of_le_left hLC] at h2
    exact hJ.ne h2

theorem glaPPrimeCore_eq_bot_of_two_subnormal {p : ℕ} (hp : p.Prime) {C L₁ L₂ : Subgroup Q}
    (h₁ : IsSubnormal L₁ C) (h₂ : IsSubnormal L₂ C) (hq₁ : CFSG.Open.IsQuasisimple ↥L₁)
    (hq₂ : CFSG.Open.IsQuasisimple ↥L₂) (hp₁ : p ∣ Nat.card ↥L₁) (hp₂ : p ∣ Nat.card ↥L₂)
    (hcent : IsPGroup p ↥(C ⊓ Subgroup.centralizer (L₁ : Set Q) ⊓
      Subgroup.centralizer (L₂ : Set Q))) : GLAPPrimeCore p ↥C = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥C := GLAPPrimeCore p ↥C with hN
  have hcop : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C)
  have key : ∀ {L : Subgroup Q}, IsSubnormal L C → CFSG.Open.IsQuasisimple ↥L →
      p ∣ Nat.card ↥L → ⁅L.subgroupOf C, N⁆ = ⊥ := by
    intro L hL hq hpL
    have hLC : L ≤ C := hL.le
    have e1 : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
    have hq1 : CFSG.Open.IsQuasisimple ↥(L.subgroupOf C) :=
      isQuasisimple_of_mulEquiv' e1.symm hq
    have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf C) :=
      ⟨⟨hq1.1⟩, hq1.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq1⟩
    have hK : CFSG.IsComponent (L.subgroupOf C) := ⟨hq', hL.subgroupOf⟩
    rcases CFSG.LocalCores.component_normal_subgroup hK (inferInstance : N.Normal) with h | h
    · exfalso
      have h1 : Nat.card (L.subgroupOf C) ∣ Nat.card N := Subgroup.card_dvd_of_le h
      have h2 : p ∣ Nat.card (L.subgroupOf C) := by
        rw [Nat.card_congr e1.toEquiv]
        exact hpL
      exact hp.ne_one (hcop.eq_one_of_dvd (h2.trans h1))
    · exact h
  have c₁ := key h₁ hq₁ hp₁
  have c₂ := key h₂ hq₂ hp₂
  have cent : ∀ {L : Subgroup Q}, L ≤ C → ⁅L.subgroupOf C, N⁆ = ⊥ →
      ∀ n ∈ N, (n : Q) ∈ Subgroup.centralizer (L : Set Q) := by
    intro L hLC hc n hn
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro l hl
    have hl' : (⟨l, hLC hl⟩ : ↥C) ∈ L.subgroupOf C := hl
    have hc' : ⁅(⟨l, hLC hl⟩ : ↥C), n⁆ ∈ ⁅L.subgroupOf C, N⁆ :=
      Subgroup.commutator_mem_commutator hl' hn
    rw [hc, Subgroup.mem_bot] at hc'
    have := congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hc')
    exact this
  have hle : N.map C.subtype ≤ C ⊓ Subgroup.centralizer (L₁ : Set Q) ⊓
      Subgroup.centralizer (L₂ : Set Q) := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨⟨n.2, cent h₁.le c₁ n hn⟩, cent h₂.le c₂ n hn⟩
  have hNp : IsPGroup p N :=
    (hcent.to_le hle).of_equiv (N.equivMapOfInjective C.subtype C.subtype_injective).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hNp
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hcop
    exact hp.ne_one (hcop.eq_one_of_dvd (dvd_pow_self p hk0))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq N hk

theorem eq_or_of_glaPComponent_two {p : ℕ} (hp : p.Prime) {C L₁ L₂ J : Subgroup Q}
    (h₁ : IsSubnormal L₁ C) (h₂ : IsSubnormal L₂ C) (hq₁ : CFSG.Open.IsQuasisimple ↥L₁)
    (hq₂ : CFSG.Open.IsQuasisimple ↥L₂) (hcore : GLAPPrimeCore p ↥C = ⊥)
    (hcent : IsPGroup p ↥(C ⊓ Subgroup.centralizer (L₁ : Set Q) ⊓
      Subgroup.centralizer (L₂ : Set Q)))
    (hJ : GLAPComponent p C J) : J = L₁ ∨ J = L₂ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  rw [not_or] at hne
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) :=
    mk'_injective_of_eq_bot _ hcore
  have hJC : J ≤ C := hJ.1
  have cent : ∀ {L : Subgroup Q}, IsSubnormal L C → CFSG.Open.IsQuasisimple ↥L → J ≠ L →
      ∀ x ∈ J, x ∈ Subgroup.centralizer (L : Set Q) := by
    intro L hL hq hJL x hx
    have hLC : L ≤ C := hL.le
    have hLc : GLAPComponent p C L := glaPComponent_of_subnormal_quasisimple hL hq hcore
    have hb : barX p C J ≠ barX p C L := fun h => hJL (glaPComponent_unique hJ hLc h)
    have hcomm : ⁅barX p C J, barX p C L⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hJ.2.2.1 hLc.2.2.1 hb
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro l hl
    have hx' : (⟨x, hJC hx⟩ : ↥C) ∈ J.subgroupOf C := hx
    have hl' : (⟨l, hLC hl⟩ : ↥C) ∈ L.subgroupOf C := hl
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hJC hx⟩ ∈ barX p C J :=
      Subgroup.mem_map_of_mem _ hx'
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨l, hLC hl⟩ ∈ barX p C L :=
      Subgroup.mem_map_of_mem _ hl'
    have hc : ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hJC hx⟩,
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨l, hLC hl⟩⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator h1 h2
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    rw [← map_commutatorElement] at hc
    have hc2 := hinj (hc.trans (map_one _).symm)
    have := commutatorElement_eq_one_iff_mul_comm.1 hc2
    exact (congrArg Subtype.val this).symm
  have hJcent : J ≤ C ⊓ Subgroup.centralizer (L₁ : Set Q) ⊓ Subgroup.centralizer (L₂ : Set Q) :=
    fun x hx => ⟨⟨hJC hx, cent h₁ hq₁ hne.1 x hx⟩, cent h₂ hq₂ hne.2 x hx⟩
  have hJp : IsPGroup p ↥J := hcent.to_le hJcent
  have hbp : IsPGroup p ↥(barX p C J) := by
    have h1 : IsPGroup p ↥(J.subgroupOf C) :=
      hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJC).symm
    exact h1.of_equiv ((J.subgroupOf C).equivMapOfInjective _ hinj)
  have hq := hJ.2.2.1.2.2
  haveI : Nontrivial ↥(barX p C J) := by
    have := hq.2.exists_pair_ne
    obtain ⟨a, b, hab⟩ := this
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  haveI : Group.IsNilpotent ↥(barX p C J) := hbp.isNilpotent
  have hsolv : Group.IsSolvable ↥(barX p C J) := inferInstance
  have hperf : Group.IsPerfect ↥(barX p C J) := ⟨hq.1⟩
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem multiShapeAt_of_two_components {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    {Good Rk : ∀ (T : Type) [Group T], Prop} {t : Q} (E L₁ L₂ : Subgroup Q)
    (hEC : E ≤ Subgroup.centralizer ({t} : Set Q))
    (hEn : ∀ g ∈ Subgroup.centralizer ({t} : Set Q), ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (h₁E : L₁ ≤ E) (h₂E : L₂ ≤ E) (h₁n : ∀ g ∈ E, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁)
    (h₂n : ∀ g ∈ E, ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂) (hq₁ : CFSG.Open.IsQuasisimple ↥L₁)
    (hq₂ : CFSG.Open.IsQuasisimple ↥L₂) (hp₁ : p ∣ Nat.card ↥L₁) (hp₂ : p ∣ Nat.card ↥L₂)
    (hcent : IsPGroup p ↥(Subgroup.centralizer ({t} : Set Q) ⊓ Subgroup.centralizer (L₁ : Set Q) ⊓
      Subgroup.centralizer (L₂ : Set Q)))
    (hG₁ : Good (PSimple p L₁)) (hR₁ : Rk (PQuot p L₁)) (hG₂ : Good (PSimple p L₂))
    (hR₂ : Rk (PQuot p L₂)) : MultiShapeAt p Good Rk t := by
  set C : Subgroup Q := Subgroup.centralizer ({t} : Set Q) with hC
  have hE : IsSubnormal E C :=
    IsSubnormal.step hEC (normalSubgroupOf_of_conj_aux hEn) (IsSubnormal.refl C)
  have hs₁ : IsSubnormal L₁ C := IsSubnormal.step h₁E (normalSubgroupOf_of_conj_aux h₁n) hE
  have hs₂ : IsSubnormal L₂ C := IsSubnormal.step h₂E (normalSubgroupOf_of_conj_aux h₂n) hE
  have hcore := glaPPrimeCore_eq_bot_of_two_subnormal hp hs₁ hs₂ hq₁ hq₂ hp₁ hp₂ hcent
  refine Or.inr ⟨[L₁, L₂], by simpa using hp2, fun J hJ => ?_, fun J hJ => ?_⟩
  · rcases eq_or_of_glaPComponent_two hp hs₁ hs₂ hq₁ hq₂ hcore hcent hJ with rfl | rfl <;> simp
  · rcases eq_or_of_glaPComponent_two hp hs₁ hs₂ hq₁ hq₂ hcore hcent hJ with rfl | rfl
    exacts [⟨hG₁, hR₁⟩, ⟨hG₂, hR₂⟩]

end TwoComp

section TwoSubtype

theorem isQuasisimpleOpen_of_simple_nonab {J : Type} [Group J] [IsSimpleGroup J]
    (hnab : ∃ a b : J, a * b ≠ b * a) : CFSG.Open.IsQuasisimple J := by
  have hZ : Subgroup.center J = ⊥ := center_eq_bot_of_simple_nonab hnab
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
  · exact h

variable {G : Type} [Group G]

theorem multiShapeAt_of_subgroup_data_two {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (P : Subgroup G) [Finite P] (x : ↥P) (E L₁ L₂ : Subgroup G)
    (hEC : E ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hEn : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (h₁E : L₁ ≤ E) (h₂E : L₂ ≤ E) (h₁n : ∀ g ∈ E, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁)
    (h₂n : ∀ g ∈ E, ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂) (hs₁ : IsSimpleGroup ↥L₁)
    (hs₂ : IsSimpleGroup ↥L₂) (hnab₁ : ∃ a b : ↥L₁, a * b ≠ b * a)
    (hnab₂ : ∃ a b : ↥L₂, a * b ≠ b * a) (hp₁ : p ∣ Nat.card ↥L₁) (hp₂ : p ∣ Nat.card ↥L₂)
    (hcent : IsPGroup p ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P ⊓
      Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₂ : Set G)))
    (hG₁ : Good ↥L₁) (hR₁ : Rk ↥L₁) (hG₂ : Good ↥L₂) (hR₂ : Rk ↥L₂) :
    MultiShapeAt p Good Rk x := by
  have hL₁P : L₁ ≤ P := fun l hl => (hEC (h₁E hl)).2
  have hL₂P : L₂ ≤ P := fun l hl => (hEC (h₂E hl)).2
  let C' : Subgroup ↥P := Subgroup.centralizer ({x} : Set ↥P)
  have hmapC : C'.map P.subtype = Subgroup.centralizer ({(x : G)} : Set G) ⊓ P :=
    map_centralizer_subtype' P x
  have memC : ∀ g : ↥P, g ∈ C' ↔
      (g : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
    intro g
    rw [← hmapC]
    exact (Subgroup.mem_map_iff_mem P.subtype_injective).symm
  let E' : Subgroup ↥P := E.comap P.subtype
  let L₁' : Subgroup ↥P := L₁.comap P.subtype
  let L₂' : Subgroup ↥P := L₂.comap P.subtype
  have eL₁ : ↥L₁' ≃* ↥L₁ := Subgroup.subgroupOfEquivOfLe hL₁P
  have eL₂ : ↥L₂' ≃* ↥L₂ := Subgroup.subgroupOfEquivOfLe hL₂P
  have hEC' : E' ≤ C' := fun e he => (memC e).2 (hEC he)
  have hEn' : ∀ g ∈ C', ∀ e ∈ E', g * e * g⁻¹ ∈ E' :=
    fun g hg e he => hEn _ ((memC g).1 hg) _ he
  have h₁E' : L₁' ≤ E' := fun l hl => h₁E hl
  have h₂E' : L₂' ≤ E' := fun l hl => h₂E hl
  have h₁n' : ∀ g ∈ E', ∀ l ∈ L₁', g * l * g⁻¹ ∈ L₁' := fun g hg l hl => h₁n _ hg _ hl
  have h₂n' : ∀ g ∈ E', ∀ l ∈ L₂', g * l * g⁻¹ ∈ L₂' := fun g hg l hl => h₂n _ hg _ hl
  have hs₁' : IsSimpleGroup ↥L₁' := eL₁.isSimpleGroup_congr.2 hs₁
  have hs₂' : IsSimpleGroup ↥L₂' := eL₂.isSimpleGroup_congr.2 hs₂
  have hnab₁' : ∃ a b : ↥L₁', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab₁
    exact ⟨eL₁.symm a, eL₁.symm b, fun h => hab (by simpa using congrArg eL₁ h)⟩
  have hnab₂' : ∃ a b : ↥L₂', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab₂
    exact ⟨eL₂.symm a, eL₂.symm b, fun h => hab (by simpa using congrArg eL₂ h)⟩
  have hp₁' : p ∣ Nat.card ↥L₁' := by
    rw [Nat.card_congr eL₁.toEquiv]
    exact hp₁
  have hp₂' : p ∣ Nat.card ↥L₂' := by
    rw [Nat.card_congr eL₂.toEquiv]
    exact hp₂
  have hcent' : IsPGroup p ↥(C' ⊓ Subgroup.centralizer (L₁' : Set ↥P) ⊓
      Subgroup.centralizer (L₂' : Set ↥P)) := by
    let D' : Subgroup ↥P := C' ⊓ Subgroup.centralizer (L₁' : Set ↥P) ⊓
      Subgroup.centralizer (L₂' : Set ↥P)
    have hmem : ∀ d : ↥D', ((d : ↥P) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P ⊓
        Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₂ : Set G) := by
      intro d
      obtain ⟨⟨hdC, hd1⟩, hd2⟩ := d.2
      refine ⟨⟨(memC _).1 hdC, ?_⟩, ?_⟩
      · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
        have := Subgroup.mem_centralizer_iff.1 hd1 (⟨l, hL₁P hl⟩ : ↥P) hl
        exact congrArg Subtype.val this
      · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
        have := Subgroup.mem_centralizer_iff.1 hd2 (⟨l, hL₂P hl⟩ : ↥P) hl
        exact congrArg Subtype.val this
    let f : ↥D' →* ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P ⊓
        Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₂ : Set G)) :=
      (P.subtype.comp D'.subtype).codRestrict _ hmem
    refine hcent.of_injective f ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hcore₁ : GLAPPrimeCore p ↥L₁' = ⊥ := glaPPrimeCore_eq_bot_of_simple hp hp₁'
  have hcore₂ : GLAPPrimeCore p ↥L₂' = ⊥ := glaPPrimeCore_eq_bot_of_simple hp hp₂'
  have hZ₁ : Subgroup.center ↥L₁' = ⊥ := center_eq_bot_of_simple_nonab hnab₁'
  have hZ₂ : Subgroup.center ↥L₂' = ⊥ := center_eq_bot_of_simple_nonab hnab₂'
  exact multiShapeAt_of_two_components hp hp2 E' L₁' L₂' hEC' hEn' h₁E' h₂E' h₁n' h₂n'
    (isQuasisimpleOpen_of_simple_nonab hnab₁') (isQuasisimpleOpen_of_simple_nonab hnab₂') hp₁' hp₂'
    hcent'
    (hGood _ _ ((pSimpleEquivSelf L₁' hcore₁ hZ₁).trans eL₁).symm hG₁)
    (hRk _ _ ((pQuotEquivSelf L₁' hcore₁).trans eL₁).symm hR₁)
    (hGood _ _ ((pSimpleEquivSelf L₂' hcore₂ hZ₂).trans eL₂).symm hG₂)
    (hRk _ _ ((pQuotEquivSelf L₂' hcore₂).trans eL₂).symm hR₂)

end TwoSubtype

end CFSG.HardMathSupport.Dickson.I271
