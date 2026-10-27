module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1419
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsUniAux.Block
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1419b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer
  b3Lie_comp_le_or_comm b3Lie_isQuasisimple_of_simple b3Lie_center_eq_bot)
open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot)
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Arith

theorem sl_order_ne {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) :
    q ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, (q ^ i - 1) ≠ 25920 * m.gcd (q - 1) := by
  intro h
  have hcop : Nat.Coprime (q ^ (m * (m - 1) / 2)) (m.gcd (q - 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right m (q - 1)) ?_
    have : Nat.Coprime (q - 1 + 1) (q - 1) := by simp
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hdvd : q ^ (m * (m - 1) / 2) ∣ 25920 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [← h]
    exact Dvd.intro _ rfl
  have hle : q ^ (m * (m - 1) / 2) ≤ 25920 := Nat.le_of_dvd (by norm_num) hdvd
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have h5 : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega : 5 ≤ m) (by omega : 4 ≤ m - 1)
    have h10 : 10 ≤ m * (m - 1) / 2 := by omega
    have hd10 : q ^ 10 ∣ 25920 := (pow_dvd_pow q h10).trans hdvd
    have hq2 : q = 2 := by
      by_contra hq2
      have h3 : 3 ^ 10 ≤ q ^ 10 := Nat.pow_le_pow_left (by omega) 10
      have := Nat.le_of_dvd (by norm_num) hd10
      omega
    subst hq2
    revert hd10
    decide
  interval_cases m
  · simp at h
    have hg : (2 : ℕ).gcd (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hq37 : q ≤ 37 := by
      by_contra hcon
      have h38 : 38 ≤ q := by omega
      have : q * (q ^ 2 - 1) ≥ 38 * (38 ^ 2 - 1) := by
        apply Nat.mul_le_mul h38
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h38 2) 1
      omega
    interval_cases q <;> simp_all
  · have hI : Finset.Icc 2 3 = {2, 3} := by decide
    simp [hI] at h hle
    have hq29 : q ≤ 29 := by
      by_contra hcon
      have h30 : 30 ≤ q := by omega
      have : 30 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h30 3
      omega
    interval_cases q <;> simp_all
  · have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
    simp [hI] at h hle
    have hq5 : q ≤ 5 := by
      by_contra hcon
      have h6 : 6 ≤ q := by omega
      have : 6 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left h6 6
      omega
    interval_cases q <;> simp_all

end Arith

section Cover

theorem isSolvable_sl_two_of_card_lt_four {E : Type} [Field E] [Fintype E]
    (h : Fintype.card E < 4) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
    Matrix.SpecialLinearGroup.toGL_injective

theorem not_isSolvable_of_quasisimple {L : Type*} [Group L] (hL : CFSG.Open.IsQuasisimple L) :
    ¬ Group.IsSolvable L := by
  intro hs
  have : Group.IsPerfect L := ⟨hL.1⟩
  have : Nontrivial L := by
    have := hL.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (congrArg _ h)⟩
  exact Group.IsPerfect.not_isSolvable L hs

theorem card_eq_mul_center_of_cover {X L T : Type*} [Group X] [Finite X] [Group L] [Group T]
    (hX : commutator X = ⊤) (f : X →* L) (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center X)
    (ρ : L →* T) (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center L)
    (hT : Subgroup.center T = ⊥) :
    Nat.card X = Nat.card T * Nat.card (Subgroup.center X) := by
  set g : X →* T := ρ.comp f with hg
  have hgs : Function.Surjective g := hρ.comp hf
  have hker : g.ker = Subgroup.center X := by
    apply le_antisymm
    · intro x hx
      have h1 : f x ∈ Subgroup.center L := hρk ((MonoidHom.mem_ker).2 hx)
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.comap_center_of_surjective hX f hf hfk]
      exact h1
    · intro z hz
      rw [MonoidHom.mem_ker]
      have h1 : g z ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨y, rfl⟩ := hgs t
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y)]
      rw [hT, Subgroup.mem_bot] at h1
      exact h1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgs).toEquiv, hker]

theorem false_of_sl_cover {E : Type} [Field E] [Fintype E] {m : ℕ} (hm : 2 ≤ m)
    {L : Type} [Group L] (hL : CFSG.Open.IsQuasisimple L)
    (f : Matrix.SpecialLinearGroup (Fin m) E →* L) (hf : Function.Surjective f)
    (hfk : f.ker ≤ Subgroup.center _)
    {T : Type} [Group T] [IsSimpleGroup T] (hTna : ∃ a b : T, a * b ≠ b * a)
    (hT : Nat.card T = 25920) (ρ : L →* T) (hρ : Function.Surjective ρ) : False := by
  have h4 : 3 ≤ m ∨ 4 ≤ Nat.card E := by
    by_contra hcon
    push Not at hcon
    obtain rfl : m = 2 := by omega
    have hlt : Fintype.card E < 4 := by rw [← Nat.card_eq_fintype_card]; exact hcon.2
    haveI := isSolvable_sl_two_of_card_lt_four hlt
    exact not_isSolvable_of_quasisimple hL (Group.isSolvable_of_surjective hf)
  have hX := CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm h4
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ :=
    Group.isPerfect_def.mp hX.1
  have hρk : ρ.ker ≤ Subgroup.center L := by
    refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL ρ.ker ?_
    intro htop
    obtain ⟨a, b, hab⟩ := hTna
    apply hab
    have hone : ∀ t : T, t = 1 := fun t => by
      obtain ⟨l, rfl⟩ := hρ t
      exact (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top l)
    rw [hone a, hone b]
  have hcard := card_eq_mul_center_of_cover hperf f hf hfk ρ hρ hρk (b3Lie_center_eq_bot hTna)
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear E m (by omega),
    CFSG.OrderReductions.LinearOrders.card_specialLinear_center E m (by omega), hT] at hcard
  have hq : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  exact sl_order_ne hq hm hcard

end Cover

section Onto

theorem exists_perfect_map_eq_top {H F : Type*} [Group H] [Finite H] [Group F]
    (π : H →* F) (hπ : Function.Surjective π) (hF : commutator F = ⊤) :
    ∃ P : Subgroup H, ⁅P, P⁆ = P ∧ P.map π = ⊤ := by
  classical
  have hex : ∃ n, ∃ P : Subgroup H, P.map π = ⊤ ∧ Nat.card P = n :=
    ⟨_, ⊤, by rw [Subgroup.map_top]; exact MonoidHom.range_eq_top_of_surjective π hπ, rfl⟩
  obtain ⟨P, hP, hPn⟩ := Nat.find_spec hex
  refine ⟨P, ?_, hP⟩
  have h1 : (⁅P, P⁆).map π = ⊤ := by
    rw [Subgroup.map_commutator, hP, ← _root_.commutator_def]
    exact hF
  have h2 : Nat.find hex ≤ Nat.card (⁅P, P⁆ : Subgroup H) := Nat.find_min' hex ⟨⁅P, P⁆, h1, rfl⟩
  have hle : ⁅P, P⁆ ≤ P := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  exact Subgroup.eq_of_le_of_card_ge hle (hPn ▸ h2)

theorem mem_sup_of_commute {G : Type*} [Group G] {A Z : Subgroup G}
    (h : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a) {x : G} (hx : x ∈ A ⊔ Z) :
    ∃ a ∈ A, ∃ z ∈ Z, x = a * z := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, Z.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, Z.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    obtain ⟨a', ha', z', hz', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', z * z', Z.mul_mem hz hz', ?_⟩
    have := h a' ha' z hz
    calc a * z * (a' * z') = a * (z * a') * z' := by group
      _ = a * (a' * z) * z' := by rw [this]
      _ = a * a' * (z * z') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, z⁻¹, Z.inv_mem hz, ?_⟩
    have := h a ha z hz
    calc (a * z)⁻¹ = (z * a)⁻¹ := by rw [this]
      _ = a⁻¹ * z⁻¹ := by group

theorem exists_component_onto {S : Type} [Group S] [Finite S] {C H : Subgroup S}
    (hHC : IsSubnormal H C)
    (hlayer : ∀ P : Subgroup S, P ≤ C → ⁅P, P⁆ = P → P ≤ GLALayer C)
    {F : Type} [Group F] [IsSimpleGroup F] (hna : ∃ a b : F, a * b ≠ b * a)
    (ψ : ↥H →* F) (hψ : Function.Surjective ψ) :
    ∃ (K : Subgroup S) (hKH : K ≤ H), IsComponentOf K C ∧
      Function.Surjective (ψ.comp (Subgroup.inclusion hKH)) := by
  have hFperf : commutator F = ⊤ := (b3Lie_isQuasisimple_of_simple hna).1
  have hZF : Subgroup.center F = ⊥ := b3Lie_center_eq_bot hna
  obtain ⟨P, hPP, hPψ⟩ := exists_perfect_map_eq_top ψ hψ hFperf
  by_contra hno'
  have hno : ∀ (K : Subgroup S) (hKH : K ≤ H), IsComponentOf K C →
      ¬ Function.Surjective (ψ.comp (Subgroup.inclusion hKH)) :=
    fun K hKH hK hs => hno' ⟨K, hKH, hK, hs⟩
  have hHle : H ≤ C := hHC.le
  have step1 : ∀ (K : Subgroup S) (hKH : K ≤ H), IsComponentOf K C →
      ∀ k : ↥K, ψ (Subgroup.inclusion hKH k) = 1 := by
    intro K hKH hK k
    have hKsub : IsSubnormal K H := by
      have := hK.2.1.inf_of_le hHle
      rwa [inf_eq_left.2 hKH] at this
    have hsn : ((K.subgroupOf H).map ψ).IsSubnormal := (hKsub.subgroupOf).map hψ
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsn with h | h
    · have hmem : ψ (Subgroup.inclusion hKH k) ∈ (K.subgroupOf H).map ψ :=
        Subgroup.mem_map_of_mem ψ (show Subgroup.inclusion hKH k ∈ K.subgroupOf H from k.2)
      rw [h] at hmem
      exact (Subgroup.mem_bot).1 hmem
    · exfalso
      refine hno K hKH hK fun f => ?_
      have hf : f ∈ (K.subgroupOf H).map ψ := h ▸ Subgroup.mem_top f
      obtain ⟨y, hy, rfl⟩ := hf
      exact ⟨⟨y.1, hy⟩, rfl⟩
  set A : Subgroup S := ψ.ker.map H.subtype with hA
  set Z : Subgroup S := Subgroup.centralizer (H : Set S) with hZ
  have hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := by
    rintro _ ⟨a, ha, rfl⟩ z hz
    exact Subgroup.mem_centralizer_iff.1 hz a a.2
  have hlay : GLALayer C ≤ A ⊔ Z := by
    refine sSup_le fun K hK => ?_
    by_cases hKH : K ≤ H
    · refine le_sup_of_le_left ?_
      intro k hk
      exact ⟨⟨k, hKH hk⟩, (MonoidHom.mem_ker).2 (step1 K hKH hK ⟨k, hk⟩), rfl⟩
    · refine le_sup_of_le_right ?_
      rcases b3Lie_comp_le_or_comm hK hHle hHC with h | h
      · exact absurd h hKH
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have step3 : ∀ p ∈ P, ψ p = 1 := by
    intro p hp
    have hP'C : P.map H.subtype ≤ C := (Subgroup.map_subtype_le P).trans hHle
    have hP'perf : ⁅P.map H.subtype, P.map H.subtype⁆ = P.map H.subtype := by
      rw [← Subgroup.map_commutator, hPP]
    have hx : (p : S) ∈ A ⊔ Z := hlay (hlayer _ hP'C hP'perf ⟨p, hp, rfl⟩)
    obtain ⟨a, ha, z, hz, hpaz⟩ := mem_sup_of_commute hAZ hx
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨zH, hzH⟩ : ∃ zH : ↥H, zH = a'⁻¹ * p := ⟨_, rfl⟩
    have hpa : p = a' * zH := by rw [hzH]; group
    have hzHz : (zH : S) = z := by
      have h1 : (p : S) = (a' : S) * (zH : S) := congrArg (fun x : ↥H => (x : S)) hpa
      exact mul_left_cancel (h1.symm.trans hpaz)
    have hcen : ψ zH ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro f
      obtain ⟨y, rfl⟩ := hψ f
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (y : S) * (zH : S) = (zH : S) * (y : S)
      rw [hzHz]
      exact Subgroup.mem_centralizer_iff.1 hz y y.2
    rw [hZF, Subgroup.mem_bot] at hcen
    have ha1 : ψ a' = 1 := (MonoidHom.mem_ker).1 ha'
    rw [hpa, map_mul, ha1, hcen, one_mul]
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  have hone : ∀ f : F, f = 1 := fun f => by
    have hf : f ∈ P.map ψ := hPψ ▸ Subgroup.mem_top f
    obtain ⟨p, hp, rfl⟩ := hf
    exact step3 p hp
  rw [hone a, hone b]

@[expose] def SLCover (L : Type) [Group L] : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Fintype E) (m : ℕ), 2 ≤ m ∧
    ∃ f : Matrix.SpecialLinearGroup (Fin m) E →* L, Function.Surjective f ∧
      f.ker ≤ Subgroup.center _

theorem false_of_layer_sl {S : Type} [Group S] [Finite S] {β : MulAut S} (hlayer : PerfectInLayer β)
    (htype : ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) → SLCover ↥L)
    {A : Subgroup S} (hA : GLAPComponent 5 (fixSubgroup β) A) (hcard : Nat.card (PSimple 5 A) = 25920) :
    False := by
  obtain ⟨hsimp, hna⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian Nat.prime_five hA
  haveI := hsimp
  let ψ : ↥A →* PSimple 5 A :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 5 A))).comp (QuotientGroup.mk' (GLAPPrimeCore 5 ↥A))
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨L, hLA, hL, hLs⟩ := exists_component_onto hA.2.1 hlayer hna ψ hψ
  obtain ⟨E, _, _, m, hm, f, hf, hfk⟩ := htype L hL
  exact false_of_sl_cover hm hL.2.2 f hf hfk hna hcard (ψ.comp (Subgroup.inclusion hLA)) hLs

end Onto

section Transport

theorem fixSubgroup_congr {S G : Type} [Group S] [Group G] (e : S ≃* G) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map e.toMonoidHom := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

theorem comp_congr {S G : Type} [Group S] [Finite S] [Group G] {p : ℕ} (hp : p.Prime) (e : S ≃* G)
    {β : MulAut S} {A : Subgroup S} (hA : GLAPComponent p (fixSubgroup β) A) :
    GLAPComponent p (fixSubgroup (MulAut.congr e β)) (A.map e.toMonoidHom) ∧
      Nat.card (PSimple p (A.map e.toMonoidHom)) = Nat.card (PSimple p A) := by
  refine ⟨?_, ?_⟩
  · rw [fixSubgroup_congr]
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv hp e hA
  · exact (Nat.card_congr
      (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p (A.equivMapOfInjective e.toMonoidHom
        e.injective)).toEquiv).symm

theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

end Transport

section Linear

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem exists_card_eq_pow_ringChar {K : Type} [Field K] [Finite K] :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩

theorem linear_cases_of_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL n K)) (hβ : β ^ p = 1) :
    (∃ (A : GL (Fin n) K) (c : Kˣ), A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL n K)) (σ : K ≃+* K), orderOf σ = p ∧
      β = h * LinearFlag.fieldAut n K σ * h⁻¹) := by
  obtain ⟨f, hf, hℓ, hK⟩ := exists_card_eq_pow_ringChar (K := K)
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    hℓ hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n K
  · left
    have hrange : LinearFlag.linearAutGroup n K = (LinearFlag.conjAut n K).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ p ∈ (LinearFlag.conjAut n K).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, rfl⟩
  · right
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ∈
        LinearFlag.semilinearAutGroup n K :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A))
        (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
    have hne : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ≠ 1 := fun h =>
      hlin (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) = p :=
      orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hℓ hf hn hK hp
        hmem hlin hord
    exact ⟨h, τ, hτ, hβτ⟩

theorem five_ne_zero_of_dvd {F : Type} [Field F] [Finite F] (h5 : 5 ∣ Nat.card F - 1) :
    (5 : F) ≠ 0 := by
  intro h0
  obtain ⟨f, hf, hℓ, hK⟩ := exists_card_eq_pow_ringChar (K := F)
  have hdvd : ringChar F ∣ 5 := (CharP.cast_eq_zero_iff F (ringChar F) 5).1 (by exact_mod_cast h0)
  have hℓ5 : ringChar F = 5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 hdvd
  rw [hℓ5] at hK
  have h1 : 5 ∣ Nat.card F := by rw [hK]; exact dvd_pow_self 5 (by omega)
  have hpos : 1 ≤ Nat.card F := Nat.card_pos
  have : 5 ∣ 1 := by
    have h2 : Nat.card F = Nat.card F - 1 + 1 := by omega
    rw [h2] at h1
    exact (Nat.dvd_add_right h5).1 h1
  omega

theorem false_of_psl_five {F : Type} [Field F] [Finite F] (h5 : 5 ∣ Nat.card F - 1)
    (β : MulAut (LinearFlag.projectiveSL 5 F)) (hβ : β ^ 5 = 1)
    {A : Subgroup (LinearFlag.projectiveSL 5 F)} (hA : GLAPComponent 5 (fixSubgroup β) A)
    (hcard : Nat.card (PSimple 5 A) = 25920) : False := by
  have hF5 := five_ne_zero_of_dvd h5
  rcases linear_cases_of_three_le Nat.prime_five (by norm_num) (by norm_num) β hβ with
    ⟨A0, c, hA0, rfl⟩ | ⟨h, σ, hσ, rfl⟩
  · refine false_of_layer_sl
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conjAut
        (p := 5) (by exact_mod_cast hF5) hA0) (fun L hL => ?_) hA hcard
    obtain ⟨E, hE1, hE2, m, hm, -, f, hf, hfk⟩ :=
      linear_inner_component_type (p := 5) (by exact_mod_cast hF5) hA0 L hL
    exact ⟨E, hE1, hE2, m, hm, f, hf, hfk⟩
  ·
    have hconj : MulAut.congr ((h⁻¹ : MulAut _) : _ ≃* _)
        (h * LinearFlag.fieldAut 5 F σ * h⁻¹) = LinearFlag.fieldAut 5 F σ := by
      rw [congr_self_eq]
      group
    obtain ⟨hA', hcard'⟩ := comp_congr Nat.prime_five ((h⁻¹ : MulAut _) : _ ≃* _) hA
    rw [hconj] at hA'
    refine false_of_layer_sl
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_fieldAut
        (by norm_num) Nat.prime_five (by norm_num) σ hσ) (fun L hL => ?_) hA' (hcard'.trans hcard)
    obtain ⟨-, f, hf, hfk⟩ := linearFieldAut_components (n := 5) (by norm_num) σ L hL
    haveI : Finite ↥(CFSG.GH74.GLS.IVK.fixedField σ) := inferInstance
    exact ⟨_, inferInstance, Fintype.ofFinite _, 5, by norm_num, f, hf, hfk⟩

end Linear

section SUCover

open CFSG.ClassicalGroups.UnitaryFlag

theorem su_order_ne {q m g : ℕ} (hq : 3 ≤ q) (hm : 3 ≤ m) (hg : g ∣ q + 1) {P : ℤ}
    (hP : P = ∏ i ∈ Finset.Icc 2 m, ((q : ℤ) ^ i - (-1) ^ i))
    (h : (q : ℤ) ^ (m * (m - 1) / 2) * P = 25920 * g) : False := by
  have hcop : Nat.Coprime q g := by
    refine Nat.Coprime.coprime_dvd_right hg ?_
    simp
  have hcopZ : IsCoprime ((q : ℤ) ^ (m * (m - 1) / 2)) (g : ℤ) :=
    (Nat.isCoprime_iff_coprime.2 hcop).pow_left
  have hdvdZ : ((q : ℤ) ^ (m * (m - 1) / 2)) ∣ 25920 :=
    hcopZ.dvd_of_dvd_mul_right (Dvd.intro _ h)
  have hdvd : q ^ (m * (m - 1) / 2) ∣ 25920 := by
    exact_mod_cast hdvdZ
  have hk : 3 ≤ m * (m - 1) / 2 := by
    have : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    omega
  have h3 : q ^ 3 ∣ 25920 := (pow_dvd_pow q hk).trans hdvd
  have hq29 : q ≤ 29 := by
    by_contra hcon
    have h30 : 30 ≤ q := by omega
    have h1 : 30 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h30 3
    have h2 : q ^ 3 ≤ 25920 := Nat.le_of_dvd (by norm_num) h3
    omega
  have hm3 : m = 3 := by
    by_contra hne
    have h6 : 6 ≤ m * (m - 1) / 2 := by
      have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hd6 : q ^ 6 ∣ 25920 := (pow_dvd_pow q h6).trans hdvd
    have hq5 : q ≤ 5 := by
      by_contra hcon
      have h1 : 6 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have h2 : q ^ 6 ≤ 25920 := Nat.le_of_dvd (by norm_num) hd6
      omega
    interval_cases q <;> revert hd6 <;> decide
  subst hm3
  have hgle : g ≤ q + 1 := Nat.le_of_dvd (by omega) hg
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hP, hI, Finset.prod_pair (by decide)] at h
  interval_cases q <;> norm_num at h <;> omega

theorem natCard_statedSU_cast {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card ↥(StatedSU n (p ^ f) K) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).2.1
  rw [show StatedSU n (p ^ f) K = unitarySU p f K n from rfl, unitarySU_eq_gramSU h, card_gramSU,
    hU]

theorem exists_pow_of_card_sq {K : Type} [Field K] [Fintype K] {q : ℕ}
    (hK : Fintype.card K = q ^ 2) : ∃ f : ℕ, 1 ≤ f ∧ q = ringChar K ^ f ∧ (ringChar K).Prime := by
  haveI := ringChar.charP K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hq : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hp).1 hq
  refine ⟨f, ?_, hqf, hp⟩
  by_contra h0
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hqf
  have h1 : Fintype.card K = 1 := by rw [hK, hqf]; norm_num
  have := Fintype.one_lt_card (α := K)
  omega

theorem false_of_su_cover {K : Type} [Field K] [Fintype K] {m q : ℕ} (hm : 3 ≤ m) (hq : 3 ≤ q)
    (hK : Fintype.card K = q ^ 2) {L : Type} [Group L] (hL : CFSG.Open.IsQuasisimple L)
    (f : ↥(StatedSU m q K) →* L) (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center _)
    {T : Type} [Group T] [IsSimpleGroup T] (hTna : ∃ a b : T, a * b ≠ b * a)
    (hT : Nat.card T = 25920) (ρ : L →* T) (hρ : Function.Surjective ρ) : False := by
  obtain ⟨g, hg, rfl, hp⟩ := exists_pow_of_card_sq hK
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hNat : Nat.card K = (ringChar K ^ g) ^ 2 := by rw [Nat.card_eq_fintype_card, hK]
  have hUF : UnitaryFieldData (ringChar K) g K := ⟨hp, hg, by rw [hNat, ← pow_mul, mul_comm]⟩
  have hmq : (m, ringChar K ^ g) ≠ (3, 2) := fun hc => by
    have := (Prod.mk.inj hc).2
    omega
  obtain ⟨hQ, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat hm hmq
  have hperf : commutator ↥(StatedSU m (ringChar K ^ g) K) = ⊤ := Group.isPerfect_def.mp hQ.1
  have hρk : ρ.ker ≤ Subgroup.center L := by
    refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL ρ.ker ?_
    intro htop
    obtain ⟨a, b, hab⟩ := hTna
    apply hab
    have hone : ∀ t : T, t = 1 := fun t => by
      obtain ⟨l, rfl⟩ := hρ t
      exact (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top l)
    rw [hone a, hone b]
  have hcard := card_eq_mul_center_of_cover hperf f hf hfk ρ hρ hρk (b3Lie_center_eq_bot hTna)
  have hZc : Nat.card (Subgroup.center ↥(StatedSU m (ringChar K ^ g) K)) =
      Nat.gcd m (ringChar K ^ g + 1) := by
    rw [hZ]
    exact (CFSG.LinearGroups.unitary_scalar_kernel hp hNat (by omega)).2.2
  rw [hT, hZc] at hcard
  have hform := natCard_statedSU_cast hUF (n := m) (by omega)
  rw [hcard] at hform
  exact su_order_ne (q := ringChar K ^ g) (m := m) (g := Nat.gcd m (ringChar K ^ g + 1)) hq hm
    (Nat.gcd_dvd_right _ _) rfl (by push_cast at hform ⊢; linarith)

@[expose] def SUCover (L : Type) [Group L] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (m q : ℕ), 3 ≤ m ∧ 3 ≤ q ∧ Fintype.card K = q ^ 2 ∧
    ∃ f : ↥(StatedSU m q K) →* L, Function.Surjective f ∧ f.ker ≤ Subgroup.center _

theorem false_of_layer {S : Type} [Group S] [Finite S] {β : MulAut S} (hlayer : PerfectInLayer β)
    (htype : ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) → SLCover ↥L ∨ SUCover ↥L)
    {A : Subgroup S} (hA : GLAPComponent 5 (fixSubgroup β) A) (hcard : Nat.card (PSimple 5 A) = 25920) :
    False := by
  obtain ⟨hsimp, hna⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian Nat.prime_five hA
  haveI := hsimp
  let ψ : ↥A →* PSimple 5 A :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 5 A))).comp (QuotientGroup.mk' (GLAPPrimeCore 5 ↥A))
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨L, hLA, hL, hLs⟩ := exists_component_onto hA.2.1 hlayer hna ψ hψ
  rcases htype L hL with ⟨E, _, _, m, hm, f, hf, hfk⟩ | ⟨E, _, _, m, q, hm, hq, hE, f, hf, hfk⟩
  · exact false_of_sl_cover hm hL.2.2 f hf hfk hna hcard (ψ.comp (Subgroup.inclusion hLA)) hLs
  · exact false_of_su_cover hm hq hE hL.2.2 f hf hfk hna hcard (ψ.comp (Subgroup.inclusion hLA)) hLs

end SUCover

section UnitaryBlock

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem specialBlock_type_of_good (hℓ : 3 ≤ ℓ) (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a) :
    (∃ (E : Type) (_ : Field E) (_ : Fintype E) (m : ℕ), 2 ≤ m ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃* Matrix.SpecialLinearGroup (Fin m) E)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Fintype E) (m q : ℕ), 3 ≤ m ∧ 3 ≤ q ∧
        Fintype.card E = q ^ 2 ∧ Nonempty (↥(specialBlock B x (a : K[X])) ≃* ↥(StatedSU m q E))) := by
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos hK.one_le hd
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.nonempty_specialBlock_mulEquiv_sesqSU
        hself (selfDualPrimaryBlock H a hself)
    have hcardE : Fintype.card (AdjoinRoot (a : K[X])) =
        (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hE.card_eq_sq
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      exact Or.inl ⟨hE.fixedField, inferInstance, Fintype.ofFinite _, 2, le_rfl, ⟨e.trans e2⟩⟩
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (e.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hq3 : 3 ≤ ℓ ^ (f * (a : K[X]).natDegree) := hℓ.trans (Nat.le_self_pow (by omega) ℓ)
      exact Or.inr ⟨AdjoinRoot (a : K[X]), inferInstance, inferInstance,
        primaryMultiplicity (x : Module.End K V) (a : K[X]), ℓ ^ (f * (a : K[X]).natDegree), hm, hq3,
        hcardE, ⟨e4⟩⟩
  · obtain ⟨e⟩ := CFSG.HardMathSupport.Dickson.Sec6.nonempty_specialBlock_mulEquiv_SL
      (pairedPrimaryBlock H a (Ne.symm hself))
    exact Or.inl ⟨AdjoinRoot (a : K[X]), inferInstance, inferInstance, _, hm2, ⟨e⟩⟩

end UnitaryBlock

section UnitaryComp

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem ker_le_center_comp (X : Type) [Group X] (F : Subgroup ↥(gramSU h (idGram K n)))
    (ε : X ≃* ↥F) :
    (((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).subgroupMap F).comp
      ε.toMonoidHom).ker ≤ Subgroup.center X := by
  intro u hu
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
  have h1 : QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
      (ε u : ↥(gramSU h (idGram K n))) = 1 := congrArg Subtype.val hu
  have h2 : ((ε u : ↥F) : ↥(gramSU h (idGram K n))) ∈
      normOneScalars h (gramSU h (idGram K n)) n := (QuotientGroup.eq_one_iff _).1 h1
  have h3 := normOneScalars_le_center h _ n h2
  rw [Subgroup.mem_center_iff]
  intro w
  apply ε.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 h3 _

theorem cover_of_component_primeFormConjHom (hℓ : 3 ≤ ℓ) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (T : Subgroup (primeFormP h (idGram K n)))
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A))) :
    SLCover ↥T ∨ SUCover ↥T := by
  classical
  haveI := h.finite
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have H := UnitaryBlocks.primaryData_toLin' h A.2 hp hpℓ hA
  obtain ⟨a, ha⟩ := UnitaryBlocks.exists_good_block_of_component hq A rfl H T hT
  have hSle : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X]) ≤ (UnitaryBlocks.toLinSU h n).range := fun g hg =>
    UnitaryBlocks.mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  set F : Subgroup ↥(gramSU h (idGram K n)) :=
    (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])).comap (UnitaryBlocks.toLinSU h n) with hFdef
  have hFmap : F.map (UnitaryBlocks.toLinSU h n) = specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X]) :=
    Subgroup.map_comap_eq_self hSle
  let εF : ↥F ≃* ↥(specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])) :=
    (Subgroup.equivMapOfInjective F (UnitaryBlocks.toLinSU h n)
      UnitaryBlocks.toLinSU_injective).trans (MulEquiv.subgroupCongr hFmap)
  subst ha
  rcases specialBlock_type_of_good hℓ H a.1 a.2 with ⟨E, _, _, m, hm, ⟨e⟩⟩ |
      ⟨E, _, _, m, q, hm, hq3, hE, ⟨e⟩⟩
  · left
    let ε : Matrix.SpecialLinearGroup (Fin m) E ≃* ↥F := e.symm.trans εF.symm
    exact ⟨E, inferInstance, inferInstance, m, hm,
      ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).subgroupMap F).comp
        ε.toMonoidHom,
      (MonoidHom.subgroupMap_surjective _ F).comp ε.surjective, ker_le_center_comp _ F ε⟩
  · right
    let ε : ↥(StatedSU m q E) ≃* ↥F := e.symm.trans εF.symm
    exact ⟨E, inferInstance, inferInstance, m, q, hm, hq3, hE,
      ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).subgroupMap F).comp
        ε.toMonoidHom,
      (MonoidHom.subgroupMap_surjective _ F).comp ε.surjective, ker_le_center_comp _ F ε⟩

end UnitaryComp

section Unitary

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

theorem false_of_psu_five {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 3 f F)
    (β : MulAut (primeFormP h (idGram F 5))) (hβ : β ^ 5 = 1)
    {A : Subgroup (primeFormP h (idGram F 5))} (hA : GLAPComponent 5 (fixSubgroup β) A)
    (hcard : Nat.card (PSimple 5 A) = 25920) : False := by
  haveI := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 5) F) := isPrimeFormGram_idGram
  have hn3 : 3 ≤ 5 := by norm_num
  have hq' : ¬(5 = 3 ∧ 3 ^ f = 2) := by omega
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' β = 1
  · have hβD : β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A0, hA0⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A0 ^ 5, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA0, hβ, map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A0 : GL (Fin 5) F) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
      rwa [SubgroupClass.coe_pow] at hc
    subst hA0
    exact false_of_layer
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_primeFormConjHom h
        Nat.prime_five (by norm_num) A0 hAp)
      (fun L hL => cover_of_component_primeFormConjHom le_rfl Nat.prime_five (by norm_num) A0 hAp L hL)
      hA hcard
  · have hne : β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hord : orderOf β = 5 := orderOf_eq_prime hβ hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' β) = 5 :=
      orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' Nat.prime_five
        (by norm_num) β hord _ rfl hσp
    have hconj : MulAut.congr (((primeFormConjHom h (idGram F 5) M)⁻¹ : MulAut _) : _ ≃* _) β =
        primeFormFieldHom h hC (primeFormFieldFactor h hC hn3 hq' β) := by
      rw [congr_self_eq, inv_inv]
      exact hM
    obtain ⟨hA', hcard'⟩ :=
      comp_congr Nat.prime_five (((primeFormConjHom h (idGram F 5) M)⁻¹ : MulAut _) : _ ≃* _) hA
    rw [hconj] at hA'
    refine false_of_layer
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_primeFormFieldHom h hn3
        Nat.prime_five (by norm_num) _ hσp) (fun L hL => Or.inr ?_) hA' (hcard'.trans hcard)
    obtain ⟨-, g, hg, hgk⟩ := unitary_fieldAut_components h hn3 hC Nat.prime_five (by norm_num) hσp L hL
    have h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_five (by norm_num) hσp
    haveI := h₀.finite
    letI : Fintype (CFSG.LieType.Chevalley.fixSubfield (primeFormFieldFactor h hC hn3 hq' β)) :=
      Fintype.ofFinite _
    refine ⟨_, inferInstance, inferInstance, 5, 3 ^ (f / 5), by norm_num, ?_, ?_, g, hg, hgk⟩
    · exact Nat.le_self_pow (by have := h₀.one_le; omega) 3
    · rw [← Nat.card_eq_fintype_card]
      exact h₀.card_eq_sq

end Unitary

section Transfer

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)

theorem center_transfer {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (x : MulAut K)
    {J : Subgroup K} (hJ : GLAPComponent p (fixSubgroup x) J) :
    GLAPComponent p (fixSubgroup (centerQuotientHom K x))
        (J.map (QuotientGroup.mk' (Subgroup.center K))) ∧
      Nonempty (PSimple p J ≃* PSimple p (J.map (QuotientGroup.mk' (Subgroup.center K)))) := by
  have hπs : Function.Surjective (QuotientGroup.mk' (Subgroup.center K)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ Subgroup.center K :=
    (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ k, QuotientGroup.mk' (Subgroup.center K) (x k) =
      centerQuotientHom K x (QuotientGroup.mk' (Subgroup.center K) k) :=
    fun k => (onCenterQuotient_apply_mk x k).symm
  have hJ' := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup _ hker x _ hαβ
    hπs hp hJ
  exact ⟨hJ', CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map hp _ hJ hJ'⟩

theorem exists_pow_of_natCard_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : ∃ f : ℕ, 1 ≤ f ∧ q = ringChar K ^ f ∧ (ringChar K).Prime := by
  letI := Fintype.ofFinite K
  exact exists_pow_of_card_sq (by rw [← Nat.card_eq_fintype_card]; exact hK)

end Transfer

section SporOrder

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (typeSign)

@[expose] def SporNoOmegaDown (p : ℕ) (ε : Bool) (n : ℕ) (name : TauCeti.SporadicName) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    ∀ s : T, orderOf s = p → ∀ I : Subgroup T,
      GLAPComponent p (Subgroup.centralizer ({s} : Set T)) I → ¬ IsOmegaTwo ε (n + 1) (PSimple p I)

@[expose] def sporOmegaCases : List (TauCeti.SporadicName × Bool × ℕ × ℕ) :=
  [(.McL, false, 2, 5), (.Suz, false, 2, 5), (.Co3, false, 2, 5), (.Co2, false, 2, 5),
    (.HN, false, 2, 5), (.Ly, false, 2, 5), (.Th, false, 2, 5), (.Fi23, false, 2, 5),
    (.Co1, false, 2, 5), (.Fi24Prime, false, 2, 5), (.B, false, 2, 5), (.M, false, 2, 5),
    (.Th, true, 3, 7), (.Co1, true, 3, 7), (.Fi24Prime, true, 3, 7), (.B, true, 3, 7),
    (.M, true, 3, 7), (.B, true, 4, 5), (.M, true, 4, 5), (.M, false, 5, 11)]

theorem mul_card_pSimple_dvd {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) {s : T}
    (hs : orderOf s = p) {I : Subgroup T}
    (hI : GLAPComponent p (Subgroup.centralizer ({s} : Set T)) I) :
    p * Nat.card (PSimple p I) ∣ Nat.card (Subgroup.centralizer ({s} : Set T)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup T := Subgroup.centralizer ({s} : Set T) with hC
  have hQ : Nat.card (PQuot p I) =
      Nat.card (Subgroup.center (PQuot p I)) * Nat.card (PSimple p I) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot p I))]
    exact mul_comm _ _
  have hQI : Nat.card (PQuot p I) ∣ Nat.card I := Subgroup.card_quotient_dvd_card _
  have hIC : Nat.card I ∣ Nat.card C := Subgroup.card_dvd_of_le hI.1
  have hAI : Nat.card (PSimple p I) ∣ Nat.card I := (Dvd.intro_left _ hQ.symm).trans hQI
  by_cases hZ : Subgroup.center (PQuot p I) = ⊥
  ·
    have hsI : s ∉ I := by
      intro hsI
      have hcen : (⟨s, hsI⟩ : ↥I) ∈ Subgroup.center ↥I := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.1 (hI.1 g.2)
      have himg : (QuotientGroup.mk (⟨s, hsI⟩ : ↥I) : PQuot p I) ∈ Subgroup.center (PQuot p I) :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨_, hcen, rfl⟩
      rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at himg
      have hdvd : orderOf (⟨s, hsI⟩ : ↥I) ∣ Nat.card (GLAPPrimeCore p ↥I) :=
        Subgroup.orderOf_dvd_natCard _ himg
      rw [Subgroup.orderOf_mk, hs] at hdvd
      have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥I)) := CFSG.pPrimeCore_coprime_card
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hcomm : ∀ (a : ↥I) (b : ↥(Subgroup.zpowers s)),
        Commute (I.subtype a) ((Subgroup.zpowers s).subtype b) := by
      intro a b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
      have ha : Commute (a : T) s := Subgroup.mem_centralizer_singleton_iff.1 (hI.1 a.2)
      show Commute (a : T) (b : T)
      rw [← hk]
      exact ha.zpow_right k
    set φ : ↥I × ↥(Subgroup.zpowers s) →* T :=
      MonoidHom.noncommCoprod I.subtype (Subgroup.zpowers s).subtype hcomm with hφ
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      have hab' : (a : T) * (b : T) = 1 := hab
      have hab2 : (a : T) = (b : T)⁻¹ := eq_inv_of_mul_eq_one_left hab'
      have hbI : ((b : T)⁻¹) ∈ I := hab2 ▸ a.2
      have hb1 : (b : T) = 1 := by
        by_contra hb1
        have hbI' : (b : T) ∈ I := by simpa using I.inv_mem hbI
        have hne : I ⊓ Subgroup.zpowers s ≠ ⊥ := by
          intro hbot
          have : (b : T) ∈ I ⊓ Subgroup.zpowers s := ⟨hbI', b.2⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact hb1 this
        have hprime : (Nat.card ↥(Subgroup.zpowers s)).Prime := by
          rw [Nat.card_zpowers, hs]; exact hp
        have hsub : (I ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s) = ⊤ := by
          haveI : Fact (Nat.card ↥(Subgroup.zpowers s)).Prime := ⟨hprime⟩
          rcases Subgroup.eq_bot_or_eq_top_of_prime_card
            ((I ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s)) with h | h
          · exact absurd ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le inf_le_right) hne
          · exact h
        have hle : Subgroup.zpowers s ≤ I ⊓ Subgroup.zpowers s :=
          Subgroup.subgroupOf_eq_top.1 hsub
        exact hsI (hle (Subgroup.mem_zpowers s)).1
      have ha1 : (a : T) = 1 := by rw [hab2, hb1, inv_one]
      exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
    have hrange : φ.range ≤ C := by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      show (a : T) * (b : T) ∈ C
      refine C.mul_mem (hI.1 a.2) ?_
      exact (Subgroup.zpowers_le.2 hsC) b.2
    have hcard : Nat.card φ.range = Nat.card I * p := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
        hs]
    have h1 : Nat.card I * p ∣ Nat.card C := hcard ▸ Subgroup.card_dvd_of_le hrange
    rw [mul_comm p]
    exact (Nat.mul_dvd_mul_right hAI p).trans h1
  ·
    have hZp : IsPGroup p ↥(Subgroup.center (PQuot p I)) :=
      Inputs1419.isPGroup_center hp (glaPPrimeCore_quotient_eq_bot hp)
    have hpZ : p ∣ Nat.card ↥(Subgroup.center (PQuot p I)) := by
      rcases hZp.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZ
      · exact h1
    calc p * Nat.card (PSimple p I)
        ∣ Nat.card (Subgroup.center (PQuot p I)) * Nat.card (PSimple p I) :=
          Nat.mul_dvd_mul_right hpZ _
      _ = Nat.card (PQuot p I) := hQ.symm
      _ ∣ Nat.card C := hQI.trans hIC

theorem exists_spor_comp (hOut : SporadicOuterLeTwo) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) {name : TauCeti.SporadicName}
    (f : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.sporadic name).Group) {x : MulAut K}
    (hx : orderOf x = p) {J₁ : Subgroup K} (hJ₁ : GLAPComponent p (fixSubgroup x) J₁) :
    ∃ s : K ⧸ Subgroup.center K, orderOf s = p ∧ ∃ I : Subgroup (K ⧸ Subgroup.center K),
      GLAPComponent p (Subgroup.centralizer ({s} : Set (K ⧸ Subgroup.center K))) I ∧
        Nonempty (PSimple p J₁ ≃* PSimple p I) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut (K ⧸ Subgroup.center K) inferInstance hnab name ⟨f⟩
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm
  obtain ⟨hJ', ⟨eJ⟩⟩ := center_transfer hp x hJ₁
  have hβp : centerQuotientHom K x ^ p = 1 := by rw [← map_pow, hxp, map_one]
  obtain ⟨s, hs, hsp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen
    hout (centerQuotientHom K x) hβp
  have hs1 : s ≠ 1 := by
    rintro rfl
    haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
    apply hx1
    apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
    rw [← hs]
    simp only [map_one]
  have hso : orderOf s = p := orderOf_eq_prime hsp hs1
  rw [← hs, CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at hJ'
  exact ⟨s, hso, _, hJ', ⟨eJ⟩⟩

theorem fpf_cases {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : Bool} {n : ℕ} (hn : 1 ≤ n) (hn6 : n ≤ 6)
    (hF : p ∣ typeSign ε n) :
    (ε = false ∧ n = 2 ∧ p = 5) ∨ (ε = true ∧ n = 3 ∧ p = 7) ∨ (ε = true ∧ n = 4 ∧ p = 5) ∨
      (ε = false ∧ n = 4 ∧ p = 17) ∨ (ε = true ∧ n = 5 ∧ p = 31) ∨ (ε = false ∧ n = 5 ∧ p = 11) ∨
      (ε = true ∧ n = 6 ∧ p = 7) ∨ (ε = false ∧ n = 6 ∧ p = 5) ∨ (ε = false ∧ n = 6 ∧ p = 13) := by
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  have h5 : 5 ∣ p → p = 5 := fun h => ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 h).symm
  interval_cases n <;> cases ε <;> norm_num [typeSign] at hF <;>
    first
    | omega
    | (have hle := Nat.le_of_dvd (by norm_num) hF
       interval_cases p <;> first | omega | (norm_num at hp; done) | simp)

theorem spor_omega_cases {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hF : p ∣ typeSign ε n) (name : TauCeti.SporadicName)
    (h : p * OmegaFacts.omegaOrd ε (n + 1) ∣ sporOrd name) :
    (name, ε, n, p) ∈ sporOmegaCases ∨ (name = .Fi22 ∧ ε = false ∧ n = 2 ∧ p = 5) := by
  have h2 : 2 ^ ((n + 1) * n) ∣ sporOrd name := by
    refine Dvd.dvd.trans ?_ ((dvd_mul_left _ p).trans h)
    unfold OmegaFacts.omegaOrd
    rw [Nat.add_sub_cancel]
    exact (dvd_mul_right _ _).mul_right _
  have h47 : ¬ 2 ^ 47 ∣ sporOrd name := by cases name <;> decide +kernel
  have hn6 : n ≤ 6 := by
    by_contra hc
    have h7 : 7 ≤ n := by omega
    have h56 : 47 ≤ (n + 1) * n := by nlinarith
    exact h47 ((Nat.pow_dvd_pow 2 h56).trans h2)
  rcases fpf_cases hp hp5 hn hn6 hF with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ <;>
    revert h <;> cases name <;> decide +kernel

end SporOrder

section Fi22

theorem sporNoOmegaDown_Fi22 : SporNoOmegaDown 5 false 2 .Fi22 := by
  intro T _ _ hT s hs I hI hΩ
  obtain ⟨eL⟩ := SporFacts.input14_21_holds T hT s hs
  have hIL : I ≤ GLAPLayer 5 (Subgroup.centralizer ({s} : Set T)) := le_sSup hI
  have hL : Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({s} : Set T))) = 60 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hI60 : Nat.card I ∣ 60 := by
    rw [← hL]
    exact Subgroup.card_dvd_of_le hIL
  have hcard : Nat.card (PSimple 5 I) = 25920 := by
    obtain ⟨e⟩ := hΩ
    rw [Nat.card_congr e.toEquiv]
    exact (OmegaFacts.card_statedOmega_quadMinus_of_two_le (k := 2) le_rfl).trans
      OmegaFacts.omegaOrd_three_minus
  have hdvd : Nat.card (PSimple 5 I) ∣ Nat.card I :=
    (Subgroup.card_quotient_dvd_card (Subgroup.center (PQuot 5 I))).trans
      (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 5 ↥I))
  rw [hcard] at hdvd
  have h := Nat.le_of_dvd (by norm_num) (hdvd.trans hI60)
  omega

end Fi22

section FiveCent

theorem sporNoU42Down_of_card {name : TauCeti.SporadicName} {M : Type} [Group M] [Finite M]
    (hM : Nonempty (M ≃* (TauCeti.CFSGIndex.sporadic name).Group))
    (h : ∀ y : M, orderOf y = 5 → Nat.card (Subgroup.centralizer ({y} : Set M)) < 129600) :
    SporNoOmegaDown 5 false 2 name := by
  intro T _ _ hT s hs I hI hΩ
  obtain ⟨f⟩ := hT
  obtain ⟨g⟩ := hM
  let e : T ≃* M := f.trans g.symm
  have hcard : Nat.card (PSimple 5 I) = 25920 := by
    obtain ⟨e'⟩ := hΩ
    rw [Nat.card_congr e'.toEquiv]
    exact (OmegaFacts.card_statedOmega_quadMinus_of_two_le (k := 2) le_rfl).trans
      OmegaFacts.omegaOrd_three_minus
  have h1 := mul_card_pSimple_dvd Nat.prime_five hs hI
  rw [hcard] at h1
  have hC : Nat.card (Subgroup.centralizer ({s} : Set T)) =
      Nat.card (Subgroup.centralizer ({e s} : Set M)) := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv e s,
      Subgroup.card_map_of_injective e.injective]
  have h2 := h (e s) (by rw [MulEquiv.orderOf_eq, hs])
  have h3 := Nat.le_of_dvd Nat.card_pos h1
  omega

theorem card_centralizer_le_of_lines {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P Q R : Subgroup G} (hQP : Q ≤ P) (hPR : P ≤ R)
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*} (line : ι → G)
    (hlines : ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j))
    {N : ℕ} (hline : ∀ j, Nat.card ↥(Subgroup.centralizer ({line j} : Set G) ⊓ R) ≤ N) :
    ∀ y ∈ P, orderOf y = p → Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ P) ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro y hyP hyo
  obtain ⟨g, hgP, hgQ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQP hQ hyP hyo
  set t := g⁻¹ * y * g with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj g⁻¹ : G ≃* G).orderOf_eq y
    simpa [MulAut.conj_apply, htdef, hyo] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have hy : y = g * t * g⁻¹ := by rw [htdef]; group
  have hg1 : ∀ q ∈ P, g * q * g⁻¹ ∈ P := fun q hq => P.mul_mem (P.mul_mem hgP hq) (P.inv_mem hgP)
  have hg2 : ∀ q ∈ P, g⁻¹ * q * g ∈ P := fun q hq => by
    simpa using P.mul_mem (P.mul_mem (P.inv_mem hgP) hq) hgP
  calc Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ P)
      = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ P) := by
        rw [hy, ← CFSG.HardMathSupport.Solomon.Coordinator.map_conj_centralizer_inf hg1 hg2 t,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
    _ ≤ Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ R) :=
        Subgroup.card_le_of_le (inf_le_inf_left _ hPR)
    _ = Nat.card ↥(Subgroup.centralizer ({line j} : Set G) ⊓ R) := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers hj]
    _ ≤ N := hline j

theorem card_centralizer_conj_inf {G : Type*} [Group G] [Finite G] {R : Subgroup G} {h : G}
    (hh : h ∈ R) (x : G) :
    Nat.card ↥(Subgroup.centralizer ({h * x * h⁻¹} : Set G) ⊓ R) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ R) := by
  have h1 : ∀ q ∈ R, h * q * h⁻¹ ∈ R := fun q hq => R.mul_mem (R.mul_mem hh hq) (R.inv_mem hh)
  have h2 : ∀ q ∈ R, h⁻¹ * q * h ∈ R := fun q hq => by
    simpa using R.mul_mem (R.mul_mem (R.inv_mem hh) hq) hh
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_conj_centralizer_inf h1 h2 x,
    Subgroup.card_map_of_injective (MulAut.conj h).injective]

theorem card_centralizer_subtype_lt {G : Type*} [Group G] [Finite G] {P : Subgroup G} {N : ℕ}
    (h : ∀ y ∈ P, orderOf y = 5 → Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ P) ≤ N)
    (hN : N < 129600) :
    ∀ y : ↥P, orderOf y = 5 → Nat.card (Subgroup.centralizer ({y} : Set ↥P)) < 129600 := by
  intro y hy
  have h1 := h y y.2 (by rw [Subgroup.orderOf_coe]; exact hy)
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype P y,
    Subgroup.card_map_of_injective P.subtype_injective] at h1
  omega

end FiveCent

section FiveCo3

open CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3

theorem card_centralizer_co3P_le :
    ∀ y ∈ co3P, orderOf y = 5 →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) ≤ 1500 := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec0, hrec25, hC0, hC0card, -, -, -, -, -, hC25,
    hC25card, -⟩ := R3E_Co3_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine card_centralizer_le_of_lines Nat.prime_five hQP le_rfl
    (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) co3FiveLine
    (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines) fun j => ?_
  obtain ⟨hjP, hjconj⟩ := htrans j
  rw [← hjconj, card_centralizer_conj_inf hjP]
  by_cases h : (j : ℕ) = 25
  · rw [(hrec25 j).2 h, ← hC25]
    exact hC25card.le
  · rw [(hrec0 j).2 h, ← hC0]
    exact hC0card.le.trans (by norm_num)

theorem sporNoOmegaDown_Co3 (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporNoOmegaDown 5 false 2 .Co3 :=
  sporNoU42Down_of_card ⟨co3PermEquiv.symm.trans (hbr .Co3).some⟩
    (card_centralizer_subtype_lt card_centralizer_co3P_le (by norm_num))

end FiveCo3

section FiveCo2

open CFSG.RankThree.Native CFSG.Sporadic.Co2Cert

theorem card_centralizer_co2P_le :
    ∀ y ∈ co2P, orderOf y = 5 →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) ≤ 3000 := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, -, hC0, hC0card, -, -, -, -, -, -, hC1, hC1card,
    -⟩ := R3E_Co2_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine card_centralizer_le_of_lines Nat.prime_five hQP le_rfl
    (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) co2FiveLine
    (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines) fun j => ?_
  obtain ⟨hjP, hjconj⟩ := htrans j
  rw [← hjconj, card_centralizer_conj_inf hjP]
  have hr : co2FiveRepLine (co2FiveRecordOf j) = 0 ∨ co2FiveRepLine (co2FiveRecordOf j) = 1 := by
    unfold co2FiveRecordOf
    split
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  rcases hr with hr | hr
  · rw [hr, ← hC0]
    exact hC0card.le
  · rw [hr, ← hC1]
    exact hC1card.le.trans (by norm_num)

theorem sporNoOmegaDown_Co2 (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporNoOmegaDown 5 false 2 .Co2 :=
  sporNoU42Down_of_card ⟨co2PermEquiv.symm.trans (hbr .Co2).some⟩
    (card_centralizer_subtype_lt card_centralizer_co2P_le (by norm_num))

end FiveCo2

section FiveMcL

open CFSG.RankThree.Native

theorem card_centralizer_mcl275P_le :
    ∀ y ∈ mcl275P, orderOf y = 5 →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 275))) ⊓ mcl275P) ≤ 1500 := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0card⟩, ⟨hC1, hC1card⟩, -⟩ :=
    R3E_McL_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPR : mcl275P ≤ mcl275R :=
    Subgroup.closure_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  refine card_centralizer_le_of_lines Nat.prime_five hQP hPR
    (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) mcl275FiveLine
    (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines) fun j => ?_
  obtain ⟨hjR, hjconj⟩ := htrans j
  rw [← hjconj, card_centralizer_conj_inf hjR]
  have hr : mcl275FiveRecordOf j = 0 ∨ mcl275FiveRecordOf j = 1 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hr with hr | hr
  · rw [hr, ← hC0]
    exact hC0card.le.trans (by norm_num)
  · rw [hr, ← hC1]
    exact hC1card.le

theorem sporNoOmegaDown_McL (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporNoOmegaDown 5 false 2 .McL :=
  sporNoU42Down_of_card ⟨mcl275Equiv.symm.trans (hbr .McL).some⟩
    (card_centralizer_subtype_lt card_centralizer_mcl275P_le (by norm_num))

end FiveMcL

section FiveSuz

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore

theorem card_centralizer_suzM_le :
    ∀ y ∈ suzM, orderOf y = 5 →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) ≤ 3600 := by
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlines, -⟩, hrec, hgood, hbad⟩ :=
    R3E_Suz_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine card_centralizer_le_of_lines Nat.prime_five hQP suzM_le_suzT
    (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) suzFiveLine
    (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines) fun i => ?_
  rw [← (hrec i).1]
  by_cases hg : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
  · exact (hgood i hg).1.le
  · have hb : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
      have := i.2
      omega
    exact (hbad i hb).1.le.trans (by norm_num)

theorem sporNoOmegaDown_Suz (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporNoOmegaDown 5 false 2 .Suz :=
  sporNoU42Down_of_card ⟨suzEquivM.symm.trans (hbr .Suz).some⟩
    (card_centralizer_subtype_lt card_centralizer_suzM_le (by norm_num))

end FiveSuz

section OpenTable

@[expose] def sporOmegaCasesOpen : List (TauCeti.SporadicName × Bool × ℕ × ℕ) :=
  [(.HN, false, 2, 5), (.Ly, false, 2, 5), (.Th, false, 2, 5), (.Fi23, false, 2, 5),
    (.Co1, false, 2, 5), (.Fi24Prime, false, 2, 5), (.B, false, 2, 5), (.M, false, 2, 5),
    (.Th, true, 3, 7), (.Co1, true, 3, 7), (.Fi24Prime, true, 3, 7), (.B, true, 3, 7),
    (.M, true, 3, 7), (.B, true, 4, 5), (.M, true, 4, 5), (.M, false, 5, 11)]

@[expose] def SporOmegaTableOpen : Prop :=
  ∀ (name : TauCeti.SporadicName) (ε : Bool) (n p : ℕ), (name, ε, n, p) ∈ sporOmegaCasesOpen →
    SporNoOmegaDown p ε n name

theorem sporOmegaCases_split : ∀ c ∈ sporOmegaCases, c ∈ sporOmegaCasesOpen ∨
    (c.1 ∈ [TauCeti.SporadicName.McL, .Suz, .Co3, .Co2] ∧ c.2 = (false, 2, 5)) := by
  decide +kernel

end OpenTable

section Main

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem ringChar_eq_three {X : Type} [Group X] (hC3 : IsLieChar (· = 3) X) {Q : ℕ} {F : Type}
    [Field F] [Finite F] (hFQ : Nat.card F = Q ^ 2)
    (e : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSU 5 Q F)) :
    ∃ g : ℕ, 1 ≤ g ∧ Q = 3 ^ g := by
  obtain ⟨g, hg, hQg, hℓ⟩ := exists_pow_of_natCard_sq hFQ
  subst hQg
  refine ⟨g, hg, ?_⟩
  have hX : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 5 (ringChar F) g := by
    refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ?_⟩
    exact ⟨⟨hℓ, hg, by norm_num, fun hc => by have := (Prod.mk.inj hc).1; omega⟩, F,
      inferInstance, inferInstance, hFQ, ⟨e⟩⟩
  obtain ⟨d, ⟨e3⟩, hd3⟩ := hC3
  obtain ⟨-, -, t', n', f', hY⟩ := CrossCharOdd.lie_cases (q := 3) ⟨.lie d, hd3, ⟨e3⟩⟩
  have hℓ3 : ringChar F = 3 := by
    by_cases hℓ2 : ringChar F = 2
    · exfalso
      have hodd : CFSG.Blueprint.OddLieType (X ⧸ Subgroup.center X) :=
        ⟨t', n', 3, f', Nat.prime_three, by norm_num, hY.admissible, hY⟩
      rw [hℓ2] at hX
      rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
          CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hX hodd with
        ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩
      · exact absurd h1 (by decide)
      · exact absurd h1 (by decide)
      · omega
    · exact CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds _ _ _ _ _ _ _ _ _ hℓ2
        (by norm_num) hX hY
  rw [hℓ3]

theorem inputU42Lin5_holds : Inputs1419.InputU42Lin5 := by
  intro K _ _ hK hO hC3 J _ hJ x hx hQ
  obtain ⟨Q, hQ⟩ := hQ
  obtain ⟨hxo, J1, hJ1, ⟨eJ⟩⟩ := hx
  haveI : Finite J := Finite.of_equiv _ eJ.toEquiv
  have hZJ : Subgroup.center J = ⊥ := Inputs1419.center_eq_bot_of_isOmegaTwo (n := 2) le_rfl hJ
  have hJcard : Nat.card J = 25920 := by
    obtain ⟨e⟩ := hJ
    rw [Nat.card_congr e.toEquiv]
    exact (OmegaFacts.card_statedOmega_quadMinus_of_two_le (k := 2) le_rfl).trans
      OmegaFacts.omegaOrd_three_minus
  have hJ1' : GLAPComponent 5 (fixSubgroup x) J1 := by
    rw [show fixSubgroup x = Lemma1314.fixSub x from Subgroup.ext fun _ => Iff.rfl]
    exact hJ1
  obtain ⟨hA, ⟨eA⟩⟩ := center_transfer Nat.prime_five x hJ1'
  have hβ5 : centerQuotientHom K x ^ 5 = 1 := by
    rw [← map_pow, ← hxo, pow_orderOf_eq_one, map_one]
  have hcardA : Nat.card (PSimple 5 (J1.map (QuotientGroup.mk' (Subgroup.center K)))) = 25920 := by
    rw [← Nat.card_congr eA.toEquiv]
    have e1 : PSimple 5 J1 ≃* J :=
      (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).trans
        (Inputs1419.quotCenterEquivOfBot hZJ)
    rw [Nat.card_congr e1.toEquiv, hJcard]
  rcases hQ with ⟨⟨F, _, _, hFQ, ⟨e⟩⟩, h5⟩ | ⟨⟨F, _, _, hFQ, ⟨e⟩⟩, h5⟩
  ·
    let e' : (K ⧸ Subgroup.center K) ≃* LinearFlag.projectiveSL 5 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
    obtain ⟨hA', hcard'⟩ := comp_congr Nat.prime_five e' hA
    exact false_of_psl_five (by rw [hFQ]; exact h5) _ (by rw [← map_pow, hβ5, map_one]) hA'
      (hcard'.trans hcardA)
  ·
    obtain ⟨g, hg, rfl⟩ := ringChar_eq_three hC3 hFQ e
    have hUF : UnitaryFieldData 3 g F := ⟨Nat.prime_three, hg, by rw [hFQ, ← pow_mul, mul_comm]⟩
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv hUF (isPrimeFormGram_idGram (n := 5) (K := F))
    let e' : (K ⧸ Subgroup.center K) ≃* primeFormP hUF (idGram F 5) :=
      (e.trans (unitaryPSUEquiv hUF (by norm_num)).symm).trans eP.symm
    obtain ⟨hA', hcard'⟩ := comp_congr Nat.prime_five e' hA
    exact false_of_psu_five hUF _ (by rw [← map_pow, hβ5, map_one]) hA' (hcard'.trans hcardA)

end Main

section MainAll

theorem input14_19_3c_holds : Claims1314.Input14_19_3c :=
  Inputs1419.input14_19_3c_of_u42 inputU42Lin5_holds

end MainAll

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1419b

end
