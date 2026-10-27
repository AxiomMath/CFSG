module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.CharacterTheory.Semidihedral.OddProjectiveCoverKernel
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7RkA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open scoped commutatorElement

private theorem hom_eq_one_of_commute {X H : Type*} [Group X] [Group H] (hperf : commutator X = ⊤)
    (f : X →* H) (hf : ∀ x y : X, f x * f y = f y * f x) : f = 1 := by
  have h : commutator X ≤ f.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf x y
  rw [hperf] at h
  exact MonoidHom.ext fun x => MonoidHom.mem_ker.mp (h (Subgroup.mem_top x))

private theorem mul_le_card_of_lt {q : ℕ} (hq : q.Prime) {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup q G) {A B : Subgroup G} (hAB : A ≤ B) (hne : A ≠ B) :
    q * Nat.card A ≤ Nat.card B := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := (hG.to_subgroup A).exists_card_eq
  obtain ⟨b, hb⟩ := (hG.to_subgroup B).exists_card_eq
  have hlt : Nat.card A < Nat.card B := by
    rcases (Subgroup.card_le_of_le hAB).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hAB h.ge) hne
  rw [ha, hb] at hlt ⊢
  have hab : a < b := (Nat.pow_lt_pow_iff_right hq.one_lt).mp hlt
  calc q * q ^ a = q ^ (a + 1) := by ring
    _ ≤ q ^ b := Nat.pow_le_pow_right hq.pos hab

private theorem center_quotient_card_le {q : ℕ} (hq : q.Prime) {G : Type*} [Group G] [Finite G]
    (hexp : ∀ x : G, x ^ q = 1) (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hab : ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ q ^ 2) :
    Nat.card (Subgroup.center G) ≤ q ^ 2 ∧ Nat.card (G ⧸ Subgroup.center G) ≤ q ^ 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q G := fun g => ⟨1, by simpa using hexp g⟩
  refine ⟨hab _ inferInstance, ?_⟩
  show (Subgroup.center G).index ≤ q ^ 2
  by_cases hZ : Subgroup.center G = ⊤
  · rw [hZ, Subgroup.index_top]
    exact Nat.one_le_pow _ _ hq.pos
  obtain ⟨x, hx⟩ : ∃ x : G, x ∉ Subgroup.center G := by
    by_contra h
    push Not at h
    exact hZ ((Subgroup.eq_top_iff' _).mpr h)
  have hxc : ∀ z ∈ Subgroup.center G, Commute x z := fun z hz =>
    (Subgroup.mem_center_iff.mp hz x)
  have hnt : Nontrivial G := ⟨⟨x, 1, fun h => hx (h ▸ Subgroup.one_mem _)⟩⟩
  have hZne : Subgroup.center G ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hG.center_nontrivial
  have hZq : q ≤ Nat.card (Subgroup.center G) := by
    have := mul_le_card_of_lt hq hG (bot_le : (⊥ : Subgroup G) ≤ Subgroup.center G) hZne.symm
    simpa using this
  set B1 : Subgroup G := Subgroup.closure (insert x (Subgroup.center G : Set G)) with hB1
  have hB1comm : IsMulCommutative B1 := by
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb _
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact Commute.refl _
      · exact hxc b hb
    · rcases hb with rfl | hb
      · exact (hxc a ha).symm
      · exact (Subgroup.mem_center_iff.mp hb a)
  have hZB1 : Subgroup.center G ≤ B1 := fun z hz =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hz)
  have hxB1 : x ∈ B1 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB1ne : Subgroup.center G ≠ B1 := fun h => hx (h ▸ hxB1)
  have h3B1 := mul_le_card_of_lt hq hG hZB1 hB1ne
  have hB1card := hab B1 hB1comm
  have hB1ge : q ^ 2 ≤ Nat.card B1 :=
    calc q ^ 2 = q * q := sq q
      _ ≤ q * Nat.card (Subgroup.center G) := Nat.mul_le_mul_left q hZq
      _ ≤ Nat.card B1 := h3B1
  have hCle : Subgroup.centralizer ({x} : Set G) ≤ B1 := by
    intro y hy
    by_contra hyB1
    set B2 : Subgroup G := Subgroup.closure (insert y (insert x (Subgroup.center G : Set G)))
      with hB2
    have hyx : Commute y x := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hB2comm : IsMulCommutative B2 := by
      apply Subgroup.isMulCommutative_closure
      intro a ha b hb _
      have hz : ∀ c ∈ insert x (Subgroup.center G : Set G), Commute y c := by
        intro c hc
        rcases hc with rfl | hc
        · exact hyx
        · exact (Subgroup.mem_center_iff.mp hc y)
      have hz' : ∀ c ∈ insert x (Subgroup.center G : Set G), ∀ d ∈ insert x
          (Subgroup.center G : Set G), Commute c d := by
        intro c hc d hd
        rcases hc with rfl | hc
        · rcases hd with rfl | hd
          · exact Commute.refl _
          · exact hxc d hd
        · rcases hd with rfl | hd
          · exact (hxc c hc).symm
          · exact (Subgroup.mem_center_iff.mp hd c)
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact Commute.refl _
        · exact hz b hb
      · rcases hb with rfl | hb
        · exact (hz a ha).symm
        · exact hz' a ha b hb
    have hB12 : B1 ≤ B2 := Subgroup.closure_mono (Set.subset_insert _ _)
    have hyB2 : y ∈ B2 := Subgroup.subset_closure (Set.mem_insert _ _)
    have hne : B1 ≠ B2 := fun h => hyB1 (h ▸ hyB2)
    have h3 := mul_le_card_of_lt hq hG hB12 hne
    have h4 := hab B2 hB2comm
    have hpos : 0 < Nat.card B1 := Nat.card_pos
    have h2 : 2 * Nat.card B1 ≤ q * Nat.card B1 := Nat.mul_le_mul_right _ hq.two_le
    omega
  have hCq : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ q ^ 2 :=
    (Subgroup.card_le_of_le hCle).trans hB1card
  have hidx := CFSG.HardMathSupport.Solomon.Coordinator.i227rk_index_centralizer_le hcomm x
  have hGC := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  have hGZ := Subgroup.card_mul_index (Subgroup.center G)
  have hpos : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  have hle : Nat.card (Subgroup.center G) * (Subgroup.center G).index ≤
      Nat.card (Subgroup.center G) * q ^ 2 := by
    rw [hGZ, ← hGC]
    calc Nat.card (Subgroup.centralizer ({x} : Set G)) *
          (Subgroup.centralizer ({x} : Set G)).index
        ≤ q ^ 2 * Nat.card (Subgroup.center G) := Nat.mul_le_mul hCq hidx
      _ = Nat.card (Subgroup.center G) * q ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_left hle hpos

private theorem isCyclic_of_isPGroup_of_injective {H : Type*} [Group H] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (f : H →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (hf : Function.Injective f)
    (P : Subgroup H) (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨R, hR⟩ := (hP.map f).exists_le_sylow
  have hRc : IsCyclic (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod q))) :=
    CFSG.Semidihedral.OddProjectiveCoverKernel.nativeSL_odd_sylow_cyclic (ZMod q) Fact.out
      (by rw [ZMod.ringChar_zmod_n]; exact hq2) (by rw [Nat.card_zmod, pow_one]) Fact.out hp2
      hqp.symm R
  have : IsCyclic (P.map f) := Subgroup.isCyclic_of_le hR
  exact isCyclic_of_injective (Subgroup.equivMapOfInjective P f hf).toMonoidHom
    (Subgroup.equivMapOfInjective P f hf).injective

private theorem card_le_of_isElemAbelian_of_surjective {H Q : Type*} [Group H] [Finite H]
    [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ P : Subgroup H, IsPGroup p P → IsCyclic P) (ψ : H →* Q)
    (hψ : Function.Surjective ψ) (E : Subgroup Q) (hE : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p := by
  have hpow : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (hE.2 x x.2)
  obtain ⟨S, hES⟩ := (show IsPGroup p E from fun g => ⟨1, by simpa using hpow g⟩).exists_le_sylow
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hψ p S
  have hPc : IsCyclic (P : Subgroup H) := hcyc _ P.isPGroup'
  have hSc : IsCyclic ((P.mapSurjective hψ : Sylow p Q) : Subgroup Q) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (ψ.subgroupMap _) (ψ.subgroupMap_surjective _)
  have : IsCyclic E := Subgroup.isCyclic_of_le hES
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos (Monoid.exponent_dvd_of_forall_pow_eq_one hpow)

theorem sl2_hom_eq_one {X : Type*} [Group X] [Finite X] {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (M : Subgroup X) [M.Normal]
    (hM : ∀ N : Subgroup X, N.Normal → N ≠ ⊤ → N ≤ M)
    (hrk : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ M)))
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : φ = 1 := by
  by_contra hφ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hker : φ.ker ≠ ⊤ := fun h =>
    hφ (MonoidHom.ext fun x => MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  have hkM : φ.ker ≤ M := hM φ.ker inferInstance hker
  let ψ : X ⧸ φ.ker →* X ⧸ M :=
    QuotientGroup.lift φ.ker (QuotientGroup.mk' M)
      fun x hx => (QuotientGroup.eq_one_iff x).mpr (hkM hx)
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(x : X ⧸ φ.ker), rfl⟩
  have hcyc : ∀ P : Subgroup (X ⧸ φ.ker), IsPGroup p P → IsCyclic P :=
    isCyclic_of_isPGroup_of_injective hp2 hq2 hqp (QuotientGroup.kerLift φ)
      (QuotientGroup.kerLift_injective φ)
  have hle : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ M)) ≤ 1 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => by
      rw [pow_one]
      exact card_le_of_isElemAbelian_of_surjective hcyc ψ hψ E hE
  omega

private theorem gl_hom_eq_one {X : Type*} [Group X] {q : ℕ} (hperf : commutator X = ⊤)
    (hSL : ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1) {n : ℕ} (hn : n ≤ 2)
    (f : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod q)) : f = 1 := by
  interval_cases n
  · exact MonoidHom.ext fun x => Units.ext (Matrix.ext fun i _ => i.elim0)
  · exact hom_eq_one_of_commute hperf f fun x y => CFSG.SectionRank.Ccomm.GL_one_comm _ _
  · have hdet : ∀ x : X, (f x : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := fun x => by
      have h := hom_eq_one_of_commute hperf (Matrix.GeneralLinearGroup.det.comp f)
        fun x y => mul_comm _ _
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using
        congrArg (fun g : X →* (ZMod q)ˣ => ((g x : (ZMod q)ˣ) : ZMod q)) h
    let φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
      { toFun := fun x => ⟨(f x : Matrix (Fin 2) (Fin 2) (ZMod q)), hdet x⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp; rfl) }
    exact MonoidHom.ext fun x => Units.ext (congrArg
      (fun g : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) =>
        ((g x : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)))
      (hSL φ))

theorem mulAut_hom_eq_one_of_card_le {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hperf : commutator X = ⊤)
    (hSL : ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1)
    {A : Type*} [Group A] [Finite A] (hexp : ∀ a : A, a ^ q = 1)
    (hcomm : ∀ a b : A, a * b = b * a) (hcard : Nat.card A ≤ q ^ 2) (ψ : X →* MulAut A) :
    ψ = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := (show IsPGroup q A from fun a => ⟨1, by simpa using hexp a⟩).exists_card_eq
  have hn2 : n ≤ 2 := by
    rw [hn] at hcard
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp hcard
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := q) hcomm hexp hn
  have h := gl_hom_eq_one hperf hSL hn2
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ψ)
  exact MonoidHom.ext fun x => (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
    (by simpa using DFunLike.congr_fun h x)

theorem centralizes_of_rank_le_two {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hperf : commutator X = ⊤)
    (hSL : ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1)
    (V : Subgroup X) [V.Normal] (hV : IsPGroup q V)
    (hr : ∀ E : Subgroup X, E ≤ V → CFSG.Open.IsElemAbelian q E → Nat.card E ≤ q ^ 2) :
    ∀ k : X, ∀ v ∈ V, k * v = v * k := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hVb : V = ⊥
  · intro k v hv
    rw [hVb, Subgroup.mem_bot] at hv
    subst hv
    simp
  have hnt : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVb
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hV
  haveI := hDchar
  let φ : X →* MulAut V := MulAut.conjNormal
  obtain ⟨ρ, hρ⟩ : ∃ ρ : X →* MulAut D, ∀ (k : X) (d : D), ((ρ k d : D) : V) = φ k d :=
    ⟨(CFSG.FiveTransitive.CharacteristicAutomorphism.restrict D).comp φ, fun _ _ => rfl⟩
  have hDexp' : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hDexp x x.2)
  have hDcomm' : ∀ x y : D, ⁅x, y⁆ ∈ Subgroup.center D := by
    intro x y
    rw [Subgroup.mem_center_iff]
    intro g
    have hmem := hDcomm (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top y.1))
    have hg := (Subgroup.mem_centralizer_iff.mp hmem.2) g.1 g.2
    apply Subtype.ext
    simpa [commutatorElement_def] using hg
  have hDab : ∀ B : Subgroup D, IsMulCommutative B → Nat.card B ≤ q ^ 2 := by
    intro B hB
    let f : D →* X := V.subtype.comp D.subtype
    have hf : Function.Injective f := V.subtype_injective.comp D.subtype_injective
    have hE : CFSG.Open.IsElemAbelian q (B.map f) :=
      CFSG.SectionRank.isElemAbelian_map ⟨hB, fun x _ => hDexp' x⟩ f
    have hle : B.map f ≤ V := by
      rintro _ ⟨a, -, rfl⟩
      exact (a : V).2
    have := hr _ hle hE
    rwa [← Nat.card_congr (Subgroup.equivMapOfInjective B f hf).toEquiv] at this
  obtain ⟨hZcard, hQcard⟩ := center_quotient_card_le hq hDexp' hDcomm' hDab
  have hZfix : ∀ (k : X) (z : D), z ∈ Subgroup.center D → ρ k z = z := by
    intro k z hz
    have h := mulAut_hom_eq_one_of_card_le hq hperf hSL (A := Subgroup.center D)
      (fun a => Subtype.ext (by simpa using hDexp' a.1))
      (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp a.2 b.1).symm) hZcard
      ((CFSG.FiveTransitive.CharacteristicAutomorphism.restrict (Subgroup.center D)).comp ρ)
    simpa using congrArg
      (fun f : X →* MulAut (Subgroup.center D) => ((f k ⟨z, hz⟩ : Subgroup.center D) : D)) h
  have hQfix : ∀ (k : X) (d : D), d⁻¹ * ρ k d ∈ Subgroup.center D := by
    intro k d
    have hexp : ∀ a : D ⧸ Subgroup.center D, a ^ q = 1 := fun a => by
      induction a using QuotientGroup.induction_on with
      | H d => rw [← QuotientGroup.mk_pow, hDexp' d, QuotientGroup.mk_one]
    have hcomm : ∀ a b : D ⧸ Subgroup.center D, a * b = b * a := fun a b => by
      induction a using QuotientGroup.induction_on with
      | H d₁ =>
        induction b using QuotientGroup.induction_on with
        | H d₂ =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          simpa [commutatorElement_def, mul_assoc] using hDcomm' d₂⁻¹ d₁⁻¹
    have h := mulAut_hom_eq_one_of_card_le hq hperf hSL (A := D ⧸ Subgroup.center D) hexp hcomm
      hQcard ((CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center D)).comp ρ)
    have h2 := congrArg (fun f : X →* MulAut (D ⧸ Subgroup.center D) =>
      f k (QuotientGroup.mk' (Subgroup.center D) d)) h
    simp only [MonoidHom.comp_apply,
      CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk, MonoidHom.one_apply,
      MulAut.one_apply] at h2
    exact QuotientGroup.eq.mp h2.symm
  have hρ1 : ρ = 1 := by
    refine hom_eq_one_of_commute hperf ρ fun x y => MulEquiv.ext fun d => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply]
    obtain ⟨a, haZ, ha⟩ : ∃ a ∈ Subgroup.center D, ρ x d = d * a :=
      ⟨d⁻¹ * ρ x d, hQfix x d, by group⟩
    obtain ⟨b, hbZ, hb⟩ : ∃ b ∈ Subgroup.center D, ρ y d = d * b :=
      ⟨d⁻¹ * ρ y d, hQfix y d, by group⟩
    rw [hb, map_mul, hZfix x b hbZ, ha, map_mul, hZfix y a haZ, hb, mul_assoc, mul_assoc,
      Subgroup.mem_center_iff.mp haZ b]
  have hfix : ∀ k : X, φ k ∈ fixingSubgroup (MulAut V) (D : Set V) := by
    intro k
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have := hρ k ⟨y, hy⟩
    simpa [hρ1] using this.symm
  let ψ : X →* fixingSubgroup (MulAut V) (D : Set V) := φ.codRestrict _ hfix
  have : Finite (fixingSubgroup (MulAut V) (D : Set V)) := inferInstance
  have hnil : Group.IsNilpotent (fixingSubgroup (MulAut V) (D : Set V)) := hDfix.isNilpotent
  have hψ : ∀ k : X, ψ k = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.i227rk_hom_eq_one_of_solvable hperf ψ
  intro k v hv
  have h1 : φ k = 1 := congrArg Subtype.val (hψ k)
  have h2 := congrArg (fun a : MulAut V => ((a ⟨v, hv⟩ : V) : X)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc k * v = k * v * k⁻¹ * k := by group
    _ = v * k := by rw [h2]

end CFSG.LocalAnalysis.GLTheoremA.H248L227
