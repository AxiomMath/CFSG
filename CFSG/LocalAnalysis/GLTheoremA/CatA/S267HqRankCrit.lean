module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Reduce
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.LocalAnalysis.GLTheoremA.S9.I314

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem not_dvd_card_GL_of_prime {F : Type} [Group F] {q s k : ℕ} (hq : q.Prime) (hs : s.Prime)
    (hsq : s ≠ q) (hsF : s ∣ Nat.card F) (hord : ∀ i, 1 ≤ i → i ≤ k → ¬ s ∣ q ^ i - 1) :
    ∀ m, m ≤ k → ¬ Nat.card F ∣ Nat.card (GL (Fin m) (ZMod q)) := by
  intro m hm hdvd
  have : Fact q.Prime := ⟨hq⟩
  have h1 : s ∣ ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by
    rw [← CFSG.SectionRank.Ccomm.card_GL_zmod]
    exact hsF.trans hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hs.prime _).1 h1
  have hi2 := i.2
  have hsplit : q ^ m - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (m - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hi2.le]
  rw [hsplit] at hi
  rcases (Nat.Prime.dvd_mul hs).1 hi with h | h
  · exact hsq ((Nat.prime_dvd_prime_iff_eq hs hq).1 (hs.dvd_of_dvd_pow h))
  · exact hord (m - i) (by omega) (by omega) h

theorem le_ker_of_isPGroup {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {q : ℕ} (hq : q.Prime) {X : Type} [Group X] [Finite X]
    (φ : X →* F) (hφ : Function.Surjective φ) {K : Subgroup X} (hKn : K.Normal)
    (hK : IsPGroup q K) : K ≤ φ.ker := by
  have : Fact q.Prime := ⟨hq⟩
  rcases (hKn.map φ hφ).eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff K).1 h
  · exfalso
    have h1 : IsPGroup q (K.map φ) := hK.map φ
    rw [h] at h1
    have hFq : IsPGroup q F := h1.of_equiv Subgroup.topEquiv
    obtain ⟨a₀, b₀, hab₀⟩ := hnc
    have : Nontrivial F := ⟨⟨a₀, 1, fun h => hab₀ (by rw [h]; simp)⟩⟩
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hFq.center_nontrivial
      (i1021_center_eq_bot ⟨a₀, b₀, hab₀⟩)

section Action

variable {X : Type} [Group X] (R : Subgroup X) [R.Normal]

private noncomputable def abelAction : X →* MulAut (Abelianization R) where
  toFun x := (MulAut.conjNormal x).abelianizationCongr
  map_one' := by
    rw [map_one]
    exact abelianizationCongr_refl
  map_mul' x y := by
    rw [map_mul]
    exact (abelianizationCongr_trans _ _).symm

private theorem mem_commutator_of_mem_ker {x : X} (hx : x ∈ (abelAction R).ker) {d : X}
    (hd : d ∈ R) : d⁻¹ * (x * d * x⁻¹) ∈ ⁅R, R⁆ := by
  have h1 : abelAction R x (Abelianization.of ⟨d, hd⟩) = Abelianization.of ⟨d, hd⟩ := by
    rw [MonoidHom.mem_ker.1 hx]
    rfl
  change Abelianization.of (MulAut.conjNormal x ⟨d, hd⟩) = Abelianization.of ⟨d, hd⟩ at h1
  have h2 : (⟨d, hd⟩ : R)⁻¹ * MulAut.conjNormal x ⟨d, hd⟩ ∈ commutator ↥R :=
    (QuotientGroup.eq (s := commutator ↥R)).1 h1.symm
  rw [← Subgroup.map_subtype_commutator R]
  refine ⟨_, h2, ?_⟩
  simp [MulAut.conjNormal_apply]

private theorem commutatorElement_mul_mul {a b u v : X} (hub : Commute u b) (huv : Commute u v)
    (hva : Commute v a) : ⁅a * u, b * v⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ = a * (u * (b * v)) * u⁻¹ * a⁻¹ * (b * v)⁻¹ := by
        group
    _ = a * ((b * v) * u) * u⁻¹ * a⁻¹ * (b * v)⁻¹ := by rw [(hub.mul_right huv).eq]
    _ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * v) * v⁻¹ * b⁻¹ := by rw [hva.inv_right.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem conj_eq_of_mem_ker {q : ℕ} (hRexp : ∀ x ∈ R, x ^ q = 1)
    (hRZ : ⁅R, R⁆ ≤ centralizer (R : Set X)) {x : X} (hx : x ∈ (abelAction R).ker)
    (hcop : (orderOf x).Coprime q) {d : X} (hd : d ∈ R) : x * d * x⁻¹ = d := by
  have hR'R : ⁅R, R⁆ ≤ R := commutator_le_left R R
  have hxR' : ⁅R, R⁆ ≤ centralizer ({x} : Set X) := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have hca := mem_commutator_of_mem_ker R hx ha
    have hcb := mem_commutator_of_mem_ker R hx hb
    have hcomm : ∀ {w : X}, w ∈ ⁅R, R⁆ → ∀ {y : X}, y ∈ R → Commute w y := fun hw _ hy =>
      ((mem_centralizer_iff.1 (hRZ hw)) _ hy).symm
    have hconj : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      have e := map_commutatorElement (MulAut.conj x) a b
      simp only [MulAut.conj_apply] at e
      rw [e, ← mul_inv_cancel_left a (x * a * x⁻¹), ← mul_inv_cancel_left b (x * b * x⁻¹)]
      exact commutatorElement_mul_mul (hcomm hca hb) (hcomm hca (hR'R hcb)) (hcomm hcb ha)
    calc x * ⁅a, b⁆ = x * ⁅a, b⁆ * x⁻¹ * x := by group
      _ = ⁅a, b⁆ * x := by rw [hconj]
  set c := d⁻¹ * (x * d * x⁻¹) with hcdef
  have hc : c ∈ ⁅R, R⁆ := mem_commutator_of_mem_ker R hx hd
  have hxc : x * c = c * x := (mem_centralizer_iff.1 (hxR' hc)) x rfl
  have hxd : x * d = d * c * x := by rw [hcdef]; group
  have hpow : ∀ n : ℕ, x ^ n * d = d * c ^ n * x ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxcn : x * c ^ n = c ^ n * x := (Commute.pow_right (show Commute x c from hxc) n).eq
      calc x ^ (n + 1) * d = x * (x ^ n * d) := by rw [pow_succ', mul_assoc]
        _ = (x * d) * c ^ n * x ^ n := by rw [ih]; group
        _ = d * c * (x * c ^ n) * x ^ n := by rw [hxd]; group
        _ = d * c ^ (n + 1) * x ^ (n + 1) := by rw [hxcn, pow_succ', pow_succ']; group
  have hcn : c ^ orderOf x = 1 := by
    have := hpow (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hcq : c ^ q = 1 := hRexp c (hR'R hc)
  have hc1 : c = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hcn)
      (orderOf_dvd_of_pow_eq_one hcq)
  rw [hcdef, inv_mul_eq_one] at hc1
  exact hc1.symm

end Action

theorem le_pRank_caseA_crit {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hinv : ∀ m, m ≤ r ^ 2 / 4 → ¬ Nat.card F ∣ Nat.card (GL (Fin m) (ZMod q)))
    {X : Type} [Group X] [Finite X] (ψ : X →* F) (hψ : Function.Surjective ψ)
    (hY : IsPGroup q ψ.ker) (hYne : ψ.ker ≠ ⊥) (hC : centralizer (ψ.ker : Set X) ≤ ψ.ker) :
    r ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  set Y : Subgroup X := ψ.ker with hYdef
  haveI : Nontrivial ↥Y := (nontrivial_iff_ne_bot Y).2 hYne
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hY
  haveI : D.Characteristic := hDchar
  set R : Subgroup X := D.map Y.subtype with hRdef
  haveI hRn : R.Normal := ConjAct.normal_of_characteristic_of_normal
  have hRY : R ≤ Y := map_subtype_le D
  have hRexp : ∀ x ∈ R, x ^ q = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    have := congrArg Subtype.val (hDexp d hd)
    simpa using this
  have hRZ : ⁅R, R⁆ ≤ centralizer (R : Set X) := by
    rw [commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have hab : ⁅a, b⁆ ∈ centralizer (D : Set ↥Y) :=
      (hDcomm (commutator_mem_commutator ha (mem_top b))).2
    have := congrArg Subtype.val ((mem_centralizer_iff.1 hab) c hc)
    have e : ((⁅a, b⁆ : ↥Y) : X) = ⁅(a : X), (b : X)⁆ := map_commutatorElement Y.subtype a b
    simp only [coe_mul, e] at this
    exact this
  have hRcen : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, ⁅a, b⁆ * c = c * ⁅a, b⁆ := fun a ha b hb c hc =>
    ((mem_centralizer_iff.1 (hRZ (commutator_mem_commutator ha hb))) c hc).symm
  have hfix : ∀ x : X, (∀ d ∈ R, x * d * x⁻¹ = d) → (orderOf x).Coprime q → x = 1 := by
    intro x hxR hcop
    have hmem : MulAut.conjNormal (H := Y) x ∈ fixingSubgroup (MulAut ↥Y) (D : Set ↥Y) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      rw [MulAut.smul_def, MulAut.conjNormal_apply]
      exact hxR _ ⟨d, hd, rfl⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hDfix ⟨_, hmem⟩
    rw [Subgroup.orderOf_mk] at hk
    have h2 : orderOf (MulAut.conjNormal (H := Y) x) ∣ orderOf x := orderOf_map_dvd _ x
    rw [hk] at h2
    have h3 : q ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop.symm) h2
    rw [h3, orderOf_eq_one_iff] at hk
    have hxY : x ∈ Y := hC (by
      rw [mem_centralizer_iff]
      intro y hy
      have := congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : X)) hk
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group)
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hY ⟨x, hxY⟩
    rw [Subgroup.orderOf_mk] at hj
    rw [← orderOf_eq_one_iff]
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j hcop) (hj ▸ dvd_rfl)
  set K : Subgroup X := (abelAction R).ker with hKdef
  have hKq : IsPGroup q K := by
    refine CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one (p := q) fun a hcop => ?_
    obtain ⟨x, hx⟩ := a
    rw [Subgroup.orderOf_mk] at hcop
    exact Subtype.ext (hfix x (fun d hd => conj_eq_of_mem_ker R hRexp hRZ hx hcop hd) hcop)
  have hKY : K ≤ Y := le_ker_of_isPGroup hnc hq ψ hψ (MonoidHom.normal_ker _) hKq
  have hRq : IsPGroup q R := hY.to_le hRY
  have hAbq : IsPGroup q (Abelianization R) :=
    hRq.of_surjective Abelianization.of (QuotientGroup.mk_surjective (s := commutator ↥R))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hAbq
  have hpow : ∀ a : Abelianization R, a ^ q = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H d =>
      have hd : d ^ q = 1 := Subtype.ext (by simpa using hRexp d d.2)
      change Abelianization.of d ^ q = 1
      rw [← map_pow, hd, map_one]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := q)
    (W := Abelianization R) (fun a b => mul_comm a b) hpow hm
  have hdvd : Nat.card F ∣ Nat.card (GL (Fin m) (ZMod q)) := by
    rw [← CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
    have e1 : Nat.card F = Y.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv).symm
    have e2 : K.index = Nat.card (abelAction R).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (abelAction R)).toEquiv
    rw [e1]
    exact (Subgroup.index_dvd_of_le hKY).trans (e2 ▸ Subgroup.card_subgroup_dvd_card _)
  have hm4 : r ^ 2 < 4 * m := by
    by_contra h
    exact hinv m (by omega) hdvd
  have hcard : q ^ m * Nat.card ↥⁅R, R⁆ ≤ Nat.card R := by
    have h1 : Nat.card R = Nat.card (Abelianization R) * Nat.card (commutator ↥R) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥R)
    have h2 : Nat.card ↥⁅R, R⁆ = Nat.card (commutator ↥R) := by
      rw [← Subgroup.map_subtype_commutator R]
      exact Subgroup.card_map_of_injective R.subtype_injective
    rw [h1, h2, hm]
  have h314 := CFSG.LocalAnalysis.GLTheoremA.i314At_holds X q m R ⁅R, R⁆ hq hRexp hRcen le_rfl
    (commutator_le_left R R) hcard
  have hrR : r ≤ CFSG.Open.pRank q R := by
    by_contra h
    have h' : CFSG.Open.pRank q R + 1 ≤ r := by omega
    have := Nat.pow_le_pow_left h' 2
    omega
  exact hrR.trans (CFSG.SectionRank.pRank_mono hq.one_lt le_top)

private theorem le_pRank_of_surj_crit_aux {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcen : ∀ (L : Type) [Group L] [Finite L] (ψ : L →* F), Function.Surjective ψ →
      commutator L = ⊤ → ψ.ker ≤ center L → IsPGroup q ψ.ker →
        r ≤ CFSG.Open.pRank q (⊤ : Subgroup L))
    (hinv : ∀ m, m ≤ r ^ 2 / 4 → ¬ Nat.card F ∣ Nat.card (GL (Fin m) (ZMod q))) :
    ∀ (m : ℕ) (X : Type) [Group X] [Finite X], Nat.card X ≤ m → ∀ φ : X →* F,
      Function.Surjective φ → r ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a₀, b₀, hab₀⟩ := hnc
  have : Nontrivial F := ⟨⟨a₀, 1, fun h => hab₀ (by rw [h]; simp)⟩⟩
  have hF1 : ⁅(⊤ : Subgroup F), (⊤ : Subgroup F)⁆ = ⊤ := i1020_commutator_top ⟨a₀, b₀, hab₀⟩
  intro m
  induction m with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ m ih =>
    intro X _ _ hX φ hφ
    by_cases hYq : IsPGroup q φ.ker
    · by_cases hC : centralizer (φ.ker : Set X) ≤ φ.ker
      ·
        have hYne : φ.ker ≠ ⊥ := by
          intro hbot
          obtain ⟨a, ha⟩ := exists_ne (1 : F)
          obtain ⟨x, hx⟩ := hφ a
          have hx1 : x ∈ φ.ker := hC (by
            rw [hbot, mem_centralizer_iff]
            intro h hh
            rw [SetLike.mem_coe, mem_bot] at hh
            rw [hh, one_mul, mul_one])
          rw [MonoidHom.mem_ker, hx] at hx1
          exact ha hx1
        exact le_pRank_caseA_crit ⟨a₀, b₀, hab₀⟩ hq hq2 hinv φ hφ hYq hYne hC
      ·
        set C : Subgroup X := centralizer (φ.ker : Set X) with hCdef
        have hCn : C.Normal := inferInstance
        have hCmap : C.map φ = ⊤ := by
          rcases (hCn.map φ hφ).eq_bot_or_eq_top with h | h
          · exact absurd ((Subgroup.map_eq_bot_iff C).1 h) hC
          · exact h
        obtain ⟨L, ⟨hLC, hLtop⟩, hLmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X))
          {L : Subgroup X | L ≤ C ∧ L.map φ = ⊤} ⟨C, le_rfl, hCmap⟩
        have hcomm_le : ⁅L, L⁆ ≤ L := commutator_le.2 fun a ha b hb => by
          simp only [commutatorElement_def]
          exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
        have hD : ⁅L, L⁆ = L := by
          by_contra hne
          refine hLmin ⁅L, L⁆ ⟨hcomm_le.trans hLC, ?_⟩ (lt_of_le_of_ne hcomm_le hne)
          rw [map_commutator, hLtop]
          exact hF1
        have hLperf : commutator ↥L = ⊤ := (Subgroup.isPerfect_iff.2 hD).commutator_eq_top
        set ψ : ↥L →* F := φ.comp L.subtype with hψdef
        have hψ : Function.Surjective ψ := by
          intro f
          have : f ∈ L.map φ := hLtop ▸ mem_top f
          obtain ⟨l, hl, hlf⟩ := mem_map.1 this
          exact ⟨⟨l, hl⟩, hlf⟩
        have hker : ∀ l : ↥L, l ∈ ψ.ker ↔ φ (l : X) = 1 := fun l => Iff.rfl
        have hcen' : ψ.ker ≤ center ↥L := by
          intro l hl
          rw [mem_center_iff]
          intro g
          have hlY : (l : X) ∈ φ.ker := (hker l).1 hl
          have hgC : (g : X) ∈ C := hLC g.2
          have := (mem_centralizer_iff.1 hgC) (l : X) hlY
          exact Subtype.ext this.symm
        have hpg : IsPGroup q ψ.ker := by
          rw [IsPGroup.iff_orderOf]
          intro g
          have hgY : ((g : ↥L) : X) ∈ φ.ker := (hker g).1 g.2
          obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hYq ⟨_, hgY⟩
          refine ⟨k, ?_⟩
          have e1 : orderOf g = orderOf (g : ↥L) := (Subgroup.orderOf_coe g).symm
          have e2 : orderOf (g : ↥L) = orderOf ((g : ↥L) : X) := (Subgroup.orderOf_coe _).symm
          have e3 : orderOf (⟨((g : ↥L) : X), hgY⟩ : φ.ker) = orderOf ((g : ↥L) : X) :=
            Subgroup.orderOf_mk _ _
          exact e1.trans (e2.trans (e3.symm.trans hk))
        exact (hcen ↥L ψ hψ hLperf hcen' hpg).trans
          (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt L.subtype L.subtype_injective)
    ·
      obtain ⟨p, hp, hpq, hpY⟩ := i1021_exists_prime_ne hYq
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p φ.ker))
      set P' : Subgroup X := (P : Subgroup φ.ker).map φ.ker.subtype with hP'def
      have hfr : normalizer (P' : Set X) ⊔ φ.ker = ⊤ := Sylow.normalizer_sup_eq_top P
      have hP'Y : P' ≤ φ.ker := map_subtype_le _
      obtain ⟨m', hm⟩ := IsPGroup.iff_card.1 (P.isPGroup'.map φ.ker.subtype)
      have hP'q : ¬ q ∣ Nat.card P' := by
        rw [hm]
        intro h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm
      by_cases htop : normalizer (P' : Set X) = ⊤
      ·
        have hP'n : P'.Normal := normalizer_eq_top_iff.1 htop
        have hP'ne : P' ≠ ⊥ :=
          (map_eq_bot_iff_of_injective _ φ.ker.subtype_injective).not.2
            (P.ne_bot_of_dvd_card hpY)
        have hlt : Nat.card (X ⧸ P') < Nat.card X := by
          rw [card_eq_card_quotient_mul_card_subgroup P']
          have h1 : 1 < Nat.card P' := (one_lt_card_iff_ne_bot P').2 hP'ne
          have h2 : 0 < Nat.card (X ⧸ P') := Nat.card_pos
          nlinarith
        have hsurj : Function.Surjective (QuotientGroup.lift P' φ hP'Y) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          exact ⟨x, rfl⟩
        have := ih (X ⧸ P') (by omega) (QuotientGroup.lift P' φ hP'Y) hsurj
        rwa [CFSG.SectionRank.pRank_quotient_eq P' hP'q] at this
      ·
        set X₀ : Subgroup X := normalizer (P' : Set X)
        have hφ₀ : Function.Surjective (φ.comp X₀.subtype) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          have hx : x ∈ X₀ ⊔ φ.ker := hfr ▸ mem_top x
          obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.1 hx
          refine ⟨⟨a, ha⟩, ?_⟩
          simp [MonoidHom.mem_ker.1 hb]
        have hlt : Nat.card X₀ < Nat.card X := by
          rw [← card_top (G := X)]
          exact card_lt_of_lt (lt_top_iff_ne_top.2 htop)
        exact (ih X₀ (by omega) (φ.comp X₀.subtype) hφ₀).trans
          (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt X₀.subtype
            X₀.subtype_injective)

theorem le_pRank_of_surj_crit {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcen : ∀ (L : Type) [Group L] [Finite L] (ψ : L →* F), Function.Surjective ψ →
      commutator L = ⊤ → ψ.ker ≤ center L → IsPGroup q ψ.ker →
        r ≤ CFSG.Open.pRank q (⊤ : Subgroup L))
    (hinv : ∀ m, m ≤ r ^ 2 / 4 → ¬ Nat.card F ∣ Nat.card (GL (Fin m) (ZMod q)))
    {X : Type} [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    r ≤ CFSG.Open.pRank q (⊤ : Subgroup X) :=
  le_pRank_of_surj_crit_aux hnc hq hq2 hcen hinv _ X le_rfl φ hφ

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
