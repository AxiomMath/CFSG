module

public import CFSG.ClassicalInvolution.Q3.Q3TLTShape
public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge
public import CFSG.LocalAnalysis.ComponentClassification.ThompsonAB

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

namespace TightDatum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  (d : TightDatum R S t)

theorem mulAut_mem_fitting (δ : MulAut d.Dbar) {p : d.Dbar} (hp : p ∈ genFittingFitting d.Dbar) :
    δ p ∈ genFittingFitting d.Dbar := by
  have hchar : (CFSG.fittingSubgroup d.Dbar).Characteristic := inferInstance
  have h1 := hchar.fixed δ.symm
  have hp' : p ∈ CFSG.fittingSubgroup d.Dbar := hp
  show δ p ∈ CFSG.fittingSubgroup d.Dbar
  rw [← h1]
  show δ.symm (δ p) ∈ CFSG.fittingSubgroup d.Dbar
  simpa using hp'

theorem dbarAct_fixes_fitting_of_centralizer {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) {ub : d.Dbar} (hu2 : ub ^ 2 = 1) (hxu : d.dbarAct x ub = ub)
    (hC : ∀ c ∈ Subgroup.centralizer ({ub} : Set d.Dbar),
      c⁻¹ * d.dbarAct x c ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar))) :
    ∀ p ∈ genFittingFitting d.Dbar, d.dbarAct x p = p := by
  classical
  set δ : MulAut d.Dbar := d.dbarAct x with hδ
  set F : Subgroup d.Dbar := genFittingFitting d.Dbar with hF
  have : F.Normal := genFittingFitting_normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 F := d.isPGroup_two_fitting_dbar
  have hB : IsPGroup 2 (Subgroup.zpowers ub) := by
    rintro ⟨g, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have : (ub ^ n) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
    simpa using this
  have hδF : ∀ p ∈ F, δ p ∈ F := fun p hp => d.mulAut_mem_fitting δ hp
  have hδF' : ∀ p ∈ F, δ.symm p ∈ F := fun p hp => d.mulAut_mem_fitting δ.symm hp
  let δF : MulAut F :=
    { toFun := fun p => ⟨δ p, hδF p p.2⟩
      invFun := fun p => ⟨δ.symm p, hδF' p p.2⟩
      left_inv := fun p => Subtype.ext (by simp)
      right_inv := fun p => Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by simp) }
  have hδFapp : ∀ p : F, ((δF p : F) : d.Dbar) = δ p := fun _ => rfl
  let action : Subgroup.zpowers ub →* MulAut F :=
    (MulAut.conjNormal (H := F)).comp (Subgroup.zpowers ub).subtype
  have hδb : ∀ b : Subgroup.zpowers ub, δ b = b := by
    rintro ⟨b, n, rfl⟩
    simp [map_zpow, hxu]
  have hcomm : ∀ b : Subgroup.zpowers ub, Commute δF (action b) := by
    intro b
    refine MulEquiv.ext fun p => Subtype.ext ?_
    simp only [MulAut.mul_apply, hδFapp]
    show δ ((b : d.Dbar) * p * (b : d.Dbar)⁻¹) = (b : d.Dbar) * δ p * (b : d.Dbar)⁻¹
    rw [map_mul, map_mul, map_inv, hδb b]
  have hfix : ∀ p : F, (∀ b : Subgroup.zpowers ub, action b p = p) → δF p = p := by
    intro p hp
    have h1 : (ub : d.Dbar) * p * ub⁻¹ = p :=
      congrArg Subtype.val (hp ⟨ub, Subgroup.mem_zpowers ub⟩)
    have hpC : (p : d.Dbar) ∈ Subgroup.centralizer ({ub} : Set d.Dbar) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (p : d.Dbar) * ub = ub * p * ub⁻¹ * ub := by rw [h1]
        _ = ub * p := by group
    have h2 := hC p hpC
    have h3 : (p : d.Dbar)⁻¹ * δ p ∈ F := F.mul_mem (F.inv_mem p.2) (hδF p p.2)
    have h4 : (p : d.Dbar)⁻¹ * δ p = 1 := by
      have hodd := Balance.odd_card_oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar))
      obtain ⟨m, hm⟩ := hV ⟨_, h3⟩
      have hdvd2 : orderOf ((p : d.Dbar)⁻¹ * δ p) ∣ 2 ^ m := by
        have := congrArg Subtype.val hm
        exact orderOf_dvd_of_pow_eq_one (by simpa using this)
      have hdvdo : orderOf ((p : d.Dbar)⁻¹ * δ p) ∣
          Nat.card (Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar))) := by
        have := orderOf_dvd_natCard (⟨_, h2⟩ :
          Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)))
        simpa using this
      have hodd' : Odd (orderOf ((p : d.Dbar)⁻¹ * δ p)) := hodd.of_dvd_nat hdvdo
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
      rw [hj'] at hodd'
      have : j = 0 := by
        by_contra hj0
        exact (Nat.not_even_iff_odd.mpr hodd') ((Nat.even_pow' hj0).mpr even_two)
      rw [this, pow_zero] at hj'
      exact orderOf_eq_one_iff.mp hj'
    apply Subtype.ext
    rw [hδFapp]
    calc δ p = p * ((p : d.Dbar)⁻¹ * δ p) := by group
      _ = p := by rw [h4, mul_one]
  have hpow : δF ^ 3 ^ k = 1 := by
    have hδk : δ ^ 3 ^ k = 1 := by rw [hδ, ← map_pow, hx, map_one]
    have hgen : ∀ n : ℕ, ∀ p : F, (((δF ^ n) p : F) : d.Dbar) = (δ ^ n) p := by
      intro n
      induction n with
      | zero => intro p; rfl
      | succ n ih =>
        intro p
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
        rfl
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [hgen, hδk]
    rfl
  have hcop : (3 ^ k).Coprime 2 := Nat.Coprime.pow_left k (by norm_num)
  have h1 := ComponentClassification.ThompsonAB.coprime_eq_one 2 hV hB action δF hcomm hfix
    (3 ^ k) hpow hcop
  intro p hp
  have := congrArg (fun φ : MulAut F => ((φ ⟨p, hp⟩ : F) : d.Dbar)) h1
  simpa [hδFapp] using this

theorem oddCoreIn_top_dbar_eq_bot : Balance.oddCoreIn (⊤ : Subgroup d.Dbar) = ⊥ := by
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant
    (Subgroup.topEquiv (G := d.Dbar)).symm
  have h2 : componentClassificationOddCore d.Dbar = ⊥ := d.oddCore_dbar_eq_bot
  rw [h2, Subgroup.map_bot] at h1
  unfold Balance.oddCoreIn
  rw [← h1, Subgroup.map_bot]

theorem component_inf_oddCoreIn_eq_bot {ub : d.Dbar} {K : Subgroup d.Dbar}
    (hK : IsComponentOf K ⊤) (hKC : K ≤ Subgroup.centralizer ({ub} : Set d.Dbar)) {y : d.Dbar}
    (hyK : y ∈ K) (hyO : y ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar))) :
    y = 1 := by
  set Ou := Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)) with hOu
  have hnorm : K ≤ Subgroup.normalizer ((K ⊓ Ou : Subgroup d.Dbar) : Set d.Dbar) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hkC := hKC hk
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨K.mul_mem (K.mul_mem hk hz1) (K.inv_mem hk), Balance.conj_mem_oddCoreIn hkC hz2⟩
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, ?_⟩
      · have := K.mul_mem (K.mul_mem (K.inv_mem hk) hz1) hk
        simpa [mul_assoc] using this
      · have := Balance.conj_mem_oddCoreIn (Subgroup.inv_mem _ hkC) hz2
        simpa [mul_assoc] using this
  have hodd : Odd (Nat.card (K ⊓ Ou : Subgroup d.Dbar)) :=
    (Balance.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have h1 := Balance.le_oddCoreIn_of_normalizes inf_le_left hnorm hodd
  have h2 : Balance.oddCoreIn K ≤ Balance.oddCoreIn ⊤ := Balance.oddCoreIn_le_of_isSubnormal hK.2.1
  rw [d.oddCoreIn_top_dbar_eq_bot] at h2
  have := h2 (h1 ⟨hyK, hyO⟩)
  exact (Subgroup.mem_bot.mp this)

theorem not_comm_of_isQuasisimple {X : Type*} [Group X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple K) : ¬ ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
  intro hcomm
  obtain ⟨h1, h2⟩ := hK
  have hbot : commutator K = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hcomm a a.2 b b.2)
  rw [hbot] at h1
  have htriv : Subsingleton K := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Subgroup K) := h1 ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup K) := h1 ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hq : Subsingleton (K ⧸ Subgroup.center K) := inferInstance
  exact (IsSimpleGroup.toNontrivial (G := K ⧸ Subgroup.center K)).exists_pair_ne.elim
    fun a ha => ha.elim fun b hab => hab (Subsingleton.elim a b)

theorem dbarAct_fixes_component_of_commute {x : Subgroup.centralizer ({t} : Set G)}
    {ub : d.Dbar}
    (hC : ∀ c ∈ Subgroup.centralizer ({ub} : Set d.Dbar),
      c⁻¹ * d.dbarAct x c ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)))
    {K : Subgroup d.Dbar} (hK : IsComponentOf K ⊤) (hKu : ∀ y ∈ K, y * ub = ub * y) :
    ∀ y ∈ K, d.dbarAct x y = y := by
  classical
  set δ : MulAut d.Dbar := d.dbarAct x with hδ
  set Ou := Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)) with hOu
  have hKC : K ≤ Subgroup.centralizer ({ub} : Set d.Dbar) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKu y hy)
  have hKO : ∀ y ∈ K, y ∈ Ou → y = 1 := fun y hy hyO =>
    d.component_inf_oddCoreIn_eq_bot hK hKC hy hyO
  have ho : ∀ y ∈ K, y⁻¹ * δ y ∈ Ou := fun y hy => hC y (hKC hy)
  have hU : (K.map δ.toMonoidHom).IsSubnormal := by
    have h1 := isSubnormal_map_mulEquiv δ hK.2.1
    rw [Subgroup.map_top_of_surjective δ.toMonoidHom δ.surjective] at h1
    exact (CFSG.Adapters.isSubnormal_top_iff _).mp h1
  rcases CFSG.LocalCores.component_subnormal_subgroup ((CFSG.isComponent_iff_open K).mpr hK) hU
    with hle | hcomm
  ·
    have heq : K = K.map δ.toMonoidHom := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (f := δ.toMonoidHom) δ.injective]
    intro y hy
    have hδy : δ y ∈ K := by rw [heq]; exact ⟨y, hy, rfl⟩
    have h1 := hKO _ (K.mul_mem (K.inv_mem hy) hδy) (ho y hy)
    calc δ y = y * (y⁻¹ * δ y) := by group
      _ = y := by rw [h1, mul_one]
  ·
    exfalso
    have hcen : K.map δ.toMonoidHom ≤ Subgroup.centralizer (K : Set d.Dbar) := by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact ((Subgroup.mem_centralizer_iff.mp (this ha)) z hz).symm
    refine not_comm_of_isQuasisimple hK.2.2 fun a ha b hb => ?_
    have hab : a * δ b = δ b * a :=
      (Subgroup.mem_centralizer_iff.mp (hcen ⟨b, hb, rfl⟩)) a ha
    set o := b⁻¹ * δ b with ho'
    have hoO : o ∈ Ou := ho b hb
    have hδb : δ b = b * o := by rw [ho']; group
    have haC := hKC ha
    have h1 : b⁻¹ * a * b * a⁻¹ ∈ Ou := by
      have h2 : b⁻¹ * a * b * a⁻¹ = o * (a * o⁻¹ * a⁻¹) := by
        have : a * (b * o) = (b * o) * a := by rw [← hδb]; exact hab
        calc b⁻¹ * a * b * a⁻¹ = b⁻¹ * (a * (b * o)) * o⁻¹ * a⁻¹ := by group
          _ = b⁻¹ * ((b * o) * a) * o⁻¹ * a⁻¹ := by rw [this]
          _ = o * (a * o⁻¹ * a⁻¹) := by group
      rw [h2]
      exact Ou.mul_mem hoO (Balance.conj_mem_oddCoreIn haC (Ou.inv_mem hoO))
    have h3 : b⁻¹ * a * b * a⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hb) ha) hb) (K.inv_mem ha)
    have h4 := hKO _ h3 h1
    calc a * b = b * (b⁻¹ * a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h4, mul_one]

theorem innerOnLayer_of_centralizer {x : Subgroup.centralizer ({t} : Set G)} {ub : d.Dbar}
    (hC : ∀ c ∈ Subgroup.centralizer ({ub} : Set d.Dbar),
      c⁻¹ * d.dbarAct x c ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)))
    (hK : ∀ K : Subgroup d.Dbar, IsComponentOf K ⊤ → (∃ y ∈ K, y * ub ≠ ub * y) →
      ∃ e ∈ K, ∀ y ∈ K, d.dbarAct x y = e * y * e⁻¹)
    (huniq : ∀ K₁ K₂ : Subgroup d.Dbar, IsComponentOf K₁ ⊤ → IsComponentOf K₂ ⊤ →
      (∃ y ∈ K₁, y * ub ≠ ub * y) → (∃ y ∈ K₂, y * ub ≠ ub * y) → K₁ = K₂) :
    d.InnerOnLayer x := by
  classical
  set δ : MulAut d.Dbar := d.dbarAct x with hδ
  have hext : ∀ e : d.Dbar, (∀ L : Subgroup d.Dbar, IsComponentOf L ⊤ → ∀ y ∈ L,
      δ y = e * y * e⁻¹) → ∀ y ∈ genFittingLayer d.Dbar, δ y = e * y * e⁻¹ := by
    intro e he
    have hle : genFittingLayer d.Dbar ≤
        MonoidHom.eqLocus δ.toMonoidHom (MulAut.conj e).toMonoidHom := by
      refine sSup_le fun L hL y hy => ?_
      show δ y = MulAut.conj e y
      rw [MulAut.conj_apply]
      exact he L hL y hy
    intro y hy
    have h : δ y = (MulAut.conj e) y := hle hy
    simpa [MulAut.conj_apply] using h
  by_cases hex : ∃ K₀ : Subgroup d.Dbar, IsComponentOf K₀ ⊤ ∧ ∃ y ∈ K₀, y * ub ≠ ub * y
  · obtain ⟨K₀, hK₀c, hK₀u⟩ := hex
    obtain ⟨e, he, hee⟩ := hK K₀ hK₀c hK₀u
    refine ⟨e, (le_sSup (s := {L : Subgroup d.Dbar | IsComponentOf L ⊤}) hK₀c) he,
      hext e fun L hLc => ?_⟩
    by_cases hLu : ∃ y ∈ L, y * ub ≠ ub * y
    · rw [huniq L K₀ hLc hK₀c hLu hK₀u]
      exact hee
    · push Not at hLu
      intro y hy
      rw [d.dbarAct_fixes_component_of_commute hC hLc hLu y hy]
      have hne : L ≠ K₀ := by
        rintro rfl
        obtain ⟨z, hz, hzu⟩ := hK₀u
        exact hzu (hLu z hz)
      rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open L).mpr hLc)
        ((CFSG.isComponent_iff_open K₀).mpr hK₀c) with h | h
      · exact absurd h hne
      · have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        have hey : e * y = y * e := (Subgroup.mem_centralizer_iff.mp (hcen hy)) e he
        calc y = y * e * e⁻¹ := by group
          _ = e * y * e⁻¹ := by rw [← hey]
  · push Not at hex
    refine ⟨1, Subgroup.one_mem _, hext 1 fun L hLc y hy => ?_⟩
    rw [d.dbarAct_fixes_component_of_commute hC hLc (fun z hz => hex L hLc z hz) y hy]
    group

theorem good_of_centralizer {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) {ub : d.Dbar} (hu2 : ub ^ 2 = 1) (hxu : d.dbarAct x ub = ub)
    (hC : ∀ c ∈ Subgroup.centralizer ({ub} : Set d.Dbar),
      c⁻¹ * d.dbarAct x c ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)))
    (hK : ∀ K : Subgroup d.Dbar, IsComponentOf K ⊤ → (∃ y ∈ K, y * ub ≠ ub * y) →
      ∃ e ∈ K, ∀ y ∈ K, d.dbarAct x y = e * y * e⁻¹)
    (huniq : ∀ K₁ K₂ : Subgroup d.Dbar, IsComponentOf K₁ ⊤ → IsComponentOf K₂ ⊤ →
      (∃ y ∈ K₁, y * ub ≠ ub * y) → (∃ y ∈ K₂, y * ub ≠ ub * y) → K₁ = K₂) :
    d.Good x := by
  refine ⟨fun p hp => ?_, d.innerOnLayer_of_centralizer hC hK huniq⟩
  rw [d.dbarAct_fixes_fitting_of_centralizer hx hu2 hxu hC p hp, mul_inv_cancel]
  exact Subgroup.one_mem _

end TightDatum

namespace TightDatum

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  (d : TightDatum R S t)

theorem goodThreeElement_of_good {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) (hx1 : d.act x ≠ 1) (hg : d.Good x) : GoodThreeElement R t := by
  have hD := d.diagFree_of_good hx hx1 hg
  have hx3 : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hx
  have hxR : ∃ r ∈ R, ⁅(x : G), r⁆ ∉ oddCoreImg R := by
    by_contra hcon
    push Not at hcon
    exact hx1 ((d.act_eq_one_iff x.2).mpr hcon)
  obtain ⟨x', k', hx'C, hx'3, hx'R, hW⟩ := hD (x : G) k x.2 hx3 hxR
  exact ⟨x', k', hx'C, hx'3, hx'R, hW⟩

end TightDatum

end CFSG.ClassicalInvolution.Q3
