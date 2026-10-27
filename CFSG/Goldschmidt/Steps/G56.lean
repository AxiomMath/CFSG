module

public import CFSG.Goldschmidt.Steps.G56Main
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom

public section

namespace CFSG.Goldschmidt.G55

open CFSG.GorensteinWalter CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_sup_le_of_le_normalizer {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) ≤ Nat.card H * Nat.card N := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun q : H × N => (⟨q.1 * q.2, Subgroup.mul_mem_sup q.1.2 q.2.2⟩ : ↥(H ⊔ N))) fun x => ?_
  obtain ⟨u, hu, v, hv, huv⟩ := mem_sup_of_le_normalizer h x.2
  exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext huv⟩

omit [Finite G] in
theorem isElementaryAbelian_subgroupOf {E P : Subgroup G} {p : ℕ}
    (hE : CFSG.Open.IsElemAbelian p E) : IsElementaryAbelian p (E.subgroupOf P) where
  is_comm := ⟨fun x y => Subtype.ext (Subtype.ext (by
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨((x : P) : G), x.2⟩ ⟨((y : P) : G), y.2⟩)
    exact h))⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (Subtype.ext (by simpa using hE.2 _ x.2))

theorem exists_normal_isElemAbelian {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p P) (h3 : 3 ≤ CFSG.Open.pRank p P) :
    ∃ K ≤ P, P ≤ Subgroup.normalizer (K : Set G) ∧ CFSG.Open.IsElemAbelian p K ∧
      Nat.card K = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, hE₀P, hE₀, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt P
  have hE₀3 : p ^ 3 ≤ Nat.card E₀ := hE₀c ▸ Nat.pow_le_pow_right hp.pos h3
  obtain ⟨k, hk⟩ := (hPp.to_le hE₀P).exists_card_eq
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p (n := 3)
    (hk ▸ Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp (hk ▸ hE₀3)))
  set E₃ := K₀.map E₀.subtype
  have hE₃P : E₃ ≤ P := (Subgroup.map_subtype_le _).trans hE₀P
  have hE₃ : CFSG.Open.IsElemAbelian p E₃ := isElemAbelian_of_le hE₀ (Subgroup.map_subtype_le _)
  have hE₃c : Nat.card E₃ = p ^ 3 := by
    rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK₀]
  have : IsElementaryAbelian p (E₃.subgroupOf P) := isElementaryAbelian_subgroupOf hE₃
  have hrank : 3 ≤ groupRank P := by
    refine groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3' (p := p)
      (B := E₃.subgroupOf P) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₃P).toEquiv, hE₃c]
  have hPc : ¬ IsCyclic P := fun hcyc => not_isCyclic_of_isElemAbelian hp hE₃
    (by rw [hE₃c]; exact Nat.pow_le_pow_right hp.pos (by norm_num)) (isCyclic_of_le hE₃P hcyc)
  obtain ⟨X, hXP, hXc, hXexp, hXN⟩ := exists_noncyclic_exponent_le hp hp2 hPp hPc
  obtain ⟨z, hzX, x, hxX, hz1, hzC, hxz, hxP, -, -⟩ := exists_typePP hp hp2 hPp hXP
    (P.le_normalizer.trans hXN) hXexp hXc (t := 1) (mul_one 1) (Subgroup.one_mem _)
    (Subgroup.one_mem _)
  set E₂ := Subgroup.zpowers z ⊔ Subgroup.zpowers x with hE₂def
  have hzx : Subgroup.zpowers z ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) :
      Set G) := by
    rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hzC) x (hXP hxX)).symm
  have hE₂ : CFSG.Open.IsElemAbelian p E₂ := isElemAbelian_sup (isElemAbelian_zpowers
    (hXexp z hzX)) (isElemAbelian_zpowers (hXexp x hxX)) hzx
  have hE₂P : E₂ ≤ P := sup_le (Subgroup.zpowers_le.mpr (hXP hzX))
    (Subgroup.zpowers_le.mpr (hXP hxX))
  have hzp : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hXexp z hzX) hz1]
  have hxp : Nat.card (Subgroup.zpowers x) = p := by
    have hx1 : x ≠ 1 := fun h => hxz (h ▸ Subgroup.one_mem _)
    rw [Nat.card_zpowers, orderOf_eq_prime (hXexp x hxX) hx1]
  have hE₂c : Nat.card E₂ = p ^ 2 := by
    refine le_antisymm ?_ ?_
    · have := card_sup_le_of_le_normalizer (hzx.trans (Subgroup.centralizer_le_normalizer _))
      rwa [hzp, hxp, ← pow_two] at this
    · have hlt : Subgroup.zpowers z < E₂ := lt_of_le_of_ne le_sup_left fun h =>
        hxz (h ▸ (le_sup_right : Subgroup.zpowers x ≤ E₂) (Subgroup.mem_zpowers x))
      have hge := card_ge_of_lt' hp (hPp.to_le hE₂P) hlt
      rwa [hzp, ← pow_two] at hge
  have hPE₂ : P ≤ Subgroup.normalizer (E₂ : Set G) := by
    intro g hg
    apply Bender35.mem_normalizer_of_map_conj_eq
    have hle : E₂.map (MulAut.conj g).toMonoidHom ≤ E₂ := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · show g * z * g⁻¹ ∈ E₂
        rw [(Subgroup.mem_centralizer_iff.mp hzC) g hg, mul_inv_cancel_right]
        exact (le_sup_left : Subgroup.zpowers z ≤ E₂) (Subgroup.mem_zpowers z)
      · show g * x * g⁻¹ ∈ E₂
        have hc := hxP g hg
        have heq : g * x * g⁻¹ = (⁅x, g⁆)⁻¹ * x := by rw [commutatorElement_def]; group
        rw [heq]
        exact E₂.mul_mem (E₂.inv_mem ((le_sup_left : Subgroup.zpowers z ≤ E₂) hc))
          ((le_sup_right : Subgroup.zpowers x ≤ E₂) (Subgroup.mem_zpowers x))
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hE₂n : (E₂.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₂P).mpr hPE₂
  have hE₂mem : E₂.subgroupOf P ∈ elementaryAbelianSubgroupsOfRank p 2 P :=
    ⟨by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂P).toEquiv, hE₂c],
      isElementaryAbelian_subgroupOf hE₂⟩
  obtain ⟨B, hBn, hBel, hBc, -⟩ :=
    exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal hp2 hPp hrank hE₂mem
  refine ⟨B.map P.subtype, Subgroup.map_subtype_le B,
    le_normalizer_of_isNormalIn (isNormalIn_map_subtype P B), ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.map_isMulCommutative _ _
  · rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (A := B) b hb)
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hBc]

theorem card_le_of_commutator_mem {K I : Subgroup G} (hKc : IsMulCommutative K) {x : G}
    (hI : I ≤ K) (hKI : ∀ k ∈ K, ⁅k, x⁆ ∈ I) :
    Nat.card K ≤
      Nat.card I * Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  have hmem : ∀ k ∈ K, ⁅k, x⁆ ∈ K := fun k hk => hI (hKI k hk)
  have hcomm : ∀ u ∈ K, ∀ v ∈ K, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hKc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  let φ : K →* K :=
    { toFun := fun k => ⟨⁅(k : G), x⁆, hmem k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k₁ k₂ => Subtype.ext (by
        show ⁅(k₁ : G) * k₂, x⁆ = ⁅(k₁ : G), x⁆ * ⁅(k₂ : G), x⁆
        exact commutatorElement_mul_left_of_commute (hcomm _ k₁.2 _ (hmem k₂ k₂.2))
          (hcomm _ (hmem k₁ k₁.2) _ (hmem k₂ k₂.2))) }
  have hker : φ.ker = (Subgroup.centralizer ({x} : Set G)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : ⁅(k : G), x⁆ = 1 := congrArg Subtype.val h
      rwa [commutatorElement_eq_one_iff_mul_comm] at h'
    · intro h
      apply Subtype.ext
      show ⁅(k : G), x⁆ = 1
      rwa [commutatorElement_eq_one_iff_mul_comm]
  have hrange : φ.range ≤ I.subgroupOf K := by
    rintro _ ⟨k, rfl⟩
    exact hKI k k.2
  have h1 : Nat.card K = Nat.card φ.ker * Nat.card φ.range := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
  have h2 : Nat.card φ.range ≤ Nat.card I := by
    refine (Subgroup.card_le_of_le hrange).trans_eq ?_
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI).toEquiv
  have h3 : Nat.card φ.ker = Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem exists_isElemAbelian_of_card_inf_centralizer {P K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p P) (hKP : K ≤ P) (hK : CFSG.Open.IsElemAbelian p K)
    (hKc : Nat.card K = p ^ 3) {x : G} (hxP : x ∈ P) (hxp : x ^ p = 1)
    (hcard : p ^ 2 ≤ Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) :
    ∃ E ≤ P, CFSG.Open.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E ∧ x ∈ E := by
  by_cases hxK : x ∈ K
  · exact ⟨K, hKP, hK, hKc.ge, hxK⟩
  · set C := K ⊓ Subgroup.centralizer ({x} : Set G)
    have hxC : Subgroup.zpowers x ≤ Subgroup.centralizer (C : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hE := isElemAbelian_sup (isElemAbelian_zpowers hxp) (isElemAbelian_of_le hK inf_le_left)
      hxC
    have hEP : Subgroup.zpowers x ⊔ C ≤ P :=
      sup_le (Subgroup.zpowers_le.mpr hxP) (inf_le_left.trans hKP)
    have hlt : C < Subgroup.zpowers x ⊔ C := lt_of_le_of_ne le_sup_right fun h =>
      hxK ((h ▸ (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ C)
        (Subgroup.mem_zpowers x) : x ∈ C).1)
    have hge := card_ge_of_lt' hp (hPp.to_le hEP) hlt
    refine ⟨_, hEP, hE, ?_, (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)⟩
    calc p ^ 3 = p * p ^ 2 := by ring
      _ ≤ p * Nat.card C := Nat.mul_le_mul_left _ hcard
      _ ≤ _ := hge

section Main

variable {S : Sylow 2 G} {A : Subgroup G} {a : G} {H : Subgroup G}

theorem zpowers_mem_goldA_of_le
    (h31 : S_G31) (h37 : S_G37) (hS : GoldSetting G S A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hH : H ∈ CFSG.Walter.benderM a) (ha2 : a ∈ qCoreOf H 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hEP : E ≤ qCoreOf H p)
    (hE : CFSG.Open.IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) {v : G} (hv : v ∈ E)
    (hv1 : v ≠ 1) : Subgroup.zpowers v ∈ goldA a H := by
  set P := qCoreOf H p with hPdef
  set Ω := omegaOneCenter P p with hΩdef
  have hPn := qCoreOf_normal_in H p
  have hΩH : H ≤ Subgroup.normalizer (Ω : Set G) := le_normalizer_omegaOneCenter hPn p
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE3
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  have hP1 : P ≠ ⊥ := fun h => hE1 (le_bot_iff.mp (h ▸ hEP))
  have hΩ1 : Ω ≠ ⊥ := omegaOneCenter_ne_bot hp (qCoreOf_isPGroup H p) hP1
  have hΩn : IsNormalIn Ω H := ⟨(omegaOneCenter_le P p).trans hPn.1, fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.mp (hΩH hh) z).mp hz⟩
  have hHco := isCoatom_of_mem_benderM hH
  have hNΩ : Subgroup.normalizer (Ω : Set G) = H :=
    normalizer_eq_of_nontrivial_normal_in_coatom hS.isSimpleGroup hHco hΩn.1 hΩ1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hΩn.1).mpr hΩH)
  have hΩel : CFSG.Open.IsElemAbelian p Ω := by
    refine ⟨⟨⟨fun z w => Subtype.ext ?_⟩⟩, fun z hz => pow_eq_one_of_mem_omegaOneCenter hz⟩
    exact ((Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_centralizer P p w.2)) z
      (omegaOneCenter_le P p z.2))
  have hEΩ : E ≤ Subgroup.centralizer (Ω : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_centralizer P p hz)) e
      (hEP he)).symm
  have hVel := isElemAbelian_sup hE hΩel hEΩ
  let T : Gold37 G :=
    { Syl := S, A := A, hS := hS, h31 := h31, h37 := h37, a := a, haA := haA, ha1 := ha1,
      H := H, hH := hHco, hCH := centralizer_le_of_mem_benderM hH, ha2 := ha2, p := p,
      hp := hp, hp2 := hp2, V := E ⊔ Ω, hVP := sup_le hEP (omegaOneCenter_le P p),
      hVcomm := hVel.1, hVexp := hVel.2,
      hV3 := hE3.trans (Subgroup.card_le_of_le le_sup_left),
      hCV := (Subgroup.centralizer_le (le_sup_right : Ω ≤ E ⊔ Ω)).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNΩ.le) }
  exact T.zpowers_mem_goldA ((le_sup_left : E ≤ E ⊔ Ω) hv) hv1

end Main

end CFSG.Goldschmidt.G55

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter CFSG.Walter G55
open scoped commutatorElement

theorem G56_of
    (h31 : S_G31) (h37 : S_G37) (h53 : S_G53) (h55 : S_G55) : S_G56 := by
  intro G _ _ S A hS a haA ha1 H hH ⟨p, hp, hp2, hrank⟩
  by_cases ha2 : a ∈ qCoreOf H 2
  swap
  · exact h55 G S A hS a haA ha1 H hH ha2
  intro Y hY1 hYF0 hYsn0 haY
  by_contra hYA
  obtain ⟨hYF, hYsn⟩ := isSubnormal_of_fstarZero hYF0 hYsn0
  have hY : IsBad a H Y := ⟨hY1, hYF, hYsn, haY, hYA⟩
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have haP : P ≤ Subgroup.centralizer ({a} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp
      (qCoreOf_centralizer_of_ne H hp Nat.prime_two hp2 ha2)) x hx
  have hfinal : ∀ E ≤ P, CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
      E ≤ Subgroup.normalizer (Y : Set G) →
      (∀ e ∈ E, e ≠ 1 → Subgroup.zpowers e ∈ goldA a H) → False := by
    intro E hEP hE hEc hEY hEg
    obtain ⟨hEF, hEsn⟩ := Bender35.le_and_isSubnormal hp hEP
    have hEa : E ≤ Subgroup.centralizer ({a} : Set G) := hEP.trans haP
    refine false_of_isBad h53 hS haA ha1 hH hY hEF hEsn ?_ hEY ?_ hp hp2 hE hEc hEg
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEa he)
    · rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEa he)
  obtain ⟨K, hKP, hPK, hKel, hKc⟩ := exists_normal_isElemAbelian hp hp2 hPp hrank
  have hgood : ∀ x ∈ P, x ≠ 1 → x ^ p = 1 →
      p ^ 2 ≤ Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) →
      Subgroup.zpowers x ∈ goldA a H := by
    intro x hxP hx1 hxp hcard
    obtain ⟨E, hEP, hE, hE3, hxE⟩ :=
      exists_isElemAbelian_of_card_inf_centralizer hp hPp hKP hKel hKc hxP hxp hcard
    exact zpowers_mem_goldA_of_le h31 h37 hS haA ha1 hH ha2 hp hp2 hEP hE hE3 hxE hx1
  have hcomK : ∀ x ∈ P, ∀ k ∈ K, ⁅k, x⁆ ∈ K ⊓ ⁅P, P⁆ := by
    intro x hxP k hk
    refine ⟨?_, Subgroup.commutator_mem_commutator (hKP hk) hxP⟩
    have : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hPK hxP) _).mp (K.inv_mem hk))
  have hP'P : ⁅P, P⁆ ≤ P := Bender35.commutator_self_le P
  by_cases hP'c : IsCyclic (⁅P, P⁆ : Subgroup G)
  ·
    have hI : Nat.card (K ⊓ ⁅P, P⁆ : Subgroup G) ≤ p :=
      Bender35.card_le_of_isCyclic_of_pow_eq_one hp (isCyclic_of_le inf_le_right hP'c)
        (isElemAbelian_of_le hKel inf_le_left).2
    have hCK : ∀ x ∈ P,
        p ^ 2 ≤ Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
      intro x hxP
      have h := card_le_of_commutator_mem hKel.1 inf_le_left (hcomK x hxP)
      rw [hKc] at h
      have h' : p * p ^ 2 ≤ p * Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) :
          Subgroup G) := by
        calc p * p ^ 2 = p ^ 3 := by ring
          _ ≤ _ := h
          _ ≤ _ := Nat.mul_le_mul_right _ hI
      exact Nat.le_of_mul_le_mul_left h' hp.pos
    set Q := Y ⊓ P with hQdef
    set N := P ⊓ Subgroup.normalizer (Q : Set G) with hNdef
    have hNc : ¬ IsCyclic N := by
      intro hcyc
      have hQN : Q ≤ N := le_inf inf_le_right Subgroup.le_normalizer
      obtain ⟨⟨q, hqQ⟩, hgen⟩ := (isCyclic_of_le hQN hcyc).exists_zpow_surjective
      have hQq : Q = Subgroup.zpowers q := by
        refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hqQ)
        obtain ⟨k, hk⟩ := hgen ⟨y, hy⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hCN : K ⊓ Subgroup.centralizer ({q} : Set G) ≤ N := by
        intro c hc
        refine ⟨hKP hc.1, ?_⟩
        rw [hQq]
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [centralizer_zpowers_eq']
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
      exact not_isCyclic_of_isElemAbelian hp (isElemAbelian_of_le hKel inf_le_left)
        (hCK q hqQ.2) (isCyclic_of_le hCN hcyc)
    obtain ⟨E, hEN, hE, hEc⟩ := exists_isElemAbelian_card_sq hp hp2 (hPp.to_le inf_le_left) hNc
    refine hfinal E (hEN.trans inf_le_left) hE hEc (fun e he => ?_) (fun e he he1 => ?_)
    · exact mem_normalizer_of_mem_normalizer_inf_qCoreOf hp hYF hYsn (hEN he).1 (hEN he).2
    · exact hgood e (hEN he).1 he1 (hE.2 e he) (hCK e (hEN he).1)
  ·
    have hZc := not_isCyclic_center_commutator hp hp2 hPp hP'c
    obtain ⟨E, hEZ, hE, hEc⟩ :=
      exists_isElemAbelian_card_sq hp hp2 (hPp.to_le (inf_le_left.trans hP'P)) hZc
    have hEP : E ≤ P := hEZ.trans (inf_le_left.trans hP'P)
    refine hfinal E hEP hE hEc (fun e he => ?_) (fun e he he1 => ?_)
    · have hEC := hEZ.trans (center_commutator_le_centralizer_fstarZero H hp)
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hYF0 (hEC he))
    · refine hgood e (hEP he) he1 (hE.2 e he) ?_
      set C := K ⊓ Subgroup.centralizer ({e} : Set G) with hCdef
      have hKe : ∀ k ∈ K, ⁅k, e⁆ ∈ C := by
        intro k hk
        refine ⟨(hcomK e (hEP he) k hk).1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        exact (Subgroup.mem_centralizer_iff.mp (hEZ he).2) _ (hcomK e (hEP he) k hk).2
      have h := card_le_of_commutator_mem hKel.1 (inf_le_left : C ≤ K) hKe
      rw [hKc] at h
      obtain ⟨j, hj⟩ := (hPp.to_le (inf_le_left.trans hKP : C ≤ P)).exists_card_eq
      rw [hj, ← pow_add] at h
      have h3 : 3 ≤ j + j := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
      rw [hj]
      exact Nat.pow_le_pow_right hp.pos (by omega)

end CFSG.Goldschmidt
