module

public import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.Asc75.Unique

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

theorem exists_pow_orderOf_two {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hx1 : x ≠ 1) : ∃ n : ℕ, orderOf (x ^ n) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by
    rw [← hk]; exact (Subgroup.orderOf_mk x hx).symm
  have hk1 : 1 ≤ k := by
    by_contra hlt
    have h0 : k = 0 := by omega
    rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
    exact hx1 hk'
  refine ⟨2 ^ (k - 1), ?_⟩
  rw [orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hk']
  have : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [this, Nat.gcd_eq_right (dvd_mul_right _ _)]
  exact Nat.mul_div_cancel_left 2 ((Nat.two_pow_pos _))

theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← sq]; exact hx ▸ pow_orderOf_eq_one x

theorem orderOf_eq_two_of_mul_self_eq_one {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    orderOf x = 2 := by
  apply orderOf_eq_prime _ hx1
  rw [sq]; exact hx

theorem isPGroup_zpowers_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem exists_conj_mem_sylow [Finite G] (K : Subgroup G) (T : Sylow 2 G)
    (hTK : (T : Subgroup G) ≤ K) (W : Subgroup G) (hWK : W ≤ K) (hW : IsPGroup 2 W) :
    ∃ k ∈ K, ∀ w ∈ W, k⁻¹ * w * k ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_sylow (p := 2) K T hTK W hWK hW
  refine ⟨c⁻¹, K.inv_mem hcK, fun w hw => ?_⟩
  have := hc (Subgroup.mem_map_of_mem _ hw)
  simpa [MulAut.conj_apply] using this

theorem FixedOnlyElt.mem {H : Subgroup G} {a : G} (h : FixedOnlyElt H a) : a ∈ H := h.1

theorem FixedOnlyElt.mem_of_conj {H : Subgroup G} {a g : G} (h : FixedOnlyElt H a)
    (hg : g⁻¹ * a * g ∈ H) : g ∈ H := h.2 g hg

theorem FixedOnlyElt.mem_of_conj_eq {H : Subgroup G} {a g : G} (h : FixedOnlyElt H a)
    (hg : g⁻¹ * a * g = a) : g ∈ H :=
  h.2 g (by rw [hg]; exact h.1)

theorem FixedOnlyElt.conj {H : Subgroup G} {a c : G} (h : FixedOnlyElt H a) (hc : c ∈ H) :
    FixedOnlyElt H (c⁻¹ * a * c) := by
  refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hc) h.1) hc, fun g hg => ?_⟩
  have : (c * g)⁻¹ * a * (c * g) ∈ H := by
    have e : (c * g)⁻¹ * a * (c * g) = g⁻¹ * (c⁻¹ * a * c) * g := by group
    rw [e]; exact hg
  have h2 := h.2 _ this
  have e : g = c⁻¹ * (c * g) := by group
  rw [e]
  exact H.mul_mem (H.inv_mem hc) h2

theorem FixedOnlyElt.of_pow {H : Subgroup G} {a : G} (ha : a ∈ H) {n : ℕ}
    (h : FixedOnlyElt H (a ^ n)) : FixedOnlyElt H a := by
  refine ⟨ha, fun g hg => h.2 g ?_⟩
  have e : g⁻¹ * a ^ n * g = (g⁻¹ * a * g) ^ n := by
    simpa using (conj_pow (a := g⁻¹) (b := a) (i := n)).symm
  rw [e]
  exact H.pow_mem hg n

section HypAux

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.mem_of_conj_eq (h : Hyp S A₁ A₂ H) {a d : G} (ha : a ∈ uSet A₁ A₂) (ha1 : a ≠ 1)
    (hd : d⁻¹ * a * d = a) : d ∈ H := by
  rcases ha with ha | ha
  · exact h.mem_of_conj_mem (Or.inl rfl) (Or.inl rfl) ha ha1 (by rw [hd]; exact ha)
  · exact h.mem_of_conj_mem (Or.inr rfl) (Or.inr rfl) ha ha1 (by rw [hd]; exact ha)

theorem Hyp.mem_S_of_mem_uSet (h : Hyp S A₁ A₂ H) {a : G} (ha : a ∈ uSet A₁ A₂) : a ∈ S := by
  rcases ha with ha | ha
  · exact h.le₁ ha
  · exact h.le₂ ha

end HypAux


section More

variable [Finite G]

omit [Finite G] in
theorem isElemAbelian_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · rw [sq]; exact ha
    · rw [Set.mem_singleton_iff.mp hy, sq]; exact hb
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure ({a, b} : Set G)) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [sq] at hy hz ⊢
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hc]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy, hz, one_mul]
  | inv y _ hy => rw [inv_pow, hy, inv_one]

theorem three_le_card_of_distinct {E : Subgroup G} {a b : G} (haE : a ∈ E) (hbE : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : 3 ≤ Nat.card E := by
  have hsub : ({1, a, b} : Set G) ⊆ (E : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact E.one_mem
    · exact haE
    · exact hbE
  have h3 : ({1, a, b} : Set G).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, a, b, ha1.symm, hb1.symm, hne, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  omega

theorem two_le_pRank_of_pair {H : Subgroup G} {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (haH : a ∈ H)
    (hbH : b ∈ H) : 2 ≤ CFSG.Open.pRank 2 H := by
  set E := Subgroup.closure ({a, b} : Set G) with hE
  have hEel : IsElemAbelian 2 E := isElemAbelian_closure_pair ha hb hab
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hEH : E ≤ H := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact haH
    · rw [Set.mem_singleton_iff.mp hx]; exact hbH)
  have hpg : IsPGroup 2 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hEel.2 x x.2⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
  have h3 : 3 ≤ Nat.card E := three_le_card_of_distinct haE hbE ha1 hb1 hne
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : Nat.card E ≤ 2 := by
      rw [hn]
      interval_cases n <;> simp
    omega
  exact hn2.trans (CFSG.SectionRank.le_pRank one_lt_two hEH hEel hn)

theorem two_le_pRank_inf_centralizer {P : Subgroup G} (hP : IsPGroup 2 P)
    (hrank : 2 ≤ CFSG.Open.pRank 2 P) {c : G} (hcP : c ∈ P) (hc1 : c ≠ 1) (hc2 : c * c = 1) :
    2 ≤ CFSG.Open.pRank 2 (P ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have : Nontrivial ↥P := ⟨⟨⟨c, hcP⟩, 1, fun h => hc1 (congrArg Subtype.val h)⟩⟩
  have hcn := hP.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  have hzP : (z : G) ∈ P := z.2
  have hz1' : (z : G) ≠ 1 := fun e => hz1 (Subtype.ext (Subtype.ext e))
  obtain ⟨n, hn⟩ := exists_pow_orderOf_two hP hzP hz1'
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : G, z₀ = (z : G) ^ n := ⟨_, rfl⟩
  rw [← hz₀] at hn
  have hz₀P : z₀ ∈ P := by rw [hz₀]; exact P.pow_mem hzP n
  have hz₀2 : z₀ * z₀ = 1 := mul_self_eq_one_of_orderOf_eq_two hn
  have hz₀1 : z₀ ≠ 1 := fun e => by
    rw [e, orderOf_one] at hn
    omega
  have hz₀c : ∀ p ∈ P, p * z₀ = z₀ * p := by
    intro p hp
    have := Subgroup.mem_center_iff.1 ((Subgroup.center ↥P).pow_mem hzc n) ⟨p, hp⟩
    rw [hz₀]
    simpa using congrArg Subtype.val this
  by_cases hzcx : z₀ = c
  · have hle : P ≤ P ⊓ Subgroup.centralizer ({c} : Set G) := by
      intro p hp
      refine ⟨hp, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hzcx]
      exact hz₀c p hp
    exact hrank.trans (CFSG.SectionRank.pRank_mono one_lt_two hle)
  · exact two_le_pRank_of_pair hc2 hz₀2 (hz₀c c hcP) hc1 hz₀1 (Ne.symm hzcx)
      ⟨hcP, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
      ⟨hz₀P, Subgroup.mem_centralizer_singleton_iff.2 (hz₀c c hcP).symm⟩

theorem exists_two_ne_one {E : Subgroup G} (h : 3 ≤ Nat.card E) :
    ∃ a ∈ E, ∃ a' ∈ E, a ≠ 1 ∧ a' ≠ 1 ∧ a ≠ a' := by
  by_contra hno
  push Not at hno
  have hne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h
    omega
  obtain ⟨y₁', hy₁'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hy₁ : (y₁' : G) ∈ E := y₁'.2
  have hy₁1 : (y₁' : G) ≠ 1 := fun e => hy₁' (Subtype.ext e)
  have hsub : (E : Set G) ⊆ {1, (y₁' : G)} := by
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    · have := hno (y₁' : G) hy₁ y hy hy₁1 hy1
      simp [this]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, (y₁' : G)} : Set G).ncard ≤ 2 := by
    calc ({1, (y₁' : G)} : Set G).ncard ≤ ({(y₁' : G)} : Set G).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  rw [← Nat.card_coe_set_eq] at h1
  change Nat.card E ≤ _ at h1
  omega

theorem isPGroup_le_of_fixedOnlyElt {H P : Subgroup G} (hP : IsPGroup 2 P) {a : G} (haP : a ∈ P)
    (h : FixedOnlyElt H a) : P ≤ H := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  set W : Subgroup ↥P := (H ⊓ P).subgroupOf P with hW
  by_cases htop : W = ⊤
  · intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ W := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.mp this).1
  · exfalso
    have hlt : W < Subgroup.normalizer (W : Set ↥P) := hnc W (lt_top_iff_ne_top.mpr htop)
    obtain ⟨u, hun, huW⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hlt).2
    have haW : (⟨a, haP⟩ : ↥P) ∈ W := Subgroup.mem_subgroupOf.mpr ⟨h.1, haP⟩
    have h1 : u⁻¹ * ⟨a, haP⟩ * u ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (W : Set ↥P)).inv_mem hun) ⟨a, haP⟩).mp haW
      simpa using this
    have h2 : (u : G)⁻¹ * a * u ∈ H := (Subgroup.mem_subgroupOf.mp h1).1
    exact huW (Subgroup.mem_subgroupOf.mpr ⟨h.2 (u : G) h2, u.2⟩)

theorem exists_comm_of_normalizes {A : Subgroup G} {t : G} (hA : A ≠ ⊥)
    (ht : t ∈ Subgroup.normalizer (A : Set G))
    (hQ : IsPGroup 2 (Subgroup.zpowers t ⊔ A : Subgroup G)) :
    ∃ a ∈ A, a ≠ 1 ∧ a * t = t * a := by
  set Q : Subgroup G := Subgroup.zpowers t ⊔ A with hQdef
  have hnorm : (A.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer ((Subgroup.zpowers_le).2 ht)
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hne : A.subgroupOf Q ≠ ⊥ := by
    intro h0
    apply hA
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ Q := (le_sup_right : A ≤ Subgroup.zpowers t ⊔ A) hx
    have : (⟨x, hxQ⟩ : ↥Q) ∈ A.subgroupOf Q := Subgroup.mem_subgroupOf.2 hx
    rw [h0, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simp at this
    exact Subgroup.mem_bot.2 this
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  obtain ⟨hxA, hxZ⟩ := Subgroup.mem_inf.1 hx
  have htQ : t ∈ Q := (le_sup_left : Subgroup.zpowers t ≤ Subgroup.zpowers t ⊔ A) (Subgroup.mem_zpowers t)
  refine ⟨(x : G), Subgroup.mem_subgroupOf.1 hxA, ?_, ?_⟩
  · intro e
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    exact e
  · have := Subgroup.mem_center_iff.1 hxZ ⟨t, htQ⟩
    simpa using congrArg Subtype.val this.symm

theorem exists_sylow_le_of_isPGroup (K W : Subgroup G) (hWK : W ≤ K) (hW : IsPGroup 2 W) :
    ∃ P : Subgroup G, P ≤ K ∧ W ≤ P ∧ IsPGroup 2 P ∧ ¬ 2 ∣ P.relIndex K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 ↥(W.subgroupOf K) := hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  obtain ⟨P', hP'⟩ := hW'.exists_le_sylow
  refine ⟨(P' : Subgroup ↥K).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hWK hx⟩, hP' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · exact P'.isPGroup'.map K.subtype
  · have e : ((P' : Subgroup ↥K).map K.subtype).relIndex K = (P' : Subgroup ↥K).index := by
      show (((P' : Subgroup ↥K).map K.subtype).comap K.subtype).index = _
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    rw [e]
    exact P'.not_dvd_index' (Subgroup.index_ne_zero_of_finite)

omit [Finite G] in
theorem centralizer_singleton_conj (u c : G) :
    Subgroup.centralizer ({c⁻¹ * u * c} : Set G) = conjugate (Subgroup.centralizer ({u} : Set G)) c := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c * x * c⁻¹ * u = c * (x * (c⁻¹ * u * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * u * c) * x) * c⁻¹ := by rw [h]
      _ = u * (c * x * c⁻¹) := by group
  · intro h
    calc x * (c⁻¹ * u * c) = c⁻¹ * ((c * x * c⁻¹) * u) * c := by group
      _ = c⁻¹ * (u * (c * x * c⁻¹)) * c := by rw [h]
      _ = (c⁻¹ * u * c) * x := by group

end More


section MoreFixed

theorem FixedOnlyElt.centralizer_le {H : Subgroup G} {a : G} (h : FixedOnlyElt H a) :
    Subgroup.centralizer ({a} : Set G) ≤ H := fun x hx => by
  have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  refine h.mem_of_conj_eq ?_
  calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
    _ = x⁻¹ * (x * a) := by rw [hxa]
    _ = a := by group

theorem relIndex_conjugate (P K : Subgroup G) (c : G) :
    (conjugate P c).relIndex (conjugate K c) = P.relIndex K := by
  unfold conjugate
  exact Subgroup.relIndex_map_map_of_injective P K (MulAut.conj c⁻¹).injective

theorem not_two_dvd_relIndex_inf_conjugate {S K P : Subgroup G} {c : G} (hPK : P ≤ K)
    (hPS : ∀ w ∈ P, c⁻¹ * w * c ∈ S) (hsyl : ¬ 2 ∣ P.relIndex K) :
    ¬ 2 ∣ (S ⊓ conjugate K c).relIndex (conjugate K c) := by
  have hle : conjugate P c ≤ S ⊓ conjugate K c := by
    intro y hy
    have hw : c * y * c⁻¹ ∈ P := mem_conjugate_iff.1 hy
    refine ⟨?_, mem_conjugate_iff.2 (hPK hw)⟩
    have := hPS _ hw
    rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at this
  have hmul := Subgroup.relIndex_mul_relIndex (conjugate P c) (S ⊓ conjugate K c)
    (conjugate K c) hle (inf_le_right : S ⊓ conjugate K c ≤ conjugate K c)
  rw [relIndex_conjugate] at hmul
  intro hd
  exact hsyl (hd.trans (Dvd.intro_left _ hmul))

end MoreFixed


section CoprimeGeneration

theorem isElementaryAbelian_of_isElemAbelian' {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    CFSG.IsElementaryAbelian 2 A := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA

theorem le_of_forall_inf_centralizer_le' [Finite G] {B V W : Subgroup G}
    (hB : CFSG.IsElementaryAbelian 2 B) (hBcard : 2 ^ 2 ≤ Nat.card B) (hpV : ¬ 2 ∣ Nat.card V)
    (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hle : ∀ b ∈ B, b ≠ 1 → V ⊓ Subgroup.centralizer ({b} : Set G) ≤ W) : V ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction B V := MulDistribMulAction.compHom V (Subgroup.inclusion hBV)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := B) (H := V) hBcard hpV
  have hle' : (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro v hv
    have hfix : a • v = v :=
      (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a v).mp hv
    have hc : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val hfix
    have hcomm : (v : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (v : G) * a = a * v * (a : G)⁻¹ * a := by rw [hc]
        _ = a * v := by group
    exact hle a a.2 (fun h => ha (Subtype.ext h)) ⟨v.2, hcomm⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈
      (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle' hmem

end CoprimeGeneration

end CFSG.Asc75
