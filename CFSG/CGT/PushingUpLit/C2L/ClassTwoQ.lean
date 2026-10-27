module

public import CFSG.CGT.PushingUpLit.T2KSW.ClassThreeWC

public section

namespace CFSG.CGT.PushingUpLit.C2L.ClassTwoQ

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement
open T2KSW.Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

structure TIRDSetup (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  sec4 : Sec4 G L M T n
  MN : M ≤ Subgroup.normalizer (L : Set G)
  ME : M ≤ Subgroup.normalizer (Ec L T : Set G)
  ne_bot : Ec L T ≠ ⊥
  facts : RDFacts L T

namespace TIRDSetup

variable (hc : TIRDSetup G L M T n)
include hc

theorem centralizer_le_M {x : G} (hx : x ∈ Ec L T) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hsq : x ^ 2 = 1 := hc.sec4.S_elem.2 x hx
  obtain ⟨N, hCN, hNmax⟩ :=
    RankThree.PartOne.Sec15Final.exists_isMaximalTwoLocal_ge
      (T2K.isPLocal_centralizer_of_sq hsq hx1)
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx.2 l hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun y hy => hCN (hLC hy)⟩
    rw [hc.sec4.hyp.unique] at this
    exact this
  rw [← hNM]
  exact hCN

theorem mem_M_of_map_conj_le {k : G} (hk : T.map (MulAut.conj k).toMonoidHom ≤ M) : k ∈ M := by
  have hP : IsPGroup 2 ↥(T.map (MulAut.conj k).toMonoidHom) := hc.sec4.sylow.isPGroup.map _
  obtain ⟨m, hm, hmT⟩ := T2K.exists_conj_le_of_isPGroup hc.sec4.sylow hP hk
  have e : (T.map (MulAut.conj k).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      T.map (MulAut.conj (m * k)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e] at hmT
  have hmk : m * k ∈ Subgroup.normalizer (T : Set G) :=
    T2K.mem_normalizer_of_map_conj_eq
      (Subgroup.eq_of_le_of_card_ge hmT (by rw [T2K.card_map_conj]))
  have := M.mul_mem (M.inv_mem hm) (hc.sec4.N_T hmk)
  simpa using this

theorem conj_Ec_inf_ZT {g : G} (hg : g ∉ M) :
    (Ec L T).map (MulAut.conj g).toMonoidHom ⊓ ZT T = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyE, hyZ⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  replace hyE : g⁻¹ * y * g ∈ Ec L T := (T2K.mem_map_conj_iff g _ y).1 hyE
  have hx1 : g⁻¹ * y * g ≠ 1 := fun h => hy1 (by
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e, h]
    group)
  have hcent := hc.centralizer_le_M hyE hx1
  refine hg ?_
  have hginv : g⁻¹ ∈ M := hc.mem_M_of_map_conj_le (k := g⁻¹) fun w hw => by
    rw [T2K.mem_map_conj_iff, inv_inv] at hw
    apply hcent
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : w * (g⁻¹ * y * g) = g⁻¹ * ((g * w * g⁻¹) * y) * g := by group
    have e2 : (g⁻¹ * y * g) * w = g⁻¹ * (y * (g * w * g⁻¹)) * g := by group
    rw [e1, e2, (mem_ZT.1 hyZ).2 _ hw]
  simpa using M.inv_mem hginv

theorem Ec_inf_ZT_ne_bot : Ec L T ⊓ ZT T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hc.sec4.sylow.isPGroup.isNilpotent
  have hTE : T ≤ Subgroup.normalizer (Ec L T : Set G) := hc.sec4.sylow.le.trans hc.ME
  have : ((Ec L T).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hTE
  have hne : (Ec L T).subgroupOf T ≠ ⊥ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot
    intro h
    have hmem : (⟨x, hx.1⟩ : ↥T) ∈ (Ec L T).subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at hmem
    exact hx1 (Subtype.ext (by simpa using congrArg Subtype.val hmem))
  obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hmE : (m : G) ∈ Ec L T := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hm).1
  have hmZ : (m : G) ∈ ZT T := by
    refine mem_ZT.2 ⟨m.2, fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hm).2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨(m : G), hmE, hmZ⟩, fun h => hm1 ?_⟩
  exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

theorem exists_Q_of_not_weaklyClosed
    (hnwc : ∃ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T ∧
      (Ec L T).map (MulAut.conj g).toMonoidHom ≠ Ec L T) :
    ∃ Q : Subgroup G, Q ≤ T ∧ Ec L T ≤ Q ∧ ZT T ≤ Q ∧
      (∃ m ∈ Subgroup.normalizer (Q : Set G), m ∉ Subgroup.normalizer (Ec L T : Set G)) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q) ∧
      ∀ P : Subgroup G, P ≤ T →
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (P : Set G) → P ≤ Q ∨ P ⊔ Q = T := by
  obtain ⟨Q, hQT, hEQ, hCQ, hmove, hmax⟩ :=
    exists_good_Q T (Ec L T) hc.sec4.sylowG Ec_le_T hnwc
  have hZQ : ZT T ≤ Q := fun z hz =>
    hCQ ⟨Subgroup.mem_centralizer_iff.2 fun q hq => (mem_ZT.1 hz).2 q (hQT hq), (mem_ZT.1 hz).1⟩
  have hsup : ZR L T ⊔ Ec L T ≤ Q := sup_le (hc.facts.ZR_le.trans hZQ) hEQ
  have hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q := fun x hx y hy =>
    ⟨hsup (hc.facts.sq_mem x hx),
      hsup (hc.facts.comm_le (Subgroup.commutator_mem_commutator hx hy))⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Ec L T : Set G) :=
    hc.sec4.N_T.trans hc.ME
  obtain ⟨-, hTR⟩ := tr_of_good_Q_uniform hc.sec4.sylowG hQT hTQ hmove hmax hNT
  exact ⟨Q, hQT, hEQ, hZQ, hmove, hTQ, fun P hPT hNP => hTR P hPT (inf_le_right.trans hNP)⟩

theorem false_of_Rl_le_Q {Q : Subgroup G} (hQT : Q ≤ T) (hZQ : ZT T ≤ Q)
    (hmove : ∃ m ∈ Subgroup.normalizer (Q : Set G), m ∉ Subgroup.normalizer (Ec L T : Set G))
    (hRQ : Rl L T ≤ Q) : False := by
  obtain ⟨m, hmQ, hmE⟩ := hmove
  have hmM : m ∉ M := fun h => hmE (hc.ME h)
  set A : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  set E₁ : Subgroup G := Ec L T ⊓ A
  set Z : Subgroup G := ZT T
  have hZA : Z ≤ A := fun z hz =>
    ⟨hZQ hz, Subgroup.mem_centralizer_iff.2 fun q hq => (mem_ZT.1 hz).2 q (hQT hq)⟩
  have hTE : T ≤ Subgroup.normalizer (Ec L T : Set G) := hc.sec4.sylow.le.trans hc.ME
  have hZRE : ZR L T ≤ Subgroup.normalizer (Ec L T : Set G) :=
    (ZR_le_Rl.trans Rl_le_T).trans hTE
  have hAZE : A ≤ Z ⊔ E₁ := by
    intro a ha
    have haC : a ∈ T ⊓ Subgroup.centralizer (Rl L T : Set G) :=
      ⟨hQT ha.1, Subgroup.mem_centralizer_iff.2 fun r hr =>
        Subgroup.mem_centralizer_iff.1 ha.2 r (hRQ hr)⟩
    obtain ⟨z, hz, e, he, rfl⟩ := (mem_sup_iff_mul hZRE).1 (hc.facts.cent_R_le haC)
    have hzZ : z ∈ Z := hc.facts.ZR_le hz
    have heA : e ∈ A := by
      have := A.mul_mem (A.inv_mem (hZA hzZ)) ha
      simpa using this
    exact (Z ⊔ E₁).mul_mem (Subgroup.mem_sup_left hzZ) (Subgroup.mem_sup_right ⟨he, heA⟩)
  set F : Subgroup G := E₁.map (MulAut.conj m).toMonoidHom
  have hFA : F ≤ A := by
    rintro _ ⟨e, he, rfl⟩
    have hmQ' : ∀ q ∈ Q, m⁻¹ * q * m ∈ Q := fun q hq => by
      have :=
        (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Q : Set G)).inv_mem hmQ) q).1 hq
      simpa using this
    refine ⟨(Subgroup.mem_normalizer_iff.1 hmQ e).1 he.2.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro q hq
    have h1 : e * (m⁻¹ * q * m) = (m⁻¹ * q * m) * e :=
      (Subgroup.mem_centralizer_iff.1 he.2.2 _ (hmQ' q hq)).symm
    have e1 : q * (MulAut.conj m).toMonoidHom e = m * ((m⁻¹ * q * m) * e) * m⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (MulAut.conj m).toMonoidHom e * q = m * (e * (m⁻¹ * q * m)) * m⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, e2, h1]
  have hFZ : Z ⊓ F = ⊥ := by
    rw [eq_bot_iff, ← hc.conj_Ec_inf_ZT hmM, inf_comm]
    exact inf_le_inf (Subgroup.map_mono (inf_le_left : E₁ ≤ Ec L T)) le_rfl
  have hcentZ : ∀ f ∈ A, f ∈ Subgroup.normalizer (Z : Set G) := fun f hf =>
    Subgroup.centralizer_le_normalizer (Z : Set G) (Subgroup.mem_centralizer_iff.2 fun z hz =>
      Subgroup.mem_centralizer_iff.1 hf.2 z (hZQ hz))
  have c1 := card_sup_mul_card_inf_of_le_normalizer (fun f hf => hcentZ f (hFA hf))
  have c2 := card_sup_mul_card_inf_of_le_normalizer
    (A := Z) (B := E₁) (fun f hf => hcentZ f hf.2)
  rw [hFZ, Subgroup.card_bot, mul_one] at c1
  have hF_card : Nat.card F = Nat.card E₁ := T2K.card_map_conj E₁ m
  have hle : Nat.card (Z ⊔ F : Subgroup G) ≤ Nat.card (Z ⊔ E₁ : Subgroup G) :=
    Subgroup.card_le_of_le ((sup_le hZA hFA).trans hAZE)
  have hpos : 0 < Nat.card (Z ⊔ E₁ : Subgroup G) := Nat.card_pos
  have hZE : Nat.card (Z ⊓ E₁ : Subgroup G) = 1 := by
    have h3 : Nat.card ↥(Z ⊔ E₁) * Nat.card ↥(Z ⊓ E₁) ≤ Nat.card ↥(Z ⊔ E₁) * 1 := by
      rw [mul_one, c2, ← hF_card, ← c1]
      exact hle
    have h4 : Nat.card ↥(Z ⊓ E₁) ≤ 1 := Nat.le_of_mul_le_mul_left h3 hpos
    have h5 : 0 < Nat.card ↥(Z ⊓ E₁) := Nat.card_pos
    omega
  have hbot : Z ⊓ E₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ hZE
  refine hc.Ec_inf_ZT_ne_bot (eq_bot_iff.2 fun x hx => ?_)
  have hx' : x ∈ Z ⊓ E₁ := ⟨hx.2, hx.1, hZA hx.2⟩
  rw [hbot] at hx'
  exact hx'

end TIRDSetup

omit [Finite G] in
theorem centralizes_of_normal_of_inf_center {T Q E' : Subgroup G} (hT : ClassLETwo T)
    (hQ : Q ≤ T) (hE : E' ≤ Q) (hn : ∀ q ∈ Q, ∀ e ∈ E', q * e * q⁻¹ ∈ E')
    (hZ : ∀ x ∈ E', (∀ t ∈ T, x * t = t * x) → x = 1) :
    ∀ q ∈ Q, ∀ e ∈ E', q * e = e * q := by
  intro q hq e he
  have h1 : ⁅e, q⁆ ∈ E' := by
    have h := E'.mul_mem he (E'.inv_mem (hn q hq e he))
    have : ⁅e, q⁆ = e * (q * e * q⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact h
  have h2 : ∀ t ∈ T, ⁅e, q⁆ * t = t * ⁅e, q⁆ := by
    intro t ht
    have h3 : ⁅⁅e, q⁆, t⁆ = 1 := hT e (hQ (hE he)) q (hQ hq) t ht
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have h4 : ⁅e, q⁆ = 1 := hZ _ h1 h2
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm

theorem classTwo_Q_facts (hc : TIRDSetup G L M T n)
    (hcl : ClassLETwo T)
    (hnwc : ∃ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T ∧
      (Ec L T).map (MulAut.conj g).toMonoidHom ≠ Ec L T) :
    ∃ Q : Subgroup G, Q ≤ T ∧ Ec L T ≤ Q ∧ ZT T ≤ Q ∧
      (∃ m ∈ Subgroup.normalizer (Q : Set G), m ∉ Subgroup.normalizer (Ec L T : Set G)) ∧
      (∀ P : Subgroup G, P ≤ T →
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (P : Set G) → P ≤ Q ∨ P ⊔ Q = T) ∧
      ¬ Rl L T ≤ Q ∧ Rl L T ⊔ Q = T ∧ Ec L T ≤ ZT T ∧
      (∀ a ∈ Subgroup.normalizer (Q : Set G), a ∉ M →
        ∀ q ∈ Q, ∀ e ∈ (Ec L T).map (MulAut.conj a).toMonoidHom, q * e = e * q) := by
  obtain ⟨Q, hQT, hEQ, hZQ, hmove, hTQ, hTR⟩ := hc.exists_Q_of_not_weaklyClosed hnwc
  have hRQ : ¬ Rl L T ≤ Q := fun h => hc.false_of_Rl_le_Q hQT hZQ hmove h
  have hTN : T ≤ Subgroup.normalizer (Q : Set G) :=
    ClassThree.le_normalizer_of_comm_mem hQT fun x hx y hy => (hTQ x hx y hy).2
  have hNR : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Rl L T : Set G) :=
    fun m hm => mem_normalizer_Rl hc.MN (hc.sec4.N_T hm) hm
  have hRQT : Rl L T ⊔ Q = T := (hTR _ Rl_le_T hNR).resolve_left hRQ
  have hTE : T ≤ Subgroup.normalizer (Ec L T : Set G) := hc.sec4.sylow.le.trans hc.ME
  have hcent : ∀ a ∈ Subgroup.normalizer (Q : Set G), a ∉ M →
      ∀ q ∈ Q, ∀ e ∈ (Ec L T).map (MulAut.conj a).toMonoidHom, q * e = e * q := by
    intro a ha haM
    have hQa : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx => (Subgroup.mem_normalizer_iff.1 ha x).1 hx
    have hQa' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := fun x hx => by
      have :=
        (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Q : Set G)).inv_mem ha) x).1 hx
      simpa using this
    refine centralizes_of_normal_of_inf_center hcl hQT ?_ ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact hQa e (hEQ he)
    · rintro q hq _ ⟨e, he, rfl⟩
      refine ⟨(a⁻¹ * q * a) * e * (a⁻¹ * q * a)⁻¹, ?_, ?_⟩
      · have hq' : a⁻¹ * q * a ∈ T := hQT (hQa' q hq)
        have := (Subgroup.mem_normalizer_iff.1 (hTE hq') e).1 he
        exact this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · intro x hx hxc
      have hxT : x ∈ T := by
        obtain ⟨e, he, rfl⟩ := hx
        exact hQT (hQa e (hEQ he))
      have hxZ : x ∈ ZT T := mem_ZT.2 ⟨hxT, fun t ht => (hxc t ht).symm⟩
      have : x ∈ (Ec L T).map (MulAut.conj a).toMonoidHom ⊓ ZT T := ⟨hx, hxZ⟩
      rw [hc.conj_Ec_inf_ZT haM] at this
      exact Subgroup.mem_bot.1 this
  refine ⟨Q, hQT, hEQ, hZQ, hmove, hTR, hRQ, hRQT, ?_, hcent⟩
  obtain ⟨a, haQ, haE⟩ := hmove
  have haM : a ∉ M := fun h => haE (hc.ME h)
  intro e he
  have hQe : ∀ q ∈ Q, q * e = e * q := by
    intro q hq
    have hQa : a * q * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 haQ q).1 hq
    have h1 := hcent a haQ haM (a * q * a⁻¹) hQa (a * e * a⁻¹) ⟨e, he, rfl⟩
    have e1 : q * e = a⁻¹ * ((a * q * a⁻¹) * (a * e * a⁻¹)) * a := by group
    have e2 : e * q = a⁻¹ * ((a * e * a⁻¹) * (a * q * a⁻¹)) * a := by group
    rw [e1, e2, h1]
  refine mem_ZT.2 ⟨Ec_le_T he, fun t ht => ?_⟩
  obtain ⟨r, hr, q, hq, rfl⟩ := (mem_sup_iff_mul (Rl_le_T.trans hTN)).1 (hRQT.ge ht)
  have h1 : r * e = e * r := Subgroup.mem_centralizer_iff.1 he.2 r (Rl_le_L hr)
  calc (r * q) * e = r * (q * e) := by group
    _ = r * (e * q) := by rw [hQe q hq]
    _ = (r * e) * q := by group
    _ = (e * r) * q := by rw [h1]
    _ = e * (r * q) := by group

end CFSG.CGT.PushingUpLit.C2L.ClassTwoQ
