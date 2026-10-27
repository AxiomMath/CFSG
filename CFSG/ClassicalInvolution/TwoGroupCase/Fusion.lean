module

public import CFSG.ClassicalInvolution.TwoGroupCase.TightPair
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def oddCoreImg (R : Subgroup G) : Subgroup G := (oddCore R).map R.subtype

theorem oddCoreImg_le (R : Subgroup G) : oddCoreImg R ≤ R := Subgroup.map_subtype_le _

theorem odd_natCard_oddCoreImg [Finite G] (R : Subgroup G) : Odd (Nat.card (oddCoreImg R)) := by
  rw [oddCoreImg, Subgroup.card_map_of_injective R.subtype_injective]
  exact QuaternionStructure.odd_natCard_oddCore R

theorem natCard_oddCoreImg (R : Subgroup G) : Nat.card (oddCoreImg R) = Nat.card (oddCore R) :=
  Subgroup.card_map_of_injective R.subtype_injective

theorem conj_mem_oddCoreImg [Finite G] {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {o : G} (ho : o ∈ oddCoreImg R) :
    g * o * g⁻¹ ∈ oddCoreImg R := by
  obtain ⟨o', ho', rfl⟩ := ho
  let α : MulAut R := Subgroup.normalizerMonoidHom R ⟨g, hg⟩
  have hchar : (oddCore R).Characteristic := by
    rw [QuaternionStructure.oddCore_eq_pPrimeCore_two]
    infer_instance
  have hα : α o' ∈ oddCore R := by
    have := Subgroup.characteristic_iff_map_eq.mp hchar α
    rw [← this]
    exact ⟨o', ho', rfl⟩
  exact ⟨α o', hα, rfl⟩

theorem exists_conj_of_sylow {X : Type*} [Group X] [Finite X] (P Q : Sylow 2 X) :
    ∃ g : X, (Q : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [MulAut.smul_def]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [MulAut.smul_def]⟩

theorem IsSylow2Of.exists_conj [Finite G] {P Q A : Subgroup G} (hP : IsSylow2Of P A)
    (hQ : IsSylow2Of Q A) : ∃ a ∈ A, Q = conjSubgroup a P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, rfl⟩ := hP.exists_sylow
  obtain ⟨T₂, rfl⟩ := hQ.exists_sylow
  obtain ⟨g, hg⟩ := exists_conj_of_sylow T₁ T₂
  refine ⟨g, g.2, ?_⟩
  rw [hg, Subgroup.map_map]
  show _ = Subgroup.map (MulAut.conj (g : G)).toMonoidHom (Subgroup.map A.subtype (T₁ : Subgroup A))
  rw [Subgroup.map_map]
  congr 1

section Quotients

variable {A B N D : Subgroup G}

theorem surjective_ker_quotient [hNn : (N.subgroupOf B).Normal] (hAB : A ≤ B)
    (hfac : ∀ b ∈ B, ∃ a ∈ A, ∃ n ∈ N, b = a * n) :
    ∃ φ : A →* B ⧸ N.subgroupOf B, (∀ a : A, φ a = QuotientGroup.mk (Subgroup.inclusion hAB a)) ∧
      Function.Surjective φ ∧ φ.ker = (A ⊓ N).subgroupOf A := by
  refine ⟨(QuotientGroup.mk' (N.subgroupOf B)).comp (Subgroup.inclusion hAB), fun _ => rfl, ?_, ?_⟩
  · intro q
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, n, hn', rfl⟩ := hfac b hb
    refine ⟨⟨a, ha⟩, ?_⟩
    show (QuotientGroup.mk (⟨a, hAB ha⟩ : B)) = QuotientGroup.mk ⟨a * n, hb⟩
    rw [QuotientGroup.eq]
    show ((a⁻¹ * (a * n) : G)) ∈ N
    simpa using hn'
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk (⟨(x : G), hAB x.2⟩ : B) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem exists_mulEquiv_quotient [hNn : (N.subgroupOf B).Normal] [(D.subgroupOf A).Normal]
    (hAB : A ≤ B) (hD : A ⊓ N = D) (hfac : ∀ b ∈ B, ∃ a ∈ A, ∃ n ∈ N, b = a * n) :
    ∃ e : (A ⧸ D.subgroupOf A) ≃* (B ⧸ N.subgroupOf B),
      ∀ a : A, e (QuotientGroup.mk a) = QuotientGroup.mk (Subgroup.inclusion hAB a) := by
  obtain ⟨φ, hφa, hφ, hker⟩ := surjective_ker_quotient (N := N) hAB hfac
  rw [hD] at hker
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ), fun a => ?_⟩
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact hφa a

theorem natCard_mul_natCard_inf [Finite G] [hNn : (N.subgroupOf B).Normal] (hAB : A ≤ B)
    (hNB : N ≤ B) (hfac : ∀ b ∈ B, ∃ a ∈ A, ∃ n ∈ N, b = a * n) :
    Nat.card B * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  obtain ⟨φ, -, hφ, hker⟩ := surjective_ker_quotient (N := N) hAB hfac
  have e := (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf B)
  have h3 : Nat.card φ.ker = Nat.card (A ⊓ N : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h4 : Nat.card (N.subgroupOf B) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  rw [Nat.card_congr e, h3] at h1
  rw [h4] at h2
  rw [h2, h1]
  ring

theorem relIndex_eq_relIndex_inf [Finite G] [(N.subgroupOf B).Normal] (hAB : A ≤ B) (hNB : N ≤ B)
    (hfac : ∀ b ∈ B, ∃ a ∈ A, ∃ n ∈ N, b = a * n) :
    A.relIndex B = (A ⊓ N).relIndex N := by
  have h := natCard_mul_natCard_inf (N := N) hAB hNB hfac
  have h1 : Nat.card A * A.relIndex B = Nat.card B := by
    have := Subgroup.card_mul_index (A.subgroupOf B)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at this
  have h2 : Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N = Nat.card N := by
    have := Subgroup.card_mul_index ((A ⊓ N).subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at this
  have hA : 0 < Nat.card A := Nat.card_pos
  have hD : 0 < Nat.card (A ⊓ N : Subgroup G) := Nat.card_pos
  have key : Nat.card A * Nat.card (A ⊓ N : Subgroup G) * A.relIndex B =
      Nat.card A * Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N := by
    calc Nat.card A * Nat.card (A ⊓ N : Subgroup G) * A.relIndex B
        = Nat.card (A ⊓ N : Subgroup G) * (Nat.card A * A.relIndex B) := by ring
      _ = Nat.card (A ⊓ N : Subgroup G) * Nat.card B := by rw [h1]
      _ = Nat.card A * Nat.card N := by rw [mul_comm]; exact h
      _ = Nat.card A * (Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N) := by rw [h2]
      _ = Nat.card A * Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hA hD) key

end Quotients

structure OddByQuat (R S : Subgroup G) (t : G) : Prop where
  sylow : IsSylow2Of S R
  t_mem : t ∈ S
  t_ord : orderOf t = 2
  unique : ∀ x ∈ S, orderOf x = 2 → x = t
  le_C : R ≤ Subgroup.centralizer ({t} : Set G)
  normal : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (R : Set G)
  two : IsPGroup 2 (R ⧸ oddCore R)

namespace OddByQuat

variable [Finite G] {R S : Subgroup G} {t : G} (d : OddByQuat R S t)
include d

omit [Finite G] in
theorem S_le : S ≤ R := d.sylow.1

omit [Finite G] in
theorem S_two : IsPGroup 2 S := d.sylow.2.1

omit [Finite G] in
theorem t_mem_of_ne_bot {P : Subgroup G} (hPS : P ≤ S) (hP1 : P ≠ ⊥) : t ∈ P := by
  obtain ⟨x, hxP, hx⟩ := exists_mem_orderOf_eq_two_of_isPGroup_subgroup (d.S_two.to_le hPS) hP1
  exact d.unique x (hPS hxP) hx ▸ hxP

theorem conj_mem_O {h : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G)) {o : G}
    (ho : o ∈ oddCoreImg R) : h * o * h⁻¹ ∈ oddCoreImg R :=
  conj_mem_oddCoreImg (d.normal hh) ho

omit [Finite G] in
theorem O_le_C : oddCoreImg R ≤ Subgroup.centralizer ({t} : Set G) :=
  (oddCoreImg_le R).trans d.le_C

omit [Finite G] in
theorem commute_t_O {o : G} (ho : o ∈ oddCoreImg R) : t * o = o * t := by
  exact Subgroup.mem_centralizer_iff.mp (d.O_le_C ho) t rfl

theorem inf_O_S : oddCoreImg R ⊓ S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := d.S_two.exists_card_eq
  have hcop : (Nat.card S).Coprime (Nat.card (oddCoreImg R)) := by
    rw [hm]
    exact (Nat.coprime_two_left.mpr (odd_natCard_oddCoreImg R)).pow_left m
  have hdisj : Disjoint S (oddCoreImg R) := Subgroup.disjoint_of_coprime_natCard hcop
  rw [inf_comm]
  exact disjoint_iff.mp hdisj

theorem conj_eq_of_mem {o x : G} (ho : o ∈ oddCoreImg R) (hx : x ∈ S) (hox : o * x * o⁻¹ ∈ S) :
    o * x * o⁻¹ = x := by
  have h1 : (o * x * o⁻¹) * x⁻¹ ∈ oddCoreImg R := by
    have e : (o * x * o⁻¹) * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
    rw [e]
    refine (oddCoreImg R).mul_mem ho ?_
    have := conj_mem_oddCoreImg (Subgroup.le_normalizer (d.S_le hx)) ((oddCoreImg R).inv_mem ho)
    exact this
  have h2 : (o * x * o⁻¹) * x⁻¹ ∈ S := S.mul_mem hox (S.inv_mem hx)
  have h3 : (o * x * o⁻¹) * x⁻¹ ∈ oddCoreImg R ⊓ S := ⟨h1, h2⟩
  rw [d.inf_O_S, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

theorem natCard_R : Nat.card R = Nat.card (oddCoreImg R) * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := d.two.exists_card_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore R)
  rw [hk, ← natCard_oddCoreImg] at h1
  have h2 := d.sylow.card_eq
  rw [h1, mul_comm, two_pow_factorization_mul (Nat.card_pos).ne'] at h2
  have h3 : (Nat.card (oddCoreImg R)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (by simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr (odd_natCard_oddCoreImg R)))
  rw [h3] at h2
  rw [h2, h1, mul_comm]
  simp

theorem exists_mul_O_S : ∀ x ∈ R, ∃ o ∈ oddCoreImg R, ∃ s ∈ S, x = o * s :=
  exists_mul_of_natCard_eq (oddCoreImg_le R) d.S_le d.inf_O_S d.natCard_R

theorem exists_mul_S_O : ∀ x ∈ R, ∃ s ∈ S, ∃ o ∈ oddCoreImg R, x = s * o := by
  intro x hx
  obtain ⟨o, ho, s, hs, hxe⟩ := d.exists_mul_O_S x⁻¹ (R.inv_mem hx)
  refine ⟨s⁻¹, S.inv_mem hs, o⁻¹, (oddCoreImg R).inv_mem ho, ?_⟩
  have : x = (x⁻¹)⁻¹ := (inv_inv x).symm
  rw [this, hxe]
  group

theorem bijective_restrict :
    Function.Bijective ((QuotientGroup.mk' (oddCore R)).comp (Subgroup.inclusion d.S_le)) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (Subgroup.inclusion d.S_le x : R) ∈ oddCore R := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : G) ∈ oddCoreImg R ⊓ S := ⟨⟨_, h1, rfl⟩, x.2⟩
    rw [d.inf_O_S, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  · intro q
    obtain ⟨⟨r, hr⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, o, ho, rfl⟩ := d.exists_mul_S_O r hr
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk (⟨s, d.S_le hs⟩ : R) : R ⧸ oddCore R) = QuotientGroup.mk ⟨s * o, hr⟩
    rw [QuotientGroup.eq]
    obtain ⟨o', ho', rfl⟩ := ho
    have : ((⟨s, d.S_le hs⟩ : R)⁻¹ * ⟨s * R.subtype o', hr⟩ : R) = o' := by
      apply Subtype.ext
      simp
    rw [this]
    exact ho'

omit [Finite G] in
theorem M_le_C {m : G} (hm : m ∈ Subgroup.normalizer (S : Set G)) :
    m ∈ Subgroup.centralizer ({t} : Set G) := by
  have h1 : m * t * m⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hm t).mp d.t_mem
  have h2 : orderOf (m * t * m⁻¹) = 2 := by
    have := (MulAut.conj m).orderOf_eq t
    rw [MulAut.conj_apply] at this
    rw [this]
    exact d.t_ord
  have h3 : m * t * m⁻¹ = t := d.unique _ h1 h2
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  calc h * m = (m * h * m⁻¹) * m := by rw [h3]
    _ = m * h := by group

theorem exists_mul_M_O {h : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ m ∈ Subgroup.normalizer (S : Set G), ∃ o ∈ oddCoreImg R, h = m * o := by
  have hS' : IsSylow2Of (conjSubgroup h S) R := by
    have := d.sylow.conj h
    rwa [conjSubgroup_eq_self_iff.mpr (d.normal hh)] at this
  obtain ⟨r, hr, hrS⟩ := d.sylow.exists_conj hS'
  have hm : r⁻¹ * h ∈ Subgroup.normalizer (S : Set G) := by
    rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_conjSubgroup, hrS, conjSubgroup_conjSubgroup,
      inv_mul_cancel, conjSubgroup_one]
  obtain ⟨s, hs, o, ho, hro⟩ := d.exists_mul_S_O r hr
  have hmH : r⁻¹ * h ∈ Subgroup.centralizer ({t} : Set G) := d.M_le_C hm
  refine ⟨s * (r⁻¹ * h), ?_, (r⁻¹ * h)⁻¹ * o * (r⁻¹ * h), ?_, ?_⟩
  · exact (Subgroup.normalizer (S : Set G)).mul_mem (Subgroup.le_normalizer hs) hm
  · have := d.conj_mem_O ((Subgroup.centralizer ({t} : Set G)).inv_mem hmH) ho
    simpa [mul_assoc] using this
  · calc h = r * (r⁻¹ * h) := by group
      _ = s * o * (r⁻¹ * h) := by rw [← hro]
      _ = s * (r⁻¹ * h) * ((r⁻¹ * h)⁻¹ * o * (r⁻¹ * h)) := by group

theorem exists_mul_O_M {h : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ o ∈ oddCoreImg R, ∃ m ∈ Subgroup.normalizer (S : Set G), h = o * m := by
  obtain ⟨m, hm, o, ho, he⟩ := d.exists_mul_M_O ((Subgroup.centralizer ({t} : Set G)).inv_mem hh)
  refine ⟨o⁻¹, (oddCoreImg R).inv_mem ho, m⁻¹, (Subgroup.normalizer (S : Set G)).inv_mem hm, ?_⟩
  have : h = (h⁻¹)⁻¹ := (inv_inv h).symm
  rw [this, he]
  group

theorem inf_O_M : oddCoreImg R ⊓ Subgroup.normalizer (S : Set G) =
    oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) := by
  ext o
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨ho, ?_⟩
    show o ∈ Subgroup.centralizer (S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : o * x * o⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hm x).mp hx
    have h2 := d.conj_eq_of_mem ho hx h1
    calc x * o = (o * x * o⁻¹) * o := by rw [h2]
      _ = o * x := by group
  · rintro ⟨ho, hc⟩
    exact ⟨ho, Subgroup.centralizer_le_normalizer _ hc⟩

theorem M_le_normalizer_D : Subgroup.normalizer (S : Set G) ≤
    Subgroup.normalizer
      ((oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun m hm o ho => ?_
  refine ⟨d.conj_mem_O (d.M_le_C hm) ho.1, ?_⟩
  show m * o * m⁻¹ ∈ Subgroup.centralizer (S : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxm : m⁻¹ * x * m ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem hm) x).mp hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp ho.2 _ hxm
  calc x * (m * o * m⁻¹) = m * ((m⁻¹ * x * m) * o) * m⁻¹ := by group
    _ = m * (o * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
    _ = (m * o * m⁻¹) * x := by group

theorem C_le_normalizer_O : Subgroup.centralizer ({t} : Set G) ≤
    Subgroup.normalizer ((oddCoreImg R : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun _ hh _ ho => d.conj_mem_O hh ho

theorem normal_O_subgroupOf :
    ((oddCoreImg R).subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer d.O_le_C).mpr d.C_le_normalizer_O

omit [Finite G] d in
theorem D_le_M :
    oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (S : Set G) :=
  fun _ hx => Subgroup.centralizer_le_normalizer _ hx.2

theorem normal_D_subgroupOf :
    ((oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
      (Subgroup.normalizer (S : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer D_le_M).mpr d.M_le_normalizer_D

theorem exists_mulEquiv_M_H
    [((oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
      (Subgroup.normalizer (S : Set G))).Normal]
    [((oddCoreImg R).subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal] :
    ∃ e : (Subgroup.normalizer (S : Set G) ⧸
        (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
          (Subgroup.normalizer (S : Set G))) ≃*
      (Subgroup.centralizer ({t} : Set G) ⧸
        (oddCoreImg R).subgroupOf (Subgroup.centralizer ({t} : Set G))),
      ∀ m : Subgroup.normalizer (S : Set G), e (QuotientGroup.mk m) =
        QuotientGroup.mk (Subgroup.inclusion (fun _ hm => d.M_le_C hm) m) :=
  exists_mulEquiv_quotient (A := Subgroup.normalizer (S : Set G))
    (B := Subgroup.centralizer ({t} : Set G)) (N := oddCoreImg R)
    (D := oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)) (fun _ hm => d.M_le_C hm)
    (by rw [inf_comm]; exact d.inf_O_M) fun _ hh => d.exists_mul_M_O hh

theorem relIndex_M_H :
    (Subgroup.normalizer (S : Set G)).relIndex (Subgroup.centralizer ({t} : Set G)) =
        (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).relIndex (oddCoreImg R) ∧
      Odd ((Subgroup.normalizer (S : Set G)).relIndex (Subgroup.centralizer ({t} : Set G))) := by
  have hn := d.normal_O_subgroupOf
  have h1 := relIndex_eq_relIndex_inf (A := Subgroup.normalizer (S : Set G))
    (B := Subgroup.centralizer ({t} : Set G)) (N := oddCoreImg R) (fun _ hm => d.M_le_C hm)
    d.O_le_C fun _ hh => d.exists_mul_M_O hh
  rw [inf_comm, d.inf_O_M] at h1
  refine ⟨h1, ?_⟩
  rw [h1]
  exact (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.relIndex_dvd_card _ _)

theorem exists_conj_eq_of_sylow {S' : Subgroup G} (hS' : IsSylow2Of S' R) :
    ∃ o ∈ oddCoreImg R, S' = conjSubgroup o S := by
  obtain ⟨a, ha, hS'a⟩ := d.sylow.exists_conj hS'
  obtain ⟨o, ho, s, hs, rfl⟩ := d.exists_mul_O_S a ha
  refine ⟨o, ho, ?_⟩
  rw [hS'a, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_self_of_mem hs]

theorem conj_eq_self_iff_mem {o : G} (ho : o ∈ oddCoreImg R) :
    conjSubgroup o S = S ↔ o ∈ oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) := by
  rw [conjSubgroup_eq_self_iff, ← d.inf_O_M]
  exact ⟨fun h => ⟨ho, h⟩, fun h => h.2⟩

theorem card_sylow : Nat.card {P : Subgroup G // IsSylow2Of P R} =
    (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).relIndex (oddCoreImg R) := by
  set O' := oddCoreImg R with hO'
  set D : Subgroup G := O' ⊓ Subgroup.centralizer (S : Set G) with hD
  have hsyl : ∀ o : O', IsSylow2Of (conjSubgroup (o : G) S) R := fun o => by
    have := d.sylow.conj (o : G)
    rwa [conjSubgroup_eq_self_of_mem (oddCoreImg_le R o.2)] at this
  let f : O' → {P : Subgroup G // IsSylow2Of P R} := fun o => ⟨conjSubgroup (o : G) S, hsyl o⟩
  have hf : ∀ a b : O', f a = f b ↔ a⁻¹ * b ∈ D.subgroupOf O' := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subtype.mk.injEq]
    have hab : (↑(a⁻¹ * b) : G) = (a : G)⁻¹ * b := rfl
    have hmem : (a : G)⁻¹ * b ∈ O' := O'.mul_mem (O'.inv_mem a.2) b.2
    have key : conjSubgroup (a : G) S = conjSubgroup (b : G) S ↔
        conjSubgroup ((a : G)⁻¹ * b) S = S := by
      constructor
      · intro h
        have := congrArg (conjSubgroup (a : G)⁻¹) h
        rw [conjSubgroup_inv_conjSubgroup, conjSubgroup_conjSubgroup] at this
        exact this.symm
      · intro h
        have := congrArg (conjSubgroup (a : G)) h
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left] at this
        exact this.symm
    rw [key, hab]
    exact d.conj_eq_self_iff_mem hmem
  let g : O' ⧸ D.subgroupOf O' → {P : Subgroup G // IsSylow2Of P R} :=
    Quotient.lift f fun a b hab => (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Bijective g := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      intro hxy
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hf _ _).mp hxy))
    · rintro ⟨P, hP⟩
      obtain ⟨o, ho, rfl⟩ := d.exists_conj_eq_of_sylow hP
      exact ⟨Quotient.mk _ ⟨o, ho⟩, rfl⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem inf_conj_eq_centralizer {o : G} (ho : o ∈ oddCoreImg R) :
    S ⊓ conjSubgroup o S = S ⊓ Subgroup.centralizer ({o} : Set G) := by
  ext x
  constructor
  · rintro ⟨hx, hxo⟩
    refine ⟨hx, ?_⟩
    have hxo' : x ∈ conjSubgroup o S := hxo
    rw [mem_conjSubgroup_iff] at hxo'
    have h1 := d.conj_eq_of_mem ((oddCoreImg R).inv_mem ho) hx (by simpa using hxo')
    have h2 : o⁻¹ * x * o = x := by simpa using h1
    show x ∈ Subgroup.centralizer ({o} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * x = h * (h⁻¹ * x * h) := by rw [h2]
      _ = x * h := by group
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, ?_⟩
    show x ∈ conjSubgroup o S
    rw [mem_conjSubgroup_iff]
    have hc := Subgroup.mem_centralizer_iff.mp hxc o rfl
    have : o⁻¹ * x * o = x := by
      calc o⁻¹ * x * o = o⁻¹ * (x * o) := by rw [mul_assoc]
        _ = o⁻¹ * (o * x) := by rw [hc]
        _ = x := by group
    rw [this]
    exact hx

omit [Finite G] in
theorem mem_C_of_conj_mem {g : G} (hg : g * t * g⁻¹ ∈ S) :
    g ∈ Subgroup.centralizer ({t} : Set G) := by
  have h2 : orderOf (g * t * g⁻¹) = 2 := by
    have := (MulAut.conj g).orderOf_eq t
    rw [MulAut.conj_apply] at this
    rw [this]
    exact d.t_ord
  have h3 : g * t * g⁻¹ = t := d.unique _ hg h2
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  calc h * g = (g * h * g⁻¹) * g := by rw [h3]
    _ = g * h := by group

omit [Finite G] in
theorem fusion_mem_C {P : Subgroup G} (hP1 : P ≠ ⊥) (hPS : P ≤ S) {g : G}
    (hg : conjSubgroup g P ≤ S) : g ∈ Subgroup.centralizer ({t} : Set G) :=
  d.mem_C_of_conj_mem (hg (mem_conjSubgroup_of_mem (d.t_mem_of_ne_bot hPS hP1)))

theorem fusion_factor {P : Subgroup G} (hPS : P ≤ S) {g : G} (hg : conjSubgroup g P ≤ S) {m o : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (ho : o ∈ oddCoreImg R) (hgmo : g = m * o) :
    (∀ p ∈ P, o * p = p * o) ∧ ∀ p ∈ P, g * p * g⁻¹ = m * p * m⁻¹ := by
  have key : ∀ p ∈ P, o * p * o⁻¹ = p := by
    intro p hp
    have h1 : g * p * g⁻¹ ∈ S := hg (mem_conjSubgroup_of_mem hp)
    have h2 : o * p * o⁻¹ ∈ S := by
      have e : o * p * o⁻¹ = m⁻¹ * (g * p * g⁻¹) * m := by rw [hgmo]; group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem hm)
        (g * p * g⁻¹)).mp h1
      simpa using this
    exact d.conj_eq_of_mem ho (hPS hp) h2
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · calc o * p = (o * p * o⁻¹) * o := by group
      _ = p * o := by rw [key p hp]
  · calc g * p * g⁻¹ = m * (o * p * o⁻¹) * m⁻¹ := by rw [hgmo]; group
      _ = m * p * m⁻¹ := by rw [key p hp]

theorem fusion {P : Subgroup G} (hP1 : P ≠ ⊥) (hPS : P ≤ S) {g : G} (hg : conjSubgroup g P ≤ S) :
    ∃ m ∈ Subgroup.normalizer (S : Set G), ∀ p ∈ P, g * p * g⁻¹ = m * p * m⁻¹ := by
  obtain ⟨m, hm, o, ho, hgmo⟩ := d.exists_mul_M_O (d.fusion_mem_C hP1 hPS hg)
  exact ⟨m, hm, (d.fusion_factor hPS hg hm ho hgmo).2⟩

section Local

variable {P : Subgroup G} (hP1 : P ≠ ⊥) (hPS : P ≤ S)
include hP1 hPS

omit [Finite G] in
theorem normalizer_le_C :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({t} : Set G) := fun _ hg =>
  d.fusion_mem_C hP1 hPS (by rw [conjSubgroup_eq_self_iff.mpr hg]; exact hPS)

theorem normalizer_le_normalizer_K : Subgroup.normalizer (P : Set G) ≤
    Subgroup.normalizer ((oddCoreImg R ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun g hg k hk => by
    refine ⟨d.conj_mem_O (d.normalizer_le_C hP1 hPS hg) hk.1, ?_⟩
    show g * k * g⁻¹ ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : g⁻¹ * p * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (P : Set G)).inv_mem hg) p).mp hp
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hk.2 _ hp'
    calc p * (g * k * g⁻¹) = g * ((g⁻¹ * p * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
      _ = (g * k * g⁻¹) * p := by group

omit hP1 in
theorem inf_K_M : (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) ⊓
    Subgroup.normalizer (S : Set G) = oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) := by
  ext x
  constructor
  · rintro ⟨⟨ho, _⟩, hm⟩
    have : x ∈ oddCoreImg R ⊓ Subgroup.normalizer (S : Set G) := ⟨ho, hm⟩
    rwa [d.inf_O_M] at this
  · rintro ⟨ho, hc⟩
    exact ⟨⟨ho, Subgroup.centralizer_le (fun y hy => hPS hy) hc⟩,
      Subgroup.centralizer_le_normalizer _ hc⟩

theorem factor_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    ∃ m ∈ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G),
      ∃ o ∈ oddCoreImg R ⊓ Subgroup.centralizer (P : Set G), g = m * o := by
  have hgS : conjSubgroup g P ≤ S := by rw [conjSubgroup_eq_self_iff.mpr hg]; exact hPS
  obtain ⟨m, hm, o, ho, hgmo⟩ := d.exists_mul_M_O (d.fusion_mem_C hP1 hPS hgS)
  obtain ⟨hoc, hact⟩ := d.fusion_factor hPS hgS hm ho hgmo
  refine ⟨m, ⟨hm, ?_⟩, o, ⟨ho, ?_⟩, hgmo⟩
  · show m ∈ Subgroup.normalizer (P : Set G)
    rw [← conjSubgroup_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSubgroup m P).ge
    rintro _ ⟨p, hp, rfl⟩
    show m * p * m⁻¹ ∈ P
    rw [← hact p hp]
    exact (Subgroup.mem_normalizer_iff.mp hg p).mp hp
  · show o ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hoc p hp).symm

theorem factor_centralizer {g : G} (hg : g ∈ Subgroup.centralizer (P : Set G)) :
    ∃ m ∈ Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G),
      ∃ o ∈ oddCoreImg R ⊓ Subgroup.centralizer (P : Set G), g = m * o := by
  have hgS : conjSubgroup g P ≤ S := by
    rw [conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hg)]
    exact hPS
  obtain ⟨m, hm, o, ho, hgmo⟩ := d.exists_mul_M_O (d.fusion_mem_C hP1 hPS hgS)
  obtain ⟨hoc, hact⟩ := d.fusion_factor hPS hgS hm ho hgmo
  refine ⟨m, ⟨hm, ?_⟩, o, ⟨ho, ?_⟩, hgmo⟩
  · show m ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 := hact p hp
    have h2 : g * p * g⁻¹ = p := by
      have := Subgroup.mem_centralizer_iff.mp hg p hp
      calc g * p * g⁻¹ = (g * p) * g⁻¹ := rfl
        _ = (p * g) * g⁻¹ := by rw [← this]
        _ = p := by group
    rw [h2] at h1
    calc p * m = (m * p * m⁻¹) * m := by rw [← h1]
      _ = m * p := by group
  · show o ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hoc p hp).symm

omit [Finite G] d hP1 in
theorem D_le_K : oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) ≤
    oddCoreImg R ⊓ Subgroup.centralizer (P : Set G) :=
  fun _ hx => ⟨hx.1, Subgroup.centralizer_le (fun _ hy => hPS hy) hx.2⟩

omit d hP1 hPS in
theorem odd_K : Odd (Nat.card (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) :=
  (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem normalizer_eq : Subgroup.normalizer (P : Set G) =
    (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) ⊔
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G)) := by
  refine le_antisymm (fun g hg => ?_)
    (sup_le (fun k hk => Subgroup.centralizer_le_normalizer _ hk.2) inf_le_right)
  obtain ⟨m, hm, o, ho, rfl⟩ := d.factor_normalizer hP1 hPS hg
  rw [sup_comm]
  exact Subgroup.mul_mem_sup hm ho

theorem centralizer_eq : Subgroup.centralizer (P : Set G) =
    (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) ⊔
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G)) := by
  refine le_antisymm (fun g hg => ?_)
    (sup_le (fun k hk => hk.2) inf_le_right)
  obtain ⟨m, hm, o, ho, rfl⟩ := d.factor_centralizer hP1 hPS hg
  rw [sup_comm]
  exact Subgroup.mul_mem_sup hm ho

theorem exists_mulEquiv_normalizer
    [((oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
      (Subgroup.normalizer (P : Set G))).Normal]
    [((oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G))).Normal] :
    ∃ e : ((Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) ⧸
        (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
          (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G))) ≃*
      ((Subgroup.normalizer (P : Set G)) ⧸
        (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
          (Subgroup.normalizer (P : Set G))),
      ∀ a : ↥(Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G)),
        e (QuotientGroup.mk a) = QuotientGroup.mk (Subgroup.inclusion inf_le_right a) := by
  refine exists_mulEquiv_quotient (A := Subgroup.normalizer (S : Set G) ⊓
      Subgroup.normalizer (P : Set G)) (B := Subgroup.normalizer (P : Set G))
    (N := oddCoreImg R ⊓ Subgroup.centralizer (P : Set G))
    (D := oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)) inf_le_right ?_
    fun g hg => d.factor_normalizer hP1 hPS hg
  ext x
  constructor
  · rintro ⟨⟨hm, _⟩, hk⟩
    rw [← d.inf_K_M hPS]
    exact ⟨hk, hm⟩
  · intro hx
    exact ⟨⟨D_le_M hx, Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun y hy => hPS hy) hx.2)⟩, D_le_K hPS hx⟩

theorem exists_mulEquiv_centralizer
    [((oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
      (Subgroup.centralizer (P : Set G))).Normal]
    [((oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G))).Normal] :
    ∃ e : ((Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ⧸
        (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).subgroupOf
          (Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G))) ≃*
      ((Subgroup.centralizer (P : Set G)) ⧸
        (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
          (Subgroup.centralizer (P : Set G))),
      ∀ a : ↥(Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G)),
        e (QuotientGroup.mk a) = QuotientGroup.mk (Subgroup.inclusion inf_le_right a) := by
  refine exists_mulEquiv_quotient (A := Subgroup.normalizer (S : Set G) ⊓
      Subgroup.centralizer (P : Set G)) (B := Subgroup.centralizer (P : Set G))
    (N := oddCoreImg R ⊓ Subgroup.centralizer (P : Set G))
    (D := oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)) inf_le_right ?_
    fun g hg => d.factor_centralizer hP1 hPS hg
  ext x
  constructor
  · rintro ⟨⟨hm, _⟩, hk⟩
    rw [← d.inf_K_M hPS]
    exact ⟨hk, hm⟩
  · intro hx
    exact ⟨⟨D_le_M hx, Subgroup.centralizer_le (fun y hy => hPS hy) hx.2⟩, D_le_K hPS hx⟩

theorem relIndex_eq :
    (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (Subgroup.normalizer (P : Set G)) =
      (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).relIndex
        (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) ∧
    (Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G)).relIndex
        (Subgroup.centralizer (P : Set G)) =
      (oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).relIndex
        (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) ∧
    Odd ((oddCoreImg R ⊓ Subgroup.centralizer (S : Set G)).relIndex
        (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G))) := by
  have hKN : oddCoreImg R ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    fun _ hk => Subgroup.centralizer_le_normalizer _ hk.2
  have hKC : oddCoreImg R ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    inf_le_right
  have hnN := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr
    (d.normalizer_le_normalizer_K hP1 hPS)
  have hnC := (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr
    (fun g hg => d.normalizer_le_normalizer_K hP1 hPS (Subgroup.centralizer_le_normalizer _ hg))
  have h1 := relIndex_eq_relIndex_inf (A := Subgroup.normalizer (S : Set G) ⊓
      Subgroup.normalizer (P : Set G)) (B := Subgroup.normalizer (P : Set G))
    (N := oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) inf_le_right hKN
    fun g hg => d.factor_normalizer hP1 hPS hg
  have h2 := relIndex_eq_relIndex_inf (A := Subgroup.normalizer (S : Set G) ⊓
      Subgroup.centralizer (P : Set G)) (B := Subgroup.centralizer (P : Set G))
    (N := oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) inf_le_right hKC
    fun g hg => d.factor_centralizer hP1 hPS hg
  have e1 : (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (P : Set G)) ⊓
      (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) =
      oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨hm, _⟩, hk⟩
      rw [← d.inf_K_M hPS]
      exact ⟨hk, hm⟩
    · intro hx
      exact ⟨⟨D_le_M hx, Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (fun y hy => hPS hy) hx.2)⟩, D_le_K hPS hx⟩
  have e2 : (Subgroup.normalizer (S : Set G) ⊓ Subgroup.centralizer (P : Set G)) ⊓
      (oddCoreImg R ⊓ Subgroup.centralizer (P : Set G)) =
      oddCoreImg R ⊓ Subgroup.centralizer (S : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨hm, _⟩, hk⟩
      rw [← d.inf_K_M hPS]
      exact ⟨hk, hm⟩
    · intro hx
      exact ⟨⟨D_le_M hx, Subgroup.centralizer_le (fun y hy => hPS hy) hx.2⟩, D_le_K hPS hx⟩
  rw [e1] at h1
  rw [e2] at h2
  refine ⟨h1, h2, ?_⟩
  exact (odd_K (R := R) (P := P)).of_dvd_nat (Subgroup.relIndex_dvd_card _ _)

end Local

theorem sylow_of_sylow_M {T : Subgroup G} (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    IsSylow2Of T (Subgroup.centralizer ({t} : Set G)) ∧ S ≤ T ∧ t ∈ T ∧
      ∀ x ∈ T, t * x = x * t := by
  have hTM : T ≤ Subgroup.normalizer (S : Set G) := hT.1
  have hTH : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx => d.M_le_C (hTM hx)
  obtain ⟨-, hodd⟩ := d.relIndex_M_H
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set G)) =
      Nat.card (Subgroup.normalizer (S : Set G)) *
        (Subgroup.normalizer (S : Set G)).relIndex (Subgroup.centralizer ({t} : Set G)) := by
    have := Subgroup.card_mul_index ((Subgroup.normalizer (S : Set G)).subgroupOf
      (Subgroup.centralizer ({t} : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => d.M_le_C hx)).toEquiv] at this
    exact this.symm
  have h2 : (Nat.card (Subgroup.centralizer ({t} : Set G))).factorization 2 =
      (Nat.card (Subgroup.normalizer (S : Set G))).factorization 2 := by
    have hnd : ¬ 2 ∣ (Subgroup.normalizer (S : Set G)).relIndex
        (Subgroup.centralizer ({t} : Set G)) := fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' hodd.pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hnd]
  have hsylow : IsSylow2Of T (Subgroup.centralizer ({t} : Set G)) :=
    isSylow2Of_of_card hTH hT.2.1 (by rw [h2, hT.card_eq])
  have hsup : S ⊔ T = T := hT.2.2 (S ⊔ T) (sup_le Subgroup.le_normalizer hTM)
    (IsPGroup.to_sup_of_normal_left' d.S_two hT.2.1 hTM) le_sup_right
  have hST : S ≤ T := hsup ▸ le_sup_left
  exact ⟨hsylow, hST, hST d.t_mem, fun x hx => Subgroup.mem_centralizer_iff.mp (hTH hx) t rfl⟩

omit d in
theorem of_quaternion {R : Subgroup G} (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (h2 : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)) :
    OddByQuat R ((S : Subgroup R).map R.subtype) t where
  sylow := isSylow2Of_map_subtype S
  t_mem := ht
  t_ord := hto
  unique := fun _ hx hx2 => eq_of_orderOf_eq_two_of_quaternion_sylow
    (Subgroup.map_subtype_le _ ht) hto hRC S hS (Subgroup.map_subtype_le _ hx) hx2
  le_C := hRC
  normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  two := h2

end OddByQuat

end CFSG.ClassicalInvolution
