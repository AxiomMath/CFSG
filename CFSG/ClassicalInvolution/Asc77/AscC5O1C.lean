module

public import CFSG.ClassicalInvolution.Asc77.AscC5O1N
public import CFSG.ClassicalInvolution.Asc77.AscC25Y1

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def cOne (z : G) (K K' : Subgroup G) : Subgroup G :=
  Subgroup.centralizer ({z} : Set G) ⊓ trivialOnQuot K ⊓ trivialOnQuot K'

theorem mem_trivialOnQuot_of_isUniqueInvolution {J : Subgroup G} {z : G}
    (hz : IsUniqueInvolution J z) : z ∈ trivialOnQuot J := by
  refine ⟨mem_normalizer_of_conjSub_eq (conjSub_eq_self_of_mem hz.mem), fun x hx => ?_⟩
  have h1 : x * z * x⁻¹ ∈ J := J.mul_mem (J.mul_mem hx hz.mem) (J.inv_mem hx)
  have h2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · have hzx : z * x = x * z := by
      calc z * x = (x * z * x⁻¹) * x := by rw [h]
        _ = x * z := by group
    rw [(commutatorElement_eq_one_iff_mul_comm).mpr hzx]
    exact one_mem _

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem cOne_conj [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {c y : G}
    (hc : c * z * c⁻¹ = z)
    (hy : y ∈ cOne z K K') : c * y * c⁻¹ ∈ cOne z K K' := by
  obtain ⟨⟨hyz, hyK⟩, hyK'⟩ := hy
  obtain ⟨h1, h2⟩ := C25Y.trivialOnQuot_pair_conj C.hyp.std.setting hyK hyK' hc
  refine ⟨⟨?_, h1⟩, h2⟩
  have hyz' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyz
  have hc' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]
      _ = z := by group
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc c * y * c⁻¹ * z = c * (y * (c⁻¹ * z * c)) * c⁻¹ := by group
    _ = c * (y * z) * c⁻¹ := by rw [hc']
    _ = c * (z * y) * c⁻¹ := by rw [hyz']
    _ = (c * z * c⁻¹) * (c * y * c⁻¹) := by group
    _ = z * (c * y * c⁻¹) := by rw [hc]

theorem z_mem_cOne (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : z ∈ cOne z K K' := by
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  exact ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    mem_trivialOnQuot_of_isUniqueInvolution hs.hz⟩,
    mem_trivialOnQuot_of_isUniqueInvolution (isUniqueInvolution_of_mem_twinSet hs.hz hs.hK')⟩

theorem a_mem_cOne [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    a ∈ cOne z K K' := by
  obtain ⟨-, -, -, hK₂, hK₂', -⟩ := C.om5
  exact ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr C.comm, hK₂.2⟩, hK₂'.2⟩

theorem mem_A_of_mem_cOne (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hs : s ∈ cOne z K K') :
    s ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have key : ∀ J : Subgroup G, s ∈ trivialOnQuot J → ∀ r ∈ J, r ∈ (S : Subgroup G) →
      r ∈ Subgroup.centralizer ({s} : Set G) := by
    intro J hsJ r hrJ hrS
    have h1 : ⁅s, r⁆ ∈ oddCoreIn J := hsJ.2 r hrJ
    have h2 : ⁅s, r⁆ ∈ (S : Subgroup G) := by
      rw [commutatorElement_def]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
        ((S : Subgroup G).mul_mem hsS hrS) ((S : Subgroup G).inv_mem hsS))
        ((S : Subgroup G).inv_mem hrS)
    have h3 := eq_one_of_isPGroup_of_odd S.isPGroup' (odd_card_oddCoreIn J) h2 h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr h3.symm
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({s} : Set G) :=
    sup_le (fun r hr => key K hs.1.2 r (C.hyp.hR.2.1 hr) (C.hyp.hR.2.2 hr))
      (fun r hr => key K' hs.2 r (C.hyp.hR'.2.1 hr) (C.hyp.hR'.2.2 hr))
  exact ⟨hsS, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hh)⟩

theorem A_le_cOne [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≤ cOne z K K' := by
  intro b hb
  rcases C.hA0 b hb with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact C.a_mem_cOne
  · exact C.z_mem_cOne
  · exact mul_mem C.a_mem_cOne C.z_mem_cOne

theorem isSylow2In_cOne [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
      (cOne z K K') := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  refine ⟨C.A_le_cOne, S.isPGroup'.to_le inf_le_left, fun V' hV'C hV' hle => ?_⟩
  have hSz : IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) :=
    ⟨fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (C.hyp.hzS s hs), S.isPGroup',
      fun V'' _ hV'' hle' => S.is_maximal' hV'' hle'⟩
  have hV'z : V' ≤ Subgroup.centralizer ({z} : Set G) := fun v hv => (hV'C hv).1.1
  obtain ⟨V, hV, hV'V⟩ := IsSylow2In.exists_ge hV' hV'z
  obtain ⟨c, hc, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSz)
    (show IsSylow2Of _ _ from hV)
  have hcz : c⁻¹ * z * c⁻¹⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [h]
      _ = z := by group
  have hmap : ∀ v ∈ V', c⁻¹ * v * c ∈ A₀ := by
    intro v hv
    have h1 : c⁻¹ * v * c ∈ (S : Subgroup G) := by
      have := hV'V hv
      rw [hVeq] at this
      exact mem_conjSubgroup_iff.mp this
    have h2 : c⁻¹ * v * c ∈ cOne z K K' := by
      have := C.cOne_conj hcz (hV'C hv)
      rwa [inv_inv] at this
    exact C.mem_A_of_mem_cOne h1 h2
  have hcard : Nat.card V' ≤ Nat.card A₀ := by
    refine Nat.card_le_card_of_injective (fun v : V' => (⟨c⁻¹ * v * c, hmap v v.2⟩ : A₀)) ?_
    intro v w hvw
    have h := congrArg Subtype.val hvw
    simp only [mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem conjSub_cOne [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {c : G}
    (hc : c * z * c⁻¹ = z) : conjSub c (cOne z K K') = cOne z K K' := by
  have hc' : c⁻¹ * z * c⁻¹⁻¹ = z := by
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]; group
      _ = z := by group
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have := C.cOne_conj hc hy
    simpa [mul_assoc] using this
  · intro hy
    have := C.cOne_conj hc' hy
    simpa using this

theorem oddCore_cOne_le [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    oddCoreIn (cOne z K K') ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  refine le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans fun x hx => hx.1.1) ?_
    (odd_card_oddCoreIn _)
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]; group
  have h := oddCoreIn_conjSub_eq c (cOne z K K')
  rw [C.conjSub_cOne hcz] at h
  exact mem_normalizer_of_conjSub_eq h.symm

theorem cOne_normalizer_le [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    ∀ g ∈ cOne z K K', (∀ x : G, x ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ↔ g * x * g⁻¹ ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) →
      ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g * x = x * g := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  intro g hg hgn x hx
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg.1.1]; group
  have hgN : g ∈ Subgroup.normalizer (A₀ : Set G) := Subgroup.mem_normalizer_iff.mpr hgn
  have hcommA : ∀ y ∈ A₀, y * a = a * y := by
    intro y hy
    rcases C.hA0 y hy with h | h | h | h <;> rw [h]
    · group
    · exact C.comm.symm
    · calc a * z * a = a * (z * a) := by group
        _ = a * (a * z) := by rw [C.comm]
  have hga : g * a * g⁻¹ = a := by
    have hm : g * a * g⁻¹ ∈ A₀ := (hgn a).mp C.haA
    rcases C.hA0 _ hm with h | h | h | h
    · exfalso
      apply C.ha1
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
    · exact absurd (show g⁻¹ * z * g⁻¹⁻¹ = a by rw [← h]; group) (C.not_conj_z g⁻¹)
    · exfalso
      have hstep : ∀ (n : ℕ) (y : G), g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ =
          g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ := by
        intro n y; rw [pow_succ']; group
      have hazz : g * (a * z) * g⁻¹ = a := by
        calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
          _ = a := by rw [h, hgz, C.mul_z_mul_z]
      have hpar : ∀ j : ℕ, g ^ (2 * j) * a * (g ^ (2 * j))⁻¹ = a ∧
          g ^ (2 * j + 1) * a * (g ^ (2 * j + 1))⁻¹ = a * z := by
        intro j
        induction j with
        | zero => exact ⟨by simp, by simpa using h⟩
        | succ j ih =>
          have e1 : g ^ (2 * (j + 1)) * a * (g ^ (2 * (j + 1)))⁻¹ = a := by
            rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, hstep, ih.2, hazz]
          exact ⟨e1, by rw [hstep, e1, h]⟩
      have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
      obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
      obtain ⟨j, rfl⟩ := hm
      have hm0 : 2 * j + 1 ≠ 0 := by omega
      have hord : orderOf (g ^ (2 * j + 1)) = 2 ^ k := by
        rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hn.symm), hn,
          Nat.mul_div_cancel _ (by omega)]
      have h2 : IsPGroup 2 (Subgroup.zpowers (g ^ (2 * j + 1))) :=
        IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])
      have hle : Subgroup.zpowers (g ^ (2 * j + 1)) ≤ Subgroup.normalizer (A₀ : Set G) :=
        Subgroup.zpowers_le.mpr (pow_mem hgN _)
      have hp := IsPGroup.to_sup_of_normal_right' h2 (S.isPGroup'.to_le inf_le_left) hle
      have hle' : Subgroup.zpowers (g ^ (2 * j + 1)) ⊔ A₀ ≤ cOne z K K' :=
        sup_le (Subgroup.zpowers_le.mpr (pow_mem hg _)) C.A_le_cOne
      have heq := C.isSylow2In_cOne.2.2 _ hle' hp le_sup_right
      have hgA : g ^ (2 * j + 1) ∈ A₀ := by
        have h4 := le_sup_left (a := Subgroup.zpowers (g ^ (2 * j + 1))) (b := A₀)
          (Subgroup.mem_zpowers (g ^ (2 * j + 1)))
        rw [heq] at h4
        exact h4
      have h3 := (hpar j).2
      rw [show g ^ (2 * j + 1) * a * (g ^ (2 * j + 1))⁻¹ = a by
        rw [hcommA _ hgA]; group] at h3
      apply C.hz1
      calc z = a⁻¹ * (a * z) := by group
        _ = 1 := by rw [← h3]; group
  rcases C.hA0 x hx with h | h | h | h <;> rw [h]
  · group
  · calc g * a = (g * a * g⁻¹) * g := by group
      _ = a * g := by rw [hga]
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  · calc g * (a * z) = (g * a * g⁻¹) * (g * z * g⁻¹) * g := by group
      _ = a * z * g := by rw [hga, hgz]

theorem cOne_eq_mul [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    ∀ c ∈ cOne z K K', ∃ o ∈ oddCoreIn (cOne z K K'), ∃ b ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), c = o * b :=
  exists_oddCore_mul_of_normalizer_le C.isSylow2In_cOne C.cOne_normalizer_le

theorem conj_a_mem [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {c : G}
    (hc : c * z * c⁻¹ = z) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      c * a * c⁻¹ = a * o ∨ c * a * c⁻¹ = a * z * o := by
  have hm : c * a * c⁻¹ ∈ cOne z K K' := C.cOne_conj hc C.a_mem_cOne
  obtain ⟨o, ho, b, hb, hob⟩ := C.cOne_eq_mul _ hm
  have hO := C.oddCore_cOne_le
  have hinv : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
    calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [C.ha2]; group
  rcases C.hA0 b hb with h | h | h | h
  · exfalso
    have hp : IsPGroup 2 (Subgroup.zpowers (c * a * c⁻¹)) := isPGroup_zpowers_of_sq_eq_one hinv
    have h1 : c * a * c⁻¹ ∈ oddCoreIn (cOne z K K') := by rw [hob, h, mul_one]; exact ho
    have h2 := eq_one_of_isPGroup_of_odd hp (odd_card_oddCoreIn _) (Subgroup.mem_zpowers _) h1
    apply C.ha1
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = 1 := by rw [h2]; group
  · have hai : a⁻¹ ∈ cOne z K K' := Subgroup.inv_mem _ C.a_mem_cOne
    have h1 := conj_mem_oddCoreIn hai ho
    rw [inv_inv] at h1
    refine ⟨a⁻¹ * o * a, hO h1, Or.inl ?_⟩
    rw [hob, h]; group
  · exfalso
    have hzo : z * (c * a * c⁻¹) ∈ oddCoreIn (cOne z K K') := by
      rw [hob, h]
      have h1 := conj_mem_oddCoreIn C.z_mem_cOne ho
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hz2
      rw [hzi] at h1
      simpa [mul_assoc] using h1
    obtain ⟨n, -, hn⟩ := C25Y.exists_conj_of_involutions_odd (odd_card_oddCoreIn _) C.hz2 hinv hzo
    exact C.not_conj_z (c⁻¹ * n) (by
      calc c⁻¹ * n * z * (c⁻¹ * n)⁻¹ = c⁻¹ * (n * z * n⁻¹) * c := by group
        _ = a := by rw [← hn]; group)
  · have hazi : (a * z)⁻¹ ∈ cOne z K K' :=
      Subgroup.inv_mem _ (mul_mem C.a_mem_cOne C.z_mem_cOne)
    have h1 := conj_mem_oddCoreIn hazi ho
    rw [inv_inv] at h1
    refine ⟨(a * z)⁻¹ * o * (a * z), hO h1, Or.inr ?_⟩
    rw [hob, h]; group

theorem frattini [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {c : G}
    (hc : c * z * c⁻¹ = z) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)), o⁻¹ * c ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) : Subgroup G) :
        Set G) := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hsyl := C.isSylow2In_cOne
  have hsyl' : IsSylow2In (conjSub c A₀) (cOne z K K') := by
    have := hsyl.conj c
    rwa [C.conjSub_cOne hc] at this
  obtain ⟨m, hm, hmeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hsyl)
    (show IsSylow2Of _ _ from hsyl')
  obtain ⟨o, ho, b, hb, hmob⟩ := C.cOne_eq_mul m hm
  refine ⟨o, C.oddCore_cOne_le ho, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
  have key : ∀ y : G, y ∈ conjSub c A₀ ↔ b⁻¹ * (o⁻¹ * y * o) * b ∈ A₀ := by
    intro y
    rw [hmeq, mem_conjSubgroup_iff, hmob]
    have e : (o * b)⁻¹ * y * (o * b) = b⁻¹ * (o⁻¹ * y * o) * b := by group
    rw [e]
  have hbA : ∀ y : G, b⁻¹ * y * b ∈ A₀ ↔ y ∈ A₀ := by
    intro y
    constructor
    · intro hy
      have h1 := A₀.mul_mem (A₀.mul_mem hb hy) (A₀.inv_mem hb)
      have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
      rwa [e] at h1
    · intro hy
      exact A₀.mul_mem (A₀.mul_mem (A₀.inv_mem hb) hy) hb
  constructor
  · intro hx
    have h1 : c * x * c⁻¹ ∈ conjSub c A₀ := by
      rw [mem_conjSub_iff]
      have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      rw [e]; exact hx
    have h2 := (hbA _).mp ((key _).mp h1)
    have e : o⁻¹ * (c * x * c⁻¹) * o = o⁻¹ * c * x * (o⁻¹ * c)⁻¹ := by group
    rwa [e] at h2
  · intro hx
    have e : o⁻¹ * (c * x * c⁻¹) * o = o⁻¹ * c * x * (o⁻¹ * c)⁻¹ := by group
    have h2 : b⁻¹ * (o⁻¹ * (c * x * c⁻¹) * o) * b ∈ A₀ := (hbA _).mpr (by rw [e]; exact hx)
    have h1 := mem_conjSub_iff.mp ((key _).mpr h2)
    have e' : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rwa [e'] at h1

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O
