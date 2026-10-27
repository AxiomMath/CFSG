module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem isPGroup_map_of_isPGroup {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (T : Subgroup X) (hT : IsPGroup p ↥T) : IsPGroup p ↥(T.map f) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
  obtain ⟨n, hn⟩ := hT ⟨x, hx⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg Subtype.val hn
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hxy, ← map_pow, this, map_one]

theorem isElemAbelian_map_of_injOn {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨x', hx', hxb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hxa, ← hxb, ← map_mul, ← map_mul, isElemAbelian_commute hE hx hx']
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_of_map_injOn {J M : Type} [Group J] [Group M] {p : ℕ} (π : J →* M)
    {W : Subgroup J} (hinj : Function.Injective (π.comp W.subtype))
    (hE : CFSG.Open.IsElemAbelian p (W.map π)) : CFSG.Open.IsElemAbelian p W := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply hinj
    have h := hE.1.1.comm ⟨π a, Subgroup.mem_map.2 ⟨a, a.2, rfl⟩⟩ ⟨π b, Subgroup.mem_map.2 ⟨b, b.2, rfl⟩⟩
    simpa using congrArg Subtype.val h
  · have hpow : (⟨x, hx⟩ : ↥W) ^ p = 1 := by
      apply hinj
      have hx' : π x ^ p = 1 := hE.2 (π x) (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
      simpa [map_pow] using hx'
    simpa using congrArg Subtype.val hpow

theorem card_map_of_injective_comp {X Y : Type} [Group X] [Group Y] (f : X →* Y) (S : Subgroup X)
    (hinj : Function.Injective (f.comp S.subtype)) : Nat.card (S.map f) = Nat.card S := by
  have hrange : (⊤ : Subgroup S).map (f.comp S.subtype) = S.map f := by
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, trivial, rfl⟩
  rw [← hrange, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem map_mem_normalizer_of_mem {X Y : Type} [Group X] [Group Y] (f : X →* Y) {V : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (V : Set X)) : f x ∈ Subgroup.normalizer ((V.map f : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h'
  constructor
  · intro hh
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨x * v * x⁻¹, (hx v).1 hv, ?_⟩
    simp [map_mul, map_inv, mul_assoc]
  · intro hh
    obtain ⟨v, hv, hvq⟩ := Subgroup.mem_map.1 hh
    have hx1 : x⁻¹ * v * x ∈ V := by
      rw [hx]
      simpa [mul_assoc] using hv
    have hh' : h' = f (x⁻¹ * v * x) := by
      rw [map_mul, map_mul, map_inv, hvq]
      group
    rw [hh']
    exact Subgroup.mem_map.2 ⟨x⁻¹ * v * x, hx1, rfl⟩

variable {G : Type} [Group G] [Finite G]

theorem twoLocal_of_witness {K A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hAK : A ⊓ K = ⊥)
    (hAc : ∀ a ∈ A, ∀ k ∈ K, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 K)
    {s : ℕ} (V E : Subgroup (PQuot 3 K)) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEV : E ≤ Subgroup.normalizer (V : Set (PQuot 3 K)))
    (hEc : Nat.card E = 3 ^ s) :
    ∃ P W : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧ W ≤ Subgroup.normalizer (P : Set G) ∧
      CFSG.Open.IsElemAbelian 3 W ∧ Nat.card W = 3 ^ s * Nat.card A := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hOK : GLAPPrimeCoreOf 3 K ≤ K := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.map_subtype_le _
  have hKJ : K ≤ K ⊔ A := le_sup_left
  have hAJ : A ≤ K ⊔ A := le_sup_right
  have hOJ : GLAPPrimeCoreOf 3 K ≤ K ⊔ A := hOK.trans hKJ
  have hKN : K ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf 3 K
  have hAN' : A ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    hAN.trans (normalizer_le_normalizer_glaPPrimeCoreOf 3 K)
  have hJN : K ⊔ A ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    sup_le hKN hAN'
  haveI hOn : ((GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).2 hJN
  let π : ↥(K ⊔ A) →* ↥(K ⊔ A) ⧸ ((GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)) :=
    QuotientGroup.mk' _
  have hπker : π.ker = (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A) := QuotientGroup.ker_mk' _
  have hOcard : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K : Subgroup G) := not_dvd_card_glaPPrimeCoreOf hp K
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact hOcard
  have hAO : A ⊓ GLAPPrimeCoreOf 3 K = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hA)
    have hdvd : Nat.card (A ⊓ GLAPPrimeCoreOf 3 K : Subgroup G) ∣ 3 ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj0 : j = 0 := by
      by_contra hne
      apply hOcard
      have h3 : 3 ∣ Nat.card (A ⊓ GLAPPrimeCoreOf 3 K : Subgroup G) := by
        rw [hj]
        exact dvd_pow_self 3 hne
      exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)
    rw [hj0, pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq _ hj
  have hAel : CFSG.Open.IsElemAbelian 3 (A.subgroupOf (K ⊔ A)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext (isElemAbelian_commute hA (Subgroup.mem_subgroupOf.1 a.2)
        (Subgroup.mem_subgroupOf.1 b.2)))
    · apply Subtype.ext
      simpa using hA.2 ((x : ↥(K ⊔ A)) : G) (Subgroup.mem_subgroupOf.1 hx)
  have hπA : Function.Injective (π.comp (A.subgroupOf (K ⊔ A)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : ((x : ↥(K ⊔ A)) : G) ∈ GLAPPrimeCoreOf 3 K := by
      have hxker : ((x : ↥(K ⊔ A))) ∈ π.ker := hx
      rw [hπker] at hxker
      exact Subgroup.mem_subgroupOf.1 hxker
    have hxA : ((x : ↥(K ⊔ A)) : G) ∈ A := Subgroup.mem_subgroupOf.1 x.2
    have hx1 : ((x : ↥(K ⊔ A)) : G) = 1 := by
      have : ((x : ↥(K ⊔ A)) : G) ∈ A ⊓ GLAPPrimeCoreOf 3 K := ⟨hxA, hxO⟩
      rw [hAO] at this
      exact Subgroup.mem_bot.1 this
    exact Subtype.ext (Subtype.ext hx1)
  have hcore : GLAPPrimeCoreOf 3 (K.subgroupOf (K ⊔ A)) = π.ker ⊓ K.subgroupOf (K ⊔ A) := by
    apply Subgroup.map_injective (f := (K ⊔ A).subtype) (K ⊔ A).subtype_injective
    rw [map_subtype_glaPPrimeCoreOf_subgroupOf 3 hKJ, hπker,
      Subgroup.map_inf _ _ _ (K ⊔ A).subtype_injective, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hOJ, inf_eq_left.2 hKJ, inf_eq_left.2 hOK]
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map_self (p := 3) (ψ := π) (K := K.subgroupOf (K ⊔ A)) hcore
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_subgroupOf 3 hKJ
  let ψ : PQuot 3 K ≃* ↥((K.subgroupOf (K ⊔ A)).map π) := e₂.symm.trans e₁
  set Kp : Subgroup (↥(K ⊔ A) ⧸ (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)) :=
    (K.subgroupOf (K ⊔ A)).map π with hKp
  let ι : PQuot 3 K →* (↥(K ⊔ A) ⧸ (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)) :=
    Kp.subtype.comp ψ.toMonoidHom
  have hι : Function.Injective ι := fun x y hxy => ψ.injective (Subtype.ext hxy)
  have hιK : ∀ x, ι x ∈ Kp := fun x => (ψ x).2
  set Em : Subgroup (↥(K ⊔ A) ⧸ (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)) := E.map ι with hEm
  set Vm : Subgroup (↥(K ⊔ A) ⧸ (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)) := V.map ι with hVm'
  set Ap : Subgroup (↥(K ⊔ A) ⧸ (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A)) :=
    (A.subgroupOf (K ⊔ A)).map π with hAp
  have hEmKp : Em ≤ Kp := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hz
    exact hιK x
  have hVmKp : Vm ≤ Kp := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hz
    exact hιK x
  have hcomm : ∀ x ∈ Kp, ∀ y ∈ Ap, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have hkG : ((k : ↥(K ⊔ A)) : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have haG : ((a : ↥(K ⊔ A)) : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have hc : ⁅k, a⁆ ∈ (GLAPPrimeCoreOf 3 K).subgroupOf (K ⊔ A) := by
      rw [Subgroup.mem_subgroupOf]
      exact hAc _ haG _ hkG
    have h1 : π ⁅k, a⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hEmel : CFSG.Open.IsElemAbelian 3 Em := isElemAbelian_map_of_injOn ι E hE
  have hApel : CFSG.Open.IsElemAbelian 3 Ap := isElemAbelian_map_of_injOn π _ hAel
  have hEmAp : Em ⊓ Ap = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxA⟩ := hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 (hEmKp hxE)
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hxA
    have h1 : π (k⁻¹ * a) = 1 := by rw [map_mul, map_inv, hkx, hax, inv_mul_cancel]
    have h2 : ((k⁻¹ * a : ↥(K ⊔ A)) : G) ∈ GLAPPrimeCoreOf 3 K := by
      have h3 : k⁻¹ * a ∈ π.ker := h1
      rw [hπker] at h3
      exact Subgroup.mem_subgroupOf.1 h3
    have hkG : ((k : ↥(K ⊔ A)) : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have haK : ((a : ↥(K ⊔ A)) : G) ∈ K := by
      have e : ((a : ↥(K ⊔ A)) : G) = ((k : ↥(K ⊔ A)) : G) * ((k⁻¹ * a : ↥(K ⊔ A)) : G) := by
        simp
      rw [e]
      exact K.mul_mem hkG (hOK h2)
    have haA : ((a : ↥(K ⊔ A)) : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have ha1 : ((a : ↥(K ⊔ A)) : G) = 1 := by
      have hmem : ((a : ↥(K ⊔ A)) : G) ∈ A ⊓ K := ⟨haA, haK⟩
      rw [hAK] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [Subgroup.mem_bot, ← hax]
    have ha' : a = 1 := Subtype.ext ha1
    rw [ha', map_one]
  have hE0el : CFSG.Open.IsElemAbelian 3 (Em ⊔ Ap) :=
    CFSG.LocalAnalysis.GLTheoremA.S8.L84.isElemAbelian_sup_of_commute hEmel hApel
      (fun w hw d hd => hcomm w (hEmKp hw) d hd)
  have hApN : Ap ≤ Subgroup.normalizer (Em : Set _) := fun y hy =>
    CFSG.LocalAnalysis.GLTheoremA.S8.L84.mem_normalizer_of_commute
      (fun x hx => (hcomm x (hEmKp hx) y hy).symm)
  have hEmN : Em ≤ Subgroup.normalizer (Vm : Set _) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact map_mem_normalizer_of_mem ι (hEV hx)
  have hApNV : Ap ≤ Subgroup.normalizer (Vm : Set _) := fun y hy =>
    CFSG.LocalAnalysis.GLTheoremA.S8.L84.mem_normalizer_of_commute
      (fun x hx => (hcomm x (hVmKp hx) y hy).symm)
  have hE0N : Em ⊔ Ap ≤ Subgroup.normalizer (Vm : Set _) := sup_le hEmN hApNV
  have hVm_ne : Vm ≠ ⊥ := by
    intro h
    apply hV
    exact Subgroup.map_injective hι (h.trans (Subgroup.map_bot _).symm)
  have hVm2 : IsPGroup 2 Vm := isPGroup_map_of_isPGroup ι V hV2
  have hπr : π.range = ⊤ := MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)
  have hE0π : Em ⊔ Ap ≤ π.range := by rw [hπr]; exact le_top
  have hVπ : Vm ≤ π.range := by rw [hπr]; exact le_top
  obtain ⟨W, P, -, hWmap, hWinj, hPp, hPmap, hWP⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lift_normalizing π hk3 (isPGroup_of_isElemAbelian hE0el) hVm2 hE0π hVπ hE0N
  have hWel : CFSG.Open.IsElemAbelian 3 W :=
    isElemAbelian_of_map_injOn π hWinj (by rw [hWmap]; exact hE0el)
  refine ⟨P.map (K ⊔ A).subtype, W.map (K ⊔ A).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hVm_ne
    have hP : P = ⊥ := Subgroup.map_injective (K ⊔ A).subtype_injective (h.trans (Subgroup.map_bot _).symm)
    rw [← hPmap, hP, Subgroup.map_bot]
  · exact isPGroup_map_of_isPGroup (K ⊔ A).subtype P hPp
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    exact map_mem_normalizer_of_mem (K ⊔ A).subtype (hWP hw)
  · exact isElemAbelian_map_of_injOn _ W hWel
  · rw [Subgroup.card_map_of_injective (K ⊔ A).subtype_injective,
      ← card_map_of_injective_comp π W hWinj, hWmap]
    have hsum := card_sup_mul_card_inf_of_le_normalizer (A := Em) (B := Ap) hApN
    rw [hEmAp, Subgroup.card_bot, mul_one] at hsum
    rw [hsum, Subgroup.card_map_of_injective hι, hEc,
      card_map_of_injective_comp π (A.subgroupOf (K ⊔ A)) hπA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv]

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
