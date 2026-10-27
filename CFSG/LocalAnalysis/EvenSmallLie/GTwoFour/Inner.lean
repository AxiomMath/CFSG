module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Standard
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CoverRoots
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.TwoToOne

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.Chevalley.G2FieldFour
open scoped commutatorElement

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem card_posU
    (hK : Nat.card K = 4) : Nat.card (posU K) = 2 ^ 12 := by
  rw [show Nat.card (posU K) = Nat.card (posUnipotent .G2 K) from
    Nat.card_congr (subgroupOfEquivOfLe posUnipotent_le_adjointGroup).toEquiv,
    card_posUnipotent, ncard_posRoots, hK]
  norm_num

theorem exists_eq_map_conj_posU
    (hK : Nat.card K = 4) {P : Subgroup (adjointGroup .G2 K)}
    (hP2 : IsPGroup 2 P) (hcard : Nat.card P = 2 ^ 12) :
    ∃ g : adjointGroup .G2 K, P = (posU K).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element .G2
  obtain ⟨U₀, hU₀⟩ := (exceptional_ordinary_Sylow_opposition .G2 K 2 w₀ hw₀).1
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) U₀ Q
  have hQ : (Q : Subgroup (adjointGroup .G2 K)) = (posU K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_smul_sylow_eq_map, hU₀]
  have hcardQ : Nat.card (Q : Subgroup (adjointGroup .G2 K)) = 2 ^ 12 := by
    rw [hQ, card_map_of_injective (MulAut.conj g).injective, card_posU hK]
  exact ⟨g, (eq_of_le_of_card_ge hPQ (by rw [hcardQ, hcard])).trans hQ⟩

omit [Finite K] [CharP K 2] in
theorem card_sq_map_conj (g : adjointGroup .G2 K) (Q : Subgroup (adjointGroup .G2 K))
    (x : adjointGroup .G2 K) :
    Nat.card {q // q ∈ Q.map (MulAut.conj g).toMonoidHom ∧ q * q = x} =
      Nat.card {q // q ∈ Q ∧ q * q = g⁻¹ * x * g} :=
  Nat.card_congr ((MulAut.conj g⁻¹).toEquiv.subtypeEquiv fun q => by
    change q ∈ Q.map (MulAut.conj g).toMonoidHom ∧ q * q = x ↔
      g⁻¹ * q * g⁻¹⁻¹ ∈ Q ∧ g⁻¹ * q * g⁻¹⁻¹ * (g⁻¹ * q * g⁻¹⁻¹) = g⁻¹ * x * g
    rw [mem_map_equiv, inv_inv, show g⁻¹ * q * g * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g by group]
    exact and_congr Iff.rfl ⟨fun h => by rw [h], fun h => mul_left_cancel (mul_right_cancel h)⟩)

omit [Finite K] [CharP K 2] in
theorem card_isConj_map_conj (g : adjointGroup .G2 K) (Q : Subgroup (adjointGroup .G2 K))
    (x : adjointGroup .G2 K) :
    Nat.card {q // q ∈ Q.map (MulAut.conj g).toMonoidHom ∧ IsConj q x} =
      Nat.card {q // q ∈ Q ∧ IsConj q x} :=
  Nat.card_congr ((MulAut.conj g⁻¹).toEquiv.subtypeEquiv fun q => by
    change q ∈ Q.map (MulAut.conj g).toMonoidHom ∧ IsConj q x ↔
      g⁻¹ * q * g⁻¹⁻¹ ∈ Q ∧ IsConj (g⁻¹ * q * g⁻¹⁻¹) x
    rw [mem_map_equiv]
    refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · exact (isConj_iff.2 ⟨g, by rw [inv_inv]; group⟩).trans h
    · exact (isConj_iff.2 ⟨g⁻¹, rfl⟩).trans h)

end Sylow

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2] {M : Type*} [Group M] [Finite M]
  [Group.IsPerfect M] {π : M →* adjointGroup .G2 K} {z : M}

theorem card_sq_lt
    (hK : Nat.card K = 4) (hπ : Function.Surjective π) (hz1 : z ≠ 1)
    (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z) (hker : ∀ k, π k = 1 → k ∈ center M)
    {S : Subgroup M} (hzS : z ∈ S) (hS : Nat.card S = 2 ^ 13) {a : S} (ha : a ∈ center S)
    (hπa : π a ≠ 1) :
    Nat.card {s : S // s * s = a} ≤ 480 ∧ 576 ≤ Nat.card {s : S // s * s = ⟨z, hzS⟩} := by
  have hzc : z ∈ center M := hker z ((hz z).2 (Or.inr rfl))
  set P := S.map π with hPdef
  have hP : Nat.card P = 2 ^ 12 := by
    have h1 := card_le_two_mul hπ hz S (fun _ => True)
    have h2 := two_mul_card_le hz hz1 S hzS (fun _ => True)
    have e1 : Nat.card {s : S // True} = Nat.card S := Nat.card_congr (Equiv.subtypeUnivEquiv
      fun _ => trivial)
    have e2 : Nat.card {q // q ∈ P ∧ True} = Nat.card P :=
      Nat.card_congr (Equiv.subtypeEquivRight fun q => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)
    rw [e1, e2] at h1 h2
    have hS' : Nat.card S = 8192 := by rw [hS]; norm_num
    rw [show (2 : ℕ) ^ 12 = 4096 by norm_num]
    omega
  have hP2 : IsPGroup 2 P := by
    refine IsPGroup.of_card (n := 12) hP
  obtain ⟨g, hg⟩ := exists_eq_map_conj_posU hK hP2 hP
  have hπaP : π a ∈ P := ⟨a, a.2, rfl⟩
  have hcomm : ∀ q ∈ P, π a * q = q * π a := by
    rintro _ ⟨s, hs, rfl⟩
    have h := congrArg Subtype.val (mem_center_iff.1 ha ⟨s, hs⟩)
    simp only [Subgroup.coe_mul] at h
    rw [← map_mul, ← map_mul, h]
  have hmemP : ∀ u ∈ posU K, g * u * g⁻¹ ∈ P := fun u hu => by
    rw [hg]; exact ⟨u, hu, rfl⟩
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : K, g⁻¹ * π a * g = rootX rootC F₀ := by
    have hU : g⁻¹ * π a * g ∈ posU K := by
      rw [hg] at hπaP
      obtain ⟨u, hu, hu'⟩ := hπaP
      rw [← hu']
      simpa [MulAut.conj_apply, mul_assoc] using hu
    have hc : ∀ v ∈ posU K, g⁻¹ * π a * g * v = v * (g⁻¹ * π a * g) := fun v hv => by
      have h := hcomm _ (hmemP v hv)
      calc g⁻¹ * π a * g * v = g⁻¹ * (π a * (g * v * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * v * g⁻¹) * π a) * g := by rw [h]
        _ = v * (g⁻¹ * π a * g) := by group
    exact eq_rootX_c_of_commute hU (hc _ (rootX_mem_posU rootR_mem 1))
      (hc _ (rootX_mem_posU rootV_mem 1)) (hc _ (rootX_mem_posU rootA_mem 1))
  have hF₀0 : F₀ ≠ 0 := by
    rintro rfl
    apply hπa
    have h : g⁻¹ * π a * g = 1 := by rw [hF₀, rootX_zero]
    rw [show π a = g * (g⁻¹ * π a * g) * g⁻¹ by group, h, mul_one, mul_inv_cancel]
  refine ⟨?_, ?_⟩
  ·
    calc Nat.card {s : S // s * s = a}
        ≤ Nat.card {s : S // π s * π s = π a} := card_subtype_le_of_imp fun s hs => by
          rw [← map_mul, ← hs]; rfl
      _ ≤ 2 * Nat.card {q // q ∈ P ∧ q * q = π a} :=
          card_le_two_mul hπ hz S (fun q => q * q = π a)
      _ = 2 * 240 := by
          rw [hg, card_sq_map_conj, hF₀, card_sq_eq_rootX_c hK hF₀0]
      _ = 480 := by norm_num
  ·
    have hF2 : ∀ m : M, IsConj (π m) (rootX rootV 1) → m * m = z := fun m hm =>
      mul_self_eq_of_isConj_rootX_v hz1 hz hK hπ hker hm
    calc 576 = 2 * 288 := by norm_num
      _ ≤ 2 * Nat.card {q // q ∈ P ∧ IsConj q (rootX rootV 1)} := by
          rw [hg, card_isConj_map_conj]
          exact Nat.mul_le_mul_left 2 (le_card_isConj_rootX_v hK)
      _ ≤ Nat.card {s : S // IsConj (π s) (rootX rootV 1)} :=
          two_mul_card_le hz hz1 S hzS (fun q => IsConj q (rootX rootV 1))
      _ ≤ Nat.card {s : S // s * s = ⟨z, hzS⟩} := card_subtype_le_of_imp fun s hs =>
          Subtype.ext (hF2 s hs)

end Count

section Preimage

variable {K : Type} [Field K] {M : Type*} [Group M] {π : M →* adjointGroup .G2 K} {z : M}

theorem commutator_comap_eq (hπ : Function.Surjective π) (hz1 : z ≠ 1)
    (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z) (hker : ∀ k, π k = 1 → k ∈ center M)
    {Z : Subgroup (adjointGroup .G2 K)} (hZ : ⁅Z, Z⁆ = Z) {m₀ : M} (hm₀ : π m₀ ∈ Z)
    (hm₀2 : m₀ * m₀ = z) : ⁅Z.comap π, Z.comap π⁆ = Z.comap π := by
  set D := ⁅Z.comap π, Z.comap π⁆ with hD
  have hDmap : D.map π = Z := by
    rw [hD, map_commutator, map_comap_eq_self_of_surjective hπ, hZ]
  have hlift : ∀ x : M, π x ∈ Z → ∃ d ∈ D, π d = π x := fun x hx => by
    rw [← hDmap] at hx
    obtain ⟨d, hd, hdx⟩ := hx
    exact ⟨d, hd, hdx⟩
  have hzD : z ∈ D := by
    obtain ⟨d, hd, hdm⟩ := hlift m₀ hm₀
    have hsq := mul_self_eq_of_map_eq hz1 hz hker hdm
    rw [hm₀2] at hsq
    rw [hsq]
    exact mul_mem hd hd
  refine le_antisymm (Subgroup.commutator_le_self _) fun x hx => ?_
  obtain ⟨d, hd, hdx⟩ := hlift x hx
  rcases eq_or_eq_mul_of_map_eq hz hdx with h | h
  · rw [h]; exact hd
  · rw [h]; exact mul_mem hd hzD

theorem commutator_comap_le_centralizer (hker : ∀ k, π k = 1 → k ∈ center M) (y : M) :
    ⁅(centralizer {π y}).comap π, (centralizer {π y}).comap π⁆ ≤ centralizer {y} := by
  rw [commutator_le]
  intro a ha b hb
  rw [mem_centralizer_singleton_iff]
  have ha' := mem_centralizer_singleton_iff.1 (mem_comap.1 ha)
  have hb' := mem_centralizer_singleton_iff.1 (mem_comap.1 hb)
  exact (commute_of_commutatorElement hker ha'.symm hb'.symm).symm

end Preimage

namespace Setup

theorem centralizer_conj {X : Type*} [Group X] (k x : X) :
    centralizer {k * x * k⁻¹} = (centralizer {x}).map (MulAut.conj k).toMonoidHom := by
  ext w
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  change w * (k * x * k⁻¹) = k * x * k⁻¹ * w ↔ k⁻¹ * w * k * x = x * (k⁻¹ * w * k)
  constructor
  · intro h
    calc k⁻¹ * w * k * x = k⁻¹ * (w * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * x * k⁻¹ * w) * k := by rw [h]
      _ = x * (k⁻¹ * w * k) := by group
  · intro h
    calc w * (k * x * k⁻¹) = k * (k⁻¹ * w * k * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * w * k)) * k⁻¹ := by rw [h]
      _ = k * x * k⁻¹ * w := by group

end Setup

namespace SeitzSetup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  (S : SeitzSetup G L K)

omit [CharP K 2] in
include S in
theorem finite_field : Finite K := Nat.finite_of_card_ne_zero (by rw [S.card_field]; norm_num)

theorem sq_eq_tL_of_isConj_v
    {m : L} (hm : IsConj (S.π m) (rootX rootV 1)) : m * m = S.tL := by
  have := S.isPerfect
  exact mul_self_eq_of_isConj_rootX_v S.tL_ne_one S.π_eq_one_iff_tL S.card_field S.π_surjective
    S.ker_le_center hm

theorem sq_eq_one_of_isConj_c
    {m : L} (hm : IsConj (S.π m) (rootX rootC 1)) : m * m = 1 :=
  mul_self_eq_one_of_isConj_rootX_c S.tL_ne_one S.π_eq_one_iff_tL S.card_field S.π_surjective
    S.ker_le_center hm

theorem eq_t_of_isConj
    {y : G} (hyL : y ∈ L) (hy : IsConj S.t y) : y = S.t := by
  have := S.finite_field
  have := S.isPerfect
  by_contra hne
  obtain ⟨c, hc⟩ := isConj_iff.1 hy
  let yL : L := ⟨y, hyL⟩
  have hy2 : yL * yL = 1 := Subtype.ext (by
    change y * y = 1
    rw [← hc, show c * S.t * c⁻¹ * (c * S.t * c⁻¹) = c * (S.t * S.t) * c⁻¹ by group, S.t_mul_t,
      mul_one, mul_inv_cancel])
  have hyne1 : yL ≠ 1 := fun h => S.t_ne_one (by
    have h' : y = 1 := congrArg Subtype.val h
    rw [← hc] at h'
    rw [show S.t = c⁻¹ * (c * S.t * c⁻¹) * c by group, h', mul_one, inv_mul_cancel])
  have hynet : yL ≠ S.tL := fun h => hne (congrArg Subtype.val h)
  have hπy : S.π yL ≠ 1 := fun h => by
    rcases (S.π_eq_one_iff_tL yL).1 h with h | h
    exacts [hyne1 h, hynet h]
  have hπy2 : orderOf (S.π yL) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hy2, map_one]) hπy
  have hconj : IsConj (S.π yL) (rootX rootC 1) := by
    rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) _ hπy2 with h | h
    · exact h
    · exfalso
      have h' := S.sq_eq_tL_of_isConj_v h
      rw [hy2] at h'
      exact S.tL_ne_one h'.symm
  obtain ⟨k, hk⟩ := isConj_iff.1 hconj.symm
  set Z : Subgroup (adjointGroup .G2 K) := centralizer {S.π yL} with hZdef
  have hZ : Z = (centralizer {rootX rootC (1 : K)}).map (MulAut.conj k).toMonoidHom := by
    rw [hZdef, ← hk, Setup.centralizer_conj]
  have hZperf : ⁅Z, Z⁆ = Z := by
    rw [hZ, ← map_commutator, commutator_centralizer_rootX_c S.card_field]
  obtain ⟨m₀, hm₀⟩ := S.π_surjective (k * rootX rootV 1 * k⁻¹)
  have hm₀Z : S.π m₀ ∈ Z := by
    rw [hm₀, hZ]
    exact ⟨_, rootX_v_mem_centralizer_c, rfl⟩
  have hm₀2 : m₀ * m₀ = S.tL :=
    S.sq_eq_tL_of_isConj_v (by rw [hm₀]; exact isConj_iff.2 ⟨k⁻¹, by group⟩)
  set C := Z.comap S.π with hCdef
  have hCperf : ⁅C, C⁆ = C :=
    commutator_comap_eq S.π_surjective S.tL_ne_one S.π_eq_one_iff_tL S.ker_le_center hZperf
      hm₀Z hm₀2
  have hCy : C ≤ centralizer {yL} := by
    rw [← hCperf]
    exact commutator_comap_le_centralizer S.ker_le_center yL
  set CG := (C.map L.subtype).map (MulAut.conj c⁻¹).toMonoidHom with hCG
  have hCGperf : ⁅CG, CG⁆ = CG := by
    rw [hCG, ← map_commutator, ← map_commutator, hCperf]
  have hCGt : CG ≤ centralizer {S.t} := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hCy hx))
    simp only [Subgroup.coe_mul] at h
    change c⁻¹ * (x : G) * c⁻¹⁻¹ * S.t = S.t * (c⁻¹ * x * c⁻¹⁻¹)
    rw [inv_inv]
    calc c⁻¹ * (x : G) * c * S.t = c⁻¹ * ((x : G) * (c * S.t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * S.t * c⁻¹) * x) * c := by rw [hc]; exact congrArg (fun w => c⁻¹ * w * c) h
      _ = S.t * (c⁻¹ * x * c) := by group
  set Ut := (posU K).map (MulAut.conj k).toMonoidHom with hUt
  have hUtZ : Ut ≤ Z := by
    rw [hUt, hZ]
    exact map_mono posU_le_centralizer_c
  set SL := Ut.comap S.π with hSL
  have hSLC : SL ≤ C := comap_mono hUtZ
  have htSL : S.tL ∈ SL := by
    rw [hSL, mem_comap, (S.π_eq_one_iff_tL _).2 (Or.inr rfl)]
    exact one_mem _
  have hySL : yL ∈ SL := by
    rw [hSL, mem_comap, ← hk]
    exact ⟨_, rootX_mem_posU rootC_mem 1, rfl⟩
  have hcardSL : Nat.card SL = 2 ^ 13 := by
    have hzc : S.tL ∈ center L := S.tL_mem_center
    have h1 := card_le_two_mul S.π_surjective S.π_eq_one_iff_tL SL (fun _ => True)
    have h2 := two_mul_card_le S.π_eq_one_iff_tL S.tL_ne_one SL htSL (fun _ => True)
    have e1 : Nat.card {s : SL // True} = Nat.card SL :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    have e2 : Nat.card {q // q ∈ SL.map S.π ∧ True} = Nat.card Ut := by
      rw [hSL, map_comap_eq_self_of_surjective S.π_surjective]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun q => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)
    have hUtcard : Nat.card Ut = 2 ^ 12 := by
      rw [hUt, card_map_of_injective (MulAut.conj k).injective, card_posU S.card_field]
    rw [e1, e2, hUtcard] at h1 h2
    omega
  have hconjL : ∀ x ∈ SL, c⁻¹ * (x : G) * c ∈ L := fun x hx => by
    have hx2 : x ^ (2 ^ 13) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (hcardSL ▸ Subgroup.orderOf_dvd_natCard SL hx)
    have hmem : (MulAut.conj c⁻¹).toMonoidHom (L.subtype x) ∈ CG := ⟨_, ⟨x, hSLC hx, rfl⟩, rfl⟩
    have hpow : ((MulAut.conj c⁻¹).toMonoidHom (L.subtype x)) ^ (2 ^ 13) = 1 := by
      rw [← map_pow, ← map_pow, hx2, map_one, map_one]
    have h := S.mem_L_of_perfect hCGt hCGperf hmem hpow
    simpa [MulAut.conj_apply] using h
  have hyc : (⟨yL, hySL⟩ : SL) ∈ center SL := Subgroup.mem_center_iff.2 fun s => Subtype.ext (by
    have h := mem_centralizer_singleton_iff.1 (hCy (hSLC s.2))
    exact h)
  obtain ⟨-, h576⟩ := card_sq_lt S.card_field S.π_surjective S.tL_ne_one S.π_eq_one_iff_tL
    S.ker_le_center htSL hcardSL hyc hπy
  let ψ : SL →* L :=
    { toFun := fun s => ⟨c⁻¹ * ((s : L) : G) * c, hconjL s s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s s' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hψinj : Function.Injective ψ := fun s s' h => by
    have h' := congrArg (fun x : L => (x : G)) h
    change c⁻¹ * ((s : L) : G) * c = c⁻¹ * ((s' : L) : G) * c at h'
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  let e : SL ≃* ψ.range := MonoidHom.ofInjective hψinj
  have he : ∀ s : SL, ((e s : ψ.range) : L) = ψ s := fun s => rfl
  have hψy : ψ ⟨yL, hySL⟩ = S.tL := Subtype.ext (by
    change c⁻¹ * y * c = S.t
    rw [← hc]; group)
  have htS₁ : S.tL ∈ ψ.range := ⟨_, hψy⟩
  have hcardS₁ : Nat.card ψ.range = 2 ^ 13 := by rw [← Nat.card_congr e.toEquiv, hcardSL]
  have hac : e ⟨S.tL, htSL⟩ ∈ center ψ.range := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨s, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.1 S.tL_mem_center s)
  have hπa : S.π (e ⟨S.tL, htSL⟩) ≠ 1 := by
    rw [he]
    intro h
    rcases (S.π_eq_one_iff_tL _).1 h with h | h
    · have h' := congrArg (fun x : L => (x : G)) h
      change c⁻¹ * S.t * c = 1 at h'
      apply S.t_ne_one
      rw [show S.t = c * (c⁻¹ * S.t * c) * c⁻¹ by group, h', mul_one, mul_inv_cancel]
    · have h' := congrArg (fun x : L => (x : G)) h
      change c⁻¹ * S.t * c = S.t at h'
      apply hne
      calc y = c * S.t * c⁻¹ := hc.symm
        _ = c * (c⁻¹ * S.t * c) * c⁻¹ := by rw [h']
        _ = S.t := by group
  obtain ⟨h480, -⟩ := card_sq_lt S.card_field S.π_surjective S.tL_ne_one S.π_eq_one_iff_tL
    S.ker_le_center htS₁ hcardS₁ hac hπa
  rw [← card_sq_eq_of_mulEquiv e] at h480
  omega

end SeitzSetup

end CFSG.EvenSmallLie.GTwoFour
