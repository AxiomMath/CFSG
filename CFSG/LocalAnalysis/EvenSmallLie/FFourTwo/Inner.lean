module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Fusion
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.FFourTwo

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace Cover

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M) [Finite M]
  [Group.IsPerfect M]

omit [Group.IsPerfect M] in
theorem exists_conj_mem_Uhat
    {P : Subgroup M} (hP : IsPGroup 2 P) :
    ∃ c : M, ∀ p ∈ P, c * p * c⁻¹ ∈ C.Uhat := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  set U' := C.isPGroup_Uhat.toSylow C.not_two_dvd_index_Uhat
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q U'
  have hU' : ((U' : Sylow 2 M) : Subgroup M) = C.Uhat := IsPGroup.toSylow_coe _ _
  refine ⟨c, fun p hp => ?_⟩
  rw [← hU', ← hc, Sylow.coe_subgroup_smul]
  exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 (by
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hQ hp)

theorem exists_isConj_r8_of_mem
    {m : M} (h2 : m * m = 1) (h1 : m ≠ 1) (hz : m ≠ C.z) :
    ∃ r ∈ r8, IsConj m (Pc.nf C.gU r) := by
  have hP : IsPGroup 2 (zpowers m) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq, h2]) h1)
  obtain ⟨c, hc⟩ := C.exists_conj_mem_Uhat hP
  have hm := hc m (mem_zpowers m)
  obtain ⟨r, hr, hrc⟩ := C.exists_isConj_r8 hm
    (by rw [show c * m * c⁻¹ * (c * m * c⁻¹) = c * (m * m) * c⁻¹ by group, h2, mul_one,
      mul_inv_cancel])
    (fun h => h1 (by rwa [mul_inv_eq_one, mul_eq_left] at h))
    (fun h => hz (by rw [mul_inv_eq_iff_eq_mul, ← C.z_comm] at h; exact mul_left_cancel h))
  exact ⟨r, hr, (isConj_iff.2 ⟨c, rfl⟩).trans hrc⟩

theorem eq_z_of_hom
    (θ : C.Uhat →* M) (hθ : Function.Injective θ) {x : C.Uhat}
    (hx : θ x = C.z) : (x : M) = C.z := by
  obtain ⟨c, hc⟩ := C.exists_conj_mem_Uhat
    (C.isPGroup_Uhat.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective)
  let ψ : C.Uhat →* C.Uhat := ((MulAut.conj c).toMonoidHom.comp θ).codRestrict C.Uhat
    (fun u => hc _ ⟨u, rfl⟩)
  have hψ : Function.Injective ψ := fun u v h => hθ ((MulAut.conj c).injective
    (congrArg Subtype.val h))
  have h1 := C.aut_fixes_z ψ hψ
  have h2 : (ψ x : M) = C.z := by
    change c * θ x * c⁻¹ = C.z
    rw [hx, C.z_comm, mul_inv_cancel_right]
  have h3 : ψ x = ψ ⟨C.z, C.z_mem_Uhat⟩ := Subtype.ext (h2.trans h1.symm)
  exact congrArg Subtype.val (hψ h3)

end Cover

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  (S : Setup G L K)

omit [Finite G] in
variable (L) in
@[expose] def conjSub (g : G) : Subgroup L := (L.map (MulAut.conj g).toMonoidHom).comap L.subtype

omit [Finite G] in
theorem mem_conjSub {g : G} {l : L} : l ∈ conjSub L g ↔ g⁻¹ * (l : G) * g ∈ L := by
  rw [conjSub, mem_comap, mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem commute_conj {g h : G} (hh : h * (g * S.t * g⁻¹) = g * S.t * g⁻¹ * h) :
    g⁻¹ * h * g ∈ centralizer ({S.t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  calc g⁻¹ * h * g * S.t = g⁻¹ * (h * (g * S.t * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * S.t * g⁻¹ * h) * g := by rw [hh]
    _ = S.t * (g⁻¹ * h * g) := by group

theorem conj_mem_of_pow_three
    {g h : G} (hh : h * (g * S.t * g⁻¹) = g * S.t * g⁻¹ * h)
    (h3 : h ^ 3 = 1) : g⁻¹ * h * g ∈ L :=
  S.mem_L_of_pow_three (S.commute_conj hh) (by
    rw [show g⁻¹ * h * g = g⁻¹ * h * g⁻¹⁻¹ by rw [inv_inv], conj_pow, h3, mul_one,
      mul_inv_cancel])

theorem conj_mem_of_commute {g h : G} (hh : h * (g * S.t * g⁻¹) = g * S.t * g⁻¹ * h) {l : G}
    (hl : g⁻¹ * l * g ∈ L) : g⁻¹ * (h * l * h⁻¹) * g ∈ L := by
  have := S.conj_mem_L (S.commute_conj hh) hl
  rwa [show g⁻¹ * h * g * (g⁻¹ * l * g) * (g⁻¹ * h * g)⁻¹ = g⁻¹ * (h * l * h⁻¹) * g by group]
    at this

section Words

variable
    {g : G} {X : ℕ} (hX : ((Pc.nf S.cover.gU X : L) : G) = g * S.t * g⁻¹)
include hX

theorem hEl_mem_conjSub
    : ∀ a < 4, S.cover.hEl a * Pc.nf S.cover.gU X =
    Pc.nf S.cover.gU X * S.cover.hEl a → S.cover.hEl a ∈ conjSub L g := by
  intro a ha hc
  rw [mem_conjSub]
  refine S.conj_mem_of_pow_three ?_ ?_
  · rw [← hX]; exact_mod_cast congrArg Subtype.val hc
  · exact_mod_cast congrArg Subtype.val (S.cover.hEl_pow_three ha)

theorem conj_mem_conjSub
    : ∀ u : L, u * Pc.nf S.cover.gU X = Pc.nf S.cover.gU X * u →
    ∀ n ∈ conjSub L g, u * n * u⁻¹ ∈ conjSub L g := by
  intro u hu n hn
  rw [mem_conjSub] at hn ⊢
  have hu' : (u : G) * (g * S.t * g⁻¹) = g * S.t * g⁻¹ * u := by
    rw [← hX]; exact_mod_cast congrArg Subtype.val hu
  simpa using S.conj_mem_of_commute hu' hn

theorem eq_z_of_genOK
    (hXlt : X < 2 ^ 25) {ws : List (List (ℕ × ℕ))}
    (h : genOK X ws = true) : Pc.nf S.cover.gU X = S.cover.z := by
  have := S.isPerfect
  have hle := S.cover.Uhat_le_of_genOK hXlt (S.hEl_mem_conjSub hX) (S.conj_mem_conjSub hX) h
  let θ : S.cover.Uhat →* L :=
    ((MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp S.cover.Uhat.subtype)).codRestrict L
      fun u => by simpa using mem_conjSub.1 (hle u.2)
  have hθ : Function.Injective θ := fun u v huv => Subtype.ext (Subtype.ext
    ((MulAut.conj g⁻¹).injective (congrArg Subtype.val huv)))
  have hx : θ ⟨Pc.nf S.cover.gU X, S.cover.nf_mem hXlt⟩ = S.cover.z := by
    refine Subtype.ext ?_
    change g⁻¹ * ((Pc.nf S.cover.gU X : L) : G) * g⁻¹⁻¹ = S.t
    rw [hX]; group
  exact S.cover.eq_z_of_hom θ hθ hx

theorem false_of_witOK
    (hXlt : X < 2 ^ 25) {w : List (ℕ × ℕ)} (h : witOK X w = true) :
    False := by
  have := S.isPerfect
  obtain ⟨y, hy, hyy⟩ :=
    S.cover.exists_sq_of_witOK hXlt (S.hEl_mem_conjSub hX) (S.conj_mem_conjSub hX) h
  refine S.cover.mul_self_ne_z_of_mem ⟨g⁻¹ * y * g, mem_conjSub.1 hy⟩ (Subtype.ext ?_)
  change g⁻¹ * (y : G) * g * (g⁻¹ * y * g) = S.t
  have hyy' : (y : G) * y = g * S.t * g⁻¹ := by rw [← hX]; exact_mod_cast congrArg Subtype.val hyy
  calc g⁻¹ * (y : G) * g * (g⁻¹ * y * g) = g⁻¹ * ((y : G) * y) * g := by group
    _ = S.t := by rw [hyy']; group

end Words

theorem eq_t_of_isConj_of_mem
    {y : G} (hyL : y ∈ L) (hy : IsConj S.t y) : y = S.t := by
  have := S.isPerfect
  by_contra hyt
  obtain ⟨g, rfl⟩ := isConj_iff.1 hy
  have hy2 : (⟨g * S.t * g⁻¹, hyL⟩ : L) * ⟨g * S.t * g⁻¹, hyL⟩ = 1 := Subtype.ext (by
    change g * S.t * g⁻¹ * (g * S.t * g⁻¹) = 1
    rw [show g * S.t * g⁻¹ * (g * S.t * g⁻¹) = g * (S.t * S.t) * g⁻¹ by group, S.t_mul_t,
      mul_one, mul_inv_cancel])
  have hy1 : (⟨g * S.t * g⁻¹, hyL⟩ : L) ≠ 1 := fun h => S.t_ne_one (by
    have h' : g * S.t * g⁻¹ = 1 := congrArg Subtype.val h
    rwa [mul_inv_eq_one, mul_eq_left] at h')
  have hyz : (⟨g * S.t * g⁻¹, hyL⟩ : L) ≠ S.cover.z := fun h => hyt (congrArg Subtype.val h)
  obtain ⟨r, hr, hrc⟩ := S.cover.exists_isConj_r8_of_mem hy2 hy1 hyz
  obtain ⟨c, hc⟩ := isConj_iff.1 hrc
  have hX : ((Pc.nf S.cover.gU r : L) : G) = (c * g) * S.t * (c * g)⁻¹ := by
    rw [← hc]; change (c : G) * (g * S.t * g⁻¹) * (c : G)⁻¹ = _; group
  have hz24 : Pc.nf S.cover.gU (2 ^ 24) = S.cover.z := by rw [Pc.nf_two_pow, Cover.gU_24]
  have hne : ∀ r', r' < 2 ^ 25 → r' ≠ 2 ^ 24 → Pc.nf S.cover.gU r' ≠ S.cover.z := fun r' h1 h2 h =>
    h2 (S.cover.nf_inj h1 (by norm_num) (h.trans hz24.symm))
  obtain ⟨g1, g2, g3, g4⟩ := gen_spec
  obtain ⟨w1, w2, w3, w4⟩ := wit_spec
  simp only [r8, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hne _ (by norm_num) (by norm_num) (S.eq_z_of_genOK hX (by norm_num) g1)
  · exact hne _ (by norm_num) (by norm_num) (S.eq_z_of_genOK hX (by norm_num) g2)
  · exact hne _ (by norm_num) (by norm_num) (S.eq_z_of_genOK hX (by norm_num) g3)
  · exact hne _ (by norm_num) (by norm_num) (S.eq_z_of_genOK hX (by norm_num) g4)
  · exact S.false_of_witOK hX (by norm_num) w1
  · exact S.false_of_witOK hX (by norm_num) w2
  · exact S.false_of_witOK hX (by norm_num) w3
  · exact S.false_of_witOK hX (by norm_num) w4

theorem eq_t_of_isConj_of_mem_sup
    {y : G} (hy : y ∈ L ⊔ centralizer (L : Set G))
    (hyc : IsConj S.t y) : y = S.t := by
  have := S.isPerfect
  have hy2 : y ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := isConj_iff.1 hyc
    rw [sq, show g * S.t * g⁻¹ * (g * S.t * g⁻¹) = g * (S.t * S.t) * g⁻¹ by group, S.t_mul_t,
      mul_one, mul_inv_cancel]
  have hsq : ∀ a : L, a ^ 2 ∈ center L → a ^ 2 = 1 := fun a ha => by
    rcases (S.mem_center_iff _).1 ha with h | h
    · exact h
    · exact absurd (Subtype.ext (by rw [← sq]; exact h)) (S.cover.mul_self_ne_z_of_mem a)
  have hev : Even (Nat.card (center L)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine even_iff_two_dvd.2 ?_
    have := Subgroup.orderOf_dvd_natCard (center L) S.tL_mem_center
    rwa [show orderOf S.tL = 2 from by rw [← Subgroup.orderOf_coe]; exact S.orderOf_t] at this
  exact S.eq_t_of_isConj_of_mem
    (mem_of_sq_eq_one_of_mem_sup_centralizer S.center_facts.2.1 hev hsq hy hy2) hyc

end Setup

end CFSG.EvenSmallLie.FFourTwo
