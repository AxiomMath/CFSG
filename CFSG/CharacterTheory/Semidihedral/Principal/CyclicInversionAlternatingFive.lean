module

public import CFSG.CharacterTheory.Semidihedral.Principal.OddCentralAlternatingFiveSplit
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionSymmetricFour

public section

namespace CFSG.Semidihedral.Principal

universe u

namespace CyclicAlternatingFive

open Equiv

section SymmetricFive

@[expose] def genX : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def genY : alternatingGroup (Fin 5) :=
  ⟨swap 0 2 * swap 2 4, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem gen_relations : genX ^ 2 = 1 ∧ genY ^ 3 = 1 ∧ (genX * genY) ^ 5 = 1 ∧ genX ≠ 1 ∧
    genY ≠ 1 ∧ genX * genY ≠ 1 := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
theorem exists_conj_of_relations : ∀ u v : alternatingGroup (Fin 5), u ^ 2 = 1 → v ^ 3 = 1 →
    (u * v) ^ 5 = 1 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → ∃ s : Perm (Fin 5),
      s * (genX : Perm (Fin 5)) * s⁻¹ = u ∧ s * (genY : Perm (Fin 5)) * s⁻¹ = v := by
  decide +kernel

theorem eq_one_of_forall_commute : ∀ s : Perm (Fin 5),
    (∀ g : alternatingGroup (Fin 5), s * g = g * s) → s = 1 := by
  decide +kernel

theorem alternating_eq_one_of_forall_commute : ∀ g : alternatingGroup (Fin 5),
    (∀ h : alternatingGroup (Fin 5), g * h = h * g) → g = 1 := by
  decide +kernel

theorem nat_card_alternating_involutions :
    Nat.card {g : alternatingGroup (Fin 5) // g ^ 2 = 1 ∧ g ≠ 1} = 15 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem nat_card_odd_involutions :
    Nat.card {s : Perm (Fin 5) // Perm.sign s = -1 ∧ s ^ 2 = 1} = 10 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem alternating_involution_conj : ∀ g g' : alternatingGroup (Fin 5), g ^ 2 = 1 → g ≠ 1 →
    g' ^ 2 = 1 → g' ≠ 1 → ∃ c : alternatingGroup (Fin 5), c * g * c⁻¹ = g' := by
  decide +kernel

theorem isSwap_iff (s : Perm (Fin 5)) : s.IsSwap ↔ (Perm.sign s = -1 ∧ s ^ 2 = 1) := by
  unfold Perm.IsSwap
  revert s
  decide +kernel

theorem odd_involution_conj (s s' : Perm (Fin 5)) (hs : Perm.sign s = -1) (hs2 : s ^ 2 = 1)
    (hs' : Perm.sign s' = -1) (hs2' : s' ^ 2 = 1) : ∃ c : Perm (Fin 5), c * s * c⁻¹ = s' := by
  obtain ⟨a, b, hab, rfl⟩ := (isSwap_iff s).mpr ⟨hs, hs2⟩
  obtain ⟨a', b', hab', rfl⟩ := (isSwap_iff s').mpr ⟨hs', hs2'⟩
  exact isConj_iff.mp (Perm.isConj_swap hab hab')

theorem nat_card_alternating : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem eq_of_eq_gen (f g : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5))
    (hx : f genX = g genX) (hy : g genY = f genY) : f = g := by
  obtain ⟨hx2, hy3, hxy5, hx1, hy1, hxy1⟩ := gen_relations
  set E := MonoidHom.eqLocus f g with hE
  have hxE : genX ∈ E := hx
  have hyE : genY ∈ E := hy.symm
  have hxyE : genX * genY ∈ E := Subgroup.mul_mem _ hxE hyE
  have h2 : 2 ∣ Nat.card E := by
    have h1 := Subgroup.orderOf_dvd_natCard E hxE
    rwa [orderOf_eq_prime hx2 hx1] at h1
  have h3 : 3 ∣ Nat.card E := by
    have h1 := Subgroup.orderOf_dvd_natCard E hyE
    rwa [orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) hy3 hy1] at h1
  have h5 : 5 ∣ Nat.card E := by
    have h1 := Subgroup.orderOf_dvd_natCard E hxyE
    rwa [orderOf_eq_prime (p := 5) (hp := ⟨by norm_num⟩) hxy5 hxy1] at h1
  have h30 : 30 ∣ Nat.card E := by
    have h6 : 6 ∣ Nat.card E := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 6 5) h6 h5
  have hindex := E.card_mul_index
  rw [nat_card_alternating] at hindex
  have hE60 : Nat.card E ∣ 60 := Dvd.intro _ hindex
  have hcases : E.index = 1 ∨ E.index = 2 := by
    obtain ⟨k, hk⟩ := h30
    have hk' : 30 * k * E.index = 60 := by rw [← hk]; exact hindex
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hk'
        simp at hk'
      · exact h
    have : k * E.index = 2 := by nlinarith
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      right
      omega
    · left
      nlinarith
  have htop : E = ⊤ := by
    rcases hcases with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · have : E.Normal := Subgroup.normal_of_index_eq_two h2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E with hbot | htop
      · exact absurd ((Subgroup.mem_bot).mp (hbot ▸ hxE)) hx1
      · exact htop
  refine MonoidHom.ext fun a => ?_
  have ha : a ∈ E := by
    rw [htop]
    trivial
  exact ha

theorem conjNormal_surjective : Function.Surjective
    (MulAut.conjNormal : Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) := by
  intro β
  obtain ⟨hx2, hy3, hxy5, hx1, hy1, hxy1⟩ := gen_relations
  have hne : ∀ g : alternatingGroup (Fin 5), g ≠ 1 → β g ≠ 1 := fun g hg h =>
    hg (β.injective (h.trans (map_one β).symm))
  obtain ⟨s, hsx, hsy⟩ := exists_conj_of_relations (β genX) (β genY)
    (by rw [← map_pow, hx2, map_one]) (by rw [← map_pow, hy3, map_one])
    (by rw [← map_mul, ← map_pow, hxy5, map_one]) (hne _ hx1) (hne _ hy1)
    (by rw [← map_mul]; exact hne _ hxy1)
  refine ⟨s, MulEquiv.ext fun a => ?_⟩
  have h := eq_of_eq_gen (MulAut.conjNormal s).toMonoidHom β.toMonoidHom
    (Subtype.ext (show s * (genX : Perm (Fin 5)) * s⁻¹ = (β genX : Perm (Fin 5)) from hsx))
    (Subtype.ext (show (β genY : Perm (Fin 5)) = s * (genY : Perm (Fin 5)) * s⁻¹ from hsy.symm))
  exact DFunLike.congr_fun h a

theorem conjNormal_injective : Function.Injective
    (MulAut.conjNormal : Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  apply eq_one_of_forall_commute s
  intro g
  have h := congrArg (fun f : MulAut (alternatingGroup (Fin 5)) =>
    ((f g : alternatingGroup (Fin 5)) : Perm (Fin 5))) hs
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc s * (g : Perm (Fin 5)) = s * g * s⁻¹ * s := by group
    _ = g * s := by rw [h]

@[expose] noncomputable def autEquiv : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conjNormal ⟨conjNormal_injective, conjNormal_surjective⟩

theorem autEquiv_apply (s : Perm (Fin 5)) : autEquiv s = MulAut.conjNormal s := rfl

end SymmetricFive

section Conjugation

variable {G : Type*} [Group G] {n : ℕ}

@[expose] noncomputable def conjugationPermOf
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n))) (J : Subgroup G) [J.Normal]
    (φ : J ≃* alternatingGroup (Fin n)) : G →* Perm (Fin n) :=
  autE.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal)

theorem conjugationPermOf_apply_of_mem
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))
    (hautE : ∀ s, autE s = MulAut.conjNormal s) (J : Subgroup G) [J.Normal]
    (φ : J ≃* alternatingGroup (Fin n)) (j : J) :
    conjugationPermOf autE J φ j = (φ j : Perm (Fin n)) := by
  have h1 : MulAut.congr φ (MulAut.conjNormal (j : G)) = autE (φ j : Perm (Fin n)) := by
    rw [MulAut.conjNormal_val, hautE, MulAut.conjNormal_val]
    refine MulEquiv.ext fun g => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]
  unfold conjugationPermOf
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, h1, MulEquiv.symm_apply_apply]

theorem conjugationPermOf_eq_one_iff
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n))) (J : Subgroup G) [J.Normal]
    (φ : J ≃* alternatingGroup (Fin n)) (h : G) :
    conjugationPermOf autE J φ h = 1 ↔ h ∈ Subgroup.centralizer (J : Set G) := by
  unfold conjugationPermOf
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 j hj
    have h2 := congrArg (fun f : MulAut J => ((f ⟨j, hj⟩ : J) : G)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc j * h = h * j * h⁻¹ * h := by rw [h2]
      _ = h * j := by group
  · intro h1
    refine MulEquiv.ext fun j => Subtype.ext ?_
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h1 j j.2, mul_inv_cancel_right]

end Conjugation

section Quotient

open scoped Classical

variable {H : Type u} [Group H] (W : Subgroup H) [W.Normal]

abbrev centralizerImage : Subgroup (H ⧸ W) :=
  (Subgroup.centralizer (W : Set H)).map (QuotientGroup.mk' W)

theorem mk_mem_centralizerImage_iff (hWK : W ≤ Subgroup.centralizer (W : Set H)) (h : H) :
    (h : H ⧸ W) ∈ centralizerImage W ↔ h ∈ Subgroup.centralizer (W : Set H) := by
  change QuotientGroup.mk' W h ∈ _ ↔ _
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hWK)]

theorem centralizerImage_normal (hindex : (Subgroup.centralizer (W : Set H)).index = 2) :
    (centralizerImage W).Normal :=
  (Subgroup.normal_of_index_eq_two hindex).map _ (QuotientGroup.mk'_surjective W)

theorem nonempty_centralizerImage_equiv {n : ℕ}
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin n)) :
    Nonempty (centralizerImage W ≃* alternatingGroup (Fin n)) := by
  let f : Subgroup.centralizer (W : Set H) →* H ⧸ W :=
    (QuotientGroup.mk' W).comp (Subgroup.centralizer (W : Set H)).subtype
  have hker : f.ker = W.subgroupOf (Subgroup.centralizer (W : Set H)) := by
    ext k
    simp [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = centralizerImage W := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans ψ))⟩

theorem eq_one_of_mem_centralizer_of_mem {n : ℕ}
    (hcenter : ∀ a : alternatingGroup (Fin n), (∀ b, a * b = b * a) → a = 1)
    (φA : centralizerImage W ≃* alternatingGroup (Fin n)) (g : H ⧸ W)
    (hg : g ∈ Subgroup.centralizer (centralizerImage W : Set (H ⧸ W)))
    (hgA : g ∈ centralizerImage W) : g = 1 := by
  have h1 : φA ⟨g, hgA⟩ = 1 := by
    apply hcenter
    intro b
    obtain ⟨a, rfl⟩ := φA.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg a a.2).symm
  exact congrArg Subtype.val (φA.injective (h1.trans (map_one φA).symm))

variable [Finite H]

theorem mem_of_mem_centralizer {n : ℕ} (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hcenter : ∀ a : alternatingGroup (Fin n), (∀ b, a * b = b * a) → a = 1)
    (φA : centralizerImage W ≃* alternatingGroup (Fin n)) (P : Sylow 2 H)
    (eP : (P : Subgroup H) ≃* DihedralGroup 4) (g : H ⧸ W)
    (hg : g ∈ Subgroup.centralizer (centralizerImage W : Set (H ⧸ W))) :
    g ∈ centralizerImage W := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  rw [mk_mem_centralizerImage_iff W hWK]
  by_contra hhK
  have hh2W : h ^ 2 ∈ W := by
    have h1 : ((h ^ 2 : H) : H ⧸ W) ∈ centralizerImage W :=
      (mk_mem_centralizerImage_iff W hWK _).mpr (Subgroup.sq_mem_of_index_two hindex h)
    have h2 : ((h ^ 2 : H) : H ⧸ W) ∈
        Subgroup.centralizer (centralizerImage W : Set (H ⧸ W)) := by
      rw [QuotientGroup.mk_pow]
      exact Subgroup.pow_mem _ hg 2
    exact (QuotientGroup.eq_one_iff _).mp (eq_one_of_mem_centralizer_of_mem W hcenter φA _ h2 h1)
  obtain ⟨s, hs⟩ := hodd
  have hm : (h ^ 2) ^ Nat.card W = 1 := by
    have h1 : (⟨h ^ 2, hh2W⟩ : W) ^ Nat.card W = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  obtain ⟨z, hz⟩ : ∃ z, z = h ^ Nat.card W := ⟨_, rfl⟩
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, mul_comm, pow_mul, hm]
  have hzK : z ∉ Subgroup.centralizer (W : Set H) := by
    intro hzK
    apply hhK
    have hsK : (h ^ 2) ^ s ∈ Subgroup.centralizer (W : Set H) :=
      Subgroup.pow_mem _ (Subgroup.sq_mem_of_index_two hindex h) s
    have heq : h = ((h ^ 2) ^ s)⁻¹ * z := by
      rw [hz, hs, pow_succ h (2 * s), pow_mul h 2 s, inv_mul_cancel_left]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsK) hzK
  have hz1 : z ≠ 1 := fun h1 => hzK (h1 ▸ Subgroup.one_mem _)
  have hzC : (z : H ⧸ W) ∈ Subgroup.centralizer (centralizerImage W : Set (H ⧸ W)) := by
    rw [hz, QuotientGroup.mk_pow]
    exact Subgroup.pow_mem _ hg _
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨P', hP'⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, hzord, pow_one] :
      Nat.card (Subgroup.zpowers z) = 2 ^ 1)).exists_le_sylow
  have hzP' : z ∈ (P' : Subgroup H) := hP' (Subgroup.mem_zpowers z)
  let e' : (P' : Subgroup H) ≃* DihedralGroup 4 := (Sylow.equiv P P').symm.trans eP
  have hP'card : Nat.card (P' : Subgroup H) = 8 := by
    rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card]
  have hKn : (Subgroup.centralizer (W : Set H)).Normal := Subgroup.normal_of_index_eq_two hindex
  have hrel : (Subgroup.centralizer (W : Set H)).relIndex (P' : Subgroup H) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (H := Subgroup.centralizer (W : Set H))
      (K := (P' : Subgroup H))
    rw [hindex] at hdvd
    have hne : (Subgroup.centralizer (W : Set H)).relIndex (P' : Subgroup H) ≠ 1 := fun h1 =>
      hzK (Subgroup.relIndex_eq_one.mp h1 hzP')
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne
    · exact h2
  have hcardKP : Nat.card ((Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H)) =
      2 ^ 2 := by
    have h1 := Subgroup.card_mul_index
      ((Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H))
    change _ * (Subgroup.centralizer (W : Set H)).relIndex (P' : Subgroup H) = _ at h1
    rw [hrel, hP'card] at h1
    omega
  have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardKP
  have hWP : ∀ x ∈ W, x ∈ (P' : Subgroup H) → x = 1 := by
    intro x hxW hxP
    have h1 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hxW
    have h2 : orderOf x ∣ 2 ^ 3 := by
      have h3 := Subgroup.orderOf_dvd_natCard _ hxP
      rw [hP'card] at h3
      norm_num
      exact h3
    have hcop : Nat.Coprime (2 ^ 3) (Nat.card W) :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr ⟨s, hs⟩)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1)
  have hzcomm : ∀ x ∈ (P' : Subgroup H), x ∈ Subgroup.centralizer (W : Set H) → Commute x z := by
    intro x hxP hxK
    have h1 : ((x : H) : H ⧸ W) * (z : H ⧸ W) = (z : H ⧸ W) * (x : H ⧸ W) :=
      Subgroup.mem_centralizer_iff.mp hzC _ ((mk_mem_centralizerImage_iff W hWK x).mpr hxK)
    have h2 : x * z * x⁻¹ * z⁻¹ ∈ W := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1]
      group
    have h3 : x * z * x⁻¹ * z⁻¹ ∈ (P' : Subgroup H) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxP hzP')
        (Subgroup.inv_mem _ hxP)) (Subgroup.inv_mem _ hzP')
    have h4 := hWP _ h2 h3
    calc x * z = x * z * x⁻¹ * z⁻¹ * (z * x) := by group
      _ = z * x := by rw [h4, one_mul]
  have hKcomm : ∀ x ∈ (P' : Subgroup H), x ∈ Subgroup.centralizer (W : Set H) →
      ∀ y ∈ (P' : Subgroup H), y ∈ Subgroup.centralizer (W : Set H) → Commute x y := by
    intro x hxP hxK y hyP hyK
    have h1 := hab.is_comm.comm
      (⟨⟨x, hxP⟩, hxK⟩ : (Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H))
      ⟨⟨y, hyP⟩, hyK⟩
    exact congrArg (fun t : (Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H) =>
      ((t : (P' : Subgroup H)) : H)) h1
  have hdecomp : ∀ x ∈ (P' : Subgroup H), ∃ y ∈ (P' : Subgroup H),
      y ∈ Subgroup.centralizer (W : Set H) ∧ (x = y ∨ x = y * z) := by
    intro x hxP
    by_cases hxK : x ∈ Subgroup.centralizer (W : Set H)
    · exact ⟨x, hxP, hxK, Or.inl rfl⟩
    · refine ⟨x * z, Subgroup.mul_mem _ hxP hzP',
        (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hxK hzK), Or.inr ?_⟩
      rw [mul_assoc, ← pow_two, hz2, mul_one]
  have hcommP : ∀ x ∈ (P' : Subgroup H), ∀ y ∈ (P' : Subgroup H), Commute x y := by
    intro x hxP y hyP
    obtain ⟨x', hx'P, hx'K, hx⟩ := hdecomp x hxP
    obtain ⟨y', hy'P, hy'K, hy⟩ := hdecomp y hyP
    have hxy := hKcomm x' hx'P hx'K y' hy'P hy'K
    have hxz := hzcomm x' hx'P hx'K
    have hyz := hzcomm y' hy'P hy'K
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy
    · exact hxy.mul_right hxz
    · exact hxy.mul_left hyz.symm
    · exact (hxy.mul_right hxz).mul_left (hyz.symm.mul_right (Commute.refl z))
  obtain ⟨x, y, hxy⟩ := CyclicSymmetricFour.dihedral_not_commutative
  apply hxy
  have h1 : e'.symm x * e'.symm y = e'.symm y * e'.symm x :=
    Subtype.ext (hcommP _ (e'.symm x).2 _ (e'.symm y).2).eq
  simpa using congrArg e' h1

theorem card_quotient {n : ℕ} (hn : 2 ≤ n) (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin n)) :
    Nat.card (H ⧸ W) = Nat.card (Perm (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup W
  have h2 := (Subgroup.centralizer (W : Set H)).card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (W.subgroupOf (Subgroup.centralizer (W : Set H)))
  rw [Nat.card_congr ψ.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at h3
  rw [hindex, h3] at h2
  have h4 := two_mul_nat_card_alternatingGroup (α := Fin n)
  have hW : 0 < Nat.card W := Nat.card_pos
  have h5 : Nat.card (H ⧸ W) * Nat.card W = Nat.card (Perm (Fin n)) * Nat.card W := by
    rw [← h1, ← h2, ← h4]
    ring
  exact Nat.eq_of_mul_eq_mul_right hW h5

theorem exists_perm_hom {n : ℕ} (hn : 2 ≤ n)
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))
    (hautE : ∀ s, autE s = MulAut.conjNormal s)
    (hcenter : ∀ a : alternatingGroup (Fin n), (∀ b, a * b = b * a) → a = 1)
    (hodd : Odd (Nat.card W)) (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin n)) (P : Sylow 2 H) (eP : (P : Subgroup H) ≃* DihedralGroup 4) :
    ∃ σH : H →* Perm (Fin n), Function.Surjective σH ∧ (∀ h, σH h = 1 ↔ h ∈ W) ∧
      ∀ h, h ∈ Subgroup.centralizer (W : Set H) ↔ σH h ∈ alternatingGroup (Fin n) := by
  obtain ⟨φA⟩ := nonempty_centralizerImage_equiv W ψ
  have := centralizerImage_normal W hindex
  set σX := conjugationPermOf autE (centralizerImage W) φA with hσX
  have hinj : Function.Injective σX := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hσX, conjugationPermOf_eq_one_iff] at hg
    exact eq_one_of_mem_centralizer_of_mem W hcenter φA g hg
      (mem_of_mem_centralizer W hodd hWK hindex hcenter φA P eP g hg)
  have hbij : Function.Bijective σX :=
    hinj.bijective_of_nat_card_le (by rw [card_quotient W hn hWK hindex ψ])
  refine ⟨σX.comp (QuotientGroup.mk' W), hbij.2.comp (QuotientGroup.mk'_surjective W),
    fun h => ?_, fun h => ?_⟩
  · rw [MonoidHom.comp_apply, ← map_one σX, hinj.eq_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  · constructor
    · intro hh
      have h1 : σX (h : H ⧸ W) =
          (φA ⟨(h : H ⧸ W), (mk_mem_centralizerImage_iff W hWK h).mpr hh⟩ : Perm (Fin n)) :=
        conjugationPermOf_apply_of_mem autE hautE _ φA ⟨_, _⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, h1]
      exact (φA _).2
    · intro hs
      obtain ⟨a, ha⟩ := φA.surjective ⟨_, hs⟩
      have h1 : σX (a : H ⧸ W) = (φA a : Perm (Fin n)) :=
        conjugationPermOf_apply_of_mem autE hautE _ φA a
      rw [ha] at h1
      have h2 : (a : H ⧸ W) = (h : H ⧸ W) := hinj h1
      rw [← mk_mem_centralizerImage_iff W hWK, ← h2]
      exact a.2

end Quotient

section Involutions

variable {H : Type u} [Group H] (W : Subgroup H) {n : ℕ} (σH : H →* Perm (Fin n))

theorem sq_eq_one_of_not_mem (hodd : Odd (Nat.card W))
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) {h : H}
    (hh : h ∉ Subgroup.centralizer (W : Set H)) (hh2 : h ^ 2 ∈ W) : h ^ 2 = 1 := by
  have h1 := hinv h hh (h ^ 2) hh2
  have h2 : h * h ^ 2 * h⁻¹ = h ^ 2 := by group
  rw [h2] at h1
  apply CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd hh2
  rw [pow_two (h ^ 2)]
  nth_rewrite 2 [h1]
  exact mul_inv_cancel _

theorem inner_eq_of_perm_eq (hodd : Odd (Nat.card W))
    (hσker : ∀ h, σH h = 1 ↔ h ∈ W) {u u' : H} (hu : u ∈ Subgroup.centralizer (W : Set H))
    (hu2 : u ^ 2 = 1) (hu'2 : u' ^ 2 = 1) (h : σH u = σH u') : u = u' := by
  have hw : u⁻¹ * u' ∈ W := (hσker _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
  have hc : Commute u (u⁻¹ * u') := (Subgroup.mem_centralizer_iff.mp hu _ hw).symm
  have hw2 : (u⁻¹ * u') ^ 2 = 1 := by
    have h1 : u' = u * (u⁻¹ * u') := by group
    rw [h1, hc.mul_pow, hu2, one_mul] at hu'2
    exact hu'2
  have hw1 := CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd hw hw2
  calc u = u * (u⁻¹ * u') := by rw [hw1, mul_one]
    _ = u' := by group

theorem card_inner_involutions (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hσsurj : Function.Surjective σH)
    (hσker : ∀ h, σH h = 1 ↔ h ∈ W)
    (hσK : ∀ h, h ∈ Subgroup.centralizer (W : Set H) ↔ σH h ∈ alternatingGroup (Fin n)) :
    Nat.card {u : H // u ∈ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
      Nat.card {g : alternatingGroup (Fin n) // g ^ 2 = 1 ∧ g ≠ 1} := by
  have hsq : ∀ u : H, orderOf u = 2 → u ^ 2 = 1 := fun u hu => by
    rw [← hu]
    exact pow_orderOf_eq_one u
  refine Nat.card_eq_of_bijective (fun u => ⟨⟨σH u, (hσK u).mp u.2.1⟩, ?_, ?_⟩) ⟨?_, ?_⟩
  · apply Subtype.ext
    change σH u ^ 2 = 1
    rw [← map_pow, hsq u u.2.2, map_one]
  · intro h1
    have h2 : σH u = 1 := congrArg Subtype.val h1
    have hu1 := CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd ((hσker u).mp h2) (hsq u u.2.2)
    have h3 := u.2.2
    rw [hu1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  · intro u u' h
    have h1 : σH u = σH u' := congrArg (fun g => ((g.1 : alternatingGroup (Fin n)) :
      Perm (Fin n))) h
    exact Subtype.ext (inner_eq_of_perm_eq W σH hodd hσker u.2.1 (hsq u u.2.2) (hsq u' u'.2.2) h1)
  · rintro ⟨g, hg2, hg1⟩
    obtain ⟨h, hh⟩ := hσsurj g
    have hhK : h ∈ Subgroup.centralizer (W : Set H) := (hσK h).mpr (hh ▸ g.2)
    have hh2 : h ^ 2 ∈ W := (hσker _).mp (by
      rw [map_pow, hh]
      exact congrArg Subtype.val hg2)
    obtain ⟨y, hyW, hy⟩ := CyclicSymmetricFour.exists_sq_eq W hodd (h ^ 2)⁻¹
      (Subgroup.inv_mem _ hh2)
    have hc : Commute h y := (Subgroup.mem_centralizer_iff.mp hhK y hyW).symm
    have hσy : σH y = 1 := (hσker y).mpr hyW
    have hu2 : (h * y) ^ 2 = 1 := by rw [hc.mul_pow, hy, mul_inv_cancel]
    have hσu : σH (h * y) = g := by rw [map_mul, hσy, mul_one, hh]
    have hu1 : h * y ≠ 1 := fun h1 => hg1 (Subtype.ext (by rw [← hσu, h1, map_one]; rfl))
    refine ⟨⟨h * y, Subgroup.mul_mem _ hhK (hWK hyW), orderOf_eq_prime hu2 hu1⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hσu

theorem card_outer_involutions (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hσsurj : Function.Surjective σH) (hσker : ∀ h, σH h = 1 ↔ h ∈ W)
    (hσK : ∀ h, h ∈ Subgroup.centralizer (W : Set H) ↔ σH h ∈ alternatingGroup (Fin n)) :
    Nat.card {u : H // u ∉ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
      Nat.card W * Nat.card {s : Perm (Fin n) // Perm.sign s = -1 ∧ s ^ 2 = 1} := by
  have hodd_not : ∀ s : Perm (Fin n), Perm.sign s = -1 → s ∉ alternatingGroup (Fin n) :=
    fun s hs h => by
      rw [Perm.mem_alternatingGroup, hs] at h
      exact absurd h (by decide)
  choose ℓ hℓ using hσsurj
  have hℓK : ∀ s : {s : Perm (Fin n) // Perm.sign s = -1 ∧ s ^ 2 = 1},
      ℓ s ∉ Subgroup.centralizer (W : Set H) := fun s h =>
    hodd_not s.1 s.2.1 (by rw [← hℓ s.1]; exact (hσK _).mp h)
  have hℓ2 : ∀ s : {s : Perm (Fin n) // Perm.sign s = -1 ∧ s ^ 2 = 1}, ℓ s ^ 2 = 1 := fun s =>
    sq_eq_one_of_not_mem W hodd hinv (hℓK s) ((hσker _).mp (by rw [map_pow, hℓ, s.2.2]))
  have hmem : ∀ (w : W) (s : {s : Perm (Fin n) // Perm.sign s = -1 ∧ s ^ 2 = 1}),
      (w : H) * ℓ s ∉ Subgroup.centralizer (W : Set H) ∧ orderOf ((w : H) * ℓ s) = 2 := by
    intro w s
    have hK : (w : H) * ℓ s ∉ Subgroup.centralizer (W : Set H) := fun h => hℓK s (by
      have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWK w.2)) h
      rwa [inv_mul_cancel_left] at h1)
    refine ⟨hK, orderOf_eq_prime ?_ fun h1 => hK (h1 ▸ Subgroup.one_mem _)⟩
    rw [CyclicSymmetricFour.sq_mul_of_inverts (hinv _ (hℓK s) w w.2), hℓ2]
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective (fun x => ⟨(x.1 : H) * ℓ x.2, hmem x.1 x.2⟩) ⟨?_, ?_⟩
  · rintro ⟨w, s⟩ ⟨w', s'⟩ h
    have h1 : (w : H) * ℓ s = (w' : H) * ℓ s' := congrArg Subtype.val h
    have h2 : σH ((w : H) * ℓ s) = σH ((w' : H) * ℓ s') := by rw [h1]
    rw [map_mul, map_mul, (hσker _).mpr w.2, (hσker _).mpr w'.2, one_mul, one_mul, hℓ, hℓ] at h2
    have hs : s = s' := Subtype.ext h2
    subst hs
    have hw : w = w' := Subtype.ext (mul_right_cancel h1)
    rw [hw]
  · rintro ⟨u, huK, hu⟩
    have hsK : σH u ∉ alternatingGroup (Fin n) := fun h => huK ((hσK u).mpr h)
    have hsign : Perm.sign (σH u) = -1 := by
      rcases Int.units_eq_one_or (Perm.sign (σH u)) with h | h
      · exact absurd (Perm.mem_alternatingGroup.mpr h) hsK
      · exact h
    have hsq : σH u ^ 2 = 1 := by
      rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
    let s : {s : Perm (Fin n) // Perm.sign s = -1 ∧ s ^ 2 = 1} := ⟨σH u, hsign, hsq⟩
    have hw : u * (ℓ s)⁻¹ ∈ W := (hσker _).mp (by rw [map_mul, map_inv, hℓ, mul_inv_cancel])
    refine ⟨(⟨u * (ℓ s)⁻¹, hw⟩, s), ?_⟩
    apply Subtype.ext
    change u * (ℓ s)⁻¹ * ℓ s = u
    group

theorem isConj_involutions_iff (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hσsurj : Function.Surjective σH) (hσker : ∀ h, σH h = 1 ↔ h ∈ W)
    (hσK : ∀ h, h ∈ Subgroup.centralizer (W : Set H) ↔ σH h ∈ alternatingGroup (Fin n))
    (hconjA : ∀ g g' : alternatingGroup (Fin n), g ^ 2 = 1 → g ≠ 1 → g' ^ 2 = 1 → g' ≠ 1 →
      ∃ c : alternatingGroup (Fin n), c * g * c⁻¹ = g')
    (hconjS : ∀ s s' : Perm (Fin n), Perm.sign s = -1 → s ^ 2 = 1 → Perm.sign s' = -1 →
      s' ^ 2 = 1 → ∃ c : Perm (Fin n), c * s * c⁻¹ = s')
    (u v : H) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v ↔ (u ∈ Subgroup.centralizer (W : Set H) ↔ v ∈ Subgroup.centralizer (W : Set H)) := by
  have hKn := Subgroup.normal_of_index_eq_two hindex
  have hsq : ∀ x : H, orderOf x = 2 → x ^ 2 = 1 := fun x hx => by
    rw [← hx]
    exact pow_orderOf_eq_one x
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    constructor
    · intro huK
      rw [← hc]
      exact hKn.conj_mem u huK c
    · intro hvK
      have h1 : u = c⁻¹ * v * c⁻¹⁻¹ := by rw [← hc]; group
      rw [h1]
      exact hKn.conj_mem v hvK c⁻¹
  intro huv
  have hσne : ∀ x : H, orderOf x = 2 → σH x ≠ 1 := fun x hx h1 => by
    have hx1 := CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd ((hσker x).mp h1) (hsq x hx)
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  by_cases huK : u ∈ Subgroup.centralizer (W : Set H)
  · have hvK := huv.mp huK
    have hu' : (⟨σH u, (hσK u).mp huK⟩ : alternatingGroup (Fin n)) ^ 2 = 1 :=
      Subtype.ext (by change σH u ^ 2 = 1; rw [← map_pow, hsq u hu, map_one])
    have hv' : (⟨σH v, (hσK v).mp hvK⟩ : alternatingGroup (Fin n)) ^ 2 = 1 :=
      Subtype.ext (by change σH v ^ 2 = 1; rw [← map_pow, hsq v hv, map_one])
    obtain ⟨c, hc⟩ := hconjA _ _ hu' (fun h => hσne u hu (congrArg Subtype.val h)) hv'
      (fun h => hσne v hv (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := hσsurj c
    have hkK : k ∈ Subgroup.centralizer (W : Set H) := (hσK k).mpr (hk ▸ c.2)
    refine isConj_iff.mpr ⟨k, ?_⟩
    apply inner_eq_of_perm_eq W σH hodd hσker (hKn.conj_mem u huK k)
      (by rw [conj_pow, hsq u hu, mul_one, mul_inv_cancel]) (hsq v hv)
    rw [map_mul, map_mul, map_inv, hk]
    exact congrArg Subtype.val hc
  · have hvK : v ∉ Subgroup.centralizer (W : Set H) := fun h => huK (huv.mpr h)
    have hsign : ∀ x : H, x ∉ Subgroup.centralizer (W : Set H) → Perm.sign (σH x) = -1 := by
      intro x hx
      rcases Int.units_eq_one_or (Perm.sign (σH x)) with h | h
      · exact absurd ((hσK x).mpr (Perm.mem_alternatingGroup.mpr h)) hx
      · exact h
    obtain ⟨c, hc⟩ := hconjS (σH u) (σH v) (hsign u huK)
      (by rw [← map_pow, hsq u hu, map_one]) (hsign v hvK) (by rw [← map_pow, hsq v hv, map_one])
    obtain ⟨g, hg⟩ := hσsurj c
    have hw : g * u * g⁻¹ * v⁻¹ ∈ W := (hσker _).mp (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, hc, mul_inv_cancel])
    obtain ⟨y, hyW, hy⟩ := CyclicSymmetricFour.exists_sq_eq W hodd (g * u * g⁻¹ * v⁻¹)⁻¹
      (Subgroup.inv_mem _ hw)
    have hinvy : v * y⁻¹ * v⁻¹ = y := by
      rw [hinv v hvK y⁻¹ (Subgroup.inv_mem _ hyW), inv_inv]
    have hcomm : y * (g * u * g⁻¹ * v⁻¹) = (g * u * g⁻¹ * v⁻¹) * y :=
      Subgroup.mem_centralizer_iff.mp (hWK hw) y hyW
    refine isConj_iff.mpr ⟨y * g, ?_⟩
    calc y * g * u * (y * g)⁻¹ = y * (g * u * g⁻¹ * v⁻¹) * (v * y⁻¹ * v⁻¹) * v := by group
      _ = y * (g * u * g⁻¹ * v⁻¹) * y * v := by rw [hinvy]
      _ = y ^ 2 * (g * u * g⁻¹ * v⁻¹) * v := by
        rw [mul_assoc y, ← hcomm, pow_two, mul_assoc y y]
      _ = v := by rw [hy, inv_mul_cancel, one_mul]

variable [Finite H]

theorem card_centralizer_mul (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hσsurj : Function.Surjective σH) (hσker : ∀ h, σH h = 1 ↔ h ∈ W)
    (hσK : ∀ h, h ∈ Subgroup.centralizer (W : Set H) ↔ σH h ∈ alternatingGroup (Fin n))
    (hconjA : ∀ g g' : alternatingGroup (Fin n), g ^ 2 = 1 → g ≠ 1 → g' ^ 2 = 1 → g' ≠ 1 →
      ∃ c : alternatingGroup (Fin n), c * g * c⁻¹ = g')
    (hconjS : ∀ s s' : Perm (Fin n), Perm.sign s = -1 → s ^ 2 = 1 → Perm.sign s' = -1 →
      s' ^ 2 = 1 → ∃ c : Perm (Fin n), c * s * c⁻¹ = s')
    (u : H) (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer {u}) *
      Nat.card {v : H // (v ∈ Subgroup.centralizer (W : Set H) ↔
        u ∈ Subgroup.centralizer (W : Set H)) ∧ orderOf v = 2} = Nat.card H := by
  rw [← CyclicSymmetricFour.card_centralizer_mul_card_conj u]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun h => ?_, fun h => ?_⟩)
  · exact (isConj_involutions_iff W σH hodd hWK hinv hindex hσsurj hσker hσK hconjA hconjS v u
      h.2 hu).mpr h.1
  · have hv : orderOf v = 2 := by
      rw [← hu]
      obtain ⟨c, hc⟩ := isConj_iff.mp h
      rw [← hc]
      exact ((MulAut.conj c).orderOf_eq v).symm
    exact ⟨(isConj_involutions_iff W σH hodd hWK hinv hindex hσsurj hσker hσK hconjA hconjS v u
      hv hu).mp h, hv⟩

end Involutions

section Extension

theorem mem_or_mul_mem_of_mem_sup {G : Type*} [Group G] (J : Subgroup G) [J.Normal] {x : G}
    (hx : x ^ 2 = 1) (e : G) (he : e ∈ J ⊔ Subgroup.zpowers x) : e ∈ J ∨ e * x ∈ J := by
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at he
  obtain ⟨j, hj, y, hy, rfl⟩ := he
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hx]
  have hxk : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, hx2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hxk, h0, zpow_zero, mul_one]
    exact hj
  · right
    rw [hxk, h1, zpow_one, mul_assoc, ← pow_two, hx, mul_one]
    exact hj

end Extension

end CyclicAlternatingFive

open CyclicAlternatingFive

theorem odd_cyclic_inversion_normalizer_alternating_five_centralizer_splits_by_sign
    {H : Type u} [Group H] [Finite H] (W : Subgroup H) [W.Normal] [IsCyclic W]
    (hodd : Odd (Nat.card W)) (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hquot : Nonempty (Subgroup.centralizer (W : Set H) ⧸
      W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃* alternatingGroup (Fin 5)))
    (hdihedral : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4)) :
    ∃ (J : Subgroup H) (x : H) (E : Subgroup H) (σ : E ≃* Equiv.Perm (Fin 5)),
      J = (commutator (Subgroup.centralizer (W : Set H))).map
        (Subgroup.centralizer (W : Set H)).subtype ∧
      W ⊔ J = Subgroup.centralizer (W : Set H) ∧ W ⊓ J = ⊥ ∧
      (∀ w ∈ W, ∀ j ∈ J, w * j = j * w) ∧ J.Normal ∧ Nonempty (J ≃* alternatingGroup (Fin 5)) ∧
      x ∉ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2 ∧ E = J ⊔ Subgroup.zpowers x ∧
      W ⊔ E = ⊤ ∧ W ⊓ E = ⊥ ∧
      (∀ e : E, (e : H) ∈ J ↔ σ e ∈ alternatingGroup (Fin 5)) ∧
      (∀ e : E, ∀ w ∈ W,
        (e : H) * w * (e : H)⁻¹ = w ^ ((Equiv.Perm.sign (σ e) : ℤˣ) : ℤ)) ∧
      Nat.card (Subgroup.centralizer (W : Set H)) = 60 * Nat.card W ∧
      Nat.card H = 120 * Nat.card W ∧
      (∀ u : H, orderOf u = 2 → u ∈ J ∨ u ∉ Subgroup.centralizer (W : Set H)) ∧
      Nat.card {u : H // u ∈ J ∧ orderOf u = 2} = 15 ∧
      Nat.card {u : H // u ∉ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
        10 * Nat.card W ∧
      (∀ u v : H, orderOf u = 2 → orderOf v = 2 → (IsConj u v ↔ (u ∈ J ↔ v ∈ J))) ∧
      (∀ u ∈ J, orderOf u = 2 → Nat.card (Subgroup.centralizer {u}) = 8 * Nat.card W) ∧
      (∀ u : H, u ∉ Subgroup.centralizer (W : Set H) → orderOf u = 2 →
        Nat.card (Subgroup.centralizer {u}) = 12) ∧
      ∀ e : E, (σ e).IsSwap → (e : H) ∉ Subgroup.centralizer (W : Set H) ∧ orderOf (e : H) = 2 := by
  obtain ⟨ψ⟩ := hquot
  obtain ⟨P, ⟨eP⟩⟩ := hdihedral
  have hWK : W ≤ Subgroup.centralizer (W : Set H) := CyclicInversion.le_centralizer_of_isCyclic W
  have hKn : (Subgroup.centralizer (W : Set H)).Normal := Subgroup.normal_of_index_eq_two hindex
  obtain ⟨σH, hσsurj, hσker, hσK⟩ := exists_perm_hom W (by norm_num) autEquiv autEquiv_apply
    alternating_eq_one_of_forall_commute hodd hWK hindex ψ P eP
  have hZc : W.subgroupOf (Subgroup.centralizer (W : Set H)) ≤
      Subgroup.center (Subgroup.centralizer (W : Set H)) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp k.2 z hz).symm
  have hZodd : Odd (Nat.card (W.subgroupOf (Subgroup.centralizer (W : Set H)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv]
    exact hodd
  obtain ⟨hinfK, hsupK, -, hcomplK, -, ⟨φK⟩, hchar⟩ :=
    odd_central_alternating_five_extension_splits_over_derived_subgroup
      (K := Subgroup.centralizer (W : Set H)) (α := Fin 5) (by simp)
      (W.subgroupOf _) hZc hZodd ⟨ψ⟩
  have hJK : (commutator (Subgroup.centralizer (W : Set H))).map
      (Subgroup.centralizer (W : Set H)).subtype ≤ Subgroup.centralizer (W : Set H) :=
    Subgroup.map_subtype_le _
  have hJn : ((commutator (Subgroup.centralizer (W : Set H))).map
      (Subgroup.centralizer (W : Set H)).subtype).Normal := inferInstance
  set J := (commutator (Subgroup.centralizer (W : Set H))).map
    (Subgroup.centralizer (W : Set H)).subtype with hJ
  have hJW : W ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    rintro h ⟨hW, c, hc, rfl⟩
    have h1 : c ∈ W.subgroupOf (Subgroup.centralizer (W : Set H)) ⊓
        commutator (Subgroup.centralizer (W : Set H)) := ⟨hW, hc⟩
    rw [hinfK, Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hWJ : W ⊔ J = Subgroup.centralizer (W : Set H) := by
    have h := congrArg (Subgroup.map (Subgroup.centralizer (W : Set H)).subtype) hsupK
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    rwa [inf_of_le_left hWK] at h
  let φJ : J ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm.trans φK
  have hswap : Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1) = -1 ∧
      (Equiv.swap (0 : Fin 5) 1) ^ 2 = 1 := by
    decide
  obtain ⟨x, hx⟩ := hσsurj (Equiv.swap 0 1)
  have hxK : x ∉ Subgroup.centralizer (W : Set H) := fun h => by
    have h1 := (hσK x).mp h
    rw [hx, Equiv.Perm.mem_alternatingGroup, hswap.1] at h1
    exact absurd h1 (by decide)
  have hx2 : x ^ 2 = 1 := sq_eq_one_of_not_mem W hodd hinv hxK
    ((hσker _).mp (by rw [map_pow, hx, hswap.2]))
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 (fun h => hxK (h ▸ Subgroup.one_mem _))
  set E := J ⊔ Subgroup.zpowers x with hE
  have hEJ : ∀ e ∈ E, e ∈ J ∨ e * x ∈ J := mem_or_mul_mem_of_mem_sup J hx2
  have hxE : x ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hJE : J ≤ E := le_sup_left
  have hJsurj : ∀ a : Equiv.Perm (Fin 5), a ∈ alternatingGroup (Fin 5) → ∃ j ∈ J, σH j = a := by
    let f : J → alternatingGroup (Fin 5) := fun j => ⟨σH j, (hσK j).mp (hJK j.2)⟩
    have hfinj : Function.Injective f := by
      intro j j' h
      have h1 : σH j = σH j' := congrArg Subtype.val h
      have h2 : (j : H)⁻¹ * j' ∈ W := (hσker _).mp (by rw [map_mul, map_inv, h1, inv_mul_cancel])
      have h3 : (j : H)⁻¹ * j' ∈ J := Subgroup.mul_mem _ (Subgroup.inv_mem _ j.2) j'.2
      have h4 : (j : H)⁻¹ * j' ∈ W ⊓ J := ⟨h2, h3⟩
      rw [hJW, Subgroup.mem_bot, inv_mul_eq_one] at h4
      exact Subtype.ext h4
    have hfbij := hfinj.bijective_of_nat_card_le (le_of_eq (Nat.card_congr φJ.toEquiv).symm)
    intro a ha
    obtain ⟨j, hj⟩ := hfbij.2 ⟨a, ha⟩
    exact ⟨j, j.2, congrArg Subtype.val hj⟩
  have hxmem : ∀ e : H, e * x ∈ J → e ∈ Subgroup.centralizer (W : Set H) → False := by
    intro e hexJ heK
    apply hxK
    have h1 : x = e⁻¹ * (e * x) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ heK) (hJK hexJ)
  have hinjE : Function.Injective (σH.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have heW : (e : H) ∈ W := (hσker _).mp he
    rcases hEJ e e.2 with heJ | hexJ
    · have h4 : (e : H) ∈ W ⊓ J := ⟨heW, heJ⟩
      rw [hJW, Subgroup.mem_bot] at h4
      exact Subtype.ext h4
    · exact (hxmem e hexJ (hWK heW)).elim
  have hsurjE : Function.Surjective (σH.comp E.subtype) := by
    intro a
    by_cases ha : a ∈ alternatingGroup (Fin 5)
    · obtain ⟨j, hj, hja⟩ := hJsurj a ha
      exact ⟨⟨j, hJE hj⟩, hja⟩
    · have hsign : Equiv.Perm.sign a = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) ha
        · exact h
      have ha' : a * (σH x)⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign, hx, hswap.1]
        decide
      obtain ⟨j, hj, hja⟩ := hJsurj _ ha'
      refine ⟨⟨j * x, Subgroup.mul_mem _ (hJE hj) hxE⟩, ?_⟩
      change σH (j * x) = a
      rw [map_mul, hja, inv_mul_cancel_right]
  let σ : E ≃* Equiv.Perm (Fin 5) := MulEquiv.ofBijective _ ⟨hinjE, hsurjE⟩
  have hσ : ∀ e : E, σ e = σH e := fun e => rfl
  have hσJ : ∀ e : E, (e : H) ∈ J ↔ σ e ∈ alternatingGroup (Fin 5) := by
    intro e
    rw [hσ]
    constructor
    · intro he
      exact (hσK _).mp (hJK he)
    · intro he
      rcases hEJ e e.2 with heJ | hexJ
      · exact heJ
      · exact (hxmem e hexJ ((hσK _).mpr he)).elim
  have hsign : ∀ e : E, ∀ w ∈ W,
      (e : H) * w * (e : H)⁻¹ = w ^ ((Equiv.Perm.sign (σ e) : ℤˣ) : ℤ) := by
    intro e w hw
    by_cases heJ : (e : H) ∈ J
    · have hs : Equiv.Perm.sign (σ e) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp ((hσJ e).mp heJ)
      rw [hs, Units.val_one, zpow_one]
      have hc : w * e = e * w := Subgroup.mem_centralizer_iff.mp (hJK heJ) w hw
      rw [← hc, mul_inv_cancel_right]
    · have hs : Equiv.Perm.sign (σ e) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (σ e)) with h | h
        · exact absurd ((hσJ e).mpr (Equiv.Perm.mem_alternatingGroup.mpr h)) heJ
        · exact h
      rw [hs, Units.val_neg, Units.val_one, zpow_neg, zpow_one]
      have heK : (e : H) ∉ Subgroup.centralizer (W : Set H) := fun h =>
        heJ ((hσJ e).mpr ((hσ e).symm ▸ (hσK _).mp h))
      exact hinv e heK w hw
  have hWE : W ⊔ E = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨e, he⟩ := hsurjE (σH h)
    have he' : σH (e : H) = σH h := he
    have h1 : h * (e : H)⁻¹ ∈ W := (hσker _).mp (by rw [map_mul, map_inv, he', mul_inv_cancel])
    have h2 : h = (h * (e : H)⁻¹) * e := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right e.2)
  have hWE' : W ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heW, heE⟩
    have h1 : (σH.comp E.subtype) ⟨e, heE⟩ = 1 := (hσker e).mpr heW
    have h2 := hinjE (h1.trans (map_one _).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
  have hKcard : Nat.card (Subgroup.centralizer (W : Set H)) = 60 * Nat.card W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (W.subgroupOf (Subgroup.centralizer (W : Set H))),
      Nat.card_congr ψ.toEquiv, nat_card_alternating,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv]
  have hHcard : Nat.card H = 120 * Nat.card W := by
    rw [← (Subgroup.centralizer (W : Set H)).card_mul_index, hKcard, hindex]
    ring
  have hinJ : ∀ u : H, u ∈ Subgroup.centralizer (W : Set H) → orderOf u = 2 → u ∈ J := by
    intro u huK hu
    obtain ⟨⟨z, c⟩, hzc, -⟩ := Subgroup.IsComplement.existsUnique hcomplK ⟨u, huK⟩
    have hw : (((z : Subgroup.centralizer (W : Set H)) : H)) ∈ W := z.2
    have hj : (((c : Subgroup.centralizer (W : Set H)) : H)) ∈ J := ⟨c, c.2, rfl⟩
    have hu' : ((z : Subgroup.centralizer (W : Set H)) : H) *
        ((c : Subgroup.centralizer (W : Set H)) : H) = u := congrArg Subtype.val hzc
    have hcomm : Commute ((z : Subgroup.centralizer (W : Set H)) : H)
        ((c : Subgroup.centralizer (W : Set H)) : H) :=
      Subgroup.mem_centralizer_iff.mp (hJK hj) _ hw
    have hu2 : u ^ 2 = 1 := by
      rw [← hu]
      exact pow_orderOf_eq_one u
    rw [← hu', hcomm.mul_pow] at hu2
    have hw2 : ((z : Subgroup.centralizer (W : Set H)) : H) ^ 2 ∈ W ⊓ J := by
      refine ⟨Subgroup.pow_mem _ hw 2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hu2]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hj 2)
    rw [hJW, Subgroup.mem_bot] at hw2
    rw [← hu', CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd hw hw2, one_mul]
    exact hj
  have hinner := card_inner_involutions W σH hodd hWK hσsurj hσker hσK
  rw [nat_card_alternating_involutions] at hinner
  have hinnerJ : Nat.card {u : H // u ∈ J ∧ orderOf u = 2} = 15 := by
    rw [← hinner]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u =>
      ⟨fun h => ⟨hJK h.1, h.2⟩, fun h => ⟨hinJ u h.1 h.2, h.2⟩⟩)
  have houter := card_outer_involutions W σH hodd hWK hinv hσsurj hσker hσK
  rw [nat_card_odd_involutions, mul_comm] at houter
  have hclass := isConj_involutions_iff W σH hodd hWK hinv hindex hσsurj hσker hσK
    alternating_involution_conj odd_involution_conj
  have hKJ : ∀ u : H, orderOf u = 2 → (u ∈ Subgroup.centralizer (W : Set H) ↔ u ∈ J) :=
    fun u hu => ⟨fun h => hinJ u h hu, fun h => hJK h⟩
  have hcent := card_centralizer_mul W σH hodd hWK hinv hindex hσsurj hσker hσK
    alternating_involution_conj odd_involution_conj
  have hWpos : 0 < Nat.card W := Nat.card_pos
  refine ⟨J, x, E, σ, rfl, hWJ, hJW, fun w hw j hj => Subgroup.mem_centralizer_iff.mp (hJK hj) w hw,
    hJn, ⟨φJ⟩, hxK, hxord, rfl, hWE, hWE', hσJ, hsign, hKcard, hHcard, ?_, hinnerJ, houter, ?_,
    ?_, ?_, ?_⟩
  · intro u hu
    by_cases huK : u ∈ Subgroup.centralizer (W : Set H)
    · exact Or.inl (hinJ u huK hu)
    · exact Or.inr huK
  · intro u v hu hv
    rw [hclass u v hu hv, hKJ u hu, hKJ v hv]
  · intro u huJ hu
    have h1 := hcent u hu
    have h2 : Nat.card {v : H // (v ∈ Subgroup.centralizer (W : Set H) ↔
        u ∈ Subgroup.centralizer (W : Set H)) ∧ orderOf v = 2} = 15 := by
      rw [← hinner]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
        ⟨fun h => ⟨h.1.mpr (hJK huJ), h.2⟩, fun h => ⟨iff_of_true h.1 (hJK huJ), h.2⟩⟩)
    rw [h2, hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 15) (by rw [h1]; ring)
  · intro u huK hu
    have h1 := hcent u hu
    have h2 : Nat.card {v : H // (v ∈ Subgroup.centralizer (W : Set H) ↔
        u ∈ Subgroup.centralizer (W : Set H)) ∧ orderOf v = 2} = 10 * Nat.card W := by
      rw [← houter]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
        ⟨fun h => ⟨fun hv => huK (h.1.mp hv), h.2⟩, fun h => ⟨iff_of_false h.1 huK, h.2⟩⟩)
    rw [h2, hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 10 * Nat.card W) (by rw [h1]; ring)
  · intro e he
    obtain ⟨hs, hs2⟩ := (isSwap_iff (σ e)).mp he
    have heK : (e : H) ∉ Subgroup.centralizer (W : Set H) := fun h => by
      have h1 := (hσK _).mp h
      rw [← hσ, Equiv.Perm.mem_alternatingGroup, hs] at h1
      exact absurd h1 (by decide)
    refine ⟨heK, orderOf_eq_prime ?_ (fun h1 => heK (h1 ▸ Subgroup.one_mem _))⟩
    have h1 : e ^ 2 = 1 := σ.injective (by rw [map_pow, hs2, map_one])
    exact congrArg Subtype.val h1

end CFSG.Semidihedral.Principal
