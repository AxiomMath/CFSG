module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import Certificates.Certificate33001
public import Certificates.Certificate33002

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

namespace RLev

theorem ncard_conj_orbit_mul_card {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    {y : G | ∃ k ∈ K, y = k * g * k⁻¹}.ncard * Nat.card ↥(centralizer ({g} : Set G) ⊓ K) =
      Nat.card K := by
  have horb : MulAction.orbit (K.map (MulAut.conj (G := G))) g =
      {y | ∃ k ∈ K, y = k * g * k⁻¹} := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 ha
      exact ⟨k, hk, by simp [Subgroup.smul_def]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨MulAut.conj k, Subgroup.mem_map_of_mem _ hk⟩, by simp [Subgroup.smul_def]⟩
  have hidx : (centralizer ({g} : Set G)).relIndex K =
      (MulAction.stabilizer (K.map (MulAut.conj (G := G))) g).index := by
    rw [← MulAction.stabilizer_comap_conj_eq_centralizer_singleton, Subgroup.relIndex_comap,
      Subgroup.relIndex, MulAction.stabilizer_subgroupOf]
  rw [← horb, ← MulAction.index_stabilizer, ← hidx]
  exact Subgroup.relIndex_mul_card _ _

theorem ncard_conj_orbit_R (x : R) :
    {y : Equiv.Perm (Fin 42) | ∃ k ∈ R, y = k * (x : Equiv.Perm (Fin 42)) * k⁻¹}.ncard =
      Nat.card (ConjClasses.mk x).carrier := by
  have h : {y : Equiv.Perm (Fin 42) | ∃ k ∈ R, y = k * (x : Equiv.Perm (Fin 42)) * k⁻¹} =
      Subtype.val '' (ConjClasses.mk x).carrier := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k * x * k⁻¹, R.mul_mem (R.mul_mem hk x.2) (R.inv_mem hk)⟩,
        ⟨⟨k⁻¹, R.inv_mem hk⟩, Subtype.ext ?_⟩, rfl⟩
      simp [mul_assoc]
    · rintro ⟨z, ⟨c, hc⟩, rfl⟩
      refine ⟨(c : Equiv.Perm (Fin 42))⁻¹, R.inv_mem c.2, ?_⟩
      have := congrArg (fun w : R => (w : Equiv.Perm (Fin 42))) hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      group
  rw [h, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]

theorem orbit_S_eq_orbit_R {x : R} {n : ℕ}
    (hS : Nat.card S = n * Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} :
      Set (Equiv.Perm (Fin 42))) ⊓ S))
    (hR : Nat.card (ConjClasses.mk x).carrier = n) :
    {y : Equiv.Perm (Fin 42) | ∃ k ∈ S, y = k * (x : Equiv.Perm (Fin 42)) * k⁻¹} =
      {y | ∃ k ∈ R, y = k * (x : Equiv.Perm (Fin 42)) * k⁻¹} := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · rintro y ⟨k, hk, rfl⟩
    exact ⟨k, S_le_R hk, rfl⟩
  · rw [ncard_conj_orbit_R, hR]
    have h1 := ncard_conj_orbit_mul_card S (x : Equiv.Perm (Fin 42))
    rw [hS] at h1
    have hpos : 0 < Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} :
      Set (Equiv.Perm (Fin 42))) ⊓ S) := Nat.card_pos
    have := Nat.eq_of_mul_eq_mul_right hpos h1
    omega

theorem orbit_S_eq_orbit_R₁ :
    {y : Equiv.Perm (Fin 42) | ∃ k ∈ S, y = k * r₁ * k⁻¹} =
      {y | ∃ k ∈ R, y = k * r₁ * k⁻¹} := by
  refine orbit_S_eq_orbit_R (x := r₁R) (n := 315) ?_ conjClass₁.2
  have h1 : Nat.card ↥(centralizer ({r₁} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 64 := card_C₁
  rw [card_S, show (r₁R : Equiv.Perm (Fin 42)) = r₁ from rfl, h1]

theorem orbit_S_eq_orbit_R₄ :
    {y : Equiv.Perm (Fin 42) | ∃ k ∈ S, y = k * r₄ * k⁻¹} =
      {y | ∃ k ∈ R, y = k * r₄ * k⁻¹} := by
  refine orbit_S_eq_orbit_R (x := r₄R) (n := 280) ?_ conjClass₄.2
  have h1 : Nat.card ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 := card_C₄
  rw [card_S, show (r₄R : Equiv.Perm (Fin 42)) = r₄ from rfl, h1]

theorem exists_conj_r₁ {x : Equiv.Perm (Fin 42)} (hx : x ∈ S)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : ∃ c ∈ S, x = c * r₁ * c⁻¹ := by
  let xR : R := ⟨x, S_le_R hx⟩
  have hord : orderOf xR = 2 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (by rw [pow_two]; exact hx2)
    · exact fun h => hx1 (congrArg Subtype.val h)
  rcases (orderOf_eq_two_iff xR).1 hord with h | h | h | h
  · obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
    have hmem : x ∈ {y : Equiv.Perm (Fin 42) | ∃ k ∈ R, y = k * r₁ * k⁻¹} := ⟨c, hc, he⟩
    rw [← orbit_S_eq_orbit_R₁] at hmem
    exact hmem
  · exact absurd hx (not_mem_S_of_isConj h not_mem_S_r₂)
  · exact absurd hx (not_mem_S_of_isConj h not_mem_S_r₃)
  · exact absurd hx (not_mem_S_of_isConj h not_mem_S_r₄)

theorem exists_conj_r₄ {σ : Equiv.Perm (Fin 42)} (h : isUni σ) :
    ∃ c ∈ S, σ = c * r₄ * c⁻¹ := by
  obtain ⟨c, hc, rfl⟩ := h
  have hmem : c * r₄ * c⁻¹ ∈ {y : Equiv.Perm (Fin 42) | ∃ k ∈ R, y = k * r₄ * k⁻¹} :=
    ⟨c, hc, rfl⟩
  rw [← orbit_S_eq_orbit_R₄] at hmem
  exact hmem

end RLev

theorem inner_invol_conj {s s' : Equiv.Perm (Fin 42)} (hs : s ∈ S)
    (hs' : s' ∈ S) (hs2 : s * s = 1) (hs'2 : s' * s' = 1) (h1 : s ≠ 1) (h1' : s' ≠ 1) :
    ∃ c ∈ S, c * s * c⁻¹ = s' := by
  obtain ⟨c, hc, hcs⟩ := RLev.exists_conj_r₁ hs hs2 h1
  obtain ⟨c', hc', hcs'⟩ := RLev.exists_conj_r₁ hs' hs'2 h1'
  refine ⟨c' * c⁻¹, S.mul_mem hc' (S.inv_mem hc), ?_⟩
  rw [hcs, hcs']
  group

theorem uni_conj {σ σ' : Equiv.Perm (Fin 42)} (h : isUni σ)
    (h' : isUni σ') : ∃ c ∈ S, c * σ * c⁻¹ = σ' := by
  obtain ⟨c, hc, hcσ⟩ := RLev.exists_conj_r₄ h
  obtain ⟨c', hc', hcσ'⟩ := RLev.exists_conj_r₄ h'
  refine ⟨c' * c⁻¹, S.mul_mem hc' (S.inv_mem hc), ?_⟩
  rw [hcσ, hcσ']
  group

theorem exists_uni_commuting_inner {s : Equiv.Perm (Fin 42)}
    (hs : s ∈ S) (hs2 : s * s = 1) (h1 : s ≠ 1) :
    ∃ σ : Equiv.Perm (Fin 42), isUni σ ∧ σ * s = s * σ := by
  have h2 : 2 ∣ Nat.card C₄ := by rw [card_C₄]; norm_num
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzz : (z : Equiv.Perm (Fin 42)) * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz, pow_two] at this
    exact congrArg Subtype.val this
  have hz1 : (z : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨c, hc, hcz⟩ := inner_invol_conj z.2.2 hs hzz hs2 hz1 h1
  refine ⟨c * r₄ * c⁻¹, ⟨c, S_le_R hc, rfl⟩, ?_⟩
  have hzr : (z : Equiv.Perm (Fin 42)) * r₄ = r₄ * z :=
    Subgroup.mem_centralizer_singleton_iff.1 z.2.1
  rw [← hcz]
  calc c * r₄ * c⁻¹ * (c * z * c⁻¹) = c * (r₄ * z) * c⁻¹ := by group
    _ = c * (z * r₄) * c⁻¹ := by rw [hzr]
    _ = c * z * c⁻¹ * (c * r₄ * c⁻¹) := by group

theorem exists_E16_T0 :
    ∃ E : Subgroup (Equiv.Perm (Fin 42)), E ≤ L34Facts.T0 ∧ IsElemTwo E ∧ Nat.card E = 16 := by
  have h := Certificates.certificate33001
  simp only [l34E16Check, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, and_assoc] at h
  obtain ⟨hT, hfound, hE, hsize, hel⟩ := h
  have hT0 : Enumerates L34Facts.T0 (enumBFS 42 (L34Facts.wordTabs L34Facts.wT₀) 64).tabs.toList :=
    L34Facts.enumerates_wordClosure hT
  let A : Set (Equiv.Perm (Fin 42)) := {a | ∃ j < e16Gens.size, TabRep e16Gens[j]! a}
  have hgens : ∀ j < e16Gens.size, ∃ a ∈ A, TabRep e16Gens[j]! a := by
    intro j hj
    obtain ⟨g, -, hrep⟩ := hT0.sound _ (mem_of_found (hfound j hj))
    exact ⟨g, ⟨j, hj, hrep⟩, hrep⟩
  have hAT : A ⊆ L34Facts.T0 := by
    rintro a ⟨j, hj, ha⟩
    obtain ⟨g, hg, hrep⟩ := hT0.sound _ (mem_of_found (hfound j hj))
    rwa [ha.perm_eq hrep]
  have hEnum : Enumerates (Subgroup.closure A) (enumBFS 42 e16Gens 16).tabs.toList :=
    enumerates_closure (fun a ha => ha) hgens hE
  refine ⟨Subgroup.closure A, (Subgroup.closure_le _).2 hAT, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨tx, htx, hrx⟩ := hEnum.complete x hx
    obtain ⟨ty, hty, hry⟩ := hEnum.complete y hy
    obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem htx
    obtain ⟨l, hl, rfl⟩ := exists_getElem!_of_mem hty
    exact ((hrx.comp hry).eq_iff (hry.comp hrx)).1 ((hel k hk).2 l hl)
  · intro x hx
    obtain ⟨tx, htx, hrx⟩ := hEnum.complete x hx
    obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem htx
    exact ((hrx.comp hrx).eq_iff TabRep.idTab).1 (hel k hk).1
  · rw [hEnum.card, Array.length_toList, hsize]

namespace RLev

@[expose] def centConjEquivR {x r : Equiv.Perm (Fin 42)} (hx : x ∈ R) :
    ↥(centralizer ({x * r * x⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ R) ≃*
      ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ R) where
  toFun y := ⟨x⁻¹ * y * x, by
    obtain ⟨hy, hyR⟩ := y.2
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      R.mul_mem (R.mul_mem (R.inv_mem hx) hyR) hx⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc x⁻¹ * y * x * r = x⁻¹ * (y * (x * r * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * r * x⁻¹) * y) * x := by rw [h]
      _ = r * (x⁻¹ * y * x) := by group⟩
  invFun y := ⟨x * y * x⁻¹, by
    obtain ⟨hy, hyR⟩ := y.2
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      R.mul_mem (R.mul_mem hx hyR) (R.inv_mem hx)⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc x * y * x⁻¹ * (x * r * x⁻¹) = x * (y * r) * x⁻¹ := by group
      _ = x * (r * y) * x⁻¹ := by rw [h]
      _ = x * r * x⁻¹ * (x * y * x⁻¹) := by group⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' y z := Subtype.ext (by simp [mul_assoc])

theorem solvable_cent_r₄ :
    Group.IsSolvable ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) :=
  Certificates.certificate33002.2

end RLev

theorem solvable_cent_uni
    {σ : Equiv.Perm (Fin 42)} (h : isUni σ) :
    Group.IsSolvable ↥(centralizer ({σ} : Set (Equiv.Perm (Fin 42))) ⊓ R) := by
  obtain ⟨c, hc, rfl⟩ := h
  have := RLev.solvable_cent_r₄
  let e := RLev.centConjEquivR (r := r₄) hc
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

namespace RLev

theorem e_eq_false_of_comm {a' c : WrE} (hA : IsA a') (hca : c * a' = a' * c) : c.e = false := by
  obtain ⟨hae, -, hcases⟩ := hA
  by_contra hce
  have hce' : c.e = true := by simpa using hce
  have h1 := congrArg WrE.a hca
  simp only [WrE.mul_def, hae, hce', Bool.false_eq_true, ↓reduceIte] at h1
  rcases hcases with ⟨ha1, hb1, -⟩ | ⟨hb1, ha1, -⟩
  · rw [ha1, mul_one] at h1
    have : a'.b * c.a = 1 * c.a := by rw [one_mul]; exact h1.symm
    exact hb1 (mul_right_cancel this)
  · rw [hb1, one_mul] at h1
    have : c.a * a'.a = c.a * 1 := by rw [mul_one]; exact h1
    exact ha1 (mul_left_cancel this)

theorem mul_a_of_e_false {c d : WrE} (hd : d.e = false) : (c * d).a = c.a * d.a := by
  simp [WrE.mul_def, hd]

theorem mul_b_of_e_false {c d : WrE} (hd : d.e = false) : (c * d).b = c.b * d.b := by
  simp [WrE.mul_def, hd]

theorem coord_comm {c y' : WrE} (hce : c.e = false) (hye : y'.e = false) (h : c * y' = y' * c) :
    c.a * y'.a = y'.a * c.a ∧ c.b * y'.b = y'.b * c.b := by
  have ha := congrArg WrE.a h
  have hb := congrArg WrE.b h
  rw [mul_a_of_e_false hye, mul_a_of_e_false hce] at ha
  rw [mul_b_of_e_false hye, mul_b_of_e_false hce] at hb
  exact ⟨ha, hb⟩

end RLev

theorem solvable_centralizer_pair
    {a' y' : WrE} (hA : IsA a') (hU : IsUU y') (ha : a' ∈ wrR) (hy : y' ∈ wrR)
    (hc : a' * y' = y' * a') :
    Group.IsSolvable ↥(centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE) ⊓ wrR) := by
  obtain ⟨hye, -, hya, hyb⟩ := hU
  set H : Subgroup WrE := centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE) ⊓ wrR
    with hH
  have hnoswap : ∀ c ∈ H, c.e = false := fun c hcH =>
    RLev.e_eq_false_of_comm hA (Subgroup.mem_centralizer_singleton_iff.1 hcH.1.1)
  have hdata : ∀ c ∈ H, c.a ∈ centralizer ({y'.a} : Set (Equiv.Perm (Fin 42))) ⊓ R ∧
      c.b ∈ centralizer ({y'.b} : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    intro c hcH
    obtain ⟨h1, h2⟩ := RLev.coord_comm (hnoswap c hcH) hye
      (Subgroup.mem_centralizer_singleton_iff.1 hcH.1.2)
    exact ⟨⟨Subgroup.mem_centralizer_singleton_iff.2 h1, hcH.2.1⟩,
      ⟨Subgroup.mem_centralizer_singleton_iff.2 h2, hcH.2.2⟩⟩
  haveI : Group.IsSolvable ↥(centralizer ({y'.a} : Set (Equiv.Perm (Fin 42))) ⊓ R) :=
    solvable_cent_uni hya
  haveI : Group.IsSolvable ↥(centralizer ({y'.b} : Set (Equiv.Perm (Fin 42))) ⊓ R) :=
    solvable_cent_uni hyb
  let fa : H →* ↥(centralizer ({y'.a} : Set (Equiv.Perm (Fin 42))) ⊓ R) :=
    { toFun := fun c => ⟨c.1.a, (hdata c.1 c.2).1⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun c d => Subtype.ext (RLev.mul_a_of_e_false (hnoswap d.1 d.2)) }
  let fb : H →* ↥(centralizer ({y'.b} : Set (Equiv.Perm (Fin 42))) ⊓ R) :=
    { toFun := fun c => ⟨c.1.b, (hdata c.1 c.2).2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun c d => Subtype.ext (RLev.mul_b_of_e_false (hnoswap d.1 d.2)) }
  have hinj : Function.Injective (fa.prod fb) := by
    intro c d hcd
    have h1 := congrArg (fun p => (p.1 : Equiv.Perm (Fin 42))) hcd
    have h2 := congrArg (fun p => (p.2 : Equiv.Perm (Fin 42))) hcd
    refine Subtype.ext (WrE.ext h1 h2 ?_)
    rw [hnoswap c.1 c.2, hnoswap d.1 d.2]
  exact Group.isSolvable_of_isSolvable_injective hinj

end CFSG.ComponentClassification.GrSLit.L34Tw
