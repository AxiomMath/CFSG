module

public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBackSpin
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups Pointwise

namespace F3L221

theorem gwIsQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    GorensteinWalter.IsQuasisimple Q :=
  ⟨LocalCores.isQuasisimple_nontrivial hQ, (Group.isPerfect_def).1 hQ.1, hQ.2.1⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem isSolvable_of_isSolvableTwoComponentIn {K A : Subgroup Y}
    (hK : IsSolvableTwoComponentIn K A) : Group.IsSolvable ↥K := by
  have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have : Group.IsSolvable ↥(pPrimeCore 2 ↥K) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_pPrimeCore_two ↥K)
  have : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) := by
    have : Group.IsSolvable SL(2, ZMod 3) :=
      LieType.HighestRoot.isSolvable_of_mulEquiv h3 (MulEquiv.refl _)
    rcases hK.2.2.2 with h1 | h1
    · obtain ⟨e⟩ := h1
      have : Group.IsSolvable (PSL(2, ZMod 3)) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · obtain ⟨e⟩ := h1
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.isSolvable_of_ker_le_range (pPrimeCore 2 ↥K).subtype
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (by rw [QuotientGroup.ker_mk', range_subtype])

theorem commute_of_isQuasisimple {C D K : Subgroup Y} (hDC : D ≤ C)
    (hDs : (D.subgroupOf C).IsSubnormal) (hDq : IsQuasisimple ↥D) (hKC : K ≤ C)
    (hKs : (K.subgroupOf C).IsSubnormal) (hKsol : Group.IsSolvable ↥K) :
    ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := by
  have hEq : IsQuasisimple ↥(D.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDC).symm hDq
  have hE : GorensteinWalter.IsComponentOf (D.subgroupOf C) (⊤ : Subgroup ↥C) :=
    ⟨le_top, hDs.subgroupOf, gwIsQuasisimple hEq⟩
  rcases GorensteinWalter.component_le_or_commutator_eq_bot hE hKs with hle | hbot
  · exfalso
    have hDK : D ≤ K := fun d hd =>
      hle (show (⟨d, hDC hd⟩ : ↥C) ∈ D.subgroupOf C from hd)
    have : Group.IsSolvable ↥D :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hDK) (inclusion_injective hDK)
    have : Nontrivial ↥D := LocalCores.isQuasisimple_nontrivial hDq
    have : Group.IsPerfect ↥D := hDq.1
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥D
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  · intro k hk d hd
    have h1 := commutator_mem_commutator (show (⟨d, hDC hd⟩ : ↥C) ∈ D.subgroupOf C from hd)
      (show (⟨k, hKC hk⟩ : ↥C) ∈ K.subgroupOf C from hk)
    rw [hbot, mem_bot] at h1
    have h2 : d * k * d⁻¹ * k⁻¹ = 1 := by
      have := congrArg Subtype.val h1
      simpa [commutatorElement_def] using this
    calc k * d = (d * k * d⁻¹ * k⁻¹)⁻¹ * (d * k) := by group
      _ = d * k := by rw [h2, inv_one, one_mul]

theorem commute_of_centralizes {L K : Subgroup Y} (hLs : L.IsSubnormal)
    (hLq : IsQuasisimple ↥L) {z : Y} (hzL : ∀ l ∈ L, z * l = l * z)
    (hK : IsSolvableTwoComponentIn K (centralizer {z})) : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k := by
  have hLC : L ≤ centralizer ({z} : Set Y) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (hzL l hl).symm
  exact commute_of_isQuasisimple hLC hLs.subgroupOf hLq hK.1 hK.2.1
    (isSolvable_of_isSolvableTwoComponentIn hK)

omit [Finite Y] in
theorem mem_normalizer_iff_map_conj_eq {L : Subgroup Y} {g : Y} :
    g ∈ normalizer (L : Set Y) ↔ L.map (MulAut.conj g).toMonoidHom = L := by
  constructor
  · intro hg
    ext x
    rw [mem_map_equiv, MulAut.conj_symm_apply]
    have h1 := (mem_normalizer_iff.mp (inv_mem hg) x)
    rw [inv_inv] at h1
    exact h1.symm
  · intro h
    rw [mem_normalizer_iff]
    intro x
    have h1 : x ∈ L ↔ g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by
      rw [mem_map_equiv, MulAut.conj_symm_apply]
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    rw [h] at h1
    exact h1

omit [Finite Y] in
theorem exists_sq_eq_of_odd {K : Subgroup Y} {x : Y} (hx : x ∈ K) (hodd : Odd (orderOf x)) :
    ∃ y ∈ K, y * y = x := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨x ^ (m + 1), pow_mem hx _, ?_⟩
  rw [← pow_add, show m + 1 + (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem le_of_forall_odd {K A : Subgroup Y} (hK : IsSolvableTwoComponentIn K A) {N : Subgroup Y}
    (hN : ∀ x ∈ K, Odd (orderOf x) → x ∈ N) : K ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  set R := pPrimeCore 2 ↥K with hR
  set π := QuotientGroup.mk' R with hπ
  set N' := N.subgroupOf K with hN'
  have hodd := odd_card_pPrimeCore_two ↥K
  obtain ⟨φ, hφ⟩ : ∃ φ : SL(2, ZMod 3) →* ↥K ⧸ R, Function.Surjective φ := by
    rcases hK.2.2.2 with h | h
    · obtain ⟨e⟩ := h
      exact ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _),
        e.symm.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    · obtain ⟨e⟩ := h
      exact ⟨e.symm.toMonoidHom, e.symm.surjective⟩
  have hcube : ∀ y : ↥K, y ^ 3 ∈ R → (y : Y) ∈ N := by
    intro y hy
    refine hN y y.2 ?_
    have h1 : y ^ (3 * Nat.card R) = 1 := by
      rw [pow_mul]
      have h2 := pow_card_eq_one' (G := ↥R) (x := ⟨y ^ 3, hy⟩)
      have h3' := congrArg Subtype.val h2
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h3'
    have h4 : orderOf y ∣ 3 * Nat.card R := orderOf_dvd_of_pow_eq_one h1
    have h5 : Odd (3 * Nat.card R) := Odd.mul (by decide) hodd
    rw [← Subgroup.orderOf_coe] at h4
    exact h5.of_dvd_nat h4
  have hcl : closure {x : ↥K ⧸ R | x ^ 3 = 1} = ⊤ := by
    have h1 := LieType.HighestRoot.closure_orderOf_three_eq_top_of_mulEquiv h3
      (MulEquiv.refl (SL(2, ZMod 3)))
    have h2 := congrArg (Subgroup.map φ) h1
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective φ hφ] at h2
    rw [eq_top_iff, ← h2]
    refine closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 := by
      have h : orderOf y = 3 := hy
      have h' := pow_orderOf_eq_one y
      rwa [h] at h'
    show φ y ^ 3 = 1
    rw [← map_pow, hy3, map_one]
  have hmap : N'.map π = ⊤ := by
    refine top_unique ?_
    rw [← hcl, closure_le]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R x
    have hy : y ^ 3 ∈ R := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hx
    exact ⟨y, hcube y hy, rfl⟩
  have hker : π.ker ≤ N' := by
    intro y hy
    rw [hπ, QuotientGroup.ker_mk'] at hy
    have h1 : y ^ 3 ∈ R := pow_mem hy 3
    exact hcube y h1
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥K) ∈ (N'.map π).comap π := by
    rw [mem_comap, hmap]
    exact mem_top _
  rw [comap_map_eq, sup_eq_left.mpr hker] at h1
  exact h1

theorem false_of_not_mem_normalizer {L K : Subgroup Y} (hLs : L.IsSubnormal)
    (hLq : IsQuasisimple ↥L) {z : Y} (hz : orderOf z = 2) (hzN : z ∉ normalizer (L : Set Y))
    (hK : IsSolvableTwoComponentIn K (centralizer {z})) (hzK : z ∈ K) : False := by
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hσσ : ∀ y : Y, z * (z * y * z⁻¹) * z⁻¹ = y := by
    intro y
    rw [show z * (z * y * z⁻¹) * z⁻¹ = (z * z) * y * (z * z)⁻¹ by group, hzz]
    group
  set cj : Y → Subgroup Y := fun g => L.map (MulAut.conj g).toMonoidHom with hcj
  have hcomp : ∀ g : Y, GorensteinWalter.IsComponentOf (cj g) (⊤ : Subgroup Y) := by
    intro g
    have hq : IsQuasisimple ↥(cj g) :=
      LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ (MulAut.conj g).injective)
        hLq
    exact ⟨le_top, (hLs.map (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective).subgroupOf, gwIsQuasisimple hq⟩
  have hcompL : GorensteinWalter.IsComponentOf L (⊤ : Subgroup Y) :=
    ⟨le_top, hLs.subgroupOf, gwIsQuasisimple hLq⟩
  have hcomm : ∀ {A B : Subgroup Y}, GorensteinWalter.IsComponentOf A ⊤ →
      GorensteinWalter.IsComponentOf B ⊤ → A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B hA hB hAB a ha b hb
    have h1 := commutator_mem_commutator ha hb
    rw [GorensteinWalter.component_commute_of_ne hA hB hAB, mem_bot,
      commutatorElement_def] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hcjmul : ∀ g h : Y, cj (g * h) = (cj h).map (MulAut.conj g).toMonoidHom := by
    intro g h
    simp only [hcj]
    rw [map_map]
    congr 1
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
      MulAut.conj_apply]
    group
  have hσσL : ∀ A : Subgroup Y,
      (A.map (MulAut.conj z).toMonoidHom).map (MulAut.conj z).toMonoidHom = A := by
    intro A
    rw [map_map]
    convert Subgroup.map_id A
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    exact hσσ x
  set L' := cj z with hL'
  have hL'ne : L' ≠ L := fun h => hzN (mem_normalizer_iff_map_conj_eq.mpr h)
  have hLL' : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := hcomm hcompL (hcomp z) (Ne.symm hL'ne)
  have hconjL : ∀ {x : Y}, x ∈ L → z * x * z⁻¹ ∈ L' := fun hx => ⟨_, hx, rfl⟩
  have hconjL' : ∀ {x : Y}, x ∈ L' → z * x * z⁻¹ ∈ L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : z * ((MulAut.conj z).toMonoidHom y) * z⁻¹ = y := hσσ y
    rw [h1]
    exact hy
  let φ : ↥L →* Y := MonoidHom.mk' (fun x => (x : Y) * (z * x * z⁻¹)) (by
    intro x y
    have hc : (y : Y) * (z * x * z⁻¹) = (z * x * z⁻¹) * y := hLL' y y.2 _ (hconjL x.2)
    simp only [Subgroup.coe_mul]
    calc (x : Y) * y * (z * (x * y) * z⁻¹) = x * (y * (z * x * z⁻¹)) * (z * y * z⁻¹) := by
          group
      _ = x * ((z * x * z⁻¹) * y) * (z * y * z⁻¹) := by rw [hc]
      _ = x * (z * x * z⁻¹) * (y * (z * y * z⁻¹)) := by group)
  have hφ : ∀ x : ↥L, φ x = (x : Y) * (z * x * z⁻¹) := fun x => rfl
  set D := φ.range with hD
  set C := centralizer ({z} : Set Y) with hC
  have hDC : D ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff, hφ]
    have hc := hLL' x x.2 _ (hconjL x.2)
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have h1 : z * (x : Y) = (z * x * z⁻¹) * z := by group
    have h2 : z * (z * x * z⁻¹) = (x : Y) * z := by
      calc z * (z * x * z⁻¹) = (z * z) * x * z⁻¹ := by group
        _ = (x : Y) * z := by rw [hzz, one_mul, hzi]
    calc (x : Y) * (z * x * z⁻¹) * z = (z * x * z⁻¹) * x * z := by rw [hc]
      _ = (z * x * z⁻¹) * (x * z) := by group
      _ = (z * x * z⁻¹) * (z * (z * x * z⁻¹)) := by rw [h2]
      _ = (z * x * z⁻¹) * z * (z * x * z⁻¹) := by group
      _ = z * x * (z * x * z⁻¹) := by rw [← h1]
      _ = z * ((x : Y) * (z * x * z⁻¹)) := by group
  have hker : φ.rangeRestrict.ker ≤ center ↥L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (x : Y) * (z * x * z⁻¹) = 1 := congrArg Subtype.val hx
    have hxL' : (x : Y) ∈ L' := by
      rw [eq_inv_of_mul_eq_one_left hx1]
      exact inv_mem (hconjL x.2)
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hLL' g g.2 x hxL')
  have hDq : IsQuasisimple ↥D :=
    LocalCores.isQuasisimple_of_surjective hLq φ.rangeRestrict φ.rangeRestrict_surjective hker
  set M := L ⊔ L' with hM
  have hL's : L'.IsSubnormal :=
    hLs.map (f := (MulAut.conj z).toMonoidHom) (MulAut.conj z).surjective
  have hMs : M.IsSubnormal := CFSG.GroupTheory.isSubnormal_sup hLs hL's
  have hL'N : L' ≤ normalizer (L : Set Y) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hc := hLL' h hh b hb
      rw [show b * h * b⁻¹ = h by rw [← hc]; group]
      exact hh
    · intro hh
      have hc : b * h * b⁻¹ * b = b * (b * h * b⁻¹) := hLL' _ hh b hb
      have h1 : h = b * h * b⁻¹ := by
        calc h = b⁻¹ * (b * h * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hc]
          _ = b * h * b⁻¹ := by group
      rw [h1]
      exact hh
  have hMC : ((M ⊓ C).subgroupOf C).IsSubnormal := by
    have h1 : (M ⊓ C).subgroupOf C = M.subgroupOf C := by
      ext x
      simp only [mem_subgroupOf, mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    rw [h1]
    exact hMs.subgroupOf
  have hDMC : D ≤ M ⊓ C := by
    rintro _ ⟨x, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mem_sup_left x.2) (mem_sup_right (hconjL x.2)), hDC ⟨x, rfl⟩⟩
  have hconjD : ∀ y ∈ M ⊓ C, ∀ x : ↥L, y * φ x * y⁻¹ ∈ D := by
    intro y hy x
    obtain ⟨hyM, hyC⟩ := mem_inf.mp hy
    have hy' : y ∈ (L : Set Y) * (L' : Set Y) := by
      rw [← coe_mul_of_right_le_normalizer_left L L' hL'N]
      exact hyM
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    have hab' : a * b = y := hab
    subst hab'
    have hb'L : z * b * z⁻¹ ∈ L := hconjL' hb
    have ha'L' : z * a * z⁻¹ ∈ L' := hconjL ha
    have hyz : z * (a * b) * z⁻¹ = a * b := by
      rw [mem_centralizer_singleton_iff] at hyC
      calc z * (a * b) * z⁻¹ = ((a * b) * z) * z⁻¹ := by rw [← hyC]
        _ = a * b := by group
    have hcomm1 : (z * b * z⁻¹) * (z * a * z⁻¹) = (z * a * z⁻¹) * (z * b * z⁻¹) :=
      hLL' _ hb'L _ ha'L'
    have h1 : a * b = (z * b * z⁻¹) * (z * a * z⁻¹) := by
      rw [hcomm1]
      calc a * b = z * (a * b) * z⁻¹ := hyz.symm
        _ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
    have hζeq : (z * b * z⁻¹)⁻¹ * a = (z * a * z⁻¹) * b⁻¹ := by
      calc (z * b * z⁻¹)⁻¹ * a = (z * b * z⁻¹)⁻¹ * (a * b) * b⁻¹ := by group
        _ = (z * b * z⁻¹)⁻¹ * ((z * b * z⁻¹) * (z * a * z⁻¹)) * b⁻¹ := by rw [h1]
        _ = (z * a * z⁻¹) * b⁻¹ := by group
    have hζL' : (z * b * z⁻¹)⁻¹ * a ∈ L' := by
      rw [hζeq]
      exact mul_mem ha'L' (inv_mem hb)
    set ζ := (z * b * z⁻¹)⁻¹ * a with hζ
    have hxζ : (x : Y) * ζ = ζ * x := hLL' x x.2 ζ hζL'
    have hbx : (x : Y) * b = b * x := hLL' x x.2 b hb
    set u := a * (x : Y) * a⁻¹ with hu
    have huL : u ∈ L := mul_mem (mul_mem ha x.2) (inv_mem ha)
    have hb' : z * b * z⁻¹ = a * ζ⁻¹ := by rw [hζ]; group
    have hbxz : b * (z * x * z⁻¹) * b⁻¹ = z * u * z⁻¹ := by
      calc b * (z * x * z⁻¹) * b⁻¹
          = (z * (z * b * z⁻¹) * z⁻¹) * (z * x * z⁻¹) * (z * (z * b * z⁻¹) * z⁻¹)⁻¹ := by
            rw [hσσ b]
        _ = z * ((z * b * z⁻¹) * x * (z * b * z⁻¹)⁻¹) * z⁻¹ := by group
        _ = z * ((a * ζ⁻¹) * x * (a * ζ⁻¹)⁻¹) * z⁻¹ := by rw [hb']
        _ = z * (a * (ζ⁻¹ * ((x : Y) * ζ)) * a⁻¹) * z⁻¹ := by group
        _ = z * (a * (ζ⁻¹ * (ζ * x)) * a⁻¹) * z⁻¹ := by rw [hxζ]
        _ = z * u * z⁻¹ := by rw [hu]; group
    have haw : a * (z * u * z⁻¹) = (z * u * z⁻¹) * a := hLL' a ha _ (hconjL huL)
    have hfinal : (a * b) * φ x * (a * b)⁻¹ = φ ⟨u, huL⟩ := by
      rw [hφ, hφ]
      calc (a * b) * ((x : Y) * (z * x * z⁻¹)) * (a * b)⁻¹
          = a * (b * x) * (z * x * z⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = a * (x * b) * (z * x * z⁻¹) * b⁻¹ * a⁻¹ := by rw [← hbx]
        _ = a * x * (b * (z * x * z⁻¹) * b⁻¹) * a⁻¹ := by group
        _ = a * x * (z * u * z⁻¹) * a⁻¹ := by rw [hbxz]
        _ = (a * x * a⁻¹) * ((a * (z * u * z⁻¹)) * a⁻¹) := by group
        _ = (a * x * a⁻¹) * (((z * u * z⁻¹) * a) * a⁻¹) := by rw [haw]
        _ = u * (z * u * z⁻¹) := by rw [hu]; group
    rw [hfinal]
    exact ⟨⟨u, huL⟩, rfl⟩
  have hDn : (D.subgroupOf (M ⊓ C)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hn
    simp only [coe_mul, coe_inv]
    rw [← hx]
    exact hconjD g g.2 x
  have hDs : (D.subgroupOf C).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hDMC inf_le_right hDn.isSubnormal hMC
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k :=
    commute_of_isQuasisimple hDC hDs hDq hK.1 hK.2.1 (isSolvable_of_isSolvableTwoComponentIn hK)
  have hperm : ∀ k ∈ K, cj k = L ∨ cj k = L' := by
    intro k hk
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2⟩ := hne
    have hkz : k * z = z * k := mem_centralizer_singleton_iff.mp (hK.1 hk)
    set L₂ := cj (z * k) with hL₂
    have hL₂eq : L₂ = (cj k).map (MulAut.conj z).toMonoidHom := hcjmul z k
    have hL'k : L'.map (MulAut.conj k).toMonoidHom = L₂ := by
      rw [hL', ← hcjmul, hkz]
    have h3 : L₂ ≠ L := by
      intro h
      apply h2
      rw [← hσσL (cj k), ← hL₂eq, h]
    have h4 : L₂ ≠ L' := by
      intro h
      apply h1
      rw [← hσσL (cj k), ← hL₂eq, h, hL', hσσL]
    have hDk : ∀ d ∈ D, d ∈ cj k ⊔ L₂ := by
      intro d hd
      have hdk : k * d * k⁻¹ = d := by rw [hKD k hk d hd, mul_inv_cancel_right]
      have hdM : d ∈ M := (hDMC hd).1
      have h5 : k * d * k⁻¹ ∈ M.map (MulAut.conj k).toMonoidHom := ⟨d, hdM, rfl⟩
      rw [hM, Subgroup.map_sup, hL'k, hdk] at h5
      exact h5
    have hcen : ∀ e ∈ cj k ⊔ L₂, ∀ m ∈ M, e * m = m * e := by
      intro e he m hm
      have hcL : cj k ⊔ L₂ ≤ centralizer (L : Set Y) := by
        refine sup_le (fun x hx => mem_centralizer_iff.mpr fun l hl => ?_)
          (fun x hx => mem_centralizer_iff.mpr fun l hl => ?_)
        · exact (hcomm (hcomp k) hcompL h1 x hx l hl).symm
        · exact (hcomm (hcomp (z * k)) hcompL h3 x hx l hl).symm
      have hcL' : cj k ⊔ L₂ ≤ centralizer (L' : Set Y) := by
        refine sup_le (fun x hx => mem_centralizer_iff.mpr fun l hl => ?_)
          (fun x hx => mem_centralizer_iff.mpr fun l hl => ?_)
        · exact (hcomm (hcomp k) (hcomp z) h2 x hx l hl).symm
        · exact (hcomm (hcomp (z * k)) (hcomp z) h4 x hx l hl).symm
      have hMe : M ≤ centralizer ({e} : Set Y) := sup_le
        (fun l hl => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hcL he) l hl))
        (fun l hl => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hcL' he) l hl))
      exact (mem_centralizer_singleton_iff.mp (hMe hm)).symm
    have hcommD : ∀ a b : ↥D, a * b = b * a := by
      intro a b
      exact Subtype.ext (hcen a (hDk a a.2) b (hDMC b.2).1)
    have : Group.IsPerfect ↥D := hDq.1
    have : Nontrivial ↥D := LocalCores.isQuasisimple_nontrivial hDq
    have hbot : commutator ↥D = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun a _ => mem_centralizer_iff.mpr fun b _ => hcommD b a
    rw [Group.IsPerfect.commutator_eq_top] at hbot
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥D
    have ha : a ∈ (⊥ : Subgroup ↥D) := hbot ▸ mem_top a
    have hb : b ∈ (⊥ : Subgroup ↥D) := hbot ▸ mem_top b
    rw [mem_bot] at ha hb
    exact hab (ha.trans hb.symm)
  have hsq : ∀ y ∈ K, y * y ∈ normalizer (L : Set Y) := by
    intro y hy
    rcases hperm y hy with h | h
    · have hyN := mem_normalizer_iff_map_conj_eq.mpr h
      exact mul_mem hyN hyN
    · have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp (hK.1 hy)
      rw [mem_normalizer_iff_map_conj_eq]
      change cj (y * y) = L
      rw [hcjmul, h, hL', ← hcjmul, hyz, hcjmul, h, hL', hσσL]
  have hKN : K ≤ normalizer (L : Set Y) := le_of_forall_odd hK fun x hx hodd => by
    obtain ⟨y, hy, rfl⟩ := exists_sq_eq_of_odd hx hodd
    exact hsq y hy
  exact hzN (hKN hzK)

end F3L221

end CFSG.ComponentClassification.HarrisLit.T1
