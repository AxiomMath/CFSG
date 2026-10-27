module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.HardMathSupport.Lang.E6Descent.RankE6
public import CFSG.LocalAnalysis.EvenBN.Common.SL2FourCenter
public import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc.E6Three

section E6Torus


private def cubeOnePi (F : Type) [Field F] : Subgroup (Fin Tag.E6.rank → Fˣ) :=
  (CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix (G := Fˣ)
    (Matrix.diagonal fun _ : Fin Tag.E6.rank => ((3 : ℕ) : ℤ))).ker

private theorem mem_cubeOnePi {F : Type} [Field F] {t : Fin Tag.E6.rank → Fˣ} :
    t ∈ cubeOnePi F ↔ ∀ i, t i ^ 3 = 1 := by
  constructor
  · intro h i
    rw [cubeOnePi, MonoidHom.mem_ker] at h
    rw [← CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_diagonal_apply (fun _ => 3) t i, h]
    rfl
  · intro h
    rw [cubeOnePi, MonoidHom.mem_ker]
    funext i
    rw [CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_diagonal_apply (fun _ => 3) t i, h i]
    rfl

private theorem card_cubeOnePi {F : Type} [Field F] [Finite F]
    (h3 : 3 ∣ Nat.card F - 1) : Nat.card (cubeOnePi F) = 3 ^ 6 := by
  rw [cubeOnePi, CFSG.Timmesfeld.ExceptionalOrders.card_ker_zpowMatrix_diagonal (G := Fˣ)
    (fun _ : Fin Tag.E6.rank => 3)]
  simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units]
  rw [Nat.gcd_eq_right h3]
  simp
  decide

private noncomputable def torusCoordModGL (F : Type) [Field F] :
    (Fin Tag.E6.rank → Fˣ) →* ModGL Tag.E6 F :=
  (torusGroup Tag.E6 F).subtype.comp (torusCoordHom Tag.E6 F)

private theorem torusCoordModGL_ker {F : Type} [Field F] :
    (torusCoordModGL F).ker =
      (CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix (G := Fˣ) Tag.E6.cartan).ker := by
  ext t
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact (Subtype.coe_injective.eq_iff).trans
    (CFSG.Timmesfeld.ExceptionalOrders.torusCoordHom_eq_one_iff t)

private theorem torusCoordModGL_apply {F : Type} [Field F] (t : Fin Tag.E6.rank → Fˣ) :
    (torusCoordModGL F t : ModGL Tag.E6 F) =
      (List.ofFn fun i => torusElt Tag.E6 F i (t i)).prod := rfl

private theorem torusCoordModGL_mulSingle {F : Type} [Field F] (i : Fin Tag.E6.rank)
    (s : Fˣ) : (torusCoordModGL F (Pi.mulSingle i s) : ModGL Tag.E6 F) = torusElt Tag.E6 F i s :=
  coe_torusCoordHom_mulSingle i s

private noncomputable def cubeOneMap (F : Type) [Field F] :
    ↥(cubeOnePi F) →* ModGL Tag.E6 F :=
  (torusCoordModGL F).comp (cubeOnePi F).subtype

private theorem card_ker_torusCoordModGL_le_three {F : Type} [Field F] [Finite F] :
    Nat.card (torusCoordModGL F).ker ≤ 3 := by
  rw [torusCoordModGL_ker]
  exact CFSG.HardMathSupport.Lang.E6Descent.card_ker_zpowMatrix_cartan_E6_le

private theorem card_ker_cubeOneMap_le_three {F : Type} [Field F] [Finite F] :
    Nat.card (cubeOneMap F).ker ≤ 3 := by
  haveI : Finite ↥(torusCoordModGL F).ker :=
    Finite.of_injective (fun x : ↥(torusCoordModGL F).ker => (x.1 : Fin Tag.E6.rank → Fˣ))
      Subtype.val_injective
  have hinj : Function.Injective (fun x : ↥(cubeOneMap F).ker =>
      (⟨(x.1 : Fin Tag.E6.rank → Fˣ), by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        simpa [cubeOneMap] using hx⟩ : ↥(torusCoordModGL F).ker)) := by
    intro x y hxy
    apply Subtype.ext
    simpa using congrArg (fun z : ↥(torusCoordModGL F).ker =>
      (z : Fin Tag.E6.rank → Fˣ)) hxy
  exact (Nat.card_le_card_of_injective _ hinj).trans card_ker_torusCoordModGL_le_three

private def cartanKexp : Fin Tag.E6.rank → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 1
  | _ => 2

private def cartanKernelTuple {F : Type} [Field F] (ζ : Fˣ) : Fin Tag.E6.rank → Fˣ :=
  fun i => ζ ^ cartanKexp i

private theorem cartanKexp_dvd :
    ∀ j : Fin Tag.E6.rank,
      (3 : ℤ) ∣ ∑ i : Fin Tag.E6.rank, ((cartanKexp i : ℕ) : ℤ) * Tag.E6.cartan i j := by
  decide +kernel

private theorem cartanKernelTuple_mem_ker {F : Type} [Field F] {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    cartanKernelTuple ζ ∈
      (CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix (G := Fˣ) Tag.E6.cartan).ker := by
  rw [MonoidHom.mem_ker]
  funext j
  rw [CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_apply, Pi.one_apply]
  have h1 : ∏ i : Fin Tag.E6.rank, cartanKernelTuple ζ i ^ Tag.E6.cartan i j =
      ζ ^ (∑ i : Fin Tag.E6.rank, ((cartanKexp i : ℕ) : ℤ) * Tag.E6.cartan i j) := by
    rw [← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [cartanKernelTuple, ← zpow_natCast, ← zpow_mul]
  rw [h1, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  exact cartanKexp_dvd j

private theorem cartanKernelTuple_pow_three {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) : cartanKernelTuple ζ ^ 3 = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, cartanKernelTuple, ← pow_mul,
    show cartanKexp i * 3 = 3 * cartanKexp i by ring, pow_mul,
    show ζ ^ 3 = 1 by rw [← hζ]; exact pow_orderOf_eq_one ζ, one_pow]

private theorem cartanKernelTuple_ne_one {F : Type} [Field F] {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    cartanKernelTuple ζ ≠ 1 := by
  intro h
  have h1 : cartanKernelTuple ζ ⟨0, by decide⟩ = (1 : Fin Tag.E6.rank → Fˣ) ⟨0, by decide⟩ := by
    rw [h]
  rw [cartanKernelTuple, Pi.one_apply, cartanKexp] at h1
  have h2 : orderOf ζ = 1 := orderOf_eq_one_iff.2 (by simpa using h1)
  rw [hζ] at h2
  exact absurd h2 (by norm_num)

private theorem three_le_card_ker_cubeOneMap {F : Type} [Field F] [Finite F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) : 3 ≤ Nat.card (cubeOneMap F).ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : ↥(cubeOnePi F) := ⟨cartanKernelTuple ζ, mem_cubeOnePi.2 fun i => by
    simpa using congrFun (cartanKernelTuple_pow_three hζ) i⟩
  have hx : x ∈ (cubeOneMap F).ker := by
    have h := cartanKernelTuple_mem_ker hζ
    rw [← torusCoordModGL_ker, MonoidHom.mem_ker] at h
    exact h
  haveI : Finite ↥(cubeOneMap F).ker :=
    Finite.of_injective (fun y : ↥(cubeOneMap F).ker => (y.1 : ↥(cubeOnePi F)))
      Subtype.val_injective
  have hcard := Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hx)
  have hx3 : x ^ 3 = 1 := Subtype.ext (cartanKernelTuple_pow_three hζ)
  have hx1 : x ≠ 1 := fun h => cartanKernelTuple_ne_one hζ (congrArg Subtype.val h)
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  rwa [Nat.card_zpowers, hord] at hcard

private theorem card_ker_cubeOneMap {F : Type} [Field F] [Finite F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) : Nat.card (cubeOneMap F).ker = 3 :=
  le_antisymm card_ker_cubeOneMap_le_three (three_le_card_ker_cubeOneMap hζ)

private theorem card_range_cubeOneMap {F : Type} [Field F] [Finite F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) : Nat.card (cubeOneMap F).range = 3 ^ 5 := by
  have h3 : 3 ∣ Nat.card F - 1 := by
    have h := orderOf_dvd_natCard ζ
    rwa [hζ, Nat.card_units] at h
  have hcard : Nat.card ↥(cubeOnePi F) =
      Nat.card (cubeOneMap F).range * Nat.card (cubeOneMap F).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (cubeOneMap F).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (cubeOneMap F)).toEquiv]
  have h : 3 ^ 6 = Nat.card (cubeOneMap F).range * 3 := by
    rw [← card_cubeOnePi h3, hcard, card_ker_cubeOneMap hζ]
  rw [show (3 : ℕ) ^ 5 = 243 by norm_num]
  rw [show (3 : ℕ) ^ 6 = 729 by norm_num] at h
  omega

private theorem map_cubeOnePi_le_torusThree {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) : Subgroup.map (torusCoordModGL F) (cubeOnePi F) ≤ e6TorusThree F ζ := by
  rintro _ ⟨t, ht, rfl⟩
  rw [torusCoordModGL_apply]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  have ht' : ∀ i, t i ^ 3 = 1 := mem_cubeOnePi.1 ht
  obtain ⟨m, hm⟩ := CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζ (ht' i)
  rw [← hm,
    show torusElt Tag.E6 F i (ζ ^ m.val) = (torusEltHom Tag.E6 F i ζ) ^ m.val from
      map_pow (torusEltHom Tag.E6 F i) ζ m.val]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) m.val

private theorem torusThree_le_map_cubeOnePi {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) : e6TorusThree F ζ ≤ Subgroup.map (torusCoordModGL F) (cubeOnePi F) := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.mulSingle i ζ, mem_cubeOnePi.2 ?_, torusCoordModGL_mulSingle i ζ⟩
  intro j
  by_cases hji : j = i
  · rw [hji, Pi.mulSingle_eq_same, hζ3]
  · rw [Pi.mulSingle_eq_of_ne hji]
    exact one_pow 3

theorem card_e6TorusThree {F : Type} [Field F] [Finite F] {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    Nat.card (e6TorusThree F ζ) = 3 ^ 5 := by
  have hEq : (cubeOneMap F).range = e6TorusThree F ζ := by
    have hfr : (cubeOneMap F).range =
        Subgroup.map (torusCoordModGL F) (cubeOnePi F) := by
      rw [MonoidHom.range_eq_map, cubeOneMap, ← Subgroup.map_map, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [hfr]
    exact le_antisymm (map_cubeOnePi_le_torusThree hζ) (torusThree_le_map_cubeOnePi hζ)
  rw [← hEq]
  exact card_range_cubeOneMap hζ

end E6Torus

section RootLift


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {F : Type}
  [Field F] [Finite F] [CharP F 2]

private noncomputable def simpleRootSub (i : Fin Tag.E6.rank) :
    SL2 F →* ↥(adjointGroup Tag.E6 F) :=
  (simpleRootSL2 Tag.E6 F i).codRestrict (adjointGroup Tag.E6 F)
    (fun g => simpleRootSL2_mem_adjointGroup i g)

private noncomputable def simpleRootImage (i : Fin Tag.E6.rank) :
    Subgroup ↥(adjointGroup Tag.E6 F) :=
  (simpleRootSub (F := F) i).range

private theorem simpleRootSub_injective (i : Fin Tag.E6.rank) :
    Function.Injective (simpleRootSub (F := F) i) :=
  fun _ _ hgh =>
    CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo i (congrArg Subtype.val hgh)

private noncomputable def simpleRootEquiv (i : Fin Tag.E6.rank) :
    SL2 F ≃* ↥(simpleRootImage (F := F) i) :=
  MonoidHom.ofInjective (simpleRootSub_injective (F := F) i)

private theorem simpleRootEquiv_coe (i : Fin Tag.E6.rank) (g : SL2 F) :
    ((simpleRootEquiv (F := F) i g : ↥(simpleRootImage (F := F) i)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g := rfl

variable (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))

private noncomputable def rootPreimage (i : Fin Tag.E6.rank) : Subgroup ↥S :=
  (simpleRootImage (F := F) i).comap M.π

private noncomputable def rootPreimageHom (i : Fin Tag.E6.rank) :
    ↥(rootPreimage M i) →* ↥(simpleRootImage (F := F) i) :=
  (M.π.comp (rootPreimage M i).subtype).codRestrict _ (fun x => x.2)

private theorem rootPreimageHom_surjective (i : Fin Tag.E6.rank) :
    Function.Surjective (rootPreimageHom M i) := by
  intro y
  obtain ⟨s, hs⟩ := M.surj (y : ↥(adjointGroup Tag.E6 F))
  exact ⟨⟨s, by
    show M.π s ∈ simpleRootImage (F := F) i
    rw [hs]
    exact y.2⟩, Subtype.ext hs⟩

private noncomputable def rootPreimageMap (i : Fin Tag.E6.rank) :
    ↥(rootPreimage M i) →* SL2 F :=
  (simpleRootEquiv (F := F) i).symm.toMonoidHom.comp (rootPreimageHom M i)

private theorem rootPreimageMap_surjective (i : Fin Tag.E6.rank) :
    Function.Surjective (rootPreimageMap M i) := by
  intro g
  obtain ⟨x, hx⟩ := rootPreimageHom_surjective M i (simpleRootEquiv (F := F) i g)
  exact ⟨x, by
    rw [rootPreimageMap, MonoidHom.comp_apply, hx]
    exact MulEquiv.symm_apply_apply (simpleRootEquiv (F := F) i) g⟩

private theorem rootPreimageMap_ker_le_center (i : Fin Tag.E6.rank) :
    (rootPreimageMap M i).ker ≤ Subgroup.center ↥(rootPreimage M i) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx1 : (x.1 : ↥S) ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker]
    have h2 : rootPreimageHom M i x = 1 := by
      have h3 := congrArg (simpleRootEquiv (F := F) i) hx
      simpa [rootPreimageMap] using h3
    exact congrArg Subtype.val h2
  exact Subgroup.mem_center_iff.1 hx1 y.1

private theorem odd_card_center_rootPreimage (i : Fin Tag.E6.rank)
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) :
    Odd (Nat.card (Subgroup.center ↥(rootPreimage M i))) := by
  have hle : (Subgroup.center ↥(rootPreimage M i)).map (rootPreimage M i).subtype ≤
      Subgroup.center ↥S := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hc : rootPreimageMap M i x ∈ Subgroup.center (SL2 F) := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨y, rfl⟩ := rootPreimageMap_surjective M i u
      rw [← map_mul, ← map_mul, hx y]
    rw [CFSG.LocalAnalysis.EvenBN.Common.center_sl2_eq_bot_of_charP_two,
      Subgroup.mem_bot] at hc
    have hx1 : (x.1 : ↥S) ∈ Subgroup.center ↥S := by
      rw [← M.ker_π, MonoidHom.mem_ker]
      have h2 : rootPreimageHom M i x = 1 := by
        have h3 := congrArg (simpleRootEquiv (F := F) i) hc
        simpa [rootPreimageMap] using h3
      exact congrArg Subtype.val h2
    exact Subgroup.mem_center_iff.1 hx1 g
  have hdvd : Nat.card (Subgroup.center ↥(rootPreimage M i)) ∣ 3 := by
    have h1 : Nat.card (Subgroup.center ↥(rootPreimage M i)) =
        Nat.card ↥((Subgroup.center ↥(rootPreimage M i)).map (rootPreimage M i).subtype) :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective (rootPreimage M i))).symm
    have h2 : Nat.card ↥((Subgroup.center ↥(rootPreimage M i)).map
        (rootPreimage M i).subtype) ∣ Nat.card (Subgroup.center ↥S) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [h1]
    exact h2.trans hZ
  obtain h | h := (Nat.dvd_prime Nat.prime_three).1 hdvd
  · rw [h]; norm_num
  · rw [h]; norm_num

private theorem commutator_inf_ker_rootPreimageMap (hq : 4 ≤ Nat.card F)
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) (i : Fin Tag.E6.rank) :
    commutator ↥(rootPreimage M i) ⊓ (rootPreimageMap M i).ker = ⊥ := by
  by_cases h4 : Nat.card F = 4
  · have h := CFSG.LocalAnalysis.EvenBN.Common.commutator_inf_ker_eq_bot_of_card_four
      (k := F) h4 (π := rootPreimageMap M i) (Y := ⊤)
      (by rw [Subgroup.map_top_of_surjective _ (rootPreimageMap_surjective M i)])
      (by rw [top_inf_eq]; exact rootPreimageMap_ker_le_center M i)
      (odd_card_center_rootPreimage M i hZ)
    rwa [commutator_def]
  · have h5 : 5 ≤ Nat.card F := by omega
    have h9 : Nat.card F ≠ 9 := by
      intro h
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : Fintype F := Fintype.ofFinite F
      have hc3 : CharP F 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2) (by
        rw [← Nat.card_eq_fintype_card, h]; norm_num)
      have hc2 : CharP F 2 := ‹CharP F 2›
      have h23 := CharP.eq F hc2 hc3
      norm_num at h23
    exact CFSG.LocalAnalysis.EvenBN.Common.commutator_inf_ker_eq_bot_sl2 h5 h9
      (rootPreimageMap_surjective M i) (rootPreimageMap_ker_le_center M i)

private theorem exists_psi_of_commutator (i : Fin Tag.E6.rank) (hq : 4 ≤ Nat.card F)
    (hcomm : commutator ↥(rootPreimage M i) ⊓ (rootPreimageMap M i).ker = ⊥) :
    ∃ ψ : SL2 F →* ↥S, ∀ g, (M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) =
      simpleRootEquiv (F := F) i g := by
  haveI hperf : Group.IsPerfect (SL2 F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hq
  set C : Subgroup ↥(rootPreimage M i) := commutator ↥(rootPreimage M i) with hCdef
  have hCmap : Subgroup.map (rootPreimageMap M i) C = ⊤ := by
    rw [hCdef, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (rootPreimageMap_surjective M i), ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hCsurj : Function.Surjective ((rootPreimageMap M i).comp C.subtype) := by
    intro g
    have hg : g ∈ Subgroup.map (rootPreimageMap M i) C := by rw [hCmap]; exact Subgroup.mem_top g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hg
    exact ⟨⟨x, hx⟩, hxg⟩
  have hCinj : Function.Injective ((rootPreimageMap M i).comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : ↥(rootPreimage M i)) ∈ C ⊓ (rootPreimageMap M i).ker :=
      Subgroup.mem_inf.2 ⟨x.2, hx⟩
    rw [show C ⊓ (rootPreimageMap M i).ker = ⊥ from hcomm] at hx'
    exact Subtype.ext (Subgroup.mem_bot.1 hx')
  let e : ↥C ≃* SL2 F :=
    MulEquiv.ofBijective ((rootPreimageMap M i).comp C.subtype) ⟨hCinj, hCsurj⟩
  let ψ : SL2 F →* ↥S := ((rootPreimage M i).subtype.comp C.subtype).comp e.symm.toMonoidHom
  refine ⟨ψ, fun g => ?_⟩
  have h1 : (rootPreimageMap M i) ((e.symm g : ↥C) : ↥(rootPreimage M i)) = g :=
    MulEquiv.apply_symm_apply e g
  have h2 : rootPreimageHom M i ((e.symm g : ↥C) : ↥(rootPreimage M i)) =
      simpleRootEquiv (F := F) i g := by
    have h3 : (simpleRootEquiv (F := F) i)
        ((rootPreimageMap M i) ((e.symm g : ↥C) : ↥(rootPreimage M i))) =
        (simpleRootEquiv (F := F) i) g := by rw [h1]
    simpa [rootPreimageMap] using h3
  have h4 : (M.π ((e.symm g : ↥C) : ↥(rootPreimage M i)) :
      ↥(adjointGroup Tag.E6 F)) = simpleRootEquiv (F := F) i g := congrArg Subtype.val h2
  simpa [ψ] using h4

theorem exists_rootSL2_lift (hq : 4 ≤ Nat.card F)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) (i : Fin Tag.E6.rank) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S,
      ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
        simpleRootSL2 Tag.E6 F i g := by
  obtain ⟨ψ, hψ⟩ := exists_psi_of_commutator M i hq
    (commutator_inf_ker_rootPreimageMap M hq hZ i)
  exact ⟨ψ, fun g => by rw [hψ g]; exact simpleRootEquiv_coe i g⟩

end RootLift

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
