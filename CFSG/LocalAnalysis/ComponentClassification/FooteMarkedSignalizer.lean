module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedBalanced

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
  CFSG.ComponentClassification.Sol76.Sig
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {T : Type} [Group T] [IsSimpleGroup T]
variable {family : Set (Subgroup G)}
variable {N : Subgroup G}
variable {Ki Kj B E F : Subgroup G}

private theorem exists_actual_hull_of_kernel_involution
    (hfamily : IsomorphicFamily family T)
    {K : Subgroup G} (hK : Marked family T K)
    {w : G} (hw2 : orderOf w = 2) (hwK : w ∈ coreActionKernel K) :
    ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({w} : Set G)) ∧
      Marked family T J ∧
      fixedShadow K (zpowers w) ⊔ oddCoreIn J = J ∧
      twoLayerIn (K ⊓ centralizer ({w} : Set G)) ⊔ oddCoreIn J = J := by
  have hqK : IsQuasisimple (K ⧸ pPrimeCore 2 K) := hK.quotient_quasisimple hfamily
  have hST : MarkedST family T := markedST_of_isomorphicFamily hfamily
  have hU : IsPGroup 2 (zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw2, pow_one])
  have hUK : zpowers w ≤ coreActionKernel K := zpowers_le.mpr hwK
  have hU0 : zpowers w ≠ ⊥ := zpowers_ne_bot_of_orderOf_eq_two hw2
  obtain ⟨J, hJcomp, hJmarked, -, hJcover⟩ := hST K hK (zpowers w) hU hUK hU0
  have hJcomp' : IsTwoComponentIn J (centralizer ({w} : Set G)) := by
    rwa [CFSG.ComponentClassification.Sol76.Sig.centralizer_zpowers_eq] at hJcomp
  have hshadow := fixedShadow_eq_twoLayer hqK hU hUK
  have hcover : twoLayerIn (K ⊓ centralizer ({w} : Set G)) ⊔ oddCoreIn J = J := by
    simpa only [hshadow, CFSG.ComponentClassification.Sol76.Sig.centralizer_zpowers_eq] using hJcover
  exact ⟨J, hJcomp', hJmarked, hJcover, hcover⟩

private theorem hullFamilies_of_isomorphicFamily
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj) :
    (∀ a ∈ B, a ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({a} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J ∧
          IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J)) ∧
    (∀ u ∈ F, u ≠ 1 → ∃ I : Subgroup G,
      IsTwoComponentIn I (centralizer ({u} : Set G)) ∧
        E ≤ I ∧ ⁅I, F⁆ ≤ oddCoreIn (centralizer ({u} : Set G))) := by
  obtain ⟨f₀, hf₀F, hf₀1⟩ := exists_mem_ne_one_of_isKleinFour hF
  obtain ⟨e₀, he₀E, he₀1⟩ := exists_mem_ne_one_of_isKleinFour hE
  have hqKi : IsQuasisimple (Ki ⧸ pPrimeCore 2 Ki) := hKi.quotient_quasisimple hfamily
  have hqKj : IsQuasisimple (Kj ⧸ pPrimeCore 2 Kj) := hKj.quotient_quasisimple hfamily
  constructor
  · intro a haB ha1
    have haK : a ∈ coreActionKernel Ki := hBKi haB
    have ha2 : orderOf a = 2 := orderOf_eq_prime (hB.2 a haB) ha1
    obtain ⟨J, hJcomp', hJmarked, -, hcover⟩ :=
      exists_actual_hull_of_kernel_involution hfamily hKi ha2 haK
    have hBa : B ≤ centralizer ({a} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hB.1.is_comm.comm (⟨b, hb⟩ : B) ⟨a, haB⟩))
    have hf₀a : f₀ ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF haB)) f₀ hf₀F)
    have hpump := mem_cover_and_commutator_le_oddCoreIn_of_fixed_pump
      (K := Ki) (J := J) (V := B) (w := a) (f := f₀)
      hqKi haK ha2 hBKi hBa (hFKi hf₀F)
      (orderOf_eq_two_of_isKleinFour hF hf₀F hf₀1) hf₀a hJcomp' hcover
    have hBJ : B ≤ coreActionKernel J :=
      CFSG.ComponentClassification.Sol76T13.R12.le_coreActionKernel_of_commutator_le_oddCoreIn hJcomp' hBa hpump.2
    have hFJ : F ≤ J := by
      intro f hf
      by_cases hf1 : f = 1
      · rw [hf1]
        exact one_mem J
      · exact (mem_cover_and_commutator_le_oddCoreIn_of_fixed_pump
          (K := Ki) (J := J) (V := B) (w := a) (f := f)
          hqKi haK ha2 hBKi hBa (hFKi hf)
          (orderOf_eq_two_of_isKleinFour hF hf hf1)
          (mem_centralizer_singleton_iff.mpr
            ((mem_centralizer_iff.mp (hBF haB)) f hf))
          hJcomp' hcover).1
    have hJsimple : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) :=
      (MulEquiv.isSimpleGroup_congr hJmarked.2.1.some).mpr inferInstance
    exact ⟨J, hJcomp', hFJ, hBJ, hJsimple⟩
  · intro u huF hu1
    have huK : u ∈ coreActionKernel Kj := hFKj huF
    have hu2 : orderOf u = 2 := orderOf_eq_two_of_isKleinFour hF huF hu1
    obtain ⟨I, hIcomp', -, -, hcover⟩ :=
      exists_actual_hull_of_kernel_involution hfamily hKj hu2 huK
    have hFu : F ≤ centralizer ({u} : Set G) := fun f hf =>
      mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hF f hf u huF)
    have he₀u : e₀ ∈ centralizer ({u} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF (hEB he₀E))) u huF).symm
    have hpump := mem_cover_and_commutator_le_oddCoreIn_of_fixed_pump
      (K := Kj) (J := I) (V := F) (w := u) (f := e₀)
      hqKj huK hu2 hFKj hFu (hEKj he₀E)
      (orderOf_eq_two_of_isKleinFour hE he₀E he₀1) he₀u hIcomp' hcover
    have hEI : E ≤ I := by
      intro e heE
      by_cases he1 : e = 1
      · rw [he1]
        exact one_mem I
      · exact (mem_cover_and_commutator_le_oddCoreIn_of_fixed_pump
          (K := Kj) (J := I) (V := F) (w := u) (f := e)
          hqKj huK hu2 hFKj hFu (hEKj heE)
          (orderOf_eq_two_of_isKleinFour hE heE he1)
          (mem_centralizer_singleton_iff.mpr
            ((mem_centralizer_iff.mp (hBF (hEB heE))) u huF).symm)
          hIcomp' hcover).1
    exact ⟨I, hIcomp', hEI, hpump.2⟩

theorem wGroup_eq_of_isomorphicFamily
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj) :
    CFSG.ComponentClassification.Sol76.Sig.wGroup B F = CFSG.ComponentClassification.Sol76.Sig.wGroup E F := by
  obtain ⟨hleft, hright⟩ := hullFamilies_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB
    hFKi hEKj hBKi hFKj
  exact CFSG.ComponentClassification.Sol76.Sig.wGroup_eq_of_two_actual_hulls hE hF hEB hBF hB
    (fun e he he1 => by
      obtain ⟨J, hJ, hFJ, hBJ, -⟩ := hleft e (hEB he) he1
      exact ⟨J, hJ, hFJ, hBJ⟩)
    hright

theorem theta_inf_le_theta_of_isomorphicFamily
    {a b : G}
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B) (hb1 : b ≠ 1) :
    CFSG.ComponentClassification.Sol76.Sig.theta F b ⊓ centralizer ({a} : Set G) ≤
      CFSG.ComponentClassification.Sol76.Sig.theta F a := by
  obtain ⟨hleft, hright⟩ := hullFamilies_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB
    hFKi hEKj hBKi hFKj
  have hleftE : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({e} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J := by
    intro e he he1
    obtain ⟨J, hJ, hFJ, hBJ, -⟩ := hleft e (hEB he) he1
    exact ⟨J, hJ, hFJ, hBJ⟩
  have hfixed := theta_inf_centralizer_le_of_two_actual_hulls hE hF hEB hBF hB hleftE hright hb hb1
  obtain ⟨Ja, hJacomp, hFJa, hBJa, -⟩ := hleft a ha ha1
  have hlocal : ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({a} : Set G)) →
        zpowers b ≤ coreActionKernel M ∨
          ⁅M, F⁆ ≤ oddCoreIn (centralizer ({a} : Set G)) :=
    component_dichotomy_of_actual_hull_kernel hJacomp (zpowers_le.mpr (hBJa hb)) hFJa
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hB.2 a ha) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hB.2 b hb) hb1
  have hFa : F ≤ centralizer ({a} : Set G) := fun f hf =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF ha)) f hf)
  have hFb : F ≤ centralizer ({b} : Set G) := fun f hf =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF hb)) f hf)
  exact theta_inf_le_theta_of_target_dichotomy hF ha2 hb2 (hB.comm ha hb) hFa hFb hlocal hfixed

theorem wGroup_spec_of_isomorphicFamily
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    (h8 : 2 ^ 3 ∣ Nat.card B) :
    Nat.Coprime 2 (Nat.card (CFSG.ComponentClassification.Sol76.Sig.wGroup B F)) ∧
      Group.IsSolvable (CFSG.ComponentClassification.Sol76.Sig.wGroup B F) ∧
      ∀ b ∈ B, b ≠ 1 →
        CFSG.ComponentClassification.Sol76.Sig.theta F b =
          CFSG.ComponentClassification.Sol76.Sig.wGroup B F ⊓ centralizer ({b} : Set G) := by
  have hbalance : ∀ a ∈ B, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      CFSG.ComponentClassification.Sol76.Sig.theta F a ⊓ centralizer ({b} : Set G) ≤
        CFSG.ComponentClassification.Sol76.Sig.theta F b := by
    intro a ha ha1 b hb hb1
    exact theta_inf_le_theta_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB
      hFKi hEKj hBKi hFKj hb hb1 ha ha1
  exact CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2 Nat.prime_two
    (by norm_num) B hB.1 hB.2 h8 (CFSG.ComponentClassification.Sol76.Sig.theta F)
    (isSolvableSignalizerFunctor_theta_of_balance hB.1 hBF hbalance)

theorem le_normalizer_wGroup_of_odd_of_isomorphicFamily
    {X : Subgroup G}
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    (hX : Nat.Coprime 2 (Nat.card X))
    (hEX : E ≤ normalizer (X : Set G))
    (hFX : F ≤ normalizer (X : Set G)) :
    X ≤ normalizer (CFSG.ComponentClassification.Sol76.Sig.wGroup B F : Set G) := by
  obtain ⟨hleft, hright⟩ := hullFamilies_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB
    hFKi hEKj hBKi hFKj
  exact CFSG.ComponentClassification.Sol76.Sig.le_normalizer_wGroup_of_odd_of_two_actual_hulls hE hF hEB hBF hB
    (fun e he he1 => hleft e (hEB he) he1) hright hX hEX hFX

theorem le_normalizer_wGroup_oddCoreIn_centralizer_of_isomorphicFamily
    {s : G}
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    (hEs : E ≤ centralizer ({s} : Set G))
    (hFs : F ≤ centralizer ({s} : Set G)) :
    oddCoreIn (centralizer ({s} : Set G)) ≤
      normalizer (CFSG.ComponentClassification.Sol76.Sig.wGroup B F : Set G) := by
  obtain ⟨hleft, hright⟩ := hullFamilies_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB
    hFKi hEKj hBKi hFKj
  exact CFSG.ComponentClassification.Sol76.Sig.le_normalizer_wGroup_oddCoreIn_centralizer_of_two_actual_hulls hE hF hEB hBF
    hB (fun e he he1 => hleft e (hEB he) he1) hright hEs hFs

theorem theta_inf_le_oddCoreIn_of_isomorphicFamily
    (hfamily : IsomorphicFamily family T)
    {K A : Subgroup G} (hK : Marked family T K)
    (hA : IsKleinFour A) (hAK : A ≤ coreActionKernel K)
    {f : G} (hfK : f ∈ K) (hf2 : orderOf f = 2)
    (hfA : A ≤ centralizer ({f} : Set G))
    {u : G} (hu : u ∈ A) (hu1 : u ≠ 1) :
    theta A f ⊓ centralizer ({u} : Set G) ≤
      oddCoreIn (centralizer ({u} : Set G)) := by
  have hqK : IsQuasisimple (K ⧸ pPrimeCore 2 K) := hK.quotient_quasisimple hfamily
  have hhulls : ∀ w ∈ A, w ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({w} : Set G)) ∧ f ∈ J ∧
        ⁅J, A⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hA hw hw1
    have hwK : w ∈ coreActionKernel K := hAK hw
    obtain ⟨J, hJcomp, -, -, hcover⟩ :=
      exists_actual_hull_of_kernel_involution hfamily hK hw2 hwK
    have hAw : A ≤ centralizer ({w} : Set G) := fun a ha =>
      mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hA a ha w hw)
    have hfw : f ∈ centralizer ({w} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_singleton_iff.mp (hfA hw)).symm)
    obtain ⟨hfJ, hJA⟩ := mem_cover_and_commutator_le_oddCoreIn_of_fixed_pump
      (K := K) (J := J) (V := A) (w := w) (f := f)
      hqK hwK hw2 hAK hAw hfK hf2 hfw hJcomp hcover
    exact ⟨J, hJcomp, hfJ, hJA⟩
  exact theta_inf_le_oddCoreIn_of_component_dichotomy hA hf2 hfA
    (component_dichotomy_of_actual_hulls hhulls) hu hu1

theorem theta_eq_theta_zpowers_of_isomorphicFamily
    (hfamily : IsomorphicFamily family T)
    {K A : Subgroup G} (hK : Marked family T K)
    (hA : IsKleinFour A) (hAK : A ≤ coreActionKernel K)
    {f : G} (hfK : f ∈ K) (hf2 : orderOf f = 2)
    (hfA : A ≤ centralizer ({f} : Set G))
    {u : G} (hu : u ∈ A) (hu1 : u ≠ 1) :
    theta A f = theta (zpowers u) f :=
  theta_eq_theta_zpowers_of_fixed_bound hA hfA hu hu1
    (theta_inf_le_oddCoreIn_of_isomorphicFamily hfamily hK hA hAK hfK hf2 hfA hu hu1)

theorem theta_eq_theta_zpowers_of_kernel_involution
    (hfamily : IsomorphicFamily family T)
    {K A : Subgroup G} (hK : Marked family T K)
    (hA : IsKleinFour A) (hAK : A ≤ coreActionKernel K)
    {f : G} (hfK : f ∈ K) (hf2 : orderOf f = 2)
    (hfA : A ≤ centralizer ({f} : Set G))
    {z : G} (hz2 : orderOf z = 2) (hzK : z ∈ coreActionKernel K)
    (hAz : A ≤ centralizer ({z} : Set G)) (hfz : f * z = z * f) :
    theta A f = theta (zpowers z) f := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    norm_num at hz2
  by_cases hzA : z ∈ A
  · exact theta_eq_theta_zpowers_of_isomorphicFamily hfamily hK hA hAK hfK hf2 hfA hzA hz1
  · obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one_of_isKleinFour hA
    have ha2 : orderOf a = 2 := orderOf_eq_two_of_isKleinFour hA ha ha1
    let D : Subgroup G := zpowers a ⊔ zpowers z
    have hD : IsKleinFour D :=
      CFSG.ComponentClassification.FooteLit.isKleinFour_sup_zpowers
        (sq_eq_one_of_orderOf_eq_two ha2) (sq_eq_one_of_orderOf_eq_two hz2) ha1 hz1
        (fun h => hzA (h ▸ ha)) (mem_centralizer_singleton_iff.mp (hAz ha))
    have hDK : D ≤ coreActionKernel K :=
      sup_le (zpowers_le.mpr (hAK ha)) (zpowers_le.mpr hzK)
    have hDf : D ≤ centralizer ({f} : Set G) :=
      sup_le (zpowers_le.mpr (hfA ha))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hfz.symm))
    have hAa : theta A f = theta (zpowers a) f :=
      theta_eq_theta_zpowers_of_isomorphicFamily (hfamily := hfamily) (hK := hK)
        (hA := hA) (hAK := hAK) (hfK := hfK) (hf2 := hf2) (hfA := hfA)
        (hu := ha) (hu1 := ha1)
    have hPa : theta D f = theta (zpowers a) f :=
      theta_eq_theta_zpowers_of_isomorphicFamily (hfamily := hfamily) (hK := hK)
        (hA := hD) (hAK := hDK) (hfK := hfK) (hf2 := hf2) (hfA := hDf)
        (hu := show a ∈ D from mem_sup_left (Subgroup.mem_zpowers a)) (hu1 := ha1)
    have hPz : theta D f = theta (zpowers z) f :=
      theta_eq_theta_zpowers_of_isomorphicFamily (hfamily := hfamily) (hK := hK)
        (hA := hD) (hAK := hDK) (hfK := hfK) (hf2 := hf2) (hfA := hDf)
        (hu := show z ∈ D from mem_sup_right (Subgroup.mem_zpowers z)) (hu1 := hz1)
    exact hAa.trans (hPa.symm.trans hPz)

theorem wGroup_eq_cyclic_of_kernel_involution
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    {z : G} (hz2 : orderOf z = 2)
    (hzKi : z ∈ coreActionKernel Ki) (hzKj : z ∈ coreActionKernel Kj)
    (hEz : E ≤ centralizer ({z} : Set G)) (hFz : F ≤ centralizer ({z} : Set G)) :
    wGroup B F = wGroup E (zpowers z) ∧ wGroup B F = wGroup F (zpowers z) := by
  have hEF : E ≤ centralizer (F : Set G) := hEB.trans hBF
  have hWBF : wGroup B F = wGroup E F :=
    wGroup_eq_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB hFKi hEKj hBKi hFKj
  have hEFfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤ oddCoreIn (centralizer ({v} : Set G)) := by
    intro b hb hb1 v hv hv1
    have hb2 : orderOf b = 2 := orderOf_eq_two_of_isKleinFour hE hb hb1
    have hFb : F ≤ centralizer ({b} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF (hEB hb))) w hw)
    exact theta_inf_le_oddCoreIn_of_isomorphicFamily (hfamily := hfamily) (hK := hKj)
      (hA := hF) (hAK := hFKj) (hfK := hEKj hb) (hf2 := hb2) (hfA := hFb)
      (hu := hv) (hu1 := hv1)
  have hFEfix : ∀ v ∈ F, v ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      theta E v ⊓ centralizer ({b} : Set G) ≤ oddCoreIn (centralizer ({b} : Set G)) := by
    intro v hv hv1 b hb hb1
    have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hF hv hv1
    have hEv : E ≤ centralizer ({v} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF (hEB he))) v hv).symm
    exact theta_inf_le_oddCoreIn_of_isomorphicFamily (hfamily := hfamily) (hK := hKi)
      (hA := hE) (hAK := hEB.trans hBKi) (hfK := hFKi hv) (hf2 := hv2) (hfA := hEv)
      (hu := hb) (hu1 := hb1)
  have hswap : wGroup E F = wGroup F E :=
    wGroup_eq_swap_of_fixed_bounds hE hF hEF hEFfix hFEfix
  have hthetaF : ∀ e ∈ E, e ≠ 1 → theta F e = theta (zpowers z) e := by
    intro e he he1
    have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
    have hFe : F ≤ centralizer ({e} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF (hEB he))) w hw)
    exact theta_eq_theta_zpowers_of_kernel_involution (hfamily := hfamily) (hK := hKj)
      (hA := hF) (hAK := hFKj) (hfK := hEKj he) (hf2 := he2) (hfA := hFe)
      (hz2 := hz2) (hzK := hzKj) (hAz := hFz)
      (hfz := mem_centralizer_singleton_iff.mp (hEz he))
  have hthetaE : ∀ v ∈ F, v ≠ 1 → theta E v = theta (zpowers z) v := by
    intro v hv hv1
    have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hF hv hv1
    have hEv : E ≤ centralizer ({v} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF (hEB he))) v hv).symm
    exact theta_eq_theta_zpowers_of_kernel_involution (hfamily := hfamily) (hK := hKi)
      (hA := hE) (hAK := hEB.trans hBKi) (hfK := hFKi hv) (hf2 := hv2) (hfA := hEv)
      (hz2 := hz2) (hzK := hzKi) (hAz := hEz)
      (hfz := mem_centralizer_singleton_iff.mp (hFz hv))
  have hWEz : wGroup E F = wGroup E (zpowers z) := by
    refine le_antisymm (iSup₂_le fun e he => iSup_le fun he1 => ?_)
      (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    · rw [hthetaF e he he1]
      exact theta_le_wGroup he he1
    · rw [← hthetaF e he he1]
      exact theta_le_wGroup he he1
  have hWFz : wGroup F E = wGroup F (zpowers z) := by
    refine le_antisymm (iSup₂_le fun v hv => iSup_le fun hv1 => ?_)
      (iSup₂_le fun v hv => iSup_le fun hv1 => ?_)
    · rw [hthetaE v hv hv1]
      exact theta_le_wGroup hv hv1
    · rw [← hthetaE v hv hv1]
      exact theta_le_wGroup hv hv1
  exact ⟨hWBF.trans hWEz, hWBF.trans (hswap.trans hWFz)⟩

theorem components_le_normalizer_wGroup_of_kernel_involution
    {N : Subgroup G}
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    {z : G} (hz2 : orderOf z = 2)
    (hzKi : z ∈ coreActionKernel Ki) (hzKj : z ∈ coreActionKernel Kj)
    (hEz : E ≤ centralizer ({z} : Set G)) (hFz : F ≤ centralizer ({z} : Set G))
    (hKiN : IsTwoComponentIn Ki N) (hKjN : IsTwoComponentIn Kj N) :
    (oddCoreIn N ⊔ Ki ⊔ Kj) ≤ normalizer (wGroup B F : Set G) := by
  obtain ⟨hW1, hW2⟩ := wGroup_eq_cyclic_of_kernel_involution hfamily hKi hKj hE hF hEB hBF hB
    hFKi hEKj hBKi hFKj hz2 hzKi hzKj hEz hFz
  have hEN : E ≤ N := hEKj.trans hKjN.1
  have hFN : F ≤ N := hFKi.trans hKiN.1
  have hON : oddCoreIn N ≤ normalizer (wGroup B F : Set G) :=
    le_normalizer_wGroup_of_odd_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB
      hFKi hEKj hBKi hFKj (Nat.coprime_two_left.mpr (odd_card_oddCoreIn N))
      (hEN.trans (CFSG.ComponentClassification.Sol76.le_normalizer_oddCoreIn N))
      (hFN.trans (CFSG.ComponentClassification.Sol76.le_normalizer_oddCoreIn N))
  have hOKi : oddCoreIn Ki ≤ normalizer (wGroup B F : Set G) :=
    (CFSG.ComponentClassification.Sol76.Sig.oddCoreIn_le_of_isTwoComponentIn hKiN).trans hON
  have hOKj : oddCoreIn Kj ≤ normalizer (wGroup B F : Set G) :=
    (CFSG.ComponentClassification.Sol76.Sig.oddCoreIn_le_of_isTwoComponentIn hKjN).trans hON
  have hzP : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hEzC : E ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rwa [CFSG.ComponentClassification.Sol76.Sig.centralizer_zpowers_eq z]
  have hFzC : F ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rwa [CFSG.ComponentClassification.Sol76.Sig.centralizer_zpowers_eq z]
  have hS2 : IsPGroup 2 (E ⊔ zpowers z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_isKleinFour hE) hzP
      (hEzC.trans (Subgroup.centralizer_le_normalizer _))
  have hS2' : IsPGroup 2 (F ⊔ zpowers z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_isKleinFour hF) hzP
      (hFzC.trans (Subgroup.centralizer_le_normalizer _))
  have hSK : E ⊔ zpowers z ≤ coreActionKernel Ki :=
    sup_le (hEB.trans hBKi) (zpowers_le.mpr hzKi)
  have hSK' : F ⊔ zpowers z ≤ coreActionKernel Kj :=
    sup_le hFKj (zpowers_le.mpr hzKj)
  have hcovKi : (Ki ⊓ centralizer ((E ⊔ zpowers z : Subgroup G) : Set G)) ⊔
      oddCoreIn Ki = Ki :=
    CFSG.ComponentClassification.Sol76.inf_centralizer_sup_oddCoreIn_eq hS2 hSK
  have hcovKj : (Kj ⊓ centralizer ((F ⊔ zpowers z : Subgroup G) : Set G)) ⊔
      oddCoreIn Kj = Kj :=
    CFSG.ComponentClassification.Sol76.inf_centralizer_sup_oddCoreIn_eq hS2' hSK'
  have hCD : centralizer ((E ⊔ zpowers z : Subgroup G) : Set G) ≤
      normalizer (wGroup E (zpowers z) : Set G) := by
    intro g hg
    have hgE : g ∈ centralizer (E : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast (le_sup_left : E ≤ E ⊔ zpowers z)) hg
    have hgz : g ∈ centralizer ((zpowers z : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast (le_sup_right : zpowers z ≤ E ⊔ zpowers z)) hg
    exact le_normalizer_wGroup
      (Subgroup.centralizer_le_normalizer (E : Set G) hgE)
      (Subgroup.centralizer_le_normalizer ((zpowers z : Subgroup G) : Set G) hgz)
  have hCD' : centralizer ((F ⊔ zpowers z : Subgroup G) : Set G) ≤
      normalizer (wGroup F (zpowers z) : Set G) := by
    intro g hg
    have hgF : g ∈ centralizer (F : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast (le_sup_left : F ≤ F ⊔ zpowers z)) hg
    have hgz : g ∈ centralizer ((zpowers z : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast (le_sup_right : zpowers z ≤ F ⊔ zpowers z)) hg
    exact le_normalizer_wGroup
      (Subgroup.centralizer_le_normalizer (F : Set G) hgF)
      (Subgroup.centralizer_le_normalizer ((zpowers z : Subgroup G) : Set G) hgz)
  have hCDW : centralizer ((E ⊔ zpowers z : Subgroup G) : Set G) ≤
      normalizer (wGroup B F : Set G) := by
    rwa [← hW1] at hCD
  have hCDW' : centralizer ((F ⊔ zpowers z : Subgroup G) : Set G) ≤
      normalizer (wGroup B F : Set G) := by
    rwa [← hW2] at hCD'
  have hKiH : Ki ≤ normalizer (wGroup B F : Set G) := by
    rw [← hcovKi]
    exact sup_le (inf_le_right.trans hCDW) hOKi
  have hKjH : Kj ≤ normalizer (wGroup B F : Set G) := by
    rw [← hcovKj]
    exact sup_le (inf_le_right.trans hCDW') hOKj
  exact sup_le (sup_le hON hKiH) hKjH

theorem base_le_normalizer_wGroup_of_balanced
    (hfamily : IsomorphicFamily family T)
    (hKi : Marked family T Ki) (hKj : Marked family T Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hFKi : F ≤ Ki) (hEKj : E ≤ Kj)
    (hBKi : B ≤ coreActionKernel Ki)
    (hFKj : F ≤ coreActionKernel Kj)
    (hKiN : IsTwoComponentIn Ki N) (hKjN : IsTwoComponentIn Kj N)
    (hne : Ki ≠ Kj)
    (hN : Balanced family T N) :
    base N ≤ Subgroup.normalizer
      (CFSG.ComponentClassification.Sol76.Sig.wGroup B F : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.normalizer (CFSG.ComponentClassification.Sol76.Sig.wGroup B F : Set G)
  have hEF : E ≤ centralizer (F : Set G) := hEB.trans hBF
  have hS : IsPGroup 2 (E ⊔ F : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_isKleinFour hE)
      (isPGroup_of_isKleinFour hF)
      (hEF.trans (Subgroup.centralizer_le_normalizer (F : Set G)))
  obtain ⟨S, z, hES0, hFS0, -, hzQ, hz2, hzC, -⟩ :=
    exists_central_sylow_admissible_pair (family := family) (T := T) (N := N)
      (Ki := Ki) (Kj := Kj) (E := E) (F := F)
      hfamily hN ⟨hKiN, hKi⟩ ⟨hKjN, hKj⟩ hne hE hF hEKj hFKi hEF
  obtain ⟨-, hQKernels, -, -⟩ :=
    pair_kernel_facts_of_balanced (family := family) (T := T) (N := N)
      (Ki := Ki) (Kj := Kj) hfamily hN ⟨hKiN, hKi⟩ ⟨hKjN, hKj⟩ hne
  have hzKi : z ∈ UnbalancedLayer.coreActionKernel Ki := (hQKernels hzQ).1
  have hzKj : z ∈ UnbalancedLayer.coreActionKernel Kj := (hQKernels hzQ).2
  have hEz : E ≤ centralizer ({z} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzC e (hES0 he))
  have hFz : F ≤ centralizer ({z} : Set G) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzC f (hFS0 hf))
  have hActor : (FooteLit.oddCoreIn N ⊔ Ki ⊔ Kj) ≤ H :=
    components_le_normalizer_wGroup_of_kernel_involution
      hfamily hKi hKj hE hF hEB hBF hB hFKi hEKj hBKi hFKj
      hz2 hzKi hzKj hEz hFz hKiN hKjN
  have hOH : FooteLit.oddCoreIn N ≤ H := by
    have h1 : FooteLit.oddCoreIn N ≤ FooteLit.oddCoreIn N ⊔ Ki := le_sup_left
    have h2 : FooteLit.oddCoreIn N ⊔ Ki ≤ (FooteLit.oddCoreIn N ⊔ Ki) ⊔ Kj :=
      le_sup_left
    exact h1.trans (h2.trans hActor)
  have hKiH : Ki ≤ H := by
    have h1 : Ki ≤ FooteLit.oddCoreIn N ⊔ Ki := le_sup_right
    have h2 : FooteLit.oddCoreIn N ⊔ Ki ≤ (FooteLit.oddCoreIn N ⊔ Ki) ⊔ Kj :=
      le_sup_left
    exact h1.trans (h2.trans hActor)
  have hKjH : Kj ≤ H := by
    have h1 : Kj ≤ (FooteLit.oddCoreIn N ⊔ Ki) ⊔ Kj := le_sup_right
    exact h1.trans hActor
  have hWBF : CFSG.ComponentClassification.Sol76.Sig.wGroup B F =
      CFSG.ComponentClassification.Sol76.Sig.wGroup E F :=
    wGroup_eq_of_isomorphicFamily hfamily hKi hKj hE hF hEB hBF hB hFKi hEKj hBKi hFKj
  have hCH : N ⊓ centralizer ((E ⊔ F : Subgroup G) : Set G) ≤ H := by
    intro g hg
    have hEsub : (E : Set G) ⊆ ((E ⊔ F : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.mem_sup_left hx
    have hFsub : (F : Set G) ⊆ ((E ⊔ F : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.mem_sup_right hx
    have hgE : g ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.centralizer_le hEsub hg.2
    have hgF : g ∈ Subgroup.centralizer (F : Set G) :=
      Subgroup.centralizer_le hFsub hg.2
    have hgEn : g ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.centralizer_le_normalizer (E : Set G) hgE
    have hgFn : g ∈ Subgroup.normalizer (F : Set G) :=
      Subgroup.centralizer_le_normalizer (F : Set G) hgF
    have hgW : g ∈ Subgroup.normalizer
        (CFSG.ComponentClassification.Sol76.Sig.wGroup E F : Set G) :=
      le_normalizer_wGroup hgEn hgFn
    change g ∈ Subgroup.normalizer
      (CFSG.ComponentClassification.Sol76.Sig.wGroup B F : Set G)
    rw [← hWBF] at hgW
    exact hgW
  have hBaseH : base N ≤ H := by
    have h := Sol76.Sig.oddTwoCoreIn_sup_twoLayerIn_le_of_components_and_centralizer
      (N := N) (J := Ki) (K := Kj) (S := E ⊔ F) (H := H)
      hKiN hKjN hS (sup_le (hEKj.trans le_sup_right) (hFKi.trans le_sup_left))
      hKiH hKjH hOH hCH
    simpa only [CFSG.ComponentClassification.FooteMarked.base] using h
  exact hBaseH

end CFSG.ComponentClassification.FooteMarked
