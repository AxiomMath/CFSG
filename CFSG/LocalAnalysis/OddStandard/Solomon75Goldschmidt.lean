module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedProductFixedPoints
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_hyperplane_commutator_lt [Finite G] {A X : Subgroup G}
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hA4 : 4 ≤ Nat.card A)
    (hAX : A ≤ normalizer (X : Set G)) (hodd : Odd (Nat.card X))
    (hX1 : X ≠ ⊥) :
    ∃ K : Subgroup G, K ≤ A ∧ K ≠ ⊥ ∧ ⁅X, K⁆ < X := by
  classical
  let S : Set (Subgroup G) :=
    {N | N ≤ X ∧ N ≠ X ∧ A ≤ normalizer (N : Set G) ∧ X ≤ normalizer (N : Set G)}
  have hbot : (⊥ : Subgroup G) ∈ S := by
    have h : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := normalizer_eq_top_iff.mpr inferInstance
    exact ⟨bot_le, Ne.symm hX1, h ▸ le_top, h ▸ le_top⟩
  obtain ⟨N, hNS, hNmax⟩ := S.exists_max_image (fun N => Nat.card N) S.toFinite ⟨⊥, hbot⟩
  obtain ⟨hNX, hNne, hAN, hXN⟩ := hNS
  have hmax : ∀ N' ∈ S, N ≤ N' → N' = N := fun N' hN' hle =>
    (Subgroup.eq_of_le_of_card_ge hle (hNmax N' hN')).symm
  have hNn : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  let _act : MulDistribMulAction A X := conjugationAction A X hAX
  have hinv : ∀ a : A, ∀ x ∈ N.subgroupOf X, a • x ∈ N.subgroupOf X := by
    intro a x hx
    show (a : G) * (x : G) * (a : G)⁻¹ ∈ N
    exact Subgroup.le_normalizer_iff.mp hAN a a.2 x hx
  let _qact : MulDistribMulAction A (X ⧸ N.subgroupOf X) :=
    invariantQuotientAction (N.subgroupOf X) hinv
  have hequiv : ∀ (a : A) (x : X), QuotientGroup.mk' (N.subgroupOf X) (a • x) =
      a • QuotientGroup.mk' (N.subgroupOf X) x :=
    invariant_quotient_equivariant (N.subgroupOf X) hinv
  have key : ∀ V : Subgroup (X ⧸ N.subgroupOf X), V.Normal →
      (∀ a : A, ∀ v ∈ V, a • v ∈ V) → V = ⊥ ∨ V = ⊤ := by
    intro V hVn hVinv
    let π := QuotientGroup.mk' (N.subgroupOf X)
    let M : Subgroup G := (V.comap π).map X.subtype
    have hMX : M ≤ X := Subgroup.map_subtype_le _
    have hmemM : ∀ x : X, (x : G) ∈ M ↔ π x ∈ V := by
      intro x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro h
        exact ⟨x, h, rfl⟩
    have hNM : N ≤ M := by
      intro n hn
      have h1 : π ⟨n, hNX hn⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hn
      exact (hmemM ⟨n, hNX hn⟩).mpr (by rw [h1]; exact V.one_mem)
    have hAM : A ≤ normalizer (M : Set G) := by
      refine Subgroup.le_normalizer_iff.mpr ?_
      intro a ha y hy
      have hyX : y ∈ X := hMX hy
      have h1 := (hmemM ⟨y, hyX⟩).mp hy
      have h2 : π ((⟨a, ha⟩ : A) • (⟨y, hyX⟩ : X)) ∈ V := by
        rw [hequiv]
        exact hVinv _ _ h1
      exact (hmemM ((⟨a, ha⟩ : A) • (⟨y, hyX⟩ : X))).mpr h2
    have hXM : X ≤ normalizer (M : Set G) := by
      refine Subgroup.le_normalizer_iff.mpr ?_
      intro x hx y hy
      have hyX : y ∈ X := hMX hy
      have h1 := (hmemM ⟨y, hyX⟩).mp hy
      have h2 : π (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) ∈ V := by
        rw [map_mul, map_mul, map_inv]
        exact hVn.conj_mem _ h1 _
      exact (hmemM (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹)).mpr h2
    by_cases hMeq : M = X
    · right
      refine eq_top_iff.mpr fun v _ => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      have : (x : G) ∈ M := by
        rw [hMeq]
        exact x.2
      exact (hmemM x).mp this
    · left
      have hMS : M ∈ S := ⟨hMX, hMeq, hAM, hXM⟩
      have hMN : M = N := hmax M hMS hNM
      refine eq_bot_iff.mpr fun v hv => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      have : (x : G) ∈ M := (hmemM x).mpr hv
      rw [hMN] at this
      exact (QuotientGroup.eq_one_iff _).mpr this
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hNtriv : N.subgroupOf X ≠ ⊤ := by
    intro h
    rw [subgroupOf_eq_top] at h
    exact hNne (le_antisymm hNX h)
  have : Nontrivial (X ⧸ N.subgroupOf X) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hNtriv
    refine eq_top_iff.mpr fun x _ => ?_
    have h : ((x : X) : X ⧸ N.subgroupOf X) = ((1 : X) : X ⧸ N.subgroupOf X) :=
      Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp (by simpa using h)
  have hcommA : ∀ a : A, ∀ v ∈ commutator (X ⧸ N.subgroupOf X),
      a • v ∈ commutator (X ⧸ N.subgroupOf X) := by
    intro a v hv
    have hmem : a • v ∈ (commutator (X ⧸ N.subgroupOf X)).map
        (MulDistribMulAction.toMonoidHom (X ⧸ N.subgroupOf X) a) :=
      Subgroup.mem_map_of_mem _ hv
    rw [_root_.commutator_def, Subgroup.map_commutator] at hmem
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top hmem
  have hc : commutator (X ⧸ N.subgroupOf X) = ⊥ := by
    rcases key _ inferInstance hcommA with h | h
    · exact h
    · exact absurd h (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne
  have hcomm : ∀ u v : X ⧸ N.subgroupOf X, u * v = v * u := by
    intro u v
    have h : ⁅u, v⁆ ∈ commutator (X ⧸ N.subgroupOf X) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top u) (mem_top v)
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hirr : ∀ U : Subgroup (X ⧸ N.subgroupOf X), (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hUn : U.Normal :=
      ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
    exact key U hUn hU
  let _ : CommGroup (X ⧸ N.subgroupOf X) :=
    { (inferInstance : Group (X ⧸ N.subgroupOf X)) with mul_comm := hcomm }
  have : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (comm_of_sq_eq_one hA2 a.2 b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun a => Subtype.ext (by simpa using hA2 a a.2)) }
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hBi, hBtriv⟩ :=
    CFSG.SolvableHall.exists_hyperplane_acting_trivially_of_irreducible (p := 2) (A := A)
      (H := X ⧸ N.subgroupOf X) hirr
  refine ⟨B.map A.subtype, Subgroup.map_subtype_le B, ?_, ?_⟩
  · intro h
    have hB1 : B = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective B A.subtype_injective).mp h
    have hcard := B.card_mul_index
    rw [hBi, hB1, Subgroup.card_bot] at hcard
    omega
  · refine lt_of_le_of_lt ?_ (lt_of_le_of_ne hNX hNne)
    rw [commutator_le]
    intro x hx k hk
    obtain ⟨b, hb, rfl⟩ := hk
    have h1 := hBtriv b hb (QuotientGroup.mk' (N.subgroupOf X) ⟨x, hx⟩)
    rw [← hequiv] at h1
    have h1' : (((b : A) • (⟨x, hx⟩ : X) : X) : X ⧸ N.subgroupOf X) =
        ((⟨x, hx⟩ : X) : X ⧸ N.subgroupOf X) := h1
    have h2 : ((b : A) • (⟨x, hx⟩ : X))⁻¹ * ⟨x, hx⟩ ∈ N.subgroupOf X := QuotientGroup.eq.mp h1'
    have h3 : (↑b * x * (↑b)⁻¹)⁻¹ * x ∈ N := h2
    have h4 : x * ((↑b * x * (↑b)⁻¹)⁻¹ * x) * x⁻¹ ∈ N :=
      Subgroup.le_normalizer_iff.mp hXN x hx _ h3
    have h5 : ⁅x, (A.subtype b : G)⁆ = x * ((↑b * x * (↑b)⁻¹)⁻¹ * x) * x⁻¹ := by
      rw [commutatorElement_def]
      change x * (b : G) * x⁻¹ * (b : G)⁻¹ = _
      group
    rw [h5]
    exact h4

section Goldschmidt

variable [Finite G]

@[expose] def goldschmidtGen (A X : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, ⨆ (_ : a ≠ 1), (centralizer (A : Set G) ⊓ ⁅X ⊓ cen a, A⁆)

omit [Finite G] in
theorem goldschmidtGen_mono {A X Y : Subgroup G} (h : X ≤ Y) :
    goldschmidtGen A X ≤ goldschmidtGen A Y :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_left _ (Subgroup.commutator_mono_left (inf_le_inf_right _ h))

theorem goldschmidt_aux {A : Subgroup G} (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hA4 : 4 ≤ Nat.card A) :
    ∀ (n : ℕ) (X : Subgroup G), Nat.card X = n → A ≤ normalizer (X : Set G) →
      Odd (Nat.card X) → ⁅X, A⁆ = X → X ⊓ centralizer (A : Set G) ≤ goldschmidtGen A X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hXn hAX hodd hXA
  by_cases hX1 : X = ⊥
  · rw [hX1]
    simp
  have hpA : IsPGroup 2 A := isPGroup_two_of_sq hA2
  obtain ⟨K, hKA, hK1, hKX⟩ := exists_hyperplane_commutator_lt hA2 hA4 hAX hodd hX1
  have hpK : IsPGroup 2 K := isPGroup_two_of_sq (fun k hk => hA2 k (hKA hk))
  have hKXn : K ≤ normalizer (X : Set G) := hKA.trans hAX
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => comm_of_sq_eq_one hA2 hx hy
  have hAK : A ≤ normalizer (K : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun a ha k hk => ?_
    have h : a * k = k * a := hcommA a ha k (hKA hk)
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  set W := ⁅X, K⁆ with hWdef
  have hWX : W ≤ X := commutator_le_of_normalizing X K hKXn
  have hWodd : Odd (Nat.card W) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hWX)
  have hAW : A ≤ normalizer (W : Set G) := fun a ha => mem_normalizer_commutator (hAX ha) (hAK ha)
  have hXW : X ≤ normalizer (W : Set G) := normalized_commutator_target_normalizes K X hKXn
  have hWW : ⁅W, A⁆ = W := by
    have h1 : ⁅W, K⁆ = W :=
      coprime_normalized_commutator_idempotent 2 Nat.prime_two K X hpK hKXn
        (Nat.coprime_two_left.mpr hodd)
    refine le_antisymm (commutator_le_of_normalizing W A hAW) ?_
    calc W = ⁅W, K⁆ := h1.symm
      _ ≤ ⁅W, A⁆ := Subgroup.commutator_mono_right hKA
  have hWlt : Nat.card W < n := hXn ▸ Subgroup.card_lt_of_lt hKX
  have hIH := ih _ hWlt W rfl hAW hWodd hWW
  set XK := X ⊓ centralizer (K : Set G) with hXKdef
  have hAcK : A ≤ centralizer (K : Set G) := fun a ha =>
    mem_centralizer_iff.mpr (fun k hk => hcommA k (hKA hk) a ha)
  have hAXK : A ≤ normalizer (XK : Set G) := fun a ha =>
    mem_normalizer_inf (hAX ha) (Subgroup.le_normalizer (hAcK ha))
  have hXKX : XK ≤ X := inf_le_left
  have hXKodd : Odd (Nat.card XK) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hXKX)
  have hfactK : W ⊔ XK = X :=
    coprime_normalized_commutator_factorization 2 Nat.prime_two K X hpK hKXn
      (Nat.coprime_two_left.mpr hodd)
  set M := ⁅XK, A⁆ with hMdef
  set D := XK ⊓ W with hDdef
  have hMXK : M ≤ XK := commutator_le_of_normalizing XK A hAXK
  have hDXK : D ≤ XK := inf_le_left
  have hAM : A ≤ normalizer (M : Set G) := normalized_commutator_normalized A XK hAXK
  have hXKD : XK ≤ normalizer (D : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (hXW (hXKX hx))
  have hAD : A ≤ normalizer (D : Set G) := fun a ha => mem_normalizer_inf (hAXK ha) (hAW ha)
  have hAXA : ⁅X, A⁆ ≤ W ⊔ M := by
    rw [commutator_le]
    intro x hx a ha
    obtain ⟨w, hw, y, hy, rfl⟩ :=
      (mem_sup_of_normalizing W XK (fun z hz => hXW (hXKX hz)) x).mp (by rw [hfactK]; exact hx)
    have hid : ⁅w * y, a⁆ = w * ⁅y, a⁆ * (a * w * a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    refine (W ⊔ M).mul_mem ((W ⊔ M).mul_mem (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right ?_)) (Subgroup.mem_sup_left ?_)
    · exact Subgroup.commutator_mem_commutator hy ha
    · exact W.inv_mem (Subgroup.le_normalizer_iff.mp hAW a ha w hw)
  have hXWM : X ≤ W ⊔ M := by
    calc X = ⁅X, A⁆ := hXA.symm
      _ ≤ W ⊔ M := hAXA
  have hwhole : subgroupProduct M D = (XK : Set G) := by
    apply (subgroup_product_eq_subgroup_iff XK M D hMXK hDXK).mpr
    intro y hy
    have hyX : y ∈ X := hXKX hy
    obtain ⟨w, hw, m, hm, hwm⟩ :=
      (mem_sup_of_normalizing W M (fun z hz => hXW (hXKX (hMXK hz))) y).mp (hXWM hyX)
    have hwXK : w ∈ XK := by
      have h : w = y * m⁻¹ := by
        rw [← hwm]
        group
      rw [h]
      exact XK.mul_mem hy (XK.inv_mem (hMXK hm))
    have hwD : w ∈ D := ⟨hwXK, hw⟩
    refine ⟨m, hm, m⁻¹ * w * m, ?_, ?_⟩
    · have h := Subgroup.le_normalizer_iff.mp hXKD m⁻¹ (XK.inv_mem (hMXK hm)) w hwD
      simpa using h
    · rw [← hwm]
      group
  have hprod := normalized_product_fixed_points 2 Nat.prime_two A XK M D hpA hAXK hAM hAD hMXK hDXK
    (Nat.coprime_two_left.mpr hXKodd) hwhole
  intro x hx
  have hxXK : x ∈ ((XK ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    ⟨⟨hx.1, Subgroup.centralizer_le (Set.subset_def.mpr fun k hk => hKA hk) hx.2⟩, hx.2⟩
  rw [← hprod] at hxXK
  obtain ⟨m, hm, d, hd, rfl⟩ := hxXK
  obtain ⟨⟨a, haK⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hXKa : XK ≤ X ⊓ cen a :=
    inf_le_inf_left X (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haK))
  have hmR : m ∈ goldschmidtGen A X := by
    have hmM : m ∈ ⁅X ⊓ cen a, A⁆ := (Subgroup.commutator_mono_left hXKa) hm.1
    have hle : centralizer (A : Set G) ⊓ ⁅X ⊓ cen a, A⁆ ≤ goldschmidtGen A X :=
      le_iSup_of_le a (le_iSup_of_le (hKA haK) (le_iSup_of_le ha1' le_rfl))
    exact hle ⟨hm.2, hmM⟩
  have hdR : d ∈ goldschmidtGen A X := goldschmidtGen_mono hWX (hIH ⟨hd.1.2, hd.2⟩)
  exact (goldschmidtGen A X).mul_mem hmR hdR

end Goldschmidt

section GoldschmidtMain

theorem goldschmidtGen_le {A X : Subgroup G} (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAX : A ≤ normalizer (X : Set G)) : goldschmidtGen A X ≤ X ⊓ centralizer (A : Set G) := by
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun _ => ?_
  have hAT : A ≤ normalizer ((X ⊓ cen a : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hAX hx) (Subgroup.le_normalizer (mem_cen_of_mem hA2 ha hx))
  exact fun x hx => ⟨(commutator_le_of_normalizing _ _ hAT hx.2).1, hx.1⟩

theorem goldschmidt72_thm23 :
    ∀ (G : Type) [Group G] [Finite G] (A X : Subgroup G), (∀ a ∈ A, a ^ 2 = 1) →
      4 ≤ Nat.card A → A ≤ normalizer (X : Set G) → Odd (Nat.card X) → ⁅X, A⁆ = X →
        X ⊓ centralizer (A : Set G) =
          ⨆ a ∈ A, ⨆ (_ : a ≠ 1), (centralizer (A : Set G) ⊓ ⁅X ⊓ cen a, A⁆) := by
  intro G _ _ A X hA2 hA4 hAX hodd hXA
  exact le_antisymm (goldschmidt_aux hA2 hA4 _ X rfl hAX hodd hXA) (goldschmidtGen_le hA2 hAX)

end GoldschmidtMain

end CFSG.OddStandard.Solomon75
