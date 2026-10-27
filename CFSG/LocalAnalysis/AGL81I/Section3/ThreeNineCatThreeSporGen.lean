module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGen
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSpor
public import CFSG.RankThree.OddKernel.ComponentRanks

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree

open CFSG.Open CFSG.LocalAnalysis.AGL81I.Section3.SporGen
open CFSG.ComponentClassification.OuterAutomorphisms (Outer centerQuotient_outer_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (equivalence)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

@[expose] noncomputable def coverGen {L : Type*} [Group L] (A : Subgroup L) : Subgroup L :=
  ⨆ (a : L) (_ : a ∈ A) (_ : a ≠ 1),
    Subgroup.closure ({a} ∪ {x | x * a = a * x ∧ Nat.Coprime (orderOf x) 3})

theorem commute_of_coprime_of_mk {K : Type*} [Group K] {Z : Subgroup K} [Z.Normal]
    (hZc : Z ≤ Subgroup.center K) (hZ : IsPGroup 3 Z) {x b : K}
    (hxb : (QuotientGroup.mk (x * b) : K ⧸ Z) = QuotientGroup.mk (b * x))
    (hx : Nat.Coprime (orderOf (QuotientGroup.mk x : K ⧸ Z)) 3) : x * b = b * x := by
  set c : K := (b * x)⁻¹ * (x * b) with hcdef
  have hcZ : c ∈ Z := QuotientGroup.eq.mp hxb.symm
  have hcc : c ∈ Subgroup.center K := hZc hcZ
  have hxbc : x * b = b * x * c := by rw [hcdef]; group
  have key : ∀ n : ℕ, x ^ n * b = b * x ^ n * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * b = x * (x ^ n * b) := by group
        _ = x * (b * x ^ n * c ^ n) := by rw [ih]
        _ = x * b * x ^ n * c ^ n := by group
        _ = b * x * c * x ^ n * c ^ n := by rw [hxbc]
        _ = b * x * (c * x ^ n) * c ^ n := by group
        _ = b * x * (x ^ n * c) * c ^ n := by
            rw [(Subgroup.mem_center_iff.mp hcc (x ^ n)).symm]
        _ = b * x ^ (n + 1) * c ^ (n + 1) := by group
  set m := orderOf (QuotientGroup.mk x : K ⧸ Z) with hm
  have hxm : x ^ m ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm, pow_orderOf_eq_one]
  have hxmc : x ^ m * b = b * x ^ m :=
    (Subgroup.mem_center_iff.mp (hZc hxm) b).symm
  have hcm : c ^ m = 1 := by
    have := (key m).symm.trans hxmc
    exact mul_left_cancel (a := b * x ^ m) (this.trans (mul_one _).symm)
  obtain ⟨k, hk⟩ := hZ ⟨c, hcZ⟩
  have hck : c ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf c ∣ Nat.gcd m (3 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcm) (orderOf_dvd_of_pow_eq_one hck)
  have hgcd : Nat.gcd m (3 ^ k) = 1 := Nat.Coprime.pow_right k hx
  rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  rw [hxbc, hdvd, mul_one]

theorem eq_top_of_sup_center_eq_top {K : Type*} [Group K] [Group.IsPerfect K] {H Z : Subgroup K}
    (hZc : Z ≤ Subgroup.center K) (h : H ⊔ Z = ⊤) : H = ⊤ := by
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g]
    simpa using hz⟩
  have hdecomp : ∀ x : K, ∃ y ∈ H, ∃ z ∈ Z, y * z = x := fun x =>
    Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  have hcomm : commutator K ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def]
    obtain ⟨u, hu, z, hz, rfl⟩ := hdecomp x
    obtain ⟨v, hv, w, hw, rfl⟩ := hdecomp y
    have hzc := Subgroup.mem_center_iff.mp (hZc hz)
    have hwc := Subgroup.mem_center_iff.mp (hZc hw)
    have : u * z * (v * w) * (u * z)⁻¹ * (v * w)⁻¹ = u * v * u⁻¹ * v⁻¹ := by
      calc u * z * (v * w) * (u * z)⁻¹ * (v * w)⁻¹
          = u * (z * (v * w)) * z⁻¹ * u⁻¹ * w⁻¹ * v⁻¹ := by group
        _ = u * ((v * w) * z) * z⁻¹ * u⁻¹ * w⁻¹ * v⁻¹ := by rw [← hzc (v * w)]
        _ = u * v * (w * u⁻¹) * w⁻¹ * v⁻¹ := by group
        _ = u * v * (u⁻¹ * w) * w⁻¹ * v⁻¹ := by rw [← hwc u⁻¹]
        _ = u * v * u⁻¹ * v⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.mul_mem hu hv) (H.inv_mem hu)) (H.inv_mem hv)
  rw [eq_top_iff, ← (Group.isPerfect_def.mp inferInstance)]
  exact hcomm

theorem finite_outer {L : Type*} [Group L] [Finite L] : Finite (Outer L) := by
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  infer_instance

theorem le_gammaOver_of_coverGen {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    [hKn : K.Normal] (hKq : CFSG.IsQuasisimple ↥K) (hZ : IsPGroup 3 (Subgroup.center ↥K))
    (hout : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) ≤ 2)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hgen : ∀ A : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      coverGen A = ⊤) :
    K ≤ gammaOver 1 3 E K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect ↥K := hKq.1
  have : Finite (Outer (↥K ⧸ Subgroup.center ↥K)) := finite_outer
  have hout' : Nat.card (Outer ↥K) ≤ 2 :=
    (Nat.card_le_card_of_injective _ (centerQuotient_outer_injective ↥K)).trans hout
  have hinn : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := fun e he =>
    exists_inner_of_card_outer_le_two (p := 3) hout' (by norm_num) (hE.2 e he)
  by_cases hker : ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ K, e * x * e⁻¹ = x
  · obtain ⟨e, heE, he1, hcomm⟩ := hker
    refine le_trans (fun x hx => Subgroup.mem_inf.mpr ⟨?_, hx⟩)
      (centralizer_inf_le_gammaOver (p := 3) heE he1 (hE.2 e heE))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcomm x hx
    calc x * e = e * x * e⁻¹ * e := by rw [this]
      _ = e * x := by group
  push Not at hker
  choose κ hκK hκ using hinn
  set Z : Subgroup ↥K := Subgroup.center ↥K with hZdef
  let kk : ∀ e ∈ E, ↥K := fun e he => ⟨κ e he, hκK e he⟩
  have hmk : ∀ k k' : ↥K, (∀ x ∈ K, (k : X) * x * (k : X)⁻¹ = k' * x * (k' : X)⁻¹) →
      (QuotientGroup.mk k : ↥K ⧸ Z) = QuotientGroup.mk k' := by
    intro k k' h
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have := h y y.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (y : X) * ((k : X)⁻¹ * k') = (k : X)⁻¹ * (k * y * (k : X)⁻¹) * k' := by group
      _ = (k : X)⁻¹ * (k' * y * (k' : X)⁻¹) * k' := by rw [this]
      _ = (k : X)⁻¹ * k' * y := by group
  let φ : E →* ↥K ⧸ Z :=
    { toFun := fun e => QuotientGroup.mk (kk e e.2)
      map_one' := by
        rw [← QuotientGroup.mk_one]
        refine hmk _ 1 fun x hx => ?_
        show κ _ _ * x * (κ _ _)⁻¹ = _
        rw [← hκ _ _ x hx]
        simp
      map_mul' := by
        rintro ⟨e, he⟩ ⟨f, hf⟩
        rw [← QuotientGroup.mk_mul]
        refine hmk _ _ fun x hx => ?_
        simp only [kk, Subgroup.coe_mul]
        rw [← hκ _ (E.mul_mem he hf) x hx]
        have h1 := hκ f hf x hx
        have h2 := hκ e he (κ f hf * x * (κ f hf)⁻¹)
          (K.mul_mem (K.mul_mem (hκK f hf) hx) (K.inv_mem (hκK f hf)))
        calc e * f * x * (e * f)⁻¹ = e * (f * x * f⁻¹) * e⁻¹ := by group
          _ = e * (κ f hf * x * (κ f hf)⁻¹) * e⁻¹ := by rw [h1]
          _ = κ e he * (κ f hf * x * (κ f hf)⁻¹) * (κ e he)⁻¹ := h2
          _ = κ e he * κ f hf * x * (κ e he * κ f hf)⁻¹ := by group }
  have hφ : ∀ (e : X) (he : e ∈ E), φ ⟨e, he⟩ = QuotientGroup.mk (kk e he) := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, he⟩ h1
    by_contra hne
    have he1 : e ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨x, hx, hxne⟩ := hker e he he1
    apply hxne
    rw [hφ, QuotientGroup.eq_one_iff] at h1
    have hc := Subgroup.mem_center_iff.mp h1 ⟨x, hx⟩
    rw [hκ e he x hx]
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, kk] at this
    rw [← this]
    group
  set A : Subgroup (↥K ⧸ Z) := φ.range with hAdef
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [← hEc, hAdef, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
      Subgroup.card_top]
  have hAel : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩ => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← φ.map_mul, ← φ.map_mul]
      congr 1
      exact hE.1.is_comm.comm a b
    · rintro _ ⟨⟨a, ha⟩, rfl⟩
      rw [← φ.map_pow]
      have : (⟨a, ha⟩ : E) ^ 3 = 1 := Subtype.ext (by simpa using hE.2 a ha)
      rw [this, φ.map_one]
  have hcov := hgen A hAel hAc
  set H : Subgroup ↥K := ⨆ (e : X) (he : e ∈ E) (_ : e ≠ 1),
    Subgroup.centralizer ({kk e he} : Set ↥K) with hHdef
  have hcentH : ∀ (e : X) (he : e ∈ E), e ≠ 1 →
      Subgroup.centralizer ({kk e he} : Set ↥K) ≤ H := fun e he he1 =>
    le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le he1 le_rfl))
  have hHtop : H = ⊤ := by
    refine eq_top_of_sup_center_eq_top (Z := Z) le_rfl ?_
    rw [← QuotientGroup.ker_mk' Z, ← Subgroup.comap_map_eq, eq_top_iff,
      ← Subgroup.map_le_iff_le_comap,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z), ← hcov]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    obtain ⟨⟨e, he⟩, rfl⟩ := ha
    have he1 : e ≠ 1 := by
      rintro rfl
      exact ha1 ((congrArg φ (Subtype.ext rfl)).trans φ.map_one)
    rw [Subgroup.closure_le]
    rintro y (hy | ⟨hya, hyc⟩)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨kk e he, hcentH e he he1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl), rfl⟩
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
      refine ⟨x, hcentH e he he1 ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm := commute_of_coprime_of_mk (Z := Z) le_rfl hZ (x := x) (b := kk e he)
        (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hya) hyc
      exact hcomm
  intro x hx
  have hxH : (⟨x, hx⟩ : ↥K) ∈ H := hHtop ▸ Subgroup.mem_top _
  have hmap : H.map K.subtype ≤ gammaOver 1 3 E K := by
    rw [hHdef, Subgroup.map_iSup]
    refine iSup_le fun e => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun he => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun he1 => ?_
    refine le_trans ?_ (centralizer_inf_le_gammaOver (p := 3) he he1 (hE.2 e he))
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
    have hy' : y * kk e he = kk e he * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hy'' := congrArg Subtype.val hy'
    simp only [Subgroup.coe_mul, kk] at hy''
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hκ e he y y.2
    have h2 : e * (y : X) * e⁻¹ = y := by
      rw [h1]
      calc κ e he * (y : X) * (κ e he)⁻¹ = (y : X) * κ e he * (κ e he)⁻¹ := by rw [hy'']
        _ = y := by group
    show (y : X) * e = e * y
    calc (y : X) * e = e * y * e⁻¹ * e := by rw [h2]
      _ = e * y := by group
  exact hmap ⟨⟨x, hx⟩, hxH, rfl⟩

theorem card_outer_le_of_quasisimple {K : Type*} [Group K] [Finite K] (hKq : CFSG.IsQuasisimple K)
    (hout : Nat.card (Outer (K ⧸ Subgroup.center K)) ≤ 2) : Nat.card (Outer K) ≤ 2 := by
  have : Group.IsPerfect K := hKq.1
  have : Finite (Outer (K ⧸ Subgroup.center K)) := finite_outer
  exact (Nat.card_le_card_of_injective _ (centerQuotient_outer_injective K)).trans hout

theorem four_le_pRank_sup_of_not_mem {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    {e : X} (heE : e ∈ E) (heK : e ∉ K) (he3 : e ^ 3 = 1) {k : X} (hkK : k ∈ K)
    (hk : ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹) (hk3 : k ^ 3 = 1)
    {A : Subgroup X} (hAK : A ≤ K) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 3) :
    4 ≤ CFSG.Open.pRank 3 (K ⊔ E) := by
  set c : X := k⁻¹ * e with hcdef
  have hcK : ∀ x ∈ K, x * c = c * x := by
    intro x hx
    have := hk x hx
    calc x * c = k⁻¹ * (k * x * k⁻¹) * e := by rw [hcdef]; group
      _ = k⁻¹ * (e * x * e⁻¹) * e := by rw [this]
      _ = c * x := by rw [hcdef]; group
  have hke : Commute k⁻¹ e := by
    have h := hk k hkK
    have : e * k = k * e := by
      calc e * k = e * k * e⁻¹ * e := by group
        _ = k * k * k⁻¹ * e := by rw [h]
        _ = k * e := by group
    exact (Commute.inv_left this.symm)
  have hc3 : c ^ 3 = 1 := by
    rw [hcdef, hke.mul_pow, inv_pow, hk3, he3]
    group
  have hcA : c ∉ A := by
    intro hc
    apply heK
    have : e = k * c := by rw [hcdef]; group
    rw [this]
    exact K.mul_mem hkK (hAK hc)
  have := CFSG.RankThree.OddKernel.succ_le_pRank_of_commute Nat.prime_three hA hAc
    (fun a ha => (hcK a (hAK ha))) hc3 hcA (hAK.trans le_sup_left)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hkK))
      (Subgroup.mem_sup_right heE))
  simpa using this

theorem le_gammaOver_of_e9Gen {X : Type} [Group X] [Finite X] {K E : Subgroup X} [hKn : K.Normal]
    (hKq : CFSG.IsQuasisimple ↥K) (hZ3 : Nat.card (Subgroup.center ↥K) = 3)
    (hout : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) ≤ 2)
    (hexp : ∀ x : ↥K, x ^ 9 = 1 → x ^ 3 = 1)
    (hA : ∃ A : Subgroup ↥K, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3)
    (hgen : ∀ F : Subgroup ↥K, IsElemAbelian 3 F → Nat.card F = 3 ^ 2 →
      F ⊓ Subgroup.center ↥K = ⊥ →
      ⨆ (f : ↥K) (_ : f ∈ F) (_ : f ≠ 1), Subgroup.centralizer ({f} : Set ↥K) = ⊤)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) (hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3) :
    K ≤ gammaOver 1 3 E K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hout' := card_outer_le_of_quasisimple hKq hout
  have hinn : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := fun e he =>
    exists_inner_of_card_outer_le_two (p := 3) hout' (by norm_num) (hE.2 e he)
  by_cases hker : ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ K, e * x * e⁻¹ = x
  · obtain ⟨e, heE, he1, hcomm⟩ := hker
    refine le_trans (fun x hx => Subgroup.mem_inf.mpr ⟨?_, hx⟩)
      (centralizer_inf_le_gammaOver (p := 3) heE he1 (hE.2 e heE))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcomm x hx
    calc x * e = e * x * e⁻¹ * e := by rw [this]
      _ = e * x := by group
  push Not at hker
  by_cases hEK : E ≤ K
  ·
    set F : Subgroup ↥K := E.subgroupOf K with hFdef
    have hFel : IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · simpa using congrArg Subtype.val (hE.1.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
      · simpa using hE.2 x (Subgroup.mem_subgroupOf.mp hx)
    have hFc : Nat.card F = 3 ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv).trans hEc
    have hFZ : F ⊓ Subgroup.center ↥K = ⊥ := by
      rw [eq_bot_iff]
      rintro f ⟨hfF, hfZ⟩
      rw [Subgroup.mem_bot]
      by_contra hf1
      have he1 : (f : X) ≠ 1 := fun h => hf1 (Subtype.ext h)
      obtain ⟨x, hx, hxne⟩ := hker f (Subgroup.mem_subgroupOf.mp hfF) he1
      apply hxne
      have := Subgroup.mem_center_iff.mp hfZ ⟨x, hx⟩
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h'
      rw [← h']
      group
    have hgenF := hgen F hFel hFc hFZ
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥K) ∈ ⨆ (f : ↥K) (_ : f ∈ F) (_ : f ≠ 1),
        Subgroup.centralizer ({f} : Set ↥K) := hgenF ▸ Subgroup.mem_top _
    have hmap : (⨆ (f : ↥K) (_ : f ∈ F) (_ : f ≠ 1),
        Subgroup.centralizer ({f} : Set ↥K)).map K.subtype ≤ gammaOver 1 3 E K := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun f => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hf => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hf1 => ?_
      have hfE : (f : X) ∈ E := Subgroup.mem_subgroupOf.mp hf
      have hf1' : (f : X) ≠ 1 := fun h => hf1 (Subtype.ext h)
      refine le_trans ?_ (centralizer_inf_le_gammaOver (p := 3) hfE hf1' (hE.2 f hfE))
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
      have hy' : y * f = f * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hy'
    exact hmap ⟨⟨x, hx⟩, hx', rfl⟩
  ·
    exfalso
    obtain ⟨e, heE, heK⟩ := Set.not_subset.mp hEK
    obtain ⟨k, hkK, hk⟩ := hinn e heE
    have he3 : e ^ 3 = 1 := hE.2 e heE
    have hk3 : k ^ 3 = 1 := by
      set c : X := k⁻¹ * e with hcdef
      have hcK : ∀ x ∈ K, x * c = c * x := by
        intro x hx
        have := hk x hx
        calc x * c = k⁻¹ * (k * x * k⁻¹) * e := by rw [hcdef]; group
          _ = k⁻¹ * (e * x * e⁻¹) * e := by rw [this]
          _ = c * x := by rw [hcdef]; group
      have hke : e * k = k * e := by
        have h := hk k hkK
        calc e * k = e * k * e⁻¹ * e := by group
          _ = k * k * k⁻¹ * e := by rw [h]
          _ = k * e := by group
      have hkc : k ^ 3 * c ^ 3 = 1 := by
        have hcomm : Commute k c := hcK k hkK
        have : (k * c) ^ 3 = 1 := by rw [hcdef, mul_inv_cancel_left]; exact he3
        rwa [hcomm.mul_pow] at this
      have hcen : (⟨k ^ 3, K.pow_mem hkK 3⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hk3c : k ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hkc
        rw [hk3c]
        have hyc := hcK y y.2
        have : (y : X) * c ^ 3 = c ^ 3 * y := (Commute.pow_right hyc 3)
        calc (y : X) * (c ^ 3)⁻¹ = (c ^ 3)⁻¹ * (c ^ 3 * y) * (c ^ 3)⁻¹ := by group
          _ = (c ^ 3)⁻¹ * (y * c ^ 3) * (c ^ 3)⁻¹ := by rw [this]
          _ = (c ^ 3)⁻¹ * y := by group
      have hz3 : (⟨k ^ 3, K.pow_mem hkK 3⟩ : ↥K) ^ 3 = 1 := by
        have h := orderOf_dvd_natCard (⟨⟨k ^ 3, K.pow_mem hkK 3⟩, hcen⟩ : Subgroup.center ↥K)
        rw [hZ3] at h
        have := orderOf_dvd_iff_pow_eq_one.mp h
        exact congrArg Subtype.val this
      have h9 : (⟨k, hkK⟩ : ↥K) ^ 9 = 1 := by
        have : (⟨k, hkK⟩ : ↥K) ^ 9 = ((⟨k, hkK⟩ : ↥K) ^ 3) ^ 3 := by rw [← pow_mul]
        rw [this]
        exact hz3
      exact congrArg Subtype.val (hexp _ h9)
    obtain ⟨A, hAel, hAc⟩ := hA
    have hAel' : IsElemAbelian 3 (A.map K.subtype) := by
      refine ⟨⟨⟨fun ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩ => Subtype.ext ?_⟩⟩, ?_⟩
      · have hab := hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
        simpa using congrArg Subtype.val (congrArg Subtype.val hab)
      · rintro _ ⟨a, ha, rfl⟩
        simpa using congrArg Subtype.val (hAel.2 a ha)
    have hAc' : Nat.card (A.map K.subtype) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hAc]
    have h4 := four_le_pRank_sup_of_not_mem heE heK he3 hkK hk hk3
      (Subgroup.map_subtype_le A) hAel' hAc'
    omega

section Dispatch

open TauCeti
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.RankThree.PartTwo.Sec4.Census (sporadicMultiplierOrder)

@[expose] def SporadicCoverGen (s : SporadicName) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* s.Group) →
    ∀ A : Subgroup L, IsElemAbelian 3 A → Nat.card A = 3 ^ 2 → coverGen A = ⊤

@[expose] def ONTripleCoverFacts : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃* SporadicName.ONan.Group) →
    (∀ x : L, x ^ 9 = 1 → x ^ 3 = 1) ∧ (∃ A : Subgroup L, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3) ∧
    ∀ F : Subgroup L, IsElemAbelian 3 F → Nat.card F = 3 ^ 2 → F ⊓ Subgroup.center L = ⊥ →
      ⨆ (f : L) (_ : f ∈ F) (_ : f ≠ 1), Subgroup.centralizer ({f} : Set L) = ⊤

@[expose] def RankFourSporadic (s : SporadicName) : Prop :=
  s = .Suz ∨ s = .ONan ∨ s = .Co1 ∨ s = .Co2 ∨ s = .Co3 ∨ s = .Fi22 ∨ s = .Fi23 ∨
    s = .Fi24Prime ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M

theorem le_gammaOver_of_centGen_simple {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    [hKn : K.Normal] {s : SporadicName} (hgen : SporadicCentGen 3 s)
    (hout : Nat.card (Outer s.Group) ≤ 2) (hZ : Subgroup.center ↥K = ⊥)
    (φ : ↥K ⧸ Subgroup.center ↥K ≃* s.Group) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) : K ≤ gammaOver 1 3 E K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : ↥K ≃* s.Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ
  have hout' : Nat.card (Outer ↥K) ≤ 2 :=
    (Nat.card_congr (equivalence ψ).toEquiv).le.trans
      hout
  refine le_gammaOver_of_inner (p := 3) ?_
    (fun e he => exists_inner_of_card_outer_le_two (p := 3) hout' (by norm_num) (hE.2 e he))
    hE hEc fun A hAK hA hAc => le_iSup_centralizer_inf_of_centGen hAK ?_
  · intro k hk hcomm
    have hc : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcomm y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · refine hgen ↥K ⟨ψ⟩ (A.subgroupOf K) ?_ ?_
    · refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · simpa using congrArg Subtype.val (hA.1.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
      · simpa using hA.2 x (Subgroup.mem_subgroupOf.mp hx)
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv).trans hAc

theorem le_gammaOver_of_coverGen_spor {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    [hKn : K.Normal] {s : SporadicName} (hgen : SporadicCoverGen s)
    (hout : Nat.card (Outer s.Group) ≤ 2) (hKq : CFSG.IsQuasisimple ↥K)
    (hZ : IsPGroup 3 (Subgroup.center ↥K)) (φ : ↥K ⧸ Subgroup.center ↥K ≃* s.Group)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) : K ≤ gammaOver 1 3 E K :=
  le_gammaOver_of_coverGen hKq hZ
    ((Nat.card_congr (equivalence φ).toEquiv).le.trans
      hout) hE hEc fun A hA hAc => hgen _ ⟨φ⟩ A hA hAc

theorem sporadicGen24_12Three_of
    (hmult : ∀ (s : SporadicName) (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty (L ⧸ Subgroup.center L ≃* s.Group) →
      Nat.card (Subgroup.center L) ∣ sporadicMultiplierOrder s)
    (hout : ∀ s : SporadicName, s ≠ .M → Nat.card (Outer s.Group) ≤ 2)
    (hrank : ∀ s : SporadicName, RankFourSporadic s → ∀ (L : Type) [Group L] [Finite L],
      Nonempty (L ≃* s.Group) → 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L))
    (hcover : ∀ s : SporadicName, (s = .J3 ∨ s = .Suz ∨ s = .Fi22 ∨ s = .Fi24Prime) →
      ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      3 ∣ Nat.card (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* s.Group) →
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L))
    (hJ1 : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* SporadicName.J1.Group) →
      ¬ 3 ^ 2 ∣ Nat.card L)
    (hgen : ∀ s : SporadicName, (s = .M23 ∨ s = .HS ∨ s = .J2 ∨ s = .M24 ∨ s = .He ∨ s = .Ru ∨
      s = .J4) → SporadicCentGen 3 s)
    (hM22 : SporadicCoverGen .M22) (hON : ONTripleCoverFacts) :
    SporadicGen24_12Three := by
  intro X _ _ K E s hKn hKq hOp ⟨φ⟩ hMcL hZin hE hEc hrk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hKn
  have hZp : IsPGroup 3 (Subgroup.center ↥K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥K) inferInstance inferInstance hOp
  have hdvd := hmult s ↥K hKq ⟨φ⟩
  have hrkK : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left).trans hrk
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hZbot : ¬ 3 ∣ sporadicMultiplierOrder s → Subgroup.center ↥K = ⊥ := fun h3 => by
    rcases n with _ | n
    · exact Subgroup.card_eq_one.mp (by simpa using hn)
    · exact absurd ((dvd_pow_self 3 n.succ_ne_zero).trans (hn ▸ hdvd)) h3
  have hZ3 : Subgroup.center ↥K ≠ ⊥ → 3 ∣ Nat.card (Subgroup.center ↥K) := fun h => by
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) h
    · rw [hn]
      exact dvd_pow_self 3 n.succ_ne_zero
  have hiso : Subgroup.center ↥K = ⊥ → Nonempty (↥K ≃* s.Group) := fun h =>
    ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm.trans φ⟩
  have hvac : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) → K ≤ gammaOver 1 3 E K := fun h4 => by
    omega
  have hrank' : RankFourSporadic s → ¬ 3 ∣ sporadicMultiplierOrder s →
      K ≤ gammaOver 1 3 E K := fun hs h3 =>
    hvac (hrank s hs ↥K (hiso (hZbot h3)))
  have hsimple : (s = .M23 ∨ s = .HS ∨ s = .J2 ∨ s = .M24 ∨ s = .He ∨ s = .Ru ∨ s = .J4) →
      s ≠ .M → ¬ 3 ∣ sporadicMultiplierOrder s → K ≤ gammaOver 1 3 E K := fun hs hM h3 =>
    le_gammaOver_of_centGen_simple (hgen s hs) (hout s hM) (hZbot h3) φ hE hEc
  have hcov' : (s = .J3 ∨ s = .Suz ∨ s = .Fi22 ∨ s = .Fi24Prime) → Subgroup.center ↥K ≠ ⊥ →
      K ≤ gammaOver 1 3 E K := fun hs hZ =>
    hvac (hcover s hs ↥K hKq (hZ3 hZ) ⟨φ⟩)
  cases s
  case McL => exact absurd rfl hMcL
  case M11 => exact absurd (Or.inl rfl) (hZin (hZbot (by decide)))
  case M12 => exact absurd (Or.inr (Or.inl rfl)) (hZin (hZbot (by decide)))
  case J3 =>
    by_cases hZ : Subgroup.center ↥K = ⊥
    · exact absurd (Or.inr (Or.inr rfl)) (hZin hZ)
    · exact hcov' (Or.inl rfl) hZ
  case Suz =>
    by_cases hZ : Subgroup.center ↥K = ⊥
    · exact hvac (hrank .Suz (Or.inl rfl) ↥K (hiso hZ))
    · exact hcov' (Or.inr (Or.inl rfl)) hZ
  case Fi22 =>
    by_cases hZ : Subgroup.center ↥K = ⊥
    · exact hvac (hrank .Fi22 (by simp [RankFourSporadic]) ↥K (hiso hZ))
    · exact hcov' (Or.inr (Or.inr (Or.inl rfl))) hZ
  case Fi24Prime =>
    by_cases hZ : Subgroup.center ↥K = ⊥
    · exact hvac (hrank .Fi24Prime (by simp [RankFourSporadic]) ↥K (hiso hZ))
    · exact hcov' (Or.inr (Or.inr (Or.inr rfl))) hZ
  case ONan =>
    by_cases hZ : Subgroup.center ↥K = ⊥
    · exact hvac (hrank .ONan (by simp [RankFourSporadic]) ↥K (hiso hZ))
    · have hcard : Nat.card (Subgroup.center ↥K) = 3 := by
        have h3 : Nat.card (Subgroup.center ↥K) ∣ 3 := hdvd
        rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hZ
        · exact h1
      obtain ⟨hexp, hA, hgenF⟩ := hON ↥K hKq hcard ⟨φ⟩
      exact le_gammaOver_of_e9Gen hKq hcard
        ((Nat.card_congr
          (equivalence φ).toEquiv).le.trans
          (hout .ONan (by decide))) hexp hA hgenF hE hEc hrk
  case J1 =>
    refine le_gammaOver_of_coverGen hKq hZp
      ((Nat.card_congr
        (equivalence φ).toEquiv).le.trans
        (hout .J1 (by decide))) hE hEc fun A _ hAc => ?_
    exfalso
    have hJ := hJ1 (↥K ⧸ Subgroup.center ↥K) ⟨φ⟩
    exact hJ (hAc ▸ Subgroup.card_subgroup_dvd_card A)
  case M22 =>
    exact le_gammaOver_of_coverGen_spor hM22 (hout .M22 (by decide)) hKq hZp φ hE hEc
  case M23 => exact hsimple (Or.inl rfl) (by decide) (by decide)
  case HS => exact hsimple (Or.inr (Or.inl rfl)) (by decide) (by decide)
  case J2 => exact hsimple (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
  case M24 => exact hsimple (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) (by decide)
  case He => exact hsimple (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide) (by decide)
  case Ru =>
    exact hsimple (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (by decide) (by decide)
  case J4 =>
    exact hsimple (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (by decide) (by decide)
  all_goals exact hrank' (by simp [RankFourSporadic]) (by decide)

end Dispatch

end CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree
