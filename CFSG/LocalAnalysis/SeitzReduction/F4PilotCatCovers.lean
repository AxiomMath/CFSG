module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.Adapters.LieModelSimple
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

theorem statedClassicalModel_of_lieModel_psp {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSp n p f) : StatedClassicalModel X .PSp n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem isSimpleGroup_of_lieModel_PSp {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSp n p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem center_eq_bot_of_isQuasisimple {X : Type*} [Group X] (hq : IsQuasisimple X)
    (hs : IsSimpleGroup X) : center X = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    have : Nontrivial (X ⧸ center X) := hq.2.1.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ center X)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [QuotientGroup.eq, h]
    exact mem_top _

section Induced

variable {K : Type} [Group K]

theorem eq_one_of_centerQuotientAut_eq_one [hK : Group.IsPerfect K] {τ : MulAut K}
    (h : centerQuotientAut τ = 1) : τ = 1 := by
  have hz : ∀ x : K, x⁻¹ * τ x ∈ center K := by
    intro x
    have h1 : centerQuotientAut τ (QuotientGroup.mk' (center K) x) =
        QuotientGroup.mk' (center K) x := by
      rw [h, MulAut.one_apply]
    rw [centerQuotientAut_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  let δ : K →* center K :=
    { toFun := fun x => ⟨x⁻¹ * τ x, hz x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := mem_center_iff.mp (hz x) y⁻¹
        change (x * y)⁻¹ * τ (x * y) = (x⁻¹ * τ x) * (y⁻¹ * τ y)
        calc (x * y)⁻¹ * τ (x * y) = y⁻¹ * (x⁻¹ * τ x) * τ y := by rw [map_mul]; group
          _ = (x⁻¹ * τ x) * y⁻¹ * τ y := by rw [hc]
          _ = (x⁻¹ * τ x) * (y⁻¹ * τ y) := by group }
  ext x
  have h1 : δ x = 1 := Abelianization.commutator_subset_ker δ Group.IsPerfect.mem_commutator
  have h2 : x⁻¹ * τ x = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp h2).symm

theorem orderOf_centerQuotientAut [Group.IsPerfect K] {τ : MulAut K} (hτ : orderOf τ = 2) :
    orderOf (centerQuotientAut τ) = 2 := by
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    have := congrArg (fun φ : MulAut K => φ x) hτ2
    simpa [pow_two] using this
  apply orderOf_eq_prime
  · ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) y
    rw [pow_two, MulAut.mul_apply, centerQuotientAut_mk, centerQuotientAut_mk, hττ,
      MulAut.one_apply]
  · intro h1
    have h2 := eq_one_of_centerQuotientAut_eq_one h1
    rw [h2, orderOf_one] at hτ
    exact absurd hτ (by norm_num)

theorem centerQuotientAut_conj (k : K) :
    centerQuotientAut (MulAut.conj k) = MulAut.conj (QuotientGroup.mk' (center K) k) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) y
  rw [centerQuotientAut_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem centerQuotientAut_mem_range {τ : MulAut K}
    (h : τ ∈ (MulAut.conj : K →* MulAut K).range) :
    centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨QuotientGroup.mk' (center K) k, (centerQuotientAut_conj k).symm⟩

end Induced

section Image

variable {K : Type} [Group K] {τ : MulAut K}

abbrev centerFixedProjection (τ : MulAut K) :
    fixedSubgroup τ →* fixedSubgroup (centerQuotientAut τ) :=
  fixedProjection (center K) τ (map_center_mulAut τ)

theorem coe_centerFixedProjection (x : fixedSubgroup τ) :
    ((centerFixedProjection τ x : fixedSubgroup (centerQuotientAut τ)) : K ⧸ center K) =
      QuotientGroup.mk' (center K) (x : K) :=
  rfl

theorem injective_centerFixedProjection_comp {D : Subgroup (fixedSubgroup τ)}
    (hZD : center D = ⊥) : Function.Injective ((centerFixedProjection τ).comp D.subtype) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have hdZ : ((d : fixedSubgroup τ) : K) ∈ center K := by
    have h1 : QuotientGroup.mk' (center K) ((d : fixedSubgroup τ) : K) = 1 :=
      congrArg Subtype.val hd
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hdc : d ∈ center D := by
    rw [mem_center_iff]
    intro d'
    apply Subtype.ext
    apply Subtype.ext
    exact mem_center_iff.mp hdZ _
  rw [hZD, mem_bot] at hdc
  exact hdc

theorem isComponent_map_fixedProjection {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hZD : center D = ⊥) :
    IsComponent (D.map (centerFixedProjection τ)) ∧
      Nonempty (D ≃* D.map (centerFixedProjection τ)) := by
  have hinv := map_center_mulAut τ
  have hrange : ((centerFixedProjection τ).comp D.subtype).range =
      D.map (centerFixedProjection τ) := by
    rw [MonoidHom.range_comp, range_subtype]
  let e : D ≃* D.map (centerFixedProjection τ) :=
    (MonoidHom.ofInjective (injective_centerFixedProjection_comp hZD)).trans
      (MulEquiv.subgroupCongr hrange)
  refine ⟨⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hD.1, ?_⟩, ⟨e⟩⟩
  have hsub : (D.map (fixedImageProjection (center K) τ hinv)).IsSubnormal :=
    hD.2.map (fixedImageProjection_surjective (center K) τ hinv)
  have hnormal : (fixedImage (center K) τ hinv).Normal :=
    fixedImage_normal (center K) τ hinv le_rfl
  have htrans := hsub.trans' hnormal.isSubnormal
  have hcomp : (fixedImage (center K) τ hinv).subtype.comp
      (fixedImageProjection (center K) τ hinv) = centerFixedProjection τ :=
    MonoidHom.ext fun _ => rfl
  rwa [map_map, hcomp] at htrans

theorem isPGroup_zpowers_of_pow_eq_one {u : K} {k : ℕ} (hu : u ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers u) := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

end Image

section TwoFree

variable {K : Type} [Group K] [Finite K] {τ : MulAut K}

theorem odd_card_center_of_twoFree {D : Subgroup (fixedSubgroup τ)} (hτ : orderOf τ = 2)
    (hodd : FixedCentralizerTwoFree τ D) : Odd (Nat.card (center K)) := by
  by_contra hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (center K) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := center K) 2 h2
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    have := congrArg (fun φ : MulAut K => φ x) hτ2
    simpa [pow_two] using this
  set z : K := (g : K) with hzdef
  have hzZ : z ∈ center K := g.2
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    exact congrArg Subtype.val h
  have hz1 : z ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hτzZ : τ z ∈ center K := by
    rw [← map_center_mulAut τ]
    exact mem_map_of_mem _ hzZ
  obtain ⟨w, hwZ, hw2, hw1, hτw⟩ : ∃ w : K, w ∈ center K ∧ w ^ 2 = 1 ∧ w ≠ 1 ∧ τ w = w := by
    by_cases hfix : τ z = z
    · exact ⟨z, hzZ, hz2, hz1, hfix⟩
    · have hzinv : z⁻¹ = z := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2]
      have hcomm : z * τ z = τ z * z := mem_center_iff.mp hzZ (τ z) |>.symm
      refine ⟨z * τ z, mul_mem hzZ hτzZ, ?_, ?_, ?_⟩
      · have hτz2 : (τ z) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
        rw [(Commute.mul_pow hcomm 2), hz2, hτz2, one_mul]
      · intro h
        apply hfix
        have h' : τ z = z⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [h', hzinv]
      · rw [map_mul, hττ, ← hcomm]
  have hU := hodd (zpowers w) (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hw2))
    (by
      rw [zpowers_le, mem_centralizer_iff]
      intro h _
      exact mem_center_iff.mp hwZ h)
    (by rw [zpowers_le]; exact hτw)
  exact hw1 (zpowers_eq_bot.mp hU)

theorem twoFree_centerQuotientAut {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hτ : orderOf τ = 2) (hodd : FixedCentralizerTwoFree τ D) :
    FixedCentralizerTwoFree (centerQuotientAut τ) (D.map (centerFixedProjection τ)) := by
  have hZ := odd_card_center_of_twoFree hτ hodd
  intro U hU hUc hUf
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  obtain ⟨k, hk⟩ := hU ⟨y, hy⟩
  have hyk : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) y
  set n := 2 ^ k with hn
  have hcop : (Nat.card (center K)).Coprime n :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hZ)
  have hxn : x ^ n ∈ center K := by
    have h1 : QuotientGroup.mk' (center K) (x ^ n) = 1 := by rw [map_pow]; exact hyk
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨z, hz⟩ := (Nat.Coprime.pow_left_bijective hcop).2 (⟨x ^ n, hxn⟩ : center K)⁻¹
  have hzn : (z : K) ^ n = (x ^ n)⁻¹ := by
    have := congrArg Subtype.val hz
    simpa using this
  set u : K := x * z with hudef
  have hzc : ∀ g : K, g * (z : K) = z * g := fun g => mem_center_iff.mp z.2 g
  have hun : u ^ n = 1 := by
    rw [hudef, Commute.mul_pow (hzc x), hzn, mul_inv_cancel]
  have hmku : QuotientGroup.mk' (center K) u = QuotientGroup.mk' (center K) x := by
    have hz1 : QuotientGroup.mk' (center K) (z : K) = 1 := (QuotientGroup.eq_one_iff _).mpr z.2
    rw [hudef, map_mul, hz1, mul_one]
  have hτu : τ u = u := by
    have h1 : QuotientGroup.mk' (center K) (τ u) = QuotientGroup.mk' (center K) u := by
      rw [← centerQuotientAut_mk, hmku]
      exact hUf hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    set c := (τ u)⁻¹ * u with hcdef
    have hcZ : c ∈ center K := h1
    have hτu' : τ u = u * c⁻¹ := by rw [hcdef]; group
    have hcn : c ^ n = 1 := by
      have h2 : (τ u) ^ n = 1 := by rw [← map_pow, hun, map_one]
      have hcomm : Commute u c⁻¹ := mem_center_iff.mp (inv_mem hcZ) u
      rw [hτu', hcomm.mul_pow, hun, one_mul, inv_pow] at h2
      exact inv_eq_one.mp h2
    have hco : orderOf (⟨c, hcZ⟩ : center K) = 1 := by
      have h3 : orderOf (⟨c, hcZ⟩ : center K) ∣ n :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hcn))
      exact Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard _) hcop) h3
    have hc1 : c = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hco)
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1
  let ι : D →* K := (fixedSubgroup τ).subtype.comp D.subtype
  have hcomZ : ∀ d : D, u * ι d * u⁻¹ * (ι d)⁻¹ ∈ center K := by
    intro d
    have hmem : ((centerFixedProjection τ (d : fixedSubgroup τ) :
        fixedSubgroup (centerQuotientAut τ)) : K ⧸ center K) ∈
        ((D.map (centerFixedProjection τ)).map (fixedSubgroup (centerQuotientAut τ)).subtype :
          Subgroup (K ⧸ center K)) :=
      mem_map_of_mem _ (mem_map_of_mem _ d.2)
    have h1 := mem_centralizer_iff.mp (hUc hy) _ hmem
    rw [coe_centerFixedProjection, ← hmku, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have hab : (ι d * u)⁻¹ * (u * ι d) ∈ center K := h1
    have hc := mem_center_iff.mp hab (ι d * u)
    have heq : u * ι d * u⁻¹ * (ι d)⁻¹ = (ι d * u)⁻¹ * (u * ι d) := by
      calc u * ι d * u⁻¹ * (ι d)⁻¹ =
            ((ι d * u) * ((ι d * u)⁻¹ * (u * ι d))) * (ι d * u)⁻¹ := by group
        _ = (((ι d * u)⁻¹ * (u * ι d)) * (ι d * u)) * (ι d * u)⁻¹ := by rw [hc]
        _ = (ι d * u)⁻¹ * (u * ι d) := by group
    rw [heq]
    exact hab
  let γ : D →* center K :=
    { toFun := fun d => ⟨u * ι d * u⁻¹ * (ι d)⁻¹, hcomZ d⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        have hb := mem_center_iff.mp (hcomZ b) (ι a)⁻¹
        change u * ι (a * b) * u⁻¹ * (ι (a * b))⁻¹ =
          (u * ι a * u⁻¹ * (ι a)⁻¹) * (u * ι b * u⁻¹ * (ι b)⁻¹)
        calc u * ι (a * b) * u⁻¹ * (ι (a * b))⁻¹ =
              u * ι a * u⁻¹ * ((u * ι b * u⁻¹ * (ι b)⁻¹) * (ι a)⁻¹) := by
                rw [map_mul]; group
          _ = u * ι a * u⁻¹ * ((ι a)⁻¹ * (u * ι b * u⁻¹ * (ι b)⁻¹)) := by rw [hb]
          _ = (u * ι a * u⁻¹ * (ι a)⁻¹) * (u * ι b * u⁻¹ * (ι b)⁻¹) := by group }
  have : Group.IsPerfect D := hD.1.1
  have hγ : ∀ d : D, u * ι d = ι d * u := by
    intro d
    have h1 : γ d = 1 := Abelianization.commutator_subset_ker γ Group.IsPerfect.mem_commutator
    have h2 : u * ι d * u⁻¹ * (ι d)⁻¹ = 1 := congrArg Subtype.val h1
    calc u * ι d = (u * ι d * u⁻¹ * (ι d)⁻¹) * (ι d * u) := by group
      _ = ι d * u := by rw [h2, one_mul]
  have hU1 := hodd (zpowers u) (isPGroup_zpowers_of_pow_eq_one hun)
    (by
      rw [zpowers_le, mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      exact (hγ ⟨g, hg⟩).symm)
    (by rw [zpowers_le]; exact hτu)
  have hu1 : u = 1 := zpowers_eq_bot.mp hU1
  rw [← hmku, hu1, map_one]

end TwoFree

theorem catSp6Covers : CatSp6Covers := by
  intro K _ _ hK τ hτ f D hD hD6
  have : Group.IsPerfect K := hK.1
  have hZD : center D = ⊥ := center_eq_bot_of_isQuasisimple hD.1 (isSimpleGroup_of_lieModel_PSp hD6)
  obtain ⟨hD', ⟨e⟩⟩ := isComponent_map_fixedProjection hD hZD
  refine ⟨orderOf_centerQuotientAut hτ, centerQuotientAut_mem_range,
    D.map (centerFixedProjection τ), hD', LieType.CurtisTits.lieModel_of_mulEquiv e hD6,
    fun hodd => ⟨odd_card_center_of_twoFree hτ hodd, twoFree_centerQuotientAut hD hτ hodd⟩⟩

end CFSG.SeitzReduction.F4Pilot
