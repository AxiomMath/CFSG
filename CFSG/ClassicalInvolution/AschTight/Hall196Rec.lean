module

public import CFSG.ClassicalInvolution.AschTight.Hall196Ker
public import CFSG.ClassicalInvolution.AschTight.Hall196Lift
public import CFSG.ClassicalInvolution.AschTight.Hall196GW
public import CFSG.ClassicalInvolution.AschTight.Hall196XK

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.QuaternionStructure
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isSL2ModOdd_of_surjective {H P : Subgroup G} {z : G} (hP : IsSylow2In P H)
    (hQ : IsQuaternionSub P) (hzP : z ∈ P) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ h ∈ H, h * z = z * h) {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (ψ : ↥H →* GorensteinWalter.PSL2 F) (hψ : Function.Surjective ψ)
    (hker : ∀ y : ↥H, ψ y = 1 ↔ (y : G) ∈ oddCoreOf H ⊔ Subgroup.zpowers z) :
    IsSL2ModOdd H (Nat.card F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzH : z ∈ H := hP.1 hzP
  set z' : ↥H := ⟨z, hzH⟩ with hz'
  have hON : Subgroup.zpowers z ≤ Subgroup.normalizer (oddCoreOf H : Set G) :=
    Subgroup.zpowers_le.mpr
      (AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hzH))
  have hOle : classicalInvolutionOddCore ↥H ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_left ⟨x, hx, rfl⟩
  set ψ' := QuotientGroup.lift (classicalInvolutionOddCore ↥H) ψ hOle with hψ'
  have hψ's : Function.Surjective ψ' := by
    intro g
    obtain ⟨y, rfl⟩ := hψ g
    exact ⟨QuotientGroup.mk y, QuotientGroup.lift_mk _ hOle y⟩
  set zb : ↥H ⧸ classicalInvolutionOddCore ↥H := QuotientGroup.mk z' with hzb
  have hker' : ψ'.ker = Subgroup.zpowers zb := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hψ', QuotientGroup.lift_mk, hker]
      constructor
      · intro hy
        have hy' : (y : G) ∈ ((oddCoreOf H ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := hy
        rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hON] at hy'
        obtain ⟨o, ho, w, hw, how⟩ := Set.mem_mul.mp hy'
        obtain ⟨o', ho', rfl⟩ := ho
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hyeq : y = o' * z' ^ i := Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_zpow, ← how]
          rfl)
        refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
        rw [hyeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o').mpr ho', one_mul, hzb,
          QuotientGroup.mk_zpow]
      · intro hy
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [hzb, ← QuotientGroup.mk_zpow, QuotientGroup.eq] at hi
        have h1 : ((z' ^ i)⁻¹ * y : G) ∈ oddCoreOf H := ⟨_, hi, rfl⟩
        have e : (y : G) = z ^ i * ((z' ^ i)⁻¹ * y : G) := by
          simp only [Subgroup.coe_inv, Subgroup.coe_zpow]
          show (y : G) = z ^ i * ((z ^ i)⁻¹ * (y : G))
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers z i))
          (Subgroup.mem_sup_left h1)
  have hzO : z' ∉ classicalInvolutionOddCore ↥H := by
    intro h
    have h1 : z ∈ oddCoreOf H := ⟨z', h, rfl⟩
    have h2 : z ∈ P ⊓ oddCoreOf H := ⟨hzP, h1⟩
    rw [S1916.inf_oddCoreOf_eq_bot hP.2.1 H, Subgroup.mem_bot] at h2
    exact hz1 h2
  have hzb2 : orderOf zb = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hzb, sq, ← QuotientGroup.mk_mul]
      have : z' * z' = 1 := Subtype.ext hz2
      rw [this, QuotientGroup.mk_one]
    · intro h
      exact hzO ((QuotientGroup.eq_one_iff z').mp h)
  have hzbc : zb ∈ Subgroup.center (↥H ⧸ classicalInvolutionOddCore ↥H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H y =>
      rw [hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hzc y y.2)
  have huniq : ∀ t : ↥H ⧸ classicalInvolutionOddCore ↥H, orderOf t = 2 → t = zb := by
    intro t ht
    have hmks : Function.Surjective (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) :=
      QuotientGroup.mk'_surjective _
    have hP' : IsSylow2In (P.subgroupOf H) ⊤ := by
      have := isSylow2In_subgroupOf_of_le hP le_rfl
      rwa [Subgroup.subgroupOf_self] at this
    have hPb := isSylow2In_map_hom (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) hP'
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hmks] at hPb
    have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    obtain ⟨S'', hS'', htS''⟩ := IsSylow2In.exists_ge ht2 le_top
    obtain ⟨g, -, hg⟩ := exists_conjSub_eq_of_isSylow2In hPb hS''
    have htg : t ∈ conjSub g ((P.subgroupOf H).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥H))) :=
      hg ▸ htS'' (Subgroup.mem_zpowers t)
    rw [mem_conjSub_iff] at htg
    obtain ⟨x, hx, hxt⟩ := htg
    have hxo : orderOf (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x) = 2 := by
      rw [hxt, ← ht, show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp]
      exact MulEquiv.orderOf_eq _ _
    have hxsq : QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (x * x) = 1 := by
      have h1 := pow_orderOf_eq_one (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x)
      rw [hxo, sq, ← map_mul] at h1
      exact h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxsq
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have hx2 : (x : G) * x = 1 := by
      have h2 : ((x * x : ↥H) : G) ∈ P ⊓ oddCoreOf H := ⟨P.mul_mem hxP hxP, ⟨_, hxsq, rfl⟩⟩
      rw [S1916.inf_oddCoreOf_eq_bot hP.2.1 H, Subgroup.mem_bot] at h2
      exact h2
    have hx1 : (x : G) ≠ 1 := by
      intro h
      have hx1' : x = 1 := Subtype.ext h
      rw [hx1', map_one, orderOf_one] at hxo
      omega
    have hxz : x = z' := Subtype.ext
      (IsQuaternionSub.eq_of_mul_self_eq_one hQ hxP hzP hx2 hz2 hx1 hz1)
    rw [hxz] at hxt
    have hgt : t = g * zb * g⁻¹ := by
      rw [show zb = QuotientGroup.mk' (classicalInvolutionOddCore ↥H) z' from rfl, hxt]
      group
    rw [hgt, Subgroup.mem_center_iff.mp hzbc g]
    group
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_of_ker hF ψ' hψ's hker' hzb2 huniq
  exact isSL2ModOdd_of_mulEquiv hF e

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
theorem isSL2ModOdd_sec19Y [IsSimpleGroup G] (hstar : C19_11aTmp p f) {K : Subgroup G} {z : G}
    {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) :
    sec19Y K z = oddCoreOf (sec19Y K z) ⊔ ((S : Subgroup G) ⊓ sec19Y K z) ∨
      ∃ m : ℕ, IsSL2ModOdd (sec19Y K z) m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have := normal_subgroupOf_sec19X hd
  obtain ⟨hD, h8⟩ := hasDihedralSylowTwo_sec19X_quot hstar hDT hQ
  obtain ⟨hNidx, hNn, hNY⟩ := index_map_sup_sec19Y hd
  have hYX : sec19Y K z ≤ sec19X K z := sec19Y_le_sec19X K z
  have hzY : z ∈ sec19Y K z := S1916.sd_mem_Y hd
  have hzP : z ∈ (S : Subgroup G) ⊓ sec19Y K z := ⟨S1916.sd_mem_S hd, hzY⟩
  have hSY : (S : Subgroup G) ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
    hd.hSz.trans (centralizer_le_normalizer_sec19Y hd.tight)
  have hP := isSylow2In_inf_of_le_normalizer S hSY
  set Q := ↥(sec19X K z) ⧸ K.subgroupOf (sec19X K z) with hQdef
  set π := QuotientGroup.mk' (K.subgroupOf (sec19X K z)) with hπ
  have : (pPrimeCore 2 Q).Normal := pPrimeCore_normal
  set ρ₀ : ↥(sec19Y K z) →* Q ⧸ pPrimeCore 2 Q :=
    (QuotientGroup.mk' (pPrimeCore 2 Q)).comp (π.comp (Subgroup.inclusion hYX)) with hρ₀
  have hker : ∀ y : ↥(sec19Y K z), ρ₀ y = 1 ↔ (y : G) ∈ oddCoreOf (sec19Y K z) ⊔
      Subgroup.zpowers z := ker_sec19Y_quot hd hQ
  have hrange : ρ₀.range = (((K ⊔ sec19Y K z).subgroupOf (sec19X K z)).map π).map
      (QuotientGroup.mk' (pPrimeCore 2 Q)) := by
    rw [hρ₀, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range, hNY]
  rcases gw_index_two hD eq_top_of_normal_of_odd_index_sec19X_quot hNidx h8 with
    h2 | ⟨F, _, _, hF, ⟨eF⟩⟩
  ·
    left
    rw [← hrange] at h2
    have hP' : IsSylow2In (((S : Subgroup G) ⊓ sec19Y K z).subgroupOf (sec19Y K z)) ⊤ := by
      have := isSylow2In_subgroupOf_of_le hP le_rfl
      rwa [Subgroup.subgroupOf_self] at this
    have hPb := isSylow2In_map_hom ρ₀ hP'
    rw [← MonoidHom.range_eq_map] at hPb
    have heq := hPb.2.2 ρ₀.range le_rfl h2 hPb.1
    refine le_antisymm (fun y hy => ?_) (sup_le (oddCoreOf_le_self _) inf_le_right)
    have hmem : ρ₀ ⟨y, hy⟩ ∈ ρ₀.range := ⟨⟨y, hy⟩, rfl⟩
    rw [heq] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    have h1 : ρ₀ (x⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hker] at h1
    have hxP : (x : G) ∈ (S : Subgroup G) ⊓ sec19Y K z := Subgroup.mem_subgroupOf.mp hx
    have e : y = (x : G) * ((x⁻¹ * ⟨y, hy⟩ : ↥(sec19Y K z)) : G) := by simp
    rw [e]
    have hle : oddCoreOf (sec19Y K z) ⊔ Subgroup.zpowers z ≤
        oddCoreOf (sec19Y K z) ⊔ ((S : Subgroup G) ⊓ sec19Y K z) :=
      sup_le le_sup_left ((Subgroup.zpowers_le.mpr hzP).trans le_sup_right)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxP) (hle h1)
  ·
    right
    have hFc : ringChar F ≠ 2 :=
      ringChar_ne_two_of_odd_natCard F (odd_natCard_of_isOddPrimePower hF)
    let ψ : ↥(sec19Y K z) →* GorensteinWalter.PSL2 F :=
      eF.toMonoidHom.comp ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp ρ₀.rangeRestrict)
    have hψ : Function.Surjective ψ := eF.surjective.comp
      ((MulEquiv.subgroupCongr hrange).surjective.comp ρ₀.rangeRestrict_surjective)
    have hψ1 : ∀ y, ψ y = 1 ↔ ρ₀ y = 1 := by
      intro y
      change eF ((MulEquiv.subgroupCongr hrange) (ρ₀.rangeRestrict y)) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, Subtype.ext_iff]
      rfl
    have hzc : ∀ h ∈ sec19Y K z, h * z = z * h := fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (sec19Y_le_centralizer K z hh)
    exact ⟨Nat.card F, isSL2ModOdd_of_surjective hP hQ hzP hI.ne_one hI.sq hzc hFc ψ hψ
      fun y => (hψ1 y).trans (hker y)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
