module

public import CFSG.GH74.Generic.S1.RZD
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic

theorem x_mem_of_proj_eq {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hxK : xbar x ∈ K)
    (H : Subgroup ↥(centralizer ({x} : Set G))) (hproj : H.map (proj x) = K) : xH x ∈ H := by
  have hmem : xbar x ∈ H.map (proj x) := hproj ▸ hxK
  obtain ⟨h, hhH, hπ⟩ := hmem
  have ho : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨a, m, hm, hof⟩ := Nat.exists_eq_two_pow_mul_odd ho
  set h₂ := h ^ m with hh₂
  have hxx := xbar_mul_self hx
  have hπx : xbar x = proj x (xH x) := rfl
  have hπ₂ : proj x h₂ = xbar x := by
    rw [hh₂, map_pow, hπ]
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_succ, pow_mul, sq, hxx, one_pow, one_mul]
  have hh₂H : h₂ ∈ H := H.pow_mem hhH m
  have hord : h₂ ^ (2 ^ a) = 1 := by
    rw [hh₂, ← pow_mul, mul_comm, ← hof]
    exact pow_orderOf_eq_one h
  set r := (xH x)⁻¹ * h₂ with hr
  have hxH2 : xH x * xH x = 1 := xH_mul_self hx
  have hcomm : Commute h₂ (xH x) := (xH_central x h₂ : _)
  have hπr : proj x r = 1 := by
    rw [hr, map_mul, map_inv, hπ₂, ← hπx, inv_mul_cancel]
  have hrodd : Odd (orderOf r) := proj_odd x r hπr
  have hr2 : r ^ (2 ^ (a + 1)) = 1 := by
    have hc : Commute (xH x)⁻¹ h₂ := hcomm.symm.inv_left
    rw [hr, hc.mul_pow]
    have h1 : ((xH x)⁻¹) ^ (2 ^ (a + 1)) = 1 := by
      rw [inv_pow, pow_succ', pow_mul, sq, hxH2, one_pow, inv_one]
    have h2 : h₂ ^ (2 ^ (a + 1)) = 1 := by
      rw [pow_succ, pow_mul, hord, one_pow]
    rw [h1, h2, mul_one]
  have hord_r : orderOf r ∣ 2 ^ (a + 1) := orderOf_dvd_of_pow_eq_one hr2
  have hr1' : orderOf r = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord_r
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hi
    · exfalso
      have : 2 ∣ orderOf r := by
        rw [hi]
        exact dvd_pow_self 2 hi0.ne'
      exact (Nat.not_even_iff_odd.2 hrodd) (even_iff_two_dvd.2 this)
  have hr1 : r = 1 := orderOf_eq_one_iff.1 hr1'
  have h₂eq : h₂ = xH x := by
    rw [hr] at hr1
    exact (inv_mul_eq_one.1 hr1).symm
  rw [← h₂eq]
  exact hh₂H


theorem two_classes {G : Type} [Group G] {G₁ : Subgroup G} {a b x y : G} (hxy : ¬ IsConj x y)
    (hab : ∀ z ∈ G₁, orderOf z = 2 → (∃ g ∈ G₁, g⁻¹ * z * g = a) ∨ ∃ g ∈ G₁, g⁻¹ * z * g = b)
    (hx : x ∈ G₁) (hy : y ∈ G₁) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∀ z ∈ G₁, orderOf z = 2 → ∃ g ∈ G₁, g⁻¹ * z * g = x ∨ g⁻¹ * z * g = y := by
  have htrans : ∀ {u v w : G}, (∃ g ∈ G₁, g⁻¹ * u * g = v) → (∃ g ∈ G₁, g⁻¹ * v * g = w) →
      ∃ g ∈ G₁, g⁻¹ * u * g = w := by
    rintro u v w ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    refine ⟨g₁ * g₂, G₁.mul_mem hg₁ hg₂, ?_⟩
    rw [← h₂, ← h₁]
    group
  have hsymm : ∀ {u v : G}, (∃ g ∈ G₁, g⁻¹ * u * g = v) → ∃ g ∈ G₁, g⁻¹ * v * g = u := by
    rintro u v ⟨g, hg, h⟩
    refine ⟨g⁻¹, G₁.inv_mem hg, ?_⟩
    rw [← h]
    group
  have hconj : ∀ {u v : G}, (∃ g ∈ G₁, g⁻¹ * u * g = v) → IsConj u v := by
    rintro u v ⟨g, -, h⟩
    rw [isConj_iff]
    exact ⟨g⁻¹, by rw [← h]; group⟩
  intro z hz hz2
  rcases hab x hx hx2 with hxa | hxb <;> rcases hab y hy hy2 with hya | hyb
  · exact absurd (hconj (htrans hxa (hsymm hya))) hxy
  ·
    rcases hab z hz hz2 with hza | hzb
    · obtain ⟨g, hg, h⟩ := htrans hza (hsymm hxa)
      exact ⟨g, hg, Or.inl h⟩
    · obtain ⟨g, hg, h⟩ := htrans hzb (hsymm hyb)
      exact ⟨g, hg, Or.inr h⟩
  ·
    rcases hab z hz hz2 with hza | hzb
    · obtain ⟨g, hg, h⟩ := htrans hza (hsymm hya)
      exact ⟨g, hg, Or.inr h⟩
    · obtain ⟨g, hg, h⟩ := htrans hzb (hsymm hxb)
      exact ⟨g, hg, Or.inl h⟩
  · exact absurd (hconj (htrans hxb (hsymm hyb))) hxy


theorem card_le_of_index_le_two {X : Type} [Group X] [Finite X] (K T : Subgroup X)
    (hT : IsPGroup 2 T) (h : (K.subgroupOf T).index ≤ 2) :
    Nat.card T ≤ 2 * 2 ^ (Nat.card K).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : IsPGroup 2 ↥(K.subgroupOf T) := hT.to_subgroup _
  let ι : ↥(K.subgroupOf T) →* ↥K :=
    { toFun := fun n => ⟨(n : T).1, Subgroup.mem_subgroupOf.1 n.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : ↥K => (k : X)) hab
  have hP2 : IsPGroup 2 ↥ι.range := hN.of_equiv (MonoidHom.ofInjective hι)
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  have h1 : Nat.card ↥(K.subgroupOf T) = Nat.card ↥ι.range :=
    Nat.card_congr (MonoidHom.ofInjective hι).toEquiv
  have h2 : Nat.card ↥ι.range ≤ 2 ^ (Nat.card ↥K).factorization 2 :=
    (Subgroup.card_le_of_le hQ).trans (Sylow.card_eq_multiplicity Q).le
  have h3 := Subgroup.index_mul_card (K.subgroupOf T)
  calc Nat.card T = (K.subgroupOf T).index * Nat.card ↥(K.subgroupOf T) := h3.symm
    _ ≤ 2 * 2 ^ (Nat.card K).factorization 2 := by
      calc (K.subgroupOf T).index * Nat.card ↥(K.subgroupOf T)
          ≤ 2 * Nat.card ↥(K.subgroupOf T) := Nat.mul_le_mul_right _ h
        _ ≤ 2 * 2 ^ (Nat.card K).factorization 2 := by
          apply Nat.mul_le_mul_left
          rw [h1]
          exact h2


theorem odd_index_of_counts {G : Type} [Group G] [Finite G] (hG : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hfr : Q8Frame ↥K)
    (hOut : ∀ T : Subgroup (CentralizerBar x), IsPGroup 2 T → (K.subgroupOf T).index ≤ 2)
    (G₁ : Subgroup G) (hcnt : (Nat.card K).factorization 2 + 1 ≤ (Nat.card G₁).factorization 2) :
    Odd G₁.index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer ({x} : Set G))) := inferInstance
  obtain ⟨T, hTS, -, -, -⟩ := frame_sylow_centralizer_isSylow hG hx hfr S
  have hSG : Nat.card (S : Subgroup ↥(centralizer ({x} : Set G))) =
      2 ^ (Nat.card G).factorization 2 := by
    have h1 : Nat.card (T : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
      Sylow.card_eq_multiplicity T
    rw [hTS] at h1
    rw [← h1]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  let f : ↥(S : Subgroup ↥(centralizer ({x} : Set G))) →* CentralizerBar x :=
    (proj x).comp (S : Subgroup ↥(centralizer ({x} : Set G))).subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hπ : proj x (s : ↥(centralizer ({x} : Set G))) = 1 := hs
    have hmem : (s : ↥(centralizer ({x} : Set G))) ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) :=
      (QuotientGroup.eq_one_iff _).1 hπ
    exact Subtype.ext (eq_one_of_mem_sylow_of_mem_pPrimeCore S s.2 hmem)
  have hTbar2 : IsPGroup 2 ↥f.range := by
    have : IsPGroup 2 ↥(S : Subgroup ↥(centralizer ({x} : Set G))) := S.isPGroup'
    exact this.of_equiv (MonoidHom.ofInjective hfinj)
  have hcard1 : Nat.card ↥f.range = Nat.card (S : Subgroup ↥(centralizer ({x} : Set G))) :=
    (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hbound := card_le_of_index_le_two K f.range hTbar2 (hOut _ hTbar2)
  rw [hcard1, hSG] at hbound
  have hνG : (Nat.card G).factorization 2 ≤ (Nat.card K).factorization 2 + 1 := by
    have : 2 ^ (Nat.card G).factorization 2 ≤ 2 ^ ((Nat.card K).factorization 2 + 1) := by
      rw [pow_succ, mul_comm]
      exact hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hdvd : Nat.card G₁ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card G₁
  have hν₁ : (Nat.card G₁).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (Nat.card_pos).ne').2 hdvd 2
  have hmul := Subgroup.index_mul_card G₁
  have hfac : (Nat.card G).factorization 2 = G₁.index.factorization 2 + (Nat.card G₁).factorization 2 := by
    rw [← hmul, Nat.factorization_mul (Subgroup.index_ne_zero_of_finite) (Nat.card_pos).ne',
      Finsupp.add_apply]
  have h0 : G₁.index.factorization 2 = 0 := by omega
  rw [Nat.odd_iff]
  have hne : G₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_contra hev
  have h2 : 2 ∣ G₁.index := by omega
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hne h2
  omega


theorem eq_of_proj_eq {G : Type} [Group G] [Finite G] {x : G} {u v : ↥(centralizer ({x} : Set G))}
    (hu : u * u = 1) (hv : v * v = 1) (hc : u * v = v * u) (h : proj x u = proj x v) : u = v := by
  have hr : proj x (u⁻¹ * v) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have hrodd : Odd (orderOf (u⁻¹ * v)) := proj_odd x _ hr
  have hr2 : (u⁻¹ * v) ^ 2 = 1 := by
    have hc' : Commute u⁻¹ v := (show Commute u v from hc).inv_left
    rw [hc'.mul_pow, inv_pow, sq, sq, hu, hv, inv_one, one_mul]
  have hd : orderOf (u⁻¹ * v) ∣ 2 := orderOf_dvd_of_pow_eq_one hr2
  have h1 : orderOf (u⁻¹ * v) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h' | h'
    · exact h'
    · exfalso
      rw [h'] at hrodd
      exact absurd hrodd (by decide)
  have := orderOf_eq_one_iff.1 h1
  exact inv_mul_eq_one.1 this

theorem levelE_of_data
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hxK : xbar x ∈ K) (hfr : Q8Frame ↥K)
    (hB5 : NoNoncentralInvolutionConj x K)
    (hOut : ∀ T : Subgroup (CentralizerBar x), IsPGroup 2 T → (K.subgroupOf T).index ≤ 2)
    (J : Fin 4 → Subgroup G) (hJC : ∀ i : Fin 3, J i.succ ≤ centralizer ({x} : Set G))
    (hHK : (⨆ i : Fin 3, (J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) = K)
    (hperf : ⁅(⨆ i, J i : Subgroup G), (⨆ i, J i : Subgroup G)⁆ = (⨆ i, J i : Subgroup G))
    (hcnt : (Nat.card K).factorization 2 + 1 ≤ (Nat.card ↥(⨆ i, J i : Subgroup G)).factorization 2)
    (y : G) (hyJ : y ∈ J 1) (hy2 : orderOf y = 2) (hnoncomm : ¬ ∀ v ∈ J 2, v * y = y * v)
    (hnorm : ∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ Subgroup.closure {x, y} →
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer ((⨆ i, J i : Subgroup G) : Set G))
    (hab : ∃ a b : G, ∀ z ∈ (⨆ i, J i : Subgroup G), orderOf z = 2 →
      (∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = a) ∨
        ∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = b) :
    (⨆ i, J i : Subgroup G) = ⊤ := by
  classical
  have := hs
  set G₁ : Subgroup G := ⨆ i, J i with hG₁
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  set H' : Subgroup ↥C := ⨆ i : Fin 3, (J i.succ).subgroupOf C with hH'
  have hH'G : H'.map C.subtype ≤ G₁ := by
    rw [hH', Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hJC i)]
    exact le_iSup J i.succ
  have hxH : xH x ∈ H' := x_mem_of_proj_eq hx hxK H' hHK
  have hxG₁ : x ∈ G₁ := hH'G ⟨xH x, hxH, rfl⟩
  have hyG₁ : y ∈ G₁ := le_iSup J 1 hyJ
  have hyC : y ∈ C := hJC 0 hyJ
  have hyH : (⟨y, hyC⟩ : ↥C) ∈ H' := by
    have : (⟨y, hyC⟩ : ↥C) ∈ (J (0 : Fin 3).succ).subgroupOf C := hyJ
    exact le_iSup (fun i : Fin 3 => (J i.succ).subgroupOf C) 0 this
  have hbarK : barOf hyC ∈ K := by
    rw [← hHK]
    exact Subgroup.mem_map_of_mem _ hyH
  have hyx : y ≠ x := by
    intro h
    apply hnoncomm
    intro v hv
    have hvC : v ∈ C := hJC 1 hv
    have := Subgroup.mem_centralizer_iff.1 hvC y (by rw [h]; exact Set.mem_singleton x)
    exact this.symm
  have hbarne : barOf hyC ≠ xbar x := by
    intro h
    apply hyx
    have hu : (⟨y, hyC⟩ : ↥C) * ⟨y, hyC⟩ = 1 := Subtype.ext hyy
    have hv : xH x * xH x = 1 := xH_mul_self hx
    have hc : (⟨y, hyC⟩ : ↥C) * xH x = xH x * ⟨y, hyC⟩ := (xH_central x ⟨y, hyC⟩ : _)
    have := eq_of_proj_eq hu hv hc h
    exact congrArg Subtype.val this
  have hxy : ¬ IsConj x y := hB5 y hyC hyy hbarK hbarne
  obtain ⟨a, b, hab'⟩ := hab
  have hcl := two_classes hxy hab' hxG₁ hyG₁ hx hy2
  have hCx : centralizer ({x} : Set G) ≤ normalizer (G₁ : Set G) := by
    have h1 := hnorm (Subgroup.zpowers x) (by
        intro h
        apply hx1
        have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
        rw [h] at this
        exact this)
      ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp)))
    refine le_trans (fun g hg => ?_) h1
    rw [Subgroup.mem_normalizer_iff]
    have hgc : g * x = x * g := by
      have := Subgroup.mem_centralizer_iff.1 hg x (Set.mem_singleton x)
      exact this.symm
    have hconj : ∀ k : ℤ, g * x ^ k * g⁻¹ = x ^ k := fun k => by
      have hcomm : Commute g (x ^ k) := (show Commute g x from hgc).zpow_right k
      rw [hcomm.eq]; group
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [hconj k]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rw [← hk] at h1
      have hcomm : Commute g⁻¹ (x ^ k) := (show Commute g x from hgc).inv_left.zpow_right k
      rw [hcomm.eq, inv_mul_cancel_right] at h1
      rw [← h1]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have hCy : centralizer ({y} : Set G) ≤ normalizer (G₁ : Set G) := by
    have h1 := hnorm (Subgroup.zpowers y) (by
        intro h
        apply hy1
        have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
        rw [h] at this
        exact this)
      ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp)))
    refine le_trans (fun g hg => ?_) h1
    rw [Subgroup.mem_normalizer_iff]
    have hgc : g * y = y * g := by
      have := Subgroup.mem_centralizer_iff.1 hg y (Set.mem_singleton y)
      exact this.symm
    have hconj : ∀ k : ℤ, g * y ^ k * g⁻¹ = y ^ k := fun k => by
      have hcomm : Commute g (y ^ k) := (show Commute g y from hgc).zpow_right k
      rw [hcomm.eq]; group
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [hconj k]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rw [← hk] at h1
      have hcomm : Commute g⁻¹ (y ^ k) := (show Commute g y from hgc).inv_left.zpow_right k
      rw [hcomm.eq, inv_mul_cancel_right] at h1
      rw [← h1]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have hodd : Odd G₁.index := odd_index_of_counts hgen hx hfr hOut G₁ hcnt
  have hne : G₁ ≠ ⊥ := by
    intro h
    apply hy1
    have : y ∈ G₁ := hyG₁
    rw [h] at this
    exact this
  exact eq_top_of_zd hnab G₁ hperf hne hodd hxG₁ hyG₁ hx hy2 hxy hcl hCx hCy

end CFSG.GH74.Generic.S1
