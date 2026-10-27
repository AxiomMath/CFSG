module

public import CFSG.GH74.Generic.S1.RLevelECore
public import CFSG.GH74.Generic.S1.SymLayer

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem LayerData.eq_ι_of_involution {y : G} (D : LayerData y S) {t : G}
    (ht : t ∈ centralizer ({y} : Set G)) (ht2 : t * t = 1) (htK : proj y ⟨t, ht⟩ ∈ D.K) :
    t = D.ι (D.iso ⟨proj y ⟨t, ht⟩, htK⟩) := by
  set u : ↥(centralizer ({y} : Set G)) := ⟨t, ht⟩ with hu
  set k : ↥D.K := ⟨proj y u, htK⟩ with hk
  set s : ↥S := D.iso k with hs
  have hu2 : u * u = 1 := Subtype.ext ht2
  have hks : D.iso.symm s = k := D.iso.symm_apply_apply k
  have hπv : proj y (D.ιC s) = proj y u := by rw [D.proj_ιC s, hks]
  have hss : s * s = 1 := by
    have h1 : k * k = 1 := by
      apply Subtype.ext
      show proj y u * proj y u = 1
      rw [← map_mul, hu2, map_one]
    rw [hs, ← map_mul, h1, map_one]
  have hv2 : D.ιC s * D.ιC s = 1 := by rw [← map_mul, hss, map_one]
  have hLn : (liftL y D.K).Normal := liftL_normal
  have hc : u * D.ιC s = D.ιC s * u := by
    set c : ↥(centralizer ({y} : Set G)) := u * D.ιC s * u⁻¹ * (D.ιC s)⁻¹ with hcdef
    have hcL : c ∈ liftL y D.K :=
      (liftL y D.K).mul_mem (hLn.conj_mem _ (D.ιC_mem s) u) ((liftL y D.K).inv_mem (D.ιC_mem s))
    have hπc : proj y c = 1 := by
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hπv]
      group
    have h1 : c = 1 := D.exact c hcL hπc
    have h2 : ⁅u, D.ιC s⁆ = 1 := by rw [commutatorElement_def]; exact h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have heq : u = D.ιC s := eq_of_proj_eq hu2 hv2 hc hπv.symm
  exact congrArg Subtype.val heq

theorem exists_center_involution_of_layer {x : G} (hx : orderOf x = 2) (D : LayerData x S)
    (hxK : xbar x ∈ D.K) :
    ∃ s : ↥S, s ∈ Subgroup.center ↥S ∧ s * s = 1 ∧ s ≠ 1 ∧ D.ι s = x := by
  set k : ↥D.K := ⟨xbar x, hxK⟩ with hk
  refine ⟨D.iso k, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k', rfl⟩ := D.iso.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (xbar_comm x (k' : CentralizerBar x))
  · rw [← map_mul]
    have : k * k = 1 := Subtype.ext (xbar_mul_self hx)
    rw [this, map_one]
  · intro h
    have : k = 1 := D.iso.injective (by rw [h, map_one])
    exact xbar_ne_one hx (congrArg Subtype.val this)
  · have hxC : x ∈ centralizer ({x} : Set G) := (xH x).2
    have := LayerData.eq_ι_of_involution D hxC (by rw [← sq, ← hx]; exact pow_orderOf_eq_one x)
      (show proj x ⟨x, hxC⟩ ∈ D.K from hxK)
    exact this.symm

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ normalizer (A : Set G) → g' ∈ normalizer (B : Set G) →
      ∀ h ∈ A ⊔ B, g' * h * g'⁻¹ ∈ A ⊔ B := by
    intro g' hA' hB' h hh
    have hmap : (A ⊔ B).map (MulAut.conj g').toMonoidHom =
        A.map (MulAut.conj g').toMonoidHom ⊔ B.map (MulAut.conj g').toMonoidHom :=
      Subgroup.map_sup A B _
    have hle : (A ⊔ B).map (MulAut.conj g').toMonoidHom ≤ A ⊔ B := by
      rw [hmap]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (mem_normalizer_iff.1 hA' a).1 ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (mem_normalizer_iff.1 hB' b).1 hb
    exact hle ⟨h, hh, rfl⟩
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hA hB h, fun hh => ?_⟩
  have hA' : g⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hA
  have hB' : g⁻¹ ∈ normalizer (B : Set G) := (normalizer (B : Set G)).inv_mem hB
  have := key g⁻¹ hA' hB' _ hh
  simpa [mul_assoc] using this

theorem LayerData.mem_normalizer_range {y : G} (D : LayerData y S) {n : G}
    (hn : n ∈ centralizer ({y} : Set G)) : n ∈ normalizer (D.ι.range : Set G) := by
  have hLn : (liftL y D.K).Normal := liftL_normal
  have key : ∀ n' : G, n' ∈ centralizer ({y} : Set G) → ∀ m ∈ D.ι.range, n' * m * n'⁻¹ ∈ D.ι.range := by
    intro n' hn' m hm
    obtain ⟨s, rfl⟩ := hm
    set N : ↥(centralizer ({y} : Set G)) := ⟨n', hn'⟩ with hN
    have hmem : N * D.ιC s * N⁻¹ ∈ liftL y D.K := hLn.conj_mem _ (D.ιC_mem s) N
    obtain ⟨s', hs'⟩ := (D.liftIso.surjective ⟨_, hmem⟩)
    refine ⟨s', ?_⟩
    have h1 : D.ιC s' = N * D.ιC s * N⁻¹ := by
      have := congrArg (fun z : ↥(liftL y D.K) => (z : ↥(centralizer ({y} : Set G)))) hs'
      exact this
    have h2 := congrArg Subtype.val h1
    exact h2
  rw [mem_normalizer_iff]
  intro m
  refine ⟨key n hn m, fun hm => ?_⟩
  have hn' : n⁻¹ ∈ centralizer ({y} : Set G) := (centralizer ({y} : Set G)).inv_mem hn
  have := key n⁻¹ hn' _ hm
  simpa [mul_assoc] using this

theorem range_eq_sup_of_gen {y : G} (D : LayerData y S) {blk : Fin 4 → Fin 4 → Subgroup ↥S}
    {J1 J2 J3 : Subgroup G} (hJ1 : J1 = (blk 0 1).map D.ι) (hJ2 : J2 = (blk 1 2).map D.ι)
    (hJ3 : J3 = (blk 2 3).map D.ι) (hgen : blk 0 1 ⊔ blk 1 2 ⊔ blk 2 3 = ⊤) :
    D.ι.range = J1 ⊔ J2 ⊔ J3 := by
  rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, Subgroup.map_sup, hJ1, hJ2, hJ3]

omit [Finite G] in
theorem iSup_fin_four (J : Fin 4 → Subgroup G) : (⨆ i, J i : Subgroup G) = J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact sup_le (sup_le (sup_le (le_iSup J 0) (le_iSup J 1)) (le_iSup J 2)) (le_iSup J 3)


theorem LayerData.range_facts {y : G} (D : LayerData y S) {t : G} (ht : t ∈ D.ι.range) :
    ∃ h : t ∈ centralizer ({y} : Set G), proj y ⟨t, h⟩ ∈ D.K := by
  obtain ⟨s, rfl⟩ := ht
  refine ⟨D.ι_mem_cent s, ?_⟩
  have : proj y ⟨D.ι s, D.ι_mem_cent s⟩ = proj y (D.ιC s) := rfl
  rw [this, D.proj_ιC s]
  exact (D.iso.symm s).2

theorem proj_ne_xbar_of_ne {x : G} (hx : orderOf x = 2) {t : G} (ht : t ∈ centralizer ({x} : Set G))
    (ht2 : t * t = 1) (htx : t ≠ x) : barOf ht ≠ xbar x := by
  intro h
  apply htx
  have h1 := eq_of_proj_eq (u := ⟨t, ht⟩) (v := xH x) (Subtype.ext ht2) (xH_mul_self hx)
    (xH_central x _) (show proj x ⟨t, ht⟩ = proj x (xH x) from h)
  exact congrArg Subtype.val h1

theorem xy_facts {x : G} (hx : orderOf x = 2) (D : LayerData x S) (hxK : xbar x ∈ D.K)
    {blk : Fin 4 → Fin 4 → Subgroup ↥S} {J : Fin 4 → Subgroup G}
    (hJ1 : J 1 = (blk 0 1).map D.ι) (hJ2 : J 2 = (blk 1 2).map D.ι) (hJ3 : J 3 = (blk 2 3).map D.ι)
    (hneg : ∀ s z : ↥S, s ∈ Subgroup.center ↥S → s * s = 1 → s ≠ 1 → z ∈ blk 0 1 → z * z = 1 →
      z ≠ 1 → (∀ g ∈ blk 0 1, g * z = z * g) → s * z ∈ blk 2 3)
    (hcomm : ∀ g ∈ blk 0 1, ∀ h ∈ blk 2 3, g * h = h * g)
    {y : G} (hyJ : y ∈ J 1) (hy2 : orderOf y = 2) (hyc : ∀ a ∈ J 1, a * y = y * a)
    (hnoncomm : ¬ ∀ v ∈ J 2, v * y = y * v) :
    x * y ∈ J 3 ∧ orderOf (x * y) = 2 ∧ (∀ a ∈ J 3, a * (x * y) = (x * y) * a) := by
  obtain ⟨s, hsc, hs2, hs1, hsx⟩ := exists_center_involution_of_layer hx D hxK
  have hyJ' := hyJ
  rw [hJ1] at hyJ'
  obtain ⟨z, hz, hzy⟩ := hyJ'
  have hz2 : orderOf z = 2 := by rw [← orderOf_injective D.ι D.ι_injective z, hzy]; exact hy2
  have hzz : z * z = 1 := by rw [← sq, ← hz2]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzc : ∀ g ∈ blk 0 1, g * z = z * g := by
    intro g hg
    have hgJ : D.ι g ∈ J 1 := by rw [hJ1]; exact ⟨g, hg, rfl⟩
    have := hyc _ hgJ
    rw [← hzy, ← map_mul, ← map_mul] at this
    exact D.ι_injective this
  have hsz : s * z ∈ blk 2 3 := hneg s z hsc hs2 hs1 hz hzz hz1 hzc
  have hxy : x * y = D.ι (s * z) := by
    calc x * y = D.ι s * D.ι z := by rw [hsx, hzy]
      _ = D.ι (s * z) := (map_mul _ _ _).symm
  have hsc' : ∀ g : ↥S, g * s = s * g := fun g => (Subgroup.mem_center_iff.1 hsc g)
  have hyx : y ≠ x := by
    intro h
    apply hnoncomm
    intro v hv
    rw [hJ2] at hv
    obtain ⟨g, -, rfl⟩ := hv
    have h1 : D.ι g * D.ι s = D.ι s * D.ι g := by rw [← map_mul, ← map_mul, hsc' g]
    rw [hsx] at h1
    rw [h]
    exact h1
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  refine ⟨?_, ?_, ?_⟩
  · rw [hxy, hJ3]
    exact ⟨s * z, hsz, rfl⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [hxy, sq, ← map_mul]
      have : s * z * (s * z) = 1 := by
        calc s * z * (s * z) = s * (z * s) * z := by group
          _ = s * (s * z) * z := by rw [← hsc' z]
          _ = (s * s) * (z * z) := by group
          _ = 1 := by rw [hs2, hzz, one_mul]
      rw [this, map_one]
    · intro h
      apply hyx
      have : y = x⁻¹ := by
        have h' : x * y = 1 := h
        exact (eq_inv_of_mul_eq_one_right h')
      rw [this]
      exact inv_eq_of_mul_eq_one_right hxx
  · intro a ha
    rw [hJ3] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    rw [hxy, ← map_mul, ← map_mul]
    congr 1
    calc g * (s * z) = (g * s) * z := by group
      _ = (s * g) * z := by rw [hsc' g]
      _ = s * (g * z) := by group
      _ = s * (z * g) := by rw [← hcomm z hz g hg]
      _ = (s * z) * g := by group

theorem centralizer_xy_le_of_comp {x : G} (hx : orderOf x = 2) (D : LayerData x S) (hxK : xbar x ∈ D.K)
    {blk : Fin 4 → Fin 4 → Subgroup ↥S} {J : Fin 4 → Subgroup G}
    (hJ1 : J 1 = (blk 0 1).map D.ι) (hJ2 : J 2 = (blk 1 2).map D.ι) (hJ3 : J 3 = (blk 2 3).map D.ι)
    (hgen : blk 0 1 ⊔ blk 1 2 ⊔ blk 2 3 = ⊤)
    (hneg : ∀ s z : ↥S, s ∈ Subgroup.center ↥S → s * s = 1 → s ≠ 1 → z ∈ blk 0 1 → z * z = 1 →
      z ≠ 1 → (∀ g ∈ blk 0 1, g * z = z * g) → s * z ∈ blk 2 3)
    (hcomm : ∀ g ∈ blk 0 1, ∀ h ∈ blk 2 3, g * h = h * g)
    (hJcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ J i, ∀ b ∈ J j, a * b = b * a)
    (hfus : ∀ s t : G, s ∈ J 0 ⊔ J 1 → t ∈ J 0 ⊔ J 1 → orderOf s = 2 → orderOf t = 2 →
      ∃ g ∈ J 0 ⊔ J 1, g * s * g⁻¹ = t)
    (hL : ∀ c ∈ J 3, orderOf c = 2 → (∀ a ∈ J 3, a * c = c * a) →
      centralizer ({c} : Set G) ≤ normalizer ((J 0 ⊔ J 1 : Subgroup G) : Set G))
    {y : G} (hyJ : y ∈ J 1) (hy2 : orderOf y = 2) (hyc : ∀ a ∈ J 1, a * y = y * a)
    (hnoncomm : ¬ ∀ v ∈ J 2, v * y = y * v) :
    centralizer ({x * y} : Set G) ≤ normalizer ((⨆ i, J i : Subgroup G) : Set G) := by
  obtain ⟨hxyJ, hxy2, hxyc⟩ := xy_facts hx D hxK hJ1 hJ2 hJ3 hneg hcomm hyJ hy2 hyc hnoncomm
  have hLc := hL (x * y) hxyJ hxy2 hxyc
  have hM : D.ι.range = J 1 ⊔ J 2 ⊔ J 3 := range_eq_sup_of_gen D hJ1 hJ2 hJ3 hgen
  have hG₁ : (⨆ i, J i : Subgroup G) = (J 0 ⊔ J 1) ⊔ D.ι.range := by
    rw [iSup_fin_four, hM]
    apply le_antisymm
    · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · exact (le_sup_of_le_left le_sup_left : J 0 ≤ (J 0 ⊔ J 1) ⊔ (J 1 ⊔ J 2 ⊔ J 3))
      · exact (le_sup_of_le_left le_sup_right : J 1 ≤ (J 0 ⊔ J 1) ⊔ (J 1 ⊔ J 2 ⊔ J 3))
      · exact (le_sup_of_le_right (le_sup_of_le_left le_sup_right) :
          J 2 ≤ (J 0 ⊔ J 1) ⊔ (J 1 ⊔ J 2 ⊔ J 3))
      · exact (le_sup_of_le_right le_sup_right : J 3 ≤ (J 0 ⊔ J 1) ⊔ (J 1 ⊔ J 2 ⊔ J 3))
    · refine sup_le (sup_le ?_ ?_) (sup_le (sup_le ?_ ?_) ?_)
      · exact (le_sup_of_le_left (le_sup_of_le_left le_sup_left) : J 0 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
      · exact (le_sup_of_le_left (le_sup_of_le_left le_sup_right) : J 1 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
      · exact (le_sup_of_le_left (le_sup_of_le_left le_sup_right) : J 1 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
      · exact (le_sup_of_le_left le_sup_right : J 2 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
      · exact (le_sup_right : J 3 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  intro n hn
  have hnc : n * (x * y) = (x * y) * n := mem_centralizer_singleton_iff.1 hn
  have hnL : n ∈ normalizer ((J 0 ⊔ J 1 : Subgroup G) : Set G) := hLc hn
  have hyL : y ∈ J 0 ⊔ J 1 := (le_sup_right : J 1 ≤ J 0 ⊔ J 1) hyJ
  have htL : n * y * n⁻¹ ∈ J 0 ⊔ J 1 := (mem_normalizer_iff.1 hnL y).1 hyL
  have ht2 : orderOf (n * y * n⁻¹) = 2 := by
    rw [← hy2]
    exact (IsConj.orderOf_eq (isConj_iff.2 ⟨n, rfl⟩ : IsConj y (n * y * n⁻¹))).symm
  obtain ⟨l, hlL, hl⟩ := hfus y (n * y * n⁻¹) hyL htL hy2 ht2
  have hmy : l⁻¹ * n * y = y * (l⁻¹ * n) := by
    have h1 : n * y = l * y * l⁻¹ * n := by rw [hl]; group
    calc l⁻¹ * n * y = l⁻¹ * (n * y) := by group
      _ = l⁻¹ * (l * y * l⁻¹ * n) := by rw [h1]
      _ = y * (l⁻¹ * n) := by group
  have hlc : J 0 ⊔ J 1 ≤ centralizer ({x * y} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact mem_centralizer_singleton_iff.2 (hJcomm 0 3 (by decide) a ha _ hxyJ)
    · exact mem_centralizer_singleton_iff.2 (hJcomm 1 3 (by decide) a ha _ hxyJ)
  have hmc : l⁻¹ * n ∈ centralizer ({x * y} : Set G) :=
    (centralizer ({x * y} : Set G)).mul_mem ((centralizer ({x * y} : Set G)).inv_mem (hlc hlL)) hn
  have hmx : l⁻¹ * n ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hmc' : l⁻¹ * n * (x * y) = (x * y) * (l⁻¹ * n) := mem_centralizer_singleton_iff.1 hmc
    have hxe : x = (x * y) * y := by rw [mul_assoc, hyy, mul_one]
    calc l⁻¹ * n * x = l⁻¹ * n * ((x * y) * y) := by rw [← hxe]
      _ = (l⁻¹ * n * (x * y)) * y := by group
      _ = ((x * y) * (l⁻¹ * n)) * y := by rw [hmc']
      _ = (x * y) * (l⁻¹ * n * y) := by group
      _ = (x * y) * (y * (l⁻¹ * n)) := by rw [hmy]
      _ = ((x * y) * y) * (l⁻¹ * n) := by group
      _ = x * (l⁻¹ * n) := by rw [← hxe]
  have hmM : l⁻¹ * n ∈ normalizer (D.ι.range : Set G) := D.mem_normalizer_range hmx
  have hmL : l⁻¹ * n ∈ normalizer ((J 0 ⊔ J 1 : Subgroup G) : Set G) := hLc hmc
  have hmG : l⁻¹ * n ∈ normalizer ((⨆ i, J i : Subgroup G) : Set G) := by
    rw [hG₁]
    exact mem_normalizer_sup hmL hmM
  have hlG : l ∈ normalizer ((⨆ i, J i : Subgroup G) : Set G) :=
    le_normalizer (by rw [hG₁]; exact (le_sup_left : J 0 ⊔ J 1 ≤ (J 0 ⊔ J 1) ⊔ D.ι.range) hlL)
  have : n = l * (l⁻¹ * n) := by group
  rw [this]
  exact (normalizer ((⨆ i, J i : Subgroup G) : Set G)).mul_mem hlG hmG

theorem centralizer_y_le_of_comp {x : G} (hx : orderOf x = 2) (D : LayerData x S) (hxK : xbar x ∈ D.K)
    (hb5 : NoNoncentralInvolutionConj x D.K)
    {blk : Fin 4 → Fin 4 → Subgroup ↥S} {J : Fin 4 → Subgroup G}
    (hJ1 : J 1 = (blk 0 1).map D.ι) (hJ2 : J 2 = (blk 1 2).map D.ι) (hJ3 : J 3 = (blk 2 3).map D.ι)
    (hgen : blk 0 1 ⊔ blk 1 2 ⊔ blk 2 3 = ⊤)
    (hneg : ∀ s z : ↥S, s ∈ Subgroup.center ↥S → s * s = 1 → s ≠ 1 → z ∈ blk 0 1 → z * z = 1 →
      z ≠ 1 → (∀ g ∈ blk 0 1, g * z = z * g) → s * z ∈ blk 2 3)
    (hcomm : ∀ g ∈ blk 0 1, ∀ h ∈ blk 2 3, g * h = h * g)
    (hJcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ J i, ∀ b ∈ J j, a * b = b * a)
    (hfus : ∀ s t : G, s ∈ J 0 ⊔ J 1 → t ∈ J 0 ⊔ J 1 → orderOf s = 2 → orderOf t = 2 →
      ∃ g ∈ J 0 ⊔ J 1, g * s * g⁻¹ = t)
    (hL : ∀ c ∈ J 3, orderOf c = 2 → (∀ a ∈ J 3, a * c = c * a) →
      centralizer ({c} : Set G) ≤ normalizer ((J 0 ⊔ J 1 : Subgroup G) : Set G))
    (hab : ∃ a b : G, ∀ z ∈ (⨆ i, J i : Subgroup G), orderOf z = 2 →
      (∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = a) ∨
        ∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = b)
    {y : G} (hyJ : y ∈ J 1) (hy2 : orderOf y = 2) (hyc : ∀ a ∈ J 1, a * y = y * a)
    (hnoncomm : ¬ ∀ v ∈ J 2, v * y = y * v) :
    centralizer ({y} : Set G) ≤ normalizer ((⨆ i, J i : Subgroup G) : Set G) := by
  have h1 := centralizer_xy_le_of_comp hx D hxK hJ1 hJ2 hJ3 hgen hneg hcomm hJcomm hfus hL hyJ hy2 hyc
    hnoncomm
  obtain ⟨hxyJ, hxy2, -⟩ := xy_facts hx D hxK hJ1 hJ2 hJ3 hneg hcomm hyJ hy2 hyc hnoncomm
  obtain ⟨s, -, -, -, hsx⟩ := exists_center_involution_of_layer hx D hxK
  have hM : D.ι.range = J 1 ⊔ J 2 ⊔ J 3 := range_eq_sup_of_gen D hJ1 hJ2 hJ3 hgen
  have hxG₁ : x ∈ (⨆ i, J i : Subgroup G) := by
    have hxM : x ∈ D.ι.range := ⟨s, hsx⟩
    rw [hM] at hxM
    exact (sup_le (sup_le (le_iSup J 1) (le_iSup J 2)) (le_iSup J 3)) hxM
  have hyG₁ : y ∈ (⨆ i, J i : Subgroup G) := le_iSup J 1 hyJ
  have hxyG₁ : x * y ∈ (⨆ i, J i : Subgroup G) := (⨆ i, J i : Subgroup G).mul_mem hxG₁ hyG₁
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hJ2C : ∀ v ∈ J 2, v ∈ centralizer ({x} : Set G) := by
    intro v hv
    rw [hJ2] at hv
    obtain ⟨g, -, rfl⟩ := hv
    exact D.ι_mem_cent g
  have hyx : y ≠ x := by
    intro h
    apply hnoncomm
    intro v hv
    have := mem_centralizer_singleton_iff.1 (hJ2C v hv)
    rw [h]
    exact this
  have hyM : y ∈ D.ι.range := by
    rw [hM]
    exact (le_sup_of_le_left le_sup_left : J 1 ≤ J 1 ⊔ J 2 ⊔ J 3) hyJ
  have hxyM : x * y ∈ D.ι.range := by
    rw [hM]
    exact (le_sup_right : J 3 ≤ J 1 ⊔ J 2 ⊔ J 3) hxyJ
  obtain ⟨hyC, hyK⟩ := D.range_facts hyM
  obtain ⟨hxyC, hxyK⟩ := D.range_facts hxyM
  have hxy_nc : ¬ IsConj x y :=
    hb5 y hyC hyy hyK (proj_ne_xbar_of_ne hx hyC hyy hyx)
  have hxy1 : x * y ≠ x := by
    intro h
    apply hy1
    have := congrArg (fun z => x⁻¹ * z) h
    simpa using this
  have hxyy : (x * y) * (x * y) = 1 := by
    have hc : x * y = y * x := by
      have := mem_centralizer_singleton_iff.1 hyC
      exact this.symm
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  have hxxy_nc : ¬ IsConj x (x * y) :=
    hb5 (x * y) hxyC hxyy hxyK (proj_ne_xbar_of_ne hx hxyC hxyy hxy1)
  obtain ⟨a, b, hab'⟩ := hab
  have hcl := two_classes hxy_nc hab' hxG₁ hyG₁ hx hy2
  obtain ⟨g, hg, hcase⟩ := hcl (x * y) hxyG₁ hxy2
  rcases hcase with h | h
  · exfalso
    refine hxxy_nc (isConj_iff.2 ⟨g, ?_⟩)
    calc g * x * g⁻¹ = g * (g⁻¹ * (x * y) * g) * g⁻¹ := by rw [h]
      _ = x * y := by group
  · intro n hn
    have hnc : n * y = y * n := mem_centralizer_singleton_iff.1 hn
    have hxyg : x * y = g * y * g⁻¹ := by
      calc x * y = g * (g⁻¹ * (x * y) * g) * g⁻¹ := by group
        _ = g * y * g⁻¹ := by rw [h]
    have hm : g * n * g⁻¹ ∈ centralizer ({x * y} : Set G) := by
      rw [mem_centralizer_singleton_iff, hxyg]
      calc g * n * g⁻¹ * (g * y * g⁻¹) = g * (n * y) * g⁻¹ := by group
        _ = g * (y * n) * g⁻¹ := by rw [hnc]
        _ = g * y * g⁻¹ * (g * n * g⁻¹) := by group
    have hgn := h1 hm
    have hgN : g ∈ normalizer ((⨆ i, J i : Subgroup G) : Set G) := le_normalizer hg
    have : n = g⁻¹ * (g * n * g⁻¹) * g := by group
    rw [this]
    exact (normalizer ((⨆ i, J i : Subgroup G) : Set G)).mul_mem
      ((normalizer ((⨆ i, J i : Subgroup G) : Set G)).mul_mem
        ((normalizer ((⨆ i, J i : Subgroup G) : Set G)).inv_mem hgN) hgn) hgN

end CFSG.GH74.Generic.S1
