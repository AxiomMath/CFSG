module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR9
import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng
public import CFSG.ClassicalInvolution.Asc77.AscFusionB

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
open scoped commutatorElement MatrixGroups Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_order_four_comm (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z t : G}
    {R : Subgroup G} (hK : IsClassicalMember p f K z) (hR2 : IsPGroup 2 R)
    (hRK : IsSylow2In (R ⊓ K) K) (htR : t ∈ R) (htK : t ∈ Subgroup.normalizer (K : Set G))
    (ht2 : t * t = 1) (hnt : ¬ ∀ x ∈ K, ⁅t, x⁆ ∈ oddCoreOf K)
    (hin : ∃ k ∈ K, ∀ x ∈ K, t * x * t⁻¹ * (k * x * k⁻¹)⁻¹ ∈ oddCoreOf K) :
    ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  classical
  obtain ⟨φ, hφs, hφk⟩ := exists_chart_of_classical hK
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hodd
  have hzK : z ∈ K := hKz.mem
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htmem : ∀ x : G, x ∈ K → t * x * t⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htK x).mp hx
  let αt : ↥K → ↥K := fun x => ⟨t * x * t⁻¹, htmem x x.2⟩
  obtain ⟨k, hkK, hk⟩ := hin
  set s : SL(2, GaloisField p f) := φ ⟨k, hkK⟩ with hs
  have hαφ : ∀ x : ↥K, φ (αt x) = s * φ x * s⁻¹ := by
    intro x
    have hmem : t * (x : G) * t⁻¹ * (k * (x : G) * k⁻¹)⁻¹ ∈ oddCoreOf K := hk x x.2
    obtain ⟨hmemK, hmemO⟩ := mem_oddCoreOf_iff.mp hmem
    have e : (⟨t * (x : G) * t⁻¹ * (k * (x : G) * k⁻¹)⁻¹, hmemK⟩ : ↥K) =
        αt x * (⟨k, hkK⟩ * x * (⟨k, hkK⟩ : ↥K)⁻¹)⁻¹ := by
      apply Subtype.ext
      simp [αt]
    have h1 : φ (αt x * (⟨k, hkK⟩ * x * (⟨k, hkK⟩ : ↥K)⁻¹)⁻¹) = 1 := by
      rw [← e]
      exact (hφk _).mpr hmemO
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hαα : ∀ x : ↥K, αt (αt x) = x := by
    intro x
    apply Subtype.ext
    show t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    rw [hti]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; group
  have hcomm : ∀ g : SL(2, GaloisField p f), g * (s * s) = (s * s) * g := by
    intro g
    obtain ⟨x, rfl⟩ := hφs g
    have h1 := hαφ (αt x)
    rw [hαα, hαφ] at h1
    calc φ x * (s * s) = (s * (s * φ x * s⁻¹) * s⁻¹) * (s * s) := by rw [← h1]
      _ = s * s * φ x := by group
  have hcen : s * s ∈ Subgroup.center SL(2, GaloisField p f) := Subgroup.mem_center_iff.mpr hcomm
  have hss : s * s = 1 ∨ s * s = -1 := by
    obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    rw [Fintype.card_fin] at hr
    rcases sq_eq_one_iff.mp hr with h | h
    · left
      apply Subtype.ext
      rw [← hrs, h]
      simp
    · right
      apply Subtype.ext
      rw [← hrs, h]
      exact (CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix (GaloisField p f)).symm
  have hm1sq : (-1 : SL(2, GaloisField p f)) * (-1) = 1 := by
    have := CFSG.Semidihedral.OddFieldSL2.minusIdentity_square (GaloisField p f)
    rw [pow_two] at this
    exact this
  have hm1ne : (-1 : SL(2, GaloisField p f)) ≠ 1 :=
    CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one _ h2
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) := by
    refine isPGroup_zpowers_of_sq_sq ?_
    rcases hss with h | h
    · rw [h, one_mul]
    · rw [h, hm1sq]
  let Q' : Sylow 2 ↥K := AscL62.sylowOfIsSylow2In'' hRK
  let P : Sylow 2 SL(2, GaloisField p f) := Sylow.mapSurjective hφs Q'
  have hPeq : (P : Subgroup SL(2, GaloisField p f)) = (Q' : Subgroup ↥K).map φ :=
    Sylow.coe_mapSurjective hφs Q'
  have hQ'mem : ∀ x : ↥K, x ∈ (Q' : Subgroup ↥K) ↔ (x : G) ∈ R ⊓ K := fun x => Iff.rfl
  have hαQ : ∀ x : ↥K, x ∈ (Q' : Subgroup ↥K) → αt x ∈ (Q' : Subgroup ↥K) := by
    intro x hx
    rw [hQ'mem] at hx ⊢
    refine ⟨R.mul_mem (R.mul_mem htR hx.1) (R.inv_mem htR), (αt x).2⟩
  have hsN' : s ∈ Subgroup.normalizer ((P : Subgroup SL(2, GaloisField p f)) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hPeq] at hy ⊢
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨αt x, hαQ x hx, hαφ x⟩
    · intro hy
      rw [hPeq] at hy ⊢
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨αt x, hαQ x hx, ?_⟩
      have h1 := hαφ (αt x)
      rw [hαα] at h1
      have h2 : s * φ (αt x) * s⁻¹ = s * y * s⁻¹ := by rw [← h1, hxy]
      have h3 : φ (αt x) = y := by
        have := mul_right_cancel h2
        exact mul_left_cancel this
      exact h3
  have hsN : s ∈ Subgroup.normalizer (P : Set SL(2, GaloisField p f)) := hsN'
  have hsP : s ∈ (P : Subgroup SL(2, GaloisField p f)) := by
    have hmem : s ∈ Subgroup.zpowers s ⊓ Subgroup.normalizer (P : Set SL(2, GaloisField p f)) :=
      ⟨Subgroup.mem_zpowers s, hsN⟩
    rw [hs2.inf_normalizer_sylow P] at hmem
    exact hmem.2
  rw [hPeq] at hsP
  obtain ⟨q₀, hq₀, hq₀s⟩ := hsP
  have hq₀R : (q₀ : G) ∈ R := ((hQ'mem q₀).mp hq₀).1
  have hq₀K : (q₀ : G) ∈ K := q₀.2
  have hcomm₀ : t * (q₀ : G) = (q₀ : G) * t := by
    have h1 : φ (αt q₀) = φ q₀ := by
      rw [hαφ, hq₀s]
      group
    have h3 : αt q₀ * q₀⁻¹ ∈ classicalInvolutionOddCore ↥K := by
      apply (hφk _).mp
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h4 : t * (q₀ : G) * t⁻¹ * (q₀ : G)⁻¹ ∈ oddCoreOf K :=
      mem_oddCoreOf_iff.mpr ⟨K.mul_mem (αt q₀).2 (K.inv_mem hq₀K), h3⟩
    have h5 : t * (q₀ : G) * t⁻¹ * (q₀ : G)⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem htR hq₀R) (R.inv_mem htR)) (R.inv_mem hq₀R)
    have h6 : t * (q₀ : G) * t⁻¹ * (q₀ : G)⁻¹ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h4
        (hR2.to_le (Subgroup.zpowers_le.mpr h5))
    calc t * (q₀ : G) = (t * (q₀ : G) * t⁻¹ * (q₀ : G)⁻¹) * (q₀ : G) * t := by group
      _ = (q₀ : G) * t := by rw [h6]; group
  refine ⟨(q₀ : G), ⟨hq₀R, hq₀K⟩, ?_, hcomm₀⟩
  rcases hss with h | h
  ·
    exfalso
    apply hnt
    intro x hx
    have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right h
    have hsc : ∀ g : SL(2, GaloisField p f), g * s = s * g := by
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self _ h2 s hs1 with
        h' | h'
      · intro g
        rw [h', one_mul, mul_one]
      · intro g
        have := (Subgroup.mem_center_iff.mp
          (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center (GaloisField p f))) g
        rw [h']
        exact this
    have hφx : φ (αt ⟨x, hx⟩) = φ ⟨x, hx⟩ := by
      rw [hαφ]
      calc s * φ ⟨x, hx⟩ * s⁻¹ = φ ⟨x, hx⟩ * s * s⁻¹ := by rw [← hsc (φ ⟨x, hx⟩)]
        _ = φ ⟨x, hx⟩ := by group
    have h1 : αt ⟨x, hx⟩ * (⟨x, hx⟩ : ↥K)⁻¹ ∈ classicalInvolutionOddCore ↥K := by
      apply (hφk _).mp
      rw [map_mul, map_inv, hφx, mul_inv_cancel]
    have hmemK : ⁅t, x⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (htmem x hx) (K.inv_mem hx)
    refine mem_oddCoreOf_iff.mpr ⟨hmemK, ?_⟩
    have e : (⟨⁅t, x⁆, hmemK⟩ : ↥K) = αt ⟨x, hx⟩ * (⟨x, hx⟩ : ↥K)⁻¹ := by
      apply Subtype.ext
      simp [αt, commutatorElement_def]
    rw [e]
    exact h1
  ·
    have hq₀sq : φ q₀ * φ q₀ = -1 := by rw [hq₀s]; exact h
    have h4 : (q₀ * q₀) * (q₀ * q₀) ∈ classicalInvolutionOddCore ↥K := by
      apply (hφk _).mp
      rw [map_mul, map_mul, hq₀sq, hm1sq]
    have h4G : ((q₀ : G) * q₀) * ((q₀ : G) * q₀) ∈ oddCoreOf K :=
      mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.mul_mem hq₀K hq₀K) (K.mul_mem hq₀K hq₀K), h4⟩
    have h4R : ((q₀ : G) * q₀) * ((q₀ : G) * q₀) ∈ R :=
      R.mul_mem (R.mul_mem hq₀R hq₀R) (R.mul_mem hq₀R hq₀R)
    have h41 : ((q₀ : G) * q₀) * ((q₀ : G) * q₀) = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h4G
        (hR2.to_le (Subgroup.zpowers_le.mpr h4R))
    rcases hKz.unique ((q₀ : G) * q₀) (K.mul_mem hq₀K hq₀K) h41 with h5 | h5
    · exfalso
      have h6 : φ (q₀ * q₀) = 1 := by
        have : q₀ * q₀ = 1 := Subtype.ext h5
        rw [this, map_one]
      rw [map_mul, hq₀sq] at h6
      exact hm1ne h6
    · exact h5

omit [Finite G] in
theorem le_oddCoreOf_of_normal_odd {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M :=
  CFSG.ClassicalInvolution.Asc77.AscFusion.le_oddCoreOf_of_normal_odd_gen hNM hn hodd

theorem exists_classical_of_twin_pairs (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K K' : Subgroup G} {z : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hK' : K' ∈ CoreAssembly.conjClass K₀)
    (hKz : IsUniqueInvolution K z) (hK'z : IsUniqueInvolution K' z) (hne : K ≠ K')
    {a κ b κ' : G} (ha : a ∈ K) (hκ : κ ∈ K) (hb : b ∈ K') (hκ' : κ' ∈ K')
    (ha2 : a * a = z) (hb2 : b * b = z) (hab : a * b = b * a)
    (hκ2 : κ * κ = z) (hκ'2 : κ' * κ' = z) (hκκ' : κ * κ' = κ' * κ)
    {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K₀)
    (hJt : IsUniqueInvolution J (a * b)) :
    ∃ I ∈ CoreAssembly.conjClass K₀, IsUniqueInvolution I (κ * κ') := by
  classical
  have hKm : IsClassicalMember p f K z := isClassicalMember_of_mem_conjClass hp2 hq h₀ hK hKz
  have hK'm : IsClassicalMember p f K' z := isClassicalMember_of_mem_conjClass hp2 hq h₀ hK' hK'z
  obtain ⟨g, hgK, hg⟩ := exists_conj_in_member hp2 hq hKm hκ ha hκ2 ha2
  obtain ⟨g', hg'K', hg'⟩ := exists_conj_in_member hp2 hq hK'm hκ' hb hκ'2 hb2
  obtain ⟨hK'N, hKN', hcomm⟩ := twin_facts_general hq hp2 h₀ hK hK' hKz hK'z hne
  set M : Subgroup G := K ⊔ K' with hM
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  set N : Subgroup G := oddCoreOf M with hN
  have hMN : ∀ m ∈ M, m ∈ Subgroup.normalizer (N : Set G) := fun m hm =>
    mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
  have hOK : oddCoreOf K ≤ N := by
    refine le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self K).trans hKM) ?_ (oddCoreOf_odd_natCard K)
    refine sup_le ?_ ?_
    · exact fun m hm => mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
    · exact fun m hm => mem_normalizer_oddCoreOf_of_mem_normalizer' (hK'N hm)
  have hcN : ∀ u ∈ K, ∀ w ∈ K', ⁅u, w⁆ ∈ N := fun u hu w hw =>
    hOK (hcomm (Subgroup.commutator_mem_commutator hu hw)).1
  have hcN' : ∀ w ∈ K', ∀ u ∈ K, ⁅w, u⁆ ∈ N := fun w hw u hu => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hcN u hu w hw)
  set x : G := g * g' with hx
  set y : G := x * (κ * κ') * x⁻¹ with hy
  set c₁ : G := g' * κ * g'⁻¹ * κ⁻¹ with hc₁
  set c₂ : G := g * b * g⁻¹ * b⁻¹ with hc₂
  have hc₁N : c₁ ∈ N := by
    have : c₁ = ⁅g', κ⁆ := by rw [hc₁, commutatorElement_def]
    rw [this]
    exact hcN' g' hg'K' κ hκ
  have hc₂N : c₂ ∈ N := by
    have : c₂ = ⁅g, b⁆ := by rw [hc₂, commutatorElement_def]
    rw [this]
    exact hcN g hgK b hb
  have hgM : g ∈ M := hKM hgK
  have haM : a ∈ M := hKM ha
  have hbM : b ∈ M := hK'M hb
  have hy' : y = (g * c₁ * g⁻¹) * a * c₂ * b := by
    have e1 : g' * κ' * g'⁻¹ = b := hg'
    have e2 : g * κ * g⁻¹ = a := hg
    calc y = g * (g' * κ * g'⁻¹) * (g' * κ' * g'⁻¹) * g⁻¹ := by rw [hy, hx]; group
      _ = g * (c₁ * κ) * b * g⁻¹ := by
        rw [e1]
        congr 3
        rw [hc₁]
        group
      _ = (g * c₁ * g⁻¹) * (g * κ * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * c₁ * g⁻¹) * a * c₂ * b := by
        rw [e2]
        have : g * b * g⁻¹ = c₂ * b := by rw [hc₂]; group
        rw [this]
        group
  have hn1 : g * c₁ * g⁻¹ ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN g hgM) c₁).mp hc₁N
    exact this
  have hn2 : a⁻¹ * (g * c₁ * g⁻¹) * a ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN a⁻¹ (M.inv_mem haM)) (g * c₁ * g⁻¹)).mp hn1
    simpa using this
  have hn3 : b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN b⁻¹ (M.inv_mem hbM)) _).mp
      (N.mul_mem hn2 hc₂N)
    simpa using this
  have hxy : (a * b)⁻¹ * y ∈ N := by
    have : (a * b)⁻¹ * y = b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b := by
      rw [hy']
      group
    rw [this]
    exact hn3
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; exact hKz.sq
  have hδ2 : (κ * κ') * (κ * κ') = 1 := by
    calc (κ * κ') * (κ * κ') = κ * (κ' * κ) * κ' := by group
      _ = κ * (κ * κ') * κ' := by rw [← hκκ']
      _ = (κ * κ) * (κ' * κ') := by group
      _ = 1 := by rw [hκ2, hκ'2]; exact hKz.sq
  have hy2 : y * y = 1 := by
    calc y * y = x * ((κ * κ') * (κ * κ')) * x⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hδ2]; group
  have hxt : IsPGroup 2 (Subgroup.zpowers (a * b)) :=
    isPGroup_zpowers_of_sq_sq (by rw [hab2]; group)
  have hyt : IsPGroup 2 (Subgroup.zpowers y) :=
    isPGroup_zpowers_of_sq_sq (by rw [hy2]; group)
  obtain ⟨h, -, hh⟩ := exists_conj_of_odd_coset (oddCoreOf_odd_natCard M) hxt hyt
    (hMN (a * b) (M.mul_mem haM hbM)) hxy
  refine ⟨conjSub (x⁻¹ * h) J, conjSub_mem_conjClass hJ _, ?_⟩
  have := hJt.conj (x⁻¹ * h)
  have e : (x⁻¹ * h) * (a * b) * (x⁻¹ * h)⁻¹ = κ * κ' := by
    calc (x⁻¹ * h) * (a * b) * (x⁻¹ * h)⁻¹ = x⁻¹ * (h * (a * b) * h⁻¹) * x := by group
      _ = x⁻¹ * y * x := by rw [hh]
      _ = κ * κ' := by rw [hy]; group
  rwa [e] at this

omit [Finite G] in
theorem dual_delta_facts {z t a κ : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (ha2 : a * a = z)
    (hta : t * a = a * t) (hκ2 : κ * κ = t) (hκn : (a * a)⁻¹ * κ * (a * a) = κ⁻¹)
    (hκc : κ * (a⁻¹ * κ * a) = (a⁻¹ * κ * a) * κ) :
    ∃ δ : G, δ * δ = 1 ∧ z * δ = δ * z ∧ δ⁻¹ * a * δ = a * t := by
  set κ₂ : G := a⁻¹ * κ * a with hκ₂
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hza : a * z = z * a := by rw [← ha2]; group
  have hza' : a⁻¹ * z = z * a⁻¹ := by
    calc a⁻¹ * z = a⁻¹ * z * a * a⁻¹ := by group
      _ = a⁻¹ * (z * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * z) * a⁻¹ := by rw [hza]
      _ = z * a⁻¹ := by group
  have hata : a⁻¹ * t * a = t := by
    calc a⁻¹ * t * a = a⁻¹ * (t * a) := by group
      _ = a⁻¹ * (a * t) := by rw [hta]
      _ = t := by group
  have hκ₂2 : κ₂ * κ₂ = t := by
    calc κ₂ * κ₂ = a⁻¹ * (κ * κ) * a := by rw [hκ₂]; group
      _ = t := by rw [hκ2, hata]
  have hzκ : z * κ = κ⁻¹ * z := by
    have h := hκn
    rw [ha2, hzi] at h
    calc z * κ = (z * κ * z) * z⁻¹ := by group
      _ = κ⁻¹ * z⁻¹ := by rw [h]
      _ = κ⁻¹ * z := by rw [hzi]
  have hzκ₂ : z * κ₂ = κ₂⁻¹ * z := by
    calc z * κ₂ = (z * a⁻¹) * κ * a := by rw [hκ₂]; group
      _ = a⁻¹ * (z * κ) * a := by rw [← hza']; group
      _ = a⁻¹ * (κ⁻¹ * z) * a := by rw [hzκ]
      _ = a⁻¹ * κ⁻¹ * (z * a) := by group
      _ = a⁻¹ * κ⁻¹ * (a * z) := by rw [hza]
      _ = κ₂⁻¹ * z := by rw [hκ₂]; group
  refine ⟨κ * κ₂, ?_, ?_, ?_⟩
  · calc κ * κ₂ * (κ * κ₂) = κ * (κ₂ * κ) * κ₂ := by group
      _ = κ * (κ * κ₂) * κ₂ := by rw [← hκc]
      _ = (κ * κ) * (κ₂ * κ₂) := by group
      _ = 1 := by rw [hκ2, hκ₂2, ht2]
  · have hδ2 : κ * κ₂ * (κ * κ₂) = 1 := by
      calc κ * κ₂ * (κ * κ₂) = κ * (κ₂ * κ) * κ₂ := by group
        _ = κ * (κ * κ₂) * κ₂ := by rw [← hκc]
        _ = (κ * κ) * (κ₂ * κ₂) := by group
        _ = 1 := by rw [hκ2, hκ₂2, ht2]
    have hδi : (κ * κ₂)⁻¹ = κ * κ₂ := inv_eq_of_mul_eq_one_right hδ2
    calc z * (κ * κ₂) = (z * κ) * κ₂ := by group
      _ = κ⁻¹ * (z * κ₂) := by rw [hzκ]; group
      _ = κ⁻¹ * (κ₂⁻¹ * z) := by rw [hzκ₂]
      _ = (κ₂ * κ)⁻¹ * z := by group
      _ = (κ * κ₂)⁻¹ * z := by rw [← hκc]
      _ = (κ * κ₂) * z := by rw [hδi]
  · have hδ2 : κ * κ₂ * (κ * κ₂) = 1 := by
      calc κ * κ₂ * (κ * κ₂) = κ * (κ₂ * κ) * κ₂ := by group
        _ = κ * (κ * κ₂) * κ₂ := by rw [← hκc]
        _ = (κ * κ) * (κ₂ * κ₂) := by group
        _ = 1 := by rw [hκ2, hκ₂2, ht2]
    have hδi : (κ * κ₂)⁻¹ = κ * κ₂ := inv_eq_of_mul_eq_one_right hδ2
    have hκ₂a : a⁻¹ * κ₂ * a = κ⁻¹ := by
      have h := hκn
      rw [ha2] at h
      calc a⁻¹ * κ₂ * a = (a * a)⁻¹ * κ * (a * a) := by rw [hκ₂]; group
        _ = κ⁻¹ := hκn
    have h1 : a⁻¹ * (κ * κ₂) * a = (κ * κ₂) * t := by
      calc a⁻¹ * (κ * κ₂) * a = (a⁻¹ * κ * a) * (a⁻¹ * κ₂ * a) := by group
        _ = κ₂ * κ⁻¹ := by rw [← hκ₂, hκ₂a]
        _ = (κ₂ * κ) * (κ * κ)⁻¹ := by group
        _ = (κ * κ₂) * t := by rw [← hκc, hκ2, hti]
    have h2 : (κ * κ₂) * a = a * ((κ * κ₂) * t) := by
      calc (κ * κ₂) * a = a * (a⁻¹ * (κ * κ₂) * a) := by group
        _ = a * ((κ * κ₂) * t) := by rw [h1]
    have h3 : ((κ * κ₂)⁻¹ * a * (κ * κ₂)) * t = a := by
      calc ((κ * κ₂)⁻¹ * a * (κ * κ₂)) * t = (κ * κ₂)⁻¹ * (a * ((κ * κ₂) * t)) := by group
        _ = (κ * κ₂)⁻¹ * ((κ * κ₂) * a) := by rw [h2]
        _ = a := by group
    calc (κ * κ₂)⁻¹ * a * (κ * κ₂) = ((κ * κ₂)⁻¹ * a * (κ * κ₂)) * t * t⁻¹ := by group
      _ = a * t⁻¹ := by rw [h3]
      _ = a * t := by rw [hti]

theorem commutator_mem_oddCoreOf_of_product (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G}
    {z₀ : G} (h₀ : IsClassicalMember p f K₀ z₀) {K K₃ K' : Subgroup G} {z : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hK₃ : K₃ ∈ CoreAssembly.conjClass K₀)
    (hK' : K' ∈ CoreAssembly.conjClass K₀) (hKz : IsUniqueInvolution K z)
    (hK₃z : IsUniqueInvolution K₃ z) (hK'z : IsUniqueInvolution K' z) (hKK' : K ≠ K')
    (hK₃K' : K₃ ≠ K') {x y : G} (hx : x ∈ K) (hy : y ∈ K₃) :
    ∀ k ∈ K', ⁅x * y, k⁆ ∈ oddCoreOf K' := by
  intro k hk
  obtain ⟨-, hKN, hcomm⟩ := twin_facts_general hq hp2 h₀ hK hK' hKz hK'z hKK'
  obtain ⟨-, -, hcomm₃⟩ := twin_facts_general hq hp2 h₀ hK₃ hK' hK₃z hK'z hK₃K'
  have h1 : ⁅y, k⁆ ∈ oddCoreOf K' := (hcomm₃ (Subgroup.commutator_mem_commutator hy hk)).2
  have h2 : ⁅x, k⁆ ∈ oddCoreOf K' := (hcomm (Subgroup.commutator_mem_commutator hx hk)).2
  have h3 : x * ⁅y, k⁆ * x⁻¹ ∈ oddCoreOf K' :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (hKN hx) h1
  have e : ⁅x * y, k⁆ = (x * ⁅y, k⁆ * x⁻¹) * ⁅x, k⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreOf K').mul_mem h3 h2

end CFSG.ClassicalInvolution.Asc77.AscFusion
