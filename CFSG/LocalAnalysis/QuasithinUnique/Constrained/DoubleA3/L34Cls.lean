module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34T
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_eq_six {Y : Subgroup G} {w : G} (hL : L27Aut ↥Y)
    (hwY : w ∈ normalizer (Y : Set G)) (hw2 : w * w = 1)
    (hout : ¬ ∃ k ∈ Y, ∀ y ∈ Y, w⁻¹ * y * w = k⁻¹ * y * k) :
    Nat.card ↥(Y ⊓ centralizerElem w) = 6 := by
  obtain ⟨β, hβ⟩ := exists_conjAut hwY
  have hβout : ¬ IsInner β := by
    rintro ⟨k, hk⟩
    apply hout
    refine ⟨((k⁻¹ : ↥Y) : G), (k⁻¹ : ↥Y).2, fun y hy => ?_⟩
    have h1 := congrArg Subtype.val (hk ⟨y, hy⟩)
    rw [hβ] at h1
    simpa using h1
  have hββ : ∀ y : ↥Y, β (β y) = y := by
    intro y
    apply Subtype.ext
    rw [hβ, hβ]
    have : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    rw [this]
    calc w * (w * (y : G) * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw2]; group
  have hβ2 : β * β = 1 := by
    ext y
    exact congrArg Subtype.val (hββ y)
  have hcard := hL.outer_fix_card β hβout hβ2
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun k => ⟨⟨k.1, k.2.1⟩, ?_⟩
      invFun := fun k => ⟨(k : ↥Y), (k : ↥Y).2, ?_⟩
      left_inv := fun k => rfl
      right_inv := fun k => rfl }
  · rw [mem_autFix]
    apply Subtype.ext
    rw [hβ]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp k.2.2
    calc w⁻¹ * k.1 * w = w⁻¹ * (k.1 * w) := by group
      _ = w⁻¹ * (w * k.1) := by rw [h1]
      _ = k.1 := by group
  · have hk := k.2
    rw [mem_autFix] at hk
    have h1 := congrArg Subtype.val hk
    rw [hβ] at h1
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc ((k : ↥Y) : G) * w = w * (w⁻¹ * ((k : ↥Y) : G) * w) := by group
      _ = w * ((k : ↥Y) : G) := by rw [h1]

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section Cls

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))

section NoF

include hD h27_1 hI hK hc

theorem A3A3K.involution_mem_conjClass_K
    {v : G} (hv : v ∈ K) (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    v ∈ conjClass z₂ := by
  have hd := hK.l2pData_K hD h27_1 hI hc
  have hz₁K := hK.z₁_mem_K
  have hz₁2 : z₁ * z₁ = 1 := by simpa [pow_two] using hK.sq₁
  have hz₁ord : orderOf (⟨z₁, hz₁K⟩ : ↥K) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hK.sq₁)) (fun h => hK.z₁_ne (congrArg Subtype.val h))
  have hvord : orderOf (⟨v, hv⟩ : ↥K) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hv2)) (fun h => hv1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := hd.single_class _ _ hz₁ord hvord
  have hk' : (k : G) * z₁ * (k : G)⁻¹ = v := congrArg Subtype.val hk
  refine ⟨s⁻¹ * (k : G)⁻¹, ?_⟩
  have hz₂ := hK.z₂_def
  calc v = (k : G) * z₁ * (k : G)⁻¹ := hk'.symm
    _ = (s⁻¹ * (k : G)⁻¹)⁻¹ * z₂ * (s⁻¹ * (k : G)⁻¹) := by rw [hz₂]; group

theorem A3A3K.involution_mem_conjClass_Ks
    {v : G} (hv : v ∈ conjR K s) (hv2 : v * v = 1)
    (hv1 : v ≠ 1) : v ∈ conjClass z₂ := by
  have hd := hK.l2pData_Ks hD h27_1 hI hc
  have hz₂K' : z₂ ∈ conjR K s := hK.z₂_mem_conjR
  have hz₂2 : z₂ * z₂ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₂
  have hz₂ord : orderOf (⟨z₂, hz₂K'⟩ : ↥(conjR K s)) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hK.toA3A3x.sq₂))
      (fun h => hK.toA3A3x.z₂_ne (congrArg Subtype.val h))
  have hvord : orderOf (⟨v, hv⟩ : ↥(conjR K s)) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hv2)) (fun h => hv1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := hd.single_class _ _ hz₂ord hvord
  have hk' : (k : G) * z₂ * (k : G)⁻¹ = v := congrArg Subtype.val hk
  refine ⟨(k : G)⁻¹, ?_⟩
  calc v = (k : G) * z₂ * (k : G)⁻¹ := hk'.symm
    _ = ((k : G)⁻¹)⁻¹ * z₂ * (k : G)⁻¹ := by group

theorem A3A3K.mixed_mem_conjClass_z
    {a b : G} (ha : a ∈ K) (hb : b ∈ conjR K s)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a * b ∈ conjClass (z₁ * z₂) := by
  have hd := hK.l2pData_K hD h27_1 hI hc
  have hd' := hK.l2pData_Ks hD h27_1 hI hc
  have hz₁K := hK.z₁_mem_K
  have hz₂K' : z₂ ∈ conjR K s := hK.z₂_mem_conjR
  have hz₁ord : orderOf (⟨z₁, hz₁K⟩ : ↥K) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hK.sq₁)) (fun h => hK.z₁_ne (congrArg Subtype.val h))
  have hz₂ord : orderOf (⟨z₂, hz₂K'⟩ : ↥(conjR K s)) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hK.toA3A3x.sq₂))
      (fun h => hK.toA3A3x.z₂_ne (congrArg Subtype.val h))
  have haord : orderOf (⟨a, ha⟩ : ↥K) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using ha2)) (fun h => ha1 (congrArg Subtype.val h))
  have hbord : orderOf (⟨b, hb⟩ : ↥(conjR K s)) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hb2)) (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := hd.single_class _ _ hz₁ord haord
  obtain ⟨k', hk'⟩ := hd'.single_class _ _ hz₂ord hbord
  have hka : (k : G) * z₁ * (k : G)⁻¹ = a := congrArg Subtype.val hk
  have hkb : (k' : G) * z₂ * (k' : G)⁻¹ = b := congrArg Subtype.val hk'
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjR K s, a * b = b * a := hK.comm_K_Ks hD h27_1 hI hc
  have h1 : z₁ * (k' : G) = (k' : G) * z₁ := hcomm z₁ hz₁K k' k'.2
  have h2 : (k : G)⁻¹ * ((k' : G) * z₂ * (k' : G)⁻¹) = ((k' : G) * z₂ * (k' : G)⁻¹) * (k : G)⁻¹ :=
    hcomm _ (K.inv_mem k.2) _ ((conjR K s).mul_mem ((conjR K s).mul_mem k'.2 hz₂K')
      ((conjR K s).inv_mem k'.2))
  refine ⟨((k : G) * k')⁻¹, ?_⟩
  calc a * b = (k : G) * z₁ * (k : G)⁻¹ * ((k' : G) * z₂ * (k' : G)⁻¹) := by rw [hka, hkb]
    _ = (k : G) * z₁ * ((k : G)⁻¹ * ((k' : G) * z₂ * (k' : G)⁻¹)) := by group
    _ = (k : G) * z₁ * (((k' : G) * z₂ * (k' : G)⁻¹) * (k : G)⁻¹) := by rw [h2]
    _ = (k : G) * (z₁ * (k' : G)) * z₂ * (k' : G)⁻¹ * (k : G)⁻¹ := by group
    _ = (k : G) * ((k' : G) * z₁) * z₂ * (k' : G)⁻¹ * (k : G)⁻¹ := by rw [h1]
    _ = ((k : G) * k')⁻¹⁻¹ * (z₁ * z₂) * ((k : G) * k')⁻¹ := by group

theorem A3A3K.mixed_not_mem_conjClass_z₂
    {a b : G} (ha : a ∈ K) (hb : b ∈ conjR K s)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a * b ∉ conjClass z₂ := by
  intro hmem
  apply hK.z_not_mem_conjClass hD h27_1
  obtain ⟨g, hg⟩ := hK.mixed_mem_conjClass_z hD h27_1 hI hc ha hb ha2 hb2 ha1 hb1
  have := conj_mem_conjClass hmem g⁻¹
  rw [hg] at this
  have e : g⁻¹⁻¹ * (g⁻¹ * (z₁ * z₂) * g) * g⁻¹ = z₁ * z₂ := by group
  rw [e] at this
  exact this

theorem A3A3K.exists_decomp_involution
    {u : G} (huN : u ∈ K ⊔ conjR K s) (hu2 : u * u = 1) :
    ∃ a ∈ K, ∃ b ∈ conjR K s, u = a * b ∧ a * a = 1 ∧ b * b = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute
    (hK.comm_K_Ks hD h27_1 hI hc) huN
  have hcomm := hK.comm_K_Ks hD h27_1 hI hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcomm]
      _ = (a * b) * (a * b) := by group
      _ = u * u := by rw [hab]
      _ = 1 := hu2
  have haa : a * a = 1 := by
    have hmem : a * a ∈ K ⊓ conjR K s :=
      ⟨K.mul_mem ha ha, by
        have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
        rw [this]
        exact (conjR K s).inv_mem ((conjR K s).mul_mem hb hb)⟩
    rwa [hK.inf_K_Ks hD h27_1 hI hc, Subgroup.mem_bot] at hmem
  have hbb : b * b = 1 := by rwa [haa, one_mul] at hsq
  exact ⟨a, ha, b, hb, hab, haa, hbb⟩

theorem A3A3K.involution_sup_cases
    {u : G} (huN : u ∈ K ⊔ conjR K s) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : u ∈ conjClass z₂ ∨ u ∈ conjClass (z₁ * z₂) := by
  obtain ⟨a, ha, b, hb, rfl, haa, hbb⟩ := hK.exists_decomp_involution hD h27_1 hI hc huN hu2
  by_cases ha1 : a = 1
  · left
    subst ha1
    rw [one_mul] at hu1 ⊢
    exact hK.involution_mem_conjClass_Ks hD h27_1 hI hc hb hbb hu1
  by_cases hb1 : b = 1
  · left
    subst hb1
    rw [mul_one] at hu1 ⊢
    exact hK.involution_mem_conjClass_K hD h27_1 hI hc ha haa ha1
  · right
    exact hK.mixed_mem_conjClass_z hD h27_1 hI hc ha hb haa hbb ha1 hb1

end NoF

section NoF2

include hD h27_1 hI hK hc

theorem A3A3K.not_inner_of_mem_xR
    {u : G} (hu : x⁻¹ * u ∈ baum S) :
    ¬ ∃ k ∈ K, ∀ y ∈ K, u⁻¹ * y * u = k⁻¹ * y * k := by
  rintro ⟨k, hkK, hk⟩
  have hrN := hK.baum_le_sup hD h27_1 hI hc hu
  obtain ⟨r₁, hr₁, r₂, hr₂, hr⟩ := exists_mul_of_mem_sup_of_commute
    (hK.comm_K_Ks hD h27_1 hI hc) hrN
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjR K s, a * b = b * a := hK.comm_K_Ks hD h27_1 hI hc
  have hux : u = x * (r₁ * r₂) := by rw [← hr]; group
  have hxK := hK.x_mem_normalizer_K
  apply hK.x_not_inner hD h27_1 hI hc
  refine ⟨k * r₁⁻¹, K.mul_mem hkK (K.inv_mem hr₁), fun y hy => ?_⟩
  have hv : x⁻¹ * y * x ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem hxK) y).mp hy
    simpa using this
  have hw : r₁⁻¹ * (x⁻¹ * y * x) * r₁ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hr₁) hv) hr₁
  have h2 : (r₁⁻¹ * (x⁻¹ * y * x) * r₁) * r₂ = r₂ * (r₁⁻¹ * (x⁻¹ * y * x) * r₁) :=
    hcomm _ hw r₂ hr₂
  have e1 : u⁻¹ * y * u = r₁⁻¹ * (x⁻¹ * y * x) * r₁ := by
    rw [hux]
    calc (x * (r₁ * r₂))⁻¹ * y * (x * (r₁ * r₂))
        = r₂⁻¹ * ((r₁⁻¹ * (x⁻¹ * y * x) * r₁) * r₂) := by group
      _ = r₂⁻¹ * (r₂ * (r₁⁻¹ * (x⁻¹ * y * x) * r₁)) := by rw [h2]
      _ = r₁⁻¹ * (x⁻¹ * y * x) * r₁ := by group
  calc x⁻¹ * y * x = r₁ * (r₁⁻¹ * (x⁻¹ * y * x) * r₁) * r₁⁻¹ := by group
    _ = r₁ * (k⁻¹ * y * k) * r₁⁻¹ := by rw [← e1, hk y hy]
    _ = (k * r₁⁻¹)⁻¹ * y * (k * r₁⁻¹) := by group

theorem A3A3K.not_inner_of_mem_xR_Ks
    {u : G} (hu : x⁻¹ * u ∈ baum S) :
    ¬ ∃ k ∈ conjR K s, ∀ y ∈ conjR K s, u⁻¹ * y * u = k⁻¹ * y * k := by
  rintro ⟨k, hkK, hk⟩
  have hrN := hK.baum_le_sup hD h27_1 hI hc hu
  obtain ⟨r₁, hr₁, r₂, hr₂, hr⟩ := exists_mul_of_mem_sup_of_commute
    (hK.comm_K_Ks hD h27_1 hI hc) hrN
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjR K s, a * b = b * a := hK.comm_K_Ks hD h27_1 hI hc
  have hux : u = x * (r₁ * r₂) := by rw [← hr]; group
  have hxK' := hK.x_mem_normalizer_Ks hD h27_1 hI hc
  apply hK.x_not_inner_Ks hD h27_1 hI hc
  refine ⟨k * r₂⁻¹, (conjR K s).mul_mem hkK ((conjR K s).inv_mem hr₂), fun y hy => ?_⟩
  have hv : x⁻¹ * y * x ∈ conjR K s := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((normalizer ((conjR K s : Subgroup G) : Set G)).inv_mem hxK') y).mp hy
    simpa using this
  have h2 : r₁ * (x⁻¹ * y * x) = (x⁻¹ * y * x) * r₁ := hcomm r₁ hr₁ _ hv
  have e1 : u⁻¹ * y * u = r₂⁻¹ * (x⁻¹ * y * x) * r₂ := by
    rw [hux]
    calc (x * (r₁ * r₂))⁻¹ * y * (x * (r₁ * r₂))
        = r₂⁻¹ * (r₁⁻¹ * (x⁻¹ * y * x) * r₁) * r₂ := by group
      _ = r₂⁻¹ * (r₁⁻¹ * ((x⁻¹ * y * x) * r₁)) * r₂ := by group
      _ = r₂⁻¹ * (r₁⁻¹ * (r₁ * (x⁻¹ * y * x))) * r₂ := by rw [← h2]
      _ = r₂⁻¹ * (x⁻¹ * y * x) * r₂ := by group
  calc x⁻¹ * y * x = r₂ * (r₂⁻¹ * (x⁻¹ * y * x) * r₂) * r₂⁻¹ := by group
    _ = r₂ * (k⁻¹ * y * k) * r₂⁻¹ := by rw [← e1, hk y hy]
    _ = (k * r₂⁻¹)⁻¹ * y * (k * r₂⁻¹) := by group

theorem A3A3K.mem_baum_or_xR
    {u : G} (huT : u ∈ T) (huK : u ∈ normalizer (K : Set G)) :
    u ∈ baum S ∨ x⁻¹ * u ∈ baum S := by
  have hcs := hK.cs
  obtain ⟨σ, hσS, hσ2, hσK⟩ := hK.exists_sigma hD h27_1 hI hc
  have hσT : σ ∈ T := hcs.le_T hσS
  have hKne : conjR K σ ≠ K := by
    rw [hσK]
    intro h
    have hbot := hK.inf_K_Ks hD h27_1 hI hc
    have hnt : K ≠ ⊥ := by
      intro h0
      have := hK.card_K_eq hD h27_1 hI hc
      rw [h0, Subgroup.card_bot] at this
      omega
    rw [h, inf_idem] at hbot
    exact hnt hbot
  have hσs : σ ∉ sOne S x := by
    intro h
    have : σ ∈ normalizer (K : Set G) := by
      have hsub : sOne S x ≤ normalizer (K : Set G) := by
        rw [sOne]
        exact sup_le (hK.baum_le_normalizer_K hD h27_1 hI hc)
          (Subgroup.zpowers_le.mpr hK.x_mem_normalizer_K)
      exact hsub h
    exact hKne (mem_normalizer_iff_conjR_eq.mp this)
  have hrel := A3A3x.relIndex_sOne hD h27_1 hK.toA3A3x
  have hB := basic31 hD h27_1 hK.toA3A3
  have hRx := hK.relIndex_baum_sOne hD h27_1
  have hxsO : x ∈ sOne S x := mem_sup_right (Subgroup.mem_zpowers x)
  have hxR : x ∉ baum S := fun h => hK.x_not_mem ((inf_le_left : baum S ≤ S) h)
  rcases mem_or_inv_mul_mem_of_relIndex_two hrel hσT hσs huT with h | h
  · exact mem_or_inv_mul_mem_of_relIndex_two hRx hxsO hxR h
  · exfalso
    have hsub : sOne S x ≤ normalizer (K : Set G) := by
      rw [sOne]
      exact sup_le (hK.baum_le_normalizer_K hD h27_1 hI hc)
        (Subgroup.zpowers_le.mpr hK.x_mem_normalizer_K)
    have h1 : σ⁻¹ * u ∈ normalizer (K : Set G) := hsub h
    have : σ ∈ normalizer (K : Set G) := by
      have := (normalizer (K : Set G)).mul_mem huK ((normalizer (K : Set G)).inv_mem h1)
      simpa using this
    exact hKne (mem_normalizer_iff_conjR_eq.mp this)

end NoF2

include hD h27_1 hI hK hc

theorem A3A3K.not_mem_conjClass_of_E9
    {u a₃ a₃' : G} (ha₃ : a₃ ∈ K) (ha₃' : a₃' ∈ conjR K s)
    (hu3 : a₃ ∈ centralizerElem u) (hu3' : a₃' ∈ centralizerElem u) (ho3 : orderOf a₃ = 3)
    (ho3' : orderOf a₃' = 3) : u ∉ conjClass z₂ := by
  rintro ⟨g, rfl⟩
  have hodd3 : Odd (orderOf a₃) := by rw [ho3]; decide
  have hodd3' : Odd (orderOf a₃') := by rw [ho3']; decide
  have h1 : a₃ ∈ conjR K g := hK.mem_conjR_K_of_odd hD h27_1 hI hc hu3 hodd3
  have h2 : a₃' ∈ conjR K g := hK.mem_conjR_K_of_odd hD h27_1 hI hc hu3' hodd3'
  have hcomm : a₃ * a₃' = a₃' * a₃ := hK.comm_K_Ks hD h27_1 hI hc a₃ ha₃ a₃' ha₃'
  have hinf : Subgroup.zpowers a₃ ⊓ Subgroup.zpowers a₃' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyK : y ∈ K := (Subgroup.zpowers_le.mpr ha₃) hy.1
    have hyK' : y ∈ conjR K s := (Subgroup.zpowers_le.mpr ha₃') hy.2
    have : y ∈ K ⊓ conjR K s := ⟨hyK, hyK'⟩
    rwa [hK.inf_K_Ks hD h27_1 hI hc] at this
  obtain ⟨A, hA, -, hA9⟩ := Id2519.exists_E9_of_commute ho3 ho3' hcomm hinf
  have hAle : A ≤ conjR K g := by
    rw [hA]
    exact sup_le (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)
  have hdvd : 9 ∣ Nat.card ↥(conjR K g) := hA9 ▸ Subgroup.card_dvd_of_le hAle
  rw [card_conjR, hK.card_K_eq hD h27_1 hI hc] at hdvd
  omega

theorem A3A3K.not_mem_conjClass_z₂_of_mem_xR
    {u : G} (hu2 : u * u = 1) (hu : x⁻¹ * u ∈ baum S) :
    u ∉ conjClass z₂ := by
  have hxK := hK.x_mem_normalizer_K
  have hxK' := hK.x_mem_normalizer_Ks hD h27_1 hI hc
  have huK : u ∈ normalizer (K : Set G) := by
    have := (normalizer (K : Set G)).mul_mem hxK (hK.baum_le_normalizer_K hD h27_1 hI hc hu)
    simpa using this
  have huK' : u ∈ normalizer ((conjR K s : Subgroup G) : Set G) := by
    have := (normalizer ((conjR K s : Subgroup G) : Set G)).mul_mem hxK'
      (hK.baum_le_normalizer_Ks hD h27_1 hI hc hu)
    simpa using this
  have hout := hK.not_inner_of_mem_xR hD h27_1 hI hc hu
  have hout' := hK.not_inner_of_mem_xR_Ks hD h27_1 hI hc hu
  have c6 := card_inf_centralizer_eq_six (hK.l27Aut_K hD h27_1 hI hc) huK hu2 hout
  have c6' := card_inf_centralizer_eq_six (hK.l27Aut_Ks hD h27_1 hI hc) huK' hu2 hout'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a₃, ha₃⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [c6]; norm_num : 3 ∣ Nat.card ↥(K ⊓ centralizerElem u))
  obtain ⟨a₃', ha₃'⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [c6']; norm_num : 3 ∣ Nat.card ↥(conjR K s ⊓ centralizerElem u))
  have ho3 : orderOf (a₃ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ha₃
  have ho3' : orderOf (a₃' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ha₃'
  exact hK.not_mem_conjClass_of_E9 hD h27_1 hI hc a₃.2.1 a₃'.2.1 a₃.2.2 a₃'.2.2 ho3 ho3'

theorem A3A3K.involution_conjR_mem_conjClass
    {g v : G} (hv : v ∈ conjR K g) (hv2 : v * v = 1)
    (hv1 : v ≠ 1) : v ∈ conjClass z₂ := by
  have hv' : g * v * g⁻¹ ∈ K := mem_conjR.mp hv
  have h2 : (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := by
    calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have h1 : g * v * g⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have := conj_mem_conjClass (hK.involution_mem_conjClass_K hD h27_1 hI hc hv' h2 h1) g
  have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
  rwa [e] at this

theorem A3A3K.false_of_swap_mem_conjClass
    {u : G} (hu2 : u * u = 1)
    (hsw : conjR K u = conjR K s) (hz : u ∈ conjClass z₂) : False := by
  obtain ⟨g, hg⟩ := hz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huu : ∀ y : G, u * (u * y * u) * u = y := fun y => by
    calc u * (u * y * u) * u = (u * u) * y * (u * u) := by group
      _ = y := by rw [hu2]; group
  have hKK' : ∀ y ∈ K, u * y * u ∈ conjR K s := by
    intro y hy
    rw [← hsw, mem_conjR, hui, huu]
    exact hy
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjR K s, a * b = b * a := hK.comm_K_Ks hD h27_1 hI hc
  let θ : ↥K →* G :=
    { toFun := fun a => (a : G) * (u * (a : G) * u)
      map_one' := by simpa using hu2
      map_mul' := fun a a' => by
        have h1 : (a' : G) * (u * (a : G) * u) = (u * (a : G) * u) * (a' : G) :=
          hcomm _ a'.2 _ (hKK' _ a.2)
        have e : u * ((a : G) * (a' : G)) * u = (u * (a : G) * u) * (u * (a' : G) * u) := by
          calc u * ((a : G) * (a' : G)) * u = u * (a : G) * (u * u) * (a' : G) * u := by
                rw [hu2]; group
            _ = (u * (a : G) * u) * (u * (a' : G) * u) := by group
        show ((a : G) * (a' : G)) * (u * ((a : G) * (a' : G)) * u) =
          ((a : G) * (u * (a : G) * u)) * ((a' : G) * (u * (a' : G) * u))
        calc ((a : G) * (a' : G)) * (u * ((a : G) * (a' : G)) * u)
            = (a : G) * ((a' : G) * (u * (a : G) * u)) * (u * (a' : G) * u) := by rw [e]; group
          _ = (a : G) * ((u * (a : G) * u) * (a' : G)) * (u * (a' : G) * u) := by rw [h1]
          _ = ((a : G) * (u * (a : G) * u)) * ((a' : G) * (u * (a' : G) * u)) := by group }
  have hθ : ∀ a : ↥K, θ a = (a : G) * (u * (a : G) * u) := fun a => rfl
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hθ] at ha
    have h1 : (a : G) = (u * (a : G) * u)⁻¹ := eq_inv_of_mul_eq_one_left ha
    have hmem : (a : G) ∈ K ⊓ conjR K s :=
      ⟨a.2, by rw [h1]; exact (conjR K s).inv_mem (hKK' _ a.2)⟩
    rw [hK.inf_K_Ks hD h27_1 hI hc, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  let D : Subgroup G := θ.range
  let eD : ↥K ≃* ↥D := MonoidHom.ofInjective hθinj
  have hDsimple : IsSimpleGroup ↥D := (MulEquiv.isSimpleGroup_congr eD).mp hK.isSimpleGroup
  have hDu : D ≤ centralizerElem u := by
    rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [hθ]
    have h1 : (a : G) * (u * (a : G) * u) = (u * (a : G) * u) * (a : G) :=
      hcomm _ a.2 _ (hKK' _ a.2)
    calc (a : G) * (u * (a : G) * u) * u = (a : G) * u * (a : G) * (u * u) := by group
      _ = u * (u * (a : G) * u * (a : G)) := by
          rw [hu2]
          calc (a : G) * u * (a : G) * 1 = (u * u) * (a : G) * u * (a : G) := by rw [hu2]; group
            _ = u * (u * (a : G) * u * (a : G)) := by group
      _ = u * ((a : G) * (u * (a : G) * u)) := by rw [← h1]
  have hDg : D ≤ conjR K g := by
    let H' : Subgroup ↥D := (conjR K g).subgroupOf D
    have hodd : ∀ d : ↥D, Odd (orderOf d) → d ∈ H' := by
      intro d hd
      have hdC : (d : G) ∈ centralizerElem (g⁻¹ * z₂ * g) := hg ▸ hDu d.2
      have hdo : Odd (orderOf (d : G)) := by rwa [Subgroup.orderOf_coe]
      exact hK.mem_conjR_K_of_odd hD h27_1 hI hc hdC hdo
    have hW : Subgroup.normalClosure {d : ↥D | Odd (orderOf d)} ≤ H' := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro b hb
      rw [Group.mem_conjugatesOfSet_iff] at hb
      obtain ⟨a, ha, hab⟩ := hb
      obtain ⟨c, hc'⟩ := isConj_iff.mp hab
      apply hodd
      have h1 := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
      have h2 : (MulAut.conj c).toMonoidHom a = b := by simpa using hc'
      rw [h2] at h1
      rw [h1]
      exact ha
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card K := by rw [hK.card_K_eq hD h27_1 hI hc]; norm_num
    obtain ⟨a₃, ha₃⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hd₃ : orderOf (eD a₃) = 3 := (orderOf_injective eD.toMonoidHom eD.injective a₃).trans ha₃
    have hne : Subgroup.normalClosure {d : ↥D | Odd (orderOf d)} ≠ ⊥ := by
      intro hbot
      have hmem : eD a₃ ∈ Subgroup.normalClosure {d : ↥D | Odd (orderOf d)} :=
        Subgroup.subset_normalClosure (by show Odd (orderOf (eD a₃)); rw [hd₃]; decide)
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : orderOf (eD a₃) = 1 := by rw [hmem]; exact orderOf_one
      omega
    have htop : Subgroup.normalClosure {d : ↥D | Odd (orderOf d)} = ⊤ :=
      (hDsimple.eq_bot_or_eq_top_of_normal _).resolve_left hne
    have hH' : H' = ⊤ := eq_top_iff.mpr (htop ▸ hW)
    intro d hd
    have : (⟨d, hd⟩ : ↥D) ∈ H' := by rw [hH']; exact Subgroup.mem_top _
    exact this
  have hz₁K := hK.z₁_mem_K
  have hz₁2 : z₁ * z₁ = 1 := by simpa [pow_two] using hK.sq₁
  have hbK' : u * z₁ * u ∈ conjR K s := hKK' z₁ hz₁K
  have hb2 : (u * z₁ * u) * (u * z₁ * u) = 1 := by
    calc (u * z₁ * u) * (u * z₁ * u) = u * z₁ * (u * u) * z₁ * u := by group
      _ = u * (z₁ * z₁) * u := by rw [hu2]; group
      _ = 1 := by rw [hz₁2]; simpa using hu2
  have hb1 : u * z₁ * u ≠ 1 := by
    intro h
    apply hK.z₁_ne
    calc z₁ = u * (u * z₁ * u) * u := (huu z₁).symm
      _ = 1 := by rw [h]; simpa using hu2
  have hd₀D : z₁ * (u * z₁ * u) ∈ D := ⟨⟨z₁, hz₁K⟩, rfl⟩
  have hd₀2 : (z₁ * (u * z₁ * u)) * (z₁ * (u * z₁ * u)) = 1 := by
    have h1 : z₁ * (u * z₁ * u) = (u * z₁ * u) * z₁ := hcomm z₁ hz₁K _ hbK'
    calc (z₁ * (u * z₁ * u)) * (z₁ * (u * z₁ * u))
        = z₁ * ((u * z₁ * u) * z₁) * (u * z₁ * u) := by group
      _ = z₁ * (z₁ * (u * z₁ * u)) * (u * z₁ * u) := by rw [h1]
      _ = (z₁ * z₁) * ((u * z₁ * u) * (u * z₁ * u)) := by group
      _ = 1 := by rw [hz₁2, hb2]; group
  have hd₀1 : z₁ * (u * z₁ * u) ≠ 1 := by
    intro h
    have h' : θ ⟨z₁, hz₁K⟩ = θ 1 := by rw [map_one]; exact h
    exact hK.z₁_ne (congrArg Subtype.val (hθinj h'))
  have hcl : z₁ * (u * z₁ * u) ∈ conjClass z₂ :=
    hK.involution_conjR_mem_conjClass hD h27_1 hI hc (hDg hd₀D) hd₀2 hd₀1
  exact hK.mixed_not_mem_conjClass_z₂ hD h27_1 hI hc hz₁K hbK' hz₁2 hb2 hK.z₁_ne hb1 hcl

theorem A3A3K.isComponentIn_sup
    : IsComponentIn K (K ⊔ conjR K s) := by
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK.K_comp
  refine ⟨le_sup_left, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ conjR K s)).symm hq
  · apply Subgroup.Normal.isSubnormal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer
      (C5.le_normalizer_of_commute fun b hb a ha =>
        (hK.comm_K_Ks hD h27_1 hI hc a ha b hb).symm)

theorem A3A3K.conjR_K_cases
    {r : G} (hr : r ∈ normalizer ((K ⊔ conjR K s : Subgroup G) : Set G)) :
    conjR K r = K ∨ conjR K r = conjR K s := by
  obtain ⟨σ, -, hσ2, hσK⟩ := hK.exists_sigma hD h27_1 hI hc
  have hσK' : CFSG.conjugate K σ = conjR K s := hσK
  have hA : IsComponentIn K (K ⊔ CFSG.conjugate K σ) := by
    rw [hσK']; exact hK.isComponentIn_sup hD h27_1 hI hc
  have hr' : r ∈ Subgroup.normalizer ((K ⊔ CFSG.conjugate K σ : Subgroup G) : Set G) := by
    rw [hσK']; exact hr
  rcases Id2519.conj_eq_or_conj_eq hσ2 hA hr' with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hσK')

theorem A3A3K.mem_K_or_Ks_of_conjClass
    {u : G} (huT : u ∈ T) (hu2 : u * u = 1)
    (hz : u ∈ conjClass z₂) : u ∈ K ∨ u ∈ conjR K s := by
  have hTN := hK.T_le_normalizer_sup hD h27_1 hI hc huT
  by_cases huN : u ∈ K ⊔ conjR K s
  · obtain ⟨a, ha, b, hb, rfl, haa, hbb⟩ := hK.exists_decomp_involution hD h27_1 hI hc huN hu2
    by_cases ha1 : a = 1
    · right; rw [ha1, one_mul]; exact hb
    by_cases hb1 : b = 1
    · left; rw [hb1, mul_one]; exact ha
    exact absurd hz (hK.mixed_not_mem_conjClass_z₂ hD h27_1 hI hc ha hb haa hbb ha1 hb1)
  · exfalso
    rcases hK.conjR_K_cases hD h27_1 hI hc hTN with h | h
    ·
      have huK : u ∈ normalizer (K : Set G) := mem_normalizer_iff_conjR_eq.mpr h
      rcases hK.mem_baum_or_xR hD h27_1 hI hc huT huK with hR | hxR
      · exact huN (hK.baum_le_sup hD h27_1 hI hc hR)
      · exact hK.not_mem_conjClass_z₂_of_mem_xR hD h27_1 hI hc hu2 hxR hz
    · exact hK.false_of_swap_mem_conjClass hD h27_1 hI hc hu2 h hz

end Cls

end Main

end CFSG.QuasithinUnique.DoubleA3
