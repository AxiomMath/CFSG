module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0L

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped commutatorElement MatrixGroups

theorem apply_mem_fusionZStar_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A}
    (ha : a ∈ Open.fusionZStar A) : e a ∈ Open.fusionZStar B := by
  rw [OddQuot.mem_fusionZStar_iff] at ha ⊢
  intro m
  have h1 := Subgroup.mem_map_of_mem e.toMonoidHom (ha (e.symm m))
  rw [pPrimeCore_map_iso 2 e] at h1
  have h2 : e.toMonoidHom ⁅a, e.symm m⁆ = ⁅e a, m⁆ := by
    rw [MulEquiv.coe_toMonoidHom, map_commutatorElement, MulEquiv.apply_symm_apply]
  rwa [h2] at h1

theorem map_fusionZStar_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Open.fusionZStar A).map e.toMonoidHom = Open.fusionZStar B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact apply_mem_fusionZStar_of_mulEquiv e ha
  · intro hb
    refine ⟨e.symm b, apply_mem_fusionZStar_of_mulEquiv e.symm hb, ?_⟩
    simp

theorem gs82HConfig_of_centralizer {X : Type} [Group X] [Finite X] {t : X} (ht : orderOf t = 2)
    {q : ℕ} {K R T : Subgroup ↥(centralizer ({t} : Set X))} {w : ↥(centralizer ({t} : Set X))}
    (hK : IsPComponent 2 K) (hR : IsPGroup 2 R) (hRK : R ≤ normalizer (K : Set _))
    (hTKR : T ≤ K ⊓ centralizer (R : Set _))
    (hT : IsPComponent 2 (T.subgroupOf (K ⊓ centralizer (R : Set _))))
    (hSL : HarrisLit.IsSLTwoOver q (↥T ⧸ pPrimeCore 2 ↥T)) (hw : orderOf w = 2) (hwT : w ∈ T)
    (hwK : w ∈ (Open.fusionZStar ↥K).map K.subtype) :
    GS82HConfig q t (K.map (centralizer ({t} : Set X)).subtype)
      (R.map (centralizer ({t} : Set X)).subtype) (T.map (centralizer ({t} : Set X)).subtype)
      (w : X) := by
  have hinj := (centralizer ({t} : Set X)).subtype_injective
  have hsub : ∀ A : Subgroup ↥(centralizer ({t} : Set X)),
      (A.map (centralizer ({t} : Set X)).subtype).subgroupOf (centralizer ({t} : Set X)) = A :=
    fun A => Subgroup.comap_map_eq_self_of_injective hinj A
  have hA : (K ⊓ centralizer (R : Set _)).map (centralizer ({t} : Set X)).subtype =
      K.map (centralizer ({t} : Set X)).subtype ⊓
        centralizer ((R.map (centralizer ({t} : Set X)).subtype : Subgroup X) : Set X) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyK, hyR⟩ := mem_inf.mp hy
      refine mem_inf.mpr ⟨⟨y, hyK, rfl⟩, ?_⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hyR r hr)
    · intro hx
      obtain ⟨⟨y, hyK, rfl⟩, hyR⟩ := mem_inf.mp hx
      refine ⟨y, mem_inf.mpr ⟨hyK, ?_⟩, rfl⟩
      rw [mem_centralizer_iff]
      intro r hr
      exact Subtype.ext (mem_centralizer_iff.mp hyR _ ⟨r, hr, rfl⟩)
  refine ⟨ht, map_subtype_le _, (hsub K).symm ▸ hK, hR.map _, map_subtype_le _,
    (map_mono hRK).trans (Subgroup.le_normalizer_map _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hA]
    exact map_mono hTKR
  ·
    let e := ((K ⊓ centralizer (R : Set _)).equivMapOfInjective
      (centralizer ({t} : Set X)).subtype hinj).trans (MulEquiv.subgroupCongr hA)
    have h1 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hT
    convert h1 using 1
    ext ⟨x, hx⟩
    constructor
    · intro h
      obtain ⟨y, hyT, rfl⟩ := mem_subgroupOf.mp h
      exact ⟨⟨y, hTKR hyT⟩, mem_subgroupOf.mpr hyT, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [mem_subgroupOf]
      have h3 : x = ((y : ↥(centralizer ({t} : Set X))) : X) :=
        (congrArg Subtype.val hyx).symm
      change x ∈ T.map (centralizer ({t} : Set X)).subtype
      rw [h3]
      exact ⟨y, mem_subgroupOf.mp hy, rfl⟩
  · exact HConfig.isSLTwoOver_of_mulEquiv
      (T.equivMapOfInjective (centralizer ({t} : Set X)).subtype hinj) hSL
  · rw [Subgroup.orderOf_coe]
    exact hw
  · exact ⟨w, hwT, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := hwK
    let eK := K.equivMapOfInjective (centralizer ({t} : Set X)).subtype hinj
    refine ⟨eK k, ?_, rfl⟩
    rw [← map_fusionZStar_of_mulEquiv eK]
    exact ⟨k, hk, rfl⟩

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  haveI := hperf
  have : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a' b']
  exact Group.IsPerfect.not_isSolvable Q

namespace Eight2

theorem CtxA0.orderOf_abz {X : Type} [Group X] [Finite X] (c : CtxA0 X) :
    orderOf (c.s.h.a * c.b * c.Z.z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : c.s.h.a * c.b * c.Z.z * (c.s.h.a * c.b * c.Z.z) = 1 := by
    calc c.s.h.a * c.b * c.Z.z * (c.s.h.a * c.b * c.Z.z)
        = c.s.h.a * c.b * (c.Z.z * (c.s.h.a * c.b)) * c.Z.z := by group
      _ = c.s.h.a * c.b * (c.s.h.a * c.b * c.Z.z) * c.Z.z := by rw [← c.ab_comm_z]
      _ = (c.s.h.a * c.b * (c.s.h.a * c.b)) * (c.Z.z * c.Z.z) := by group
      _ = 1 := by rw [c.ab_mul_ab, c.Z.hzz, one_mul]
  have hne : c.s.h.a * c.b * c.Z.z ≠ 1 := by
    intro h
    apply c.z_ne_ab
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right c.ab_mul_ab]
  exact orderOf_eq_prime (by rw [sq]; exact hsq) hne

end Eight2

end CFSG.ComponentClassification.GSThmB
