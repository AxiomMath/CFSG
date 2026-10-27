module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

theorem isSylow_S_of_caseA (hSa : IsSylowIn h.S (centralizer ({h.a} : Set X)))
    (hN : normalizer (h.S : Set X) ≤ centralizer ({h.a} : Set X)) :
    ∃ R : Sylow 2 X, (R : Subgroup X) = h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV⟩ := hSa.isPGroup.exists_le_sylow
  refine ⟨V, ?_⟩
  by_contra hne
  have hlt : h.S.subgroupOf (V : Subgroup X) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun x hx => ?_) hV
    have : (⟨x, hx⟩ : ↥(V : Subgroup X)) ∈ h.S.subgroupOf (V : Subgroup X) := htop ▸ mem_top _
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent ↥(V : Subgroup X) := V.isPGroup'.isNilpotent
  obtain ⟨g, hgN, hgS⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hgN' : (g : X) ∈ normalizer (h.S : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := (mem_normalizer_iff.mp hgN ⟨x, hV hx⟩).mp (mem_subgroupOf.mpr hx)
      exact mem_subgroupOf.mp this
    · intro hx
      have hxV : x ∈ (V : Subgroup X) := by
        have := mul_mem (mul_mem (inv_mem g.2) (hV hx)) g.2
        rwa [show (g : X)⁻¹ * ((g : X) * x * (g : X)⁻¹) * g = x by group] at this
      have := (mem_normalizer_iff.mp hgN ⟨x, hxV⟩).mpr (mem_subgroupOf.mpr hx)
      exact mem_subgroupOf.mp this
  obtain ⟨hSC, R, hR⟩ := hSa
  have hW2 : IsPGroup 2 ↥((h.S ⊔ zpowers (g : X)).subgroupOf (centralizer ({h.a} : Set X))) :=
    (V.isPGroup'.to_le (sup_le hV (zpowers_le.mpr g.2))).comap_subtype
  have hle : (R : Subgroup ↥(centralizer ({h.a} : Set X))) ≤
      (h.S ⊔ zpowers (g : X)).subgroupOf (centralizer ({h.a} : Set X)) := by
    rw [hR]
    exact fun x hx => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))
  have heq := R.is_maximal' hW2 hle
  have hgC : (g : X) ∈ centralizer ({h.a} : Set X) := hN hgN'
  have hg : (⟨g, hgC⟩ : ↥(centralizer ({h.a} : Set X))) ∈
      (h.S ⊔ zpowers (g : X)).subgroupOf (centralizer ({h.a} : Set X)) :=
    mem_subgroupOf.mpr (mem_sup_right (mem_zpowers _))
  rw [heq, hR] at hg
  exact hgS (mem_subgroupOf.mpr (mem_subgroupOf.mp hg))

theorem not_conj_a_z (Z : ZData h) (hSa : IsSylowIn h.S (centralizer ({h.a} : Set X)))
    (hN : normalizer (h.S : Set X) ≤ centralizer ({h.a} : Set X)) (g : X) :
    g⁻¹ * h.a * g ≠ Z.z := by
  intro hg
  have hSz : h.S ≤ centralizer ({Z.z} : Set X) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (Z.hzS w hw)
  obtain ⟨g', hg'N, hg'⟩ := exists_normalizer_conj_of_sylow hSa hSz hg
  have hg'a := mem_centralizer_singleton_iff.mp (hN hg'N)
  have : g'⁻¹ * h.a * g' = h.a := by rw [mul_assoc, ← hg'a, inv_mul_cancel_left]
  rw [this] at hg'
  exact Z.hzP (hg' ▸ h.a_mem_P)

namespace Setting3

variable (s : Setting3 X)

theorem conj_z_mem_Dt (Z : ZData s.h) : s.t⁻¹ * Z.z * s.t ∈ s.Dt := by
  rw [mem_conjugate_iff, show s.t * (s.t⁻¹ * Z.z * s.t) * s.t⁻¹ = Z.z by group]
  exact Z.hzD

theorem center_Dt (Z : ZData s.h) {w : X} (hw : w ∈ s.Dt) (hwc : ∀ e ∈ s.Dt, w * e = e * w) :
    w = 1 ∨ w = s.t⁻¹ * Z.z * s.t := by
  rw [mem_conjugate_iff] at hw
  have hc : ∀ d ∈ s.h.D, s.t * w * s.t⁻¹ * d = d * (s.t * w * s.t⁻¹) := by
    intro d hd
    have hd' : s.t⁻¹ * d * s.t ∈ s.Dt := by
      rw [mem_conjugate_iff, show s.t * (s.t⁻¹ * d * s.t) * s.t⁻¹ = d by group]
      exact hd
    have h1 := hwc _ hd'
    calc s.t * w * s.t⁻¹ * d = s.t * (w * (s.t⁻¹ * d * s.t)) * s.t⁻¹ := by group
      _ = s.t * ((s.t⁻¹ * d * s.t) * w) * s.t⁻¹ := by rw [h1]
      _ = d * (s.t * w * s.t⁻¹) := by group
  rcases Z.hZDz _ hw hc with h1 | h1
  · left
    calc w = s.t⁻¹ * (s.t * w * s.t⁻¹) * s.t := by group
      _ = 1 := by rw [h1]; group
  · right
    calc w = s.t⁻¹ * (s.t * w * s.t⁻¹) * s.t := by group
      _ = s.t⁻¹ * Z.z * s.t := by rw [h1]

theorem exists_b (Z : ZData s.h) :
    ∃ b ∈ s.h.secB0 s.y, b * b = 1 ∧ s.t⁻¹ * Z.z * s.t = s.h.a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haG : s.h.a ∈ s.h.secSub s.y := s.secCond.a_mem_secSub
  have hzt := s.conj_z_mem_Dt Z
  have hztG : s.t⁻¹ * Z.z * s.t ∈ s.h.secSub s.y := s.Dt_le_secSub hzt
  have hinj := secQ_injOn s.isPGroup_Dt s.Dt_inf_B0
  have haD := (mem_inf.mp s.a_mem_Dt).1
  rw [← s.map_Dt_eq] at haD
  obtain ⟨e, he, hea⟩ := mem_map.mp haD
  have heD : (e : X) ∈ s.Dt := mem_subgroupOf.mp he
  have hec : ∀ f ∈ s.Dt, (e : X) * f = f * e := by
    intro f hf
    have hfG : f ∈ s.h.secSub s.y := s.Dt_le_secSub hf
    have h1 := s.a_central (s.h.subQ s.y ⟨f, hfG⟩) (by
      rw [← s.map_Dt_eq]
      exact mem_map_of_mem _ (show (⟨f, hfG⟩ : ↥(s.h.secSub s.y)) ∈ s.Dt.subgroupOf _ from hf))
    rw [← hea, ← map_mul, ← map_mul] at h1
    have h2 := hinj (mul_mem he (show (⟨f, hfG⟩ : ↥(s.h.secSub s.y)) ∈ s.Dt.subgroupOf _ from hf))
      (mul_mem (show (⟨f, hfG⟩ : ↥(s.h.secSub s.y)) ∈ s.Dt.subgroupOf _ from hf) he) h1
    exact congrArg Subtype.val h2
  have ha1 : s.sec.a ≠ 1 := by
    intro h1
    have h2 := s.sec.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have he1 : (e : X) ≠ 1 := by
    intro h1
    apply ha1
    rw [← hea, show e = 1 from Subtype.ext h1, map_one]
  have hez : (e : X) = s.t⁻¹ * Z.z * s.t := (s.center_Dt Z heD hec).resolve_left he1
  have h1 : s.h.subQ s.y ⟨s.t⁻¹ * Z.z * s.t, hztG⟩ = s.h.subQ s.y ⟨s.h.a, haG⟩ := by
    rw [← s.sec_a haG, ← hea]
    congr 1
    exact Subtype.ext hez.symm
  have hcomm : s.h.a * (s.t⁻¹ * Z.z * s.t) = s.t⁻¹ * Z.z * s.t * s.h.a :=
    (s.h.comm_a (s.Dt_le_S hzt)).symm
  have haa : s.h.a * s.h.a = 1 := Six.a_mul_a_self s.h
  have hzz : s.t⁻¹ * Z.z * s.t * (s.t⁻¹ * Z.z * s.t) = 1 := by
    rw [show s.t⁻¹ * Z.z * s.t * (s.t⁻¹ * Z.z * s.t) = s.t⁻¹ * (Z.z * Z.z) * s.t by group, Z.hzz]
    group
  set b := s.h.a * (s.t⁻¹ * Z.z * s.t) with hb
  have hbb : b * b = 1 := by
    calc b * b = s.h.a * ((s.t⁻¹ * Z.z * s.t) * s.h.a) * (s.t⁻¹ * Z.z * s.t) := by
          rw [hb]; group
      _ = s.h.a * (s.h.a * (s.t⁻¹ * Z.z * s.t)) * (s.t⁻¹ * Z.z * s.t) := by rw [← hcomm]
      _ = (s.h.a * s.h.a) * ((s.t⁻¹ * Z.z * s.t) * (s.t⁻¹ * Z.z * s.t)) := by group
      _ = 1 := by rw [haa, hzz, one_mul]
  have hbG : b ∈ s.h.secSub s.y := mul_mem haG hztG
  have hbθ : s.h.subQ s.y ⟨b, hbG⟩ = 1 := by
    have : (⟨b, hbG⟩ : ↥(s.h.secSub s.y)) = ⟨s.h.a, haG⟩ * ⟨s.t⁻¹ * Z.z * s.t, hztG⟩ := rfl
    rw [this, map_mul, h1, ← map_mul,
      show (⟨s.h.a, haG⟩ : ↥(s.h.secSub s.y)) * ⟨s.h.a, haG⟩ = 1 from Subtype.ext haa, map_one]
  have hbB := secQ_eq_one_of_two (w := ⟨b, hbG⟩) (k := 1) (by rw [pow_one, pow_two]; exact hbb)
    hbθ
  refine ⟨b, hbB, hbb, ?_⟩
  rw [hb, ← mul_assoc, haa, one_mul]

end Setting3

end Eight2

end CFSG.ComponentClassification.GSThmB
