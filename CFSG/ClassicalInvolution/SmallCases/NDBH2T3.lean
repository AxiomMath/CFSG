module

public import CFSG.ClassicalInvolution.SmallCases.NDBH2T1
public import CFSG.ClassicalInvolution.SmallCases.NDBH2T2
public import CFSG.ClassicalInvolution.Asc77.AscT8RX
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.AschTight.S1916Omega
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3Main
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Final
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UTyp
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBH2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace HTri

variable {Ω : Set (Subgroup G)} {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
  {R₁ R₂ R₃ P : Subgroup G}

theorem comm (hT : HTri p f Ω K₁ K₂ K₃ z₁ z₂ z₃ R₁ R₂ R₃ P) (hz : IsClassicalMember p f K₁ z₁) :
    z₁ * z₂ = z₂ * z₁ := by
  have h1 : z₁ * z₁ = 1 := hz.isCentralInvolution.sq
  have h2 : z₂ * z₂ = 1 := hT.cls₂.isCentralInvolution.sq
  have h3 : z₁ * z₂ * (z₁ * z₂) = 1 := by
    rw [hT.prod]
    exact hT.cls₃.isCentralInvolution.sq
  symm
  calc z₂ * z₁ = z₂ * z₁ * (z₁ * z₂ * (z₁ * z₂)) := by rw [h3, mul_one]
    _ = z₂ * (z₁ * z₁) * z₂ * (z₁ * z₂) := by group
    _ = z₁ * z₂ := by rw [h1, mul_one, h2, one_mul]

theorem mul₂₁ (hT : HTri p f Ω K₁ K₂ K₃ z₁ z₂ z₃ R₁ R₂ R₃ P) (hz : IsClassicalMember p f K₁ z₁) :
    z₂ * z₁ = z₃ := by
  rw [← hT.comm hz, hT.prod]

theorem mul₁₃ (hT : HTri p f Ω K₁ K₂ K₃ z₁ z₂ z₃ R₁ R₂ R₃ P) (hz : IsClassicalMember p f K₁ z₁) :
    z₁ * z₃ = z₂ := by
  rw [← hT.prod, ← mul_assoc, hz.isCentralInvolution.sq, one_mul]

theorem mul₃₁ (hT : HTri p f Ω K₁ K₂ K₃ z₁ z₂ z₃ R₁ R₂ R₃ P) (hz : IsClassicalMember p f K₁ z₁) :
    z₃ * z₁ = z₂ := by
  rw [← hT.prod, mul_assoc, ← hT.comm hz, ← mul_assoc, hz.isCentralInvolution.sq, one_mul]

theorem ne₂₁ (hT : HTri p f Ω K₁ K₂ K₃ z₁ z₂ z₃ R₁ R₂ R₃ P) (hz : IsClassicalMember p f K₁ z₁) :
    z₂ ≠ z₁ := fun h => hT.cls₃.isCentralInvolution.ne_one (by
  rw [← hT.prod, h, hz.isCentralInvolution.sq])

theorem ne₃₁ (hT : HTri p f Ω K₁ K₂ K₃ z₁ z₂ z₃ R₁ R₂ R₃ P) (hz : IsClassicalMember p f K₁ z₁) :
    z₃ ≠ z₁ := fun h => hT.cls₂.isCentralInvolution.ne_one (by
  rw [← hT.mul₁₃ hz, h, hz.isCentralInvolution.sq])

theorem mem_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {M R : Subgroup G}
    {m : G} (hM : M ∈ Ω) (hm : IsClassicalMember p f M m) (hR : IsSylow2In R M) : m ∈ R :=
  T3.mem_of_isPGroup (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hm) hR.1 hR.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hM hR); omega)

end HTri

theorem eq_of_mem_RSet_of_le {K : Subgroup G} {z : G} (C : Asc77.XCtx p f (𝒞 K) z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) (hz : IsClassicalMember p f K z)
    (hnt : ¬ HasTwin p f K z) {K₂ K₃ : Subgroup G} {z₂ z₃ : G} {R₁ R₂ R₃ P : Subgroup G}
    (hT : HTri p f (𝒞 K) K K₂ K₃ z z₂ z₃ R₁ R₂ R₃ P) {S : Sylow 2 G}
    (hPS : P ≤ (S : Subgroup G)) {Q : Subgroup G} (hQ : Q ∈ RSet (𝒞 K))
    (hQS : Q ≤ (S : Subgroup G)) : Q = R₁ ∨ Q = R₂ ∨ Q = R₃ := by
  have hp := C.hp
  have hq := C.hq
  have hΩ := C.hΩ
  have hK : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz
  have hR₁Ω : R₁ ∈ RSet (𝒞 K) := mem_RSet_of_isSylow2In hK hT.syl₁
  have hR₁S : R₁ ≤ (S : Subgroup G) := hT.le₁.trans hPS
  by_contra hcon
  push Not at hcon
  obtain ⟨hQ₁, hQ₂, hQ₃⟩ := hcon
  obtain ⟨M, hM, hQM⟩ := exists_isSylow2In_of_mem_RSet hQ
  have hcomm : Commutes Q R₁ :=
    l6_7_proved p f hp hq G (𝒞 K) hΩ S Q hQ R₁ hR₁Ω hQS hR₁S hQ₁
  have hzR : z ∈ R₁ := HTri.mem_sylow hp hq hΩ hK hz hT.syl₁
  have hQc : Q ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have hMK : M ≠ K := by
    rintro rfl
    exact hQ₁ (T8R.eq_of_isSylow2In_of_le_sylow hQM hT.syl₁ hQS hR₁S)
  have hQN : Q ≤ Subgroup.normalizer (K : Set G) := hQc.trans
    (AscHypOmega.centralizer_le_normalizer_of_not_hasTwin hKz (not_hasTwin_unique hp hq hz hnt))
  have hMtq : M ∈ tqMembers (𝒞 K) z :=
    mem_tqMembers_of_mem_omegaNbr hp hq hΩ hK ⟨hM, hMK, Q, hQ, hQM.1, hQN⟩ hz
  obtain ⟨m, hm⟩ := hΩ.classical M hM
  have hmz : m ≠ z := by
    rintro rfl
    exact hnt ⟨M, hM, hMK, hm⟩
  have hmQ : m ∈ Q := HTri.mem_sylow hp hq hΩ hM hm hQM
  have hz₂R : z₂ ∈ R₂ := HTri.mem_sylow hp hq hΩ hT.mem₂ hT.cls₂ hT.syl₂
  rcases eq_or_eq_mul_of_mem C hnoF hall hMtq ⟨hT.mem₂, hT.tq₂₁⟩ hm hT.cls₂ hmz (hT.ne₂₁ hz)
      S.isPGroup' (hQS hmQ) (hT.le₂.trans hPS hz₂R) (hR₁S hzR) with e | e
  · rw [e] at hm
    rw [eq_of_isClassicalMember hp hq hz hnt hM hT.mem₂ hm hT.cls₂] at hQM
    exact hQ₂ (T8R.eq_of_isSylow2In_of_le_sylow hQM hT.syl₂ hQS (hT.le₂.trans hPS))
  · rw [e, hT.prod] at hm
    rw [eq_of_isClassicalMember hp hq hz hnt hM hT.mem₃ hm hT.cls₃] at hQM
    exact hQ₃ (T8R.eq_of_isSylow2In_of_le_sylow hQM hT.syl₃ hQS (hT.le₃.trans hPS))

theorem conj_mem_triangle {K : Subgroup G} {z : G} (C : Asc77.XCtx p f (𝒞 K) z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) (hz : IsClassicalMember p f K z)
    (hnt : ¬ HasTwin p f K z) {K₂ K₃ : Subgroup G} {z₂ z₃ : G} {R₁ R₂ R₃ P : Subgroup G}
    (hT : HTri p f (𝒞 K) K K₂ K₃ z z₂ z₃ R₁ R₂ R₃ P) {S : Sylow 2 G}
    (hPS : P ≤ (S : Subgroup G))
    (hc3 : ∀ x ∈ ({z, z₂, z₃} : Set G), ∀ L ∈ 𝒞 K, ∀ l : G, IsClassicalMember p f L l →
      l ≠ x → l * x = x * l → L ∈ tqMembers (𝒞 K) x)
    {h : G} (hbS : h * z * h⁻¹ ∈ (S : Subgroup G)) :
    h * z * h⁻¹ = z ∨ h * z * h⁻¹ = z₂ ∨ h * z * h⁻¹ = z₃ := by
  have hp := C.hp
  have hq := C.hq
  have hΩ := C.hΩ
  have hK : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  obtain ⟨b, hb⟩ : ∃ b, b = h * z * h⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hbS ⊢
  have hbcl : IsClassicalMember p f (conjSub h K) b := hb ▸ hz.conj h
  have hb2 : b * b = 1 := hbcl.isCentralInvolution.sq
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hU₁ := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz
  have hzR : z ∈ R₁ := HTri.mem_sylow hp hq hΩ hK hz hT.syl₁
  have hzS : z ∈ (S : Subgroup G) := hPS (hT.le₁ hzR)
  have hz₂S : z₂ ∈ (S : Subgroup G) :=
    hPS (hT.le₂ (HTri.mem_sylow hp hq hΩ hT.mem₂ hT.cls₂ hT.syl₂))
  have hz₃S : z₃ ∈ (S : Subgroup G) :=
    hPS (hT.le₃ (HTri.mem_sylow hp hq hΩ hT.mem₃ hT.cls₃ hT.syl₃))
  have hD1 : b * z * b⁻¹ = z ∨ b * z * b⁻¹ = z₂ ∨ b * z * b⁻¹ = z₃ := by
    have hR₁b : conjSub b R₁ ∈ RSet (𝒞 K) :=
      mem_RSet_of_isSylow2In ⟨b, rfl⟩ (Disconnected.AschTight.S1916.IsSylow2In.conj hT.syl₁ b)
    have hR₁bS : conjSub b R₁ ≤ (S : Subgroup G) :=
      (conjSub_mono (hT.le₁.trans hPS)).trans (conjSub_eq_self_of_mem hbS).le
    have hmem : b * z * b⁻¹ ∈ conjSub b R₁ := conj_mem_conjSub hzR
    have hsq : b * z * b⁻¹ * (b * z * b⁻¹) = 1 := by
      calc b * z * b⁻¹ * (b * z * b⁻¹) = b * (z * z) * b⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    have hne : b * z * b⁻¹ ≠ 1 := fun h1 => hU₁.ne_one (by
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel])
    rcases eq_of_mem_RSet_of_le C hnoF hall hz hnt hT hPS hR₁b hR₁bS with e | e | e <;>
      rw [e] at hmem
    · exact Or.inl ((hU₁.unique _ (hT.syl₁.1 hmem) hsq).resolve_left hne)
    · exact Or.inr (Or.inl
        (((ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hT.cls₂).unique _
          (hT.syl₂.1 hmem) hsq).resolve_left hne))
    · exact Or.inr (Or.inr
        (((ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hT.cls₃).unique _
          (hT.syl₃.1 hmem) hsq).resolve_left hne))
  have hconj : ∀ {x : G}, b * x * b⁻¹ = x → b * x = x * b := fun {x} e => by
    calc b * x = b * x * b⁻¹ * b := by group
      _ = x * b := by rw [e]
  have hback : ∀ {x y : G}, b * x * b⁻¹ = y → b * y * b⁻¹ = x := fun {x y} e => by
    rw [← e, hbinv]
    calc b * (b * x * b) * b = (b * b) * x * (b * b) := by group
      _ = x := by rw [hb2, one_mul, mul_one]
  have hmul : ∀ x y : G, b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := fun x y => by
    group
  obtain ⟨x, hx, hbx⟩ : ∃ x ∈ ({z, z₂, z₃} : Set G), b * x = x * b := by
    rcases hD1 with e | e | e
    · exact ⟨z, Or.inl rfl, hconj e⟩
    · refine ⟨z₃, Or.inr (Or.inr rfl), hconj ?_⟩
      rw [← hT.prod, hmul, e, hback e, ← hT.comm hz]
    · refine ⟨z₂, Or.inr (Or.inl rfl), hconj ?_⟩
      rw [← hT.mul₁₃ hz, hmul, e, hback e, hT.mul₃₁ hz, hT.mul₁₃ hz]
  by_cases hbx' : b = x
  · rcases hx with rfl | rfl | rfl
    · exact Or.inl hbx'
    · exact Or.inr (Or.inl hbx')
    · exact Or.inr (Or.inr hbx')
  have hLx := hc3 x hx (conjSub h K) ⟨h, rfl⟩ b hbcl hbx' hbx
  obtain ⟨g₂, hg₂⟩ := hT.mem₂
  obtain ⟨g₃, hg₃⟩ := hT.mem₃
  have hz₂g : z₂ = g₂ * z * g₂⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hT.cls₂).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hg₂ ▸ hz.conj g₂))
  have hz₃g : z₃ = g₃ * z * g₃⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hT.cls₃).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hg₃ ▸ hz.conj g₃))
  rcases hx with rfl | rfl | rfl
  · rcases eq_or_eq_mul_of_conj C hnoF hall (g := 1) (by group) hLx ⟨hT.mem₂, hT.tq₂₁⟩ hbcl
        hT.cls₂ hbx' (hT.ne₂₁ hz) S.isPGroup' hbS hz₂S hzS with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (e.trans hT.prod))
  · rcases eq_or_eq_mul_of_conj C hnoF hall hz₂g hLx ⟨hK, hT.tq₁₂⟩ hbcl hz hbx'
        (hT.ne₂₁ hz).symm S.isPGroup' hbS hzS hz₂S with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (e.trans (hT.mul₂₁ hz)))
  · rcases eq_or_eq_mul_of_conj C hnoF hall hz₃g hLx ⟨hK, hT.tq₁₃⟩ hbcl hz hbx'
        (hT.ne₃₁ hz).symm S.isPGroup' hbS hzS hz₃S with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl (e.trans (hT.mul₃₁ hz)))

end NDBH2

end CFSG.ClassicalInvolution.NDB
