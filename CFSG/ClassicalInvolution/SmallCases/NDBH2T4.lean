module

public import CFSG.ClassicalInvolution.SmallCases.NDBH2T3
public import CFSG.ClassicalInvolution.AschTight.StronglyClosed
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3120
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBH2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  CFSG.ClassicalInvolution.Asc77.ChainFrame.mem_closure_four ha hb hab hx

theorem false_of_hTri [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G}
    {z : G} (C : Asc77.XCtx p f (𝒞 K) z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) (hz : IsClassicalMember p f K z)
    (hnt : ¬ HasTwin p f K z) {K₂ K₃ : Subgroup G} {z₂ z₃ : G} {R₁ R₂ R₃ P : Subgroup G}
    (hT : HTri p f (𝒞 K) K K₂ K₃ z z₂ z₃ R₁ R₂ R₃ P)
    (hc3 : ∀ x ∈ ({z, z₂, z₃} : Set G), ∀ L ∈ 𝒞 K, ∀ l : G, IsClassicalMember p f L l →
      l ≠ x → l * x = x * l → L ∈ tqMembers (𝒞 K) x) : False := by
  have hp := C.hp
  have hq := C.hq
  have hΩ := C.hΩ
  have hK : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  obtain ⟨S, hPS⟩ := hT.two.exists_le_sylow
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hz₂2 : z₂ * z₂ = 1 := hT.cls₂.isCentralInvolution.sq
  have hcomm := hT.comm hz
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz
  have hzR : z ∈ R₁ := HTri.mem_sylow hp hq hΩ hK hz hT.syl₁
  have hzS : z ∈ (S : Subgroup G) := hPS (hT.le₁ hzR)
  have hz₂S : z₂ ∈ (S : Subgroup G) :=
    hPS (hT.le₂ (HTri.mem_sylow hp hq hΩ hT.mem₂ hT.cls₂ hT.syl₂))
  obtain ⟨g₂, hg₂⟩ := hT.mem₂
  obtain ⟨g₃, hg₃⟩ := hT.mem₃
  have hz₂g : z₂ = g₂ * z * g₂⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hT.cls₂).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hg₂ ▸ hz.conj g₂))
  have hz₃g : z₃ = g₃ * z * g₃⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hT.cls₃).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hg₃ ▸ hz.conj g₃))
  set E : Subgroup G := Subgroup.closure ({z, z₂} : Set G) with hE
  have hzE : z ∈ E := Subgroup.subset_closure (Set.mem_insert z _)
  have hz₂E : z₂ ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
  have hmemE : ∀ {y : G}, y = z ∨ y = z₂ ∨ y = z₃ → y ∈ E := by
    rintro y (rfl | rfl | rfl)
    · exact hzE
    · exact hz₂E
    · rw [← hT.prod]
      exact Subgroup.mul_mem _ hzE hz₂E
  have hES : E ≤ (S : Subgroup G) := (Subgroup.closure_le _).mpr (by
    rintro y (rfl | rfl)
    · exact hzS
    · exact hz₂S)
  have hEab : IsMulCommutative E := Subgroup.isMulCommutative_closure (by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [Commute.refl _, hcomm, hcomm.symm, Commute.refl _])
  have hcl : ∀ a ∈ E, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ E := by
    intro a ha g hg
    rcases mem_closure_pair hz2 hz₂2 hcomm ha with h | h | h | h <;> rw [h] at hg ⊢
    · rw [mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    · have e : g⁻¹ * z * g = g⁻¹ * z * g⁻¹⁻¹ := by rw [inv_inv]
      rw [e] at hg ⊢
      exact hmemE (conj_mem_triangle C hnoF hall hz hnt hT hPS hc3 hg)
    · have e : g⁻¹ * z₂ * g = (g⁻¹ * g₂) * z * (g⁻¹ * g₂)⁻¹ := by rw [hz₂g]; group
      rw [e] at hg ⊢
      exact hmemE (conj_mem_triangle C hnoF hall hz hnt hT hPS hc3 hg)
    · have e : g⁻¹ * (z * z₂) * g = (g⁻¹ * g₃) * z * (g⁻¹ * g₃)⁻¹ := by
        rw [hT.prod, hz₃g]; group
      rw [e] at hg ⊢
      exact hmemE (conj_mem_triangle C hnoF hall hz hnt hT hPS hc3 hg)
  have hR8 : 8 ≤ Nat.card R₁ := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hT.syl₁)
  have hRu : ∀ x ∈ R₁, ∀ y ∈ R₁, orderOf x = 2 → orderOf y = 2 → x = y := by
    have key : ∀ x ∈ R₁, orderOf x = 2 → x = z := fun x hx hx2 => by
      refine (hU.unique x (hT.syl₁.1 hx) ?_).resolve_left ?_
      · rw [← sq, ← hx2, pow_orderOf_eq_one]
      · rintro rfl
        rw [orderOf_one] at hx2
        omega
    intro x hx y hy hx2 hy2
    rw [key x hx hx2, key y hy hy2]
  have hbot := Disconnected.AschTight.eq_bot_of_stronglyClosed_of_abelian hnab
    hz.orderOf_eq_two (RouteD.le_centralizer_of_isClassicalMember hz)
    (CoreAssembly.not_isSolvable_of_isClassicalMember hz) hT.syl₁.2.1 hR8 hRu hT.rank S hES
    hEab hcl
  rw [hbot] at hzE
  exact hU.ne_one (Subgroup.mem_bot.mp hzE)

end NDBH2

end CFSG.ClassicalInvolution.NDB
