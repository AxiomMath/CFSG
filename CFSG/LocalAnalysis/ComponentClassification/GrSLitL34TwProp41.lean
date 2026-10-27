module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWFus
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTBasic
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwBounds
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwCentA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTrans

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}
  {ρ : ↥(normalizer (W : Set G)) →* WrE}

theorem prop41
    (hMax : MaximalTwoComponentInput)
    (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) {y d : ↥(normalizer (W : Set G))}
    (hy2 : y * y = 1) (hyU : IsUU (ρ y)) (hya : (y : G) * a = a * (y : G))
    (hdT : (d : G) ∈ T) (hd2 : d * d = 1) (hdD : IsD (ρ d))
    (hdZ : ∀ z ∈ T, z * (d : G) = (d : G) * z) (g : G) : g⁻¹ * (y : G) * g ≠ (d : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hg
  have hTsyl := h.hTsyl
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM : T ≤ normalizer (W : Set G) := hTsyl.1
  have hker := hρ.ker_iff
  have haord : orderOf a = 2 := h.hset.2.1.1
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
    rwa [pow_two] at h2
  have hyg : (y : G) = g * (d : G) * g⁻¹ := by rw [← hg]; group
  have ha₁d : g⁻¹ * a * g * (d : G) = (d : G) * (g⁻¹ * a * g) := by
    rw [← hg]
    calc g⁻¹ * a * g * (g⁻¹ * (y : G) * g) = g⁻¹ * (a * (y : G)) * g := by group
      _ = g⁻¹ * ((y : G) * a) * g := by rw [hya]
      _ = g⁻¹ * (y : G) * g * (g⁻¹ * a * g) := by group
  have ha₁2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have ha₁1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    have : a = 1 := by
      have := congrArg (fun z => g * z * g⁻¹) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at haord
    exact absurd haord (by norm_num)
  have hV2 : IsPGroup 2 (zpowers (g⁻¹ * a * g)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha₁2) ha₁1
  have hSylC : IsSylowTwoIn T (centralizer ({(d : G)} : Set G)) :=
    GrS5S.isSylowTwoIn_centralizer hT2 (fun s hs => hdZ s hs) h.hTG
  have hVC : zpowers (g⁻¹ * a * g) ≤ centralizer ({(d : G)} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ha₁d)
  obtain ⟨c, hcC, hc⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn hSylC hVC hV2
  have hcd : c * (d : G) = (d : G) * c := mem_centralizer_singleton_iff.mp hcC
  have ha'T : c⁻¹ * (g⁻¹ * a * g) * c ∈ T := hc _ (mem_zpowers _)
  have ha'eq : c⁻¹ * (g⁻¹ * a * g) * c = (g * c)⁻¹ * a * (g * c) := by group
  rw [ha'eq] at ha'T
  set g' : G := g * c with hg'
  set a' : G := g'⁻¹ * a * g' with ha'
  have ha'M : a' ∈ normalizer (W : Set G) := hTM ha'T
  have ha'2 : a' * a' = 1 := by
    calc a' * a' = g'⁻¹ * (a * a) * g' := by simp only [ha']; group
      _ = 1 := by rw [ha2]; group
  have ha'1 : a' ≠ 1 := by
    intro h1
    have : a = 1 := by
      have := congrArg (fun z => g' * z * g'⁻¹) h1
      simpa [ha', mul_assoc] using this
    rw [this, orderOf_one] at haord
    exact absurd haord (by norm_num)
  have hyd : g' * (d : G) * g'⁻¹ = (y : G) := by
    rw [hyg, hg']
    calc g * c * (d : G) * (g * c)⁻¹ = g * (c * (d : G) * c⁻¹) * g⁻¹ := by group
      _ = g * (d : G) * g⁻¹ := by rw [hcd]; group
  let m' : ↥(normalizer (W : Set G)) := ⟨a', ha'M⟩
  have hm'2 : m' * m' = 1 := Subtype.ext ha'2
  have hm'T : (m' : G) ∈ T := ha'T
  have hm'X : ρ m' ∈ imgT T (normalizer (W : Set G)) ρ := mem_imgT_iff.mpr ⟨m', hm'T, rfl⟩
  have hρm'1 : ρ m' ≠ 1 := by
    intro h1
    have h2 : (m' : G) ∈ oddIn (normalizer (W : Set G)) := (hker m').mp h1
    have h3 : (m' : G) ∈ T ⊓ oddIn (normalizer (W : Set G)) := mem_inf.mpr ⟨hm'T, h2⟩
    rw [inf_oddIn_eq_bot_of_syl hTsyl, mem_bot] at h3
    exact ha'1 h3
  have hρm'2 : ρ m' * ρ m' = 1 := by rw [← map_mul, hm'2, map_one]
  rcases hC.inv_types _ hm'X hρm'2 hρm'1 with hA | hD | hU
  ·
    have hbig := hC.a_big _ hm'X hA
    set P0 : Subgroup G := T ⊓ centralizer ({a'} : Set G) with hP0
    have hcardP0 : 2 ^ 10 ≤ Nat.card ↥P0 := by
      refine le_trans hbig (Nat.card_le_card_of_surjective
        (fun z : ↥P0 => (⟨ρ ⟨z.1, hTM (mem_inf.mp z.2).1⟩, ?_⟩ :
          ↥(imgT T (normalizer (W : Set G)) ρ ⊓ centralizer ({ρ m'} : Set WrE)))) ?_)
      · refine mem_inf.mpr ⟨mem_imgT_iff.mpr ⟨_, (mem_inf.mp z.2).1, rfl⟩, ?_⟩
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp z.2).2)
      · rintro ⟨z, hz⟩
        obtain ⟨hzX, hzC⟩ := mem_inf.mp hz
        obtain ⟨m₂, hm₂T, rfl⟩ := mem_imgT_iff.mp hzX
        have hcomm : ρ (m₂ * m') = ρ (m' * m₂) := by
          rw [map_mul, map_mul]
          exact (mem_centralizer_singleton_iff.mp hzC)
        have hcomm' : m₂ * m' = m' * m₂ :=
          eq_of_rho_eq hTsyl hker (mul_mem hm₂T hm'T) (mul_mem hm'T hm₂T) hcomm
        refine ⟨⟨(m₂ : G), mem_inf.mpr ⟨hm₂T, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val hcomm')⟩⟩, ?_⟩
        rfl
    have hP2 : IsPGroup 2 (P0.map (MulAut.conj g').toMonoidHom) :=
      (hT2.to_le inf_le_left).map _
    have hPle : P0.map (MulAut.conj g').toMonoidHom ≤
        centralizer ({a} : Set G) ⊓ centralizer ({(y : G)} : Set G) := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hzT, hzC⟩ := mem_inf.mp hz
      have hza' : z * a' = a' * z := mem_centralizer_singleton_iff.mp hzC
      have hzd : z * (d : G) = (d : G) * z := hdZ z hzT
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
        mem_centralizer_singleton_iff.mpr ?_⟩
      · show g' * z * g'⁻¹ * a = a * (g' * z * g'⁻¹)
        have : a = g' * a' * g'⁻¹ := by simp only [ha']; group
        rw [this]
        calc g' * z * g'⁻¹ * (g' * a' * g'⁻¹) = g' * (z * a') * g'⁻¹ := by group
          _ = g' * (a' * z) * g'⁻¹ := by rw [hza']
          _ = g' * a' * g'⁻¹ * (g' * z * g'⁻¹) := by group
      · show g' * z * g'⁻¹ * (y : G) = (y : G) * (g' * z * g'⁻¹)
        rw [← hyd]
        calc g' * z * g'⁻¹ * (g' * (d : G) * g'⁻¹) = g' * (z * (d : G)) * g'⁻¹ := by group
          _ = g' * ((d : G) * z) * g'⁻¹ := by rw [hzd]
          _ = g' * (d : G) * g'⁻¹ * (g' * z * g'⁻¹) := by group
    have hcardP : Nat.card ↥(P0.map (MulAut.conj g').toMonoidHom) = Nat.card ↥P0 :=
      Subgroup.card_map_of_injective (MulAut.conj g').injective
    have hbound := (cent_bounds hMax h hρ hC hy2 hyU hya).1 _ hP2 hPle
    omega
  ·
    exact a_not_conj_d hMax h hρ hC hm'2 hD g' rfl
  ·
    obtain ⟨k, hk⟩ := invol_conj_of_type h hρ hm'2 hy2 (Or.inr (Or.inr ⟨hU, hyU⟩))
    have hk' : (k : G)⁻¹ * a' * k = (y : G) := congrArg Subtype.val hk
    refine a_not_conj_d hMax h hρ hC hd2 hdD (g' * (k : G) * g) ?_
    calc (g' * (k : G) * g)⁻¹ * a * (g' * (k : G) * g)
        = g⁻¹ * ((k : G)⁻¹ * (g'⁻¹ * a * g') * k) * g := by group
      _ = g⁻¹ * (y : G) * g := by rw [← ha', hk']
      _ = (d : G) := hg

end CFSG.ComponentClassification.GrSLit.L34Tw
