module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125CMt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E X : Subgroup G}

theorem sec125_X_le_CMt (F : Sec12Frame t L S) (hS : S ≤ centralizer ({t} : Set G))
    (hsup : X ⊔ secA t S L = (secM t S L ⊓ L) ⊔ S) : X ≤ secCMt t S L := by
  have h1 : (secM t S L ⊓ L) ⊔ S ≤ secCMt t S L := by
    refine sup_le ?_ ?_
    · intro y hy
      refine Subgroup.mem_inf.mpr ⟨hy.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact ((Subgroup.mem_centralizer_iff.mp F.htC) y hy.2).symm
    · intro s hs
      exact Subgroup.mem_inf.mpr ⟨F.hSM hs, hS hs⟩
  intro x hx
  have h2 : x ∈ X ⊔ secA t S L := Subgroup.mem_sup_left hx
  rw [hsup] at h2
  exact h1 h2

theorem sec125_cent_A (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) {y : G}
    (hyD : y ∈ centralizer (secV t S L E : Set G)) (hyt : y * t = t * y) :
    y ∈ centralizer (secA t S L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases h.mem_E.mp (sec120_A_le_E F hE ha) with hV | ⟨v, hv, rfl⟩
  · exact Subgroup.mem_centralizer_iff.mp hyD a hV
  · have hvy : v * y = y * v := Subgroup.mem_centralizer_iff.mp hyD v hv
    calc v * t * y = v * (t * y) := by group
      _ = v * (y * t) := by rw [hyt]
      _ = (v * y) * t := by group
      _ = (y * v) * t := by rw [hvy]
      _ = y * (v * t) := by group

theorem sec125_comm_t {x : G} (hx : x ∈ secCMt t S L) : x * t = t * x :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 t (Set.mem_singleton t)).symm

theorem sec125_X_inf_D (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) (hXC : X ≤ secCMt t S L)
    (hXA : X ⊓ centralizer (secA t S L : Set G) = ⊥) {x : G} (hx : x ∈ X)
    (hxD : x ∈ centralizer (secV t S L E : Set G)) : x = 1 := by
  have hxA := sec125_cent_A F hE h hxD (sec125_comm_t (hXC hx))
  have hmem : x ∈ X ⊓ centralizer (secA t S L : Set G) := Subgroup.mem_inf.mpr ⟨hx, hxA⟩
  rw [hXA] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem sec125_betaT_ne (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) (hXC : X ≤ secCMt t S L)
    (hXA : X ⊓ centralizer (secA t S L : Set G) = ⊥) {x : G} (hx : x ∈ X) :
    betaOf (secV t S L E) t ≠ betaOf (secV t S L E) x := by
  intro heq
  have hxN : x ∈ normalizer (secV t S L E : Set G) := sec125_CMt_le_N F hE (hXC hx)
  have hy : t⁻¹ * x ∈ centralizer (secV t S L E : Set G) :=
    (sec127_betaOf_eq_iff h.t_mem_normalizer hxN).mp heq
  have hxt : x * t = t * x := sec125_comm_t (hXC hx)
  have hyt : (t⁻¹ * x) * t = t * (t⁻¹ * x) := by
    have e1 : t⁻¹ * x * t = x := by
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
        _ = t⁻¹ * (t * x) := by rw [hxt]
        _ = x := by group
    have e2 : t * (t⁻¹ * x) = x := by group
    rw [e1, e2]
  have hyA := sec125_cent_A F hE h hy hyt
  have hxA : x ∈ centralizer (secA t S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hay : a * (t⁻¹ * x) = (t⁻¹ * x) * a := Subgroup.mem_centralizer_iff.mp hyA a ha
    have hat : a * t = t * a :=
      sec12E_A_comm F ha (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    calc a * x = (a * t) * (t⁻¹ * x) := by group
      _ = (t * a) * (t⁻¹ * x) := by rw [hat]
      _ = t * (a * (t⁻¹ * x)) := by group
      _ = t * ((t⁻¹ * x) * a) := by rw [hay]
      _ = x * a := by group
  have hx1 : x = 1 := by
    have hmem : x ∈ X ⊓ centralizer (secA t S L : Set G) := Subgroup.mem_inf.mpr ⟨hx, hxA⟩
    rw [hXA] at hmem
    exact Subgroup.mem_bot.mp hmem
  have ht1 : betaOf (secV t S L E) t = 1 := by rw [heq, hx1, sec127_betaOf_one]
  have htD := (sec127_betaOf_eq_one_iff h.t_mem_normalizer).mp ht1
  obtain ⟨v, hv, hne⟩ := h.nofix
  exact hne (Subgroup.mem_centralizer_iff.mp htD v hv).symm

theorem sec125_R_cent_E (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) {r : G}
    (hr : r ∈ secR t) : r ∈ centralizer (E : Set G) := by
  have hEM : E ≤ secM t S L := hE.1.trans inf_le_left
  have hRM : secR t ≤ secM t S L :=
    (sec12E_R_le_C F).trans fun x hx => Subgroup.centralizer_le_normalizer _ hx
  have hEn : (E.subgroupOf (secM t S L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEM]
    exact sec12E_sylow_normal F hE
  have hRn : ((secR t).subgroupOf (secM t S L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRM]
    intro r m hr hm
    exact sec12E_R_normal F hm hr
  have hcomm := commute_of_normal_two_odd hEM hRM hEn hRn hE.2.1 (odd_card_oddCoreIn _)
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact hcomm e he r hr

theorem sec125_beta_decomp (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) (hXC : X ≤ secCMt t S L)
    (hXaut : autIn X (secA t S L) = autIn (secCMt t S L) (secA t S L)) {g : G}
    (hg : g ∈ secCMt t S L) :
    ∃ x ∈ X, betaOf (secV t S L E) g = betaOf (secV t S L E) x ∨
      betaOf (secV t S L E) g = betaOf (secV t S L E) x * betaOf (secV t S L E) t := by
  have hgM : g ∈ normalizer (secA t S L : Set G) := (Subgroup.mem_inf.mp hg).1
  have hmem : (secA t S L).normalizerMonoidHom ⟨g, hgM⟩ ∈
      autIn (secCMt t S L) (secA t S L) :=
    Subgroup.mem_map.mpr ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  rw [← hXaut] at hmem
  obtain ⟨⟨x, hxN⟩, hxX, hxeq⟩ := Subgroup.mem_map.mp hmem
  have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hact : ∀ a ∈ secA t S L, x * a * x⁻¹ = g * a * g⁻¹ := fun a ha =>
    congrArg (fun φ : MulAut ↥(secA t S L) => ((φ ⟨a, ha⟩ : ↥(secA t S L)) : G)) hxeq
  have hcA : x⁻¹ * g ∈ centralizer (secA t S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    calc a * (x⁻¹ * g) = x⁻¹ * (x * a * x⁻¹) * g := by group
      _ = x⁻¹ * (g * a * g⁻¹) * g := by rw [hact a ha]
      _ = (x⁻¹ * g) * a := by group
  obtain ⟨a, ha, r, hr, hcar⟩ := sec12E_C_decomp F hcA
  have hxN' : x ∈ normalizer (secV t S L E : Set G) := sec125_CMt_le_N F hE (hXC hxX')
  have haN : a ∈ normalizer (secV t S L E : Set G) :=
    sec121_E_le_normalizer_V F hE (sec120_A_le_E F hE ha)
  have hrD : r ∈ centralizer (secV t S L E : Set G) :=
    Subgroup.centralizer_le h.V_le (sec125_R_cent_E F hE hr)
  have hrN : r ∈ normalizer (secV t S L E : Set G) := Subgroup.centralizer_le_normalizer _ hrD
  have hbr : betaOf (secV t S L E) r = 1 := (sec127_betaOf_eq_one_iff hrN).mpr hrD
  have hga : betaOf (secV t S L E) g =
      betaOf (secV t S L E) x * betaOf (secV t S L E) a := by
    have e : g = x * (a * r) := by rw [← hcar]; group
    rw [e, sec127_betaOf_mul hxN' (mul_mem haN hrN), sec127_betaOf_mul haN hrN, hbr, mul_one]
  refine ⟨x, hxX', ?_⟩
  rcases (sec12E_mem_A F).mp ha with hB | ⟨b, hb, rfl⟩
  · left
    have haV : a ∈ secV t S L E := sec121_B_le_V F hE hB
    have haD : a ∈ centralizer (secV t S L E : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => h.comm v hv a haV
    rw [hga, (sec127_betaOf_eq_one_iff haN).mpr haD, mul_one]
  · right
    have hbV : b ∈ secV t S L E := sec121_B_le_V F hE hb
    have hbD : b ∈ centralizer (secV t S L E : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => h.comm v hv b hbV
    have hbN : b ∈ normalizer (secV t S L E : Set G) := Subgroup.centralizer_le_normalizer _ hbD
    rw [hga, sec127_betaOf_mul h.t_mem_normalizer hbN, (sec127_betaOf_eq_one_iff hbN).mpr hbD,
      mul_one]

end CFSG.OddStandard.SmallF3.Omega
