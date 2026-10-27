module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FTwo
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3VFour

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.EvenSmallLie.UnitarySix.YamadaD (crossedHom mem_ker_crossedHom crossed_conj
  card_eq_of_crossed_onto)

theorem eq_of_abelian_of_relIndex_eq_two {G : Type*} [Group G] [Finite G]
    {F D A Z : Subgroup G} (hidx : F.relIndex D = 2) (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    {t : G} (htD : t ∈ D) (htF : t ∉ F) (hFt : F ⊓ centralizer ({t} : Set G) ≤ Z)
    (hZ : 2 * Nat.card Z < Nat.card F) (hAD : A ≤ D) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAcard : Nat.card A = Nat.card F) : A = F := by
  by_contra hne
  obtain ⟨a, haA, haF⟩ := IsConcreteLE.not_le_iff_exists.1 fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard]))
  have hidx' : (F.subgroupOf D).index = 2 := hidx
  have htinv : t⁻¹ ∉ F := fun h' => htF (by simpa using inv_mem h')
  have hat : a * t⁻¹ ∈ F := by
    have := (mul_mem_iff_of_index_two hidx' (a := ⟨a, hAD haA⟩) (b := ⟨t⁻¹, inv_mem htD⟩)).2
      (iff_of_false (by rwa [mem_subgroupOf]) (by rwa [mem_subgroupOf]))
    exact mem_subgroupOf.1 this
  have hZ' : F ⊓ A ≤ Z := by
    intro w hw
    obtain ⟨hwF, hwA⟩ := Subgroup.mem_inf.1 hw
    refine hFt (Subgroup.mem_inf.2 ⟨hwF, mem_centralizer_singleton_iff.2 ?_⟩)
    have e1 := hAc w hwA a haA
    have e2 := hFc w hwF _ hat
    have e3 : a * (w * t⁻¹) = a * (t⁻¹ * w) := by
      calc a * (w * t⁻¹) = w * a * t⁻¹ := by rw [e1]; group
        _ = w * (a * t⁻¹) := by group
        _ = a * t⁻¹ * w := e2
        _ = a * (t⁻¹ * w) := by group
    have e4 : w * t⁻¹ = t⁻¹ * w := mul_left_cancel e3
    calc w * t = t * (t⁻¹ * w) * t := by group
      _ = t * (w * t⁻¹) * t := by rw [e4]
      _ = t * w := by group
  have hle : F.relIndex A ≤ 2 := hidx ▸ relIndex_le_of_le_right hAD (by rw [hidx]; norm_num)
  have e := relIndex_mul_card F A
  rw [hAcard] at e
  have h1 : Nat.card F ≤ 2 * Nat.card Z := e ▸ Nat.mul_le_mul hle (card_le_of_le hZ')
  omega

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.F_comm (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∀ x ∈ d.F, ∀ y ∈ d.F, x * y = y * x :=
  hd.F_comm_of fun _ hx _ hy => hd.comm_of_mem_V hGMS hx hy

theorem Hyp.isElementaryAbelian_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.IsElementaryAbelian 2 d.F :=
  hd.isElementaryAbelian_F_of (fun _ hx _ hy => hd.comm_of_mem_V hGMS hx hy)
    fun _ hx => hd.mul_self_eq_one_of_mem_V hGMS hx

theorem Hyp.t_not_mem_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.t ∉ d.F := by
  intro htF
  have hFc := hd.F_comm hGMS
  have hVt : d.V ≤ d.Zp := by
    intro v hv
    rw [← hd.V_inf_centralizer_t]
    exact Subgroup.mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 (hFc v (d.V_le_F hv) d.t htF)⟩
  have h1 := Subgroup.card_le_of_le hVt
  rw [hd.card_V, d.card_Zp] at h1
  have h4 := hd.four_le
  nlinarith

theorem Hyp.F_inf_B₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ d.B₃ = d.A₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf hd.A₁_le_F (d.A₁_le_A₃.trans d.A₃_le_B₃))
  obtain ⟨hxF, hxB⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, ha, h1 | h1⟩ :=
    hd.exists_of_mem_B₁ (hd.mem_B₁_of_mem_B₃ hxB (hd.F_le_centralizer_A₃ hxF))
  · rw [h1]
    exact ha
  · exfalso
    apply hd.t_not_mem_F hGMS
    have := mul_mem hxF (inv_mem (hd.A₁_le_F ha))
    rwa [h1, mul_inv_cancel_right] at this

theorem Hyp.F_inf_centralizer_t (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ centralizer ({d.t} : Set G) = d.A₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf hd.A₁_le_F
    (((d.A₁_le_A₃.trans d.A₃_le_P).trans d.P_le_L).trans hd.L_le_centralizer))
  rw [← hd.F_inf_B₃ hGMS]
  refine Subgroup.mem_inf.2 ⟨hx.1, ?_⟩
  rw [← hd.two_core_B₅.2.2.1]
  exact Subgroup.mem_inf.2 ⟨hd.F_le_B₅ hx.1, hx.2⟩

theorem Hyp.card_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.F = (2 ^ f) ^ 8 := by
  have hc := hd.cosetData_B₁
  rw [card_eq_of_crossed_onto hd.t_mul_t hd.F_le_centralizer_A₁
    (fun x hx => hc.crossed_mem x (hd.F_le_normalizer_B₁ hx))
    (fun _ hy => hd.exists_F_cr_eq hy), hd.F_inf_centralizer_t hGMS, d.card_A₁]
  ring

theorem Hyp.Ft_inf_centralizer_t (hd : d.Hyp) :
    (d.F ⊔ zpowers d.t) ⊓ centralizer ({d.t} : Set G) = d.B₁ := by
  have htC : d.t ∈ centralizer ({d.t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hA₁C : d.A₁ ≤ centralizer ({d.t} : Set G) :=
    ((d.A₁_le_A₃.trans d.A₃_le_P).trans d.P_le_L).trans hd.L_le_centralizer
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le (zpowers_le.2 (mem_sup_right
    (mem_zpowers _))) (hd.A₁_le_F.trans le_sup_left)) (sup_le (zpowers_le.2 htC) hA₁C))
  obtain ⟨hxD, hxt⟩ := Subgroup.mem_inf.1 hx
  rw [← hd.B₅_inf_centralizer_A₃] at hxD
  refine hd.mem_B₁_of_mem_B₃ ?_ hxD.2
  rw [← hd.two_core_B₅.2.2.1]
  exact Subgroup.mem_inf.2 ⟨hxD.1, hxt⟩

theorem Hyp.card_Ft (hd : d.Hyp) : Nat.card (d.F ⊔ zpowers d.t : Subgroup G) = 2 * (2 ^ f) ^ 8 := by
  have hc := hd.cosetData_B₁
  have hDB : d.F ⊔ zpowers d.t ≤ d.B₅ := by
    rw [← hd.B₅_inf_centralizer_A₃]
    exact inf_le_left
  rw [card_eq_of_crossed_onto hd.t_mul_t (hDB.trans hd.two_core_B₅.1)
    (fun x hx => hc.crossed_mem x (d.B₅_le (hDB hx))) (fun _ hy => by
      obtain ⟨x, hx, hxt⟩ := hd.exists_F_cr_eq hy
      exact ⟨x, mem_sup_left hx, hxt⟩), hd.Ft_inf_centralizer_t, hd.card_B₁, d.card_A₁]
  ring

theorem Hyp.eq_F_of_abelian (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {A : Subgroup G} (hA : A ≤ d.F ⊔ zpowers d.t) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAcard : Nat.card A = (2 ^ f) ^ 8) : A = d.F := by
  have hidx : d.F.relIndex (d.F ⊔ zpowers d.t) = 2 := by
    have e := relIndex_mul_card d.F (d.F ⊔ zpowers d.t)
    rw [inf_eq_left.2 le_sup_left, hd.card_F hGMS, hd.card_Ft] at e
    exact Nat.eq_of_mul_eq_mul_right (by positivity) e
  have h4 := hd.four_le
  refine eq_of_abelian_of_relIndex_eq_two hidx (hd.F_comm hGMS) (mem_sup_right (mem_zpowers _))
    (hd.t_not_mem_F hGMS) (hd.F_inf_centralizer_t hGMS).le ?_ hA hAc
    (by rw [hAcard, hd.card_F hGMS])
  rw [d.card_A₁, hd.card_F hGMS]
  have hQ : 4 ≤ (2 ^ f) ^ 4 := h4.trans (Nat.le_self_pow (by norm_num) _)
  have e : (2 ^ f) ^ 8 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
  rw [e]
  nlinarith

theorem Hyp.normalizer_B₁_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : normalizer (d.B₁ : Set G) ≤ normalizer (d.F : Set G) := by
  intro g hg
  refine mem_normalizer_of_map_conj_eq (hd.eq_F_of_abelian hGMS ?_ ?_ ?_)
  · rw [← map_conj_eq_of_mem_normalizer (hd.normalizer_B₁_le_normalizer_Ft hg)]
    exact map_mono le_sup_left
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hd.F_comm hGMS x hx y hy]
  · rw [card_map_of_injective (MulAut.conj g).injective, hd.card_F hGMS]

theorem Hyp.exists_F_mul (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.B₁ : Set G)) :
    ∃ x ∈ d.F, ∃ c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G), g = x * c := by
  obtain ⟨c, hc, y, hy, rfl⟩ := hd.two_core_B₅.2.2.2.2 g hg
  obtain ⟨x, hx, b, hb, rfl⟩ := hd.exists_mul_of_mem_B₅ hy
  have hbN : b ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    ⟨(hd.B₃_le_kernel hb).1.1, hd.B₃_le_centralizer hb⟩
  refine ⟨c * x * c⁻¹, (mem_normalizer_iff.1 (hd.normalizer_B₁_le_normalizer_F hGMS hc.1) x).1 hx,
    c * b, mul_mem hc hbN, by group⟩

theorem Hyp.exists_crossedHom_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∃ ψ : d.F →* d.A₁, Function.Surjective ψ ∧ ψ.ker = d.A₁.subgroupOf d.F ∧
      (∀ x : d.F, (ψ x : G) = (x : G)⁻¹ * d.t * x * d.t) ∧
      ∀ c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ x : d.F,
        ∃ hx : c * x * c⁻¹ ∈ d.F, (ψ ⟨c * x * c⁻¹, hx⟩ : G) = c * ψ x * c⁻¹ := by
  have hc := hd.cosetData_B₁
  refine ⟨crossedHom hd.t_mul_t d.A₁ d.F hd.F_le_centralizer_A₁ fun x hx =>
    hc.crossed_mem x (hd.F_le_normalizer_B₁ hx), ?_, ?_, fun x => rfl, fun c hc' x => ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxt⟩ := hd.exists_F_cr_eq hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxt⟩
  · ext x
    rw [mem_ker_crossedHom, mem_subgroupOf, ← hd.F_inf_centralizer_t hGMS, mem_inf,
      mem_centralizer_singleton_iff]
    exact ⟨fun e => ⟨x.2, e⟩, fun e => e.2⟩
  · exact ⟨(mem_normalizer_iff.1 (hd.normalizer_B₁_le_normalizer_F hGMS hc'.1) x).1 x.2,
      crossed_conj (mem_centralizer_singleton_iff.1 hc'.2)⟩

theorem Hyp.sec3_4 (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) = normalizer (d.B₃ : Set G) ∧
      normalizer (d.B₁ : Set G) =
        d.F ⊔ (normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G)) ∧
      (∀ g ∈ normalizer (d.B₁ : Set G), ∃ x ∈ d.F,
        ∃ c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G), g = x * c) ∧
      d.F ≤ normalizer (d.B₁ : Set G) ∧ normalizer (d.B₁ : Set G) ≤ normalizer (d.F : Set G) ∧
      d.B₅ = d.F ⊔ d.B₃ ∧ d.F ⊓ d.B₃ = d.A₁ ∧
      CFSG.IsElementaryAbelian 2 d.F ∧ Nat.card d.F = (2 ^ f) ^ 8 ∧
      ∃ ψ : d.F →* d.A₁, Function.Surjective ψ ∧ ψ.ker = d.A₁.subgroupOf d.F ∧
        (∀ x : d.F, (ψ x : G) = (x : G)⁻¹ * d.t * x * d.t) ∧
        ∀ c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ x : d.F,
          ∃ hx : c * x * c⁻¹ ∈ d.F, (ψ ⟨c * x * c⁻¹, hx⟩ : G) = c * ψ x * c⁻¹ := by
  refine ⟨hd.normalizer_B₁_eq, le_antisymm (fun g hg => ?_)
    (sup_le hd.F_le_normalizer_B₁ inf_le_left), fun _ hg => hd.exists_F_mul hGMS hg,
    hd.F_le_normalizer_B₁, hd.normalizer_B₁_le_normalizer_F hGMS, hd.B₅_eq_F_sup_B₃,
    hd.F_inf_B₃ hGMS, hd.isElementaryAbelian_F hGMS, hd.card_F hGMS, hd.exists_crossedHom_F hGMS⟩
  obtain ⟨x, hx, c, hc, rfl⟩ := hd.exists_F_mul hGMS hg
  exact mul_mem (mem_sup_left hx) (mem_sup_right hc)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
