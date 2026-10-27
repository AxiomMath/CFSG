module

public import CFSG.ClassicalInvolution.Asc77.AscT7FG
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
import CFSG.ClassicalInvolution.Asc77.AscT7FGEng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.mem_inf_W_of_isUniqueInvolution (ρ :
    Rep Ω W) {z : G} (hz : IsUniqueInvolution ρ.K z) :
    z ∈ ρ.R ⊓ W := by
  obtain ⟨w, hwRW, hw4⟩ := exists_orderOf_four c.hΩ c.hW ρ.hR
  have hw4' : w ^ 4 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw4] at this
  have hw2 : w * w ≠ 1 := fun h => by
    have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hw4] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hwwsq : (w * w) * (w * w) = 1 := by
    calc (w * w) * (w * w) = w ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hw4'
  have hwwR : w * w ∈ ρ.R := ρ.R.mul_mem hwRW.1 hwRW.1
  have hwwK : w * w ∈ ρ.K := ρ.hRK.1 hwwR
  have hwz : w * w = z := (hz.unique (w * w) hwwK hwwsq).resolve_left hw2
  rw [← hwz]
  exact ⟨hwwR, W.mul_mem hwRW.2 hwRW.2⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.mem_W_of_isUniqueInvolution (ρ : Rep Ω
    W) {z : G} (hz : IsUniqueInvolution ρ.K z) :
    z ∈ W :=
  (c.mem_inf_W_of_isUniqueInvolution ρ hz).2

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.clique_dichotomy (hclC :
    Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) {x₀ : ↥(muGroup Ω W)}
    (hx₀ : x₀ ∈ muDelta Ω W) :
    (∀ u ∈ Star3T.cent (muDelta Ω W) x₀, ∀ v ∈ Star3T.cent (muDelta Ω W) x₀, u * v = v * u) ∧
      ∀ x ∈ muDelta Ω W, ∀ y ∈ Star3T.cent (muDelta Ω W) x₀, x * y = y * x →
        x ∈ Star3T.cent (muDelta Ω W) x₀ := by
  have hP : PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ :=
    exists_not_conn_of_not_connected c.hΩ c.hW hnc
  obtain ⟨q₀, hq₀, hpq₀⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) x₀ a := by
    by_cases h : Star3T.Conn (muDelta Ω W) x₀ d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hpl : Star3T.IsPlane (muDelta Ω W) x₀ q₀ (x₀ * q₀ * x₀) := ⟨hx₀, hq₀, hpq₀, rfl⟩
  refine ⟨fun u hu v hv => hTT.isClique_cent hS hx₀ hq₀ hpq₀ hu hv, ?_⟩
  intro x hx y hy hxy
  have hxU : x ∈ Star3T.cent (muDelta Ω W) x₀ ∪ Star3T.cent (muDelta Ω W) q₀ ∪
      Star3T.cent (muDelta Ω W) (x₀ * q₀ * x₀) := by
    rw [← Star3T.IsTT.cent_union_eq hS hpl]
    exact hx
  have hpx : Star3T.Conn (muDelta Ω W) x₀ x :=
    (Star3T.conn_of_mem_cent hx₀ hy).trans (Star3T.conn_of_commute hy.1 hx hxy.symm)
  rcases hxU with (h1 | h2) | h3
  · exact h1
  · exact absurd (hpx.trans (Star3T.conn_of_mem_cent hq₀ h2).symm) hpq₀
  · exact absurd (hpx.trans (Star3T.conn_of_mem_cent (hTT.mem_third hpl) h3).symm)
      (hTT.not_conn_third_left hpl)
end Ctx
end Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}
end Frame
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.sq_eq_of_conj {r u za zb w s : G} (hza
    : za ∈ W) (hzb : zb ∈ W) (hw : w ∈ W)
    (hs : s ∈ W) (hu : u = za * (w * s)) (hru : r * u * r⁻¹ = u)
    (hrza : r * za * r⁻¹ = zb * za) (hrw : r * w * r⁻¹ = w⁻¹) (hrs : r * s * r⁻¹ = s) :
    w * w = zb :=
  CFSG.ClassicalInvolution.Asc77.Thompson.sq_eq_of_conj_gen (W := W) c.comm_W hza hzb hw hs hu hru
    hrza hrw hrs
end Ctx
end Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}
end Frame
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c
open Classical in

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.clique_relation' (rep : ↥(muGroup Ω W)
    → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {a d P : ↥(muGroup Ω W)} {B : Finset ↥(muGroup Ω W)}
    (hcfg : Star3T.Cfg (muDelta Ω W) d a)
    (hBC : (↑B : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hP : P ∈ Star3T.cent (muDelta Ω W) d) (hPB : P ∉ B) (hB3 : B.card = 3) :
    ∃ (za : G) (g : ↥(muGroup Ω W) → G), IsUniqueInvolution (rep a).K za ∧
      (∀ x ∈ insert P B, g x ∈ (rep x).K ⊓ W ∧ orderOf (g x) = 4) ∧
      ∀ x₁ x₂ x₃ x₄ : ↥(muGroup Ω W), x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₂ ≠ x₃ → x₂ ≠ x₄ →
        x₃ ≠ x₄ → ({x₁, x₂, x₃, x₄} : Finset ↥(muGroup Ω W)) = insert P B →
          za = g x₁ * g x₂ * g x₃ * g x₄ := by
  classical
  obtain ⟨zP, hzP⟩ := c.hΩ.exists_uniqueInvolution (rep P).hK
  have hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W := fun x hx => (hBC hx).1
  have haΔ := hcfg.mem_a
  have hconj := hcfg.tt.exists_conj_of_not_conn hcfg.mem_d hcfg.mem_a hcfg.not_conn
  have hPΔ : P ∈ muDelta Ω W := hP.1
  obtain ⟨za, hza⟩ := c.hΩ.exists_uniqueInvolution (rep a).hK
  obtain ⟨u, huRW, hu4⟩ := exists_orderOf_four c.hΩ c.hW (rep P).hR
  obtain ⟨hRW, -, -, -, -⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW (rep P).hR (rep P).hK (rep
      P).hRK
  have huKW : u ∈ (rep P).K ⊓ W := by rw [← hRW]; exact huRW
  have hu_pow : u ^ 4 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu4] at this
  have huW : u ∈ W := huKW.2
  have hzu : u * u = zP := sq_eq_involution_of_orderOf_four hzP huKW.1 hu4
  have hu2 : u * u ≠ 1 := hzu ▸ hzP.ne_one
  have huW₀ : u ∈ c.UU rep (insert a (↑B : Set ↥(muGroup Ω W))) :=
    c.U4_le_UU_of_generates rep hrep hBΔ haΔ hdB hgen hconj hPΔ ⟨huKW.1, huW, hu_pow⟩
  obtain ⟨x, hx, a₁, ha₁, hu_eq⟩ := c.exists_mul_of_mem_UU_insert rep huW₀
  have hxW : x ∈ W := c.U4_le_W _ hx
  have ha₁W : a₁ ∈ W := c.W4_le (c.UU_le_W4 rep _ ha₁)
  have hpA : ∀ g ∈ c.UU rep (↑B : Set ↥(muGroup Ω W)),
      (rep P).r * g * (rep P).r⁻¹ = g :=
    c.centralizes_UU rep hrep hPΔ (fun s hs => ⟨hBΔ hs, fun e => hPB (e ▸ hs),
      hcfg.comm_cent hP (hBC hs)⟩)
  have h1 : (rep P).r * u * (rep P).r⁻¹ = u⁻¹ := c.conj_inv (rep P) huKW
  have h2 : (rep P).r * a₁ * (rep P).r⁻¹ = a₁ := hpA a₁ ha₁
  have hx_eq : x = u * a₁⁻¹ := by rw [hu_eq]; group
  have hpx : (rep P).r * x * (rep P).r⁻¹ = u⁻¹ * a₁⁻¹ := by
    calc (rep P).r * x * (rep P).r⁻¹ = (rep P).r * (u * a₁⁻¹) * (rep P).r⁻¹ := by rw [← hx_eq]
      _ = ((rep P).r * u * (rep P).r⁻¹) * ((rep P).r * a₁ * (rep P).r⁻¹)⁻¹ := by group
      _ = u⁻¹ * a₁⁻¹ := by rw [h1, h2]
  have hPa : P * a ≠ a * P := hcfg.noncomm_a hP
  obtain ⟨hKPa, hnotPa⟩ := c.rep_noncomm rep hrep hPΔ haΔ hPa
  have hx2 : x * x = 1 := by
    by_contra hx2
    have hxx4 : (x * x) * (x * x) = 1 := by
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hx.2.2
    have hxza : x * x = za :=
      (hza.unique (x * x) ((rep a).K.mul_mem hx.1 hx.1) hxx4).resolve_left hx2
    have hc : Commute u a₁⁻¹ := c.comm_W u huW a₁⁻¹ (W.inv_mem ha₁W)
    have hu2inv : (u ^ 2)⁻¹ = u ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      exact hu_pow
    have hpxx : (rep P).r * (x * x) * (rep P).r⁻¹ = x * x := by
      calc (rep P).r * (x * x) * (rep P).r⁻¹
          = ((rep P).r * x * (rep P).r⁻¹) * ((rep P).r * x * (rep P).r⁻¹) := by group
        _ = (u⁻¹ * a₁⁻¹) * (u⁻¹ * a₁⁻¹) := by rw [hpx]
        _ = (u⁻¹) ^ 2 * (a₁⁻¹) ^ 2 := by rw [← pow_two, hc.inv_left.mul_pow]
        _ = u ^ 2 * (a₁⁻¹) ^ 2 := by rw [inv_pow, hu2inv]
        _ = (u * a₁⁻¹) * (u * a₁⁻¹) := by rw [← pow_two, hc.mul_pow]
        _ = x * x := by rw [← hx_eq]
    have hconj_za := c.conj_involution (rep P) (rep a) hKPa hnotPa hzP hza
    rw [← hxza, hpxx, hxza] at hconj_za
    have : zP = 1 := by
      have h3 : zP * za = 1 * za := by rw [← hconj_za, one_mul]
      exact mul_right_cancel h3
    exact hzP.ne_one this
  have hx1 : x ≠ 1 := by
    intro hx1
    have hu_a : u = a₁ := by rw [hu_eq, hx1, one_mul]
    have h3 : (rep P).r * u * (rep P).r⁻¹ = u := by rw [hu_a]; exact hpA a₁ ha₁
    rw [h3] at h1
    apply hu2
    calc u * u = u⁻¹ * u := congrArg (· * u) h1
      _ = 1 := inv_mul_cancel u
  have hxza : x = za := (hza.unique x hx.1 hx2).resolve_left hx1
  have hu_za : u = za * a₁ := by rw [hu_eq, hxza]
  obtain ⟨b₁, b₂, b₃, h12, h13, h23, hBeq⟩ := Finset.card_eq_three.mp hB3
  have hBset : (↑B : Set ↥(muGroup Ω W)) = {b₁, b₂, b₃} := by
    rw [hBeq]
    simp [Finset.coe_insert]
  have hb₁ : b₁ ∈ B := by rw [hBeq]; simp
  have hb₂ : b₂ ∈ B := by rw [hBeq]; simp
  have hb₃ : b₃ ∈ B := by rw [hBeq]; simp
  obtain ⟨zb₁, hzb₁⟩ := c.hΩ.exists_uniqueInvolution (rep b₁).hK
  obtain ⟨zb₂, hzb₂⟩ := c.hΩ.exists_uniqueInvolution (rep b₂).hK
  obtain ⟨zb₃, hzb₃⟩ := c.hΩ.exists_uniqueInvolution (rep b₃).hK
  rw [hBset] at ha₁
  obtain ⟨w₁, hw₁, g₂, hg₂, hg₂eq⟩ := c.exists_mul_of_mem_UU_insert rep
    (B := ({b₂, b₃} : Set ↥(muGroup Ω W))) (a := b₁) ha₁
  obtain ⟨w₂, hw₂, g₃, hg₃, hg₃eq⟩ := c.exists_mul_of_mem_UU_insert rep
    (B := ({b₃} : Set ↥(muGroup Ω W))) (a := b₂) hg₂
  have hg₃' : g₃ ∈ c.UU rep (insert b₃ (∅ : Set ↥(muGroup Ω W))) := by simpa using hg₃
  obtain ⟨w₃, hw₃, g₄, hg₄, hg₄eq⟩ := c.exists_mul_of_mem_UU_insert rep
    (B := (∅ : Set ↥(muGroup Ω W))) (a := b₃) hg₃'
  have hg₄1 : g₄ = 1 := by simpa [CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.UU] using hg₄
  have ha₁eq : a₁ = w₁ * (w₂ * w₃) := by rw [hg₂eq, hg₃eq, hg₄eq, hg₄1, mul_one]
  have hu_w : u = za * (w₁ * (w₂ * w₃)) := by rw [hu_za, ha₁eq]
  have hBfix : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∀ v ∈ (rep b').K ⊓ W,
      (rep b).r * v * (rep b).r⁻¹ = v := by
    intro b hb b' hb' hne v hv
    have hnbr : (rep b').K ∈ omegaNbr Ω (rep b).K :=
      c.rep_omega rep hrep (hBΔ (Finset.mem_coe.mpr hb)) (hBΔ (Finset.mem_coe.mpr hb')) hne
        (hcfg.comm_cent (hBC (Finset.mem_coe.mpr hb)) (hBC (Finset.mem_coe.mpr hb')))
    have := c.centralizes (rep b) (rep b') hnbr hv
    rw [this]
    group
  have key : ∀ b ∈ B, ∀ (w s zb : G), w ∈ c.U4 (rep b) → s ∈ W →
      IsUniqueInvolution (rep b).K zb → u = za * (w * s) →
        (rep b).r * s * (rep b).r⁻¹ = s → w * w = zb := by
    intro b hb w s zb hw hs hzb hu hrs
    have hbΔ : b ∈ muDelta Ω W := hBΔ (Finset.mem_coe.mpr hb)
    have hne : b ≠ P := fun e => hPB (e ▸ hb)
    have hnbr : (rep P).K ∈ omegaNbr Ω (rep b).K :=
      c.rep_omega rep hrep hbΔ hPΔ hne (hcfg.comm_cent (hBC (Finset.mem_coe.mpr hb)) hP)
    have hru : (rep b).r * u * (rep b).r⁻¹ = u := by
      rw [c.centralizes (rep b) (rep P) hnbr huKW]
      group
    obtain ⟨hKne, hnot⟩ := c.rep_noncomm rep hrep hbΔ haΔ
      (hcfg.noncomm_a (hBC (Finset.mem_coe.mpr hb)))
    have hrza : (rep b).r * za * (rep b).r⁻¹ = zb * za :=
      c.conj_involution (rep b) (rep a) hKne hnot hzb hza
    have hrw : (rep b).r * w * (rep b).r⁻¹ = w⁻¹ := c.conj_inv (rep b) (c.mem_inf_of_mem_U4 hw)
    exact c.sq_eq_of_conj (c.mem_W_of_isUniqueInvolution (rep a) hza)
      (c.mem_W_of_isUniqueInvolution (rep b) hzb) (c.U4_le_W _ hw) hs hu hru hrza hrw hrs
  have hw₁W : w₁ ∈ W := c.U4_le_W _ hw₁
  have hw₂W : w₂ ∈ W := c.U4_le_W _ hw₂
  have hw₃W : w₃ ∈ W := c.U4_le_W _ hw₃
  have hfix₁ : (rep b₁).r * (w₂ * w₃) * (rep b₁).r⁻¹ = w₂ * w₃ := by
    have e2 := hBfix b₁ hb₁ b₂ hb₂ h12 w₂ (c.mem_inf_of_mem_U4 hw₂)
    have e3 := hBfix b₁ hb₁ b₃ hb₃ h13 w₃ (c.mem_inf_of_mem_U4 hw₃)
    calc (rep b₁).r * (w₂ * w₃) * (rep b₁).r⁻¹
        = ((rep b₁).r * w₂ * (rep b₁).r⁻¹) * ((rep b₁).r * w₃ * (rep b₁).r⁻¹) := by group
      _ = w₂ * w₃ := by rw [e2, e3]
  have hfix₂ : (rep b₂).r * (w₁ * w₃) * (rep b₂).r⁻¹ = w₁ * w₃ := by
    have e1 := hBfix b₂ hb₂ b₁ hb₁ (Ne.symm h12) w₁ (c.mem_inf_of_mem_U4 hw₁)
    have e3 := hBfix b₂ hb₂ b₃ hb₃ h23 w₃ (c.mem_inf_of_mem_U4 hw₃)
    calc (rep b₂).r * (w₁ * w₃) * (rep b₂).r⁻¹
        = ((rep b₂).r * w₁ * (rep b₂).r⁻¹) * ((rep b₂).r * w₃ * (rep b₂).r⁻¹) := by group
      _ = w₁ * w₃ := by rw [e1, e3]
  have hfix₃ : (rep b₃).r * (w₁ * w₂) * (rep b₃).r⁻¹ = w₁ * w₂ := by
    have e1 := hBfix b₃ hb₃ b₁ hb₁ (Ne.symm h13) w₁ (c.mem_inf_of_mem_U4 hw₁)
    have e2 := hBfix b₃ hb₃ b₂ hb₂ (Ne.symm h23) w₂ (c.mem_inf_of_mem_U4 hw₂)
    calc (rep b₃).r * (w₁ * w₂) * (rep b₃).r⁻¹
        = ((rep b₃).r * w₁ * (rep b₃).r⁻¹) * ((rep b₃).r * w₂ * (rep b₃).r⁻¹) := by group
      _ = w₁ * w₂ := by rw [e1, e2]
  have hsq₁ : w₁ * w₁ = zb₁ :=
    key b₁ hb₁ w₁ (w₂ * w₃) zb₁ hw₁ (W.mul_mem hw₂W hw₃W) hzb₁ hu_w hfix₁
  have hsq₂ : w₂ * w₂ = zb₂ := by
    refine key b₂ hb₂ w₂ (w₁ * w₃) zb₂ hw₂ (W.mul_mem hw₁W hw₃W) hzb₂ ?_ hfix₂
    rw [hu_w, ← mul_assoc w₁, c.comm_W w₁ hw₁W w₂ hw₂W, mul_assoc]
  have hsq₃ : w₃ * w₃ = zb₃ := by
    refine key b₃ hb₃ w₃ (w₁ * w₂) zb₃ hw₃ (W.mul_mem hw₁W hw₂W) hzb₃ ?_ hfix₃
    have e : w₁ * (w₂ * w₃) = w₃ * (w₁ * w₂) := by
      calc w₁ * (w₂ * w₃) = w₁ * (w₃ * w₂) := by rw [c.comm_W w₂ hw₂W w₃ hw₃W]
        _ = (w₁ * w₃) * w₂ := by rw [mul_assoc]
        _ = (w₃ * w₁) * w₂ := by rw [c.comm_W w₁ hw₁W w₃ hw₃W]
        _ = w₃ * (w₁ * w₂) := by rw [mul_assoc]
    rw [hu_w, e]
  have ord4 : ∀ {w zb : G}, w ^ 4 = 1 → w * w = zb → zb ≠ 1 → orderOf w = 4 := by
    intro w zb h4 hsq hne
    have h2 : ¬ w ^ 2 ^ 1 = 1 := by
      intro h
      apply hne
      rw [← hsq]
      simpa [pow_two] using h
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 (by simpa using h4)
    simpa using this
  have ow₁ : orderOf w₁ = 4 := ord4 hw₁.2.2 hsq₁ hzb₁.ne_one
  have ow₂ : orderOf w₂ = 4 := ord4 hw₂.2.2 hsq₂ hzb₂.ne_one
  have ow₃ : orderOf w₃ = 4 := ord4 hw₃.2.2 hsq₃ hzb₃.ne_one
  have hPb₁ : P ≠ b₁ := fun e => hPB (e ▸ hb₁)
  have hPb₂ : P ≠ b₂ := fun e => hPB (e ▸ hb₂)
  have hPb₃ : P ≠ b₃ := fun e => hPB (e ▸ hb₃)
  let g : ↥(muGroup Ω W) → G := fun x => if x = P then u else if x = b₁ then w₁⁻¹ else
    if x = b₂ then w₂⁻¹ else if x = b₃ then w₃⁻¹ else 1
  have hgP : g P = u := by simp [g]
  have hg1 : g b₁ = w₁⁻¹ := by simp [g, Ne.symm hPb₁]
  have hg2 : g b₂ = w₂⁻¹ := by simp [g, Ne.symm hPb₂, h12.symm]
  have hg3 : g b₃ = w₃⁻¹ := by simp [g, Ne.symm hPb₃, h13.symm, h23.symm]
  have hgW : ∀ x, g x ∈ W := by
    intro x
    simp only [g]
    split_ifs
    · exact huW
    · exact W.inv_mem hw₁W
    · exact W.inv_mem hw₂W
    · exact W.inv_mem hw₃W
    · exact W.one_mem
  have hzaW : za ∈ W := c.mem_W_of_isUniqueInvolution (rep a) hza
  have hWcomm : ∀ x y : ↥W, x * y = y * x := fun x y => Subtype.ext (c.comm_W x x.2 y y.2)
  refine ⟨za, g, hza, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxB
    · rw [hgP]
      exact ⟨huKW, hu4⟩
    · have hx3 : x = b₁ ∨ x = b₂ ∨ x = b₃ := by
        rw [hBeq] at hxB
        simpa using hxB
      rcases hx3 with rfl | rfl | rfl
      · rw [hg1]
        exact ⟨⟨(rep x).K.inv_mem (c.mem_inf_of_mem_U4 hw₁).1, W.inv_mem hw₁W⟩,
          by rw [orderOf_inv]; exact ow₁⟩
      · rw [hg2]
        exact ⟨⟨(rep x).K.inv_mem (c.mem_inf_of_mem_U4 hw₂).1, W.inv_mem hw₂W⟩,
          by rw [orderOf_inv]; exact ow₂⟩
      · rw [hg3]
        exact ⟨⟨(rep x).K.inv_mem (c.mem_inf_of_mem_U4 hw₃).1, W.inv_mem hw₃W⟩,
          by rw [orderOf_inv]; exact ow₃⟩
  · intro x₁ x₂ x₃ x₄ h12' h13' h14' h23' h24' h34' hS
    let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hWcomm }
    have hSeq : ({x₁, x₂, x₃, x₄} : Finset ↥(muGroup Ω W)) = {b₁, b₂, b₃, P} := by
      rw [hS, hBeq]
      ext y
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    let ζ : ↥(muGroup Ω W) → ↥W := fun x => ⟨g x, hgW x⟩
    have hprod := prod_four_eq hWcomm ζ h12' h13' h14' h23' h24' h34' h12 h13 hPb₁.symm h23
      hPb₂.symm hPb₃.symm hSeq
    have hprod' : g x₁ * g x₂ * g x₃ * g x₄ = g b₁ * g b₂ * g b₃ * g P :=
      congrArg Subtype.val hprod
    rw [hprod', hg1, hg2, hg3, hgP]
    have hu_w' : (⟨u, huW⟩ : ↥W) = ⟨za, hzaW⟩ * (⟨w₁, hw₁W⟩ * (⟨w₂, hw₂W⟩ * ⟨w₃, hw₃W⟩)) :=
      Subtype.ext hu_w
    have e : ((⟨w₁, hw₁W⟩ : ↥W)⁻¹ * (⟨w₂, hw₂W⟩ : ↥W)⁻¹ * (⟨w₃, hw₃W⟩ : ↥W)⁻¹ *
        ⟨za, hzaW⟩ * (⟨w₁, hw₁W⟩ * (⟨w₂, hw₂W⟩ * ⟨w₃, hw₃W⟩))) =
        ⟨za, hzaW⟩ * (((⟨w₁, hw₁W⟩ : ↥W)⁻¹ * ⟨w₁, hw₁W⟩) * ((⟨w₂, hw₂W⟩ : ↥W)⁻¹ * ⟨w₂, hw₂W⟩) *
          ((⟨w₃, hw₃W⟩ : ↥W)⁻¹ * ⟨w₃, hw₃W⟩)) := by ac_rfl
    have hfin : ((⟨w₁, hw₁W⟩ : ↥W)⁻¹ * (⟨w₂, hw₂W⟩ : ↥W)⁻¹ * (⟨w₃, hw₃W⟩ : ↥W)⁻¹ *
        ⟨u, huW⟩) = ⟨za, hzaW⟩ := by
      rw [hu_w']
      calc _ = ((⟨w₁, hw₁W⟩ : ↥W)⁻¹ * (⟨w₂, hw₂W⟩ : ↥W)⁻¹ * (⟨w₃, hw₃W⟩ : ↥W)⁻¹ *
        ⟨za, hzaW⟩ * (⟨w₁, hw₁W⟩ * (⟨w₂, hw₂W⟩ * ⟨w₃, hw₃W⟩))) := by
            simp only [mul_assoc]
        _ = _ := by rw [e]; simp
    exact (congrArg Subtype.val hfin).symm
end Ctx
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_relation (hclC :
    Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W)
    (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) :
    ∃ (σ : Rep Ω W) (t : G) (g : Fin 4 → G), IsUniqueInvolution σ.K t ∧
      (∀ i, σ.img * (ρ i).img ≠ (ρ i).img * σ.img) ∧
      (∀ i, g i ∈ (ρ i).K ⊓ W ∧ orderOf (g i) = 4) ∧ t = g 0 * g 1 * g 2 * g 3 := by
  classical
  have hP : PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) :=
      fun x hx => exists_rep_of_mem_muDelta hx
    have : Nonempty (Rep Ω W) := ⟨ρ 0⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  set x : Fin 4 → ↥(muGroup Ω W) := fun i => T7D.imgQ (ρ i) with hx
  have hxΔ : ∀ i, x i ∈ muDelta Ω W := fun i => T7D.imgQ_mem (ρ i)
  have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
    hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
  have hcomm_of : ∀ σ σ' : Rep Ω W, σ'.K ∈ omegaNbr Ω σ.K →
      T7D.imgQ σ * T7D.imgQ σ' = T7D.imgQ σ' * T7D.imgQ σ := fun σ σ' h =>
    Subtype.ext (c.comm_of_omega σ σ' h)
  have hxne : ∀ i j, i ≠ j → x i ≠ x j := fun i j hij => hne_of _ _ (hne i j hij)
  have hxC : ∀ i, x i ∈ Star3T.cent (muDelta Ω W) (x 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (hxΔ 0)
    · exact ⟨hxΔ i, (hcomm_of (ρ 0) (ρ i) (hnbr 0 i (Ne.symm hi))).symm⟩
  have hxC' : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxne 0 1 (by decide), hxne 0 2 (by decide),
        hxne 0 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 1 2 (by decide), hxne 1 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 2 3 (by decide)]), Finset.card_singleton]
  have hC4 : (Star3T.cent (muDelta Ω W) (x 0)).ncard = 4 := by
    have hsub : (↑({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
        Star3T.cent (muDelta Ω W) (x 0) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    have hge : 4 ≤ (Star3T.cent (muDelta Ω W) (x 0)).ncard := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, hxC'] at this
    rcases thompsonClique G Ω hP W c.hW hnc (x 0) (hxΔ 0) with h | h | ⟨h, -⟩
    · omega
    · omega
    · exact h
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := exists_not_conn_of_not_connected c.hΩ c.hW hnc
  obtain ⟨a, haΔ, hna⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) (x 0) a := by
    by_cases h : Star3T.Conn (muDelta Ω W) (x 0) d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hcfg : Star3T.Cfg (muDelta Ω W) (x 0) a := ⟨hTT, hS, hxΔ 0, haΔ, hna⟩
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  have hn : n = 2 := by
    have h4 : 2 ^ n = 2 ^ 2 := by rw [← hcard, hC4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have hB3 : B.card = 3 := by rw [hBn, hn]
  obtain ⟨P, hP', hPB⟩ : ∃ P ∈ Star3T.cent (muDelta Ω W) (x 0), P ∉ B := by
    by_contra hall
    push Not at hall
    have h1 : (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ B.card := by
      calc (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
            Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
        _ = B.card := Set.ncard_coe_finset B
    omega
  have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP' hPB
  obtain ⟨za, g, hza, hmem, hrel⟩ := c.clique_relation' rep hrep hcfg hBC hdB hgen hP' hPB hB3
  have hcardPB : (insert P B).card = 4 := by rw [Finset.card_insert_of_notMem hPB, hB3]
  have hSeq : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) = insert P B := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hxC', hcardPB])
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have hyC : y ∈ Star3T.cent (muDelta Ω W) (x 0) := by
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    by_cases hyP : y = P
    · rw [hyP]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hsub y hyC hyP)
  have hKeq : ∀ i, (rep (x i)).K = (ρ i).K := fun i =>
    c.K_eq_of_img_eq (rep (x i)) (ρ i) (hrep (x i) (hxΔ i))
  have hxmem : ∀ i, x i ∈ insert P B := fun i => by
    rw [← hSeq]
    fin_cases i <;> simp [hx]
  refine ⟨rep a, za, fun i => g (x i), hza, ?_, ?_, ?_⟩
  · intro i hcomm
    apply hna
    have h1 : a * x i = x i * a := by
      apply Subtype.ext
      have := hrep a haΔ
      have h2 : (rep a).img * (ρ i).img = (ρ i).img * (rep a).img := hcomm
      rw [this] at h2
      exact h2
    obtain ⟨-, hAON⟩ := c.clique_dichotomy hclC hnc (hxΔ 0)
    have : a ∈ Star3T.cent (muDelta Ω W) (x 0) := hAON a haΔ (x i) (hxC i) h1
    exact Star3T.conn_of_mem_cent (hxΔ 0) this
  · intro i
    have := hmem (x i) (hxmem i)
    rw [hKeq i] at this
    exact this
  · exact hrel (x 0) (x 1) (x 2) (x 3) (hxne 0 1 (by decide)) (hxne 0 2 (by decide))
      (hxne 0 3 (by decide)) (hxne 1 2 (by decide)) (hxne 1 3 (by decide))
      (hxne 2 3 (by decide)) hSeq
end Ctx
end Thompson
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
