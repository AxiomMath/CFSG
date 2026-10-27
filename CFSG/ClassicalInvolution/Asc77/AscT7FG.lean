module

public import CFSG.ClassicalInvolution.Asc77.AscT7FC
import CFSG.ClassicalInvolution.Asc77.AscT7FGEng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

theorem sq_eq_of_rel {A : Type*} [Group A] (hc : ∀ x y : A, x * y = y * x) {za zb w s : A}
    (h : za * (w * s) = (zb * za) * (w⁻¹ * s)) : w * w = zb :=
  CFSG.ClassicalInvolution.Asc77.sq_eq_of_rel_gen hc h

theorem prod_eq_one_of_sq {A : Type*} [Group A] (hc : ∀ x y : A, x * y = y * x)
    {za w₁ w₂ w₃ u z₁ z₂ z₃ zP : A} (hza : za * za = 1) (h₁ : w₁ * w₁ = z₁)
    (h₂ : w₂ * w₂ = z₂) (h₃ : w₃ * w₃ = z₃) (hz₁ : z₁ * z₁ = 1) (hz₂ : z₂ * z₂ = 1)
    (hz₃ : z₃ * z₃ = 1) (hu : u = za * (w₁ * (w₂ * w₃))) (huP : u * u = zP) :
    z₁ * z₂ * z₃ * zP = 1 := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hc }
  subst h₁ h₂ h₃ huP hu
  calc w₁ * w₁ * (w₂ * w₂) * (w₃ * w₃) * (za * (w₁ * (w₂ * w₃)) * (za * (w₁ * (w₂ * w₃))))
      = (w₁ * w₁ * (w₁ * w₁)) * (w₂ * w₂ * (w₂ * w₂)) * (w₃ * w₃ * (w₃ * w₃)) * (za * za) := by
        ac_rfl
    _ = 1 := by rw [hz₁, hz₂, hz₃, hza]; simp

theorem prod_four_eq {A : Type*} [Group A] (hc : ∀ x y : A, x * y = y * x) {ι : Type*}
    [DecidableEq ι] (ζ : ι → A) {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ι} (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃)
    (ha₁₄ : a₁ ≠ a₄) (ha₂₃ : a₂ ≠ a₃) (ha₂₄ : a₂ ≠ a₄) (ha₃₄ : a₃ ≠ a₄) (hb₁₂ : b₁ ≠ b₂)
    (hb₁₃ : b₁ ≠ b₃) (hb₁₄ : b₁ ≠ b₄) (hb₂₃ : b₂ ≠ b₃) (hb₂₄ : b₂ ≠ b₄) (hb₃₄ : b₃ ≠ b₄)
    (hS : ({a₁, a₂, a₃, a₄} : Finset ι) = {b₁, b₂, b₃, b₄}) :
    ζ a₁ * ζ a₂ * ζ a₃ * ζ a₄ = ζ b₁ * ζ b₂ * ζ b₃ * ζ b₄ := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hc }
  have e1 : ∏ x ∈ ({a₁, a₂, a₃, a₄} : Finset ι), ζ x = ζ a₁ * ζ a₂ * ζ a₃ * ζ a₄ := by
    rw [Finset.prod_insert (by simp [ha₁₂, ha₁₃, ha₁₄]), Finset.prod_insert (by simp [ha₂₃, ha₂₄]),
      Finset.prod_insert (by simp [ha₃₄]), Finset.prod_singleton]
    ac_rfl
  have e2 : ∏ x ∈ ({b₁, b₂, b₃, b₄} : Finset ι), ζ x = ζ b₁ * ζ b₂ * ζ b₃ * ζ b₄ := by
    rw [Finset.prod_insert (by simp [hb₁₂, hb₁₃, hb₁₄]), Finset.prod_insert (by simp [hb₂₃, hb₂₄]),
      Finset.prod_insert (by simp [hb₃₄]), Finset.prod_singleton]
    ac_rfl
  rw [← e1, ← e2, hS]

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem sq_eq_of_conj {r u za zb w s : G} (hza : za ∈ W) (hzb : zb ∈ W) (hw : w ∈ W)
    (hs : s ∈ W) (hu : u = za * (w * s)) (hru : r * u * r⁻¹ = u)
    (hrza : r * za * r⁻¹ = zb * za) (hrw : r * w * r⁻¹ = w⁻¹) (hrs : r * s * r⁻¹ = s) :
    w * w = zb :=
  CFSG.ClassicalInvolution.Asc77.Thompson.sq_eq_of_conj_gen (W := W) c.comm_W hza hzb hw hs hu hru
    hrza hrw hrs

theorem clique_relation (rep : ↥(muGroup Ω W) → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {a d P : ↥(muGroup Ω W)} {B : Finset ↥(muGroup Ω W)}
    (hcfg : Star3T.Cfg (muDelta Ω W) d a)
    (hBC : (↑B : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hP : P ∈ Star3T.cent (muDelta Ω W) d) (hPB : P ∉ B) (hB3 : B.card = 3) {zP : G}
    (hzP : IsUniqueInvolution (rep P).K zP) :
    ∃ b₁ b₂ b₃ : ↥(muGroup Ω W), (∀ x, x ∈ B ↔ x = b₁ ∨ x = b₂ ∨ x = b₃) ∧ b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧
      b₂ ≠ b₃ ∧
      ∃ zb₁ zb₂ zb₃ : G, IsUniqueInvolution (rep b₁).K zb₁ ∧
        IsUniqueInvolution (rep b₂).K zb₂ ∧ IsUniqueInvolution (rep b₃).K zb₃ ∧
          zb₁ * zb₂ * zb₃ * zP = 1 := by
  classical
  have hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W := fun x hx => (hBC hx).1
  have haΔ := hcfg.mem_a
  have hconj := hcfg.tt.exists_conj_of_not_conn hcfg.mem_d hcfg.mem_a hcfg.not_conn
  have hPΔ : P ∈ muDelta Ω W := hP.1
  obtain ⟨za, hza⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep a).hK
  obtain ⟨u, huRW, hu4⟩ := exists_orderOf_four c.hp c.hq c.hΩ c.hW (rep P).hR
  obtain ⟨hRW, -, -, -, -⟩ := inf_W_of_mem_D c.hp c.hq c.hΩ c.hW (rep P).hR (rep P).hK (rep P).hRK
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
  obtain ⟨zb₁, hzb₁⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep b₁).hK
  obtain ⟨zb₂, hzb₂⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep b₂).hK
  obtain ⟨zb₃, hzb₃⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep b₃).hK
  rw [hBset] at ha₁
  obtain ⟨w₁, hw₁, g₂, hg₂, hg₂eq⟩ := c.exists_mul_of_mem_UU_insert rep
    (B := ({b₂, b₃} : Set ↥(muGroup Ω W))) (a := b₁) ha₁
  obtain ⟨w₂, hw₂, g₃, hg₃, hg₃eq⟩ := c.exists_mul_of_mem_UU_insert rep
    (B := ({b₃} : Set ↥(muGroup Ω W))) (a := b₂) hg₂
  have hg₃' : g₃ ∈ c.UU rep (insert b₃ (∅ : Set ↥(muGroup Ω W))) := by simpa using hg₃
  obtain ⟨w₃, hw₃, g₄, hg₄, hg₄eq⟩ := c.exists_mul_of_mem_UU_insert rep
    (B := (∅ : Set ↥(muGroup Ω W))) (a := b₃) hg₃'
  have hg₄1 : g₄ = 1 := by simpa [Ctx.UU] using hg₄
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
  refine ⟨b₁, b₂, b₃, fun x => by rw [hBeq]; simp, h12, h13, h23, zb₁, zb₂, zb₃, hzb₁, hzb₂,
    hzb₃, ?_⟩
  have hc' : ∀ x y : ↥W, x * y = y * x := fun x y => Subtype.ext (c.comm_W x x.2 y y.2)
  have hzaW : za ∈ W := c.mem_W_of_isUniqueInvolution (rep a) hza
  have hz1W : zb₁ ∈ W := c.mem_W_of_isUniqueInvolution (rep b₁) hzb₁
  have hz2W : zb₂ ∈ W := c.mem_W_of_isUniqueInvolution (rep b₂) hzb₂
  have hz3W : zb₃ ∈ W := c.mem_W_of_isUniqueInvolution (rep b₃) hzb₃
  have hzPW : zP ∈ W := c.mem_W_of_isUniqueInvolution (rep P) hzP
  have := prod_eq_one_of_sq hc' (za := (⟨za, hzaW⟩ : ↥W)) (w₁ := ⟨w₁, hw₁W⟩) (w₂ := ⟨w₂, hw₂W⟩)
    (w₃ := ⟨w₃, hw₃W⟩) (u := ⟨u, huW⟩) (z₁ := ⟨zb₁, hz1W⟩) (z₂ := ⟨zb₂, hz2W⟩)
    (z₃ := ⟨zb₃, hz3W⟩) (zP := ⟨zP, hzPW⟩) (Subtype.ext hza.sq) (Subtype.ext hsq₁)
    (Subtype.ext hsq₂) (Subtype.ext hsq₃) (Subtype.ext hzb₁.sq) (Subtype.ext hzb₂.sq)
    (Subtype.ext hzb₃.sq) (Subtype.ext hu_w) (Subtype.ext hzu)
  exact congrArg Subtype.val this

theorem exists_fourth (hnc : ¬ DbarConnected Ω W) (ρ₁ ρ₂ ρ₃ : Rep Ω W)
    (h₁₂ : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (h₁₃ : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h₂₃ : ρ₃.K ∈ omegaNbr Ω ρ₂.K) {z₁ z₂ z₃ : G} (hz₁ : IsUniqueInvolution ρ₁.K z₁)
    (hz₂ : IsUniqueInvolution ρ₂.K z₂) (hz₃ : IsUniqueInvolution ρ₃.K z₃) :
    ∃ ρ₄ : Rep Ω W, ρ₄.K ≠ ρ₁.K ∧ ρ₄.K ≠ ρ₂.K ∧ ρ₄.K ≠ ρ₃.K ∧ ρ₄.K ∈ omegaNbr Ω ρ₁.K ∧
      ρ₄.K ∈ omegaNbr Ω ρ₂.K ∧ ρ₄.K ∈ omegaNbr Ω ρ₃.K ∧
        ∀ z₄, IsUniqueInvolution ρ₄.K z₄ → z₁ * z₂ * z₃ * z₄ = 1 := by
  classical
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hp c.hq c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) :=
      fun x hx => exists_rep_of_mem_muDelta hx
    have : Nonempty (Rep Ω W) := ⟨ρ₁⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  set x₁ := T7D.imgQ ρ₁ with hx₁
  set x₂ := T7D.imgQ ρ₂ with hx₂
  set x₃ := T7D.imgQ ρ₃ with hx₃
  have hx₁Δ : x₁ ∈ muDelta Ω W := T7D.imgQ_mem ρ₁
  have hK12 : ρ₁.K ≠ ρ₂.K := fun e => h₁₂.2.1 e.symm
  have hK13 : ρ₁.K ≠ ρ₃.K := fun e => h₁₃.2.1 e.symm
  have hK23 : ρ₂.K ≠ ρ₃.K := fun e => h₂₃.2.1 e.symm
  have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
    hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
  have hcomm_of : ∀ σ σ' : Rep Ω W, σ'.K ∈ omegaNbr Ω σ.K →
      T7D.imgQ σ * T7D.imgQ σ' = T7D.imgQ σ' * T7D.imgQ σ := fun σ σ' h =>
    Subtype.ext (c.comm_of_omega σ σ' h)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := exists_not_conn_of_not_connected c.hp c.hq c.hΩ c.hW hnc
  obtain ⟨a, haΔ, hna⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) x₁ a := by
    by_cases h : Star3T.Conn (muDelta Ω W) x₁ d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hcfg : Star3T.Cfg (muDelta Ω W) x₁ a := ⟨hTT, hS, hx₁Δ, haΔ, hna⟩
  have hx₂C : x₂ ∈ Star3T.cent (muDelta Ω W) x₁ :=
    ⟨T7D.imgQ_mem ρ₂, (hcomm_of ρ₁ ρ₂ h₁₂).symm⟩
  have hx₃C : x₃ ∈ Star3T.cent (muDelta Ω W) x₁ :=
    ⟨T7D.imgQ_mem ρ₃, (hcomm_of ρ₁ ρ₃ h₁₃).symm⟩
  have hx₁C : x₁ ∈ Star3T.cent (muDelta Ω W) x₁ := Star3T.self_mem_cent hx₁Δ
  have hx12 : x₁ ≠ x₂ := hne_of ρ₁ ρ₂ hK12
  have hx13 : x₁ ≠ x₃ := hne_of ρ₁ ρ₃ hK13
  have hx23 : x₂ ≠ x₃ := hne_of ρ₂ ρ₃ hK23
  have hC3 : 3 ≤ (Star3T.cent (muDelta Ω W) x₁).ncard := by
    have hsub : ({x₁, x₂, x₃} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) x₁ := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact hx₁C
      · exact hx₂C
      · exact hx₃C
    have h3 : ({x₁, x₂, x₃} : Set ↥(muGroup Ω W)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨x₁, x₂, x₃, hx12, hx13, hx23, rfl⟩
    rw [← h3]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hC4 : (Star3T.cent (muDelta Ω W) x₁).ncard = 4 := by
    rcases thompsonClique G Ω hP W c.hW hnc x₁ hx₁Δ with h | h | ⟨h, -⟩
    · omega
    · omega
    · exact h
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  have hn : n = 2 := by
    have h4 : 2 ^ n = 2 ^ 2 := by rw [← hcard, hC4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have hB3 : B.card = 3 := by rw [hBn, hn]
  have hex : ∃ P ∈ Star3T.cent (muDelta Ω W) x₁, P ∉ B := by
    by_contra hall
    push Not at hall
    have h1 : (Star3T.cent (muDelta Ω W) x₁).ncard ≤ B.card := by
      calc (Star3T.cent (muDelta Ω W) x₁).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
            Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
        _ = B.card := Set.ncard_coe_finset B
    omega
  obtain ⟨P, hP', hPB⟩ := hex
  have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP' hPB
  obtain ⟨zP, hzP⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep P).hK
  obtain ⟨b₁, b₂, b₃, hB, h12, h13, h23, zb₁, zb₂, zb₃, hzb₁, hzb₂, hzb₃, hrel⟩ :=
    c.clique_relation rep hrep hcfg hBC hdB hgen hP' hPB hB3 hzP
  obtain ⟨x₄, hx₄C, hx₄⟩ : ∃ y ∈ Star3T.cent (muDelta Ω W) x₁,
      y ≠ x₁ ∧ y ≠ x₂ ∧ y ≠ x₃ := by
    by_contra hall
    push Not at hall
    have hTsub : (insert P B : Finset ↥(muGroup Ω W)) ⊆ {x₁, x₂, x₃} := by
      intro y hy
      have hyC : y ∈ Star3T.cent (muDelta Ω W) x₁ := by
        rcases Finset.mem_insert.mp hy with rfl | hyB
        · exact hP'
        · exact hBC (Finset.mem_coe.mpr hyB)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hne
      push Not at hne
      exact hne.2.2 (hall y hyC hne.1 hne.2.1)
    have hle := Finset.card_le_card hTsub
    rw [Finset.card_insert_of_notMem hPB, hB3] at hle
    have : ({x₁, x₂, x₃} : Finset ↥(muGroup Ω W)).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨hx41, hx42, hx43⟩ := hx₄
  have hx₄Δ : x₄ ∈ muDelta Ω W := hx₄C.1
  have hρ₄img : (rep x₄).img = (x₄ : NQuot (W ⊔ OCW W)) := hrep x₄ hx₄Δ
  have hρ₄ : T7D.imgQ (rep x₄) = x₄ := Subtype.ext hρ₄img
  have hK4 : ∀ σ : Rep Ω W, T7D.imgQ σ ≠ x₄ → (rep x₄).K ≠ σ.K := fun σ hσ e =>
    hσ (by rw [← hρ₄]; exact (Subtype.ext (c.img_eq_of_K_eq σ (rep x₄) e.symm)))
  have hnbr4 : ∀ σ : Rep Ω W, T7D.imgQ σ ∈ Star3T.cent (muDelta Ω W) x₁ →
      T7D.imgQ σ ≠ x₄ → (rep x₄).K ∈ omegaNbr Ω σ.K := fun σ hσC hσ => by
    refine c.omega_of_comm σ (rep x₄) (fun e => hK4 σ hσ e.symm) ?_
    have := hcfg.comm_cent hσC hx₄C
    rw [← hρ₄] at this
    exact congrArg Subtype.val this
  choose zf hzf using fun x : ↥(muGroup Ω W) =>
    c.hΩ.exists_uniqueInvolution c.hp c.hq (rep x).hK
  have hK_eq : ∀ σ : Rep Ω W, (rep (T7D.imgQ σ)).K = σ.K := fun σ =>
    c.K_eq_of_img_eq (rep (T7D.imgQ σ)) σ (hrep _ (T7D.imgQ_mem σ))
  have hzf_eq : ∀ (σ : Rep Ω W) (z : G), IsUniqueInvolution σ.K z → zf (T7D.imgQ σ) = z :=
    fun σ z hz => (hzf _).eq (hK_eq σ ▸ hz)
  have hz₁' : zf x₁ = z₁ := hzf_eq ρ₁ z₁ hz₁
  have hz₂' : zf x₂ = z₂ := hzf_eq ρ₂ z₂ hz₂
  have hz₃' : zf x₃ = z₃ := hzf_eq ρ₃ z₃ hz₃
  have hzb₁' : zf b₁ = zb₁ := (hzf b₁).eq hzb₁
  have hzb₂' : zf b₂ = zb₂ := (hzf b₂).eq hzb₂
  have hzb₃' : zf b₃ = zb₃ := (hzf b₃).eq hzb₃
  have hzP' : zf P = zP := (hzf P).eq hzP
  have hb₁B : b₁ ∈ B := (hB b₁).mpr (Or.inl rfl)
  have hb₂B : b₂ ∈ B := (hB b₂).mpr (Or.inr (Or.inl rfl))
  have hb₃B : b₃ ∈ B := (hB b₃).mpr (Or.inr (Or.inr rfl))
  have hPb₁ : b₁ ≠ P := fun e => hPB (e ▸ hb₁B)
  have hPb₂ : b₂ ≠ P := fun e => hPB (e ▸ hb₂B)
  have hPb₃ : b₃ ≠ P := fun e => hPB (e ▸ hb₃B)
  have hx14 : x₁ ≠ x₄ := fun e => hx41 e.symm
  have hx24 : x₂ ≠ x₄ := fun e => hx42 e.symm
  have hx34 : x₃ ≠ x₄ := fun e => hx43 e.symm
  have hmemT : ∀ y ∈ Star3T.cent (muDelta Ω W) x₁,
      y ∈ ({b₁, b₂, b₃, P} : Finset ↥(muGroup Ω W)) := by
    intro y hy
    by_cases hyP : y = P
    · simp [hyP]
    · have := (hB y).mp (hsub y hy hyP)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  have hSsub : ({x₁, x₂, x₃, x₄} : Finset ↥(muGroup Ω W)) ⊆ {b₁, b₂, b₃, P} := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hmemT _ hx₁C
    · exact hmemT _ hx₂C
    · exact hmemT _ hx₃C
    · exact hmemT _ hx₄C
  have hScard : ({x₁, x₂, x₃, x₄} : Finset ↥(muGroup Ω W)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hx12, hx13, hx14]),
      Finset.card_insert_of_notMem (by simp [hx23, hx24]),
      Finset.card_insert_of_notMem (by simp [hx34]), Finset.card_singleton]
  have hTcard : ({b₁, b₂, b₃, P} : Finset ↥(muGroup Ω W)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, hPb₁]),
      Finset.card_insert_of_notMem (by simp [h23, hPb₂]),
      Finset.card_insert_of_notMem (by simp [hPb₃]), Finset.card_singleton]
  have hSeq : ({x₁, x₂, x₃, x₄} : Finset ↥(muGroup Ω W)) = {b₁, b₂, b₃, P} :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard, hTcard])
  have hc' : ∀ x y : ↥W, x * y = y * x := fun x y => Subtype.ext (c.comm_W x x.2 y y.2)
  let ζ : ↥(muGroup Ω W) → ↥W := fun x =>
    ⟨zf x, c.mem_W_of_isUniqueInvolution (rep x) (hzf x)⟩
  have hprod := prod_four_eq hc' ζ hx12 hx13 hx14 hx23 hx24 hx34 h12 h13
    hPb₁ h23 hPb₂ hPb₃ hSeq
  have hprod' : zf x₁ * zf x₂ * zf x₃ * zf x₄ = 1 := by
    have h1 := congrArg Subtype.val hprod
    have h2 : zf b₁ * zf b₂ * zf b₃ * zf P = 1 := by rw [hzb₁', hzb₂', hzb₃', hzP']; exact hrel
    exact h1.trans h2
  refine ⟨rep x₄, hK4 ρ₁ ?_, hK4 ρ₂ ?_, hK4 ρ₃ ?_, hnbr4 ρ₁ hx₁C ?_, hnbr4 ρ₂ hx₂C ?_,
    hnbr4 ρ₃ hx₃C ?_, ?_⟩
  · exact fun e => hx41 e.symm
  · exact fun e => hx42 e.symm
  · exact fun e => hx43 e.symm
  · exact fun e => hx41 e.symm
  · exact fun e => hx42 e.symm
  · exact fun e => hx43 e.symm
  · intro z₄ hz₄
    have hz₄' : zf x₄ = z₄ := (hzf x₄).eq hz₄
    rw [← hz₁', ← hz₂', ← hz₃', ← hz₄']
    exact hprod'

end Ctx

end Thompson

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.exists_twin_of_J (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    ∃ J' ∈ Ω, J' ≠ J ∧ IsUniqueInvolution J' t ∧ J' ≠ K ∧ J' ≠ K' ∧ J' ∈ omegaNbr Ω K ∧
      J' ∈ omegaNbr Ω K' ∧ J' ∈ omegaNbr Ω J := by
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hK hz h.hzW
  obtain ⟨ρ₂, hρ₂⟩ := c.exists_rep_of_involution_mem hK'Ω hzK' h.hzW
  obtain ⟨ρ₃, hρ₃⟩ := c.exists_rep_of_involution_mem h.hJ.1 h.ht h.htW
  have h12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K := by
    rw [hρ₁, hρ₂]
    exact T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
  have h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K := by
    rw [hρ₁, hρ₃]
    exact h.hJ.2 K (mem_twinSet_self hK hz)
  have h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K := by
    rw [hρ₂, hρ₃]
    exact h.hJ.2 K' h.std.hK'
  obtain ⟨ρ₄, hK41, hK42, hK43, hn41, hn42, hn43, hprod⟩ :=
    c.exists_fourth hnc ρ₁ ρ₂ ρ₃ h12 h13 h23 (hρ₁ ▸ hz) (hρ₂ ▸ hzK') (hρ₃ ▸ h.ht)
  obtain ⟨z₄, hz₄⟩ := hΩ.exists_uniqueInvolution hst.odd hst.five ρ₄.hK
  have h4 := hprod z₄ hz₄
  have hzz : z * z = 1 := hz.sq
  have hz₄t : z₄ = t := by
    have h1 : t * z₄ = 1 := by
      have : z * z * t * z₄ = 1 := h4
      rwa [hzz, one_mul] at this
    have h2 : z₄ = t⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_left h.ht.sq
  refine ⟨ρ₄.K, ρ₄.hK, ?_, hz₄t ▸ hz₄, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hρ₃]; exact hK43
  · rw [← hρ₁]; exact hK41
  · rw [← hρ₂]; exact hK42
  · rw [← hρ₁]; exact hn41
  · rw [← hρ₂]; exact hn42
  · rw [← hρ₃]; exact hn43

end Frame

end CFSG.ClassicalInvolution.Asc77
