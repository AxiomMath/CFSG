module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22NoV
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2205

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem comm_gen
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
  have hc12 : Commute u₁ u₂ := h.comm₁₂
  have hc13 : Commute u₁ u₃ := Q3T8.Asc77.T7J.comm₁₃ h
  have hc23 : Commute u₂ u₃ := h.comm₂₃
  have hcu₁₂ : Commute (u₁ * u₂) z :=
    Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)
  have hcu₂₃ : Commute (u₂ * u₃) z :=
    Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)
  have hmix : Commute (u₁ * u₂) (u₂ * u₃) :=
    Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hcu₁₂.eq
  · exact hmix.eq
  · exact hcu₁₂.symm.eq
  · rfl
  · exact hcu₂₃.symm.eq
  · exact hmix.symm.eq
  · exact hcu₂₃.eq
  · rfl

theorem B_le_centralizer
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)).eq

theorem isElemAbelian2_closure_23
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₂ * u₃, z} : Set G)) 2 :=
  Q3T8.Asc77.S22.isElemAbelian2_closure (Q3T8.Asc77.S22.rotate h)

theorem closure_23_le
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_thd
  · exact T7B.mem_closure_snd

theorem closure_12_le
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_fst
  · exact T7B.mem_closure_snd

theorem closure_13_le
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h.mem_B_13
  · exact T7B.mem_closure_snd

theorem isElemAbelian2_closure_13
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₃, z} : Set G)) 2 := by
  have h' := Q3T8.Asc77.S22.isElemAbelian2_closure (Q3T8.Asc77.S22.rotate (Q3T8.Asc77.S22.rotate h))
  rwa [← Q3T8.Asc77.T7J.comm₁₃ h] at h'

theorem natCard_B
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Nat.card ↥(Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) = 8 := by
  have := h.hB.1
  norm_num at this
  exact this

theorem exists_replace_third
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') :
    ∃ w : G, Q3T8.Asc77.Hyp22Setting Ω K K' M z u₁ u₂ w := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet h.hz hM
  obtain ⟨R, R', -, hR, hR', -, h₁, h₂, -, c₁₂, -, -⟩ := Q3T8.Asc77.T7J.exists_sylow_triple h
  obtain ⟨R_M, hRM, c₁, c₂⟩ := Q3T8.Asc77.T7B.exists_third_sylow hΩ h.stand.mem h.hK'.1 hM.1
    h.hz h.hzK' hzM hMK hMK' hR hR' c₁₂
  obtain ⟨w, hw, o₃⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hM.1 hRM)
  exact ⟨w, Q3T8.Asc77.S22.hyp22Setting_of_sylows h.stand h.hz h.hK' h.hne h.perp hM hMK hMK' hR
      hR' hRM c₁₂
    c₁ c₂ h₁ h₂ hw h.hu₁.2 h.hu₂.2 o₃⟩

theorem conj
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {g : G} (hg : g * z * g⁻¹ = z) :
    Q3T8.Asc77.Hyp22Setting Ω (conjSub g K) (conjSub g K') (conjSub g K₃) z (g * u₁ * g⁻¹)
      (g * u₂ * g⁻¹) (g * u₃ * g⁻¹) := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  have hcK : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hzc : IsUniqueInvolution (conjSub g K) z := by
    have := h.hz.conj g
    rwa [hg] at this
  have hmem : conjSub g K ∈ twinSet Ω K := ⟨hcK, z, h.hz, hzc⟩
  have hperp : KPerp Ω (conjSub g K) = KPerp Ω K :=
    ((CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK _ hmem).1).symm
  have htw : twinSet Ω (conjSub g K) = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz hmem
  have hB : Subgroup.closure ({(g * u₁ * g⁻¹) * (g * u₂ * g⁻¹), z,
        (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹)} : Set G) =
      conjSub g (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    rw [T7B.conjSub_closure_three, hg]
    have e1 : (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ := by group
    have e2 : (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹) = g * (u₂ * u₃) * g⁻¹ := by group
    rw [e1, e2]
  refine
    { stand := h.stand.of_mem hcK
      hz := hzc
      hK' := twinSet_conj hΩ.conjInvariant h.hK' g
      hne := fun e => h.hne (conjSub_injective g e)
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := twinSet_conj hΩ.conjInvariant h.hK₃ g
      hK₃K := fun e => h.hK₃K (conjSub_injective g e)
      hK₃K' := fun e => h.hK₃K' (conjSub_injective g e)
      hu₁ := ⟨conj_mem_conjSub h.hu₁.1, by rw [T7B.orderOf_conj']; exact h.hu₁.2⟩
      hu₂ := ⟨conj_mem_conjSub h.hu₂.1, by rw [T7B.orderOf_conj']; exact h.hu₂.2⟩
      hu₃ := ⟨conj_mem_conjSub h.hu₃.1, by rw [T7B.orderOf_conj']; exact h.hu₃.2⟩
      hB := ?_ }
  rw [hB]
  refine ⟨by rw [natCard_conjSub]; exact h.hB.1, fun x hx => ?_⟩
  have hx' := mem_conjSub_iff.mp hx
  have := h.hB.2 _ hx'
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [this]; group
end Setting
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.clique_relation
    (rep : ↥(muGroup Ω W)
    → Rep Ω W)
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
  obtain ⟨za, hza⟩ := c.hΩ.exists_uniqueInvolution (rep a).hK
  obtain ⟨u, huRW, hu4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four c.hΩ c.hW (rep P).hR
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

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_fourth
    (hclC :
    Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) (ρ₁ ρ₂ ρ₃ : Rep Ω W)
    (h₁₂ : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (h₁₃ : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h₂₃ : ρ₃.K ∈ omegaNbr Ω ρ₂.K) {z₁ z₂ z₃ : G} (hz₁ : IsUniqueInvolution ρ₁.K z₁)
    (hz₂ : IsUniqueInvolution ρ₂.K z₂) (hz₃ : IsUniqueInvolution ρ₃.K z₃) :
    ∃ ρ₄ : Rep Ω W, ρ₄.K ≠ ρ₁.K ∧ ρ₄.K ≠ ρ₂.K ∧ ρ₄.K ≠ ρ₃.K ∧ ρ₄.K ∈ omegaNbr Ω ρ₁.K ∧
      ρ₄.K ∈ omegaNbr Ω ρ₂.K ∧ ρ₄.K ∈ omegaNbr Ω ρ₃.K ∧
        ∀ z₄, IsUniqueInvolution ρ₄.K z₄ → z₁ * z₂ * z₃ * z₄ = 1 := by
  classical
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    Q3T8.Asc77.Thompson.isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    Q3T8.Asc77.Thompson.isStar_muDelta c.hΩ c.hW (Q3T8.Asc77.thompsonStar G Ω hP W c.hW)
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
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := Q3T8.Asc77.Thompson.exists_not_conn_of_not_connected c.hΩ c.hW
      hnc
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
    rcases Q3T8.Asc77.thompsonClique G Ω hP W c.hW hnc x₁ hx₁Δ with h | h | ⟨h, -⟩
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
  obtain ⟨zP, hzP⟩ := c.hΩ.exists_uniqueInvolution (rep P).hK
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
    c.hΩ.exists_uniqueInvolution (rep x).hK
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
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}
end Frame
end Asc77

end

section

namespace Asc77.T7H
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7H
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem eq_of_toBar_eq
    {x y : G} (hx : x ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c) (hy : y ∈
    Q3T8.Asc77.ExactLayer.exactLayer Ω c)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (h : Q3T8.Asc77.T7H.toBar Ω c x hx = Q3T8.Asc77.T7H.toBar Ω c y hy) : x = y := by
  have hw : (⟨x, hx⟩ : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c))⁻¹ * ⟨y, hy⟩ ∈
      classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) := QuotientGroup.eq.mp h
  have hw2 : ((⟨x, hx⟩ : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c))⁻¹ * ⟨y, hy⟩) *
      ((⟨x, hx⟩ : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c))⁻¹ * ⟨y, hy⟩) = 1 := by
    apply Subtype.ext
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    show (x⁻¹ * y) * (x⁻¹ * y) = 1
    rw [hxi]
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, mul_one]
  have := eq_one_of_mem_odd_of_sq (CFSG.ComponentClassification.OddCore.odd_card _) hw hw2
  have h1 : x⁻¹ * y = 1 := congrArg Subtype.val this
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [hxi] at h1
  exact (inv_eq_of_mul_eq_one_right h1 : x⁻¹ = y).symm.trans hxi |>.symm
end Asc77.T7H

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.ModelFacts.Orth15
section E4
end E4
section Main
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twin_section_dichotomy {n : ℕ} (hBelow : Q3T8.Generic.CITBelowU n)
    (hlt : Nat.card X < n) (hS : Q3T8.Asc77.GenSection Φ) {A A' : Subgroup X} {z : X}
    (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hne : A ≠ A')
    (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (haA' : ∀ x ∈ A', ∃ n ∈ oddCoreOf A', a * ι x * a⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) : ∀ B ∈ Φ, IsUniqueInvolution B z := by
  classical
  have hΦ : Q3T7M.HM Φ := hS.hyp
  by_cases hconn : DConnected Φ
  · have hpath : ∀ N, Relation.ReflTransGen
        (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N → N ∈ Φ ∧ IsUniqueInvolution N z := by
      intro N hN
      induction hN with
      | refl => exact ⟨hA, hzA⟩
      | tail hpre hstep ih =>
        rename_i M N'
        obtain ⟨hN'Φ, hadj⟩ := hstep
        obtain ⟨hMΦ, hzM⟩ := ih
        refine ⟨hN'Φ, ?_⟩
        rcases hadj with h | h
        · obtain ⟨w, hw1, hw2⟩ :=
            hstar M hMΦ N' hN'Φ (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΦ M h)
          have := hzM.eq hw1
          subst this
          exact hw2
        · obtain ⟨w, hw1, hw2⟩ :=
            hstar N' hN'Φ M hMΦ (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΦ N' h)
          have := hzM.eq hw2
          subst this
          exact hw1
    intro B hB
    exact (hpath B (hconn A hA B hB)).2
  · exfalso
    have hNE : ¬ DEdgeless Φ := by
      intro h
      rcases CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΦ hA hA' hzA hzA' with h' | h'
      · exact hne h'
      · exact h _ hA' _ hA (Or.inl h')
    obtain ⟨d, ε, hd5, hd8, t', n', hortag, D, hcard, i, htag, hrank⟩ :=
      Q3T8.Asc77.thm8SectBelow'_of_citBelow hBelow X hlt Φ hS
        ⟨_, hA⟩ hNE hconn
    have hsix : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
        (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4) := by
      rw [htag, hrank]
      rcases hortag with ⟨-, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨hd7, hodd, ht, hn⟩ |
        ⟨hd8', hev, -, ht, hn⟩ | ⟨hd8', hev, -, ht, hn⟩
      · exact Or.inl ⟨ht, hn⟩
      · exact Or.inr (Or.inl ⟨ht, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))))
    have htrans : Q3T8.Asc77.TransSection Φ := by
      rcases Q3T8.Asc77.transSection_or_dConnected (Uniform.thm4BelowU_of_citBelowT hBelow) hlt hS
          with h | h
      · exact absurd h hconn
      · exact h
    have htop : (⊤ : Subgroup X) ∉ Φ := top_notMem_of_transitive htrans.trans hA hA' hne.symm
    have hL : HasLieType 3 1 Φ (D.tag i) (D.rank i) := ⟨D, hcard, i, rfl, rfl⟩
    have hshape := Q3T8.Asc77.MuTab.kindShape_of_shapes htrans ⟨A, hA⟩ hL hsix
    have hdcd : ∀ K ∈ Φ, dComp Φ K = dstarComp Φ K := by
      intro K hK
      refine Set.Subset.antisymm (Q3T8.Asc77.Thompson.dComp_subset_dstarComp hΦ K) ?_
      intro J hJ
      have hJ' : Relation.ReflTransGen (dstarAdj Φ) K J := hJ
      have key : ∀ N, Relation.ReflTransGen (dstarAdj Φ) K N → N ∈ Φ ∧
          Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) K N := by
        intro N hN
        induction hN with
        | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
        | tail hpre hstep ih =>
          rename_i M N'
          obtain ⟨hN'Φ, hadj⟩ := hstep
          obtain ⟨hMΦ, hMc⟩ := ih
          refine ⟨hN'Φ, ?_⟩
          rcases hadj with h | h
          · obtain ⟨w, hw1, hw2⟩ := hstar M hMΦ N' hN'Φ h
            rcases CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΦ hN'Φ hMΦ hw2 hw1 with h'
                | h'
            · rw [h']
              exact hMc
            · exact hMc.tail ⟨hN'Φ, Or.inl h'⟩
          · obtain ⟨w, hw1, hw2⟩ := hstar N' hN'Φ M hMΦ h
            rcases CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΦ hMΦ hN'Φ hw2 hw1 with h'
                | h'
            · rw [← h']
              exact hMc
            · exact hMc.tail ⟨hN'Φ, Or.inr h'⟩
      exact (key J hJ').2
    have hbad : ¬ ∃ K ∈ Φ, dComp Φ K ≠ dstarComp Φ K := fun ⟨K, hK, h⟩ => h (hdcd K hK)
    have hvac : ((D.tag i = .PSp ∧ D.rank i = 2) ∨
        (D.tag i = .PSL ∧ D.rank i = 4 ∧ 3 % 4 = 3) ∨
        (D.tag i = .PSU ∧ D.rank i = 4 ∧ 3 % 4 = 1)) → False := by
      intro hE4
      have hG2 : D.tag i ≠ .G2 := by
        rcases hE4 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
      have hD4 : D.tag i ≠ .trialityD4 := by
        rcases hE4 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
      have hexp : D.exp i = 1 := (D.exp_eq i).resolve_right fun h => hD4 h.1
      have hΦex : Q3T8.Asc77.HypOmega Φ := Q3T8.Sect.hypOmega_of_modU_exact hΦ
          (Q3T8.Asc77.OmegaLie.exactMembers hΦ D)
      have hsurj : Function.Surjective (D.hom i) := D.hom_surjective_of_gen hcard hS.gen i
      obtain ⟨j, R, hRf, hAR⟩ := D.fundamental A hA
      obtain ⟨j', R', hR'f, hAR'⟩ := D.fundamental A' hA'
      have hsub : Subsingleton (Fin D.card) := by
        rw [hcard]
        infer_instance
      obtain rfl : i = j := Subsingleton.elim _ _
      obtain rfl : i = j' := Subsingleton.elim _ _
      have hKΦ : R.map (D.hom i) ∈ Φ := by rw [← hAR]; exact hA
      have hK'Φ : R'.map (D.hom i) ∈ Φ := by rw [← hAR']; exact hA'
      have hzK : IsUniqueInvolution (R.map (D.hom i)) z := by rw [← hAR]; exact hzA
      have hzK' : IsUniqueInvolution (R'.map (D.hom i)) z := by rw [← hAR']; exact hzA'
      have hneR : R.map (D.hom i) ≠ R'.map (D.hom i) := by rw [← hAR, ← hAR']; exact hne
      obtain ⟨hRR', hcomm, x, hx, x', hx', hx2, hx1, hx'2, hx'1, hψx, hψx'⟩ :=
        Q3T8.Asc77.twinShape_of_twin hΦex D hcard hS.gen i hG2 hD4 hRf hR'f hKΦ hK'Φ hzK hzK' hneR
      let ψ' : (modelUniv (D.tag i) (D.rank i) 3 (D.exp i) Fact.out).K →* H :=
        ι.comp (D.hom i)
      have hpair : TwinPairOn (D.tag i) (modelUniv (D.tag i) (D.rank i) 3 (D.exp i) Fact.out)
          ψ' R R' x x' :=
        { ker := by
            intro y hy
            apply D.ker_le_center i
            rw [MonoidHom.mem_ker] at hy ⊢
            refine hι ?_
            rw [map_one]
            exact hy
          mem := hRf
          mem' := hR'f
          ne := hRR'
          comm := hcomm
          hx := hx
          hx2 := hx2
          hx1 := hx1
          hx' := hx'
          hx'2 := hx'2
          hx'1 := hx'1
          same := by simp only [ψ', MonoidHom.comp_apply, hψx, hψx'] }
      have hrange : ψ'.range = ι.range := by
        ext y
        simp only [ψ', MonoidHom.mem_range, MonoidHom.comp_apply]
        constructor
        · rintro ⟨s, rfl⟩
          exact ⟨_, rfl⟩
        · rintro ⟨x, rfl⟩
          obtain ⟨s, rfl⟩ := hsurj x
          exact ⟨s, rfl⟩
      have hn : a ∈ Subgroup.normalizer (ψ'.range : Set H) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [hrange]
        constructor
        · rintro ⟨x, rfl⟩
          exact (ha x).1
        · intro hy
          obtain ⟨x, hx⟩ := hy
          obtain ⟨y', hy'⟩ := (ha x).2
          have : y = a⁻¹ * ι x * a := by
            rw [hx]
            group
          rw [this]
          exact (ha x).2
      let v : ↥(inducedAutOn ψ'.range) := toInducedAutOn ψ'.range ⟨a, hn⟩
      have hexc : ∀ {B : Subgroup X}, B ∈ Φ →
          (∀ x ∈ B, ∃ n ∈ oddCoreOf B, a * ι x * a⁻¹ = ι (n * x)) →
          ∀ x ∈ B, a * ι x = ι x * a := by
        intro B hB hh x hx
        obtain ⟨n, hn, hnx⟩ := hh x hx
        rw [oddCoreOf_eq_bot_of_exact hΦex.exact hB, Subgroup.mem_bot] at hn
        rw [hn, one_mul] at hnx
        calc a * ι x = (a * ι x * a⁻¹) * a := by group
          _ = ι x * a := by rw [hnx]
      have hψ'A : ∀ r ∈ R, ψ' r ∈ ι '' (A : Set X) := by
        intro r hr
        refine ⟨D.hom i r, ?_, rfl⟩
        rw [hAR]
        exact Subgroup.mem_map_of_mem _ hr
      have hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ' r = FrameVertex.innerHom ψ' r * v := by
        intro r hr
        obtain ⟨s, hs, hsr⟩ := hψ'A r hr
        rw [FrameVertex.innerHom_apply, ← map_mul, ← map_mul]
        congr 1
        refine Subtype.ext ?_
        show a * ψ' r = ψ' r * a
        rw [← hsr]
        exact hexc hA haA s hs
      have hψ'A' : ∀ r ∈ R', ψ' r ∈ ι '' (A' : Set X) := by
        intro r hr
        refine ⟨D.hom i r, ?_, rfl⟩
        rw [hAR']
        exact Subgroup.mem_map_of_mem _ hr
      have hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ' r = FrameVertex.innerHom ψ' r * v := by
        intro r hr
        obtain ⟨s, hs, hsr⟩ := hψ'A' r hr
        rw [FrameVertex.innerHom_apply, ← map_mul, ← map_mul]
        congr 1
        refine Subtype.ext ?_
        show a * ψ' r = ψ' r * a
        rw [← hsr]
        exact hexc hA' haA' s hs
      have hvv : v * v = FrameVertex.innerHom ψ' x := by
        rw [FrameVertex.innerHom_apply, ← map_mul]
        congr 1
        refine Subtype.ext ?_
        show a * a = ψ' x
        simp only [ψ', MonoidHom.comp_apply, hψx]
        exact ha2
      have hE4' : (D.tag i = .PSp ∧ D.rank i = 2) ∨
          (D.tag i = .PSL ∧ D.rank i = 4 ∧ 3 ^ D.exp i % 4 = 3) ∨
          (D.tag i = .PSU ∧ D.rank i = 4 ∧ 3 ^ D.exp i % 4 = 1) := by
        rw [hexp]
        exact hE4
      exact Q3T8.Asc77.S22.noV_of_e4 (D.tag i) (D.rank i) (D.exp i) hexp (D.admissible i) hE4' ψ' R
          R' x x'
        hpair v hvR hvR' hvv
    rcases hsix with ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩
    · exact hvac (Or.inl ⟨ht, hk⟩)
    · by_cases hπ : piSign 3 1 = true
      · have h4 : MuTab.KindShape Φ .s4 := by
          have := hshape
          rw [ht, hk, hπ] at this
          simpa [MuTab.muKind] using this
        exact hbad h4.2.2
      · have hπf : piSign 3 1 = false := by simpa using hπ
        exact hvac (Or.inr (Or.inl ⟨ht, hk, MuTab.pow_mod_four_of_piSign_false (by norm_num) hπf⟩))
    · by_cases hπ : piSign 3 1 = true
      · exact hvac (Or.inr (Or.inr ⟨ht, hk, MuTab.piSign_true_iff.mp hπ⟩))
      · have hπf : piSign 3 1 = false := by simpa using hπ
        have h4 : MuTab.KindShape Φ .s4 := by
          have := hshape
          rw [ht, hk, hπf] at this
          simpa [MuTab.muKind] using this
        exact hbad h4.2.2
    · have h4 : MuTab.KindShape Φ .s4 := by
        have := hshape
        rw [ht, hk] at this
        simpa [MuTab.muKind] using this
      exact hbad h4.2.2
    · have h4 : MuTab.KindShape Φ .wyl := by
        have := hshape
        rw [ht, hk] at this
        simpa [MuTab.muKind] using this
      exact hbad h4.2.2
    · have h4 : MuTab.KindShape Φ .s4 := by
        have := hshape
        rw [ht, hk] at this
        simpa [MuTab.muKind] using this
      exact hbad h4.2.2
end Main
end S22
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
