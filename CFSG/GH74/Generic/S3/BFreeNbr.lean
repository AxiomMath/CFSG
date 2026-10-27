module

public import CFSG.GH74.Generic.S3.NoFus2
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.Generic.S3.NoOutMain
public import CFSG.GH74.Generic.S3.NbrComp

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Filter.ClassicalOdd (Q8)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem normalizerAct_apply_mk coe_conjOn
  mem_centralizer_of_normalizerAct_eq_one)

section Main

variable {G : Type} [Group G] [Finite G]

theorem noFusionAt_of_nbrComp {x : G} {K : Subgroup (CentralizerBar x)} (hN : NbrCompAt x K)
    (hset : S3Setup G x K) (honly : OnlyInvX x K) (hLy : LyAt x K) : NoFusionAt x K := by
  intro t p f y Iw Iv hnd himg _ ⟨g, hg⟩
  classical
  have hx2 := hnd.x_sq
  have hy2 := hnd.y_sq
  have hp := hnd.prime.1
  have hp2 := hnd.prime.2.1
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hIv : IsCompC Iv y := hN t p f y Iw Iv hnd himg (hLy t p f y Iw Iv hnd himg)
  have hcomm : ∀ i ∈ Iv, ∀ b ∈ Iw, (g⁻¹ * i * g) * b = b * (g⁻¹ * i * g) :=
    hnd.commute_conj_Iv hIv hg
  have hconjx : ∀ i ∈ Iv, (g⁻¹ * i * g) * x = x * (g⁻¹ * i * g) := by
    intro i hi
    have hiy : i * y = y * i := hnd.Iv_central i hi
    have hxg : x = g⁻¹ * y * g := by rw [← hg]; group
    calc (g⁻¹ * i * g) * x = g⁻¹ * (i * y) * g := by rw [hxg]; group
      _ = g⁻¹ * (y * i) * g := by rw [hiy]
      _ = x * (g⁻¹ * i * g) := by rw [hxg]; group
  obtain ⟨F, hFfld, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have hV : CFSG.GH74.GLS.HasSL2Model ↥Iv (fun q' => q' = p ^ f) :=
    ⟨F, hFfld, hFfin, hF, ⟨e.symm.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩
  obtain ⟨ψ₀, hψ₀, hψ₀V⟩ := CFSG.GH74.Generic.S1.exists_q8_of_hasSL2Model hqodd hV
  let ψ : Q8 →* G := (MulAut.conj g⁻¹).toMonoidHom.comp ψ₀
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp hψ₀
  have hψapp : ∀ a, ψ a = g⁻¹ * ψ₀ a * g := fun a => by simp [ψ]
  have hψx : ∀ a, ψ a ∈ centralizer ({x} : Set G) := fun a => by
    rw [Subgroup.mem_centralizer_singleton_iff, hψapp]
    exact hconjx _ (hψ₀V a)
  have hψc : ∀ a, ∀ b ∈ Iw, ψ a * b = b * ψ a := fun a b hb => by
    rw [hψapp]
    exact hcomm _ (hψ₀V a) b hb
  have hmod4 := hnd.mod_four_of_quaternion hset himg ψ hψ hψx hψc
  have hlib : LibData t p f := by
    rcases hmod4 with ⟨rfl, h3⟩ | ⟨rfl, h1⟩
    · exact libData_lin hp hp2 hnd.prime.2.2 h3
    · exact libData_uni hp hp2 hnd.prime.2.2
  obtain ⟨S, hS⟩ := hnd.exists_S hlib
  have himgS := hnd.image_Iv hS
  have hX : StatedClassicalModel (↥Iw ⧸ center ↥Iw) t 3 p f := by
    rcases hnd.tag with rfl | rfl
    · exact stated_of_lieModel_PSL hnd.model_w
    · exact stated_of_lieModel_PSU hnd.model_w
  set x₁ : G := g⁻¹ * x * g with hx₁
  have hx₁sq : x₁ * x₁ = 1 := by
    calc x₁ * x₁ = g⁻¹ * (x * x) * g := by rw [hx₁]; group
      _ = 1 := by rw [hx2]; group
  have hx₁C : x₁ ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : x₁ * x = g⁻¹ * (x * y) * g := by rw [← hg]; simp only [hx₁]; group
    have e2 : x * x₁ = g⁻¹ * (y * x) * g := by rw [← hg]; simp only [hx₁]; group
    rw [e1, e2, hnd.comm]
  have hx₁N : ∀ i ∈ Iw, x₁ * i * x₁⁻¹ ∈ Iw := hnd.comp_w.conj x₁ hx₁C
  have heven : 2 ∣ Nat.card ↥Iw := by
    have h1 : orderOf (⟨y, hnd.y_Iw⟩ : ↥Iw) ∣ Nat.card ↥Iw := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hnd.y_inv] at h1
  have hxIw := hnd.x_notin_Iw
  have hxcIw : ∀ b ∈ Iw, b * x = x * b := fun b hb =>
    mem_centralizer_singleton_iff.1 (hnd.Iw_le hb)
  have hkey : ∃ c₁ ∈ Iw, c₁ * c₁ = 1 ∧ c₁ ≠ 1 ∧ c₁ * x₁ = x₁ * c₁ ∧ c₁ ≠ x₁ ∧ c₁ ≠ x₁ * x := by
    obtain ⟨c₁, hc₁Iw, hc₁2, hc₁1, hc₁c⟩ := exists_involution_mem_centralizer hx₁sq hx₁N heven
    by_cases hbad : c₁ = x₁ ∨ c₁ = x₁ * x
    · obtain ⟨b, hb2, hb1, hba, hbc⟩ := exists_involution_comm_ne (L := ↥Iw) hnd.tag hp2 hnd.odd_w hX
        (a := ⟨c₁, hc₁Iw⟩) (Subtype.ext hc₁2) (fun h => hc₁1 (congrArg Subtype.val h))
      have hbc' : (b : G) * c₁ = c₁ * (b : G) := congrArg Subtype.val hbc
      have hbx := hxcIw b b.2
      have hbne : (b : G) ≠ c₁ := fun h => hba (Subtype.ext h)
      refine ⟨(b : G), b.2, congrArg Subtype.val hb2, fun h => hb1 (Subtype.ext h), ?_, ?_, ?_⟩
      · rcases hbad with h | h
        · rw [← h]; exact hbc'
        · have hx₁eq : x₁ = c₁ * x := by rw [h, mul_assoc, hx2, mul_one]
          rw [hx₁eq, ← mul_assoc, hbc', mul_assoc, hbx, ← mul_assoc]
      · intro h
        rcases hbad with h' | h'
        · exact hbne (h.trans h'.symm)
        · apply hxIw
          have hx₁Iw : x₁ ∈ Iw := h ▸ b.2
          have : x₁ * x ∈ Iw := h' ▸ hc₁Iw
          have := Iw.mul_mem (Iw.inv_mem hx₁Iw) this
          rwa [inv_mul_cancel_left] at this
      · intro h
        rcases hbad with h' | h'
        · apply hxIw
          have hx₁Iw : x₁ ∈ Iw := h' ▸ hc₁Iw
          have : x₁ * x ∈ Iw := h ▸ b.2
          have := Iw.mul_mem (Iw.inv_mem hx₁Iw) this
          rwa [inv_mul_cancel_left] at this
        · exact hbne (h.trans h'.symm)
    · push Not at hbad
      exact ⟨c₁, hc₁Iw, hc₁2, hc₁1, hc₁c, hbad.1, hbad.2⟩
  obtain ⟨c₁, hc₁Iw, hc₁2, hc₁1, hc₁x₁, hc₁ne, hc₁ne'⟩ := hkey
  set c : G := g * c₁ * g⁻¹ with hc
  have hc2 : c * c = 1 := by
    calc c * c = g * (c₁ * c₁) * g⁻¹ := by rw [hc]; group
      _ = 1 := by rw [hc₁2]; group
  have hcx : c * x = x * c := by
    have h1 : c₁ * x₁ = x₁ * c₁ := hc₁x₁
    calc c * x = g * (c₁ * x₁) * g⁻¹ := by rw [hc, hx₁]; group
      _ = g * (x₁ * c₁) * g⁻¹ := by rw [h1]
      _ = x * c := by rw [hc, hx₁]; group
  have hcy : c * y = y * c := by
    have h1 : c₁ * x = x * c₁ := hxcIw c₁ hc₁Iw
    calc c * y = g * (c₁ * x) * g⁻¹ := by rw [hc, ← hg]; group
      _ = g * (x * c₁) * g⁻¹ := by rw [h1]
      _ = y * c := by rw [hc, ← hg]; group
  have hcIv : ∀ i ∈ Iv, i * c = c * i := by
    intro i hi
    have h1 := hcomm i hi c₁ hc₁Iw
    calc i * c = g * ((g⁻¹ * i * g) * c₁) * g⁻¹ := by rw [hc]; group
      _ = g * (c₁ * (g⁻¹ * i * g)) * g⁻¹ := by rw [h1]
      _ = c * i := by rw [hc]; group
  have hcxne : c ≠ x := by
    intro h
    apply hc₁ne
    calc c₁ = g⁻¹ * c * g := by rw [hc]; group
      _ = x₁ := by rw [h]
  have hcyne : c ≠ y := by
    intro h
    apply hxIw
    have : c₁ = x := by
      calc c₁ = g⁻¹ * c * g := by rw [hc]; group
        _ = g⁻¹ * y * g := by rw [h]
        _ = x := by rw [← hg]; group
    rw [← this]
    exact hc₁Iw
  have hcxyne : c ≠ x * y := by
    intro h
    apply hc₁ne'
    calc c₁ = g⁻¹ * c * g := by rw [hc]; group
      _ = g⁻¹ * (x * y) * g := by rw [h]
      _ = x₁ * x := by rw [← hg]; simp only [hx₁]; group
  have : Group.IsPerfect ↥Iw := hnd.Iw_quasisimple.1
  have hcC : c ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hcx
  have hcN : c ∈ normalizer (Iw : Set G) := hnd.comp_w.le_normalizer hcC
  have hσ2 : normalizerAct Iw ⟨c, hcN⟩ * normalizerAct Iw ⟨c, hcN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨c, hcN⟩ : normalizer (Iw : Set G)) * ⟨c, hcN⟩ = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hσfix : ∀ s ∈ S, normalizerAct Iw ⟨c, hcN⟩ s = s := by
    intro s hs
    obtain ⟨i, hiIv, rfl⟩ := (himgS s).1 hs
    rw [normalizerAct_apply_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjOn]
    show c * (i : G) * c⁻¹ = i
    have := hcIv (i : G) hiIv
    calc c * (i : G) * c⁻¹ = (i * c) * c⁻¹ := by rw [this]
      _ = i := by group
  have hyN : y ∈ normalizer (Iw : Set G) := Subgroup.le_normalizer hnd.y_Iw
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  rcases hS.aut_fixing _ hσ2 hσfix with h | h
  · have hcI : c ∈ centralizer (Iw : Set G) := mem_centralizer_of_normalizerAct_eq_one Iw h
    rcases hnd.involution_cent_Iw honly himg hcC hcI hc2 with h1 | h1
    · exact hc₁1 (by
        calc c₁ = g⁻¹ * c * g := by rw [hc]; group
          _ = 1 := by rw [h1]; group)
    · exact hcxne h1
  · have h1 : normalizerAct Iw (⟨c, hcN⟩ * ⟨y, hyN⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h, normalizerAct_of_mem Iw hnd.y_Iw, mul_inv_cancel]
    have hcyI : c * y ∈ centralizer (Iw : Set G) := by
      have := mem_centralizer_of_normalizerAct_eq_one Iw h1
      simpa [hyinv] using this
    have hcyC : c * y ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem hcC (mem_centralizer_singleton_iff.2 hnd.comm)
    have hcy2 : (c * y) * (c * y) = 1 := by
      calc (c * y) * (c * y) = c * (y * c) * y := by group
        _ = c * (c * y) * y := by rw [← hcy]
        _ = (c * c) * (y * y) := by group
        _ = 1 := by rw [hc2, hy2, one_mul]
    rcases hnd.involution_cent_Iw honly himg hcyC hcyI hcy2 with h2 | h2
    · apply hcyne
      calc c = (c * y) * y⁻¹ := by group
        _ = y := by rw [h2, one_mul, hyinv]
    · apply hcxyne
      calc c = (c * y) * y⁻¹ := by group
        _ = x * y := by rw [h2, hyinv]

theorem b_S3_noFusionJNT_of_nbrComp (hN : B_S3_nbrComp) : B_S3_noFusionJNT :=
  fun G _ _ x K hset hmax hthin honly hLy =>
    noFusionAt_of_nbrComp (hN G x K hset hmax hthin honly) hset honly hLy

end Main

theorem b_S3_nontrivJNT_of_nbrComp (hN : B_S3_nbrComp) : B_S3_nontrivJNT :=
  b_S3_nontrivJNT_of_residues (b_S3_noFusionJNT_of_nbrComp hN)
    (b_S3_noOuterJNT_of_noFusion (b_S3_noFusionJNT_of_nbrComp hN))

end CFSG.GH74.Generic.S3
