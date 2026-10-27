module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AResid
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut)
open CFSG.LocalAnalysis.GLTheoremA.S172 CFSG.LocalAnalysis.GLTheoremA

theorem exists_partner {n r : ℕ} (hn : n = 2 * r + 1) (hr : 3 ≤ r) {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} {x : Ω} (Θ : VecAut n →* Ω) (φ : ↥B →* VecAut n)
    (hΘ : Function.Injective Θ) (hΘS : Θ.range = S)
    (hconj : ∀ (b : ↥B) (g : VecAut n), (b : Ω) * Θ g * (b : Ω)⁻¹ = Θ (φ b * g * (φ b)⁻¹))
    (hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x)
    (hBel : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hcard : 3 ^ r ≤ Nat.card φ.range) :
    ∃ D₁ K₁ : Subgroup Ω, GLAStdSubPre 3 B x S D₁ K₁ ∧
      catalogIs (PSimple 3 K₁) (isLnA (n - 2) 2) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV : Module.finrank (ZMod 2) (Fin n → ZMod 2) = 2 * r + 1 := by
    rw [Module.finrank_fin_fun, hn]
  have hEel := isElemAbelian_range φ hBel
  obtain ⟨e₀, he₀E, h3, hfr⟩ := GL.exists_oneBlock (V := Fin n → ZMod 2) hEel hV (by omega) hcard
  obtain ⟨b₀, hb₀⟩ := he₀E
  have he₀1 : e₀ ≠ 1 := by
    intro h
    rw [h] at hfr
    have : GL.comSp (1 : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) = ⊥ := by
      rw [GL.comSp, LinearMap.range_eq_bot]
      ext v
      simp [GL.ds]
    rw [this] at hfr
    simp at hfr
  have hord : orderOf e₀ = 3 := orderOf_eq_prime h3 he₀1
  have hNC : GL.Nsub h3 ≤ Subgroup.centralizer ({e₀} : Set (VecAut n)) := GL.Nsub_le_cent h3
  let Z : Subgroup (VecAut n) := Subgroup.zpowers e₀
  have hZR : Z ≤ φ.range := Subgroup.zpowers_le.2 ⟨b₀, hb₀⟩
  let D₁ : Subgroup Ω := (Z.comap φ).map B.subtype
  let K₁ : Subgroup Ω := (GL.Nsub h3).map Θ
  have hmemD : ∀ b : Ω, b ∈ D₁ ↔ ∃ c : ↥B, φ c ∈ Z ∧ (c : Ω) = b := by
    intro b
    simp only [D₁, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
  have hZN : ∀ z ∈ Z, ∀ g ∈ GL.Nsub h3, z * g = g * z := by
    intro z hz g hg
    obtain ⟨k, rfl⟩ := hz
    have hge : g * e₀ = e₀ * g := Subgroup.mem_centralizer_singleton_iff.1 (hNC hg)
    exact ((Commute.zpow_left (show Commute e₀ g from hge.symm) k).eq)
  have hcentD₁ : S ⊓ Subgroup.centralizer (D₁ : Set Ω) =
      (Subgroup.centralizer ({e₀} : Set (VecAut n))).map Θ := by
    ext y
    constructor
    · rintro ⟨hyS, hyc⟩
      rw [← hΘS] at hyS
      obtain ⟨g, rfl⟩ := hyS
      refine ⟨g, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hb₀D : (b₀ : Ω) ∈ D₁ :=
        (hmemD _).2 ⟨b₀, by rw [hb₀]; exact Subgroup.mem_zpowers e₀, rfl⟩
      have h1 := (Subgroup.mem_centralizer_iff.1 hyc) _ hb₀D
      have h2 := hconj b₀ g
      rw [hb₀] at h2
      have h4 : (b₀ : Ω) * Θ g * (b₀ : Ω)⁻¹ = Θ g := by rw [h1, mul_inv_cancel_right]
      have h5 : g = e₀ * g * e₀⁻¹ := hΘ (h4.symm.trans h2)
      rw [eq_mul_inv_iff_mul_eq] at h5
      exact h5
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hΘS]; exact ⟨g, rfl⟩
      · refine Subgroup.mem_centralizer_iff.2 ?_
        intro d hd
        obtain ⟨c, hcZ, rfl⟩ := (hmemD d).1 hd
        have hge : g * e₀ = e₀ * g := Subgroup.mem_centralizer_singleton_iff.1 hg
        obtain ⟨k, hk⟩ := hcZ
        have hcomm : φ c * g = g * φ c := by
          rw [← hk]
          exact ((Commute.zpow_left (show Commute e₀ g from hge.symm) k).eq)
        have h2 := hconj c g
        have h4 : Θ (φ c * g * (φ c)⁻¹) = Θ g := by
          rw [hcomm, mul_inv_cancel_right]
        rw [h4, mul_inv_eq_iff_eq_mul] at h2
        exact h2
  have hDeq : D₁ = B ⊓ Subgroup.centralizer (K₁ : Set Ω) := by
    ext b
    constructor
    · intro hb
      obtain ⟨c, hcZ, rfl⟩ := (hmemD b).1 hb
      refine ⟨c.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨n', hn', rfl⟩
      have hcomm := hZN _ hcZ n' hn'
      have h2 := hconj c n'
      have h4 : Θ (φ c * n' * (φ c)⁻¹) = Θ n' := by
        rw [hcomm, mul_inv_cancel_right]
      rw [h4, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · rintro ⟨hbB, hbc⟩
      refine (hmemD b).2 ⟨⟨b, hbB⟩, ?_, rfl⟩
      have hEcomm : ∀ e₁ ∈ φ.range, ∀ e₂ ∈ φ.range, e₁ * e₂ = e₂ * e₁ := fun e₁ he₁ e₂ he₂ =>
        congrArg Subtype.val (hEel.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
      refine GL.cent_Nsub_le_zpowers hV hr h3 hfr ?_ ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hEcomm _ ⟨⟨b, hbB⟩, rfl⟩ _ ⟨b₀, hb₀⟩
      · intro h hh
        have hcb := (Subgroup.mem_centralizer_iff.1 hbc) (Θ h) ⟨h, hh, rfl⟩
        have h2 := hconj ⟨b, hbB⟩ h
        have h4 : (b : Ω) * Θ h * (b : Ω)⁻¹ = Θ h := by rw [← hcb, mul_inv_cancel_right]
        have h5 : h = φ ⟨b, hbB⟩ * h * (φ ⟨b, hbB⟩)⁻¹ := hΘ (h4.symm.trans h2)
        rw [eq_mul_inv_iff_mul_eq] at h5
        exact h5.symm
  have hNq : CFSG.Open.IsQuasisimple ↥(GL.Nsub h3) := GL.Nsub_isQuasisimple hV hr h3 hfr
  have hle : K₁ ≤ (Subgroup.centralizer ({e₀} : Set (VecAut n))).map Θ := Subgroup.map_mono hNC
  have hnorm : (K₁.subgroupOf ((Subgroup.centralizer ({e₀} : Set (VecAut n))).map Θ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h g hh hg
    obtain ⟨n', hn', rfl⟩ := hh
    obtain ⟨c, hc, rfl⟩ := hg
    have hn'' : c * n' * c⁻¹ ∈ GL.Nsub h3 :=
      (Subgroup.normal_subgroupOf_iff hNC).1 (GL.Nsub_normal h3) n' c hn' hc
    exact ⟨c * n' * c⁻¹, hn'', by simp [map_mul, map_inv]⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K₁ :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (GL.Nsub h3) Θ hΘ) hNq
  have hcomm : ⁅(Subgroup.centralizer ({e₀} : Set (VecAut n))).map Θ,
      (Subgroup.centralizer ({e₀} : Set (VecAut n))).map Θ⁆ ≤ K₁ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (GL.comm_le_Nsub h3 hfr)
  have hlay := layer_eq_of_normal_quasisimple hle hnorm hKq hcomm
  have hDB : D₁ ≤ B := Subgroup.map_subtype_le _
  have hDel : IsElemAbelian 3 D₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hBel.2 y (hDB hy)⟩
    exact Subtype.ext (congrArg (Subtype.val : ↥B → Ω) (hBel.1.is_comm.comm ⟨a.1, hDB a.2⟩ ⟨b.1, hDB b.2⟩))
  have hDcard : Nat.card D₁ = 3 ^ 2 := by
    have h1 : Nat.card D₁ = Nat.card (Z.comap φ) :=
      Subgroup.card_map_of_injective (f := B.subtype) Subtype.val_injective
    rw [h1, card_comap_eq φ Z hZR, card_ker_eq_three φ hker hBel hxB hx1, Nat.card_zpowers, hord]
    norm_num
  have hxD : x ∈ D₁ :=
    (hmemD x).2 ⟨⟨x, hxB⟩, by rw [(hker _).2 (Subgroup.mem_zpowers x)]; exact Z.one_mem, rfl⟩
  refine ⟨D₁, K₁, ⟨hDB, hDel, hDcard, hxD, ?_, ?_, hDeq⟩, ?_⟩
  · rw [hcentD₁]; exact hlay.2.symm
  · rw [hcentD₁]; exact hlay.1
  ·
    have eN := GL.NsubEquiv hV h3 hfr
    have eK : ↥K₁ ≃* ↥(GL.Nsub h3) := (Subgroup.equivMapOfInjective (GL.Nsub h3) Θ hΘ).symm
    obtain ⟨hs, hnab⟩ := GL.Nsub_simple_nonab hV hr h3 hfr
    have hKsn := GL.simple_nonab_of_equiv eK ⟨hs, hnab⟩
    haveI := hKsn.1
    have hKZ : Subgroup.center ↥K₁ = ⊥ := GL.center_eq_bot_of_simple_nonab hKsn.2
    have hK3 : 3 ∣ Nat.card ↥K₁ := by
      rw [Nat.card_congr eK.toEquiv]
      exact GL.three_dvd_card_Nsub hV hr h3 hfr
    obtain ⟨eP⟩ := pSimple_equiv hKq hKZ hK3
    have hn2 : n - 2 = 2 * r - 1 := by omega
    rw [hn2]
    exact catalogIs_isLnA_of_vecAut (by omega) (eP.trans (eK.trans eN))


theorem s172AExist_holds :
    S172AExist := by
  intro n hn hn7 Ω _ _ S B D K x hcfg hS _
  obtain ⟨r, hr⟩ := hn
  have hr3 : 3 ≤ r := by omega
  haveI : S.Normal := hcfg.normal
  obtain ⟨hZ, ⟨θ⟩, hin⟩ := exists_theta (n := n) (by omega) hcfg.qs hS
  obtain ⟨Θ, φ, hΘ, hΘS, hconj, hker'⟩ :=
    exists_action (B := B) (fun b hb => hcfg.elem.2 b hb) hZ θ hin
  have hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x := by
    intro b
    rw [hker', ← hcfg.cent b b.2, Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      exact (h s hs).symm
    · intro h s hs
      exact (h s hs).symm
  have hxS : ∀ g : VecAut n, x * Θ g = Θ g * x := by
    intro g
    have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
      (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
    have hg : Θ g ∈ S := by rw [← hΘS]; exact ⟨g, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.1 hxc) _ hg).symm
  have hZ' : Subgroup.center (VecAut n) = ⊥ := by
    rw [← Subgroup.map_center_eq θ, hZ, Subgroup.map_bot]
  have hcard := card_range_ge (n := n) (r := r) hr hr3 Θ φ hΘ hker hcfg.elem hcfg.mem
    hcfg.ne_one hxS hZ' hcfg.rank
  exact exists_partner hr hr3 Θ φ hΘ hΘS hconj hker hcfg.elem hcfg.mem hcfg.ne_one hcard


end CFSG.LocalAnalysis.GLTheoremA.S172A

end
