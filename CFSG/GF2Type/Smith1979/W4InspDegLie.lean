module

public import CFSG.GF2Type.Smith1979.W4InspDefs
public import CFSG.GF2Type.Smith1979.W4InspOrd
public import CFSG.LargeExtraspecial.S12InspFamESp
public import CFSG.LargeExtraspecial.S12I4MMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.Setting
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

omit [IsSimpleGroup G] in
theorem fuseCert_of_sp_four (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hw : S.width = 4) (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t) {m : ℕ}
    (hm : 3 ≤ m) {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (φ : S.Xbar12 g ≃* S12InspSp.SpG b) (htX : t ∈ S.Xbar12 g) {v : Fin (2 * m) → ZMod 2}
    (hv0 : v ≠ 0) (hT : ∀ x, S12InspSp.act (φ ⟨t, htX⟩) x = x + b x v • v) :
    S.S12FuseCert g t := by
  have hXM := xbar12_eq_mbar_of_sp hS hm halt hnd φ
  have h4 : 4 < Fintype.card (Fin (2 * m)) := by rw [Fintype.card_fin]; omega
  set W := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hWdef
  set T := φ ⟨t, htX⟩ with hTdef
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : S12InspSp.SpG b →* S.O,
      ψ = (S.Xbar12 g).subtype.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hψ : ∀ (x : S.O) (hx : x ∈ S.Xbar12 g), ψ (φ ⟨x, hx⟩) = x := fun x hx => by
    rw [hψdef]
    simp
  have hψinj : Function.Injective ψ := by
    rw [hψdef]
    exact (S.Xbar12 g).subtype_injective.comp φ.symm.injective
  have hψT : ψ T = t := hψ t htX
  have hψX : ∀ c, ψ c ∈ S.Xbar12 g := fun c => by
    rw [hψdef]
    exact (φ.symm c).2
  have hψC : ∀ c ∈ centralizer {T}, ψ c * t = t * ψ c := fun c hc => by
    rw [← hψT, ← ψ.map_mul, ← ψ.map_mul, mem_centralizer_singleton_iff.mp hc]
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (S12InspSp.SpG b), N = (S.fixSub12 W).comap ψ := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup (S12InspSp.SpG b), L = (S.Lbar g).comap ψ := ⟨_, rfl⟩
  have hmemN : ∀ c, c ∈ N ↔ ψ c ∈ S.fixSub12 W := fun c => by rw [hNdef, Subgroup.mem_comap]
  have hmemL : ∀ c, c ∈ L ↔ ψ c ∈ S.Lbar g := fun c => by rw [hLdef, Subgroup.mem_comap]
  have hN : ∀ c ∈ centralizer {T}, ∀ n ∈ N, c * n * c⁻¹ ∈ N := fun c hc n hn => by
    rw [hmemN, ψ.map_mul, ψ.map_mul, ψ.map_inv]
    exact conj_mem_fixSub12 (hψC c hc) ((hmemN n).mp hn)
  have hP : ∀ c ∈ centralizer {T}, ∀ d ∈ centralizer {T}, c * c = 1 → d * d = 1 →
      c * d = d * c → c ∉ N → d ∉ N → c * d ∈ N := fun c hc d hd hc2 _ hcd hcN hdN => by
    rw [hmemN, ψ.map_mul]
    rw [hmemN] at hcN hdN
    exact mul_mem_fixSub12_of_commute htA (hψC c hc) (hψC d hd)
      (by rw [← ψ.map_mul, hc2, ψ.map_one]) (by rw [← ψ.map_mul, hcd, ψ.map_mul]) hcN hdN
  have haW : S.cl (g * S.z * g⁻¹) ∈ W := (S.timmesfeld_12_6 haQ hne ht htA).1
  have hNL : N ≤ normalizer (L : Set (S12InspSp.SpG b)) := fun n hn => by
    have hnM : ψ n ∈ S.Mbar := Xbar12_le_Mbar (hψX n)
    have hfix := (mem_fixSub12.mp ((hmemN n).mp hn)) _ haW
    have hnN := (mem_normalizer_Lbar_iff_fix haQ hne (by omega) hnM).mpr hfix
    rw [hLdef]
    exact s12_mem_normalizer_comap ψ hnN
  have hcommL : ∀ {x y : S.O}, x ∈ S.Lbar g → y ∈ S.Lbar g → x * y = y * x := fun hx hy =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hLC : L ≤ centralizer {T} := fun ℓ hℓ => by
    rw [mem_centralizer_singleton_iff]
    apply hψinj
    rw [ψ.map_mul, ψ.map_mul, hψT]
    exact hcommL ((hmemL ℓ).mp hℓ) ht
  have hL2 : IsPGroup 2 L := by
    have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
    intro ℓ
    refine ⟨1, Subtype.ext (hψinj ?_)⟩
    have h1 : ψ (ℓ : S12InspSp.SpG b) ^ 2 = 1 := by
      simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) _
        ((hmemL ℓ).mp ℓ.2)
    simpa using h1
  have hTL : T ∈ L := by rw [hmemL, hψT]; exact ht
  have hbig : ∃ ℓ ∈ L, ℓ ≠ 1 ∧ ℓ ≠ T := by
    obtain ⟨ℓ, hℓ, hℓ1, hℓt⟩ : ∃ ℓ ∈ S.Lbar g, ℓ ≠ 1 ∧ ℓ ≠ t := by
      by_contra h
      push Not at h
      have hle : S.Lbar g ≤ zpowers t := fun ℓ hℓ => by
        by_cases h1 : ℓ = 1
        · rw [h1]
          exact one_mem _
        · rw [h ℓ hℓ h1]
          exact mem_zpowers t
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at h1
      have h2 : orderOf t ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact Subtype.ext htA.2.2.1)
      have h3 := S.card_Lbar_ge haQ hne
      have h5 : 2 ^ 3 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hℓX : ℓ ∈ S.Xbar12 g := hXM ▸ S.Lbar_le_Mbar g hℓ
    refine ⟨φ ⟨ℓ, hℓX⟩, by rw [hmemL, hψ]; exact hℓ, fun h => hℓ1 ?_, fun h => hℓt ?_⟩
    · have := congrArg ψ h
      rwa [hψ, ψ.map_one] at this
    · have := congrArg ψ h
      rwa [hψ, hψT] at this
  have hcore := S12InspSp.centralizer_le_normalizer_of halt hnd h4 hv0 hT hN hP hNL hLC hL2 hTL
    hbig
  intro c hcM hct
  have hcX : c ∈ S.Xbar12 g := hXM ▸ hcM
  have hct' : c * t = t * c := by
    calc c * t = c * t * c⁻¹ * c := by group
      _ = t * c := by rw [hct]
  have hcC : φ ⟨c, hcX⟩ ∈ centralizer {T} := by
    rw [mem_centralizer_singleton_iff]
    apply hψinj
    rw [ψ.map_mul, ψ.map_mul, hψ, hψT]
    exact hct'
  have hcn := hcore hcC
  rw [mem_normalizer_iff]
  intro ℓ
  constructor
  · intro hℓ
    have hℓX : ℓ ∈ S.Xbar12 g := hXM ▸ S.Lbar_le_Mbar g hℓ
    have h1 : φ ⟨ℓ, hℓX⟩ ∈ L := by rw [hmemL, hψ]; exact hℓ
    have h2 := (mem_normalizer_iff.mp hcn _).mp h1
    rwa [hmemL, ψ.map_mul, ψ.map_mul, ψ.map_inv, hψ, hψ] at h2
  · intro hℓ
    have hℓX : ℓ ∈ S.Xbar12 g := by
      have h1 : c * ℓ * c⁻¹ ∈ S.Xbar12 g := hXM ▸ S.Lbar_le_Mbar g hℓ
      have h2 : c⁻¹ * (c * ℓ * c⁻¹) * c ∈ S.Xbar12 g := mul_mem (mul_mem (inv_mem hcX) h1) hcX
      simpa [mul_assoc] using h2
    have h1 : φ ⟨c, hcX⟩ * φ ⟨ℓ, hℓX⟩ * (φ ⟨c, hcX⟩)⁻¹ ∈ L := by
      rw [hmemL, ψ.map_mul, ψ.map_mul, ψ.map_inv, hψ, hψ]
      exact hℓ
    have h2 := (mem_normalizer_iff.mp hcn _).mpr h1
    rwa [hmemL, hψ] at h2

omit [IsSimpleGroup G] in
theorem fuseCert_of_sp3 (hc : Ctx S g t)
    (h : FischerSp3 (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : S.S12FuseCert g t := by
  obtain ⟨m, hm, b, halt, hnd, φ, hφ⟩ := h
  have hE := mem_Ebar12_of_mem_Lbar hc.ht hc.htA
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 hE
  obtain ⟨v, hv0, hvT⟩ := (hφ ⟨t, htX⟩).1 hE
  exact fuseCert_of_sp_four hc.haQ hc.hne hc.hw hc.ht hc.htA hc.hS hm halt hnd φ htX hv0 hvT

omit [IsSimpleGroup G] in
theorem false_of_psu (hc : Ctx S g t)
    (h : FischerPSU (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : False := by
  obtain ⟨m, hm4, hmod⟩ := h
  have hn : 3 ≤ S.width := by have := hc.hw; omega
  rcases Nat.lt_or_ge m 5 with hm5 | hm5
  · obtain rfl : m = 4 := by omega
    by_cases hy : ∀ y ∈ S.Xbar12 g, y ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) →
        y ^ 3 = 1 → y ≠ 1 → ∃ x ∈ S.Xbar12 g, x ∈ S.Lbar g ∧
          x ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∧ x * y ≠ y * x
    · exact S12I4M.false_of_psu_four hc.haQ hc.hne hc.hw hc.ht hc.htA hc.hred hmod hy
    · push Not at hy
      obtain ⟨y, hyX, hyK, hy3, hy1, hcomm⟩ := hy
      exact false_of_order_three_mem_fixSub12 hc.haQ hc.hne hn hc.ht hc.htA
        (Xbar12_le_Mbar hyX) hyX hyK hy3 hy1 hcomm
  · exact false_of_psu_ge_five hc.haQ hc.hne hn hc.ht hc.htA hm5 hmod

omit [IsSimpleGroup G] in
theorem false_of_f3 (hc : Ctx S g t)
    (h : FischerF3 (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : False := by
  obtain ⟨m, hm, f, hsymm, hnd, hmodel⟩ := h
  have hn : 3 ≤ S.width := by have := hc.hw; omega
  have hf : CFSG.Fischer.Classification.IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff _).1 hmodel
  by_cases hm6 : 6 ≤ m
  · exact false_of_R3 r3SimpleInput hc.haQ hc.hne hn hc.ht hc.htA hm hf (fun h => by omega) ψ hψ
  obtain rfl : m = 5 := by omega
  rcases CFSG.Fischer.Classification.R3_five_cases hf with ⟨h45, -⟩ | ⟨h36, -⟩
  · obtain ⟨ψ', hψ'⟩ := CFSG.Fischer.Classification.exists_mulEquiv_U2_four_of_ncard hf h45
    have himg : ψ '' (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) =
        CFSG.Fischer.Classification.D3 f := by
      ext q
      refine ⟨?_, fun hq => ⟨ψ.symm q, (hψ _).2 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply ψ q⟩⟩
      rintro ⟨x, hx, rfl⟩
      exact (hψ x).1 hx
    have hmodel' : CFSG.Open.fischerCentralQuotientModel
        (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
        (CFSG.Fischer.Classification.Unitary.SUm 4)
        (CFSG.Fischer.Classification.Unitary.TU 4) := by
      refine CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2.2 ⟨ψ.trans ψ', ?_⟩
      rw [MulEquiv.coe_trans, Set.image_comp, himg, hψ']
    exact false_of_psu hc ⟨4, le_rfl, hmodel'⟩
  · exact false_of_R3 r3SimpleInput hc.haQ hc.hne hn hc.ht hc.htA le_rfl hf (fun _ => h36) ψ hψ

omit [IsSimpleGroup G] in
theorem false_of_fi (hc : Ctx S g t)
    (h : FischerFi (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : False := by
  have hd := card_Xbar_dvd S g hc.hw
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at hd <;> norm_num at hd

end CFSG.GF2Type.Smith1979.W4Insp
