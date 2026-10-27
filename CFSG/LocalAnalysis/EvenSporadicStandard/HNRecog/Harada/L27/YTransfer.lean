module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.FiveSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.SylowConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

theorem smallSections_quotient {X : Type} [Group X] (N : Subgroup X) [N.Normal]
    (h : SmallSections X) : SmallSections (X ⧸ N) := by
  intro Kbar Lbar inst hsimple hnonab
  letI : Lbar.Normal := inst
  letI : IsSimpleGroup (Kbar ⧸ Lbar) := hsimple
  let K : Subgroup X := Kbar.comap (QuotientGroup.mk' N)
  let f : K →* Kbar ⧸ Lbar :=
    (QuotientGroup.mk' Lbar).comp ((QuotientGroup.mk' N).subgroupComap Kbar)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective Lbar x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (k : X ⧸ N)
    let yK : K := ⟨y, by
      show (QuotientGroup.mk' N) y ∈ Kbar
      rw [hy]
      exact k.2⟩
    refine ⟨yK, ?_⟩
    have hsub : ((QuotientGroup.mk' N).subgroupComap Kbar) yK = k :=
      Subtype.ext hy
    show (QuotientGroup.mk' Lbar) (((QuotientGroup.mk' N).subgroupComap Kbar) yK) = x
    rw [hsub, hk]
  let e : K ⧸ f.ker ≃* Kbar ⧸ Lbar := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hnonab' : ∃ a b : K ⧸ f.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, ?_⟩
    intro hcontra
    apply hab
    have hh := congrArg e hcontra
    simpa using hh
  have hres := h K f.ker (MulEquiv.isSimpleGroup e) hnonab'
  constructor
  · rw [← Nat.card_congr e.toEquiv]
    exact hres.1
  · haveI : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (K ⧸ f.ker)) := hres.2
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e

theorem nonempty_mulEquiv_map_mk' {X : Type*} [Group X] (S : Subgroup X) [S.Normal]
    (K : Subgroup X) (h : K ⊓ S = ⊥) : Nonempty (K.map (QuotientGroup.mk' S) ≃* K) := by
  have hf : Function.Injective ((QuotientGroup.mk' S).domRestrict K) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [← Subgroup.inf_subgroupOf_left S K, h, Subgroup.bot_subgroupOf]
  have hrange : ((QuotientGroup.mk' S).domRestrict K).range = K.map (QuotientGroup.mk' S) :=
    MonoidHom.domRestrict_range K (QuotientGroup.mk' S)
  exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem nonconj_of_wrData {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : X →* (W ≃ₗ[ZMod 2] W)} {w : W} {P F : Subgroup X} {v : X}
    (h : WrData X ρ w P F v) :
    ∀ x ∈ F, orderOf x = 5 → ∀ p ∈ P, orderOf p = 5 →
      ∀ y : X, y * x * y⁻¹ ∉ Subgroup.zpowers p := by
  intro x hx hxord p hp hpord y hyconj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyconj
  have hpkP : p ^ k ∈ P := Subgroup.zpow_mem (K := P) hp k
  have h1 : ρ (p ^ k) w = w := h.P_fix (p ^ k) hpkP
  have h2 : ρ (y * x * y⁻¹) w = w := by
    rw [← hk]
    exact h1
  set z : W := (ρ y)⁻¹ w with hz
  have hyz : ρ y z = w := by
    rw [hz]
    exact LinearEquiv.apply_symm_apply (ρ y) w
  have h2' : ρ y (ρ x z) = w := by
    have hh := h2
    rw [map_mul, map_mul, map_inv] at hh
    simpa only [LinearEquiv.mul_apply, ← hz] using hh
  have hzfix : ρ x z = z := by
    have hh : (ρ y).symm (ρ y (ρ x z)) = (ρ y).symm w := congrArg (ρ y).symm h2'
    simpa [hz] using hh
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hzero : ρ y z = 0 := by simp [hz0]
    rw [hyz] at hzero
    exact h.w_ne_zero hzero
  exact hz_ne (h.F_fpf x hx hxord z hzfix)

theorem nonconj_quotient {X : Type} [Group X] [Finite X] (S : Subgroup X) [S.Normal]
    (h5 : ¬ 5 ∣ Nat.card S) {F P' : Subgroup X} (hF : F ⊓ S = ⊥) (hP : P' ⊓ S = ⊥)
    (hnc : ∀ x ∈ F, orderOf x = 5 → ∀ p ∈ P', orderOf p = 5 →
      ∀ y : X, y * x * y⁻¹ ∉ Subgroup.zpowers p) :
    ∀ x ∈ F.map (QuotientGroup.mk' S), orderOf x = 5 →
      ∀ p ∈ P'.map (QuotientGroup.mk' S), orderOf p = 5 →
        ∀ y : X ⧸ S, y * x * y⁻¹ ∉ Subgroup.zpowers p := by
  intro x hx hxord p hp hpord y hyconj
  obtain ⟨x₀, hx₀F, hx₀eq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨p₀, hp₀P, hp₀eq⟩ := Subgroup.mem_map.mp hp
  have hinjF : Function.Injective ((QuotientGroup.mk' S).domRestrict F) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [← Subgroup.inf_subgroupOf_left S F, hF, Subgroup.bot_subgroupOf]
  have hinjP : Function.Injective ((QuotientGroup.mk' S).domRestrict P') := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [← Subgroup.inf_subgroupOf_left S P', hP, Subgroup.bot_subgroupOf]
  have hxord₀ : orderOf x₀ = 5 := by
    have hh := orderOf_injective ((QuotientGroup.mk' S).domRestrict F) hinjF ⟨x₀, hx₀F⟩
    rw [MonoidHom.domRestrict_apply, hx₀eq] at hh
    have hxo : orderOf x₀ = orderOf x :=
      (Subgroup.orderOf_coe (⟨x₀, hx₀F⟩ : F)).trans hh.symm
    rw [hxo, hxord]
  have hpord₀ : orderOf p₀ = 5 := by
    have hh := orderOf_injective ((QuotientGroup.mk' S).domRestrict P') hinjP ⟨p₀, hp₀P⟩
    rw [MonoidHom.domRestrict_apply, hp₀eq] at hh
    have hpo : orderOf p₀ = orderOf p :=
      (Subgroup.orderOf_coe (⟨p₀, hp₀P⟩ : P')).trans hh.symm
    rw [hpo, hpord]
  have hZS : Subgroup.zpowers p₀ ⊓ S = ⊥ := by
    apply le_bot_iff.mp
    calc Subgroup.zpowers p₀ ⊓ S ≤ P' ⊓ S :=
          inf_le_inf_right S (Subgroup.zpowers_le.mpr hp₀P)
      _ = ⊥ := hP
  let L : Subgroup X := S ⊔ Subgroup.zpowers p₀
  have hrelZ : S.relIndex (Subgroup.zpowers p₀) = 5 := by
    rw [← QuotientGroup.ker_mk' (N := S), Subgroup.relIndex_ker]
    have hiso : Nat.card ((Subgroup.zpowers p₀).map (QuotientGroup.mk' S)) =
        Nat.card (Subgroup.zpowers p₀) := by
      obtain ⟨e⟩ := nonempty_mulEquiv_map_mk' S (Subgroup.zpowers p₀) hZS
      exact Nat.card_congr e.toEquiv
    rw [hiso, Nat.card_zpowers]
    exact hpord₀
  have hcard : Nat.card L = 5 * Nat.card S := by
    have hh := Subgroup.relIndex_mul_card (H := S) (K := L)
    have hSinfL : S ⊓ L = S := inf_eq_left.mpr le_sup_left
    rw [hSinfL] at hh
    have hrel : S.relIndex L = 5 := by
      change S.relIndex (S ⊔ Subgroup.zpowers p₀) = 5
      rw [sup_comm, Subgroup.relIndex_sup_right]
      exact hrelZ
    rw [hrel] at hh
    exact hh.symm
  have hnot25 : ¬ 25 ∣ Nat.card L := by
    rw [hcard, show (25 : ℕ) = 5 * 5 from by norm_num,
      mul_dvd_mul_iff_left (by norm_num : (5 : ℕ) ≠ 0)]
    exact h5
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective S y
  have hπconj : (QuotientGroup.mk' S) (g * x₀ * g⁻¹) = y * x * y⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg, hx₀eq]
  have hmem : (QuotientGroup.mk' S) (g * x₀ * g⁻¹) ∈ Subgroup.zpowers p := by
    rw [hπconj]
    exact hyconj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hpk : (QuotientGroup.mk' S) (p₀ ^ k) = (QuotientGroup.mk' S) (g * x₀ * g⁻¹) := by
    rw [map_zpow, hp₀eq]
    exact hk
  have hsS : (g * x₀ * g⁻¹) * (p₀ ^ k)⁻¹ ∈ S := by
    rw [← QuotientGroup.ker_mk' (N := S), MonoidHom.mem_ker]
    rw [map_mul, map_inv, hpk, mul_inv_cancel]
  have hz_mem : g * x₀ * g⁻¹ ∈ L := by
    have hdecomp : g * x₀ * g⁻¹ = ((g * x₀ * g⁻¹) * (p₀ ^ k)⁻¹) * p₀ ^ k := by group
    rw [hdecomp]
    exact L.mul_mem
      (Subgroup.mem_sup_left (S := S) (T := Subgroup.zpowers p₀) hsS)
      (Subgroup.mem_sup_right (S := S) (T := Subgroup.zpowers p₀)
        (Subgroup.zpow_mem_zpowers p₀ k))
  have hzord : orderOf (g * x₀ * g⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj g) x₀]
    exact hxord₀
  have hp₀_mem : p₀ ∈ L :=
    Subgroup.mem_sup_right (S := S) (T := Subgroup.zpowers p₀) (Subgroup.mem_zpowers p₀)
  obtain ⟨l, -, hl_conj⟩ :=
    exists_conj_mem_zpowers_of_five L hnot25 hz_mem hp₀_mem hzord hpord₀
  have hconj2 : (l * g) * x₀ * (l * g)⁻¹ ∈ Subgroup.zpowers p₀ := by
    convert hl_conj using 1
    group
  exact hnc x₀ hx₀F hxord₀ p₀ hp₀P hpord₀ (l * g) hconj2

theorem centralizer_quotient_le {X : Type} [Group X] (S : Subgroup X) [S.Normal] [Finite S]
    {F : Subgroup X} {v : X} (hinv : ∀ s ∈ S, v * s * v⁻¹ = s⁻¹)
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hodd : Odd (Nat.card S))
    (hC : ∀ g : X, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v) :
    ∀ y : X ⧸ S, y * QuotientGroup.mk' S v = QuotientGroup.mk' S v * y →
      y ∈ F.map (QuotientGroup.mk' S) ⊔ Subgroup.zpowers (QuotientGroup.mk' S v) := by
  intro y hy
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective S y
  have hcomm : y * (QuotientGroup.mk' S) v * y⁻¹ = (QuotientGroup.mk' S) v := by
    rw [hy, mul_assoc, mul_inv_cancel, mul_one]
  have hsS : g * v * g⁻¹ * v⁻¹ ∈ S := by
    rw [← QuotientGroup.ker_mk' (N := S), MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, hcomm, mul_inv_cancel]
  set s : X := g * v * g⁻¹ * v⁻¹ with hsdef
  have hsS' : s ∈ S := by
    rw [hsdef]
    exact hsS
  obtain ⟨m, hm⟩ := hodd
  let t : S := (⟨s, hsS'⟩ : S) ^ (m + 1)
  have ht : t * t = ⟨s, hsS'⟩ := by
    have hpow : t * t = (⟨s, hsS'⟩ : S) ^ (m + 1 + (m + 1)) := by
      change (⟨s, hsS'⟩ : S) ^ (m + 1) * (⟨s, hsS'⟩ : S) ^ (m + 1) =
        (⟨s, hsS'⟩ : S) ^ (m + 1 + (m + 1))
      rw [← pow_add]
    rw [hpow]
    have hsum : m + 1 + (m + 1) = Nat.card S + 1 := by omega
    rw [hsum, pow_succ, pow_card_eq_one', one_mul]
  have ht2 : (t : X) * (t : X) = s := by
    have hh : ((t * t : S) : X) = (t : X) * (t : X) := rfl
    rw [ht] at hh
    exact hh.symm
  have htv : (t : X) * v * (t : X)⁻¹ = s * v := by
    have hinvt : v * (t : X) * v⁻¹ = (t : X)⁻¹ := hinv (t : X) t.2
    have hinvt' : v * (t : X)⁻¹ * v⁻¹ = (t : X) := by
      calc v * (t : X)⁻¹ * v⁻¹ = (v * (t : X) * v⁻¹)⁻¹ := by group
        _ = ((t : X)⁻¹)⁻¹ := by rw [hinvt]
        _ = (t : X) := inv_inv _
    calc (t : X) * v * (t : X)⁻¹
        = (t : X) * (v * (t : X)⁻¹ * v⁻¹) * v := by group
      _ = (t : X) * (t : X) * v := by rw [hinvt']
      _ = s * v := by rw [ht2]
  have hgv : g * v * g⁻¹ = s * v := by
    rw [hsdef]
    group
  have hgcomm : ((t : X)⁻¹ * g) * v = v * ((t : X)⁻¹ * g) := by
    have hgt : g * v * g⁻¹ = (t : X) * v * (t : X)⁻¹ := hgv.trans htv.symm
    have key : ((t : X)⁻¹ * g) * v * ((t : X)⁻¹ * g)⁻¹ = v := by
      calc ((t : X)⁻¹ * g) * v * ((t : X)⁻¹ * g)⁻¹
          = (t : X)⁻¹ * (g * v * g⁻¹) * (t : X) := by group
        _ = (t : X)⁻¹ * ((t : X) * v * (t : X)⁻¹) * (t : X) := by rw [hgt]
        _ = v := by group
    calc ((t : X)⁻¹ * g) * v
        = (((t : X)⁻¹ * g) * v * ((t : X)⁻¹ * g)⁻¹) * ((t : X)⁻¹ * g) := by group
      _ = v * ((t : X)⁻¹ * g) := by rw [key]
  have htπ : (QuotientGroup.mk' S) (t : X) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (t : X)).mpr t.2
  have hπeq : (QuotientGroup.mk' S) ((t : X)⁻¹ * g) = y := by
    rw [map_mul, map_inv, htπ, hg]
    simp
  have hmemmap : y ∈ (F ⊔ Subgroup.zpowers v).map (QuotientGroup.mk' S) :=
    Subgroup.mem_map.mpr ⟨(t : X)⁻¹ * g, hC _ hgcomm, hπeq⟩
  rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at hmemmap

theorem finalData_quotient {X : Type} [Group X] [Finite X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] {ρ : X →* (W ≃ₗ[ZMod 2] W)} {w : W} {P F : Subgroup X}
    {v : X} (h : WrData X ρ w P F v) :
    FinalData (X ⧸ CFSG.solvableRadical X) (P.map (QuotientGroup.mk' (CFSG.solvableRadical X)))
      (F.map (QuotientGroup.mk' (CFSG.solvableRadical X)))
      (QuotientGroup.mk' (CFSG.solvableRadical X) v) := by
  let S : Subgroup X := CFSG.solvableRadical X
  haveI hSn : S.Normal := inferInstance
  obtain ⟨hvS, -, hinv, hab, hodd⟩ := radical_structure h
  have h5 : ¬ 5 ∣ Nat.card S := not_five_dvd_card_solvableRadical h
  have hPS : P ⊓ S = ⊥ := by
    obtain ⟨eP⟩ := h.P_iso
    exact inf_eq_bot_of_equiv_perm_five P eP S
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := X))
  have hFS : F ⊓ S = ⊥ := by
    obtain ⟨eF⟩ := h.F_iso
    exact inf_eq_bot_of_equiv_a5 F eF S
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := X))
  have hP'_le_P : ⁅P, P⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have hP'_S : ⁅P, P⁆ ⊓ S = ⊥ := by
    apply le_bot_iff.mp
    calc ⁅P, P⁆ ⊓ S ≤ P ⊓ S := inf_le_inf_right S hP'_le_P
      _ = ⊥ := hPS
  refine
    { free := CFSG.ComponentClassification.SolvableRadical.quotient_free X
      card_le := (Nat.card_le_card_of_surjective (QuotientGroup.mk' S)
        (QuotientGroup.mk'_surjective S)).trans h.card_le
      P_iso := ?_
      F_iso := ?_
      v_sq := ?_
      v_ne_one := ?_
      F_comm := ?_
      centralizer_le := ?_
      nonconj := ?_ }
  · obtain ⟨e⟩ := h.P_iso
    obtain ⟨e'⟩ := nonempty_mulEquiv_map_mk' S P hPS
    exact ⟨e'.trans e⟩
  · obtain ⟨e⟩ := h.F_iso
    obtain ⟨e'⟩ := nonempty_mulEquiv_map_mk' S F hFS
    exact ⟨e'.trans e⟩
  · rw [← map_mul, h.v_sq, map_one]
  · intro hπv
    apply hvS
    exact (QuotientGroup.eq_one_iff v).mp (by simpa only [QuotientGroup.mk'_apply] using hπv)
  · intro f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Subgroup.mem_map.mp hf
    rw [← map_mul, ← map_mul, h.F_comm f₀ hf₀]
  · exact centralizer_quotient_le S hinv hab hodd h.centralizer_le
  · rw [← Subgroup.map_commutator]
    exact nonconj_quotient S h5 hFS hP'_S
      (fun x hx hxord p hp hpord y => nonconj_of_wrData h x hx hxord p (hP'_le_P hp) hpord y)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
