module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.KFact2811

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6

open CFSG.Open CFSG.GH74.Exceptional Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

namespace PSp43

variable {T : Type*} [Group T] [Finite T] {L : Subgroup T} [L.Normal]

theorem exists_fixed_conj {U : Subgroup T} (hU : IsPGroup 3 U) (s : T → Prop)
    (hs : ∀ u ∈ U, ∀ y, s y → s (u * y * u⁻¹)) (hcard : ¬ 3 ∣ Nat.card {y // s y}) :
    ∃ y, s y ∧ ∀ u ∈ U, u * y * u⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : MulAction U {y // s y} :=
    { smul := fun u y => ⟨(u : T) * y.1 * (u : T)⁻¹, hs u u.2 y.1 y.2⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : U) : T) * y.1 * ((1 : U) : T)⁻¹ = y.1
        simp)
      mul_smul := fun u v y => Subtype.ext (by
        show ((u * v : U) : T) * y.1 * ((u * v : U) : T)⁻¹ =
          (u : T) * ((v : T) * y.1 * (v : T)⁻¹) * (u : T)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  obtain ⟨⟨y, hy⟩, hfix⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card _ hcard
  refine ⟨y, hy, fun u hu => ?_⟩
  have := hfix ⟨u, hu⟩
  exact congrArg Subtype.val this

theorem exists_outer_centralizing {U Y : Subgroup T} (hUL : U ≤ L) (hU : IsPGroup 3 U)
    (hY : IsPGroup 2 Y) (hN : U ≤ normalizer (Y : Set T)) {c : T} (hcY : c ∈ Y) (hcL : c ∉ L) :
    ∃ c' ∈ Y, c' ∉ L ∧ ∀ u ∈ U, u * c' * u⁻¹ = c' := by
  set s : T → Prop := fun y => y ∈ Y ∧ y * c⁻¹ ∈ L
  have hs : ∀ u ∈ U, ∀ y, s y → s (u * y * u⁻¹) := by
    rintro u hu y ⟨hyY, hyL⟩
    refine ⟨(mem_normalizer_iff.1 (hN hu) y).1 hyY, ?_⟩
    have huL := hUL hu
    have h1 : c * u⁻¹ * c⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ (L.inv_mem huL) c
    have : u * y * u⁻¹ * c⁻¹ = u * (y * c⁻¹) * (c * u⁻¹ * c⁻¹) := by group
    rw [this]
    exact mul_mem (mul_mem huL hyL) h1
  have hcard : ¬ 3 ∣ Nat.card {y // s y} := by
    have e : Nat.card {y // s y} = Nat.card ↥(Y ⊓ L) := by
      refine Nat.card_congr
        { toFun := fun y => ⟨y.1 * c⁻¹, Subgroup.mem_inf.2 ⟨Y.mul_mem y.2.1 (Y.inv_mem hcY), y.2.2⟩⟩
          invFun := fun w => ⟨w.1 * c, ⟨Y.mul_mem (Subgroup.mem_inf.1 w.2).1 hcY,
            by simpa using (Subgroup.mem_inf.1 w.2).2⟩⟩
          left_inv := fun y => Subtype.ext (by simp)
          right_inv := fun w => Subtype.ext (by simp) }
    rw [e]
    obtain ⟨n, hn⟩ := (hY.to_le (inf_le_left : Y ⊓ L ≤ Y)).exists_card_eq
    rw [hn]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  obtain ⟨c', ⟨hc'Y, hc'L⟩, hfix⟩ := exists_fixed_conj hU s hs hcard
  refine ⟨c', hc'Y, fun h => hcL ?_, hfix⟩
  have : c = (c' * c⁻¹)⁻¹ * c' := by group
  rw [this]
  exact mul_mem (inv_mem hc'L) h

end PSp43

theorem kFactPSp43TwoSubgroups_holds : KFactPSp43TwoSubgroups := by
  intro T _ _ L hLn ⟨e⟩ hC Q U x hQL hQ hQc hUQ hUc hxU hxL hxc hwc Y hY hN
  set φ := modelHom e
  have hφ := modelHom_injective e
  set φ' : L ≃* P := e.trans psiEquiv
  have hφφ' : ∀ ℓ : L, (φ' ℓ : Equiv.Perm (Fin 45)) = φ ℓ := fun ℓ => rfl
  have hUL : U ≤ L := hUQ.trans hQL
  set x₀ : L := ⟨x, hxL⟩
  set Q₀ := Q.comap L.subtype
  set U₀ := U.comap L.subtype
  have hQ₀ : Q₀.map L.subtype = Q := map_comap_subtype hQL
  have hU₀ : U₀.map L.subtype = U := map_comap_subtype hUL
  have hU₀Q₀ : U₀ ≤ Q₀ := Subgroup.comap_mono hUQ
  have hQ'P : Q₀.map φ ≤ P := fun q hq => by
    obtain ⟨a, -, rfl⟩ := hq
    exact modelHom_mem e a
  have hQ'comm : ∀ a ∈ Q₀.map φ, ∀ b ∈ Q₀.map φ, a * b = b * a :=
    comm_of_map (fun u hu v hv => L.subtype_injective (by
      rw [map_mul, map_mul]; exact comm_of_isElemAbelian hQ _ hu _ hv))
  have hQ'c : Nat.card (Q₀.map φ) = 27 := by
    rw [Subgroup.card_map_of_injective hφ, ← Subgroup.card_map_of_injective L.subtype_injective,
      hQ₀, hQc]
  have hU'c : Nat.card (U₀.map φ) = 9 := by
    rw [Subgroup.card_map_of_injective hφ, ← Subgroup.card_map_of_injective L.subtype_injective,
      hU₀, hUc]
  have hxU₀ : x₀ ∈ U₀ := hxU
  have hxc' := card_model_centralizer e x₀
  rw [hxc] at hxc'
  have hconjT : ∀ (H : Subgroup L) (ℓ : L), (H.map (MulAut.conj ℓ).toMonoidHom).map L.subtype =
      (H.map L.subtype).map (MulAut.conj (ℓ : T)).toMonoidHom := fun H ℓ =>
    PSp43.map_map_conj L.subtype H ℓ
  have hwc' : ∀ h ∈ P, (zpowers (φ x₀)).map (MulAut.conj h).toMonoidHom ≤ U₀.map φ →
      (zpowers (φ x₀)).map (MulAut.conj h).toMonoidHom = zpowers (φ x₀) := by
    intro h hh hle
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : L, φ ℓ = h := (range_modelHom e ▸ hh : h ∈ φ.range)
    rw [← MonoidHom.map_zpowers, ← PSp43.map_map_conj] at hle ⊢
    rw [Subgroup.map_le_map_iff_of_injective hφ] at hle
    have h1 := Subgroup.map_mono (f := L.subtype) hle
    rw [hconjT, hU₀, MonoidHom.map_zpowers] at h1
    have h2 := hwc ℓ ℓ.2 h1
    have h3 : (zpowers x₀).map (MulAut.conj ℓ).toMonoidHom = zpowers x₀ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [hconjT, MonoidHom.map_zpowers L.subtype x₀]
      exact h2
    rw [h3]
  obtain ⟨g, hgP, hgU⟩ := exists_conj_edge hQ'P hQ'comm hQ'c (Subgroup.map_mono hU₀Q₀) hU'c
    ⟨x₀, hxU₀, rfl⟩ hxc' hwc'
  have hU3 : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hUc]; norm_num)
  have hYL : Y ≤ L := by
    intro c hcY
    by_contra hcL
    obtain ⟨c', hc'Y, hc'L, hc'U⟩ :=
      PSp43.exists_outer_centralizing hUL hU3 hY hN hcY hcL
    set Φ : T →* Equiv.Perm (Fin 45) :=
      autPerm.comp ((MulAut.congr φ').toMonoidHom.comp MulAut.conjNormal)
    set α : MulAut P := MulAut.congr φ' (MulAut.conjNormal c')
    have hΦ : Φ c' = autPerm α := rfl
    have hαu : ∀ u ∈ U₀, α (φ' u) = φ' u := by
      intro u hu
      have hcu : (c' : T) * u * c'⁻¹ = u := by
        have h := hc'U u hu
        calc (c' : T) * u * c'⁻¹ = (u * c' * (u : T)⁻¹) * u * c'⁻¹ := by rw [h]
          _ = u := by group
      have h1 : MulAut.conjNormal c' u = u :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hcu)
      show φ' (MulAut.conjNormal c' (φ'.symm (φ' u))) = φ' u
      rw [MulEquiv.symm_apply_apply, h1]
    have hcomm : ∀ u' ∈ U₀.map φ, Φ c' * u' = u' * Φ c' := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : α * MulAut.conj (φ' u) = MulAut.conj (φ' u) * α := by
        ext y
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hαu u hu]
      have h2 := congrArg autPerm h1
      rw [map_mul, map_mul, autPerm_conj] at h2
      rw [hΦ]
      exact h2
    have h2c : IsPGroup 2 (zpowers (Φ c')) := by
      rw [← MonoidHom.map_zpowers]
      exact (hY.to_le ((zpowers_le).2 hc'Y)).map _
    have hπP := mem_P_of_equivariant_conj hgP hgU (hΦ ▸ isEquivariant_autPerm α) hcomm h2c
    set p : P := ⟨Φ c', hπP⟩
    have hαp : α = MulAut.conj p := autPerm_injective (by rw [autPerm_conj, ← hΦ])
    set ℓ₀ : L := φ'.symm p
    have hcomm' : ∀ ℓ : L, (c' : T) * ℓ * c'⁻¹ = (ℓ₀ : T) * ℓ * (ℓ₀ : T)⁻¹ := by
      intro ℓ
      have h1 : φ' (MulAut.conjNormal c' ℓ) = p * φ' ℓ * p⁻¹ := by
        have h0 : α (φ' ℓ) = p * φ' ℓ * p⁻¹ := by rw [hαp]; rfl
        have e1 : α (φ' ℓ) = φ' (MulAut.conjNormal c' ℓ) := by
          show φ' (MulAut.conjNormal c' (φ'.symm (φ' ℓ))) = _
          rw [MulEquiv.symm_apply_apply]
        rw [← e1, h0]
      have h2 : MulAut.conjNormal c' ℓ = ℓ₀ * ℓ * ℓ₀⁻¹ := by
        apply φ'.injective
        rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      have := congrArg Subtype.val h2
      rw [MulAut.conjNormal_apply] at this
      simpa using this
    have hcen : (ℓ₀ : T)⁻¹ * c' ∈ centralizer (L : Set T) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := hcomm' ⟨y, hy⟩
      calc y * ((ℓ₀ : T)⁻¹ * c') =
            (ℓ₀ : T)⁻¹ * ((ℓ₀ : T) * y * (ℓ₀ : T)⁻¹) * ℓ₀ * ((ℓ₀ : T)⁻¹ * c') := by
            group
        _ = (ℓ₀ : T)⁻¹ * (c' * y * c'⁻¹) * ℓ₀ * ((ℓ₀ : T)⁻¹ * c') := by rw [h1]
        _ = (ℓ₀ : T)⁻¹ * c' * y := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    exact hc'L (hcen ▸ ℓ₀.2)
  set Y₀ := Y.comap L.subtype
  have hY₀ : Y₀.map L.subtype = Y := map_comap_subtype hYL
  have hY'P : Y₀.map φ ≤ P := fun q hq => by
    obtain ⟨a, -, rfl⟩ := hq
    exact modelHom_mem e a
  have hY' : IsPGroup 2 (Y₀.map φ) := by
    have : IsPGroup 2 Y₀ := hY.of_equiv
      ((Subgroup.equivMapOfInjective Y₀ L.subtype L.subtype_injective).trans
        (MulEquiv.subgroupCongr hY₀)).symm
    exact this.map _
  have hN' : U₀.map φ ≤ normalizer ((Y₀.map φ : Subgroup _) : Set (Equiv.Perm (Fin 45))) := by
    rintro _ ⟨u, hu, rfl⟩
    refine mem_normalizer_of_conj_mem' _ _ fun y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    refine ⟨u * y₀ * u⁻¹, ?_, by simp⟩
    show ((u * y₀ * u⁻¹ : L) : T) ∈ Y
    exact (mem_normalizer_iff.1 (hN hu) y₀).1 hy₀
  obtain ⟨z', hz'P, hz'2, hz'1, hz'c, hYz'⟩ := exists_z_of_normalized hgP hgU hY'P hY' hN'
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : L, φ z₀ = z' := (range_modelHom e ▸ hz'P : z' ∈ φ.range)
  right
  refine ⟨z₀, z₀.2, ?_, ?_, ?_, ?_⟩
  · have : z₀ ^ 2 = 1 := hφ (by rw [map_pow, hz'2, map_one])
    exact congrArg Subtype.val this
  · intro h
    apply hz'1
    have : z₀ = 1 := Subtype.ext h
    rw [this, map_one]
  · rw [← card_model_centralizer e z₀]
    exact hz'c
  · rw [← map_model_centralizer, pCoreOf_map_of_injective' hφ,
      Subgroup.map_le_map_iff_of_injective hφ] at hYz'
    rw [← hY₀, ← map_subtype_centralizer, pCoreOf_map_of_injective' L.subtype_injective]
    exact Subgroup.map_mono hYz'

end CFSG.LocalAnalysis.RankThreeTheoremC.A6
